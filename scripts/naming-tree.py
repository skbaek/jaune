#!/usr/bin/env python3
"""Plan and apply compiler-resolved renames across a captured Lean source tree.

All tracked and unignored files are bound to the capture. Every Lean source is
scanned; any affected source without compiler references prevents application.
No build or elaboration runs here. Output plans belong outside the checkout (or
in an ignored directory), so they do not change their own input inventory.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys
import subprocess

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location('naming_candidate', ROOT / 'scripts/naming-candidate.py')
CANDIDATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CANDIDATE)
APPLY = CANDIDATE.FIDELITY.APPLY
MAP = CANDIDATE.FIDELITY.MAP


def read_map(path):
    data = json.loads(Path(path).read_bytes())
    CANDIDATE.FIDELITY.MAP.validate_map(data)
    return data


def words(entries):
    return MAP.Renamer(entries).words()


def code_only(text):
    """Blank comments and plain string contents, keeping offsets (lexer rules)."""
    out, i = list(text), 0
    def blank(a, b):
        for k in range(a, b):
            if out[k] not in '\r\n':
                out[k] = ' '
    while i < len(text):
        if text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            blank(i, end)
            i = end
        elif text.startswith('/-', i):
            depth, j = 1, i + 2
            while depth and j < len(text):
                if text.startswith('/-', j):
                    depth, j = depth + 1, j + 2
                elif text.startswith('-/', j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            blank(i, j)
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            blank(i + 1, min(j, len(text)))
            i = j + 1
        else:
            i += 1
    return ''.join(out)


IMPORT = re.compile(r'^[ \t]*(?:(?:public|meta|private)[ \t]+)*import[ \t]+(?:all[ \t]+)?([^\s]+)', re.M)


def import_spans(text, expected):
    """Lexed import module spans, accepted only when they equal Lean's own
    header parse (the capture's compiler header inventory)."""
    code = code_only(text)
    found = [(m.start(1), m.end(1), APPLY.module_name(m.group(1))) for m in IMPORT.finditer(code)]
    if [name for _, _, name in found] != list(expected):
        raise ValueError('lexed imports differ from the compiler header inventory')
    return found


def closure_of(modules, root):
    seen, stack = set(), [root]
    while stack:
        module = stack.pop()
        for dependency in modules.get(module, {}).get('imports', []):
            if dependency in modules and dependency not in seen:
                seen.add(dependency)
                stack.append(dependency)
    return seen


def occurrences(text, affected):
    return [(a, b, word) for a, b, word in APPLY.identifiers(text) if word in affected]


def needs(root, source_dirs, mapping):
    inventory = CANDIDATE.inventory(root, source_dirs)
    modules = {row['path']: name for name, row in inventory['modules'].items()}
    affected = words(mapping['entries'])
    files = []
    for path in sorted(inventory['files']):
        if not path.endswith('.lean'):
            continue
        matches = occurrences((root / path).read_bytes().decode('utf-8'), affected)
        if matches:
            files.append(dict(path=path, module=modules.get(path), tokens=len(matches)))
    return dict(status='OK', scope='tracked-and-unignored-lean-sources',
                inventory_sha256=APPLY.digest(CANDIDATE.FIDELITY.encoded(inventory).encode()),
                lean_sources=sum(p.endswith('.lean') for p in inventory['files']),
                modules=sorted(row['module'] for row in files if row['module']), files=files)


def current_inventory(root, candidate):
    current = CANDIDATE.inventory(root, candidate['source_dirs'])
    # HEAD is provenance, not source identity: committing unchanged bytes must
    # not invalidate an otherwise exact capture.
    if current['files'] != candidate['files'] or current['modules'] != {
            name: {k: row[k] for k in ('path', 'sha256')}
            for name, row in candidate['modules'].items()}:
        raise ValueError('tree inventory changed since capture (added, removed or modified input)')
    return current


def current_artifacts(snapshot):
    for field in ('artifacts', 'local_built'):
        records = snapshot[field]
        paths = {name: {part: row['path'] if row else None for part, row in parts.items()}
                 for name, parts in records.items()}
        if CANDIDATE.bind_artifacts(paths) != records:
            raise ValueError(f'{field} changed since capture; re-export current imports')


def plan_sources(root, candidate, bundles, mapping):
    """Pure planning over an already-validated source inventory and bundles."""
    by_path = {row['path']: name for name, row in candidate['modules'].items()}
    renamer = MAP.Renamer(mapping['entries'])
    affected = renamer.words()
    records, texts = [], {}
    universe = APPLY.Universe(universe_names(bundles), renamer, compiler_named(bundles))
    excluded = {}
    if 'scripts/naming-inventory.json' in candidate['files']:
        raw = APPLY.safe_path(root, 'scripts/naming-inventory.json').read_bytes()
        if APPLY.digest(raw) != candidate['files']['scripts/naming-inventory.json']:
            raise ValueError('naming inventory changed during planning')
        inventory = json.loads(raw)
        if inventory.get('schema_version') != 1:
            raise ValueError('unsupported naming inventory')
        excluded = {row['path']: row for row in inventory['excluded_sources']}
    capture = dict(capture_checked=0, capture_unverifiable=0, capture_requalified=0,
                   capture_unverifiable_edited=0)
    for relative in sorted(candidate['files']):
        if not relative.endswith('.lean'):
            continue
        raw = APPLY.safe_path(root, relative).read_bytes()
        if APPLY.digest(raw) != candidate['files'][relative]:
            raise ValueError(f'{relative}: source changed during planning')
        text = raw.decode('utf-8')
        texts[relative] = text
        module = by_path.get(relative)
        bundle = bundles.get(module)
        exclusion = excluded.get(relative)
        if exclusion is not None:
            # A registered, digest-pinned exclusion is accounted for, not omitted.
            if exclusion['sha256'] != APPLY.digest(raw):
                problems = [dict(start=0, end=0, reason='registered naming exclusion digest differs; re-review it')]
            else:
                problems = []
            records.append(dict(path=relative, sha256=APPLY.digest(raw), module=module, indexed=False,
                                excluded=exclusion['status'], excluded_tokens=len(occurrences(text, affected)),
                                edits=[], unresolved=problems))
            continue
        if bundle is not None:
            if bundle['source'] != text or APPLY.module_name(bundle['index']['module']) != module:
                raise ValueError(f'{relative}: compiler bundle source/module mismatch')
            stats = {}
            edits, problems = APPLY.plan_file(text, bundle['index'], mapping['entries'], renamer,
                                              universe, stats)
            for key, value in stats.items():
                capture[key] += value
        else:
            edits = []
            problems = [dict(start=a, end=b, reason=f'affected token {word!r} has no compiler export')
                        for a, b, word in occurrences(text, affected)]
        records.append(dict(path=relative, sha256=APPLY.digest(raw), module=module,
                            indexed=bundle is not None, edits=edits, unresolved=problems))
    by_record = {row['path']: row for row in records}
    plan_sources.capture = capture
    moves = plan_modules(candidate, texts, by_record, renamer)
    plan_relocations(candidate, texts, by_record, bundles, mapping, renamer)
    for row in records:
        row['edits'].sort(key=lambda e: (e['start'], e['end']))
        for left, right in zip(row['edits'], row['edits'][1:]):
            if right['start'] < left['end']:
                row['unresolved'].append(dict(start=right['start'], end=left['end'],
                                              reason='overlapping rename and relocation edits'))
    return records, moves


def universe_names(bundles):
    """Every exported module's constants plus every constant any export references."""
    names = set()
    for bundle in bundles.values():
        names.update(bundle.get('names', []))
        for key in bundle['index']['references']:
            const = json.loads(key).get('c')
            if const:
                names.add(const['n'])
    return names


def compiler_named(bundles):
    """Declarations whose definition range spells a keyword, not their name."""
    result = set()
    for bundle in bundles.values():
        positions = APPLY.Positions(bundle['source'])
        for name, loc in bundle['index']['decls'].items():
            a, b = APPLY.span(positions, loc[4:] if len(loc) == 8 else loc)
            spans = APPLY.components(bundle['source'], a, b)
            private = MAP.split_private(name) if name.startswith('_private.') else None
            parts = APPLY.split_name(private[2] if private else name)
            if spans is None or parts[-len(spans):] != [bundle['source'][x:y] for x, y in spans]:
                result.add(name)
    return result


def source_dir(candidate, path):
    dirs = sorted(candidate['source_dirs'], key=lambda d: len(Path(d).parts), reverse=True)
    for directory in dirs:
        if Path(path).is_relative_to(Path(directory)):
            return Path(directory)
    raise ValueError(f'{path}: outside every source directory')


def plan_modules(candidate, texts, records, renamer):
    """Module rows: move the file, rewrite every compiler-confirmed import, and
    report the old module name anywhere else in code (lakefile roots, audit
    module prefixes, name literals)."""
    moves = []
    if not renamer.modules:
        return moves
    modules = candidate['modules']
    targets = set()
    for old, new in sorted(renamer.modules.items()):
        if old not in modules:
            raise ValueError(f'module row names an unknown module: {old}')
        path = modules[old]['path']
        target = (source_dir(candidate, path) / Path(*new.split('.'))).with_suffix('.lean').as_posix()
        if target in candidate['files'] or target in targets or new in modules:
            raise ValueError(f'module target already exists: {new}')
        targets.add(target)
        moves.append([path, target])
    pattern = re.compile('|'.join(r'(?<![\w.])' + re.escape(old) + r'(?![\w])'
                                  for old in sorted(renamer.modules, key=len, reverse=True)))
    for relative, text in texts.items():
        record = records[relative]
        spans = []
        module = record['module']
        if module is not None:
            for a, b, name in import_spans(text, modules[module]['imports']):
                spans.append((a, b))
                if name in renamer.modules:
                    record['edits'].append(dict(start=a, end=b, old=name, new=renamer.modules[name],
                                                declaration=f'module {name}'))
        code = code_only(text)
        for match in pattern.finditer(code):
            if not any(a <= match.start() and match.end() <= b for a, b in spans):
                record['unresolved'].append(dict(start=match.start(), end=match.end(),
                    reason=f'module name {match.group(0)!r} spelled outside an import '
                           '(lakefile root, audit module prefix or name literal): manual edit, then N4'))
    return moves


def render_open(row, renamer):
    kind = row[0]
    if kind == 'simple':
        ns, hidden = renamer.scope(row[1]), row[2]
        return f'open {ns}' + (' hiding ' + ' '.join(hidden) if hidden else '')
    alias, declaration = row[1], renamer(row[2])
    prefix, _, last = declaration.rpartition('.')
    if not prefix:
        raise ValueError(f'cannot render explicit open of root declaration {declaration}')
    return f'open {prefix} ({last})' if last == alias else f'open {prefix} renaming {last} → {alias}'


def plan_relocations(candidate, texts, records, bundles, mapping, renamer):
    """Move each relocated declaration's whole command to the end of its target
    module, in a section that restores its namespace and open declarations.

    Import obligations are reported, never invented: the target must already
    import what the command references, and each indexed module that still uses
    the declaration must import the target. Section variables, options and
    universes in scope, a target ending inside an open scope, private names
    still used in their old module, and commands declaring other names are
    unresolved: they need a manual edit before planning, then N4.
    """
    rows = [row for row in mapping['entries'] if row['kind'] == 'relocation']
    if not rows:
        return
    modules = candidate['modules']
    by_module = {row['module']: row for row in records.values() if row['module']}
    moving = {}
    for row in rows:
        source, target = row['from_module'], row['to_module']
        for module in (source, target):
            if module not in modules:
                raise ValueError(f'relocation names an unknown module: {module}')
        record = by_module[source]
        problem = lambda reason, a=0, b=0: record['unresolved'].append(
            dict(start=a, end=b, reason=f'relocation {row["old"]}: {reason}'))
        if source not in bundles or target not in bundles:
            problem('source and target modules need compiler exports')
            continue
        text, index = texts[record['path']], bundles[source]['index']
        meta = index.get('naming_syntax') or {}
        if meta.get('version') != 2:
            problem('export lacks version-2 command scopes')
            continue
        positions = APPLY.Positions(text)
        offsets = APPLY.byte_offsets(text)
        decls = {}
        for name, loc in index['decls'].items():
            user = MAP.split_private(name)
            decls.setdefault(user[2] if user else name, []).append((name, APPLY.span(positions, loc[:4])))
        found = decls.get(row['old'], [])
        if len(found) != 1:
            problem(f'{len(found)} declarations of this name in {source}')
            continue
        full, (a, b) = found[0]
        commands = [(APPLY.char_span(offsets, r[0], r[1], text), r) for r in meta['commands'] if r[0] < r[1]]
        containing = [(span, r) for span, r in commands if span[0] <= a and b <= span[1]]
        if len(containing) != 1:
            problem('declaration is not inside exactly one top-level command', a, b)
            continue
        (start, end), command = containing[0]
        moving.setdefault((source, start, end), dict(command=command, rows=[], target=target))
        entry = moving[(source, start, end)]
        entry['rows'].append(row)
        if entry['target'] != target:
            problem('one command relocated to two modules', start, end)
        entry['private'] = entry.get('private', []) + ([full] if full.startswith('_private.') else [])
    for (source, start, end), entry in sorted(moving.items()):
        record = by_module[source]
        target = entry['target']
        names = {row['old'] for row in entry['rows']}
        problem = lambda reason, a=start, b=end: record['unresolved'].append(
            dict(start=a, end=b, reason=f'relocation of {sorted(names)}: {reason}'))
        text, index = texts[record['path']], bundles[source]['index']
        positions = APPLY.Positions(text)
        command = entry['command']
        if any(command[5]):
            problem('command elaborates under section variables, options or universes in scope')
            continue
        others = []
        for name, loc in index['decls'].items():
            na, nb = APPLY.span(positions, loc[:4])
            user = MAP.split_private(name)
            user = user[2] if user else name
            if start <= na and nb <= end and not any(user == n or user.startswith(n + '.') for n in names):
                others.append(user)
        if others:
            problem(f'command also declares {sorted(others)}')
            continue
        target_record = by_module[target]
        eof = bundles[target]['index']['naming_syntax'].get('eof_scope')
        if not eof or eof[0] != 0:
            problem(f'target {target} ends inside an open namespace or section')
            continue
        # Imports: references made by the moved command.
        moved_decls = {name for name, loc in index['decls'].items()
                       if start <= APPLY.span(positions, loc[:4])[0] < end}
        needed, users, before = set(), {}, len(record['unresolved'])
        for key, info in index['references'].items():
            const = json.loads(key).get('c')
            if not const:
                continue
            for loc in info['usages'] + ([info['definition']] if info['definition'] else []):
                ra, rb = APPLY.span(positions, loc)
                if not (start <= ra and rb <= end):
                    continue
                if const['m'] != source:
                    needed.add(const['m'])
                elif const['n'] not in moved_decls:
                    needed.add(source)  # It still uses a declaration staying behind.
        target_closure = closure_of(modules, target) | {target}
        missing = sorted(m for m in needed if m in modules and m not in target_closure)
        if missing:
            problem(f'target {target} does not import {missing}, needed by the moved command')
        for module, bundle in bundles.items():
            if module == target:
                continue
            module_positions = positions if module == source else APPLY.Positions(bundle['source'])
            for key, info in bundle['index']['references'].items():
                const = json.loads(key).get('c')
                if not const or const['m'] != source or const['n'] not in moved_decls:
                    continue
                used = [loc for loc in info['usages']
                        if module != source or not (start <= APPLY.span(module_positions, loc)[0] < end)]
                if used:
                    users[module] = users.get(module, 0) + len(used)
        for module in sorted(users):
            if entry.get('private') and module == source:
                problem('private declaration is still used in its old module')
            elif target not in closure_of(modules, module) | {module}:
                problem(f'{module} still uses the moved declaration but does not import {target}')
        if len(record['unresolved']) != before:
            continue
        # Renames inside the moved command travel with its text.
        inner = [e for e in record['edits'] if start <= e['start'] and e['end'] <= end]
        record['edits'] = [e for e in record['edits'] if e not in inner]
        moved = text[start:end]
        for edit in sorted(inner, key=lambda e: e['start'], reverse=True):
            moved = moved[:edit['start'] - start] + edit['new'] + moved[edit['end'] - start:]
        cut = end + 1 if text.startswith('\n', end) else end
        record['edits'].append(dict(start=start, end=cut, old=text[start:cut], new='',
                                    declaration=f'relocation {sorted(names)} -> {target}'))
        ns = renamer.scope(command[3]) if command[3] != '[anonymous]' else ''
        lines = ['', 'section'] + [render_open(row, renamer) for row in command[4]]
        lines += ([f'namespace {ns}'] if ns else []) + [moved] + ([f'end {ns}'] if ns else []) + ['end', '']
        target_text = texts[target_record['path']]
        insertion = ('' if target_text.endswith('\n') else '\n') + '\n'.join(lines)
        target_record['edits'].append(dict(start=len(target_text), end=len(target_text), old='',
                                           new=insertion, declaration=f'relocation {sorted(names)} <- {source}'))


def build_plan(root, snapshot_path, map_path):
    snapshot_path = Path(snapshot_path).resolve(strict=True)
    mapping = read_map(map_path)
    snapshot = CANDIDATE.read_snapshot(snapshot_path, fidelity=False)
    snapshot.pop('export_paths')
    current_inventory(root, snapshot['candidate'])
    current_artifacts(snapshot)
    bundles = {}
    for module, row in snapshot['exports'].items():
        data = json.loads((snapshot_path.parent / row['path']).read_bytes())
        bundles[module] = {key: data[key] for key in ('source', 'index')}
        bundles[module]['names'] = sorted(data.get('constants', {}))
    records, moves = plan_sources(root, snapshot['candidate'], bundles, mapping)
    current_inventory(root, snapshot['candidate'])
    tools = {name: CANDIDATE.file_sha(ROOT / 'scripts' / name) for name in
             ('naming-tree.py', 'naming-candidate.py', 'apply-naming-map.py',
              'check-naming-map.py', 'check-naming-fidelity.py')}
    return dict(schema_version=1, scope='tracked-and-unignored-lean-sources',
                snapshot=str(snapshot_path), snapshot_sha256=CANDIDATE.file_sha(snapshot_path),
                map_sha256=CANDIDATE.file_sha(map_path), tool_sources=tools,
                inventory_sha256=APPLY.digest(CANDIDATE.FIDELITY.encoded(snapshot['candidate']).encode()),
                files=records, moves=moves, name_capture=plan_sources.capture,
                status='unresolved' if any(r['unresolved'] for r in records) else 'planned')


def apply_plan(root, plan, map_path):
    if (plan.get('schema_version') != 1 or plan.get('status') != 'planned' or
            plan.get('scope') != 'tracked-and-unignored-lean-sources'):
        raise ValueError('only a fully resolved whole-Lean-tree plan may be applied')
    if CANDIDATE.file_sha(map_path) != plan['map_sha256']:
        raise ValueError('rename map changed since planning')
    expected = build_plan(root, Path(plan['snapshot']), map_path)
    if expected != plan:
        raise ValueError('snapshot, tools or plan changed since planning')
    pending, moves = prepare_writes(root, plan['files'], plan.get('moves', []))
    snapshot_bytes = Path(plan['snapshot']).read_bytes()
    if APPLY.digest(snapshot_bytes) != plan['snapshot_sha256']:
        raise ValueError('snapshot changed after preflight')
    snapshot = json.loads(snapshot_bytes)
    current_inventory(root, snapshot['candidate'])
    # All files and inputs are checked before the first write. Filesystem I/O
    # failure can still interrupt writes, as with the selected-file editor.
    return write(pending, moves)


def prepare_writes(root, records, move_rows):
    pending = []
    for row in records:
        path = APPLY.safe_path(root, row['path'])
        text = path.read_bytes().decode('utf-8')
        for edit in reversed(row['edits']):
            if text[edit['start']:edit['end']] != edit['old']:
                raise ValueError('source changed after preflight')
            text = text[:edit['start']] + edit['new'] + text[edit['end']:]
        if row['edits']:
            pending.append((path, text.encode('utf-8')))
    moves = [(APPLY.safe_path(root, a), APPLY.safe_path(root, b)) for a, b in move_rows]
    for _, target in moves:
        if target.exists():
            raise ValueError(f'module move target exists: {target}')
    return pending, moves


def write(pending, moves):
    for path, raw in pending:
        path.write_bytes(raw)
    for source, target in moves:
        target.parent.mkdir(parents=True, exist_ok=True)
        source.rename(target)
    return len(pending) + len(moves)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    for command in ('needs', 'plan', 'apply'):
        p = commands.add_parser(command)
        p.add_argument('--tree', type=Path, required=True)
        p.add_argument('--map', type=Path, required=True)
        if command == 'needs':
            p.add_argument('--source-dir', action='append', required=True)
        elif command == 'plan':
            p.add_argument('--snapshot', type=Path, required=True)
        else:
            p.add_argument('--plan', type=Path, required=True)
    args = parser.parse_args()
    try:
        root = args.tree.resolve(strict=True)
        if args.command == 'needs':
            result = needs(root, args.source_dir, read_map(args.map))
        elif args.command == 'plan':
            result = build_plan(root, args.snapshot, args.map)
        else:
            result = dict(status='applied', files_changed=apply_plan(
                root, json.loads(args.plan.read_bytes()), args.map))
        print(json.dumps(result, indent=2, ensure_ascii=False))
        return 1 if result['status'] == 'unresolved' else 0
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(f'REFUSED — naming tree: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
