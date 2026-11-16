#!/usr/bin/env python3
"""Carry name-bearing pin rows across a tool-applied rename (goal 9.2 item 1).

    naming-pins.py --tree CHECKOUT --before-rev REV --plan PLAN.json --map MAP.json
                   [--write] FILE...

Allowlist rows of the form `[R<n>] <relpath> <normalised source line>[  ## note]`
(`integrity-allow.txt`, `rule-data-allow.txt`, `hygiene-allow.txt`) quote a
source line. Each quoted line is found in the file's text at REV (the tree the
whole-tree PLAN was made on) and replaced by the same line after the plan's
own edits, normalised as the gates do (trimmed, whitespace runs collapsed). A
row's note and every other byte stay. JSON manifests
(`assurance-manifest.json`) name declarations: each string that is a constant
the map renames becomes its new name. Nothing is added, dropped or loosened:
the row count is unchanged and only spellings the plan or map changed move.

With `--guard-msgs --snapshot CAPTURE/snapshot.json`, each Lean FILE's
`#guard_msgs` expected text (the doc comment right before it) is respelled
exactly as N4 compares it (`check-naming-fidelity.py`, `respell_message`, over
the before capture's constants): every whole qualified-name token, by the
names-only rule. Golden text moves only this way, in the packet commit.

Without `--write` the changes are only reported. Every change is listed with
its file, row, old and new text and the map rows behind the plan edits that
produced it. A quoted line found nowhere, or found more than once with
different renamed forms, is reported and left unchanged. Exit 0 when every
row was carried or needed no change, 1 when a row was reported, 2 on refusal.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location('check_naming_map', ROOT / 'scripts/check-naming-map.py')
MAP = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(MAP)

ROW = re.compile(r'^(?P<lead>\s*)(?P<rule>R\d+\s+)?(?P<path>[\w./-]+\.lean)\s+(?P<line>.*?)(?P<note>\s+##.*)?$')


def normalise(s):
    return ' '.join(s.split())


def renamed_lines(before, edits):
    """(normalised before line, normalised after line, declarations) per line."""
    out = []
    pos = 0
    for raw in before.split('\n'):
        start, end = pos, pos + len(raw)
        pos = end + 1
        inside = [e for e in edits if start <= e['start'] and e['end'] <= end]
        if any(e['start'] < end and start < e['end'] and e not in inside for e in edits):
            out.append((normalise(raw), None, ['edit crosses a line boundary']))
            continue
        text = raw
        for e in sorted(inside, key=lambda e: e['start'], reverse=True):
            text = text[:e['start'] - start] + e['new'] + text[e['end'] - start:]
        out.append((normalise(raw), normalise(text), sorted({e['declaration'] for e in inside})))
    return out


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--tree', type=Path, required=True)
    parser.add_argument('--before-rev', required=True)
    parser.add_argument('--plan', type=Path, required=True)
    parser.add_argument('--map', type=Path, required=True)
    parser.add_argument('--write', action='store_true')
    parser.add_argument('--guard-msgs', action='store_true')
    parser.add_argument('--snapshot', type=Path)
    parser.add_argument('files', nargs='+', type=Path)
    args = parser.parse_args(argv)
    try:
        plan = json.loads(args.plan.read_bytes())
        mapping = json.loads(args.map.read_bytes())
        MAP.validate_map(mapping)
        renamer = MAP.Renamer(mapping['entries'])
        edits = {row['path']: row['edits'] for row in plan['files']}
    except (OSError, ValueError, KeyError) as error:
        print(f'REFUSED — naming pins: {error}', file=sys.stderr)
        return 2
    cache = {}
    if args.guard_msgs:
        return guard_msgs(args, mapping, renamer)

    def lines_of(path):
        if path not in cache:
            try:
                before = subprocess.run(['git', '-C', str(args.tree), 'show', f'{args.before_rev}:{path}'],
                                        check=True, capture_output=True).stdout.decode('utf-8')
            except subprocess.CalledProcessError:
                cache[path] = None
            else:
                cache[path] = renamed_lines(before, edits.get(path, []))
        return cache[path]

    changes, reports = [], []
    for file in args.files:
        text = (args.tree / file).read_text(encoding='utf-8')
        if file.suffix == '.json':
            def walk(value):
                if isinstance(value, str) and renamer.renames(value):
                    changes.append(dict(file=str(file), old=value, new=renamer(value),
                                        rows=[value if value in renamer.exact else 'namespace']))
                    return renamer(value)
                if isinstance(value, list):
                    return [walk(v) for v in value]
                if isinstance(value, dict):
                    return {k: walk(v) for k, v in value.items()}
                return value
            data = json.loads(text)
            new_text = json.dumps(walk(data), indent=2, ensure_ascii=False) + '\n'
            if json.dumps(data, indent=2, ensure_ascii=False) + '\n' != text:
                reports.append(dict(file=str(file), reason='manifest is not in the canonical indent-2 form; '
                                                           'refusing to rewrite it'))
                new_text = text
        else:
            out = []
            for number, row in enumerate(text.split('\n'), 1):
                m = ROW.match(row)
                if not m or row.lstrip().startswith('#'):
                    out.append(row)
                    continue
                quoted = normalise(m.group('line'))
                found = [(a, d) for b, a, d in (lines_of(m.group('path')) or []) if b == quoted]
                if not found:
                    reports.append(dict(file=str(file), row=number, reason='quoted line not found at the '
                                        'before revision', text=row))
                    out.append(row)
                    continue
                results = {a for a, _ in found}
                if None in results or len(results) != 1:
                    reports.append(dict(file=str(file), row=number, reason='quoted line renames ambiguously',
                                        candidates=sorted(str(r) for r in results), text=row))
                    out.append(row)
                    continue
                after = results.pop()
                module = m.group('path')[:-len('.lean')].replace('/', '.')
                path = (renamer.module(module).replace('.', '/') + '.lean') if module in renamer.modules \
                    else m.group('path')
                if after == quoted and path == m.group('path'):
                    out.append(row)
                    continue
                declarations = sorted({d for _, ds in found for d in ds} |
                                      ({f'module {module}'} if path != m.group('path') else set()))
                new_row = (m.group('lead') + (m.group('rule') or '') + path + ' ' + after +
                           (m.group('note') or ''))
                changes.append(dict(file=str(file), row=number, old=row, new=new_row, rows=declarations))
                out.append(new_row)
            new_text = '\n'.join(out)
        if args.write and new_text != text:
            (args.tree / file).write_text(new_text, encoding='utf-8')
    print(json.dumps(dict(write=args.write, changes=changes, reports=reports), indent=1, ensure_ascii=False))
    print(f'{"OK" if not reports else "REPORTED"} — naming pins: {len(changes)} row(s) carried, '
          f'{len(reports)} reported', file=sys.stderr)
    return 0 if not reports else 1


def guard_msgs(args, mapping, renamer):
    spec = importlib.util.spec_from_file_location('check_naming_fidelity', ROOT / 'scripts/check-naming-fidelity.py')
    fidelity = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(fidelity)
    base = args.snapshot.parent
    snapshot = json.loads(args.snapshot.read_bytes())
    constants = {}
    for row in snapshot['exports'].values():
        constants.update(json.loads((base / row['path']).read_bytes()).get('constants', {}))
    before = dict(constants=constants, roots=set(constants))
    renamed = {renamer(name): value for name, value in constants.items()}
    after = dict(constants=renamed, roots=set(renamed))
    comparison = fidelity.Comparison(before, after, renamer)
    golden = re.compile(r'(/--\n)(.*?)(-/\s*\n#guard_msgs\b)', re.S)
    changes = []
    for file in args.files:
        text = (args.tree / file).read_text(encoding='utf-8')
        def one(m):
            new = comparison.respell_message(m.group(2) + '-/', 'guard_msgs')[:-2]
            if new != m.group(2):
                changes.append(dict(file=str(file), line=text.count('\n', 0, m.start(2)) + 1,
                                    old=m.group(2), new=new))
            return m.group(1) + new + m.group(3)
        new_text = golden.sub(one, text)
        if args.write and new_text != text:
            (args.tree / file).write_text(new_text, encoding='utf-8')
    print(json.dumps(dict(write=args.write, guard_msgs=changes), indent=1, ensure_ascii=False))
    print(f'OK — naming pins: {len(changes)} #guard_msgs text(s) respelled', file=sys.stderr)
    return 0


if __name__ == '__main__':
    sys.exit(main())
