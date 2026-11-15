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
import sys
import subprocess

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location('naming_candidate', ROOT / 'scripts/naming-candidate.py')
CANDIDATE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CANDIDATE)
APPLY = CANDIDATE.FIDELITY.APPLY


def read_map(path):
    data = json.loads(Path(path).read_bytes())
    CANDIDATE.FIDELITY.MAP.validate_map(data)
    return data


def words(entries):
    return {part for row in entries for i, part in enumerate(row['old'].split('.'))
            if i >= len(row['new'].split('.')) or part != row['new'].split('.')[i]}


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
    affected = words(mapping['entries'])
    records = []
    for relative in sorted(candidate['files']):
        if not relative.endswith('.lean'):
            continue
        raw = APPLY.safe_path(root, relative).read_bytes()
        if APPLY.digest(raw) != candidate['files'][relative]:
            raise ValueError(f'{relative}: source changed during planning')
        text = raw.decode('utf-8')
        module = by_path.get(relative)
        bundle = bundles.get(module)
        if bundle is not None:
            if bundle['source'] != text or bundle['index']['module'] != module:
                raise ValueError(f'{relative}: compiler bundle source/module mismatch')
            edits, problems = APPLY.plan_file(text, bundle['index'], mapping['entries'])
        else:
            edits = []
            problems = [dict(start=a, end=b, reason=f'affected token {word!r} has no compiler export')
                        for a, b, word in occurrences(text, affected)]
        records.append(dict(path=relative, sha256=APPLY.digest(raw), module=module,
                            indexed=bundle is not None, edits=edits, unresolved=problems))
    unsupported = [dict(old=row['old'], new=row['new'],
                        reason='module/relocation rows need explicit relocation support')
                   for row in mapping['entries'] if row['kind'] in ('module', 'relocation')]
    return records, unsupported


def build_plan(root, snapshot_path, map_path):
    snapshot_path = Path(snapshot_path).resolve(strict=True)
    mapping = read_map(map_path)
    snapshot = CANDIDATE.read_snapshot(snapshot_path)
    snapshot.pop('fidelity')  # The apply plan needs references, not retained kernel graphs.
    current_inventory(root, snapshot['candidate'])
    current_artifacts(snapshot)
    bundles = {}
    for module, row in snapshot['exports'].items():
        data = json.loads((snapshot_path.parent / row['path']).read_bytes())
        bundles[module] = {key: data[key] for key in ('source', 'index')}
    records, unsupported = plan_sources(root, snapshot['candidate'], bundles, mapping)
    current_inventory(root, snapshot['candidate'])
    tools = {name: CANDIDATE.file_sha(ROOT / 'scripts' / name) for name in
             ('naming-tree.py', 'naming-candidate.py', 'apply-naming-map.py',
              'check-naming-map.py', 'check-naming-fidelity.py')}
    return dict(schema_version=1, scope='tracked-and-unignored-lean-sources',
                snapshot=str(snapshot_path), snapshot_sha256=CANDIDATE.file_sha(snapshot_path),
                map_sha256=CANDIDATE.file_sha(map_path), tool_sources=tools,
                inventory_sha256=APPLY.digest(CANDIDATE.FIDELITY.encoded(snapshot['candidate']).encode()),
                files=records, unsupported=unsupported,
                status='unresolved' if unsupported or any(r['unresolved'] for r in records) else 'planned')


def apply_plan(root, plan, map_path):
    if (plan.get('schema_version') != 1 or plan.get('status') != 'planned' or
            plan.get('scope') != 'tracked-and-unignored-lean-sources'):
        raise ValueError('only a fully resolved whole-Lean-tree plan may be applied')
    if CANDIDATE.file_sha(map_path) != plan['map_sha256']:
        raise ValueError('rename map changed since planning')
    expected = build_plan(root, Path(plan['snapshot']), map_path)
    if expected != plan:
        raise ValueError('snapshot, tools or plan changed since planning')
    pending = []
    for row in plan['files']:
        path = APPLY.safe_path(root, row['path'])
        text = path.read_bytes().decode('utf-8')
        for edit in reversed(row['edits']):
            if text[edit['start']:edit['end']] != edit['old']:
                raise ValueError('source changed after preflight')
            text = text[:edit['start']] + edit['new'] + text[edit['end']:]
        if row['edits']:
            pending.append((path, text.encode('utf-8')))
    snapshot_bytes = Path(plan['snapshot']).read_bytes()
    if APPLY.digest(snapshot_bytes) != plan['snapshot_sha256']:
        raise ValueError('snapshot changed after preflight')
    snapshot = json.loads(snapshot_bytes)
    current_inventory(root, snapshot['candidate'])
    # All files and inputs are checked before the first write. Filesystem I/O
    # failure can still interrupt writes, as with the selected-file editor.
    for path, raw in pending:
        path.write_bytes(raw)
    return len(pending)


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
