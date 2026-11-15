#!/usr/bin/env python3
"""Capture and compare source-bound local dependency closures for naming fidelity.

Capture requires an explicit owned build command prefix and explicit host
admission/release commands. It never invents a build/admission policy. All argv
values are JSON arrays, executed without a shell. Output must be outside the
checkout. Comparison is read-only and does not require Lean or host admission.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

# Reuse the checked map, compiler comparator.
import importlib.util
ROOT = Path(__file__).resolve().parent.parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


FIDELITY = load('check-naming-fidelity.py')
PARTS = ('olean', 'olean.server', 'olean.private', 'ir.sig', 'ir')
CONFIG = ('lean-toolchain', 'lake-manifest.json', 'lakefile.lean', 'lakefile.toml')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def file_sha(path):
    with Path(path).open('rb') as source:
        return hashlib.file_digest(source, 'sha256').hexdigest()


def save(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')


def argv(value):
    parsed = json.loads(value)
    if not isinstance(parsed, list) or not parsed or not all(isinstance(s, str) and s for s in parsed):
        raise ValueError('command must be a nonempty JSON array of nonempty strings')
    return parsed


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])


def inventory(root, source_dirs):
    paths = git(root, 'ls-files', '-z', '--cached', '--others', '--exclude-standard').decode().split('\0')
    files, modules = {}, {}
    dirs = sorted(set(source_dirs), key=lambda p: len(Path(p).parts), reverse=True)
    for relative in sorted(set(paths) - {''}):
        path = root / relative
        if path.is_symlink() or not path.is_file() or not path.resolve().is_relative_to(root):
            raise ValueError(f'candidate contains missing, non-file or symlink input: {relative}')
        files[relative] = file_sha(path)
        if not relative.endswith('.lean') or relative == 'lakefile.lean':
            continue
        for directory in dirs:
            prefix = Path(directory)
            if Path(relative).is_relative_to(prefix):
                module = '.'.join(Path(relative).relative_to(prefix).with_suffix('').parts)
                if not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_-]*(\.[A-Za-z_][A-Za-z0-9_-]*)*', module):
                    raise ValueError(f'unsupported module spelling: {relative}')
                if module in modules:
                    raise ValueError(f'module source collision: {module}')
                modules[module] = dict(path=relative, sha256=files[relative])
                break
    if not modules:
        raise ValueError('no candidate modules')
    unmapped = {p for p in files if p.endswith('.lean') and p != 'lakefile.lean'} - {
        row['path'] for row in modules.values()}
    if unmapped:
        raise ValueError(f'Lean sources outside the module inventory: {sorted(unmapped)}')
    return dict(head=git(root, 'rev-parse', 'HEAD').decode().strip(), files=files, modules=modules,
                source_dirs=sorted(set(source_dirs)))


def bind_headers(source, headers):
    if headers['schema_version'] != 1 or headers['modules'].keys() != source['modules'].keys():
        raise ValueError('compiler header inventory does not cover all candidate modules')
    result = {**source, 'modules': {}}
    for module, row in source['modules'].items():
        header = headers['modules'][module]
        if header['path'] != row['path']:
            raise ValueError(f'compiler header source path differs: {module}')
        result['modules'][module] = {**row, 'imports': [entry[0] for entry in header['direct_imports']],
                                     'is_module': header['is_module']}
    return result


def closure(modules, roots):
    seen, active, order = set(), set(), []
    def visit(module):
        if module in active:
            raise ValueError(f'local import cycle at {module}')
        if module in seen:
            return
        if module not in modules:
            raise ValueError(f'unknown local root: {module}')
        active.add(module)
        for dependency in modules[module]['imports']:
            if dependency in modules:
                visit(dependency)
        active.remove(module)
        seen.add(module)
        order.append(module)
    for root in roots:
        visit(root)
    return order


def artifact_parts(olean):
    return {part: str(Path(olean).with_suffix('.' + part).absolute())
            if Path(olean).with_suffix('.' + part).is_file() else None for part in PARTS}


def bind_artifacts(imports):
    result = {}
    for module, parts in imports.items():
        if set(parts) != set(PARTS) or parts['olean'] is None:
            raise ValueError(f'incomplete artifact inventory: {module}')
        if artifact_parts(parts['olean']) != parts:
            raise ValueError(f'artifact part appeared, disappeared or changed path: {module}')
        result[module] = {}
        for part, path in parts.items():
            result[module][part] = dict(path=path, sha256=file_sha(path)) if path else None
    return result


def artifact_identity(parts):
    return {part: record['sha256'] if record else None for part, record in parts.items()}


def run(root, out, label, command):
    proc = subprocess.run(command, cwd=root, capture_output=True)
    (out / (label + '.log')).write_bytes(proc.stdout + proc.stderr)
    receipt = dict(argv=command, cwd=str(root), exit=proc.returncode,
                   log_sha256=sha(proc.stdout + proc.stderr))
    save(out / (label + '.command.json'), receipt)
    if proc.returncode:
        raise ValueError(f'{label} exited {proc.returncode}; see {out / (label + ".log")}')
    return receipt


def capture(args):
    root, out = args.root.resolve(), args.output.resolve()
    if out.is_relative_to(root):
        raise ValueError('capture output must be outside the candidate checkout')
    source_dirs = [str(Path(p)) for p in args.source_dir]
    for directory in source_dirs:
        if Path(directory).is_absolute() or '..' in Path(directory).parts:
            raise ValueError('source directories must stay within the candidate')
    source_before = inventory(root, source_dirs)
    out.mkdir(parents=True, exist_ok=False)
    save(out / 'source-before.json', source_before)
    # Use Lean's parser for the entire graph, not a line scanner: an omitted
    # import in an unexported, unchanged client would defeat reverse closure.
    tool_build = run(root, out, 'tool-build', argv(args.build_prefix) + ['jaune-naming-fidelity'])
    exporter = root / '.lake/build/bin/jaune-naming-fidelity'
    exporter_hash = file_sha(exporter)
    header_input = out / 'header-input.json'
    header_output = out / 'headers.json'
    save(header_input, [[module, row['path']] for module, row in source_before['modules'].items()])
    run(root, out, 'header-admit', argv(args.admit_command))
    try:
        run(root, out, 'headers', ['lake', 'env', str(exporter), '--headers', str(header_input), str(header_output)])
    finally:
        run(root, out, 'header-release', argv(args.release_command))
    initial = bind_headers(source_before, json.loads(header_output.read_bytes()))
    if inventory(root, source_dirs) != source_before:
        raise ValueError('candidate changed during header discovery')
    selected = closure(initial['modules'], args.module)
    if any(initial['modules'][m]['is_module'] for m in selected):
        raise ValueError('module-system visibility is not yet supported by fidelity exports')
    build = run(root, out, 'build', argv(args.build_prefix) + selected)
    if inventory(root, source_dirs) != source_before or file_sha(exporter) != exporter_hash:
        raise ValueError('candidate or exporter changed during build')
    # Bind local producer artifacts immediately after the successful owned
    # build, before loading an environment or starting an exporter.
    local_paths = {m: artifact_parts(root / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean'))
                   for m in selected}
    local_built = bind_artifacts(local_paths)
    tool_sources = {p: initial['files'].get(p) for p in
                    ('scripts/NamingFidelity.lean', 'scripts/check-naming-fidelity.py',
                     'scripts/naming-candidate.py', 'scripts/check-naming-map.py',
                     'scripts/apply-naming-map.py')}
    run(root, out, 'admit', argv(args.admit_command))
    try:
        imports, discovery, exports = {}, {}, {}
        for module in selected:
            path = initial['modules'][module]['path']
            target = out / (module + '.imports.json')
            run(root, out, module + '-imports', ['lake', 'env', str(exporter), '--imports', path, module, str(target)])
            data = json.loads(target.read_bytes())
            direct = [entry[0] for entry in data['direct_imports']]
            if data['module'] != module or direct != initial['modules'][module]['imports']:
                raise ValueError(f'compiler/source import disagreement: {module}')
            discovery[module] = data
            for name, parts in data['imports'].items():
                if name in imports and imports[name] != parts:
                    raise ValueError(f'inconsistent import resolution: {name}')
                if name in initial['modules']:
                    if name not in selected or parts != local_paths[name]:
                        raise ValueError(f'local import escaped the built source closure: {name}')
                elif parts['olean'] and Path(parts['olean']).absolute().is_relative_to(root / '.lake/build'):
                    raise ValueError(f'uninventoried local import: {name}')
                imports[name] = parts
        bound = bind_artifacts(imports)
        for name in selected:
            if name in bound and bound[name] != local_built[name]:
                raise ValueError(f'local artifact changed after build: {name}')
        for module in selected:
            path = initial['modules'][module]['path']
            target = out / (module + '.export.json')
            run(root, out, module + '-export', ['lake', 'env', str(exporter), path, module, str(target)])
            data = json.loads(target.read_bytes())
            if (data['schema_version'] != 5 or data['imports'] != discovery[module]['imports'] or
                data['index']['module'] != module or
                data['index']['directImports'] != discovery[module]['direct_imports'] or
                data['lean_version'] != discovery[module]['lean_version'] or
                sha(data['source'].encode()) != initial['modules'][module]['sha256']):
                raise ValueError(f'export is not bound to the discovered candidate: {module}')
            exports[module] = dict(path=target.name, sha256=file_sha(target))
        if bind_artifacts(imports) != bound or bind_artifacts(local_paths) != local_built:
            raise ValueError('import artifacts changed during export')
        if inventory(root, source_dirs) != source_before or file_sha(exporter) != exporter_hash:
            raise ValueError('candidate or exporter changed during export')
        result = dict(schema_version=2, status='OK', scope='local-import-closure',
                      candidate=initial, roots=args.module, selected=selected, build=build, tool_build=tool_build,
                      headers_sha256=file_sha(header_output),
                      exporter_sha256=exporter_hash, tool_sources=tool_sources,
                      artifacts=bound, local_built=local_built, exports=exports)
        # Validate the assembled bundle before advertising success.
        FIDELITY.read_exports([out / record['path'] for record in exports.values()])
    finally:
        run(root, out, 'release', argv(args.release_command))
    save(out / 'snapshot.json', result)
    return dict(status='OK', snapshot=str(out / 'snapshot.json'), modules=len(selected))


def read_snapshot(path):
    path = Path(path)
    data = json.loads(path.read_bytes())
    if data['schema_version'] != 2 or data['status'] != 'OK' or data['build']['exit'] != 0:
        raise ValueError('not a successful candidate capture')
    candidate = data['candidate']
    header_path = path.parent / 'headers.json'
    if file_sha(header_path) != data['headers_sha256']:
        raise ValueError('compiler header inventory digest changed')
    source = json.loads((path.parent / 'source-before.json').read_bytes())
    if bind_headers(source, json.loads(header_path.read_bytes())) != candidate:
        raise ValueError('candidate graph differs from compiler header inventory')
    selected = closure(candidate['modules'], data['roots'])
    if selected != data['selected'] or set(selected) != data['exports'].keys():
        raise ValueError('incomplete candidate export closure')
    exports = []
    for module, row in candidate['modules'].items():
        if candidate['files'].get(row['path']) != row['sha256']:
            raise ValueError('module source digest differs from candidate file inventory')
    inventoried = {row['path'] for row in candidate['modules'].values()}
    if {p for p in candidate['files'] if p.endswith('.lean') and p != 'lakefile.lean'} - inventoried:
        raise ValueError('candidate omits Lean sources from its module inventory')
    for module, record in data['exports'].items():
        export = path.parent / record['path']
        if not export.resolve().is_relative_to(path.parent.resolve()) or file_sha(export) != record['sha256']:
            raise ValueError('export missing, outside snapshot, or digest changed')
        raw = json.loads(export.read_bytes())
        if (raw['schema_version'] not in (4, 5) or raw['index']['module'] != module or
            sha(raw['source'].encode()) != candidate['modules'][module]['sha256'] or
            [entry[0] for entry in raw['index']['directImports']] != candidate['modules'][module]['imports']):
            raise ValueError('export source does not match candidate inventory')
        for name, parts in raw['imports'].items():
            bound = data['artifacts'][name]
            if parts != {part: item['path'] if item else None for part, item in bound.items()}:
                raise ValueError('export import binding differs from snapshot')
            if name in candidate['modules']:
                if name not in selected or bound != data['local_built'][name]:
                    raise ValueError('import is outside built local closure')
        exports.append(export)
    data['fidelity'] = FIDELITY.read_exports(exports)
    if any(candidate['modules'][m]['is_module'] for m in selected):
        raise ValueError('module-system visibility is not yet supported by fidelity exports')
    if data['fidelity']['version'] != json.loads(header_path.read_bytes())['lean_version']:
        raise ValueError('compiler header and export Lean versions differ')
    return data


def affected_modules(before, after):
    changed = {m for m in before.keys() | after.keys()
               if before.get(m) != after.get(m)}
    affected = set(changed)
    while True:
        more = {m for graph in (before, after) for m, row in graph.items()
                if set(row['imports']) & affected}
        if more <= affected:
            return affected
        affected |= more


def compare(before, after, mapping):
    left, right = before['candidate'], after['candidate']
    if left['source_dirs'] != right['source_dirs']:
        raise ValueError('module source layout changed; explicit relocation support is required')
    for config in CONFIG:
        if left['files'].get(config) != right['files'].get(config):
            raise ValueError(f'build/dependency configuration changed: {config}')
    if before['tool_sources'] != after['tool_sources']:
        raise ValueError('capture/comparison implementation changed between candidates')
    covered = {row['path'] for data in (before, after) for m, row in data['candidate']['modules'].items()
               if m in data['selected']}
    changed_lean = {p for p in left['files'].keys() | right['files'].keys()
                    if p.endswith('.lean') and left['files'].get(p) != right['files'].get(p)}
    if changed_lean - covered:
        raise ValueError(f'changed Lean sources outside exports: {sorted(changed_lean - covered)}')
    affected = affected_modules(left['modules'], right['modules'])
    for side in (before, after):
        missing = (affected & side['candidate']['modules'].keys()) - set(side['selected'])
        if missing:
            raise ValueError(f'affected importers outside exports: {sorted(missing)}')
    boundaries = []
    for side in (before, after):
        boundaries.append({name: artifact_identity(parts) for name, parts in side['artifacts'].items()
                           if name not in side['candidate']['modules']})
    if boundaries[0] != boundaries[1]:
        raise ValueError('external import artifact boundary changed')
    result = FIDELITY.check(before['fidelity'], after['fidelity'], mapping)
    result.update(scope='candidate-affected-local-closure',
                  before_candidate=left['head'], after_candidate=right['head'],
                  before_inventory_sha256=sha(FIDELITY.encoded(left).encode()),
                  after_inventory_sha256=sha(FIDELITY.encoded(right).encode()),
                  affected_modules=sorted(affected))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest='command', required=True)
    cap = commands.add_parser('capture')
    cap.add_argument('--root', type=Path, required=True)
    cap.add_argument('--source-dir', action='append', required=True)
    cap.add_argument('--module', action='append', required=True)
    cap.add_argument('--build-prefix', required=True)
    cap.add_argument('--admit-command', required=True)
    cap.add_argument('--release-command', required=True)
    cap.add_argument('--output', type=Path, required=True)
    comp = commands.add_parser('compare')
    comp.add_argument('--before', type=Path, required=True)
    comp.add_argument('--after', type=Path, required=True)
    comp.add_argument('--map', type=Path, required=True)
    args = parser.parse_args()
    try:
        if args.command == 'capture':
            result = capture(args)
        else:
            result = compare(read_snapshot(args.before), read_snapshot(args.after), json.loads(args.map.read_bytes()))
            result['map_sha256'] = file_sha(args.map)
        print(json.dumps(result, indent=2))
        return 0
    except FIDELITY.Mismatch as error:
        print(f'REGRESSION — naming candidate: {error}', file=sys.stderr)
        return 1
    except (OSError, ValueError, KeyError, TypeError, subprocess.SubprocessError) as error:
        print(f'SETUP — naming candidate: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
