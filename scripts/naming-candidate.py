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


def build_modules(modules, roots, source_only):
    """Only explicit, globally unimported roots may omit a producer artifact."""
    leaves = set(source_only)
    if not leaves <= set(roots):
        raise ValueError('source-only modules must be explicit capture roots')
    imported = {name for row in modules.values() for name in row['imports']}
    if leaves & imported:
        raise ValueError(f'source-only root is imported by a local source: {sorted(leaves & imported)}')
    return [m for m in closure(modules, roots) if m not in leaves]


def environments(modules, selected):
    """Maximal source environments, each with its own local import closure."""
    selected = set(selected)
    imported = {name for m in selected for name in modules[m]['imports']}
    return {root: closure(modules, [root]) for root in sorted(selected - imported)}


def read_bundles(paths):
    return {m: FIDELITY.read_exports([path]) for m, path in paths.items()}


def read_environments(paths, modules, selected, bundles=None):
    # Parse each module once. Merged environments share the kernel objects of
    # common dependencies, rather than duplicating those graphs per executable.
    bundles = bundles if bundles is not None else read_bundles(paths)
    result = {}
    for root, members in environments(modules, selected).items():
        merged = dict(constants={}, roots=set(), guards=[], attributes=[],
                      modules={}, receipts=[], checks=[], version=None, coalesced_equations=[], owners={})
        for member in members:
            data = bundles[member]
            if merged['version'] is not None and merged['version'] != data['version']:
                raise ValueError('mixed Lean versions in capture environment')
            merged['version'] = data['version']
            try:
                overlap = FIDELITY.merge_constants(merged['constants'], merged['roots'],
                                                   data['constants'], data['roots'])
            except ValueError as error:
                raise ValueError(f'{root}: duplicate constants in one import environment: {error}') from error
            merged['coalesced_equations'] = sorted(set(merged['coalesced_equations']) | overlap)
            merged['roots'].update(data['roots'])
            merged['modules'].update(data['modules'])
            for name, owner in data.get('owners', {}).items():
                merged['owners'].setdefault(name, owner)
            for field in ('guards', 'attributes', 'receipts', 'checks'):
                merged[field].extend(data[field])
        result[root] = merged
    if not result:
        raise ValueError('no captured source environments')
    return result


def union_environment(bundles):
    """All exported modules as one comparison scope, for relocations that move
    declarations or checks between independent roots. A name defined in two
    independent modules (each executable's `main`) is keyed per module."""
    from collections import Counter
    counts = Counter(name for data in bundles.values() for name in data['constants'])
    merged = dict(constants={}, roots=set(), guards=[], attributes=[], modules={}, receipts=[],
                  checks=[], version=None, coalesced_equations=[], owners={})
    for module, data in sorted(bundles.items()):
        if merged['version'] is not None and merged['version'] != data['version']:
            raise ValueError('mixed Lean versions in capture')
        merged['version'] = data['version']
        for name, constant in data['constants'].items():
            key = name
            if counts[name] > 1:
                existing = merged['constants'].get(name)
                if not (existing is not None and constant.get('equation_origin') is not None and
                        existing == constant and name not in data['roots']):
                    key = f'{name}@{module}'
            if key == name and name in merged['constants']:
                merged['coalesced_equations'].append(name)
            merged['constants'][key] = constant
            merged['owners'].setdefault(key, module)
            if name in data['roots']:
                merged['roots'].add(key)
        merged['modules'].update(data['modules'])
        for field in ('guards', 'attributes', 'receipts', 'checks'):
            merged[field].extend(data[field])
    for key in [k for k in merged['constants'] if '@' in k]:
        if key.rsplit('@', 1)[0] in merged['constants']:
            raise ValueError(f'colliding name also defined once without collision: {key}')
    return merged


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


def reuse_or_run(reuse, root, out, label, command, target):
    """Resume after a later failure: copy a prior capture's output and receipt
    for the identical command instead of rerunning it. Every binding check of
    this capture still runs on the copied files."""
    if reuse is not None:
        prior = Path(reuse)
        receipt = prior / (label + '.command.json')
        if receipt.is_file() and (prior / target.name).is_file():
            data = json.loads(receipt.read_bytes())
            argv = data.get('argv') or []
            if (argv[:-1] == command[:-1] and Path(argv[-1]).name == Path(command[-1]).name and
                    data.get('exit') == 0):
                import shutil
                shutil.copyfile(prior / target.name, target)
                shutil.copyfile(prior / (label + '.log'), out / (label + '.log'))
                save(out / (label + '.command.json'), dict(data, reused_from=str(prior)))
                return dict(data, reused_from=str(prior))
    return run(root, out, label, command)


def parallel(jobs, calls):
    """Run independent exporter commands, at most `jobs` at once; every receipt
    is kept and the first failure (in input order) is raised after all finish."""
    from concurrent.futures import ThreadPoolExecutor
    def attempt(call):
        try:
            if len(call) == 6:
                return reuse_or_run(*call), None
            return run(*call), None
        except ValueError as error:
            return None, error
    with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        results = list(pool.map(attempt, calls))
    for _, error in results:
        if error is not None:
            raise error
    return [receipt for receipt, _ in results]


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
    if args.reuse is not None:
        prior = json.loads((Path(args.reuse) / 'source-before.json').read_bytes())
        def lean_inputs(files):  # Exports depend on Lean sources and configuration only.
            return {p: h for p, h in files.items() if p.endswith('.lean') or p in CONFIG}
        if lean_inputs(prior['files']) != lean_inputs(source_before['files']):
            raise ValueError('reuse refused: the prior capture saw different Lean sources or configuration')
    if inventory(root, source_dirs) != source_before:
        raise ValueError('candidate changed during header discovery')
    selected = closure(initial['modules'], args.module)
    if any(initial['modules'][m]['is_module'] for m in selected):
        raise ValueError('module-system visibility is not yet supported by fidelity exports')
    source_only = sorted(set(args.source_only))
    producers = build_modules(initial['modules'], args.module, source_only)
    if producers:
        build = run(root, out, 'build', argv(args.build_prefix) + producers)
    else:
        # An empty target list would accidentally build the package defaults.
        build = dict(exit=0, argv=[], skipped='no local producer modules')
        save(out / 'build.command.json', build)
    if inventory(root, source_dirs) != source_before or file_sha(exporter) != exporter_hash:
        raise ValueError('candidate or exporter changed during build')
    # Bind local producer artifacts immediately after the successful owned
    # build, before loading an environment or starting an exporter.
    local_paths = {m: artifact_parts(root / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean'))
                   for m in producers}
    local_built = bind_artifacts(local_paths)
    tool_sources = {p: initial['files'].get(p) for p in
                    ('scripts/NamingFidelity.lean', 'scripts/NamingReferencesCore.lean',
                     'scripts/check-naming-fidelity.py',
                     'scripts/naming-candidate.py', 'scripts/check-naming-map.py',
                     'scripts/apply-naming-map.py')}
    run(root, out, 'admit', argv(args.admit_command))
    try:
        imports, discovery, exports = {}, {}, {}
        # Independent elaborations; the caller's admission covers `--jobs` of them.
        parallel(args.jobs, [(args.reuse, root, out, module + '-imports',
                              ['lake', 'env', str(exporter), '--imports', initial['modules'][module]['path'],
                               module, str(out / (module + '.imports.json'))], out / (module + '.imports.json'))
                             for module in selected])
        for module in selected:
            target = out / (module + '.imports.json')
            data = json.loads(target.read_bytes())
            direct = [entry[0] for entry in data['direct_imports']]
            if data['module'] != module or direct != initial['modules'][module]['imports']:
                raise ValueError(f'compiler/source import disagreement: {module}')
            discovery[module] = data
            for name, parts in data['imports'].items():
                if name in imports and imports[name] != parts:
                    raise ValueError(f'inconsistent import resolution: {name}')
                if name in initial['modules']:
                    if name not in local_paths or parts != local_paths[name]:
                        raise ValueError(f'local import escaped the built source closure: {name}')
                elif parts['olean'] and Path(parts['olean']).absolute().is_relative_to(root / '.lake/build'):
                    raise ValueError(f'uninventoried local import: {name}')
                imports[name] = parts
        bound = bind_artifacts(imports)
        for name in producers:
            if name in bound and bound[name] != local_built[name]:
                raise ValueError(f'local artifact changed after build: {name}')
        parallel(args.jobs, [(args.reuse, root, out, module + '-export',
                              ['lake', 'env', str(exporter), initial['modules'][module]['path'], module,
                               str(out / (module + '.export.json'))], out / (module + '.export.json'))
                             for module in selected])
        for module in selected:
            target = out / (module + '.export.json')
            data = json.loads(target.read_bytes())
            if (data['schema_version'] != 6 or data['imports'] != discovery[module]['imports'] or
                FIDELITY.APPLY.module_name(data['index']['module']) != module or
                data['index']['directImports'] != discovery[module]['direct_imports'] or
                data['lean_version'] != discovery[module]['lean_version'] or
                sha(data['source'].encode()) != initial['modules'][module]['sha256']):
                raise ValueError(f'export is not bound to the discovered candidate: {module}')
            exports[module] = dict(path=target.name, sha256=file_sha(target))
        if bind_artifacts(imports) != bound or bind_artifacts(local_paths) != local_built:
            raise ValueError('import artifacts changed during export')
        if inventory(root, source_dirs) != source_before or file_sha(exporter) != exporter_hash:
            raise ValueError('candidate or exporter changed during export')
        result = dict(schema_version=3, status='OK', scope='local-import-closure', jobs=args.jobs,
                      candidate=initial, roots=args.module, selected=selected, build=build, tool_build=tool_build,
                      source_only=source_only, producers=producers,
                      headers_sha256=file_sha(header_output),
                      exporter_sha256=exporter_hash, tool_sources=tool_sources,
                      artifacts=bound, local_built=local_built, exports=exports)
        # Validate the assembled bundle before advertising success.
        read_environments({m: out / row['path'] for m, row in exports.items()},
                          initial['modules'], selected)
    finally:
        run(root, out, 'release', argv(args.release_command))
    save(out / 'snapshot.json', result)
    return dict(status='OK', snapshot=str(out / 'snapshot.json'), modules=len(selected))


def read_snapshot(path, fidelity=True):
    path = Path(path)
    data = json.loads(path.read_bytes())
    if data['schema_version'] not in (2, 3) or data['status'] != 'OK' or data['build']['exit'] != 0:
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
    if data['schema_version'] == 2 and data.get('source_only'):
        raise ValueError('schema 2 does not support source-only roots')
    source_only = data['source_only'] if data['schema_version'] == 3 else []
    producers = build_modules(candidate['modules'], data['roots'], source_only)
    if data['schema_version'] == 3 and (producers != data['producers'] or
                                       set(producers) != data['local_built'].keys()):
        raise ValueError('producer artifact inventory differs from required build closure')
    exports = {}
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
        if (raw['schema_version'] not in (4, 5, 6) or FIDELITY.APPLY.module_name(raw['index']['module']) != module or
            sha(raw['source'].encode()) != candidate['modules'][module]['sha256'] or
            [entry[0] for entry in raw['index']['directImports']] != candidate['modules'][module]['imports']):
            raise ValueError('export source does not match candidate inventory')
        for name, parts in raw['imports'].items():
            bound = data['artifacts'][name]
            if parts != {part: item['path'] if item else None for part, item in bound.items()}:
                raise ValueError('export import binding differs from snapshot')
            if name in candidate['modules']:
                if name not in producers or bound != data['local_built'][name]:
                    raise ValueError('import is outside built local closure')
        exports[module] = export
    if not fidelity:
        # Planning needs bound sources and references, not kernel graphs.
        data['export_paths'] = exports
        return data
    data['module_bundles'] = read_bundles(exports)
    data['fidelity'] = read_environments(exports, candidate['modules'], selected, data['module_bundles'])
    if any(candidate['modules'][m]['is_module'] for m in selected):
        raise ValueError('module-system visibility is not yet supported by fidelity exports')
    if any(env['version'] != json.loads(header_path.read_bytes())['lean_version']
           for env in data['fidelity'].values()):
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
    if before.get('source_only', []) != after.get('source_only', []):
        raise ValueError('source-only root classification changed between candidates')
    if before['fidelity'].keys() != after['fidelity'].keys():
        if not any(row['kind'] in ('module', 'relocation') for row in mapping['entries']):
            raise ValueError('capture environment roots changed without module/relocation rows')
        # Relocation may move declarations and checks between independent
        # roots: compare the union of all exported modules, still per module key.
        results = {'<union>': FIDELITY.check(union_environment(before['module_bundles']),
                                             union_environment(after['module_bundles']), mapping)}
    else:
        results = {root: FIDELITY.check(env, after['fidelity'][root], mapping)
                   for root, env in before['fidelity'].items()}
    result = dict(status='OK', environments=results)
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
    cap.add_argument('--source-only', action='append', default=[],
                     help='explicit standalone leaf root: elaborate source, build only its imports')
    cap.add_argument('--build-prefix', required=True)
    cap.add_argument('--admit-command', required=True)
    cap.add_argument('--release-command', required=True)
    cap.add_argument('--output', type=Path, required=True)
    cap.add_argument('--reuse', type=Path,
                     help='prior capture directory whose identical exporter commands are reused (resume)')
    cap.add_argument('--jobs', type=int, default=1,
                     help='concurrent exporter processes; size the admission command for them')
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
