#!/usr/bin/env python3
"""Capture and compare source-bound local dependency closures for naming fidelity.

Capture requires an explicit owned build command prefix and explicit host
admission/release commands. It never invents a build/admission policy. All argv
values are JSON arrays, executed without a shell. Output must be outside the
checkout. Comparison is read-only and does not require Lean or host admission.
"""
import argparse
from collections import defaultdict
import gc
import hashlib
import json
import os
from pathlib import Path
import re
import resource
import shutil
import subprocess
import sys
import threading
import time

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
    # A tracked file deleted in the working tree (a module row's move) is not
    # part of the candidate; its replacement is an untracked file.
    deleted = set(git(root, 'ls-files', '-z', '--deleted').decode().split('\0'))
    paths = [p for p in paths if p not in deleted]
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


def read_environments(paths, modules, selected, bundles=None, roots=None):
    # Parse each module once. Merged environments share the kernel objects of
    # common dependencies, rather than duplicating those graphs per executable.
    # `roots` limits the merge to those maximal environments (a batched compare).
    bundles = bundles if bundles is not None else read_bundles(paths)
    result = {}
    for root, members in environments(modules, selected).items():
        if roots is not None and root not in roots:
            continue
        merged = empty_environment()
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
            for name, modules in data.get('holders', {}).items():
                merged['holders'].setdefault(name, set()).update(modules)
            extend_items(merged, data)
        result[root] = merged
    if not result:
        raise ValueError('no captured source environments')
    return result


def empty_environment():
    return dict(constants={}, roots=set(), guards=[], attributes=[], modules={}, receipts=[],
                checks=[], version=None, coalesced_equations=[], owners={}, holders={},
                item_modules={key: [] for key in FIDELITY.ITEMS}, schemas=set(), derived={})


def extend_items(merged, data):
    """Append one module bundle's checks, keeping the module of each."""
    for field in FIDELITY.ITEMS:
        merged[field].extend(data[field])
        owners = (data.get('item_modules') or {}).get(field)
        if owners is None or len(owners) != len(data[field]):
            raise ValueError(f'bundle without a module record for its {field}')
        merged['item_modules'][field].extend(owners)
    merged['receipts'].extend(data['receipts'])
    merged['schemas'] |= set(data.get('schemas', ()))
    merged.setdefault('derived', {}).update(data.get('derived', {}))
    merged['dot_identifiers_resolved'] = merged.get('dot_identifiers_resolved', 0) + data.get('dot_identifiers_resolved', 0)
    if '_pools' in data:
        merged.setdefault('_pools', []).extend(data['_pools'])
    if '_special_ids' in data:
        merged.setdefault('_special_ids', set()).update(data['_special_ids'])
    for field in ('quotation_sites', 'module_sources', 'module_decls', 'module_commands', 'import_modules'):
        merged.setdefault(field, {}).update(data.get(field, {}))


def union_environment(bundles):
    """All exported modules as one comparison scope, for relocations that move
    declarations or checks between independent roots. Checks keep their
    module (the comparator tags them), so unrelated roots are not pooled.
    Identical non-authored copies of one name coalesce as within an import
    environment; any other name defined in two independent modules (each
    executable's `main`) is keyed per module."""
    merged = empty_environment()
    occurrences = {}
    for module, data in sorted(bundles.items()):
        if merged['version'] is not None and merged['version'] != data['version']:
            raise ValueError('mixed Lean versions in capture')
        merged['version'] = data['version']
        for name, constant in data['constants'].items():
            occurrences.setdefault(name, []).append((module, constant, name in data['roots']))
        merged['modules'].update(data['modules'])
        extend_items(merged, data)
    for name, rows in sorted(occurrences.items()):
        first = rows[0][1]
        coalesce = len(rows) > 1 and not any(root for _, _, root in rows) and all(
            FIDELITY.dag_equal(constant, first) for _, constant, _ in rows)
        if len(rows) == 1 or coalesce:
            merged['constants'][name] = first
            merged['owners'][name] = rows[0][0]
            merged['holders'][name] = {module for module, _, _ in rows}
            if rows[0][2]:
                merged['roots'].add(name)
            if coalesce:
                merged['coalesced_equations'].append(name)
            continue
        for module, constant, root in rows:
            key = f'{name}@{module}'
            if name in merged['derived']:
                merged['derived'][key] = merged['derived'][name]
            merged['constants'][key] = constant
            merged['owners'][key] = module
            merged['holders'][key] = {module}
            if root:
                merged['roots'].add(key)
    return merged


def ilean_path(root, module):
    return root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.ilean')


def bind_ileans(root, producers):
    result = {}
    for module in producers:
        path = ilean_path(root, module)
        if not path.is_file():
            raise ValueError(f'missing producer .ilean artifact: {module}')
        result[module] = dict(path=str(path.absolute()), sha256=file_sha(path))
    return result


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
    start = time.monotonic()
    proc = subprocess.run(command, cwd=root, capture_output=True)
    (out / (label + '.log')).write_bytes(proc.stdout + proc.stderr)
    receipt = dict(argv=command, cwd=str(root), exit=proc.returncode,
                   log_sha256=sha(proc.stdout + proc.stderr), seconds=round(time.monotonic() - start, 3))
    save(out / (label + '.command.json'), receipt)
    if proc.returncode:
        raise ValueError(f'{label} exited {proc.returncode}; see {out / (label + ".log")}')
    return receipt


# Incremental capture. A module's `--imports` and export outputs depend only on
# its source bytes (at its candidate-relative path), the import artifacts (for
# full elab) or its own compiled `.olean`/`.ilean` artifacts (for `--from-olean`),
# the exporter binary, the toolchain and Lake configuration, and the export schema.
KEY_SCHEMA = 2


def compact(value):
    """The exporter's own serialization (Lean's `Json.compress`): Lean escapes
    only quote, backslash, `\\n` and `\\r` by name and every other control
    character as `\\u00xx`, where Python names `\\t`, `\\b` and `\\f`."""
    text = json.dumps(value, separators=(',', ':'), ensure_ascii=False)
    return re.sub(r'(?<!\\)((?:\\\\)*)\\([tbf])',
                  lambda m: m.group(1) + '\\u00' + dict(t='09', b='08', f='0c')[m.group(2)], text)


def reuse_key_elab(module, row, exporter_hash, config, identities, export_schema):
    return sha(json.dumps(dict(key_schema=KEY_SCHEMA, export_schema=export_schema, mode='elab', module=module,
                               path=row['path'], source_sha256=row['sha256'], exporter_sha256=exporter_hash,
                               config=config, imports=identities), sort_keys=True).encode())


def reuse_key_olean(module, row, exporter_hash, config, own_identity, ilean_sha, export_schema):
    return sha(json.dumps(dict(key_schema=KEY_SCHEMA, export_schema=export_schema, mode='olean', module=module,
                               path=row['path'], source_sha256=row['sha256'], exporter_sha256=exporter_hash,
                               config=config, own_artifacts=own_identity, ilean_sha256=ilean_sha), sort_keys=True).encode())


def reuse_key(module, row, exporter_hash, config, identities, export_schema):
    return reuse_key_elab(module, row, exporter_hash, config, identities, export_schema)


def config_identity(files):
    return {name: files.get(name) for name in CONFIG}


def lean_resolve(search_path, name):
    """Lean 4.35 `findWithExt`: the first search-path entry holding the root
    package directory (or root `.olean`) decides the module's file."""
    parts = name.split('.')
    if not all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_\'!?]*', p) for p in parts):
        return None  # escaped spellings: not resolved here, so not reused
    for entry in search_path:
        if (Path(entry) / parts[0]).is_dir() or (Path(entry) / (parts[0] + '.olean')).exists():
            return str(Path(entry).joinpath(*parts).with_suffix('.olean'))
    return None


def prior_index(directory):
    """What a prior capture recorded for reuse, or None."""
    directory = Path(directory)
    if (directory / 'reuse-index.json').is_file():
        index = json.loads((directory / 'reuse-index.json').read_bytes())
        if index.get('key_schema') != KEY_SCHEMA:
            return None
    elif (directory / 'snapshot.json').is_file() and (directory / 'headers.command.json').is_file():
        data = json.loads((directory / 'snapshot.json').read_bytes())
        if data.get('status') != 'OK' or data.get('schema_version') not in (3, 4):
            return None
        first = min(data['exports'].values(), key=lambda row: (directory / row['path']).stat().st_size)
        index = dict(root=json.loads((directory / 'headers.command.json').read_bytes())['cwd'],
                     export_schema=json.loads((directory / first['path']).read_bytes())['schema_version'],
                     exporter_sha256=data['exporter_sha256'], config=config_identity(data['candidate']['files']),
                     artifacts={name: artifact_identity(parts) for name, parts in data['artifacts'].items()},
                     local_built={m: artifact_identity(parts) for m, parts in data.get('local_built', {}).items()},
                     local_ileans={m: row['sha256'] for m, row in data.get('local_ileans', {}).items()},
                     modules={m: dict(path=data['candidate']['modules'][m]['path'],
                                      sha256=data['candidate']['modules'][m]['sha256'],
                                      from_olean=bool(data['exports'][m].get('from_olean', False)))
                              for m in data['selected']})
    else:
        return None
    index['directory'] = directory
    local_built = index.get('local_built', {})
    local_ileans = index.get('local_ileans', {})
    for module, row in index['modules'].items():
        row['key'] = None
        row['olean_key'] = None
        imports = directory / (module + '.imports.json')
        if imports.is_file():
            names = json.loads(imports.read_bytes())['imports']
            if all(name in index['artifacts'] for name in names):
                row['key'] = reuse_key_elab(module, row, index['exporter_sha256'], index['config'],
                                            {name: index['artifacts'][name] for name in names}, index['export_schema'])
        if module in local_built and module in local_ileans:
            row['olean_key'] = reuse_key_olean(
                module, row, index['exporter_sha256'], index['config'],
                local_built[module], local_ileans[module], index['export_schema'])
    return index


def prior_output(index, label, target, root, parse=True):
    """The prior's output for `label` if its command succeeded. A prior from
    another root must re-serialize byte-identically (so relocating its paths
    changes nothing else); one from this root is copied verbatim, and is
    parsed only when `parse` asks for its contents."""
    directory = index['directory']
    receipt, log, output = (directory / (label + '.command.json'), directory / (label + '.log'),
                            directory / target.name)
    if not (receipt.is_file() and log.is_file() and output.is_file()):
        return None
    receipt = json.loads(receipt.read_bytes())
    if receipt.get('exit') != 0:
        return None
    same_root = Path(index['root']) == Path(root)
    if same_root and not parse:
        return receipt, None, log, output
    raw = output.read_bytes()
    try:
        data = json.loads(raw)
    except ValueError:
        return None
    if not same_root and compact(data).encode() != raw.rstrip(b'\n'):
        return None
    return receipt, data, log, output


def relocate_parts(parts, old_root, new_root):
    def move(path):
        if path is None or not Path(path).is_relative_to(old_root):
            return path
        return str(Path(new_root) / Path(path).relative_to(old_root))
    return {part: move(path) for part, path in parts.items()}


def install_reused(index, receipt, data, log, output, root, out, label, command, target):
    import shutil
    if Path(index['root']) == Path(root) or (data is not None and 'imports' not in data):
        shutil.copyfile(output, target)
    else:
        data = dict(data, imports={name: relocate_parts(parts, index['root'], root)
                                   for name, parts in data['imports'].items()})
        target.write_text(compact(data))
    if label.endswith('-export'):
        module = label[:-len('-export')]
        prior_meta = index['directory'] / (module + '.meta.json')
        if prior_meta.is_file():
            shutil.copyfile(prior_meta, out / (module + '.meta.json'))
    (out / (label + '.log')).write_bytes(log.read_bytes())
    new = dict(argv=command, cwd=str(root), exit=0, log_sha256=receipt['log_sha256'],
               reused_from=str(index['directory']), seconds=receipt.get('seconds'))
    save(out / (label + '.command.json'), new)
    return new


def prior_seconds(indexes, label):
    for index in indexes:
        path = index['directory'] / (label + '.command.json')
        if path.is_file():
            seconds = json.loads(path.read_bytes()).get('seconds')
            if isinstance(seconds, (int, float)):
                return seconds
    return None


def longest_first(calls, indexes):
    """Start order: longest prior wall time first, modules with no recorded
    time before all timed ones, so a large file never runs alone at the end."""
    def weight(position):
        seconds = prior_seconds(indexes, calls[position][2])
        return (seconds is not None, -(seconds or 0), position)
    return sorted(range(len(calls)), key=weight)


def parallel(jobs, calls, indexes=()):
    """Run independent exporter commands, at most `jobs` at once, started
    longest first; every receipt is kept and the first failure (in input order)
    is raised after all finish."""
    from concurrent.futures import ThreadPoolExecutor
    def attempt(call):
        try:
            return run(*call), None
        except ValueError as error:
            return None, error
    with ThreadPoolExecutor(max_workers=max(1, jobs)) as pool:
        futures = {position: pool.submit(attempt, calls[position])
                   for position in longest_first(calls, indexes)}
        results = [futures[position].result() for position in range(len(calls))]
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
    cache_dir = Path(args.cache_dir).resolve() if getattr(args, 'cache_dir', None) else None
    plan_only = bool(getattr(args, 'plan_only', False))
    full_elab = bool(plan_only or getattr(args, 'full_elab', False))
    full_elab_mods = set(getattr(args, 'full_elab_module', None) or ())
    if cache_dir is not None:
        if cache_dir.is_relative_to(root):
            raise ValueError('cache directory must be outside the candidate checkout')
        (cache_dir / 'exports').mkdir(parents=True, exist_ok=True)
    source_before = inventory(root, source_dirs)
    out.mkdir(parents=True, exist_ok=False)
    save(out / 'source-before.json', source_before)
    tool_root = root if args.tool_root is None else args.tool_root.resolve(strict=True)
    if tool_root != root:
        if args.tool_build_prefix is None:
            raise ValueError('--tool-root needs --tool-build-prefix (the owned build in that checkout)')
        if (tool_root / 'lean-toolchain').read_bytes() != (root / 'lean-toolchain').read_bytes():
            raise ValueError('tool checkout and candidate use different Lean toolchains')
    elif args.tool_build_prefix is not None:
        raise ValueError('--tool-build-prefix is only for an external --tool-root')
    tool_build = run(tool_root, out, 'tool-build',
                     argv(args.tool_build_prefix or args.build_prefix) + ['jaune-naming-fidelity'])
    exporter = tool_root / '.lake/build/bin/jaune-naming-fidelity'
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
    unknown_fe = full_elab_mods - set(initial['modules'])
    if unknown_fe:
        raise ValueError(f'--full-elab-module names unknown module(s): {sorted(unknown_fe)}')
    reuse = [args.reuse] if isinstance(args.reuse, (str, Path)) else list(args.reuse or [])
    indexes = [index for index in map(prior_index, reuse) if index is not None]
    config = config_identity(source_before['files'])
    if inventory(root, source_dirs) != source_before:
        raise ValueError('candidate changed during header discovery')
    selected = closure(initial['modules'], args.module)
    if any(initial['modules'][m]['is_module'] for m in selected):
        raise ValueError('module-system visibility is not yet supported by fidelity exports')
    source_only = sorted(set(args.source_only))
    source_only_set = set(source_only)
    producers = build_modules(initial['modules'], args.module, source_only)
    if producers:
        build = run(root, out, 'build', argv(args.build_prefix) + producers)
    else:
        build = dict(exit=0, argv=[], skipped='no local producer modules')
        save(out / 'build.command.json', build)
    if inventory(root, source_dirs) != source_before or file_sha(exporter) != exporter_hash:
        raise ValueError('candidate or exporter changed during build')
    local_paths = {m: artifact_parts(root / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean'))
                   for m in producers}
    local_built = bind_artifacts(local_paths)
    local_ileans = bind_ileans(root, producers)
    tool_paths = ('scripts/NamingFidelity.lean', 'scripts/NamingReferencesCore.lean',
                  'scripts/check-naming-fidelity.py',
                  'scripts/naming-candidate.py', 'scripts/check-naming-map.py',
                  'scripts/apply-naming-map.py')
    if tool_root == root:
        tool_sources = {p: initial['files'].get(p) for p in tool_paths}
    else:
        tool_sources = {p: file_sha(tool_root / p) for p in tool_paths}
    search_path = None
    if indexes:
        printed = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=root, capture_output=True)
        if printed.returncode == 0:
            search_path = [str(root / entry) for entry in printed.stdout.decode().strip().split(':') if entry]
    hashes = {}
    def identity(parts):
        for path in parts.values():
            if path is not None and path not in hashes:
                hashes[path] = file_sha(path)
        return {part: hashes[path] if path else None for part, path in parts.items()}
    local_identity = {m: artifact_identity(parts) for m, parts in local_built.items()}
    verdicts = {}

    def reusable_imports(index, module):
        row = index['modules'].get(module)
        if (row is None or search_path is None or row['path'] != initial['modules'][module]['path'] or
                row['sha256'] != initial['modules'][module]['sha256'] or
                index['exporter_sha256'] != exporter_hash or index['config'] != config):
            return None
        found = prior_output(index, module + '-imports', out / (module + '.imports.json'), root)
        if found is None or found[1].get('module') != module:
            return None
        for name, parts in found[1]['imports'].items():
            memo = (id(index), name, tuple(sorted(parts.items())))
            if memo not in verdicts:
                verdicts[memo] = import_still_bound(index, name, parts)
            if not verdicts[memo]:
                return None
        return found

    def import_still_bound(index, name, parts):
        if name not in index['artifacts'] or set(parts) != set(PARTS) or parts['olean'] is None:
            return False
        parts = relocate_parts(parts, index['root'], root)
        if name in initial['modules']:
            return (name in local_paths and parts == local_paths[name] and
                    local_identity[name] == index['artifacts'][name])
        return (lean_resolve(search_path, name) == parts['olean'] and artifact_parts(parts['olean']) == parts and
                identity(parts) == index['artifacts'][name])

    def try_cache_hit(key, module, label, target, target_meta, command):
        if cache_dir is None or key is None:
            return None
        cdir = cache_dir / 'exports'
        c_exp = cdir / f'{key}.export.json'
        c_meta = cdir / f'{key}.meta.json'
        c_log = cdir / f'{key}.log'
        c_cmd = cdir / f'{key}.command.json'
        if not (c_exp.is_file() and c_meta.is_file() and c_log.is_file() and c_cmd.is_file()):
            return None
        try:
            meta = json.loads(c_meta.read_bytes())
            old_cmd = json.loads(c_cmd.read_bytes())
        except ValueError:
            return None
        if (meta.get('meta_version') != 1 or meta.get('schema_version') != FIDELITY.CURRENT_SCHEMA or
                meta.get('module') != module or meta.get('export_sha256') != file_sha(c_exp) or
                meta.get('source_sha256') != initial['modules'][module]['sha256']):
            return None
        shutil.copyfile(c_exp, target)
        shutil.copyfile(c_meta, target_meta)
        (out / (label + '.log')).write_bytes(c_log.read_bytes())
        new = dict(argv=command, cwd=str(root), exit=0, log_sha256=old_cmd.get('log_sha256', ''),
                   reused_from=str(cache_dir), seconds=old_cmd.get('seconds'))
        save(out / (label + '.command.json'), new)
        return dict(reused_from=str(cache_dir), cache_hit=True)

    def store_cache(key, target, target_meta, label):
        if cache_dir is None or key is None:
            return
        cdir = cache_dir / 'exports'
        suffix = f'.tmp.{os.getpid()}.{threading.get_ident()}'
        for src_p, dst_name in ((target, f'{key}.export.json'),
                                (out / f'{label}.log', f'{key}.log'),
                                (out / f'{label}.command.json', f'{key}.command.json'),
                                (target_meta, f'{key}.meta.json')):
            tmp_p = cdir / (dst_name + suffix)
            shutil.copyfile(src_p, tmp_p)
            os.replace(tmp_p, cdir / dst_name)

    def validate_resolved(module, resolved_path, used_olean):
        resolved = json.loads(resolved_path.read_bytes())
        expected_imps = {n: {p: r['path'] if r else None for p, r in bound[n].items()}
                         for n in discovery[module]['imports']}
        if (resolved.get('schema_version') != 1 or resolved.get('module') != module or
                resolved.get('lean_version') != discovery[module]['lean_version'] or
                resolved.get('direct_imports') != discovery[module]['direct_imports'] or
                resolved.get('imports') != expected_imps):
            raise ValueError(f'resolved import artifacts differ from discovery: {module}')
        if used_olean and (resolved.get('own_artifacts') != local_paths[module] or
                           resolved.get('ilean') != local_ileans[module]['path']):
            raise ValueError(f'resolved own artifacts differ from build: {module}')

    def validate_and_meta(module, target, target_meta):
        raw = target.read_bytes()
        data = json.loads(raw)
        if data['schema_version'] != FIDELITY.CURRENT_SCHEMA:
            raise ValueError(f'export is not bound to the discovered candidate: {module}')
        if data['schema_version'] >= 8:
            imp_mods = data.get('import_modules')
            if not isinstance(imp_mods, list) or sorted(imp_mods) != sorted(discovery[module]['imports'].keys()):
                raise ValueError(f'export is not bound to the discovered candidate: {module}')
        elif data.get('imports') != discovery[module]['imports']:
            raise ValueError(f'export is not bound to the discovered candidate: {module}')
        if (FIDELITY.APPLY.module_name(data['index']['module']) != module or
                data['index']['directImports'] != discovery[module]['direct_imports'] or
                data['lean_version'] != discovery[module]['lean_version'] or
                sha(data['source'].encode()) != initial['modules'][module]['sha256']):
            raise ValueError(f'export is not bound to the discovered candidate: {module}')
        export_sha = sha(raw)
        if plan_only:
            return dict(path=target.name, sha256=export_sha)
        if target_meta.is_file():
            try:
                meta = json.loads(target_meta.read_bytes())
                if meta.get('meta_version') == 1 and meta.get('export_sha256') == export_sha and meta.get('module') == module:
                    return dict(path=target.name, sha256=export_sha, meta_path=target_meta.name,
                                meta_sha256=file_sha(target_meta), from_olean=bool(meta.get('from_olean', False)))
            except ValueError:
                pass
        meta = FIDELITY.extract_module_meta(target, export_sha)
        (out / target_meta.name).write_bytes(compact(meta).encode())
        return dict(path=target.name, sha256=export_sha, meta_path=target_meta.name,
                    meta_sha256=file_sha(target_meta), from_olean=bool(meta.get('from_olean', False)))

    run(root, out, 'admit', argv(args.admit_command))
    try:
        imports, discovery, exports, provenance = {}, {}, {}, {}
        need_imports = []
        for module in selected:
            label, target = module + '-imports', out / (module + '.imports.json')
            command = ['lake', 'env', str(exporter), '--imports', initial['modules'][module]['path'],
                       module, str(target)]
            for index in indexes:
                found = reusable_imports(index, module)
                if found is not None:
                    install_reused(index, *found, root, out, label, command, target)
                    provenance[module] = dict(imports=dict(reused_from=str(index['directory'])))
                    break
            else:
                provenance[module] = dict(imports='elaborated')
                need_imports.append([module, initial['modules'][module]['path']])
        if need_imports:
            batch_in = out / 'imports-batch-input.json'
            batch_out = out / 'imports-batch.json'
            save(batch_in, need_imports)
            batch_cmd = ['lake', 'env', str(exporter), '--imports-batch', str(batch_in), str(batch_out)]
            batch_receipt = run(root, out, 'imports-batch', batch_cmd)
            batch_data = json.loads(batch_out.read_bytes())
            batch_log = (out / 'imports-batch.log').read_bytes()
            if (batch_data.get('schema_version') != 1 or
                    set(batch_data.get('modules', {})) != {m for m, _ in need_imports}):
                raise ValueError('invalid --imports-batch output')
            arts = batch_data['artifacts']
            for module, _ in need_imports:
                row = batch_data['modules'][module]
                imp_dict = {name: arts[name] for name in row['import_modules']}
                per_mod = dict(schema_version=1, module=module, lean_version=batch_data['lean_version'],
                               direct_imports=row['direct_imports'], imports=imp_dict)
                (out / f'{module}.imports.json').write_bytes(compact(per_mod).encode())
                (out / f'{module}-imports.log').write_bytes(batch_log)
                save(out / f'{module}-imports.command.json', dict(
                    argv=batch_cmd, cwd=str(root), exit=0,
                    log_sha256=batch_receipt['log_sha256'], seconds=batch_receipt['seconds']))
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
        elab_keys = {module: reuse_key_elab(module, initial['modules'][module], exporter_hash, config,
                                             {name: artifact_identity(bound[name]) for name in discovery[module]['imports']},
                                             FIDELITY.CURRENT_SCHEMA)
                     for module in selected}
        olean_keys = {module: reuse_key_olean(module, initial['modules'][module], exporter_hash, config,
                                              local_identity[module], local_ileans[module]['sha256'],
                                              FIDELITY.CURRENT_SCHEMA)
                      for module in producers}
        save(out / 'reuse-index.json', dict(
            key_schema=KEY_SCHEMA, root=str(root), exporter_sha256=exporter_hash, config=config,
            export_schema=FIDELITY.CURRENT_SCHEMA,
            artifacts={name: artifact_identity(parts) for name, parts in bound.items()},
            local_built=local_identity,
            local_ileans={m: row['sha256'] for m, row in local_ileans.items()},
            modules={m: dict(path=initial['modules'][m]['path'], sha256=initial['modules'][m]['sha256'],
                             key=elab_keys[m], olean_key=olean_keys.get(m)) for m in selected}))

        fresh_calls = []
        late_candidates = []
        export_modes = {}

        for module in selected:
            label = module + '-export'
            target = out / (module + '.export.json')
            target_meta = out / (module + '.meta.json')
            src_path = initial['modules'][module]['path']
            wants_olean = (not full_elab) and (module not in full_elab_mods) and (module not in source_only_set)
            resolved_path = out / f'{module}.resolved.json'
            cmd_elab = ['lake', 'env', str(exporter), src_path, module, str(target),
                        '--resolved-out', str(resolved_path)]
            if wants_olean:
                okey = olean_keys[module]
                hit = try_cache_hit(okey, module, label, target, target_meta, cmd_elab)
                if hit is not None:
                    provenance[module]['export'] = hit
                    export_modes[module] = 'cached-olean'
                    continue
                matching_o = [index for index in indexes if (index['modules'].get(module) or {}).get('olean_key') == okey]
                if matching_o:
                    late_candidates.append((module, label, target, target_meta, cmd_elab, matching_o, 'olean', okey))
                    continue
                fresh_calls.append((module, True, elab_keys[module], okey))
            else:
                ekey = elab_keys[module]
                hit = try_cache_hit(ekey, module, label, target, target_meta, cmd_elab)
                if hit is not None:
                    provenance[module]['export'] = hit
                    export_modes[module] = 'cached-elab'
                    continue
                matching_e = [index for index in indexes if (index['modules'].get(module) or {}).get('key') == ekey]
                if matching_e:
                    late_candidates.append((module, label, target, target_meta, cmd_elab, matching_e, 'elab', ekey))
                    continue
                fresh_calls.append((module, False, ekey, None))

        def run_fresh(item):
            module, wants_olean, ekey, okey = item
            label = module + '-export'
            target = out / f'{module}.export.json'
            target_meta = out / f'{module}.meta.json'
            resolved_path = out / f'{module}.resolved.json'
            src_path = initial['modules'][module]['path']
            cmd_elab = ['lake', 'env', str(exporter), src_path, module, str(target),
                        '--resolved-out', str(resolved_path)]
            if wants_olean:
                cmd_olean = ['lake', 'env', str(exporter), '--from-olean', src_path, module,
                             local_ileans[module]['path'], str(target), '--resolved-out', str(resolved_path)]
                t0 = time.monotonic()
                proc = subprocess.run(cmd_olean, cwd=root, capture_output=True)
                elapsed = round(time.monotonic() - t0, 3)
                if proc.returncode == 0:
                    (out / (label + '.log')).write_bytes(proc.stdout + proc.stderr)
                    save(out / (label + '.command.json'), dict(
                        argv=cmd_olean, cwd=str(root), exit=0,
                        log_sha256=sha(proc.stdout + proc.stderr), seconds=elapsed))
                    validate_resolved(module, resolved_path, True)
                    row = validate_and_meta(module, target, target_meta)
                    store_cache(okey, target, target_meta, label)
                    return module, row, 'from_olean', okey
                if proc.returncode != 3:
                    (out / (label + '.log')).write_bytes(proc.stdout + proc.stderr)
                    save(out / (label + '.command.json'), dict(
                        argv=cmd_olean, cwd=str(root), exit=proc.returncode,
                        log_sha256=sha(proc.stdout + proc.stderr), seconds=elapsed))
                    raise ValueError(f'{label} exited {proc.returncode}; see {out / (label + ".log")}')
                # Exit 3 (`NEEDS_ELAB`): check elab cache / reuse before running full elaboration.
                for p in (target, resolved_path):
                    if p.exists():
                        p.unlink()
                hit = try_cache_hit(ekey, module, label, target, target_meta, cmd_elab)
                if hit is not None:
                    row = validate_and_meta(module, target, target_meta)
                    return module, row, hit, ekey
                for index in indexes:
                    if (index['modules'].get(module) or {}).get('key') == ekey:
                        found = prior_output(index, label, target, root, parse=False)
                        if found is not None:
                            install_reused(index, *found, root, out, label, cmd_elab, target)
                            row = validate_and_meta(module, target, target_meta)
                            return module, row, dict(reused_from=str(index['directory'])), ekey
            run(root, out, label, cmd_elab)
            validate_resolved(module, resolved_path, False)
            row = validate_and_meta(module, target, target_meta)
            store_cache(ekey, target, target_meta, label)
            return module, row, 'elaborated', ekey

        # Order fresh calls longest first based on prior timing receipts.
        def fresh_weight(pos):
            m = fresh_calls[pos][0]
            sec = prior_seconds(indexes, m + '-export')
            return (sec is not None, -(sec or 0), pos)

        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
            fresh_futures = {pos: pool.submit(run_fresh, fresh_calls[pos])
                             for pos in sorted(range(len(fresh_calls)), key=fresh_weight)}
            # While fresh subprocesses run, install reused candidates on main thread; fallbacks run after.
            fallback_calls = []
            for module, label, target, target_meta, cmd_elab, matching, mode_tag, key_used in late_candidates:
                for index in matching:
                    found = prior_output(index, label, target, root, parse=False)
                    if found is not None:
                        install_reused(index, *found, root, out, label, cmd_elab, target)
                        provenance[module]['export'] = dict(reused_from=str(index['directory']))
                        exports[module] = validate_and_meta(module, target, target_meta)
                        store_cache(key_used, target, target_meta, label)
                        break
                else:
                    fallback_calls.append((module, mode_tag == 'olean', elab_keys[module], olean_keys.get(module)))
            fresh_results = [fresh_futures[pos].result() for pos in range(len(fresh_calls))]
        for module, row, prov, _ in fresh_results:
            exports[module] = row
            provenance[module]['export'] = prov
        if fallback_calls:
            with ThreadPoolExecutor(max_workers=max(1, args.jobs)) as pool:
                fb_futures = [pool.submit(run_fresh, item) for item in fallback_calls]
                for fut in fb_futures:
                    module, row, prov, _ = fut.result()
                    exports[module] = row
                    provenance[module]['export'] = prov

        for module in selected:
            if module not in exports:
                exports[module] = validate_and_meta(module, out / f'{module}.export.json', out / f'{module}.meta.json')

        if bind_artifacts(imports) != bound or bind_artifacts(local_paths) != local_built or bind_ileans(root, producers) != local_ileans:
            raise ValueError('import or .ilean artifacts changed during export')
        if inventory(root, source_dirs) != source_before or file_sha(exporter) != exporter_hash:
            raise ValueError('candidate or exporter changed during export')
        if tool_root != root and {p: file_sha(tool_root / p) for p in tool_paths} != tool_sources:
            raise ValueError('tool checkout sources changed during export')
        result = dict(schema_version=4, status='OK', scope='local-import-closure', jobs=args.jobs,
                      candidate=initial, roots=args.module, selected=selected, build=build, tool_build=tool_build,
                      source_only=source_only, producers=producers,
                      headers_sha256=file_sha(header_output),
                      exporter_sha256=exporter_hash, tool_sources=tool_sources,
                      **({} if tool_root == root else dict(tool_root=str(tool_root))),
                      **(dict(purpose='plan') if plan_only else {}),
                      artifacts=bound, local_built=local_built, local_ileans=local_ileans, exports=exports,
                      **({'provenance': provenance} if (reuse or cache_dir) else {}))
    finally:
        run(root, out, 'release', argv(args.release_command))
    save(out / 'snapshot.json', result)
    return dict(status='OK', snapshot=str(out / 'snapshot.json'), modules=len(selected))


def read_snapshot(path, fidelity=True, roots=None, light=False):
    """`roots`: with fidelity, load and merge only these maximal environments (a
    batched compare); with `light=True`, verify `.meta.json` and export digests
    without JSON-parsing `.export.json` up front."""
    path = Path(path)
    data = json.loads(path.read_bytes())
    if data['schema_version'] not in (2, 3, 4) or data['status'] != 'OK' or data['build']['exit'] != 0:
        raise ValueError('not a successful candidate capture')
    if fidelity and data.get('purpose') == 'plan':
        raise ValueError('plan-only capture cannot be used for fidelity comparison')
    candidate = data['candidate']
    header_path = path.parent / 'headers.json'
    if file_sha(header_path) != data['headers_sha256']:
        raise ValueError('compiler header inventory digest changed')
    header_data = json.loads(header_path.read_bytes())
    source = json.loads((path.parent / 'source-before.json').read_bytes())
    if bind_headers(source, header_data) != candidate:
        raise ValueError('candidate graph differs from compiler header inventory')
    selected = closure(candidate['modules'], data['roots'])
    if selected != data['selected'] or set(selected) != data['exports'].keys():
        raise ValueError('incomplete candidate export closure')
    if data['schema_version'] == 2 and data.get('source_only'):
        raise ValueError('schema 2 does not support source-only roots')
    source_only = data['source_only'] if data['schema_version'] >= 3 else []
    producers = build_modules(candidate['modules'], data['roots'], source_only)
    if data['schema_version'] >= 3 and (producers != data['producers'] or
                                        set(producers) != data['local_built'].keys()):
        raise ValueError('producer artifact inventory differs from required build closure')
    if data['schema_version'] >= 4 and set(producers) != data.get('local_ileans', {}).keys():
        raise ValueError('producer .ilean inventory differs from required build closure')
    for module, row in candidate['modules'].items():
        if candidate['files'].get(row['path']) != row['sha256']:
            raise ValueError('module source digest differs from candidate file inventory')
    inventoried = {row['path'] for row in candidate['modules'].values()}
    if {p for p in candidate['files'] if p.endswith('.lean') and p != 'lakefile.lean'} - inventoried:
        raise ValueError('candidate omits Lean sources from its module inventory')
    if any(candidate['modules'][m]['is_module'] for m in selected):
        raise ValueError('module-system visibility is not yet supported by fidelity exports')

    exports, metas = {}, {}
    snap_parent = path.parent.resolve()
    for module, record in data['exports'].items():
        export = path.parent / record['path']
        if not export.resolve().is_relative_to(snap_parent) or file_sha(export) != record['sha256']:
            raise ValueError('export missing, outside snapshot, or digest changed')
        meta_loaded = None
        if light and 'meta_path' in record:
            meta_file = path.parent / record['meta_path']
            if not meta_file.resolve().is_relative_to(snap_parent) or file_sha(meta_file) != record['meta_sha256']:
                raise ValueError(f'{module}: meta sidecar missing, outside snapshot, or digest changed')
            meta = json.loads(meta_file.read_bytes())
            if fidelity and meta['schema_version'] != FIDELITY.CURRENT_SCHEMA:
                raise ValueError(f'export {module} has schema {meta["schema_version"]}; recapture with the '
                                 f'current exporter (schema {FIDELITY.CURRENT_SCHEMA})')
            if (meta.get('meta_version') != 1 or meta.get('export_sha256') != record['sha256'] or
                    meta.get('schema_version') not in (4, 5, 6, 7, 8) or
                    meta.get('module') != module or
                    meta.get('source_sha256') != candidate['modules'][module]['sha256'] or
                    [entry[0] for entry in meta.get('direct_imports', ())] != candidate['modules'][module]['imports']):
                raise ValueError('export metadata does not match candidate inventory')
            if fidelity and meta.get('lean_version') != header_data['lean_version']:
                raise ValueError('compiler header and export Lean versions differ')
            imp_mods = meta.get('import_modules')
            if meta['schema_version'] >= 8:
                if not isinstance(imp_mods, list):
                    raise ValueError(f'{module}: missing import_modules in schema 8 metadata')
                for name in imp_mods:
                    if name not in data['artifacts']:
                        raise ValueError(f'{module}: import {name} missing from snapshot artifacts')
                    if name in candidate['modules'] and (name not in producers or data['artifacts'][name] != data['local_built'][name]):
                        raise ValueError('import is outside built local closure')
            meta_loaded = meta
        else:
            raw = json.loads(export.read_bytes())
            if fidelity and raw['schema_version'] != FIDELITY.CURRENT_SCHEMA:
                raise ValueError(f'export {module} has schema {raw["schema_version"]}; recapture with the '
                                 f'current exporter (schema {FIDELITY.CURRENT_SCHEMA})')
            if (raw['schema_version'] not in (4, 5, 6, 7, 8) or FIDELITY.APPLY.module_name(raw['index']['module']) != module or
                    sha(raw['source'].encode()) != candidate['modules'][module]['sha256'] or
                    [entry[0] for entry in raw['index']['directImports']] != candidate['modules'][module]['imports']):
                raise ValueError('export source does not match candidate inventory')
            if fidelity and raw['lean_version'] != header_data['lean_version']:
                raise ValueError('compiler header and export Lean versions differ')
            if raw['schema_version'] >= 8:
                for name in raw['import_modules']:
                    if name not in data['artifacts']:
                        raise ValueError(f'{module}: import {name} missing from snapshot artifacts')
                    if name in candidate['modules'] and (name not in producers or data['artifacts'][name] != data['local_built'][name]):
                        raise ValueError('import is outside built local closure')
            else:
                for name, parts in raw['imports'].items():
                    bound = data['artifacts'][name]
                    if parts != {part: item['path'] if item else None for part, item in bound.items()}:
                        raise ValueError('export import binding differs from snapshot')
                    if name in candidate['modules']:
                        if name not in producers or bound != data['local_built'][name]:
                            raise ValueError('import is outside built local closure')
        exports[module] = export
        metas[module] = meta_loaded
    if not fidelity:
        data['export_paths'] = exports
        data['metas'] = metas
        return data
    if light:
        data['export_paths'] = exports
        data['metas'] = metas
        data['all_environments'] = sorted(environments(candidate['modules'], selected))
        return data
    data['all_environments'] = sorted(environments(candidate['modules'], selected))
    if roots is not None:
        unknown = sorted(set(roots) - set(data['all_environments']))
        if unknown:
            raise ValueError(f'unknown capture environments: {unknown}')
        members = set().union(*(closure(candidate['modules'], [r]) for r in roots))
        exports = {m: e for m, e in exports.items() if m in members}
    data['module_bundles'] = read_bundles(exports)
    data['fidelity'] = read_environments(exports, candidate['modules'], selected, data['module_bundles'],
                                         roots=None if roots is None else set(roots))
    if any(env['version'] != header_data['lean_version'] for env in data['fidelity'].values()):
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


REVIEWED_KEYS = {'module', 'constant', 'before', 'after', 'map_old', 'map_new', 'decision', 'reason', 'precedent'}


def stale_quotations(records, used):
    """Every reviewed quotation record must have been used by some comparison."""
    stale = [row for index, row in enumerate(records) if index not in used]
    if stale:
        raise FIDELITY.Mismatch(f'reviewed quotation records that occur nowhere (stale): {stale}')


def plan_edits(plan_raw, map_raw, before_raw):
    """The applied plan's edits as (module, start, end, old, new), bound to
    the comparison: the plan must be a `planned` whole-tree plan made from
    exactly this map and this before snapshot (by digest)."""
    plan = json.loads(plan_raw)
    if plan.get('status') != 'planned':
        raise ValueError(f'plan status is {plan.get("status")!r}, not planned')
    if plan.get('map_sha256') != sha(map_raw):
        raise ValueError('plan was made from another map (map_sha256 differs)')
    if plan.get('snapshot_sha256') != sha(before_raw):
        raise ValueError('plan was made from another before snapshot (snapshot_sha256 differs)')
    path_module = {row['path']: name for name, row in json.loads(before_raw)['candidate']['modules'].items()}
    return {(path_module.get(f['path']), e['start'], e['end'], e['old'], e['new'])
            for f in plan['files'] for e in f['edits']}


def _validate_compare_inputs(before, after, mapping, inventory, reviewed):
    """Shared whole-tree accounting, exclusion, boundary, and reviewed-quotation validation."""
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
    excluded = set()
    if inventory is not None:
        raw, rows = inventory
        for side in (left, right):
            if side['files'].get('scripts/naming-inventory.json') != sha(raw):
                raise ValueError('naming inventory differs from a candidate\'s registered inventory')
        for row in rows['excluded_sources']:
            if left['files'].get(row['path']) == right['files'].get(row['path']) == row['sha256']:
                excluded |= {m for m, r in left['modules'].items() if r['path'] == row['path']}
    for side in (before, after):
        missing = (affected & side['candidate']['modules'].keys()) - set(side['selected']) - excluded
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
    FIDELITY.MAP.validate_map(mapping)
    renamer = FIDELITY.MAP.Renamer(mapping['entries'])
    records = []
    if reviewed is not None:
        data = json.loads(reviewed[0])
        if data.get('schema_version') != 1 or not isinstance(data.get('quotations'), list):
            raise ValueError('unsupported reviewed quotations')
        for row in data['quotations']:
            if not isinstance(row, dict) or set(row) != REVIEWED_KEYS or not all(
                    isinstance(v, str) and v.strip() for v in row.values()):
                raise ValueError(f'invalid reviewed quotation: {row!r}')
        records = data['quotations']
    return affected, excluded, renamer, records


def _is_map_disjoint(meta, renamer, aux_pattern, mapping_has_entries, reviewed_modules, plan_edit_modules, module):
    """True iff module's verified metadata guarantees no rename rule touches it."""
    if module in reviewed_modules or module in plan_edit_modules:
        return False
    if meta.get('check_count', 0) > 0 and mapping_has_entries:
        return False
    for entry in meta.get('direct_imports', ()):
        if renamer.module(entry[0]) != entry[0]:
            return False
    for imp in (meta.get('import_modules') or ()):
        if renamer.module(imp) != imp:
            return False
    derived_ns = renamer.derived()
    exact_parents = {old.rsplit('.', 1)[0] for old in renamer.exact if '.' in old}
    syms = set(meta.get('all_constants', ())) | set(meta.get('referenced_constants', ()))
    for sym in syms:
        if renamer(sym) != sym:
            return False
        base = sym.rsplit('@', 1)[0]
        if base.startswith('_private.'):
            sp = FIDELITY.MAP.split_private(base)
            if sp and (renamer.module(sp[0]) != sp[0] or renamer(sp[2]) != sp[2]):
                return False
            check_name = sp[2] if sp else base
        else:
            check_name = base
        if check_name in exact_parents:
            return False
        if aux_pattern is not None and aux_pattern.search('.' + check_name):
            return False
        parts = check_name.split('.')
        for k in range(1, len(parts) + 1):
            prefix = '.'.join(parts[:k])
            if (prefix in renamer.exact or prefix in renamer.namespaces or
                    prefix in derived_ns or renamer.scope(prefix) != prefix):
                return False
    return True


def _tarjan_sccs(nodes, adj):
    """Iterative Tarjan's SCC returning components in dependency-first topological order."""
    index = 0
    indices = {}
    lowlink = {}
    on_stack = set()
    scc_stack = []
    out = []
    for start in sorted(nodes):
        if start in indices:
            continue
        call_stack = [(start, iter(sorted(adj.get(start, ()))), True)]
        while call_stack:
            v, it, entering = call_stack[-1]
            if entering:
                indices[v] = lowlink[v] = index
                index += 1
                scc_stack.append(v)
                on_stack.add(v)
                call_stack[-1] = (v, it, False)
            try:
                w = next(it)
                if w not in indices:
                    call_stack.append((w, iter(sorted(adj.get(w, ()))), True))
                elif w in on_stack:
                    if indices[w] < lowlink[v]:
                        lowlink[v] = indices[w]
            except StopIteration:
                call_stack.pop()
                if call_stack:
                    parent = call_stack[-1][0]
                    if lowlink[v] < lowlink[parent]:
                        lowlink[parent] = lowlink[v]
                if lowlink[v] == indices[v]:
                    comp = []
                    while True:
                        w = scc_stack.pop()
                        on_stack.remove(w)
                        comp.append(w)
                        if w == v:
                            break
                    out.append(comp)
    return out


def _build_global_context_side(selected, metas):
    occ = {}
    ext_ref_mods = {}
    for mod in sorted(selected):
        meta = metas[mod]
        roots = set(meta['authored_roots'])
        for c in meta['all_constants']:
            occ.setdefault(c, []).append((mod, c in roots))
        for c in meta['kernel_referenced_constants']:
            ext_ref_mods.setdefault(c, set()).add(mod)
    all_roots, all_consts, owners, holders = set(), set(), {}, {}
    for name, rows in occ.items():
        if len(rows) == 1 or not any(r for _, r in rows):
            all_consts.add(name)
            owners[name] = rows[0][0]
            holders[name] = {m for m, _ in rows}
            if rows[0][1]:
                all_roots.add(name)
        else:
            all_consts.add(name)
            all_roots.add(name)
            for m, r in rows:
                key = f'{name}@{m}'
                all_consts.add(key)
                owners[key] = m
                holders[key] = {m}
                if r:
                    all_roots.add(key)
    return all_roots, all_consts, owners, holders, ext_ref_mods


def compare_components(before, after, mapping, inventory=None, reviewed=None, collect=False, plan_edits=None):
    """Per-component topological SCC DAG comparator with byte-identical fast path."""
    if isinstance(before, (str, Path)):
        before = read_snapshot(before, light=True)
    if isinstance(after, (str, Path)):
        after = read_snapshot(after, light=True)
    affected, excluded, renamer, records = _validate_compare_inputs(before, after, mapping, inventory, reviewed)
    used = set()
    left, right = before['candidate'], after['candidate']
    before_metas = before.setdefault('metas', {})
    after_metas = after.setdefault('metas', {})
    before_had_meta = {m: ('meta_path' in row and before_metas.get(m) is not None)
                       for m, row in before['exports'].items()}
    after_had_meta = {m: ('meta_path' in row and after_metas.get(m) is not None)
                      for m, row in after['exports'].items()}
    for snap, metas in ((before, before_metas), (after, after_metas)):
        for m in snap['selected']:
            if metas.get(m) is None:
                metas[m] = FIDELITY.extract_module_meta(snap['export_paths'][m])

    before_ver = next((before_metas[m]['lean_version'] for m in before['selected']), None)
    after_ver = next((after_metas[m]['lean_version'] for m in after['selected']), None)
    if before_ver != after_ver:
        raise ValueError('Lean versions differ')

    reloc_before = {src for _, (src, _) in renamer.relocations.items()} | {
        FIDELITY.MAP.split_private(p)[0] for p in renamer.public_from}
    reloc_after = {renamer.module(src) for src in reloc_before} | {
        dst for _, (_, dst) in renamer.relocations.items()}
    reviewed_mods = {row['module'] for row in records}
    plan_edit_mods = {e[0] for e in (plan_edits or ())}
    aux_pattern = FIDELITY.Comparison.aux_module_table(renamer)[1]
    has_entries = bool(mapping['entries'])

    fast_path = set()
    for m in before['selected']:
        if (m not in affected and m in after['selected'] and renamer.module(m) == m and
                m not in reloc_before and m not in reloc_after and
                before_had_meta.get(m) and after_had_meta.get(m) and
                before_metas[m]['schema_version'] == after_metas[m]['schema_version'] == FIDELITY.CURRENT_SCHEMA and
                before['exports'][m]['sha256'] == after['exports'][m]['sha256'] and
                _is_map_disjoint(before_metas[m], renamer, aux_pattern, has_entries, reviewed_mods, plan_edit_mods, m)):
            fast_path.add(m)

    # Ensure mapped partners of active modules are never stranded on fast_path.
    for m in set(before['selected']) - fast_path:
        img = renamer.module(m)
        fast_path.discard(img)
    for m in set(after['selected']) - fast_path:
        fast_path.discard(m)

    active_before = set(before['selected']) - fast_path
    active_after = set(after['selected']) - fast_path
    for bm in sorted(active_before):
        am = renamer.module(bm)
        if am in active_after:
            b_fo = bool(before_metas[bm].get('from_olean', False))
            a_fo = bool(after_metas[am].get('from_olean', False))
            if b_fo != a_fo:
                raise ValueError(
                    f'export mode mismatch for {bm} -> {am} (from_olean={b_fo} vs {a_fo}); '
                    f'recapture the --from-olean side with --full-elab-module')

    b_roots, b_consts, b_owners, b_holders, b_ext_ref_mods = _build_global_context_side(before['selected'], before_metas)
    a_roots, a_consts, a_owners, a_holders, a_ext_ref_mods = _build_global_context_side(after['selected'], after_metas)
    global_context = dict(
        before_roots=b_roots, after_roots=a_roots,
        before_constants=b_consts, after_constants=a_consts,
        before_owners=b_owners, after_owners=a_owners,
        before_holders=b_holders, after_holders=a_holders,
    )
    record_cache = {}

    def before_record(name):
        """The before kernel record of `name`, read from its owner's export
        (a `#guard_msgs` field-notation token names a constant of another
        module, outside the compared environment)."""
        module = b_owners.get(name)
        if module is None or module not in before['export_paths']:
            return None
        if module not in record_cache:
            record_cache[module] = FIDELITY.read_exports([before['export_paths'][module]])['constants']
        return record_cache[module].get(name)
    global_context['before_record'] = before_record

    uf_parent = {}
    def uf_find(x):
        while uf_parent.get(x, x) != x:
            uf_parent[x] = uf_parent.get(uf_parent[x], uf_parent[x])
            x = uf_parent[x]
        return x

    def uf_union(a, b):
        ra, rb = uf_find(a), uf_find(b)
        if ra != rb:
            uf_parent[max(ra, rb)] = min(ra, rb)

    for m in active_before:
        uf_find(('B', m))
        img = renamer.module(m)
        if img in active_after:
            uf_union(('B', m), ('A', img))
    for m in active_after:
        uf_find(('A', m))

    rev_after_to_before = defaultdict(list)
    for m in active_before:
        rev_after_to_before[renamer.module(m)].append(m)

    for _, (src, dst) in renamer.relocations.items():
        group = []
        if src in active_before:
            group.append(('B', src))
        if renamer.module(src) in active_after:
            group.append(('A', renamer.module(src)))
        if dst in active_after:
            group.append(('A', dst))
        for bmod in rev_after_to_before.get(dst, ()):
            group.append(('B', bmod))
        for item in group[1:]:
            uf_union(group[0], item)

    for private in renamer.public_from:
        src = FIDELITY.MAP.split_private(private)[0]
        if src in active_before and renamer.module(src) in active_after:
            uf_union(('B', src), ('A', renamer.module(src)))

    comp_before = defaultdict(set)
    comp_after = defaultdict(set)
    for m in active_before:
        comp_before[uf_find(('B', m))].add(m)
    for m in active_after:
        comp_after[uf_find(('A', m))].add(m)
    comp_ids = sorted(comp_before.keys() | comp_after.keys())

    adj = defaultdict(set)
    for cid in comp_ids:
        for m in comp_before[cid]:
            for dep in left['modules'][m]['imports']:
                if dep in active_before:
                    dcid = uf_find(('B', dep))
                    if dcid != cid:
                        adj[cid].add(dcid)
        for m in comp_after[cid]:
            for dep in right['modules'][m]['imports']:
                if dep in active_after:
                    dcid = uf_find(('A', dep))
                    if dcid != cid:
                        adj[cid].add(dcid)

    sccs = _tarjan_sccs(comp_ids, adj)

    global_gen_pairs = {}
    global_aux_pairs = set()
    global_aux_classes = {}
    global_before_aux_rep = {}
    global_after_aux_rep = {}
    global_after_gen = set()

    seen_relocations = set()
    seen_public_from = set()
    ignored_before_all = set()
    ignored_after_all = set()
    component_stats = []
    failures = []
    # The audit trail of every comparison (master ruling R17): each derived
    # respelling (R5 literals, union audit prefixes, R12/R12b drops) and each
    # unhygienic respelling, in component order.
    respelled_all, respelled_seen = [], set()
    unhygienic_all = []

    def update_aux_tables(new_aux_pairs):
        if not new_aux_pairs:
            return
        global_aux_pairs.update(new_aux_pairs)
        parent = {}
        def find_a(x):
            while parent.get(x, x) != x:
                x = parent[x]
            return x
        for a, b in global_aux_pairs:
            global_after_gen.add(b)
            parent.setdefault(a, a)
            parent.setdefault(b, b)
            ra, rb = find_a(a), find_a(b)
            if ra != rb:
                parent[rb] = ra
        rights_by_root = defaultdict(set)
        for _, b in global_aux_pairs:
            rights_by_root[find_a(b)].add(b)
        rep_by_root = {r: min(bs) for r, bs in rights_by_root.items()}
        for a, _ in global_aux_pairs:
            r = find_a(a)
            global_aux_classes[a] = rights_by_root[r]
            global_before_aux_rep[a] = rep_by_root[r]
        for _, b in global_aux_pairs:
            global_after_aux_rep[b] = rep_by_root[find_a(b)]

    for scc in sccs:
        b_mods = set().union(*(comp_before[c] for c in scc))
        a_mods = set().union(*(comp_after[c] for c in scc))
        scoped_relocs = {
            row_old: pair for row_old, pair in renamer.relocations.items()
            if pair[0] in b_mods or renamer.module(pair[0]) in a_mods or pair[1] in a_mods
        }
        scoped_pub = [
            p for p in renamer.public_from
            if FIDELITY.MAP.split_private(p)[0] in b_mods or renamer.module(FIDELITY.MAP.split_private(p)[0]) in a_mods
        ]
        seen_relocations.update(scoped_relocs.keys())
        seen_public_from.update(scoped_pub)

        t0 = time.monotonic()
        before_bundles = {m: FIDELITY.read_exports([before['export_paths'][m]]) for m in sorted(b_mods)}
        after_bundles = {m: FIDELITY.read_exports([after['export_paths'][m]]) for m in sorted(a_mods)}
        before_env = union_environment(before_bundles)
        after_env = union_environment(after_bundles)
        if before_env['version'] is None:
            before_env['version'] = before_ver
        if after_env['version'] is None:
            after_env['version'] = after_ver

        ext_before = {g for g in before_env['constants'] if b_ext_ref_mods.get(g, set()) - b_mods}
        ext_after = {g for g in after_env['constants'] if a_ext_ref_mods.get(g, set()) - a_mods}
        external = dict(
            gen_pairs=global_gen_pairs,
            aux_classes=global_aux_classes,
            before_aux_rep=global_before_aux_rep,
            after_aux_rep=global_after_aux_rep,
            after_gen=global_after_gen,
            referenced_before=ext_before,
            referenced_after=ext_after,
            scoped_relocations=scoped_relocs,
            scoped_public_from=scoped_pub,
        )
        comp_state = {}
        try:
            verdict = FIDELITY.check(
                before_env, after_env, mapping, records, used, collect, plan_edits,
                global_context=global_context, external=external, state=comp_state,
            )
            ign = verdict['ignored_unreferenced_realized_theorems']
            for holder, old, new, reason in verdict['derived_literals_respelled']:
                module = holder if reason == 'union audit module prefix' else b_owners.get(holder)
                row = dict(constant=None if reason == 'union audit module prefix' else holder,
                           module=module, old=old, new=new, reason=reason)
                row_key = json.dumps(row, sort_keys=True, default=str)
                if row_key not in respelled_seen:
                    respelled_seen.add(row_key)
                    respelled_all.append(row)
            unhygienic_all.extend(verdict['unhygienic_respellings'])
            ignored_before_all.update(ign['before'])
            ignored_after_all.update(ign['after'])
            component_stats.append(dict(
                before_modules=sorted(b_mods),
                after_modules=sorted(a_mods),
                size=len(b_mods | a_mods),
                wall_s=round(time.monotonic() - t0, 3),
                rss_mib=round(resource.getrusage(resource.RUSAGE_SELF).ru_maxrss / 1024.0, 2),
                authored_constants=verdict['authored_constants'],
                generated_constants=verdict['generated_constants'],
                ignored_unreferenced_realized_theorems=dict(before=len(ign['before']), after=len(ign['after'])),
            ))
        except FIDELITY.Mismatch as error:
            if not collect:
                raise
            label = ','.join(sorted(b_mods | a_mods))
            failures.append(f'[{label}] {error}')
        finally:
            comp_obj = comp_state.get('comparison')
            if comp_obj is not None:
                for a, b in comp_obj.pairs.items():
                    if a in comp_obj.generated_left:
                        global_gen_pairs[a] = b
                        global_after_gen.add(b)
                update_aux_tables(comp_obj.aux_pairs)
        del before_bundles, after_bundles, before_env, after_env, comp_state
        gc.collect()

    missing_reloc = sorted(set(renamer.relocations) - seen_relocations)
    missing_pub = sorted(set(renamer.public_from) - seen_public_from)
    if missing_reloc or missing_pub:
        msg = f'relocation or promotion outside every active component: {missing_reloc + missing_pub}'
        if not collect:
            raise FIDELITY.Mismatch(msg)
        failures.append(msg)
    if failures:
        raise FIDELITY.Mismatch('\n'.join(failures))
    stale_quotations(records, used)

    result = dict(
        status='OK',
        mode='component-scc',
        scope='candidate-affected-local-closure',
        fast_path_modules=sorted(fast_path),
        active_components=component_stats,
        ignored_unreferenced_realized_theorems=dict(
            before=sorted(ignored_before_all),
            after=sorted(ignored_after_all),
        ),
        before_candidate=left['head'],
        after_candidate=right['head'],
        before_inventory_sha256=sha(FIDELITY.encoded(left).encode()),
        after_inventory_sha256=sha(FIDELITY.encoded(right).encode()),
        affected_modules=sorted(affected),
        excluded_importers=sorted(affected & excluded),
        derived_literals_respelled=respelled_all,
        preresolved_drops=[r for r in respelled_all if r['reason'].startswith('preresolved ')],
        unhygienic_respellings=unhygienic_all,
    )
    if reviewed is not None:
        result['reviewed_quotations'] = dict(sha256=sha(reviewed[0]), records=records)
    return result


def compare(before, after, mapping, inventory=None, reviewed=None, collect=False, plan_edits=None, batch=False):
    """`batch`: the snapshots were read with a subset of environments; the result lists
    the environments compared and the relocation/promotion rows checked, and
    `combine` must show that the batches together cover every environment and row."""
    affected, excluded, renamer, records = _validate_compare_inputs(before, after, mapping, inventory, reviewed)
    left, right = before['candidate'], after['candidate']
    used = set()
    roots = {renamer.module(root): root for root in before['fidelity']}
    if batch and (reviewed is not None or [renamer.module(r) for r in before['all_environments']]
                  != after['all_environments']):
        raise ValueError('a batched compare needs unchanged environment roots and no reviewed quotations')
    if roots.keys() != after['fidelity'].keys():
        if batch:
            raise ValueError('a batched compare needs the same environments on both sides')
        if not any(row['kind'] in ('module', 'relocation') for row in mapping['entries']):
            raise ValueError('capture environment roots changed without module/relocation rows')
        # Relocation may move declarations between independent roots: compare
        # all exported modules as one scope. Constants of independent roots
        # stay keyed per module, and every check, guard and attribute command
        # keeps its module, so unrelated roots are not pooled.
        results = {'<union>': FIDELITY.check(union_environment(before['module_bundles']),
                                             union_environment(after['module_bundles']), mapping,
                                             records, used, collect, plan_edits)}
    else:
        # Module rows rename roots; each environment is compared with its image.
        import gc
        results, failures = {}, []
        # An unrelated executable has no instance of a relocation to verify.
        # Every scoped row must still be checked in at least one environment.
        checked_rows = set()
        scoped = {i for i, row in enumerate(mapping['entries'])
                  if row['kind'] == 'relocation' or 'public_from' in row}
        for root, env in before['fidelity'].items():
            # One environment at a time; its comparison state is released
            # before the next (collect-all semantics unchanged).
            try:
                new_env = after['fidelity'][renamer.module(root)]
                applicable = set()
                for i in scoped:
                    row = mapping['entries'][i]
                    if row['kind'] == 'relocation':
                        src, dst = row['from_module'], row['to_module']
                    else:
                        src = FIDELITY.MAP.split_private(row['public_from'])[0]
                        dst = renamer.module(src)
                    if src in env['modules'] or dst in new_env['modules']:
                        applicable.add(i)
                checked_rows.update(applicable)
                local_map = dict(mapping, entries=[row for i, row in enumerate(mapping['entries'])
                                                   if i not in scoped or i in applicable])
                results[root] = FIDELITY.check(env, new_env, local_map,
                                               records, used, collect, plan_edits)
            except FIDELITY.Mismatch as error:
                if not collect:
                    raise
                failures.append(f'[{root}] {error}')
            gc.collect()
        if scoped - checked_rows and not batch:
            missing = [mapping['entries'][i]['old'] for i in sorted(scoped - checked_rows)]
            failures.append(f'relocation or promotion outside every compared environment: {missing}')
        if failures:
            raise FIDELITY.Mismatch('\n'.join(failures))
        if batch:
            batch_record = dict(environments=sorted(results), all_environments=before['all_environments'],
                                scoped_rows=sorted(scoped), scoped_rows_checked=sorted(checked_rows))
    stale_quotations(records, used)
    result = dict(status='OK', environments=results)
    if batch:
        result['batch'] = batch_record
    if reviewed is not None:
        result['reviewed_quotations'] = dict(sha256=sha(reviewed[0]), records=records)
    result.update(scope='candidate-affected-local-closure',
                  before_candidate=left['head'], after_candidate=right['head'],
                  before_inventory_sha256=sha(FIDELITY.encoded(left).encode()),
                  after_inventory_sha256=sha(FIDELITY.encoded(right).encode()),
                  affected_modules=sorted(affected),
                  excluded_importers=sorted(affected & excluded))
    return result


def combine(batches):
    """Batched compares together: every batch OK on the same snapshots, map and
    plan; their environments partition every maximal environment; every
    relocation or promotion row is checked in at least one environment."""
    keys = ('before_candidate', 'after_candidate', 'before_inventory_sha256', 'after_inventory_sha256',
            'map_sha256', 'before_snapshot_sha256', 'after_snapshot_sha256')
    first = batches[0]
    for b in batches:
        if b.get('status') != 'OK' or 'batch' not in b:
            raise FIDELITY.Mismatch('a batch is not an OK batched compare')
        if any(b.get(k) != first.get(k) for k in keys) or b['batch']['all_environments'] != first['batch']['all_environments'] \
                or b['batch']['scoped_rows'] != first['batch']['scoped_rows']:
            raise ValueError('batches compare different candidates, snapshots or maps')
    seen = [r for b in batches for r in b['batch']['environments']]
    if len(seen) != len(set(seen)) or sorted(seen) != first['batch']['all_environments']:
        raise FIDELITY.Mismatch(f'batches do not partition the environments: missing '
                                f'{sorted(set(first["batch"]["all_environments"]) - set(seen))}, repeated '
                                f'{sorted({r for r in seen if seen.count(r) > 1})}')
    checked = set().union(*(b['batch']['scoped_rows_checked'] for b in batches))
    missing = sorted(set(first['batch']['scoped_rows']) - checked)
    if missing:
        raise FIDELITY.Mismatch(f'relocation or promotion rows outside every compared environment: {missing}')
    return dict({k: first.get(k) for k in keys}, status='OK', batches=len(batches),
                environments=sorted(seen), scoped_rows=len(checked))


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
    cap.add_argument('--reuse', type=Path, action='append',
                     help='prior capture directory (repeatable): reuse each module output whose content key '
                          '(source, import artifact bytes, exporter, toolchain/configuration, schema) is unchanged')
    cap.add_argument('--cache-dir', type=Path,
                     help='content-addressed cache directory shared across captures and worktrees')
    cap.add_argument('--full-elab', action='store_true',
                     help='disable --from-olean fast path and elaborate every module from source')
    cap.add_argument('--full-elab-module', action='append', default=[],
                     help='elaborate this module from source even when --from-olean is enabled')
    cap.add_argument('--tool-root', type=Path,
                     help='Jaune checkout that builds the exporter, for a candidate consuming Jaune as a package')
    cap.add_argument('--tool-build-prefix',
                     help='owned-build argv prefix (JSON) run in --tool-root')
    cap.add_argument('--plan-only', action='store_true',
                     help='capture for rename planning only; implies --full-elab and is refused by compare')
    cap.add_argument('--jobs', type=int, default=1,
                     help='concurrent exporter processes; size the admission command for them')
    comp = commands.add_parser('compare')
    comp.add_argument('--before', type=Path, required=True)
    comp.add_argument('--after', type=Path, required=True)
    comp.add_argument('--map', type=Path, required=True)
    comp.add_argument('--plan', type=Path,
                      help='the whole-tree plan the rename applied: rule E ties each unhygienic respelling to its edit')
    comp.add_argument('--collect-all', action='store_true',
                      help='report every mismatch class in one run (the verdict still fails on any)')
    comp.add_argument('--reviewed-quotations', type=Path,
                      help='scripts/naming-quotations.json: reviewed capture-qualified quotations')
    comp.add_argument('--inventory', type=Path,
                      help='scripts/naming-inventory.json of both candidates: registered exclusions')
    comp.add_argument('--environments', help='comma-separated maximal environments: compare only these '
                      '(a batch); `combine` then checks that the batches cover every environment and row')
    comb = commands.add_parser('combine')
    comb.add_argument('batches', type=Path, nargs='+', help='batched compare outputs')
    args = parser.parse_args()
    try:
        if args.command == 'capture':
            result = capture(args)
        elif args.command == 'combine':
            result = combine([json.loads(b.read_bytes()) for b in args.batches])
        else:
            inventory = None
            if args.inventory:
                raw = args.inventory.read_bytes()
                inventory = (raw, json.loads(raw))
            reviewed = (args.reviewed_quotations.read_bytes(),) if args.reviewed_quotations else None
            edits = None
            if args.plan:
                edits = plan_edits(args.plan.read_bytes(), args.map.read_bytes(), args.before.read_bytes())
            roots = args.environments.split(',') if args.environments else None
            mapping = json.loads(args.map.read_bytes())
            if roots is not None:
                after_roots = [FIDELITY.MAP.Renamer(mapping['entries']).module(r) for r in roots]
                result = compare(read_snapshot(args.before, roots=roots), read_snapshot(args.after, roots=after_roots),
                                 mapping, inventory, reviewed, args.collect_all, edits, batch=True)
            else:
                result = compare_components(read_snapshot(args.before, light=True),
                                            read_snapshot(args.after, light=True),
                                            mapping, inventory, reviewed, args.collect_all, edits)
            result['map_sha256'] = file_sha(args.map)
            result['before_snapshot_sha256'] = file_sha(args.before)
            result['after_snapshot_sha256'] = file_sha(args.after)
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
