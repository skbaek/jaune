#!/usr/bin/env python3
"""Field-reader walk (goal `jaune-shape-and-names-v1`, decision 13 condition 2).

Before a structure field is deleted, report every constant of the built environment that
reads it, separated from writers (structure literals and `{ s with f := ... }`) and from
copies, which are discounted. The Lean half is `scripts/FieldReaders.lean` (executable
`jaune-field-readers`); this driver chooses the environments, runs it through `lake env`,
merges its per-module cache and renders the verdict.

Requires a current owned build of `jaune-field-readers` and of the walked targets
(default: `Jaune JauneChecks Examples Assurance jaune jaune-memory-probe jaune-trace`).
It builds nothing. Results are cached per module, keyed by Lake's trace hash, the query
list and a digest of the tool binary, so a warm run walks only modules whose trace changed.

Verdict per query: `deletable` when no constant outside the deletion set (`--field`
queries plus `--also-deleted`) and outside the generated class reads it; otherwise
`reader exists`. Exit status 0 when every query is deletable, 1 otherwise, 2 on error.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
READ_KINDS = ('projFn', 'proj', 'cases', 'match', 'ref')
ASSURANCE = ['AxiomAudit', 'ExecutionAxioms', 'JauneUnionAxioms', 'UnionAxiomsControls',
             'UnionAxiomsFixture.Good', 'UnionAxiomsFixture.Bad', 'UnionAxiomsFixture.Dep',
             'UnionAxiomsFixture.ViaDep']
SCOPE = ['Jaune', 'JauneChecks', 'Examples', 'Main', 'TraceMain', 'MemoryProbe'] + \
    ['AxiomAudit', 'ExecutionAxioms', 'JauneUnionAxioms', 'UnionAxiomsControls', 'UnionAxiomsFixture']


def library_modules(root):
    mods = []
    for top in ('Jaune', 'Examples'):
        for f in sorted((root / top).rglob('*.lean')):
            mods.append('.'.join(f.relative_to(root).with_suffix('').parts))
    return ['Jaune', 'JauneChecks', 'Examples'] + mods


def default_environments(root):
    """Environments that can be imported together. Executable roots each define `main`,
    and the axiom-audit fixtures may clash, so they get their own environments."""
    envs = [library_modules(root) + ['AxiomAudit', 'ExecutionAxioms', 'JauneUnionAxioms',
                                     'UnionAxiomsControls', 'Main']]
    envs += [['TraceMain'], ['MemoryProbe']]
    envs += [[m] for m in ASSURANCE if m.startswith('UnionAxiomsFixture')]
    return envs


def olean(root, module):
    return root / '.lake/build/lib/lean' / (module.replace('.', '/') + '.olean')


def run_walk(root, exe, cache, salt, scope, queries, imports, lean_path=()):
    cmd = ['lake', 'env', str(exe), '--cache', str(cache), '--salt', salt]
    for s in scope:
        cmd += ['--scope-root', s]
    for q in queries:
        cmd += ['--query', q]
    for m in imports:
        cmd += ['--import', m]
    env = dict(os.environ)
    if lean_path:
        env['LEAN_PATH'] = os.pathsep.join([str(p) for p in lean_path] +
                                           ([env['LEAN_PATH']] if env.get('LEAN_PATH') else []))
    proc = subprocess.run(cmd, cwd=root, capture_output=True, text=True, env=env)
    if proc.returncode != 0:
        raise RuntimeError(f'walk failed ({proc.returncode}): {proc.stderr.strip()[-2000:]}')
    return json.loads(proc.stdout.strip().splitlines()[-1])


def aggregate(cache, modules, queries, deleted):
    per = {q: {'readers': {}, 'writers': {}, 'copies': {}, 'generated': {}, 'in_set': {}}
           for q in queries}
    for m in sorted(modules):
        data = json.loads((cache / f'{m}.json').read_text())
        for e in data['entries']:
            q = e['query']
            if q not in per:
                continue
            row = per[q]
            ident = (e['owner'], e['module'], e['line'], e['kind'])
            if e['class'] == 'generated':
                bucket = row['generated']
            elif e['how'] == 'write':
                bucket = row['writers']
            elif e['how'] == 'copy':
                bucket = row['copies']
            elif e['owner'] in deleted:
                bucket = row['in_set']
            else:
                bucket = row['readers']
            bucket.setdefault(ident, set()).add(e['how'])
    out = {}
    for q, row in per.items():
        rendered = {}
        for name, bucket in row.items():
            rendered[name] = [{'owner': o, 'module': mod, 'line': ln, 'kind': k, 'how': sorted(h)}
                              for (o, mod, ln, k), h in sorted(bucket.items())]
        rendered['verdict'] = 'deletable' if not row['readers'] else 'reader exists'
        out[q] = rendered
    return out


def table(result):
    lines = ['| query | readers | writers | copies | verdict |', '|---|---|---|---|---|']
    for q, r in result.items():
        readers = '; '.join(f"`{x['owner']}` ({x['kind']}, {'/'.join(x['how'])}, {x['module']}:{x['line']})"
                            for x in r['readers']) or '—'
        if r['in_set']:
            readers += ' [in deletion set: ' + ', '.join(f"`{x['owner']}`" for x in r['in_set']) + ']'
        writers = '; '.join(f"`{x['owner']}`" for x in r['writers']) or '—'
        lines.append(f"| `{q}` | {readers} | {writers} | {len(r['copies'])} | {r['verdict']} |")
    return '\n'.join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--field', action='append', default=[], help='fully qualified field or constant')
    ap.add_argument('--fields-file', type=Path, help='one query per line; # comments')
    ap.add_argument('--also-deleted', action='append', default=[],
                    help='a constant deleted together with the queries (its reads are not blocking)')
    ap.add_argument('--root', type=Path, default=ROOT)
    ap.add_argument('--exe', type=Path, help='default: ROOT/.lake/build/bin/jaune-field-readers')
    ap.add_argument('--cache', type=Path, help='default: ROOT/.lake/field-readers-cache')
    ap.add_argument('--env', action='append', default=[],
                    help='comma-separated modules imported together (repeatable); default: the Jaune environments')
    ap.add_argument('--scope-root', action='append', default=[], help='default: the Jaune roots')
    ap.add_argument('--lean-path', action='append', type=Path, default=[],
                    help='extra olean directory (synthetic controls); appended to Lake\'s path')
    ap.add_argument('--json', type=Path, help='write the full result here')
    ap.add_argument('--table', action='store_true', help='print a Markdown table')
    args = ap.parse_args(argv)

    root = args.root.resolve()
    queries = list(args.field)
    if args.fields_file:
        for line in args.fields_file.read_text().splitlines():
            line = line.split('#', 1)[0].strip()
            if line:
                queries.append(line)
    if not queries:
        ap.error('no queries')
    exe = (args.exe or root / '.lake/build/bin/jaune-field-readers').resolve()
    cache = (args.cache or root / '.lake/field-readers-cache').resolve()
    envs = [e.split(',') for e in args.env] or default_environments(root)
    scope = args.scope_root or SCOPE
    if not exe.exists():
        print(f'missing {exe}: run an owned build of jaune-field-readers first', file=sys.stderr)
        return 2
    missing = [m for env in envs for m in env if not olean(root, m).exists() and not args.env]
    if missing:
        print(f'unbuilt modules (owned build first): {missing[:10]}', file=sys.stderr)
        return 2
    salt = hashlib.sha256(exe.read_bytes()).hexdigest()[:16]
    stats, modules, unknown = [], set(), None
    start = time.monotonic()
    try:
        for env in envs:
            s = run_walk(root, exe, cache, salt, scope, queries, env, args.lean_path)
            modules.update(s.pop('modules'))
            here = set(s.pop('unknown'))
            unknown = here if unknown is None else unknown & here
            s['env_head'] = env[0]
            stats.append(s)
    except RuntimeError as e:
        print(e, file=sys.stderr)
        return 2
    wall = time.monotonic() - start
    if unknown:
        print(f'unknown in every environment: {sorted(unknown)}', file=sys.stderr)
        return 2
    result = aggregate(cache, modules, queries, set(queries) | set(args.also_deleted))
    report = {'root': str(root), 'queries': queries, 'also_deleted': args.also_deleted,
              'wall_seconds': round(wall, 2), 'runs': stats, 'modules': len(modules), 'result': result}
    if args.json:
        args.json.write_text(json.dumps(report, indent=1, sort_keys=True))
    if args.table:
        print(table(result))
    walked = sum(s['modules_walked'] for s in stats)
    reused = sum(s['modules_reused'] for s in stats)
    print(f'field-readers: {len(queries)} queries, {len(modules)} modules '
          f'(walked {walked}, reused {reused}), {wall:.1f} s', file=sys.stderr)
    for q, r in result.items():
        print(f'{q}: {r["verdict"]} (readers {len(r["readers"])}, writers {len(r["writers"])}, '
              f'copies {len(r["copies"])}, generated {len(r["generated"])}, in set {len(r["in_set"])})')
    return 0 if all(r['verdict'] == 'deletable' for r in result.values()) else 1


if __name__ == '__main__':
    sys.exit(main())
