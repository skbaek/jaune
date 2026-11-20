#!/usr/bin/env python3
"""N3 production policy and census.

`vocabulary` regenerates the registered draft word list (`scripts/naming-policy.json`)
from the repository's own English prose: Markdown documents and Lean comments,
with code spans removed. A word must occur at least twice; retired tokens are
never words. The list is a reviewed input to the lint, not proof that a token
is English: review it like any policy change.

`census` runs `check-naming.py` in report mode over every Lean file under the
registered lint roots, using the compiler exports of a candidate capture, and
writes every flagged declaration, field and constructor name (token, name,
module, reason) with summary counts. It needs no Lean: exports come from
`naming-candidate.py capture`. With `--final`, it also enforces pending retired
names and returns the strict whole-tree lint verdict.
"""
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def load(filename):
    spec = importlib.util.spec_from_file_location(filename, ROOT / 'scripts' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


LINT = load('check-naming.py')
CANDIDATE = load('naming-candidate.py')
WORD = re.compile(r"(?<![A-Za-z0-9_'`.])[a-z][a-z]+(?![A-Za-z0-9_`])")


def prose(text, lean):
    if lean:
        chunks = re.findall(r'/-.*?-/', text, re.S) + re.findall(r'--[^\n]*', text)
        text = '\n'.join(chunks)
    else:
        text = re.sub(r'```.*?```', ' ', text, flags=re.S)
    return re.sub(r'`[^`\n]*`', ' ', text)


def vocabulary(tree, retired):
    files = subprocess.check_output(['git', '-C', str(tree), 'ls-files', '*.md', '*.lean']).decode().split()
    counts = Counter()
    for relative in files:
        text = (tree / relative).read_text(encoding='utf-8', errors='replace')
        counts.update(WORD.findall(prose(text, relative.endswith('.lean'))))
    banned = {token.lower() for token in retired}
    return sorted(w for w, n in counts.items() if n >= 2 and w not in banned)


def census(tree, snapshot_path, policy_path, map_path, source_root, final=False):
    inventory = json.loads((tree / 'scripts/naming-inventory.json').read_bytes())
    roots = inventory['lint_roots']
    if final and set(roots) != {'Jaune', 'JauneConsensus'}:
        raise ValueError('final naming census requires both registered product roots')
    snapshot_digest = CANDIDATE.file_sha(snapshot_path)
    snapshot = CANDIDATE.read_snapshot(snapshot_path, fidelity=False, light=True)
    if CANDIDATE.file_sha(snapshot_path) != snapshot_digest:
        raise ValueError('snapshot changed during verification')
    modules = snapshot['candidate']['modules']
    selected = {modules[m]['path']: m for m in snapshot['exports']
                if any(modules[m]['path'].startswith(root + '/') for root in roots)}
    files = [(p, snapshot['export_paths'][selected[p]]) for p in sorted(selected)]
    # Product sources are checked against the bytes actually parsed by the lint below.
    # Other local imports and Lake inputs also affect the names the compiler resolved.
    imports = set(CANDIDATE.closure(modules, sorted(selected.values()))) - set(selected.values())
    inputs = {modules[m]['path'] for m in imports}
    inputs.update(set(snapshot['candidate']['files']) & {'lean-toolchain', 'lakefile.lean', 'lakefile.toml', 'lake-manifest.json'})
    for path in sorted(inputs):
        if CANDIDATE.file_sha(LINT.APPLY.safe_path(tree, path)) != snapshot['candidate']['files'][path]:
            raise ValueError(f'{path}: compiler input differs from capture')
    map_raw = Path(map_path).read_bytes()
    policy_raw = Path(policy_path).read_bytes()
    result = LINT.check(tree, json.loads(map_raw), json.loads(policy_raw), source_root, files, roots, final=final)
    for row in result['files']:
        module = selected[row['source']]
        if (row['source_sha256'] != modules[module]['sha256']
                or row['bundle_sha256'] != snapshot['exports'][module]['sha256']):
            raise ValueError(f'{module}: lint input differs from verified capture')
    flagged = []
    for problem in result['problems']:
        module = selected.get(problem.get('source'))
        flagged.append(dict(name=problem['name'], module=module, source=problem.get('source'),
                            reason=problem['reason'], segment=problem.get('segment'),
                            tokens=problem.get('tokens', [])))
    names = {(row['module'], row['name']) for row in flagged}
    tokens = Counter(token for row in flagged for token in row['tokens'])
    retired = Counter(token for row in flagged if row['reason'] == 'retired token' for token in row['tokens'])
    layer = Counter(('consensus' if (row['source'] or '').startswith('JauneConsensus/') else 'execution')
                    for row in flagged if row['reason'] == 'retired token')
    summary = dict(files=len(result['files']), declarations=sum(r['declarations'] for r in result['files']),
                   findings=len(flagged), flagged_names=len(names),
                   retired_token_names=len({(r['module'], r['name']) for r in flagged if r['reason'] == 'retired token'}),
                   retired_by_layer=dict(layer), retired_tokens=dict(retired.most_common()),
                   unregistered_tokens=len([t for t in tokens if t not in retired]),
                   top_unregistered=dict(Counter({t: n for t, n in tokens.items() if t not in retired}).most_common(60)),
                   by_reason=dict(Counter(row['reason'] for row in flagged)))
    return dict(status=result['status'] if final else 'OK', mode='final' if final else 'report',
                scope=result['scope'], roots=roots, snapshot_sha256=snapshot_digest,
                policy_sha256=hashlib.sha256(policy_raw).hexdigest(), map_sha256=hashlib.sha256(map_raw).hexdigest(),
                summary=summary, findings=flagged)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    v = sub.add_parser('vocabulary')
    v.add_argument('--tree', type=Path, default=ROOT)
    v.add_argument('--output', type=Path, required=True)
    c = sub.add_parser('census')
    c.add_argument('--tree', type=Path, default=ROOT)
    c.add_argument('--snapshot', type=Path, required=True)
    c.add_argument('--policy', type=Path, default=ROOT / 'scripts/naming-policy.json')
    c.add_argument('--map', type=Path, default=ROOT / 'scripts/naming-map.json')
    c.add_argument('--source-root', type=Path, default=ROOT)
    c.add_argument('--output', type=Path, required=True)
    c.add_argument('--final', action='store_true', help='enforce the final whole-tree naming gate')
    args = parser.parse_args()
    try:
        if args.command == 'vocabulary':
            mapping = json.loads((args.tree / 'scripts/naming-map.json').read_bytes())
            words = vocabulary(args.tree.resolve(), mapping['retired_tokens'])
            args.output.write_text(json.dumps(dict(schema_version=1, words=words, sources={}, bindings={}),
                                              indent=1) + '\n')
            print(f'OK — naming vocabulary: {len(words)} words')
            return 0
        result = census(args.tree.resolve(), args.snapshot, args.policy, args.map, args.source_root.resolve(), args.final)
        args.output.mkdir(parents=True, exist_ok=False)
        (args.output / 'census.json').write_text(json.dumps(result, indent=1) + '\n')
        with (args.output / 'census.tsv').open('w') as out:
            out.write('module\tname\treason\tsegment\ttokens\n')
            for row in sorted(result['findings'], key=lambda r: (r['module'] or '', r['name'])):
                out.write(f"{row['module']}\t{row['name']}\t{row['reason']}\t{row['segment'] or ''}\t{','.join(row['tokens'])}\n")
        print(f"{result['status']} — naming census: " + json.dumps(result['summary']['by_reason']))
        return 0 if result['status'] == 'OK' else 1
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'SETUP — naming census: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
