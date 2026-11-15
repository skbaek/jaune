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
`naming-candidate.py capture`.
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


def census(tree, snapshot_path, policy_path, map_path, source_root):
    inventory = json.loads((tree / 'scripts/naming-inventory.json').read_bytes())
    roots = inventory['lint_roots']
    snapshot = json.loads(Path(snapshot_path).read_bytes())
    exports = {snapshot['candidate']['modules'][m]['path']: Path(snapshot_path).parent / row['path']
               for m, row in snapshot['exports'].items()}
    selected = sorted(p for p in exports if any(p.startswith(r + '/') for r in roots))
    mapping = json.loads(Path(map_path).read_bytes())
    policy = json.loads(Path(policy_path).read_bytes())
    result = LINT.check(tree, mapping, policy, source_root, [(p, exports[p]) for p in selected], roots)
    flagged = []
    for problem in result['problems']:
        module = next((m for m, row in snapshot['candidate']['modules'].items()
                       if row['path'] == problem.get('source')), None)
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
    return dict(status='OK', mode='report', scope=result['scope'], roots=roots,
                snapshot_sha256=CANDIDATE.file_sha(snapshot_path),
                policy_sha256=CANDIDATE.file_sha(policy_path), map_sha256=CANDIDATE.file_sha(map_path),
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
    args = parser.parse_args()
    try:
        if args.command == 'vocabulary':
            mapping = json.loads((args.tree / 'scripts/naming-map.json').read_bytes())
            words = vocabulary(args.tree.resolve(), mapping['retired_tokens'])
            args.output.write_text(json.dumps(dict(schema_version=1, words=words, sources={}, bindings={}),
                                              indent=1) + '\n')
            print(f'OK — naming vocabulary: {len(words)} words')
            return 0
        result = census(args.tree.resolve(), args.snapshot, args.policy, args.map, args.source_root.resolve())
        args.output.mkdir(parents=True, exist_ok=False)
        (args.output / 'census.json').write_text(json.dumps(result, indent=1) + '\n')
        with (args.output / 'census.tsv').open('w') as out:
            out.write('module\tname\treason\tsegment\ttokens\n')
            for row in sorted(result['findings'], key=lambda r: (r['module'] or '', r['name'])):
                out.write(f"{row['module']}\t{row['name']}\t{row['reason']}\t{row['segment'] or ''}\t{','.join(row['tokens'])}\n")
        print('OK — naming census: ' + json.dumps(result['summary']['by_reason']))
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'SETUP — naming census: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
