#!/usr/bin/env python3
"""Fake jaune-naming-fidelity: the same command line and output fields the
capture binds, without Lean. Every run appends `MODE MODULE` to FAKE_CALLS."""
import json
import os
from pathlib import Path
import sys

PARTS = ('olean', 'olean.server', 'olean.private', 'ir.sig', 'ir')


def compact(value):
    return json.dumps(value, separators=(',', ':'), ensure_ascii=False)


def direct(text):
    return [line.split()[1] for line in text.splitlines() if line.startswith('import ')]


def resolve(name):
    for entry in os.environ['LEAN_PATH'].split(':'):
        root = Path(entry)
        if (root / name.split('.')[0]).is_dir() or (root / (name.split('.')[0] + '.olean')).exists():
            olean = root.joinpath(*name.split('.')).with_suffix('.olean')
            return {part: str(olean.with_suffix('.' + part)) if olean.with_suffix('.' + part).exists() else None
                    for part in PARTS}
    raise SystemExit(f'unknown import {name}')


def closure(text):
    seen, todo = {'Init'}, direct(text)
    while todo:
        name = todo.pop()
        if name not in seen:
            seen.add(name)
            todo += direct(Path(name.replace('.', '/') + '.lean').read_text())
    return {name: resolve(name) for name in sorted(seen)}


args = sys.argv[1:]
if args[0] == '--headers':
    entries = json.loads(Path(args[1]).read_text())
    Path(args[2]).write_text(compact(dict(schema_version=1, lean_version='fake', modules={
        m: dict(path=p, is_module=False, direct_imports=[[i, False, False, False] for i in direct(Path(p).read_text())])
        for m, p in entries})))
    raise SystemExit(0)
mode = 'imports' if args[0] == '--imports' else 'export'
source, module, output = args[-3:]
with open(os.environ['FAKE_CALLS'], 'a') as calls:
    calls.write(f'{mode} {module}\n')
text = Path(source).read_text()
imports = [[i, False, False, False] for i in direct(text)]
if mode == 'imports':
    data = dict(schema_version=1, module=module, lean_version='fake', direct_imports=imports, imports=closure(text))
else:
    data = dict(schema_version=int(os.environ.get('FAKE_SCHEMA', '7')), lean_version='fake', imports=closure(text),
                source=text, index=dict(module=module, directImports=imports, decls={}), constants={})
Path(output).write_text(compact(data))
print(f'OK fake {mode} {module}')
