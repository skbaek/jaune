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
resolved_out = None
if '--resolved-out' in args:
    idx = args.index('--resolved-out')
    resolved_out = args[idx + 1]
    args = args[:idx] + args[idx + 2:]

if args[0] == '--headers':
    entries = json.loads(Path(args[1]).read_text())
    Path(args[2]).write_text(compact(dict(schema_version=1, lean_version='fake', modules={
        m: dict(path=p, is_module=False, direct_imports=[[i, False, False, False] for i in direct(Path(p).read_text())])
        for m, p in entries})))
    raise SystemExit(0)

if args[0] == '--imports-batch':
    entries = json.loads(Path(args[1]).read_text())
    arts, mods = {}, {}
    for module, source in entries:
        with open(os.environ['FAKE_CALLS'], 'a') as calls:
            calls.write(f'imports {module}\n')
        text = Path(source).read_text()
        imps = closure(text)
        arts.update(imps)
        mods[module] = dict(direct_imports=[[i, False, False, False] for i in direct(text)],
                            import_modules=sorted(imps))
    Path(args[2]).write_text(compact(dict(schema_version=1, lean_version='fake', artifacts=arts, modules=mods)))
    print(f'OK fake imports-batch {len(entries)}')
    raise SystemExit(0)

if args[0] == '--imports':
    mode = 'imports'
    source, module, output = args[1:]
    ilean = None
elif args[0] == '--from-olean':
    mode = 'olean'
    source, module, ilean, output = args[1:]
    if module in {x.strip() for x in os.environ.get('FAKE_OLEAN_EXIT3', '').split(',') if x.strip()}:
        with open(os.environ['FAKE_CALLS'], 'a') as calls:
            calls.write(f'olean-exit3 {module}\n')
        raise SystemExit(3)
else:
    mode = 'export'
    source, module, output = args[-3:]
    ilean = None

with open(os.environ['FAKE_CALLS'], 'a') as calls:
    calls.write(f'{mode} {module}\n')
text = Path(source).read_text()
imports = [[i, False, False, False] for i in direct(text)]
imps = closure(text)
if resolved_out is not None:
    resolved = dict(
        schema_version=1,
        module=module,
        lean_version='fake',
        direct_imports=imports,
        imports=imps,
        own_artifacts=resolve(module) if mode == 'olean' else None,
        ilean=str(Path(ilean).resolve()) if ilean is not None else None,
    )
    Path(resolved_out).write_text(compact(resolved))

if mode == 'imports':
    data = dict(schema_version=1, module=module, lean_version='fake', direct_imports=imports, imports=imps)
else:
    schema = int(os.environ.get('FAKE_SCHEMA', '8'))
    ns_syntax = dict(version=2, commands=[], from_olean=(mode == 'olean'))
    if schema >= 8:
        data = dict(
            schema_version=schema,
            lean_version='fake',
            import_modules=sorted(imps),
            source=text,
            level_pool=[],
            expr_pool=[],
            index=dict(version=5, module=module, directImports=imports, decls={}, references={}, naming_syntax=ns_syntax),
            constants={},
            guards=[],
            attribute_syntax=[],
            checked_commands=[],
        )
    else:
        data = dict(schema_version=schema, lean_version='fake', imports=imps,
                    source=text, index=dict(version=5, module=module, directImports=imports, decls={}, references={}),
                    constants={}, guards=[], attribute_syntax=[], checked_commands=[])
Path(output).write_text(compact(data))
print(f'OK fake {mode} {module}')
