#!/usr/bin/env python3
"""Real compiler controls for fidelity; requires host Lean admission, never builds."""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent


def load(filename):
    spec = importlib.util.spec_from_file_location(filename, ROOT / 'scripts' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


CHECK = load('check-naming-fidelity.py')
APPLY = load('apply-naming-map.py')


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def export(source, target, exporter, module='Fidelity'):
    argv = ['lake', 'env', str(exporter), str(source), module, str(target)]
    proc = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
    target.with_suffix('.log').write_text(proc.stdout + proc.stderr)
    save(target.with_suffix('.command.json'), dict(argv=argv, cwd=str(ROOT), exit=proc.returncode))
    if proc.returncode:
        raise ValueError(f'export exit {proc.returncode}: {proc.stdout}{proc.stderr}')


def run(directory, exporter):
    source = directory / 'Fidelity.lean'
    original = (ROOT / 'scripts/tests/naming/Fidelity.lean').read_bytes()
    source.write_bytes(original)
    before = directory / 'before.json'
    export(source, before, exporter)
    mapping = dict(schema_version=1, retired_tokens=[], allowed_abbreviations=[], entries=[
        dict(old='Fidelity.Tx.gas', new='Fidelity.Tx.gasLimit', kind='field', layer='execution',
             rule='2', source='Synthetic shared-field fidelity control')])
    map_path = directory / 'map.json'
    save(map_path, mapping)
    plan = APPLY.build_plan(directory, map_path, [('Fidelity.lean', 'before.json')])
    save(directory / 'plan.json', plan)
    APPLY.apply_plan(directory, plan, map_path)
    renamed = source.read_bytes()
    variants = [('rename', renamed, None),
        ('body', renamed.replace(b'def value : Nat := 7', b'def value : Nat := 8'), 'kernel'),
        ('csimp', renamed.replace(b'@[csimp] ', b''), 'attributes'),
        ('simp', renamed.replace(b'@[simp] ', b''), 'attributes'),
        ('inline', renamed.replace(b'@[inline] ', b''), 'attributes'),
        ('reducibility', renamed.replace(b'@[irreducible] ', b''), 'attributes'),
        ('instance-priority', renamed.replace(b'instance :', b'instance (priority := 50) :'), 'attributes'),
        ('guard', renamed.replace(b'#guard message.gas == 17', b'#guard message.gas == 17 && true'), 'guards'),
        ('drop-guard', renamed.replace(b'#guard message.gas == 17\n', b''), 'guards'),
        ('move-guard', renamed.replace(b'#guard transaction.gasLimit == 11\n', b'').replace(
            b'end Fidelity', b'#guard transaction.gasLimit == 11\nend Fidelity'), None)]
    records = []
    for label, content, expected in variants:
        source.write_bytes(content)
        after = directory / (label + '.json')
        export(source, after, exporter)
        try:
            result = CHECK.check(CHECK.read_exports([before]), CHECK.read_exports([after]), mapping)
        except CHECK.Mismatch as error:
            if expected is None or expected not in str(error):
                raise ValueError(f'{label}: wrong rejection: {error}') from error
            result = dict(status='REGRESSION', rejection=str(error))
        else:
            if expected is not None:
                raise ValueError(f'{label}: mutation escaped the control')
        save(directory / (label + '-verdict.json'), result)
        records.append(dict(control=label, status=result['status']))
        source.write_bytes(original)
        if source.read_bytes() != original:
            raise ValueError('restoration differs from green baseline')
    source.write_bytes(renamed.replace(b'#guard (3 : Nat) == 3\n', b''))
    moved = directory / 'guard-module-main.json'
    export(source, moved, exporter)
    check_source = directory / 'FidelityCheck.lean'
    check_source.write_text('import Lean\n#guard (3 : Nat) == 3\n')
    check_bundle = directory / 'guard-module-check.json'
    export(check_source, check_bundle, exporter, module='FidelityCheck')
    result = CHECK.check(CHECK.read_exports([before]), CHECK.read_exports([moved, check_bundle]), mapping)
    save(directory / 'guard-module-verdict.json', result)
    records.append(dict(control='guard-module-move', status=result['status']))
    source.write_bytes(original)
    array_source = directory / 'ArrayInput.lean'
    array_source.write_text('import Lean\ndef literal : Array Nat := #[1, 2]\n#guard literal.size == 2\n')
    array_bundle = directory / 'array.json'
    export(array_source, array_bundle, exporter, module='ArrayInput')
    array_data = json.loads(array_bundle.read_text())
    if len(array_data['guards']) != 1 or 'literal' not in array_data['constants']:
        raise ValueError('array literal confused command/guard inventory')
    records.append(dict(control='array-literal', status='OK'))
    unsupported = directory / 'Unsupported.lean'
    unsupported.write_text('import Lean\n#guard_expr (1 : Nat) = (1 : Nat)\n')
    try:
        export(unsupported, directory / 'unsupported.json', exporter, module='Unsupported')
    except ValueError as error:
        if 'unsupported hash command' not in str(error):
            raise
        save(directory / 'unsupported-verdict.json', dict(status='REFUSED', rejection=str(error)))
    else:
        raise ValueError('unsupported command was silently omitted')
    records.append(dict(control='unsupported-command', status='REFUSED'))
    return dict(status='OK', controls=records, restored_sha256=APPLY.digest(source.read_bytes()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exporter', type=Path, default=ROOT / '.lake/build/bin/jaune-naming-fidelity')
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    start = time.monotonic()
    try:
        if args.output:
            args.output.mkdir(parents=True, exist_ok=False)
            result = run(args.output.resolve(), args.exporter.resolve())
            result['wall_seconds'] = round(time.monotonic() - start, 3)
            save(args.output / 'result.json', result)
        else:
            with tempfile.TemporaryDirectory(prefix='jaune-fidelity-') as scratch:
                result = run(Path(scratch), args.exporter.resolve())
        print('OK — naming fidelity tool: ' + json.dumps(result, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError) as error:
        print(f'REGRESSION — naming fidelity tool: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
