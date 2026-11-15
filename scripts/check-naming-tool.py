#!/usr/bin/env python3
"""End-to-end compiler/reference/apply control. Requires built naming exporter.

This elaborates a synthetic Lean fixture: use the host's admission mechanism.
No build is started. All edits are confined to a fresh temporary directory.
"""
import argparse
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location('naming_apply', ROOT / 'scripts/apply-naming-map.py')
APPLY = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(APPLY)


def export(root, source, target, exporter):
    proc = subprocess.run(['lake', 'env', str(exporter), str(source), 'Pilot', str(target)],
                          cwd=root, capture_output=True, text=True)
    target.with_suffix('.log').write_text(proc.stdout + proc.stderr)
    if proc.returncode:
        raise ValueError(f'export failed ({proc.returncode}): {proc.stdout}{proc.stderr}')


def run(directory, exporter):
    source = directory / 'Pilot.lean'
    original = (ROOT / 'scripts/tests/naming/Pilot.lean').read_bytes()
    source.write_bytes(original)
    map_path = directory / 'map.json'
    mapping = dict(schema_version=1, retired_tokens=[], allowed_abbreviations=[], entries=[
        dict(old='Pilot.Tx.gas', new='Pilot.Tx.gasLimit', kind='field', layer='execution',
             rule='2', source='Transaction gasLimit; synthetic shared-field control')])
    map_path.write_text(json.dumps(mapping, indent=2) + '\n')
    export(ROOT, source, directory / 'before.json', exporter)
    plan = APPLY.build_plan(directory, map_path, [('Pilot.lean', 'before.json')])
    (directory / 'plan.json').write_text(json.dumps(plan, indent=2) + '\n')
    if plan['status'] != 'planned':
        raise ValueError(f'unresolved synthetic uses: {plan}')
    tampered = json.loads(json.dumps(plan))
    tampered['files'][0]['edits'][0]['new'] = 'wrong'
    (directory / 'tampered-plan.json').write_text(json.dumps(tampered, indent=2) + '\n')
    controls = []
    try:
        APPLY.apply_plan(directory, tampered, map_path)
    except ValueError as error:
        controls.append(dict(control='tampered-plan', rejection=str(error)))
    else:
        raise ValueError('tampered plan was accepted')
    if source.read_bytes() != original:
        raise ValueError('tampered-plan refusal wrote source')
    changed = APPLY.apply_plan(directory, plan, map_path)
    if changed != 1:
        raise ValueError(f'expected one edited file, got {changed}')
    renamed = source.read_bytes()
    if b'message.gas == 17' not in renamed or b'transaction.gasLimit == 11' not in renamed:
        raise ValueError('shared field distinction lost')
    export(ROOT, source, directory / 'after.json', exporter)
    # Compare resolved constant identities and occurrences, including the field
    # declaration. This tests the renamer; N4 still owns type/value fidelity.
    def counts(path):
        refs = json.loads(path.read_text())['index']['references']
        return {json.loads(key)['c']['n']: len(value['usages']) + (value['definition'] is not None)
                for key, value in refs.items() if 'c' in json.loads(key)}
    before, after = counts(directory / 'before.json'), counts(directory / 'after.json')
    expected = {('Pilot.Tx.gasLimit' if name == 'Pilot.Tx.gas' else name): count
                for name, count in before.items()}
    if expected != after:
        raise ValueError('resolved constant references differ beyond the map')
    # Re-application must fail, without writing anything.
    try:
        APPLY.apply_plan(directory, plan, map_path)
    except ValueError as error:
        controls.append(dict(control='stale-plan', rejection=str(error)))
    else:
        raise ValueError('stale plan was accepted')
    if source.read_bytes() != renamed:
        raise ValueError('stale-plan refusal wrote source')
    # Invert using a newly elaborated bundle, never the old reference offsets.
    row = mapping['entries'][0]
    row['old'], row['new'] = row['new'], row['old']
    map_path = directory / 'inverse-map.json'
    map_path.write_text(json.dumps(mapping, indent=2) + '\n')
    inverse = APPLY.build_plan(directory, map_path, [('Pilot.lean', 'after.json')])
    (directory / 'inverse-plan.json').write_text(json.dumps(inverse, indent=2) + '\n')
    APPLY.apply_plan(directory, inverse, map_path)
    if source.read_bytes() != original:
        raise ValueError('inverse rename did not restore exact bytes')
    (directory / 'controls.json').write_text(json.dumps(controls, indent=2) + '\n')
    return dict(status='OK', edits=len(plan['files'][0]['edits']),
                tx_references=before['Pilot.Tx.gas'], msg_references=before['Pilot.Msg.gas'],
                original_sha256=APPLY.digest(original), renamed_sha256=APPLY.digest(renamed),
                restored_sha256=APPLY.digest(source.read_bytes()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exporter', type=Path, default=ROOT / '.lake/build/bin/jaune-naming-references')
    parser.add_argument('--output', type=Path, help='fresh directory for retained raw evidence')
    args = parser.parse_args()
    start = time.monotonic()
    try:
        if args.output:
            args.output.mkdir(parents=True, exist_ok=False)
            result = run(args.output.resolve(), args.exporter.resolve())
            result['wall_seconds'] = round(time.monotonic() - start, 3)
            (args.output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
        else:
            with tempfile.TemporaryDirectory(prefix='jaune-naming-') as directory:
                result = run(Path(directory), args.exporter.resolve())
        print('OK — naming tool: ' + json.dumps(result, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError) as error:
        print(f'REGRESSION — naming tool: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
