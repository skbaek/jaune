#!/usr/bin/env python3
"""Compiler controls for the name lint; needs Lean admission, never builds."""
import argparse
import importlib.util
import json
from pathlib import Path
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parent.parent


def load(filename):
    spec = importlib.util.spec_from_file_location(filename, ROOT / 'scripts' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


LINT = load('check-naming.py')
TOOL = load('check-naming-tool.py')


def save(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')


def run(directory, exporter):
    source = directory / 'Lint.lean'
    original = (ROOT / 'scripts/tests/naming/Lint.lean').read_bytes()
    source.write_bytes(original)
    # Synthetic authority, deliberately not the production vocabulary/registry.
    upstream = b'SLOAD\neth1_data\n'
    (directory / 'source.txt').write_bytes(upstream)
    policy = dict(schema_version=1, words=['account', 'balance', 'gas', 'limit',
        'result', 'success', 'failed', 'context'], sources=dict(fixture=dict(
        path='source.txt', sha256=LINT.sha(upstream), citation='Synthetic source fixture')),
        bindings={
            'Jaune.sload': dict(rule='1', source='fixture', spelling='SLOAD', style='lowerCamel'),
            'JauneConsensus.Context.eth1_data': dict(rule='1', source='fixture', spelling='eth1_data', style='verbatim')})
    mapping = LINT.read_json(ROOT / 'scripts/naming-map.json')
    save(directory / 'policy.json', policy)
    save(directory / 'map.json', mapping)
    controls = []
    for label, old, new in [('green', b'', b''), ('execution', b'gasLimit', b'bal'),
                            ('consensus', b'Context', b'Ctx')]:
        changed = original if not old else original.replace(old, new)
        source.write_bytes(changed)
        bundle = directory / (label + '.json')
        TOOL.export(ROOT, source, bundle, exporter)
        result = LINT.check(directory, mapping, policy, directory,
                            [('Lint.lean', str(bundle))], [])
        save(directory / (label + '-lint.json'), result)
        if label == 'green':
            if result['status'] != 'OK':
                raise ValueError(f'baseline did not pass: {result}')
            names = LINT.declarations(changed.decode(), LINT.read_json(bundle)['index'])
            required = {'Jaune.Account.balance', 'Jaune.Account.gasLimit',
                        'Jaune.Result.success', 'Jaune.Result.failed',
                        'JauneConsensus.Context.eth1_data'}
            if not required.issubset(names):
                raise ValueError(f'compiler omitted field/constructor definitions: {required - names.keys()}')
        elif not any(p['reason'] == 'retired token' and new.decode() in p['tokens'] for p in result['problems']):
            raise ValueError(f'{label}: mutation escaped retired-token control')
        controls.append(dict(control=label, status=result['status'], source_sha256=LINT.sha(changed)))
        source.write_bytes(original)
        if source.read_bytes() != original:
            raise ValueError('restoration differs from green bytes')
    return dict(status='OK', controls=controls, restored_sha256=LINT.sha(source.read_bytes()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exporter', type=Path, default=ROOT / '.lake/build/bin/jaune-naming-references')
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
            with tempfile.TemporaryDirectory(prefix='jaune-naming-lint-') as directory:
                result = run(Path(directory), args.exporter.resolve())
        print('OK — naming lint tool: ' + json.dumps(result, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError) as error:
        print(f'REGRESSION — naming lint tool: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
