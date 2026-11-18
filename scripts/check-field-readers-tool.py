#!/usr/bin/env python3
"""Control for the field-reader walk (`scripts/field-readers.py`, `scripts/FieldReaders.lean`).

Needs a current owned build of `jaune-field-readers FieldReadersTests`; builds nothing
through Lake. Two parts:

1. Fixture (`scripts/tests/field-readers/FieldReadersFixture.lean`): every reader kind
   (projection function, kernel projection, `casesOn` minor premise, matcher alternative,
   proof body, constant mention) is reported; literals and record updates are writers and
   copies, not readers; a matcher shared by two declarations links each only to the field
   its own alternative uses.
2. Plant: a synthetic module importing the fixture, elaborated with `lake env lean` into a
   fresh directory. With one planted reader of `FRFix.P.c` the verdict is `reader exists`
   naming the plant; with only the plant's line removed it is `deletable` again.

Exit 0 when both parts hold.
"""
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
DRIVER = ROOT / 'scripts' / 'field-readers.py'

EXPECTED = {
    'FRFix.P.a': {
        'readers': {('FRFix.readProj', 'projFn'), ('FRFix.readKernel', 'proj'),
                    ('FRFix.readCases', 'cases'), ('FRFix.readMatch', 'match'),
                    ('FRFix.shareA', 'match')},
        'writers': {'FRFix.mkP'},
        'copies': {'FRFix.setB'},
        'verdict': 'reader exists',
    },
    'FRFix.P.b': {
        'readers': {('FRFix.readThm', 'projFn'), ('FRFix.shareB', 'match'),
                    ('FRFix.useMkP', 'projFn')},
        'writers': {'FRFix.mkP', 'FRFix.setB'},
        'copies': set(),
        'verdict': 'reader exists',
    },
    'FRFix.P.c': {
        'readers': set(),
        'writers': {'FRFix.mkP'},
        'copies': {'FRFix.setB'},
        'verdict': 'deletable',
    },
    'FRFix.mkP': {
        'readers': {('FRFix.useMkP', 'ref')},
        'writers': set(),
        'copies': set(),
        'verdict': 'reader exists',
    },
}

PLANT_LINE = 'def plant (p : FRFix.P) : Nat := p.c  -- PLANT\n'
PLANT_SOURCE = (
    'import FieldReadersFixture\n'
    'namespace FRPlant\n'
    'def other (p : FRFix.P) : Nat := p.a\n'
    + PLANT_LINE +
    'end FRPlant\n')


def walk(work, tag, fields, env, scope, lean_path=None):
    out = work / f'{tag}.json'
    cmd = [sys.executable, str(DRIVER), '--cache', str(work / f'cache-{tag}'), '--json', str(out),
           '--env', env, '--scope-root', scope]
    for f in fields:
        cmd += ['--field', f]
    if lean_path:
        cmd += ['--lean-path', str(lean_path)]
    proc = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    (work / f'{tag}.log').write_text(' '.join(cmd) + '\n' + proc.stdout + proc.stderr)
    if proc.returncode not in (0, 1):
        raise SystemExit(f'{tag}: driver failed ({proc.returncode}): {proc.stderr}')
    return proc.returncode, json.loads(out.read_text())['result']


def check_fixture(work):
    code, result = walk(work, 'fixture', list(EXPECTED), 'FieldReadersFixture', 'FieldReadersFixture')
    failures = []
    for q, exp in EXPECTED.items():
        r = result[q]
        readers = {(x['owner'], h) for x in r['readers'] for h in x['how']}
        got = {'readers': readers, 'writers': {x['owner'] for x in r['writers']},
               'copies': {x['owner'] for x in r['copies']}, 'verdict': r['verdict']}
        for k, v in exp.items():
            if got[k] != v:
                failures.append(f'{q} {k}: expected {sorted(v) if isinstance(v, set) else v}, '
                                f'got {sorted(got[k]) if isinstance(got[k], set) else got[k]}')
    if code != 1:
        failures.append(f'fixture exit {code}, expected 1 (readers exist)')
    return failures


def elaborate(work, tag, source):
    src = work / tag / 'FRPlant.lean'
    src.parent.mkdir(parents=True)
    src.write_text(source)
    olean_dir = work / tag / 'lib'
    olean_dir.mkdir()
    proc = subprocess.run(['lake', 'env', 'lean', '-o', str(olean_dir / 'FRPlant.olean'), str(src)],
                          cwd=ROOT, capture_output=True, text=True)
    if proc.returncode != 0:
        raise SystemExit(f'{tag}: elaboration failed: {proc.stdout}{proc.stderr}')
    return olean_dir


def check_plant(work):
    failures = []
    planted = elaborate(work, 'planted', PLANT_SOURCE)
    code, result = walk(work, 'planted', ['FRFix.P.c'], 'FRPlant', 'FRPlant', planted)
    r = result['FRFix.P.c']
    owners = {x['owner'] for x in r['readers']}
    if r['verdict'] != 'reader exists' or owners != {'FRPlant.plant'} or code != 1:
        failures.append(f'planted: verdict {r["verdict"]}, readers {sorted(owners)}, exit {code}')
    clean_source = PLANT_SOURCE.replace(PLANT_LINE, '')
    assert clean_source != PLANT_SOURCE and len(clean_source) == len(PLANT_SOURCE) - len(PLANT_LINE)
    clean = elaborate(work, 'clean', clean_source)
    code, result = walk(work, 'clean', ['FRFix.P.c'], 'FRPlant', 'FRPlant', clean)
    r = result['FRFix.P.c']
    if r['verdict'] != 'deletable' or r['readers'] or code != 0:
        failures.append(f'clean: verdict {r["verdict"]}, readers {r["readers"]}, exit {code}')
    return failures


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--output', type=Path, help='fresh directory for logs (default: a temporary one)')
    args = ap.parse_args(argv)
    if args.output:
        args.output.mkdir(parents=True)
        work = args.output.resolve()
    else:
        work = Path(tempfile.mkdtemp(prefix='field-readers-'))
    failures = check_fixture(work) + check_plant(work)
    for f in failures:
        print('FAIL', f)
    print(('field-readers control: OK' if not failures else 'field-readers control: FAILED') + f' ({work})')
    return 1 if failures else 0


if __name__ == '__main__':
    sys.exit(main())
