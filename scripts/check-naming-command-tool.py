#!/usr/bin/env python3
"""Compiler controls for message and axiom checks; requires Lean admission."""
import argparse
import importlib.util
import json
from pathlib import Path
import tempfile
import sys

ROOT = Path(__file__).resolve().parent.parent


def load(filename):
    spec = importlib.util.spec_from_file_location(filename, ROOT / 'scripts' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


TOOL = load('check-naming-fidelity-tool.py')
CHECK = TOOL.CHECK

SOURCE = '''import Lean
import AxiomAudit
import UnionAxiomsFixture.Good
import Mathlib.Util.CountHeartbeats
namespace CommandFidelity
macro "repeat_check " n:num : command => do
  let command ← `(command| #guard_msgs in #guard true)
  return ⟨Lean.mkNullNode (Array.replicate n.getNat command.raw)⟩
repeat_check 2
def old : Nat := 1
def other : Nat := 1
#eval old
#count_heartbeats in
example : old = 1 := rfl
run_cmd do
  unless 1 == 1 do throwError "control"
#expect_axioms CommandFidelity.old []
#union_axioms_of_modules UnionAxiomsFixture.Good [propext]
#guard_msgs in
#guard old == 1
/-- error: Tactic `decide` proved that the proposition
  False
is false -/
#guard_msgs in
example : False := by decide
end CommandFidelity
'''


def run(directory, exporter):
    source = directory / 'CommandFidelity.lean'
    source.write_text(SOURCE)
    before = directory / 'before.json'
    TOOL.export(source, before, exporter, 'CommandFidelity')
    baseline = CHECK.read_exports([before])
    if len(baseline['checks']) < 8 or baseline['guards']:
        raise ValueError('message checks or audit commands were omitted/double-counted')
    mapping = dict(schema_version=1, retired_tokens=[], allowed_abbreviations=[], entries=[
        dict(old='CommandFidelity.old', new='CommandFidelity.renamed', kind='declaration',
             layer='execution', rule='4', source='Compiler checked-command control')])
    TOOL.save(directory / 'map.json', mapping)
    renamed = SOURCE.replace('def old', 'def renamed').replace('CommandFidelity.old',
        'CommandFidelity.renamed').replace('#guard old', '#guard renamed').replace('#eval old', '#eval renamed').replace('example : old', 'example : renamed')
    variants = [
        ('rename', renamed, None),
        ('macro-multiplicity', renamed.replace('repeat_check 2', 'repeat_check 1'), 'checks'),
        ('eval-expression', renamed.replace('#eval renamed', '#eval (renamed + 0)'), 'checks'),
        ('drop-heartbeat-wrapper', renamed.replace('#count_heartbeats in\n', ''), 'checks'),
        ('run-command', renamed.replace('unless 1 == 1', 'unless 2 == 2'), 'checks'),
        ('drop-audit', renamed.replace('#expect_axioms CommandFidelity.renamed []\n', ''), 'checks'),
        ('retarget-audit', renamed.replace('#expect_axioms CommandFidelity.renamed []',
                                         '#expect_axioms CommandFidelity.other []'), 'checks'),
        ('widen-union', renamed.replace('[propext]', '[propext, Classical.choice]'), 'checks'),
        ('guarded-expression', renamed.replace('#guard renamed == 1',
                                              '#guard renamed == 1 && true'), 'checks'),
        ('message-options', renamed.replace('#guard_msgs in\n#guard',
                                            '#guard_msgs (drop info) in\n#guard'), 'checks'),
        ('message-filter', renamed.replace('#guard_msgs in\nexample',
                                           '#guard_msgs (whitespace := lax) in\nexample'), 'checks'),
    ]
    results = []
    try:
        for label, content, expected in variants:
            source.write_text(content)
            after = directory / (label + '.json')
            TOOL.export(source, after, exporter, 'CommandFidelity')
            try:
                result = CHECK.check(baseline, CHECK.read_exports([after]), mapping)
            except CHECK.Mismatch as error:
                if expected is None or expected not in str(error):
                    raise ValueError(f'{label}: wrong rejection: {error}') from error
                result = dict(status='REGRESSION', rejection=str(error))
            else:
                if expected is not None:
                    raise ValueError(f'{label}: change escaped comparison')
            TOOL.save(directory / (label + '-verdict.json'), result)
            results.append(dict(control=label, status=result['status']))
    finally:
        source.write_text(SOURCE)
    if source.read_text() != SOURCE:
        raise ValueError('control source restoration differs')
    return dict(status='OK', controls=results,
                restored_sha256=TOOL.APPLY.digest(source.read_bytes()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--exporter', type=Path, default=ROOT / '.lake/build/bin/jaune-naming-fidelity')
    args = parser.parse_args()
    try:
        if args.output:
            args.output.mkdir(parents=True, exist_ok=False)
            result = run(args.output.resolve(), args.exporter.resolve())
            TOOL.save(args.output / 'result.json', result)
        else:
            with tempfile.TemporaryDirectory(prefix='jaune-command-fidelity-') as tmp:
                result = run(Path(tmp), args.exporter.resolve())
        print('OK — checked-command fidelity: ' + json.dumps(result, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError) as error:
        print(f'REGRESSION — checked-command fidelity: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
