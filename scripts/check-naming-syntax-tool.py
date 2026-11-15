#!/usr/bin/env python3
"""Compiler controls for parsed literals and registered audit references; never builds."""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location('naming_fidelity', ROOT / 'scripts/check-naming-fidelity.py')
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)
APPLY = CHECK.APPLY

SOURCE = r'''import AxiomAudit

structure SyntaxProbe.Tx where
  syntaxProbeGas : Nat

def SyntaxProbe.syntaxProbeGas : Nat := 7

def SyntaxProbe.render (t : SyntaxProbe.Tx) : String :=
  s!"syntaxProbeGas 😀 {t.syntaxProbeGas} {s!"syntaxProbeGas {SyntaxProbe.syntaxProbeGas}"} {"syntaxProbeGas"} \{syntaxProbeGas}"

def SyntaxProbe.spaced (t : SyntaxProbe.Tx) := s! "{t.syntaxProbeGas}"
def SyntaxProbe.traced (t : SyntaxProbe.Tx) := dbg_trace "{t.syntaxProbeGas}"; t.syntaxProbeGas

#expect_axioms SyntaxProbe.syntaxProbeGas []
namespace Shadow
def SyntaxProbe.syntaxProbeGas : Nat := 99
#expect_axioms SyntaxProbe.syntaxProbeGas []
end Shadow
#guard SyntaxProbe.syntaxProbeGas == 7
#eval SyntaxProbe.render ⟨3⟩

def SyntaxProbe.lifted (t : SyntaxProbe.Tx) : IO Nat := do
  match (← pure t.syntaxProbeGas) with
  | 0 => pure 0
  | n => pure n

def SyntaxProbe.built (n : Nat) : SyntaxProbe.Tx := SyntaxProbe.Tx.mk (syntaxProbeGas := n)

def SyntaxProbe.punned (syntaxProbeGas : Nat) : SyntaxProbe.Tx := { syntaxProbeGas }

inductive SyntaxProbe.Op where
  | syntaxProbeGas
  | stop

def SyntaxProbe.cost : SyntaxProbe.Op → Nat → Option Nat
  | .syntaxProbeGas, n => some (n + 1)
  | .stop, _ => none

theorem SyntaxProbe.cost_le (o : SyntaxProbe.Op) (n m : Nat)
    (h : SyntaxProbe.cost o n = some m) : m ≤ n + 1 := by
  cases o <;> simp only [SyntaxProbe.cost] at h
  case stop => cases h
  case syntaxProbeGas => simp at h; omega
'''

# A lifted `(← e)` discriminant is one local reference spanning the whole
# expression; it must not cover a token inside it that has no provenance.
HIDDEN = '''
def SyntaxProbe.hidden : IO Nat := do
  let f := fun (syntaxProbeGas : Nat) => syntaxProbeGas
  match (← pure (f (syntaxProbeGas := 2))) with
  | n => pure n
'''


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def run(directory, exporter):
    source = directory / 'SyntaxProvenance.lean'
    source.write_text(SOURCE)
    mapping = dict(schema_version=1, retired_tokens=[], allowed_abbreviations=[], entries=[
        dict(old=a, new=b, kind=kind, layer='execution', rule='4',
             source='Synthetic parser and literal-audit provenance control')
        for a, b, kind in [('SyntaxProbe.syntaxProbeGas', 'SyntaxProbe.syntaxProbeAmount', 'declaration'),
                           ('SyntaxProbe.Tx.syntaxProbeGas', 'SyntaxProbe.Tx.syntaxProbeLimit', 'field')]])
    map_path = directory / 'map.json'
    save(map_path, mapping)

    def export(label):
        target = directory / (label + '.json')
        argv = ['lake', 'env', str(exporter), str(source), 'SyntaxProvenance', str(target)]
        p = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
        (directory / (label + '.log')).write_text(p.stdout + p.stderr)
        save(directory / (label + '.command.json'), dict(argv=argv, cwd=str(ROOT), exit=p.returncode))
        if p.returncode:
            raise ValueError(f'{label}: export failed: {p.stdout}{p.stderr}')
        return target

    try:
        before = export('before')
        plan = APPLY.build_plan(directory, map_path, [(source.name, before.name)])
        save(directory / 'plan.json', plan)
        plan_edits = plan['files'][0]['edits']
        APPLY.apply_plan(directory, plan, map_path)
        renamed = source.read_text()
        if ('#expect_axioms SyntaxProbe.syntaxProbeAmount []' not in renamed or
                'def SyntaxProbe.syntaxProbeGas : Nat := 99' not in renamed or
                's!"syntaxProbeGas 😀 {t.syntaxProbeLimit}' not in renamed):
            raise ValueError('audit shadowing or literal text changed incorrectly')
        if ('match (← pure t.syntaxProbeLimit) with' not in renamed or
                'SyntaxProbe.Tx.mk (syntaxProbeLimit := n)' not in renamed or
                '| .syntaxProbeGas, n =>' not in renamed or
                'case syntaxProbeGas => simp at h; omega' not in renamed or
                '{ syntaxProbeLimit := syntaxProbeGas }' not in renamed):
            raise ValueError('lifted, named-argument or constructor-case provenance changed incorrectly')
        after = export('after')
        verdict = CHECK.check(CHECK.read_exports([before]), CHECK.read_exports([after]), mapping)
        save(directory / 'rename-verdict.json', verdict)
        inverse = copy.deepcopy(mapping)
        for row in inverse['entries']:
            row['old'], row['new'] = row['new'], row['old']
        inverse_path = directory / 'inverse-map.json'
        save(inverse_path, inverse)
        inverse_plan = APPLY.build_plan(directory, inverse_path, [(source.name, after.name)])
        APPLY.apply_plan(directory, inverse_plan, inverse_path)
        # The inverse keeps the field abbreviation expanded (`{ f := f }`).
        if source.read_bytes() != SOURCE.replace('{ syntaxProbeGas }', '{ syntaxProbeGas := syntaxProbeGas }').encode():
            raise ValueError('inverse differs from original bytes (up to the expanded abbreviation)')
        source.write_text(SOURCE.replace('s!"syntaxProbeGas 😀', 's!"changed literal 😀'))
        mutated = export('literal-mutated')
        try:
            CHECK.check(CHECK.read_exports([before]), CHECK.read_exports([mutated]), {**mapping, 'entries': []})
        except CHECK.Mismatch as error:
            if 'constant SyntaxProbe.render.kernel' not in str(error):
                raise ValueError(f'wrong literal rejection: {error}') from error
            save(directory / 'literal-verdict.json', dict(status='REGRESSION', reason=str(error)))
        else:
            raise ValueError('changed literal escaped fidelity')
        override = 'elab_rules : command\n  | `(#expect_axioms $id:ident [ $axs:ident,* ]) => pure ()\n\n'
        source.write_text(SOURCE.replace('#expect_axioms SyntaxProbe.syntaxProbeGas []',
                                        override + '#expect_axioms SyntaxProbe.syntaxProbeGas []', 1))
        overridden = export('replacement-elaborator')
        plan = APPLY.build_plan(directory, map_path, [(source.name, overridden.name)])
        save(directory / 'replacement-plan.json', plan)
        unchanged = source.read_bytes()
        if plan['status'] != 'unresolved':
            raise ValueError('replacement audit elaborator received invented provenance')
        try:
            APPLY.apply_plan(directory, plan, map_path)
        except ValueError:
            pass
        else:
            raise ValueError('unresolved plan applied')
        if source.read_bytes() != unchanged:
            raise ValueError('refused plan wrote source')
        source.write_text(SOURCE + HIDDEN)
        hidden = export('lifted-hidden')
        plan = APPLY.build_plan(directory, map_path, [(source.name, hidden.name)])
        save(directory / 'lifted-hidden-plan.json', plan)
        reasons = [p['reason'] for p in plan['files'][0]['unresolved']]
        if plan['status'] != 'unresolved' or not any('without a constant head' in r for r in reasons):
            raise ValueError(f'token inside a lifted local span was masked: {reasons}')
        return dict(status='OK', rename='OK', inverse_identical=True, edits=len(plan_edits),
                    literal_mutation='REGRESSION', replacement_elaborator='UNRESOLVED',
                    lifted_hidden='UNRESOLVED', refusal_no_writes=True)
    finally:
        source.write_text(SOURCE)
        save(directory / 'restoration.json', dict(identical=source.read_bytes() == SOURCE.encode()))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path)
    parser.add_argument('--exporter', type=Path, default=ROOT / '.lake/build/bin/jaune-naming-fidelity')
    args = parser.parse_args()
    try:
        if args.output:
            args.output.mkdir(parents=True, exist_ok=False)
            result = run(args.output.resolve(), args.exporter.resolve())
            save(args.output / 'result.json', result)
        else:
            with tempfile.TemporaryDirectory(prefix='jaune-syntax-') as tmp:
                result = run(Path(tmp), args.exporter.resolve())
        print('OK — naming syntax controls: ' + json.dumps(result, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError) as error:
        print(f'REGRESSION — naming syntax controls: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
