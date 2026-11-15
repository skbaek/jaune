#!/usr/bin/env python3
"""Compiler controls for namespace renames and declaration relocation; never builds.

Two standalone modules elaborate with the fidelity exporter. A namespace row
renames a type and every descendant (`namespace`/`end`/`open ... in`/`export`,
dot notation, a compiler-named instance), a field row overrides one descendant,
and a relocation row moves a documented declaration between the modules. The
whole-tree planner's pure functions plan both files from the real exports; the
renamed files elaborate and N4 compares both modules together, including the
module of every authored constant. A guard moved by hand is still compared as
an expression. Controls: a body change, a guard change and an unrecorded move
fail N4 after successful elaboration; a planned relocation into a target that
does not import a needed module is reported unresolved. A reference that a
bare new name would let another namespace's `U256` capture is qualified
(`ScopeA.U256`). The namespace-only inverse restores the original bytes up to
that kept qualification.
"""
import argparse
import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
SPEC = importlib.util.spec_from_file_location('naming_tree', ROOT / 'scripts/naming-tree.py')
TREE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TREE)
CHECK = TREE.CANDIDATE.FIDELITY
APPLY = TREE.APPLY

SCOPE_A = '''import Lean

namespace ScopeA

structure B256 where
  val : Nat
deriving Repr, DecidableEq

instance : Inhabited B256 := ⟨⟨0⟩⟩

namespace B256
def toNat (x : B256) : Nat := x.val
def ofNat (n : Nat) : B256 := ⟨n⟩
end B256

open B256 in
def twice (x : B256) : Nat := toNat x + x.toNat

export B256 (ofNat)

structure Tx where
  gas : Nat
  to : B256

def mkTx (g : Nat) : Tx := Tx.mk (gas := g) (to := ofNat 1)

/-- A declaration that moves to `ScopeB`; it uses only `Lean`. -/
def moved (n : Nat) : Nat := n * 3

#guard (mkTx 5).gas == 5
#guard twice (ScopeA.B256.ofNat 2) == 4
#guard moved 2 == 6

end ScopeA

namespace ScopeC
open ScopeA
structure U256 where
  w : Nat
-- After the rename a bare `U256` here would denote `ScopeC.U256`.
def pick (x : B256) : Nat := x.toNat
open ScopeA in
def pickIn (x : B256) : Nat := x.toNat
end ScopeC
'''

SCOPE_B = '''import Lean

namespace ScopeB
def base := 1
end ScopeB
'''

ROWS = [('ScopeA.B256', 'ScopeA.U256', 'namespace', {}),
        ('ScopeA.Tx.gas', 'ScopeA.Tx.gasLimit', 'field', {}),
        ('ScopeA.moved', 'ScopeA.moved', 'relocation', dict(from_module='ScopeA', to_module='ScopeB'))]


def save(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def mapping(rows):
    return dict(schema_version=1, retired_tokens=[], allowed_abbreviations=[], entries=[
        dict(old=a, new=b, kind=k, layer='execution', rule='4',
             source='Synthetic namespace and relocation control', **extra) for a, b, k, extra in rows])


class Run:
    def __init__(self, directory, exporter):
        self.directory, self.exporter = directory, exporter

    def export(self, module, label):
        target = self.directory / f'{label}-{module}.json'
        argv = ['lake', 'env', str(self.exporter), str(self.directory / f'{module}.lean'), module, str(target)]
        p = subprocess.run(argv, cwd=ROOT, capture_output=True, text=True)
        (self.directory / f'{label}-{module}.log').write_text(p.stdout + p.stderr)
        save(self.directory / f'{label}-{module}.command.json', dict(argv=argv, cwd=str(ROOT), exit=p.returncode))
        if p.returncode:
            raise ValueError(f'{label} {module}: export failed: {p.stdout}{p.stderr}')
        return target

    def candidate(self):
        modules = {}
        for module in ('ScopeA', 'ScopeB'):
            path = f'{module}.lean'
            digest = APPLY.digest((self.directory / path).read_bytes())
            modules[module] = dict(path=path, sha256=digest, imports=['Lean'], is_module=False)
        return dict(files={r['path']: r['sha256'] for r in modules.values()}, modules=modules,
                    source_dirs=['.'], head='synthetic')

    def plan(self, rows, exports):
        bundles = {}
        for m, p in exports.items():
            data = json.loads(p.read_bytes())
            bundles[m] = dict(source=data['source'], index=data['index'], names=sorted(data['constants']))
        records, moves = TREE.plan_sources(self.directory, self.candidate(), bundles, mapping(rows))
        return records, moves

    def apply(self, records, moves):
        pending, moves = TREE.prepare_writes(self.directory, records, moves)
        return TREE.write(pending, moves)


def run(directory, exporter):
    r = Run(directory, exporter)
    (directory / 'ScopeA.lean').write_text(SCOPE_A)
    (directory / 'ScopeB.lean').write_text(SCOPE_B)
    before = {m: r.export(m, 'before') for m in ('ScopeA', 'ScopeB')}
    # A check of the moving declaration moves by hand (as W0 moves test
    # apparatus); planning first reports the old module's remaining use.
    records, _ = r.plan(ROWS, before)
    reasons = [p['reason'] for row in records for p in row['unresolved']]
    if not any('still uses the moved declaration' in reason for reason in reasons):
        raise ValueError(f'remaining use of the moved declaration not reported: {reasons}')
    guard = '#guard moved 2 == 6\n'
    (directory / 'ScopeA.lean').write_text(SCOPE_A.replace(guard, ''))
    planned = dict(before, ScopeA=r.export('ScopeA', 'unguarded'))
    records, moves = r.plan(ROWS, planned)
    save(directory / 'plan.json', dict(files=records, moves=moves))
    unresolved = [p for row in records for p in row['unresolved']]
    if unresolved:
        raise ValueError(f'unresolved scope plan: {unresolved}')
    r.apply(records, moves)
    a, b = (directory / 'ScopeA.lean').read_text(), (directory / 'ScopeB.lean').read_text()
    expected_a = ['namespace U256', 'end U256', 'open U256 in', 'export U256 (ofNat)', 'to : U256',
                  'Tx.mk (gasLimit := g)', '(mkTx 5).gasLimit', 'ScopeA.U256.ofNat 2', 'x.toNat',
                  'def pick (x : ScopeA.U256)', 'def pickIn (x : ScopeA.U256)']
    if [e for e in expected_a if e not in a] or 'B256' in a or 'def moved' in a:
        raise ValueError(f'namespace or relocation edits wrong:\n{a}')
    if '/-- A declaration that moves to `ScopeB`' not in b or 'namespace ScopeA\n/--' not in b:
        raise ValueError(f'relocated command or its scope wrong:\n{b}')
    # N4 compares the hand-moved guard as an expression across modules.
    (directory / 'ScopeB.lean').write_text(b.replace('end ScopeA\nend\n', guard + 'end ScopeA\nend\n'))
    renamed = {m: (directory / f'{m}.lean').read_bytes() for m in ('ScopeA', 'ScopeB')}
    after = {m: r.export(m, 'after') for m in ('ScopeA', 'ScopeB')}
    left = CHECK.read_exports(list(before.values()))
    verdict = CHECK.check(left, CHECK.read_exports(list(after.values())), mapping(ROWS))
    save(directory / 'verdict.json', verdict)
    controls = []

    def control(label, module, old, new, rows, expected):
        (directory / f'{module}.lean').write_bytes(renamed[module].replace(old, new))
        mutated = dict(after, **{module: r.export(module, label)})
        try:
            CHECK.check(left, CHECK.read_exports(list(mutated.values())), mapping(rows))
        except CHECK.Mismatch as error:
            if expected not in str(error):
                raise ValueError(f'{label}: wrong rejection: {error}') from error
            controls.append(dict(control=label, status='REGRESSION', reason=str(error)))
        else:
            raise ValueError(f'{label}: escaped N4')
        finally:
            (directory / f'{module}.lean').write_bytes(renamed[module])

    control('body', 'ScopeB', b'n * 3', b'3 * n', ROWS, 'kernel')
    control('moved-guard', 'ScopeB', guard.encode(), b'#guard moved 2 == 6 && true\n', ROWS, 'guards')
    control('unrecorded-move', 'ScopeB', b'', b'', ROWS[:2], 'module ScopeA became ScopeB')
    # Relocation into a target that lacks a needed import is reported.
    (directory / 'ScopeA.lean').write_text(SCOPE_A)
    (directory / 'ScopeB.lean').write_text(SCOPE_B)
    needy = [('ScopeA.twice', 'ScopeA.twice', 'relocation', dict(from_module='ScopeA', to_module='ScopeB'))]
    records, _ = r.plan(needy, before)
    reasons = [p['reason'] for row in records for p in row['unresolved']]
    if not any("target ScopeB does not import ['ScopeA']" in reason for reason in reasons):
        raise ValueError(f'missing-import obligation not reported: {reasons}')
    controls.append(dict(control='missing-import', status='UNRESOLVED', reasons=reasons))
    controls.append(dict(control='old-module-still-uses', status='UNRESOLVED'))
    # Namespace-only rename inverts to the original bytes from fresh exports.
    rows = ROWS[:2]
    records, moves = r.plan(rows, before)
    r.apply(records, moves)
    forward = {m: r.export(m, 'namespace-only') for m in ('ScopeA', 'ScopeB')}
    inverse = [(b_, a_, k, extra) for a_, b_, k, extra in rows]
    records, moves = r.plan(inverse, forward)
    r.apply(records, moves)
    # Capture qualification is kept by the inverse (it stays unambiguous).
    qualified = SCOPE_A.replace('def pick (x : B256)', 'def pick (x : ScopeA.B256)').replace(
        'def pickIn (x : B256)', 'def pickIn (x : ScopeA.B256)')
    if (directory / 'ScopeA.lean').read_text() != qualified:
        raise ValueError('namespace inverse did not restore the original bytes up to capture qualification')
    return dict(status='OK', authored_constants=verdict['authored_constants'],
                generated_constants=verdict['generated_constants'], guards=verdict['guards'],
                controls=controls, inverse_identical_up_to_capture_qualification=True)


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
            with tempfile.TemporaryDirectory(prefix='jaune-scope-') as tmp:
                result = run(Path(tmp), args.exporter.resolve())
        print('OK — naming scope controls: ' + json.dumps(result, sort_keys=True))
        return 0
    except (OSError, ValueError, KeyError) as error:
        print(f'REGRESSION — naming scope controls: {error}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
