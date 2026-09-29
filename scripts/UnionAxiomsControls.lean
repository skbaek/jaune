import AxiomAudit
import UnionAxiomsFixture.Good
import UnionAxiomsFixture.Bad
import UnionAxiomsFixture.ViaDep

/-!
# Controls for `#union_axioms_of_modules`

Each control fails the default `Assurance` build if the behaviour it pins
changes, because `#guard_msgs` (or an explicit check) must see exactly the
expected outcome: a compliant population passes, a root reaching a
non-allowed axiom fails and is located, an empty population fails closed, and a
reached constant absent from the environment fails. The fixtures are
`UnionAxiomsFixture.Good` and `UnionAxiomsFixture.Bad`.
-/

open Jaune.AxiomAudit Lean Elab Command

-- A compliant population passes (default allowed set)…
#guard_msgs (drop info) in
#union_axioms_of_modules UnionAxiomsFixture.Good

-- …with exactly the expected union and exactly the module's own constants as roots.
run_cmd do
  let env ← getEnv
  let (roots, mods) := moduleRoots env `UnionAxiomsFixture.Good
  match unionCheck env "Good" roots mods #["propext"] with
  | .error e => throwError "control: expected a pass, got: {e}"
  | .ok r =>
    unless r.axioms == #["propext"] && r.modules == 1 do
      throwError "control: wrong union {r.axioms} / modules {r.modules}"
    unless roots.contains ``goodExt && roots.contains ``GoodTree.node
        && roots.contains ``goodSize && !roots.contains ``badAx do
      throwError "control: unexpected roots {roots}"

-- An explicit allowed list is honoured, and the empty list allows nothing.
#guard_msgs (drop info) in
#union_axioms_of_modules UnionAxiomsFixture.Good [propext]

/--
error: #union_axioms_of_modules: UnionAxiomsFixture.Good reaches axioms outside #[]: #[propext]
  propext <- root goodExt: goodExt -> propext
  propext <- root GoodTree.node.injEq: GoodTree.node.injEq -> Eq.propIntro -> propext
-/
#guard_msgs in
#union_axioms_of_modules UnionAxiomsFixture.Good []

-- A root reaching a non-allowed axiom fails, and the axiom and its roots are named.
/--
error: #union_axioms_of_modules: UnionAxiomsFixture.Bad reaches axioms outside #[Classical.choice, Quot.sound, propext]: #[badAx]
  badAx is itself a root
  badAx <- root viaBad: viaBad -> badAx
  badAx <- root chainedBad: chainedBad -> viaBad -> badAx
-/
#guard_msgs in
#union_axioms_of_modules UnionAxiomsFixture.Bad

-- Axioms outside the population are found across its boundary: `depAx` only
-- through the constructor of an inductive the population mentions, `depAx2`
-- only through a private theorem.
/--
error: #union_axioms_of_modules: UnionAxiomsFixture.ViaDep reaches axioms outside #[Classical.choice, Quot.sound, propext]: #[depAx, depAx2]
  depAx <- root useDep: useDep -> DepInd -> DepInd.mk -> depAx
  depAx2 <- root _private.UnionAxiomsFixture.ViaDep.0.hiddenDep: _private.UnionAxiomsFixture.ViaDep.0.hiddenDep -> depAx2
-/
#guard_msgs in
#union_axioms_of_modules UnionAxiomsFixture.ViaDep

-- An empty population fails closed: no such module, and a name that is only a
-- textual (not component-wise) prefix of a module.
/--
error: #union_axioms_of_modules: no constants found for UnionAxiomsFixture.Nope (0 matching modules, 0 roots); an empty population audits nothing
-/
#guard_msgs in
#union_axioms_of_modules UnionAxiomsFixture.Nope

/--
error: #union_axioms_of_modules: no constants found for UnionAxiomsFixture.Goo (0 matching modules, 0 roots); an empty population audits nothing
-/
#guard_msgs in
#union_axioms_of_modules UnionAxiomsFixture.Goo

-- A reached constant absent from the environment fails and is located.
run_cmd do
  let env ← getEnv
  let (roots, mods) := moduleRoots env `UnionAxiomsFixture.Good
  match unionCheck env "Good" (roots.push `absentConstant) mods
      #["Classical.choice", "Quot.sound", "propext"] with
  | .ok _ => throwError "control: an absent constant was accepted"
  | .error e =>
    unless e.startsWith "#union_axioms_of_modules: Good reaches 1 constants absent from the environment, e.g. #[absentConstant]"
        && (e.splitOn "\n").contains "  absentConstant is itself a root" do
      throwError "control: unexpected failure text: {e}"
