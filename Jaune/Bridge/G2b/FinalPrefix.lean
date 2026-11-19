import Jaune.Bridge.G2b.FinalDerivation
import Jaune.MessageCall.FinalDerivOrder

namespace Jaune

noncomputable def Exec.Deriv.observe (node : Exec.Deriv) (clean : node.devm.output = []) : Staging.Exec.Deriv :=
  ⟨_, _, node.exc.observe clean⟩

/-- Immediate caller continuations lift, including the state restored after a child. -/
theorem Exec.Deriv.ParentStep.observe {next root : Exec.Deriv} (edge : next.ParentStep root)
    (clean : root.devm.output = []) :
    ∃ hc, (next.observe hc).ParentStep (root.observe clean) := by
  cases edge with
  | cont hs next => exact ⟨Evm.next_output_eq_nil hs clean, rfl⟩
  | doneOk hs he hr next =>
    exact ⟨resumeCaller_output_eq_nil (Evm.spawn_legacyOutput_eq_nil hs clean) hr, rfl⟩
  | runOk hs he child hr next =>
    exact ⟨resumeCaller_output_eq_nil (Evm.spawn_legacyOutput_eq_nil hs clean) hr, rfl⟩

/-- Every native continuation of a converted node arises from one old caller edge. -/
theorem Exec.Deriv.observe_parentStep_iff {root : Exec.Deriv}
    (clean : root.devm.output = []) (node : Staging.Exec.Deriv) :
    node.ParentStep (root.observe clean) ↔
      ∃ next : Exec.Deriv, next.ParentStep root ∧ ∃ hc, next.observe hc = node := by
  constructor
  · intro edge
    rcases root with ⟨pc, s, d, out, run⟩
    cases run with
    | halt hs => cases edge
    | cont hs next =>
      have adj := Evm.next_output_eq_nil hs clean
      exact ⟨_, .cont hs next, adj, Option.some.inj edge⟩
    | doneErr hs he hr => cases edge
    | doneOk hs he hr next =>
      have adj := resumeCaller_output_eq_nil (Evm.spawn_legacyOutput_eq_nil hs clean) hr
      exact ⟨_, .doneOk hs he hr next, adj, Option.some.inj edge⟩
    | runErr hs he child hr => cases edge
    | runOk hs he child hr next =>
      have adj := resumeCaller_output_eq_nil (Evm.spawn_legacyOutput_eq_nil hs clean) hr
      exact ⟨_, .runOk hs he child hr next, adj, Option.some.inj edge⟩
  · rintro ⟨next, edge, hc, rfl⟩
    exact (edge.observe clean).choose_spec

/-- A path in the same frame exists exactly when it is the image of an old same-frame path. -/
theorem Exec.Deriv.observe_parentPrefix_iff {start : Exec.Deriv}
    (clean : start.devm.output = []) (node : Staging.Exec.Deriv) :
    (start.observe clean).ParentPrefix node ↔
      ∃ tail : Exec.Deriv, start.ParentPrefix tail ∧ ∃ hc, tail.observe hc = node := by
  constructor
  · intro path
    induction path with
    | refl => exact ⟨_, .refl _, clean, rfl⟩
    | tail path edge ih =>
      obtain ⟨prior, prefixPath, hp, rfl⟩ := ih
      obtain ⟨next, nextOld, hn, rfl⟩ := (observe_parentStep_iff hp _).mp edge
      exact ⟨next, prefixPath.snoc nextOld, hn, rfl⟩
  · rintro ⟨tail, path, ht, rfl⟩
    induction path with
    | refl => exact .refl
    | step edge path ih =>
      obtain ⟨hp, first⟩ := edge.observe clean
      exact Relation.ReflTransGen.head first (ih hp ht)

end Jaune
