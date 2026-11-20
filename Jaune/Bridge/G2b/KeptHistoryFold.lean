import Jaune.Bridge.G2b.CheckedTop

/-!
# The waiting configured-history theorems over the switched transition (goal
`jaune-shape-and-names-v1`, G2b)

`Staging.KeptStep.of_transition` and `Staging.KeptHistory.of_fold`, moved here unchanged in
name and statement from `Jaune.Bridge.G2b.KeptHistory` when the production transition switched
to `Checked.stateTransitionCoreE`. The waiting step still records the W1 transition, so the
witness now passes through the block bridge `Checked.stateTransitionCoreE_observe`.
-/

namespace Jaune.Staging

theorem KeptStep.of_transition {cfg : ChainConfig} {parent post : BlockChain} {block : Block}
    (h : stateTransitionUsing cfg parent block = .ok post) :
    ∃ fork, KeptStep cfg fork parent block post := by
  unfold stateTransitionUsing at h
  obtain ⟨u, chain, h⟩ := Except.bind_eq_ok h
  cases u
  obtain ⟨fork, hf, h⟩ := Except.bind_eq_ok h
  refine ⟨fork, Except.mapError_eq_ok_iff.mp chain, Except.mapError_eq_ok_iff.mp hf, ?_⟩
  rw [← Checked.stateTransitionCoreE_observe, ← Jaune.stateTransitionScheduledE_eq_ok_iff]
  cases hs : Jaune.stateTransitionScheduledE cfg fork parent block with
  | error err => rw [hs] at h; cases h
  | ok result =>
    rw [hs] at h
    exact congrArg Except.ok (Except.mapError_eq_ok_iff.mp h)

/-- Successful configured transitions are represented at all forks in their original order. -/
theorem KeptHistory.of_fold {cfg : ChainConfig} {start current post : BlockChain}
    {blocks : List KeptBlock} (prior : KeptHistory cfg start blocks current)
    (inputs : List Block) (accepted : inputs.foldlM (stateTransitionUsing cfg) current = .ok post) :
    ∃ suffix, suffix.map KeptBlock.block = inputs ∧ KeptHistory cfg start (blocks ++ suffix) post := by
  induction inputs generalizing current blocks with
  | nil =>
    cases accepted
    exact ⟨[], rfl, by simpa using prior⟩
  | cons first rest ih =>
    obtain ⟨next, step, tail⟩ := Except.bind_eq_ok accepted
    obtain ⟨fork, checkedStep⟩ := KeptStep.of_transition step
    obtain ⟨b, hb, history⟩ := prior.exists_snoc checkedStep
    obtain ⟨suffix, entries, full⟩ := ih history tail
    refine ⟨b :: suffix, by simp [hb, entries], ?_⟩
    simpa only [List.append_assoc, List.singleton_append] using full

end Jaune.Staging
