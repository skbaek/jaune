import Jaune.MessageCall.CheckedSpawnFacts
import Jaune.MessageCall.SpawnFacts
import Jaune.Run.Message

/-!
# The kind coherence of the checked top-level preparation, over the waiting types (G2b N4-0)

The three lemmas that state the checked preparation's kind coherence over `Msg`, `Benv`, `Tenv`
and `Jaune.Frame`. Extracted unchanged from `Jaune.MessageCall.CheckedSpawnFacts`, so that module
no longer imports the waiting interpreter.
-/

section
open Jaune
namespace Jaune.Checked
/-- A prepared creation keeps its code address and a prepared call has one. -/
theorem prepareTopLevelAmsterdam_message {state : StateGasRules} {msg : Msg} {p : Msg × Devm}
    (h : prepareTopLevelAmsterdam state msg = .ok p) :
    p.1.target = msg.target ∧ (msg.target = none → p.1.codeAddress = msg.codeAddress) ∧
      (msg.target ≠ none → p.1.codeAddress ≠ none) := by
  have hcall : ∀ {d : Devm} {p : Msg × Devm}, resolveTopLevelCallAmsterdam msg d = .ok p →
      p.1.target = msg.target ∧ p.1.codeAddress ≠ none := by
    intro d p hc
    unfold resolveTopLevelCallAmsterdam at hc
    obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
    cases hc
    exact ⟨rfl, by simp⟩
  have key : ∀ d1, finishTopLevelAmsterdam state msg d1 = .ok p →
      p.1.target = msg.target ∧ (msg.target = none → p.1.codeAddress = msg.codeAddress) ∧
        (msg.target ≠ none → p.1.codeAddress ≠ none) := by
    intro d1 h
    unfold finishTopLevelAmsterdam dispatchTopLevelAmsterdam at h
    generalize (if msg.tenv.stat.auths.isEmpty then d1 else d1.commitStateGas) = d2 at h
    dsimp only at h
    split at h
    · rename_i hnone
      have ht : msg.target = none := Option.isNone_iff_eq_none.mp hnone
      split at h
      · simp only [reduceCtorEq] at h
      · split at h <;> obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h <;> cases h <;>
          exact ⟨rfl, fun _ => rfl, fun hne => absurd ht hne⟩
    · rename_i hsome
      have ht : msg.target ≠ none := fun e => hsome (by simp [e])
      split at h <;> obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h <;>
        exact ⟨(hcall h).1, fun e => absurd e ht, fun _ => (hcall h).2⟩
  unfold prepareTopLevelAmsterdam at h
  dsimp only at h
  split at h <;> obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h <;> exact key _ h
end Jaune.Checked
end

section
open Jaune
namespace Jaune.Checked
private theorem prepare_amsterdam_coherent {state : StateGasRules} {msg : Msg} {f : Jaune.Frame}
    {refund : Nat} (hcode : msg.codeAddress = none ↔ msg.target = none)
    (h : TopLevel.prepare.amsterdam state msg msg.target.isNone = .ok (.frame f refund)) :
    f.message.KindCoherent := by
  unfold TopLevel.prepare.amsterdam at h
  split at h
  · cases h
  · exact absurd (by assumption) (prepareTopLevelAmsterdam_error_ne_revert _ _ _)
  · cases h
  · cases h
  rename_i prepared d hp
  cases h
  obtain ⟨_, hc, hcall⟩ := prepareTopLevelAmsterdam_message hp
  apply (Message.ofTop_kindCoherent_iff _ _).mpr
  cases ht : msg.target with
  | none => simpa [ht] using (hc ht).trans (hcode.mpr ht)
  | some a => simp [hcall (by simp [ht])]
end Jaune.Checked
end

section
open Jaune
namespace Jaune.Checked
/-- A prepared top-level frame has a creation kind exactly when its code address is absent. -/
theorem TopLevel.prepare_kindCoherent {benv : Benv} {tenv : Tenv} {tx : Transaction} {msg : Msg}
    {f : Jaune.Frame} {refund : Nat} (hm : prepareMessage benv tenv tx = .ok msg)
    (h : TopLevel.prepare msg = .ok (.frame f refund)) : f.message.KindCoherent := by
  have hcode := prepareMessage_codeAddress_eq_none_iff hm
  cases ht : msg.target with
  | none =>
    simp only [TopLevel.prepare, ht, Option.isNone_none, ↓reduceIte, TopLevel.prepare.create] at h
    cases hs : msg.benv.stat.rules.stateGas with
    | none =>
      simp only [hs] at h
      split at h
      · cases h
      · cases h
        exact prepareMessage_create_kindCoherent hm ht
    | some st =>
      simp only [hs] at h
      apply prepare_amsterdam_coherent hcode
      simpa only [ht, Option.isNone_none] using h
  | some a =>
    simp only [TopLevel.prepare, ht, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
      TopLevel.prepare.call] at h
    cases hs : msg.benv.stat.rules.stateGas with
    | none =>
      simp only [hs] at h
      split at h
      · cases h
      · rename_i d refund' ha
        cases h
        exact resolveCodeDelegation_call_kindCoherent
          (Jaune.TopLevel.applyAuthorizations_codeAddress ha (fun eq => by have := hcode.mp eq; simp [ht] at this))
    | some st =>
      simp only [hs] at h
      apply prepare_amsterdam_coherent hcode
      simpa only [ht, Option.isNone_some] using h
end Jaune.Checked
end
