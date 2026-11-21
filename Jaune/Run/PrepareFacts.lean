import Jaune.Run.Message
import Jaune.MessageCall.SpawnFacts

/-!
# The kind coherence of the checked top-level preparation (goal `jaune-shape-and-names-v1`, G2b)

A prepared top-level frame has a creation kind exactly when its code address is absent, given
that the input message has. Native counterpart of the preparation fact that was stated over the
waiting `Msg`, `Benv` and `Tenv`.
-/

namespace Jaune.TopLevel

open Jaune

private theorem authorizationStep_message {auth : Authorization} {input input' : Input}
    {refund refund' : U256} (h : authorizationStep auth input refund = .ok (input', refund')) :
    input'.message = input.message := by
  unfold authorizationStep at h
  repeat' (first | (cases h; done) | dsimp only at h | split at h)
  all_goals (simp only [Except.ok.injEq, Prod.mk.injEq] at h; rw [← h.1])

private theorem authorizationLoop_message :
    ∀ {auths : List Authorization} {input input' : Input} {refund refund' : U256},
      authorizationLoop auths input refund = .ok (input', refund') → input'.message = input.message
  | [], _, _, _, _, h => by cases h; rfl
  | _ :: _, _, _, _, _, h => by
    simp only [authorizationLoop] at h
    obtain ⟨⟨i, r⟩, h1, h⟩ := Except.bind_eq_ok h
    exact (authorizationLoop_message h).trans (authorizationStep_message h1)

private theorem applyAuthorizations_message {input input' : Input} {refund : Nat}
    (h : applyAuthorizations input = .ok (input', refund)) :
    input'.message.kind = input.message.kind ∧ input'.message.codeAddress = input.message.codeAddress := by
  unfold applyAuthorizations at h
  split at h
  · cases h; exact ⟨rfl, rfl⟩
  · obtain ⟨⟨i, r⟩, h1, h⟩ := Except.bind_eq_ok h
    have hm := authorizationLoop_message h1
    dsimp only at h
    split at h
    · cases h
    · rename_i a ha
      cases h
      exact ⟨by simp [hm], by simp [hm]⟩

private theorem resolveCodeDelegation_kindCoherent {input : Input}
    (hk : input.message.kind = .call) (h : input.message.KindCoherent) :
    (resolveCodeDelegation input).message.KindCoherent := by
  unfold resolveCodeDelegation
  dsimp only
  split
  · exact h
  · unfold Message.KindCoherent
    simp [hk]

private theorem dispatchAmsterdam_kindCoherent {rules : StateGasRules} {m message : Message}
    {s s' : Frame.State} (hcoh : m.KindCoherent)
    (hp : dispatchAmsterdam rules m s = .ok (message, s')) : message.KindCoherent := by
  unfold dispatchAmsterdam at hp
  dsimp only at hp
  split at hp
  · split at hp
    · cases hp
    · split at hp <;> obtain ⟨s2, _, hp⟩ := Except.bind_eq_ok hp <;> cases hp <;> exact hcoh
  · rename_i hk
    replace hp : ∃ s2, resolveAmsterdamCall m s2 = .ok (message, s') := by
      split at hp <;> obtain ⟨s2, _, hp⟩ := Except.bind_eq_ok hp <;> exact ⟨_, hp⟩
    obtain ⟨s2, hp⟩ := hp
    unfold resolveAmsterdamCall at hp
    obtain ⟨s3, _, hp⟩ := Except.bind_eq_ok hp
    cases hp
    unfold Message.KindCoherent
    simp [hk]

/-- A prepared top-level frame keeps the kind coherence of its input message: a creation has no
code address and a call has one. -/
theorem prepare_kindCoherent {input : Input} {message : Message} {checkpoint : Frame.State}
    {refund : Nat} (hcoh : input.message.KindCoherent)
    (h : prepare input = .ok (.frame message checkpoint refund)) : message.KindCoherent := by
  unfold prepare at h
  split at h
  · unfold prepareWithoutStateGas at h
    split at h
    · split at h
      · cases h
      · cases h; exact hcoh
    · rename_i hk
      obtain ⟨⟨i, r⟩, h1, h⟩ := Except.bind_eq_ok h
      cases h
      obtain ⟨k, c⟩ := applyAuthorizations_message h1
      apply resolveCodeDelegation_kindCoherent (k.trans hk)
      unfold Message.KindCoherent at hcoh ⊢
      rw [k, c]; exact hcoh
  · split at h
    · rename_i rules m s hp
      cases h
      unfold prepareAmsterdamFrame at hp
      dsimp only at hp
      split at hp <;> obtain ⟨s1, _, hp⟩ := Except.bind_eq_ok hp <;>
        exact dispatchAmsterdam_kindCoherent hcoh hp
    · cases h
    · cases h

end Jaune.TopLevel
