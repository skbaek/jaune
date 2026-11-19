import Jaune.Run.Body
import Jaune.Bridge.G2a.Old.Body

section
open Jaune
namespace Jaune.Staging
/-- A configured block transition that succeeds found the active fork and the scheduled
transition's success. -/
theorem stateTransitionUsing_run {cfg : ChainConfig} {ch ch' : BlockChain}
    {block : Block} (h : stateTransitionUsing cfg ch block = .ok ch') :
    ∃ f, cfg.forkAt block.header.number block.header.timestamp = .ok f ∧
      stateTransitionScheduledE cfg f ch block = .ok (.ok ch') := by
  unfold stateTransitionUsing at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨f, hf, h⟩ := Except.bind_eq_ok h
  refine ⟨f, Except.mapError_eq_ok_iff.mp hf, ?_⟩
  cases hs : stateTransitionScheduledE cfg f ch block with
  | error e => rw [hs] at h; cases h
  | ok r =>
    rw [hs] at h
    have hr : r = .ok ch' := Except.mapError_eq_ok_iff.mp h
    rw [hr]
end Jaune.Staging
end
