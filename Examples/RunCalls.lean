import Jaune.FrameRun.Entered

/-!
# Calls over a frame run, against the public API (G2b, U102)

A property over `calls` that mentions children that finished at entry, such as precompiles: the
calls of a run are its child frames plus the children answered at entry, and each of the latter
is exactly what `enter` handed back.
-/

namespace Examples.RunCalls

open Jaune

private theorem length_split (cs : List Frame.Run.Call) :
    cs.length = (cs.filter (·.ran.isNone)).length + (cs.filterMap Frame.Run.Call.ran).length := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    cases h : c.ran <;> simp [h, ih] <;> omega

/-- A run makes one call per child frame it runs, plus one per child that finished at entry. -/
theorem calls_length {r : Frame.Running} {out} (t : Frame.Run r (.exit out)) :
    (Frame.Run.calls t).length =
      ((Frame.Run.calls t).filter (·.ran.isNone)).length + ((Frame.Run.frames t).length - 1) := by
  rw [Frame.Run.frames_eq_calls, List.length_cons, Nat.add_sub_cancel]
  exact length_split _

/-- A call that finished at entry, such as a precompile, carries the result `enter` handed back,
and its caller stepped to it. -/
theorem entry_call {r : Frame.Running} {out} {t : Frame.Run r (.exit out)} {c : Frame.Run.Call}
    (hc : c ∈ Frame.Run.calls t) (hdone : c.ran = none) :
    enter c.child = .done c.result ∧
      ∃ pending pc, step c.site.node.start = .ok (.spawn c.child pending pc) :=
  ⟨(Frame.Run.calls_ran_eq_none_iff hc).mp hdone, Frame.Run.calls_step_spawn hc⟩

end Examples.RunCalls
