import Jaune.FrameRun.Prefix

namespace Examples.CheckedPrefix

open Jaune Jaune

/-- Every same-frame prefix of the checked interpreter, including calls which execute and settle a
child, spends at most the starting machine's gas measure. -/
theorem gasMeasure_le {r s : Frame.Running} (p : Frame.Run.Prefix r s) :
    s.state.machine.gasMeasure ≤ r.state.machine.gasMeasure :=
  Frame.Run.prefix_induction (P := fun x => x.state.machine.gasMeasure ≤ r.state.machine.gasMeasure)
    (fun hs ih => (Frame.Running.step_next_gasMeasure_lt hs).le.trans ih)
    (fun hs child hr ih => (Frame.Running.call_gasMeasure_lt hs child hr).le.trans ih)
    p (Nat.le_refl _)

end Examples.CheckedPrefix
