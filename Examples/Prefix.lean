import Jaune.FrameRun.Prefix

namespace Examples.Prefix

open Jaune Jaune.Staging

/-- Every same-frame prefix, including calls which execute and settle a child, spends
at most the starting machine's gas measure. -/
theorem gasMeasure_le {r s : Frame.Running} (p : Staging.Frame.Run.Prefix r s) :
    s.state.machine.gasMeasure ≤ r.state.machine.gasMeasure :=
  Staging.Frame.Run.prefix_induction (P := fun x => x.state.machine.gasMeasure ≤ r.state.machine.gasMeasure)
    (fun hs ih => (Staging.Frame.Running.step_cont_gasMeasure_lt hs).le.trans ih)
    (fun hs child hr ih => (Staging.Frame.Running.call_gasMeasure_lt hs child hr).le.trans ih)
    p (Nat.le_refl _)

end Examples.Prefix
