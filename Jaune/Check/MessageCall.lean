-- Check/MessageCall.lean : executable checks of the four-part message call's `resume`.
--
-- Check module (see `scripts/layering.json`). The guards of the deleted `Resume.run`, formerly
-- in `Jaune/Check/Execution.lean`, restated over `Frame.Result` values (goal
-- `jaune-shape-and-names-v1`, W1 unit L). Six of the seven carry over. The seventh, a failed
-- child with refund 1, has no counterpart: a failed `Frame.Result` carries no refund, so the
-- state it rejected cannot be built. The default build compiles this module through
-- `JauneChecks.lean`.
import Jaune.MessageCall.Resume

namespace Jaune

open Jaune

/-- The saved caller and its world, substate and trail: the default machine. -/
private def resumeCheckSaved : Frame.State := Frame.State.ofDevm default

private def resumeCheckCreate : Pending := ⟨.create 0, false, [], none⟩

private def resumeCheckCall : Pending := ⟨.call 0 0, false, [], none⟩

/-- A successful child with the given meter. -/
private def resumeCheckSuccess (meter : StateGasMeter) : Frame.Result :=
  .success [] 0 meter resumeCheckSaved.world resumeCheckSaved.substate resumeCheckSaved.trail

/-- A reverted child with the given meter. -/
private def resumeCheckRevert (meter : StateGasMeter) : Frame.Result :=
  .revert [] 0 meter resumeCheckSaved.trail

private def resumeCheckIsInvariantFault :
    Except Fault (Except (ExceptionalHalt × Devm) Devm) → Bool
  | .error (.internal (.invariant _)) => true
  | _ => false

private def resumeCheckStack :
    Except Fault (Except (ExceptionalHalt × Devm) Devm) → Option (List U256)
  | .ok (.ok devm) => some devm.stack
  | _ => none

-- Under Amsterdam's rules `resume` rejects a child whose committed spill would otherwise
-- disappear, and a failed child whose meter is not settled. A clean success and a settled
-- failure still reach the merge.
#guard resumeCheckIsInvariantFault <|
  resume amsterdamRules resumeCheckCreate resumeCheckSaved
    (resumeCheckSuccess {StateGasMeter.zero with committedSpill := 1})
#guard resumeCheckIsInvariantFault <|
  resume amsterdamRules resumeCheckCall resumeCheckSaved
    (resumeCheckRevert {StateGasMeter.zero with spilled := 1})
#guard resumeCheckIsInvariantFault <|
  resume amsterdamRules resumeCheckCreate resumeCheckSaved
    (resumeCheckRevert {StateGasMeter.zero with committedSpill := 1})
#guard resumeCheckIsInvariantFault <|
  resume amsterdamRules resumeCheckCreate resumeCheckSaved
    (resumeCheckRevert {StateGasMeter.zero with baseline := 1})
#guard resumeCheckStack
    (resume amsterdamRules resumeCheckCreate resumeCheckSaved
      (resumeCheckSuccess StateGasMeter.zero)) = some [0]
#guard resumeCheckStack
    (resume amsterdamRules resumeCheckCall resumeCheckSaved
      (resumeCheckRevert StateGasMeter.zero)) = some [0]

end Jaune
