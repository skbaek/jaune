-- Check/CheckedMessageCall.lean : the guards of `Jaune/Check/MessageCall.lean`, restated over the
-- Checked `resume`.
--
-- Check module (see `scripts/layering.json`). Goal `jaune-shape-and-names-v1`, G2b (unit jsn-u85,
-- S0): the six `resume` guards of `Jaune/Check/MessageCall.lean` over `Checked.resume`, with the
-- same observations and expected values. The saved caller is the empty machine (`Devm`'s default,
-- as `Checked.Message.initialCheckpoint` builds it for a zero grant). A Checked pending record
-- carries only the return target and the new-account charge. The default build compiles this
-- module through `JauneChecks.lean`.
import Jaune.MessageCall.Parts

namespace Jaune

open Jaune

/-- The saved caller and its world, substate and trail: the empty machine. -/
private def resumeCheckSaved : Frame.State :=
  { machine := { stack := [], memory := .empty, gasLeft := 0, returnData := [] }
    world := ⟨.empty, .empty, .emptyWithCapacity⟩
    substate := { logs := [], refund := 0, selfDestructs := .emptyWithCapacity
                  accessedAddresses := .emptyWithCapacity
                  accessedStorageKeys := .emptyWithCapacity }
    trail := { createdAccounts := .emptyWithCapacity } }

private def resumeCheckCreate : Pending := ⟨.create 0, false⟩

private def resumeCheckCall : Pending := ⟨.call 0 0, false⟩

/-- A successful child with the given meter. -/
private def resumeCheckSuccess (meter : StateGasMeter) : Frame.Result :=
  .success [] 0 meter resumeCheckSaved.world resumeCheckSaved.substate resumeCheckSaved.trail

/-- A reverted child with the given meter. -/
private def resumeCheckRevert (meter : StateGasMeter) : Frame.Result :=
  .revert [] 0 meter resumeCheckSaved.trail

private def resumeCheckIsInvariantFault :
    Except Fault (Except (ExceptionalHalt × Frame.State) Frame.State) → Bool
  | .error (.internal (.invariant _)) => true
  | _ => false

private def resumeCheckStack :
    Except Fault (Except (ExceptionalHalt × Frame.State) Frame.State) → Option (List U256)
  | .ok (.ok s) => some s.stack
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
