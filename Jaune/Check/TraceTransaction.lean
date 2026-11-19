import Jaune.TraceTransaction
import Jaune.Bridge.G2a.Old.Trace

/-!
# Checks of the traced transaction's settlement (goal `jaune-shape-and-names-v1`, check module)

The EIP-161 sweep guards over the tracer's transaction settlement, moved verbatim out of
`Jaune.TraceTransaction` so that its settlement can wait in the G2a bridge (`Bridge/G2a/Old/Trace`)
while these checks keep running.
-/

namespace Jaune

/-! ### EIP-161: the sweep runs in transaction settlement

`processTransaction_eq` makes `finishTransaction` the public settlement, so
these checks pin that `processTransaction` sweeps the touched accounts its
message call reports: an account holding only storage is erased under Gray
Glacier and kept under Prague. -/

private def TraceTransaction.sweepGuardAdr : Address := 0x2000

private def TraceTransaction.sweepGuardSurvives (fork : Fork) : Bool :=
  let state := State.setStorVal .empty TraceTransaction.sweepGuardAdr 1 1
  let benv : Benv := { (default : Benv) with
    state := state
    stat := { (default : BenvStat) with fork := fork, origState := state } }
  let prepared : Bridge.G2a.Old.TraceTransaction.PreparedTransaction :=
    ⟨benv, .init, 0x5000, 0, 0, 0, default⟩
  let tx : Transaction := {
    nonce := 0
    gasLimit := 0
    value := 0
    data := []
    v := 27
    r := []
    s := []
    type := .legacy 0 (some 0) }
  let out : Bridge.G2a.Old.MessageCallOutput := {
    gasLeft := 0
    refundCounter := 0
    logs := []
    accountsToDelete := .emptyWithCapacity
    error := none
    returnData := []
    touchedAccounts := (.emptyWithCapacity : AdrSet).insert TraceTransaction.sweepGuardAdr }
  match Bridge.G2a.Old.TraceTransaction.finishTransaction prepared tx 0 state out with
  | .ok (post, _) => post[TraceTransaction.sweepGuardAdr]?.isSome
  | .error _ => true

#guard !TraceTransaction.sweepGuardSurvives .grayGlacier
#guard TraceTransaction.sweepGuardSurvives .prague

end Jaune
