import Jaune.Transaction

section
open Jaune
namespace Jaune
structure Bridge.G2a.Old.MessageCallOutput : Type where
  gasLeft : Nat
  refundCounter : Int
  logs : List Log
  accountsToDelete : AdrSet
  error: Option SettledHalt
  returnData : Bytes
  /-- State-gas reservoir returned by the top frame. Zero on the legacy path. -/
  stateGasLeft : Nat := 0
  /-- Net state gas consumed by the transaction; refunds may make it negative. -/
  stateGasUsed : Int := 0
  /-- EIP-7928: the accounts the top frame and its children read (goal C).
  Empty on the legacy path and under `rules.bal = none`. -/
  accountReads : AdrSet := .emptyWithCapacity
  /-- EIP-7928: the storage slots read. -/
  storageReads : KeySet := .emptyWithCapacity
  /-- Explicit writes surviving frame rollback and storage deletion. -/
  storageWrites : KeySet := .emptyWithCapacity
  /-- EIP-161: the accounts the transaction touched, for the end-of-transaction
  sweep. Empty when the transaction failed, on the Amsterdam path, and under
  every rule set without `settle.touchedSweep`. -/
  touchedAccounts : AdrSet := .emptyWithCapacity
end Jaune
end

section
open Jaune
namespace Jaune
/-- The refund counter a top-level result reports: a success's substate refund (an internal fault
if negative), a failure's zero. -/
def Bridge.G2a.Old.Frame.Result.refundCounter : Frame.Result → Except EvmError Nat
  | .success _ _ _ _ substate _ =>
    (Int.toNat? substate.refund).toExcept
      (EvmError.internal (.invariant (.text "refund counter is negative")))
  | _ => .ok 0
end Jaune
end

section
open Jaune
namespace Jaune
/-- What a top-level frame hands the transaction under rules without state gas. A call adds its
authorization refund; a failed frame keeps no log, deletion or touch. -/
def Bridge.G2a.Old.Frame.output (f : Frame) (authorizationRefund : Nat) (r : Frame.Result) :
    Except EvmError (Jaune.State × Bridge.G2a.Old.MessageCallOutput) := do
  let refund ← Bridge.G2a.Old.Frame.Result.refundCounter r
  let (logs, accountsToDelete, touchedAccounts) := match r with
    | .success _ _ _ _ substate _ =>
      (substate.logs, substate.selfDestructs, substate.touchedAccounts)
    | _ => ([], .emptyWithCapacity, .emptyWithCapacity)
  .ok ⟨(f.worldAfter r).state, {
    gasLeft := r.gasLeft, refundCounter := authorizationRefund + refund,
    logs := logs, accountsToDelete := accountsToDelete, error := r.error?, returnData := r.output, touchedAccounts := touchedAccounts }⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- What a top-level frame hands the transaction under rules with state gas: the read sets and the
explicit writes in every outcome, the state-gas meter, and no touched accounts. -/
def Bridge.G2a.Old.Frame.outputAmsterdam (f : Frame) (r : Frame.Result) :
    Except EvmError (Jaune.State × Bridge.G2a.Old.MessageCallOutput) := do
  let refundCounter ← Bridge.G2a.Old.Frame.Result.refundCounter r
  let (logs, accountsToDelete) := match r with
    | .success _ _ _ _ substate _ => (substate.logs, substate.selfDestructs)
    | _ => ([], .emptyWithCapacity)
  let stateGasUsed :=
    Int.ofNat f.message.stateGasGrant - Int.ofNat r.stateGas.left +
      Int.ofNat r.stateGas.spilled + Int.ofNat r.stateGas.committedSpill
  .ok ⟨(f.worldAfter r).state, {
    accountReads := r.trail.accountReads
    storageReads := r.trail.storageReads
    storageWrites := (f.worldAfter r).storageWrites
    gasLeft := r.gasLeft
    refundCounter := refundCounter
    logs := logs
    accountsToDelete := accountsToDelete
    error := r.error?
    returnData := r.output
    stateGasLeft := r.stateGas.left
    stateGasUsed := stateGasUsed
  }⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- Settle a top-level Amsterdam message call whose preparation failed before
the interpreter was entered: a halt forfeits the remaining gas and reports the
pre-call state with the reads preparation had already recorded, while every
other error propagates unchanged. The machine's world is not read: the reported
state is the message's. Amsterdam-only, and reached only from
`processTopLevelAmsterdam`'s error branch. -/
def Bridge.G2a.Old.settleTopLevelPreparationFailure (msg : Msg) (error : EvmError)
    (devm : Devm) : Except EvmError (State × Bridge.G2a.Old.MessageCallOutput) :=
  match error with
  | .halt reason =>
    let devm := (devm.restoreStateGasToEntry msg.stateGasGrant).forfeitRemainingGas
    -- The reads the preparation recorded before it halted -- the authorities
    -- of every processed tuple, the recipient once dispatch loaded it -- stay
    -- in the block-level access list: `incorporate_tx_into_block` runs for a
    -- halted transaction too, and a read survives the rollback (EIP-7928).
    .ok ⟨msg.benv.state, {
      accountReads := devm.meta.accountReads
      storageReads := devm.meta.storageReads
      storageWrites := msg.benv.storageWrites
      gasLeft := devm.gasLeft
      refundCounter := 0
      logs := []
      accountsToDelete := .emptyWithCapacity
      error := some (.halt reason)
      returnData := []
      stateGasLeft := devm.stateGasLeft
      stateGasUsed := 0
    }⟩
  | .revert => .error .revert
  | .crypto reason => .error (.crypto reason)
  | .internal reason => .error (.internal reason)
end Jaune
end
