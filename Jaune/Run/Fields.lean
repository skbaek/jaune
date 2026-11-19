import Jaune.Run.Message

/-!
# What a top-level message run hands on (goal `jaune-shape-and-names-v1`, W2 cut B2)

The transaction and the system calls read a top-level message run through the functions below,
one per value they need. Each is a function of the `MessageRun`, branching on its preparation and
result and, where the two lanes differ, once on the rules' state gas. There is no output record:
`MsgCallOutput` dissolves into these functions (W2 design revision 3, §3.1, the table of output fields).

* A frame that ran reports its result: the world after it, its gas, output and settled halt; on
  success its substate's logs, deletions and (without state gas) touched accounts. With state gas
  it also reports the trail's reads, the world's explicit writes and the state-gas meter.
* A refusal reports the message's state. Without state gas (a creation's address collision) it
  reports nothing else. With state gas (a halt during preparation) it reports the halted machine,
  its state gas restored to the grant and its remaining gas forfeit: its gas, reads and state-gas
  reservoir, and the message's explicit writes.

The refund counter is the one value that can fault: a successful frame whose substate refund is
negative breaks an internal invariant. The transaction reads it first; a system call reads it and
discards it. A run whose preparation is a frame always has a result (`Message.run_result`); the
refund counter of a run without one is an internal fault too, so every function here is total over
every `MessageRun`.

Staged under `Jaune.Staging` beside `MessageRun.output`; a G2a bridge proves that
`MessageRun.output` is these functions assembled.
-/

namespace Jaune

open Jaune


/-- The state-gas rules the message ran under: none before Amsterdam. -/
def TopLevelRun.stateGasRules (run : TopLevelRun) : Option StateGasRules :=
  run.entry.benv.stat.rules.stateGas

/-- The machine a refusal with state gas reports: the halted machine with its state gas restored
to the message's grant and its remaining gas forfeit. -/
def TopLevelRun.refusalMachine (run : TopLevelRun) (halted : Devm) : Devm :=
  (halted.restoreStateGasToEntry run.entry.stateGasGrant).forfeitRemainingGas

/-- The state after the message: the world after the frame, or the message's state for a
refusal. -/
def TopLevelRun.state (run : TopLevelRun) : State :=
  match run.preparation, run.result with
  | .frame f _, some r => (f.worldAfter r).state
  | _, _ => run.entry.benv.state

/-- The execution gas left: the frame's, or a refusal's (none without state gas, the refusal
machine's with it). -/
def TopLevelRun.gasLeft (run : TopLevelRun) : Nat :=
  match run.preparation, run.result with
  | .frame _ _, some r => r.gasLeft
  | .frame _ _, none => 0
  | .refused _ halted, _ =>
    match run.stateGasRules with
    | none => 0
    | some _ => (run.refusalMachine halted).gasLeft

/-- The refund counter: a successful frame's substate refund (an internal fault if negative), a
failed frame's zero, plus without state gas the call's authorization refund; a refusal's zero. -/
def TopLevelRun.refundCounter (run : TopLevelRun) : Except Fault Nat :=
  match run.preparation, run.result with
  | .frame _ authorizationRefund, some r =>
    let refund : Except Fault Nat := match r with
      | .success _ _ _ _ substate _ =>
        (Int.toNat? substate.refund).toExcept
          (Fault.internal (.invariant (.text "refund counter is negative")))
      | _ => .ok 0
    match run.stateGasRules with
    | none => (authorizationRefund + ·) <$> refund
    | some _ => refund
  | .frame _ _, none =>
    -- Unreachable: `Message.run` records a result for every frame (`Message.run_result`).
    .error (.internal (.invariant (.text "message run: a frame without a result")))
  | .refused .., _ => .ok 0

/-- The logs: a successful frame's. -/
def TopLevelRun.logs (run : TopLevelRun) : List Log :=
  match run.preparation, run.result with
  | .frame _ _, some (.success _ _ _ _ substate _) => substate.logs
  | _, _ => []

/-- The accounts to delete: a successful frame's self-destructs. -/
def TopLevelRun.accountsToDelete (run : TopLevelRun) : AdrSet :=
  match run.preparation, run.result with
  | .frame _ _, some (.success _ _ _ _ substate _) => substate.selfDestructs
  | _, _ => .emptyWithCapacity

/-- The settled halt: the frame's, or a refusal's halt; none for a success. -/
def TopLevelRun.error (run : TopLevelRun) : Option SettledHalt :=
  match run.preparation, run.result with
  | .frame _ _, some r => r.error?
  | .frame _ _, none => none
  | .refused reason _, _ => some (.halt reason)

/-- The return data: the frame's output. -/
def TopLevelRun.returnData (run : TopLevelRun) : Bytes :=
  match run.preparation, run.result with
  | .frame _ _, some r => r.output
  | _, _ => []

/-- EIP-161: the accounts a successful frame touched, without state gas. -/
def TopLevelRun.touchedAccounts (run : TopLevelRun) : AdrSet :=
  match run.preparation, run.result with
  | .frame _ _, some (.success _ _ _ _ substate _) =>
    match run.stateGasRules with
    | none => substate.touchedAccounts
    | some _ => .emptyWithCapacity
  | _, _ => .emptyWithCapacity

/-- The state-gas reservoir left, with state gas: the frame's meter, or the refusal machine's. -/
def TopLevelRun.stateGasLeft (run : TopLevelRun) : Nat :=
  match run.stateGasRules with
  | none => 0
  | some _ =>
    match run.preparation, run.result with
    | .frame _ _, some r => r.stateGas.left
    | .frame _ _, none => 0
    | .refused _ halted, _ => (run.refusalMachine halted).stateGasLeft

/-- The net state gas used, with state gas, by a frame: its grant less what it left, plus what
spilled and the committed spill. -/
def TopLevelRun.stateGasUsed (run : TopLevelRun) : Int :=
  match run.stateGasRules with
  | none => 0
  | some _ =>
    match run.preparation, run.result with
    | .frame f _, some r =>
      Int.ofNat f.message.stateGasGrant - Int.ofNat r.stateGas.left +
        Int.ofNat r.stateGas.spilled + Int.ofNat r.stateGas.committedSpill
    | _, _ => 0

/-- EIP-7928, with state gas: the accounts read, from the frame's trail or the refusal machine. -/
def TopLevelRun.accountReads (run : TopLevelRun) : AdrSet :=
  match run.stateGasRules with
  | none => .emptyWithCapacity
  | some _ =>
    match run.preparation, run.result with
    | .frame _ _, some r => r.trail.accountReads
    | .frame _ _, none => .emptyWithCapacity
    | .refused _ halted, _ => (run.refusalMachine halted).meta.accountReads

/-- EIP-7928, with state gas: the storage slots read, from the frame's trail or the refusal
machine. -/
def TopLevelRun.storageReads (run : TopLevelRun) : KeySet :=
  match run.stateGasRules with
  | none => .emptyWithCapacity
  | some _ =>
    match run.preparation, run.result with
    | .frame _ _, some r => r.trail.storageReads
    | .frame _ _, none => .emptyWithCapacity
    | .refused _ halted, _ => (run.refusalMachine halted).meta.storageReads

/-- With state gas, the explicit storage writes that survive: the world's after the frame, or the
message's for a refusal. -/
def TopLevelRun.storageWrites (run : TopLevelRun) : KeySet :=
  match run.stateGasRules with
  | none => .emptyWithCapacity
  | some _ =>
    match run.preparation, run.result with
    | .frame f _, some r => (f.worldAfter r).storageWrites
    | .frame _ _, none => .emptyWithCapacity
    | .refused _ _, _ => run.entry.benv.storageWrites


end Jaune
