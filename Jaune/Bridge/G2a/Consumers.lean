import Jaune.Bridge.G2a.Run
import Jaune.Run.Settle
import Jaune.Run.SystemCall

/-!
# W2 cut B2: bridges (goal `jaune-shape-and-names-v1`, gate G2a, bridge)

The consumers of the top-level message call read the `MessageRun` through its functions
(`Jaune.Run.Fields`); `MsgCallOutput` is no longer handed on. Old side = the definitions at
`ba15f397` (`Jaune.Transaction`), unedited, and for the transaction also cut A's staged
`Staging.processTransaction` (`Jaune.Run.Transaction`). New side = `Jaune.Run.Settle` and
`Jaune.Run.SystemCall`.

* `MessageRun.output_eq`: W2-1's rendering `MessageRun.output` is the run's functions assembled,
  for every run. `outputOf` is that assembly, and exists only for the bridge.
* Consumers whose type survives (every input, the whole result, rejection text included):
  `processTransaction`, `runRequestContracts`, `processGeneralPurposeRequestsAt`,
  `processGeneralPurposeRequests`, `beaconRootsCall`, `historyStorageCall`.
* Consumers whose type changes (the run replaces the state and output pair), through the output
  map `render`: `processSystemTransaction`, `processUncheckedSystemTransaction`,
  `processCheckedSystemTransaction`.
-/

namespace Jaune.Bridge.G2a

open Jaune

/-! ### The run's functions assembled are W2-1's rendering -/

/-- The output record the run's functions assemble, given its refund counter. Bridge only. -/
def outputOf (run : Staging.MessageRun) (refundCounter : Nat) : MsgCallOutput :=
  { gasLeft := run.gasLeft
    refundCounter := refundCounter
    logs := run.logs
    accountsToDelete := run.accountsToDelete
    error := run.error
    returnData := run.returnData
    stateGasLeft := run.stateGasLeft
    stateGasUsed := run.stateGasUsed
    accountReads := run.accountReads
    storageReads := run.storageReads
    storageWrites := run.storageWrites
    touchedAccounts := run.touchedAccounts }

/-- **The output square.** For every run, W2-1's rendering is the run's refund counter, then the
state and the output the run's functions assemble. -/
theorem MessageRun.output_eq (run : Staging.MessageRun) :
    run.output = (do
      let n ← run.refundCounter.mapError Fault.toEvmError
      pure (run.state, outputOf run n)) := by
  obtain ⟨entry, prep, root, result⟩ := run
  cases prep with
  | refused reason halted =>
    cases hs : entry.benv.stat.rules.stateGas <;>
      simp [Staging.MessageRun.output, Staging.MessageRun.refundCounter, outputOf,
        settleTopLevelPreparationFailure, Staging.MessageRun.state, Staging.MessageRun.gasLeft,
        Staging.MessageRun.logs, Staging.MessageRun.accountsToDelete, Staging.MessageRun.error,
        Staging.MessageRun.returnData, Staging.MessageRun.stateGasLeft,
        Staging.MessageRun.stateGasUsed, Staging.MessageRun.accountReads,
        Staging.MessageRun.storageReads, Staging.MessageRun.storageWrites,
        Staging.MessageRun.touchedAccounts, Staging.MessageRun.stateGasRules,
        Staging.MessageRun.refusalMachine, hs, bind, Except.bind, Except.mapError, pure,
        Except.pure]
  | frame f a =>
    cases result with
    | none => rfl
    | some r =>
      cases hs : entry.benv.stat.rules.stateGas <;> cases r <;>
        simp [Staging.MessageRun.output, Staging.MessageRun.refundCounter, outputOf,
          Frame.output, Frame.outputAmsterdam, Frame.Result.refundCounter,
          Staging.MessageRun.state, Staging.MessageRun.gasLeft,
          Staging.MessageRun.logs, Staging.MessageRun.accountsToDelete, Staging.MessageRun.error,
          Staging.MessageRun.returnData, Staging.MessageRun.stateGasLeft,
          Staging.MessageRun.stateGasUsed, Staging.MessageRun.accountReads,
          Staging.MessageRun.storageReads, Staging.MessageRun.storageWrites,
          Staging.MessageRun.touchedAccounts, Staging.MessageRun.stateGasRules, hs, bind,
          Except.bind, Except.mapError, pure, Except.pure]
      all_goals
        rename_i _ _ _ _ substate _
        cases substate.refund.toNat? <;> rfl

/-- The state and output pair the old system calls returned, read from a run: the output map of
the system-call bridges. A system call returns only runs whose refund counter is a number
(`Staging.processSystemTransaction` reads it), which is the counter rendered. Bridge only. -/
def render (run : Staging.MessageRun) : State × MsgCallOutput :=
  (run.state, outputOf run (match run.refundCounter with | .ok n => n | .error _ => 0))

/-! ### System calls -/

/-- **Bridge at `processSystemTransaction`** (output map `render`). For every block environment,
target, code and data, the old call's result is the staged run rendered, faults included. -/
theorem processSystemTransaction_eq (benv : Benv) (target : Address) (code : ByteArray)
    (data : Bytes) :
    processSystemTransaction benv target code data =
      render <$> (Staging.processSystemTransaction benv target code data).mapError
        Fault.toEvmError := by
  unfold processSystemTransaction Staging.processSystemTransaction
  rw [← processMessageCall_eq]
  unfold Staging.processMessageCall
  dsimp only
  generalize Staging.Message.run _ = x
  cases x with
  | error e => rfl
  | ok run =>
    simp only [bind, Except.bind, Except.mapError]
    rw [MessageRun.output_eq]
    cases hr : run.refundCounter <;> simp [Except.mapError, bind, Except.bind, pure, Except.pure,
      Functor.map, Except.map, render, hr]

/-- **Bridge at `processUncheckedSystemTransaction`** (output map `render`). -/
theorem processUncheckedSystemTransaction_eq (benv : Benv) (target : Address) (data : Bytes) :
    processUncheckedSystemTransaction benv target data =
      render <$> (Staging.processUncheckedSystemTransaction benv target data).mapError
        Fault.toEvmError :=
  processSystemTransaction_eq _ _ _ _

/-- **Bridge at `processCheckedSystemTransaction`** (output map `render`), rejection text
included. -/
theorem processCheckedSystemTransaction_eq (benv : Benv) (target : Address) (data : Bytes) :
    processCheckedSystemTransaction benv target data =
      render <$> Staging.processCheckedSystemTransaction benv target data := by
  unfold processCheckedSystemTransaction Staging.processCheckedSystemTransaction
  by_cases hc : (benv.state.getCode target).isEmpty
  · simp [hc, bind, Except.bind, Functor.map, Except.map]
  · simp only [hc, Bool.false_eq_true, ↓reduceIte]
    rw [processSystemTransaction_eq]
    cases Staging.processSystemTransaction benv target (benv.state.getCode target) data with
    | error e => rfl
    | ok run =>
      cases he : run.error <;>
        simp [bind, Except.bind, Except.mapError, Functor.map, Except.map,
          render, outputOf, he]

/-- **Bridge at `runRequestContracts`.** Every index, contract list, block environment,
accumulator and builder; the whole result. -/
theorem runRequestContracts_eq (idx : Nat) (contracts : List (UInt8 × Address)) (benv : Benv)
    (acc : List Bytes) (bal : BlockAccessListBuilder) :
    Staging.runRequestContracts idx contracts benv acc bal =
      runRequestContracts idx contracts benv acc bal := by
  induction contracts generalizing benv acc bal with
  | nil => rfl
  | cons c rest ih =>
    obtain ⟨requestType, address⟩ := c
    simp only [Staging.runRequestContracts, runRequestContracts,
      processCheckedSystemTransaction_eq]
    cases Staging.processCheckedSystemTransaction benv address [] with
    | error e => rfl
    | ok run =>
      simp only [bind, Except.bind, Functor.map, Except.map, render, outputOf]
      exact ih _ _ _

/-- **Bridge at `processGeneralPurposeRequestsAt`.** -/
theorem processGeneralPurposeRequestsAt_eq (balIndex : Nat) (benv : Benv) (bout : BlockOutput) :
    Staging.processGeneralPurposeRequestsAt balIndex benv bout =
      processGeneralPurposeRequestsAt balIndex benv bout := by
  simp only [Staging.processGeneralPurposeRequestsAt, processGeneralPurposeRequestsAt,
    runRequestContracts_eq]

/-- **Bridge at `processGeneralPurposeRequests`.** -/
theorem processGeneralPurposeRequests_eq (benv : Benv) (bout : BlockOutput) :
    Staging.processGeneralPurposeRequests benv bout = processGeneralPurposeRequests benv bout :=
  processGeneralPurposeRequestsAt_eq _ _ _

/-- **Bridge at `beaconRootsCall`.** Every rule set and block environment; the whole result. -/
theorem beaconRootsCall_eq (rules : ForkRules) (benv : Benv) :
    Staging.beaconRootsCall rules benv = beaconRootsCall rules benv := by
  unfold Staging.beaconRootsCall beaconRootsCall
  split
  · rw [processUncheckedSystemTransaction_eq]
    cases Staging.processUncheckedSystemTransaction benv beaconRootsAddress
        benv.stat.parentBeaconBlockRoot.toBytes <;> rfl
  · rfl

/-- **Bridge at `historyStorageCall`.** Every rule set, block environment and builder; the whole
result. -/
theorem historyStorageCall_eq (rules : ForkRules) (benv : Benv) (bal : BlockAccessListBuilder) :
    Staging.historyStorageCall rules benv bal = historyStorageCall rules benv bal := by
  unfold Staging.historyStorageCall historyStorageCall
  split
  · cases benv.stat.blockHashes.getLast? with
    | none => rfl
    | some lastHash =>
      simp only [Option.toExcept, bind, Except.bind]
      rw [processUncheckedSystemTransaction_eq]
      cases Staging.processUncheckedSystemTransaction benv historyStorageAddress
          lastHash.toBytes <;> rfl
  · rfl

/-! ### The transaction -/

/-- Settling a run whose refund counter is `n` is cut A's settlement of its state and assembled
output. -/
theorem Transaction.settle_eq (prepared : Staging.Transaction.Prepared) (tx : Transaction)
    (index : Nat) (run : Staging.MessageRun) {n : Nat} (hn : run.refundCounter = .ok n) :
    Staging.B2.Transaction.settle prepared tx index run =
      Staging.Transaction.settle prepared tx index run.state (outputOf run n) := by
  simp only [Staging.B2.Transaction.settle, Staging.Transaction.settle, hn, outputOf]
  rfl

/-- **Bridge B2 at `processTransaction`, against cut A.** For every block environment, block
output, transaction and index, settling the run computes exactly cut A's staged result. -/
theorem processTransaction_eq_staged (benv : Benv) (bout : BlockOutput) (tx : Transaction)
    (index : Nat) :
    Staging.B2.processTransaction benv bout tx index =
      Staging.processTransaction benv bout tx index := by
  simp only [Staging.B2.processTransaction, Staging.processTransaction]
  cases Staging.Transaction.check benv bout tx index with
  | error e => rfl
  | ok checked =>
    simp only [bind, Except.bind]
    cases Staging.Transaction.prepare checked tx index with
    | error e => rfl
    | ok prepared =>
      simp only [Staging.processMessageCall]
      cases Staging.Message.run prepared.msg with
      | error e => rfl
      | ok run =>
        simp only [Except.mapError, bind, Except.bind]
        rw [MessageRun.output_eq]
        cases hr : run.refundCounter with
        | error e =>
          simp [Staging.B2.Transaction.settle, hr, Except.mapError, bind, Except.bind]
        | ok n =>
          rw [Transaction.settle_eq prepared tx index run hr]
          simp [Except.mapError, bind, Except.bind, pure, Except.pure]

/-- **Bridge B2 at `processTransaction`.** For every block environment, block output,
transaction and index, settling the run computes exactly today's `processTransaction` result,
rejection text included. -/
theorem processTransaction_eq_b2 (benv : Benv) (bout : BlockOutput) (tx : Transaction)
    (index : Nat) :
    Staging.B2.processTransaction benv bout tx index = processTransaction benv bout tx index := by
  rw [processTransaction_eq_staged, processTransaction_eq]

end Jaune.Bridge.G2a
