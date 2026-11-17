import Jaune.Exec
import Jaune.MessageCall.Top

/-!
# From raw code execution to settled message results

Contract-neutral adapters between `exec (initEvm msg)` and top-level
`processMessage msg`, including canonical settled machines for REVERT and
exceptional-halt outcomes.
-/

namespace Jaune

-- `ByteArray.getInst` and other extensions of root types live in `Jaune`;
-- opening it lets generalized field notation (`code.getInst`) find them.
open Jaune

namespace MessageExecution

/-- Any call frame that enters an EVM settles the total execution selected by
that exact entry.  This is the generic bridge for callers that already retain
the `Frame.enter` equation, including delegated children. -/
theorem processMessage_eq_settle_exec_of_enter
    (msg : Msg) (evm : Evm)
    (henter : (Legacy.Frame.ofCall msg).enter = .run evm) :
    processMessage msg = (Legacy.Frame.ofCall msg).settle (Legacy.exec evm) := by
  unfold processMessage runFrame
  rw [henter]

/-- A successful transfer enters ordinary EVM code whenever the selected code
address is not a precompile under the active fork.  Unlike the convenient
`disablePrecompiles` adapter below, this is the bridge used by ordinary
messages whose precompile switch remains enabled. -/
theorem frameEnter_eq_run_afterTransfer_of_notPrecompile
    (msg : Msg) (afterTransfer : Benv) (codeAddress : Address)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hcode : msg.codeAddress = some codeAddress)
    (hnotPrecompile :
      ¬ afterTransfer.stat.rules.isPrecompile codeAddress) :
    (Legacy.Frame.ofCall msg).enter =
      .run (initEvm (msg.withBenv afterTransfer)) := by
  have hcode' :
      (msg.withBenv afterTransfer).codeAddress = some codeAddress := hcode
  have henter : executeCode.enter (msg.withBenv afterTransfer) =
      .inl (initEvm (msg.withBenv afterTransfer)) := by
    unfold executeCode.enter
    rw [hcode']
    simp [hnotPrecompile]
  unfold Legacy.Frame.enter Legacy.Frame.ofCall
  rw [hentry]
  simp only
  rw [henter]

/-- The corresponding `processMessage` bridge for an ordinary non-precompile
entry after value transfer. -/
theorem processMessage_eq_settle_exec_afterTransfer_of_notPrecompile
    (msg : Msg) (afterTransfer : Benv) (codeAddress : Address)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hcode : msg.codeAddress = some codeAddress)
    (hnotPrecompile :
      ¬ afterTransfer.stat.rules.isPrecompile codeAddress) :
    processMessage msg =
      (Legacy.Frame.ofCall msg).settle
        (Legacy.exec (initEvm (msg.withBenv afterTransfer))) :=
  processMessage_eq_settle_exec_of_enter msg _
    (frameEnter_eq_run_afterTransfer_of_notPrecompile
      msg afterTransfer codeAddress hentry hcode hnotPrecompile)

/-- A successful transfer enters the supplied creation code directly when the
message has no separate code address.  This is independent of the precompile
switch because there is no address to classify as a precompile. -/
theorem processMessage_eq_settle_exec_afterTransfer_of_noCodeAddress
    (msg : Msg) (afterTransfer : Benv)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hcodeAddress : msg.codeAddress = .none) :
    processMessage msg =
      (Legacy.Frame.ofCall msg).settle
        (Legacy.exec (initEvm (msg.withBenv afterTransfer))) := by
  unfold processMessage runFrame Legacy.Frame.enter Legacy.Frame.ofCall
  rw [hentry]
  unfold executeCode.enter
  simp only [Msg.withBenv, hcodeAddress]

/-- When value transfer prepares a distinct entry environment and precompiles
are disabled, `processMessage` settles the raw execution started from that
actual transferred environment. -/
theorem processMessage_eq_settle_exec_afterTransfer
    (msg : Msg) (afterTransfer : Benv)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hdisable : msg.disablePrecompiles = true) :
    processMessage msg =
      (Legacy.Frame.ofCall msg).settle
        (Legacy.exec (initEvm (msg.withBenv afterTransfer))) := by
  have henter : executeCode.enter (msg.withBenv afterTransfer) =
      .inl (initEvm (msg.withBenv afterTransfer)) := by
    unfold executeCode.enter
    have hdisable' :
        (msg.withBenv afterTransfer).disablePrecompiles = true := hdisable
    cases (msg.withBenv afterTransfer).codeAddress <;>
      simp [hdisable']
  have hframe :
      (Legacy.Frame.ofCall msg).enter =
        .run (initEvm (msg.withBenv afterTransfer)) := by
    unfold Legacy.Frame.enter Legacy.Frame.ofCall
    rw [hentry]
    simp only
    rw [henter]
  exact processMessage_eq_settle_exec_of_enter
    msg (initEvm (msg.withBenv afterTransfer)) hframe

/-- A message with an ordinary code address enters the interpreter whenever
that address is not a precompile.  This covers normal transaction messages
with `disablePrecompiles = false`; the flag is deliberately not a premise. -/
theorem executeCode_enter_of_codeAddress_not_precompile
    (msg : Msg) (benv : Benv) (codeAddress : Address)
    (hcodeAddress : msg.codeAddress = some codeAddress)
    (hnotPrecompile :
      decide (benv.stat.rules.isPrecompile codeAddress) = false) :
    executeCode.enter (msg.withBenv benv) =
      .inl (initEvm (msg.withBenv benv)) := by
  unfold executeCode.enter
  simp only [Msg.withBenv, hcodeAddress, hnotPrecompile, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]

/-- After successful value transfer, an exact interpreter-entry equation is
enough to expose `processMessage` as settlement of the raw execution from the
actual post-transfer environment. -/
theorem processMessage_eq_settle_exec_afterTransfer_of_codeEntry
    (msg : Msg) (benv : Benv)
    (hentry : msg.benvAfterTransfer = .ok benv)
    (hcodeEntry : executeCode.enter (msg.withBenv benv) =
      .inl (initEvm (msg.withBenv benv))) :
    processMessage msg =
      (Legacy.Frame.ofCall msg).settle
        (Legacy.exec (initEvm (msg.withBenv benv))) := by
  have henter :
      (Legacy.Frame.ofCall msg).enter =
        .run (initEvm (msg.withBenv benv)) := by
    unfold Legacy.Frame.enter Legacy.Frame.ofCall
    rw [hentry]
    simp only
    rw [hcodeEntry]
  unfold processMessage runFrame
  rw [henter]

/-- Under the ordinary entry identity with precompiles disabled,
`processMessage` is the call frame's settlement of the raw code execution. -/
theorem processMessage_eq_settle_exec
    (msg : Msg)
    (hentry : msg.benvAfterTransfer = .ok msg.benv)
    (hdisable : msg.disablePrecompiles = true) :
    processMessage msg =
      (Legacy.Frame.ofCall msg).settle (Legacy.exec (initEvm msg)) := by
  have hself : msg.withBenv msg.benv = msg := by
    cases msg
    rfl
  simpa only [hself] using
    processMessage_eq_settle_exec_afterTransfer
      msg msg.benv hentry hdisable

/-- The message-settled machine produced by a raw REVERT outcome. -/
def settledRevert (msg : Msg) (raw : Devm) : Devm :=
  ((raw.withError (some .revert)).rollback
    msg.benv.state msg.tenv.transientStorage).withStorageWrites msg.benv.storageWrites

/-- The message-settled machine produced by a raw exceptional halt. -/
def settledHalt
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) : Devm :=
  (((raw.withGasLeft 0).setMeta
      {raw.meta with output := [], error := some (.halt reason)}).rollback
    msg.benv.state msg.tenv.transientStorage).withStorageWrites msg.benv.storageWrites

/-- A clean execution from the actual post-transfer environment settles to the
same clean machine. -/
theorem processMessage_clean_of_exec_afterTransfer
    (msg : Msg) (afterTransfer : Benv) (post : Devm)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hdisable : msg.disablePrecompiles = true)
    (hsweep : msg.benv.stat.rules.settlement.touchedSweep = false)
    (hexec : Legacy.exec (initEvm (msg.withBenv afterTransfer)) = .ok post)
    (herror : post.error = none) :
    processMessage msg = .ok post := by
  rw [processMessage_eq_settle_exec_afterTransfer
    msg afterTransfer hentry hdisable, hexec]
  simp [Legacy.Frame.ofCall, Legacy.Frame.settle, Legacy.Frame.settleMsg,
    executeCode.handleErrorWith_ok, processMessage.settle, herror, hsweep,
    Bind.bind, Except.bind]

/-- A clean raw execution settles to the same clean machine. -/
theorem processMessage_clean_of_exec
    (msg : Msg) (post : Devm)
    (hentry : msg.benvAfterTransfer = .ok msg.benv)
    (hdisable : msg.disablePrecompiles = true)
    (hsweep : msg.benv.stat.rules.settlement.touchedSweep = false)
    (hexec : Legacy.exec (initEvm msg) = .ok post)
    (herror : post.error = none) :
    processMessage msg = .ok post := by
  have hself : msg.withBenv msg.benv = msg := by
    cases msg
    rfl
  exact processMessage_clean_of_exec_afterTransfer
    msg msg.benv post hentry hdisable hsweep
      (by simpa only [hself] using hexec) herror

/-- A raw REVERT from the actual post-transfer environment settles to
`settledRevert`. -/
theorem processMessage_revert_of_exec_afterTransfer
    (msg : Msg) (afterTransfer : Benv) (raw : Devm)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hdisable : msg.disablePrecompiles = true)
    (hgas : msg.benv.stat.rules.stateGas = none)
    (hsweep : msg.benv.stat.rules.settlement.touchedSweep = false)
    (hexec : Legacy.exec (initEvm (msg.withBenv afterTransfer)) =
      .error (.revert, raw)) :
    processMessage msg = .ok (settledRevert msg raw) := by
  rw [processMessage_eq_settle_exec_afterTransfer
    msg afterTransfer hentry hdisable, hexec]
  simp only [Legacy.Frame.settle_eq_settleMsg_handleErrorWith, Legacy.Frame.ofCall, hgas]
  simp only [Legacy.Frame.settleMsg, processMessage.settle, Devm.recordTouch_of_not_touchedSweep hsweep]
  rfl

/-- A raw REVERT from creation code with no separate code address settles to
`settledRevert`, without requiring the message to disable precompiles. -/
theorem processMessage_revert_of_exec_afterTransfer_of_noCodeAddress
    (msg : Msg) (afterTransfer : Benv) (raw : Devm)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hcodeAddress : msg.codeAddress = .none)
    (hgas : msg.benv.stat.rules.stateGas = none)
    (hsweep : msg.benv.stat.rules.settlement.touchedSweep = false)
    (hexec : Legacy.exec (initEvm (msg.withBenv afterTransfer)) =
      .error (.revert, raw)) :
    processMessage msg = .ok (settledRevert msg raw) := by
  rw [processMessage_eq_settle_exec_afterTransfer_of_noCodeAddress
    msg afterTransfer hentry hcodeAddress, hexec]
  simp only [Legacy.Frame.settle_eq_settleMsg_handleErrorWith, Legacy.Frame.ofCall, hgas]
  simp only [Legacy.Frame.settleMsg, processMessage.settle, Devm.recordTouch_of_not_touchedSweep hsweep]
  rfl

/-- A clean raw execution from an exact post-transfer interpreter entry
settles successfully to the same clean machine. -/
theorem processMessage_clean_of_exec_afterTransfer_of_codeEntry
    (msg : Msg) (benv : Benv) (post : Devm)
    (hentry : msg.benvAfterTransfer = .ok benv)
    (hcodeEntry : executeCode.enter (msg.withBenv benv) =
      .inl (initEvm (msg.withBenv benv)))
    (hsweep : msg.benv.stat.rules.settlement.touchedSweep = false)
    (hexec : Legacy.exec (initEvm (msg.withBenv benv)) = .ok post)
    (herror : post.error = none) :
    processMessage msg = .ok post := by
  rw [processMessage_eq_settle_exec_afterTransfer_of_codeEntry
    msg benv hentry hcodeEntry, hexec]
  simp [Legacy.Frame.ofCall, Legacy.Frame.settle, Legacy.Frame.settleMsg,
    executeCode.handleErrorWith_ok, processMessage.settle, herror, hsweep,
    Bind.bind, Except.bind]

/-- A raw REVERT settles to `settledRevert`. -/
theorem processMessage_revert_of_exec
    (msg : Msg) (raw : Devm)
    (hentry : msg.benvAfterTransfer = .ok msg.benv)
    (hdisable : msg.disablePrecompiles = true)
    (hgas : msg.benv.stat.rules.stateGas = none)
    (hsweep : msg.benv.stat.rules.settlement.touchedSweep = false)
    (hexec : Legacy.exec (initEvm msg) = .error (.revert, raw)) :
    processMessage msg = .ok (settledRevert msg raw) := by
  have hself : msg.withBenv msg.benv = msg := by
    cases msg
    rfl
  exact processMessage_revert_of_exec_afterTransfer
    msg msg.benv raw hentry hdisable hgas hsweep
      (by simpa only [hself] using hexec)

/-- A raw exceptional halt from the actual post-transfer environment settles
to `settledHalt`. -/
theorem processMessage_halt_of_exec_afterTransfer
    (msg : Msg) (afterTransfer : Benv)
    (reason : ExceptionalHalt) (raw : Devm)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hdisable : msg.disablePrecompiles = true)
    (hgas : msg.benv.stat.rules.stateGas = none)
    (hsweep : msg.benv.stat.rules.settlement.touchedSweep = false)
    (hexec : Legacy.exec (initEvm (msg.withBenv afterTransfer)) =
      .error (.halt reason, raw)) :
    processMessage msg = .ok (settledHalt msg reason raw) := by
  rw [processMessage_eq_settle_exec_afterTransfer
    msg afterTransfer hentry hdisable, hexec]
  simp only [Legacy.Frame.settle_eq_settleMsg_handleErrorWith, Legacy.Frame.ofCall, hgas]
  simp only [Legacy.Frame.settleMsg, processMessage.settle, Devm.recordTouch_of_not_touchedSweep hsweep]
  rfl

/-- A raw exceptional halt settles to `settledHalt`. -/
theorem processMessage_halt_of_exec
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm)
    (hentry : msg.benvAfterTransfer = .ok msg.benv)
    (hdisable : msg.disablePrecompiles = true)
    (hgas : msg.benv.stat.rules.stateGas = none)
    (hsweep : msg.benv.stat.rules.settlement.touchedSweep = false)
    (hexec : Legacy.exec (initEvm msg) = .error (.halt reason, raw)) :
    processMessage msg = .ok (settledHalt msg reason raw) := by
  have hself : msg.withBenv msg.benv = msg := by
    cases msg
    rfl
  exact processMessage_halt_of_exec_afterTransfer
    msg msg.benv reason raw hentry hdisable hgas hsweep
      (by simpa only [hself] using hexec)

@[simp] theorem settledRevert_error (msg : Msg) (raw : Devm) :
    (settledRevert msg raw).error = some .revert := rfl

@[simp] theorem settledRevert_output (msg : Msg) (raw : Devm) :
    (settledRevert msg raw).output = raw.output := rfl

@[simp] theorem settledRevert_logs (msg : Msg) (raw : Devm) :
    (settledRevert msg raw).logs = raw.logs := rfl

@[simp] theorem settledRevert_state (msg : Msg) (raw : Devm) :
    (settledRevert msg raw).state = msg.benv.state := rfl

@[simp] theorem settledRevert_transientStorage (msg : Msg) (raw : Devm) :
    (settledRevert msg raw).transientStorage =
      msg.tenv.transientStorage := rfl

@[simp] theorem settledHalt_error
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) :
    (settledHalt msg reason raw).error = some (.halt reason) := rfl

@[simp] theorem settledHalt_output
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) :
    (settledHalt msg reason raw).output = [] := rfl

@[simp] theorem settledHalt_logs
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) :
    (settledHalt msg reason raw).logs = raw.logs := rfl

@[simp] theorem settledHalt_state
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) :
    (settledHalt msg reason raw).state = msg.benv.state := rfl

@[simp] theorem settledHalt_transientStorage
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) :
    (settledHalt msg reason raw).transientStorage =
      msg.tenv.transientStorage := rfl

end MessageExecution

/-! ## Canonical message-entry projections -/

@[simp] theorem Msg.initDevm_stack (msg : Msg) :
    (initDevm msg).stack = [] := rfl

@[simp] theorem Msg.initDevm_memory (msg : Msg) :
    (initDevm msg).memory = Mem.empty := rfl

@[simp] theorem Msg.initDevm_accessedStorageKeys (msg : Msg) :
    (initDevm msg).accessedStorageKeys = msg.accessedStorageKeys := rfl

@[simp] theorem Msg.initSevm_data (msg : Msg) :
    (initSevm msg).data = msg.data := rfl

@[simp] theorem Msg.initSevm_currentTarget (msg : Msg) :
    (initSevm msg).currentTarget = msg.currentTarget := rfl

/-! ## On the four-part message call

The same adapters for `Frame.runTop`, `enterWith` and `settle`. A failed frame's result
carries no world, logs or substate (S3), so where the adapters above name a rolled-back
machine these name the result: its output, gas and meter; the world after it is the
checkpoint's (`Frame.worldAfter`). -/

namespace MessageExecution

/-- A frame entered into the interpreter settles the total execution selected by that entry. -/
theorem runTop_eq_settle_exec_of_enter (f : Frame) (evm : Evm)
    (henter : enterWith f f.checkpoint.toDevm = .run evm) :
    Frame.runTop f = settle f (exec evm) := by
  unfold Frame.runTop
  rw [henter]

/-- After a successful transfer, a frame whose code address is not a precompile under its
rules enters the interpreter on the transferred world. -/
theorem enterWith_eq_run_of_notPrecompile (f : Frame) (start : Devm) (world : World)
    (codeAddress : Address)
    (htransfer : f.message.transfer f.enteredWorld = .ok world)
    (hcode : f.message.codeAddress = some codeAddress)
    (hnotPrecompile : ¬ f.message.context.block.rules.isPrecompile codeAddress) :
    enterWith f start =
      .run ⟨0, f.message.sevm, (start.setWorld world).withCreatedAccounts
        f.enteredCreatedAccounts⟩ := by
  unfold enterWith
  simp only [htransfer, hcode, hnotPrecompile, decide_false, Bool.and_false,
    Bool.false_eq_true, ↓reduceIte]

/-- After a successful transfer, a frame with no code address (a creation) enters its code. -/
theorem enterWith_eq_run_of_noCodeAddress (f : Frame) (start : Devm) (world : World)
    (htransfer : f.message.transfer f.enteredWorld = .ok world)
    (hcode : f.message.codeAddress = none) :
    enterWith f start =
      .run ⟨0, f.message.sevm, (start.setWorld world).withCreatedAccounts
        f.enteredCreatedAccounts⟩ := by
  unfold enterWith
  simp only [htransfer, hcode]

/-- After a successful transfer, a frame with precompiles disabled enters its code. -/
theorem enterWith_eq_run_of_disablePrecompiles (f : Frame) (start : Devm) (world : World)
    (htransfer : f.message.transfer f.enteredWorld = .ok world)
    (hdisable : f.message.disablePrecompiles = true) :
    enterWith f start =
      .run ⟨0, f.message.sevm, (start.setWorld world).withCreatedAccounts
        f.enteredCreatedAccounts⟩ := by
  unfold enterWith
  simp only [htransfer, hdisable]
  split <;> simp

/-- A call frame's clean finish settles to a success carrying its output and its machine after
its own touch. -/
theorem settle_ok_call (f : Frame) (d : Devm) (hkind : f.message.kind = .call) :
    settle f (.ok d) =
      let d' := d.recordTouch f.message.context.block.rules true f.message.context.recipient
      .ok (Frame.Result.ofSuccess d'.output d') := by
  unfold settle
  simp only [hkind]

/-- Without state gas, a raw REVERT settles to a revert with the raw output, gas and meter. -/
theorem settle_revert (f : Frame) (d : Devm)
    (hgas : f.message.context.block.rules.stateGas = none) :
    ∃ trail, settle f (.error (.revert, d)) = .ok (.revert d.output d.gasLeft d.mach.stateGas trail) := by
  unfold settle
  simp only [hgas]
  exact ⟨_, rfl⟩

/-- Without state gas, a raw exceptional halt settles to a halt with the raw meter. -/
theorem settle_halt (f : Frame) (reason : ExceptionalHalt) (d : Devm)
    (hgas : f.message.context.block.rules.stateGas = none) :
    ∃ trail, settle f (.error (.halt reason, d)) = .ok (.halt reason d.mach.stateGas trail) := by
  unfold settle
  simp only [hgas]
  exact ⟨_, rfl⟩

/-- A failed result leaves the frame's world as its checkpoint's. -/
theorem worldAfter_of_failed (f : Frame) (r : Frame.Result) (hfailed : r.failed = true) :
    f.worldAfter r = f.checkpoint.world := by
  cases r with
  | success => simp [Frame.Result.failed] at hfailed
  | revert => rfl
  | halt => rfl

end MessageExecution

end Jaune
