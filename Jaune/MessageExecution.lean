import Jaune.Exec

/-!
# From raw code execution to settled message results

Contract-neutral adapters between `exec (initEvm msg)` and top-level
`processMessage msg`, including canonical settled machines for REVERT and
exceptional-halt outcomes.
-/

namespace Blanc

open Jaune

namespace MessageExecution

/-- Any call frame that enters an EVM settles the total execution selected by
that exact entry.  This is the generic bridge for callers that already retain
the `Frame.enter` equation, including delegated children. -/
theorem processMessage_eq_settle_exec_of_enter
    (msg : Msg) (evm : Evm)
    (henter : (Frame.ofCall msg).enter = .run evm) :
    processMessage msg = (Frame.ofCall msg).settle (exec evm) := by
  unfold processMessage runFrame
  rw [henter]

/-- A successful transfer enters ordinary EVM code whenever the selected code
address is not a precompile under the active fork.  Unlike the convenient
`disablePrecompiles` adapter below, this is the bridge used by ordinary
messages whose precompile switch remains enabled. -/
theorem frameEnter_eq_run_afterTransfer_of_notPrecompile
    (msg : Msg) (afterTransfer : Benv) (codeAddress : Adr)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hcode : msg.codeAddress = some codeAddress)
    (hnotPrecompile :
      ¬ afterTransfer.stat.rules.isPrecomp codeAddress) :
    (Frame.ofCall msg).enter =
      .run (initEvm (msg.withBenv afterTransfer)) := by
  have hcode' :
      (msg.withBenv afterTransfer).codeAddress = some codeAddress := hcode
  have henter : executeCode.enter (msg.withBenv afterTransfer) =
      .inl (initEvm (msg.withBenv afterTransfer)) := by
    unfold executeCode.enter
    rw [hcode']
    simp [hnotPrecompile]
  unfold Frame.enter Frame.ofCall
  rw [hentry]
  simp only
  rw [henter]

/-- The corresponding `processMessage` bridge for an ordinary non-precompile
entry after value transfer. -/
theorem processMessage_eq_settle_exec_afterTransfer_of_notPrecompile
    (msg : Msg) (afterTransfer : Benv) (codeAddress : Adr)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hcode : msg.codeAddress = some codeAddress)
    (hnotPrecompile :
      ¬ afterTransfer.stat.rules.isPrecomp codeAddress) :
    processMessage msg =
      (Frame.ofCall msg).settle
        (exec (initEvm (msg.withBenv afterTransfer))) :=
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
      (Frame.ofCall msg).settle
        (exec (initEvm (msg.withBenv afterTransfer))) := by
  unfold processMessage runFrame Frame.enter Frame.ofCall
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
      (Frame.ofCall msg).settle
        (exec (initEvm (msg.withBenv afterTransfer))) := by
  have henter : executeCode.enter (msg.withBenv afterTransfer) =
      .inl (initEvm (msg.withBenv afterTransfer)) := by
    unfold executeCode.enter
    have hdisable' :
        (msg.withBenv afterTransfer).disablePrecompiles = true := hdisable
    cases (msg.withBenv afterTransfer).codeAddress <;>
      simp [hdisable']
  have hframe :
      (Frame.ofCall msg).enter =
        .run (initEvm (msg.withBenv afterTransfer)) := by
    unfold Frame.enter Frame.ofCall
    rw [hentry]
    simp only
    rw [henter]
  exact processMessage_eq_settle_exec_of_enter
    msg (initEvm (msg.withBenv afterTransfer)) hframe

/-- A message with an ordinary code address enters the interpreter whenever
that address is not a precompile.  This covers normal transaction messages
with `disablePrecompiles = false`; the flag is deliberately not a premise. -/
theorem executeCode_enter_of_codeAddress_not_precompile
    (msg : Msg) (benv : Benv) (codeAddress : Adr)
    (hcodeAddress : msg.codeAddress = some codeAddress)
    (hnotPrecompile :
      decide (benv.stat.rules.isPrecomp codeAddress) = false) :
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
      (Frame.ofCall msg).settle
        (exec (initEvm (msg.withBenv benv))) := by
  have henter :
      (Frame.ofCall msg).enter =
        .run (initEvm (msg.withBenv benv)) := by
    unfold Frame.enter Frame.ofCall
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
      (Frame.ofCall msg).settle (exec (initEvm msg)) := by
  have hself : msg.withBenv msg.benv = msg := by
    cases msg
    rfl
  simpa only [hself] using
    processMessage_eq_settle_exec_afterTransfer
      msg msg.benv hentry hdisable

/-- The message-settled machine produced by a raw REVERT outcome. -/
def settledRevert (msg : Msg) (raw : Devm) : Devm :=
  (raw.withError (some .revert)).rollback
    msg.benv.state msg.tenv.transientStorage

/-- The message-settled machine produced by a raw exceptional halt. -/
def settledHalt
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm) : Devm :=
  (((raw.withGasLeft 0).setMeta
      {raw.meta with output := [], error := some (.halt reason)}).rollback
    msg.benv.state msg.tenv.transientStorage)

/-- A clean execution from the actual post-transfer environment settles to the
same clean machine. -/
theorem processMessage_clean_of_exec_afterTransfer
    (msg : Msg) (afterTransfer : Benv) (post : Devm)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hdisable : msg.disablePrecompiles = true)
    (hexec : exec (initEvm (msg.withBenv afterTransfer)) = .ok post)
    (herror : post.error = none) :
    processMessage msg = .ok post := by
  rw [processMessage_eq_settle_exec_afterTransfer
    msg afterTransfer hentry hdisable, hexec]
  simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
    executeCode.handleErrorWith_ok, processMessage.settle]
  change (if post.error.isSome = true then
    Except.ok (post.rollback msg.benv.state msg.tenv.transientStorage)
    else Except.ok post) = Except.ok post
  rw [herror]
  rfl

/-- A clean raw execution settles to the same clean machine. -/
theorem processMessage_clean_of_exec
    (msg : Msg) (post : Devm)
    (hentry : msg.benvAfterTransfer = .ok msg.benv)
    (hdisable : msg.disablePrecompiles = true)
    (hexec : exec (initEvm msg) = .ok post)
    (herror : post.error = none) :
    processMessage msg = .ok post := by
  have hself : msg.withBenv msg.benv = msg := by
    cases msg
    rfl
  exact processMessage_clean_of_exec_afterTransfer
    msg msg.benv post hentry hdisable
      (by simpa only [hself] using hexec) herror

/-- A raw REVERT from the actual post-transfer environment settles to
`settledRevert`. -/
theorem processMessage_revert_of_exec_afterTransfer
    (msg : Msg) (afterTransfer : Benv) (raw : Devm)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hdisable : msg.disablePrecompiles = true)
    (hgas : msg.benv.stat.rules.stateGas = none)
    (hexec : exec (initEvm (msg.withBenv afterTransfer)) =
      .error (.revert, raw)) :
    processMessage msg = .ok (settledRevert msg raw) := by
  rw [processMessage_eq_settle_exec_afterTransfer
    msg afterTransfer hentry hdisable, hexec]
  simp only [Frame.settle_eq_settleMsg_handleErrorWith, Frame.ofCall, hgas]
  rfl

/-- A raw REVERT from creation code with no separate code address settles to
`settledRevert`, without requiring the message to disable precompiles. -/
theorem processMessage_revert_of_exec_afterTransfer_of_noCodeAddress
    (msg : Msg) (afterTransfer : Benv) (raw : Devm)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hcodeAddress : msg.codeAddress = .none)
    (hgas : msg.benv.stat.rules.stateGas = none)
    (hexec : exec (initEvm (msg.withBenv afterTransfer)) =
      .error (.revert, raw)) :
    processMessage msg = .ok (settledRevert msg raw) := by
  rw [processMessage_eq_settle_exec_afterTransfer_of_noCodeAddress
    msg afterTransfer hentry hcodeAddress, hexec]
  simp only [Frame.settle_eq_settleMsg_handleErrorWith, Frame.ofCall, hgas]
  rfl

/-- A clean raw execution from an exact post-transfer interpreter entry
settles successfully to the same clean machine. -/
theorem processMessage_clean_of_exec_afterTransfer_of_codeEntry
    (msg : Msg) (benv : Benv) (post : Devm)
    (hentry : msg.benvAfterTransfer = .ok benv)
    (hcodeEntry : executeCode.enter (msg.withBenv benv) =
      .inl (initEvm (msg.withBenv benv)))
    (hexec : exec (initEvm (msg.withBenv benv)) = .ok post)
    (herror : post.error = none) :
    processMessage msg = .ok post := by
  rw [processMessage_eq_settle_exec_afterTransfer_of_codeEntry
    msg benv hentry hcodeEntry, hexec]
  simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
    executeCode.handleErrorWith_ok, processMessage.settle]
  change (if post.error.isSome = true then
    Except.ok (post.rollback msg.benv.state msg.tenv.transientStorage)
    else Except.ok post) = Except.ok post
  rw [herror]
  rfl

/-- A raw REVERT settles to `settledRevert`. -/
theorem processMessage_revert_of_exec
    (msg : Msg) (raw : Devm)
    (hentry : msg.benvAfterTransfer = .ok msg.benv)
    (hdisable : msg.disablePrecompiles = true)
    (hgas : msg.benv.stat.rules.stateGas = none)
    (hexec : exec (initEvm msg) = .error (.revert, raw)) :
    processMessage msg = .ok (settledRevert msg raw) := by
  have hself : msg.withBenv msg.benv = msg := by
    cases msg
    rfl
  exact processMessage_revert_of_exec_afterTransfer
    msg msg.benv raw hentry hdisable hgas
      (by simpa only [hself] using hexec)

/-- A raw exceptional halt from the actual post-transfer environment settles
to `settledHalt`. -/
theorem processMessage_halt_of_exec_afterTransfer
    (msg : Msg) (afterTransfer : Benv)
    (reason : ExceptionalHalt) (raw : Devm)
    (hentry : msg.benvAfterTransfer = .ok afterTransfer)
    (hdisable : msg.disablePrecompiles = true)
    (hgas : msg.benv.stat.rules.stateGas = none)
    (hexec : exec (initEvm (msg.withBenv afterTransfer)) =
      .error (.halt reason, raw)) :
    processMessage msg = .ok (settledHalt msg reason raw) := by
  rw [processMessage_eq_settle_exec_afterTransfer
    msg afterTransfer hentry hdisable, hexec]
  simp only [Frame.settle_eq_settleMsg_handleErrorWith, Frame.ofCall, hgas]
  rfl

/-- A raw exceptional halt settles to `settledHalt`. -/
theorem processMessage_halt_of_exec
    (msg : Msg) (reason : ExceptionalHalt) (raw : Devm)
    (hentry : msg.benvAfterTransfer = .ok msg.benv)
    (hdisable : msg.disablePrecompiles = true)
    (hgas : msg.benv.stat.rules.stateGas = none)
    (hexec : exec (initEvm msg) = .error (.halt reason, raw)) :
    processMessage msg = .ok (settledHalt msg reason raw) := by
  have hself : msg.withBenv msg.benv = msg := by
    cases msg
    rfl
  exact processMessage_halt_of_exec_afterTransfer
    msg msg.benv reason raw hentry hdisable hgas
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

end Blanc
