import Examples.ShapePilot.Lifetime

/-! An executable WP adapter, not W1's replacement interpreter. The existing
opcode primitives still perform instruction execution, call preparation, the
creation set-up, the value transfer and the code-deposit charge. The adapter
immediately discards their legacy frame/resume packaging. Frames, entry,
settlement, caller resumption and the bounded driver below use the new
lifetime representation. No legacy frame settlement or resume is called.
-/
namespace Examples.ShapePilot.Prototype
open Jaune

structure CallContext where
  caller : Adr
  recipient : Adr
  value : B256
  calldata : Bytes
  code : ByteArray
  depthLeft : Nat
  isStatic : Bool
  tx : TenvStat
  block : BenvStat

def CallContext.ofLegacy (s : Sevm) : CallContext :=
  ⟨s.caller, s.currentTarget, s.value, s.data, s.code, s.depth, s.isStatic,
    s.tenvStat, s.benvStat⟩

/-- The five message-only fields have no reader in `Evm.step` (the environment
walk in `FieldReaders.lean`). They are absent from CallContext and filled with
inert values at this instruction adapter. -/
def CallContext.toLegacy (c : CallContext) : Sevm := {
  caller := c.caller, currentTarget := c.recipient, value := c.value,
  data := c.calldata, code := c.code, depth := c.depthLeft, isStatic := c.isStatic,
  tenvStat := c.tx, benvStat := c.block,
  target := none, gas := 0, codeAddress := none,
  shouldTransferValue := false, disablePrecompiles := false }

/-- A call names the account whose code runs; a creation runs its initcode and
has no code account. Creation is the kind, not an absent address. -/
inductive MessageKind where
  | call (codeAddress : Adr)
  | create
  deriving DecidableEq

/-- No saved world: it lives exactly once, in the frame's checkpoint. -/
structure Message where
  context : CallContext
  kind : MessageKind
  target : Option Adr
  gasLimit : Nat
  stateGasGrant : Nat
  transferValue : Bool
  disablePrecompiles : Bool

/-- Today's message shape: the creation flag (`Frame.isCreate`, or a top-level
message's absent target) and an optional code address. A well-formed legacy
message has a code address exactly when it is not a creation (`callMsg`,
`createMsg`, `prepareMessage`); any other shape is refused. -/
def MessageKind.ofLegacy (creating : Bool) (codeAddress : Option Adr) :
    Option MessageKind :=
  match creating, codeAddress with
  | true, none => some .create
  | false, some address => some (.call address)
  | _, _ => none

def Message.ofLegacy (msg : Msg) (creating : Bool) : Option Message := do
  let kind ← MessageKind.ofLegacy creating msg.codeAddress
  pure {
    context := CallContext.ofLegacy (initSevm msg), kind
    target := msg.target, gasLimit := msg.gas, stateGasGrant := msg.stateGasGrant,
    transferValue := msg.shouldTransferValue, disablePrecompiles := msg.disablePrecompiles }

def Message.codeAccount (m : Message) : Option Adr := match m.kind with
  | .call address => some address
  | .create => none

def Message.isCreate (m : Message) : Bool := match m.kind with
  | .call _ => false
  | .create => true

structure Frame where
  message : Message
  checkpoint : Checkpoint

/-- Decision 13: a statement about a frame that names its message. Whether it
is a creation is its kind, and a frame that is not a creation runs the code of
a definite account, which its kind names. -/
theorem Frame.message_identity (f : Frame) :
    (f.message.isCreate = true ↔ f.message.kind = .create) ∧
    (f.message.isCreate = false ↔ ∃ address, f.message.kind = .call address) ∧
    (∀ address, f.message.codeAccount = some address ↔
      f.message.kind = .call address) := by
  refine ⟨?_, ?_, fun address => ?_⟩ <;>
    cases h : f.message.kind <;>
    simp [Message.isCreate, Message.codeAccount, h]

/-- The kind is read off the legacy message without loss: creation is the
legacy creation flag, and a call's account is the legacy code address. -/
theorem Message.ofLegacy_kind {msg : Msg} {creating : Bool} {m : Message}
    (h : Message.ofLegacy msg creating = some m) :
    (m.kind = .create ↔ creating = true) ∧
    (∀ address, m.kind = .call address ↔
      creating = false ∧ msg.codeAddress = some address) := by
  simp only [Message.ofLegacy, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def, Option.some.injEq] at h
  obtain ⟨kind, hk, rfl⟩ := h
  cases creating <;> cases hc : msg.codeAddress <;>
    simp only [MessageKind.ofLegacy, hc, reduceCtorEq, Option.some.injEq] at hk <;>
    subst hk <;> simp

/-- Reconstruct the legacy primitive input from the single checkpoint. A
child's deletions are inherited or none by rule, as `callMsg` and `createMsg`
seed them. -/
def Frame.legacyMessage (f : Frame) : Msg :=
  let m := f.message
  let c := m.context
  let cp := f.checkpoint
  { (default : Msg) with
    caller := c.caller, currentTarget := c.recipient, value := c.value,
    data := c.calldata, code := c.code, depth := c.depthLeft, isStatic := c.isStatic,
    target := m.target, gas := m.gasLimit, stateGasGrant := m.stateGasGrant,
    codeAddress := m.codeAccount, shouldTransferValue := m.transferValue,
    disablePrecompiles := m.disablePrecompiles,
    accessedAddresses := cp.substate.accessedAddresses,
    accessedStorageKeys := cp.substate.accessedStorageKeys,
    inheritedDeletions :=
      if c.block.rules.settle.selfdestructRefund = 0 then .emptyWithCapacity
      else cp.substate.selfDestructs,
    benv := { (default : Benv) with
      stat := c.block, state := cp.world.state,
      storageWrites := cp.world.storageWrites, createdAccounts := cp.trail.createdAccounts },
    tenv := { (default : Tenv) with
      stat := c.tx, transientStorage := cp.world.transientStorage } }

/-- The kind's set-up, before the value transfer: a creation clears the
target's storage, records it as created and increments its nonce
(`processCreateMessage.msg`); a call has none. -/
def Frame.setUp (f : Frame) : Msg :=
  match f.message.kind with
  | .create => processCreateMessage.msg f.legacyMessage
  | .call _ => f.legacyMessage

structure Runtime where
  pc : Nat
  context : CallContext
  dynamic : Dynamic

def Fault.ofError : EvmError → Fault
  | .crypto reason => .crypto reason
  | .internal reason => .internal reason
  | _ => .internal (.invariant (.text "shape pilot: a failure is not a fault"))

/-- A failed frame's result. Meter restoration uses the existing pure meter
primitive. The frame's own touch of RIPEMD-160 is tested, when `selfTouch`,
on the world after the kind's set-up, exactly where `processMessage.settle`
tests it on the inner message; the deposit path does not test it, as today. -/
def failedResult (f : Frame) (selfTouch : Bool) (error : EvmError) (d : Devm) :
    Except Fault Frame.Result :=
  let rules := f.message.context.block.rules
  let recipient := f.message.context.recipient
  let touched := if selfTouch then
      ({ d with world := { d.world with state := f.setUp.benv.state } }).recordTouch rules
        (recipient == ripemd160Address) recipient
    else d
  let trail := Trail.ofFailedLegacy touched
  let meter := if rules.stateGas.isSome then d.mach.restoreStateGas else d.mach
  match error with
  | .revert => .ok (.revert d.output meter.gasLeft meter.stateGas trail)
  | .halt reason => .ok (.halt reason meter.stateGas trail)
  | error => .error (Fault.ofError error)

def successResult (d : Devm) : Frame.Result :=
  let view := Dynamic.ofLegacy d
  .success d.output d.gasLeft d.stateGas view.world view.substate view.trail

/-- A creation's code deposit, after its initcode succeeded. -/
def Frame.deposit (f : Frame) (d : Devm) : Except Fault Frame.Result :=
  match processCreateMessage.chargeCodeGas f.message.context.block.rules d with
  | .ok d => .ok (successResult (d.setCode f.message.context.recipient ⟨⟨d.output⟩⟩))
  | .error (error, d) => failedResult f false error d

/-- Settlement dispatches on the kind: only a creation deposits code. The
frame's own target is touched before the deposit, as today's three layers do. -/
def settle (f : Frame) (raw : Execution) : Except Fault Frame.Result :=
  match raw with
  | .error (error, d) => failedResult f true error d
  | .ok d =>
    let d := d.recordTouch f.message.context.block.rules true f.message.context.recipient
    match f.message.kind with
    | .call _ => .ok (successResult d)
    | .create => f.deposit d

inductive Entry where
  | run (runtime : Runtime)
  | done (result : Except Fault Frame.Result)

/-- Precompile dispatch is on the kind: only a call names an account, and
only that account can be a precompile. -/
def Frame.dispatch (f : Frame) (msg : Msg) (d : Devm) : Entry :=
  let runtime := Runtime.mk 0 f.message.context (Dynamic.ofLegacy d)
  match f.message.kind with
  | .call address =>
    if !f.message.disablePrecompiles && f.message.context.block.rules.isPrecomp address then
      .done (settle f (executePrecomp ⟨0, initSevm msg, d⟩ address))
    else .run runtime
  | .create => .run runtime

/-- Entry: the kind's set-up, the value transfer, today's seeds (`initDevm`),
then dispatch. A failed transfer is a fault, as today. -/
def enter (f : Frame) : Entry :=
  let msg := f.setUp
  match msg.benvAfterTransfer with
  | .error (error, _) => .done (.error (Fault.ofError error))
  | .ok benv =>
    let msg := msg.withBenv benv
    f.dispatch msg (initDevm msg)

/-! The kind drives `enter` and `settle`. -/

theorem Frame.setUp_create (f : Frame) (h : f.message.kind = .create) :
    f.setUp = processCreateMessage.msg f.legacyMessage := by
  simp only [Frame.setUp, h]

theorem Frame.setUp_call (f : Frame) (address : Adr) (h : f.message.kind = .call address) :
    f.setUp = f.legacyMessage := by
  simp only [Frame.setUp, h]

theorem Frame.legacyMessage_codeAddress (f : Frame) :
    f.legacyMessage.codeAddress = f.message.codeAccount := rfl

theorem Frame.dispatch_create (f : Frame) (msg : Msg) (d : Devm)
    (h : f.message.kind = .create) :
    f.dispatch msg d = .run ⟨0, f.message.context, .ofLegacy d⟩ := by
  simp only [Frame.dispatch, h]

theorem Frame.dispatch_call (f : Frame) (msg : Msg) (d : Devm) (address : Adr)
    (h : f.message.kind = .call address) :
    f.dispatch msg d =
      if !f.message.disablePrecompiles && f.message.context.block.rules.isPrecomp address then
        .done (settle f (executePrecomp ⟨0, initSevm msg, d⟩ address))
      else .run ⟨0, f.message.context, .ofLegacy d⟩ := by
  simp only [Frame.dispatch, h]

theorem settle_ok_call (f : Frame) (d : Devm) (address : Adr)
    (h : f.message.kind = .call address) :
    settle f (.ok d) = .ok (successResult
      (d.recordTouch f.message.context.block.rules true f.message.context.recipient)) := by
  simp only [settle, h]

theorem settle_ok_create (f : Frame) (d : Devm) (h : f.message.kind = .create) :
    settle f (.ok d) =
      f.deposit (d.recordTouch f.message.context.block.rules true f.message.context.recipient) := by
  simp only [settle, h]

/-- Decode only the packaging of the old opcode preparation result. The
child's kind is the legacy creation flag; a call's account is its code address. -/
def prepared (legacy : Jaune.Frame) (continuation : Jaune.Resume) :
    Option (Frame × Continuation) := do
  let message ← Message.ofLegacy legacy.outer legacy.isCreate
  pure <| match continuation with
  | .call saved index size =>
    (⟨message, .ofLegacy saved⟩, ⟨(Dynamic.ofLegacy saved).machine, .call index size, false, 0⟩)
  | .create saved address =>
    (⟨message, .ofLegacy saved⟩, ⟨(Dynamic.ofLegacy saved).machine, .create address, false, 0⟩)
  | .callAmsterdam state saved index size charged =>
    (⟨message, .ofLegacy saved⟩, ⟨(Dynamic.ofLegacy saved).machine, .call index size, true,
      if charged then state.newAccount else 0⟩)
  | .createAmsterdam state saved address charged =>
    (⟨message, .ofLegacy saved⟩, ⟨(Dynamic.ofLegacy saved).machine, .create address, true,
      if charged then state.newAccount else 0⟩)

inductive Step where
  | next (runtime : Runtime)
  | spawn (frame : Frame) (continuation : Continuation) (nextPc : Nat)
  | finish (raw : Execution)

def step (runtime : Runtime) : Except Fault Step :=
  match (Evm.mk runtime.pc runtime.context.toLegacy runtime.dynamic.toLegacy).step with
  | .cont pc d => .ok (.next ⟨pc, runtime.context, .ofLegacy d⟩)
  | .spawn frame continuation pc =>
    match prepared frame continuation with
    | some (frame, continuation) => .ok (.spawn frame continuation pc)
    | none => .error (.internal (.invariant (.text "shape pilot: ill-formed child message")))
  | .halt raw => .ok (.finish raw)

/-- Diagnostic information is outside Frame.Result. A caller consumes only
`result`; `terminalMachine` lets this pilot observe a frame's final stack, and
is absent when entry finished the frame before any code ran. -/
structure RunReport where
  result : Frame.Result
  terminalMachine : Option Machine

/-- Fuel bounds this pilot, not EVM semantics. Exhaustion is an internal fault,
so it cannot be mistaken for an EVM halt, revert, or successful execution. -/
def drive : Nat → Frame → Option Runtime → Except Fault RunReport
  | 0, _, _ => .error (.internal (.invariant (.text "shape pilot fuel exhausted")))
  | fuel + 1, f, none =>
    match enter f with
    | .done r => r.map fun result => ⟨result, none⟩
    | .run runtime => drive fuel f (some runtime)
  | fuel + 1, f, some runtime =>
    match step runtime with
    | .error fault => .error fault
    | .ok (.next runtime) => drive fuel f (some runtime)
    | .ok (.finish raw) => (settle f raw).map fun result => ⟨result, some runtime.dynamic.machine⟩
    | .ok (.spawn child continuation pc) => do
      let report ← drive fuel child none
      match resume continuation child.checkpoint report.result with
      | .error fault => .error fault
      | .ok (.ok dynamic) => drive fuel f (some ⟨pc, runtime.context, dynamic⟩)
      | .ok (.error (reason, merged)) =>
        (settle f (.error (.halt reason, merged.toLegacy))).map
          fun result => ⟨result, some merged.machine⟩

/-- A failed push at `resume` halts the parent at its own merged state, as
`execFueled` does with `Resume.run`'s error (`Execution.lean:1936`). -/
theorem drive_resume_halt (fuel : Nat) (f child : Frame) (runtime : Runtime)
    (continuation : Continuation) (pc : Nat) (report : RunReport)
    (reason : ExceptionalHalt) (merged : Dynamic)
    (stepped : step runtime = .ok (.spawn child continuation pc))
    (childRan : drive fuel child none = .ok report)
    (resumed : resume continuation child.checkpoint report.result =
      .ok (.error (reason, merged))) :
    drive (fuel + 1) f (some runtime) =
      (settle f (.error (.halt reason, merged.toLegacy))).map
        fun result => ⟨result, some merged.machine⟩ := by
  simp only [drive, stepped, childRan, resumed, bind, Except.bind]

/-- A top-level message's checkpoint: the state it was prepared on. -/
def Checkpoint.ofMessage (msg : Msg) : Checkpoint := {
  world := Jaune.World.mk msg.benv.state msg.tenv.transientStorage msg.benv.storageWrites
  substate := ⟨[], 0, msg.inheritedDeletions, msg.accessedAddresses,
    msg.accessedStorageKeys, .emptyWithCapacity⟩
  trail := ⟨msg.benv.createdAccounts, .emptyWithCapacity, .emptyWithCapacity, false⟩ }

/-- A top-level frame is a creation exactly when its message has no target, as
`processMessageCall` decides. -/
def topFrame (msg : Msg) : Option Frame := do
  let message ← Message.ofLegacy msg msg.target.isNone
  pure ⟨message, .ofMessage msg⟩

end Examples.ShapePilot.Prototype
