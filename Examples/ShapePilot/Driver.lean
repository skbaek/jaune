import Examples.ShapePilot.Lifetime

/-! An executable WP adapter, not W1's replacement interpreter. The existing
opcode primitives still perform instruction execution and call preparation.
The adapter immediately discards their legacy frame/resume packaging. Frames,
entry, settlement, caller resumption and the bounded driver below use the new
lifetime representation. No legacy frame settlement or resume is called.
-/
namespace Examples.ShapePilot.Prototype
open Jaune

structure CallContext where
  caller : Address
  recipient : Address
  value : U256
  calldata : Bytes
  code : ByteArray
  depthLeft : Nat
  isStatic : Bool
  tx : TenvStat
  block : BenvStat

def CallContext.ofLegacy (s : Sevm) : CallContext :=
  ⟨s.caller, s.currentTarget, s.value, s.data, s.code, s.depth, s.isStatic,
    s.tenvStat, s.benvStat⟩

/-- The five message-only fields have no reader in `Evm.step`. They are absent
from CallContext and filled with inert values at this instruction adapter. -/
def CallContext.toLegacy (c : CallContext) : Sevm := {
  caller := c.caller, currentTarget := c.recipient, value := c.value,
  data := c.calldata, code := c.code, depth := c.depthLeft, isStatic := c.isStatic,
  tenvStat := c.tx, benvStat := c.block,
  target := none, gas := 0, codeAddress := none,
  shouldTransferValue := false, disablePrecompiles := false }

inductive MessageKind where
  | call (codeAddress : Option Address)
  | create
  deriving DecidableEq

/-- No saved world: it lives exactly once, in the frame's checkpoint. -/
structure Message where
  context : CallContext
  kind : MessageKind
  target : Option Address
  gasLimit : Nat
  stateGasGrant : Nat
  transferValue : Bool
  disablePrecompiles : Bool

def Message.ofLegacy (msg : Msg) (creating : Bool) : Message := {
  context := CallContext.ofLegacy (initSevm msg)
  kind := if creating then .create else .call msg.codeAddress
  target := msg.target, gasLimit := msg.gas, stateGasGrant := msg.stateGasGrant,
  transferValue := msg.shouldTransferValue, disablePrecompiles := msg.disablePrecompiles }

def Message.codeAddress (m : Message) : Option Address := match m.kind with
  | .call address => address
  | .create => none

def Message.isCreate (m : Message) : Bool := match m.kind with
  | .call _ => false
  | .create => true

structure Frame where
  message : Message
  checkpoint : Dynamic

/-- The statement names the frame's message: creation has no account code
identity, while a call names the account whose code it executes. -/
theorem Frame.message_identity (f : Frame) :
    (f.message.kind = .create → f.message.isCreate = true ∧
      f.message.codeAddress = none) ∧
    (∀ address, f.message.kind = .call address → f.message.isCreate = false ∧
      f.message.codeAddress = address) := by
  constructor
  · intro h
    simp only [Message.isCreate, Message.codeAddress, h, and_self]
  · intro address h
    simp only [Message.isCreate, Message.codeAddress, h, and_self]

/-- Reconstruct the legacy primitive input from the single checkpoint. -/
def Frame.legacyMessage (f : Frame) : Msg :=
  let m := f.message
  let c := m.context
  let d := f.checkpoint
  { (default : Msg) with
    caller := c.caller, currentTarget := c.recipient, value := c.value,
    data := c.calldata, code := c.code, depth := c.depthLeft, isStatic := c.isStatic,
    target := m.target, gas := m.gasLimit, stateGasGrant := m.stateGasGrant,
    codeAddress := m.codeAddress, shouldTransferValue := m.transferValue,
    disablePrecompiles := m.disablePrecompiles,
    accessedAddresses := d.substate.accessedAddresses,
    accessedStorageKeys := d.substate.accessedStorageKeys,
    inheritedDeletions := d.substate.selfDestructs,
    benv := { (default : Benv) with
      stat := c.block, state := d.world.state,
      storageWrites := d.world.storageWrites, createdAccounts := d.trail.createdAccounts },
    tenv := { (default : Tenv) with
      stat := c.tx, transientStorage := d.world.transientStorage } }

structure Runtime where
  pc : Nat
  context : CallContext
  dynamic : Dynamic

inductive Fault where
  | crypto (reason : CryptoError) (world : Jaune.World) (trail : Trail)
  | internal (reason : InternalError) (world : Jaune.World) (trail : Trail)

/-- Meter restoration uses the existing pure meter primitive. Failure never
hands the child's world or ordinary substate to a caller. -/
def failedResult (f : Frame) (error : EvmError) (d : Devm) : Except Fault Frame.Result :=
  let rules := f.message.context.block.rules
  let touched := ({ d with world := f.checkpoint.world }).recordTouch rules
    (f.message.context.recipient == ripemd160Address) f.message.context.recipient
  let trail := (Dynamic.ofLegacy touched).trail
  let meter := if rules.stateGas.isSome then d.mach.restoreStateGas else d.mach
  match error with
  | .revert => .ok (.revert d.output meter.gasLeft meter.stateGas trail)
  | .halt reason => .ok (.halt reason meter.stateGas trail)
  | .crypto reason => .error (.crypto reason d.world (Dynamic.ofLegacy d).trail)
  | .internal reason => .error (.internal reason d.world (Dynamic.ofLegacy d).trail)

/-- Deposit is part of settlement, after successful initcode execution. -/
def settle (f : Frame) (raw : Execution) : Except Fault Frame.Result :=
  match raw with
  | .error (error, d) => failedResult f error d
  | .ok d =>
    let deposited := if f.message.isCreate then do
      let d ← processCreateMessage.chargeCodeGas f.message.context.block.rules d
      pure (d.setCode f.message.context.recipient ⟨⟨d.output⟩⟩)
      else .ok d
    match deposited with
    | .error (error, d) => failedResult f error d
    | .ok d =>
      let d := d.recordTouch f.message.context.block.rules true f.message.context.recipient
      let view := Dynamic.ofLegacy d
      .ok (.success d.output d.gasLeft d.stateGas view.world view.substate view.trail)

inductive Entry where
  | run (runtime : Runtime)
  | done (result : Except Fault Frame.Result)

def enter (f : Frame) : Entry :=
  let msg := f.legacyMessage
  let msg := if f.message.isCreate then processCreateMessage.msg msg else msg
  match msg.benvAfterTransfer with
  | .error (error, state, created, tra) =>
    let d := ((initDevm msg).withState state).withCreatedAccounts created
    .done (failedResult f error { d with world := { d.world with transientStorage := tra } })
  | .ok benv =>
    let msg := msg.withBenv benv
    let initial := initDevm msg
    let saved := f.checkpoint
    let d := { initial with «meta» := { initial.meta with
      logs := saved.substate.logs ++ initial.logs
      refundCounter := saved.substate.refund
      accountsToDelete := saved.substate.selfDestructs
      touchedAccounts := saved.substate.touchedAccounts
      accountReads := saved.trail.accountReads
      storageReads := saved.trail.storageReads } }
    let runtime := Runtime.mk 0 f.message.context (Dynamic.ofLegacy d)
    match f.message.codeAddress with
    | some adr =>
      if !f.message.disablePrecompiles && f.message.context.block.rules.isPrecompile adr then
        .done (settle f (executePrecompile ⟨0, initSevm msg, d⟩ adr))
      else .run runtime
    | none => .run runtime

/-- Decode only the packaging of the old opcode preparation result. -/
def prepared (legacy : Jaune.Frame) (continuation : Jaune.Resume) : Frame × Continuation :=
  let message := Message.ofLegacy legacy.outer legacy.isCreate
  match continuation with
  | .call saved index size =>
    (⟨message, .ofLegacy saved⟩, ⟨.call index size, false, 0⟩)
  | .create saved address =>
    (⟨message, .ofLegacy saved⟩, ⟨.create address, false, 0⟩)
  | .callAmsterdam state saved index size charged =>
    (⟨message, .ofLegacy saved⟩,
      ⟨.call index size, true, if charged then state.newAccount else 0⟩)
  | .createAmsterdam state saved address charged =>
    (⟨message, .ofLegacy saved⟩,
      ⟨.create address, true, if charged then state.newAccount else 0⟩)

inductive Step where
  | next (runtime : Runtime)
  | spawn (frame : Frame) (continuation : Continuation) (nextPc : Nat)
  | finish (raw : Execution)

def step (runtime : Runtime) : Step :=
  match (Evm.mk runtime.pc runtime.context.toLegacy runtime.dynamic.toLegacy).step with
  | .cont pc d => .next ⟨pc, runtime.context, .ofLegacy d⟩
  | .spawn frame continuation pc =>
    let (frame, continuation) := prepared frame continuation
    .spawn frame continuation pc
  | .halt raw => .finish raw

/-- Diagnostic information is outside Frame.Result. A caller consumes only
`result`; `terminalMachine` lets this pilot observe the parent's final stack. -/
structure RunReport where
  result : Frame.Result
  terminalMachine : Machine

/-- Fuel bounds this pilot, not EVM semantics. Exhaustion is an internal fault,
so it cannot be mistaken for an EVM halt, revert, or successful execution. -/
def drive : Nat → Frame → Option Runtime → Except Fault RunReport
  | 0, f, _ => .error (.internal (.invariant (.text "shape pilot fuel exhausted"))
      f.checkpoint.world f.checkpoint.trail)
  | fuel + 1, f, none =>
    match enter f with
    | .done r => r.map fun result => ⟨result, f.checkpoint.machine⟩
    | .run runtime => drive fuel f (some runtime)
  | fuel + 1, f, some runtime =>
    match step runtime with
    | .next runtime => drive fuel f (some runtime)
    | .finish raw => (settle f raw).map fun result => ⟨result, runtime.dynamic.machine⟩
    | .spawn child continuation pc => do
      let report ← drive fuel child none
      match resume continuation child.checkpoint report.result with
      | .ok dynamic => drive fuel f (some ⟨pc, runtime.context, dynamic⟩)
      | .error reason =>
        let raw := .error (.halt reason, child.checkpoint.toLegacy)
        (settle f raw).map fun result => ⟨result, child.checkpoint.machine⟩

def topFrame (msg : Msg) : Frame :=
  ⟨Message.ofLegacy msg false, Dynamic.ofLegacy (initDevm msg)⟩

end Examples.ShapePilot.Prototype
