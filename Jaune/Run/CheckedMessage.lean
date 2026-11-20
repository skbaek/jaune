import Jaune.MessageCall.CheckedContext
import Jaune.MessageCall.CheckedExec
import Jaune.MessageCall.CheckedMessageOps
import Jaune.Execution

namespace Jaune.Checked

open Jaune

/-- Store or clear a designation, then increment its authority's nonce. Each write
applies the account-clearing rule to the surviving storage-write keys. -/
def Frame.State.writeDelegation (s : Frame.State) (authority target : Address) : Frame.State :=
  let code := if target = 0 then .empty else (eoaDelegationMarker ++ target.toBytes).toByteArray
  let world := ({ s.world with state := s.world.state.setCode authority code })
    |>.clearStorageWritesIfEmpty authority
  let world := ({ world with state := world.state.incrNonce authority })
    |>.clearStorageWritesIfEmpty authority
  s.withWorld world

namespace TopLevel

/-- Open a system call on its own transaction-start state and with an empty write ledger. -/
def systemInput (block : BlockContext) (state : State)
    (recipient : Address) (code : ByteArray) (calldata : Bytes) : Input :=
  let rules := block.rules
  let (stateGasGrant, accessedAddresses) : Nat × AdrSet := match rules.stateGas with
    | none => (0, .emptyWithCapacity)
    | some stateGas => (stateGas.systemReservoir,
      (.emptyWithCapacity : AdrSet).insertMany (rules.precompiles ++ [systemAddress, recipient]))
  let message : Message := {
    context := {
      caller := systemAddress, recipient, value := 0, calldata, code, depthLeft := 1024
      isStatic := false, block
      tx := {
        origin := systemAddress
        gasPrice := block.baseFeePerGas
        blobVersionedHashes := []
        originalState := state } }
    kind := .call
    codeAddress := some recipient
    target := some recipient
    gas := systemTransactionGas
    stateGasGrant
    transfersValue := false
    disablePrecompiles := false }
  let checkpoint := message.initialCheckpoint ⟨state, .empty, .emptyWithCapacity⟩
    accessedAddresses .emptyWithCapacity .emptyWithCapacity .emptyWithCapacity
  ⟨message, checkpoint, []⟩

/-- A prepared native message with its rollback checkpoint, or a refusal at preparation. -/
inductive Prepared where
  | refused (reason : Refusal)
  | frame (message : Message) (checkpoint : Frame.State) (authorizationRefund : Nat)

def Prepared.toPreparation : Prepared → Preparation
  | .refused reason => .refused reason
  | .frame message checkpoint refund => .frame ⟨message, checkpoint⟩ refund

/-- Apply one authorization before state gas. Successful recovery warms the authority
before its code and nonce are checked. -/
def authorizationStep (auth : Authorization) (input : Input) (refund : U256) :
    Except Fault (Input × U256) :=
  let block := input.message.context.block
  if auth.chainId != block.chainId.toU256 && auth.chainId != 0 then
    .ok (input, refund)
  else if auth.nonce = UInt64.max then
    .ok (input, refund)
  else
    match recoverAuthority auth with
    | .error (.invalidSignature _) => .ok (input, refund)
    | .error fault => .error (.crypto fault)
    | .ok authority =>
      let checkpoint := input.checkpoint.addAccessedAddress authority
      let input := { input with checkpoint }
      let world := checkpoint.world.state
      let account := world.get authority
      if ¬(account.code.isEmpty ∨ isValidDelegation account.code) then
        .ok (input, refund)
      else if account.nonce != auth.nonce then
        .ok (input, refund)
      else
        let refund := if AccountExists world authority then
          refund + (block.rules.gas.perAuthorizationIntrinsic - Gas.perAuthBaseCost).toU256
          else refund
        .ok ({ input with checkpoint := checkpoint.writeDelegation authority auth.address }, refund)

def authorizationLoop : List Authorization → Input → U256 → Except Fault (Input × U256)
  | [], input, refund => .ok (input, refund)
  | auth :: rest, input, refund => do
    let (input, refund) ← authorizationStep auth input refund
    authorizationLoop rest input refund

/-- Apply the transaction's authorization tuples, then reload the recipient's code. -/
def applyAuthorizations (input : Input) : Except Fault (Input × Nat) := do
  if !input.message.context.block.rules.delegationEnabled || input.authorizationList.isEmpty then
    .ok (input, 0)
  else
    let (authorized, refund) ← authorizationLoop input.authorizationList input 0
    match authorized.message.codeAddress with
    | none => .error (.internal (.invariant (.text "Invalid type 4 transaction: no target")))
    | some address =>
      let code := authorized.checkpoint.world.state.getCode address
      .ok ({ authorized with message.context.code := code }, refund.toNat)

/-- Resolve top-level delegation and warm the delegate without a nested-call surcharge. -/
def resolveCodeDelegation (input : Input) : Input :=
  let context := input.message.context
  match context.block.rules.delegatedCodeAddress context.code with
  | none => input
  | some address =>
    let code := input.checkpoint.world.state.getCode address
    { input with
      message := { input.message with
        context := { context with code }
        codeAddress := some address
        disablePrecompiles := true }
      checkpoint := input.checkpoint.addAccessedAddress address }

/-- Prepare a call or creation under rules without state gas. -/
def prepareWithoutStateGas (input : Input) : Except Fault Prepared := do
  match input.message.kind with
  | .create =>
    if accountHasCodeOrNonce input.checkpoint.world.state input.message.context.recipient then
      .ok (.refused (.collision (.addressCollision .none)))
    else .ok (.frame input.message input.checkpoint 0)
  | .call =>
    let (input, refund) ← applyAuthorizations input
    let input := resolveCodeDelegation input
    .ok (.frame input.message input.checkpoint refund)

/-- A failure during Amsterdam preparation, with its state at the point of failure. -/
inductive PreparationFailure where
  | halt (reason : ExceptionalHalt)
  | fault (reason : Fault)

abbrev PreparationResult (α : Type) := Except (PreparationFailure × Frame.State) α

def preparationCharge (charge : Except (ExceptionalHalt × Frame.State) Frame.State) :
    PreparationResult Frame.State :=
  charge.mapError (fun (reason, state) => (.halt reason, state))

def chargeNewAuthority (rules : StateGasRules) (authority : Address) (s : Frame.State) :
    PreparationResult Frame.State :=
  if ¬AccountExists s.world.state authority then preparationCharge (s.chargeStateGas rules.newAccount)
  else .ok s

def chargeAuthorityWrite (rules : StateGasRules) (authority : Address) (s : Frame.State)
    (paidWrites : AdrSet) : PreparationResult (Frame.State × AdrSet) :=
  if paidWrites.contains authority then .ok (s, paidWrites)
  else do
    let s ← preparationCharge (s.chargeGas rules.accountWrite)
    .ok (s, paidWrites.insert authority)

def chargeAuthorizationBase (rules : StateGasRules) (originalState : State)
    (authority target : Address) (s : Frame.State) (delegationSetFor : AdrSet) :
    PreparationResult (Frame.State × AdrSet) :=
  if target = 0 then .ok (s, delegationSetFor)
  else do
    let delegatedBeforeTx := isValidDelegation (originalState.getCode authority)
    let s ← if ¬delegatedBeforeTx && ¬delegationSetFor.contains authority then
      preparationCharge (s.chargeStateGas rules.authBase)
      else .ok s
    .ok (s, delegationSetFor.insert authority)

def applyValidatedAuthorization (rules : StateGasRules) (context : CallContext)
    (authority target : Address) (s : Frame.State) (paidWrites delegationSetFor : AdrSet) :
    PreparationResult (Frame.State × AdrSet × AdrSet) := do
  let s ← chargeNewAuthority rules authority s
  let (s, paidWrites) ← chargeAuthorityWrite rules authority s paidWrites
  let (s, delegationSetFor) ←
    chargeAuthorizationBase rules context.tx.originalState authority target s delegationSetFor
  .ok (s.writeDelegation authority target, paidWrites, delegationSetFor)

def amsterdamAuthorizationStep (rules : StateGasRules) (context : CallContext)
    (auth : Authorization) (s : Frame.State) (paidWrites delegationSetFor : AdrSet) :
    PreparationResult (Frame.State × AdrSet × AdrSet) :=
  if auth.chainId != context.block.chainId.toU256 && auth.chainId != 0 then
    .ok (s, paidWrites, delegationSetFor)
  else if auth.nonce = UInt64.max then
    .ok (s, paidWrites, delegationSetFor)
  else
    match recoverAuthority auth with
    | .error (.invalidSignature _) => .ok (s, paidWrites, delegationSetFor)
    | .error reason => .error (.fault (.crypto reason), s)
    | .ok authority =>
      let s := (s.addAccessedAddress authority).recordAccountRead context.block.rules authority
      let account := s.world.state.get authority
      if ¬(account.code.isEmpty ∨ isValidDelegation account.code) then
        .ok (s, paidWrites, delegationSetFor)
      else if account.nonce != auth.nonce then
        .ok (s, paidWrites, delegationSetFor)
      else
        applyValidatedAuthorization rules context authority auth.address s paidWrites delegationSetFor

def amsterdamAuthorizationLoop (rules : StateGasRules) (context : CallContext) :
    List Authorization → Frame.State → AdrSet → AdrSet →
      PreparationResult (Frame.State × AdrSet × AdrSet)
  | [], s, paidWrites, delegationSetFor => .ok (s, paidWrites, delegationSetFor)
  | auth :: rest, s, paidWrites, delegationSetFor => do
    let (s, paidWrites, delegationSetFor) ←
      amsterdamAuthorizationStep rules context auth s paidWrites delegationSetFor
    amsterdamAuthorizationLoop rules context rest s paidWrites delegationSetFor

def _root_.Jaune.Checked.Message.isCreate (message : Message) : Bool :=
  match message.kind with
  | .create => true
  | .call => false

def applyAmsterdamAuthorizations (rules : StateGasRules) (input : Input) :
    PreparationResult Frame.State := do
  let context := input.message.context
  let paidWrites : AdrSet := {context.caller}
  let paidWrites :=
    if input.message.isCreate || context.value != 0 then paidWrites.insert context.recipient
    else paidWrites
  let (s, _, _) ← amsterdamAuthorizationLoop rules context input.authorizationList input.checkpoint
    paidWrites .emptyWithCapacity
  .ok s

def resolveAmsterdamCall (message : Message) (s : Frame.State) :
    PreparationResult (Message × Frame.State) := do
  let context := message.context
  let rules := context.block.rules
  let (delegated, codeAddress, accessCost) :=
    Checked.ForkRules.delegationCost rules s context.recipient
  let s ← preparationCharge (s.chargeGas accessCost)
  let (code, s) := completeDelegationAccess s delegated codeAddress
  let s := s.recordAccountRead rules codeAddress
  .ok ({ message with
    context := { context with code }
    codeAddress := some codeAddress
    disablePrecompiles := delegated }, s)

def dispatchAmsterdam (rules : StateGasRules) (message : Message) (s : Frame.State) :
    PreparationResult (Message × Frame.State) := do
  let context := message.context
  let recipient := context.recipient
  let s := s.recordAccountRead context.block.rules recipient
  match message.kind with
  | .create =>
    if accountHasCodeOrNonce s.world.state recipient then
      .error (.halt (.addressCollision .none), s)
    else do
      let s ← if (context.tx.originalState.get recipient).isEmpty then
        preparationCharge (s.chargeStateGas rules.newAccount)
        else .ok s
      .ok (message, s)
  | .call =>
    let s ← if context.value != 0 && decide (s.world.state.get recipient).isEmpty then
      preparationCharge (s.chargeStateGas rules.newAccount)
      else .ok s
    resolveAmsterdamCall message s

def prepareAmsterdamFrame (rules : StateGasRules) (input : Input) :
    PreparationResult (Message × Frame.State) := do
  let s ← if input.authorizationList.isEmpty then .ok input.checkpoint
    else applyAmsterdamAuthorizations rules input
  let s := if input.authorizationList.isEmpty then s else s.commitStateGas
  dispatchAmsterdam rules input.message s

/-- Prepare a native Checked message with its fork's charge and refusal rules. -/
def prepareNative (input : Input) : Except Fault Prepared :=
  match input.message.context.block.rules.stateGas with
  | none => prepareWithoutStateGas input
  | some rules =>
    match prepareAmsterdamFrame rules input with
    | .ok (message, s) => .ok (.frame message s 0)
    | .error (.fault fault, _) => .error fault
    | .error (.halt reason, s) => .ok (.refused (.stateGas reason input.message.stateGasGrant
        s.trail.accountReads s.trail.storageReads))

/-- Prepare and execute a top-level Checked input, preserving the entered root when present. -/
def runNative (input : Input) : Except Fault Run :=
  prepareNative input >>= fun prepared => prepared.toPreparation.run

/-- The world, gas and effects reported by a settled top-level message. -/
structure Settlement where
  state : State
  gasLeft : Nat := 0
  stateGasLeft : Nat := 0
  stateGasUsed : Int := 0
  error : Option SettledHalt := none
  returnData : Bytes := []
  logs : List Log := []
  accountsToDelete : AdrSet := .emptyWithCapacity
  touchedAccounts : AdrSet := .emptyWithCapacity
  accountReads : AdrSet := .emptyWithCapacity
  storageReads : KeySet := .emptyWithCapacity
  storageWrites : KeySet := .emptyWithCapacity

/-- A refusal keeps the entry world. A settled frame reports its successful world or
its rollback checkpoint. Reads and storage writes are observed on state-gas forks. -/
def Run.settlement (run : Run) (input : Input) : Settlement :=
  let entryWorld := input.checkpoint.world
  match run with
  | .refused (.collision reason) =>
    { state := entryWorld.state, error := some (.halt reason) }
  | .refused (.stateGas reason grant accountReads storageReads) =>
    { state := entryWorld.state, error := some (.halt reason), stateGasLeft := grant
      accountReads, storageReads, storageWrites := entryWorld.storageWrites }
  | .frame f _ run =>
    let result := run.result
    let (world, substate) := match result with
      | .success _ _ _ world substate _ => (world, some substate)
      | _ => (f.checkpoint.world, none)
    let settled : Settlement := {
      state := world.state
      gasLeft := result.gasLeft
      error := result.error?
      returnData := result.output
      logs := (substate.map Substate.logs).getD []
      accountsToDelete := (substate.map Substate.selfDestructs).getD .emptyWithCapacity }
    match input.message.context.block.rules.stateGas with
    | none => { settled with
        touchedAccounts := (substate.map Substate.touchedAccounts).getD .emptyWithCapacity }
    | some _ =>
      let gas := result.stateGas
      { settled with
        stateGasLeft := gas.left
        stateGasUsed := Int.ofNat f.message.stateGasGrant - Int.ofNat gas.left +
          Int.ofNat gas.spilled + Int.ofNat gas.committedSpill
        accountReads := result.trail.accountReads
        storageReads := result.trail.storageReads
        storageWrites := world.storageWrites }

end TopLevel

/-- The actual message and input of a protocol system call. -/
structure SystemRun where
  input : TopLevel.Input
  message : TopLevel.Run

def SystemRun.settlement (run : SystemRun) : TopLevel.Settlement :=
  run.message.settlement run.input

/-- Run a protocol system call on its current world and validate the refund counter. -/
def processSystemRun (block : BlockContext) (state : State)
    (target : Address) (code : ByteArray) (data : Bytes) : Except Fault SystemRun := do
  let input := TopLevel.systemInput block state target code data
  let run ← TopLevel.runNative input
  let _ ← run.refundCounter
  pure ⟨input, run⟩

def processSystemTransaction (block : BlockContext) (state : State)
    (target : Address) (code : ByteArray) (data : Bytes) : Except Fault TopLevel.Settlement :=
  (processSystemRun block state target code data).map SystemRun.settlement

end Jaune.Checked
