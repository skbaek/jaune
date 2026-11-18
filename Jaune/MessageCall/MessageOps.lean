import Jaune.Execution
import Jaune.MessageCall.State

/-!
# Message operations over `Frame.State` (goal `jaune-shape-and-names-v1`, W3 unit W3-2c)

The successors of `MessageOp.step`, its four tails, the child-message builders and the
delegation helpers, written over the `CallContext` a frame reads and the lifetime-grouped
`Frame.State` instead of `Sevm` and `Devm`:

* a message operation either finishes in place, with a halt-only outcome
  (`Except (ExceptionalHalt × Frame.State) Frame.State`, design §2.5), or spawns a child `Frame`
  whose checkpoint is the caller's state after call preparation;
* the `Pending` a spawn hands the driver is the final one: where the child's result goes and
  whether the spawn charged a new account's state gas. It carries no output and no stored error;
* `callMessage` and `createMessage` read the `CallContext` instead of a `Sevm`;
* the gas obligations of `Jaune.MessageCall.StepGas` (`GasDecreasing`, `Halt`) are restated over
  the new outcome.

Every definition is staged under `Jaune.Staging` beside the `Devm` interpreter, which nothing here
replaces yet. The squares against the old definitions, under `Frame.State.ofDevm` and
`CallContext.ofSevm`, are in `Jaune.Bridge.G2b.MessageOps`.
-/

namespace Jaune.Staging

open Jaune

/-! ### What a message operation hands the driver -/

/-- What the caller waits with while its child runs, besides the saved caller itself. -/
structure Pending : Type where
  /-- Where the child's result goes. -/
  target : ReturnTarget
  /-- Whether the spawn charged a new account's state gas, which a failed child refunds. -/
  newAccountCharged : Bool

/-- The result of a message operation: finished in place, or a child frame to run. -/
inductive MessageOp.Outcome : Type
  /-- The operation finished without opening a frame. -/
  | done (r : Except (ExceptionalHalt × Frame.State) Frame.State)
  /-- The operation opens a child frame. -/
  | spawn (child : Frame) (pending : Pending)

/-- A message operation's result, from a computation that can halt first. -/
def MessageOp.Outcome.ofExcept :
    Except (ExceptionalHalt × Frame.State) MessageOp.Outcome → MessageOp.Outcome
  | .error e => .done (.error e)
  | .ok step => step

/-! ### Delegation (EIP-7702) -/

/-- Nested code access with Prague's cold access (`accessDelegation`): for a delegation
designator, warm the delegated address and read its code. -/
def accessDelegation (s : Frame.State) (adr : Address) :
    Bool × Address × ByteArray × Nat × Frame.State :=
  let code := s.code adr
  match getDelegatedCodeAddress code with
  | some adr =>
    let accessGasCost := Jaune.accessCost adr s.accessedAddresses
    let s' := s.addAccessedAddress adr
    ⟨true, adr, s.code adr, accessGasCost, s'⟩
  | none => ⟨false, adr, code, 0, s⟩

/-- Nested code access with the schedule's cold access. -/
def GasSchedule.accessDelegation (gas : GasSchedule) (s : Frame.State) (adr : Address) :
    Bool × Address × ByteArray × Nat × Frame.State :=
  let code := s.code adr
  match getDelegatedCodeAddress code with
  | some adr =>
    let accessGasCost := gas.accessCost adr s.accessedAddresses
    let s' := s.addAccessedAddress adr
    ⟨true, adr, s.code adr, accessGasCost, s'⟩
  | none => ⟨false, adr, code, 0, s⟩

/-- `calculate_delegation_cost`: the designation and the delegated address's price, without
warming it or reading its code. -/
def GasSchedule.delegationCost (gas : GasSchedule) (s : Frame.State) (adr : Address) :
    Bool × Address × Nat :=
  match getDelegatedCodeAddress (s.code adr) with
  | some delegated => ⟨true, delegated, gas.accessCost delegated s.accessedAddresses⟩
  | none => ⟨false, adr, 0⟩

/-- Fork-aware nested code access; with delegation off the state is unchanged. -/
def ForkRules.accessDelegation (rules : ForkRules) (s : Frame.State) (adr : Address) :
    Bool × Address × ByteArray × Nat × Frame.State :=
  if rules.delegationEnabled then GasSchedule.accessDelegation rules.gas s adr
  else ⟨false, adr, s.code adr, 0, s⟩

/-- Fork-aware price discovery. -/
def ForkRules.delegationCost (rules : ForkRules) (s : Frame.State) (adr : Address) :
    Bool × Address × Nat :=
  if rules.delegationEnabled then GasSchedule.delegationCost rules.gas s adr
  else ⟨false, adr, 0⟩

/-- The state-access half of delegation resolution, after the delegated price has passed its
affordability check. -/
def completeDelegationAccess (s : Frame.State) (delegated : Bool) (adr : Address) :
    ByteArray × Frame.State :=
  let s := if delegated then s.addAccessedAddress adr else s
  ⟨s.code adr, s⟩

/-! ### Building a child's message -/

/-- The message a call-family operation sends its child. -/
def callMessage (ctx : CallContext) (gas : Nat) (value : U256) (caller target codeAddress : Address)
    (transfersValue isStaticcall : Bool) (calldata : Bytes) (code : ByteArray)
    (disablePrecompiles : Bool) : Message :=
  { context :=
      { caller := caller, recipient := target, value := value, calldata := calldata, code := code
        depthLeft := ctx.depthLeft - 1, isStatic := isStaticcall || ctx.isStatic, tx := ctx.tx
        block := ctx.block }
    kind := .call
    codeAddress := some codeAddress
    target := some target
    gas := gas
    stateGasGrant := 0
    transfersValue := transfersValue
    disablePrecompiles := disablePrecompiles }

/-- The message a creation operation sends its child: the initcode is the code run, the calldata
is empty. -/
def createMessage (ctx : CallContext) (createGas : Nat) (endowment : U256) (newAddress : Address)
    (initcode : Bytes) : Message :=
  { context :=
      { caller := ctx.recipient, recipient := newAddress, value := endowment, calldata := []
        code := .mk <| .mk initcode, depthLeft := ctx.depthLeft - 1, isStatic := false
        tx := ctx.tx, block := ctx.block }
    kind := .create
    codeAddress := none
    target := none
    gas := createGas
    stateGasGrant := 0
    transfersValue := true
    disablePrecompiles := false }

/-! ### The four tails -/

/-- `generic_create` before state gas: the initcode bound, the child grant, the preflight, the
creator's nonce, the collision test, and the spawn. The checkpoint is the creator after its nonce
increment. -/
def genericCreate.step (ctx : CallContext) (s : Frame.State) (endowment : U256)
    (newAddress : Address) (memoryIndex memorySize : Nat) : MessageOp.Outcome :=
  MessageOp.Outcome.ofExcept do
    let calldata := s.memory.data.sliceD memoryIndex memorySize 0
    Except.assert
      (ctx.block.rules.creation.initCodeLimit →
        memorySize ≤ ctx.block.rules.code.maxInitCodeSize)
      (.outOfGas .none, s)
    let createGas := except64th s.gasLeft
    let s := s.withGasLeft (s.gasLeft - createGas)
    s.assertDynamic ctx
    let s := s.withReturnData []
    let sender := s.account ctx.recipient
    if sender.balance < endowment ∨ sender.nonce = UInt64.max ∨ ctx.depthLeft = 0 then
      let s ← (s.withGasLeft (s.gasLeft + createGas)).push 0
      return .done (.ok s)
    let s := s.incrNonce ctx.recipient
    let s := s.addAccessedAddress newAddress
    if
      (let target := s.account newAddress
       target.nonce ≠ (0 : UInt64) ∨
       target.code.size ≠ 0) then
      let s ← s.push 0
      return .done (.ok s)
    let message := createMessage ctx createGas endowment newAddress calldata
    return .spawn ⟨message, s⟩ ⟨.create newAddress, false⟩

/-- `generic_call` before state gas: the depth check, and the spawn. -/
def genericCall.step (ctx : CallContext) (s : Frame.State) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat) (code : ByteArray)
    (disablePrecompiles : Bool) : MessageOp.Outcome :=
  let s1 := s.withReturnData []
  if ctx.depthLeft = 0 then
    MessageOp.Outcome.ofExcept do
      let s ← (s1.withGasLeft (s1.gasLeft + gas)).push 0
      return .done (.ok s)
  else
    let calldata := s1.memory.data.sliceD inputIndex inputSize 0
    let message :=
      callMessage ctx gas value caller target codeAddress shouldTransferValue isStaticcall
        calldata code disablePrecompiles
    .spawn ⟨message, s1⟩ ⟨.call outputIndex outputSize, false⟩

/-- `generic_call` under state gas: the preflight that refuses the spawn, returning both grants
and refilling a charged creation, or the spawn with the reservoir as the child's grant. -/
def genericCallAmsterdam.step (ctx : CallContext) (state : StateGasRules) (s : Frame.State)
    (gas reservoir : Nat) (value : U256) (caller target codeAddress : Address)
    (shouldTransferValue isStaticcall : Bool) (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles newAccountCharged insufficientBalance : Bool) :
    MessageOp.Outcome :=
  let s1 := s.withReturnData []
  if ctx.depthLeft = 0 ∨ insufficientBalance then
    MessageOp.Outcome.ofExcept do
      let s1 := s1.restoreChildGas gas reservoir
      let s1 := if newAccountCharged then s1.creditStateGasRefund state.newAccount else s1
      let s ← s1.push 0
      return .done (.ok s)
  else
    let calldata := s1.memory.data.sliceD inputIndex inputSize 0
    let message :=
      { callMessage ctx gas value caller target codeAddress shouldTransferValue isStaticcall
          calldata code disablePrecompiles
        with stateGasGrant := reservoir }
    .spawn ⟨message, s1⟩ ⟨.call outputIndex outputSize, newAccountCharged⟩

/-- `generic_create` under state gas: the preflight, the destination access with its creation
charge, the withheld grant, the collision that consumes it, and the spawn with the whole
reservoir. The checkpoint is the creator after its nonce increment. -/
def genericCreateAmsterdam.step (ctx : CallContext) (state : StateGasRules) (s : Frame.State)
    (endowment : U256) (newAddress : Address) (memoryIndex memorySize : Nat) :
    MessageOp.Outcome :=
  MessageOp.Outcome.ofExcept do
    let calldata := s.memory.data.sliceD memoryIndex memorySize 0
    let s := s.withReturnData []
    let s := s.recordAccountRead ctx.block.rules ctx.recipient
    let sender := s.account ctx.recipient
    if sender.balance < endowment ∨ sender.nonce = UInt64.max ∨ ctx.depthLeft = 0 then
      let s ← s.push 0
      return .done (.ok s)
    let s := s.addAccessedAddress newAddress
    let s := s.recordAccountRead ctx.block.rules newAddress
    let newAccountCharged := (s.account newAddress).isEmpty
    let s ← if newAccountCharged then s.chargeStateGas state.newAccount else .ok s
    let ⟨createGas, s⟩ := s.withholdCreateGas
    if
      (let target := s.account newAddress
       target.nonce ≠ (0 : UInt64) ∨
       target.code.size ≠ 0) then
      let s := s.incrNonce ctx.recipient
      let s ← s.push 0
      return .done (.ok s)
    let ⟨reservoir, s⟩ := s.drainStateGasReservoir
    let s := s.incrNonce ctx.recipient
    let message :=
      { createMessage ctx createGas endowment newAddress calldata with stateGasGrant := reservoir }
    return .spawn ⟨message, s⟩ ⟨.create newAddress, decide newAccountCharged⟩

/-! ### The step -/

/-- One message operation over the frame's context and state. -/
def MessageOp.step (ctx : CallContext) (s : Frame.State) : MessageOp → MessageOp.Outcome
  | .create =>
    match ctx.block.rules.stateGas with
    | none =>
      MessageOp.Outcome.ofExcept do
        let ⟨endowment, s⟩ ← s.pop
        let ⟨memoryIndex, s⟩ ← s.popToNat
        let ⟨memorySize, s⟩ ← s.popToNat
        let extendCost := s.extCost [⟨memoryIndex, memorySize⟩]
        let initCodeCost := if ctx.block.rules.creation.initCodeLimit then
          Gas.initcodeWordCost * ceilDiv memorySize 32 else 0
        let s ← s.chargeGas (ctx.block.rules.gas.createAccess + extendCost + initCodeCost)
        let s := s.memExtends [⟨memoryIndex, memorySize⟩]
        let newAddress := computeContractAddress ctx.recipient (s.account ctx.recipient).nonce
        return genericCreate.step ctx s endowment newAddress memoryIndex memorySize
    | some state =>
      MessageOp.Outcome.ofExcept do
        s.assertDynamic ctx
        let ⟨endowment, s⟩ ← s.pop
        let ⟨memoryIndex, s⟩ ← s.popToNat
        let ⟨memorySize, s⟩ ← s.popToNat
        let extendCost := s.extCost [⟨memoryIndex, memorySize⟩]
        let initCodeCost := Gas.initcodeWordCost * ceilDiv memorySize 32
        let s ← s.chargeGas (ctx.block.rules.gas.createAccess + extendCost + initCodeCost)
        Except.assert (memorySize ≤ ctx.block.rules.code.maxInitCodeSize) (.outOfGas .none, s)
        let s := s.memExtends [⟨memoryIndex, memorySize⟩]
        let newAddress := computeContractAddress ctx.recipient (s.account ctx.recipient).nonce
        return genericCreateAmsterdam.step ctx state s endowment newAddress memoryIndex memorySize
  | .create2 =>
    if ctx.block.rules.opcodes.create2 then
      match ctx.block.rules.stateGas with
      | none =>
        MessageOp.Outcome.ofExcept do
          let ⟨endowment, s⟩ ← s.pop
          let ⟨memoryIndex, s⟩ ← s.popToNat
          let ⟨memorySize, s⟩ ← s.popToNat
          let ⟨salt, s⟩ ← s.pop
          let extendCost := s.extCost [⟨memoryIndex, memorySize⟩]
          let initCodeHashCost := Gas.keccak256Word * ceilDiv memorySize 32
          let initCodeCost := if ctx.block.rules.creation.initCodeLimit then
            Gas.initcodeWordCost * ceilDiv memorySize 32 else 0
          let s ← s.chargeGas
            (ctx.block.rules.gas.createAccess + initCodeHashCost + extendCost + initCodeCost)
          let s := s.memExtends [⟨memoryIndex, memorySize⟩]
          let newAddress :=
            create2NewAddress ctx.recipient salt (s.memory.data.sliceD memoryIndex memorySize 0)
          return genericCreate.step ctx s endowment newAddress memoryIndex memorySize
      | some state =>
        MessageOp.Outcome.ofExcept do
          s.assertDynamic ctx
          let ⟨endowment, s⟩ ← s.pop
          let ⟨memoryIndex, s⟩ ← s.popToNat
          let ⟨memorySize, s⟩ ← s.popToNat
          let ⟨salt, s⟩ ← s.pop
          let extendCost := s.extCost [⟨memoryIndex, memorySize⟩]
          let initCodeHashCost := Gas.keccak256Word * ceilDiv memorySize 32
          let initCodeCost := Gas.initcodeWordCost * ceilDiv memorySize 32
          let s ← s.chargeGas
            (ctx.block.rules.gas.createAccess + initCodeHashCost + extendCost + initCodeCost)
          Except.assert (memorySize ≤ ctx.block.rules.code.maxInitCodeSize) (.outOfGas .none, s)
          let s := s.memExtends [⟨memoryIndex, memorySize⟩]
          let newAddress :=
            create2NewAddress ctx.recipient salt (s.memory.data.sliceD memoryIndex memorySize 0)
          return genericCreateAmsterdam.step ctx state s endowment newAddress memoryIndex
            memorySize
    else
      MessageOp.Outcome.ofExcept (.error (.invalidOpcode .none, s))
  | .call =>
    match ctx.block.rules.stateGas with
    | none =>
      MessageOp.Outcome.ofExcept do
        let ⟨gas, s⟩ ← s.pop
        let ⟨callee, s⟩ ← s.popToAddress
        let ⟨value, s⟩ ← s.pop
        let ⟨inputIndex, s⟩ ← s.popToNat
        let ⟨inputSize, s⟩ ← s.popToNat
        let ⟨outputIndex, s⟩ ← s.popToNat
        let ⟨outputSize, s⟩ ← s.popToNat
        let extendCost := s.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let gasRules := ctx.block.rules.gas
        let preAccessCost :=
          match ctx.block.rules.access with
          | .eip2929 => gasRules.accessCost callee s.accessedAddresses
          | .flat g => g.call
        let s :=
          match ctx.block.rules.access with
          | .eip2929 => s.addAccessedAddress callee
          | .flat _ => s
        let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, s⟩ :=
          ForkRules.accessDelegation ctx.block.rules s callee
        let accessCost := preAccessCost + delegatedAccessGasCost
        let createCost := if (¬ (s.account callee).isEmpty) ∨ value = 0 then 0 else Gas.newAccount
        let transferCost := if value = 0 then 0 else gasRules.callValue
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas value.toNat gas.toNat s.gasLeft extendCost
            (accessCost + createCost + transferCost)
        let s ← s.chargeGas (msgCallCost + extendCost)
        Except.assert (!ctx.isStatic ∨ value = 0) (.writeInStaticContext .none, s)
        let s := s.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let senderBal := (s.account ctx.recipient).balance
        if senderBal < value then
          let s ← s.push 0
          return .done (.ok ((s.withReturnData []).withGasLeft (s.gasLeft + msgCallStipend)))
        else
          return genericCall.step ctx s msgCallStipend value ctx.recipient callee newCodeAddress
            true false inputIndex inputSize outputIndex outputSize code disablePrecompiles
    | some state =>
      MessageOp.Outcome.ofExcept do
        let ⟨gas, s⟩ ← s.pop
        let ⟨callee, s⟩ ← s.popToAddress
        let ⟨value, s⟩ ← s.pop
        let ⟨inputIndex, s⟩ ← s.popToNat
        let ⟨inputSize, s⟩ ← s.popToNat
        let ⟨outputIndex, s⟩ ← s.popToNat
        let ⟨outputSize, s⟩ ← s.popToNat
        Except.assert (!ctx.isStatic ∨ value = 0) (.writeInStaticContext .none, s)
        let gasRules := ctx.block.rules.gas
        let extendCost := s.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let accessGas := gasRules.accessCost callee s.accessedAddresses
        let transferCost := if value = 0 then 0 else gasRules.callValue
        Except.assert (accessGas + transferCost + extendCost ≤ s.gasLeft) (.outOfGas .none, s)
        let s := s.addAccessedAddress callee
        let ⟨disablePrecompiles, newCodeAddress, delegatedAccessGasCost⟩ :=
          ForkRules.delegationCost ctx.block.rules s callee
        let s := s.recordAccountRead ctx.block.rules callee
        let extraGas := accessGas + transferCost + delegatedAccessGasCost
        Except.assert (extraGas + extendCost ≤ s.gasLeft) (.outOfGas .none, s)
        let s := s.recordAccountRead ctx.block.rules newCodeAddress
        let ⟨code, s⟩ := completeDelegationAccess s disablePrecompiles newCodeAddress
        let s ← s.chargeGas (extraGas + extendCost)
        let newAccountCharged := value ≠ 0 ∧ (s.account callee).isEmpty
        let s ← if newAccountCharged then s.chargeStateGas state.newAccount else .ok s
        let ⟨msgCallCost, msgCallStipend⟩ := calculateMsgCallGas value.toNat gas.toNat s.gasLeft 0 0
        let s ← s.chargeGas msgCallCost
        let ⟨reservoir, s⟩ := s.drainStateGasReservoir
        let s := s.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let senderBal := (s.account ctx.recipient).balance
        return genericCallAmsterdam.step ctx state s msgCallStipend reservoir value ctx.recipient
          callee newCodeAddress true false inputIndex inputSize outputIndex outputSize code
          disablePrecompiles (decide newAccountCharged) (decide (senderBal < value))
  | .callcode =>
    match ctx.block.rules.stateGas with
    | none =>
      MessageOp.Outcome.ofExcept do
        let ⟨gas, s⟩ ← s.pop
        let ⟨codeAddress, s⟩ ← s.popToAddress
        let ⟨value, s⟩ ← s.pop
        let ⟨inputIndex, s⟩ ← s.popToNat
        let ⟨inputSize, s⟩ ← s.popToNat
        let ⟨outputIndex, s⟩ ← s.popToNat
        let ⟨outputSize, s⟩ ← s.popToNat
        let extendCost := s.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let gasRules := ctx.block.rules.gas
        let preAccessCost :=
          match ctx.block.rules.access with
          | .eip2929 => gasRules.accessCost codeAddress s.accessedAddresses
          | .flat g => g.call
        let s :=
          match ctx.block.rules.access with
          | .eip2929 => s.addAccessedAddress codeAddress
          | .flat _ => s
        let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, s⟩ :=
          ForkRules.accessDelegation ctx.block.rules s codeAddress
        let accessCost := preAccessCost + delegatedAccessGasCost
        let transferCost := if value = 0 then 0 else gasRules.callValue
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas value.toNat gas.toNat s.gasLeft extendCost (accessCost + transferCost)
        let s ← s.chargeGas (msgCallCost + extendCost)
        let s := s.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let senderBal := (s.account ctx.recipient).balance
        if senderBal < value then
          let s ← s.push 0
          return .done (.ok ((s.withGasLeft (s.gasLeft + msgCallStipend)).withReturnData []))
        else
          return genericCall.step ctx s msgCallStipend value ctx.recipient ctx.recipient
            newCodeAddress true false inputIndex inputSize outputIndex outputSize code
            disablePrecompiles
    | some state =>
      MessageOp.Outcome.ofExcept do
        let ⟨gas, s⟩ ← s.pop
        let ⟨codeAddress, s⟩ ← s.popToAddress
        let ⟨value, s⟩ ← s.pop
        let ⟨inputIndex, s⟩ ← s.popToNat
        let ⟨inputSize, s⟩ ← s.popToNat
        let ⟨outputIndex, s⟩ ← s.popToNat
        let ⟨outputSize, s⟩ ← s.popToNat
        let senderBal := (s.account ctx.recipient).balance
        let gasRules := ctx.block.rules.gas
        let extendCost := s.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let accessGas := gasRules.accessCost codeAddress s.accessedAddresses
        let transferCost := if value = 0 then 0 else gasRules.callValue
        Except.assert (accessGas + extendCost + transferCost ≤ s.gasLeft) (.outOfGas .none, s)
        let s := s.addAccessedAddress codeAddress
        let ⟨disablePrecompiles, newCodeAddress, delegatedAccessGasCost⟩ :=
          ForkRules.delegationCost ctx.block.rules s codeAddress
        let s := s.recordAccountRead ctx.block.rules codeAddress
        let extraGas := accessGas + transferCost + delegatedAccessGasCost
        Except.assert (extraGas + extendCost ≤ s.gasLeft) (.outOfGas .none, s)
        let s := s.recordAccountRead ctx.block.rules newCodeAddress
        let ⟨code, s⟩ := completeDelegationAccess s disablePrecompiles newCodeAddress
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas value.toNat gas.toNat s.gasLeft extendCost extraGas
        let s ← s.chargeGas (msgCallCost + extendCost)
        let ⟨reservoir, s⟩ := s.drainStateGasReservoir
        let s := s.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        return genericCallAmsterdam.step ctx state s msgCallStipend reservoir value ctx.recipient
          ctx.recipient newCodeAddress true false inputIndex inputSize outputIndex outputSize code
          disablePrecompiles false (decide (senderBal < value))
  | .delegatecall =>
    match ctx.block.rules.stateGas with
    | none =>
      MessageOp.Outcome.ofExcept do
        let ⟨gas, s⟩ ← s.pop
        let ⟨codeAddress, s⟩ ← s.popToAddress
        let ⟨inputIndex, s⟩ ← s.popToNat
        let ⟨inputSize, s⟩ ← s.popToNat
        let ⟨outputIndex, s⟩ ← s.popToNat
        let ⟨outputSize, s⟩ ← s.popToNat
        let extendCost := s.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let gasRules := ctx.block.rules.gas
        let preAccessCost :=
          match ctx.block.rules.access with
          | .eip2929 => gasRules.accessCost codeAddress s.accessedAddresses
          | .flat g => g.call
        let s :=
          match ctx.block.rules.access with
          | .eip2929 => s.addAccessedAddress codeAddress
          | .flat _ => s
        let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, s⟩ :=
          ForkRules.accessDelegation ctx.block.rules s codeAddress
        let accessCost := preAccessCost + delegatedAccessGasCost
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas 0 gas.toNat s.gasLeft extendCost accessCost
        let s ← s.chargeGas (msgCallCost + extendCost)
        let s := s.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        return genericCall.step ctx s msgCallStipend ctx.value ctx.caller ctx.recipient
          newCodeAddress false false inputIndex inputSize outputIndex outputSize code
          disablePrecompiles
    | some state =>
      MessageOp.Outcome.ofExcept do
        let ⟨gas, s⟩ ← s.pop
        let ⟨codeAddress, s⟩ ← s.popToAddress
        let ⟨inputIndex, s⟩ ← s.popToNat
        let ⟨inputSize, s⟩ ← s.popToNat
        let ⟨outputIndex, s⟩ ← s.popToNat
        let ⟨outputSize, s⟩ ← s.popToNat
        let gasRules := ctx.block.rules.gas
        let extendCost := s.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let accessGas := gasRules.accessCost codeAddress s.accessedAddresses
        let transferCost := 0
        Except.assert (accessGas + extendCost ≤ s.gasLeft) (.outOfGas .none, s)
        let s := s.addAccessedAddress codeAddress
        let ⟨disablePrecompiles, newCodeAddress, delegatedAccessGasCost⟩ :=
          ForkRules.delegationCost ctx.block.rules s codeAddress
        let s := s.recordAccountRead ctx.block.rules codeAddress
        let extraGas := accessGas + transferCost + delegatedAccessGasCost
        Except.assert (extraGas + extendCost ≤ s.gasLeft) (.outOfGas .none, s)
        let s := s.recordAccountRead ctx.block.rules newCodeAddress
        let ⟨code, s⟩ := completeDelegationAccess s disablePrecompiles newCodeAddress
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas 0 gas.toNat s.gasLeft extendCost extraGas
        let s ← s.chargeGas (msgCallCost + extendCost)
        let ⟨reservoir, s⟩ := s.drainStateGasReservoir
        let s := s.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        return genericCallAmsterdam.step ctx state s msgCallStipend reservoir ctx.value ctx.caller
          ctx.recipient newCodeAddress false false inputIndex inputSize outputIndex outputSize code
          disablePrecompiles false false
  | .staticcall =>
    match ctx.block.rules.stateGas with
    | none =>
      MessageOp.Outcome.ofExcept do
        let ⟨gas, s⟩ ← s.pop
        let ⟨target, s⟩ ← s.popToAddress
        let ⟨inputIndex, s⟩ ← s.popToNat
        let ⟨inputSize, s⟩ ← s.popToNat
        let ⟨outputIndex, s⟩ ← s.popToNat
        let ⟨outputSize, s⟩ ← s.popToNat
        let extendCost := s.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let gasRules := ctx.block.rules.gas
        let preAccessCost :=
          match ctx.block.rules.access with
          | .eip2929 => gasRules.accessCost target s.accessedAddresses
          | .flat g => g.call
        let s :=
          match ctx.block.rules.access with
          | .eip2929 => s.addAccessedAddress target
          | .flat _ => s
        let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, s⟩ :=
          ForkRules.accessDelegation ctx.block.rules s target
        let accessCost := preAccessCost + delegatedAccessGasCost
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas 0 gas.toNat s.gasLeft extendCost accessCost
        let s ← s.chargeGas (msgCallCost + extendCost)
        let s := s.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        return genericCall.step ctx s msgCallStipend 0 ctx.recipient target newCodeAddress true
          true inputIndex inputSize outputIndex outputSize code disablePrecompiles
    | some state =>
      MessageOp.Outcome.ofExcept do
        let ⟨gas, s⟩ ← s.pop
        let ⟨codeAddress, s⟩ ← s.popToAddress
        let ⟨inputIndex, s⟩ ← s.popToNat
        let ⟨inputSize, s⟩ ← s.popToNat
        let ⟨outputIndex, s⟩ ← s.popToNat
        let ⟨outputSize, s⟩ ← s.popToNat
        let gasRules := ctx.block.rules.gas
        let extendCost := s.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let accessGas := gasRules.accessCost codeAddress s.accessedAddresses
        let transferCost := 0
        Except.assert (accessGas + extendCost ≤ s.gasLeft) (.outOfGas .none, s)
        let s := s.addAccessedAddress codeAddress
        let ⟨disablePrecompiles, newCodeAddress, delegatedAccessGasCost⟩ :=
          ForkRules.delegationCost ctx.block.rules s codeAddress
        let s := s.recordAccountRead ctx.block.rules codeAddress
        let extraGas := accessGas + transferCost + delegatedAccessGasCost
        Except.assert (extraGas + extendCost ≤ s.gasLeft) (.outOfGas .none, s)
        let s := s.recordAccountRead ctx.block.rules newCodeAddress
        let ⟨code, s⟩ := completeDelegationAccess s disablePrecompiles newCodeAddress
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas 0 gas.toNat s.gasLeft extendCost extraGas
        let s ← s.chargeGas (msgCallCost + extendCost)
        let ⟨reservoir, s⟩ := s.drainStateGasReservoir
        let s := s.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        return genericCallAmsterdam.step ctx state s msgCallStipend reservoir 0 ctx.recipient
          codeAddress newCodeAddress true true inputIndex inputSize outputIndex outputSize code
          disablePrecompiles false false

/-! ### Gas obligations (`Jaune.MessageCall.StepGas`, restated) -/

/-- A state's spill: what an exceptional halt keeps of its state-gas meter. -/
def _root_.Jaune.Frame.State.spill (s : Frame.State) : Nat :=
  s.stateGas.spilled + s.stateGas.committedSpill

/-- The call-family obligation against the measure `n` the step began with: a finished
operation leaves less, and a spawn's child grant plus its checkpoint's measure is less, with the
child under the spawning frame's rules. -/
def MessageOp.Outcome.GasDecreasing (ctx : CallContext) (n : Nat) : MessageOp.Outcome → Prop
  | .done r => ∀ s, r = .ok s → s.machine.gasMeasure < n
  | .spawn child _ =>
      child.message.gas + child.checkpoint.machine.gasMeasure < n ∧
        child.message.context.block.rules = ctx.block.rules

/-- What a message operation owes on its halt branch: a spill `n` still covers. The outcome type
has no revert, so the old "no `Revert` tag" clause is gone. -/
def MessageOp.Outcome.Halt (n : Nat) : MessageOp.Outcome → Prop
  | .done r => ∀ p, r = .error p → p.2.spill ≤ n
  | .spawn _ _ => True

end Jaune.Staging
