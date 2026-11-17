import Jaune.Execution
import Jaune.MessageCall

/-!
# The four-part message call: `step` (goal `jaune-shape-and-names-v1`, W1 unit E)

One step of a running frame, with call preparation handing the driver a child `Frame` and a
`Pending`.

Three points of its shape (`genericCreate.step` through `Evm.step`):

* the four tails, the only producers of a spawn, end in
  `.spawn ⟨message, Frame.State.ofDevm saved⟩ ⟨target, charged, saved.output, saved.error⟩`;
* the child's message is built by `callMessage` and `createMessage`, which build a `Message`
  and read no state: the world a child is entered on is its frame's checkpoint;
* a message opcode's result is a `MessageOp.Outcome`, and a step that goes on is `Step.next`.

The running machine is an `Evm` over `Devm`.
-/

namespace Jaune

open Jaune

/-! ### Building a child's message -/

/-- The message a call-family opcode sends its child (`callMsg`'s counterpart, without the
world: the child's world is its frame's checkpoint). -/
def callMessage (sevm : Sevm) (gas : Nat) (value : U256) (caller target codeAddress : Address)
    (transfersValue isStaticcall : Bool) (calldata : Bytes) (code : ByteArray)
    (disablePrecompiles : Bool) : Message :=
  { context :=
      { caller := caller, recipient := target, value := value, calldata := calldata, code := code, depthLeft := sevm.depth - 1
        isStatic := isStaticcall || sevm.isStatic, tx := sevm.tenvStat, block := sevm.benvStat }
    kind := .call
    codeAddress := some codeAddress
    target := some target
    gas := gas
    stateGasGrant := 0
    transfersValue := transfersValue
    disablePrecompiles := disablePrecompiles }

/-- The message a creation opcode sends its child (`createMsg`'s counterpart, without the
world). The initcode is the code run; the calldata is empty. -/
def createMessage (sevm : Sevm) (createGas : Nat) (endowment : U256) (newAddress : Address)
    (initcode : Bytes) : Message :=
  { context :=
      { caller := sevm.currentTarget, recipient := newAddress, value := endowment
        calldata := [], code := .mk <| .mk initcode, depthLeft := sevm.depth - 1
        isStatic := false, tx := sevm.tenvStat, block := sevm.benvStat }
    kind := .create
    codeAddress := none
    target := none
    gas := createGas
    stateGasGrant := 0
    transfersValue := true
    disablePrecompiles := false }

/-! ### Results of a step -/

/-- A message opcode's result, from a computation that can halt first. -/
def MessageOp.Outcome.ofExcept : Except (EvmError × Devm) MessageOp.Outcome → MessageOp.Outcome
  | .error e => .done (.error e)
  | .ok step => step

/-- A frame-local result as a step that goes on at `pc`. -/
def Step.ofExecution (pc : Nat) : Execution → Step
  | .error e => .halt (.error e)
  | .ok devm => .next pc devm

/-- A jump's result as a step. -/
def Step.ofJump : Except (EvmError × Devm) (Nat × Devm) → Step
  | .error e => .halt (.error e)
  | .ok ⟨pc, devm⟩ => .next pc devm

/-- A message opcode's result as a step that goes on at `pc`. -/
def MessageOp.Outcome.toStep (pc : Nat) : MessageOp.Outcome → Step
  | .done ex => Step.ofExecution pc ex
  | .spawn child pending => .spawn child pending pc

/-! ### The four tails and the step -/

def genericCreate.step
    (sevm : Sevm) (devm : Devm) (endowment : U256)
    (newAddress : Address) (memoryIndex memorySize : Nat) : MessageOp.Outcome :=
  MessageOp.Outcome.ofExcept do
    let calldata := devm.memory.data.sliceD memoryIndex memorySize 0
    -- EIP-3860 (Shanghai): the initcode bound applies only once
    -- `creation.initCodeLimit` activates; before that every size spawns.
    Except.assert
      (sevm.benvStat.rules.creation.initCodeLimit →
        memorySize ≤ sevm.benvStat.rules.code.maxInitCodeSize)
      ⟨.halt (.outOfGas .none), devm⟩
    let createGas := except64th devm.gasLeft
    let devm := devm.withGasLeft (devm.gasLeft - createGas)
    assertDynamic sevm devm
    let devm := devm.withReturnData []
    let sender := devm.state.get sevm.currentTarget
    if sender.balance < endowment ∨ sender.nonce = UInt64.max ∨ sevm.depth = 0 then
      let devm ← (devm.withGasLeft (devm.gasLeft + createGas)).push 0
      return .done (.ok devm)
    let devm := devm.incrNonce sevm.currentTarget
    let devm := addAccessedAddress devm newAddress
    if
      (let target := devm.state.get newAddress
       target.nonce ≠ (0 : UInt64) ∨
       target.code.size ≠ 0) then
      let devm ← devm.push 0
      return .done (.ok devm)
    let message := createMessage sevm createGas endowment newAddress calldata
    return .spawn ⟨message, Frame.State.ofDevm devm⟩
      ⟨.create newAddress, false, devm.output, devm.error⟩

def genericCall.step
    (sevm : Sevm) (devm : Devm) (gas : Nat) (value : U256)
    (caller target codeAddress : Address)
    (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) : MessageOp.Outcome :=
  let evm1 := devm.withReturnData []
  if sevm.depth = 0 then
    MessageOp.Outcome.ofExcept do
      let devm ← (evm1.withGasLeft (evm1.gasLeft + gas)).push 0
      return .done (.ok devm)
  else
    let calldata := evm1.memory.data.sliceD inputIndex inputSize 0
    let message :=
      callMessage sevm gas value caller target codeAddress
        shouldTransferValue isStaticcall calldata code disablePrecompiles
    .spawn ⟨message, Frame.State.ofDevm evm1⟩
      ⟨.call outputIndex outputSize, false, evm1.output, evm1.error⟩

/-- `generic_call` at the pin, for `rules.stateGas = some state`. The opcode has
already priced the call, charged both dimensions and withheld both grants; this
is the lifecycle: the preflight that aborts without spawning -- both grants
return untouched and a charged creation refills -- or the spawn, whose child
starts with the reservoir as its state-gas grant. -/
def genericCallAmsterdam.step
    (sevm : Sevm) (state : StateGasRules) (devm : Devm)
    (gas reservoir : Nat) (value : U256)
    (caller target codeAddress : Address)
    (shouldTransferValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray)
    (disablePrecompiles newAccountCharged insufficientBalance : Bool) : MessageOp.Outcome :=
  let evm1 := devm.withReturnData []
  if sevm.depth = 0 ∨ insufficientBalance then
    MessageOp.Outcome.ofExcept do
      let evm1 := evm1.restoreChildGas gas reservoir
      let evm1 :=
        if newAccountCharged then evm1.creditStateGasRefund state.newAccount
        else evm1
      let devm ← evm1.push 0
      return .done (.ok devm)
  else
    let calldata := evm1.memory.data.sliceD inputIndex inputSize 0
    let message :=
      { callMessage sevm gas value caller target codeAddress
          shouldTransferValue isStaticcall calldata code disablePrecompiles
        with stateGasGrant := reservoir }
    .spawn ⟨message, Frame.State.ofDevm evm1⟩
      ⟨.call outputIndex outputSize, newAccountCharged, evm1.output, evm1.error⟩

/-- `generic_create` at the pin, for `rules.stateGas = some state`. The opcode
has priced the operation itself; this is the lifecycle: the preflight that
aborts with nothing charged or withheld, the destination access with its
creation charge decided by existence alone, the withheld execution grant, the
collision that consumes it, and the spawn with the whole reservoir. -/
def genericCreateAmsterdam.step
    (sevm : Sevm) (state : StateGasRules) (devm : Devm) (endowment : U256)
    (newAddress : Address) (memoryIndex memorySize : Nat) : MessageOp.Outcome :=
  MessageOp.Outcome.ofExcept do
    let calldata := devm.memory.data.sliceD memoryIndex memorySize 0
    let devm := devm.withReturnData []
    -- PREFLIGHT: nothing has been charged or withheld for the child yet.
    -- `get_account(sender_address)` is a read (EIP-7928).
    let devm := devm.balReadAccount sevm.benvStat.rules sevm.currentTarget
    let sender := devm.state.get sevm.currentTarget
    if sender.balance < endowment ∨ sender.nonce = UInt64.max ∨ sevm.depth = 0 then
      let devm ← devm.push 0
      return .done (.ok devm)
    -- DESTINATION ACCESS: the creation charge, by existence alone;
    -- `is_account_alive(contract_address)` reads the destination (EIP-7928).
    let devm := addAccessedAddress devm newAddress
    let devm := devm.balReadAccount sevm.benvStat.rules newAddress
    let newAccountCharged := (devm.getAcct newAddress).isEmpty
    let devm ←
      if newAccountCharged then chargeStateGas state.newAccount devm else .ok devm
    -- CHILD GRANT: all but one 64th of the execution gas.
    let ⟨createGas, devm⟩ := devm.withholdCreateGas
    -- A collision consumes the grant and creates nothing; a collision target
    -- has code or a nonce, so the creation charge above was never taken.
    if
      (let target := devm.state.get newAddress
       target.nonce ≠ (0 : UInt64) ∨
       target.code.size ≠ 0) then
      let devm := devm.incrNonce sevm.currentTarget
      let devm ← devm.push 0
      return .done (.ok devm)
    -- The whole reservoir rides along, and comes back with the child.
    let ⟨reservoir, devm⟩ := devm.drainStateGasReservoir
    let devm := devm.incrNonce sevm.currentTarget
    let message :=
      { createMessage sevm createGas endowment newAddress calldata
        with stateGasGrant := reservoir }
    return .spawn ⟨message, Frame.State.ofDevm devm⟩
      ⟨.create newAddress, decide newAccountCharged, devm.output, devm.error⟩

def MessageOp.step (sevm : Sevm) (devm : Devm) : MessageOp → MessageOp.Outcome
  | .create =>
    match sevm.benvStat.rules.stateGas with
    | none =>
      MessageOp.Outcome.ofExcept do
        let ⟨endowment, devm⟩ ← devm.pop
        let ⟨memoryIndex, devm⟩ ← devm.popToNat
        let ⟨memorySize, devm⟩ ← devm.popToNat
        let extendCost := devm.extCost [⟨memoryIndex, memorySize⟩]
        -- EIP-3860 (Shanghai): initcode is metered per word only once
        -- `creation.initCodeLimit` activates; before that a creation pays no
        -- initcode words.
        let initCodeCost := if sevm.benvStat.rules.creation.initCodeLimit then
          Gas.initcodeWordCost * ceilDiv memorySize 32 else 0
        let devm ←
          chargeGas (sevm.benvStat.rules.gas.createAccess + extendCost + initCodeCost) devm
        let devm := devm.memExtends [⟨memoryIndex, memorySize⟩]
        let newAddress :=
          computeContractAddress
            sevm.currentTarget (devm.state.get sevm.currentTarget).nonce
        return genericCreate.step
          sevm devm endowment newAddress memoryIndex memorySize
    | some state =>
      MessageOp.Outcome.ofExcept do
        -- `create` at the pin: the static check first, `CREATE_ACCESS` from
        -- the schedule, the initcode limit after the charge.
        assertDynamic sevm devm
        let ⟨endowment, devm⟩ ← devm.pop
        let ⟨memoryIndex, devm⟩ ← devm.popToNat
        let ⟨memorySize, devm⟩ ← devm.popToNat
        let extendCost := devm.extCost [⟨memoryIndex, memorySize⟩]
        let initCodeCost := Gas.initcodeWordCost * ceilDiv memorySize 32
        let devm ←
          chargeGas (sevm.benvStat.rules.gas.createAccess + extendCost + initCodeCost)
            devm
        Except.assert
          (memorySize ≤ sevm.benvStat.rules.code.maxInitCodeSize)
          ⟨.halt (.outOfGas .none), devm⟩
        let devm := devm.memExtends [⟨memoryIndex, memorySize⟩]
        let newAddress :=
          computeContractAddress
            sevm.currentTarget (devm.state.get sevm.currentTarget).nonce
        return genericCreateAmsterdam.step
          sevm state devm endowment newAddress memoryIndex memorySize
  -- S8 (EIP-1014): availability first, the `CLZ` pattern in
  -- `PlainOp.runCore`: without the fork the byte is an undefined instruction
  -- whatever the stack holds. The two metering shapes below are untouched.
  | .create2 =>
    if sevm.benvStat.rules.opcodes.create2 then
      match sevm.benvStat.rules.stateGas with
      | none =>
        MessageOp.Outcome.ofExcept do
          let ⟨endowment, devm⟩ ← devm.pop
          let ⟨memoryIndex, devm⟩ ← devm.popToNat
          let ⟨memorySize, devm⟩ ← devm.popToNat
          let ⟨salt, devm⟩ ← devm.pop
          let extendCost := devm.extCost [⟨memoryIndex, memorySize⟩]
          let initCodeHashCost := Gas.keccak256Word * ceilDiv memorySize 32
          -- EIP-3860 (Shanghai): initcode is metered per word only once
          -- `creation.initCodeLimit` activates; before that a creation pays no
          -- initcode words. The hashing words above are EIP-1014 and stay.
          let initCodeCost := if sevm.benvStat.rules.creation.initCodeLimit then
            Gas.initcodeWordCost * ceilDiv memorySize 32 else 0
          let devm ←
            chargeGas
              (sevm.benvStat.rules.gas.createAccess + initCodeHashCost + extendCost
                + initCodeCost)
              devm
          let devm := devm.memExtends [⟨memoryIndex, memorySize⟩]
          let newAddress :=
            create2NewAddress
              sevm.currentTarget salt
              (devm.memory.data.sliceD memoryIndex memorySize 0)
          return genericCreate.step
            sevm devm endowment newAddress memoryIndex memorySize
      | some state =>
        MessageOp.Outcome.ofExcept do
          -- `create2` at the pin: as `create`, plus the initcode hashing words.
          assertDynamic sevm devm
          let ⟨endowment, devm⟩ ← devm.pop
          let ⟨memoryIndex, devm⟩ ← devm.popToNat
          let ⟨memorySize, devm⟩ ← devm.popToNat
          let ⟨salt, devm⟩ ← devm.pop
          let extendCost := devm.extCost [⟨memoryIndex, memorySize⟩]
          let initCodeHashCost := Gas.keccak256Word * ceilDiv memorySize 32
          let initCodeCost := Gas.initcodeWordCost * ceilDiv memorySize 32
          let devm ←
            chargeGas
              (sevm.benvStat.rules.gas.createAccess + initCodeHashCost + extendCost
                + initCodeCost)
              devm
          Except.assert
            (memorySize ≤ sevm.benvStat.rules.code.maxInitCodeSize)
            ⟨.halt (.outOfGas .none), devm⟩
          let devm := devm.memExtends [⟨memoryIndex, memorySize⟩]
          let newAddress :=
            create2NewAddress
              sevm.currentTarget salt
              (devm.memory.data.sliceD memoryIndex memorySize 0)
          return genericCreateAmsterdam.step
            sevm state devm endowment newAddress memoryIndex memorySize
    else
      MessageOp.Outcome.ofExcept (.error ⟨.halt (.invalidOpcode .none), devm⟩)
  | .call =>
    match sevm.benvStat.rules.stateGas with
    | none =>
      MessageOp.Outcome.ofExcept do
        let ⟨gas, devm⟩ ← devm.pop
        let ⟨callee, devm⟩ ← devm.popToAdr
        let ⟨value, devm⟩ ← devm.pop
        let ⟨inputIndex, devm⟩ ← devm.popToNat
        let ⟨inputSize, devm⟩ ← devm.popToNat
        let ⟨outputIndex, devm⟩ ← devm.popToNat
        let ⟨outputSize, devm⟩ ← devm.popToNat
        let extendCost :=
          devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let gasRules := sevm.benvStat.rules.gas
        -- Before EIP-2929 the base is flat and the accessed set is untouched.
        let preAccessCost :=
          match sevm.benvStat.rules.access with
          | .eip2929 => gasRules.accessCost callee devm.accessedAddresses
          | .flat g => g.call
        let devm :=
          match sevm.benvStat.rules.access with
          | .eip2929 => addAccessedAddress devm callee
          | .flat _ => devm
        let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
          sevm.benvStat.rules.accessDelegation devm callee
        let accessCost := preAccessCost + delegatedAccessGasCost
        let createCost :=
          if (¬ (devm.getAcct callee).isEmpty) ∨ value = 0 then 0 else Gas.newAccount
        let transferCost := if value = 0 then 0 else gasRules.callValue
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas value.toNat gas.toNat devm.gasLeft extendCost
            (accessCost + createCost + transferCost)
        let devm ← chargeGas (msgCallCost + extendCost) devm
        Except.assert (!sevm.isStatic ∨ value = 0) ⟨.halt (.writeInStaticContext .none), devm⟩
        let devm :=
          devm.memExtends
            [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let senderBal := (devm.getAcct sevm.currentTarget).balance
        if senderBal < value then
          let devm ← devm.push 0
          return .done
            (.ok
              ((devm.withReturnData []).withGasLeft
                (devm.gasLeft + msgCallStipend)))
        else
          return genericCall.step
            sevm devm msgCallStipend value sevm.currentTarget callee
            newCodeAddress true false inputIndex inputSize outputIndex outputSize
            code disablePrecompiles
    | some state =>
      MessageOp.Outcome.ofExcept do
        -- `call` at the pin: the static check before any charge; the
        -- state-independent price checked before any access; the accesses and
        -- the delegation's cost; the execution charge; `NEW_ACCOUNT` state gas
        -- for a value transfer that will create the recipient; the child grant
        -- computed after every charge, with the whole reservoir.
        let ⟨gas, devm⟩ ← devm.pop
        let ⟨callee, devm⟩ ← devm.popToAdr
        let ⟨value, devm⟩ ← devm.pop
        let ⟨inputIndex, devm⟩ ← devm.popToNat
        let ⟨inputSize, devm⟩ ← devm.popToNat
        let ⟨outputIndex, devm⟩ ← devm.popToNat
        let ⟨outputSize, devm⟩ ← devm.popToNat
        Except.assert (!sevm.isStatic ∨ value = 0)
          ⟨.halt (.writeInStaticContext .none), devm⟩
        let gasRules := sevm.benvStat.rules.gas
        let extendCost :=
          devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let accessGas := gasRules.accessCost callee devm.accessedAddresses
        let transferCost := if value = 0 then 0 else gasRules.callValue
        Except.assert (accessGas + transferCost + extendCost ≤ devm.gasLeft)
          ⟨.halt (.outOfGas .none), devm⟩
        let devm := addAccessedAddress devm callee
        let ⟨disablePrecompiles, newCodeAddress, delegatedAccessGasCost⟩ :=
          sevm.benvStat.rules.delegationCost devm callee
        -- `calculate_delegation_cost`: `get_account(to)` is a read (EIP-7928).
        let devm := devm.balReadAccount sevm.benvStat.rules callee
        let extraGas := accessGas + transferCost + delegatedAccessGasCost
        Except.assert (extraGas + extendCost ≤ devm.gasLeft)
          ⟨.halt (.outOfGas .none), devm⟩
        -- `get_account(code_address)` before the charge is a read (EIP-7928).
        let devm := devm.balReadAccount sevm.benvStat.rules newCodeAddress
        let ⟨code, devm⟩ :=
          completeDelegationAccess devm disablePrecompiles newCodeAddress
        let devm ← chargeGas (extraGas + extendCost) devm
        let newAccountCharged := value ≠ 0 ∧ (devm.getAcct callee).isEmpty
        let devm ←
          if newAccountCharged then chargeStateGas state.newAccount devm
          else .ok devm
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas value.toNat gas.toNat devm.gasLeft 0 0
        let devm ← chargeGas msgCallCost devm
        let ⟨reservoir, devm⟩ := devm.drainStateGasReservoir
        let devm :=
          devm.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let senderBal := (devm.getAcct sevm.currentTarget).balance
        return genericCallAmsterdam.step
          sevm state devm msgCallStipend reservoir value sevm.currentTarget callee
          newCodeAddress true false inputIndex inputSize outputIndex outputSize
          code disablePrecompiles (decide newAccountCharged) (decide (senderBal < value))
  | .callcode =>
    match sevm.benvStat.rules.stateGas with
    | none =>
      MessageOp.Outcome.ofExcept do
        let ⟨gas, devm⟩ ← devm.pop
        let ⟨codeAddress, devm⟩ ← devm.popToAdr
        let ⟨value, devm⟩ ← devm.pop
        let ⟨inputIndex, devm⟩ ← devm.popToNat
        let ⟨inputSize, devm⟩ ← devm.popToNat
        let ⟨outputIndex, devm⟩ ← devm.popToNat
        let ⟨outputSize, devm⟩ ← devm.popToNat
        let extendCost :=
          devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let gasRules := sevm.benvStat.rules.gas
        -- Before EIP-2929 the base is flat and the accessed set is untouched.
        let preAccessCost :=
          match sevm.benvStat.rules.access with
          | .eip2929 => gasRules.accessCost codeAddress devm.accessedAddresses
          | .flat g => g.call
        let devm :=
          match sevm.benvStat.rules.access with
          | .eip2929 => addAccessedAddress devm codeAddress
          | .flat _ => devm
        let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
          sevm.benvStat.rules.accessDelegation devm codeAddress
        let accessCost := preAccessCost + delegatedAccessGasCost
        let transferCost := if value = 0 then 0 else gasRules.callValue
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas value.toNat gas.toNat devm.gasLeft extendCost
            (accessCost + transferCost)
        let devm ← chargeGas (msgCallCost + extendCost) devm
        let devm :=
          devm.memExtends
            [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let senderBal := (devm.getAcct sevm.currentTarget).balance
        if senderBal < value then
          let devm ← devm.push 0
          return .done
            (.ok
              ((devm.withGasLeft (devm.gasLeft + msgCallStipend)).withReturnData []))
        else
          return genericCall.step
            sevm devm msgCallStipend value sevm.currentTarget
            sevm.currentTarget newCodeAddress true false
            inputIndex inputSize outputIndex outputSize code disablePrecompiles
    | some state =>
      MessageOp.Outcome.ofExcept do
        -- `callcode` at the pin: the state-independent price checked before
        -- any access; the accesses and the delegation's cost; the call's cost
        -- charged with the child grant; the whole reservoir rides along.
        let ⟨gas, devm⟩ ← devm.pop
        let ⟨codeAddress, devm⟩ ← devm.popToAdr
        let ⟨value, devm⟩ ← devm.pop
        let ⟨inputIndex, devm⟩ ← devm.popToNat
        let ⟨inputSize, devm⟩ ← devm.popToNat
        let ⟨outputIndex, devm⟩ ← devm.popToNat
        let ⟨outputSize, devm⟩ ← devm.popToNat
        let senderBal := (devm.getAcct sevm.currentTarget).balance
        let gasRules := sevm.benvStat.rules.gas
        let extendCost :=
          devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let accessGas := gasRules.accessCost codeAddress devm.accessedAddresses
        let transferCost := if value = 0 then 0 else gasRules.callValue
        Except.assert (accessGas + extendCost + transferCost ≤ devm.gasLeft)
          ⟨.halt (.outOfGas .none), devm⟩
        let devm := addAccessedAddress devm codeAddress
        let ⟨disablePrecompiles, newCodeAddress, delegatedAccessGasCost⟩ :=
          sevm.benvStat.rules.delegationCost devm codeAddress
        -- `calculate_delegation_cost`: `get_account(to)` is a read (EIP-7928).
        let devm := devm.balReadAccount sevm.benvStat.rules codeAddress
        let extraGas := accessGas + transferCost + delegatedAccessGasCost
        Except.assert (extraGas + extendCost ≤ devm.gasLeft)
          ⟨.halt (.outOfGas .none), devm⟩
        -- `get_account(code_address)` before the charge is a read (EIP-7928).
        let devm := devm.balReadAccount sevm.benvStat.rules newCodeAddress
        let ⟨code, devm⟩ :=
          completeDelegationAccess devm disablePrecompiles newCodeAddress
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas value.toNat gas.toNat devm.gasLeft extendCost extraGas
        let devm ← chargeGas (msgCallCost + extendCost) devm
        let ⟨reservoir, devm⟩ := devm.drainStateGasReservoir
        let devm :=
          devm.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        return genericCallAmsterdam.step
          sevm state devm msgCallStipend reservoir value sevm.currentTarget sevm.currentTarget
          newCodeAddress true false inputIndex inputSize outputIndex outputSize
          code disablePrecompiles false (decide (senderBal < value))
  | .delegatecall =>
    match sevm.benvStat.rules.stateGas with
    | none =>
      MessageOp.Outcome.ofExcept do
        let ⟨gas, devm⟩ ← devm.pop
        let ⟨codeAddress, devm⟩ ← devm.popToAdr
        let ⟨inputIndex, devm⟩ ← devm.popToNat
        let ⟨inputSize, devm⟩ ← devm.popToNat
        let ⟨outputIndex, devm⟩ ← devm.popToNat
        let ⟨outputSize, devm⟩ ← devm.popToNat
        let extendCost :=
          devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let gasRules := sevm.benvStat.rules.gas
        -- Before EIP-2929 the base is flat and the accessed set is untouched.
        let preAccessCost :=
          match sevm.benvStat.rules.access with
          | .eip2929 => gasRules.accessCost codeAddress devm.accessedAddresses
          | .flat g => g.call
        let devm :=
          match sevm.benvStat.rules.access with
          | .eip2929 => addAccessedAddress devm codeAddress
          | .flat _ => devm
        let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
          sevm.benvStat.rules.accessDelegation devm codeAddress
        let accessCost := preAccessCost + delegatedAccessGasCost
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas 0 gas.toNat devm.gasLeft extendCost accessCost
        let devm ← chargeGas (msgCallCost + extendCost) devm
        let devm :=
          devm.memExtends
            [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        return genericCall.step
          sevm devm msgCallStipend sevm.value sevm.caller
          sevm.currentTarget newCodeAddress false false
          inputIndex inputSize outputIndex outputSize code disablePrecompiles
    | some state =>
      MessageOp.Outcome.ofExcept do
        -- `delegatecall` at the pin: the state-independent price checked before
        -- any access; the accesses and the delegation's cost; the call's cost
        -- charged with the child grant; the whole reservoir rides along.
        let ⟨gas, devm⟩ ← devm.pop
        let ⟨codeAddress, devm⟩ ← devm.popToAdr
        let ⟨inputIndex, devm⟩ ← devm.popToNat
        let ⟨inputSize, devm⟩ ← devm.popToNat
        let ⟨outputIndex, devm⟩ ← devm.popToNat
        let ⟨outputSize, devm⟩ ← devm.popToNat
        let gasRules := sevm.benvStat.rules.gas
        let extendCost :=
          devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let accessGas := gasRules.accessCost codeAddress devm.accessedAddresses
        let transferCost := 0
        Except.assert (accessGas + extendCost ≤ devm.gasLeft)
          ⟨.halt (.outOfGas .none), devm⟩
        let devm := addAccessedAddress devm codeAddress
        let ⟨disablePrecompiles, newCodeAddress, delegatedAccessGasCost⟩ :=
          sevm.benvStat.rules.delegationCost devm codeAddress
        -- `calculate_delegation_cost`: `get_account(to)` is a read (EIP-7928).
        let devm := devm.balReadAccount sevm.benvStat.rules codeAddress
        let extraGas := accessGas + transferCost + delegatedAccessGasCost
        Except.assert (extraGas + extendCost ≤ devm.gasLeft)
          ⟨.halt (.outOfGas .none), devm⟩
        -- `get_account(code_address)` before the charge is a read (EIP-7928).
        let devm := devm.balReadAccount sevm.benvStat.rules newCodeAddress
        let ⟨code, devm⟩ :=
          completeDelegationAccess devm disablePrecompiles newCodeAddress
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas 0 gas.toNat devm.gasLeft extendCost extraGas
        let devm ← chargeGas (msgCallCost + extendCost) devm
        let ⟨reservoir, devm⟩ := devm.drainStateGasReservoir
        let devm :=
          devm.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        return genericCallAmsterdam.step
          sevm state devm msgCallStipend reservoir sevm.value sevm.caller sevm.currentTarget
          newCodeAddress false false inputIndex inputSize outputIndex outputSize
          code disablePrecompiles false false
  | .staticcall =>
    match sevm.benvStat.rules.stateGas with
    | none =>
      MessageOp.Outcome.ofExcept do
        let ⟨gas, devm⟩ ← devm.pop
        let ⟨target, devm⟩ ← devm.popToAdr
        let ⟨inputIndex, devm⟩ ← devm.popToNat
        let ⟨inputSize, devm⟩ ← devm.popToNat
        let ⟨outputIndex, devm⟩ ← devm.popToNat
        let ⟨outputSize, devm⟩ ← devm.popToNat
        let extendCost :=
          devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let gasRules := sevm.benvStat.rules.gas
        -- Before EIP-2929 the base is flat and the accessed set is untouched.
        let preAccessCost :=
          match sevm.benvStat.rules.access with
          | .eip2929 => gasRules.accessCost target devm.accessedAddresses
          | .flat g => g.call
        let devm :=
          match sevm.benvStat.rules.access with
          | .eip2929 => addAccessedAddress devm target
          | .flat _ => devm
        let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ :=
          sevm.benvStat.rules.accessDelegation devm target
        let accessCost := preAccessCost + delegatedAccessGasCost
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas 0 gas.toNat devm.gasLeft extendCost accessCost
        let devm ← chargeGas (msgCallCost + extendCost) devm
        let devm :=
          devm.memExtends
            [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        return genericCall.step
          sevm devm msgCallStipend 0 sevm.currentTarget target newCodeAddress
          true true inputIndex inputSize outputIndex outputSize code
          disablePrecompiles
    | some state =>
      MessageOp.Outcome.ofExcept do
        -- `staticcall` at the pin: the state-independent price checked before
        -- any access; the accesses and the delegation's cost; the call's cost
        -- charged with the child grant; the whole reservoir rides along.
        let ⟨gas, devm⟩ ← devm.pop
        let ⟨codeAddress, devm⟩ ← devm.popToAdr -- `to`
        let ⟨inputIndex, devm⟩ ← devm.popToNat
        let ⟨inputSize, devm⟩ ← devm.popToNat
        let ⟨outputIndex, devm⟩ ← devm.popToNat
        let ⟨outputSize, devm⟩ ← devm.popToNat
        let gasRules := sevm.benvStat.rules.gas
        let extendCost :=
          devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        let accessGas := gasRules.accessCost codeAddress devm.accessedAddresses
        let transferCost := 0
        Except.assert (accessGas + extendCost ≤ devm.gasLeft)
          ⟨.halt (.outOfGas .none), devm⟩
        let devm := addAccessedAddress devm codeAddress
        let ⟨disablePrecompiles, newCodeAddress, delegatedAccessGasCost⟩ :=
          sevm.benvStat.rules.delegationCost devm codeAddress
        -- `calculate_delegation_cost`: `get_account(to)` is a read (EIP-7928).
        let devm := devm.balReadAccount sevm.benvStat.rules codeAddress
        let extraGas := accessGas + transferCost + delegatedAccessGasCost
        Except.assert (extraGas + extendCost ≤ devm.gasLeft)
          ⟨.halt (.outOfGas .none), devm⟩
        -- `get_account(code_address)` before the charge is a read (EIP-7928).
        let devm := devm.balReadAccount sevm.benvStat.rules newCodeAddress
        let ⟨code, devm⟩ :=
          completeDelegationAccess devm disablePrecompiles newCodeAddress
        let ⟨msgCallCost, msgCallStipend⟩ :=
          calculateMsgCallGas 0 gas.toNat devm.gasLeft extendCost extraGas
        let devm ← chargeGas (msgCallCost + extendCost) devm
        let ⟨reservoir, devm⟩ := devm.drainStateGasReservoir
        let devm :=
          devm.memExtends [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
        return genericCallAmsterdam.step
          sevm state devm msgCallStipend reservoir 0 sevm.currentTarget codeAddress
          newCodeAddress true true inputIndex inputSize outputIndex outputSize
          code disablePrecompiles false false

def NextOp.step (evm : Evm) (n : NextOp) : Step :=
  let pc := evm.pc + n.size
  match n with
  -- S8 (EIP-3855): `PUSH0` is the empty push. Without the fork the byte is an
  -- undefined instruction whatever the stack and gas hold, exactly as for
  -- `CLZ` in `PlainOp.runCore`; a nonzero push is untouched.
  | .push xs _ =>
    if xs = [] && !evm.sta.benvStat.rules.opcodes.push0 then
      Step.ofExecution pc (.error ⟨.halt (.invalidOpcode .none), evm.dyna⟩)
    else
      let cost := if xs = [] then Gas.base else Gas.veryLow
      Step.ofExecution pc <| do
        let devm ← chargeGas cost evm.dyna
        devm.push xs.toU256
  | .plain r => Step.ofExecution pc (r.run evm)
  | .message x => MessageOp.Outcome.toStep pc (MessageOp.step evm.sta evm.dyna x)
  -- EIP-8024 (`vm/instructions/stack.py` `dupn`/`swapn`/`exchange`): the
  -- availability check first, as for every fork-gated opcode; then
  -- `charge_gas(VERY_LOW)` *before* the immediate is decoded, so an
  -- out-of-gas frame reports that and not the immediate; then the decode,
  -- where a forbidden immediate is the pinned `InvalidParameter`, an
  -- exceptional halt reported as an invalid instruction; then the stack.
  -- `DUPN n` duplicates position `n` (`stack[-n]`, index `n - 1` from the
  -- top), `SWAPN n` swaps the top with position `n + 1` (index `n`), and
  -- `EXCHANGE n m` swaps positions `n + 1` and `m + 1` (indices `n`, `m`).
  | .dupn imm =>
    Step.ofExecution pc <| do
      if evm.sta.benvStat.rules.opcodes.stackAccess then
        let devm ← chargeGas Gas.veryLow evm.dyna
        match decodeSingle imm with
        | none => .error ⟨.halt (.invalidOpcode .none), devm⟩
        | some n =>
          match devm.stack[n - 1]? with
          | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
          | some word => devm.push word
      else
        .error ⟨.halt (.invalidOpcode .none), evm.dyna⟩
  | .swapn imm =>
    Step.ofExecution pc <| do
      if evm.sta.benvStat.rules.opcodes.stackAccess then
        let devm ← chargeGas Gas.veryLow evm.dyna
        match decodeSingle imm with
        | none => .error ⟨.halt (.invalidOpcode .none), devm⟩
        | some n =>
          match List.swap devm.stack (n - 1) with
          | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
          | some stack => .ok (devm.withStack stack)
      else
        .error ⟨.halt (.invalidOpcode .none), evm.dyna⟩
  | .exchange imm =>
    Step.ofExecution pc <| do
      if evm.sta.benvStat.rules.opcodes.stackAccess then
        let devm ← chargeGas Gas.veryLow evm.dyna
        match decodePair imm with
        | none => .error ⟨.halt (.invalidOpcode .none), devm⟩
        | some (n, m) =>
          match List.exchange devm.stack n m with
          | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
          | some stack => .ok (devm.withStack stack)
      else
        .error ⟨.halt (.invalidOpcode .none), evm.dyna⟩

def Evm.step (evm : Evm) : Step :=
  match evm.getInst with
  | .none => .halt (.error ⟨.halt (.invalidOpcode .none), evm.dyna⟩)
  | .some (.next n) => NextOp.step evm n
  | .some (.jump j) => Step.ofJump (j.run evm)
  | .some (.halt l) => .halt (l.run evm.sta evm.dyna)

end Jaune

