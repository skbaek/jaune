import Jaune.MessageCall.State

/-!
# What a checked step reads of its message (goal `jaune-shape-and-names-v1`, G2b, decision 13)

`Checked.CallContext` holds exactly what `step` reads: the caller, the recipient, the value, the
calldata, the code, the depth left, the static flag, and two static records. The transaction
record is `TransactionContext` (`origin`, `gasPrice`, `blobVersionedHashes`, the original state);
the block record is `BlockContext`, whose fields `timestamp` and `gasLimit` are named as the header
names them. The other fields of today's message (`target`, `gas`, `codeAddress`,
`disablePrecompiles`, the value-transfer flag) are read only at `enter` and stay on the message.

-/

namespace Jaune.Checked

/-- What `step` reads of the message a frame runs (decision 13). -/
structure CallContext : Type where
  /-- The sender (`CALLER`). -/
  caller : Address
  /-- The account whose storage and balance the frame acts on (`ADDRESS`); EVMC's `recipient`. -/
  recipient : Address
  /-- The value (`CALLVALUE`). -/
  value : U256
  /-- The input (`CALLDATA*`). -/
  calldata : Bytes
  /-- The code the frame runs. -/
  code : ByteArray
  /-- The call depth left: 1024 at the top, one less in each child, no call at zero (decision
  12). The community's depth is the limit minus this. -/
  depthLeft : Nat
  /-- Whether state changes are forbidden (`STATICCALL`). -/
  isStatic : Bool
  /-- What the frame reads of its transaction. -/
  tx : TransactionContext
  /-- What the frame reads of its block. -/
  block : BlockContext

/-- The immutable inputs of a Checked frame. Its checkpoint carries the rollback state. -/
structure Message where
  context : CallContext
  kind : Jaune.Message.Kind
  codeAddress : Option Address
  target : Option Address
  gas : Nat
  stateGasGrant : Nat
  transfersValue : Bool
  disablePrecompiles : Bool

/-- Move value in the world selected for frame entry. -/
def Message.transfer (m : Message) (world : World) : Except Fault World :=
  if m.transfersValue ∧ m.context.value ≠ 0 then
    match world.subtractBalance m.context.caller m.context.value with
    | none => .error (.internal (.assertion .none))
    | some world => .ok (world.addBalance m.context.recipient m.context.value)
  else .ok world

/-- The transfer emits a log under state-gas rules when value moves between distinct accounts. -/
def Message.transferLogs (m : Message) : List Log :=
  match m.context.block.rules.stateGas with
  | none => []
  | some _ =>
    if m.transfersValue ∧ m.context.caller ≠ m.context.recipient ∧ m.context.value ≠ 0 then
      [transferLog m.context.caller m.context.recipient m.context.value]
    else []

end Jaune.Checked

namespace Jaune

/-- The rules selected by a block context satisfy the fork invariants. -/
theorem BlockContext.rules_valid (b : BlockContext) : b.rules.Valid := Fork.ruleSet_valid b.fork

/-- The block record a frame reads, from the shared `BenvStat`. -/
def BenvStat.toBlockContext (b : BenvStat) : BlockContext :=
  { fork := b.fork, chainId := b.chainId, gasLimit := b.blockGasLimit, blockHashes := b.blockHashes
    coinbase := b.coinbase, number := b.number, baseFeePerGas := b.baseFeePerGas
    timestamp := b.time, prevRandao := b.prevRandao, excessBlobGas := b.excessBlobGas
    parentBeaconBlockRoot := b.parentBeaconBlockRoot, slotNumber := b.slotNumber }

/-- The transaction record a frame reads, from the shared `TenvStat` and the original state. -/
def TenvStat.toTransactionContext (t : TenvStat) (originalState : State) : TransactionContext :=
  { origin := t.origin, gasPrice := t.gasPrice, blobVersionedHashes := t.blobVersionedHashes
    originalState }

/-- The total forgetful map from the shared call context to the checked one. -/
def CallContext.toChecked (c : CallContext) : Checked.CallContext :=
  { caller := c.caller, recipient := c.recipient, value := c.value, calldata := c.calldata
    code := c.code, depthLeft := c.depthLeft, isStatic := c.isStatic
    tx := c.tx.toTransactionContext c.block.origState, block := c.block.toBlockContext }

instance : Inhabited Checked.CallContext := ⟨(default : CallContext).toChecked⟩

end Jaune

namespace Jaune.Checked

/-- Reconstruct the waiting context for comparison and trace observation. The template supplies
the transaction fields outside the interpreter's context. -/
def CallContext.toLegacy (c : CallContext) (template : TenvStat := default) : Jaune.CallContext :=
  { caller := c.caller, recipient := c.recipient, value := c.value, calldata := c.calldata
    code := c.code, depthLeft := c.depthLeft, isStatic := c.isStatic
    tx := { template with
      origin := c.tx.origin
      gasPrice := c.tx.gasPrice
      blobVersionedHashes := c.tx.blobVersionedHashes }
    block := {
      fork := c.block.fork
      chainId := c.block.chainId
      origState := c.tx.originalState
      blockGasLimit := c.block.gasLimit
      blockHashes := c.block.blockHashes
      coinbase := c.block.coinbase
      number := c.block.number
      baseFeePerGas := c.block.baseFeePerGas
      time := c.block.timestamp
      prevRandao := c.block.prevRandao
      excessBlobGas := c.block.excessBlobGas
      parentBeaconBlockRoot := c.block.parentBeaconBlockRoot
      slotNumber := c.block.slotNumber } }

/-- Project the static fields used by the Checked interpreter from a waiting message. -/
def Message.ofLegacy (m : Jaune.Message) : Message :=
  ⟨m.context.toChecked, m.kind, m.codeAddress, m.target, m.gas, m.stateGasGrant,
    m.transfersValue, m.disablePrecompiles⟩

/-- Observe a Checked message through the waiting message interface. -/
def Message.toLegacy (m : Message) (template : TenvStat := default) : Jaune.Message :=
  ⟨m.context.toLegacy template, m.kind, m.codeAddress, m.target, m.gas, m.stateGasGrant,
    m.transfersValue, m.disablePrecompiles⟩

end Jaune.Checked
