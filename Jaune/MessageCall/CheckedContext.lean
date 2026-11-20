import Jaune.MessageCall.Records

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

/-- The default checked context, over the checked fields: no caller, recipient, value, input or
code, the full call depth, not static, and the default transaction and block records. -/
instance : Inhabited Checked.CallContext := ⟨
  { caller := 0, recipient := 0, value := 0, calldata := [], code := .empty, depthLeft := 1024
    isStatic := false, tx := default, block := default }⟩

end Jaune

namespace Jaune.Checked

end Jaune.Checked
