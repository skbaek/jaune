import Jaune.MessageCall.CheckedFrame

/-!
# What a checked step reads of its message (goal `jaune-shape-and-names-v1`, G2b, decision 13)

`Checked.CallContext` holds exactly what `step` reads: the caller, the recipient, the value, the
calldata, the code, the depth left, the static flag, and two static records. The transaction
record is `TransactionContext` (`origin`, `gasPrice`, `blobVersionedHashes`, the original state);
the block record is `BlockContext`, whose fields `timestamp` and `gasLimit` are named as the header
names them. The other fields of today's message (`target`, `gas`, `codeAddress`,
`disablePrecompiles`, the value-transfer flag) are read only at `enter` and stay on the message.

Staged: the checked frame still carries the shared `CallContext` until the run-layer retype.
`Jaune.Bridge.G2b.CheckedContext` gives the total forgetful map from the shared record.
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
  gas : Nat
  stateGasGrant : Nat
  transfersValue : Bool
  disablePrecompiles : Bool

/-- The machine and lifetime groups when top-level preparation begins. -/
def Message.initialCheckpoint (message : Message) (world : World)
    (accessedAddresses : AdrSet) (accessedStorageKeys : KeySet) (createdAccounts selfDestructs : AdrSet) :
    Frame.State :=
  let context := message.context
  let logs := match context.block.rules.stateGas with
    | none => []
    | some _ =>
      if message.transfersValue then
        if context.caller = context.recipient ∨ context.value = 0 then []
        else [transferLog context.caller context.recipient context.value]
      else []
  { machine := {
      stack := [], memory := .empty, gasLeft := message.gas, returnData := []
      stateGas := ⟨message.stateGasGrant, message.stateGasGrant, 0, 0⟩ }
    world
    substate := { logs, refund := 0, selfDestructs, accessedAddresses, accessedStorageKeys }
    trail := { createdAccounts } }

/-- Input to top-level preparation. Authorization tuples are consumed before the frame runs. -/
structure TopLevel.Input where
  message : Message
  checkpoint : Frame.State
  authorizationList : List Authorization

end Jaune.Checked
