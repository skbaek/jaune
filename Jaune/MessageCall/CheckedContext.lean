import Jaune.MessageCall

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

end Jaune.Checked
