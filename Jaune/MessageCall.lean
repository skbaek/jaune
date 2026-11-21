import Jaune.Machine

/-!
# The four-part message call: vocabulary (goal `jaune-shape-and-names-v1`, W1 unit B)

The records, results and helpers that the message call in four parts (`step`, `enter`, `settle`,
`resume`) is written over. A frame's dynamic state is grouped by what happens to it when the
frame fails:

* `Machine` is frame-local: a failed child's is discarded, and its two meters come back in the
  result;
* `World` (unchanged, `Jaune.World`) and `Substate` are dropped on failure: the caller keeps its
  own;
* `Trail` is kept on failure: the caller takes the child's.

Helpers on the kept type `World` carry their final names.

The design is the W1/W3 design note, sections 2.1-2.4, as amended by its third revision.
Until W3's unit P, `CallContext` carries the static records `TenvStat` and `BenvStat`;
`TransactionContext` and `BlockContext` are the records they will be cut down to.
-/

namespace Jaune

/-! ### World helpers

Each mirrors the `Benv` function of the same name field for field, on the world alone. -/

/-- Forget an empty account's storage writes: `Benv.clearStorageWritesIfEmpty` on the world. -/
def World.clearStorageWritesIfEmpty (w : World) (a : Address) : World :=
  { w with storageWrites :=
      w.storageWrites.clearIfEmpty w.state a }

/-- The set-up a creation makes at its new address before its initcode runs:
`processCreateMessage.msg` on the world. The storage is cleared together with its write keys
(`Benv.setStor`), then the nonce is incremented (`Benv.incrNonce`). The created-account
insertion is not a world change; it is on the trail. -/
def World.createSetUp (w : World) (a : Address) : World :=
  let w := { w with state := w.state.setStorage a .empty
                    storageWrites := w.storageWrites.eraseAddress a }
  ({ w with state := w.state.incrementNonce a }).clearStorageWritesIfEmpty a

/-- Debit a balance, or nothing if it is too small: `Benv.subBal` on the world. -/
def World.subtractBalance (w : World) (a : Address) (v : U256) : Option World := do
  let state ← w.state.subtractBalance a v
  some (({ w with state }).clearStorageWritesIfEmpty a)

/-- Credit a balance: `Benv.addBal` on the world. -/
def World.addBalance (w : World) (a : Address) (v : U256) : World :=
  ({ w with state := w.state.addBalance a v }).clearStorageWritesIfEmpty a

end Jaune

namespace Jaune

/-! ### Lifetime records -/

/-- The accrued substate a frame drops when it fails: the caller keeps its own. -/
structure Substate : Type where
  /-- Logs emitted so far. -/
  logs : List Log
  /-- The refund counter (EIP-3155 `refund`). -/
  refund : Int
  /-- The accounts scheduled for deletion by `SELFDESTRUCT`. -/
  selfDestructs : AddressSet
  /-- EIP-2929's accessed addresses. -/
  accessedAddresses : AddressSet
  /-- EIP-2929's accessed storage keys. -/
  accessedStorageKeys : KeySet
  /-- EIP-161's touched accounts, recorded only under rules with the touched-account sweep. -/
  touchedAccounts : AddressSet := .emptyWithCapacity

/-- What a frame keeps when it fails: the caller takes the child's. Upstream says of
`created_accounts` that they "are shared (not rolled back)". -/
structure Trail : Type where
  /-- The accounts created in this transaction so far. -/
  createdAccounts : AddressSet
  /-- EIP-7928's account reads. -/
  accountReads : AddressSet := .emptyWithCapacity
  /-- EIP-7928's storage reads. -/
  storageReads : KeySet := .emptyWithCapacity
  /-- Whether RIPEMD-160's address was touched in a failed frame: the one touch that survives a
  failure under rules with the touched-account sweep. `false` in a running frame; set only by
  `settle` in a failed result and read only by `resume`. -/
  touchedRIPEMD160 : Bool := false

/-! ### `Devm` and the lifetime groups

The bodies of `enter`, `settle` and `resume` run over `Devm`, so they convert between it and
`Frame.State`. Both maps go at W3's unit N, when `Devm` becomes `Frame.State`. -/

/-! ### Static records -/

/-- The block a frame runs in: `BenvStat` without the transaction's original state. The
two fields `timestamp` and `gasLimit` are named as the header names them. Not yet used:
`CallContext` carries `BenvStat` until W3's unit P. -/
structure BlockContext : Type where
  /-- The fork this block runs under; the rules derive from it. -/
  fork : Fork
  /-- The chain id. -/
  chainId : UInt64
  /-- The block's gas limit (`GASLIMIT`); `BenvStat.blockGasLimit`. -/
  gasLimit : Nat
  /-- The recent block hashes `BLOCKHASH` reads. -/
  blockHashes : List Hash32
  /-- The beneficiary (`COINBASE`). -/
  coinbase : Address
  /-- The block number. -/
  number : Nat
  /-- EIP-1559's base fee. -/
  baseFeePerGas : Nat
  /-- The block's timestamp (`TIMESTAMP`); `BenvStat.time`. -/
  timestamp : U256
  /-- `PREVRANDAO`. -/
  prevRandao : U256
  /-- EIP-4844's excess blob gas. -/
  excessBlobGas : Nat
  /-- EIP-4788's parent beacon block root. -/
  parentBeaconBlockRoot : Hash32
  /-- EIP-7843's slot number. -/
  slotNumber : UInt64 := 0

/-- The rules a block runs under, as `BenvStat.rules`. -/
def BlockContext.rules (b : BlockContext) : ForkRules := Fork.ruleSet b.fork

/-- What a frame reads of its transaction (decision 13): the four fields the interpreter reads.
Not yet used: `CallContext` carries `TenvStat` until W3's unit P. -/
structure TransactionContext : Type where
  /-- The transaction's sender (`ORIGIN`). -/
  origin : Address
  /-- The effective gas price (`GASPRICE`). -/
  gasPrice : Nat
  /-- EIP-4844's versioned hashes (`BLOBHASH`). -/
  blobVersionedHashes : List Hash32
  /-- The state the transaction started on, which `SSTORE` compares against;
  `BenvStat.origState`. -/
  originalState : State

/-! ### Message and frame -/

/-- Whether a message is a call or a creation. -/
inductive Message.Kind : Type
  /-- A message call. -/
  | call
  /-- A contract creation. -/
  | create
deriving DecidableEq, Repr

/-- A fault: a cryptographic or internal error. It is not a frame result; it ends the run
through the error channel. -/
inductive Fault : Type
  /-- A cryptographic reason a precompile could not convert. -/
  | crypto (reason : CryptoError)
  /-- A broken internal invariant. -/
  | internal (reason : InternalError)
deriving DecidableEq, Repr

/-- A fault as an `EvmError`. -/
def Fault.toEvmError : Fault → EvmError
  | .crypto reason => .crypto reason
  | .internal reason => .internal reason

/-- What a finished frame hands back to its caller, the top level or a system call. Every case
carries the trail and the state-gas meter: a halted frame under Amsterdam's rules refills its
state gas, so even a halt hands a meter back. -/
inductive Frame.Result : Type
  /-- The frame finished: its output (for a creation, the deployed code), gas left, meter, and
  the world and substate it leaves. -/
  | success (output : Bytes) (gasLeft : Nat) (stateGas : StateGasMeter)
      (world : World) (substate : Substate) (trail : Trail)
  /-- The frame reverted: its output, the gas it keeps, and its meter. -/
  | revert (output : Bytes) (gasLeft : Nat) (stateGas : StateGasMeter) (trail : Trail)
  /-- The frame halted exceptionally: the reason, and its meter. Its gas is forfeit. -/
  | halt (reason : ExceptionalHalt) (stateGas : StateGasMeter) (trail : Trail)

namespace Frame.Result

/-- Whether the frame failed (reverted or halted). -/
def failed : Frame.Result → Bool
  | .success .. => false
  | .revert .. => true
  | .halt .. => true

/-- The bytes the frame hands back; a halt hands back none. -/
def output : Frame.Result → Bytes
  | .success output .. => output
  | .revert output .. => output
  | .halt .. => []

/-- The execution gas the frame hands back; a halt hands back none. -/
def gasLeft : Frame.Result → Nat
  | .success _ gasLeft .. => gasLeft
  | .revert _ gasLeft .. => gasLeft
  | .halt .. => 0

/-- The state-gas meter the frame hands back. -/
def stateGas : Frame.Result → StateGasMeter
  | .success _ _ stateGas .. => stateGas
  | .revert _ _ stateGas _ => stateGas
  | .halt _ stateGas _ => stateGas

/-- The frame's trail. -/
def trail : Frame.Result → Trail
  | .success _ _ _ _ _ trail => trail
  | .revert _ _ _ trail => trail
  | .halt _ _ trail => trail

/-- The settled outcome as `Meta.error` records it: none for a success. -/
def error? : Frame.Result → Option SettledHalt
  | .success .. => none
  | .revert .. => some .revert
  | .halt reason .. => some (.halt reason)

end Frame.Result

/-! ### What `step` hands the driver -/

/-- Where a child's result goes in its caller. -/
inductive ReturnTarget : Type
  /-- A call: the caller's output window. -/
  | call (outputIndex outputSize : Nat)
  /-- A creation: the new address, pushed on success. -/
  | create (address : Address)

/-! ### Entry helpers -/

/-! ### Resume helpers -/

/-- A successful child's substate merged into its caller's. Under rules with state gas the
caller keeps its touched accounts. -/
def Substate.absorb (rules : ForkRules) (saved child : Substate) : Substate :=
  { logs := saved.logs ++ child.logs
    refund := saved.refund + child.refund
    selfDestructs := saved.selfDestructs.union child.selfDestructs
    accessedAddresses := saved.accessedAddresses.union child.accessedAddresses
    accessedStorageKeys := saved.accessedStorageKeys.union child.accessedStorageKeys
    touchedAccounts := match rules.stateGas with
      | none => saved.touchedAccounts.union child.touchedAccounts
      | some _ => saved.touchedAccounts }

/-- A child's trail merged into its caller's, whatever the child's outcome: the created
accounts are the child's, the read sets are unions, and the caller's flag stays. -/
def Trail.absorb (saved child : Trail) : Trail :=
  { createdAccounts := child.createdAccounts
    accountReads := saved.accountReads.union child.accountReads
    storageReads := saved.storageReads.union child.storageReads
    touchedRIPEMD160 := saved.touchedRIPEMD160 }

/-- The one touch a failed child leaves in its caller: RIPEMD-160's address, when the child's
trail records it. -/
def Substate.keepTouch (s : Substate) (child : Trail) : Substate :=
  { s with touchedAccounts :=
      if child.touchedRIPEMD160 then s.touchedAccounts.insert ripemd160Address
      else s.touchedAccounts }

end Jaune

