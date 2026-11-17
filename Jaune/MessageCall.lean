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

This module only adds declarations. Nothing in the present interpreter reads them yet; the new
chain was staged under its own namespace until the switch commit relocated it, so that
`Frame` and `Step` can sit beside today's definitions of the same names. Helpers on the
kept type `World` carry their final names.

The design is the W1/W3 design note, sections 2.1-2.4, as amended by its third revision.
Until unit P, `CallContext` carries today's static records `TenvStat` and `BenvStat`;
`TxContext` and `BlockContext` are the records they will be cut down to.
-/

namespace Jaune

/-! ### World helpers

Each mirrors the `Benv` function of the same name field for field, on the world alone. -/

/-- Forget an empty account's storage writes: `Benv.clearStorageWritesIfEmpty` on the world. -/
def World.clearStorageWritesIfEmpty (w : World) (a : Address) : World :=
  { w with storageWrites :=
      if (w.state.get a).isEmpty then w.storageWrites.eraseAddress a else w.storageWrites }

/-- The set-up a creation makes at its new address before its initcode runs:
`processCreateMessage.msg` on the world. The storage is cleared together with its write keys
(`Benv.setStor`), then the nonce is incremented (`Benv.incrNonce`). The created-account
insertion is not a world change; it is on the trail. -/
def World.createSetUp (w : World) (a : Address) : World :=
  let w := { w with state := w.state.setStor a .empty
                    storageWrites := w.storageWrites.eraseAddress a }
  ({ w with state := w.state.incrNonce a }).clearStorageWritesIfEmpty a

/-- Debit a balance, or nothing if it is too small: `Benv.subBal` on the world. -/
def World.subtractBalance (w : World) (a : Address) (v : U256) : Option World := do
  let state ← w.state.subBal a v
  some (({ w with state }).clearStorageWritesIfEmpty a)

/-- Credit a balance: `Benv.addBal` on the world. -/
def World.addBalance (w : World) (a : Address) (v : U256) : World :=
  ({ w with state := w.state.addBal a v }).clearStorageWritesIfEmpty a

end Jaune

namespace Jaune

/-! ### Lifetime records -/

/-- A frame's machine: the part of its state that is local to the frame. When a child fails its
machine is discarded and its two meters come back in the result. The program counter is not
here, so that only a jump returns one. -/
structure Machine : Type where
  /-- The operand stack, top first. -/
  stack : List U256
  /-- The frame's memory. -/
  memory : Mem
  /-- Execution gas left. -/
  gasLeft : Nat
  /-- EIP-8037's state-gas meter; `StateGasMeter.zero` under rules without state gas. -/
  stateGas : StateGasMeter := .zero
  /-- The output of the last child frame (`RETURNDATASIZE`, `RETURNDATACOPY`). -/
  returnData : Bytes

/-- The accrued substate a frame drops when it fails: the caller keeps its own. -/
structure Substate : Type where
  /-- Logs emitted so far. -/
  logs : List Log
  /-- The refund counter (EIP-3155 `refund`). -/
  refund : Int
  /-- The accounts scheduled for deletion by `SELFDESTRUCT`. -/
  selfDestructs : AdrSet
  /-- EIP-2929's accessed addresses. -/
  accessedAddresses : AdrSet
  /-- EIP-2929's accessed storage keys. -/
  accessedStorageKeys : KeySet
  /-- EIP-161's touched accounts, recorded only under rules with the touched-account sweep. -/
  touchedAccounts : AdrSet := .emptyWithCapacity

/-- What a frame keeps when it fails: the caller takes the child's. Upstream says of
`created_accounts` that they "are shared (not rolled back)". -/
structure Trail : Type where
  /-- The accounts created in this transaction so far. -/
  createdAccounts : AdrSet
  /-- EIP-7928's account reads. -/
  accountReads : AdrSet := .emptyWithCapacity
  /-- EIP-7928's storage reads. -/
  storageReads : KeySet := .emptyWithCapacity
  /-- Whether RIPEMD-160's address was touched in a failed frame: the one touch that survives a
  failure under rules with the touched-account sweep. `false` in a running frame; set only by
  `settle` in a failed result and read only by `resume`. -/
  touchedRIPEMD160 : Bool := false

/-- A frame's dynamic state, grouped by lifetime. -/
structure Frame.State : Type where
  /-- Frame-local. -/
  machine : Machine
  /-- Dropped on failure. -/
  world : World
  /-- Dropped on failure. -/
  substate : Substate
  /-- Kept on failure. -/
  trail : Trail

/-! ### Today's dynamic state and the lifetime groups

The W1 bodies of `enter`, `settle` and `resume` still run over today's `Devm`, so they convert
between it and `Frame.State`. Both maps go at unit N, when `Devm` becomes `Frame.State`. -/

/-- Today's dynamic state grouped by lifetime. It forgets `output` and `error`; the trail's
RIPEMD-160 flag is `false`, as in every running frame. -/
def Frame.State.ofDevm (d : Devm) : Frame.State :=
  { machine :=
      { stack := d.stack, memory := d.memory, gasLeft := d.gasLeft, stateGas := d.stateGas
        returnData := d.returnData }
    world := d.world
    substate :=
      { logs := d.logs, refund := d.refundCounter, selfDestructs := d.accountsToDelete
        accessedAddresses := d.accessedAddresses, accessedStorageKeys := d.accessedStorageKeys
        touchedAccounts := d.meta.touchedAccounts }
    trail :=
      { createdAccounts := d.createdAccounts, accountReads := d.meta.accountReads
        storageReads := d.meta.storageReads, touchedRIPEMD160 := false } }

/-- A lifetime-grouped state as today's dynamic state, with no output and no stored error. -/
def Frame.State.toDevm (s : Frame.State) : Devm :=
  { mach :=
      { stack := s.machine.stack, memory := s.machine.memory, gasLeft := s.machine.gasLeft
        stateGas := s.machine.stateGas }
    «meta» :=
      { logs := s.substate.logs, refundCounter := s.substate.refund, output := []
        accountsToDelete := s.substate.selfDestructs, returnData := s.machine.returnData
        error := none, accessedAddresses := s.substate.accessedAddresses
        accessedStorageKeys := s.substate.accessedStorageKeys
        createdAccounts := s.trail.createdAccounts, accountReads := s.trail.accountReads
        storageReads := s.trail.storageReads, touchedAccounts := s.substate.touchedAccounts }
    world := s.world }

/-! ### Static records -/

/-- The block a frame runs in: today's `BenvStat` without the transaction's original state. The
two fields `timestamp` and `gasLimit` are named as the header names them. Introduced for unit P;
until then `CallContext` carries `BenvStat`. -/
structure BlockContext : Type where
  /-- The fork this block runs under; the rules derive from it. -/
  fork : Fork
  /-- The chain id. -/
  chainId : UInt64
  /-- The block's gas limit (`GASLIMIT`); `BenvStat.blockGasLimit`. -/
  gasLimit : Nat
  /-- The recent block hashes `BLOCKHASH` reads. -/
  blockHashes : List U256
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
  parentBeaconBlockRoot : U256
  /-- EIP-7843's slot number. -/
  slotNumber : UInt64 := 0

/-- The rules a block runs under, as `BenvStat.rules`. -/
def BlockContext.rules (b : BlockContext) : ForkRules := Fork.ruleSet b.fork

/-- What a frame reads of its transaction (decision 13): the four fields the interpreter reads.
Introduced for unit P; until then `CallContext` carries `TenvStat`. -/
structure TxContext : Type where
  /-- The transaction's sender (`ORIGIN`). -/
  origin : Address
  /-- The effective gas price (`GASPRICE`). -/
  gasPrice : Nat
  /-- EIP-4844's versioned hashes (`BLOBHASH`). -/
  blobVersionedHashes : List U256
  /-- The state the transaction started on, which `SSTORE` compares against; today's
  `BenvStat.origState`. -/
  originalState : State

/-- What `step` reads of the message a frame runs. The other fields of today's `Sevm` (`target`,
`gas`, `codeAddress`, `disablePrecompiles`, the value-transfer flag) are read only at `enter`
and stay on the `Message`. -/
structure CallContext : Type where
  /-- The sender (`CALLER`). -/
  caller : Address
  /-- The account whose storage and balance the frame acts on (`ADDRESS`); EVMC's
  `recipient`, today's `currentTarget`. -/
  recipient : Address
  /-- The value (`CALLVALUE`). -/
  value : U256
  /-- The input (`CALLDATA*`); today's `data`. -/
  calldata : Bytes
  /-- The code the frame runs. -/
  code : ByteArray
  /-- The call depth left: 1024 at the top, one less in each child, no call at zero (decision
  12). The community's depth is the limit minus this. -/
  depthLeft : Nat
  /-- Whether state changes are forbidden (`STATICCALL`). -/
  isStatic : Bool
  /-- The transaction's static record; cut down to `TxContext` at unit P. -/
  tx : TenvStat
  /-- The block's static record; cut down to `BlockContext` at unit P. -/
  block : BenvStat

/-! ### Message and frame -/

/-- Whether a message is a call or a creation. -/
inductive Message.Kind : Type
  /-- A message call. -/
  | call
  /-- A contract creation. -/
  | create
deriving DecidableEq, Repr

/-- A message: what a frame is asked to run. It holds no saved world; the world a frame falls
back to is its `Frame`'s checkpoint. -/
structure Message : Type where
  /-- What `step` reads. -/
  context : CallContext
  /-- Call or creation. -/
  kind : Message.Kind
  /-- The account whose code is run, if any; a precompile is dispatched on it at `enter`. -/
  codeAddress : Option Address
  /-- The transaction's `to`, read only by top-level dispatch. -/
  target : Option Address
  /-- The execution gas the frame starts with. -/
  gas : Nat
  /-- EIP-8037's state-gas grant. -/
  stateGasGrant : Nat
  /-- Whether the value is transferred at `enter`, or only apparent (`DELEGATECALL`). -/
  transfersValue : Bool
  /-- Whether precompile dispatch is off for this message. -/
  disablePrecompiles : Bool

/-- A frame: one message and the one state it falls back to. The checkpoint is the saved caller
after call preparation, or for a top-level frame the state its message was prepared on. -/
structure Frame : Type where
  /-- The message the frame runs. -/
  message : Message
  /-- The state a failed frame falls back to. -/
  checkpoint : Frame.State

/-- A fault: a cryptographic or internal error. It is not a frame result; it ends the run
through the error channel. -/
inductive Fault : Type
  /-- A cryptographic reason a precompile could not convert. -/
  | crypto (reason : CryptoError)
  /-- A broken internal invariant. -/
  | internal (reason : InternalError)
deriving DecidableEq, Repr

/-- A fault as an error of today's vocabulary. -/
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

/-- The settled outcome as today's vocabulary records it: none for a success. -/
def error? : Frame.Result → Option SettledHalt
  | .success .. => none
  | .revert .. => some .revert
  | .halt reason .. => some (.halt reason)

end Frame.Result

/-- The world after the frame: the result's on success, the checkpoint's otherwise. -/
def Frame.worldAfter (f : Frame) : Frame.Result → World
  | .success _ _ _ world _ _ => world
  | _ => f.checkpoint.world

/-! ### What `step` hands the driver -/

/-- Where a child's result goes in its caller. -/
inductive ReturnTarget : Type
  /-- A call: the caller's output window. -/
  | call (outputIndex outputSize : Nat)
  /-- A creation: the new address, pushed on success. -/
  | create (address : Address)

/-- What the caller waits with while its child runs, besides the saved caller itself. -/
structure Pending : Type where
  /-- Where the child's result goes. -/
  target : ReturnTarget
  /-- Whether the spawn charged a new account's state gas, which a failed child refunds. -/
  newAccountCharged : Bool
  /-- W1 only: the caller's `Meta.output`, passed through so `resume` can rebuild its `Devm`. -/
  legacyOutput : Bytes
  /-- W1 only: the caller's `Meta.error`, passed through so `resume` can rebuild its `Devm`. -/
  legacyError : Option SettledHalt

/-- The result of a message opcode: finished in place, or a child frame to run. Today's `XStep`;
the old name carries a retired token. -/
inductive MessageOp.Outcome : Type
  /-- The opcode finished without opening a frame. -/
  | done (ex : Execution)
  /-- The opcode opens a child frame. -/
  | spawn (child : Frame) (pending : Pending)

/-- One step of a running frame. -/
inductive Step : Type
  /-- The frame stopped, with its raw result. -/
  | halt (ex : Execution)
  /-- The frame goes on at `pc`. Today's `cont`. -/
  | next (pc : Nat) (devm : Devm)
  /-- The frame opens a child, and goes on at `pc` when the child is resumed. -/
  | spawn (child : Frame) (pending : Pending) (pc : Nat)

/-- What entering a frame gives: code to run, or a result already (a precompile, or a failed
value transfer). -/
inductive Frame.Entry : Type
  /-- Run this machine. -/
  | run (evm : Evm)
  /-- The frame finished at entry, or faulted. -/
  | done (result : Except Fault Frame.Result)

/-! ### Entry helpers -/

/-- The value transfer at entry: today's `Msg.benvAfterTransfer` on the world. A balance too
small to pay is an internal fault: call preparation has already checked it. -/
def Message.transfer (m : Message) (w : World) : Except Fault World :=
  if m.transfersValue ∧ m.context.value ≠ 0 then
    match w.subtractBalance m.context.caller m.context.value with
    | none => .error (.internal (.assertion .none))
    | some w => .ok (w.addBalance m.context.recipient m.context.value)
  else .ok w

/-- The world the frame's code is entered on, before the value transfer. It is recomputed from
the checkpoint; for a creation it includes the set-up at the new address. -/
def Frame.enteredWorld (f : Frame) : World :=
  match f.message.kind with
  | .call => f.checkpoint.world
  | .create => f.checkpoint.world.createSetUp f.message.context.recipient

/-- The logs a frame starts with: under rules with state gas, EIP-7708's transfer log for a
value-transferring frame (none for a self transfer or a zero value); otherwise none. -/
def transferLogs (rules : ForkRules) (m : Message) : List Log :=
  match rules.stateGas with
  | none => []
  | some _ =>
    if m.transfersValue ∧ m.context.caller ≠ m.context.recipient ∧ m.context.value ≠ 0 then
      [transferLog m.context.caller m.context.recipient m.context.value]
    else []

/-- The static machine record of a message: today's `initSevm`. -/
def Message.sevm (m : Message) : Sevm :=
  { caller := m.context.caller, target := m.target, currentTarget := m.context.recipient
    gas := m.gas, value := m.context.value, data := m.context.calldata
    codeAddress := m.codeAddress, code := m.context.code, depth := m.context.depthLeft
    shouldTransferValue := m.transfersValue, isStatic := m.context.isStatic
    disablePrecompiles := m.disablePrecompiles
    benvStat := m.context.block, tenvStat := m.context.tx }

/-! ### Resume helpers -/

/-- A successful child's substate merged into its caller's. Under rules with state gas the
caller keeps its touched accounts, as today's Amsterdam merge does. -/
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

