import Jaune.Precompiles
import Jaune.Fuel

namespace Jaune

open Jaune

def Op.toOpString : Op → String
  | .next n => n.toOpString
  | .jump j => j.toString
  | .halt l => l.toString

def Op.toString : Op → String
  | .next n => n.toString
  | .jump j => j.toString
  | .halt l => l.toString

def State.getStor (w : State) (a : Address) : Storage := (w.get a).storage
def State.getNonce (w : State) (a : Address) : UInt64 := (w.get a).nonce
def State.getCode (w : State) (a : Address) : ByteArray := (w.get a).code

def isValidDelegation (code: ByteArray) : Prop :=
  code.size = eoaDelegatedCodeLength ∧
  code.sliceD 0 3 (0 : UInt8) = eoaDelegationMarker

instance {code} : Decidable (isValidDelegation code) := instDecidableAnd

def getDelegatedCodeAddress (code : ByteArray) : Option Address :=
  if isValidDelegation code
  then
    let adrBytes := code.sliceD eoaDelegationMarker.length 20 (0 : UInt8)
    adrBytes.toAddress?
  else none

instance : Inhabited Address := ⟨0⟩

def accessDelegation (devm : Devm) (adr : Address) :
  Bool × Address × ByteArray × Nat × Devm :=
  let state := devm.state
  let code := state.getCode adr
  -- P0.6 item 3: the delegated address is extracted by the total match below,
  -- never by a partial projection. `getDelegatedCodeAddress` answers `some`
  -- exactly on valid delegation designators, so the `none` arm is the ordinary
  -- no-delegation path.
  match getDelegatedCodeAddress code with
  | some adr =>
    let accessGasCost := accessCost adr devm.accessedAddresses
    let devm := addAccessedAddress devm adr
    let code := state.getCode adr
    ⟨true, adr, code, accessGasCost, devm⟩
  | none => ⟨false, adr, code, 0, devm⟩

/-- `calculate_delegation_cost` with the schedule's cold access. `accessDelegation`
above keeps its name and arity -- Blanc names it in 25 files -- and the
Amsterdam arms read this sibling through `rules.gas`. -/
def GasSchedule.accessDelegation (gas : GasSchedule) (devm : Devm) (adr : Address) :
  Bool × Address × ByteArray × Nat × Devm :=
  let state := devm.state
  let code := state.getCode adr
  match getDelegatedCodeAddress code with
  | some adr =>
    let accessGasCost := gas.accessCost adr devm.accessedAddresses
    let devm := addAccessedAddress devm adr
    let code := state.getCode adr
    ⟨true, adr, code, accessGasCost, devm⟩
  | none => ⟨false, adr, code, 0, devm⟩

/-- Under the Prague schedule the schedule-reading delegation access is the
original one. -/
theorem accessDelegation_eq (devm : Devm) (adr : Address) :
    pragueGasSchedule.accessDelegation devm adr = accessDelegation devm adr := rfl

/-- `eoa_delegation.py.calculate_delegation_cost` at the Amsterdam pin.
This reads the direct account's designation and prices the delegated address,
but deliberately neither warms that address nor reads its code. Amsterdam
callers perform their second affordability check before those effects. -/
def GasSchedule.delegationCost (gas : GasSchedule) (devm : Devm) (adr : Address) :
    Bool × Address × Nat :=
  let code := devm.state.getCode adr
  match getDelegatedCodeAddress code with
  | some delegated =>
    ⟨true, delegated, gas.accessCost delegated devm.accessedAddresses⟩
  | none => ⟨false, adr, 0⟩

/-- The effective code-designation lookup under the selected fork rules. -/
def ForkRules.delegatedCodeAddress (rules : ForkRules) (code : ByteArray) : Option Address :=
  if rules.delegationEnabled then getDelegatedCodeAddress code else none

/-- Fork-aware nested code access. Disabled delegation leaves the machine unchanged. -/
def ForkRules.accessDelegation (rules : ForkRules) (devm : Devm) (adr : Address) :
    Bool × Address × ByteArray × Nat × Devm :=
  if rules.delegationEnabled then rules.gas.accessDelegation devm adr
  else ⟨false, adr, devm.state.getCode adr, 0, devm⟩

/-- Fork-aware price discovery; warming and code access remain separate. -/
def ForkRules.delegationCost (rules : ForkRules) (devm : Devm) (adr : Address) : Bool × Address × Nat :=
  if rules.delegationEnabled then rules.gas.delegationCost devm adr else ⟨false, adr, 0⟩

theorem ForkRules.delegatedCodeAddress_enabled {rules : ForkRules}
    (h : rules.delegationEnabled = true) (code : ByteArray) :
    rules.delegatedCodeAddress code = getDelegatedCodeAddress code := by
  simp only [ForkRules.delegatedCodeAddress, h, ↓reduceIte]

theorem ForkRules.delegatedCodeAddress_disabled {rules : ForkRules}
    (h : rules.delegationEnabled = false) (code : ByteArray) :
    rules.delegatedCodeAddress code = none := by
  simp only [ForkRules.delegatedCodeAddress, h, Bool.false_eq_true, ↓reduceIte]

theorem ForkRules.accessDelegation_enabled {rules : ForkRules}
    (h : rules.delegationEnabled = true) (devm : Devm) (adr : Address) :
    rules.accessDelegation devm adr = rules.gas.accessDelegation devm adr := by
  simp only [ForkRules.accessDelegation, h, ↓reduceIte]

theorem ForkRules.accessDelegation_disabled {rules : ForkRules}
    (h : rules.delegationEnabled = false) (devm : Devm) (adr : Address) :
    rules.accessDelegation devm adr = ⟨false, adr, devm.state.getCode adr, 0, devm⟩ := by
  simp only [ForkRules.accessDelegation, h, Bool.false_eq_true, ↓reduceIte]

theorem ForkRules.delegationCost_enabled {rules : ForkRules}
    (h : rules.delegationEnabled = true) (devm : Devm) (adr : Address) :
    rules.delegationCost devm adr = rules.gas.delegationCost devm adr := by
  simp only [ForkRules.delegationCost, h, ↓reduceIte]

theorem ForkRules.delegationCost_disabled {rules : ForkRules}
    (h : rules.delegationEnabled = false) (devm : Devm) (adr : Address) :
    rules.delegationCost devm adr = ⟨false, adr, 0⟩ := by
  simp only [ForkRules.delegationCost, h, Bool.false_eq_true, ↓reduceIte]

/-- The state-access half of delegation resolution, called only after the
delegated access price has passed its affordability check. -/
def completeDelegationAccess (devm : Devm) (delegated : Bool) (adr : Address) :
    ByteArray × Devm :=
  let devm := if delegated then addAccessedAddress devm adr else devm
  ⟨devm.state.getCode adr, devm⟩

/-- Prague rejects 0xEF-leading deposits: its creation gate is on. -/
@[simp] theorem pragueRules_creation_rejectEf :
    pragueRules.creation.rejectEf = true := rfl

def initSevm (msg : Msg) : Sevm :=
  {
    caller := msg.caller
    target := msg.target
    currentTarget := msg.currentTarget
    gas := msg.gas
    value := msg.value
    data := msg.data
    codeAddress := msg.codeAddress
    code := msg.code
    depth := msg.depth
    shouldTransferValue := msg.shouldTransferValue
    isStatic := msg.isStatic
    disablePrecompiles := msg.disablePrecompiles
    benvStat := msg.benv.stat
    tenvStat := msg.tenv.stat
  }

def initDevm (msg : Msg) : Devm :=
  {
    mach := {
      stack := []
      memory := .empty
      gasLeft := msg.gas
      -- `create_evm` / the `GasMeter` a child frame is built with: the
      -- reservoir starts at the grant and so does the baseline a rollback
      -- refills to. With a zero grant this is `StateGasMeter.zero`, which is
      -- what every `none`-path frame gets and what `initDevm_stateGasZero`
      -- states.
      stateGas := {
        left := msg.stateGasGrant
        baseline := msg.stateGasGrant
        spilled := 0
        committedSpill := 0
      }
    }
    «meta» := {
      -- `process_call`'s value move has already happened at `Frame.enter`;
      -- under `some _` EIP-7708 logs it, ahead of everything the frame itself
      -- logs. `Devm.emitTransferLog` carries upstream's two guards (a
      -- self-transfer and a zero transfer log nothing).
      logs := match msg.benv.stat.rules.stateGas with
        | none => []
        | some _ =>
          if msg.shouldTransferValue then
            (Devm.emitTransferLog {
              mach := {
                  stack := []
                  memory := .empty
                  gasLeft := 0
                }
              «meta» := {
                  logs := []
                  refundCounter := 0
                  output := []
                  accountsToDelete := .emptyWithCapacity
                  returnData := []
                  error := .none
                  accessedAddresses := .emptyWithCapacity
                  accessedStorageKeys := .emptyWithCapacity
                  createdAccounts := .emptyWithCapacity
                }
              world := {
                  state := msg.benv.state
                  transientStorage := msg.tenv.transientStorage
                  storageWrites := msg.benv.storageWrites
                }
              }
              msg.caller msg.currentTarget msg.value).logs
          else []
      refundCounter := 0
      output := []
      accountsToDelete := msg.inheritedDeletions
      returnData := []
      error := .none
      accessedAddresses := msg.accessedAddresses
      accessedStorageKeys := msg.accessedStorageKeys
      createdAccounts := msg.benv.createdAccounts
    }
    world := {
      state := msg.benv.state
      transientStorage := msg.tenv.transientStorage
      storageWrites := msg.benv.storageWrites
    }
  }

/-- A frame with no state-gas grant starts with a zero meter.

This is where `Devm.StateGasZero` enters the interpreter: under
`rules.stateGas = none` no site sets `Msg.stateGasGrant`, so every frame --
top-level and child alike -- begins here, and the measure begins as `gasLeft`. -/
theorem initDevm_stateGasZero {msg : Msg} (h : msg.stateGasGrant = 0) :
    (initDevm msg).StateGasZero := by
  simp [initDevm, Devm.StateGasZero, StateGasMeter.zero, h]

@[simp] theorem initDevm_gasLeft (msg : Msg) : (initDevm msg).gasLeft = msg.gas :=
  rfl

@[simp] theorem initDevm_stateGasLeft (msg : Msg) :
    (initDevm msg).stateGasLeft = msg.stateGasGrant := rfl

def initEvm (msg : Msg) : Evm :=
  {
    pc := 0
    sta := initSevm msg
    dyna := initDevm msg
  }

def Msg.benvAfterTransfer (msg : Msg) :
    Except (EvmError × State × AdrSet × TransientStorage) Benv :=
  if msg.shouldTransferValue ∧ msg.value ≠ 0 then do
    let benv ←
      (msg.benv.subBal msg.caller msg.value).toExcept
        ⟨.internal (.assertion .none), msg.benv.state, msg.benv.createdAccounts,
          msg.tenv.transientStorage⟩
    .ok <| benv.addBal msg.currentTarget msg.value
  else
    .ok msg.benv

/-- A zero-value message entry leaves the entire block environment untouched. -/
@[simp] theorem Msg.benvAfterTransfer_of_value_zero {msg : Msg} (hzero : msg.value = 0) :
    msg.benvAfterTransfer = .ok msg.benv := by
  simp [Msg.benvAfterTransfer, hzero]

def Execution.withPc (pc : Nat) (exn : Execution) :
     Except (EvmError × Devm) (Nat × Devm) := do
  let devm ← exn
  .ok ⟨pc, devm⟩

def NextOp.size : NextOp → Nat
  | plain _ => 1
  | message _ => 1
  | push xs _ => xs.length + 1
  -- EIP-8024: one immediate byte, so `pc += 2` -- for an accepted immediate.
  -- A forbidden one halts before the counter moves, so its size is never read.
  | dupn _ => 2
  | swapn _ => 2
  | exchange _ => 2

-- the message passed to the sub-call performed by a call-type instruction.
-- factored out as a named definition to prevent context blowup in proofs.
def callMsg
    (sevm: Sevm)
    (evm1: Devm)
    (gas: Nat)
    (value: U256)
    (caller: Address)
    (target: Address)
    (codeAddress: Address)
    (shouldTransferValue: Bool)
    (isStaticcall: Bool)
    (calldata: Bytes)
    (code : ByteArray)
    (disablePrecompiles: Bool) : Msg :=
  {
    benv := {
      state := evm1.state
      createdAccounts := evm1.createdAccounts
      stat := sevm.benvStat
      storageWrites := evm1.world.storageWrites}
    tenv := {transientStorage := evm1.transientStorage, stat := sevm.tenvStat}
    caller := caller
    target := target
    gas := gas
    currentTarget := target
    value := value
    data := calldata
    codeAddress := codeAddress
    code := code
    depth := sevm.depth - 1
    shouldTransferValue := shouldTransferValue
    isStatic := isStaticcall || sevm.isStatic
    accessedAddresses := evm1.accessedAddresses
    accessedStorageKeys := evm1.accessedStorageKeys
    disablePrecompiles := disablePrecompiles
    inheritedDeletions :=
      if sevm.benvStat.rules.settlement.selfdestructRefund = 0 then .emptyWithCapacity
      else evm1.accountsToDelete
  }

/-!
Flattened interpreter core.  All frame-local definitions below are
non-recursive and fuel-free; `execFueled` is the single fueled driver.
-/

/-- The message passed to a CREATE/CREATE2 child.  This named barrier is the
CREATE-family counterpart of `callMsg`. -/
def createMsg
    (sevm : Sevm) (devm : Devm) (createGas : Nat) (endowment : U256)
    (newAddress : Address) (calldata : Bytes) : Msg :=
  {
    benv := Benv.mk devm.state devm.createdAccounts sevm.benvStat devm.world.storageWrites
    tenv := {transientStorage := devm.transientStorage, stat := sevm.tenvStat}
    caller := sevm.currentTarget
    target := .none
    gas := createGas
    value := endowment
    data := []
    code := .mk <| .mk calldata
    currentTarget := newAddress
    depth := sevm.depth - 1
    codeAddress := .none
    shouldTransferValue := true
    isStatic := false
    accessedAddresses := devm.accessedAddresses
    accessedStorageKeys := devm.accessedStorageKeys
    disablePrecompiles := false
    inheritedDeletions :=
      if sevm.benvStat.rules.settlement.selfdestructRefund = 0 then .emptyWithCapacity
      else devm.accountsToDelete
  }

instance {w a} : Decidable (State.isDead w a) := by
  simp [State.isDead]
  cases w[a]?
  · simp; apply instDecidableTrue
  · simp [Account.isEmpty]; apply instDecidableAnd

def State.code (w : State) (a : Address) : ByteArray :=
  match w[a]? with
  | none => ByteArray.mk #[]
  | some x => x.code

-- P0.6 item 3: the leading byte of the fixed 32-byte hash is read through the
-- total `head?`, never a partial index; an (unrepresentable) empty byte list
-- would simply fail the predicate.
def correctBlobHashVersion (h : U256) : Prop :=
  h.toBytes.head? = some 0x01

instance : DecidablePred correctBlobHashVersion := by
  intro h; simp [correctBlobHashVersion]; infer_instance

def Log.toRlpItem (l : Log) : Rlp.Item :=
  .list [
    .bytes l.address.toBytes,
    .list (l.topics.map U256.toRlpItem),
    .bytes l.data
  ]

def List.putIndex {ξ : Type u} (xs : List ξ) : List (Nat × ξ) :=
  let rec aux : Nat → List ξ → List (Nat × ξ)
    | _, [] => []
    | k, x :: xs => (k, x) :: aux (k + 1) xs
  aux 0 xs

def Bytes.toByteArray (xs : Bytes) : ByteArray := .mk <| .mk xs

def nibbleKey (pr : Bytes × Bytes) : Bytes × Bytes :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨Bytes.toNibbles ad, ac⟩

def receiptsRoot (w : List (Bytes × Bytes)) : U256 :=
  let keyVals : List (Bytes × Bytes) := (List.map nibbleKey w)
  let finalNTB : TrieBuilder := Std.TreeMap.ofList keyVals _
  trie finalNTB

def addIndexToBloom (hash : Bytes) (index : Nat) (bloom : Bytes) : Bytes :=
  let bitToSet : UInt16 :=
    (UInt16.ofBytes (hash.getD index 0) (hash.getD (index + 1) 0)) &&& (0x07FF : UInt16)
  let bitIndex : UInt16 := 0x07FF - bitToSet
  let byteIndex : Nat := (bitIndex / 8).toNat
  let bitValue : UInt8 := 0x01 <<< (0x07 - (bitIndex.lows &&& 0x07))
  let origValue : UInt8 := bloom.getD byteIndex 0
  bloom.set byteIndex (origValue ||| bitValue)

def addEntryToBloom (bloom : Bytes) (entry : Bytes) : Bytes :=
  let hash := (Bytes.keccak entry).toBytes
  addIndexToBloom hash 4 <|
  addIndexToBloom hash 2 <|
  addIndexToBloom hash 0 bloom

def addLogToBloom (bloom : Bytes) (log : Log) : Bytes :=
  let bloom' := addEntryToBloom bloom log.address.toBytes
  List.foldl addEntryToBloom bloom' (log.topics.map U256.toBytes)

def logsBloom (l : List Log) : Bytes :=
  List.foldl addLogToBloom (List.replicate 256 0x00) l

/-- A header's fork-dependent trailing fields, as `decodeHeaderOptionals`
produces them. -/
private structure HeaderOptionals : Type where
  baseFeePerGas : Option Nat := none
  withdrawalsRoot : Option U256 := none
  blobGasUsed : Option Nat := none
  excessBlobGas : Option Nat := none
  parentBeaconBlockRoot : Option U256 := none
  requestsHash : Option U256 := none
  blockAccessListHash : Option U256 := none
  slotNumber : Option UInt64 := none

/-- The representation facts the trailing fields carry: the base fee is a
`U256`, the two blob-gas fields are `U64`. -/
private def HeaderOptionals.Bounded (o : HeaderOptionals) : Prop :=
  (∀ b ∈ o.baseFeePerGas, b < 2 ^ 256) ∧
  (∀ b ∈ o.blobGasUsed, b < 2 ^ 64) ∧
  (∀ b ∈ o.excessBlobGas, b < 2 ^ 64)

/-- The rejection of a header tail no fork's shape accepts. A count that is
some fork's width (an item of the wrong kind at that width) stays a structure
error; any other count is `headerWidth`, the fixture vocabulary's
`INCORRECT_BLOCK_FORMAT` (goal U11a). The rendered detail is unchanged. -/
private def headerWidthError (n : Nat) : DecodeError :=
  let detail := s!"header : expected 15, 16, 17, 20, 21 or 23 fields, but found {n}"
  if n ∈ [15, 16, 17, 20, 21, 23] then .rlpStructure (.text detail)
  else .headerWidth (.text detail)

/-- Decode a header's fork-dependent trailing fields: everything after `nonce`.

Its own function, and not inlined into `BLT.toExHeader`, for two reasons: the
accepted shapes are a statement worth reading on their own, and the header
decoder's soundness proof then sees one `←` here and one bounds lemma about it,
rather than a case split whose arms all establish the same thing.

Exactly six tails are accepted, mirroring `Header.toBLT`'s nesting: none
(15 fields, Byzantium through Berlin), the base fee (16, London through
Paris), the withdrawals root (17, Shanghai), the Cancun triple (20), the
requests hash (21, Prague through BPO2), and the Amsterdam pair (23).
**18, 19 and 22 fields are rejected** (as `headerWidth`, see `headerWidthError`). A header carrying a block-access-list
hash but no slot number, or half of Cancun's triple, is not a header of any
fork, and accepting it would mean guessing which field the sender omitted.
Which shape a given fork requires is `validateHeader`'s rule, not this one's. -/
private def decodeHeaderOptionals :
    List Rlp.Item → Except DecodeError HeaderOptionals
  | [] => .ok {}
  | [.bytes baseFee] => do
    let baseFee ← baseFee.toRlpNat "header baseFeePerGas" 32
    .ok { baseFeePerGas := some baseFee }
  | [.bytes baseFee, .bytes withdrawalsRoot] => do
    let baseFee ← baseFee.toRlpNat "header baseFeePerGas" 32
    let withdrawalsRoot ← withdrawalsRoot.toRlpHash "header withdrawalsRoot"
    .ok { baseFeePerGas := some baseFee, withdrawalsRoot := some withdrawalsRoot }
  | .bytes baseFee :: .bytes withdrawalsRoot :: .bytes blobGasUsed ::
      .bytes excessBlobGas :: .bytes parentBeaconBlockRoot :: tail => do
    let baseFee ← baseFee.toRlpNat "header baseFeePerGas" 32
    let withdrawalsRoot ← withdrawalsRoot.toRlpHash "header withdrawalsRoot"
    let blobGasUsed ← blobGasUsed.toRlpUInt64 "header blobGasUsed"
    let excessBlobGas ← excessBlobGas.toRlpUInt64 "header excessBlobGas"
    let parentBeaconBlockRoot ←
      parentBeaconBlockRoot.toRlpHash "header parentBeaconBlockRoot"
    let cancun : HeaderOptionals :=
      { baseFeePerGas := some baseFee, withdrawalsRoot := some withdrawalsRoot
        blobGasUsed := some blobGasUsed.toNat
        excessBlobGas := some excessBlobGas.toNat
        parentBeaconBlockRoot := some parentBeaconBlockRoot }
    match tail with
    | [] => .ok cancun
    | [.bytes requestsHash] => do
      let requestsHash ← requestsHash.toRlpHash "header requestsHash"
      .ok { cancun with requestsHash := some requestsHash }
    | [.bytes requestsHash, .bytes balHash, .bytes slotNumber] => do
      let requestsHash ← requestsHash.toRlpHash "header requestsHash"
      let balHash ← balHash.toRlpHash "header blockAccessListHash"
      let slotNumber ← slotNumber.toRlpUInt64 "header slotNumber"
      .ok { cancun with
        requestsHash := some requestsHash
        blockAccessListHash := some balHash
        slotNumber := some slotNumber }
    | tail =>
      .error <| headerWidthError (20 + tail.length)
  | tail =>
    .error <| headerWidthError (15 + tail.length)

/-- Every tail `decodeHeaderOptionals` accepts carries its fields' widths. -/
private theorem decodeHeaderOptionals_bounded {tail : List Rlp.Item}
    {o : HeaderOptionals} (h : decodeHeaderOptionals tail = .ok o) :
    o.Bounded := by
  unfold decodeHeaderOptionals at h
  split at h
  · cases h; exact ⟨by simp, by simp, by simp⟩
  · simp only [Except.bind_eq_ok_iff] at h
    obtain ⟨_, hbf, hm⟩ := h
    simp only [Except.ok.injEq] at hm
    subst hm
    exact ⟨by simpa using Bytes.toRlpNat_lt_two_pow_256 hbf, by simp, by simp⟩
  · simp only [Except.bind_eq_ok_iff] at h
    obtain ⟨_, hbf, _, _, hm⟩ := h
    simp only [Except.ok.injEq] at hm
    subst hm
    exact ⟨by simpa using Bytes.toRlpNat_lt_two_pow_256 hbf, by simp, by simp⟩
  · simp only [Except.bind_eq_ok_iff] at h
    obtain ⟨bf, hbf, _, _, bgu, _, ebg, _, _, _, hm⟩ := h
    have hb : ∀ b ∈ (some bf : Option Nat), b < 2 ^ 256 := by
      simpa using Bytes.toRlpNat_lt_two_pow_256 hbf
    have hg : ∀ b ∈ (some bgu.toNat : Option Nat), b < 2 ^ 64 := by
      simpa using bgu.toNat_lt
    have he : ∀ b ∈ (some ebg.toNat : Option Nat), b < 2 ^ 64 := by
      simpa using ebg.toNat_lt
    split at hm
    · cases hm; exact ⟨hb, hg, he⟩
    · simp only [Except.bind_eq_ok_iff, Except.ok.injEq] at hm
      obtain ⟨_, _, rfl⟩ := hm
      exact ⟨hb, hg, he⟩
    · simp only [Except.bind_eq_ok_iff, Except.ok.injEq] at hm
      obtain ⟨_, _, _, _, _, _, rfl⟩ := hm
      exact ⟨hb, hg, he⟩
    · exact absurd hm (by simp)
  · exact absurd h (by simp)

def Rlp.Item.toExceptHeader : Rlp.Item → Except DecodeError Header
  | .list (
      .bytes parentHash ::
      .bytes ommersHash ::
      .bytes coinbase ::
      .bytes stateRoot ::
      .bytes txsRoot ::
      .bytes receiptRoot ::
      .bytes bloom ::
      .bytes difficulty ::
      .bytes number ::
      .bytes gasLimit ::
      .bytes gasUsed ::
      .bytes timestamp ::
      .bytes extraData ::
      .bytes prevRandao ::
      .bytes nonce ::
      tail
    ) => do
      -- Every field is checked for shape before its value is converted. The
      -- shapes are not uniform and the difference matters: hashes, roots, the
      -- coinbase, the bloom and the nonce are *fixed-width bytes*, where a
      -- leading zero is content; the integers are *canonical scalars*, where a
      -- leading zero is malformed and zero is the empty string. Widths follow
      -- execution-specs' header types -- `Uint`/`U256` for the numbers modelled
      -- here as `Nat`, and `U64` for the two blob-gas fields, which is the one
      -- place a header field carries the 64-bit overflow identity.
      let parentHash ← parentHash.toRlpHash "header parentHash"
      let ommersHash ← ommersHash.toRlpHash "header ommersHash"
      let coinbase ← coinbase.toRlpAddress "header coinbase"
      let stateRoot ← stateRoot.toRlpHash "header stateRoot"
      let txsRoot ← txsRoot.toRlpHash "header transactionsRoot"
      let receiptRoot ← receiptRoot.toRlpHash "header receiptRoot"
      let bloom ← bloom.toRlpFixed "header bloom" 256
      let difficulty ← difficulty.toRlpNat "header difficulty" 32
      let number ← number.toRlpNat "header number" 32
      let gasLimit ← gasLimit.toRlpNat "header gasLimit" 32
      let gasUsed ← gasUsed.toRlpNat "header gasUsed" 32
      let timestamp ← timestamp.toRlpNat "header timestamp" 32
      let prevRandao ← prevRandao.toRlpHash "header prevRandao"
      let nonce ← nonce.toRlpFixedUInt64 "header nonce"
      -- Shape-optional, but exactly typed when present: an absent field and a
      -- malformed one are different failures.
      let optionals ← decodeHeaderOptionals tail
      .ok {
        parentHash := parentHash
        ommersHash := ommersHash
        coinbase := coinbase
        stateRoot := stateRoot
        transactionsRoot := txsRoot
        receiptsRoot := receiptRoot
        logsBloom := bloom
        difficulty := difficulty
        number := number
        gasLimit := gasLimit
        gasUsed := gasUsed
        timestamp := timestamp
        extraData := extraData
        prevRandao := prevRandao
        nonce := nonce
        baseFeePerGas := optionals.baseFeePerGas
        withdrawalsRoot := optionals.withdrawalsRoot
        blobGasUsed := optionals.blobGasUsed
        excessBlobGas := optionals.excessBlobGas
        parentBeaconBlockRoot := optionals.parentBeaconBlockRoot
        requestsHash := optionals.requestsHash
        blockAccessListHash := optionals.blockAccessListHash
        slotNumber := optionals.slotNumber
      }
  | _ =>
    .error <| DecodeError.structure "header"
      "expected a list of 15, 16, 17, 20, 21 or 23 byte-string fields"

/-- Strict header-decoder soundness (P0.3/P0.4). Every header this decoder
produces satisfies `Header.WireWellFormed`, which is what makes that predicate
a *lift* of the decoder rather than an independently invented policy: it holds
of exactly the values the wire can deliver. -/
theorem Rlp.Item.toExceptHeader_wireWellFormed {blt : Rlp.Item} {hdr : Header}
    (h : blt.toExceptHeader = .ok hdr) : hdr.WireWellFormed := by
  unfold Rlp.Item.toExceptHeader at h
  split at h
  · simp only [Except.bind_eq_ok_iff] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hbl, _, hdf, _, hnb,
      _, hgl, _, hgu, _, hts, _, _, _, _, opt, hopt, hm⟩ := h
    have hb := Bytes.toRlpFixed_eq_ok hbl
    have h2 := Bytes.toRlpNat_lt_two_pow_256 hdf
    have h3 := Bytes.toRlpNat_lt_two_pow_256 hnb
    have h4 := Bytes.toRlpNat_lt_two_pow_256 hgl
    have h5 := Bytes.toRlpNat_lt_two_pow_256 hgu
    have h6 := Bytes.toRlpNat_lt_two_pow_256 hts
    -- The trailing fields' widths are `decodeHeaderOptionals`'s own lemma, so
    -- one bind step discharges every accepted shape at once.
    obtain ⟨h7, h8, h9⟩ := decodeHeaderOptionals_bounded hopt
    simp only [Except.ok.injEq] at hm
    subst hm
    exact ⟨hb, h2, h3, h4, h5, h6, h7, h8, h9⟩
  · exact absurd h (by simp)

/-- The child's excess blob gas.

Every parameter is read from the *child's* blob schedule, which is what makes a
BPO transition take effect on the first block of the new schedule rather than
one block late. Osaka's EIP-7918 branch also reads both fees from the parent
header: the blob fee at the parent's excess and the execution base fee the
parent actually carried. The downstream `checkHeaderShape_blobGas` theorem
in `Jaune.Transaction` ties both parent fields' presence to its rules;
`ChainConfig.ShapeCoherent` supplies that condition at configured chain heads,
so a pre-Cancun parent contributes zero through the absent fields below. -/
def calcExcessBlobGas (blob : BlobSchedule) (parentHeader : Header) : Nat :=
  -- Cancun's first block: a parent header without the blob fields counts them
  -- as zero. EELS keys this on the parent header's class
  -- (`cancun/vm/gas.py`, `isinstance(parent_header, Header)`), which is this
  -- shape test; every later parent carries both fields.
  let parentExcessBlobGas := parentHeader.excessBlobGas.getD 0
  let parentBlobGasUsed := parentHeader.blobGasUsed.getD 0
  let parentBlobGas : Nat :=
    parentExcessBlobGas + parentBlobGasUsed
  if parentBlobGas < blob.target then
    0
  else
    match blob.reserveBaseCost with
    | none =>
      parentBlobGas - blob.target
    | some reserveBaseCost =>
      let targetBlobGasPrice :=
        Gas.perBlob *
          getBaseFeePerBlobGas blob parentExcessBlobGas
      let baseBlobTxPrice :=
        reserveBaseCost * parentHeader.baseFeePerGas.getD 0
      if baseBlobTxPrice > targetBlobGasPrice then
        parentExcessBlobGas +
          parentBlobGasUsed * (blob.max - blob.target) / blob.max
      else
        parentBlobGas - blob.target

structure MsgCallOutput : Type where
  gasLeft : Nat
  refundCounter : Int
  logs : List Log
  accountsToDelete : AdrSet
  error: Option SettledHalt
  returnData : Bytes
  /-- State-gas reservoir returned by the top frame. Zero on the legacy path. -/
  stateGasLeft : Nat := 0
  /-- Net state gas consumed by the transaction; refunds may make it negative. -/
  stateGasUsed : Int := 0
  /-- EIP-7928: the accounts the top frame and its children read (goal C).
  Empty on the legacy path and under `rules.bal = none`. -/
  accountReads : AdrSet := .emptyWithCapacity
  /-- EIP-7928: the storage slots read. -/
  storageReads : KeySet := .emptyWithCapacity
  /-- Explicit writes surviving frame rollback and storage deletion. -/
  storageWrites : KeySet := .emptyWithCapacity
  /-- EIP-161: the accounts the transaction touched, for the end-of-transaction
  sweep. Empty when the transaction failed, on the Amsterdam path, and under
  every rule set without `settle.touchedSweep`. -/
  touchedAccounts : AdrSet := .emptyWithCapacity

def Except.bimap
  {ε : Type u0} {δ : Type u1} {ξ : Type u2} {υ : Type u3}
  (f : ε → δ) (g : ξ → υ) : Except ε ξ → Except δ υ
  | .error e => .error <| f e
  | .ok x => .ok <| g x

def accountHasCodeOrNonce (state : State) (adr : Address) : Bool :=
  state.getNonce adr > 0 || !(state.getCode adr).isEmpty

def accountHasStorage (state : State) (adr : Address) : Bool :=
  !(state.getStor adr).isEmpty

def Transaction.signingHash (tx : Transaction) : Option U256 :=
  match tx.type with
  | .legacy gasPrice receiver =>
    if tx.v = 27 || tx.v = 28
    then
      -- signing_hash_pre155
      some <|
        Bytes.keccak <|
          Rlp.Item.toBytes <|
            .list [
              .bytes tx.nonce.toBytes.sig,
              .bytes gasPrice.toBytes,
              .bytes tx.gasLimit.toBytes,
              .bytes ((receiver <&> Address.toBytes).getD []),
              .bytes tx.value.toBytes,
              .bytes tx.data
            ]
    else do
      -- signing_hash155
      let chainId : Nat := (tx.v - 35) / 2
      some <|
        Bytes.keccak <|
          Rlp.Item.toBytes <|
            .list [
              .bytes tx.nonce.toBytes.sig,
              .bytes gasPrice.toBytes,
              .bytes tx.gasLimit.toBytes,
              .bytes ((receiver <&> Address.toBytes).getD []),
              .bytes tx.value.toBytes,
              .bytes tx.data,
              .bytes chainId.toBytes,
              .bytes [],
              .bytes []
            ]
  -- def signing_hash2930
  | .eip2930 chainId gasPrice receiver accessList =>
    Bytes.keccak <|
      .cons (0x01 : UInt8) <|
        Rlp.Item.toBytes <|
          .list [
            .bytes chainId.toBytes.sig,
            .bytes tx.nonce.toBytes.sig,
            .bytes gasPrice.toBytes,
            .bytes tx.gasLimit.toBytes,
            .bytes ((receiver <&> Address.toBytes).getD []),
            .bytes tx.value.toBytes,
            .bytes tx.data,
            accessList.toRlpItem
          ]
  -- signing_hash1559
  | .eip1559 chainId maxPriorityFee maxFee receiver accessList =>
    Bytes.keccak <|
      .cons (0x02 : UInt8) <|
        Rlp.Item.toBytes <|
          .list [
            .bytes chainId.toBytes.sig,
            .bytes tx.nonce.toBytes.sig,
            .bytes maxPriorityFee.toBytes,
            .bytes maxFee.toBytes,
            .bytes tx.gasLimit.toBytes,
            .bytes ((receiver <&> Address.toBytes).getD []),
            .bytes tx.value.toBytes,
            .bytes tx.data,
            accessList.toRlpItem
          ]
  -- def signing_hash4844
  | .eip4844 chainId maxPriorityFee maxFee receiver accessList maxBlobFee blobHashes =>
    Bytes.keccak <|
      .cons (0x03 : UInt8) <|
        Rlp.Item.toBytes <|
          .list [
            .bytes chainId.toBytes.sig,
            .bytes tx.nonce.toBytes.sig,
            .bytes maxPriorityFee.toBytes,
            .bytes maxFee.toBytes,
            .bytes tx.gasLimit.toBytes,
            .bytes receiver.toBytes,
            .bytes tx.value.toBytes,
            .bytes tx.data,
            accessList.toRlpItem,
            .bytes maxBlobFee.toBytes,
            .list <| blobHashes.map <| .bytes ∘ U256.toBytes
          ]
  | .eip7702 chainId maxPriorityFee maxFee receiver accessList auths =>
    Bytes.keccak <|
      .cons (0x04 : UInt8) <|
        Rlp.Item.toBytes <|
          .list [
            .bytes chainId.toBytes.sig,
            .bytes tx.nonce.toBytes.sig,
            .bytes maxPriorityFee.toBytes,
            .bytes maxFee.toBytes,
            .bytes tx.gasLimit.toBytes,
            .bytes receiver.toBytes,
            .bytes tx.value.toBytes,
            .bytes tx.data,
            accessList.toRlpItem,
            .list <| auths.map Authorization.toRlpItem
          ]

def recoverSender (chain_id: UInt64) (tx: Transaction) : Except CryptoError Address := do
  let r := tx.r.toU256
  let s := tx.s.toU256
  if (r = 0 ∨ secp256k1.curveOrder.toU256 ≤ r) then
    .error (.invalidSignature (.text "bad r"))
  if (s = 0 ∨ secp256k1.curveOrder.toU256 / 2 < s) then
    .error (.invalidSignature (.text "bad s"))
  let v := tx.v
  let signingHash ←
    tx.signingHash.toExcept (.invalidSignature (.text "signing hash is None"))
  match tx.type with
  | .legacy _ _ =>
    if v = 27 ∨ v = 28
    then
      (secp256k1.recover signingHash (v - 27).toBool r s).toExcept
        (.invalidSignature (.text "sender recovery failed"))
    else
      let chain_id_x2 := (chain_id.toNat) * (2)
      .assert (v = 35 + chain_id_x2 ∨ v = 36 + chain_id_x2)
        (CryptoError.invalidSignature (.text "bad v"))
      (secp256k1.recover signingHash (v - 35 - chain_id_x2).toBool r s).toExcept
        (.invalidSignature (.text "sender recovery failed"))
  | _ =>
    .assert (v < 2) (CryptoError.invalidSignature .none)
    (secp256k1.recover signingHash v.toBool r s).toExcept
      (.invalidSignature (.text "sender recovery failed"))

def recoverAuthority (auth : Authorization) : Except CryptoError Address := do
  let yParity := auth.yParity
  let r := auth.r
  let s := auth.s
  if (
    1 < yParity ∨
    r = 0 ∨  secp256k1.curveOrder.toU256 ≤ r ∨
    s = 0 ∨ (secp256k1.curveOrder.toU256 / 2) < s
  ) then
    .error (.invalidSignature .none)
  let signingHash : U256 :=
    Bytes.keccak <|
      List.append setCodeTransactionMagic <|
        Rlp.Item.toBytes <| .list [
          .bytes auth.chainId.toBytes.sig,
          .bytes auth.address.toBytes,
          .bytes auth.nonce.toBytes.sig
        ]
  -- EIP-7702 invalidates an authorization tuple, not its enclosing
  -- transaction: a recovery failure is therefore handled by
  -- `setDelegationStep` exactly like the other invalid-signature forms.
  (secp256k1.recover signingHash yParity.toBool r s ).toExcept (.invalidSignature .none)

def setDelegationStep
    (auth : Authorization) (msg : Msg) (refundCounter : U256) :
    Except EvmError (Msg × U256) := do
  if auth.chainId != msg.benv.stat.chainId.toU256 && auth.chainId != 0 then
    .ok ⟨msg, refundCounter⟩
  else if auth.nonce = UInt64.max then
    .ok ⟨msg, refundCounter⟩
  else
    match recoverAuthority auth with
    | .error (.invalidSignature _) =>
      -- EIP-7702 invalidates the authorization tuple on exactly this reason
      -- and on no other: the tuple is skipped and processing continues.
      .ok ⟨msg, refundCounter⟩
    | .error err => .error (.crypto err)
    | .ok authority =>
      let msg := {msg with accessedAddresses := msg.accessedAddresses.insert authority}
      let authorityAccount : Account :=
        msg.benv.state.get authority
      let authorityCode : ByteArray := authorityAccount.code
      if ¬ (authorityCode.isEmpty ∨ isValidDelegation authorityCode) then
        .ok ⟨msg, refundCounter⟩
      else if authorityAccount.nonce != auth.nonce then
        .ok ⟨msg, refundCounter⟩
      else
        let refundCounter :=
          if AccountExists msg.benv.state authority then
            refundCounter +
              (msg.benv.stat.rules.gas.perAuthorizationIntrinsic - Gas.perAuthBaseCost).toU256
          else
            refundCounter
        let codeToSet : ByteArray :=
          if auth.address = 0 then
            .empty
          else
            (eoaDelegationMarker ++ auth.address.toBytes).toByteArray
        let msg := msg.setCode authority codeToSet
        let msg := msg.incrNonce authority
        .ok ⟨msg, refundCounter⟩

def setDelegationLoop : List Authorization → Msg → U256 → Except EvmError (Msg × U256)
  | [], msg, refundCounter => .ok ⟨msg, refundCounter⟩
  | auth :: auths, msg, refundCounter => do
    let ⟨msg, refundCounter⟩ ← setDelegationStep auth msg refundCounter
    setDelegationLoop auths msg refundCounter

def setDelegation (msg : Msg) : Except EvmError (Msg × U256) := do
  let ⟨msg, refundCounter⟩ ← setDelegationLoop msg.tenv.stat.auths msg 0
  let msg ←
    match msg.codeAddress with
    | none =>
      -- Unreachable: a validated type-4 transaction has a receiver, so its
      -- message always carries a code address. A breach is an internal
      -- invariant failure and must fail closed, never read as a block verdict.
      .error (.internal (.invariant (.text "Invalid type 4 transaction: no target")))
    | some ca =>
      .ok {
        msg with
        code := msg.benv.state.getCode ca
      }
  .ok ⟨msg, refundCounter⟩

--------------- CANONICALITY THROUGH EXECUTION (P0.4, STEP 4) ---------------

-- Checkpoint 2, frame half: canonicality through delegation access, message
-- initialisation, frame enter/settle/resume, the step machinery, and the
-- fueled driver. Restoration sources are exactly the ones the invariant
-- carries: a message's saved pair (`Frame.Canonical`, both messages), a
-- settlement error payload (`Except.CanonicalSettle`), and a child world
-- incorporated wholesale.

/-- Delegation access touches only the accessed-address set. Stated over the
projection because callers consume the result through an irrefutable `let`. -/
theorem accessDelegation_canonical {devm : Devm} (h : devm.Canonical)
    (adr : Address) : (accessDelegation devm adr).2.2.2.2.Canonical := by
  unfold accessDelegation
  dsimp only
  split
  · exact Devm.Canonical.of_world_eq h rfl
  · exact h

/-- The eq-conditioned form, for walks that destructure the tuple. -/
theorem accessDelegation_eq_canonical {devm d' : Devm} {adr : Address} {b : Bool}
    {a2 : Address} {code : ByteArray} {n : Nat} (h : devm.Canonical)
    (heq : accessDelegation devm adr = (b, a2, code, n, d')) : d'.Canonical := by
  have hc := accessDelegation_canonical h adr
  rw [heq] at hc
  exact hc

theorem GasSchedule.accessDelegation_canonical {gas : GasSchedule} {devm : Devm}
    (h : devm.Canonical) (adr : Address) :
    (gas.accessDelegation devm adr).2.2.2.2.Canonical := by
  unfold GasSchedule.accessDelegation
  dsimp only
  split
  · exact Devm.Canonical.of_world_eq h rfl
  · exact h

theorem ForkRules.accessDelegation_canonical {rules : ForkRules} {devm : Devm}
    (h : devm.Canonical) (adr : Address) :
    (rules.accessDelegation devm adr).2.2.2.2.Canonical := by
  unfold ForkRules.accessDelegation
  split
  · exact GasSchedule.accessDelegation_canonical h adr
  · exact h

theorem completeDelegationAccess_canonical {devm : Devm}
    (h : devm.Canonical) (delegated : Bool) (adr : Address) :
    (completeDelegationAccess devm delegated adr).2.Canonical := by
  unfold completeDelegationAccess
  dsimp only
  split
  · exact Devm.Canonical.of_world_eq h rfl
  · exact h

theorem initSevm_canonical {msg : Msg} (h : msg.Canonical) :
    (initSevm msg).Canonical := h.1.2

theorem initDevm_canonical {msg : Msg} (h : msg.Canonical) :
    (initDevm msg).Canonical := by
  change State.Canonical msg.benv.state ∧ TransientStorage.Canonical msg.tenv.transientStorage
  exact ⟨h.1.1, h.2⟩

theorem initEvm_canonical {msg : Msg} (h : msg.Canonical) :
    (initEvm msg).Canonical := by
  change Sevm.Canonical (initSevm msg) ∧
    State.Canonical msg.benv.state ∧ TransientStorage.Canonical msg.tenv.transientStorage
  exact ⟨h.1.2, h.1.1, h.2⟩

/-- A successful pre-execution value transfer moves balances through
`subBal`/`addBal` only. -/
theorem Msg.benvAfterTransfer_ok_canonical {msg : Msg} (h : msg.Canonical)
    {benv : Benv} (hb : msg.benvAfterTransfer = .ok benv) : benv.Canonical := by
  unfold Msg.benvAfterTransfer at hb
  split at hb
  · cases hsb : msg.benv.subBal msg.caller msg.value with
    | none =>
      rw [hsb] at hb
      exact absurd hb (by simp [Option.toExcept, bind, Except.bind])
    | some b1 =>
      rw [hsb] at hb
      simp only [Option.toExcept, bind, Except.bind, Except.ok.injEq] at hb
      rw [← hb]
      exact Benv.Canonical.addBal (Benv.Canonical.subBal h.1 hsb) _ _
  · cases hb
    exact h.1

/-- A failed pre-execution transfer reports exactly the message's saved
pair, which the invariant already covers. -/
theorem Msg.benvAfterTransfer_error_canonical {msg : Msg} (h : msg.Canonical)
    {e} (he : msg.benvAfterTransfer = .error e) :
    State.Canonical e.2.1 ∧ TransientStorage.Canonical e.2.2.2 := by
  unfold Msg.benvAfterTransfer at he
  split at he
  · cases hsb : msg.benv.subBal msg.caller msg.value with
    | none =>
      rw [hsb] at he
      simp only [Option.toExcept, bind, Except.bind, Except.error.injEq] at he
      rw [← he]
      exact ⟨h.1.1, h.2⟩
    | some b1 =>
      rw [hsb] at he
      exact absurd he (by simp [Option.toExcept, bind, Except.bind])
  · exact absurd he (by simp)

/-- The child message of a call-type instruction lives on the caller's world
and the frame's original state. -/
theorem callMsg_canonical {sevm : Sevm} {evm1 : Devm}
    (hs : sevm.Canonical) (hd : evm1.Canonical)
    (gas : Nat) (value : U256) (caller target codeAddress : Address)
    (shouldTransferValue isStaticcall : Bool) (calldata : Bytes)
    (code : ByteArray) (disablePrecompiles : Bool) :
    (callMsg sevm evm1 gas value caller target codeAddress
      shouldTransferValue isStaticcall calldata code
      disablePrecompiles).Canonical :=
  ⟨⟨hd.1, hs⟩, hd.2⟩

theorem createMsg_canonical {sevm : Sevm} {devm : Devm}
    (hs : sevm.Canonical) (hd : devm.Canonical)
    (createGas : Nat) (endowment : U256) (newAddress : Address)
    (calldata : Bytes) :
    (createMsg sevm devm createGas endowment newAddress calldata).Canonical :=
  ⟨⟨hd.1, hs⟩, hd.2⟩

/-- One EIP-7702 authorization step preserves the message invariant on its
success channel: every arm returns the message unchanged up to bookkeeping
fields outside the invariant, or applies `setCode`/`incrNonce`. The error
channel carries no state. -/
theorem setDelegationStep_canonical {auth : Authorization} {msg : Msg} {rc : U256}
    (h : msg.Canonical) {p} (hp : setDelegationStep auth msg rc = .ok p) :
    p.1.Canonical := by
  unfold setDelegationStep at hp
  split at hp
  · cases hp; exact h
  · split at hp
    · cases hp; exact h
    · split at hp
      · cases hp; exact h
      · nomatch hp
      · dsimp only at hp
        split at hp
        · cases hp; exact h
        · split at hp
          · cases hp; exact h
          · cases hp
            exact Msg.Canonical.incrNonce (Msg.Canonical.setCode h _ _) _

theorem setDelegationLoop_canonical :
    ∀ (auths : List Authorization) {msg : Msg} {rc : U256}, msg.Canonical →
      ∀ {p}, setDelegationLoop auths msg rc = .ok p → p.1.Canonical
  | [], _, _, h, _, hp => by cases hp; exact h
  | auth :: auths, msg, rc, h, p, hp => by
    unfold setDelegationLoop at hp
    rcases hq : setDelegationStep auth msg rc with e | q <;> rw [hq] at hp
    · nomatch hp
    · exact setDelegationLoop_canonical auths
        (setDelegationStep_canonical h hq) hp

/-- Processing an authorization list preserves the message invariant; the
final code refresh is outside the invariant. -/
theorem setDelegation_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : setDelegation msg = .ok p) : p.1.Canonical := by
  unfold setDelegation at hp
  rcases hq : setDelegationLoop msg.tenv.stat.auths msg 0 with e | q <;>
    rw [hq] at hp
  · nomatch hp
  · have hq1 := setDelegationLoop_canonical _ h hq
    simp only [bind, Except.bind] at hp
    split at hp
    · nomatch hp
    · cases hp
      exact hq1

/-! ### The zero-meter invariant through execution

The machine layer proves that every legacy instruction preserves
`Devm.StateGasZero`.  These result predicates add the frame and interpreter
structure needed to say the same thing about spawning, settlement, and the
fueled driver.  Amsterdam-only resume constructors are deliberately excluded:
under `rules.stateGas = none` they are unreachable. -/

def Evm.StateGasZero (evm : Evm) : Prop :=
  evm.sta.benvStat.rules.stateGas = none ∧ evm.dyna.StateGasZero

theorem executePrecompile_stateGasZero {evm : Evm}
    (h : evm.dyna.StateGasZero) (adr : Address) :
    (executePrecompile evm adr).StateGasZero := by
  unfold executePrecompile applyPrecompileResult
  split <;> exact h

theorem accessDelegation_stateGasZero {devm : Devm}
    (h : devm.StateGasZero) (adr : Address) :
    (accessDelegation devm adr).2.2.2.2.StateGasZero := by
  unfold accessDelegation
  dsimp only
  split <;> exact h

theorem GasSchedule.accessDelegation_stateGasZero {gas : GasSchedule}
    {devm : Devm} (h : devm.StateGasZero) (adr : Address) :
    (gas.accessDelegation devm adr).2.2.2.2.StateGasZero := by
  unfold GasSchedule.accessDelegation
  dsimp only
  split <;> exact h

theorem ForkRules.accessDelegation_stateGasZero {rules : ForkRules}
    {devm : Devm} (h : devm.StateGasZero) (adr : Address) :
    (rules.accessDelegation devm adr).2.2.2.2.StateGasZero := by
  unfold ForkRules.accessDelegation
  split
  · exact GasSchedule.accessDelegation_stateGasZero h adr
  · exact h

theorem completeDelegationAccess_stateGasZero {devm : Devm}
    (h : devm.StateGasZero) (delegated : Bool) (adr : Address) :
    (completeDelegationAccess devm delegated adr).2.StateGasZero := by
  unfold completeDelegationAccess
  dsimp only
  split <;> exact h

--------------- ACCOUNT ACCESSORS OVER STATE WRITERS ---------------

-- Account-field writers normalize empty accounts. Balance, nonce, and code
-- projections survive normalization, but storage is cleared on deletion.
-- Readers at another address remain unchanged.

theorem Devm.getCode_state (d : Devm) (a : Address) :
    d.getCode a = d.state.getCode a := rfl

theorem State.setBal_get_self {st : Jaune.State} {adr : Address} {v : U256} :
    (st.setBal adr v).get adr = ((st.get adr).withBalance v).clearIfEmpty :=
  State.setAccount_get_self _ _ _

theorem State.setBal_get_ne {st : Jaune.State} {adr a : Address} {v : U256} (h : adr ≠ a) :
    (st.setBal adr v).get a = st.get a := State.setAccount_get_ne _ h _

/-- A balance update clears storage exactly when it deletes the account. -/
theorem State.setBal_get_stor {st : Jaune.State} {b a : Address} {v : U256} :
    ((st.setBal b v).get a).storage =
      if b = a ∧ ((st.get b).withBalance v).isEmpty then .empty else (st.get a).storage := by
  by_cases h : b = a
  · subst h
    simp only [State.setBal_get_self, Account.clearIfEmpty_storage, eq_self, true_and]
    rfl
  · simp only [State.setBal_get_ne h, h, false_and, ite_false]

theorem State.setBal_get_code {st : Jaune.State} {b a : Address} {v : U256} :
    ((st.setBal b v).get a).code = (st.get a).code := by
  by_cases h : b = a
  · subst h; rw [State.setBal_get_self, Account.clearIfEmpty_code]; rfl
  · rw [State.setBal_get_ne h]

theorem State.of_subBal {st st' : Jaune.State} {ct : Address} {wad : U256}
    (h : st.subBal ct wad = some st') :
    wad ≤ st.bal ct ∧ st' = st.setBal ct (st.bal ct - wad) := by
  unfold State.subBal at h
  split_ifs at h with h_lt
  cases h
  exact ⟨U256.not_lt.mp h_lt, rfl⟩

theorem State.incrNonce_get_bal {st : Jaune.State} {adr a : Address} :
    ((st.incrNonce adr).get a).balance = (st.get a).balance := by
  simp only [State.incrNonce]
  by_cases h : adr = a
  · subst h; rw [State.setAccount_get_self, Account.clearIfEmpty_balance]
  · rw [State.setAccount_get_ne _ h]

/-- The general nonce mutator includes wraparound; callers rule out overflow.
Storage is cleared exactly when its resulting account is empty. -/
theorem State.incrNonce_get_stor {st : Jaune.State} {adr a : Address} :
    ((st.incrNonce adr).get a).storage =
      if adr = a ∧ ({st.get adr with nonce := (st.get adr).nonce + 1} : Account).isEmpty
      then .empty else (st.get a).storage := by
  simp only [State.incrNonce]
  by_cases h : adr = a
  · subst h
    simp only [State.setAccount_get_self, Account.clearIfEmpty_storage, eq_self, true_and]
  · simp only [State.setAccount_get_ne _ h, h, false_and, ite_false]

theorem State.incrNonce_get_code {st : Jaune.State} {adr a : Address} :
    ((st.incrNonce adr).get a).code = (st.get a).code := by
  simp only [State.incrNonce]
  by_cases h : adr = a
  · subst h; rw [State.setAccount_get_self, Account.clearIfEmpty_code]
  · rw [State.setAccount_get_ne _ h]

theorem State.setBal_getCode (st : State) (adr a : Address) (val : U256) :
    (st.setBal adr val).getCode a = st.getCode a :=
  State.setBal_get_code

theorem State.addBal_getCode (st : State) (adr a : Address) (val : U256) :
    (st.addBal adr val).getCode a = st.getCode a :=
  State.setBal_getCode st adr a (st.bal adr + val)

theorem State.subBal_getCode {st st' : State} {adr a : Address} {val : U256}
    (h : st.subBal adr val = some st') : st'.getCode a = st.getCode a := by
  rw [(State.of_subBal h).2]
  exact State.setBal_getCode st adr a (st.bal adr - val)

theorem Benv.addBal_getCode (benv : Benv) (adr a : Address) (val : U256) :
    (benv.addBal adr val).state.getCode a = benv.state.getCode a :=
  State.addBal_getCode benv.state adr a val

theorem Devm.incrNonce_getCode {devm : Devm} {adr a : Address} :
    (devm.incrNonce adr).getCode a = devm.getCode a :=
  State.incrNonce_get_code

theorem Benv.incrNonce_getCode {benv : Benv} {adr a : Address} :
    (benv.incrNonce adr).state.getCode a = benv.state.getCode a :=
  State.incrNonce_get_code

/-- A credit clears storage at `ca` precisely when it deletes that account. -/
theorem getStor_addBal (w : Jaune.State) (ca a : Address) (val : U256) :
    (w.addBal a val).getStor ca =
      if a = ca ∧ ((w.get a).withBalance (w.bal a + val)).isEmpty
      then .empty else w.getStor ca :=
  State.setBal_get_stor

/-- Persistent storage writes preserve account code. -/
theorem Devm.setStorVal_getCode (devm : Devm) (owner : Address)
    (key value : U256) (address : Address) :
    (devm.setStorVal owner key value).getCode address =
      devm.getCode address := by
  show ((devm.state.setStorVal owner key value).get address).code =
    (devm.state.get address).code
  by_cases h : owner = address
  · subst h
    rw [State.setStorVal_get_self]
  · rw [State.setStorVal_get_ne _ h]

/-- Installing code clears storage precisely when it deletes an empty account. -/
theorem Devm.setCode_getStor (devm : Devm) (address : Address)
    (code : ByteArray) :
    Devm.getStor (devm.setCode address code) = fun target =>
      if address = target ∧ ({devm.state.get address with code := code} : Account).isEmpty
      then .empty else devm.getStor target := by
  funext target
  change ((devm.state.setCode address code).get target).storage = _
  unfold State.setCode
  by_cases h : address = target
  · subst h
    simp only [State.setAccount_get_self, Account.clearIfEmpty_storage, eq_self, true_and]
    rfl
  · simp only [State.setAccount_get_ne _ h, h, false_and, ite_false]
    rfl

end Jaune
