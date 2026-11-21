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

def State.getStorage (w : State) (a : Address) : Storage := (w.get a).storage
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

/-- The effective code-designation lookup under the selected fork rules. -/
def ForkRules.delegatedCodeAddress (rules : ForkRules) (code : ByteArray) : Option Address :=
  if rules.delegationEnabled then getDelegatedCodeAddress code else none

theorem ForkRules.delegatedCodeAddress_enabled {rules : ForkRules}
    (h : rules.delegationEnabled = true) (code : ByteArray) :
    rules.delegatedCodeAddress code = getDelegatedCodeAddress code := by
  simp only [ForkRules.delegatedCodeAddress, h, ↓reduceIte]

theorem ForkRules.delegatedCodeAddress_disabled {rules : ForkRules}
    (h : rules.delegationEnabled = false) (code : ByteArray) :
    rules.delegatedCodeAddress code = none := by
  simp only [ForkRules.delegatedCodeAddress, h, Bool.false_eq_true, ↓reduceIte]

/-- Prague rejects 0xEF-leading deposits: its creation gate is on. -/
@[simp] theorem pragueRules_creation_rejectReservedFirstByte :
    pragueRules.creation.rejectReservedFirstByte = true := rfl

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

/-!
Message helpers for the interpreter core.  The core itself (`Evm.step`,
`enter`, `settle`, `resume`) is in `Jaune.MessageCall`, non-recursive and
fuel-free; `execFueled` (`Jaune.MessageCall.Driver`) is the single fueled driver.
-/

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
  let rec go : Nat → List ξ → List (Nat × ξ)
    | _, [] => []
    | k, x :: xs => (k, x) :: go (k + 1) xs
  go 0 xs

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

def Except.bimap
  {ε : Type u0} {δ : Type u1} {ξ : Type u2} {υ : Type u3}
  (f : ε → δ) (g : ξ → υ) : Except ε ξ → Except δ υ
  | .error e => .error <| f e
  | .ok x => .ok <| g x

def accountHasCodeOrNonce (state : State) (adr : Address) : Bool :=
  state.getNonce adr > 0 || !(state.getCode adr).isEmpty

def accountHasStorage (state : State) (adr : Address) : Bool :=
  !(state.getStorage adr).isEmpty

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

--------------- CANONICALITY THROUGH EXECUTION (P0.4, STEP 4) ---------------

-- Checkpoint 2, frame half: canonicality through delegation access, message
-- initialisation, the value transfer, child messages and delegation setting.
-- Canonicality through `enter`, `settle`, `resume`, the step and the driver is
-- in `Jaune.MessageCall.Canonical`.

/-! ### The zero-meter invariant through execution

The machine layer proves that every legacy instruction preserves
`Devm.StateGasZero`.  This section adds `Evm.StateGasZero` and the precompile
and delegation-access facts; the frame structure (spawns, `enter`, `settle`,
`resume` and the driver) is in `Jaune.MessageCall.StateGasZero`. -/

--------------- ACCOUNT ACCESSORS OVER STATE WRITERS ---------------

-- Account-field writers normalize empty accounts. Balance, nonce, and code
-- projections survive normalization, but storage is cleared on deletion.
-- Readers at another address remain unchanged.

theorem State.setBalance_get_self {st : Jaune.State} {adr : Address} {v : U256} :
    (st.setBalance adr v).get adr = ((st.get adr).withBalance v).clearIfEmpty :=
  State.setAccount_get_self _ _ _

theorem State.setBalance_get_ne {st : Jaune.State} {adr a : Address} {v : U256} (h : adr ≠ a) :
    (st.setBalance adr v).get a = st.get a := State.setAccount_get_ne _ h _

/-- A balance update clears storage exactly when it deletes the account. -/
theorem State.setBalance_get_storage {st : Jaune.State} {b a : Address} {v : U256} :
    ((st.setBalance b v).get a).storage =
      if b = a ∧ ((st.get b).withBalance v).isEmpty then .empty else (st.get a).storage := by
  by_cases h : b = a
  · subst h
    simp only [State.setBalance_get_self, Account.clearIfEmpty_storage, eq_self, true_and]
    rfl
  · simp only [State.setBalance_get_ne h, h, false_and, ite_false]

theorem State.setBalance_get_code {st : Jaune.State} {b a : Address} {v : U256} :
    ((st.setBalance b v).get a).code = (st.get a).code := by
  by_cases h : b = a
  · subst h; rw [State.setBalance_get_self, Account.clearIfEmpty_code]; rfl
  · rw [State.setBalance_get_ne h]

theorem State.of_subtractBalance {st st' : Jaune.State} {ct : Address} {wad : U256}
    (h : st.subtractBalance ct wad = some st') :
    wad ≤ st.balance ct ∧ st' = st.setBalance ct (st.balance ct - wad) := by
  unfold State.subtractBalance at h
  split_ifs at h with h_lt
  cases h
  exact ⟨U256.not_lt.mp h_lt, rfl⟩

theorem State.incrementNonce_get_balance {st : Jaune.State} {adr a : Address} :
    ((st.incrementNonce adr).get a).balance = (st.get a).balance := by
  rw [State.incrementNonce, State.writeAccount_erase_eq_clear]
  by_cases h : adr = a
  · subst h; rw [State.get_set_self, Account.clearIfEmpty_balance]
  · rw [State.get_set_ne _ h]

/-- The general nonce mutator includes wraparound; callers rule out overflow.
Storage is cleared exactly when its resulting account is empty. -/
theorem State.incrementNonce_get_storage {st : Jaune.State} {adr a : Address} :
    ((st.incrementNonce adr).get a).storage =
      if adr = a ∧ ({st.get adr with nonce := (st.get adr).nonce + 1} : Account).isEmpty
      then .empty else (st.get a).storage := by
  rw [State.incrementNonce, State.writeAccount_erase_eq_clear]
  by_cases h : adr = a
  · subst h
    simp only [State.get_set_self, Account.clearIfEmpty_storage, eq_self, true_and]
  · simp only [State.get_set_ne _ h, h, false_and, ite_false]

theorem State.incrementNonce_get_code {st : Jaune.State} {adr a : Address} :
    ((st.incrementNonce adr).get a).code = (st.get a).code := by
  rw [State.incrementNonce, State.writeAccount_erase_eq_clear]
  by_cases h : adr = a
  · subst h; rw [State.get_set_self, Account.clearIfEmpty_code]
  · rw [State.get_set_ne _ h]

theorem State.setBalance_getCode (st : State) (adr a : Address) (val : U256) :
    (st.setBalance adr val).getCode a = st.getCode a :=
  State.setBalance_get_code

theorem State.addBalance_getCode (st : State) (adr a : Address) (val : U256) :
    (st.addBalance adr val).getCode a = st.getCode a :=
  State.setBalance_getCode st adr a (st.balance adr + val)

theorem State.subtractBalance_getCode {st st' : State} {adr a : Address} {val : U256}
    (h : st.subtractBalance adr val = some st') : st'.getCode a = st.getCode a := by
  rw [(State.of_subtractBalance h).2]
  exact State.setBalance_getCode st adr a (st.balance adr - val)

/-- A credit clears storage at `ca` precisely when it deletes that account. -/
theorem getStorage_addBalance (w : Jaune.State) (ca a : Address) (val : U256) :
    (w.addBalance a val).getStorage ca =
      if a = ca ∧ ((w.get a).withBalance (w.balance a + val)).isEmpty
      then .empty else w.getStorage ca :=
  State.setBalance_get_storage

end Jaune
