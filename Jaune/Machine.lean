import Jaune.Types
import Jaune.Fork
import Jaune.EC
import Jaune.BLS
import Jaune.Hash

namespace Jaune

open Jaune _root_.Nat

/-
Design note #1: primitive signatures of the form

  `Devm → Except (EvmError × Devm) (α × Devm)`

are deliberately made isomorphic to `EStateM String Devm α`. Future edits shall
not break this isomorphism. In the future, the codebase may migrate to explicit
use of `EStateM` to hide the passing/updating of `devm : Devm` terms.
-/

/-
Design note #2: All semantics definitions must obey the following guideline:

  - no `mut` bindings
  - no `for` lopps
  - no unnamed large record literals
  - `let ← .ok` seams at inversion points
  - named defs for messages/records that would bloat contexts.

This guideline exists to prevent context bloat & facilitate downstream
verificaiton work. It should be considered a style contract between `jaune`
and the projects which depend on it, including `blanc`.
-/

abbrev AccessList : Type := List (Address × List U256)

abbrev State : Type := Std.TreeMap Address Account compare

-- class Authorization
structure Authorization : Type where
  -- EIP-7702 authorization chain IDs are uint256 values.  A value other than
  -- the execution chain ID (or zero) makes only this tuple inapplicable.
  chainId : U256
  address : Address
  nonce : UInt64
  yParity : Nat
  r : U256
  s : U256

inductive TransactionType : Type
  -- Legacy (including EIP-155)
  | legacy
    (gasPrice : Nat)
    («to» : Option Address)
  -- EIP-2930
  | eip2930
    (chainId : UInt64)
    (gasPrice : Nat)
    («to» : Option Address)
    (accessList : AccessList)
  -- EIP-1559
  | eip1559
    (chainId : UInt64)
    (maxPriorityFeePerGas : Nat)
    (maxFeePerGas : Nat)
    («to» : Option Address)
    (accessList : AccessList)
  -- EIP-4844
  | eip4844
    (chainId : UInt64)
    (maxPriorityFeePerGas : Nat)
    (maxFeePerGas : Nat)
    («to» : Address)
    (accessList : AccessList)
    (maxFeePerBlobGas : Nat)
    (blobVersionedHashes : List U256)
  | eip7702
    (chainId : UInt64)
    (maxPriorityFeePerGas : Nat)
    (maxFeePerGas : Nat)
    («to» : Address)
    (accessList : AccessList)
    (authorizationList : List Authorization)

structure Withdrawal : Type where
  (index : UInt64)
  (validatorIndex : UInt64)
  (address : Address)
  (amount : U256)

structure Header : Type where
  parentHash : U256
  ommersHash : U256
  coinbase : Address
  stateRoot : U256
  transactionsRoot : U256
  receiptsRoot : U256
  logsBloom : Bytes
  difficulty : Nat
  number : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : Nat
  extraData : Bytes
  prevRandao : U256
  nonce : UInt64
  /-- EIP-1559 (London). Like every field below it, optional in the sense
  `requestsHash` is: the field exists on the wire only at forks that define it,
  `ForkRules.header` says which those are, and `none` is "this fork has no
  such field", never "the field is zero". -/
  baseFeePerGas : Option Nat
  /-- EIP-4895 (Shanghai). -/
  withdrawalsRoot : Option U256
  /-- EIP-4844 (Cancun); present exactly when `excessBlobGas` is. -/
  blobGasUsed : Option Nat
  /-- EIP-4844 (Cancun). -/
  excessBlobGas : Option Nat
  /-- EIP-4788 (Cancun). -/
  parentBeaconBlockRoot : Option U256
  requestsHash : Option U256
  /-- EIP-7928: the commitment to the block-level access list.

  Optional in the same sense `requestsHash` is: the field exists on the wire
  only at forks that define it, and `ForkRules.header.blockAccessListHash` is
  what says which those are. `none` is "this fork has no such field", never
  "the field is zero". -/
  blockAccessListHash : Option U256
  /-- EIP-7843: the consensus slot number this block was produced for, which
  `SLOTNUM` pushes. Optional on the same terms. -/
  slotNumber : Option UInt64

/-- The canonical RLP encoding of a header.

The fork-dependent fields are emitted in nested order -- `baseFeePerGas`, then
`withdrawalsRoot`, then the Cancun triple `blobGasUsed`, `excessBlobGas`,
`parentBeaconBlockRoot`, then `requestsHash`, `blockAccessListHash` and
`slotNumber` -- which is the order upstream's header dataclasses declare them
and the order the fixtures carry them. Each field is emitted only when every
field before it is, and the Cancun triple only as a whole. Nesting rather than
concatenating independent options is deliberate: it makes the encodable shapes
exactly **15, 16, 17, 20, 21, 22 and 23** fields (Byzantium through Berlin,
London through Paris, Shanghai, Cancun, Prague through BPO2, a requests hash
with a block-access-list hash, Amsterdam), so that no 18- or 19-field encoding
can be produced at all. `BLT.toExHeader` accepts the six fork shapes and
rejects 22, and `validateHeader` is what rejects a record whose field presence
disagrees with the rules it is being validated under.

A header with every field through `parentBeaconBlockRoot` present encodes
exactly as it did when those fields were mandatory: the nested matches on
present fields reduce to the list the old code wrote literally. -/
def Header.toRlpItem (header : Header) : Rlp.Item :=
  Rlp.Item.list <| [
    Rlp.Item.bytes header.parentHash.toBytes,
    Rlp.Item.bytes header.ommersHash.toBytes,
    Rlp.Item.bytes header.coinbase.toBytes,
    Rlp.Item.bytes header.stateRoot.toBytes,
    Rlp.Item.bytes header.transactionsRoot.toBytes,
    Rlp.Item.bytes header.receiptsRoot.toBytes,
    Rlp.Item.bytes header.logsBloom,
    Rlp.Item.bytes header.difficulty.toBytes,
    Rlp.Item.bytes header.number.toBytes,
    Rlp.Item.bytes header.gasLimit.toBytes,
    Rlp.Item.bytes header.gasUsed.toBytes,
    Rlp.Item.bytes header.timestamp.toBytes,
    Rlp.Item.bytes header.extraData,
    Rlp.Item.bytes header.prevRandao.toBytes,
    Rlp.Item.bytes header.nonce.toBytes
  ] ++
    match header.baseFeePerGas with
    | none => []
    | some baseFee =>
      Rlp.Item.bytes baseFee.toBytes ::
      match header.withdrawalsRoot with
      | none => []
      | some withdrawalsRoot =>
        Rlp.Item.bytes withdrawalsRoot.toBytes ::
        match header.blobGasUsed, header.excessBlobGas,
            header.parentBeaconBlockRoot with
        | some blobGasUsed, some excessBlobGas, some parentBeaconBlockRoot =>
          Rlp.Item.bytes blobGasUsed.toBytes ::
          Rlp.Item.bytes excessBlobGas.toBytes ::
          Rlp.Item.bytes parentBeaconBlockRoot.toBytes ::
          match header.requestsHash with
          | none => []
          | some rh =>
            Rlp.Item.bytes rh.toBytes ::
              match header.blockAccessListHash with
              | none => []
              | some balHash =>
                Rlp.Item.bytes balHash.toBytes ::
                  match header.slotNumber with
                  | none => []
                  -- A canonical scalar, like `number` and `gasLimit` above
                  -- and unlike `nonce`: upstream's `slot_number` is a `U64`
                  -- quantity, so it is encoded minimally and `toRlpB64`
                  -- decodes it that way.
                  | some slot => [Rlp.Item.bytes slot.toNat.toBytes]
        | _, _, _ => []

/-- A header's identity: the keccak of its canonical RLP encoding.

This is the value a child block's `parentHash` names, the key a snapshot is
stored under, and the value `BLOCKHASH` returns. It is written out inline at
several older call sites; those keep their spelling, and this is the name the
checked chain vocabulary states its results about. -/
def Header.hash (header : Header) : U256 :=
  (Header.toRlpItem header).toBytes.keccak

structure Transaction : Type where
  (nonce : UInt64)
  (gasLimit : Nat)
    (value : Nat)
  (data : Bytes)
  (v : Nat)
  (r : Bytes)
  (s : Bytes)
  (type : TransactionType)

structure Block : Type where
  header : Header
  transactions : List (Bytes ⊕ Transaction)
  ommers : List Header
  withdrawals : List Withdrawal

structure BlockChain : Type where
  blocks : List Block
  state : State
  chainId : UInt64

def TransactionType.to? : TransactionType → Option Address
  | .legacy _ receiver => receiver
  | .eip2930 _ _ receiver _ => receiver
  | .eip1559 _ _ _ receiver _ => receiver
  | .eip4844 _ _ _ receiver _ _ _ => some receiver
  | .eip7702 _ _ _ receiver _ _ => some receiver

def TransactionType.accessList : TransactionType → AccessList
  | .legacy _ _ => []
  | .eip2930 _ _ _ al => al
  | .eip1559 _ _ _ _ al => al
  | .eip4844 _ _ _ _ al _ _ => al
  | .eip7702 _ _ _ _ al _ => al

/-- EELS's transaction-type number: legacy is 0, each typed envelope its
type byte. Unit U5 (S5) admission compares it against `rules.txr.maxType`. -/
def TransactionType.index : TransactionType → Nat
  | .legacy _ _ => 0
  | .eip2930 _ _ _ _ => 1
  | .eip1559 _ _ _ _ _ => 2
  | .eip4844 _ _ _ _ _ _ _ => 3
  | .eip7702 _ _ _ _ _ _ => 4

def Transaction.accessList (tx : Transaction) : AccessList := tx.type.accessList

def Transaction.authorizationList (tx : Transaction) : List Authorization :=
  match tx.type with
  | .eip7702 _ _ _ _ _ auths => auths
  | _ => []

def Bytes.sig (bs : Bytes) : Bytes := List.dropWhile (· = 0) bs

def AccessList.toRlpItem (al : AccessList) : Rlp.Item :=
  let aux : Address × List U256 → Rlp.Item
  | ⟨adr, words⟩ =>
    .list [.bytes adr.toBytes, .list (words.map (.bytes ∘ U256.toBytes))]
  .list (al.map aux)

def Authorization.toRlpItem (auth : Authorization) : Rlp.Item :=
  .list [
    .bytes auth.chainId.toBytes.sig,
    .bytes <| auth.address.toBytes,
    .bytes auth.nonce.toNat.toBytes,
    .bytes auth.yParity.toBytes,
    -- `r` and `s` are RLP scalars, so they must re-encode minimally: a fixed
    -- 32-byte encoding diverges from the canonical bytes whenever a signature
    -- scalar has a leading zero byte, corrupting both the type-4 signing hash
    -- and the transactions trie.
    .bytes auth.r.toBytes.sig,
    .bytes auth.s.toBytes.sig,
  ]

def Transaction.toRlpItem (tx : Transaction) : Rlp.Item :=
  match tx.type with
  | .legacy gasPrice receiver =>
    .list [
      .bytes tx.nonce.toNat.toBytes,
      .bytes gasPrice.toBytes,
      .bytes tx.gasLimit.toBytes,
      .bytes <| receiver.rec [] Address.toBytes,
      .bytes tx.value.toBytes,
      .bytes tx.data,
      .bytes tx.v.toBytes,
      .bytes (trimZero tx.r),
      .bytes (trimZero tx.s),
    ]
  | .eip2930 chainId gasPrice receiver accessList =>
    .list [
      .bytes chainId.toBytes.sig,
      .bytes tx.nonce.toNat.toBytes,
      .bytes gasPrice.toBytes,
      .bytes tx.gasLimit.toBytes,
      .bytes <| receiver.rec [] Address.toBytes,
      .bytes tx.value.toBytes,
      .bytes tx.data,
      accessList.toRlpItem,
      .bytes tx.v.toBytes,
      .bytes (trimZero tx.r),
      .bytes (trimZero tx.s)
    ]
  | .eip1559 chainId maxPriorityFee maxFee receiver accessList =>
    .list [
      .bytes chainId.toBytes.sig,
      .bytes tx.nonce.toNat.toBytes,
      .bytes maxPriorityFee.toBytes,
      .bytes maxFee.toBytes,
      .bytes tx.gasLimit.toBytes,
      .bytes <| receiver.rec [] Address.toBytes,
      .bytes tx.value.toBytes,
      .bytes tx.data,
      accessList.toRlpItem,
      .bytes tx.v.toBytes,
      .bytes (trimZero tx.r),
      .bytes (trimZero tx.s)
    ]
  | .eip4844 chainId maxPriorityFee maxFee receiver accessList maxBlobFee blobHashes =>
    .list [
      .bytes chainId.toBytes.sig,
      .bytes tx.nonce.toNat.toBytes,
      .bytes maxPriorityFee.toBytes,
      .bytes maxFee.toBytes,
      .bytes tx.gasLimit.toBytes,
      .bytes receiver.toBytes,
      .bytes tx.value.toBytes,
      .bytes tx.data,
      accessList.toRlpItem,
      .bytes maxBlobFee.toBytes,
      .list <| blobHashes.map <| .bytes ∘ U256.toBytes,
      .bytes tx.v.toBytes,
      .bytes (trimZero tx.r),
      .bytes (trimZero tx.s)
    ]
  | .eip7702 chainId maxPriorityFee maxFee receiver accessList auths =>
    .list [
      .bytes chainId.toBytes.sig,
      .bytes tx.nonce.toNat.toBytes,
      .bytes maxPriorityFee.toBytes,
      .bytes maxFee.toBytes,
      .bytes tx.gasLimit.toBytes,
      .bytes receiver.toBytes,
      .bytes tx.value.toBytes,
      .bytes tx.data,
      accessList.toRlpItem,
      .list <| auths.map <| Authorization.toRlpItem,
      .bytes tx.v.toBytes,
      .bytes (trimZero tx.r),
      .bytes (trimZero tx.s)
    ]

def BytesOrTransactionToRlpItem : Bytes ⊕ Transaction → Rlp.Item
  | .inl bs => Rlp.Item.bytes bs
  | .inr tx => tx.toRlpItem

def Withdrawal.toRlpItem (wd : Withdrawal) : Rlp.Item :=
  Rlp.Item.list [
    Rlp.Item.bytes wd.index.toBytes.sig,
    Rlp.Item.bytes wd.validatorIndex.toBytes.sig,
    Rlp.Item.bytes wd.address.toBytes,
    Rlp.Item.bytes wd.amount.toBytes.sig
  ]

def Block.toRlpItem (block : Block) : Rlp.Item :=
  let txBLTs : List Rlp.Item := block.transactions.map BytesOrTransactionToRlpItem
  .list [
    Header.toRlpItem block.header,
    .list txBLTs,
    .list <| block.ommers.map Header.toRlpItem,
    .list <| block.withdrawals.map Withdrawal.toRlpItem
  ]

def TransactionType.gasPrice (baseFee : Nat) : TransactionType → Nat
  | .legacy gp _ => gp
  | .eip2930 _ gp _ _ => gp
  | .eip1559 _ mpf mf _ _ => min mf (baseFee + mpf)
  | .eip4844 _ mpf mf _ _ _ _ => min mf (baseFee + mpf)
  | .eip7702 _ mpf mf _ _ _ => min mf (baseFee + mpf)

def TransactionType.blobVersionedHashes : TransactionType → List U256
  | .legacy _ _ => []
  | .eip2930 _ _ _ _ => []
  | .eip1559 _ _ _ _ _ => []
  | .eip4844 _ _ _ _ _ _ bhs => bhs
  | .eip7702 _ _ _ _ _ _ => []

def Transaction.blobVersionedHashes (tx : Transaction) : List U256 := tx.type.blobVersionedHashes

-- nibbles-to-bytes maps
abbrev TrieBuilder := Std.TreeMap (List UInt8) (List UInt8) (@List.compare _ ⟨UInt8.compareLows⟩)

def hexPrefixAux : Bytes → (Option UInt8 × Bytes)
  | [] => ⟨none, []⟩
  | n :: ns =>
    match hexPrefixAux ns with
    | ⟨none, bs⟩ => ⟨some n, bs⟩
    | ⟨some m, bs⟩ => ⟨none, ((n <<< 4) ||| m.lows) :: bs⟩

def hexPrefix (ns : Bytes) (t : Bool) : Bytes :=
  match hexPrefixAux ns with
  | ⟨none, bs⟩ => (cond t (0x20) 0) :: bs
  | ⟨some n, bs⟩ => ((cond t 0x30 0x10) ||| n.lows) :: bs

def Bytes.commonPrefix : Bytes → Bytes → Bytes
  | [], _ => []
  | _, [] => []
  | n :: ns, n' :: ns' =>
    if n = n' then n :: Bytes.commonPrefix ns ns'
    else []

def commonPrefix (n : UInt8) (ns : Bytes) : List Bytes → Option Bytes
  | [] => some (n :: ns)
  | ns' :: nss =>
    match Bytes.commonPrefix (n :: ns) ns' with
    | [] => none
    | (n' :: ns'') => commonPrefix n' ns'' nss

def TrieBuilder.empty : TrieBuilder := Std.TreeMap.empty

def sansPrefix : Bytes → Bytes → Option Bytes
  | [], ns => some ns
  | _, [] => none
  | n :: ns, n' :: ns' =>
    if n = n' then sansPrefix ns ns' else none

def insertSansPrefix (pfx : Bytes) (m : TrieBuilder) (ns : Bytes) (bs : Bytes) : Option TrieBuilder := do
  (m.insert · bs) <$> sansPrefix pfx ns

def TrieBuilder.factor (m : TrieBuilder) : Option (Bytes × TrieBuilder) := do
  let ((n :: ns) :: nss) ← some (m.toList.map Prod.fst) | none
  let pfx ← commonPrefix n ns nss
  let m' ← Std.TreeMap.foldlM (insertSansPrefix pfx) TrieBuilder.empty m
  some ⟨pfx, m'⟩

structure TrieBranches : Type where
  (child0 : TrieBuilder) (child1 : TrieBuilder) (child2 : TrieBuilder) (child3 : TrieBuilder)
  (child4 : TrieBuilder) (child5 : TrieBuilder) (child6 : TrieBuilder) (child7 : TrieBuilder)
  (child8 : TrieBuilder) (child9 : TrieBuilder) (childA : TrieBuilder) (childB : TrieBuilder)
  (childC : TrieBuilder) (childD : TrieBuilder) (childE : TrieBuilder) (childF : TrieBuilder)

def TrieBranches.empty : TrieBranches :=
  ⟨ .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty ⟩

def TrieBranches.update (js : TrieBranches) (f : TrieBuilder → TrieBuilder) (k : UInt8) : TrieBranches :=
  match k.toBools with
  | ⟨_, _, _, _, 0, 0, 0, 0⟩ => { js with child0 := f js.child0}
  | ⟨_, _, _, _, 0, 0, 0, 1⟩ => { js with child1 := f js.child1}
  | ⟨_, _, _, _, 0, 0, 1, 0⟩ => { js with child2 := f js.child2}
  | ⟨_, _, _, _, 0, 0, 1, 1⟩ => { js with child3 := f js.child3}
  | ⟨_, _, _, _, 0, 1, 0, 0⟩ => { js with child4 := f js.child4}
  | ⟨_, _, _, _, 0, 1, 0, 1⟩ => { js with child5 := f js.child5}
  | ⟨_, _, _, _, 0, 1, 1, 0⟩ => { js with child6 := f js.child6}
  | ⟨_, _, _, _, 0, 1, 1, 1⟩ => { js with child7 := f js.child7}
  | ⟨_, _, _, _, 1, 0, 0, 0⟩ => { js with child8 := f js.child8}
  | ⟨_, _, _, _, 1, 0, 0, 1⟩ => { js with child9 := f js.child9}
  | ⟨_, _, _, _, 1, 0, 1, 0⟩ => { js with childA := f js.childA}
  | ⟨_, _, _, _, 1, 0, 1, 1⟩ => { js with childB := f js.childB}
  | ⟨_, _, _, _, 1, 1, 0, 0⟩ => { js with childC := f js.childC}
  | ⟨_, _, _, _, 1, 1, 0, 1⟩ => { js with childD := f js.childD}
  | ⟨_, _, _, _, 1, 1, 1, 0⟩ => { js with childE := f js.childE}
  | ⟨_, _, _, _, 1, 1, 1, 1⟩ => { js with childF := f js.childF}

def TrieBranches.insert (js : TrieBranches) : Bytes → Bytes → TrieBranches
  | [], _ => js
  | n :: ns, bs => js.update (Std.TreeMap.insert · ns bs) n

def Std.TreeMap.isSingleton {K V : Type} (cmp : K → K → Ordering)
    (m : Std.TreeMap K V cmp) : Bool :=
  m.size = 1

mutual

  def nodeComp : Nat → TrieBuilder → Rlp.Item
    | 0, _ => .bytes []
    | k + 1, j =>
      if j.isEmpty
      then .bytes []
      else let r := structComp k j
           if r.toBytes.length < 32
           then r
           else .bytes <| r.toBytes.keccak.toBytes

  def structComp : Nat → TrieBuilder → Rlp.Item
    | 0, _ => .bytes []
    | k + 1, j =>
      if j.isEmpty
            then .bytes []       else if j.isSingleton
           then match j.toList with
                | [(k, v)] => .list [.bytes (hexPrefix k 1), .bytes v]
                | _ => .bytes []            else match j.factor with
                | none =>
                  let js := Std.TreeMap.foldl TrieBranches.insert TrieBranches.empty j
                  .list [ nodeComp k js.child0, nodeComp k js.child1, nodeComp k js.child2,
                          nodeComp k js.child3, nodeComp k js.child4, nodeComp k js.child5,
                          nodeComp k js.child6, nodeComp k js.child7, nodeComp k js.child8,
                          nodeComp k js.child9, nodeComp k js.childA, nodeComp k js.childB,
                          nodeComp k js.childC, nodeComp k js.childD, nodeComp k js.childE,
                          nodeComp k js.childF, .bytes (j.getD [] []) ]
                | some (pfx, j') => .list [.bytes (hexPrefix pfx 0), nodeComp k j']

end

def TrieBuilder.maxKeyLength (j : TrieBuilder) : Nat :=
  (j.toList.map (List.length ∘ Prod.fst)).maxD 0

def collapse (j : TrieBuilder) : Rlp.Item := structComp (2 * (j.maxKeyLength + 1)) j

def trie (j : TrieBuilder) : U256 :=
  Bytes.keccak <| (collapse j).toBytes

def U256.toRlpItem (w : U256) : Rlp.Item := .bytes w.toBytes

def Storage.toTrieBuilder (s : Storage) : TrieBuilder :=
  let f : TrieBuilder → U256 → U256 → TrieBuilder :=
    λ j k v =>
      j.insert
        k.keccak.toNibbles
        ((Rlp.Item.toBytes <| .bytes <| Bytes.sig <| v.toBytes))
  Std.TreeMap.foldl f TrieBuilder.empty s

def U256.zerocount (x : U256) : Nat → Nat
  | 0 => 0
  | k + 1 => if x = 0 then k + 1 else U256.zerocount (x >>> 8) k

def U256.bytecount (x : U256) : Nat := 32 - (U256.zerocount x 32)

/-- Leading zero bits of one 64-bit limb; 64 for zero. -/
def UInt64.leadingZeros (x : UInt64) : Nat :=
  if x = 0 then 64 else 63 - Nat.log2 x.toNat

/-- Leading zero bits of a 256-bit word; 256 for zero.

This is EIP-7939's `256 - x.bit_length()` stated directly, and it is computed
limb by limb so that a word is never widened to a bignum to be measured. -/
def U256.leadingZeros (x : U256) : Nat :=
  if x.1.1 ≠ 0 then UInt64.leadingZeros x.1.1
  else if x.1.2 ≠ 0 then 64 + UInt64.leadingZeros x.1.2
  else if x.2.1 ≠ 0 then 128 + UInt64.leadingZeros x.2.1
  else 192 + UInt64.leadingZeros x.2.2

def accountToKeyValue (pr : Address × Account) : Bytes × Bytes :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨
    ad.toBytes.keccak.toNibbles,
    let val' :=
      Rlp.Item.toBytes <| .list [
        .bytes (ac.nonce.toBytes.sig),
        .bytes (ac.balance.toBytes.sig),
        U256.toRlpItem (trie ac.storage.toTrieBuilder),
        U256.toRlpItem <| (Bytes.keccak ac.code.toList)
      ]
    val'
  ⟩

-- values --

def Gas.high : Nat := 10
def Gas.jumpdest : Nat := 1
def Gas.txCreate : Nat := 32000
def Gas.initcodeWordCost : Nat := 2
def Gas.base : Nat := 2
def Gas.copy : Nat := 3
def Gas.returnDataCopy : Nat := 3
def Gas.memory : Nat := 3
def Gas.keccak256 : Nat := 30
def Gas.keccak256Word : Nat := 6
def Gas.veryLow : Nat := 3
def Gas.low : Nat := 5
def Gas.mid : Nat := 8
def Gas.exp : Nat := 10
def Gas.expByte : Nat := 50
def Gas.coldSloadCost : Nat := 2100
def Gas.sstoreSetGas : Nat := 20000
def Gas.storageClearRefund : Nat := 4800
def Gas.blockhash : Nat := 20
def Gas.codeDeposit : Nat := 200
def Gas.create : Nat := 32000
def Gas.hashOpcodeGas : Nat := 3
def Gas.perBlob : Nat := 2 ^ 17
/-- SSTORE's charge for writing a slot whose original value is nonzero: EIP-2200
`SSTORE_RESET_GAS` (5000), the name geth (`SstoreResetGasEIP2200`) and revm
(`SSTORE_RESET`) also use. From Berlin Jaune charges `Gas.sstoreResetGas - Gas.coldSloadCost`
(2900), EIP-2929's redefined `SSTORE_RESET_GAS` (`5000 - COLD_SLOAD_COST`).
Other spellings: Yellow Paper `G_sreset` (5000 before Berlin, 2900 from Berlin);
execution-specs `GAS_STORAGE_UPDATE` (older layout) and `GasCosts.COLD_STORAGE_WRITE`
(at the conformance pin `e27f097e`). -/
def Gas.sstoreResetGas : Nat := 5000
def Gas.ecrecover : Nat := 3000
def Gas.p256Verify : Nat := 6900
-- `maxCodeSize` and `maxInitCodeSize` are fork rules, not global constants:
-- see `ForkRules.code` in `Jaune/Fork.lean`.
def Gas.newAccount : Nat := 25000
def Gas.selfdestructNewAccount : Nat := 25000
def Gas.callValue : Nat := 9000
def Gas.callStipend : Nat := 2300
def Gas.warmStorageReadCost : Nat := 100
def Gas.coldAccountAccessCost : Nat := 2600
def Gas.selfdestruct : Nat := 5000
def Gas.log : Nat := 375
def Gas.logData : Nat := 8
def Gas.logTopic : Nat := 375
def depositContractAddress : Address :=
  0x00000000219ab540356cbb839cbe05303d7705fa
def depositEventSignatureHash : U256 :=
  0x649bbc62d0e31342afea4e5cd82d4049e7e1ee912fc0889aa790803be39038c5
def depositEventLength : Nat := 576
def pubkeyOffset : Nat := 160
def amountOffset : Nat := 320
def signatureOffset : Nat := 384
def indexOffset : Nat := 512
def withdrawalCredentialsOffset := 256
def pubkeySize : Nat := 48
def amountSize : Nat := 8
def indexSize : Nat := 8
def signatureSize : Nat := 96
def withdrawalCredentialsSize : Nat := 32
def Gas.accessListAddressCost : Nat := 2400
def Gas.accessListStorageKeyCost : Nat := 1900
def Gas.totalCostFloorPerToken : Nat := 10
def Gas.standardTokenCost : Nat := 4
def depositRequestType : Bytes := [0]
def withdrawalRequestType : Bytes := [1]
def consolidationRequestType : Bytes := [2]
def withdrawalRequestPredeployAddress : Address := 0x00000961Ef480Eb55e80D19ad83579A64c007002
def consolidationRequestPredeployAddress : Address := 0x0000BBdDc7CE488642fb579F8B00f3a590007251
def historyStorageAddress : Address := 0x0000F90827F1C53a10cb7A02335B175320002935
def emptyOmmerHash : U256 := (Rlp.Item.list []).toBytes.keccak
def setCodeTransactionMagic : Bytes := [0x05]
def beaconRootsAddress : Address := 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
def systemAddress : Address := 0xfffffffffffffffffffffffffffffffffffffffe
def systemTransactionGas : Nat := 30000000
def versionedHashVersionKzg : UInt8 := 0x01
def eoaDelegationMarker : Bytes := [0xEF, 0x01, 0x00]
def Gas.gfround : Nat := 1
def eoaDelegatedCodeLength : Nat := 23
-- The blob target, ceiling, and base-fee update fraction are fork rules, not
-- global constants: see `ForkRules.blob` in `Jaune/Fork.lean`.
def elasticityMultiplier : Nat := 2
def gasLimitAdjustmentFactor : Nat := 1024
def gasLimitMinimum : Nat := 5000
def baseFeeMaxChangeDenominator := 8
-- EIP-1559's `INITIAL_BASE_FEE` (EELS `london/fork.py`): the base fee of the
-- first block whose header carries one, which reads no parent base fee.
def initialBaseFee : Nat := 1000000000
-- The three interpreter divisors that are global constants rather than rule
-- data. Their positivity is a closed fact, not a hypothesis anything carries:
-- `ForkRules.Valid` deliberately says nothing about them, because no caller can
-- supply a different value. `elasticityMultiplier` divides at
-- `Execution.calculateBaseFeePerGas`, `gasLimitAdjustmentFactor` at
-- `Execution.checkGasLimit`, and `baseFeeMaxChangeDenominator` twice more in
-- `calculateBaseFeePerGas`. `gasPerBlob` multiplies rather than divides, but
-- its positivity is what keeps the blob-fee product nonzero.
theorem elasticityMultiplier_pos : 0 < elasticityMultiplier := by decide
theorem gasLimitAdjustmentFactor_pos : 0 < gasLimitAdjustmentFactor := by decide
theorem baseFeeMaxChangeDenominator_pos : 0 < baseFeeMaxChangeDenominator := by
  decide
theorem Gas.perBlob_pos : 0 < Gas.perBlob := by decide

def Gas.perEmptyAccountCost := 25000
def Gas.perAuthBaseCost := 12500
def Gas.transaction : Nat := 21000

/-! ### The rule-data bridge

`ForkRules.gas`, `ForkRules.header` and `ForkRules.requests` (`Jaune/Fork.lean`)
carry the numbers a supported fork moves inside a formula both forks share. The
globals above stay defined and keep their meaning -- they are *Prague's values*,
and the interpreter now reads them through `rules.gas` so that a later fork can
supply different ones.

These lemmas are the proof that the two spellings are the same number, and they
are `rfl` because the record literal in `Jaune/Fork.lean` is definitionally the
constant here. Two things rest on that:

* **Behaviour preservation.** Every Prague-stated fact about the old globals
  survives, because nothing was renamed and nothing moved -- only the path by
  which the interpreter reaches the value.
* **Downstream proofs keep reducing.** They are `@[simp]`, so a client stating a
  goal in terms of `pragueRules.gas.callValue` (or reaching one through the
  interpreter) rewrites to `gasCallValue` and meets the arithmetic it already
  knows. Blanc is stated over Prague throughout, so this is what keeps its
  1,929 `gasLeft` mentions reducing across the pin bump.

They are also the only place the two copies of each literal can drift apart:
`Jaune/Fork.lean` is upstream of this module and cannot name these constants,
so the record spells them out, and `rfl` here is what makes that duplication
safe rather than a second source of truth. -/

@[simp] theorem pragueRules_gas_coldAccountAccess :
    pragueRules.gas.coldAccountAccess = Gas.coldAccountAccessCost := rfl
@[simp] theorem pragueRules_gas_callValue :
    pragueRules.gas.callValue = Gas.callValue := rfl
@[simp] theorem pragueRules_gas_createAccess :
    pragueRules.gas.createAccess = Gas.create := rfl
@[simp] theorem pragueRules_gas_storageClearRefund :
    pragueRules.gas.storageClearRefund = Gas.storageClearRefund := rfl
@[simp] theorem pragueRules_gas_txBase :
    pragueRules.gas.txBase = Gas.transaction := rfl
@[simp] theorem pragueRules_gas_txAccessListAddress :
    pragueRules.gas.txAccessListAddress = Gas.accessListAddressCost := rfl
@[simp] theorem pragueRules_gas_txAccessListStorageKey :
    pragueRules.gas.txAccessListStorageKey = Gas.accessListStorageKeyCost := rfl
@[simp] theorem pragueRules_gas_floorTokenCost :
    pragueRules.gas.floorTokenCost = Gas.totalCostFloorPerToken := rfl
@[simp] theorem pragueRules_gas_perAuthorizationIntrinsic :
    pragueRules.gas.perAuthorizationIntrinsic = Gas.perEmptyAccountCost := rfl
/-- The tenth field is additive with identity `0`, so the Prague formula is
literally unchanged rather than merely equal to what it was. -/
@[simp] theorem pragueRules_gas_codeReadSurcharge :
    pragueRules.gas.codeReadSurcharge = 0 := rfl

/-- `createAccess` is one number at Prague for both of its two readers: the
`CREATE`/`CREATE2` opcode base and the creation transaction's recipient cost.
Stated so that the single field is justified rather than assumed -- EIP-8037
moves both together, and if upstream ever separated them this would fail. -/
@[simp] theorem Gas.txCreate_eq_create : Gas.txCreate = Gas.create := rfl

/-- The request contracts the rule data names are the ones this module has
always called, in the same order. -/
@[simp] theorem pragueRules_requests :
    pragueRules.requests =
      [(1, withdrawalRequestPredeployAddress),
       (2, consolidationRequestPredeployAddress)] := rfl

/-- Prague carries neither Amsterdam header field (and every pre-Prague one). -/
@[simp] theorem pragueRules_header :
    pragueRules.header = { blockAccessListHash := false, slotNumber := false, baseFee := true, withdrawalsRoot := true, blobGas := true, parentBeaconBlockRoot := true, requestsHash := true } :=
  rfl

/-- Prague meters in one dimension.

This is the bridge every `stateGas = none` branch reduces through. The
interpreter's Amsterdam branches are `match`es on `rules.stateGas`, so a
Prague-stated goal that reaches one rewrites to `none` here and then to the
existing single-dimension code path by `match` reduction -- which is what makes
"the `none` path is textually today's path" a fact a proof can use rather than
a claim about the source. -/
@[simp] theorem pragueRules_stateGas : pragueRules.stateGas = none := rfl

/-- Prague prices access by EIP-2929. The bridge every access arm's `.eip2929`
branch reduces through, as `pragueRules_stateGas` is for the metering
dimension: the arms are `match`es on `rules.access`, and a Prague-stated goal
rewrites to `.eip2929` here and then to the warm/cold code by `match`
reduction. -/
@[simp] theorem pragueRules_access : pragueRules.access = .eip2929 := rfl

/-- The two literals `GasSchedule.Valid` spells out are the globals it means.

`Jaune/Fork.lean` is upstream of this module and cannot name `gasWarmAccess` or
`gCallStipend`, so the predicate writes `100` and `2300`. This is the `rfl`
proof that those are not third copies of the numbers but the same two, which is
what lets a Sufficiency obligation stated in terms of the globals be discharged
from a `Valid` hypothesis. -/
theorem gasSchedule_valid_iff (g : GasSchedule) :
    g.Valid ↔ Gas.warmStorageReadCost ≤ g.coldAccountAccess ∧ 0 < g.createAccess
      ∧ Gas.callStipend ≤ g.callValue := Iff.rfl

theorem GasSchedule.Valid.warmAccess_le {g : GasSchedule} (h : g.Valid) :
    Gas.warmStorageReadCost ≤ g.coldAccountAccess := h.1

theorem GasSchedule.Valid.createAccess_pos {g : GasSchedule} (h : g.Valid) :
    0 < g.createAccess := h.2.1

theorem GasSchedule.Valid.stipend_le_callValue {g : GasSchedule} (h : g.Valid) :
    Gas.callStipend ≤ g.callValue := h.2.2

-- The whole supported chain shares Prague's schedule, so the bridge above
-- serves every fork this build runs, not only Prague. Stated by `rfl` on the
-- records rather than field by field.
theorem osakaRules_gas : osakaRules.gas = pragueRules.gas := rfl
theorem bpo1Rules_gas : bpo1Rules.gas = pragueRules.gas := rfl
theorem bpo2Rules_gas : bpo2Rules.gas = pragueRules.gas := rfl
def g1MsmLengthPerPair : Nat := 160
def g2MsmLengthPerPair : Nat := 288
def g1MaxDiscount : Nat := 519
def g2MaxDiscount : Nat := 524

def g1KDiscount : List Nat :=
  [
    1000, 949, 848, 797, 764, 750, 738, 728,
    719, 712, 705, 698, 692, 687, 682, 677,
    673, 669, 665, 661, 658, 654, 651, 648,
    645, 642, 640, 637, 635, 632, 630, 627,
    625, 623, 621, 619, 617, 615, 613, 611,
    609, 608, 606, 604, 603, 601, 599, 598,
    596, 595, 593, 592, 591, 589, 588, 586,
    585, 584, 582, 581, 580, 579, 577, 576,
    575, 574, 573, 572, 570, 569, 568, 567,
    566, 565, 564, 563, 562, 561, 560, 559,
    558, 557, 556, 555, 554, 553, 552, 551,
    550, 549, 548, 547, 547, 546, 545, 544,
    543, 542, 541, 540, 540, 539, 538, 537,
    536, 536, 535, 534, 533, 532, 532, 531,
    530, 529, 528, 528, 527, 526, 525, 525,
    524, 523, 522, 522, 521, 520, 520, 519,
  ]

def g2KDiscount : List Nat :=
  [
    1000, 1000, 923, 884, 855, 832, 812, 796,
    782, 770, 759, 749, 740, 732, 724, 717,
    711, 704, 699, 693, 688, 683, 679, 674,
    670, 666, 663, 659, 655, 652, 649, 646,
    643, 640, 637, 634, 632, 629, 627, 624,
    622, 620, 618, 615, 613, 611, 609, 607,
    606, 604, 602, 600, 598, 597, 595, 593,
    592, 590, 589, 587, 586, 584, 583, 582,
    580, 579, 578, 576, 575, 574, 573, 571,
    570, 569, 568, 567, 566, 565, 563, 562,
    561, 560, 559, 558, 557, 556, 555, 554,
    553, 552, 552, 551, 550, 549, 548, 547,
    546, 545, 545, 544, 543, 542, 541, 541,
    540, 539, 538, 537, 537, 536, 535, 535,
    534, 533, 532, 532, 531, 530, 530, 529,
    528, 528, 527, 526, 526, 525, 524, 524
  ]

def initcodeCost (len : Nat) : Nat :=
  Gas.initcodeWordCost * (ceilDiv len 32)

instance : Hashable Address := ⟨fun x => x.2.2⟩
-- The storage-slot hash must depend on the key, not only the address: mix the
-- address hash with all four 64-bit limbs of the B256 key (finding 3.9). A
-- key-insensitive hash sent every same-address slot into one bucket.
instance : Hashable (Address × U256) :=
  ⟨λ x =>
    let k := x.2
    mixHash (hash x.1) (mixHash k.1.1 (mixHash k.1.2 (mixHash k.2.1 k.2.2)))⟩

abbrev AdrSet : Type := @Std.HashSet Address _ _
abbrev KeySet : Type := @Std.HashSet (Address × U256) _ _

abbrev TransientStorage : Type := Std.TreeMap Address Storage compare

def calculateMemoryGasCost (memSize : Nat) : Nat :=
  let memWordSize := ceilDiv memSize 32
  let linearCost := Gas.memory * memWordSize
  let quadraticCost := (memWordSize ^ 2) / 512
  linearCost + quadraticCost

structure Mem : Type where
  data : Array UInt8
  size : Nat

def Mem.empty : Mem := ⟨.empty, 0⟩

structure Log : Type where
  (address : Address)
  (topics : List U256)
  (data : Bytes)

structure BenvStat : Type where
  /-- The fork this block runs under, and through it the rules.

  The machine carries the *fork*, and `BenvStat.rules` below derives the rule
  record from it with `Fork.ruleSet`. That is what makes `ForkRules.Valid` a
  fact about every machine rather than a premise every statement has to carry:
  the only rule sets a machine can hold are the nine fork records, each
  proved usable once by `Fork.ruleSet_valid`. A rule record that describes no
  fork is not rejected, it is inexpressible.

  Carrying it here, rather than as an extra argument, is what keeps a single
  interpreter: every function that already sees a `BenvStat` -- directly, or
  through `Benv`, `Msg`, or `Sevm` -- can read the active rules without a
  signature change. Execution still branches on rule *data* and never on this
  field: it is a selection and provenance key, exactly as `ForkRules.fork`
  already is, and `Jaune`'s hygiene condition is that no `if fork = ...`
  appears in execution. -/
  fork : Fork
  chainId : UInt64
  origState : State
  blockGasLimit : Nat
  blockHashes: List U256
  coinbase : Address
  number : Nat
  baseFeePerGas : Nat
  time : U256
  prevRandao : U256
  excessBlobGas : Nat
  parentBeaconBlockRoot : U256
  /-- EIP-7843: the consensus slot number the header carries, which `SLOTNUM`
  pushes. Defaulted so that every existing `BenvStat` literal keeps
  elaborating; under rules without `op.slotnum` nothing reads it. -/
  slotNumber : UInt64 := 0

/-- The rules this block runs under.

Kept under its former name and type -- `BenvStat → ForkRules` -- so that every
*read* of the active rules, in this repository and downstream, is textually
unchanged. What moved is construction: there is no `rules` field to set, so
the only rule sets a machine can carry are the nine `Fork.ruleSet`
records. -/
def BenvStat.rules (s : BenvStat) : ForkRules := Fork.ruleSet s.fork

/-- The machine's fork index and the record it reads agree. -/
@[simp] theorem BenvStat.rules_fork (s : BenvStat) : s.rules.fork = s.fork :=
  Fork.ruleSet_fork s.fork

/-- **Every machine's rules are usable, with no premise.**

The corollary of `Fork.ruleSet_valid` that the Sufficiency results live off:
because `BenvStat` carries a `Fork`, `ForkRules.Valid` is discharged from the
machine itself rather than assumed at each statement. -/
theorem BenvStat.rules_valid (s : BenvStat) : s.rules.Valid :=
  Fork.ruleSet_valid s.fork

-- class Benvironment
structure Benv : Type where
  state : State
  createdAccounts : AdrSet
  stat : BenvStat
  /-- Committed SSTORE keys in the current transaction, rolled back with state. -/
  storageWrites : KeySet := .emptyWithCapacity

structure TenvStat : Type where
  origin: Address
  gasPrice: Nat
  gas: Nat
  /-- Amsterdam's state-gas reservoir beside the execution grant `gas`.
  Legacy transaction environments keep the default zero. -/
  stateGasReservoir : Nat := 0
  accessListAddresses: AdrSet
  accessListStorageKeys: KeySet
  blobVersionedHashes: List U256
  auths : List Authorization
  indexInBlock : Option Nat
  txHash: Option U256

-- class TransactionEnvironment
structure Tenv : Type where
  transientStorage: TransientStorage
  stat : TenvStat

-- class Message
structure Msg : Type where
  benv: Benv
  tenv: Tenv
  caller: Address
  target: Option Address
  currentTarget: Address
  gas: Nat
  value: U256
  data: Bytes
  codeAddress: Option Address
  code: ByteArray
  depth: Nat
  shouldTransferValue: Bool
  isStatic: Bool
  accessedAddresses: AdrSet
  accessedStorageKeys: KeySet
  disablePrecompiles : Bool
  /-- EIP-8037's state-gas grant: the reservoir the frame starts with, beside
  the execution grant `gas`.

  Defaulted to `0` for the same reason `Mach.stateGas` is defaulted to `zero`:
  a message built by a `none`-path caller does not name it, so every existing
  construction keeps elaborating and every `none`-path frame starts with an
  empty reservoir -- which `initDevm` then seeds as `StateGasMeter.zero`. -/
  stateGasGrant : Nat := 0
  /-- The accounts the frame's ancestors have scheduled for deletion when the
  frame is entered, which the frame's own `accountsToDelete` starts from.

  EELS's pre-London `SELFDESTRUCT` pays `REFUND_SELF_DESTRUCT` only when the
  originator is not in `refunded_accounts`, which is the frame's
  `accounts_to_delete` updated with every ancestor's (the loop over
  `parent_evm` aliases the frame's own set, berlin/vm/instructions/system.py),
  and a successful sibling's deletions are already merged into its parent's
  set. Starting a child's set from its parent's is therefore exactly that set:
  the merge on success is a union, and a failed child's set is discarded, so
  the deletions settled at the end of a transaction are unchanged. Only a fork
  that pays the refund carries the set (`callMsg`, `createMsg`); every other
  machine, Prague's included, enters with the empty set as before (unit U11d).
  Defaulted for the reason `stateGasGrant` is. -/
  inheritedDeletions : AdrSet := .emptyWithCapacity

def Msg.withBenv (msg : Msg) (benv : Benv) : Msg :=
  {msg with benv := benv}

def Benv.withState (benv : Benv) (st : State) : Benv :=
  {benv with state := st}

-- `origState` is the original state of a *transaction*, not of a block: it is
-- what `SSTORE` compares against to tell a clean update from a dirty one
-- (finding 3.8). Every normal and system transaction must open with this so
-- that its own input state, rather than the block prestate, is the original
-- state. The transaction write ledger starts empty; the remaining environment is preserved.
def Benv.beginTransaction (benv : Benv) : Benv :=
  {benv with
    stat := {benv.stat with origState := benv.state}
    storageWrites := .emptyWithCapacity}

-- EIP-7823 rejects an oversized `MODEXP` length header with a bare
-- `ExceptionalHalt` rather than one of the specification's named subclasses.
-- It is given its own tag here because every other exceptional halt this build
-- can report is already distinguishable by name, and reusing `OutOfGasError`
-- for a check that never inspects the gas counter would misreport it.
def modexpInputLimitTag : String := "ModexpInputLimitExceeded"

---------------- TRANSACTION-REJECTION REASONS -----------------

-- These tags are the transaction analogue of `blockExceptionTags` below:
-- one producer reason per official fixture identity.  Keeping nonce direction,
-- intrinsic gas, and the 256-bit gas-price product distinct is essential: the
-- fixtures name them separately, so a broad `InvalidTransaction` string cannot
-- classify them faithfully.

def gasPriceProductOverflowTag : String := "GasPriceProductOverflowError"
def gasAllowanceExceededTag : String := "GasAllowanceExceededError"
def initcodeSizeExceededTag : String := "InitcodeSizeExceededError"
def insufficientAccountFundsTag : String := "InsufficientAccountFundsError"
def insufficientMaxFeePerGasTag : String := "InsufficientMaxFeePerGasError"
/-- EIP-4844's per-blob-gas analogue of `insufficientMaxFeePerGasTag`. The
producer in `checkTransactionBlobData` always carried this exact spelling as a
literal; Step 10 names it so the typed vocabulary can pin the constructor to
the tag like every other transaction reason. Its official fixture identity is
the shared `INSUFFICIENT_MAX_FEE_PER_GAS` one. -/
def insufficientMaxFeePerBlobGasTag : String := "InsufficientMaxFeePerBlobGasError"
def transactionGasLimitExceededTag : String :=
  "TransactionGasLimitExceededError"
def intrinsicGasTooLowTag : String := "IntrinsicGasTooLowError"
def invalidChainIdTag : String := "InvalidChainIdError"
def nonceIsMaxTag : String := "NonceIsMaxError"
def nonceMismatchTooHighTag : String := "NonceMismatchTooHighError"
def nonceMismatchTooLowTag : String := "NonceMismatchTooLowError"
def priorityGreaterThanMaxFeeTag : String := "PriorityGreaterThanMaxFeeError"
def senderNotEoaTag : String := "SenderNotEoaError"
def type3BlobCountExceededTag : String := "Type3BlobCountExceededError"
def type3BlobCountLimitExceededTag : String :=
  "Type3BlobCountLimitExceededError"
def type3ContractCreationTag : String := "Type3ContractCreationError"
def type3InvalidBlobVersionedHashTag : String :=
  "Type3InvalidBlobVersionedHashError"
def type3ZeroBlobsTag : String := "Type3ZeroBlobsError"
def type4ContractCreationTag : String := "Type4ContractCreationError"
/-- A typed transaction whose type the fork does not admit (unit U5's
`maxType`; goal U11a gave it its own reason). -/
def typePreForkTag : String := "TypePreForkError"
def emptyAuthorizationListTag : String := "EmptyAuthorizationListError"

------------------- BLOCK-REJECTION REASONS --------------------

-- One tag per reason a header or a post-transition check can reject a block.
-- A bare `"InvalidBlock"` says only that *some* consensus rule failed, which is
-- exactly what let a block be rejected for the wrong reason and still be scored
-- as a pass: the official fixture vocabulary names ~17 distinct block
-- identities, and one string cannot be mapped to them. Each tag below is the
-- sole producer of its reason, so `Jaune/FixtureException.lean` can route it to
-- one identity.
--
-- Tags follow the `renderTagged` convention: a bare tag, or a tag opening
-- diagnostic text at a fixed " : ". Detail text after the delimiter is free.

/-- `gasLimit` is at or above the absolute `2 ^ 63` bound. Distinct from
`gasLimitAdjustmentTag`: the fixtures name these separately, and a gas limit
one above the bound can still sit inside the parent-relative window. -/
def gasLimitTooBigTag : String := "GasLimitTooBigError"

/-- `gasLimit` fails the parent-relative adjustment window or the minimum. -/
def gasLimitAdjustmentTag : String := "GasLimitAdjustmentError"

/-- The header's own `gasUsed` exceeds its own `gasLimit`. -/
def gasUsedOverflowTag : String := "GasUsedOverflowError"

/-- The block's computed gas used disagrees with the header's claim. Distinct
from `gasUsedOverflowTag`: this one is only knowable after execution. -/
def gasUsedMismatchTag : String := "GasUsedMismatchError"

/-- The block is no newer than its parent. -/
def timestampOlderThanParentTag : String := "TimestampOlderThanParentError"

/-- The block number is not the parent's successor. -/
def blockNumberTag : String := "BlockNumberError"

/-- The base fee disagrees with the value computed from the parent. -/
def baseFeePerGasTag : String := "BaseFeePerGasError"

/-- A nonzero difficulty, which is impossible after Paris. -/
def difficultyOverParisTag : String := "DifficultyOverParisError"

/-- An ommers hash other than the empty-list hash, impossible after Paris. -/
def ommersOverParisTag : String := "OmmersOverParisError"

/-- Before Paris: the header's difficulty disagrees with
`calculateBlockDifficulty` from the parent. -/
def invalidDifficultyTag : String := "InvalidDifficultyError"

/-- Before Paris: the block's ommers break a rule of `validateOmmers` -- the
list hash, the count, a duplicate, an ommer that is canonical or already
included, its depth or its parent, or the ommer's own header. -/
def invalidOmmersTag : String := "InvalidOmmersError"

/-- Extra data longer than 32 bytes. -/
def extraDataTooBigTag : String := "ExtraDataTooBigError"

/-- The named parent is not the block this chain is being extended from, and
the name is nonzero. -/
def unknownParentTag : String := "UnknownParentError"

/-- The named parent is the all-zero hash, which names no block. Separate from
`unknownParentTag` because the fixture vocabulary separates them. -/
def unknownParentZeroTag : String := "UnknownParentZeroError"

/-- The computed post-state root disagrees with the header. -/
def stateRootTag : String := "StateRootError"

/-- The computed transactions root disagrees with the header. -/
def transactionsRootTag : String := "TransactionsRootError"

/-- The computed receipts root disagrees with the header. -/
def receiptsRootTag : String := "ReceiptsRootError"

/-- The computed logs bloom disagrees with the header. -/
def logBloomTag : String := "LogBloomError"

/-- The computed withdrawals root disagrees with the header. -/
def withdrawalsRootTag : String := "WithdrawalsRootError"

/-- A nonzero header nonce, which is impossible after Paris. -/
def headerNonceTag : String := "HeaderNonceError"

/-- The excess blob gas disagrees with the value computed from the parent. -/
def excessBlobGasTag : String := "ExcessBlobGasError"

/-- The computed blob gas used disagrees with the header. -/
def blobGasUsedTag : String := "BlobGasUsedError"

/-- The computed requests hash disagrees with the header. -/
def requestsHashTag : String := "RequestsHashError"

/-- A deposit-contract log has the wrong ABI layout for an EIP-6110 request. -/
def depositEventLayoutTag : String := "DepositEventLayoutError"

/-- A mandatory protocol system-contract call reverted, threw, or ran out of gas. -/
def systemContractCallFailedTag : String := "SystemContractCallFailedError"
/-- A mandatory protocol system contract holds no code at the block that must
call it (EIP-7002/7251/8282 request contracts): the pinned
`process_checked_system_transaction` raises `InvalidBlock` before the call, and
the fixture identity is `BlockException.SYSTEM_CONTRACT_EMPTY`. Goal D (DP-2,
owner-approved): until then this reason was a fail-closed internal invariant. -/
def systemContractEmptyTag : String := "SystemContractEmptyError"
def blockRlpSizeExceededTag : String := "BlockRlpSizeExceededError"

/-- A fork-dependent header field is present when the rules do not define it,
or absent when they do.

One tag for both directions and both fields (EIP-7928's block-access-list hash
and EIP-7843's slot number), because it is one rule: a header carries exactly
the fields its fork defines. Which field and which direction is the detail. -/
def headerFieldPresenceTag : String := "HeaderFieldPresenceError"
-- EIP-7928 (goal C, fixed decision 9): four reasons of their own -- the
-- header's hash against the computed list (the one consensus observes), the
-- published list's content and form (refined by the fixture runner from the
-- list a fixture publishes), and the item rule.
def blockAccessListHashTag : String := "InvalidBlockAccessListHashError"
def blockAccessListContentTag : String := "InvalidBlockAccessListError"
def blockAccessListFormatTag : String := "MalformedBlockAccessListError"
def blockAccessListGasLimitTag : String := "BlockAccessListGasLimitExceededError"

------------------- STRICT CONSENSUS-FIELD DECODERS --------------------

-- The `Except`-level face of the strict shape checks in `Jaune/Types.lean`.
-- Each helper names one precise reason a consensus field can be malformed, in
-- the `renderTagged` tag convention the rest of the executable uses: a bare tag,
-- or a tag followed by " : " and free diagnostic text. The tags are separate
-- because the official fixture identities are separate -- a scalar wider than
-- 64 bits is `RLP_INVALID_FIELD_OVERFLOW_64`, a wrong list shape is
-- `RLP_STRUCTURES_ENCODING` -- so one generic `"DecodingError"` covering both
-- cannot be classified. `Jaune/FixtureException.lean` routes these exact tags;
-- adding a new decoder rejection therefore requires an explicit route there.

/-- An RLP item is not the list/string structure the field requires. -/
def rlpStructureTag : String := "RlpStructureError"

/-- A fixed-width field is not exactly as wide as it must be. -/
def rlpFixedWidthTag : String := "RlpFixedWidthError"

/-- A scalar field modelled as 64 bits does not fit in eight bytes. -/
def rlpFieldOverflow64Tag : String := "RlpFieldOverflow64Error"

/-- A scalar field modelled as 256 bits does not fit in thirty-two bytes. -/
def rlpFieldOverflow256Tag : String := "RlpFieldOverflow256Error"

/-- A scalar is within its width but not canonically encoded. -/
def rlpLeadingZerosTag : String := "RlpLeadingZerosError"

/-- A Prague block body omitted the withdrawals component altogether. This is
not the same failure as an arbitrary malformed block-list shape: the fixture
vocabulary assigns the omission its own consensus identity. -/
def rlpWithdrawalsNotReadTag : String := "RlpWithdrawalsNotReadError"

/-- The RLP decoded with valid local field shapes, but was not the canonical
encoding reconstructed from the decoded block. Kept distinct internally from
an initial structural decoding failure even though both map to the fixture's
`RLP_STRUCTURES_ENCODING` identity. -/
def rlpRoundTripTag : String := "RlpRoundTripError"

/-- A header is a list of well-formed items whose count is none of the
widths any fork's header has (15, 16, 17, 20, 21 or 23). Kept apart from
`rlpStructureTag` because the fixture vocabulary gives it its own identity,
`INCORRECT_BLOCK_FORMAT`: the Shanghai-to-Cancun transition fixtures build
exactly such headers, a Shanghai header with the blob fields or a Cancun one
without them (goal U11a). -/
def rlpHeaderWidthTag : String := "RlpHeaderWidthError"

--------------- TYPED SEMANTIC REASONS: CODEC AND VM ---------------

-- Declarations and renderers only (golden guards: `Jaune/Check/Machine.lean`);
-- no producer moves here, no rendered message changes; Steps 9 and 10 move them.
--
-- Placement is frozen by `scripts/report-integrity-design.md` section 6. All
-- four types below live in this module because their carriers and tag
-- vocabularies do: the strict field decoders and their seven tags, the
-- exceptional-halt vocabulary, and the low-level machine result are all
-- declared above. The precompile and cryptographic reasons live here too,
-- rather than in `Jaune/Precompiles.lean`, because a precompile failure must
-- be able to inhabit the machine result declared upstream of that module; a
-- reason type declared downstream could not. `Jaune/Precompiles.lean` keeps
-- only its own helpers and, from Step 9, its renderer arms.

/-- Why strict decoding rejected a value.

One constructor per reason in the strict tag vocabulary above, which is
already one producer per reason, so this is a lift rather than a redesign. The
`" : "` detail each decoder emits today -- the field label and the measured
width -- rides in the diagnostic payload; Step 10 may promote a particular
detail to a typed fact when it migrates that producer. -/
inductive DecodeError : Type
  /-- An item is not the list or string structure the field requires. -/
  | rlpStructure (detail : ErrorDetail)
  /-- A fixed-width field is not exactly as wide as it must be. -/
  | fixedWidth (detail : ErrorDetail)
  /-- A scalar modelled as 64 bits does not fit in eight bytes. -/
  | fieldOverflow64 (detail : ErrorDetail)
  /-- A scalar modelled as 256 bits does not fit in thirty-two bytes. -/
  | fieldOverflow256 (detail : ErrorDetail)
  /-- A scalar is within its width but not canonically encoded. -/
  | leadingZeros (detail : ErrorDetail)
  /-- A Prague block body omitted the withdrawals component. -/
  | withdrawalsNotRead (detail : ErrorDetail)
  /-- Local field shapes decoded, but the canonical re-encoding differs. -/
  | roundTrip (detail : ErrorDetail)
  /-- A header's field count is no fork's header width. -/
  | headerWidth (detail : ErrorDetail)
deriving DecidableEq, Repr

/-- The tag a decode reason renders under. -/
def DecodeError.tag : DecodeError → String
  | .rlpStructure _ => rlpStructureTag
  | .fixedWidth _ => rlpFixedWidthTag
  | .fieldOverflow64 _ => rlpFieldOverflow64Tag
  | .fieldOverflow256 _ => rlpFieldOverflow256Tag
  | .leadingZeros _ => rlpLeadingZerosTag
  | .withdrawalsNotRead _ => rlpWithdrawalsNotReadTag
  | .roundTrip _ => rlpRoundTripTag
  | .headerWidth _ => rlpHeaderWidthTag

/-- The diagnostic payload of a decode reason. -/
def DecodeError.detail : DecodeError → ErrorDetail
  | .rlpStructure d | .fixedWidth d | .fieldOverflow64 d
  | .fieldOverflow256 d | .leadingZeros d | .withdrawalsNotRead d
  | .roundTrip d | .headerWidth d => d

/-- The one renderer for `DecodeError`. -/
def DecodeError.render (e : DecodeError) : String :=
  renderTagged e.tag e.detail

/-- Every decode reason, for the completeness guards. -/
def DecodeError.all : List DecodeError :=
  [ .rlpStructure .none, .fixedWidth .none, .fieldOverflow64 .none,
    .fieldOverflow256 .none, .leadingZeros .none,
    .withdrawalsNotRead .none, .roundTrip .none, .headerWidth .none ]

/-- A reason the machine stops a frame with no gas returned and its state
changes rolled back.

Exactly the vocabulary declared above, one constructor per reason. Reverting
is deliberately *not* one of these: it is a separate arm of `EvmError`,
because it settles gas and returndata differently. -/
inductive ExceptionalHalt : Type
  | stackUnderflow (detail : ErrorDetail)
  | stackOverflow (detail : ErrorDetail)
  | outOfGas (detail : ErrorDetail)
  | modexpInputLimit (detail : ErrorDetail)
  | invalidOpcode (detail : ErrorDetail)
  | invalidJumpDest (detail : ErrorDetail)
  | stackDepthLimit (detail : ErrorDetail)
  | writeInStaticContext (detail : ErrorDetail)
  | outOfBoundsRead (detail : ErrorDetail)
  | invalidParameter (detail : ErrorDetail)
  | invalidContractPrefix (detail : ErrorDetail)
  | addressCollision (detail : ErrorDetail)
  | kzgProof (detail : ErrorDetail)
deriving DecidableEq, Repr

/-- The tag an exceptional halt renders under. -/
def ExceptionalHalt.tag : ExceptionalHalt → String
  | .stackUnderflow _ => "StackUnderflowError"
  | .stackOverflow _ => "StackOverflowError"
  | .outOfGas _ => "OutOfGasError"
  | .modexpInputLimit _ => modexpInputLimitTag
  | .invalidOpcode _ => "InvalidOpcode"
  | .invalidJumpDest _ => "InvalidJumpDestError"
  | .stackDepthLimit _ => "StackDepthLimitError"
  | .writeInStaticContext _ => "WriteInStaticContext"
  | .outOfBoundsRead _ => "OutOfBoundsRead"
  | .invalidParameter _ => "InvalidParameter"
  | .invalidContractPrefix _ => "InvalidContractPrefix"
  | .addressCollision _ => "AddressCollision"
  | .kzgProof _ => "KZGProofError"

/-- The diagnostic payload of an exceptional halt. -/
def ExceptionalHalt.detail : ExceptionalHalt → ErrorDetail
  | .stackUnderflow d | .stackOverflow d | .outOfGas d
  | .modexpInputLimit d | .invalidOpcode d | .invalidJumpDest d
  | .stackDepthLimit d | .writeInStaticContext d | .outOfBoundsRead d
  | .invalidParameter d | .invalidContractPrefix d | .addressCollision d
  | .kzgProof d => d

/-- The one renderer for `ExceptionalHalt`. -/
def ExceptionalHalt.render (e : ExceptionalHalt) : String :=
  renderTagged e.tag e.detail

/-- Every exceptional-halt reason, for the completeness guards. -/
def ExceptionalHalt.all : List ExceptionalHalt :=
  [ .stackUnderflow .none, .stackOverflow .none, .outOfGas .none,
    .modexpInputLimit .none, .invalidOpcode .none, .invalidJumpDest .none,
    .stackDepthLimit .none, .writeInStaticContext .none,
    .outOfBoundsRead .none, .invalidParameter .none,
    .invalidContractPrefix .none, .addressCollision .none, .kzgProof .none ]

/-- The tag a reverting frame reports. Exact, never a prefix match: reverting
is the one outcome that keeps its remaining gas. -/
def revertTag : String := "Revert"

/-- The tag an authorization or signature recovery reports when the signature
itself is malformed. Named because an EIP-7702 authorization tuple is ignored
on exactly this reason and on no other. -/
def invalidSignatureTag : String := "InvalidSignatureError"

/-- The tag a curve-point compression helper reports on failure. -/
def pointCompressionTag : String := "bCompress failed"

/-- The tag a pairing or field helper reports when its input is on the curve
but the operation has no value. -/
def cryptoValueTag : String := "ValueError"

/-- The tag reserved for a broken internal invariant. It is not a consensus
identity and must never classify as an expected block or transaction
rejection. -/
def internalErrorTag : String := "ERROR"

/-- Why a precompile or a cryptographic helper rejected its input, for the
reasons that are not already exceptional halts.

Gas exhaustion, a malformed parameter, and a failed KZG proof are exceptional
halts and stay in `ExceptionalHalt`; these three are the remainder. -/
inductive CryptoError : Type
  /-- A signature is not a well-formed secp256k1 signature. -/
  | invalidSignature (detail : ErrorDetail)
  /-- A curve point could not be compressed. -/
  | pointCompression (detail : ErrorDetail)
  /-- A pairing or field operation has no value for this input. -/
  | value (detail : ErrorDetail)
deriving DecidableEq, Repr

/-- The one renderer for `CryptoError`. -/
def CryptoError.render : CryptoError → String
  | .invalidSignature d => renderTagged invalidSignatureTag d
  | .pointCompression d => renderTagged pointCompressionTag d
  | .value d => renderTagged cryptoValueTag d

/-- A broken internal invariant.

Distinct from every consensus reason on purpose: it means this build is
wrong, not that the input is. It fails closed -- it can never be stored as a
settled exceptional halt, and it can never be scored as an expected
rejection. -/
inductive InternalError : Type
  /-- An assertion that the implementation believed unreachable. -/
  | assertion (detail : ErrorDetail)
  /-- A stated invariant of the implementation did not hold. -/
  | invariant (detail : ErrorDetail)
deriving DecidableEq, Repr

/-- The one renderer for `InternalError`. -/
def InternalError.render : InternalError → String
  | .assertion d => renderTagged "AssertionError" d
  | .invariant d => renderTagged internalErrorTag d

/-- Everything the machine can fail with.

The four arms are the four settlements: an exceptional halt zeroes gas and
rolls back, reverting keeps gas and returns data, a cryptographic reason is
converted by the precompile boundary, and an internal fault propagates out of
consensus entirely. Today the distinction is recovered from rendered text;
this type makes it a constructor. -/
inductive EvmError : Type
  | halt (reason : ExceptionalHalt)
  | revert
  | crypto (reason : CryptoError)
  | internal (reason : InternalError)
deriving DecidableEq, Repr

/-- The one renderer for `EvmError`. -/
def EvmError.render : EvmError → String
  | .halt reason => reason.render
  | .revert => revertTag
  | .crypto reason => reason.render
  | .internal reason => reason.render

/-- A settled frame outcome: the reason a frame halted exceptionally, or the
fact that it reverted. This is the storable half of `EvmError` — the frame
settlement records one of these in `Meta.error`, and a cryptographic or
internal failure is deliberately unrepresentable here, so it can only
propagate on the error channel and never read as a settled halt. -/
inductive SettledHalt : Type
  | halt (reason : ExceptionalHalt)
  | revert
deriving DecidableEq, Repr

/-- The one renderer for `SettledHalt`. A stored halt renders byte-for-byte as
the error-channel reason the settlement consumed. -/
def SettledHalt.render : SettledHalt → String
  | .halt reason => reason.render
  | .revert => revertTag

/-- The injection back into the full error vocabulary. -/
def SettledHalt.toEvmError : SettledHalt → EvmError
  | .halt reason => .halt reason
  | .revert => .revert

@[simp] theorem SettledHalt.render_toEvmError (h : SettledHalt) :
    h.toEvmError.render = h.render := by
  cases h <;> rfl

/-- The structure reason for an RLP item that is not what the field requires.
Kept here so structure failures read the same at every call site; the render
is byte-for-byte the string the retired stringly helper produced. -/
def DecodeError.structure (name : String) (detail : String) : DecodeError :=
  .rlpStructure (.text s!"{name} : {detail}")

/-- A fixed-width field: exactly `n` bytes, no more and no fewer. -/
def Bytes.toRlpFixed (name : String) (n : Nat) (xs : Bytes) :
    Except DecodeError Bytes :=
  (xs.toFixed? n).toExcept
    (.fixedWidth (.text s!"{name} must be exactly {n} bytes, but is {xs.length}"))

/-- A fixed-width 32-byte hash or root, as a `B256`. `Bytes.toB256?` is already an
exact-width decoder, so this adds the precise reason rather than a check. Note
these fields are *bytes*, not scalars: a root may legitimately begin with a zero
byte, so the canonical-scalar rule must not be applied to them. -/
def Bytes.toRlpHash (name : String) (xs : Bytes) : Except DecodeError U256 :=
  xs.toU256?.toExcept
    (.fixedWidth (.text s!"{name} must be exactly 32 bytes, but is {xs.length}"))

/-- A fixed-width 8-byte field, as a `UInt64`. Like `toRlpHash`, this is bytes
rather than a scalar: the header nonce is eight bytes of zeroes, not empty. -/
def Bytes.toRlpFixedUInt64 (name : String) (xs : Bytes) : Except DecodeError UInt64 :=
  xs.toUInt64?.toExcept
    (.fixedWidth (.text s!"{name} must be exactly 8 bytes, but is {xs.length}"))

/-- The canonicality half of scalar checking, shared by every width. The
overflow *constructor* is a parameter because the width is what the official
vocabulary distinguishes, while non-canonical encoding is one reason at every
width. -/
private def rlpScalarBytes (overflow : ErrorDetail → DecodeError)
    (name : String) (n : Nat) (xs : Bytes) : Except DecodeError Bytes := do
  if xs.length > n then
    .error <| overflow <| .text
      s!"{name} scalar is {xs.length} bytes, exceeding its {n}-byte width"
  if xs.head? = some (0 : UInt8) then
    .error <| .leadingZeros <| .text
      s!"{name} scalar 0x{Bytes.toHex xs} \
         is not canonically encoded (leading zero byte)"
  .ok xs

/-- A canonical unsigned scalar of at most `n` bytes, as a `Nat`. Overflow is
reported against the 256-bit identity, this being the widest scalar the
consensus fields have; a field modelled as 64 bits must use `toRlpB64`. -/
def Bytes.toRlpNat (name : String) (n : Nat) (xs : Bytes) :
    Except DecodeError Nat := do
  let xs ← rlpScalarBytes .fieldOverflow256 name n xs
  .ok xs.toNat

/-- A canonical 64-bit scalar: at most eight bytes, converted without
truncation. -/
def Bytes.toRlpUInt64 (name : String) (xs : Bytes) : Except DecodeError UInt64 := do
  let xs ← rlpScalarBytes .fieldOverflow64 name 8 xs
  .ok xs.toUInt64

/-- A canonical 256-bit scalar: at most thirty-two bytes, converted without
truncation. -/
def Bytes.toRlpU256 (name : String) (xs : Bytes) : Except DecodeError U256 := do
  let xs ← rlpScalarBytes .fieldOverflow256 name 32 xs
  .ok xs.toU256

/-- An address field: exactly twenty bytes. -/
def Bytes.toRlpAddress (name : String) (xs : Bytes) : Except DecodeError Address :=
  xs.toAddress?.toExcept
    (.fixedWidth (.text s!"{name} must be exactly 20 bytes, but is {xs.length}"))

/-- An optional contract-creation receiver: empty, or exactly twenty bytes. -/
def Bytes.toRlpReceiver (name : String) (xs : Bytes) :
    Except DecodeError (Option Address) :=
  xs.toReceiver?.toExcept
    (.fixedWidth (.text s!"{name} must be empty or exactly 20 bytes, \
       but is {xs.length}"))

--------------- WIRE-STRUCTURAL PREDICATES ----------------

-- P0.4's representation layer, kept deliberately separate from contextual
-- consensus validity (fixed decision 3). Each predicate below is a *lift of
-- the strict decoders above and in `Jaune/Execution.lean` /
-- `Jaune/Transaction.lean*` -- it says exactly what a decoder-produced value
-- satisfies, and nothing about nonces, base fees, gas limits or fork
-- activation. Every one is decidable by finite inspection, so a hand-built
-- record can be certified or refused without an oracle.

/-- Peel one `bind` off an `Except` `do` chain. Declared here because the
strict field decoders below are the first `do` chains this library inverts;
`Jaune/Sufficiency.lean`'s instruction walks use the same lemma. -/
theorem Except.bind_eq_ok {ε α β : Type} {e : Except ε α} {f : α → Except ε β}
    {b : β} (h : e >>= f = .ok b) : ∃ a, e = .ok a ∧ f a = .ok b := by
  cases e with
  | error err => exact absurd h (by simp [bind, Except.bind])
  | ok a => exact ⟨a, rfl, h⟩

/-- The `Iff` form, so that `simp only` can flatten a whole twenty-field
decoder chain into nested existentials in one step. -/
theorem Except.bind_eq_ok_iff {ε α β : Type} {e : Except ε α}
    {f : α → Except ε β} {b : β} :
    (e >>= f = .ok b) ↔ ∃ a, e = .ok a ∧ f a = .ok b := by
  refine ⟨Except.bind_eq_ok, ?_⟩
  rintro ⟨a, rfl, h⟩
  simpa [bind, Except.bind] using h

/-- Bridge equations for the legacy renderer adapters (P0.7 item 8). A typed
core reaches its stringly caller through `Except.mapError <Type>.render`, and
downstream proofs should invert the adapter with these two lemmas rather than
unfolding `mapError` at every boundary. -/
@[simp] theorem Except.mapError_eq_ok_iff {ε δ α : Type} {f : ε → δ}
    {x : Except ε α} {a : α} : x.mapError f = .ok a ↔ x = .ok a := by
  cases x <;> simp [Except.mapError]

theorem Except.mapError_eq_error_iff {ε δ α : Type} {f : ε → δ}
    {x : Except ε α} {d : δ} :
    x.mapError f = .error d ↔ ∃ e, x = .error e ∧ f e = d := by
  cases x with
  | error e => simp [Except.mapError]
  | ok a => simp [Except.mapError]

/-- Inversion for the `List.mapM` the list-shaped decoders use: every element
of the decoded list is something the element decoder accepted. This is what
lifts a per-element soundness theorem to a whole ommer, withdrawal,
authorisation, or transaction list. -/
theorem List.mapM_except_eq_ok_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {r : List β}, l.mapM f = .ok r → ∀ b ∈ r, ∃ a, f a = .ok b := by
  intro l
  induction l with
  | nil =>
    intro r h b hb
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    simp at hb
  | cons a as ih =>
    intro r h b hb
    rw [List.mapM_cons] at h
    obtain ⟨b0, hb0, h⟩ := Except.bind_eq_ok h
    obtain ⟨bs, hbs, h⟩ := Except.bind_eq_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases List.mem_cons.mp hb with rfl | hb'
    · exact ⟨a, hb0⟩
    · exact ih hbs b hb'

/-- The width identity the 256-bit consensus scalars are stated with: a
thirty-two byte field and a 256-bit bound are the same bound. -/
theorem pow_256_eq_pow_32 : (2 : Nat) ^ 256 = 256 ^ 32 := by norm_num

/-- The width identity for the 64-bit consensus scalars. -/
theorem pow_64_eq_pow_8 : (2 : Nat) ^ 64 = 256 ^ 8 := by norm_num

/-- A canonical RLP scalar byte string: no wider than its field, and with no
leading zero byte. This is the `Prop` face of `Bytes.isCanonicalScalar`, the
pure shape check the decoders are built from, and it is a real obligation for
`Tx.r`/`Tx.s`, which are stored as raw bytes. -/
def Bytes.CanonicalScalar (n : Nat) (xs : Bytes) : Prop :=
  Bytes.isCanonicalScalar n xs = true

instance (n : Nat) (xs : Bytes) : Decidable (Bytes.CanonicalScalar n xs) := by
  unfold Bytes.CanonicalScalar; infer_instance

theorem Bytes.canonicalScalar_iff {n : Nat} {xs : Bytes} :
    Bytes.CanonicalScalar n xs ↔ xs.length ≤ n ∧ xs.head? ≠ some (0 : UInt8) := by
  unfold Bytes.CanonicalScalar Bytes.isCanonicalScalar
  simp

private theorem rlpScalarBytes_eq_ok {overflow : ErrorDetail → DecodeError}
    {name : String} {n : Nat}
    {xs ys : Bytes} (h : rlpScalarBytes overflow name n xs = .ok ys) :
    ys = xs ∧ Bytes.CanonicalScalar n xs := by
  unfold rlpScalarBytes at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i h1
    split at h
    · exact absurd h (by simp)
    · rename_i h2
      simp only [Except.ok.injEq] at h
      refine ⟨h.symm, ?_⟩
      rw [Bytes.canonicalScalar_iff]
      exact ⟨by omega, h2⟩

/-- Soundness of the at-most-`n`-byte scalar decoder: the accepted bytes are a
canonical scalar, and the value they denote is below `256 ^ n`. -/
theorem Bytes.toRlpNat_eq_ok {name : String} {n : Nat} {xs : Bytes} {v : Nat}
    (h : xs.toRlpNat name n = .ok v) :
    Bytes.CanonicalScalar n xs ∧ v < 256 ^ n := by
  unfold Bytes.toRlpNat at h
  obtain ⟨zs, hz, hv⟩ := Except.bind_eq_ok h
  obtain ⟨rfl, hc⟩ := rlpScalarBytes_eq_ok hz
  refine ⟨hc, ?_⟩
  simp only [Except.ok.injEq] at hv
  exact hv ▸ Bytes.toNat_lt_of_length_le (Bytes.canonicalScalar_iff.mp hc).1

/-- The 256-bit scalar decoder accepts only canonical 32-byte-wide scalars. -/
theorem Bytes.toRlpU256_eq_ok {name : String} {xs : Bytes} {v : U256}
    (h : xs.toRlpU256 name = .ok v) : Bytes.CanonicalScalar 32 xs := by
  unfold Bytes.toRlpU256 at h
  obtain ⟨zs, hz, _⟩ := Except.bind_eq_ok h
  exact (rlpScalarBytes_eq_ok hz).2

/-- The form the consensus scalars are stated in: a thirty-two byte field
carries a `U256`. -/
theorem Bytes.toRlpNat_lt_two_pow_256 {name : String} {xs : Bytes} {v : Nat}
    (h : xs.toRlpNat name 32 = .ok v) : v < 2 ^ 256 := by
  rw [pow_256_eq_pow_32]
  exact (Bytes.toRlpNat_eq_ok h).2

/-- The fixed-width decoder returns exactly `n` bytes. -/
theorem Bytes.toRlpFixed_eq_ok {name : String} {n : Nat} {xs ys : Bytes}
    (h : xs.toRlpFixed name n = .ok ys) : ys.length = n := by
  unfold Bytes.toRlpFixed Bytes.toFixed? at h
  split at h
  · rename_i hl
    simp only [Option.toExcept, Except.ok.injEq] at h
    exact h ▸ hl
  · exact absurd h (by simp [Option.toExcept])

/-- Wire well-formedness of a header: precisely the representation facts
`BLT.toExHeader` establishes. The bloom is a fixed 256-byte string; the
`Nat`-modelled consensus scalars are `U256`; the two blob-gas fields are the
header's only `U64` scalars. Everything else in `Header` is already carried by
a width-exact type. -/
def Header.WireWellFormed (h : Header) : Prop :=
  h.logsBloom.length = 256 ∧
  h.difficulty < 2 ^ 256 ∧
  h.number < 2 ^ 256 ∧
  h.gasLimit < 2 ^ 256 ∧
  h.gasUsed < 2 ^ 256 ∧
  h.timestamp < 2 ^ 256 ∧
  (∀ b ∈ h.baseFeePerGas, b < 2 ^ 256) ∧
  (∀ b ∈ h.blobGasUsed, b < 2 ^ 64) ∧
  (∀ b ∈ h.excessBlobGas, b < 2 ^ 64)

instance (h : Header) : Decidable (Header.WireWellFormed h) := by
  unfold Header.WireWellFormed; infer_instance

/-- EIP-7702 authorisation tuples arrive inside type-4 transactions, so their
fields are untrusted in exactly the way a transaction's are. `yParity` is the
only one `BLT.toExAuth` reads as an unbounded scalar. -/
def Authorization.WireWellFormed (a : Authorization) : Prop := a.yParity < 2 ^ 256

instance (a : Authorization) : Decidable (Authorization.WireWellFormed a) := by
  unfold Authorization.WireWellFormed; infer_instance

/-- The per-type half of transaction well-formedness: the fee scalars each
envelope carries, and the recursive obligation on type-4 authorisations.
Access-list and blob-hash material is already width-exact by type. -/
def TransactionType.WireWellFormed : TransactionType → Prop
  | .legacy gasPrice _ => gasPrice < 2 ^ 256
  | .eip2930 _ gasPrice _ _ => gasPrice < 2 ^ 256
  | .eip1559 _ maxPriorityFee maxFee _ _ =>
    maxPriorityFee < 2 ^ 256 ∧ maxFee < 2 ^ 256
  | .eip4844 _ maxPriorityFee maxFee _ _ maxBlobFee _ =>
    maxPriorityFee < 2 ^ 256 ∧ maxFee < 2 ^ 256 ∧ maxBlobFee < 2 ^ 256
  | .eip7702 _ maxPriorityFee maxFee _ _ auths =>
    maxPriorityFee < 2 ^ 256 ∧ maxFee < 2 ^ 256 ∧
      ∀ a ∈ auths, Authorization.WireWellFormed a

instance (t : TransactionType) : Decidable (TransactionType.WireWellFormed t) := by
  cases t <;> (unfold TransactionType.WireWellFormed; infer_instance)

/-- Whether a transaction is a legacy (untyped) one. A typed transaction's
canonical block encoding is its envelope byte followed by its payload, never
the legacy list, so this is the discriminator the checked ingress needs. -/
def TransactionType.isLegacy : TransactionType → Bool
  | .legacy _ _ => true
  | _ => false

/-- Wire well-formedness of a transaction: the `U256` scalars every envelope
shares, canonical signature scalar bytes, and the per-type obligations.
`nonce` is already a `UInt64` and `data` is unconstrained on the wire. -/
def Transaction.WireWellFormed (tx : Transaction) : Prop :=
  tx.gasLimit < 2 ^ 256 ∧
  tx.value < 2 ^ 256 ∧
  tx.v < 2 ^ 256 ∧
  Bytes.CanonicalScalar 32 tx.r ∧
  Bytes.CanonicalScalar 32 tx.s ∧
  tx.type.WireWellFormed

instance (tx : Transaction) : Decidable (Transaction.WireWellFormed tx) := by
  unfold Transaction.WireWellFormed; infer_instance

/-- EIP-4895's withdrawal amount is a 64-bit Gwei scalar on the wire even
though `Withdrawal.amount` stores 256 bits for balance arithmetic, so a
decoded withdrawal always has its upper 192 bits clear. Design report §7 names
this as the one place a semantic field is wider than its wire type. -/
def Withdrawal.WireWellFormed (w : Withdrawal) : Prop :=
  w.amount.1 = ((0, 0) : U128) ∧ w.amount.2.1 = (0 : UInt64)

instance (w : Withdrawal) : Decidable (Withdrawal.WireWellFormed w) := by
  unfold Withdrawal.WireWellFormed
  apply decidable_of_iff (w.amount.1.1 = 0 ∧ w.amount.1.2 = 0 ∧ w.amount.2.1 = 0)
  · constructor
    · rintro ⟨ha, hb, hc⟩
      exact ⟨by exact Prod.ext ha hb, hc⟩
    · rintro ⟨h, hc⟩
      exact ⟨Prod.mk.inj h |>.1, Prod.mk.inj h |>.2, hc⟩

/-- Widening a `UInt64` to a `B256` leaves the upper 192 bits clear. This is
what makes `Withdrawal.WireWellFormed` a genuine lift of
`BLT.toExWithdrawal`, which reads the amount with the 64-bit scalar
decoder and then widens it. -/
theorem UInt64.toNat_toU256_high (x : UInt64) :
    (x.toNat.toU256).1 = ((0, 0) : U128) ∧ (x.toNat.toU256).2.1 = (0 : UInt64) := by
  have hx : x.toNat < 2 ^ 64 := x.toNat_lt
  have h128 : x.toNat >>> 128 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt
      (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  have h64 : x.toNat >>> 64 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hx
  constructor
  · simp [Nat.toU256, h128, Nat.toU128]
    rfl
  · simp [Nat.toU256, Nat.toU128, h64]

/-- A transaction slot inside a block body. `BLT.toExBlock` turns a list
item into a decoded legacy transaction and a byte-string item into opaque
typed-envelope bytes, so the two sides carry genuinely different obligations:
the decoded side must be a well-formed legacy transaction, while typed bytes
stay opaque until the existing decode point inside `applyBody`. Eagerly
decoding them here would change which error wins (fixed decision 5). -/
def TxEntry.WireWellFormed : Bytes ⊕ Transaction → Prop
  | .inl _ => True
  | .inr tx => Transaction.WireWellFormed tx ∧ tx.type.isLegacy = true

instance (e : Bytes ⊕ Transaction) : Decidable (TxEntry.WireWellFormed e) := by
  cases e <;> (unfold TxEntry.WireWellFormed; infer_instance)

/-- Structural canonicality of a decoded block: the header, every ommer
header, every withdrawal, and every transaction slot are wire-well-formed.
This is the componentwise lift of `BLT.toExBlock`; the byte-for-byte
re-encoding obligation is carried separately, by `CanonicalBlock`. -/
def Block.RlpCanonical (b : Block) : Prop :=
  b.header.WireWellFormed ∧
  (∀ o ∈ b.ommers, Header.WireWellFormed o) ∧
  (∀ w ∈ b.withdrawals, Withdrawal.WireWellFormed w) ∧
  (∀ e ∈ b.transactions, TxEntry.WireWellFormed e)

instance (b : Block) : Decidable (Block.RlpCanonical b) := by
  unfold Block.RlpCanonical; infer_instance

--------------- STRICT DECODER REGRESSION CHECKS ----------------

-- Each reason is reported under its own tag, and each tag is recognized by the
-- `renderTagged` convention the classifier reads -- an exact tag, or a tag
-- opening detail text at " : ". Accepted values are checked too: the point of
-- rejecting a nine-byte index is to keep the eight-byte ones exact.

/-- EIP-8037's per-frame state-gas meter.

Amsterdam meters a frame in two dimensions. `Mach.gasLeft` keeps its name and
its meaning -- it is execution gas, and `GAS` still pushes it, exactly as
upstream pushes `gas_meter.gas_left`. This record is the second dimension, and
it is nested and defaulted so that every `Mach` literal and every `with`-update
that does not name it goes on elaborating unchanged.

The four fields are upstream's, one for one:

* `left` is `state_gas_left`, the frame's reservoir. State charges draw from
  here first.
* `baseline` is `state_gas_baseline`, the level a rollback refills to. It
  starts at the frame's grant and only ever moves down, when a commit marks
  charges non-refillable.
* `spilled` is `state_gas_spilled`: execution gas that covered a state charge
  after the reservoir emptied, not yet credited back. EIP-8037 calls this
  quantity `state_gas_from_gas_left`.
* `committedSpill` is `state_gas_committed_spill`: spill a commit marked
  non-refillable. Only a rollback to frame entry credits it back.

Committed *reservoir* draw needs no field of its own: each commit lowers the
baseline, so it is the grant minus `baseline`. -/
@[ext]
structure StateGasMeter : Type where
  /-- `state_gas_left`: the frame's state-gas reservoir. -/
  left : Nat
  /-- `state_gas_baseline`: the reservoir level a rollback refills to. -/
  baseline : Nat
  /-- `state_gas_spilled`: execution gas spent covering state charges. -/
  spilled : Nat
  /-- `state_gas_committed_spill`: spill marked non-refillable by a commit. -/
  committedSpill : Nat
deriving DecidableEq, Repr

/-- The meter a single-dimension fork carries: no reservoir, no spill.

Under `rules.stateGas = none` every frame starts here and stays here, which is
the invariant `stateGasZero` states and every Prague-facing bridge lemma uses. -/
def StateGasMeter.zero : StateGasMeter := ⟨0, 0, 0, 0⟩

@[ext]
structure Mach : Type where
  stack : List U256
  memory : Mem
  /-- Execution gas. Unchanged in name and in meaning by EIP-8037: `GAS` still
  pushes it, every existing charge still draws from it, and every Prague-stated
  fact about it is the fact it was. -/
  gasLeft : Nat
  /-- EIP-8037's state-gas dimension.

  Defaulted, and that default is load-bearing rather than a convenience: a
  `Mach` literal or `with`-update that does not name this field goes on
  elaborating unchanged, which is what keeps the metering shape from rewriting
  every downstream `Mach` site. Under `rules.stateGas = none` it is `zero` at
  frame entry and stays `zero`. -/
  stateGas : StateGasMeter := .zero

@[ext]
structure Meta : Type where
  logs : List Log
  refundCounter : Int
  output : Bytes
  accountsToDelete : AdrSet
  returnData : Bytes
  error : Option SettledHalt
  accessedAddresses : AdrSet
  accessedStorageKeys : KeySet
  createdAccounts : AdrSet
  /-- EIP-7928 (goal C): the accounts this frame and its incorporated children
  read through a state accessor -- the pinned `state_tracker`'s
  `account_reads`, transcribed primitive by primitive (goal C, Appendix B).
  Recorded only under `rules.bal = some _`: `Devm.balReadAccount` is the
  identity otherwise, so no frame under Prague–BPO2 rules ever allocates it.
  Defaulted so that every `Meta` literal keeps elaborating. The set survives a
  child's halt or revert -- a failed child's `Devm` keeps its `Meta` -- and is
  merged into the parent at every incorporation, which is the pinned "shared
  by reference, never rolled back" rule. -/
  accountReads : AdrSet := .emptyWithCapacity
  /-- EIP-7928: the storage slots read (`get_storage`), under the same rules. -/
  storageReads : KeySet := .emptyWithCapacity
  /-- EIP-161: the accounts this frame and its incorporated children touched
  (EELS `Evm.touched_accounts`), swept at the end of the transaction when they
  are still empty. Recorded only under `rules.settle.touchedSweep` (Spurious
  Dragon through Gray Glacier), so it stays empty under every Paris-and-later
  rule set. Defaulted so that every `Meta` literal keeps elaborating. It dies
  with a failed child, except for EELS's RIPEMD-160 quirk
  (`Substate.keepTouch` in `resume`). -/
  touchedAccounts : AdrSet := .emptyWithCapacity

@[ext]
structure World : Type where
  state : State
  transientStorage : TransientStorage
  /-- Explicit storage writes; implicit storage deletion removes keys here.
  This belongs to the rollback snapshot, unlike the read sets in Meta. -/
  storageWrites : KeySet := .emptyWithCapacity

@[ext]
structure Devm : Type where
  mach : Mach
  «meta» : Meta
  world : World

def Devm.stack (devm : Devm) : List U256 := devm.mach.stack
def Devm.memory (devm : Devm) : Mem := devm.mach.memory
def Devm.gasLeft (devm : Devm) : Nat := devm.mach.gasLeft
def Devm.stateGas (devm : Devm) : StateGasMeter := devm.mach.stateGas
def Devm.stateGasLeft (devm : Devm) : Nat := devm.mach.stateGas.left
def Devm.logs (devm : Devm) : List Log := devm.meta.logs
def Devm.refundCounter (devm : Devm) : Int := devm.meta.refundCounter
def Devm.output (devm : Devm) : Bytes := devm.meta.output
def Devm.accountsToDelete (devm : Devm) : AdrSet := devm.meta.accountsToDelete
def Devm.returnData (devm : Devm) : Bytes := devm.meta.returnData
def Devm.error (devm : Devm) : Option SettledHalt := devm.meta.error
def Devm.accessedAddresses (devm : Devm) : AdrSet := devm.meta.accessedAddresses
def Devm.accessedStorageKeys (devm : Devm) : KeySet := devm.meta.accessedStorageKeys
def Devm.state (devm : Devm) : State := devm.world.state
def Devm.createdAccounts (devm : Devm) : AdrSet := devm.meta.createdAccounts
def Devm.transientStorage (devm : Devm) : TransientStorage := devm.world.transientStorage

def Devm.setMach (devm : Devm) (mach : Mach) : Devm :=
  { devm with mach := mach }

def Devm.setMeta (devm : Devm) (view : Meta) : Devm :=
  { devm with «meta» := view }

def Devm.setWorld (devm : Devm) (world : World) : Devm :=
  { devm with world := world }

structure Sevm : Type where
  caller : Address
  target : Option Address
  currentTarget : Address
  gas : Nat
  value : U256
  data : Bytes
  codeAddress : Option Address
  code : ByteArray
  depth : Nat
  shouldTransferValue : Bool
  isStatic : Bool
  disablePrecompiles : Bool
  benvStat : BenvStat
  tenvStat : TenvStat

@[ext]
structure Evm : Type where
  pc : Nat
  sta : Sevm
  dyna : Devm

/-- Every static machine's rules are usable, with no premise.

The form the Sufficiency results take their witness in: where a statement about
a `Sevm` used to bind `(hv : sevm.benvStat.rules.Valid)`, it now applies this. -/
theorem Sevm.rules_valid (sevm : Sevm) : sevm.benvStat.rules.Valid :=
  BenvStat.rules_valid sevm.benvStat

/-- Every machine's rules are usable, with no premise. See `Sevm.rules_valid`. -/
theorem Evm.rules_valid (evm : Evm) : evm.sta.benvStat.rules.Valid :=
  BenvStat.rules_valid evm.sta.benvStat

def Devm.withStack (devm : Devm) (stack : List U256) : Devm :=
  devm.setMach {devm.mach with stack := stack}

def Devm.withMemory (devm : Devm) (memory : Mem) : Devm :=
  devm.setMach {devm.mach with memory := memory}

def Devm.withGasLeft (devm : Devm) (gasLeft : Nat) : Devm :=
  devm.setMach {devm.mach with gasLeft := gasLeft}

def Devm.withLogs (devm : Devm) (logs : List Log) : Devm :=
  devm.setMeta {devm.meta with logs := logs}

def Devm.withRefundCounter (devm : Devm) (refundCounter : Int) : Devm :=
  devm.setMeta {devm.meta with refundCounter := refundCounter}

theorem Devm.withRefundCounter_refundCounter (devm : Devm) (rc : Int) :
    (devm.withRefundCounter rc).refundCounter = rc := rfl

def Devm.withOutput (devm : Devm) (output : Bytes) : Devm :=
  devm.setMeta {devm.meta with output := output}

theorem Devm.setMach_stack (devm : Devm) (mach : Mach) :
    (devm.setMach mach).stack = mach.stack := rfl

theorem Devm.setMach_memory (devm : Devm) (mach : Mach) :
    (devm.setMach mach).memory = mach.memory := rfl

theorem Devm.setMach_logs (devm : Devm) (mach : Mach) :
    (devm.setMach mach).logs = devm.logs := rfl

theorem Devm.setMach_refundCounter (devm : Devm) (mach : Mach) :
    (devm.setMach mach).refundCounter = devm.refundCounter := rfl

theorem Devm.setMach_output (devm : Devm) (mach : Mach) :
    (devm.setMach mach).output = devm.output := rfl

theorem Devm.setMach_accountsToDelete (devm : Devm) (mach : Mach) :
    (devm.setMach mach).accountsToDelete = devm.accountsToDelete := rfl

theorem Devm.setMach_returnData (devm : Devm) (mach : Mach) :
    (devm.setMach mach).returnData = devm.returnData := rfl

theorem Devm.setMach_error (devm : Devm) (mach : Mach) :
    (devm.setMach mach).error = devm.error := rfl

theorem Devm.setMach_accessedAddresses (devm : Devm) (mach : Mach) :
    (devm.setMach mach).accessedAddresses = devm.accessedAddresses := rfl

theorem Devm.setMach_accessedStorageKeys (devm : Devm) (mach : Mach) :
    (devm.setMach mach).accessedStorageKeys = devm.accessedStorageKeys := rfl

theorem Devm.setMach_state (devm : Devm) (mach : Mach) :
    (devm.setMach mach).state = devm.state := rfl

theorem Devm.setMach_createdAccounts (devm : Devm) (mach : Mach) :
    (devm.setMach mach).createdAccounts = devm.createdAccounts := rfl

theorem Devm.setMach_transientStorage (devm : Devm) (mach : Mach) :
    (devm.setMach mach).transientStorage = devm.transientStorage := rfl

/-- Overwriting an overwritten machine keeps only the last write. -/
theorem Devm.setMach_setMach {devm : Devm} {m m' : Mach} :
    (devm.setMach m).setMach m' = devm.setMach m' := rfl

theorem Devm.withOutput_gasLeft (devm : Devm) (out : Bytes) :
    (devm.withOutput out).gasLeft = devm.gasLeft := rfl

theorem Devm.setMeta_stack (devm : Devm) (view : Meta) :
    (devm.setMeta view).stack = devm.stack := rfl

theorem Devm.setMeta_memory (devm : Devm) (view : Meta) :
    (devm.setMeta view).memory = devm.memory := rfl

theorem Devm.setMeta_logs (devm : Devm) (view : Meta) :
    (devm.setMeta view).logs = view.logs := rfl

theorem Devm.setMeta_refundCounter (devm : Devm) (view : Meta) :
    (devm.setMeta view).refundCounter = view.refundCounter := rfl

theorem Devm.setMeta_output (devm : Devm) (view : Meta) :
    (devm.setMeta view).output = view.output := rfl

theorem Devm.setMeta_accountsToDelete (devm : Devm) (view : Meta) :
    (devm.setMeta view).accountsToDelete = view.accountsToDelete := rfl

theorem Devm.setMeta_returnData (devm : Devm) (view : Meta) :
    (devm.setMeta view).returnData = view.returnData := rfl

theorem Devm.setMeta_error (devm : Devm) (view : Meta) :
    (devm.setMeta view).error = view.error := rfl

theorem Devm.setMeta_accessedAddresses (devm : Devm) (view : Meta) :
    (devm.setMeta view).accessedAddresses = view.accessedAddresses := rfl

theorem Devm.setMeta_accessedStorageKeys (devm : Devm) (view : Meta) :
    (devm.setMeta view).accessedStorageKeys = view.accessedStorageKeys := rfl

theorem Devm.setMeta_state (devm : Devm) (view : Meta) :
    (devm.setMeta view).state = devm.state := rfl

theorem Devm.setMeta_createdAccounts (devm : Devm) (view : Meta) :
    (devm.setMeta view).createdAccounts = view.createdAccounts := rfl

theorem Devm.setMeta_transientStorage (devm : Devm) (view : Meta) :
    (devm.setMeta view).transientStorage = devm.transientStorage := rfl

theorem Devm.setWorld_stack (devm : Devm) (world : World) :
    (devm.setWorld world).stack = devm.stack := rfl

theorem Devm.setWorld_memory (devm : Devm) (world : World) :
    (devm.setWorld world).memory = devm.memory := rfl

theorem Devm.setWorld_logs (devm : Devm) (world : World) :
    (devm.setWorld world).logs = devm.logs := rfl

theorem Devm.setWorld_refundCounter (devm : Devm) (world : World) :
    (devm.setWorld world).refundCounter = devm.refundCounter := rfl

theorem Devm.setWorld_output (devm : Devm) (world : World) :
    (devm.setWorld world).output = devm.output := rfl

theorem Devm.setWorld_accountsToDelete (devm : Devm) (world : World) :
    (devm.setWorld world).accountsToDelete = devm.accountsToDelete := rfl

theorem Devm.setWorld_returnData (devm : Devm) (world : World) :
    (devm.setWorld world).returnData = devm.returnData := rfl

theorem Devm.setWorld_error (devm : Devm) (world : World) :
    (devm.setWorld world).error = devm.error := rfl

theorem Devm.setWorld_accessedAddresses (devm : Devm) (world : World) :
    (devm.setWorld world).accessedAddresses = devm.accessedAddresses := rfl

theorem Devm.setWorld_accessedStorageKeys (devm : Devm) (world : World) :
    (devm.setWorld world).accessedStorageKeys = devm.accessedStorageKeys := rfl

theorem Devm.setWorld_state (devm : Devm) (world : World) :
    (devm.setWorld world).state = world.state := rfl

theorem Devm.setWorld_createdAccounts (devm : Devm) (world : World) :
    (devm.setWorld world).createdAccounts = devm.createdAccounts := rfl

theorem Devm.setWorld_transientStorage (devm : Devm) (world : World) :
    (devm.setWorld world).transientStorage = world.transientStorage := rfl

theorem Devm.withOutput_stack (devm : Devm) (output : Bytes) :
    (devm.withOutput output).stack = devm.stack := rfl

theorem Devm.withOutput_memory (devm : Devm) (output : Bytes) :
    (devm.withOutput output).memory = devm.memory := rfl

theorem Devm.withOutput_logs (devm : Devm) (output : Bytes) :
    (devm.withOutput output).logs = devm.logs := rfl

theorem Devm.withOutput_refundCounter (devm : Devm) (output : Bytes) :
    (devm.withOutput output).refundCounter = devm.refundCounter := rfl

theorem Devm.withOutput_output (devm : Devm) (output : Bytes) :
    (devm.withOutput output).output = output := rfl

theorem Devm.withOutput_accountsToDelete (devm : Devm) (output : Bytes) :
    (devm.withOutput output).accountsToDelete = devm.accountsToDelete := rfl

theorem Devm.withOutput_returnData (devm : Devm) (output : Bytes) :
    (devm.withOutput output).returnData = devm.returnData := rfl

theorem Devm.withOutput_error (devm : Devm) (output : Bytes) :
    (devm.withOutput output).error = devm.error := rfl

theorem Devm.withOutput_accessedAddresses (devm : Devm) (output : Bytes) :
    (devm.withOutput output).accessedAddresses = devm.accessedAddresses := rfl

theorem Devm.withOutput_accessedStorageKeys (devm : Devm) (output : Bytes) :
    (devm.withOutput output).accessedStorageKeys = devm.accessedStorageKeys := rfl

theorem Devm.withOutput_state (devm : Devm) (output : Bytes) :
    (devm.withOutput output).state = devm.state := rfl

theorem Devm.withOutput_createdAccounts (devm : Devm) (output : Bytes) :
    (devm.withOutput output).createdAccounts = devm.createdAccounts := rfl

theorem Devm.withOutput_transientStorage (devm : Devm) (output : Bytes) :
    (devm.withOutput output).transientStorage = devm.transientStorage := rfl

def Devm.withAccountsToDelete (devm : Devm) (accountsToDelete : AdrSet) : Devm :=
  devm.setMeta {devm.meta with accountsToDelete := accountsToDelete}

def Devm.withReturnData (devm : Devm) (returnData : Bytes) : Devm :=
  devm.setMeta {devm.meta with returnData := returnData}

def Devm.withError (devm : Devm) (error : Option SettledHalt) : Devm :=
  devm.setMeta {devm.meta with error := error}

def Devm.withCreatedAccounts (devm : Devm) (createdAccounts : AdrSet) : Devm :=
  devm.setMeta {devm.meta with createdAccounts := createdAccounts}

def Devm.withState (devm : Devm) (state : State) : Devm :=
  devm.setWorld {devm.world with state := state}

def Devm.withStorageWrites (devm : Devm) (writes : KeySet) : Devm :=
  devm.setWorld {devm.world with storageWrites := writes}

def Devm.withTransientStorage (devm : Devm) (transientStorage : TransientStorage) : Devm :=
  devm.setWorld {devm.world with transientStorage := transientStorage}

-- Precompile activation is a fork rule and lives with the rules:
-- `ForkRules.isPrecomp` in `Jaune/Fork.lean` replaces what used to be a
-- hard-wired `1 ≤ a.toNat ∧ a.toNat ≤ 17` range stated here.

def safeSub {ξ} [Sub ξ] [LE ξ] [DecidableLE ξ] (x y : ξ) : Option ξ :=
  if y ≤ x then some (x - y) else none

abbrev Execution : Type := Except (EvmError × Devm) Devm

/-- A normalized result for a footprint-restricted core.  Both branches retain
    the core mutable state so a lift can reattach changes made before an error. -/
abbrev Footprint.Outcome (σ α : Type) : Type :=
  Except (EvmError × σ) (α × σ)

namespace Footprint

/-- Lift a normalized core outcome by projecting and reattaching its mutable
    state to the original flat `Devm`. -/
def liftOutcome (get : Devm → σ) (set : Devm → σ → Devm)
    (core : σ → Outcome σ α) (devm : Devm) :
    Except (EvmError × Devm) (α × Devm) :=
  match core (get devm) with
  | .error (err, view) => .error (err, set devm view)
  | .ok (value, view) => .ok (value, set devm view)

/-- Forget the unit payload of a lifted normalized outcome. -/
def toExecution (outcome : Except (EvmError × Devm) (Unit × Devm)) : Execution :=
  match outcome with
  | .error err => .error err
  | .ok (_, devm) => .ok devm

end Footprint

/-- Lift a Mach-only payload core. -/
def liftMach (core : Mach → Footprint.Outcome Mach α) (devm : Devm) :
    Except (EvmError × Devm) (α × Devm) :=
  Footprint.liftOutcome Devm.mach Devm.setMach core devm

/-- Lift a pure Mach-only update. -/
def liftMachPure (core : Mach → Mach) (devm : Devm) : Devm :=
  devm.setMach (core devm.mach)

/-- Lift a normalized Mach-only core to `Execution`. -/
def liftMachExecution (core : Mach → Footprint.Outcome Mach Unit)
    (devm : Devm) : Execution :=
  Footprint.toExecution (liftMach core devm)

/-- Lift a Mach+Meta payload core.  The mutable output contains no `World`. -/
def liftMachMeta
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) α)
    (devm : Devm) : Except (EvmError × Devm) (α × Devm) :=
  Footprint.liftOutcome
    (fun d => (d.mach, d.meta))
    (fun d view => { d with mach := view.1, «meta» := view.2 })
    (fun view => core view.1 view.2) devm

/-- Lift a pure Mach+Meta update. -/
def liftMachMetaPure (core : Mach → Meta → Mach × Meta) (devm : Devm) : Devm :=
  let view := core devm.mach devm.meta
  { devm with mach := view.1, «meta» := view.2 }

/-- Lift a normalized Mach+Meta core to `Execution`. -/
def liftMachMetaExecution
    (core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit)
    (devm : Devm) : Execution :=
  Footprint.toExecution (liftMachMeta core devm)

/-- Lift a normalized Mach+Meta core with read-only `World` access to
    `Execution`. -/
def liftMachMetaWorldExecution
    (core : World → Mach → Meta → Footprint.Outcome (Mach × Meta) Unit)
    (devm : Devm) : Execution :=
  liftMachMetaExecution (core devm.world) devm

def Mach.chargeGas (cost : Nat) (mach : Mach) : Footprint.Outcome Mach Unit :=
  match safeSub mach.gasLeft cost with
  | none => .error (.halt (.outOfGas .none), mach)
  | some gas => .ok ((), {mach with gasLeft := gas})

def chargeGas (cost : Nat) (devm : Devm) : Execution :=
  liftMachExecution (Mach.chargeGas cost) devm

/-- All but one sixty-fourth (EIP-150). Defined here rather than beside the
call opcodes because `Mach.withholdCreateGas` below is its first reader. -/
def except64th (n : Nat) : Nat := n - (n / 64)

/-- The termination measure the interpreter's totality argument rests on under
two reservoirs: execution gas that can still fund a step, plus the spill a
refund or a rollback can hand back to it.

The *reservoir* is deliberately outside the sum. State gas cannot pay for an
interpreter step until it spills into `gasLeft`, and a reservoir charge can be
refunded later, so counting it would make the measure rise for a reason that has
nothing to do with progress. The outstanding spill is inside the sum for the
mirror-image reason: without it, `creditStateGasRefund` would look like an
increase in `gasLeft` (`DualGasProbe.executionGas_alone_can_increase` is the
standing witness that it can be), when nothing about the frame's ability to
keep running has improved.

Under `rules.stateGas = none` the meter is `zero`, so this is `gasLeft` and
every Prague-stated decrease is the decrease it always was. -/
def Mach.gasMeasure (mach : Mach) : Nat :=
  mach.gasLeft + mach.stateGas.spilled + mach.stateGas.committedSpill

def Devm.gasMeasure (devm : Devm) : Nat := devm.mach.gasMeasure

theorem Devm.gasMeasure_def (devm : Devm) :
    devm.gasMeasure
      = devm.gasLeft + devm.mach.stateGas.spilled
          + devm.mach.stateGas.committedSpill := rfl

/-- On a zero meter the measure is exactly `gasLeft`. This is the bridge every
Prague-stated termination fact crosses. -/
@[simp] theorem Mach.gasMeasure_of_stateGas_zero {mach : Mach}
    (h : mach.stateGas = .zero) : mach.gasMeasure = mach.gasLeft := by
  simp [Mach.gasMeasure, h, StateGasMeter.zero]

@[simp] theorem Devm.gasMeasure_of_stateGas_zero {devm : Devm}
    (h : devm.mach.stateGas = .zero) : devm.gasMeasure = devm.gasLeft :=
  Mach.gasMeasure_of_stateGas_zero h

/-! ### The EIP-8037 meter operations

One definition per upstream `vm/gas.py` function, in upstream's order, each with
the lemma that says what it does to `Mach.gasMeasure`. The measure is
`gasLeft + spilled + committedSpill`: execution gas that can still fund
interpreter steps, plus the spill a refund or rollback can hand back to it. The
*reservoir* is deliberately outside it -- state gas cannot fund a step until it
spills, and a reservoir charge can be refunded, so counting it would make the
measure non-monotone for the wrong reason. `Jaune.DualGasProbe` established this
choice at the two hardest sites before any of it was written.

Every one of these runs only under `rules.stateGas = some _`. Under `none` the
meter is `StateGasMeter.zero` and stays there (`stateGasZero` below), so
`gasMeasure` is `gasLeft` and every Prague-stated termination fact is the fact
it always was. -/

/-- `charge_state_gas_from_meter`: draw from the reservoir, then spill into
execution gas, recording the spill. Out of gas only when neither pool can
cover the charge. -/
def Mach.chargeStateGas (amount : Nat) (mach : Mach) :
    Footprint.Outcome Mach Unit :=
  if amount ≤ mach.stateGas.left then
    .ok ((), { mach with
      stateGas := { mach.stateGas with left := mach.stateGas.left - amount } })
  else if amount - mach.stateGas.left ≤ mach.gasLeft then
    .ok ((), { mach with
      gasLeft := mach.gasLeft - (amount - mach.stateGas.left)
      stateGas := { mach.stateGas with
        left := 0
        spilled := mach.stateGas.spilled + (amount - mach.stateGas.left) } })
  else
    .error (.halt (.outOfGas .none), mach)

/-- `credit_state_gas_refund`: repay in LIFO order -- the spill that `gasLeft`
funded first, then the reservoir. This returns gas to exactly the pools the
charge drew it from, which is what keeps the two dimensions from drifting. -/
def Mach.creditStateGasRefund (amount : Nat) (mach : Mach) : Mach :=
  let m := mach.stateGas
  let fromGasLeft := min amount m.spilled
  { mach with
    gasLeft := mach.gasLeft + fromGasLeft
    stateGas := { m with
      left := m.left + (amount - fromGasLeft)
      spilled := m.spilled - fromGasLeft } }

/-- `commit_state_gas`: mark everything spent so far non-refillable. The
baseline drops to the current reservoir level and the outstanding spill folds
into `committedSpill`, so a later `restoreStateGas` leaves the state it bought
paid for. Only the top frame commits, and only after `set_delegation`. -/
def Mach.commitStateGas (mach : Mach) : Mach :=
  let m := mach.stateGas
  { mach with stateGas :=
      { m with
        left := m.left
        baseline := m.left
        spilled := 0
        committedSpill := m.committedSpill + m.spilled } }

/-- `restore_state_gas`: roll the frame's state gas back to the baseline on a
revert or a halt. LIFO again: the spill returns to `gasLeft`, then the
reservoir resets. Committed spill stays charged.

Upstream also zeroes the refund counter here, because its counter lives on the
meter; Jaune's lives on `Meta`, so `Devm.restoreStateGas` below does that half.
Splitting it this way is what keeps `Mach`'s operations pure functions of
`Mach`, which is what the measure lemmas need. -/
def Mach.restoreStateGas (mach : Mach) : Mach :=
  let m := mach.stateGas
  { mach with
    gasLeft := mach.gasLeft + m.spilled
    stateGas := { m with left := m.baseline, spilled := 0 } }

/-- `restore_state_gas_to_entry`: roll back to frame entry, undoing a commit.
Every spill, committed or not, returns to `gasLeft`, and both reservoir levels
reset to the frame's grant. Used only when the state rollback also reverts the
delegations a commit was protecting. -/
def Mach.restoreStateGasToEntry (grant : Nat) (mach : Mach) : Mach :=
  let m := mach.stateGas
  { mach with
    gasLeft := mach.gasLeft + m.spilled + m.committedSpill
    stateGas :=
      { left := grant, baseline := grant, spilled := 0, committedSpill := 0 } }

/-- `forfeit_remaining_gas`: an exceptionally halted frame returns no execution
gas. Upstream asserts that the spill is already zero here, which holds because
`restore_state_gas` always precedes it; the Jaune statement of that assertion is
`forfeitRemainingGas_gasMeasure_of_spilled_zero` below. -/
def Mach.forfeitRemainingGas (mach : Mach) : Mach :=
  { mach with gasLeft := 0 }

/-- `withhold_create_gas`: hand a `CREATE*` child all but one sixty-fourth of
the frame's execution gas, and return what was withheld. -/
def Mach.withholdCreateGas (mach : Mach) : Nat × Mach :=
  let child := except64th mach.gasLeft
  (child, { mach with gasLeft := mach.gasLeft - child })

/-- `drain_state_gas_reservoir`: a child receives the parent's *whole*
reservoir. There is no all-but-one-64th rule for state gas, and the parent's
reservoir comes back when the child returns. -/
def Mach.drainStateGasReservoir (mach : Mach) : Nat × Mach :=
  (mach.stateGas.left,
   { mach with stateGas := { mach.stateGas with left := 0 } })

/-- `restore_child_gas`: return a child's untouched grants when the child is
never entered -- a depth limit or a balance check refused before the spawn. -/
def Mach.restoreChildGas (gas reservoir : Nat) (mach : Mach) : Mach :=
  { mach with
    gasLeft := mach.gasLeft + gas
    stateGas :=
      { mach.stateGas with left := mach.stateGas.left + reservoir } }

/-- `repay_state_gas_spill`, introduced at the historical devnet-8 revision (#3478).

A refund can land in a different frame than the charge it undoes: the
refunding frame's spill may be smaller than the refund, so the excess credits
the reservoir while the `gasLeft` that funded the charge stays reduced. A
successful merge is where the claim and the credit first share one meter, so
the reservoir repays `gasLeft` up to the spill still outstanding. Nothing is
un-created, so no used counter moves -- gas only crosses back between the two
pools it drifted across. -/
def Mach.repayStateGasSpill (mach : Mach) : Mach :=
  let m := mach.stateGas
  let repayment := min m.left m.spilled
  { mach with
    gasLeft := mach.gasLeft + repayment
    stateGas :=
      { m with left := m.left - repayment, spilled := m.spilled - repayment } }

/-! ### What each meter operation does to the measure

One lemma per operation of the block above, and together they are the whole
arithmetic content of the migration: a state-gas operation is measure-*neutral*,
an execution charge is measure-*decreasing* by exactly what it charges, and a
spawn conserves the measure across the parent/child pair. Everything the
termination argument has to know about two reservoirs is here; the sites above
`MessageOp.step` then only have to say which operations they perform.

`Jaune.DualGasProbe` proved these same five shapes on a bounded model before any
of this existed, and its `executionGas_alone_can_increase` is why the measure
is not simply `gasLeft`. -/

theorem Mach.chargeGas_gasMeasure {cost : Nat} {mach mach' : Mach} {u : Unit}
    (h : Mach.chargeGas cost mach = .ok (u, mach')) :
    mach'.gasMeasure + cost = mach.gasMeasure := by
  unfold Mach.chargeGas safeSub at h
  by_cases hle : cost ≤ mach.gasLeft
  · simp only [ite_eq_left hle, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    simp only [Mach.gasMeasure]
    omega
  · exact absurd h (by simp [ite_eq_right hle])

/-- A state charge is measure-neutral in both of its branches: a reservoir draw
moves nothing the measure counts, and a spill moves exactly as much out of
`gasLeft` as it records in `spilled`. -/
theorem Mach.chargeStateGas_gasMeasure {amount : Nat} {mach mach' : Mach}
    {u : Unit} (h : Mach.chargeStateGas amount mach = .ok (u, mach')) :
    mach'.gasMeasure = mach.gasMeasure := by
  unfold Mach.chargeStateGas at h
  split at h
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    rfl
  · split at h
    · simp only [Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      simp only [Mach.gasMeasure]
      omega
    · exact absurd h (by simp)

/-- A refund repays `gasLeft` and the reservoir between them, and the part that
reaches `gasLeft` is exactly the part that leaves `spilled`. -/
theorem Mach.creditStateGasRefund_gasMeasure (amount : Nat) (mach : Mach) :
    (mach.creditStateGasRefund amount).gasMeasure = mach.gasMeasure := by
  simp only [Mach.creditStateGasRefund, Mach.gasMeasure]
  have : min amount mach.stateGas.spilled ≤ mach.stateGas.spilled := by
    exact Nat.min_le_right _ _
  omega

/-- A commit moves spill into committed spill. Both are inside the measure, so
it moves nothing. -/
theorem Mach.commitStateGas_gasMeasure (mach : Mach) :
    mach.commitStateGas.gasMeasure = mach.gasMeasure := by
  simp only [Mach.commitStateGas, Mach.gasMeasure]
  omega

/-- A rollback to the baseline hands the outstanding spill back to `gasLeft`.
Neutral, again because the spill was already counted. -/
theorem Mach.restoreStateGas_gasMeasure (mach : Mach) :
    mach.restoreStateGas.gasMeasure = mach.gasMeasure := by
  simp only [Mach.restoreStateGas, Mach.gasMeasure]
  omega

/-- A rollback to frame entry hands back committed spill as well. -/
theorem Mach.restoreStateGasToEntry_gasMeasure (grant : Nat) (mach : Mach) :
    (mach.restoreStateGasToEntry grant).gasMeasure = mach.gasMeasure := by
  simp only [Mach.restoreStateGasToEntry, Mach.gasMeasure]
  omega

/-- Forfeiting never raises the measure. -/
theorem Mach.forfeitRemainingGas_gasMeasure_le (mach : Mach) :
    mach.forfeitRemainingGas.gasMeasure ≤ mach.gasMeasure := by
  simp only [Mach.forfeitRemainingGas, Mach.gasMeasure]
  omega

/-- Upstream asserts that the spill is already zero when a frame forfeits,
because `restore_state_gas` always runs first. Under that hypothesis the
measure after forfeiting is exactly the committed spill -- which is the
statement a caller needs, and the reason the assertion is worth carrying. -/
theorem Mach.forfeitRemainingGas_gasMeasure_of_spilled_zero {mach : Mach}
    (h : mach.stateGas.spilled = 0) :
    mach.forfeitRemainingGas.gasMeasure = mach.stateGas.committedSpill := by
  simp only [Mach.forfeitRemainingGas, Mach.gasMeasure, h]
  omega

/-- Withholding a create child's grant splits the measure exactly: what the
parent keeps plus what the child receives is what the parent had. -/
theorem Mach.withholdCreateGas_gasMeasure (mach : Mach) :
    mach.withholdCreateGas.2.gasMeasure + mach.withholdCreateGas.1
      = mach.gasMeasure := by
  simp only [Mach.withholdCreateGas, Mach.gasMeasure, except64th]
  omega

/-- Draining the reservoir into a child is measure-neutral: the reservoir is
outside the measure on both sides. This is exactly why the reservoir is
excluded -- a rule that hands a child *everything* would otherwise look like a
collapse of the parent's budget. -/
theorem Mach.drainStateGasReservoir_gasMeasure (mach : Mach) :
    mach.drainStateGasReservoir.2.gasMeasure = mach.gasMeasure := by
  simp only [Mach.drainStateGasReservoir, Mach.gasMeasure]

/-- Returning an un-entered child's grants raises the measure by exactly the
execution gas returned; the reservoir is outside it. -/
theorem Mach.restoreChildGas_gasMeasure (gas reservoir : Nat) (mach : Mach) :
    (mach.restoreChildGas gas reservoir).gasMeasure = mach.gasMeasure + gas := by
  simp only [Mach.restoreChildGas, Mach.gasMeasure]
  omega

/-- The repay-on-merge rule moves gas from the reservoir to `gasLeft`
while cancelling an equal amount of spill. Neutral. -/
theorem Mach.repayStateGasSpill_gasMeasure (mach : Mach) :
    mach.repayStateGasSpill.gasMeasure = mach.gasMeasure := by
  simp only [Mach.repayStateGasSpill, Mach.gasMeasure]
  have : min mach.stateGas.left mach.stateGas.spilled ≤ mach.stateGas.spilled :=
    Nat.min_le_right _ _
  omega

/-! ### The same operations, at the frame

`Devm` wrappers over the `Mach` operations above, in the shape the interpreter
calls them. Two of them are more than a lift: `restoreStateGas` also discards
the frame's refunds, because upstream's refund counter lives on the meter and
Jaune's lives on `Meta`. -/
/-- `charge_state_gas`, at the frame. Reservoir first, then spill into
execution gas. Reached only under `rules.stateGas = some _`. -/
def chargeStateGas (amount : Nat) (devm : Devm) : Execution :=
  liftMachExecution (Mach.chargeStateGas amount) devm

/-- `credit_state_gas_refund`, at the frame. Total, because a refund cannot
fail. -/
def Devm.creditStateGasRefund (amount : Nat) (devm : Devm) : Devm :=
  devm.setMach (devm.mach.creditStateGasRefund amount)

/-- `commit_state_gas`, at the frame. -/
def Devm.commitStateGas (devm : Devm) : Devm :=
  devm.setMach devm.mach.commitStateGas

/-- `restore_state_gas`, at the frame. Upstream's counter lives on the meter and
Jaune's on `Meta`, so the refund discard is here rather than in `Mach`. -/
def Devm.restoreStateGas (devm : Devm) : Devm :=
  (devm.setMach devm.mach.restoreStateGas).withRefundCounter 0

/-- `restore_state_gas_to_entry`, at the frame. -/
def Devm.restoreStateGasToEntry (grant : Nat) (devm : Devm) : Devm :=
  devm.setMach (devm.mach.restoreStateGasToEntry grant)

/-- `forfeit_remaining_gas`, at the frame. -/
def Devm.forfeitRemainingGas (devm : Devm) : Devm :=
  devm.setMach devm.mach.forfeitRemainingGas

/-- `drain_state_gas_reservoir`, at the frame. -/
def Devm.drainStateGasReservoir (devm : Devm) : Nat × Devm :=
  let ⟨reservoir, mach⟩ := devm.mach.drainStateGasReservoir
  (reservoir, devm.setMach mach)

/-- `restore_child_gas`, at the frame. -/
def Devm.restoreChildGas (gas reservoir : Nat) (devm : Devm) : Devm :=
  devm.setMach (devm.mach.restoreChildGas gas reservoir)

/-- `withhold_create_gas`, at the frame. -/
def Devm.withholdCreateGas (devm : Devm) : Nat × Devm :=
  let ⟨child, mach⟩ := devm.mach.withholdCreateGas
  (child, devm.setMach mach)

theorem chargeGas_def (cost : Nat) (devm : Devm) :
    chargeGas cost devm = (do
      match safeSub devm.gasLeft cost with
      | none => .error ⟨.halt (.outOfGas .none), devm⟩
      | some gas => .ok (devm.setMach {devm.mach with gasLeft := gas})) := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  simp only [chargeGas, Mach.chargeGas, liftMachExecution, liftMach,
    Footprint.toExecution, Footprint.liftOutcome, Devm.setMach, Devm.gasLeft]
  cases safeSub gasLeft cost <;> rfl

/-- EIP-8024's `decode_single` (`vm/stack.py`): the immediate byte of `DUPN`
and `SWAPN`. Accepted immediates are `0x00–0x5A` and `0x80–0xFF`, decoding to
`(x + 145) % 256`, which is `17 ≤ n ≤ 235`; the forbidden range `0x5B–0x7F` --
`JUMPDEST` and every `PUSH1`–`PUSH32` byte -- is `none`, which the interpreter
answers with an invalid-instruction halt (the pinned `InvalidParameter`). The
forbidden range is what keeps the jump-destination analysis unchanged: see
`pinnedJumpDests_eq_legacy` below. -/
def decodeSingle (x : UInt8) : Option Nat :=
  if x ≤ 0x5A ∨ 0x80 ≤ x then some ((x.toNat + 145) % 256) else none

/-- EIP-8024's `decode_pair`: the immediate byte of `EXCHANGE`. Accepted
immediates are `0x00–0x51` and `0x80–0xFF`; `k = x ^ 143`, `(q, r) = divmod k
16`, and the pair is `(q + 1, r + 1)` when `q < r` and `(r + 1, 29 - q)`
otherwise, giving `1 ≤ n ≤ 14` and `n < m ≤ 30 - n`. -/
def decodePair (x : UInt8) : Option (Nat × Nat) :=
  if x ≤ 0x51 ∨ 0x80 ≤ x then
    let k := x.toNat ^^^ 143
    let q := k / 16
    let r := k % 16
    some (if q < r then (q + 1, r + 1) else (r + 1, 29 - q))
  else none

/-- The byte at `i`, or `0` past the end of code: the pinned `buffer_read`'s
zero fill, which is how an immediate is read when the opcode is the last
byte. -/
def ByteArray.byteD (code : ByteArray) (i : Nat) : UInt8 :=
  if h : i < code.size then code[i] else 0

inductive NextOp : Type
  | plain : PlainOp → NextOp
  | message : MessageOp → NextOp
  | push : ∀ bs : Bytes, bs.length ≤ 32 → NextOp
  /-- EIP-8024 `DUPN` (0xE6) with its one immediate byte, undecoded: decoding
  happens at execution, where a forbidden immediate is an exceptional halt. -/
  | dupn : UInt8 → NextOp
  /-- EIP-8024 `SWAPN` (0xE7) with its immediate byte. -/
  | swapn : UInt8 → NextOp
  /-- EIP-8024 `EXCHANGE` (0xE8) with its immediate byte. -/
  | exchange : UInt8 → NextOp
deriving DecidableEq

def NextOp.toOpString : NextOp → String
  | plain o => PlainOp.toString o
  | message o => MessageOp.toString o
  | push bs _ => "PUSH" ++ bs.length.repr
  | dupn _ => "DUPN"
  | swapn _ => "SWAPN"
  | exchange _ => "EXCHANGE"

def NextOp.toString : NextOp → String
  | plain o => PlainOp.toString o
  | message o => MessageOp.toString o
  | push [] _ => "PUSH0"
  | push bs _ => "PUSH" ++ bs.length.repr ++ " " ++ Bytes.toHex bs
  | dupn i => "DUPN " ++ Bytes.toHex [i]
  | swapn i => "SWAPN " ++ Bytes.toHex [i]
  | exchange i => "EXCHANGE " ++ Bytes.toHex [i]

instance : ToString NextOp := ⟨NextOp.toString⟩
instance : Repr NextOp := ⟨λ i _ => i.toString⟩

lemma NextOp.push_ext {xs ys : Bytes}
    (le : xs.length ≤ 32) (le' : ys.length ≤ 32) (eq : xs = ys) :
    NextOp.push xs le = NextOp.push ys le' := by
  revert le le'; rw [eq]; simp

inductive Op : Type
  | halt : HaltOp → Op
  | next : NextOp → Op
  | jump : JumpOp → Op

inductive OpClass
  | plain | message | jump | halt | push
deriving DecidableEq

def UInt8.toOpClass (b : UInt8) : OpClass :=
  match b.highs with
  | 0x00 => if b.lows = 0x00 then .halt else .plain
  | 0x05 =>
    match b.lows with
    | 0x06 => .jump
    | 0x07 => .jump
    | 0x0B => .jump
    | 0x0F => .push
    | _ => .plain
  | 0x06 => .push
  | 0x07 => .push
  | 0x0F =>
    match b.lows with
    | 0x03 => .halt
    | 0x0D => .halt
    | 0x0F => .halt
    | _ => .message
  | _ => .plain

lemma HaltOp.toOpClass_toUInt8 (l : HaltOp) : l.toUInt8.toOpClass = .halt := by
  cases l <;> rfl

lemma JumpOp.toOpClass_toUInt8 (j : JumpOp) : j.toUInt8.toOpClass = .jump := by
  cases j <;> rfl

lemma UInt8.lt_of_highs_lt_highs (x y : UInt8) (lt : x.highs < y.highs) : x < y := by
  rw [UInt8.lt_iff_toNat_lt]
  have lt' : x.toNat < (x.toNat ↿ 4) + 16 := by
    conv => lhs; rw [← Nat.hi_or_lo x.toNat 4]; rfl
    rw [← @Nat.add_eq_or 4]
    · rw [Nat.add_lt_add_iff_left]; apply Nat.lo_lt
    · apply Nat.two_pow_dvd_shl
    · apply Nat.lo_lt
  have le : (x.toNat ↿ 4) + 16 ≤ (y.toNat ↿ 4) := by
    simp only [Nat.hi]
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have rw : 16 = 2 ^ 4 := by rfl
    conv => lhs; arg 2; rw [rw]; rfl
    clear rw;
    rw [← Nat.succ_mul (x.toNat >>> 4) (2 ^ 4)]
    rw [Nat.mul_le_mul_right_iff (by omega)]
    apply Nat.succ_le_of_lt lt
  have le' : (y.toNat ↿ 4) ≤ y.toNat := Nat.hi_le _ _
  apply Nat.lt_of_lt_of_le lt' <| Nat.le_trans le le'

lemma le_of_toOpClass_eq_p (b : UInt8) (h : b.toOpClass = .push) :
    b.toNat ≤ 127 := by
  apply Nat.le_of_lt_succ
  apply (@UInt8.lt_iff_toNat_lt b 0x80).mp
  apply UInt8.lt_of_highs_lt_highs
  simp [UInt8.toOpClass] at h; split at h
  · split at h <;> cases h
  · rename (UInt8.highs _ =  _) => heq; rw [heq]
    apply (@UInt8.lt_iff_toNat_lt 5 8).mpr; simp
  · rename (UInt8.highs _ =  _) => heq; rw [heq]
    apply (@UInt8.lt_iff_toNat_lt 6 8).mpr; simp
  · rename (UInt8.highs _ =  _) => heq; rw [heq]
    apply (@UInt8.lt_iff_toNat_lt 7 8).mpr; simp
  · split at h <;> cases h
  · cases h

def ByteArray.getOp (code : ByteArray) (pc : Nat) : Option Op :=
  if hpc : pc < code.size
  then
    let b : UInt8 := code[pc]
    match h : b.toOpClass with
    | .plain =>
      -- EIP-8024's three stack-access instructions carry one immediate byte
      -- and are sized here, fork-independently, exactly as `push` is (D8):
      -- whether they are *defined* is `rules.op.stackAccess`, checked where
      -- they run. The immediate is read zero-filled past the end of code.
      match b with
      | 0xE6 => some (.next (.dupn (code.byteD (pc + 1))))
      | 0xE7 => some (.next (.swapn (code.byteD (pc + 1))))
      | 0xE8 => some (.next (.exchange (code.byteD (pc + 1))))
      | _ => b.toPlainOp <&> (.next ∘ .plain)
    | .message => b.toMessageOp <&> (.next ∘ .message)
    | .jump => b.toJumpOp <&> .jump
    | .halt => b.toHaltOp <&> .halt
    | .push =>
      let le := le_of_toOpClass_eq_p b h
      let bs : Bytes := code.sliceD (pc + 1) (b.toNat - 95) 0
      let le' : bs.length ≤ 32 := by
        simp [bs, ByteArray.length_sliceD, le]
      some <| .next <| .push bs le'
  else
    some (.halt .stop)

def Evm.getInst (evm : Evm) : Option Op :=
  ByteArray.getOp evm.sta.code evm.pc

/-- EELS `taylor_exponential`'s accumulator loop as a *well-founded* recursion
(P0.6 item 1): `fakeExpAux num den i numAcc` is the sum of the series continued
from state `(i, numAcc)`. There is no fuel and no failure branch.

Termination is by the lexicographic measure `(num + 1 - i, numAcc)`: while
`i ≤ num` the first component falls; once `i > num`, either `den * i = 0` (a
zero denominator — excluded from the semantic domain by `BlobSchedule.Valid` —
zeroes the accumulator immediately under `Nat` division) or `num < den * i`
strictly shrinks a positive accumulator. -/
def fakeExponentialAux (num den i numAcc : Nat) : Nat :=
  if _h : numAcc = 0 then 0
  else numAcc + fakeExponentialAux num den (i + 1) (numAcc * num / (den * i))
termination_by (num + 1 - i, numAcc)
decreasing_by
  rcases Nat.lt_or_ge i (num + 1) with hi | hi
  · exact Prod.Lex.left _ _ (by omega)
  · have h0 : num + 1 - i = 0 := by omega
    have h1 : num + 1 - (i + 1) = 0 := by omega
    rw [h0, h1]
    apply Prod.Lex.right
    rcases Nat.eq_zero_or_pos (den * i) with hd | hd
    · rw [hd, Nat.div_zero]
      exact Nat.pos_of_ne_zero _h
    · rw [Nat.div_lt_iff_lt_mul hd]
      have hden : 0 < den := Nat.pos_of_ne_zero (by rintro rfl; simp at hd)
      have hlt : num < den * i := by
        have hle : i ≤ den * i := Nat.le_mul_of_pos_left i hden
        omega
      exact mul_lt_mul_of_pos_left hlt (Nat.pos_of_ne_zero _h)

@[simp] theorem fakeExponentialAux_zero (num den i : Nat) :
    fakeExponentialAux num den i 0 = 0 := by
  unfold fakeExponentialAux
  simp

/-- The EELS recurrence equation — for *every* `Nat` numerator, including the
U64 maximum; nothing here evaluates the series. -/
theorem fakeExponentialAux_succ {numAcc : Nat} (h : numAcc ≠ 0) (num den i : Nat) :
    fakeExponentialAux num den i numAcc
      = numAcc + fakeExponentialAux num den (i + 1) (numAcc * num / (den * i)) := by
  conv_lhs => unfold fakeExponentialAux
  simp [h]

/-- The EELS accumulator recurrence as a predicate on candidate functions:
`f i numAcc` plays the role of the series sum continued from `(i, numAcc)`. -/
def FakeExponentialSpec (num den : Nat) (f : Nat → Nat → Nat) : Prop :=
  (∀ i, f i 0 = 0) ∧
  ∀ i numAcc, numAcc ≠ 0 →
    f i numAcc = numAcc + f (i + 1) (numAcc * num / (den * i))

/-- `fakeExpAux` satisfies the recurrence. -/
theorem fakeExponentialAux_spec (num den : Nat) :
    FakeExponentialSpec num den (fakeExponentialAux num den) :=
  ⟨fakeExponentialAux_zero num den,
   fun i numAcc h => fakeExponentialAux_succ (numAcc := numAcc) h num den i⟩

/-- Uniqueness: the recurrence has exactly one solution, so `fakeExpAux` is
*the* EELS accumulator function. -/
theorem fakeExponentialAux_spec_unique {num den : Nat} {f : Nat → Nat → Nat}
    (hf : FakeExponentialSpec num den f) : f = fakeExponentialAux num den := by
  funext i numAcc
  induction i, numAcc using fakeExponentialAux.induct num den with
  | case1 i => rw [hf.1, fakeExponentialAux_zero]
  | case2 i numAcc h ih => rw [hf.2 i numAcc h, ih, ← fakeExponentialAux_succ h]

/-- The pre-integrity fuelled worker as a *total* `Option`-valued reference:
`none` exactly where the old implementation exhausted its guessed fuel bound.
This is the only sanctioned old/new bridge; nothing executes it. -/
def fakeExponentialAuxRef? (num den i : Nat) : Nat → Nat → Option Nat
  | _, 0 => none
  | 0, _ => some 0
  | numAcc, fuel + 1 =>
    (fakeExponentialAuxRef? num den (i + 1) (numAcc * num / (den * i)) fuel).map
      (numAcc + ·)

/-- The accumulator sequence from `(i, numAcc)` reaches zero strictly before
the fuel runs out — the precise domain on which the old worker answered. -/
def reachesZeroBeforeFuel (num den : Nat) : Nat → Nat → Nat → Bool
  | _, _, 0 => false
  | _, 0, _ => true
  | i, numAcc, fuel + 1 =>
    reachesZeroBeforeFuel num den (i + 1) (numAcc * num / (den * i)) fuel

/-- The reference worker answers exactly on `reachesZeroBeforeFuel`. -/
theorem fakeExponentialAuxRef?_isSome (num den : Nat) :
    ∀ fuel i numAcc, (fakeExponentialAuxRef? num den i numAcc fuel).isSome
      = reachesZeroBeforeFuel num den i numAcc fuel := by
  intro fuel
  induction fuel with
  | zero => intro i numAcc; cases numAcc <;> rfl
  | succ fuel ih =>
    intro i numAcc
    cases numAcc with
    | zero => rfl
    | succ n => simp [fakeExponentialAuxRef?, reachesZeroBeforeFuel, ih]

/-- Wherever the old fuelled computation completed, it computed exactly the
total well-founded value. -/
theorem fakeExponentialAuxRef?_eq_some {num den : Nat} :
    ∀ {fuel i numAcc}, reachesZeroBeforeFuel num den i numAcc fuel = true →
      fakeExponentialAuxRef? num den i numAcc fuel
        = some (fakeExponentialAux num den i numAcc) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i numAcc h
    cases numAcc <;> simp [reachesZeroBeforeFuel] at h
  | succ fuel ih =>
    intro i numAcc h
    cases numAcc with
    | zero => simp [fakeExponentialAuxRef?]
    | succ n =>
      rw [fakeExponentialAux_succ (Nat.succ_ne_zero n)]
      simp only [fakeExponentialAuxRef?]
      rw [ih (by simpa [reachesZeroBeforeFuel] using h)]
      rfl

/-- EELS `taylor_exponential`: approximates `fac * e ^ (num / den)`. Total for
every input; the semantic domain additionally demands a positive denominator
through `BlobSchedule.Valid`. -/
def fakeExponential (fac num den : Nat) : Nat :=
  fakeExponentialAux num den 1 (fac * den) / den

def getBaseFeePerBlobGas (blob : BlobSchedule) (excessBlobGas : Nat) : Nat :=
  fakeExponential 1 excessBlobGas blob.baseFeeUpdateFraction

/-- The public EELS `calculate_blob_gas_price` equation, through the
recurrence function rather than through evaluation (`MIN_BLOB_GASPRICE = 1`). -/
theorem calculateBlobGasPrice_eq (blob : BlobSchedule) (excess : Nat) :
    getBaseFeePerBlobGas blob excess
      = fakeExponentialAux excess blob.baseFeeUpdateFraction 1
          (1 * blob.baseFeeUpdateFraction) / blob.baseFeeUpdateFraction := rfl

/-- Under a validated schedule the denominator is positive and the price is
the value of the *unique* solution of the EELS recurrence — for every `Nat`
excess. Nothing here evaluates the series. -/
theorem calculateBlobGasPrice_spec (blob : BlobSchedule) (hv : blob.Valid)
    (excess : Nat) :
    0 < blob.baseFeeUpdateFraction ∧
    ∀ f, FakeExponentialSpec excess blob.baseFeeUpdateFraction f →
      getBaseFeePerBlobGas blob excess
        = f 1 (1 * blob.baseFeeUpdateFraction) / blob.baseFeeUpdateFraction := by
  refine ⟨hv.1, fun f hf => ?_⟩
  rw [calculateBlobGasPrice_eq, fakeExponentialAux_spec_unique hf]

/-- The U64-maximum numerator, pinned explicitly: the acceptance case the plan
forbids executing is covered by the non-evaluating theorem above. -/
theorem calculateBlobGasPrice_spec_u64max (blob : BlobSchedule)
    (hv : blob.Valid) :
    0 < blob.baseFeeUpdateFraction ∧
    ∀ f, FakeExponentialSpec (2 ^ 64 - 1) blob.baseFeeUpdateFraction f →
      getBaseFeePerBlobGas blob (2 ^ 64 - 1)
        = f 1 (1 * blob.baseFeeUpdateFraction) / blob.baseFeeUpdateFraction :=
  calculateBlobGasPrice_spec blob hv (2 ^ 64 - 1)

/-- The maximum `excessBlobGas` present in the pinned current-mainnet fixture
corpus (`0xfffffffffffe0000`, reached only by invalid-header fixtures that are
rejected before any price calculation), likewise pinned non-evaluatingly. -/
theorem calculateBlobGasPrice_spec_corpusMax (blob : BlobSchedule)
    (hv : blob.Valid) :
    0 < blob.baseFeeUpdateFraction ∧
    ∀ f, FakeExponentialSpec 0xfffffffffffe0000 blob.baseFeeUpdateFraction f →
      getBaseFeePerBlobGas blob 0xfffffffffffe0000
        = f 1 (1 * blob.baseFeeUpdateFraction) / blob.baseFeeUpdateFraction :=
  calculateBlobGasPrice_spec blob hv 0xfffffffffffe0000

def Mach.push (x : U256) (mach : Mach) : Footprint.Outcome Mach Unit :=
  if mach.stack.length < 1024
  then .ok ⟨(), {mach with stack := x :: mach.stack}⟩
  else .error ⟨.halt (.stackOverflow .none), mach⟩

def Devm.push (x : U256) (devm : Devm) : Execution :=
  liftMachExecution (Mach.push x) devm

theorem Devm.push_def (x : U256) (devm : Devm) : Devm.push x devm = (do
    .assert
      (devm.stack.length < 1024)
      ⟨.halt (.stackOverflow .none), devm⟩
    .ok (devm.setMach {devm.mach with stack := x :: devm.stack})) := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  simp only [Devm.push, Mach.push, liftMachExecution, liftMach, Footprint.toExecution,
    Footprint.liftOutcome, Devm.stack, Devm.setMach, Except.assert, bind, Except.bind]
  by_cases h : stack.length < 1024 <;> simp [h]

def Mach.pop (mach : Mach) : Footprint.Outcome Mach U256 :=
  match mach.stack with
  | [] => .error ⟨.halt (.stackUnderflow .none), mach⟩
  | x :: xs => .ok ⟨x, {mach with stack := xs}⟩

def Devm.pop (devm : Devm) : Except (EvmError × Devm) (U256 × Devm) :=
  liftMach Mach.pop devm

theorem Devm.pop_def (devm : Devm) : Devm.pop devm = (do
    match devm.stack with
    | [] => .error ⟨.halt (.stackUnderflow .none), devm⟩
    | x :: xs => .ok ⟨x, devm.setMach {devm.mach with stack := xs}⟩) := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  cases stack <;> rfl

def Prod.mapFst {α₁ : Type u₁} {α₂ : Type u₂} {β : Type v} (f : α₁ → α₂) : α₁ × β → α₂ × β :=
  Prod.map f id

def Mach.popToNat (mach : Mach) : Footprint.Outcome Mach Nat :=
  match mach.pop with
  | .error err => .error err
  | .ok ⟨x, mach'⟩ => .ok ⟨x.toNat, mach'⟩

def Devm.popToNat (devm : Devm) : Except (EvmError × Devm) (Nat × Devm) :=
  liftMach Mach.popToNat devm

theorem Devm.popToNat_def (devm : Devm) :
    devm.popToNat = (devm.pop <&> Prod.mapFst U256.toNat) := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  cases stack <;> rfl

def Mach.popToAdr (mach : Mach) : Footprint.Outcome Mach Address :=
  match mach.pop with
  | .error err => .error err
  | .ok ⟨x, mach'⟩ => .ok ⟨x.toAddress, mach'⟩

def Devm.popToAdr (devm : Devm) : Except (EvmError × Devm) (Address × Devm) :=
  liftMach Mach.popToAdr devm

theorem Devm.popToAdr_def (devm : Devm) :
    devm.popToAdr = (devm.pop <&> Prod.mapFst U256.toAddress) := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  cases stack <;> rfl

def Mach.popN (mach : Mach) : Nat → Footprint.Outcome Mach (List U256)
  | 0 => .ok ⟨[], mach⟩
  | n + 1 =>
    match mach.pop with
    | .error err => .error err
    | .ok ⟨x, mach'⟩ =>
      match mach'.popN n with
      | .error err => .error err
      | .ok ⟨xs, mach''⟩ => .ok ⟨x :: xs, mach''⟩

def Devm.popN (devm : Devm) (n : Nat) :
    Except (EvmError × Devm) (List U256 × Devm) :=
  liftMach (Mach.popN · n) devm

theorem Devm.popN_def (devm : Devm) (n : Nat) : devm.popN n =
    (match n with
    | 0 => .ok ⟨[], devm⟩
    | n + 1 => do
      let ⟨x, devm'⟩ ← devm.pop
      let ⟨xs, devm''⟩ ← devm'.popN n
      .ok ⟨x :: xs, devm''⟩) := by
  cases n with
  | zero => rfl
  | succ n =>
    rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
    cases stack with
    | nil => rfl
    | cons x xs =>
      cases h : Mach.popN
          { stack := xs, memory := memory, gasLeft := gasLeft,
            stateGas := stateGas } n with
      | error err =>
        rcases err with ⟨msg, mach'⟩
        cases mach'
        simp only [Devm.popN, Mach.popN, Mach.pop, liftMach, Footprint.liftOutcome,
          Devm.pop_def, Devm.stack, Devm.setMach, bind, Except.bind, h]
      | ok out =>
        rcases out with ⟨vals, mach'⟩
        cases mach'
        simp only [Devm.popN, Mach.popN, Mach.pop, liftMach, Footprint.liftOutcome,
          Devm.pop_def, Devm.stack, Devm.setMach, bind, Except.bind, h]

def Mach.pushItem (x : U256) (c : Nat) (mach : Mach) : Footprint.Outcome Mach Unit :=
  match Mach.chargeGas c mach with
  | .error err => .error err
  | .ok ⟨_, mach'⟩ => Mach.push x mach'

def pushItem (x : U256) (c : Nat) (devm : Devm) : Execution :=
  liftMachExecution (Mach.pushItem x c) devm

theorem pushItem_def (x : U256) (c : Nat) (devm : Devm) :
    pushItem x c devm = (chargeGas c devm >>= Devm.push x) := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  simp only [pushItem, Mach.pushItem, Mach.chargeGas, Mach.push, chargeGas, Devm.push,
    liftMachExecution, liftMach, Footprint.toExecution, Footprint.liftOutcome,
    Devm.setMach, bind, Except.bind]
  cases safeSub gasLeft c with
  | none => rfl
  | some gas => dsimp only

def accessCost (x : Address) (a : AdrSet) : Nat :=
  if x ∈ a then Gas.warmStorageReadCost else Gas.coldAccountAccessCost

/-- The warm/cold account-access cost under a *fork's own* schedule.

A sibling rather than a third parameter on `accessCost`. EIP-8038 reprices the
cold half (2,600 to 3,000) and leaves the warm half alone, so the interpreter
has to read the number from `rules.gas` -- but `accessCost` is named 121 times
downstream, and widening its arity would move every one of those statements for
a reason that has nothing to do with what they say. Instead the schedule-carrying
form is the one the interpreter calls, `accessCost` stays exactly what it was,
and the `rfl` lemma below says they are the same function at Prague. -/
def GasSchedule.accessCost (gas : GasSchedule) (x : Address) (a : AdrSet) : Nat :=
  if x ∈ a then Gas.warmStorageReadCost else gas.coldAccountAccess

@[simp] theorem pragueGasSchedule_accessCost (x : Address) (a : AdrSet) :
    pragueGasSchedule.accessCost x a = accessCost x a := rfl

@[simp] theorem pragueRules_gas_accessCost (x : Address) (a : AdrSet) :
    pragueRules.gas.accessCost x a = accessCost x a := rfl

/-- The warm cost is the floor at every schedule, because only the cold half
moves. The Sufficiency family needs this, and needs it to hold of an arbitrary
schedule rather than of Prague's. -/
theorem GasSchedule.gasWarmAccess_le_accessCost (gas : GasSchedule)
    (x : Address) (a : AdrSet) (h : Gas.warmStorageReadCost ≤ gas.coldAccountAccess) :
    Gas.warmStorageReadCost ≤ gas.accessCost x a := by
  unfold GasSchedule.accessCost
  split
  · exact Nat.le_refl _
  · exact h

/-- The account-access cost is positive under any usable schedule -- the shape
`access_cost_pos` had at Prague, now stated of the schedule the interpreter
actually reads. -/
theorem GasSchedule.Valid.accessCost_pos {g : GasSchedule} (h : g.Valid)
    (x : Address) (a : AdrSet) : 0 < g.accessCost x a := by
  unfold GasSchedule.accessCost
  have hw := h.warmAccess_le
  unfold Gas.warmStorageReadCost at *
  split <;> omega

theorem GasSchedule.Valid.warmAccess_le_accessCost {g : GasSchedule}
    (h : g.Valid) (x : Address) (a : AdrSet) : Gas.warmStorageReadCost ≤ g.accessCost x a :=
  g.gasWarmAccess_le_accessCost x a h.warmAccess_le

def Meta.addAccessedAddress (view : Meta) (a : Address) : Meta :=
  {view with accessedAddresses := view.accessedAddresses.insert a}

def addAccessedAddress (devm : Devm) (a : Address) : Devm :=
  liftMachMetaPure (fun mach view => (mach, view.addAccessedAddress a)) devm

def Meta.addAccessedStorageKey (view : Meta) (a : Address) (k : U256) : Meta :=
  {view with accessedStorageKeys := view.accessedStorageKeys.insert ⟨a, k⟩}

def addAccessedStorageKey (devm : Devm) (a : Address) (k : U256) : Devm :=
  liftMachMetaPure (fun mach view => (mach, view.addAccessedStorageKey a k)) devm

/-- EIP-7928: record an account read (`state_tracker.get_account_optional`
and every accessor built on it). -/
def Meta.readAccount (view : Meta) (a : Address) : Meta :=
  {view with accountReads := view.accountReads.insert a}

/-- EIP-7928: record a storage read (`state_tracker.get_storage`). -/
def Meta.readStorage (view : Meta) (a : Address) (k : U256) : Meta :=
  {view with storageReads := view.storageReads.insert ⟨a, k⟩}

/-- Record an account read for the block-level access list, under rules that
carry one; the identity under `rules.bal = none`, so that nothing a Prague–BPO2
frame does can observe the read set (goal C, fixed decision 2). Placed at the
interpreter sites where the pinned code calls a state accessor -- after the
charge that precedes the access, so an out-of-gas frame records nothing the
pinned frame would not. -/
def Devm.balReadAccount (rules : ForkRules) (a : Address) (devm : Devm) : Devm :=
  -- The switch sits inside `setMeta` so that `mach` and `world` are preserved
  -- *definitionally* in both branches: every existing proof that reads through
  -- a meta-only update by `rfl` keeps doing so.
  devm.setMeta (if rules.blockAccessListRules.isSome then devm.meta.readAccount a else devm.meta)

/-- The storage-read twin of `Devm.balReadAccount`. -/
def Devm.balReadStorage (rules : ForkRules) (a : Address) (k : U256) (devm : Devm) :
    Devm :=
  devm.setMeta (if rules.blockAccessListRules.isSome then devm.meta.readStorage a k else devm.meta)

-- The recorders touch `meta` and nothing else; every measure, machine field
-- and world projection sees through them, and under `bal = none` they vanish.
@[simp] theorem Devm.balReadAccount_mach (rules : ForkRules) (a : Address) (devm : Devm) :
    (devm.balReadAccount rules a).mach = devm.mach := by
  rfl
@[simp] theorem Devm.balReadAccount_world (rules : ForkRules) (a : Address) (devm : Devm) :
    (devm.balReadAccount rules a).world = devm.world := by
  rfl
@[simp] theorem Devm.balReadAccount_gasLeft (rules : ForkRules) (a : Address) (devm : Devm) :
    (devm.balReadAccount rules a).gasLeft = devm.gasLeft := by
  rfl
@[simp] theorem Devm.balReadAccount_gasMeasure (rules : ForkRules) (a : Address) (devm : Devm) :
    (devm.balReadAccount rules a).gasMeasure = devm.gasMeasure := by
  rfl
@[simp] theorem Devm.balReadAccount_stack (rules : ForkRules) (a : Address) (devm : Devm) :
    (devm.balReadAccount rules a).stack = devm.stack := by
  rfl
@[simp] theorem Devm.balReadAccount_state (rules : ForkRules) (a : Address) (devm : Devm) :
    (devm.balReadAccount rules a).state = devm.state := by
  rfl
@[simp] theorem Devm.balReadAccount_stateGas (rules : ForkRules) (a : Address) (devm : Devm) :
    (devm.balReadAccount rules a).stateGas = devm.stateGas := by
  rfl
@[simp] theorem Devm.balReadAccount_stateGasLeft (rules : ForkRules) (a : Address) (devm : Devm) :
    (devm.balReadAccount rules a).stateGasLeft = devm.stateGasLeft := by
  rfl
@[simp] theorem Devm.balReadAccount_accessedAddresses (rules : ForkRules) (a : Address)
    (devm : Devm) :
    (devm.balReadAccount rules a).accessedAddresses = devm.accessedAddresses := by
  unfold Devm.balReadAccount Meta.readAccount; split <;> rfl
@[simp] theorem Devm.balReadAccount_accessedStorageKeys (rules : ForkRules) (a : Address)
    (devm : Devm) :
    (devm.balReadAccount rules a).accessedStorageKeys = devm.accessedStorageKeys := by
  unfold Devm.balReadAccount Meta.readAccount; split <;> rfl
@[simp] theorem Devm.balReadAccount_createdAccounts (rules : ForkRules) (a : Address)
    (devm : Devm) :
    (devm.balReadAccount rules a).createdAccounts = devm.createdAccounts := by
  unfold Devm.balReadAccount Meta.readAccount; split <;> rfl
@[simp] theorem Devm.balReadAccount_refundCounter (rules : ForkRules) (a : Address)
    (devm : Devm) :
    (devm.balReadAccount rules a).refundCounter = devm.refundCounter := by
  unfold Devm.balReadAccount Meta.readAccount; split <;> rfl
@[simp] theorem Devm.balReadAccount_logs (rules : ForkRules) (a : Address) (devm : Devm) :
    (devm.balReadAccount rules a).logs = devm.logs := by
  unfold Devm.balReadAccount Meta.readAccount; split <;> rfl
@[simp] theorem Devm.balReadAccount_transientStorage (rules : ForkRules) (a : Address)
    (devm : Devm) :
    (devm.balReadAccount rules a).transientStorage = devm.transientStorage := by
  rfl
theorem Devm.balReadAccount_none {rules : ForkRules} (h : rules.blockAccessListRules = none) (a : Address)
    (devm : Devm) : devm.balReadAccount rules a = devm := by
  unfold Devm.balReadAccount; simp [h, Devm.setMeta]

@[simp] theorem Devm.balReadStorage_mach (rules : ForkRules) (a : Address) (k : U256)
    (devm : Devm) : (devm.balReadStorage rules a k).mach = devm.mach := by
  rfl
@[simp] theorem Devm.balReadStorage_world (rules : ForkRules) (a : Address) (k : U256)
    (devm : Devm) : (devm.balReadStorage rules a k).world = devm.world := by
  rfl
@[simp] theorem Devm.balReadStorage_gasLeft (rules : ForkRules) (a : Address) (k : U256)
    (devm : Devm) : (devm.balReadStorage rules a k).gasLeft = devm.gasLeft := by
  rfl
@[simp] theorem Devm.balReadStorage_gasMeasure (rules : ForkRules) (a : Address) (k : U256)
    (devm : Devm) : (devm.balReadStorage rules a k).gasMeasure = devm.gasMeasure := by
  rfl
@[simp] theorem Devm.balReadStorage_stack (rules : ForkRules) (a : Address) (k : U256)
    (devm : Devm) : (devm.balReadStorage rules a k).stack = devm.stack := by
  rfl
@[simp] theorem Devm.balReadStorage_state (rules : ForkRules) (a : Address) (k : U256)
    (devm : Devm) : (devm.balReadStorage rules a k).state = devm.state := by
  rfl
@[simp] theorem Devm.balReadStorage_stateGas (rules : ForkRules) (a : Address) (k : U256)
    (devm : Devm) : (devm.balReadStorage rules a k).stateGas = devm.stateGas := by
  rfl
@[simp] theorem Devm.balReadStorage_stateGasLeft (rules : ForkRules) (a : Address) (k : U256)
    (devm : Devm) : (devm.balReadStorage rules a k).stateGasLeft = devm.stateGasLeft := by
  rfl
@[simp] theorem Devm.balReadStorage_accessedAddresses (rules : ForkRules) (a : Address)
    (k : U256) (devm : Devm) :
    (devm.balReadStorage rules a k).accessedAddresses = devm.accessedAddresses := by
  unfold Devm.balReadStorage Meta.readStorage; split <;> rfl
@[simp] theorem Devm.balReadStorage_accessedStorageKeys (rules : ForkRules) (a : Address)
    (k : U256) (devm : Devm) :
    (devm.balReadStorage rules a k).accessedStorageKeys = devm.accessedStorageKeys := by
  unfold Devm.balReadStorage Meta.readStorage; split <;> rfl
@[simp] theorem Devm.balReadStorage_createdAccounts (rules : ForkRules) (a : Address)
    (k : U256) (devm : Devm) :
    (devm.balReadStorage rules a k).createdAccounts = devm.createdAccounts := by
  unfold Devm.balReadStorage Meta.readStorage; split <;> rfl
@[simp] theorem Devm.balReadStorage_refundCounter (rules : ForkRules) (a : Address)
    (k : U256) (devm : Devm) :
    (devm.balReadStorage rules a k).refundCounter = devm.refundCounter := by
  unfold Devm.balReadStorage Meta.readStorage; split <;> rfl
@[simp] theorem Devm.balReadStorage_transientStorage (rules : ForkRules) (a : Address)
    (k : U256) (devm : Devm) :
    (devm.balReadStorage rules a k).transientStorage = devm.transientStorage := by
  rfl
theorem Devm.balReadStorage_none {rules : ForkRules} (h : rules.blockAccessListRules = none) (a : Address)
    (k : U256) (devm : Devm) : devm.balReadStorage rules a k = devm := by
  unfold Devm.balReadStorage; simp [h, Devm.setMeta]

def addAccountToDelete (devm : Devm) (a : Address) : Devm :=
  devm.withAccountsToDelete (devm.accountsToDelete.insert a)

/-- The `SELFDESTRUCT` refund hook (`REFUND_SELF_DESTRUCT`): 24000 before
EIP-3529 (London), 0 after, credited when this `SELFDESTRUCT` newly schedules
the donor -- `alreadyScheduled` is the donor's membership in
`accountsToDelete` before scheduling. At Prague the credit is 0, so the hook
is the identity there. -/
def creditSelfdestructRefund (rules : ForkRules) (alreadyScheduled : Prop)
    [Decidable alreadyScheduled] (devm : Devm) : Devm :=
  if alreadyScheduled then devm
  else devm.withRefundCounter (devm.refundCounter + rules.settlement.selfdestructRefund)

/-- Prague pays no selfdestruct refund and deletes only created accounts. -/
@[simp] theorem pragueRules_settle_selfdestructRefund :
    pragueRules.settlement.selfdestructRefund = 0 := rfl
@[simp] theorem pragueRules_settle_selfdestructOnlyCreated :
    pragueRules.settlement.selfdestructOnlyCreated = true := rfl

/-- The hook preserves the refund-counter projection. -/
theorem creditSelfdestructRefund_refundCounter {rules : ForkRules}
    {alreadyScheduled : Prop} [Decidable alreadyScheduled] {devm : Devm} :
    (creditSelfdestructRefund rules alreadyScheduled devm).refundCounter =
      if alreadyScheduled then devm.refundCounter
      else devm.refundCounter + rules.settlement.selfdestructRefund := by
  unfold creditSelfdestructRefund
  split
  · rfl
  · rw [Devm.withRefundCounter_refundCounter]

/-- The hook is meta-only: it preserves memory and output. -/
theorem creditSelfdestructRefund_memory {rules : ForkRules}
    {alreadyScheduled : Prop} [Decidable alreadyScheduled] {devm : Devm} :
    (creditSelfdestructRefund rules alreadyScheduled devm).memory =
      devm.memory := by
  unfold creditSelfdestructRefund
  split <;> rfl

theorem creditSelfdestructRefund_output {rules : ForkRules}
    {alreadyScheduled : Prop} [Decidable alreadyScheduled] {devm : Devm} :
    (creditSelfdestructRefund rules alreadyScheduled devm).output =
      devm.output := by
  unfold creditSelfdestructRefund
  split <;> rfl

/-- The hook fires exactly when the regime still pays the refund and this
`SELFDESTRUCT` newly schedules the donor. -/
theorem creditSelfdestructRefund_ne_iff {rules : ForkRules}
    {alreadyScheduled : Prop} [Decidable alreadyScheduled] {devm : Devm} :
    (creditSelfdestructRefund rules alreadyScheduled devm).refundCounter ≠
        devm.refundCounter ↔
      ¬alreadyScheduled ∧ rules.settlement.selfdestructRefund ≠ 0 := by
  rw [creditSelfdestructRefund_refundCounter]
  by_cases hb : alreadyScheduled <;> simp [hb]

/-- The new credit cannot drive the counter negative. -/
theorem creditSelfdestructRefund_nonneg_of_nonneg {rules : ForkRules}
    {alreadyScheduled : Prop} [Decidable alreadyScheduled] {devm : Devm}
    (h : 0 ≤ devm.refundCounter) :
    0 ≤ (creditSelfdestructRefund rules alreadyScheduled devm).refundCounter := by
  unfold creditSelfdestructRefund
  split
  · exact h
  · exact add_nonneg h (by positivity)

def addCreatedAccount (benv : Benv) (adr : Address) : Benv :=
  {benv with createdAccounts := benv.createdAccounts.insert adr}

def Account.nil : Account :=
  {
    nonce := 0
    balance := 0
    storage := .empty
    code := ByteArray.mk #[]
  }

lemma Std.TreeMap.eq_empty_iff_isEmpty {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} :
    t = Std.TreeMap.empty ↔ t.isEmpty = true := by
  refine' ⟨_, eq_empty_of_isEmpty⟩; intro h; cases h; rfl

/- Both instances below decide through a `Bool` test with `decidable_of_iff`, so
the kernel can reduce them: an instance built by `rw` is a `propext` cast, which
leaves every `State.set` (an `SSTORE`, a value transfer) stuck under kernel
evaluation. Both are also `@[irreducible]`, which only the elaborator reads:
without it, `whnf` inside a failing defeq check between concrete states runs
`State.set` through the Bool test instead of stopping at the instance, as the
old `rw`-built one did, and downstream proofs time out. The kernel ignores the
attribute, so kernel evaluation (`decide +kernel`) is unaffected. -/
@[irreducible] instance {stor : Storage} : Decidable (stor = .empty) :=
  decidable_of_iff (stor.isEmpty = true) Std.TreeMap.eq_empty_iff_isEmpty.symm

theorem Account.eq_nil_iff (ac : Account) :
    (ac.nonce == 0 && ac.balance == 0 && ac.storage.isEmpty && ac.code.size == 0) = true ↔
      ac = .nil := by
  rcases ac with ⟨n, b, s, ⟨c⟩⟩
  simp only [Account.nil, Bool.and_eq_true, beq_iff_eq, Account.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hn, hb⟩, hs⟩, hc⟩
    refine ⟨hn, hb, Std.TreeMap.eq_empty_of_isEmpty hs, ?_⟩
    simp only [ByteArray.size] at hc
    rw [Array.size_eq_zero_iff.mp hc]
  · rintro ⟨hn, hb, hs, hc⟩
    subst hs
    refine ⟨⟨⟨hn, hb⟩, rfl⟩, ?_⟩
    rw [hc]; rfl

@[irreducible] instance {ac : Account} : Decidable (ac = .nil) :=
  decidable_of_iff _ (Account.eq_nil_iff ac)

def State.get (w : State) (a : Address) : Account :=
  w.getD a .nil

/-- Erasing convenience update: writing the default account removes the key. -/
def State.set (w : State) (a : Address) (ac : Account) : State :=
  if ac = .nil then w.erase a else w.insert a ac

/-- Store an account as present, including an explicitly empty account.
Deletion is a separate operation, `destroyAccount`. -/
def State.setPresent (w : State) (a : Address) (ac : Account) : State :=
  w.insert a ac

def Account.isEmpty (a : Account) : Prop :=
  a.code.size = 0 ∧ a.nonce = 0 ∧ a.balance = 0

instance {a : Account} : Decidable a.isEmpty := by
 apply instDecidableAnd

def destroyAccount (w : State) (a : Address) : State := w.erase a

/-- Existence is trie membership, independently of the account's fields. -/
abbrev AccountExists (wor : State) (adr : Address) : Prop :=
  (wor[adr]?).isSome = true

/-! ### EIP-161: touched accounts (Spurious Dragon through Gray Glacier)

EELS records a touch at three sites, each only when the account
`account_exists_and_is_empty` at that moment: a successful child's target
(`incorporate_child_on_success`, and the top-level call target in
`process_message_call`), a `SELFDESTRUCT` beneficiary, and the RIPEMD-160
failed-child quirk (`incorporate_child_on_error`). After every transaction,
`destroy_touched_empty_accounts` erases the touched accounts that are still
empty. Paris removes the sweep: `modify_state` then erases an emptied account
at once (`settle.eraseEmptyOnModify`), which is what `State.setAccount` does.

Historical prestates may contain an explicitly present `Acct.nil`. Existence
is trie membership, so those accounts are recorded and swept just like empty
accounts that still carry storage. An untouched empty prestate account stays
present; neither parsing nor a fork crossing globally clears it.

All three sites are recorded: the two frame-level ones
(`settle`'s `Devm.recordTouch`, `Substate.keepTouch` in `resume`) and the `SELFDESTRUCT`
beneficiary (`Devm.creditBeneficiary`). The last includes a zero credit to an
empty beneficiary, which legacy `modify_state` keeps present and the touch
hands to the sweep. -/

/-- EELS `account_exists_and_is_empty`, over Jaune's notion of existence. -/
def accountExistsAndIsEmpty (wor : State) (adr : Address) : Prop :=
  AccountExists wor adr ∧ (wor.get adr).isEmpty

instance {wor : State} {adr : Address} : Decidable (accountExistsAndIsEmpty wor adr) := by
  unfold accountExistsAndIsEmpty; infer_instance

/-- The RIPEMD-160 precompile's address, which EELS exempts from the rollback
of a failed child's touches (mainnet block 2675119). -/
def ripemd160Address : Address := 0x03

/-- Record `adr` as touched when the rules sweep, `cond` holds, and `adr`
exists and is empty in the current state. Only `touchedAccounts` moves, so
every other projection is definitionally unchanged. -/
def Devm.recordTouch (rules : ForkRules) (cond : Bool) (adr : Address) (devm : Devm) :
    Devm :=
  devm.setMeta {devm.meta with
    touchedAccounts :=
      if rules.settlement.touchedSweep && cond && decide (accountExistsAndIsEmpty devm.state adr)
      then devm.meta.touchedAccounts.insert adr
      else devm.meta.touchedAccounts}

@[simp] theorem Devm.recordTouch_mach (devm : Devm) (rules : ForkRules) (cond : Bool)
    (adr : Address) : (devm.recordTouch rules cond adr).mach = devm.mach := rfl
@[simp] theorem Devm.recordTouch_world (devm : Devm) (rules : ForkRules) (cond : Bool)
    (adr : Address) : (devm.recordTouch rules cond adr).world = devm.world := rfl
@[simp] theorem Devm.recordTouch_state (devm : Devm) (rules : ForkRules) (cond : Bool)
    (adr : Address) : (devm.recordTouch rules cond adr).state = devm.state := rfl
@[simp] theorem Devm.recordTouch_error (devm : Devm) (rules : ForkRules) (cond : Bool)
    (adr : Address) : (devm.recordTouch rules cond adr).error = devm.error := rfl
@[simp] theorem Devm.recordTouch_output (devm : Devm) (rules : ForkRules) (cond : Bool)
    (adr : Address) : (devm.recordTouch rules cond adr).output = devm.output := rfl

/-- Under a rule set without the sweep, recording is the identity. -/
@[simp] theorem Devm.recordTouch_of_not_touchedSweep {rules : ForkRules}
    (h : rules.settlement.touchedSweep = false) (cond : Bool) (adr : Address) (devm : Devm) :
    devm.recordTouch rules cond adr = devm := by
  simp [Devm.recordTouch, h, Devm.setMeta]

/-- `destroy_touched_empty_accounts`: erase every touched account that still
exists and is empty. The identity unless the rules sweep. Each test reads only
its own address, and erasing one account changes no other, so the order of
`addresses` does not matter. -/
def sweepTouchedAccounts (rules : ForkRules) (addresses : List Address) (state : State) :
    State :=
  if rules.settlement.touchedSweep then
    addresses.foldl (fun state adr =>
      if accountExistsAndIsEmpty state adr then destroyAccount state adr else state) state
  else state

@[simp] theorem sweepTouchedAccounts_of_not_touchedSweep {rules : ForkRules}
    (h : rules.settlement.touchedSweep = false) (addresses : List Address) (state : State) :
    sweepTouchedAccounts rules addresses state = state := by
  simp [sweepTouchedAccounts, h]

/-- Modern account-field mutation deletes an empty account, including its storage.
Historical allocations and legacy beneficiary credits use `State.setPresent`;
storage setters preserve an existing owner's presence. -/
def Account.clearIfEmpty (ac : Account) : Account :=
  if ac.isEmpty then .nil else ac

/-- Which empty accounts a state update retains. Storage does not count towards EIP-161 emptiness,
but it is part of the default account tested by `eraseNil`. -/
inductive EmptyRule where
  | erase
  | keep
  | eraseNil
  | keepIfPresent

/-- Update an account under the presence rule of the operation that writes it. -/
def State.writeAccount (w : State) (rule : EmptyRule) (a : Address)
    (update : Account → Account) : State :=
  let result := update (w.get a)
  let erase : Bool := match rule with
    | .erase => decide result.isEmpty
    | .keep => false
    | .eraseNil => decide (result = .nil)
    | .keepIfPresent => !(w[a]?).isSome && decide (result = .nil)
  if erase then w.erase a else w.insert a result

/-- A balance change cannot empty an account with a nonce or code. -/
def State.Protected (w : State) (a : Address) : Prop :=
  (w.get a).nonce ≠ 0 ∨ (w.get a).code.size ≠ 0

/-- EELS `modify_state`: normalize after changing balance, nonce, or code. -/
def State.setAccount (w : State) (a : Address) (ac : Account) : State :=
  w.set a ac.clearIfEmpty

/-- Storage deletion is not a collection of SSTORE-to-zero operations. -/
def KeySet.eraseAddress (writes : KeySet) (a : Address) : KeySet :=
  writes.filter fun key => key.1 != a

/-- Forget writes at an address when the updated account is empty. -/
def KeySet.clearIfEmpty (writes : KeySet) (w : State) (a : Address) : KeySet :=
  if (w.get a).isEmpty then writes.eraseAddress a else writes

def Benv.clearStorageWritesIfEmpty (benv : Benv) (a : Address) : Benv :=
  {benv with storageWrites :=
    if (benv.state.get a).isEmpty then benv.storageWrites.eraseAddress a
    else benv.storageWrites}

def Devm.clearStorageWritesIfEmpty (devm : Devm) (a : Address) : Devm :=
  devm.withStorageWrites
    (if (devm.state.get a).isEmpty then devm.world.storageWrites.eraseAddress a
     else devm.world.storageWrites)

@[simp] theorem Account.clearIfEmpty_balance (ac : Account) :
    ac.clearIfEmpty.balance = ac.balance := by
  unfold Account.clearIfEmpty
  split
  · rename_i h; exact h.2.2.symm
  · rfl

@[simp] theorem Account.clearIfEmpty_nonce (ac : Account) :
    ac.clearIfEmpty.nonce = ac.nonce := by
  unfold Account.clearIfEmpty
  split
  · rename_i h; exact h.2.1.symm
  · rfl

@[simp] theorem Account.clearIfEmpty_code (ac : Account) :
    ac.clearIfEmpty.code = ac.code := by
  unfold Account.clearIfEmpty
  split
  · rename_i h; exact (ByteArray.size_eq_zero_iff.mp h.1).symm
  · rfl

/-- Storage is precisely the field lost when an empty account is deleted. -/
theorem Account.clearIfEmpty_storage (ac : Account) :
    ac.clearIfEmpty.storage = if ac.isEmpty then .empty else ac.storage := by
  unfold Account.clearIfEmpty
  split <;> rfl

def TransientStorage.set (τ : TransientStorage) (a : Address) (s : Storage) : TransientStorage :=
  if s.isEmpty then τ.erase a else τ.insert a s

def State.setCode (ω : State) (a : Address) (cd : ByteArray) : State :=
  let ac := ω.get a
  ω.setAccount a {ac with code := cd}

def getOrigAcct (sevm : Sevm) (a : Address) : Account :=
  sevm.benvStat.origState.get a

def Devm.getAcct (devm : Devm) (a : Address) : Account :=
  devm.state.get a

def Devm.getBal (devm : Devm) (a : Address) : U256 := (devm.getAcct a).balance
def Devm.getCode (devm : Devm) (a : Address) : ByteArray := (devm.getAcct a).code
def Devm.getStorVal (devm : Devm) (adr : Address) (key : U256) : U256 :=
  (devm.getAcct adr).storage.get key
def Devm.getStor (devm : Devm) (adr : Address) : Storage :=
  (devm.getAcct adr).storage

/-- Storage is a world field, so a machine write cannot move it. -/
theorem Devm.getStorVal_setMach {devm : Devm} {m : Mach} {a : Address} {k : U256} :
    (devm.setMach m).getStorVal a k = devm.getStorVal a k := rfl

/-- Account code is a world field, so a machine write cannot move it. -/
theorem Devm.getCode_setMach {devm : Devm} {m : Mach} {a : Address} :
    (devm.setMach m).getCode a = devm.getCode a := rfl

def Storage.set (s : Storage) (k v : U256) : Storage :=
  if v = 0 then s.erase k else s.insert k v

def State.setStorVal (wor : State) (adr : Address) (key val : U256) : State :=
  let acct : Account := wor.get adr
  if AccountExists wor adr then wor.setPresent adr {acct with storage := acct.storage.set key val}
  else wor.set adr {acct with storage := acct.storage.set key val}

def Benv.setStorVal (benv : Benv) (adr : Address) (key val : U256) : Benv :=
  {benv with
    state := benv.state.setStorVal adr key val
    storageWrites := benv.storageWrites.insert (adr, key)}

def Devm.setStorVal (devm : Devm) (adr : Address) (key val : U256) : Devm :=
  (devm.withState (devm.state.setStorVal adr key val)).withStorageWrites
    (devm.world.storageWrites.insert (adr, key))

def TransientStorage.setStorageValue (tra : TransientStorage) (adr : Address) (key val : U256) : TransientStorage :=
  let stor : Storage := tra.getD adr .empty
  tra.set adr <| stor.set key val

def Tenv.setTransVal (tenv : Tenv) (adr : Address) (key val : U256) : Tenv :=
  {tenv with transientStorage := tenv.transientStorage.setStorageValue adr key val}

def Devm.setTransVal (devm : Devm) (adr : Address) (key val : U256) : Devm :=
  devm.withTransientStorage (devm.transientStorage.setStorageValue adr key val)

def getOrigStorVal (sevm : Sevm) (adr : Address) (key : U256) : U256 :=
  (getOrigAcct sevm adr).storage.get key

/-- A created account's original storage is zero even when a storage-only
pre-state account occupied its address. Otherwise read the transaction-start
snapshot, which already includes earlier transactions' committed wipes. -/
def Devm.getOrigStorVal (devm : Devm) (sevm : Sevm) (adr : Address) (key : U256) : U256 :=
  if adr ∈ devm.createdAccounts then 0 else Jaune.getOrigStorVal sevm adr key

def Devm.getTransVal (devm : Devm) (adr : Address) (key : U256) : U256 :=
  (devm.transientStorage.getD adr .empty).get key

def memExtSize
  (current_size access_index access_size : Nat) : Nat :=
  if access_size = 0
  then current_size
  else
    32 *
    ( max
        (ceilDiv current_size 32)
        (ceilDiv (access_index + access_size) 32) )

def memExtsSize : Nat → List (Nat × Nat) → Nat
  | initSize, [] => initSize
  | initSize, ⟨accessIndex, accessSize⟩ :: pairs =>
    let expSize := memExtSize initSize accessIndex accessSize
    memExtsSize expSize pairs

def Devm.extCost (devm : Devm) (pairs : List (Nat × Nat)) : Nat :=
  let extSize := memExtsSize devm.memory.size pairs
  calculateMemoryGasCost extSize - calculateMemoryGasCost devm.memory.size

def ceil32 (n : Nat) : Nat :=
  match n % 32 with
  | 0 => n
  | m@(_ + 1) => n + 32 - m

def Mem.write (μ : Mem) (n : ℕ) : Bytes → Mem
  | [] => μ
  | xs@(_ :: _) =>
    if n + xs.length ≤ μ.size
    then
      if n + xs.length ≤ μ.data.size
      then
        ⟨Array.writeD μ.data n xs, μ.size⟩
      else
        let blank : Array UInt8 := Array.replicate (n + xs.length) 0x00
        ⟨Array.writeD (Array.copyD μ.data blank) n xs, μ.size⟩

    else
      let newSize := ceil32 (n + xs.length)
      let blank : Array UInt8 := Array.replicate newSize 0x00
      ⟨Array.writeD (Array.copyD μ.data blank) n xs, newSize⟩

def Mem.extend (μ : Mem) (index size : Nat) : Mem :=
  ⟨μ.data, memExtSize μ.size index size⟩

def Mem.extends (μ : Mem) (pairs : List (Nat × Nat)) : Mem :=
  ⟨μ.data, memExtsSize μ.size pairs⟩

def Mem.read (μ : Mem) (index size : ℕ) : Bytes × Mem :=
  ⟨μ.data.sliceD index size 0, μ.extend index size⟩

def State.isDead (w : State) (a : Address) : Prop :=
  match w[a]? with
  | none => True
  | some x => x.isEmpty

def Mach.memWrite (mach : Mach) (idx : Nat) (val : Bytes) : Mach :=
  {mach with memory := mach.memory.write idx val}

def Devm.memWrite (devm : Devm) (idx : Nat) (val : Bytes) : Devm :=
  liftMachPure (Mach.memWrite · idx val) devm

def Devm.memRead (devm : Devm) (index size : Nat) : Bytes × Devm :=
  let ⟨val, mem⟩ := devm.memory.read index size
  ⟨val, devm.withMemory mem⟩

/-- Indexed KECCAK absorber: for `7 < n` absorbs one eight-byte lane from the
reader and recurses; for `n < 8` delegates directly to the existing list
absorber on the bounded range-mapped reader sequence, reusing its exact
padding. Only the full-eight-byte branch is newly implemented. -/
private def keccakReadRun (read : Nat → UInt8) (pos n : Nat)
    (wc : Fin 17) (ws : Vector UInt64 25) : U256 :=
  if h : 7 < n then
    let b0 := read pos
    let b1 := read (pos + 1)
    let b2 := read (pos + 2)
    let b3 := read (pos + 3)
    let b4 := read (pos + 4)
    let b5 := read (pos + 5)
    let b6 := read (pos + 6)
    let b7 := read (pos + 7)
    let t : UInt64 := UInt64.ofBytes b7 b6 b5 b4 b3 b2 b1 b0
    let ws' := KECCAK.xorLane ws wc.val (by have := wc.isLt; omega) t
    keccakReadRun read (pos + 8) (n - 8) (wc + 1) <|
      if _hw : wc = 16 then KECCAK.f1600 ws' else ws'
  else
    KECCAK.Bytes.run wc ((List.range n).map (fun j => read (pos + j))) ws
  termination_by n
  decreasing_by omega

/-- Adapted from Blanc `CommonProofs.lean` `Array.sliceD_aux_eq` (source
attribution; never import Blanc into Jaune). -/
private theorem Array.sliceD_aux_eq' {ξ : Type} (xs : Array ξ) (d : ξ) :
    ∀ (n : Nat) (Acc : List ξ) (m : Nat),
      Array.sliceD.aux xs Acc m n d
        = (List.range n).map (fun j => xs.getD (m + j) d) ++ Acc := by
  intro n
  induction n with
  | zero => intro Acc m; rfl
  | succ n ih =>
    intro Acc m
    rw [show Array.sliceD.aux xs Acc m (n + 1) d
          = Array.sliceD.aux xs (xs.getD (m + n) d :: Acc) m n d from rfl,
      ih, List.range_succ]
    simp only [Array.getD_eq_getD_getElem?, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append]

/-- Adapted from Blanc `CommonProofs.lean` `Array.sliceD_eq_map` (source
attribution; never import Blanc into Jaune). -/
private theorem Array.sliceD_eq_map' {ξ : Type} (xs : Array ξ) (m n : Nat) (d : ξ) :
    Array.sliceD xs m n d = (List.range n).map (fun j => xs.getD (m + j) d) := by
  rw [show Array.sliceD xs m n d = Array.sliceD.aux xs [] m n d from rfl,
    Array.sliceD_aux_eq']
  simp only [Array.getD_eq_getD_getElem?, List.append_nil]

/-- One-element range-map split: the range-mapped reader sequence at length
`n + 1` is the length-`n` sequence followed by the last reader byte. -/
private theorem keccakRead_map_succ (read : Nat → UInt8) (pos n : Nat) :
    (List.range (n + 1)).map (fun j => read (pos + j)) =
      (List.range n).map (fun j => read (pos + j)) ++ [read (pos + n)] := by
  rw [List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- Eight-byte unfold: the range-mapped reader sequence at length `n + 8` is
the first eight reader bytes followed by the length-`n` sequence at
`pos + 8`. Uses only `List.range_succ`, list map rules, and addition
normalization; no array bounds since the accessor is total. -/
private theorem keccakRead_map_add_eight (read : Nat → UInt8) (pos n : Nat) :
    (List.range (n + 8)).map (fun j => read (pos + j)) =
      read pos :: read (pos + 1) :: read (pos + 2) :: read (pos + 3) ::
      read (pos + 4) :: read (pos + 5) :: read (pos + 6) :: read (pos + 7) ::
      (List.range n).map (fun j => read (pos + 8 + j)) := by
  induction n generalizing pos with
  | zero => rfl
  | succ n ih =>
    have h1 : n + 1 + 8 = (n + 8) + 1 := by omega
    have harg : pos + (n + 8) = pos + 8 + n := by omega
    rw [h1, keccakRead_map_succ, ih, harg]
    simp only [List.cons_append]
    rw [← keccakRead_map_succ]

/-- Reader-level invariant: the indexed absorber agrees with the existing
list absorber on the range-mapped reader sequence, for every reader,
position, length, lane counter, and initial state. `f1600` stays opaque:
both sides call the same `f1600`. -/
private theorem keccakReadRun_eq_reference (read : Nat → UInt8) (pos n : Nat)
    (wc : Fin 17) (ws : Vector UInt64 25) :
    keccakReadRun read pos n wc ws =
      KECCAK.Bytes.run wc ((List.range n).map (fun j => read (pos + j))) ws := by
  revert pos wc ws
  refine @Nat.strongRecOn (fun n => ∀ (pos : Nat) (wc : Fin 17) (ws : Vector UInt64 25),
    keccakReadRun read pos n wc ws =
      KECCAK.Bytes.run wc ((List.range n).map (fun j => read (pos + j))) ws) n ?_
  intro n ih pos wc ws
  by_cases h7 : 7 < n
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    rw [keccakRead_map_add_eight]
    set lane : UInt64 := UInt64.ofBytes (read (pos + 7)) (read (pos + 6))
      (read (pos + 5)) (read (pos + 4)) (read (pos + 3)) (read (pos + 2))
      (read (pos + 1)) (read pos) with hlane
    set xw : Vector UInt64 25 :=
      KECCAK.xorLane ws wc.val (by have := wc.isLt; omega) lane with hxw
    set st : Vector UInt64 25 :=
      (if _hw : wc = 16 then KECCAK.f1600 xw else xw) with hst
    set stI : Vector UInt64 25 :=
      (if wc = 16 then KECCAK.f1600 xw else xw) with hstI
    have hL : keccakReadRun read pos (k + 8) wc ws =
        keccakReadRun read (pos + 8) (k + 8 - 8) (wc + 1) st := by
      conv_lhs => unfold keccakReadRun
      rw [dite_eq_left h7]
    have ihk := ih (k + 8 - 8) (by omega) (pos + 8) (wc + 1) st
    rw [hL, ihk, Nat.add_sub_cancel]
    show KECCAK.Bytes.run (wc + 1)
        ((List.range k).map (fun j => read (pos + 8 + j))) st =
      KECCAK.Bytes.run (wc + 1)
        ((List.range k).map (fun j => read (pos + 8 + j))) stI
    rw [hst, hstI]
    cases Decidable.em (wc = 16) with
    | inl h => rw [dite_eq_left h, ite_eq_left h]
    | inr h => rw [dite_eq_right h, ite_eq_right h]
  · unfold keccakReadRun
    rw [dite_eq_right h7]

/-- Instantiation to array memory: the indexed absorber on the memory backing
array agrees with the list absorber on the sliced bytes, with no validity or
in-bounds premises. Covers empty input, huge/out-of-range starts, every lane
counter, and all remainder lengths. -/
private theorem keccakReadRun_data_eq (data : Array UInt8) (start len : Nat)
    (wc : Fin 17) (ws : Vector UInt64 25) :
    keccakReadRun (fun j => data.getD j 0) start len wc ws =
      KECCAK.Bytes.run wc (data.sliceD start len 0) ws := by
  rw [Array.sliceD_eq_map']
  exact keccakReadRun_eq_reference _ _ _ _ _

/-- Digest and memory pair: the optimized `(digest, extended memory)` pair
equals the reference `(memRead digest, memRead memory)`. The backing array is
unchanged; only the logical extent moves via the existing `Mem.extend`,
preserving the size-zero rule in `memExtSize`. -/
private theorem keccakReadRun_memRead_pair (devm : Devm) (start size : Nat) :
    (keccakReadRun (fun j => devm.memory.data.getD j 0) start size 0
        (.replicate 25 0),
      devm.withMemory (devm.memory.extend start size)) =
    ((devm.memRead start size).1.keccak, (devm.memRead start size).2) := by
  have hmem : devm.memRead start size =
      ((devm.memory.data.sliceD start size 0),
        devm.withMemory (devm.memory.extend start size)) := rfl
  have h := keccakReadRun_data_eq devm.memory.data start size 0 (.replicate 25 0)
  rw [hmem, Prod.mk.injEq]
  refine ⟨?_, rfl⟩
  unfold Bytes.keccak
  exact h

theorem Devm.memRead_snd_gasLeft (devm : Devm) (index size : Nat) :
    (devm.memRead index size).2.gasLeft = devm.gasLeft := rfl

theorem Devm.memRead_state (devm : Devm) (index size : Nat) :
    (devm.memRead index size).2.state = devm.state := rfl

theorem Devm.memRead_logs (devm : Devm) (index size : Nat) :
    (devm.memRead index size).2.logs = devm.logs := rfl

theorem Devm.memRead_error (devm : Devm) (index size : Nat) :
    (devm.memRead index size).2.error = devm.error := rfl

def Mach.memExtends (mach : Mach) (pairs : List (Nat × Nat)) : Mach :=
  {mach with memory := mach.memory.extends pairs}

def Devm.memExtends (devm : Devm) (pairs : List (Nat × Nat)) : Devm :=
  liftMachPure (Mach.memExtends · pairs) devm

def Meta.addLog (view : Meta) (log : Log) : Meta :=
  {view with logs := view.logs ++ [log]}

def Devm.addLog (devm : Devm) (log : Log) : Devm :=
  liftMachMetaPure (fun mach view => (mach, view.addLog log)) devm

theorem Devm.addLog_error (devm : Devm) (log : Log) :
    (devm.addLog log).error = devm.error := rfl

/-! ### EIP-7708 transfer logs

`vm/__init__.py` `emit_transfer_log`, `SYSTEM_ADDRESS` and `TRANSFER_TOPIC`
at the pin. Reached only under `rules.stateGas = some _`: at the frame-entry
value move and at `SELFDESTRUCT`'s sweep, never for withdrawals, fee refunds or
coinbase payments, which credit without a transfer. -/

/-- `SYSTEM_ADDRESS`, the address every transfer log is emitted from. -/
def transferLogAddress : Address := 0xfffffffffffffffffffffffffffffffffffffffe

/-- `TRANSFER_TOPIC`, `keccak256("Transfer(address,address,uint256)")`. Stated
as the literal so that no site hashes; `transferTopic_keccak` below pins it to
the hash. -/
def transferTopic : U256 :=
  0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef

/-- The log one non-zero ETH transfer between distinct accounts emits: the two
addresses left-padded to words as the indexed topics, the amount as the data. -/
def transferLog (sender recipient : Address) (amount : U256) : Log :=
  { address := transferLogAddress
    topics := [transferTopic, sender.toU256, recipient.toU256]
    data := amount.toBytes }

/-- `emit_transfer_log`, with both of upstream's guards folded in: a self
transfer and a zero transfer emit nothing. -/
def Devm.emitTransferLog (devm : Devm) (sender recipient : Address) (amount : U256) :
    Devm :=
  if sender = recipient ∨ amount = 0 then devm
  else devm.addLog (transferLog sender recipient amount)

def Mach.applyUnary (f : U256 → U256) (cost : Nat) (mach : Mach) :
    Footprint.Outcome Mach Unit :=
  match mach.pop with
  | .error err => .error err
  | .ok ⟨x, mach'⟩ => Mach.pushItem (f x) cost mach'

def Mach.applyBinary (f : U256 → U256 → U256) (cost : Nat) (mach : Mach) :
    Footprint.Outcome Mach Unit :=
  match mach.pop with
  | .error err => .error err
  | .ok ⟨x, mach'⟩ =>
    match mach'.pop with
    | .error err => .error err
    | .ok ⟨y, mach''⟩ => Mach.pushItem (f x y) cost mach''

def Mach.applyTernary (f : U256 → U256 → U256 → U256) (cost : Nat)
    (mach : Mach) : Footprint.Outcome Mach Unit :=
  match mach.pop with
  | .error err => .error err
  | .ok ⟨x, mach'⟩ =>
    match mach'.pop with
    | .error err => .error err
    | .ok ⟨y, mach''⟩ =>
      match mach''.pop with
      | .error err => .error err
      | .ok ⟨z, mach'''⟩ => Mach.pushItem (f x y z) cost mach'''

def applyUnary (f : U256 → U256) (cost : Nat) (devm : Devm) : Execution :=
  liftMachExecution (Mach.applyUnary f cost) devm

def applyBinary (f : U256 → U256 → U256)
  (cost : Nat) (devm : Devm) : Execution :=
  liftMachExecution (Mach.applyBinary f cost) devm

def applyTernary (f : U256 → U256 → U256 → U256)
  (cost : Nat) (devm : Devm) : Execution :=
  liftMachExecution (Mach.applyTernary f cost) devm

theorem applyUnary_def (f : U256 → U256) (cost : Nat) (devm : Devm) :
    applyUnary f cost devm = (do
      let ⟨x, devm'⟩ ← devm.pop
      pushItem (f x) cost devm') := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  cases stack with
  | nil => rfl
  | cons x xs =>
    cases h : Mach.pushItem (f x) cost
        { stack := xs, memory := memory, gasLeft := gasLeft,
          stateGas := stateGas } with
    | error err =>
      rcases err with ⟨msg, mach'⟩
      cases mach'
      simp only [applyUnary, Mach.applyUnary, Mach.pop, pushItem, liftMachExecution,
        liftMach, Footprint.toExecution, Footprint.liftOutcome, Devm.pop_def, Devm.stack,
        Devm.setMach, bind, Except.bind, h]
    | ok out =>
      rcases out with ⟨_, mach'⟩
      cases mach'
      simp only [applyUnary, Mach.applyUnary, Mach.pop, pushItem, liftMachExecution,
        liftMach, Footprint.toExecution, Footprint.liftOutcome, Devm.pop_def, Devm.stack,
        Devm.setMach, bind, Except.bind, h]

theorem applyBinary_def (f : U256 → U256 → U256) (cost : Nat) (devm : Devm) :
    applyBinary f cost devm = (do
      let ⟨x, devm'⟩ ← devm.pop
      let ⟨y, devm''⟩ ← devm'.pop
      pushItem (f x y) cost devm'') := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  cases stack with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      cases h : Mach.pushItem (f x y) cost
        { stack := ys, memory := memory, gasLeft := gasLeft,
          stateGas := stateGas } with
      | error err =>
        rcases err with ⟨msg, mach'⟩
        cases mach'
        simp only [applyBinary, Mach.applyBinary, Mach.pop, pushItem, liftMachExecution,
          liftMach, Footprint.toExecution, Footprint.liftOutcome, Devm.pop_def, Devm.stack,
          Devm.setMach, bind, Except.bind, h]
      | ok out =>
        rcases out with ⟨_, mach'⟩
        cases mach'
        simp only [applyBinary, Mach.applyBinary, Mach.pop, pushItem, liftMachExecution,
          liftMach, Footprint.toExecution, Footprint.liftOutcome, Devm.pop_def, Devm.stack,
          Devm.setMach, bind, Except.bind, h]

def List.swap {ξ} : List ξ → Nat → Option (List ξ)
  | [], _ => none
  | x :: xs, k => do
    let y ← xs[k]?
    let ys := xs.set k x
    .some (y :: ys)

/-- Exchange the items at indices `n` and `m` (both counted from the top),
or `none` when either is beyond the stack: EIP-8024 `EXCHANGE`'s
`max(n, m) + 1 > len(stack)` underflow, stated as two indexed reads. -/
def List.exchange {ξ} (l : List ξ) (n m : Nat) : Option (List ξ) := do
  let x ← l[n]?
  let y ← l[m]?
  .some ((l.set n y).set m x)

def Evm.contract (evm : Evm) : Address := evm.sta.currentTarget

def assertDynamic (sevm : Sevm) (devm : Devm) : Except (EvmError × Devm) Unit :=
  Except.assert (!sevm.isStatic) ⟨.halt (.writeInStaticContext .none), devm⟩

/-- The refund a single `SSTORE` adds to or removes from the counter.

The clear refund arrives through `gas.storageClearRefund` rather than through
the `rSClear` global, because Amsterdam reprices it inside this same formula.
Every other number here -- `gasStorageSet`, `gasStorageUpdate`, `gasColdSload`,
`gasWarmAccess` -- is a legacy-only value the supported chain shares, and stays
a global for that reason. `pragueRules_gas_storageClearRefund` below is the
`rfl` proof that no Prague caller can tell the difference. -/
def sstoreNewRefundCounter (gas : GasSchedule) (new_value : U256)
    (original_value : U256) (current_value : U256) (rc : Int) : Int :=
  if current_value ≠ new_value then
    let rc' :=
      if original_value ≠ 0 ∧ current_value ≠ 0 ∧ new_value = 0 then
        rc + gas.storageClearRefund
      else
        rc
    let rc'' :=
      if original_value ≠ 0 ∧ current_value = 0 then
        rc' - gas.storageClearRefund
      else
        rc'
    if original_value = new_value then
      if original_value = 0 then
        rc'' + (Gas.sstoreSetGas - Gas.warmStorageReadCost)
      else
        rc'' + (Gas.sstoreResetGas - Gas.coldSloadCost - Gas.warmStorageReadCost)
    else
      rc''
  else rc

/-- The pre-net-metering refund (Byzantium/Petersburg): add the clear refund
whenever a currently non-zero slot is cleared. The original value does not
affect this schedule, and restoring a cleared slot does not reverse a refund.
The original-value parameter is retained for the shared refund interface. -/
def sstoreLegacyRefundCounter (gas : GasSchedule) (new_value : U256)
    (original_value : U256) (current_value : U256) (rc : Int) : Int :=
  if current_value ≠ 0 ∧ new_value = 0 then
    rc + gas.storageClearRefund
  else rc

/-- A no-change write refunds nothing under the legacy schedule. -/
theorem sstoreLegacyRefundCounter_noop (gas : GasSchedule) (new_value : U256)
    (original_value : U256) (rc : Int) :
    sstoreLegacyRefundCounter gas new_value original_value new_value rc = rc := by
  unfold sstoreLegacyRefundCounter
  simp

/-- Clearing a non-zero slot to zero refunds the clear refund. -/
theorem sstoreLegacyRefundCounter_clear (gas : GasSchedule)
    (original_value current_value : U256) (rc : Int)
    (horig : original_value ≠ 0) (hcurr : current_value ≠ 0) :
    sstoreLegacyRefundCounter gas 0 original_value current_value rc =
      rc + gas.storageClearRefund := by
  simp [sstoreLegacyRefundCounter, hcurr]

/-- Restoring a freshly set slot refunds the set premium: what the first
change charged over the warm access. -/
theorem sstoreNewRefundCounter_restore_set (gas : GasSchedule)
    (current_value : U256) (rc : Int) (hcurr : current_value ≠ 0) :
    sstoreNewRefundCounter gas 0 0 current_value rc =
      rc + (Gas.sstoreSetGas - Gas.warmStorageReadCost) := by
  unfold sstoreNewRefundCounter
  simp [hcurr]

/-- The execution gas one pre-Berlin net-metered `SSTORE` charges on top of
the cold term (zero under flat access): the EIP-1283/EIP-2200 schedule --
20000 for a fresh set, 5000 for a fresh update, the flat no-op price when
nothing changes. The legacy schedule (no net metering) pays SET/UPDATE and
5000 for the no-op, likewise without any cold term: only the current and new
values decide the legacy charge, independently of the original value. -/
def sstoreRegimeGasCost (sstore : SstoreRules) (access : AccessSchedule)
    (gasCost2 : Nat) (new_value original_value current_value : U256) : Nat :=
  if sstore.netMetering then
    if original_value = current_value ∧ current_value ≠ new_value then
      if original_value = 0 then
        gasCost2 + Gas.sstoreSetGas
      else
        gasCost2 + match access with
          | .flat _ => Gas.sstoreResetGas
          | .eip2929 => Gas.sstoreResetGas - Gas.coldSloadCost
    else
      gasCost2 + match access with
        | .flat g => g.sload
        | .eip2929 => Gas.warmStorageReadCost
  else
    if current_value = 0 ∧ new_value ≠ 0 then Gas.sstoreSetGas
    else Gas.sstoreResetGas

/-- Every row of the pre-Berlin schedule is positive: the literals are, and
the flat no-op price is positive on valid access schedules. The termination
argument's need for the regimes the `none`-lane generalisation adds. -/
theorem sstoreRegimeGasCost_pos (sstore : SstoreRules) {access : AccessSchedule}
    (hacc : access.Valid) (gasCost2 : Nat)
    (new_value original_value current_value : U256) :
    0 < sstoreRegimeGasCost sstore access gasCost2 new_value original_value
      current_value := by
  cases access with
  | flat g =>
    have hsload : 0 < g.sload := by
      simp only [AccessSchedule.Valid, FlatAccessGas.Valid] at hacc
      exact hacc.2.2.2.1
    unfold sstoreRegimeGasCost
    dsimp only
    unfold Gas.sstoreSetGas Gas.sstoreResetGas
    split_ifs <;> omega
  | eip2929 =>
    unfold sstoreRegimeGasCost
    dsimp only
    unfold Gas.sstoreSetGas Gas.sstoreResetGas Gas.warmStorageReadCost Gas.coldSloadCost
    split_ifs <;> omega

/-- The flat net-metered refund (EIP-1283 Constantinople, EIP-2200
Istanbul/Muir Glacier): `sstoreNewRefundCounter`'s shape with every access
price read as the flat no-op price instead of the Berlin cold/warm pair --
the restore terms refund the set/update premium over `sload`. -/
def sstoreFlatRefundCounter (gas : GasSchedule) (sload : Nat)
    (new_value : U256) (original_value : U256) (current_value : U256)
    (rc : Int) : Int :=
  if current_value ≠ new_value then
    let rc' :=
      if original_value ≠ 0 ∧ current_value ≠ 0 ∧ new_value = 0 then
        rc + gas.storageClearRefund
      else
        rc
    let rc'' :=
      if original_value ≠ 0 ∧ current_value = 0 then
        rc' - gas.storageClearRefund
      else
        rc'
    if original_value = new_value then
      if original_value = 0 then
        rc'' + (Gas.sstoreSetGas - sload)
      else
        rc'' + (Gas.sstoreResetGas - sload)
    else
      rc''
  else rc

/-- Restoring a freshly set slot under flat net metering refunds the set
premium over that fork's no-op price. -/
theorem sstoreFlatRefundCounter_restore_set (gas : GasSchedule) (sload : Nat)
    (current_value : U256) (rc : Int) (hcurr : current_value ≠ 0) :
    sstoreFlatRefundCounter gas sload 0 0 current_value rc =
      rc + (Gas.sstoreSetGas - sload) := by
  unfold sstoreFlatRefundCounter
  simp [hcurr]

/-- `sstore`'s refund contribution under the Amsterdam metering shape.

A sibling of `sstoreNewRefundCounter` rather than a widening of it, because the
two forks disagree about what a restored slot refunds. Prague refunds the
difference between what a set or an update cost and what the access cost --
`gasStorageSet - gasWarmAccess`, or `gasStorageUpdate - gasColdSload -
gasWarmAccess`. Amsterdam has decomposed the write, so a restored slot simply
refunds the `STORAGE_WRITE` the first change to it paid. The clear refund is
`gas.storageClearRefund` in both, which is why that one number is a
`GasSchedule` field and these are not.

Transcribed from `vm/instructions/storage.py`'s refund block, in its order. -/
def sstoreAmsterdamRefundCounter (gas : GasSchedule) (state : StateGasRules)
    (new_value original_value current_value : U256) (rc : Int) : Int :=
  if current_value ≠ new_value then
    let rc' :=
      if original_value ≠ 0 ∧ current_value ≠ 0 ∧ new_value = 0 then
        rc + gas.storageClearRefund
      else
        rc
    let rc'' :=
      if original_value ≠ 0 ∧ current_value = 0 then
        rc' - gas.storageClearRefund
      else
        rc'
    if original_value = new_value then
      rc'' + state.storageWrite
    else
      rc''
  else rc

/-- The execution gas one `SSTORE` charges under the Amsterdam shape: the
access, cold or warm, plus `STORAGE_WRITE` on the slot's first change this
transaction. EIP-8038 re-derives the old `gasStorageSet` / `gasStorageUpdate`
lattice as exactly these two terms, with the state creation moved out into the
state dimension. -/
def sstoreAmsterdamGasCost (state : StateGasRules)
    (new_value original_value current_value : U256) (cold : Bool) : Nat :=
  (if cold then Gas.coldSloadCost else Gas.warmStorageReadCost) +
    (if original_value = current_value ∧ current_value ≠ new_value then
      state.storageWrite
    else
      0)

/-- The *state* gas one `SSTORE` charges: `STORAGE_SET` on a first-time set of a
zero slot, and nothing otherwise. The credit-back when such a slot is cleared
again in the same transaction is a refund rather than a negative charge, so it
goes through `creditStateGasRefund` at the site. -/
def sstoreAmsterdamStateGas (state : StateGasRules)
    (new_value original_value current_value : U256) : Nat :=
  if original_value = current_value ∧ current_value ≠ new_value
      ∧ original_value = 0 then
    state.storageSet
  else
    0

/-- Whether this `SSTORE` returns the slot to a zero original, which refills the
`STORAGE_SET` an earlier set in the same transaction charged. -/
def sstoreAmsterdamStateRefund (state : StateGasRules)
    (new_value original_value current_value : U256) : Nat :=
  if current_value ≠ new_value ∧ original_value = new_value
      ∧ original_value = 0 then
    state.storageSet
  else
    0

/-- The read-only-World core of `BALANCE`.  Its mutable result contains only
    `Mach` and `Meta`: it pops the address operand, charges the warm/cold
    account-access cost, records a cold access, and pushes the balance read
    from `World`.

    The cold half arrives through `gas.coldAccountAccess` rather than through
    the global, because EIP-8038 reprices it (2,600 to 3,000) inside this same
    formula. The warm half is a global still: no fork moves it. A `GasSchedule`
    parameter rather than a `Sevm` one, because that is all this core reads and
    it has no other reason to see the frame. -/
-- The read recorders are meta-only, so every state projection sees through them.
@[simp] theorem Devm.balReadAccount_getAcct (rules : ForkRules) (a x : Address) (devm : Devm) :
    (devm.balReadAccount rules a).getAcct x = devm.getAcct x := rfl
@[simp] theorem Devm.balReadAccount_getBal (rules : ForkRules) (a x : Address) (devm : Devm) :
    (devm.balReadAccount rules a).getBal x = devm.getBal x := rfl
@[simp] theorem Devm.balReadAccount_getCode (rules : ForkRules) (a x : Address) (devm : Devm) :
    (devm.balReadAccount rules a).getCode x = devm.getCode x := rfl
@[simp] theorem Devm.balReadAccount_getStorVal (rules : ForkRules) (a x : Address) (k : U256)
    (devm : Devm) : (devm.balReadAccount rules a).getStorVal x k = devm.getStorVal x k := rfl
@[simp] theorem Devm.balReadStorage_getAcct (rules : ForkRules) (a x : Address) (k : U256)
    (devm : Devm) : (devm.balReadStorage rules a k).getAcct x = devm.getAcct x := rfl
@[simp] theorem Devm.balReadStorage_getStorVal (rules : ForkRules) (a x : Address) (k k' : U256)
    (devm : Devm) : (devm.balReadStorage rules a k).getStorVal x k' = devm.getStorVal x k' := rfl

def PlainOp.balanceCore (rules : ForkRules) (world : World) (mach : Mach)
    (view : Meta) : Footprint.Outcome (Mach × Meta) Unit :=
  match mach.pop with
  | .error (err, mach') => .error (err, (mach', view))
  | .ok (x, mach') =>
    let a := x.toAddress
    let warm := a ∈ view.accessedAddresses
    -- Before EIP-2929 the price is flat and the accessed set is untouched.
    let view' :=
      match rules.access with
      | .eip2929 => if warm then view else view.addAccessedAddress a
      | .flat _ => view
    let cost :=
      match rules.access with
      | .eip2929 => if warm then Gas.warmStorageReadCost else rules.gas.coldAccountAccess
      | .flat g => g.balance
    match Mach.chargeGas cost mach' with
    | .error (err, mach'') => .error (err, (mach'', view'))
    | .ok (_, mach'') =>
      -- `environment.py` `balance`: `charge_gas` then `get_account(address)`;
      -- the read is recorded after the charge and before the push (EIP-7928).
      let view'' := if rules.blockAccessListRules.isSome then view'.readAccount a else view'
      match Mach.push (world.state.get a).balance mach'' with
      | .error (err, mach''') => .error (err, (mach''', view''))
      | .ok (_, mach''') => .ok ((), (mach''', view''))

def PlainOp.runCore
  (pc : Nat)
  (devm : Devm)
  (sevm : Sevm) : PlainOp → Execution
  | .address => pushItem sevm.currentTarget.toU256 Gas.base devm
  -- S8 (EIP-3198): availability first, the `CLZ` pattern.
  | .basefee =>
    if sevm.benvStat.rules.opcodes.baseFee then
      pushItem sevm.benvStat.baseFeePerGas.toU256 Gas.base devm
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  -- S8 (EIP-4844): availability first, the `CLZ` pattern.
  | .blobhash =>
    if sevm.benvStat.rules.opcodes.blobHash then do
      let ⟨x, devm⟩ ← devm.pop
      let y : U256 := sevm.tenvStat.blobVersionedHashes.getD x.toNat 0
      chargeGas Gas.hashOpcodeGas devm >>= Devm.push y
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  | .blobbasefee =>
    if sevm.benvStat.rules.opcodes.blobBaseFee then do
      let fee :=
        getBaseFeePerBlobGas sevm.benvStat.rules.blob sevm.benvStat.excessBlobGas
      pushItem fee.toU256 Gas.base devm
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  | .balance =>
    liftMachMetaWorldExecution (PlainOp.balanceCore sevm.benvStat.rules) devm
  | .origin => pushItem sevm.tenvStat.origin.toU256 Gas.base devm
  | .caller => pushItem sevm.caller.toU256 Gas.base devm
  | .callvalue => pushItem sevm.value Gas.base devm
  | .calldataload => do
    let ⟨start_index, devm⟩ ← devm.pop
    let devm' ← chargeGas Gas.veryLow devm
    let value := Bytes.toU256 <| sevm.data.sliceD start_index.toNat 32 0
    devm'.push value
  | .calldatasize => pushItem sevm.data.length.toU256 Gas.base devm
  | .calldatacopy => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨data_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := Gas.copy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (Gas.veryLow + copy_gas_cost + extend_memory_cost) devm
    let value := sevm.data.sliceD data_start_index size 0
    .ok <| devm.memWrite memory_start_index value
  | .codesize => pushItem sevm.code.size.toU256 Gas.base devm
  | .codecopy => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨code_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := Gas.copy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (Gas.veryLow + copy_gas_cost + extend_memory_cost) devm
    let value := sevm.code.sliceD code_start_index size (HaltOp.toUInt8 .stop)
    .ok (devm.memWrite memory_start_index value)
  | .gasprice => pushItem sevm.tenvStat.gasPrice.toU256 Gas.base devm
  -- EIP-8038 adds a code-reading surcharge to `EXTCODESIZE` and `EXTCODECOPY`,
  -- and reprices the cold half of the access. Both arrive through `rules.gas`;
  -- the surcharge is *additive with identity zero*, so the Prague formula here
  -- is literally the formula it was rather than merely equal to it.
  | .extcodesize => do
    let ⟨adr, devm⟩ ← devm.popToAdr
    let gas := sevm.benvStat.rules.gas
    let devm ←
      match sevm.benvStat.rules.access with
      | .eip2929 =>
      if adr ∈ devm.accessedAddresses
      then chargeGas (Gas.warmStorageReadCost + gas.codeReadSurcharge) devm
      else
        chargeGas (gas.coldAccountAccess + gas.codeReadSurcharge)
          (addAccessedAddress devm adr)
      | .flat g => chargeGas (g.extCode + gas.codeReadSurcharge) devm
    -- `get_account(address)` after the charge (EIP-7928).
    let devm := devm.balReadAccount sevm.benvStat.rules adr
    let codesize := (devm.getCode adr).size.toU256
    devm.push codesize
  | .extcodecopy => do
    let ⟨adr, devm⟩ ← devm.popToAdr
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨code_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := Gas.copy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let gas := sevm.benvStat.rules.gas
    let devm ←
      match sevm.benvStat.rules.access with
      | .eip2929 =>
      if adr ∈ devm.accessedAddresses
      then
        chargeGas
          (Gas.warmStorageReadCost + gas.codeReadSurcharge + copy_gas_cost
            + extend_memory_cost)
          devm
      else
        chargeGas
          (gas.coldAccountAccess + gas.codeReadSurcharge + copy_gas_cost
            + extend_memory_cost)
          (addAccessedAddress devm adr)
      | .flat g =>
        chargeGas
          (g.extCode + gas.codeReadSurcharge + copy_gas_cost
            + extend_memory_cost)
          devm
    -- `get_account(address)` after the charge (EIP-7928).
    let devm := devm.balReadAccount sevm.benvStat.rules adr
    let code := devm.getCode adr
    let value := code.sliceD code_start_index size (HaltOp.toUInt8 .stop)
    .ok (devm.memWrite memory_start_index value)
  | .returndatasize => pushItem devm.returnData.length.toU256 Gas.base devm
  | .returndatacopy => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨return_data_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := Gas.returnDataCopy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (Gas.veryLow + copy_gas_cost + extend_memory_cost) devm
    if (devm.returnData.length < return_data_start_index + size) then
      .error ⟨.halt (.outOfBoundsRead .none), devm⟩
    let value :=
      devm.returnData.sliceD return_data_start_index size 0
    .ok (devm.memWrite memory_start_index value)
  -- `EXTCODEHASH` takes the repriced cold access and *no* surcharge: upstream
  -- adds the code-reading cost at `EXTCODESIZE` and `EXTCODECOPY` only, which
  -- is a fact about those two arms rather than about reading code.
  -- S8 (EIP-1052): availability first, the `CLZ` pattern.
  | .extcodehash =>
    if sevm.benvStat.rules.opcodes.extCodeHash then do
      let ⟨adr, devm⟩ ← devm.popToAdr
      let devm ←
        match sevm.benvStat.rules.access with
        | .eip2929 =>
        if adr ∈ devm.accessedAddresses then
          chargeGas Gas.warmStorageReadCost devm
        else
          chargeGas sevm.benvStat.rules.gas.coldAccountAccess
            (addAccessedAddress devm adr)
        | .flat g => chargeGas g.extCodeHash devm
      -- `get_account(address)` after the charge (EIP-7928).
      let devm := devm.balReadAccount sevm.benvStat.rules adr
      let account := devm.getAcct adr
      let codehash : U256 :=
        if account.isEmpty then 0
        else ByteArray.keccak 0 account.code.size account.code
      devm.push codehash
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  -- `environment.py` `self_balance`: `charge_gas(LOW)`, then `get_account`
  -- on the current target -- recorded for EIP-7928 -- then the push.
  -- S8 (EIP-1884): availability first, the `CLZ` pattern.
  | .selfbalance =>
    if sevm.benvStat.rules.opcodes.selfBalance then do
      let devm ← chargeGas Gas.low devm
      (devm.balReadAccount sevm.benvStat.rules sevm.currentTarget).push
        (devm.getBal sevm.currentTarget)
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  -- S8 (EIP-1344): availability first, the `CLZ` pattern.
  | .chainid =>
    if sevm.benvStat.rules.opcodes.chainId then
      pushItem sevm.benvStat.chainId.toU256 Gas.base devm
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  | .number => pushItem sevm.benvStat.number.toU256 Gas.base devm
  | .timestamp => pushItem sevm.benvStat.time Gas.base devm
  | .gaslimit => pushItem sevm.benvStat.blockGasLimit.toU256 Gas.base devm
  | .prevrandao => pushItem sevm.benvStat.prevRandao Gas.base devm
  | .coinbase => pushItem sevm.benvStat.coinbase.toU256 Gas.base devm
  | .msize => pushItem devm.memory.size.toU256 Gas.base devm
  | .mload => do
    let ⟨start_index, devm⟩ ← devm.popToNat
    let extend_memory_cost := devm.extCost [⟨start_index, 32⟩]
    let devm ← chargeGas (Gas.veryLow + extend_memory_cost) devm
    let ⟨value, devm⟩ := devm.memRead start_index 32
    devm.push (Bytes.toU256 value)
  | .mstore => do
    let ⟨start_index, devm⟩ ← devm.popToNat
    let ⟨value, devm⟩ ← devm.pop
    let extend_memory_cost := devm.extCost [⟨start_index, 32⟩]
    let devm ← chargeGas (Gas.veryLow + extend_memory_cost) devm
    .ok <| devm.memWrite start_index value.toBytes
  | .mstore8 => do
    let ⟨start_index, devm⟩ ← devm.popToNat
    let ⟨value, devm⟩ ← devm.pop
    let extend_memory_cost := devm.extCost [⟨start_index, 1⟩]
    let devm ← chargeGas (Gas.veryLow + extend_memory_cost) devm
    .ok <| devm.memWrite start_index [value.2.2.toUInt8]
  | .gas => do
    let devm ← chargeGas Gas.base devm
    devm.push devm.gasLeft.toU256
  | .eq => applyBinary .eqCheck Gas.veryLow devm
  | .lt => applyBinary .ltCheck Gas.veryLow devm
  | .gt => applyBinary .gtCheck Gas.veryLow devm
  | .slt => applyBinary .sltCheck Gas.veryLow devm
  | .sgt => applyBinary .sgtCheck Gas.veryLow devm
  | .iszero => applyUnary (.eqCheck · 0) Gas.veryLow devm
  | .not => applyUnary (~~~ ·) Gas.veryLow devm
  | .and => applyBinary U256.and Gas.veryLow devm
  | .or => applyBinary U256.or Gas.veryLow devm
  | .xor => applyBinary U256.xor Gas.veryLow devm
  | .signextend => applyBinary U256.signext Gas.low devm
  | .pop => (devm.pop <&> Prod.snd) >>= chargeGas Gas.base
  | .byte =>
    applyBinary (λ x y => (List.getD y.toBytes x.toNat 0).toU256) Gas.veryLow devm
  -- S8 (EIP-145): the availability check comes before the pops, exactly as for
  -- `CLZ` below, so without the fork each byte is an undefined instruction
  -- whatever the stack holds.
  | .shl =>
    if sevm.benvStat.rules.opcodes.shifts then
      applyBinary (fun x y => y <<< x.toNat) Gas.veryLow devm
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  | .shr =>
    if sevm.benvStat.rules.opcodes.shifts then
      applyBinary (fun x y => y >>> x.toNat) Gas.veryLow devm
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  | .sar =>
    if sevm.benvStat.rules.opcodes.shifts then
      applyBinary (fun x y => U256.arithShiftRight y x.toNat) Gas.veryLow devm
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  | .clz =>
    -- The availability check comes before the pop, so under rules without
    -- EIP-7939 a `CLZ` byte behaves exactly like any other undefined opcode:
    -- an invalid instruction regardless of what the stack holds.
    if sevm.benvStat.rules.opcodes.clz then
      applyUnary (fun x => (U256.leadingZeros x).toU256) Gas.low devm
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  | .keccak256 => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let word_gas_cost := Gas.keccak256Word * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (Gas.keccak256 + word_gas_cost + extend_memory_cost) devm
    (devm.withMemory (devm.memory.extend memory_start_index size)).push
      (keccakReadRun (fun j => devm.memory.data.getD j 0) memory_start_index size 0
        (.replicate 25 0))
  | .sub => applyBinary (· - ·) Gas.veryLow devm
  | .mul => applyBinary (· * ·) Gas.low devm
  | .exp => do
    let ⟨base, devm⟩ ← devm.pop
    let ⟨exponent, devm⟩ ← devm.pop
    let devm ← chargeGas (Gas.exp + (Gas.expByte * exponent.bytecount)) devm
    devm.push (U256.exp base exponent)
  | .div => applyBinary (· / ·) Gas.low devm
  | .sdiv => applyBinary U256.sdiv Gas.low devm
  | .mod => applyBinary (· % ·) Gas.low devm
  | .smod => applyBinary U256.smod Gas.low devm
  | .add => applyBinary (· + ·) Gas.veryLow devm
  | .addmod => applyTernary U256.addmod Gas.mid devm
  | .mulmod => applyTernary U256.mulmod Gas.mid devm
  | .swap n => do
    let devm ← chargeGas Gas.veryLow devm
    match List.swap devm.stack n with
    | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
    | some stack => .ok (devm.withStack stack)
  -- `vm/instructions/block.py` `slot_number`: `charge_gas(OPCODE_SLOTNUM)`,
  -- where `OPCODE_SLOTNUM = BASE`, then push `U256(block_env.slot_number)`.
  -- The availability check comes first, exactly as for `CLZ`: under rules
  -- without EIP-7843 the byte is an undefined instruction.
  | .slotnum =>
    if sevm.benvStat.rules.opcodes.slotnum then
      pushItem sevm.benvStat.slotNumber.toNat.toU256 Gas.base devm
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  | .dup n => do
    let devm ← chargeGas Gas.veryLow devm
    match devm.stack[n]? with
    | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
    | some word => devm.push word
  | .sload => do
    let ⟨key, devm⟩ ← devm.pop
    let ct := sevm.currentTarget
    let devm ←
      match sevm.benvStat.rules.access with
      | .eip2929 =>
      if ⟨ct, key⟩ ∈ devm.accessedStorageKeys then
        chargeGas Gas.warmStorageReadCost devm
      else
        chargeGas Gas.coldSloadCost
          (addAccessedStorageKey devm ct key)
      | .flat g => chargeGas g.sload devm
    -- `get_storage` after the charge (EIP-7928).
    let devm := devm.balReadStorage sevm.benvStat.rules ct key
    devm.push (devm.getStorVal ct key)
  -- S8 (EIP-1153): availability first, the `CLZ` pattern.
  | .tload =>
    if sevm.benvStat.rules.opcodes.transient then do
      let ⟨key, devm⟩ ← devm.pop
      pushItem (devm.getTransVal sevm.currentTarget key) Gas.warmStorageReadCost devm
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  | .pc => pushItem pc.toU256 Gas.base devm
  -- `vm/instructions/storage.py` `sstore`. The two shapes differ in more than
  -- numbers, so this is a `match` on the switch rather than a schedule read:
  -- Amsterdam moves the static check ahead of the pops, replaces the EIP-2200
  -- stipend sentry with an explicit `check_gas`, re-derives the charge as
  -- access plus `STORAGE_WRITE`, and moves the state creation into the second
  -- dimension. Under `none` the body below is the body it has always been.
  | .sstore =>
    match sevm.benvStat.rules.stateGas with
    | none =>
      match sevm.benvStat.rules.sstore, sevm.benvStat.rules.access with
      | ⟨true, true⟩, .eip2929 => do
        let ⟨key, devm⟩ ← devm.pop
        let ⟨new_value, devm⟩ ← devm.pop
        .assert
          (Gas.callStipend < devm.gasLeft)
          ⟨.halt (.outOfGas .none), devm⟩
        let ct := sevm.currentTarget
        let original_value := devm.getOrigStorVal sevm ct key
        -- `get_storage_original` records nothing; `get_storage` records the
        -- slot (EIP-7928).
        let devm := devm.balReadStorage sevm.benvStat.rules ct key
        let current_value := devm.getStorVal ct key
        let ⟨devm, gasCost2⟩ ← .ok <|
          if ⟨ct, key⟩ ∉ devm.accessedStorageKeys then
            ( ⟨ addAccessedStorageKey devm ct key,
                Gas.coldSloadCost ⟩ : Devm × Nat )
          else
            ⟨devm, 0⟩
        let gasCost3 ← .ok <|
          if original_value = current_value ∧ current_value ≠ new_value then
            if original_value = 0 then
              gasCost2 + Gas.sstoreSetGas
            else
              gasCost2 + (Gas.sstoreResetGas - Gas.coldSloadCost)
          else
            gasCost2 + Gas.warmStorageReadCost
        let devm ← .ok <| devm.withRefundCounter <|
          sstoreNewRefundCounter
            sevm.benvStat.rules.gas
            new_value
            original_value
            current_value
            devm.refundCounter
        let devm ← chargeGas gasCost3 devm
        assertDynamic sevm devm
        -- `set_storage` asserts `get_account_optional(address)`: an account read.
        .ok ((devm.balReadAccount sevm.benvStat.rules ct).setStorVal
          sevm.currentTarget key new_value)
      | _, _ => do
        let ⟨key, devm⟩ ← devm.pop
        let ⟨new_value, devm⟩ ← devm.pop
        -- EIP-2200's stipend sentry (Istanbul onward); vacuous before, so the
        -- pre-Istanbul regimes skip the check without changing shape.
        .assert
          (sevm.benvStat.rules.sstore.stipendSentry →
            Gas.callStipend < devm.gasLeft)
          ⟨.halt (.outOfGas .none), devm⟩
        let ct := sevm.currentTarget
        let original_value := devm.getOrigStorVal sevm ct key
        -- `get_storage_original` records nothing; `get_storage` records the
        -- slot (EIP-7928).
        let devm := devm.balReadStorage sevm.benvStat.rules ct key
        let current_value := devm.getStorVal ct key
        -- Cold surcharge and warming only under EIP-2929 access; under flat
        -- access the slot is neither warmed nor surcharged.
        let ⟨devm, gasCost2⟩ ← .ok <|
          match sevm.benvStat.rules.access with
          | .flat _ => (⟨devm, 0⟩ : Devm × Nat)
          | .eip2929 =>
            if ((ct, key) : Address × U256) ∉ devm.accessedStorageKeys then
              ( ⟨ addAccessedStorageKey devm ct key,
                  Gas.coldSloadCost ⟩ : Devm × Nat )
            else
              (⟨devm, 0⟩ : Devm × Nat)
        let gasCost3 ← .ok <|
          sstoreRegimeGasCost sevm.benvStat.rules.sstore
            sevm.benvStat.rules.access gasCost2 new_value original_value
            current_value
        let devm ← .ok <| devm.withRefundCounter <|
          match sevm.benvStat.rules.sstore.netMetering,
              sevm.benvStat.rules.access with
          | false, _ => sstoreLegacyRefundCounter
              sevm.benvStat.rules.gas
              new_value
              original_value
              current_value
              devm.refundCounter
          | true, .flat g => sstoreFlatRefundCounter
              sevm.benvStat.rules.gas
              g.sload
              new_value
              original_value
              current_value
              devm.refundCounter
          | true, .eip2929 => sstoreNewRefundCounter
              sevm.benvStat.rules.gas
              new_value
              original_value
              current_value
              devm.refundCounter
        let devm ← chargeGas gasCost3 devm
        assertDynamic sevm devm
        -- `set_storage` asserts `get_account_optional(address)`: an account read.
        .ok ((devm.balReadAccount sevm.benvStat.rules ct).setStorVal
          sevm.currentTarget key new_value)
    | some state => do
      -- The static check now precedes everything, including the pops.
      assertDynamic sevm devm
      let ⟨key, devm⟩ ← devm.pop
      let ⟨new_value, devm⟩ ← devm.pop
      let ct := sevm.currentTarget
      -- GAS (state-independent). Price what is computable without touching
      -- state and check it is affordable first: the access cost can now exceed
      -- the stipend, so the EIP-2200 sentry alone no longer suffices.
      let cold := ⟨ct, key⟩ ∉ devm.accessedStorageKeys
      let accessGas := if cold then Gas.coldSloadCost else Gas.warmStorageReadCost
      .assert
        (max accessGas (Gas.callStipend + 1) ≤ devm.gasLeft)
        ⟨.halt (.outOfGas .none), devm⟩
      -- STATE ACCESS. Only now is the slot read, and only now is it warmed.
      let devm := if cold then addAccessedStorageKey devm ct key else devm
      let original_value := devm.getOrigStorVal sevm ct key
      -- `get_storage_original` records nothing; `get_storage` records the
      -- slot (EIP-7928).
      let devm := devm.balReadStorage sevm.benvStat.rules ct key
      let current_value := devm.getStorVal ct key
      let devm := devm.withRefundCounter <|
        sstoreAmsterdamRefundCounter
          sevm.benvStat.rules.gas state
          new_value original_value current_value devm.refundCounter
      -- STATE GAS. A set-then-cleared slot refills the `STORAGE_SET` its first
      -- set charged, and the credit precedes both charges as upstream's does.
      let devm :=
        devm.creditStateGasRefund
          (sstoreAmsterdamStateRefund state new_value original_value
            current_value)
      -- Execution gas before state gas, so that an execution-gas out-of-gas
      -- does not consume state gas that would inflate the parent's reservoir.
      let devm ←
        chargeGas
          (sstoreAmsterdamGasCost state new_value original_value current_value
            cold)
          devm
      let devm ←
        chargeStateGas
          (sstoreAmsterdamStateGas state new_value original_value current_value)
          devm
      -- `set_storage` asserts `get_account_optional(address)`: an account read.
      .ok ((devm.balReadAccount sevm.benvStat.rules ct).setStorVal ct key new_value)
  -- S8 (EIP-1153): availability first, the `CLZ` pattern; the two metering
  -- shapes below are untouched.
  | .tstore =>
    if sevm.benvStat.rules.opcodes.transient then
      match sevm.benvStat.rules.stateGas with
      | none => do
        let ⟨key, devm⟩ ← devm.pop
        let ⟨new_value, devm⟩ ← devm.pop
        let devm ← chargeGas Gas.warmStorageReadCost devm
        assertDynamic sevm devm
        .ok (devm.setTransVal sevm.currentTarget key new_value)
      | some _ => do
        -- `storage.py.tstore` at the pin: static execution is rejected before
        -- stack access or charging, so failure preserves both stack and gas.
        assertDynamic sevm devm
        let ⟨key, devm⟩ ← devm.pop
        let ⟨new_value, devm⟩ ← devm.pop
        let devm ← chargeGas Gas.warmStorageReadCost devm
        .ok (devm.setTransVal sevm.currentTarget key new_value)
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  -- S8 (EIP-5656): availability first, the `CLZ` pattern.
  | .mcopy =>
    if sevm.benvStat.rules.opcodes.mcopy then do
      let ⟨destination, devm⟩ ← devm.popToNat
      let ⟨source, devm⟩ ← devm.popToNat
      let ⟨length, devm⟩ ← devm.popToNat
      let words := ceilDiv length 32
      let copy_gas_cost := Gas.copy * words
      let extend_memory_cost :=
        devm.extCost [⟨source, length⟩, ⟨destination, length⟩]
      let devm ← chargeGas (Gas.veryLow + copy_gas_cost + extend_memory_cost) devm
      let ⟨value, devm⟩ := devm.memRead source length
      .ok (devm.memWrite destination value)
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  | .log n => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let ⟨topics, devm⟩ ← devm.popN n
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ←
      chargeGas
        (Gas.log + (Gas.logData * size) + (Gas.logTopic * n) + extend_memory_cost)
        devm
    assertDynamic sevm devm
    let ⟨data, devm⟩ := devm.memRead memory_start_index size
    let log : Log := ⟨sevm.currentTarget, topics, data⟩
    .ok (devm.addLog log)
  | .blockhash => do
    let ⟨blockNumberWord, devm⟩ ← devm.pop
    let blockNumber := blockNumberWord.toNat
    let devm ← chargeGas Gas.blockhash devm
    let maxBlockNumber := blockNumber + 256
    let hash : U256 :=
      if sevm.benvStat.number ≤ blockNumber ∨ maxBlockNumber < sevm.benvStat.number
      then 0
      else
        sevm.benvStat.blockHashes.getD
          (sevm.benvStat.blockHashes.length - (sevm.benvStat.number - blockNumber))
          0
    devm.push hash

def PlainOp.run (evm : Evm) := PlainOp.runCore evm.pc evm.dyna evm.sta

/-- Unconditional KECCAK compatibility: the indexed branch computes the entire
`Execution` of the reference bind chain — both pops, word and extension gas,
the charge, memory extension, digest, and push — with no fork, stack, gas,
well-formedness, or success premise. The right-hand side is exactly the former
branch. Kept out of the simp set; existing proof bodies rewrite through it
before destructuring the old branch. -/
theorem PlainOp.runCore_keccak256_eq_reference (pc : Nat) (devm : Devm) (sevm : Sevm) :
    PlainOp.runCore pc devm sevm .keccak256 = (do
      let ⟨memory_start_index, devm⟩ ← devm.popToNat
      let ⟨size, devm⟩ ← devm.popToNat
      let words := ceilDiv size 32
      let word_gas_cost := Gas.keccak256Word * words
      let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
      let devm ← chargeGas (Gas.keccak256 + word_gas_cost + extend_memory_cost) devm
      let ⟨arg, devm⟩ := devm.memRead memory_start_index size
      devm.push arg.keccak) := by
  have htail : ∀ (d3 : Devm) (start size : Nat),
      (d3.withMemory (d3.memory.extend start size)).push
        (keccakReadRun (fun j => d3.memory.data.getD j 0) start size 0 (.replicate 25 0)) =
      (d3.memRead start size).2.push (d3.memRead start size).1.keccak := by
    intro d3 start size
    exact congrArg (fun p : U256 × Devm => p.2.push p.1)
      (keccakReadRun_memRead_pair d3 start size)
  simp only [PlainOp.runCore]
  simp only [htail]

instance : Inhabited BenvStat := ⟨
  {
    fork := .prague
    chainId := 0
    origState := .empty
    blockGasLimit := 0
    blockHashes := []
    coinbase := 0
    number := 0
    baseFeePerGas := 0
    time := 0
    prevRandao := 0
    excessBlobGas := 0
    parentBeaconBlockRoot := 0
  }
⟩
instance : Inhabited Benv := ⟨
  {
    state := .empty
    createdAccounts := .emptyWithCapacity
    stat := default
  }
⟩

instance : Inhabited TenvStat := ⟨
  {
    origin := 0
    gasPrice := 0
    gas := 0
    accessListAddresses := .emptyWithCapacity
    accessListStorageKeys := .emptyWithCapacity
    blobVersionedHashes := []
    auths := []
    indexInBlock := none
    txHash := none
  }
⟩
instance : Inhabited Tenv := ⟨
  {
    transientStorage := .empty
    stat := default
  }
⟩

instance : Inhabited Msg :=
  ⟨
    {
      benv := default
      tenv := default
      caller := 0
      target := .none
      currentTarget := 0
      gas := 0
      value := 0
      data := []
      codeAddress := .none
      code := .empty
      depth := 1024
      shouldTransferValue := false
      isStatic := false
      accessedAddresses := .emptyWithCapacity
      accessedStorageKeys := .emptyWithCapacity
      disablePrecompiles := false
    }
  ⟩

instance : Inhabited Devm := ⟨
  {
    mach := {
      stack := []
      memory := ⟨.empty, 0⟩
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
      state := .empty
      transientStorage := default
    }
  }
⟩

instance : Inhabited Sevm := ⟨
  {
    caller := 0
    target := .none
    currentTarget := 0
    gas := 0
    value := 0
    data := []
    codeAddress := .none
    code := .empty
    depth := 1024
    shouldTransferValue := false
    isStatic := false
    disablePrecompiles := false
    benvStat := default
    tenvStat := default
  }
⟩

instance : Inhabited Evm := ⟨
  {
    pc := 0
    sta := default
    dyna := default
  }
⟩

instance : Inhabited Execution := ⟨.ok default⟩

def noPushBefore (cd : ByteArray) : Nat → Nat → Bool
  | 0, _ => true
  | _, 0 => true
  | k + 1, m + 1 =>
    if hk : k < cd.size
    then let b := cd[k]
         if (b < (0x7F - m.toUInt8) || 0x7F < b)
         then noPushBefore cd k m
         else if noPushBefore cd k 32
              then false
              else noPushBefore cd k m
    else noPushBefore cd k m

def jumpable (cd : ByteArray) (k : Nat) : Bool :=
  if hk : k < cd.size
  then
    if cd[k] = (JumpOp.toUInt8 .jumpdest)
    then noPushBefore cd k 32
    else false
  else false

--------------- THE FORWARD INSTRUCTION-START SCAN ---------------

-- `jumpable` keeps its backward `noPushBefore` scan, which is exponential under
-- kernel reduction. `jumpdestOk` is the linear forward scan, and
-- `jumpable_eq_jumpdestOk` proves the two equal on every byte array, so a proof
-- may rewrite with it and evaluate the forward scan instead.

/-- One step of `ByteArray.toList`'s index loop, read through the checked
index. The loop's own read is core's panicking one, reached here by `whnf`. -/
private lemma ByteArray.toList_loop_step (bs : ByteArray) (i : Nat) (r : List UInt8)
    (h : i < bs.size) :
    _root_.ByteArray.toList.loop bs i r = _root_.ByteArray.toList.loop bs (i + 1) (bs[i] :: r) := by
  conv => lhs; unfold _root_.ByteArray.toList.loop
  rw [ite_eq_left h]
  congr 2
  conv => lhs; whnf
  generalize Nat.decLt _ _ = d
  cases d with
  | isFalse h' => exact absurd h h'
  | isTrue _ => rfl

private lemma ByteArray.toList_eq_toList_data' {xs : ByteArray} :
    xs.toList = xs.data.toList := by
  have gen :
      ∀ xs ys : List UInt8,
        _root_.ByteArray.toList.loop
          ⟨⟨xs ++ ys⟩⟩ xs.length xs.reverse = xs ++ ys := by
    intro xs ys;
    induction ys generalizing xs with
      | nil =>
        unfold _root_.ByteArray.toList.loop
        rw [ite_eq_right _, List.reverse_reverse, List.append_nil]
        simp [ByteArray.size]
      | cons y ys ih =>
        rw [ByteArray.toList_loop_step _ _ _ (by simp [ByteArray.size])]
        have rw : (⟨⟨xs ++ y :: ys⟩⟩ : ByteArray)[xs.length]'(by simp [ByteArray.size]) = y := by
          simp [ByteArray.getElem_eq_getElem_data]
        have rw' : xs.length + 1 = (xs ++ [y]).length := by simp
        have rw'' : y :: xs.reverse = (xs ++ [y]).reverse := by simp
        rw [rw, List.append_cons, rw', rw'', ih]
  rcases xs with ⟨⟨xs⟩⟩; apply gen [] xs

private lemma ByteArray.getElem_of_getElem?_eq_some' {xs : ByteArray} {n : Nat}
    {x : UInt8} (eq : xs.toList[n]? = .some x) (h : n < xs.size) : xs[n] = x := by
  rw [ByteArray.toList_eq_toList_data', Array.getElem?_toList] at eq
  exact (Array.getElem?_eq_some_iff.mp eq).choose_spec

private lemma ByteArray.size_eq_length_toList' (xs : ByteArray) :
    xs.size = xs.toList.length := by
  simp only [ByteArray.size, Array.size]
  rw [ByteArray.toList_eq_toList_data']

/-- A backward-scan specification for `noPushBefore`. -/
theorem noPushBefore_eq_true_iff (cd : ByteArray) :
    ∀ (K M : Nat), M ≤ 32 →
      (noPushBefore cd K M = true ↔
        ∀ p, K ≤ p + M → p < K → ∀ (hp : p < cd.size),
          96 ≤ cd[p].toNat → cd[p].toNat ≤ 127 →
          K + (32 - M) ≤ p + (cd[p].toNat - 95) →
          noPushBefore cd p 32 = false) := by
  intro K
  induction K with
  | zero => intro M _; simp [noPushBefore]
  | succ k ih =>
    intro M hM
    match M with
    | 0 => simp [noPushBefore]; omega
    | m + 1 =>
      rw [noPushBefore]
      have hm : m ≤ 32 := by omega
      have harith : k + 1 + (32 - (m + 1)) = k + (32 - m) := by omega
      rw [harith]
      have hthr : ∀ b : UInt8, (b < 127 - m.toUInt8) ↔ (b.toNat < 127 - m) := by
        intro b; rw [UInt8.lt_iff_toNat_lt]
        simp [UInt8.toNat_sub, Nat.toUInt8]; omega
      have hgt : ∀ b : UInt8, ((127 : UInt8) < b) ↔ (127 < b.toNat) := by
        intro b; rw [UInt8.lt_iff_toNat_lt]; rfl
      by_cases hk : k < cd.size
      · rw [dite_eq_left hk]
        by_cases hc : (decide (cd[k] < 127 - m.toUInt8) || decide (127 < cd[k])) = true
        · rw [ite_eq_left hc, ih m hm]
          simp only [Bool.or_eq_true, decide_eq_true_eq, hthr, hgt] at hc
          constructor
          · intro h p h1 h2 hp h3 h4 h5
            rcases Nat.lt_or_ge p k with hlt | hge
            · exact h p (by omega) hlt hp h3 h4 h5
            · have hpk : p = k := by omega
              subst hpk; exfalso; omega
          · intro h p h1 h2 hp h3 h4 h5
            exact h p (by omega) (by omega) hp h3 h4 h5
        · simp only [Bool.or_eq_true, decide_eq_true_eq, hthr, hgt, not_or,
            Nat.not_lt] at hc
          rw [ite_eq_right (by simp [hthr, hgt]; omega)]
          by_cases hreal : noPushBefore cd k 32 = true
          · rw [ite_eq_left hreal]
            constructor
            · intro hf; cases hf
            · intro h
              rw [h k (by omega) (by omega) hk (by omega) (by omega) (by omega)] at hreal
              exact hreal
          · rw [ite_eq_right hreal, ih m hm]
            constructor
            · intro h p h1 h2 hp h3 h4 h5
              rcases Nat.lt_or_ge p k with hlt | hge
              · exact h p (by omega) hlt hp h3 h4 h5
              · have hpk : p = k := by omega
                subst hpk; simpa using hreal
            · intro h p h1 h2 hp h3 h4 h5
              exact h p (by omega) (by omega) hp h3 h4 h5
      · rw [dite_eq_right hk, ih m hm]
        constructor
        · intro h p h1 h2 hp h3 h4 h5
          rcases Nat.lt_or_ge p k with hlt | hge
          · exact h p (by omega) hlt hp h3 h4 h5
          · exact (hk (by omega)).elim
        · intro h p h1 h2 hp h3 h4 h5
          exact h p (by omega) (by omega) hp h3 h4 h5

/-- **The transport lemma.**  If `k` is a position no `PUSH` immediate covers,
and `k` opens one complete instruction of span `s`, then the position just past
that instruction is again covered by no `PUSH` immediate.

The hypothesis `hinst` is what "one complete instruction of span `s` at `k`"
means at the byte level: either `cd[k]` is one of `PUSH1 … PUSH32` and `s` is
its opcode plus immediate, or `cd[k]` takes no immediate and `s` is 1.  A
position past the end of `cd` carries no constraint at all -- Jaune reads it as
`STOP` and nothing can be pushed from there. -/
theorem noPushBefore_add {cd : ByteArray} {k s : Nat}
    (hinst : ∀ (hk : k < cd.size),
      (96 ≤ cd[k].toNat ∧ cd[k].toNat ≤ 127 ∧ s = cd[k].toNat - 94) ∨
      ((cd[k].toNat < 96 ∨ 127 < cd[k].toNat) ∧ s = 1))
    (hb : noPushBefore cd k 32 = true) :
    noPushBefore cd (k + s) 32 = true := by
  rw [noPushBefore_eq_true_iff cd (k + s) 32 (le_refl 32)]
  intro p h1 h2 hp h3 h4 h5
  rcases Nat.lt_trichotomy p k with hlt | heq | hgt
  · exact (noPushBefore_eq_true_iff cd k 32 (le_refl 32)).mp hb p
      (by omega) hlt hp h3 h4 (by omega)
  · subst heq
    rcases hinst hp with ⟨_, _, hs⟩ | ⟨_, hs⟩ <;> exfalso <;> omega
  · have hk : k < cd.size := by omega
    rcases hinst hk with ⟨hlo, hhi, hs⟩ | ⟨_, hs⟩
    · by_cases hq : noPushBefore cd p 32 = true
      · exfalso
        have h := (noPushBefore_eq_true_iff cd p 32 (le_refl 32)).mp hq k
          (by omega) hgt hk hlo hhi (by omega)
        rw [h] at hb; cases hb
      · simpa using hq
    · exfalso; omega

/-- One step of the boundary walk along a compiled block.  `(b :: ys) ++ zs`
sits at `k` and `b :: ys` is the complete encoding of one instruction, so the
"no `PUSH` immediate covers this position" property moves to `k + s`, where the
rest of the block still sits. -/
lemma noPushBefore_peel {code : ByteArray} {k s : Nat} {b : UInt8} {ys zs : Bytes}
    (h : List.Slice code.toList k ((b :: ys) ++ zs))
    (hb : noPushBefore code k 32 = true)
    (hs : s = ys.length + 1)
    (hinst : (96 ≤ b.toNat ∧ b.toNat ≤ 127 ∧ s = b.toNat - 94) ∨
             ((b.toNat < 96 ∨ 127 < b.toNat) ∧ ys = [])) :
    noPushBefore code (k + s) 32 = true ∧ List.Slice code.toList (k + s) zs := by
  have hlen : (b :: ys).length = s := by simp [hs]
  constructor
  · refine noPushBefore_add (fun hk => ?_) hb
    rw [ByteArray.getElem_of_getElem?_eq_some'
      (List.get?_eq_of_slice (List.slice_prefix h)) hk]
    rcases hinst with hp | ⟨hnp, hnil⟩
    · exact Or.inl hp
    · exact Or.inr ⟨hnp, by simp [hs, hnil]⟩
  · have hsuf := List.slice_suffix h
    rwa [hlen] at hsuf

/-- The number of immediate bytes consumed by a byte which is a `PUSH1`--`PUSH32`.

This deliberately follows `noPushBefore`, which only treats the PUSH opcode
range specially.  Jaune's Osaka decoder also gives DUPN, SWAPN, and EXCHANGE
one immediate byte, but those bytes do not affect `jumpable` and hence do not
belong in this scan. -/
def pushWidth (b : UInt8) : Nat :=
  if 0x60 ≤ b.toNat ∧ b.toNat ≤ 0x7f then b.toNat - 0x5f else 0

private def scanStarts : List UInt8 → Nat → List Bool
  | [], _ => []
  | _ :: bs, n + 1 => false :: scanStarts bs n
  | b :: bs, 0 => true :: scanStarts bs (pushWidth b)

private lemma scanStarts_skip (xs : List UInt8) :
    ∀ n, n ≤ xs.length →
      scanStarts xs n = List.replicate n false ++ scanStarts (xs.drop n) 0 := by
  intro n
  induction n generalizing xs with
  | zero => simp
  | succ n ih =>
    intro h
    cases xs with
    | nil => simp at h
    | cons b bs =>
      have hbs : n ≤ bs.length := by simp at h; omega
      simp only [scanStarts]
      rw [ih bs hbs]
      simp [List.drop, List.replicate_succ, List.cons_append]

private lemma getD_replicate_shift (q j : Nat) (xs : List Bool) :
    (List.replicate q false ++ xs).getD (q + j) false = xs.getD j false := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show Nat.succ q + j = q + (j + 1) by omega]
    simp only [List.replicate_succ, List.getD_eq_getElem?_getD]
    exact ih

/-- The linear forward instruction-start scan.

The list has one flag for each byte: a `true` flag is an instruction start,
and a `false` flag is a byte consumed as PUSH immediate data. -/
def opStarts (cd : ByteArray) : List Bool :=
  scanStarts cd.data.toList 0

/-- `instStarts` reads `cd.data.toList`, a projection, because `ByteArray.toList`'s
index loop is quadratic under kernel reduction; the two lists are equal. -/
private lemma instStarts_eq (cd : ByteArray) : opStarts cd = scanStarts cd.toList 0 := by
  rw [opStarts, ByteArray.toList_eq_toList_data']

def opStartAt (cd : ByteArray) (k : Nat) : Bool :=
  (opStarts cd).getD k false

private inductive Ops : List UInt8 → Prop
  | nil : Ops []
  | step (b : UInt8) (ys rest : List UInt8)
      (hy : ys.length = pushWidth b) (hr : Ops rest) :
      Ops ((b :: ys) ++ rest)

private def ScanCover (xs : List UInt8) (k : Nat) : Prop :=
  ∃ pre b ys rest, xs = pre ++ (b :: ys) ++ rest ∧ Ops pre ∧
    pre.length + 1 + ys.length = k ∧ ys.length < pushWidth b

private lemma scanStarts_false_cover :
    ∀ n, ∀ xs : List UInt8, xs.length = n →
      ∀ k, k < xs.length →
      (scanStarts xs 0).getD k false = false → ScanCover xs k := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs hxs k hk hf
    cases xs with
    | nil => simp at hxs hk
    | cons b bs =>
      simp only [List.length_cons] at hxs hk
      cases k with
      | zero => simp [scanStarts] at hf
      | succ j =>
        simp only [scanStarts, List.getD_cons_succ] at hf
        have hj : j < bs.length := by omega
        by_cases hq : pushWidth b = 0
        · have hf0 : (scanStarts bs 0).getD j false = false := by simpa [hq] using hf
          have hc := ih bs.length (by omega) bs rfl j hj hf0
          rcases hc with ⟨pre, c, ys, rest, heq, hpre, hlen, hys⟩
          refine ⟨(b :: []) ++ pre, c, ys, rest, ?_, ?_, ?_, hys⟩
          · simp [heq, List.append_assoc]
          · exact Ops.step b [] pre (by simp [hq]) hpre
          · simp only [List.length_cons, List.length_nil, List.length_append]
            omega
        · by_cases hsmall : j < pushWidth b
          · refine ⟨[], b, bs.take j, bs.drop j, ?_, Ops.nil, ?_, ?_⟩
            · simp [List.take_append_drop]
            · simp [List.length_take_of_le (Nat.le_of_lt hj), Nat.add_comm]
            · rw [List.length_take_of_le (Nat.le_of_lt hj)]
              exact hsmall
          · have hqj : pushWidth b ≤ j := by omega
            have hqbs : pushWidth b ≤ bs.length := le_trans hqj (Nat.le_of_lt hj)
            have hskip := scanStarts_skip bs (pushWidth b) hqbs
            rw [hskip] at hf
            have hf' :
                (scanStarts (bs.drop (pushWidth b)) 0).getD
                    (j - pushWidth b) false = false := by
              rw [← getD_replicate_shift (pushWidth b) (j - pushWidth b)]
              simpa [Nat.add_sub_of_le hqj] using hf
            have hdrop : (bs.drop (pushWidth b)).length < n := by
              simp [List.length_drop]
              omega
            have hc := ih (bs.drop (pushWidth b)).length hdrop
              (bs.drop (pushWidth b)) rfl (j - pushWidth b) (by
                simp [List.length_drop]
                omega) hf'
            rcases hc with ⟨pre, c, ys, rest, heq, hpre, hlen, hys⟩
            have htake : (bs.take (pushWidth b)).length = pushWidth b :=
              List.length_take_of_le hqbs
            refine ⟨(b :: bs.take (pushWidth b)) ++ pre, c, ys, rest,
              ?_, ?_, ?_, hys⟩
            · calc
                b :: bs = b :: (bs.take (pushWidth b) ++ bs.drop (pushWidth b)) := by
                  rw [List.take_append_drop]
                _ = b :: (bs.take (pushWidth b) ++ (pre ++ (c :: ys) ++ rest)) := by
                  rw [heq]
                _ = (b :: bs.take (pushWidth b)) ++ pre ++ (c :: ys) ++ rest := by
                  simp [List.append_assoc]
            · exact Ops.step b (bs.take (pushWidth b)) pre htake hpre
            · simp only [List.length_cons, List.length_append]
              omega

private def ScanPrefix (xs : List UInt8) (rem k : Nat) : Prop :=
  ∃ ys pre rest, xs = ys ++ pre ++ rest ∧ ys.length = rem ∧
    rem ≤ k ∧ k < xs.length ∧ pre.length = k - rem ∧ Ops pre

private lemma scanPrefix_cons_skip :
    ScanPrefix (b :: bs) (r + 1) (j + 1) ↔ ScanPrefix bs r j := by
  constructor
  · rintro ⟨ys, pre, rest, heq, hys, hrj, hbound, hpre, hi⟩
    cases ys with
    | nil => simp at hys
    | cons y ys' =>
      cases heq
      simp only [List.length_cons] at hys
      refine ⟨ys', pre, rest, rfl, by omega, by omega, ?_, ?_, hi⟩
      · exact Nat.lt_of_succ_lt_succ hbound
      · omega
  · rintro ⟨ys, pre, rest, heq, hys, hrj, hbound, hpre, hi⟩
    refine ⟨b :: ys, pre, rest, ?_, by simp [hys], by omega, ?_, ?_, hi⟩
    · simp [heq]
    · simp at hbound ⊢
      omega
    · omega

private lemma instrs_cons_inv {b : UInt8} {xs : List UInt8} (h : Ops (b :: xs)) :
    ∃ ys rest, xs = ys ++ rest ∧ ys.length = pushWidth b ∧ Ops rest := by
  cases h with
  | step b ys rest hy hr => exact ⟨ys, rest, rfl, hy, hr⟩

private lemma pushWidth_spec (b : UInt8) :
    (96 ≤ b.toNat ∧ b.toNat ≤ 127 ∧ pushWidth b = b.toNat - 95) ∨
    ((b.toNat < 96 ∨ 127 < b.toNat) ∧ pushWidth b = 0) := by
  unfold pushWidth
  by_cases h : 96 ≤ b.toNat ∧ b.toNat ≤ 127
  · left; simp [h]
  · right
    constructor
    · omega
    · simp [h]

private lemma noPushBefore_instrs {cd : ByteArray} {k : Nat}
    {pre rest : List UInt8}
    (hslice : List.Slice cd.toList k (pre ++ rest))
    (hb : noPushBefore cd k 32 = true) (hpre : Ops pre) :
    noPushBefore cd (k + pre.length) 32 = true ∧
      List.Slice cd.toList (k + pre.length) rest := by
  induction hpre generalizing k rest with
  | nil =>
    simpa using And.intro hb hslice
  | @step b ys rest0 hy hr ih =>
    have hinst :
        (96 ≤ b.toNat ∧ b.toNat ≤ 127 ∧ ys.length + 1 = b.toNat - 94) ∨
          ((b.toNat < 96 ∨ 127 < b.toNat) ∧ ys = []) := by
      rcases pushWidth_spec b with ⟨hlo, hhi, hw⟩ | ⟨hnp, hw⟩
      · left
        refine ⟨hlo, hhi, ?_⟩
        calc
          ys.length + 1 = (b.toNat - 95) + 1 := by rw [hy, hw]
          _ = b.toNat - 94 := by omega
      · right
        refine ⟨hnp, ?_⟩
        have : ys.length = 0 := by simpa [hw] using hy
        simpa using this
    have hpeel := noPushBefore_peel (code := cd) (k := k)
      (s := ys.length + 1) (b := b) (ys := ys) (zs := rest0 ++ rest)
      (by simpa [List.append_assoc] using hslice) hb rfl hinst
    rcases ih (k := k + ys.length + 1) (rest := rest) hpeel.2 hpeel.1
      with ⟨hnext, hslice'⟩
    constructor
    · simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hnext
    · simpa [List.length_append, Nat.add_assoc, Nat.add_left_comm,
        Nat.add_comm] using hslice'

private lemma scanStarts_true_iff :
    ∀ n, ∀ xs : List UInt8, xs.length = n →
      ∀ rem k, k < xs.length →
      ((scanStarts xs rem).getD k false = true ↔ ScanPrefix xs rem k) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro xs hxs rem k hk
    cases xs with
    | nil => simp at hxs hk
    | cons b bs =>
      simp only [List.length_cons] at hxs hk
      cases rem with
      | zero =>
        cases k with
        | zero => simp [scanStarts, ScanPrefix, Ops.nil]
        | succ j =>
          simp only [scanStarts, List.getD_cons_succ]
          have hbs : bs.length = n - 1 := by omega
          have hj : j < bs.length := by omega
          have hi := ih bs.length (by omega) bs rfl (pushWidth b) j hj
          rw [hi]
          constructor
          · rintro ⟨ys, pre, rest, heq, hys, hqj, hbound, hpre, hinst⟩
            refine ⟨[], (b :: ys) ++ pre, rest, ?_, by simp, by omega,
              by omega, ?_, ?_⟩
            · simp [heq, List.append_assoc]
            · simp [hpre]
              rw [hys]
              omega
            · exact Ops.step b ys pre hys hinst
          · rintro ⟨ys, pre, rest, heq, hys, hqj, hbound, hpre, hinst⟩
            have hys0 : ys = [] := by simpa using hys
            subst ys
            have hpre' : pre ≠ [] := by
              intro hnil
              simp [hnil] at hpre
            cases pre with
            | nil => contradiction
            | cons c pre' =>
              have heq' : b :: bs = c :: pre' ++ rest := by simpa using heq
              cases heq'
              rcases instrs_cons_inv hinst with ⟨ys', tail, htail, hq, hr'⟩
              have htail_len : tail.length = j - pushWidth b := by
                simp only [List.length_cons] at hpre
                simp [htail, hq] at hpre
                omega
              have hp_tail : ScanPrefix (pre' ++ rest) (pushWidth b) j := by
                have hqj' : pushWidth b ≤ j := by
                  simp [htail, hq] at hpre
                  omega
                refine ⟨ys', tail, rest, ?_, hq, hqj', ?_, htail_len, hr'⟩
                · simp [htail, List.append_assoc]
                · omega
              exact hp_tail
      | succ rem =>
        cases k with
        | zero => simp [scanStarts, ScanPrefix]
        | succ j =>
          simp only [scanStarts, List.getD_cons_succ]
          have hbs : bs.length = n - 1 := by omega
          have hj : j < bs.length := by omega
          have hi := ih bs.length (by omega) bs rfl rem j hj
          rw [hi, scanPrefix_cons_skip]

private lemma noPushBefore_of_scan_start {cd : ByteArray} {k : Nat}
    (hk : k < cd.size) (hstart : opStartAt cd k = true) :
    noPushBefore cd k 32 = true := by
  have hk' : k < cd.toList.length := by
    simpa [ByteArray.size_eq_length_toList'] using hk
  have hs : (scanStarts cd.toList 0).getD k false = true := by
    simpa [opStartAt, instStarts_eq] using hstart
  have hp := (scanStarts_true_iff cd.toList.length cd.toList rfl 0 k hk').mp hs
  rcases hp with ⟨ys, pre, rest, heq, hys, hzero, hbound, hpre, hinst⟩
  have hys0 : ys = [] := by simpa using hys
  subst ys
  have hslice : List.Slice cd.toList 0 (pre ++ rest) := by
    have heq' : cd.toList = pre ++ rest := by simpa using heq
    rw [heq']
    simpa using List.slice_refl (pre ++ rest)
  have hno := noPushBefore_instrs hslice (by rfl) hinst
  have hpre_len : pre.length = k := by simpa using hpre
  simpa [hpre_len] using hno.1

private lemma noPushBefore_iff_scan_start {cd : ByteArray} {k : Nat}
    (hk : k < cd.size) :
    noPushBefore cd k 32 = true ↔ opStartAt cd k = true := by
  constructor
  · intro hn
    by_cases hstart : opStartAt cd k = true
    · exact hstart
    · have hstart' : opStartAt cd k = false := by
        cases h : opStartAt cd k <;> simp_all
      have hk' : k < cd.toList.length := by
        simpa [ByteArray.size_eq_length_toList'] using hk
      have hs : (scanStarts cd.toList 0).getD k false = false := by
        simpa [opStartAt, instStarts_eq] using hstart'
      have hc := scanStarts_false_cover cd.toList.length cd.toList rfl k hk' hs
      rcases hc with ⟨pre, b, ys, rest, heq, hpre, hlen, hys⟩
      have hslice : List.Slice cd.toList 0 (pre ++ ((b :: ys) ++ rest)) := by
        rw [heq]
        simpa [List.append_assoc] using List.slice_refl _
      have hpre_no := noPushBefore_instrs (cd := cd) (k := 0) (pre := pre)
        (rest := (b :: ys) ++ rest) hslice (by rfl) hpre
      have hpre_no' : noPushBefore cd pre.length 32 = true := by
        simpa using hpre_no.1
      have hslice_p : List.Slice cd.toList pre.length (b :: ys ++ rest) := by
        rw [heq]
        simpa [List.append_assoc] using
          (List.append_slice_suffix (xs := pre) (ys := (b :: ys) ++ rest))
      have hget : cd.toList[pre.length]? = some b :=
        List.get?_eq_of_slice hslice_p
      have hp_lt_list : pre.length < cd.toList.length :=
        (List.getElem?_eq_some_iff.mp hget).1
      have hp_lt : pre.length < cd.size := by
        simpa [ByteArray.size_eq_length_toList'] using hp_lt_list
      have hbyte : cd[pre.length] = b :=
        ByteArray.getElem_of_getElem?_eq_some' hget hp_lt
      rcases pushWidth_spec b with ⟨hlo, hhi, hw⟩ | ⟨hnp, hw⟩
      · have hwidth : pushWidth b ≤ 32 := by omega
        have hlo' : 96 ≤ cd[pre.length].toNat := by simpa [hbyte] using hlo
        have hhi' : cd[pre.length].toNat ≤ 127 := by simpa [hbyte] using hhi
        have hfalse := (noPushBefore_eq_true_iff cd k 32 (le_refl 32)).mp hn
          pre.length (by omega) (by omega) hp_lt hlo' hhi' (by simpa [hbyte] using
            (show k ≤ pre.length + (b.toNat - 95) by omega))
        rw [hfalse] at hpre_no'
        contradiction
      · have : ys.length < 0 := by simp [hw] at hys
        omega
  · exact noPushBefore_of_scan_start hk

/-- A byte is an accepted jump destination exactly when it is an in-range
JUMPDEST at a start found by the linear scan. -/
def jumpdestOk (cd : ByteArray) (k : Nat) : Bool :=
  if hk : k < cd.size then
    decide (cd[k] = JumpOp.toUInt8 .jumpdest ∧ opStartAt cd k = true)
  else false

theorem jumpable_eq_jumpdestOk (cd : ByteArray) (k : Nat) :
    jumpable cd k = jumpdestOk cd k := by
  unfold jumpable jumpdestOk
  split
  · rename_i hk
    split
    · rename_i hbyte
      simp [hbyte]
      apply Bool.eq_iff_iff.mpr
      exact noPushBefore_iff_scan_start hk
    · rename_i hbyte
      simp [hbyte]
  · rename_i hk
    simp

--------------- EIP-8024 AND THE JUMP-DESTINATION SET ---------------

-- At the v21 conformance pin, Amsterdam uses the legacy forward walk.
-- The interpreter retains its backward `jumpable`/`noPushBefore` scan;
-- `scripts/check-jumpdest.sh` samples the bridge between those algorithms.

/-- The pre-Amsterdam walk: the same pass with no immediate-carrying opcode
other than the pushes, which is the walk `noPushBefore` characterises. -/
def legacyJumpDestsFrom (cd : ByteArray) (pc : Nat) : List Nat :=
  if h : pc < cd.size then
    let b := cd[pc]
    if b = 0x5B then pc :: legacyJumpDestsFrom cd (pc + 1)
    else if 0x60 ≤ b ∧ b ≤ 0x7F then legacyJumpDestsFrom cd (pc + (b.toNat - 0x5F) + 1)
    else legacyJumpDestsFrom cd (pc + 1)
  else []
termination_by cd.size - pc
decreasing_by all_goals omega

/-- The legacy walk steps off a byte that is neither `JUMPDEST` nor a
`PUSH1`–`PUSH32` without adding a destination. -/
theorem legacyJumpDestsFrom_skip (cd : ByteArray) (pc : Nat)
    (hj : cd.byteD pc ≠ 0x5B) (hp : ¬ (0x60 ≤ cd.byteD pc ∧ cd.byteD pc ≤ 0x7F)) :
    legacyJumpDestsFrom cd pc = legacyJumpDestsFrom cd (pc + 1) := by
  rw [legacyJumpDestsFrom]
  split
  · rename_i h
    have hb : cd[pc] = cd.byteD pc := by simp [ByteArray.byteD, h]
    simp only [hb]
    rw [ite_eq_right hj, ite_eq_right hp]
  · rename_i h
    rw [legacyJumpDestsFrom]
    rw [dite_eq_right (by omega)]

/-- The pinned Amsterdam `get_valid_jump_destinations` is the legacy walk:
only PUSH1–PUSH32 skip data. EELS #3618 removed the stack-access cases. -/
abbrev pinnedJumpDestsFrom := legacyJumpDestsFrom

/-- The pinned and legacy forward walks are now definitionally identical. -/
theorem pinnedJumpDestsFrom_eq_legacy (cd : ByteArray) (pc : Nat) :
    pinnedJumpDestsFrom cd pc = legacyJumpDestsFrom cd pc := rfl

def JumpOp.runCore (pc : Nat) (devm : Devm) (sevm : Sevm) :
    JumpOp → Except (EvmError × Devm) (Nat × Devm)
  | .jumpdest => do
    let devm' ← chargeGas Gas.jumpdest devm
    .ok ⟨pc + 1, devm'⟩
  | .jump => do
    let ⟨jump_dest, devm'⟩ ← devm.pop
    let devm'' ← chargeGas Gas.mid devm'
    .assert
      (jumpable sevm.code jump_dest.toNat)
      ⟨.halt (.invalidJumpDest .none), devm''⟩
    .ok ⟨jump_dest.toNat, devm''⟩
  | .jumpi => do
    let ⟨dest, devm'⟩ ← devm.pop
    let ⟨cond, devm''⟩ ← devm'.pop
    let devm''' ← chargeGas Gas.high devm''
    let pc' : Nat ←
      if cond = 0
      then .ok <| pc + 1
      else
        .assert
          (jumpable sevm.code dest.toNat)
          ⟨.halt (.invalidJumpDest .none), devm'''⟩
        .ok dest.toNat
    .ok ⟨pc', devm'''⟩

def JumpOp.run (evm : Evm) (j : JumpOp) : Except (EvmError × Devm) (Nat × Devm) :=
  JumpOp.runCore evm.pc evm.dyna evm.sta j

def State.bal (w : State) (a : Address) : U256 := (w.get a).balance

def State.setBal (st : State) (adr : Address) (val : U256) : State :=
  st.setAccount adr <| (st.get adr).withBalance val

def State.addBal (st : State) (adr : Address) (val : U256) : State :=
  st.setBal adr <| (st.bal adr + val)

def State.subBal (st : State) (adr : Address) (val : U256) : Option State :=
  if st.bal adr < val
  then .none
  else st.setBal adr (st.bal adr - val)

def Benv.setBal (benv : Benv) (adr : Address) (val : U256) : Benv :=
  ({benv with state := benv.state.setBal adr val} : Benv).clearStorageWritesIfEmpty adr

def Benv.subBal (benv : Benv) (adr : Address) (val : U256) : Option Benv := do
  let wor ← benv.state.subBal adr val
  some <| (benv.withState wor).clearStorageWritesIfEmpty adr

def Benv.addBal (benv : Benv) (adr : Address) (val : U256) : Benv :=
  (benv.withState (benv.state.addBal adr val)).clearStorageWritesIfEmpty adr

def Devm.setBal (devm : Devm) (adr : Address) (val : U256) : Devm :=
  (devm.withState (devm.state.setBal adr val)).clearStorageWritesIfEmpty adr

def Devm.subBal (devm : Devm) (adr : Address) (val : U256) : Option Devm := do
  let state ← devm.state.subBal adr val
  some <| (devm.withState state).clearStorageWritesIfEmpty adr

def Devm.addBal (devm : Devm) (adr : Address) (val : U256) : Devm :=
  (devm.withState (devm.state.addBal adr val)).clearStorageWritesIfEmpty adr

/-- `SELFDESTRUCT`'s beneficiary credit: EELS `set_account_balance`, then
"mark beneficiary as touched" (`account_exists_and_is_empty`).

From Paris (`settle.eraseEmptyOnModify`) the credit is `Devm.addBal`, whose
`modify_state` erases an account it leaves empty, so the beneficiary can never
be touched and empty and the touch is moot. Before Paris `modify_state` is
`set_account` alone: a zero credit to a storage-only beneficiary keeps it,
storage and all, and the touch hands it to the EIP-161 sweep, which erases it
at the end of the transaction unless something funds it first.

Every other account-field write Jaune makes before Paris goes through the
erasing `State.setAccount`, because none of them can leave an account empty
where EELS would keep it: a value transfer moves a nonzero value from a caller
that has code or a nonzero nonce; nonce increments and code deposits leave a
nonzero nonce; block and ommer rewards are positive; and the coinbase fee
credit is EELS's own explicit `destroy_account` of an emptied coinbase.
The touch is recorded after the credit rather than after the donor's balance is
zeroed: the donor has code or a nonzero nonce, so zeroing it cannot change
whether the beneficiary exists and is empty. -/
def Devm.creditBeneficiary (rules : ForkRules) (donee : Address) (val : U256)
    (devm : Devm) : Devm :=
  if rules.settlement.eraseEmptyOnModify then devm.addBal donee val
  else
    (devm.withState (devm.state.setPresent donee
      ((devm.state.get donee).withBalance (devm.state.bal donee + val)))).recordTouch
      rules true donee

/-- Under the erasing rules (Paris on) the beneficiary credit is `addBal`. -/
@[simp] theorem Devm.creditBeneficiary_of_eraseEmptyOnModify {rules : ForkRules}
    (h : rules.settlement.eraseEmptyOnModify = true) (donee : Address) (val : U256)
    (devm : Devm) : devm.creditBeneficiary rules donee val = devm.addBal donee val := by
  simp [Devm.creditBeneficiary, h]

/-- The credit moves only the world and the touched set: the machine, and with
it memory and gas, is unchanged. -/
@[simp] theorem Devm.creditBeneficiary_mach (rules : ForkRules) (donee : Address)
    (val : U256) (devm : Devm) : (devm.creditBeneficiary rules donee val).mach = devm.mach := by
  unfold Devm.creditBeneficiary; split <;> rfl

@[simp] theorem Devm.creditBeneficiary_output (rules : ForkRules) (donee : Address)
    (val : U256) (devm : Devm) :
    (devm.creditBeneficiary rules donee val).output = devm.output := by
  unfold Devm.creditBeneficiary; split <;> rfl

@[simp] theorem Devm.creditBeneficiary_memory (rules : ForkRules) (donee : Address)
    (val : U256) (devm : Devm) :
    (devm.creditBeneficiary rules donee val).memory = devm.memory := by
  unfold Devm.creditBeneficiary; split <;> rfl

@[simp] theorem pragueRules_settle_eraseEmptyOnModify :
    pragueRules.settlement.eraseEmptyOnModify = true := rfl

def HaltOp.run (sevm : Sevm) (devm : Devm) :
    HaltOp → Except (EvmError × Devm) Devm
  | .stop => .ok devm
  | .revert => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas extend_memory_cost devm
    let ⟨output, devm⟩ := devm.memRead memory_start_index size
    let devm := devm.withOutput output
    .error ⟨.revert, devm⟩
  | .return_ => do
    let ⟨index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let cost := devm.extCost [⟨index, size⟩]
    let devm ← chargeGas cost devm
    let ⟨output, devm⟩ := devm.memRead index size
    .ok (devm.withOutput output)
  -- `vm/instructions/system.py` `selfdestruct`. The two shapes differ in more
  -- than numbers, so this is a `match` on the switch: Amsterdam moves the
  -- static check ahead of the pop, checks the access cost before warming the
  -- beneficiary, replaces the 25,000 new-account charge by `ACCOUNT_WRITE`
  -- (execution) plus `NEW_ACCOUNT` (state) when the sweep creates the
  -- beneficiary, logs the sweep, and schedules the originator without zeroing
  -- it -- settlement preserves its balance (EIP-8246). Under `none` the body
  -- below is the body it has always been.
  | .selfdestruct =>
    match sevm.benvStat.rules.stateGas with
    | none => do
      let donor := sevm.currentTarget
      let ⟨donee, devm⟩ ← devm.popToAdr
      -- `is_account_alive(beneficiary)` and `get_account(originator)`
      -- (EIP-7928; the identity under this lane's `bal = none`).
      let devm := (devm.balReadAccount sevm.benvStat.rules donee).balReadAccount
        sevm.benvStat.rules donor
      let donorBal ← .ok (devm.getAcct sevm.currentTarget).balance
      let ⟨devm, gasCost2⟩ ← .ok <|
        match sevm.benvStat.rules.access with
        | .eip2929 =>
        if donee ∉ devm.accessedAddresses
          then
            ( ⟨ addAccessedAddress devm donee,
                Gas.selfdestruct + sevm.benvStat.rules.gas.coldAccountAccess ⟩ : Devm × Nat )
          else
            ⟨devm, Gas.selfdestruct⟩
        | .flat _ => (⟨devm, Gas.selfdestruct⟩ : Devm × Nat)
      let gasCost3 ← .ok <|
        if (devm.getAcct donee).isEmpty ∧ donorBal ≠ 0 then
          gasCost2 + Gas.selfdestructNewAccount
        else
          gasCost2
      let devm ← chargeGas gasCost3 devm
      assertDynamic sevm devm
      let devm ←
        (devm.subBal donor donorBal).toExcept
          ⟨.internal (.invariant (.text "InsufficientBalanceError")), devm⟩
      let devm ← .ok <| devm.creditBeneficiary sevm.benvStat.rules donee donorBal
      -- EIP-6780 (Cancun): only an account created in the same transaction is
      -- scheduled for deletion; before that every `SELFDESTRUCT` schedules.
      -- That is `¬ (onlyCreated ∧ donor ∉ created)`, i.e. the disjunction
      -- below; under `selfdestructOnlyCreated` its taken branch is the old
      -- scheduling body plus the refund hook. The hook credits
      -- `selfdestructRefund` (24000 before EIP-3529, 0 from London) when this
      -- `SELFDESTRUCT` newly schedules the donor. The EIP-7928 beneficiary
      -- read is the `balReadAccount` above; the EIP-161 touch is in
      -- `creditBeneficiary`.
      if donor ∈ devm.createdAccounts ∨
          sevm.benvStat.rules.settlement.selfdestructOnlyCreated = false then
        .ok (creditSelfdestructRefund sevm.benvStat.rules
          (donor ∈ devm.accountsToDelete)
          (addAccountToDelete (devm.setBal donor 0) donor))
      else
        .ok devm
    | some state => do
      assertDynamic sevm devm
      let donor := sevm.currentTarget
      let ⟨donee, devm⟩ ← devm.popToAdr
      -- GAS (state-independent), checked before the beneficiary is warmed.
      let cold := donee ∉ devm.accessedAddresses
      let gasCost :=
        Gas.selfdestruct +
          (if cold then sevm.benvStat.rules.gas.coldAccountAccess else 0)
      .assert (gasCost ≤ devm.gasLeft) ⟨.halt (.outOfGas .none), devm⟩
      -- STATE ACCESS: the beneficiary is warmed, then `is_account_alive` reads
      -- it and `get_account` reads the originator (EIP-7928), before the
      -- charges below.
      let devm := if cold then addAccessedAddress devm donee else devm
      let devm := (devm.balReadAccount sevm.benvStat.rules donee).balReadAccount
        sevm.benvStat.rules donor
      let donorBal := (devm.getAcct donor).balance
      -- STATE GAS. A sweep that will create the beneficiary pays the account
      -- write and the creation. Execution gas before state gas.
      let creating := (devm.getAcct donee).isEmpty ∧ donorBal ≠ 0
      let devm ← chargeGas (gasCost + if creating then state.accountWrite else 0) devm
      let devm ← chargeStateGas (if creating then state.newAccount else 0) devm
      -- OPERATION: move the whole balance, log it, schedule the deletion.
      let devm ←
        (devm.subBal donor donorBal).toExcept
          ⟨.internal (.invariant (.text "InsufficientBalanceError")), devm⟩
      let devm := devm.addBal donee donorBal
      let devm := devm.emitTransferLog donor donee donorBal
      if donor ∈ devm.createdAccounts then
        .ok (addAccountToDelete devm donor)
      else
        .ok devm

def calculateMsgCallGas
  (value gas gas_left memory_cost extra_gas : Nat)
  (cs : Nat := Gas.callStipend) : Nat × Nat :=
  let call_stipend : Nat := if value = 0 then 0 else cs
  if gas_left < extra_gas + memory_cost
  then ⟨gas + extra_gas, gas + call_stipend⟩
  else
    let gas' := min gas (except64th (gas_left - memory_cost - extra_gas))
    ⟨gas' + extra_gas, gas' + call_stipend⟩

/-! ### The zero-meter invariant

Under `rules.stateGas = none` no meter operation above is ever reached, so a
frame's meter is `zero` at entry and `zero` for ever after. That is what makes
"the `none` path is today's path" a fact rather than a claim: with the meter
zero, `gasMeasure` *is* `gasLeft`, and every Prague-stated termination fact is
the one it always was.

The predicate is stated here, beside the meter; the preservation theorems are
stated where the switch is read. -/

/-- The frame meters in one dimension: no reservoir, no spill, no commitment. -/
def Devm.StateGasZero (devm : Devm) : Prop := devm.mach.stateGas = .zero

instance {devm : Devm} : Decidable devm.StateGasZero := by
  unfold Devm.StateGasZero; infer_instance

/-- State-gas preservation for machine-result carriers.  The failing machine
is just as observable as the successful payload, so both channels carry the
zero-meter obligation. -/
def Except.StateGasZeroOn {ρ α : Type} (P : α → Prop) :
    Except (ρ × Devm) α → Prop
  | .ok a => P a
  | .error e => e.2.StateGasZero

/-- The zero-meter invariant on an execution result, on both channels. -/
abbrev Execution.StateGasZero (x : Execution) : Prop :=
  x.StateGasZeroOn Devm.StateGasZero

theorem Except.StateGasZeroOn.bind {ρ α β : Type} {P : α → Prop} {Q : β → Prop}
    {x : Except (ρ × Devm) α} {f : α → Except (ρ × Devm) β}
    (hx : x.StateGasZeroOn P)
    (hf : ∀ a, P a → (f a).StateGasZeroOn Q) :
    (x >>= f).StateGasZeroOn Q := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem Except.StateGasZeroOn.map {ρ α β : Type} {P : α → Prop} {Q : β → Prop}
    {x : Except (ρ × Devm) α} {f : α → β}
    (hx : x.StateGasZeroOn P) (hf : ∀ a, P a → Q (f a)) :
    (x <&> f).StateGasZeroOn Q := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem Except.stateGasZeroOn_ok {ρ α : Type} {P : α → Prop} {a : α}
    (h : P a) :
    (Except.ok a : Except (ρ × Devm) α).StateGasZeroOn P := h

theorem Except.stateGasZeroOn_error {ρ α : Type} {P : α → Prop}
    {e : ρ × Devm} (h : e.2.StateGasZero) :
    (Except.error e : Except (ρ × Devm) α).StateGasZeroOn P := h

theorem Except.stateGasZeroOn_assert {p : Prop} [Decidable p] {ρ : Type}
    {e : ρ × Devm} (h : e.2.StateGasZero) :
    (Except.assert p e).StateGasZeroOn (fun _ => True) := by
  unfold Except.assert
  split
  · trivial
  · exact h

/-- A footprint result preserves the state-gas record of its input machine on
both channels. -/
def Footprint.StateGasEq {α : Type} (before : Mach) :
    Footprint.Outcome Mach α → Prop
  | .error (_, mach) => mach.stateGas = before.stateGas
  | .ok (_, mach) => mach.stateGas = before.stateGas

def Footprint.MachMetaStateGasEq {α : Type} (before : Mach) :
    Footprint.Outcome (Mach × Meta) α → Prop
  | .error (_, view) => view.1.stateGas = before.stateGas
  | .ok (_, view) => view.1.stateGas = before.stateGas

/-- A Mach-only footprint preserves the zero meter whenever its core leaves
the `stateGas` field unchanged on both result channels. -/
theorem liftMach_stateGasZeroOn {α : Type}
    {core : Mach → Footprint.Outcome Mach α} {devm : Devm}
    (h : devm.StateGasZero)
    (hc : Footprint.StateGasEq devm.mach (core devm.mach)) :
    (liftMach core devm).StateGasZeroOn (fun a => a.2.StateGasZero) := by
  unfold liftMach Footprint.liftOutcome
  split <;> simp_all [Footprint.StateGasEq, Except.StateGasZeroOn,
    Devm.StateGasZero, Devm.setMach]

theorem Footprint.toExecution_stateGasZero {x : Except _ (Unit × Devm)}
    (hx : x.StateGasZeroOn (fun a => a.2.StateGasZero)) :
    (Footprint.toExecution x).StateGasZero := by
  cases x with
  | error e => exact hx
  | ok a => exact hx

theorem liftMachExecution_stateGasZero
    {core : Mach → Footprint.Outcome Mach Unit} {devm : Devm}
    (h : devm.StateGasZero)
    (hc : Footprint.StateGasEq devm.mach (core devm.mach)) :
    (liftMachExecution core devm).StateGasZero := by
  cases hcore : core devm.mach with
  | error e =>
    rw [hcore] at hc
    simpa [liftMachExecution, Footprint.toExecution, liftMach,
      Footprint.liftOutcome, hcore, Execution.StateGasZero,
      Footprint.StateGasEq, Except.StateGasZeroOn, Devm.StateGasZero,
      Devm.setMach] using hc.trans h
  | ok a =>
    rw [hcore] at hc
    simpa [liftMachExecution, Footprint.toExecution, liftMach,
      Footprint.liftOutcome, hcore, Execution.StateGasZero,
      Footprint.StateGasEq, Except.StateGasZeroOn, Devm.StateGasZero,
      Devm.setMach] using hc.trans h

theorem liftMachMetaExecution_stateGasZero
    {core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit} {devm : Devm}
    (h : devm.StateGasZero)
    (hc : Footprint.MachMetaStateGasEq devm.mach (core devm.mach devm.meta)) :
    (liftMachMetaExecution core devm).StateGasZero := by
  cases hcore : core devm.mach devm.meta with
  | error e =>
    rw [hcore] at hc
    simpa [liftMachMetaExecution, Footprint.toExecution, liftMachMeta,
      Footprint.liftOutcome, hcore, Execution.StateGasZero,
      Footprint.MachMetaStateGasEq, Except.StateGasZeroOn,
      Devm.StateGasZero] using hc.trans h
  | ok a =>
    rw [hcore] at hc
    simpa [liftMachMetaExecution, Footprint.toExecution, liftMachMeta,
      Footprint.liftOutcome, hcore, Execution.StateGasZero,
      Footprint.MachMetaStateGasEq, Except.StateGasZeroOn,
      Devm.StateGasZero] using hc.trans h
theorem Mach.chargeGas_stateGas_eq (cost : Nat) (mach : Mach) :
    Footprint.StateGasEq mach (mach.chargeGas cost) := by
  cases hs : safeSub mach.gasLeft cost <;>
    simp [Mach.chargeGas, hs, Footprint.StateGasEq]

theorem Mach.push_stateGas_eq (x : U256) (mach : Mach) :
    Footprint.StateGasEq mach (mach.push x) := by
  by_cases hs : mach.stack.length < 1024 <;>
    simp [Mach.push, hs, Footprint.StateGasEq]

theorem Mach.pop_stateGas_eq (mach : Mach) :
    Footprint.StateGasEq mach mach.pop := by
  cases hs : mach.stack <;> simp [Mach.pop, hs, Footprint.StateGasEq]

theorem Mach.popToNat_stateGas_eq (mach : Mach) :
    Footprint.StateGasEq mach mach.popToNat := by
  unfold Mach.popToNat
  cases hp : mach.pop <;>
    have hm := Mach.pop_stateGas_eq mach <;> rw [hp] at hm <;> exact hm

theorem Mach.popToAdr_stateGas_eq (mach : Mach) :
    Footprint.StateGasEq mach mach.popToAdr := by
  unfold Mach.popToAdr
  cases hp : mach.pop <;>
    have hm := Mach.pop_stateGas_eq mach <;> rw [hp] at hm <;> exact hm

theorem Mach.popN_stateGas_eq (mach : Mach) (n : Nat) :
    Footprint.StateGasEq mach (mach.popN n) := by
  induction n generalizing mach with
  | zero => rfl
  | succ n ih =>
    unfold Mach.popN
    cases hp : mach.pop with
    | error e =>
      have hm := Mach.pop_stateGas_eq mach
      rw [hp] at hm
      exact hm
    | ok a =>
      have hm := Mach.pop_stateGas_eq mach
      rw [hp] at hm
      cases hn : a.2.popN n with
      | error e =>
        have hn' := ih a.2
        rw [hn] at hn'
        simpa [hp, hn, Footprint.StateGasEq] using hn'.trans hm
      | ok b =>
        have hn' := ih a.2
        rw [hn] at hn'
        simpa [hp, hn, Footprint.StateGasEq] using hn'.trans hm

theorem Mach.pushItem_stateGas_eq (x : U256) (cost : Nat) (mach : Mach) :
    Footprint.StateGasEq mach (mach.pushItem x cost) := by
  unfold Mach.pushItem
  cases hc : mach.chargeGas cost with
  | error e =>
    have hm := Mach.chargeGas_stateGas_eq cost mach
    rw [hc] at hm
    exact hm
  | ok a =>
    have hm := Mach.chargeGas_stateGas_eq cost mach
    rw [hc] at hm
    have hp := Mach.push_stateGas_eq x a.2
    cases hpush : a.2.push x <;> rw [hpush] at hp
    · simpa [hc, hpush, Footprint.StateGasEq] using hp.trans hm
    · simpa [hc, hpush, Footprint.StateGasEq] using hp.trans hm

theorem Mach.applyUnary_stateGas_eq (f : U256 → U256) (cost : Nat) (mach : Mach) :
    Footprint.StateGasEq mach (mach.applyUnary f cost) := by
  unfold Mach.applyUnary
  cases hp : mach.pop with
  | error e =>
    have hm := Mach.pop_stateGas_eq mach
    rw [hp] at hm
    exact hm
  | ok a =>
    have hm := Mach.pop_stateGas_eq mach
    rw [hp] at hm
    have ho := Mach.pushItem_stateGas_eq (f a.1) cost a.2
    cases hpush : a.2.pushItem (f a.1) cost <;> rw [hpush] at ho
    · simpa [hp, hpush, Footprint.StateGasEq] using ho.trans hm
    · simpa [hp, hpush, Footprint.StateGasEq] using ho.trans hm

theorem Mach.applyBinary_stateGas_eq (f : U256 → U256 → U256) (cost : Nat)
    (mach : Mach) :
    Footprint.StateGasEq mach (mach.applyBinary f cost) := by
  unfold Mach.applyBinary
  cases hp : mach.pop with
  | error e =>
    have hm := Mach.pop_stateGas_eq mach
    rw [hp] at hm
    exact hm
  | ok a =>
    have hm := Mach.pop_stateGas_eq mach
    rw [hp] at hm
    cases hp2 : a.2.pop with
    | error e =>
      have hm2 := Mach.pop_stateGas_eq a.2
      rw [hp2] at hm2
      simpa [hp, hp2, Footprint.StateGasEq] using hm2.trans hm
    | ok b =>
      have hm2 := Mach.pop_stateGas_eq a.2
      rw [hp2] at hm2
      have ho := Mach.pushItem_stateGas_eq (f a.1 b.1) cost b.2
      cases hpush : b.2.pushItem (f a.1 b.1) cost <;> rw [hpush] at ho
      · simpa [hp, hp2, hpush, Footprint.StateGasEq] using
          ho.trans (hm2.trans hm)
      · simpa [hp, hp2, hpush, Footprint.StateGasEq] using
          ho.trans (hm2.trans hm)

theorem Mach.applyTernary_stateGas_eq (f : U256 → U256 → U256 → U256)
    (cost : Nat) (mach : Mach) :
    Footprint.StateGasEq mach (mach.applyTernary f cost) := by
  unfold Mach.applyTernary
  cases hp : mach.pop with
  | error e =>
    have hm := Mach.pop_stateGas_eq mach
    rw [hp] at hm
    exact hm
  | ok a =>
    have hm := Mach.pop_stateGas_eq mach
    rw [hp] at hm
    cases hp2 : a.2.pop with
    | error e =>
      have hm2 := Mach.pop_stateGas_eq a.2
      rw [hp2] at hm2
      simpa [hp, hp2, Footprint.StateGasEq] using hm2.trans hm
    | ok b =>
      have hm2 := Mach.pop_stateGas_eq a.2
      rw [hp2] at hm2
      cases hp3 : b.2.pop with
      | error e =>
        have hm3 := Mach.pop_stateGas_eq b.2
        rw [hp3] at hm3
        simpa [hp, hp2, hp3, Footprint.StateGasEq] using
          hm3.trans (hm2.trans hm)
      | ok c =>
        have hm3 := Mach.pop_stateGas_eq b.2
        rw [hp3] at hm3
        have ho := Mach.pushItem_stateGas_eq (f a.1 b.1 c.1) cost c.2
        cases hpush : c.2.pushItem (f a.1 b.1 c.1) cost <;> rw [hpush] at ho
        · simpa [hp, hp2, hp3, hpush, Footprint.StateGasEq] using
            ho.trans (hm3.trans (hm2.trans hm))
        · simpa [hp, hp2, hp3, hpush, Footprint.StateGasEq] using
            ho.trans (hm3.trans (hm2.trans hm))

theorem chargeGas_stateGasZero (cost : Nat) {devm : Devm}
    (h : devm.StateGasZero) : (chargeGas cost devm).StateGasZero :=
  liftMachExecution_stateGasZero h (Mach.chargeGas_stateGas_eq cost devm.mach)

theorem Devm.push_stateGasZero (x : U256) {devm : Devm}
    (h : devm.StateGasZero) : (devm.push x).StateGasZero :=
  liftMachExecution_stateGasZero h (Mach.push_stateGas_eq x devm.mach)

theorem pushItem_stateGasZero (x : U256) (cost : Nat) {devm : Devm}
    (h : devm.StateGasZero) : (pushItem x cost devm).StateGasZero :=
  liftMachExecution_stateGasZero h
    (Mach.pushItem_stateGas_eq x cost devm.mach)

theorem Devm.pop_stateGasZero {devm : Devm} (h : devm.StateGasZero) :
    devm.pop.StateGasZeroOn (fun a => a.2.StateGasZero) :=
  liftMach_stateGasZeroOn h (Mach.pop_stateGas_eq devm.mach)

theorem Devm.popToNat_stateGasZero {devm : Devm} (h : devm.StateGasZero) :
    devm.popToNat.StateGasZeroOn (fun a => a.2.StateGasZero) :=
  liftMach_stateGasZeroOn h (Mach.popToNat_stateGas_eq devm.mach)

theorem Devm.popToAdr_stateGasZero {devm : Devm} (h : devm.StateGasZero) :
    devm.popToAdr.StateGasZeroOn (fun a => a.2.StateGasZero) :=
  liftMach_stateGasZeroOn h (Mach.popToAdr_stateGas_eq devm.mach)

theorem Devm.popN_stateGasZero {devm : Devm} (h : devm.StateGasZero) (n : Nat) :
    (devm.popN n).StateGasZeroOn (fun a => a.2.StateGasZero) :=
  liftMach_stateGasZeroOn h (Mach.popN_stateGas_eq devm.mach n)

theorem applyUnary_stateGasZero (f : U256 → U256) (cost : Nat) {devm : Devm}
    (h : devm.StateGasZero) : (applyUnary f cost devm).StateGasZero :=
  liftMachExecution_stateGasZero h
    (Mach.applyUnary_stateGas_eq f cost devm.mach)

theorem applyBinary_stateGasZero (f : U256 → U256 → U256) (cost : Nat)
    {devm : Devm} (h : devm.StateGasZero) :
    (applyBinary f cost devm).StateGasZero :=
  liftMachExecution_stateGasZero h
    (Mach.applyBinary_stateGas_eq f cost devm.mach)

theorem applyTernary_stateGasZero (f : U256 → U256 → U256 → U256) (cost : Nat)
    {devm : Devm} (h : devm.StateGasZero) :
    (applyTernary f cost devm).StateGasZero :=
  liftMachExecution_stateGasZero h
    (Mach.applyTernary_stateGas_eq f cost devm.mach)

theorem Devm.memRead_stateGasZero {devm : Devm} (index size : Nat)
    (h : devm.StateGasZero) :
    (devm.memRead index size).2.StateGasZero := h

theorem Devm.subBal_stateGasZero {devm devm' : Devm}
    (h : devm.StateGasZero) {adr : Address} {value : U256}
    (hs : devm.subBal adr value = some devm') : devm'.StateGasZero := by
  unfold Devm.subBal at hs
  cases hw : devm.state.subBal adr value with
  | none => rw [hw] at hs; contradiction
  | some world =>
    rw [hw] at hs
    simp only [bind, Option.bind, Option.some.injEq] at hs
    rw [← hs]
    exact h

theorem Devm.addBal_stateGasZero {devm : Devm} (h : devm.StateGasZero)
    (adr : Address) (value : U256) : (devm.addBal adr value).StateGasZero := h

theorem Devm.setBal_stateGasZero {devm : Devm} (h : devm.StateGasZero)
    (adr : Address) (value : U256) : (devm.setBal adr value).StateGasZero := h

theorem Devm.creditBeneficiary_stateGasZero {devm : Devm} (h : devm.StateGasZero)
    (rules : ForkRules) (adr : Address) (value : U256) :
    (devm.creditBeneficiary rules adr value).StateGasZero := by
  unfold Devm.creditBeneficiary
  split
  · exact h
  · exact h

theorem Devm.withRefundCounter_stateGasZero {devm : Devm}
    (h : devm.StateGasZero) (refund : Int) :
    (devm.withRefundCounter refund).StateGasZero := h

/-- The hook preserves the state-gas baseline. -/
theorem creditSelfdestructRefund_stateGasZero {rules : ForkRules}
    {alreadyScheduled : Prop} [Decidable alreadyScheduled] {devm : Devm}
    (h : devm.StateGasZero) :
    (creditSelfdestructRefund rules alreadyScheduled devm).StateGasZero := by
  unfold creditSelfdestructRefund
  split
  · exact h
  · exact Devm.withRefundCounter_stateGasZero h _

theorem addAccountToDelete_stateGasZero {devm : Devm} (h : devm.StateGasZero)
    (adr : Address) : (addAccountToDelete devm adr).StateGasZero := h

theorem PlainOp.balanceCore_stateGas_eq (rules : ForkRules) (world : World)
    (mach : Mach) (view : Meta) :
    Footprint.MachMetaStateGasEq mach (PlainOp.balanceCore rules world mach view) := by
  unfold PlainOp.balanceCore
  cases hp : mach.pop with
  | error e =>
    have hm := Mach.pop_stateGas_eq mach
    rw [hp] at hm
    simpa [hp, Footprint.StateGasEq, Footprint.MachMetaStateGasEq] using hm
  | ok a =>
    have hm := Mach.pop_stateGas_eq mach
    rw [hp] at hm
    simp only []
    generalize (match rules.access with
      | .eip2929 => if a.1.toAddress ∈ view.accessedAddresses
          then Gas.warmStorageReadCost else rules.gas.coldAccountAccess
      | .flat g => g.balance) = cost
    cases hc : a.2.chargeGas cost with
    | error e =>
      have hc' := Mach.chargeGas_stateGas_eq cost a.2
      rw [hc] at hc'
      simpa [hp, hc, Footprint.MachMetaStateGasEq] using hc'.trans hm
    | ok b =>
      have hc' := Mach.chargeGas_stateGas_eq cost a.2
      rw [hc] at hc'
      have hpush := Mach.push_stateGas_eq (world.state.get a.1.toAddress).balance b.2
      cases hq : b.2.push (world.state.get a.1.toAddress).balance <;> rw [hq] at hpush
      · simpa [hp, hc, hq, Footprint.MachMetaStateGasEq] using
          hpush.trans (hc'.trans hm)
      · simpa [hp, hc, hq, Footprint.MachMetaStateGasEq] using
          hpush.trans (hc'.trans hm)

theorem PlainOp.balance_stateGasZero (rules : ForkRules) {devm : Devm}
    (h : devm.StateGasZero) :
    (liftMachMetaWorldExecution (PlainOp.balanceCore rules) devm).StateGasZero :=
  liftMachMetaExecution_stateGasZero h
    (PlainOp.balanceCore_stateGas_eq rules devm.world devm.mach devm.meta)

/-- Every register instruction preserves a zero meter when the state-gas
switch is absent.  The switch hypothesis rules out only the `SSTORE`
Amsterdam sibling; all other register operations are meter-blind. -/
theorem PlainOp.run_stateGasZero {evm : Evm} (h : evm.dyna.StateGasZero)
    (hrules : evm.sta.benvStat.rules.stateGas = none) (r : PlainOp) :
    (r.run evm).StateGasZero := by
  unfold PlainOp.run
  cases r <;> simp only [PlainOp.runCore]
  case iszero | not => exact applyUnary_stateGasZero _ _ h
  case add | mul | sub | div | sdiv | mod | smod | signextend | lt | gt | slt |
      sgt | eq | and | or | xor | byte =>
    exact applyBinary_stateGasZero _ _ h
  case shl | shr | sar =>
    split
    · exact applyBinary_stateGasZero _ _ h
    · exact Except.stateGasZeroOn_error h
  case addmod | mulmod => exact applyTernary_stateGasZero _ _ h
  case address | origin | caller | callvalue |
      calldatasize | codesize | gasprice | returndatasize |
      number | timestamp | gaslimit | prevrandao | coinbase | msize |
      pc =>
    exact pushItem_stateGasZero _ _ h
  case basefee | blobbasefee | chainid =>
    split
    · exact pushItem_stateGasZero _ _ h
    · exact Except.stateGasZeroOn_error h
  case selfbalance =>
    split
    · exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h)
        fun d hd => Devm.push_stateGasZero _ hd
    · exact Except.stateGasZeroOn_error h
  case balance => exact PlainOp.balance_stateGasZero _ h
  case mload =>
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h) ?_
    rintro ⟨start, d1⟩ h1
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h1) ?_
    intro d2 h2
    exact Devm.push_stateGasZero _ (Devm.memRead_stateGasZero start 32 h2)
  case keccak256 =>
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h) ?_
    rintro ⟨start, d1⟩ h1
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h1) ?_
    rintro ⟨size, d2⟩ h2
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h2) ?_
    intro d3 h3
    exact Devm.push_stateGasZero _ (Devm.memRead_stateGasZero start size h3)
  case mcopy =>
    split
    · refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h) ?_
      rintro ⟨dest, d1⟩ h1
      refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h1) ?_
      rintro ⟨src, d2⟩ h2
      refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h2) ?_
      rintro ⟨len, d3⟩ h3
      refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h3) ?_
      intro d4 h4
      exact Except.stateGasZeroOn_ok (Devm.memRead_stateGasZero src len h4)
    · exact Except.stateGasZeroOn_error h
  case log =>
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h) ?_
    rintro ⟨start, d1⟩ h1
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h1) ?_
    rintro ⟨size, d2⟩ h2
    refine Except.StateGasZeroOn.bind (Devm.popN_stateGasZero h2 _) ?_
    rintro ⟨topics, d3⟩ h3
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h3) ?_
    intro d4 h4
    refine Except.StateGasZeroOn.bind (Except.stateGasZeroOn_assert h4) ?_
    intro _ _
    exact Except.stateGasZeroOn_ok (Devm.memRead_stateGasZero start size h4)
  case exp =>
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero ha) fun b hb => ?_
    exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hb)
      fun d hd => Devm.push_stateGasZero _ hd
  case clz =>
    split
    · exact applyUnary_stateGasZero _ _ h
    · exact Except.stateGasZeroOn_error h
  case slotnum =>
    split
    · exact pushItem_stateGasZero _ _ h
    · exact Except.stateGasZeroOn_error h
  case calldataload =>
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ ha)
      fun d hd => Devm.push_stateGasZero _ hd
  case calldatacopy =>
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero ha) fun b hb => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hb) fun c hc => ?_
    exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hc)
      fun _ hd => Except.stateGasZeroOn_ok hd
  case codecopy =>
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero ha) fun b hb => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hb) fun c hc => ?_
    exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hc)
      fun _ hd => Except.stateGasZeroOn_ok hd
  case extcodesize =>
    refine Except.StateGasZeroOn.bind (Devm.popToAdr_stateGasZero h) fun a ha => ?_
    split <;> (try split) <;>
      exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ ha)
        fun _ hd => Devm.push_stateGasZero _ hd
  case extcodecopy =>
    refine Except.StateGasZeroOn.bind (Devm.popToAdr_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero ha) fun b hb => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hb) fun c hc => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hc) fun e he => ?_
    split <;> (try split) <;>
      exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ he)
        fun _ hd => Except.stateGasZeroOn_ok hd
  case returndatacopy =>
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero ha) fun b hb => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hb) fun c hc => ?_
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hc) fun d hd => ?_
    split
    · exact Except.StateGasZeroOn.bind
        (Except.stateGasZeroOn_error (P := fun _ => True) hd)
        fun _ _ => Except.stateGasZeroOn_ok hd
    · exact Except.stateGasZeroOn_ok hd
  case extcodehash =>
    split
    · refine Except.StateGasZeroOn.bind (Devm.popToAdr_stateGasZero h) fun a ha => ?_
      split <;> (try split) <;>
        exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ ha)
          fun _ hd => Devm.push_stateGasZero _ hd
    · exact Except.stateGasZeroOn_error h
  case blockhash =>
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ ha)
      fun _ hd => Devm.push_stateGasZero _ hd
  case blobhash =>
    split
    · refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
      exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ ha)
        fun _ hd => Devm.push_stateGasZero _ hd
    · exact Except.stateGasZeroOn_error h
  case pop =>
    exact Except.StateGasZeroOn.bind
      (Except.StateGasZeroOn.map (Devm.pop_stateGasZero h) fun _ ha => ha)
      fun _ hd => chargeGas_stateGasZero _ hd
  case mstore =>
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero ha) fun b hb => ?_
    exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hb)
      fun _ hd => Except.stateGasZeroOn_ok hd
  case mstore8 =>
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero ha) fun b hb => ?_
    exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hb)
      fun _ hd => Except.stateGasZeroOn_ok hd
  case sload =>
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    split <;> (try split) <;>
      exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ ha)
        fun _ hd => Devm.push_stateGasZero _ hd
  case sstore =>
    rw [hrules]
    dsimp only
    split
    · -- Prague: the body it has always been.
      refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
      refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero ha) fun b hb => ?_
      refine Except.StateGasZeroOn.bind (Except.stateGasZeroOn_assert hb) fun _ _ => ?_
      refine Except.StateGasZeroOn.bind
        (P := fun p : Devm × Nat => p.1.StateGasZero) ?_ fun p hp => ?_
      · exact Except.stateGasZeroOn_ok (by split <;> exact hb)
      refine Except.StateGasZeroOn.bind
        (P := fun _ => True) (Except.stateGasZeroOn_ok trivial) fun _ _ => ?_
      refine Except.StateGasZeroOn.bind
        (Except.stateGasZeroOn_ok (Devm.withRefundCounter_stateGasZero hp _))
        fun d hd => ?_
      refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hd) fun d' hd' => ?_
      refine Except.StateGasZeroOn.bind (Except.stateGasZeroOn_assert hd') fun _ _ => ?_
      exact Except.stateGasZeroOn_ok hd'
    · -- The pre-Berlin regimes: the sentry is gated, the cold term is zero
      -- under flat access, and the refund dispatches on the regime. The walk
      -- has the same shape; only the cold-pair proof cases on access.
      refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
      refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero ha) fun b hb => ?_
      refine Except.StateGasZeroOn.bind (Except.stateGasZeroOn_assert hb) fun _ _ => ?_
      refine Except.StateGasZeroOn.bind
        (P := fun p : Devm × Nat => p.1.StateGasZero) ?_ fun p hp => ?_
      · exact Except.stateGasZeroOn_ok (by
          split
          · exact hb
          · split <;> exact hb)
      refine Except.StateGasZeroOn.bind
        (P := fun _ => True) (Except.stateGasZeroOn_ok trivial) fun _ _ => ?_
      refine Except.StateGasZeroOn.bind
        (Except.stateGasZeroOn_ok (Devm.withRefundCounter_stateGasZero hp _))
        fun d hd => ?_
      refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hd) fun d' hd' => ?_
      refine Except.StateGasZeroOn.bind (Except.stateGasZeroOn_assert hd') fun _ _ => ?_
      exact Except.stateGasZeroOn_ok hd'
  case tload =>
    split
    · refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
      exact pushItem_stateGasZero _ _ ha
    · exact Except.stateGasZeroOn_error h
  case tstore =>
    split
    · rw [hrules]
      refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
      refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero ha) fun b hb => ?_
      refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hb)
        fun d hd => ?_
      refine Except.StateGasZeroOn.bind (Except.stateGasZeroOn_assert hd)
        fun _ _ => ?_
      exact Except.stateGasZeroOn_ok hd
    · exact Except.stateGasZeroOn_error h
  case gas =>
    exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h)
      fun _ hd => Devm.push_stateGasZero _ hd
  case dup =>
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h) fun d hd => ?_
    split
    · exact Except.stateGasZeroOn_error hd
    · exact Devm.push_stateGasZero _ hd
  case swap =>
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h) fun d hd => ?_
    split
    · exact Except.stateGasZeroOn_error hd
    · exact Except.stateGasZeroOn_ok hd

theorem JumpOp.run_stateGasZero {evm : Evm} (h : evm.dyna.StateGasZero)
    (j : JumpOp) :
    (j.run evm).StateGasZeroOn (fun a => a.2.StateGasZero) := by
  unfold JumpOp.run
  cases j <;> simp only [JumpOp.runCore]
  case jumpdest =>
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h) ?_
    intro d hd
    exact Except.stateGasZeroOn_ok hd
  case jump =>
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) ?_
    rintro ⟨dest, d⟩ hd
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hd) ?_
    intro d2 hd2
    refine Except.StateGasZeroOn.bind (Except.stateGasZeroOn_assert hd2) ?_
    intro _ _
    exact Except.stateGasZeroOn_ok hd2
  case jumpi =>
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) ?_
    rintro ⟨dest, d⟩ hd
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero hd) ?_
    rintro ⟨cond, d2⟩ hd2
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hd2) ?_
    intro d3 hd3
    split
    · exact Except.stateGasZeroOn_ok hd3
    · refine Except.StateGasZeroOn.bind (Except.stateGasZeroOn_assert hd3) ?_
      intro _ _
      exact Except.stateGasZeroOn_ok hd3

theorem HaltOp.run_stateGasZero {sevm : Sevm} {devm : Devm}
    (h : devm.StateGasZero) (hrules : sevm.benvStat.rules.stateGas = none)
    (l : HaltOp) : Execution.StateGasZero (l.run sevm devm) := by
  cases l <;> simp only [HaltOp.run]
  case stop => exact h
  case revert =>
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h) ?_
    rintro ⟨start, d1⟩ h1
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h1) ?_
    rintro ⟨size, d2⟩ h2
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h2) ?_
    intro d3 h3
    exact Except.stateGasZeroOn_error (Devm.memRead_stateGasZero _ _ h3)
  case return_ =>
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h) ?_
    rintro ⟨start, d1⟩ h1
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h1) ?_
    rintro ⟨size, d2⟩ h2
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h2) ?_
    intro d3 h3
    exact Except.stateGasZeroOn_ok (Devm.memRead_stateGasZero _ _ h3)
  case selfdestruct =>
    rw [hrules]
    refine Except.StateGasZeroOn.bind (Devm.popToAdr_stateGasZero h) ?_
    rintro ⟨donee, d1⟩ h1
    refine Except.StateGasZeroOn.bind
      (P := fun _ => True) (Except.stateGasZeroOn_ok trivial) ?_
    intro donorBal _
    refine Except.StateGasZeroOn.bind
      (P := fun p : Devm × Nat => p.1.StateGasZero) ?_ ?_
    · exact Except.stateGasZeroOn_ok (by split <;> (try split) <;> exact h1)
    rintro ⟨d2, cost⟩ h2
    refine Except.StateGasZeroOn.bind
      (P := fun _ => True) (Except.stateGasZeroOn_ok trivial) ?_
    intro cost3 _
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h2) ?_
    intro d3 h5
    refine Except.StateGasZeroOn.bind (Except.stateGasZeroOn_assert h5) ?_
    intro _ _
    refine Except.StateGasZeroOn.bind (P := Devm.StateGasZero) ?_ ?_
    · cases hs : d3.subBal sevm.currentTarget donorBal with
      | none => exact Except.stateGasZeroOn_error h5
      | some d4 => exact Except.stateGasZeroOn_ok (Devm.subBal_stateGasZero h5 hs)
    · intro d4 h6
      refine Except.StateGasZeroOn.bind
        (Except.stateGasZeroOn_ok (Devm.creditBeneficiary_stateGasZero h6 _ _ _)) ?_
      intro d5 h7
      split
      · exact Except.stateGasZeroOn_ok (creditSelfdestructRefund_stateGasZero
          (addAccountToDelete_stateGasZero (Devm.setBal_stateGasZero h7 _ _) _))
      · exact Except.stateGasZeroOn_ok h7

@[simp] theorem Devm.stateGasZero_gasMeasure {devm : Devm}
    (h : devm.StateGasZero) : devm.gasMeasure = devm.gasLeft :=
  Devm.gasMeasure_of_stateGas_zero h

/-- Every existing `Devm` update reaches `Mach` through `setMach` with a
`with`-update that does not name `stateGas`, so the invariant is preserved by
construction rather than by argument. These are the two spellings the
interpreter actually uses. -/
@[simp] theorem Devm.stateGasZero_setMach {devm : Devm} {mach : Mach} :
    (devm.setMach mach).StateGasZero ↔ mach.stateGas = .zero := Iff.rfl

@[simp] theorem Devm.stateGasZero_setMeta {devm : Devm} {view : Meta} :
    (devm.setMeta view).StateGasZero ↔ devm.StateGasZero := Iff.rfl

@[simp] theorem Devm.stateGasZero_setWorld {devm : Devm} {world : World} :
    (devm.setWorld world).StateGasZero ↔ devm.StateGasZero := Iff.rfl

theorem Devm.stateGasZero_withGasLeft {devm : Devm} {n : Nat}
    (h : devm.StateGasZero) : (devm.withGasLeft n).StateGasZero := h

def computeContractAddress (sender : Address) (nonce : UInt64) : Address :=
  let LA : Bytes :=
    Rlp.Item.toBytes <| .list [.bytes sender.toBytes, .bytes nonce.toBytes.sig]
  (Bytes.keccak LA).toAddress

def create2NewAddress
  (sender : Address) (salt : U256) (initCode : Bytes): Address :=
  let LA : Bytes :=
    (0xFF : UInt8) :: (sender.toBytes ++ salt.toBytes ++ initCode.keccak.toBytes)
  (Bytes.keccak LA).toAddress

def State.incrNonce (w : State) (a : Address) : State :=
  let ac := w.get a
  let ac' : Account := {ac with nonce := ac.nonce + 1}
  w.setAccount a ac'

def Msg.incrNonce (msg : Msg) (adr : Address) : Msg :=
  {
    msg with
    benv := ({msg.benv with state := msg.benv.state.incrNonce adr} : Benv)
      |>.clearStorageWritesIfEmpty adr
  }

def Devm.incrNonce (devm : Devm) (adr : Address) : Devm :=
  (devm.withState (devm.state.incrNonce adr)).clearStorageWritesIfEmpty adr

def Benv.incrNonce (benv : Benv) (adr : Address) : Benv :=
  ({benv with state := benv.state.incrNonce adr} : Benv).clearStorageWritesIfEmpty adr

def State.setStor (w : State) (a : Address) (s : Storage) : State :=
  let ac := (w.get a)
  if AccountExists w a then w.setPresent a {ac with storage := s}
  else w.set a {ac with storage := s}

def Benv.setStor (benv : Benv) (adr : Address) (stor : Storage) : Benv :=
  {benv with
    state := benv.state.setStor adr stor
    storageWrites := benv.storageWrites.eraseAddress adr}

def Msg.setCode (msg : Msg) (adr : Address) (code : ByteArray) : Msg :=
  {msg with benv :=
    ({msg.benv with state := msg.benv.state.setCode adr code} : Benv).clearStorageWritesIfEmpty adr}

def Devm.setCode (devm : Devm) (adr : Address) (code : ByteArray) : Devm :=
  (devm.withState (devm.state.setCode adr code)).clearStorageWritesIfEmpty adr

def Devm.rollback (devm : Devm) (wor : State) (tra : TransientStorage) : Devm :=
  devm.setWorld {devm.world with state := wor, transientStorage := tra}

--------------- CANONICAL STATE AND STORAGE (P0.4) ---------------

-- `State` and `Stor` are raw `Std.TreeMap`s, so nothing in their *types* stops
-- a map from storing a zero slot or an exact `Acct.nil`. Zero storage slots
-- are noncanonical; a present `Acct.nil` is a valid historical account.
-- `State.set` erases nil by convenience, while `State.setPresent` retains it.
-- `State.root` serialises whatever the map holds, so two
-- states with identical EVM-level reads can commit to different trie roots --
-- which is why canonicality is a real commitment-level property and not a
-- tidiness convention, and why `State.root` may never be changed to hide the
-- difference.
--
-- The predicates are defined by finite `toList` traversal, hence decidable
-- without quantifying over every key. `Stor.find?`/`getElem?` give the lookup
-- form semantic proofs actually use, and the `canonical_iff` lemmas below are
-- the bridge between the two. The premises are the real ones: `State.set`
-- preserves canonicality only when the account being inserted has canonical
-- storage, and `State.setStor` only when its storage argument is canonical.
-- Nothing here is stated more strongly than that.
--
-- Canonicality constrains storage, not account existence. `State.NoNil`
-- separately names the old no-default-payload convention; account membership
-- remains commitment-relevant even when all payload reads return defaults.

/-- A storage slot's own optional lookup.

`Stor.get` answers an absent slot with `0`, which is correct for the EVM and
useless for stating canonicality -- the whole point is to tell "absent" from
"present and zero" apart. `Stor` is a `def` rather than an `abbrev`, so the
`GetElem?` notation `s[k]?` does not apply to it; this is that notation. -/
def Storage.find? (s : Storage) (k : U256) : Option U256 := Std.TreeMap.get? s k

theorem Storage.find?_empty (k : U256) : Storage.empty.find? k = none := rfl

theorem Storage.find?_erase (s : Storage) (k a : U256) :
    Storage.find? (s.erase k) a = if k = a then none else s.find? a := by
  change (Std.TreeMap.erase (show Std.TreeMap U256 U256 compare from s) k)[a]? =
    if k = a then none else (show Std.TreeMap U256 U256 compare from s)[a]?
  rw [Std.TreeMap.getElem?_erase]
  simp only [Std.compare_eq_iff_eq]

theorem Storage.find?_insert (s : Storage) (k a v : U256) :
    Storage.find? (s.insert k v) a = if k = a then some v else s.find? a := by
  change (Std.TreeMap.insert (show Std.TreeMap U256 U256 compare from s) k v)[a]? =
    if k = a then some v else (show Std.TreeMap U256 U256 compare from s)[a]?
  rw [Std.TreeMap.getElem?_insert]
  simp only [Std.compare_eq_iff_eq]

/-- The defining equation of `Stor.set`, as a lookup: writing zero *erases*. -/
theorem Storage.find?_set (s : Storage) (k a v : U256) :
    (s.set k v).find? a
      = if k = a then (if v = 0 then none else some v) else s.find? a := by
  rw [Storage.set]; split <;> simp_all [Storage.find?_erase, Storage.find?_insert]

theorem Storage.get_eq_getD_find? (s : Storage) (k : U256) :
    s.get k = (s.find? k).getD 0 := by
  exact Std.TreeMap.getD_eq_getD_getElem?

theorem Storage.get_set_self (s : Storage) (k v : U256) : (s.set k v).get k = v := by
  rw [Storage.get_eq_getD_find?, Storage.find?_set, ite_eq_left rfl]
  split <;> simp_all

theorem Storage.get_set_ne (s : Storage) {k a : U256} (h : k ≠ a) (v : U256) :
    (s.set k v).get a = s.get a := by
  rw [Storage.get_eq_getD_find?, Storage.get_eq_getD_find?, Storage.find?_set, ite_eq_right h]

/-- A storage map is canonical when it stores no zero-valued slot.

Stated as a finite traversal of the map's `toList`, so it is decidable by
construction. -/
def Storage.Canonical (s : Storage) : Prop := ∀ e ∈ s.toList, e.2 ≠ 0

instance {s : Storage} : Decidable (Storage.Canonical s) := List.decidableBAll _ _

theorem Storage.mem_toList_iff {s : Storage} {k v : U256} :
    (k, v) ∈ s.toList ↔ s.find? k = some v := by
  exact Std.TreeMap.mem_toList_iff_getElem?_eq_some

/-- The lookup characterisation: the finite traversal and the pointwise
statement semantic proofs use are the same property. -/
theorem Storage.canonical_iff {s : Storage} :
    Storage.Canonical s ↔ ∀ (k v : U256), s.find? k = some v → v ≠ 0 := by
  constructor
  · intro h k v hv; exact h (k, v) (Storage.mem_toList_iff.mpr hv)
  · intro h e he; exact h e.1 e.2 (Storage.mem_toList_iff.mp (by simpa using he))

theorem Storage.canonical_empty : Storage.Canonical .empty := by
  rw [Storage.canonical_iff]; intro k v hv; cases hv

theorem Storage.Canonical.set {s : Storage} (h : Storage.Canonical s) (k v : U256) :
    Storage.Canonical (s.set k v) := by
  rw [Storage.canonical_iff] at h ⊢
  intro a w hw; rw [Storage.find?_set] at hw
  split at hw
  · split at hw
    · cases hw
    · cases hw; assumption
  · exact h a w hw

theorem Storage.Canonical.erase {s : Storage} (h : Storage.Canonical s) (k : U256) :
    Storage.Canonical (s.erase k) := by
  apply (Storage.canonical_iff).mpr
  intro a v hv; rw [Storage.find?_erase] at hv
  split at hv
  · cases hv
  · exact (Storage.canonical_iff.mp h) a v hv

/-- On a canonical map, reading zero and being absent are the same thing.

This is the property the trie commitment depends on, and the reason an
explicitly stored zero slot is not merely redundant. -/
theorem Storage.Canonical.get_eq_zero_iff {s : Storage} (h : Storage.Canonical s)
    (k : U256) : s.get k = 0 ↔ s.find? k = none := by
  rw [Storage.get_eq_getD_find?]
  cases hk : s.find? k with
  | none => simp
  | some v => simp [Storage.canonical_iff.mp h k v hk]

/-- The canonical smart constructor for storage: fold the pairs through
`Stor.set`, which drops the zero-valued ones instead of storing them. -/
def Storage.ofList (l : List (U256 × U256)) : Storage :=
  l.foldl (fun s e => s.set e.1 e.2) .empty

theorem Storage.canonical_foldl (l : List (U256 × U256)) :
    ∀ {s : Storage}, Storage.Canonical s →
      Storage.Canonical (l.foldl (fun s e => s.set e.1 e.2) s) := by
  induction l with
  | nil => intro s h; exact h
  | cons e l ih => intro s h; exact ih (h.set e.1 e.2)

/-- Smart-constructor soundness: the result is canonical whatever it was
given. -/
theorem Storage.canonical_ofList (l : List (U256 × U256)) :
    Storage.Canonical (Storage.ofList l) :=
  Storage.canonical_foldl l Storage.canonical_empty

theorem Storage.ofList_nil : Storage.ofList [] = .empty := rfl

theorem Storage.ofList_concat (l : List (U256 × U256)) (k v : U256) :
    Storage.ofList (l ++ [(k, v)]) = (Storage.ofList l).set k v := by
  rw [Storage.ofList, Storage.ofList, List.foldl_append, List.foldl_cons,
      List.foldl_nil]

/-- Smart-constructor soundness, read side: the last value written for a key is
the value read back, so canonicalisation never changes an EVM-level read. -/
theorem Storage.get_ofList_concat (l : List (U256 × U256)) (k v : U256) :
    (Storage.ofList (l ++ [(k, v)])).get k = v := by
  rw [Storage.ofList_concat, Storage.get_set_self]

theorem State.get_eq_getD (w : State) (a : Address) :
    w.get a = (w[a]?).getD .nil := by
  rw [State.get, Std.TreeMap.getD_eq_getD_getElem?]

/-- The defining equation of `State.set`, as a lookup: writing `Acct.nil`
*erases*. -/
theorem State.getElem?_set (w : State) (a b : Address) (ac : Account) :
    (w.set a ac)[b]?
      = if a = b then (if ac = .nil then none else some ac) else w[b]? := by
  rw [State.set]
  split <;> simp_all [Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert]

/-- Presence-preserving insertion never identifies `some Acct.nil` with `none`. -/
theorem State.getElem?_setPresent (w : State) (a b : Address) (ac : Account) :
    (w.setPresent a ac)[b]? = if a = b then some ac else w[b]? := by
  simp only [State.setPresent, Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq]

theorem State.accountExists_setPresent (w : State) (a : Address) (ac : Account) :
    AccountExists (w.setPresent a ac) a := by
  simp only [AccountExists, State.getElem?_setPresent, ite_true, Option.isSome_some]

theorem State.getElem?_erase (w : State) (a b : Address) :
    (w.erase a)[b]? = if a = b then none else w[b]? := by
  simp [Std.TreeMap.getElem?_erase]

/-- A world state is canonical when every present account has canonical
storage. Present empty accounts are valid historical state entries; their
membership is observed separately from default-valued account reads. -/
def State.Canonical (w : State) : Prop :=
  ∀ e ∈ w.toList, Storage.Canonical e.2.storage

/-- The stronger sparse-account property used by the erasing constructors.
It is separate from canonicality: historical prestates may store `Acct.nil`. -/
def State.NoNil (w : State) : Prop :=
  ∀ e ∈ w.toList, e.2 ≠ Account.nil

instance {w : State} : Decidable (State.NoNil w) := List.decidableBAll _ _

instance {w : State} : Decidable (State.Canonical w) := List.decidableBAll _ _

theorem State.mem_toList_iff {w : State} {a : Address} {ac : Account} :
    (a, ac) ∈ w.toList ↔ w[a]? = some ac :=
  Std.TreeMap.mem_toList_iff_getElem?_eq_some

/-- The lookup characterisation for world states. -/
theorem State.canonical_iff {w : State} :
    State.Canonical w
      ↔ ∀ (a : Address) (ac : Account),
          w[a]? = some ac → Storage.Canonical ac.storage := by
  constructor
  · intro h a ac hac; exact h (a, ac) (State.mem_toList_iff.mpr hac)
  · intro h e he; exact h e.1 e.2 (State.mem_toList_iff.mp (by simpa using he))

theorem State.canonical_empty : State.Canonical .empty := by
  rw [State.canonical_iff]; intro a ac hac; simp at hac

theorem Account.canonical_nil_storage : Storage.Canonical Account.nil.storage :=
  Storage.canonical_empty

/-- `State.set` preserves canonicality **given its real premise**: the account
being inserted must itself have canonical storage. Without that hypothesis the
statement is false, and it is not weakened here to make it look primitive. -/
theorem State.Canonical.set {w : State} (h : State.Canonical w) (a : Address)
    {ac : Account} (hs : Storage.Canonical ac.storage) :
    State.Canonical (w.set a ac) := by
  rw [State.canonical_iff] at h ⊢
  intro b ac' hb; rw [State.getElem?_set] at hb
  split at hb
  · split at hb
    · cases hb
    · cases hb; exact hs
  · exact h b ac' hb

theorem State.Canonical.setPresent {w : State} (h : State.Canonical w) (a : Address)
    {ac : Account} (hs : Storage.Canonical ac.storage) :
    State.Canonical (w.setPresent a ac) := by
  rw [State.canonical_iff] at h ⊢
  intro b ac' hb
  rw [State.getElem?_setPresent] at hb
  split at hb
  · cases hb; exact hs
  · exact h b ac' hb

theorem State.Canonical.erase {w : State} (h : State.Canonical w) (a : Address) :
    State.Canonical (w.erase a) := by
  rw [State.canonical_iff] at h ⊢
  intro b ac hb; rw [State.getElem?_erase] at hb
  split at hb
  · cases hb
  · exact h b ac hb

theorem State.noNil_iff {w : State} :
    State.NoNil w ↔ ∀ (a : Address) (ac : Account), w[a]? = some ac → ac ≠ Account.nil := by
  constructor
  · intro h a ac hac; exact h (a, ac) (State.mem_toList_iff.mpr hac)
  · intro h e he; exact h e.1 e.2 (State.mem_toList_iff.mp (by simpa using he))

/-- Canonicality with `NoNil` recovers the former sparse-state invariant. -/
theorem State.canonical_noNil_iff {w : State} :
    State.Canonical w ∧ State.NoNil w ↔
      ∀ (a : Address) (ac : Account), w[a]? = some ac →
        ac ≠ Account.nil ∧ Storage.Canonical ac.storage := by
  constructor
  · rintro ⟨hc, hn⟩ a ac ha
    exact ⟨State.noNil_iff.mp hn a ac ha, State.canonical_iff.mp hc a ac ha⟩
  · intro h
    exact ⟨State.canonical_iff.mpr (fun a ac ha => (h a ac ha).2),
      State.noNil_iff.mpr (fun a ac ha => (h a ac ha).1)⟩

theorem State.noNil_empty : State.NoNil .empty := by
  rw [State.noNil_iff]
  intro a ac ha
  cases ha

theorem State.NoNil.set {w : State} (h : State.NoNil w) (a : Address) (ac : Account) :
    State.NoNil (w.set a ac) := by
  rw [State.noNil_iff] at h ⊢
  intro b ac' hb
  rw [State.getElem?_set] at hb
  split at hb
  · split at hb
    · cases hb
    · cases hb; assumption
  · exact h b ac' hb

/-- Default reads identify absence only with the explicit no-nil premise.
Canonical storage alone permits present-empty historical accounts. -/
theorem State.Canonical.get_eq_nil_iff {w : State} (_h : State.Canonical w)
    (hnil : State.NoNil w) (a : Address) : w.get a = .nil ↔ w[a]? = none := by
  rw [State.get_eq_getD]
  cases ha : w[a]? with
  | none => simp
  | some ac => simp [(State.noNil_iff.mp hnil a ac ha)]

/-- Every account *read* out of a canonical state has canonical storage --
including an absent one, whose `Acct.nil` carries the empty map. This is what
lets the derived mutators below discharge `State.Canonical.set`'s premise
without assuming anything new. -/
theorem State.Canonical.storage {w : State} (h : State.Canonical w) (a : Address) :
    Storage.Canonical (w.get a).storage := by
  rw [State.get_eq_getD]
  cases ha : w[a]? with
  | none => exact Account.canonical_nil_storage
  | some ac => exact State.canonical_iff.mp h a ac ha

theorem State.get_set_self (w : State) (a : Address) (ac : Account) :
    (w.set a ac).get a = ac := by
  rw [State.get_eq_getD, State.getElem?_set, ite_eq_left rfl]
  split <;> simp_all

theorem State.get_set_ne (w : State) {a b : Address} (h : a ≠ b) (ac : Account) :
    (w.set a ac).get b = w.get b := by
  rw [State.get_eq_getD, State.get_eq_getD, State.getElem?_set, ite_eq_right h]

theorem State.get_setPresent_self (w : State) (a : Address) (ac : Account) :
    (w.setPresent a ac).get a = ac := by
  rw [State.get_eq_getD, State.getElem?_setPresent, ite_eq_left rfl]
  rfl

theorem State.get_setPresent_ne (w : State) {a b : Address} (h : a ≠ b) (ac : Account) :
    (w.setPresent a ac).get b = w.get b := by
  rw [State.get_eq_getD, State.get_eq_getD, State.getElem?_setPresent, ite_eq_right h]

theorem State.setStorVal_get_self (w : State) (a : Address) (k v : U256) :
    (w.setStorVal a k v).get a = {w.get a with storage := (w.get a).storage.set k v} := by
  unfold State.setStorVal
  split
  · exact State.get_setPresent_self _ _ _
  · exact State.get_set_self _ _ _

theorem State.setStorVal_get_ne (w : State) {a b : Address} (h : a ≠ b) (k v : U256) :
    (w.setStorVal a k v).get b = w.get b := by
  unfold State.setStorVal
  split
  · exact State.get_setPresent_ne _ h _
  · exact State.get_set_ne _ h _

/-- A storage write does not change membership or payload at another address. -/
theorem State.getElem?_setStorVal_ne (w : State) {a b : Address} (h : a ≠ b) (k v : U256) :
    (w.setStorVal a k v)[b]? = w[b]? := by
  unfold State.setStorVal
  split
  · rw [State.getElem?_setPresent, ite_eq_right h]
  · rw [State.getElem?_set, ite_eq_right h]

theorem State.getElem?_setStor_ne (w : State) {a b : Address} (h : a ≠ b) (stor : Storage) :
    (w.setStor a stor)[b]? = w[b]? := by
  unfold State.setStor
  split
  · rw [State.getElem?_setPresent, ite_eq_right h]
  · rw [State.getElem?_set, ite_eq_right h]

/-- Clearing storage never deletes an account that is already present. -/
theorem State.getElem?_setStorVal_self_of_exists (w : State) (a : Address) (k v : U256)
    (h : AccountExists w a) :
    (w.setStorVal a k v)[a]? = some {w.get a with storage := (w.get a).storage.set k v} := by
  rw [State.setStorVal, ite_eq_left h, State.getElem?_setPresent, ite_eq_left rfl]

theorem State.getElem?_setStor_self_of_exists (w : State) (a : Address) (stor : Storage)
    (h : AccountExists w a) :
    (w.setStor a stor)[a]? = some {w.get a with storage := stor} := by
  rw [State.setStor, ite_eq_left h, State.getElem?_setPresent, ite_eq_left rfl]

theorem State.setAccount_get_self (w : State) (a : Address) (ac : Account) :
    (w.setAccount a ac).get a = ac.clearIfEmpty :=
  State.get_set_self w a ac.clearIfEmpty

theorem State.setAccount_get_ne (w : State) {a b : Address} (h : a ≠ b) (ac : Account) :
    (w.setAccount a ac).get b = w.get b :=
  State.get_set_ne w h ac.clearIfEmpty

theorem State.Canonical.setAccount {w : State} (h : State.Canonical w) (a : Address)
    {ac : Account} (hs : Storage.Canonical ac.storage) :
    State.Canonical (w.setAccount a ac) := by
  apply h.set a
  unfold Account.clearIfEmpty
  split
  · exact Storage.canonical_empty
  · exact hs

--------------- CANONICALITY OF THE PRIMITIVE MUTATORS ---------------

-- One theorem per named state mutator. Each derives its `State.set` premise
-- from `State.Canonical.stor` rather than assuming it, except `setStor`, whose
-- storage argument comes from the caller and therefore carries a hypothesis.

theorem State.Canonical.destroyAccount {w : State} (h : State.Canonical w)
    (a : Address) : State.Canonical (destroyAccount w a) :=
  h.erase a

theorem State.Canonical.setCode {w : State} (h : State.Canonical w) (a : Address)
    (cd : ByteArray) : State.Canonical (w.setCode a cd) :=
  h.setAccount a (h.storage a)

theorem State.Canonical.setBal {w : State} (h : State.Canonical w) (a : Address)
    (v : U256) : State.Canonical (w.setBal a v) :=
  h.setAccount a (h.storage a)

theorem State.Canonical.addBal {w : State} (h : State.Canonical w) (a : Address)
    (v : U256) : State.Canonical (w.addBal a v) :=
  h.setBal a _

theorem State.Canonical.subBal {w w' : State} (h : State.Canonical w) {a : Address}
    {v : U256} (hw : w.subBal a v = some w') : State.Canonical w' := by
  rw [State.subBal] at hw
  split at hw
  · cases hw
  · cases hw; exact h.setBal a _

theorem State.Canonical.incrNonce {w : State} (h : State.Canonical w) (a : Address) :
    State.Canonical (w.incrNonce a) :=
  h.setAccount a (h.storage a)

/-- `State.setStor` carries its real premise: the storage map handed in must
already be canonical. -/
theorem State.Canonical.setStor {w : State} (h : State.Canonical w) (a : Address)
    {s : Storage} (hs : Storage.Canonical s) : State.Canonical (w.setStor a s) := by
  unfold State.setStor
  split
  · exact h.setPresent a hs
  · exact h.set a hs

theorem State.Canonical.setStorVal {w : State} (h : State.Canonical w) (a : Address)
    (k v : U256) : State.Canonical (w.setStorVal a k v) := by
  unfold State.setStorVal
  split
  · exact h.setPresent a ((h.storage a).set k v)
  · exact h.set a ((h.storage a).set k v)

/-- The canonical smart constructor for world states. Its premise is the honest
one: the accounts handed in must have canonical storage, which `Stor.ofList`
supplies for anything the fixture parser builds. -/
def State.ofList (l : List (Address × Account)) : State :=
  l.foldl (fun w e => w.set e.1 e.2) .empty

theorem State.canonical_foldl (l : List (Address × Account))
    (hl : ∀ e ∈ l, Storage.Canonical e.2.storage) :
    ∀ {w : State}, State.Canonical w →
      State.Canonical (l.foldl (fun w e => w.set e.1 e.2) w) := by
  induction l with
  | nil => intro w h; exact h
  | cons e l ih =>
    intro w h
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (h.set e.1 (hl e List.mem_cons_self))

theorem State.canonical_ofList {l : List (Address × Account)}
    (hl : ∀ e ∈ l, Storage.Canonical e.2.storage) :
    State.Canonical (State.ofList l) :=
  State.canonical_foldl l hl State.canonical_empty

theorem State.ofList_nil : State.ofList [] = .empty := rfl

theorem State.ofList_concat (l : List (Address × Account)) (a : Address) (ac : Account) :
    State.ofList (l ++ [(a, ac)]) = (State.ofList l).set a ac := by
  rw [State.ofList, State.ofList, List.foldl_append, List.foldl_cons,
      List.foldl_nil]

theorem State.get_ofList_concat (l : List (Address × Account)) (a : Address) (ac : Account) :
    (State.ofList (l ++ [(a, ac)])).get a = ac := by
  rw [State.ofList_concat, State.get_set_self]

theorem State.noNil_ofList (l : List (Address × Account)) : State.NoNil (State.ofList l) := by
  have hfold : ∀ {w : State}, State.NoNil w →
      State.NoNil (l.foldl (fun w e => w.set e.1 e.2) w) := by
    induction l with
    | nil => intro w h; exact h
    | cons e l ih => intro w h; exact ih (h.set e.1 e.2)
  exact hfold State.noNil_empty

/-- Construct an allocation without dropping explicitly present empty accounts. -/
def State.ofPresentList (l : List (Address × Account)) : State :=
  l.foldl (fun w e => w.setPresent e.1 e.2) .empty

theorem State.canonical_foldl_setPresent (l : List (Address × Account))
    (hl : ∀ e ∈ l, Storage.Canonical e.2.storage) :
    ∀ {w : State}, State.Canonical w →
      State.Canonical (l.foldl (fun w e => w.setPresent e.1 e.2) w) := by
  induction l with
  | nil => intro w h; exact h
  | cons e l ih =>
    intro w h
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (h.setPresent e.1 (hl e List.mem_cons_self))

theorem State.canonical_ofPresentList {l : List (Address × Account)}
    (hl : ∀ e ∈ l, Storage.Canonical e.2.storage) :
    State.Canonical (State.ofPresentList l) :=
  State.canonical_foldl_setPresent l hl State.canonical_empty

theorem State.ofPresentList_concat (l : List (Address × Account)) (a : Address) (ac : Account) :
    State.ofPresentList (l ++ [(a, ac)]) = (State.ofPresentList l).setPresent a ac := by
  rw [State.ofPresentList, State.ofPresentList, List.foldl_append, List.foldl_cons,
      List.foldl_nil]

theorem State.getElem?_ofPresentList_concat (l : List (Address × Account)) (a : Address) (ac : Account) :
    (State.ofPresentList (l ++ [(a, ac)]))[a]? = some ac := by
  rw [State.ofPresentList_concat, State.getElem?_setPresent, ite_eq_left rfl]

--------------- CANONICAL TRANSIENT STORAGE ---------------

-- `Tra.set` erases an empty map rather than storing it, exactly as `Stor.set`
-- erases a zero slot, so transient storage has its own canonicality with the
-- same shape. It is separate from `Stor.Canonical` because the default it
-- erases is a different one.

def TransientStorage.Canonical (τ : TransientStorage) : Prop :=
  ∀ e ∈ τ.toList, e.2 ≠ Storage.empty ∧ Storage.Canonical e.2

instance {τ : TransientStorage} : Decidable (TransientStorage.Canonical τ) := List.decidableBAll _ _

theorem TransientStorage.mem_toList_iff {τ : TransientStorage} {a : Address} {s : Storage} :
    (a, s) ∈ τ.toList ↔ τ[a]? = some s :=
  Std.TreeMap.mem_toList_iff_getElem?_eq_some

theorem TransientStorage.canonical_iff {τ : TransientStorage} :
    TransientStorage.Canonical τ
      ↔ ∀ (a : Address) (s : Storage),
          τ[a]? = some s → s ≠ Storage.empty ∧ Storage.Canonical s := by
  constructor
  · intro h a s hs; exact h (a, s) (TransientStorage.mem_toList_iff.mpr hs)
  · intro h e he; exact h e.1 e.2 (TransientStorage.mem_toList_iff.mp (by simpa using he))

theorem TransientStorage.canonical_empty : TransientStorage.Canonical .empty := by
  rw [TransientStorage.canonical_iff]; intro a s hs; simp at hs

theorem TransientStorage.getElem?_set (τ : TransientStorage) (a b : Address) (s : Storage) :
    (τ.set a s)[b]?
      = if a = b then (if s.isEmpty then none else some s) else τ[b]? := by
  rw [TransientStorage.set]
  split <;> simp_all [Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert]

theorem TransientStorage.Canonical.set {τ : TransientStorage} (h : TransientStorage.Canonical τ) (a : Address) {s : Storage}
    (hs : Storage.Canonical s) : TransientStorage.Canonical (τ.set a s) := by
  rw [TransientStorage.canonical_iff] at h ⊢
  intro b s' hb; rw [TransientStorage.getElem?_set] at hb
  split at hb
  · split at hb
    · cases hb
    · cases hb
      exact ⟨fun he =>
        absurd (Std.TreeMap.eq_empty_iff_isEmpty.mp he) (by assumption), hs⟩
  · exact h b s' hb

/-- Every transient map *read* out of a canonical `Tra` is canonical, the
absent case included. -/
theorem TransientStorage.Canonical.getD {τ : TransientStorage} (h : TransientStorage.Canonical τ) (a : Address) :
    Storage.Canonical (τ.getD a .empty) := by
  rw [Std.TreeMap.getD_eq_getD_getElem?]
  cases ha : τ[a]? with
  | none => exact Storage.canonical_empty
  | some s => exact (TransientStorage.canonical_iff.mp h a s ha).2

theorem TransientStorage.Canonical.setStorageValue {τ : TransientStorage} (h : TransientStorage.Canonical τ) (a : Address)
    (k v : U256) : TransientStorage.Canonical (τ.setStorageValue a k v) :=
  h.set a ((h.getD a).set k v)

--------------- THE EXECUTION-STATE INVARIANT VOCABULARY ---------------

-- Statements only. This is the vocabulary Step 4 of the integrity plan
-- proves the preservation corpus in; nothing here asserts that any interpreter
-- step preserves anything, and no such theorem is stated ahead of its proof.
--
-- What the vocabulary has to cover is every state a running machine can *commit
-- to or restore from*, which is three distinct things and not one:
--
--   1. the current state, in `Devm.world`;
--   2. the original state, in `BenvStat.origState`, which `SLOAD`'s original
--      value and the gas refund rules read long after it stopped being
--      current; and
--   3. every saved parent state, which in this interpreter lives in a frame's
--      checkpoint (`Frame.checkpoint`) -- its world's state and transient
--      storage are exactly the pair a failed frame falls back to in `settle`.
--
-- Transient storage is carried alongside the world state everywhere, so each
-- predicate below pairs `State.Canonical` with `Tra.Canonical` rather than
-- treating transient storage as an afterthought.

/-- A machine world -- current state and transient storage -- is canonical. -/
def World.Canonical (w : World) : Prop :=
  State.Canonical w.state ∧ TransientStorage.Canonical w.transientStorage

/-- The dynamic machine's world is canonical. -/
def Devm.Canonical (devm : Devm) : Prop := World.Canonical devm.world

/-- The block environment's *original* state is canonical. Separate from the
current one because it outlives it. -/
def BenvStat.Canonical (stat : BenvStat) : Prop := State.Canonical stat.origState

/-- A block environment: its current state and its original state. -/
def Benv.Canonical (benv : Benv) : Prop :=
  State.Canonical benv.state ∧ BenvStat.Canonical benv.stat

def Tenv.Canonical (tenv : Tenv) : Prop := TransientStorage.Canonical tenv.transientStorage

/-- A message: the parent state and transient storage saved for rollback,
together with the original state they were derived from. This is the carrier
of point 3 above -- `msg.benv.state` and `msg.tenv.transientStorage` are what a
failing frame restores. -/
def Msg.Canonical (msg : Msg) : Prop :=
  Benv.Canonical msg.benv ∧ Tenv.Canonical msg.tenv

/-- The static half of an executing frame contributes only the original
state. -/
def Sevm.Canonical (sevm : Sevm) : Prop := BenvStat.Canonical sevm.benvStat

/-- A whole executing frame: current world plus original state. -/
def Evm.Canonical (evm : Evm) : Prop :=
  Sevm.Canonical evm.sta ∧ Devm.Canonical evm.dyna

/-- A chain snapshot's state. Step 6's `ValidContext` adds the tip, root, and
retained-history conjuncts on top of this one. -/
def BlockChain.Canonical (ch : BlockChain) : Prop := State.Canonical ch.state

instance {w : World} : Decidable (World.Canonical w) := by
  unfold World.Canonical; infer_instance
instance {devm : Devm} : Decidable (Devm.Canonical devm) := by
  unfold Devm.Canonical; infer_instance
instance {stat : BenvStat} : Decidable (BenvStat.Canonical stat) := by
  unfold BenvStat.Canonical; infer_instance
instance {benv : Benv} : Decidable (Benv.Canonical benv) := by
  unfold Benv.Canonical; infer_instance
instance {tenv : Tenv} : Decidable (Tenv.Canonical tenv) := by
  unfold Tenv.Canonical; infer_instance
instance {msg : Msg} : Decidable (Msg.Canonical msg) := by
  unfold Msg.Canonical; infer_instance
instance {sevm : Sevm} : Decidable (Sevm.Canonical sevm) := by
  unfold Sevm.Canonical; infer_instance
instance {evm : Evm} : Decidable (Evm.Canonical evm) := by
  unfold Evm.Canonical; infer_instance
instance {ch : BlockChain} : Decidable (BlockChain.Canonical ch) := by
  unfold BlockChain.Canonical; infer_instance

-- The record-surgery facts that hold by projection alone. These are not
-- interpreter theorems -- each is the observation that a setter touches exactly
-- the field its name says -- and they exist so Step 4 never has to unfold a
-- `Devm` to make progress.

theorem Devm.canonical_iff {devm : Devm} :
    Devm.Canonical devm
      ↔ State.Canonical devm.state ∧ TransientStorage.Canonical devm.transientStorage :=
  Iff.rfl

theorem Devm.Canonical.withState {devm : Devm} (h : Devm.Canonical devm)
    {w : State} (hw : State.Canonical w) : Devm.Canonical (devm.withState w) :=
  ⟨hw, h.2⟩

theorem Devm.Canonical.withTransientStorage {devm : Devm}
    (h : Devm.Canonical devm) {τ : TransientStorage} (hτ : TransientStorage.Canonical τ) :
    Devm.Canonical (devm.withTransientStorage τ) :=
  ⟨h.1, hτ⟩

/-- Restoring a saved parent state is canonical exactly when what was saved
was. The current world is irrelevant, which is the point of a rollback. -/
theorem Devm.canonical_rollback {devm : Devm} {w : State} {τ : TransientStorage}
    (hw : State.Canonical w) (hτ : TransientStorage.Canonical τ) :
    Devm.Canonical (devm.rollback w τ) :=
  ⟨hw, hτ⟩

/-- A message's saved pair is exactly what `Devm.rollback` is fed at both
settlement sites, so a canonical message restores a canonical machine. -/
theorem Msg.Canonical.rollback {msg : Msg} (h : Msg.Canonical msg)
    (devm : Devm) :
    Devm.Canonical (devm.rollback msg.benv.state msg.tenv.transientStorage) :=
  ⟨h.1.1, h.2⟩

--------------- CANONICALITY THROUGH EXECUTION (P0.4, STEP 4) ---------------

-- The state-helper half of the preservation corpus: result-carrier predicates
-- for the two execution carriers, and preservation through every named
-- machine-level mutator. The predicates are generic in the error-message
-- component -- the machine or saved state a failure carries is what must stay
-- canonical, never the text riding beside it -- which also means no
-- stringly-typed carrier is respelled here.

/-- Canonicality of a machine-level result, on both channels.

The error channel always carries the machine that failed, which execution will
keep using, so it is unconditionally obliged to be canonical. The ok channel's
payload varies by operation (a bare machine, a popped value paired with one, a
unit), so its obligation is the caller's predicate. -/
def Except.CanonicalOn {ρ α : Type} (P : α → Prop) :
    Except (ρ × Devm) α → Prop
  | .ok a => P a
  | .error e => e.2.Canonical

/-- Canonicality of a whole-machine execution result on both channels. -/
abbrev Execution.Canonical (x : Execution) : Prop :=
  x.CanonicalOn Devm.Canonical

/-- Sequencing preserves canonicality: the compositional lemma the whole
interpreter corpus threads through. Nothing about a particular operation is
here -- only that `Except.bind` takes the error channel through unchanged and
feeds an ok payload to the continuation. -/
theorem Except.CanonicalOn.bind {ρ α β : Type} {P : α → Prop} {Q : β → Prop}
    {x : Except (ρ × Devm) α} {f : α → Except (ρ × Devm) β}
    (hx : x.CanonicalOn P) (hf : ∀ a, P a → (f a).CanonicalOn Q) :
    (x >>= f).CanonicalOn Q := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem Except.CanonicalOn.imp {ρ α : Type} {P Q : α → Prop}
    {x : Except (ρ × Devm) α}
    (hx : x.CanonicalOn P) (hf : ∀ a, P a → Q a) : x.CanonicalOn Q := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem Except.canonicalOn_assert {p : Prop} [inst : Decidable p] {ρ : Type}
    {e : ρ × Devm} (h : e.2.Canonical) :
    (Except.assert p e).CanonicalOn (fun _ => True) := by
  unfold Except.assert
  split
  · trivial
  · exact h

/-- Transport along an unchanged world: every operation that touches only the
computational (`Mach`) or bookkeeping (`Meta`) component preserves
canonicality by this single observation. -/
theorem Devm.Canonical.of_world_eq {devm devm' : Devm}
    (h : devm.Canonical) (hw : devm'.world = devm.world) :
    devm'.Canonical := by
  show World.Canonical devm'.world
  rw [hw]
  exact h

-- The lifted footprint combinators: everything routed through them keeps the
-- world untouched on both channels.

theorem liftMach_canonicalOn {α : Type}
    {core : Mach → Footprint.Outcome Mach α} {devm : Devm}
    (h : devm.Canonical) :
    (liftMach core devm).CanonicalOn (fun a => a.2.Canonical) := by
  unfold liftMach Footprint.liftOutcome
  split <;> exact h.of_world_eq rfl

theorem liftMachMeta_canonicalOn {α : Type}
    {core : Mach → Meta → Footprint.Outcome (Mach × Meta) α} {devm : Devm}
    (h : devm.Canonical) :
    (liftMachMeta core devm).CanonicalOn (fun a => a.2.Canonical) := by
  unfold liftMachMeta Footprint.liftOutcome
  split <;> exact h.of_world_eq rfl

theorem Footprint.toExecution_canonical
    {x : Except _ (Unit × Devm)}
    (hx : x.CanonicalOn (fun a => a.2.Canonical)) :
    (Footprint.toExecution x).Canonical := by
  cases x with
  | error e => exact hx
  | ok a => exact hx

theorem liftMachExecution_canonical
    {core : Mach → Footprint.Outcome Mach Unit} {devm : Devm}
    (h : devm.Canonical) : (liftMachExecution core devm).Canonical :=
  Footprint.toExecution_canonical (liftMach_canonicalOn h)

theorem liftMachMetaExecution_canonical
    {core : Mach → Meta → Footprint.Outcome (Mach × Meta) Unit} {devm : Devm}
    (h : devm.Canonical) : (liftMachMetaExecution core devm).Canonical :=
  Footprint.toExecution_canonical (liftMachMeta_canonicalOn h)

theorem liftMachPure_canonical {core : Mach → Mach} {devm : Devm}
    (h : devm.Canonical) : (liftMachPure core devm).Canonical :=
  h.of_world_eq rfl

theorem liftMachMetaPure_canonical {core : Mach → Meta → Mach × Meta}
    {devm : Devm} (h : devm.Canonical) :
    (liftMachMetaPure core devm).Canonical :=
  h.of_world_eq rfl

-- The named stack, gas, memory, and bookkeeping operations, each an instance
-- of the combinator facts above.

theorem chargeGas_canonical {c : Nat} {devm : Devm} (h : devm.Canonical) :
    (chargeGas c devm).Canonical :=
  liftMachExecution_canonical h

theorem Devm.push_canonical {x : U256} {devm : Devm} (h : devm.Canonical) :
    (devm.push x).Canonical :=
  liftMachExecution_canonical h

theorem Devm.pop_canonicalOn {devm : Devm} (h : devm.Canonical) :
    devm.pop.CanonicalOn (fun a => a.2.Canonical) :=
  liftMach_canonicalOn h

theorem Devm.popToNat_canonicalOn {devm : Devm} (h : devm.Canonical) :
    devm.popToNat.CanonicalOn (fun a => a.2.Canonical) :=
  liftMach_canonicalOn h

theorem Devm.popToAdr_canonicalOn {devm : Devm} (h : devm.Canonical) :
    devm.popToAdr.CanonicalOn (fun a => a.2.Canonical) :=
  liftMach_canonicalOn h

theorem Devm.popN_canonicalOn {devm : Devm} {n : Nat} (h : devm.Canonical) :
    (devm.popN n).CanonicalOn (fun a => a.2.Canonical) :=
  liftMach_canonicalOn h

theorem pushItem_canonical {x : U256} {c : Nat} {devm : Devm}
    (h : devm.Canonical) : (pushItem x c devm).Canonical :=
  liftMachExecution_canonical h

theorem applyUnary_canonical {f : U256 → U256} {c : Nat} {devm : Devm}
    (h : devm.Canonical) : (applyUnary f c devm).Canonical :=
  liftMachExecution_canonical h

theorem applyBinary_canonical {f : U256 → U256 → U256} {c : Nat} {devm : Devm}
    (h : devm.Canonical) : (applyBinary f c devm).Canonical :=
  liftMachExecution_canonical h

theorem applyTernary_canonical {f : U256 → U256 → U256 → U256} {c : Nat}
    {devm : Devm} (h : devm.Canonical) : (applyTernary f c devm).Canonical :=
  liftMachExecution_canonical h

theorem Devm.memWrite_canonical {devm : Devm} {idx : Nat} {val : Bytes}
    (h : devm.Canonical) : (devm.memWrite idx val).Canonical :=
  liftMachPure_canonical h

theorem Devm.memExtends_canonical {devm : Devm} {pairs : List (Nat × Nat)}
    (h : devm.Canonical) : (devm.memExtends pairs).Canonical :=
  liftMachPure_canonical h

theorem Devm.memRead_canonical {devm : Devm} {index size : Nat}
    (h : devm.Canonical) : (devm.memRead index size).2.Canonical := by
  unfold Devm.memRead
  rcases devm.memory.read index size with ⟨val, mem⟩
  exact h.of_world_eq rfl

theorem Devm.addLog_canonical {devm : Devm} {log : Log}
    (h : devm.Canonical) : (devm.addLog log).Canonical :=
  liftMachMetaPure_canonical h

theorem Devm.emitTransferLog_canonical {devm : Devm} {sender recipient : Address}
    {amount : U256} (h : devm.Canonical) :
    (devm.emitTransferLog sender recipient amount).Canonical := by
  unfold Devm.emitTransferLog
  split
  · exact h
  · exact Devm.addLog_canonical h

theorem addAccessedAddress_canonical {devm : Devm} {a : Address}
    (h : devm.Canonical) : (addAccessedAddress devm a).Canonical :=
  h.of_world_eq rfl

theorem addAccessedStorageKey_canonical {devm : Devm} {a : Address} {k : U256}
    (h : devm.Canonical) : (addAccessedStorageKey devm a k).Canonical :=
  h.of_world_eq rfl

theorem addAccountToDelete_canonical {devm : Devm} {a : Address}
    (h : devm.Canonical) : (addAccountToDelete devm a).Canonical :=
  h.of_world_eq rfl

/-- Canonicality sees only the world: the refund hook is meta-only. -/
theorem Devm.Canonical.withRefundCounter {devm : Devm} (h : devm.Canonical)
    (rc : Int) : (devm.withRefundCounter rc).Canonical :=
  h

theorem creditSelfdestructRefund_canonical {rules : ForkRules}
    {alreadyScheduled : Prop} [Decidable alreadyScheduled] {devm : Devm}
    (h : devm.Canonical) :
    (creditSelfdestructRefund rules alreadyScheduled devm).Canonical := by
  unfold creditSelfdestructRefund
  split
  · exact h
  · exact h.withRefundCounter _

theorem assertDynamic_canonicalOn {sevm : Sevm} {devm : Devm}
    (h : devm.Canonical) :
    (assertDynamic sevm devm).CanonicalOn (fun _ => True) :=
  Except.canonicalOn_assert h

-- The world-changing machine mutators, each discharged by the Step-3 state
-- and transient-storage ladder.

theorem Devm.Canonical.setStorVal {devm : Devm} (h : devm.Canonical)
    (adr : Address) (k v : U256) : (devm.setStorVal adr k v).Canonical :=
  h.withState (State.Canonical.setStorVal h.1 adr k v)

theorem Devm.Canonical.setTransVal {devm : Devm} (h : devm.Canonical)
    (adr : Address) (k v : U256) : (devm.setTransVal adr k v).Canonical :=
  h.withTransientStorage (TransientStorage.Canonical.setStorageValue h.2 adr k v)

theorem Devm.Canonical.setBal {devm : Devm} (h : devm.Canonical)
    (adr : Address) (v : U256) : (devm.setBal adr v).Canonical :=
  h.withState (State.Canonical.setBal h.1 adr v)

theorem Devm.Canonical.addBal {devm : Devm} (h : devm.Canonical)
    (adr : Address) (v : U256) : (devm.addBal adr v).Canonical :=
  h.withState (State.Canonical.addBal h.1 adr v)

theorem Devm.Canonical.creditBeneficiary {devm : Devm} (h : devm.Canonical)
    (rules : ForkRules) (adr : Address) (v : U256) :
    (devm.creditBeneficiary rules adr v).Canonical := by
  unfold Devm.creditBeneficiary
  split
  · exact h.addBal adr v
  · exact Devm.Canonical.of_world_eq
      (h.withState (h.1.setPresent adr (ac := (devm.state.get adr).withBalance (devm.state.bal adr + v))
        (h.1.storage adr))) rfl

theorem Devm.Canonical.subBal {devm devm' : Devm} (h : devm.Canonical)
    {adr : Address} {v : U256} (hs : devm.subBal adr v = some devm') :
    devm'.Canonical := by
  unfold Devm.subBal at hs
  cases hw : devm.state.subBal adr v with
  | none => rw [hw] at hs; exact absurd hs (by simp [bind, Option.bind])
  | some w =>
    rw [hw] at hs
    simp only [bind, Option.bind, Option.some.injEq] at hs
    rw [← hs]
    exact h.withState (State.Canonical.subBal h.1 hw)

theorem Devm.Canonical.incrNonce {devm : Devm} (h : devm.Canonical)
    (adr : Address) : (devm.incrNonce adr).Canonical :=
  h.withState (State.Canonical.incrNonce h.1 adr)

theorem Devm.Canonical.setCode {devm : Devm} (h : devm.Canonical)
    (adr : Address) (cd : ByteArray) : (devm.setCode adr cd).Canonical :=
  h.withState (State.Canonical.setCode h.1 adr cd)

-- The block-environment and message mutators used by frame construction,
-- delegation, and transaction processing.

theorem Benv.Canonical.withState {benv : Benv} (h : benv.Canonical)
    {st : State} (hs : st.Canonical) : (benv.withState st).Canonical :=
  ⟨hs, h.2⟩

theorem Benv.Canonical.setBal {benv : Benv} (h : benv.Canonical)
    (adr : Address) (v : U256) : (benv.setBal adr v).Canonical :=
  ⟨State.Canonical.setBal h.1 adr v, h.2⟩

theorem Benv.Canonical.addBal {benv : Benv} (h : benv.Canonical)
    (adr : Address) (v : U256) : (benv.addBal adr v).Canonical :=
  ⟨State.Canonical.addBal h.1 adr v, h.2⟩

theorem Benv.Canonical.subBal {benv benv' : Benv} (h : benv.Canonical)
    {adr : Address} {v : U256} (hs : benv.subBal adr v = some benv') :
    benv'.Canonical := by
  unfold Benv.subBal at hs
  cases hw : benv.state.subBal adr v with
  | none => rw [hw] at hs; exact absurd hs (by simp [bind, Option.bind])
  | some w =>
    rw [hw] at hs
    simp only [bind, Option.bind, Option.some.injEq] at hs
    rw [← hs]
    exact h.withState (State.Canonical.subBal h.1 hw)

theorem Benv.Canonical.incrNonce {benv : Benv} (h : benv.Canonical)
    (adr : Address) : (benv.incrNonce adr).Canonical :=
  ⟨State.Canonical.incrNonce h.1 adr, h.2⟩

theorem Benv.Canonical.setStor {benv : Benv} (h : benv.Canonical)
    (adr : Address) {s : Storage} (hs : Storage.Canonical s) :
    (benv.setStor adr s).Canonical :=
  ⟨State.Canonical.setStor h.1 adr hs, h.2⟩

theorem Benv.Canonical.setStorVal {benv : Benv} (h : benv.Canonical)
    (adr : Address) (k v : U256) : (benv.setStorVal adr k v).Canonical :=
  ⟨State.Canonical.setStorVal h.1 adr k v, h.2⟩

/-- Opening a transaction saves the current state as the transaction-original
state, so a canonical environment stays canonical on both components. -/
theorem Benv.Canonical.beginTransaction {benv : Benv} (h : benv.Canonical) :
    benv.beginTransaction.Canonical :=
  ⟨h.1, h.1⟩

theorem Benv.Canonical.addCreatedAccount {benv : Benv} (h : benv.Canonical)
    (adr : Address) : (addCreatedAccount benv adr).Canonical :=
  ⟨h.1, h.2⟩

theorem Tenv.Canonical.setTransVal {tenv : Tenv} (h : tenv.Canonical)
    (adr : Address) (k v : U256) : (tenv.setTransVal adr k v).Canonical :=
  TransientStorage.Canonical.setStorageValue h adr k v

theorem Msg.Canonical.withBenv {msg : Msg} (h : msg.Canonical)
    {benv : Benv} (hb : benv.Canonical) : (msg.withBenv benv).Canonical :=
  ⟨hb, h.2⟩

theorem Msg.Canonical.incrNonce {msg : Msg} (h : msg.Canonical)
    (adr : Address) : (msg.incrNonce adr).Canonical :=
  ⟨⟨State.Canonical.incrNonce h.1.1 adr, h.1.2⟩, h.2⟩

theorem Msg.Canonical.setCode {msg : Msg} (h : msg.Canonical)
    (adr : Address) (cd : ByteArray) : (msg.setCode adr cd).Canonical :=
  ⟨⟨State.Canonical.setCode h.1.1 adr cd, h.1.2⟩, h.2⟩

-- Child incorporation and the settlement-to-execution bridge: the parent's
-- world is replaced wholesale, so only the incoming state's canonicality
-- matters. These are the exact joints through which a frame's result
-- re-enters its parent.

-- Checkpoint 2 of the corpus: through the instruction arms. First the intro
-- forms and the settle-carrier sequencing lemma, then a descent tactic for
-- the homogeneous machine-level `do`-chains.

theorem Except.canonicalOn_ok {ρ α : Type} {P : α → Prop} {a : α} (h : P a) :
    (Except.ok a : Except (ρ × Devm) α).CanonicalOn P := h

/-- `.ok a >>= f` is `f a` by iota, so sequencing after a pure binding needs
no case split. Stated so the descent tactic can skip the abstraction. -/
theorem Except.canonicalOn_bind_ok {ρ α β : Type} {P : β → Prop} {a : α}
    {f : α → Except (ρ × Devm) β} (h : (f a).CanonicalOn P) :
    ((Except.ok a : Except (ρ × Devm) α) >>= f).CanonicalOn P := h

/-! ### The world frame

Every instruction that writes neither storage, transient storage, nor (through
`SELFDESTRUCT`) balances keeps three components of the machine it starts from:
the world -- state and transient storage -- and the two deletion-relevant sets,
`accountsToDelete` and `createdAccounts`. This is the one arm-by-arm walk of
those instructions (`PlainOp.runCore_worldFrame`, `JumpOp.runCore_worldFrame`,
`HaltOp.run_worldFrame`); canonicality of the same arms is a corollary of it
(`Execution.WorldFrame.canonical`), because canonicality reads only the world.
Both channels are covered: an error keeps the frame of the machine it
carries, which execution goes on using. -/

/-- `d'` keeps `d`'s world and its two deletion-relevant sets. Every other
component -- stack, memory, both gas pools, logs, refunds, output, return data,
access sets and the EIP-7928 read sets -- is left free. -/
structure Devm.WorldFrame (d d' : Devm) : Prop where
  world : d.world = d'.world
  accountsToDelete : d.accountsToDelete = d'.accountsToDelete
  createdAccounts : d.createdAccounts = d'.createdAccounts

theorem Devm.WorldFrame.refl (d : Devm) : d.WorldFrame d := ⟨rfl, rfl, rfl⟩

theorem Devm.WorldFrame.trans {d₁ d₂ d₃ : Devm} (h₁ : d₁.WorldFrame d₂)
    (h₂ : d₂.WorldFrame d₃) : d₁.WorldFrame d₃ :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2, h₁.3.trans h₂.3⟩

/-- Extend a frame by a step that leaves the three components alone; each
premise is `rfl` for a `Mach`- or `Meta`-only update. -/
theorem Devm.WorldFrame.keep {pre d d' : Devm} (h : pre.WorldFrame d)
    (hw : d.world = d'.world) (ha : d.accountsToDelete = d'.accountsToDelete)
    (hc : d.createdAccounts = d'.createdAccounts) : pre.WorldFrame d' :=
  h.trans ⟨hw, ha, hc⟩

theorem Devm.WorldFrame.state {d d' : Devm} (h : d.WorldFrame d') :
    d.state = d'.state :=
  congrArg World.state h.world

theorem Devm.WorldFrame.transientStorage {d d' : Devm} (h : d.WorldFrame d') :
    d.transientStorage = d'.transientStorage :=
  congrArg World.transientStorage h.world

theorem Devm.Canonical.of_worldFrame {d d' : Devm} (h : d.Canonical)
    (hf : d.WorldFrame d') : d'.Canonical :=
  h.of_world_eq hf.world.symm

/-- The world frame of a machine-level result, on both channels: the error
channel's machine keeps `pre`'s frame outright, an ok payload meets the
caller's predicate (for a machine payload, `pre.WorldFrame`). -/
def Except.WorldFrameOn {ρ α : Type} (pre : Devm) (P : α → Prop) :
    Except (ρ × Devm) α → Prop
  | .ok a => P a
  | .error e => pre.WorldFrame e.2

/-- A whole-machine execution result keeps `pre`'s frame on both channels. -/
abbrev Execution.WorldFrame (pre : Devm) (x : Execution) : Prop :=
  x.WorldFrameOn pre pre.WorldFrame

theorem Except.WorldFrameOn.bind {ρ α β : Type} {pre : Devm} {P : α → Prop}
    {Q : β → Prop} {x : Except (ρ × Devm) α} {f : α → Except (ρ × Devm) β}
    (hx : x.WorldFrameOn pre P) (hf : ∀ a, P a → (f a).WorldFrameOn pre Q) :
    (x >>= f).WorldFrameOn pre Q := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem Except.WorldFrameOn.map {ρ α β : Type} {pre : Devm} {P : α → Prop}
    {Q : β → Prop} {x : Except (ρ × Devm) α} {f : α → β}
    (hx : x.WorldFrameOn pre P) (hf : ∀ a, P a → Q (f a)) :
    (x <&> f).WorldFrameOn pre Q := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem Except.WorldFrameOn.imp {ρ α : Type} {pre : Devm} {P Q : α → Prop}
    {x : Except (ρ × Devm) α} (hx : x.WorldFrameOn pre P)
    (hf : ∀ a, P a → Q a) : x.WorldFrameOn pre Q := by
  cases x with
  | error e => exact hx
  | ok a => exact hf a hx

theorem Except.worldFrameOn_error {ρ α : Type} {pre : Devm} {P : α → Prop}
    {e : ρ × Devm} (h : pre.WorldFrame e.2) :
    (Except.error e : Except (ρ × Devm) α).WorldFrameOn pre P := h

theorem Except.worldFrameOn_assert {p : Prop} [Decidable p] {ρ : Type}
    {pre : Devm} {e : ρ × Devm} (h : pre.WorldFrame e.2) :
    (Except.assert p e).WorldFrameOn pre (fun _ => True) := by
  unfold Except.assert
  split
  · trivial
  · exact h

/-- Canonicality from the frame: the error channel's machine and every
payload the predicate covers share `pre`'s world. -/
theorem Except.WorldFrameOn.canonicalOn {ρ α : Type} {pre : Devm}
    {P Q : α → Prop} {x : Except (ρ × Devm) α} (hpre : pre.Canonical)
    (hx : x.WorldFrameOn pre P) (hf : ∀ a, P a → Q a) : x.CanonicalOn Q := by
  cases x with
  | error e => exact hpre.of_worldFrame hx
  | ok a => exact hf a hx

theorem Execution.WorldFrame.canonical {pre : Devm} {x : Execution}
    (hpre : pre.Canonical) (hx : x.WorldFrame pre) : x.Canonical :=
  Except.WorldFrameOn.canonicalOn hpre hx fun _ hd => hpre.of_worldFrame hd

-- The lifted footprint combinators and the named `Meta` recorders.

theorem liftMach_worldFrameOn {α : Type} {core : Mach → Footprint.Outcome Mach α}
    {pre devm : Devm} (h : pre.WorldFrame devm) :
    (liftMach core devm).WorldFrameOn pre (fun a => pre.WorldFrame a.2) := by
  unfold liftMach Footprint.liftOutcome
  split <;> exact h.keep rfl rfl rfl

theorem Footprint.toExecution_worldFrame {pre : Devm}
    {x : Except (EvmError × Devm) (Unit × Devm)}
    (hx : x.WorldFrameOn pre (fun a => pre.WorldFrame a.2)) :
    (Footprint.toExecution x).WorldFrame pre := by
  cases x with
  | error e => exact hx
  | ok a => exact hx

theorem liftMachExecution_worldFrame {core : Mach → Footprint.Outcome Mach Unit}
    {pre devm : Devm} (h : pre.WorldFrame devm) :
    (liftMachExecution core devm).WorldFrame pre :=
  Footprint.toExecution_worldFrame (liftMach_worldFrameOn h)

theorem Devm.balReadAccount_worldFrame {pre devm : Devm} {rules : ForkRules}
    {a : Address} (h : pre.WorldFrame devm) :
    pre.WorldFrame (devm.balReadAccount rules a) := by
  unfold Devm.balReadAccount
  split <;> exact h.keep rfl rfl rfl

theorem Devm.balReadStorage_worldFrame {pre devm : Devm} {rules : ForkRules}
    {a : Address} {k : U256} (h : pre.WorldFrame devm) :
    pre.WorldFrame (devm.balReadStorage rules a k) := by
  unfold Devm.balReadStorage
  split <;> exact h.keep rfl rfl rfl

/-- The eq-conditioned `memRead` step, matching the hypothesis a destructuring
`let` leaves behind. -/
theorem Devm.memRead_eq_worldFrame {pre devm d' : Devm} {i s : Nat}
    {val : Bytes} (h : pre.WorldFrame devm) (heq : devm.memRead i s = (val, d')) :
    pre.WorldFrame d' := by
  unfold Devm.memRead at heq
  rcases hm : devm.memory.read i s with ⟨v, mem⟩
  rw [hm] at heq
  cases heq
  exact h.keep rfl rfl rfl

/-- `BALANCE`'s core warms one address and records one read: neither touches
the deletion-relevant sets. -/
theorem PlainOp.balanceCore_worldFrame {rules : ForkRules} {pre devm : Devm}
    (h : pre.WorldFrame devm) :
    (liftMachMetaWorldExecution (PlainOp.balanceCore rules) devm).WorldFrame pre := by
  simp only [liftMachMetaWorldExecution, liftMachMetaExecution, liftMachMeta,
    Footprint.liftOutcome, PlainOp.balanceCore]
  have hv : ∀ v : Meta, v.accountsToDelete = devm.meta.accountsToDelete →
      v.createdAccounts = devm.meta.createdAccounts →
      ∀ m, pre.WorldFrame { mach := m, «meta» := v, world := devm.world } :=
    fun _ ha hc _ => h.keep rfl ha.symm hc.symm
  rcases hp : devm.mach.pop with ⟨err, m⟩ | ⟨⟨x, m⟩⟩
  · exact hv _ rfl rfl m
  have h1 : (match rules.access with
      | .eip2929 => if x.toAddress ∈ devm.meta.accessedAddresses then devm.meta
          else devm.meta.addAccessedAddress x.toAddress
      | .flat _ => devm.meta).accountsToDelete =
        devm.meta.accountsToDelete ∧
      (match rules.access with
      | .eip2929 => if x.toAddress ∈ devm.meta.accessedAddresses then devm.meta
          else devm.meta.addAccessedAddress x.toAddress
      | .flat _ => devm.meta).createdAccounts =
        devm.meta.createdAccounts := by
    split <;> (try split) <;> exact ⟨rfl, rfl⟩
  simp only
  rcases Mach.chargeGas (match rules.access with
      | .eip2929 => if x.toAddress ∈ devm.meta.accessedAddresses then Gas.warmStorageReadCost
          else rules.gas.coldAccountAccess
      | .flat g => g.balance) m with ⟨err, m'⟩ | ⟨_, m'⟩
  · exact hv _ h1.1 h1.2 m'
  simp only
  rcases Mach.push (devm.world.state.get x.toAddress).balance m' with ⟨err, m''⟩ | ⟨_, m''⟩ <;>
    exact hv _ (by split <;> exact h1.1) (by split <;> exact h1.2) m''

/-- The world frame through every register-instruction arm but the two
writers. -/
theorem PlainOp.runCore_worldFrame (pc : Nat) (sevm : Sevm) (devm : Devm)
    (r : PlainOp) (hs : r ≠ .sstore) (ht : r ≠ .tstore) :
    (PlainOp.runCore pc devm sevm r).WorldFrame devm := by
  have h := Devm.WorldFrame.refl devm
  cases r <;> simp only [PlainOp.runCore]
  case sstore => exact absurd rfl hs
  case tstore => exact absurd rfl ht
  case balance => exact PlainOp.balanceCore_worldFrame h
  case mload =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) ?_
    rintro ⟨start, d1⟩ h1
    refine Except.WorldFrameOn.bind (liftMachExecution_worldFrame h1) ?_
    intro d2 h2
    rcases hread : d2.memRead start 32 with ⟨val, d3⟩
    exact liftMachExecution_worldFrame (Devm.memRead_eq_worldFrame h2 hread)
  case keccak256 =>
    have hbr := PlainOp.runCore_keccak256_eq_reference pc devm sevm
    show (PlainOp.runCore pc devm sevm .keccak256).WorldFrame devm
    rw [hbr]
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) ?_
    rintro ⟨start, d1⟩ h1
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h1) ?_
    rintro ⟨size, d2⟩ h2
    refine Except.WorldFrameOn.bind (liftMachExecution_worldFrame h2) ?_
    intro d3 h3
    rcases hread : d3.memRead start size with ⟨arg, d4⟩
    exact liftMachExecution_worldFrame (Devm.memRead_eq_worldFrame h3 hread)
  case mcopy =>
    split
    · refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) ?_
      rintro ⟨dest, d1⟩ h1
      refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h1) ?_
      rintro ⟨src, d2⟩ h2
      refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h2) ?_
      rintro ⟨len, d3⟩ h3
      refine Except.WorldFrameOn.bind (liftMachExecution_worldFrame h3) ?_
      intro d4 h4
      rcases hread : d4.memRead src len with ⟨val, d5⟩
      exact (Devm.memRead_eq_worldFrame h4 hread).keep rfl rfl rfl
    · exact h
  case log =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) ?_
    rintro ⟨start, d1⟩ h1
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h1) ?_
    rintro ⟨size, d2⟩ h2
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h2) ?_
    rintro ⟨topics, d3⟩ h3
    refine Except.WorldFrameOn.bind (liftMachExecution_worldFrame h3) ?_
    intro d4 h4
    refine Except.WorldFrameOn.bind (Except.worldFrameOn_assert h4) ?_
    intro u _
    rcases hread : d4.memRead start size with ⟨data, d5⟩
    exact (Devm.memRead_eq_worldFrame h4 hread).keep rfl rfl rfl
  all_goals try exact liftMachExecution_worldFrame h
  case exp =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn ha) fun b hb => ?_
    exact Except.WorldFrameOn.bind (liftMachExecution_worldFrame hb)
      fun d hd => liftMachExecution_worldFrame hd
  case clz =>
    split
    · exact liftMachExecution_worldFrame h
    · exact h
  case slotnum =>
    split
    · exact liftMachExecution_worldFrame h
    · exact h
  case shl | shr | sar =>
    split
    · exact liftMachExecution_worldFrame h
    · exact h
  case chainid | basefee | blobbasefee =>
    split
    · exact liftMachExecution_worldFrame h
    · exact h
  case selfbalance =>
    split
    · exact Except.WorldFrameOn.bind (liftMachExecution_worldFrame h)
        fun d hd => liftMachExecution_worldFrame (Devm.balReadAccount_worldFrame hd)
    · exact h
  case calldataload =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
    exact Except.WorldFrameOn.bind (liftMachExecution_worldFrame ha)
      fun d hd => liftMachExecution_worldFrame hd
  case calldatacopy | codecopy =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn ha) fun b hb => ?_
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn hb) fun c hc => ?_
    exact Except.WorldFrameOn.bind (liftMachExecution_worldFrame hc)
      fun d hd => hd.keep rfl rfl rfl
  case extcodesize =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
    split <;> (try split) <;>
      exact Except.WorldFrameOn.bind
        (liftMachExecution_worldFrame (ha.keep rfl rfl rfl))
        fun d hd => liftMachExecution_worldFrame (Devm.balReadAccount_worldFrame hd)
  case extcodehash =>
    split
    · refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
      split <;> (try split) <;>
        exact Except.WorldFrameOn.bind
          (liftMachExecution_worldFrame (ha.keep rfl rfl rfl))
          fun d hd => liftMachExecution_worldFrame (Devm.balReadAccount_worldFrame hd)
    · exact h
  case extcodecopy =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn ha) fun b hb => ?_
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn hb) fun c hc => ?_
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn hc) fun e he => ?_
    split <;> (try split) <;>
      exact Except.WorldFrameOn.bind
        (liftMachExecution_worldFrame (he.keep rfl rfl rfl))
        fun d hd => (Devm.balReadAccount_worldFrame hd).keep rfl rfl rfl
  case returndatacopy =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn ha) fun b hb => ?_
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn hb) fun c hc => ?_
    refine Except.WorldFrameOn.bind (liftMachExecution_worldFrame hc) fun d hd => ?_
    split
    · exact Except.WorldFrameOn.bind
        (Except.worldFrameOn_error (P := fun _ => True) hd)
        fun _ _ => hd.keep rfl rfl rfl
    · exact hd.keep rfl rfl rfl
  case blockhash =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
    exact Except.WorldFrameOn.bind (liftMachExecution_worldFrame ha)
      fun d hd => liftMachExecution_worldFrame hd
  case blobhash =>
    split
    · refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
      exact Except.WorldFrameOn.bind (liftMachExecution_worldFrame ha)
        fun d hd => liftMachExecution_worldFrame hd
    · exact h
  case pop =>
    exact Except.WorldFrameOn.bind
      (Except.WorldFrameOn.map (liftMach_worldFrameOn h) fun _ ha => ha)
      fun d hd => liftMachExecution_worldFrame hd
  case mstore | mstore8 =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn ha) fun b hb => ?_
    exact Except.WorldFrameOn.bind (liftMachExecution_worldFrame hb)
      fun d hd => hd.keep rfl rfl rfl
  case sload =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
    split <;> (try split) <;>
      exact Except.WorldFrameOn.bind
        (liftMachExecution_worldFrame (ha.keep rfl rfl rfl))
        fun d hd => liftMachExecution_worldFrame (Devm.balReadStorage_worldFrame hd)
  case tload =>
    split
    · refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
      exact liftMachExecution_worldFrame ha
    · exact h
  case gas =>
    exact Except.WorldFrameOn.bind (liftMachExecution_worldFrame h)
      fun d hd => liftMachExecution_worldFrame hd
  case dup =>
    refine Except.WorldFrameOn.bind (liftMachExecution_worldFrame h) fun d hd => ?_
    split
    · exact hd
    · exact liftMachExecution_worldFrame hd
  case swap =>
    refine Except.WorldFrameOn.bind (liftMachExecution_worldFrame h) fun d hd => ?_
    split
    · exact hd
    · exact hd.keep rfl rfl rfl

theorem PlainOp.run_worldFrame (evm : Evm) (r : PlainOp) (hs : r ≠ .sstore)
    (ht : r ≠ .tstore) : (PlainOp.run evm r).WorldFrame evm.dyna :=
  PlainOp.runCore_worldFrame evm.pc evm.sta evm.dyna r hs ht

/-- Jump instructions keep the frame; the payload carries the new program
counter beside the machine. -/
theorem JumpOp.runCore_worldFrame (pc : Nat) (sevm : Sevm) (devm : Devm)
    (j : JumpOp) :
    (JumpOp.runCore pc devm sevm j).WorldFrameOn devm
      (fun a => devm.WorldFrame a.2) := by
  have h := Devm.WorldFrame.refl devm
  cases j <;> simp only [JumpOp.runCore]
  case jumpdest =>
    exact Except.WorldFrameOn.bind (liftMachExecution_worldFrame h) fun d hd => hd
  case jump =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
    refine Except.WorldFrameOn.bind (liftMachExecution_worldFrame ha) fun d hd => ?_
    exact Except.WorldFrameOn.bind (Except.worldFrameOn_assert hd) fun _ _ => hd
  case jumpi =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn ha) fun b hb => ?_
    refine Except.WorldFrameOn.bind (liftMachExecution_worldFrame hb) fun d hd => ?_
    split
    · exact hd
    · exact Except.WorldFrameOn.bind (Except.worldFrameOn_assert hd) fun _ _ => hd

theorem JumpOp.run_worldFrame (evm : Evm) (j : JumpOp) :
    (JumpOp.run evm j).WorldFrameOn evm.dyna (fun a => evm.dyna.WorldFrame a.2) :=
  JumpOp.runCore_worldFrame evm.pc evm.sta evm.dyna j

/-- The halting instructions other than `SELFDESTRUCT` keep the frame. -/
theorem HaltOp.run_worldFrame (sevm : Sevm) (devm : Devm) (l : HaltOp)
    (hl : l ≠ .selfdestruct) : Execution.WorldFrame devm (HaltOp.run sevm devm l) := by
  have h := Devm.WorldFrame.refl devm
  cases l <;> simp only [HaltOp.run]
  case selfdestruct => exact absurd rfl hl
  case stop => exact h
  case revert | return_ =>
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn h) fun a ha => ?_
    refine Except.WorldFrameOn.bind (liftMach_worldFrameOn ha) fun b hb => ?_
    refine Except.WorldFrameOn.bind (liftMachExecution_worldFrame hb) fun d hd => ?_
    rcases hread : d.memRead a.1 b.1 with ⟨out, d'⟩
    exact (Devm.memRead_eq_worldFrame hd hread).keep rfl rfl rfl

/-- Canonicality through every register-instruction arm. Only `SSTORE` and
`TSTORE` change the world, each through its named mutator, and are walked
here; every other arm keeps the world frame (`PlainOp.runCore_worldFrame`). -/
theorem PlainOp.runCore_canonical (pc : Nat) {devm : Devm} (sevm : Sevm)
    (h : devm.Canonical) (r : PlainOp) :
    (PlainOp.runCore pc devm sevm r).Canonical := by
  by_cases hs : r = .sstore
  · subst hs
    simp only [PlainOp.runCore]
    split
    · -- The `none` arm: Prague first, then the pre-Berlin regimes.
      split
      · -- Prague: the body it has always been.
        refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
        refine Except.CanonicalOn.bind (Except.canonicalOn_assert hb) fun _ _ => ?_
        split <;>
          (refine Except.canonicalOn_bind_ok ?_
           refine Except.canonicalOn_bind_ok ?_
           refine Except.canonicalOn_bind_ok ?_
           refine Except.CanonicalOn.bind
             (liftMachExecution_canonical (Devm.Canonical.of_world_eq hb rfl))
             fun d hd => ?_
           refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd) fun _ _ => ?_
           exact Devm.Canonical.setStorVal hd _ _ _)
      · -- The pre-Berlin regimes: the same binds; the cold pair cases on
        -- access, and the cold branch on the slot's warmth.
        refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
        refine Except.CanonicalOn.bind (Except.canonicalOn_assert hb) fun _ _ => ?_
        cases hac : sevm.benvStat.rules.access with
        | flat _ =>
          (refine Except.canonicalOn_bind_ok ?_
           refine Except.canonicalOn_bind_ok ?_
           refine Except.canonicalOn_bind_ok ?_
           refine Except.CanonicalOn.bind
             (liftMachExecution_canonical (Devm.Canonical.of_world_eq hb rfl))
             fun d hd => ?_
           refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd) fun _ _ => ?_
           exact Devm.Canonical.setStorVal hd _ _ _)
        | eip2929 =>
          dsimp only
          split <;>
            (refine Except.canonicalOn_bind_ok ?_
             refine Except.canonicalOn_bind_ok ?_
             refine Except.canonicalOn_bind_ok ?_
             refine Except.CanonicalOn.bind
               (liftMachExecution_canonical (Devm.Canonical.of_world_eq hb rfl))
               fun d hd => ?_
             refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd) fun _ _ => ?_
             exact Devm.Canonical.setStorVal hd _ _ _)
    · -- Amsterdam: the static check first, the pops, the pre-check, then the
      -- two charges, neither of which touches the world.
      refine Except.CanonicalOn.bind (assertDynamic_canonicalOn h) fun _ _ => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hb) fun _ _ => ?_
      split <;>
        (refine Except.CanonicalOn.bind
           (liftMachExecution_canonical (Devm.Canonical.of_world_eq hb rfl))
           fun d hd => ?_
         refine Except.CanonicalOn.bind (liftMachExecution_canonical hd)
           fun d' hd' => ?_
         exact Devm.Canonical.setStorVal hd' _ _ _)
  by_cases ht : r = .tstore
  · subst ht
    simp only [PlainOp.runCore]
    split
    · -- Gate on: the two metering shapes below, as before.
      split
      · refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
        refine Except.CanonicalOn.bind (liftMachExecution_canonical hb)
          fun d hd => ?_
        refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd)
          fun _ _ => ?_
        exact Devm.Canonical.setTransVal hd _ _ _
      · refine Except.CanonicalOn.bind (assertDynamic_canonicalOn h)
          fun _ _ => ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
        refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
        refine Except.CanonicalOn.bind (liftMachExecution_canonical hb)
          fun d hd => ?_
        exact Devm.Canonical.setTransVal hd _ _ _
    · -- Gate off: the undefined-opcode error keeps the machine.
      exact h
  exact (PlainOp.runCore_worldFrame pc sevm devm r hs ht).canonical h

theorem PlainOp.run_canonical {evm : Evm} (h : evm.dyna.Canonical) (r : PlainOp) :
    (PlainOp.run evm r).Canonical :=
  PlainOp.runCore_canonical evm.pc evm.sta h r

/-- Destroying any list of accounts preserves canonicality; transaction
settlement folds `destroyAccount` over the accounts-to-delete set. -/
theorem State.Canonical.foldl_destroyAccount {l : List Address} {w : State}
    (h : w.Canonical) : (l.foldl Jaune.destroyAccount w).Canonical := by
  induction l generalizing w with
  | nil => exact h
  | cons a l ih => exact ih (h.destroyAccount a)

/-- Jump instructions never touch the world; the payload carries the new
program counter beside the machine. -/
theorem JumpOp.runCore_canonicalOn (pc : Nat) {devm : Devm} (sevm : Sevm)
    (h : devm.Canonical) (j : JumpOp) :
    (JumpOp.runCore pc devm sevm j).CanonicalOn (fun a => a.2.Canonical) :=
  (JumpOp.runCore_worldFrame pc sevm devm j).canonicalOn h
    fun _ ha => h.of_worldFrame ha

theorem JumpOp.run_canonicalOn {evm : Evm} (h : evm.dyna.Canonical) (j : JumpOp) :
    (JumpOp.run evm j).CanonicalOn (fun a => a.2.Canonical) :=
  JumpOp.runCore_canonicalOn evm.pc evm.sta h j

/-- Canonicality through the halting instructions. `SELFDESTRUCT` is the one
world-changing arm, and it factors through `subBal`/`addBal`/`setBal`. -/
theorem HaltOp.run_canonical {sevm : Sevm} {devm : Devm}
    (h : devm.Canonical) (l : HaltOp) :
    Execution.Canonical (HaltOp.run sevm devm l) := by
  by_cases hl : l = .selfdestruct
  · subst hl
    simp only [HaltOp.run]
    split
    · -- Prague: the body it has always been.
      refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
      refine Except.canonicalOn_bind_ok ?_
      refine Except.canonicalOn_bind_ok ?_
      split <;> (try split) <;>
        (refine Except.canonicalOn_bind_ok ?_
         refine Except.CanonicalOn.bind
           (liftMachExecution_canonical (Devm.Canonical.of_world_eq ha rfl))
           fun d hd => ?_
         refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd) fun _ _ => ?_
         -- The EIP-7928 read recorders are meta-only: read the balance through them.
         simp only [Devm.balReadAccount_getAcct]
         refine Except.CanonicalOn.bind (P := Devm.Canonical) ?_ fun d' hd' => ?_
         · cases hs : d.subBal sevm.currentTarget (a.2.getAcct sevm.currentTarget).balance with
           | none => exact hd
           | some d1 => exact Devm.Canonical.subBal hd hs
         · refine Except.canonicalOn_bind_ok ?_
           split
           · exact creditSelfdestructRefund_canonical
               (Devm.Canonical.of_world_eq
                 (Devm.Canonical.setBal (hd'.creditBeneficiary _ a.1 _) _ 0) rfl)
           · exact hd'.creditBeneficiary _ a.1 _)
    · -- Amsterdam: the static check, the pop, the pre-check, the two charges
      -- (neither touches the world), the sweep, the log, the schedule.
      refine Except.CanonicalOn.bind (assertDynamic_canonicalOn h) fun _ _ => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert ha) fun _ _ => ?_
      split <;>
        (refine Except.CanonicalOn.bind
           (liftMachExecution_canonical (Devm.Canonical.of_world_eq ha rfl))
           fun d hd => ?_
         refine Except.CanonicalOn.bind (liftMachExecution_canonical hd)
           fun d' hd' => ?_
         refine Except.CanonicalOn.bind (P := Devm.Canonical) ?_ fun d2 hd2 => ?_
         · cases hs : d'.subBal sevm.currentTarget _ with
           | none => exact hd'
           | some d1 => exact Devm.Canonical.subBal hd' hs
         · split
           · exact addAccountToDelete_canonical
               (Devm.emitTransferLog_canonical (Devm.Canonical.addBal hd2 a.1 _))
           · exact Devm.emitTransferLog_canonical (Devm.Canonical.addBal hd2 a.1 _))
  exact (HaltOp.run_worldFrame sevm devm l hl).canonical h

end Jaune
