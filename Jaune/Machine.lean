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
    (blobVersionedHashes : List Hash32)
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
  parentHash : Hash32
  ommersHash : Hash32
  coinbase : Address
  stateRoot : Hash32
  transactionsRoot : Hash32
  receiptsRoot : Hash32
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
  withdrawalsRoot : Option Hash32
  /-- EIP-4844 (Cancun); present exactly when `excessBlobGas` is. -/
  blobGasUsed : Option Nat
  /-- EIP-4844 (Cancun). -/
  excessBlobGas : Option Nat
  /-- EIP-4788 (Cancun). -/
  parentBeaconBlockRoot : Option Hash32
  requestsHash : Option Hash32
  /-- EIP-7928: the commitment to the block-level access list.

  Optional in the same sense `requestsHash` is: the field exists on the wire
  only at forks that define it, and `ForkRules.header.blockAccessListHash` is
  what says which those are. `none` is "this fork has no such field", never
  "the field is zero". -/
  blockAccessListHash : Option Hash32
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
def Header.hash (header : Header) : Hash32 :=
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

def TransactionType.blobVersionedHashes : TransactionType → List Hash32
  | .legacy _ _ => []
  | .eip2930 _ _ _ _ => []
  | .eip1559 _ _ _ _ _ => []
  | .eip4844 _ _ _ _ _ _ bhs => bhs
  | .eip7702 _ _ _ _ _ _ => []

def Transaction.blobVersionedHashes (tx : Transaction) : List Hash32 := tx.type.blobVersionedHashes

-- nibbles-to-bytes maps
abbrev TrieBuilder := Std.TreeMap (List UInt8) (List UInt8) (@List.compare _ ⟨UInt8.compareLows⟩)

def packNibbles : Bytes → (Option UInt8 × Bytes)
  | [] => ⟨none, []⟩
  | n :: ns =>
    match packNibbles ns with
    | ⟨none, bs⟩ => ⟨some n, bs⟩
    | ⟨some m, bs⟩ => ⟨none, ((n <<< 4) ||| m.lows) :: bs⟩

def hexPrefix (ns : Bytes) (t : Bool) : Bytes :=
  match packNibbles ns with
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

def dropPrefix? : Bytes → Bytes → Option Bytes
  | [], ns => some ns
  | _, [] => none
  | n :: ns, n' :: ns' =>
    if n = n' then dropPrefix? ns ns' else none

def insertWithoutPrefix (pfx : Bytes) (m : TrieBuilder) (ns : Bytes) (bs : Bytes) : Option TrieBuilder := do
  (m.insert · bs) <$> dropPrefix? pfx ns

def TrieBuilder.factor (m : TrieBuilder) : Option (Bytes × TrieBuilder) := do
  let ((n :: ns) :: nss) ← some (m.toList.map Prod.fst) | none
  let pfx ← commonPrefix n ns nss
  let m' ← Std.TreeMap.foldlM (insertWithoutPrefix pfx) TrieBuilder.empty m
  some ⟨pfx, m'⟩

structure TrieBranches : Type where
  (child0 : TrieBuilder) (child1 : TrieBuilder) (child2 : TrieBuilder) (child3 : TrieBuilder)
  (child4 : TrieBuilder) (child5 : TrieBuilder) (child6 : TrieBuilder) (child7 : TrieBuilder)
  (child8 : TrieBuilder) (child9 : TrieBuilder) (child10 : TrieBuilder) (child11 : TrieBuilder)
  (child12 : TrieBuilder) (child13 : TrieBuilder) (child14 : TrieBuilder) (child15 : TrieBuilder)

def TrieBranches.empty : TrieBranches :=
  ⟨ .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty ⟩

def TrieBranches.update (js : TrieBranches) (f : TrieBuilder → TrieBuilder) (k : UInt8) : TrieBranches :=
  match k.toBits with
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
  | ⟨_, _, _, _, 1, 0, 1, 0⟩ => { js with child10 := f js.child10}
  | ⟨_, _, _, _, 1, 0, 1, 1⟩ => { js with child11 := f js.child11}
  | ⟨_, _, _, _, 1, 1, 0, 0⟩ => { js with child12 := f js.child12}
  | ⟨_, _, _, _, 1, 1, 0, 1⟩ => { js with child13 := f js.child13}
  | ⟨_, _, _, _, 1, 1, 1, 0⟩ => { js with child14 := f js.child14}
  | ⟨_, _, _, _, 1, 1, 1, 1⟩ => { js with child15 := f js.child15}

def TrieBranches.insert (js : TrieBranches) : Bytes → Bytes → TrieBranches
  | [], _ => js
  | n :: ns, bs => js.update (Std.TreeMap.insert · ns bs) n

def Std.TreeMap.isSingleton {K V : Type} (cmp : K → K → Ordering)
    (m : Std.TreeMap K V cmp) : Bool :=
  m.size = 1

mutual

  def trieNodeReference : Nat → TrieBuilder → Rlp.Item
    | 0, _ => .bytes []
    | k + 1, j =>
      if j.isEmpty
      then .bytes []
      else let r := encodeTrieNode k j
           if r.toBytes.length < 32
           then r
           else .bytes <| r.toBytes.keccak.toBytes

  def encodeTrieNode : Nat → TrieBuilder → Rlp.Item
    | 0, _ => .bytes []
    | k + 1, j =>
      if j.isEmpty
            then .bytes []       else if j.isSingleton
           then match j.toList with
                | [(k, v)] => .list [.bytes (hexPrefix k 1), .bytes v]
                | _ => .bytes []            else match j.factor with
                | none =>
                  let js := Std.TreeMap.foldl TrieBranches.insert TrieBranches.empty j
                  .list [ trieNodeReference k js.child0, trieNodeReference k js.child1, trieNodeReference k js.child2,
                          trieNodeReference k js.child3, trieNodeReference k js.child4, trieNodeReference k js.child5,
                          trieNodeReference k js.child6, trieNodeReference k js.child7, trieNodeReference k js.child8,
                          trieNodeReference k js.child9, trieNodeReference k js.child10, trieNodeReference k js.child11,
                          trieNodeReference k js.child12, trieNodeReference k js.child13, trieNodeReference k js.child14,
                          trieNodeReference k js.child15, .bytes (j.getD [] []) ]
                | some (pfx, j') => .list [.bytes (hexPrefix pfx 0), trieNodeReference k j']

end

def TrieBuilder.maxKeyLength (j : TrieBuilder) : Nat :=
  (j.toList.map (List.length ∘ Prod.fst)).maxD 0

def collapse (j : TrieBuilder) : Rlp.Item := encodeTrieNode (2 * (j.maxKeyLength + 1)) j

def trie (j : TrieBuilder) : Hash32 :=
  Bytes.keccak <| (collapse j).toBytes

def U256.toRlpItem (w : U256) : Rlp.Item := .bytes w.toBytes

def Storage.toTrieBuilder (s : Storage) : TrieBuilder :=
  let f : TrieBuilder → U256 → U256 → TrieBuilder :=
    λ j k v =>
      j.insert
        k.keccak.toNibbles
        ((Rlp.Item.toBytes <| .bytes <| Bytes.sig <| v.toBytes))
  Std.TreeMap.foldl f TrieBuilder.empty s

def U256.leadingZeroBytesWithin (x : U256) : Nat → Nat
  | 0 => 0
  | k + 1 => if x = 0 then k + 1 else U256.leadingZeroBytesWithin (x >>> 8) k

def U256.significantByteCount (x : U256) : Nat := 32 - (U256.leadingZeroBytesWithin x 32)

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
def Gas.sstoreClearsSchedule : Nat := 4800
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
def Gas.p256verify : Nat := 6900
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
def depositEventSignatureHash : Hash32 :=
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
def emptyOmmerHash : Hash32 := (Rlp.Item.list []).toBytes.keccak
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
@[simp] theorem pragueRules_gas_sstoreClearsSchedule :
    pragueRules.gas.sstoreClearsSchedule = Gas.sstoreClearsSchedule := rfl
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

theorem GasSchedule.Valid.stipend_at_most_callValue {g : GasSchedule} (h : g.Valid) :
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

abbrev AddressSet : Type := @Std.HashSet Address _ _
abbrev KeySet : Type := @Std.HashSet (Address × U256) _ _

abbrev TransientStorage : Type := Std.TreeMap Address Storage compare

def calculateMemoryGasCost (memSize : Nat) : Nat :=
  let memWordSize := ceilDiv memSize 32
  let linearCost := Gas.memory * memWordSize
  let quadraticCost := (memWordSize ^ 2) / 512
  linearCost + quadraticCost

structure Log : Type where
  (address : Address)
  (topics : List U256)
  (data : Bytes)

-- class Benvironment

-- class TransactionEnvironment

-- class Message

-- `origState` is the original state of a *transaction*, not of a block: it is
-- what `SSTORE` compares against to tell a clean update from a dirty one
-- (finding 3.8). Every normal and system transaction must open with this so
-- that its own input state, rather than the block prestate, is the original
-- state. The transaction write ledger starts empty; the remaining environment is preserved.

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
/-- A typed transaction whose type byte is not supported by EIP-2718 (decision 16). -/
def typeNotSupportedTag : String := "TypeNotSupportedError"
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
  | invalidJumpDestination (detail : ErrorDetail)
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
  | .invalidJumpDestination _ => "InvalidJumpDestError"
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
  | .modexpInputLimit d | .invalidOpcode d | .invalidJumpDestination d
  | .stackDepthLimit d | .writeInStaticContext d | .outOfBoundsRead d
  | .invalidParameter d | .invalidContractPrefix d | .addressCollision d
  | .kzgProof d => d

/-- The one renderer for `ExceptionalHalt`. -/
def ExceptionalHalt.render (e : ExceptionalHalt) : String :=
  renderTagged e.tag e.detail

/-- Every exceptional-halt reason, for the completeness guards. -/
def ExceptionalHalt.all : List ExceptionalHalt :=
  [ .stackUnderflow .none, .stackOverflow .none, .outOfGas .none,
    .modexpInputLimit .none, .invalidOpcode .none, .invalidJumpDestination .none,
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
def Bytes.toRlpHash (name : String) (xs : Bytes) : Except DecodeError Hash32 :=
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
def TransactionEntry.WireWellFormed : Bytes ⊕ Transaction → Prop
  | .inl _ => True
  | .inr tx => Transaction.WireWellFormed tx ∧ tx.type.isLegacy = true

instance (e : Bytes ⊕ Transaction) : Decidable (TransactionEntry.WireWellFormed e) := by
  cases e <;> (unfold TransactionEntry.WireWellFormed; infer_instance)

/-- Structural canonicality of a decoded block: the header, every ommer
header, every withdrawal, and every transaction slot are wire-well-formed.
This is the componentwise lift of `BLT.toExBlock`; the byte-for-byte
re-encoding obligation is carried separately, by `CanonicalBlock`. -/
def Block.RlpCanonical (b : Block) : Prop :=
  b.header.WireWellFormed ∧
  (∀ o ∈ b.ommers, Header.WireWellFormed o) ∧
  (∀ w ∈ b.withdrawals, Withdrawal.WireWellFormed w) ∧
  (∀ e ∈ b.transactions, TransactionEntry.WireWellFormed e)

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
structure World : Type where
  state : State
  transientStorage : TransientStorage
  /-- Explicit storage writes; implicit storage deletion removes keys here.
  This belongs to the rollback snapshot, unlike the read sets in Meta. -/
  storageWrites : KeySet := .emptyWithCapacity

-- Precompile activation is a fork rule and lives with the rules:
-- `ForkRules.isPrecomp` in `Jaune/Fork.lean` replaces what used to be a
-- hard-wired `1 ≤ a.toNat ∧ a.toNat ≤ 17` range stated here.

def safeSub {ξ} [Sub ξ] [LE ξ] [DecidableLE ξ] (x y : ξ) : Option ξ :=
  if y ≤ x then some (x - y) else none

/-- A normalized result for a footprint-restricted core.  Both branches retain
    the core mutable state so a lift can reattach changes made before an error. -/
abbrev Footprint.Outcome (σ α : Type) : Type :=
  Except (EvmError × σ) (α × σ)

namespace Footprint

end Footprint

/-- All but one sixty-fourth (EIP-150). Defined here rather than beside the
call opcodes because `Mach.withholdCreateGas` below is its first reader. -/
def except64th (n : Nat) : Nat := n - (n / 64)

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

/-! ### The same operations, at the frame

`Devm` wrappers over the `Mach` operations above, in the shape the interpreter
calls them. Two of them are more than a lift: `restoreStateGas` also discards
the frame's refunds, because upstream's refund counter lives on the meter and
Jaune's lives on `Meta`. -/

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

lemma NextOp.push_congr {xs ys : Bytes}
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
    conv => lhs; rw [← Nat.clearLowBits_or_lowBits x.toNat 4]; rfl
    rw [← @Nat.add_eq_or 4]
    · rw [Nat.add_lt_add_iff_left]; apply Nat.lowBits_lt
    · apply Nat.two_pow_dvd_shiftLeft
    · apply Nat.lowBits_lt
  have le : (x.toNat ↿ 4) + 16 ≤ (y.toNat ↿ 4) := by
    simp only [Nat.clearLowBits]
    rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
    have rw : 16 = 2 ^ 4 := by rfl
    conv => lhs; arg 2; rw [rw]; rfl
    clear rw;
    rw [← Nat.succ_mul (x.toNat >>> 4) (2 ^ 4)]
    rw [Nat.mul_le_mul_right_iff (by omega)]
    apply Nat.succ_le_of_lt lt
  have le' : (y.toNat ↿ 4) ≤ y.toNat := Nat.clearLowBits_le _ _
  apply Nat.lt_of_lt_of_le lt' <| Nat.le_trans le le'

lemma le_of_toOpClass_eq_push (b : UInt8) (h : b.toOpClass = .push) :
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
      let le := le_of_toOpClass_eq_push b h
      let bs : Bytes := code.sliceD (pc + 1) (b.toNat - 95) 0
      let le' : bs.length ≤ 32 := by
        simp [bs, ByteArray.length_sliceD, le]
      some <| .next <| .push bs le'
  else
    some (.halt .stop)

/-- EELS `taylor_exponential`'s accumulator loop as a *well-founded* recursion
(P0.6 item 1): `fakeExpAux num den i numAcc` is the sum of the series continued
from state `(i, numAcc)`. There is no fuel and no failure branch.

Termination is by the lexicographic measure `(num + 1 - i, numAcc)`: while
`i ≤ num` the first component falls; once `i > num`, either `den * i = 0` (a
zero denominator — excluded from the semantic domain by `BlobSchedule.Valid` —
zeroes the accumulator immediately under `Nat` division) or `num < den * i`
strictly shrinks a positive accumulator. -/
def fakeExponentialLoop (num den i numAcc : Nat) : Nat :=
  if _h : numAcc = 0 then 0
  else numAcc + fakeExponentialLoop num den (i + 1) (numAcc * num / (den * i))
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

@[simp] theorem fakeExponentialLoop_zero (num den i : Nat) :
    fakeExponentialLoop num den i 0 = 0 := by
  unfold fakeExponentialLoop
  simp

/-- The EELS recurrence equation — for *every* `Nat` numerator, including the
U64 maximum; nothing here evaluates the series. -/
theorem fakeExponentialLoop_succ {numAcc : Nat} (h : numAcc ≠ 0) (num den i : Nat) :
    fakeExponentialLoop num den i numAcc
      = numAcc + fakeExponentialLoop num den (i + 1) (numAcc * num / (den * i)) := by
  conv_lhs => unfold fakeExponentialLoop
  simp [h]

/-- The EELS accumulator recurrence as a predicate on candidate functions:
`f i numAcc` plays the role of the series sum continued from `(i, numAcc)`. -/
def FakeExponentialSpec (num den : Nat) (f : Nat → Nat → Nat) : Prop :=
  (∀ i, f i 0 = 0) ∧
  ∀ i numAcc, numAcc ≠ 0 →
    f i numAcc = numAcc + f (i + 1) (numAcc * num / (den * i))

/-- `fakeExpAux` satisfies the recurrence. -/
theorem fakeExponentialLoop_spec (num den : Nat) :
    FakeExponentialSpec num den (fakeExponentialLoop num den) :=
  ⟨fakeExponentialLoop_zero num den,
   fun i numAcc h => fakeExponentialLoop_succ (numAcc := numAcc) h num den i⟩

/-- Uniqueness: the recurrence has exactly one solution, so `fakeExpAux` is
*the* EELS accumulator function. -/
theorem fakeExponentialLoop_spec_unique {num den : Nat} {f : Nat → Nat → Nat}
    (hf : FakeExponentialSpec num den f) : f = fakeExponentialLoop num den := by
  funext i numAcc
  induction i, numAcc using fakeExponentialLoop.induct num den with
  | case1 i => rw [hf.1, fakeExponentialLoop_zero]
  | case2 i numAcc h ih => rw [hf.2 i numAcc h, ih, ← fakeExponentialLoop_succ h]

/-- The pre-integrity fuelled worker as a *total* `Option`-valued reference:
`none` exactly where the old implementation exhausted its guessed fuel bound.
This is the only sanctioned old/new bridge; nothing executes it. -/
def fakeExponentialReferenceLoop? (num den i : Nat) : Nat → Nat → Option Nat
  | _, 0 => none
  | 0, _ => some 0
  | numAcc, fuel + 1 =>
    (fakeExponentialReferenceLoop? num den (i + 1) (numAcc * num / (den * i)) fuel).map
      (numAcc + ·)

/-- The accumulator sequence from `(i, numAcc)` reaches zero strictly before
the fuel runs out — the precise domain on which the old worker answered. -/
def reachesZeroBeforeFuel (num den : Nat) : Nat → Nat → Nat → Bool
  | _, _, 0 => false
  | _, 0, _ => true
  | i, numAcc, fuel + 1 =>
    reachesZeroBeforeFuel num den (i + 1) (numAcc * num / (den * i)) fuel

/-- The reference worker answers exactly on `reachesZeroBeforeFuel`. -/
theorem fakeExponentialReferenceLoop?_isSome (num den : Nat) :
    ∀ fuel i numAcc, (fakeExponentialReferenceLoop? num den i numAcc fuel).isSome
      = reachesZeroBeforeFuel num den i numAcc fuel := by
  intro fuel
  induction fuel with
  | zero => intro i numAcc; cases numAcc <;> rfl
  | succ fuel ih =>
    intro i numAcc
    cases numAcc with
    | zero => rfl
    | succ n => simp [fakeExponentialReferenceLoop?, reachesZeroBeforeFuel, ih]

/-- Wherever the old fuelled computation completed, it computed exactly the
total well-founded value. -/
theorem fakeExponentialReferenceLoop?_eq_some {num den : Nat} :
    ∀ {fuel i numAcc}, reachesZeroBeforeFuel num den i numAcc fuel = true →
      fakeExponentialReferenceLoop? num den i numAcc fuel
        = some (fakeExponentialLoop num den i numAcc) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i numAcc h
    cases numAcc <;> simp [reachesZeroBeforeFuel] at h
  | succ fuel ih =>
    intro i numAcc h
    cases numAcc with
    | zero => simp [fakeExponentialReferenceLoop?]
    | succ n =>
      rw [fakeExponentialLoop_succ (Nat.succ_ne_zero n)]
      simp only [fakeExponentialReferenceLoop?]
      rw [ih (by simpa [reachesZeroBeforeFuel] using h)]
      rfl

/-- EELS `taylor_exponential`: approximates `fac * e ^ (num / den)`. Total for
every input; the semantic domain additionally demands a positive denominator
through `BlobSchedule.Valid`. -/
def fakeExponential (fac num den : Nat) : Nat :=
  fakeExponentialLoop num den 1 (fac * den) / den

def getBaseFeePerBlobGas (blob : BlobSchedule) (excessBlobGas : Nat) : Nat :=
  fakeExponential 1 excessBlobGas blob.baseFeeUpdateFraction

/-- The public EELS `calculate_blob_gas_price` equation, through the
recurrence function rather than through evaluation (`MIN_BLOB_GASPRICE = 1`). -/
theorem calculateBlobGasPrice_eq (blob : BlobSchedule) (excess : Nat) :
    getBaseFeePerBlobGas blob excess
      = fakeExponentialLoop excess blob.baseFeeUpdateFraction 1
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
  rw [calculateBlobGasPrice_eq, fakeExponentialLoop_spec_unique hf]

/-- The U64-maximum numerator, pinned explicitly: the acceptance case the plan
forbids executing is covered by the non-evaluating theorem above. -/
theorem calculateBlobGasPrice_spec_maxU64 (blob : BlobSchedule)
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

def Prod.mapFst {α₁ : Type u₁} {α₂ : Type u₂} {β : Type v} (f : α₁ → α₂) : α₁ × β → α₂ × β :=
  Prod.map f id

def accessCost (x : Address) (a : AddressSet) : Nat :=
  if x ∈ a then Gas.warmStorageReadCost else Gas.coldAccountAccessCost

/-- The warm/cold account-access cost under a *fork's own* schedule.

A sibling rather than a third parameter on `accessCost`. EIP-8038 reprices the
cold half (2,600 to 3,000) and leaves the warm half alone, so the interpreter
has to read the number from `rules.gas` -- but `accessCost` is named 121 times
downstream, and widening its arity would move every one of those statements for
a reason that has nothing to do with what they say. Instead the schedule-carrying
form is the one the interpreter calls, `accessCost` stays exactly what it was,
and the `rfl` lemma below says they are the same function at Prague. -/
def GasSchedule.accessCost (gas : GasSchedule) (x : Address) (a : AddressSet) : Nat :=
  if x ∈ a then Gas.warmStorageReadCost else gas.coldAccountAccess

@[simp] theorem pragueGasSchedule_accessCost (x : Address) (a : AddressSet) :
    pragueGasSchedule.accessCost x a = accessCost x a := rfl

@[simp] theorem pragueRules_gas_accessCost (x : Address) (a : AddressSet) :
    pragueRules.gas.accessCost x a = accessCost x a := rfl

/-- The warm cost is the floor at every schedule, because only the cold half
moves. The Sufficiency family needs this, and needs it to hold of an arbitrary
schedule rather than of Prague's. -/
theorem GasSchedule.warmStorageReadCost_at_most_accessCost (gas : GasSchedule)
    (x : Address) (a : AddressSet) (h : Gas.warmStorageReadCost ≤ gas.coldAccountAccess) :
    Gas.warmStorageReadCost ≤ gas.accessCost x a := by
  unfold GasSchedule.accessCost
  split
  · exact Nat.le_refl _
  · exact h

/-- The account-access cost is positive under any usable schedule -- the shape
`access_cost_pos` had at Prague, now stated of the schedule the interpreter
actually reads. -/
theorem GasSchedule.Valid.accessCost_pos {g : GasSchedule} (h : g.Valid)
    (x : Address) (a : AddressSet) : 0 < g.accessCost x a := by
  unfold GasSchedule.accessCost
  have hw := h.warmAccess_le
  unfold Gas.warmStorageReadCost at *
  split <;> omega

theorem GasSchedule.Valid.warmStorageReadCost_at_most_accessCost {g : GasSchedule}
    (h : g.Valid) (x : Address) (a : AddressSet) : Gas.warmStorageReadCost ≤ g.accessCost x a :=
  g.warmStorageReadCost_at_most_accessCost x a h.warmAccess_le

-- The recorders touch `meta` and nothing else; every measure, machine field
-- and world projection sees through them, and under `bal = none` they vanish.

/-- Prague pays no selfdestruct refund and deletes only created accounts. -/
@[simp] theorem pragueRules_settle_selfdestructRefund :
    pragueRules.settlement.selfdestructRefund = 0 := rfl
@[simp] theorem pragueRules_settle_selfdestructOnlyCreated :
    pragueRules.settlement.selfdestructOnlyCreated = true := rfl

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

/-- Erasing convenience update: writing the default account removes the key. -/
def State.set (w : State) (a : Address) (ac : Account) : State :=
  w.writeAccount .eraseNil a (fun _ => ac)

/-- Store an account as present, including an explicitly empty account.
Deletion is a separate operation, `destroyAccount`. -/
def State.setPresent (w : State) (a : Address) (ac : Account) : State :=
  w.writeAccount .keep a (fun _ => ac)

/-- A balance change cannot empty an account with a nonce or code. -/
def State.Protected (w : State) (a : Address) : Prop :=
  (w.get a).nonce ≠ 0 ∨ (w.get a).code.size ≠ 0

/-- EELS `modify_state`: normalize after changing balance, nonce, or code. -/
def State.setAccount (w : State) (a : Address) (ac : Account) : State :=
  w.writeAccount .erase a (fun _ => ac)

theorem State.writeAccount_erase_eq_clear (w : State) (a : Address) (f : Account → Account) :
    w.writeAccount .erase a f = w.set a (f (w.get a)).clearIfEmpty := by
  by_cases empty : (f (w.get a)).isEmpty
  · simp [State.writeAccount, State.set, Account.clearIfEmpty, empty]
  · have nondefault : f (w.get a) ≠ .nil := by
      intro equal
      apply empty
      rw [equal]
      decide
    simp [State.writeAccount, State.set, Account.clearIfEmpty, empty, nondefault]

theorem State.writeAccount_keepIfPresent_eq (w : State) (a : Address) (f : Account → Account) :
    w.writeAccount .keepIfPresent a f =
      if AccountExists w a then w.setPresent a (f (w.get a)) else w.set a (f (w.get a)) := by
  by_cases present : AccountExists w a
  · simp [AccountExists] at present
    simp [State.writeAccount, State.setPresent, AccountExists, present]
  · simp [AccountExists] at present
    simp [State.writeAccount, State.set, AccountExists, present]

/-- Storage deletion is not a collection of SSTORE-to-zero operations. -/
def KeySet.eraseAddress (writes : KeySet) (a : Address) : KeySet :=
  writes.filter fun key => key.1 != a

/-- Forget writes at an address when the updated account is empty. -/
def KeySet.clearIfEmpty (writes : KeySet) (w : State) (a : Address) : KeySet :=
  if (w.get a).isEmpty then writes.eraseAddress a else writes

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
  ω.writeAccount .erase a (fun ac => {ac with code := cd})

def Storage.set (s : Storage) (k v : U256) : Storage :=
  if v = 0 then s.erase k else s.insert k v

def State.setStorageValue (wor : State) (adr : Address) (key val : U256) : State :=
  wor.writeAccount .keepIfPresent adr (fun ac => {ac with storage := ac.storage.set key val})

def TransientStorage.setStorageValue (tra : TransientStorage) (adr : Address) (key val : U256) : TransientStorage :=
  let stor : Storage := tra.getD adr .empty
  tra.set adr <| stor.set key val

def memorySizeAfterAccess
  (current_size access_index access_size : Nat) : Nat :=
  if access_size = 0
  then current_size
  else
    32 *
    ( max
        (ceilDiv current_size 32)
        (ceilDiv (access_index + access_size) 32) )

def memorySizeAfterAccesses : Nat → List (Nat × Nat) → Nat
  | initSize, [] => initSize
  | initSize, ⟨accessIndex, accessSize⟩ :: pairs =>
    let expSize := memorySizeAfterAccess initSize accessIndex accessSize
    memorySizeAfterAccesses expSize pairs

def ceil32 (n : Nat) : Nat :=
  match n % 32 with
  | 0 => n
  | m@(_ + 1) => n + 32 - m

def State.isDead (w : State) (a : Address) : Prop :=
  match w[a]? with
  | none => True
  | some x => x.isEmpty

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
      if _hw : wc = 16 then KECCAK.permutation ws' else ws'
  else
    KECCAK.Bytes.run wc ((List.range n).map (fun j => read (pos + j))) ws
  termination_by n
  decreasing_by omega

/-- Adapted from Blanc `CommonProofs.lean` `Array.sliceD_aux_eq` (source
attribution; never import Blanc into Jaune). -/
private theorem Array.sliceD_go_eq' {ξ : Type} (xs : Array ξ) (d : ξ) :
    ∀ (n : Nat) (Acc : List ξ) (m : Nat),
      Array.sliceD.go xs Acc m n d
        = (List.range n).map (fun j => xs.getD (m + j) d) ++ Acc := by
  intro n
  induction n with
  | zero => intro Acc m; rfl
  | succ n ih =>
    intro Acc m
    rw [show Array.sliceD.go xs Acc m (n + 1) d
          = Array.sliceD.go xs (xs.getD (m + n) d :: Acc) m n d from rfl,
      ih, List.range_succ]
    simp only [Array.getD_eq_getD_getElem?, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.cons_append, List.nil_append]

/-- Adapted from Blanc `CommonProofs.lean` `Array.sliceD_eq_map` (source
attribution; never import Blanc into Jaune). -/
private theorem Array.sliceD_eq_map' {ξ : Type} (xs : Array ξ) (m n : Nat) (d : ξ) :
    Array.sliceD xs m n d = (List.range n).map (fun j => xs.getD (m + j) d) := by
  rw [show Array.sliceD xs m n d = Array.sliceD.go xs [] m n d from rfl,
    Array.sliceD_go_eq']
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
      (if _hw : wc = 16 then KECCAK.permutation xw else xw) with hst
    set stI : Vector UInt64 25 :=
      (if wc = 16 then KECCAK.permutation xw else xw) with hstI
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
        rc + gas.sstoreClearsSchedule
      else
        rc
    let rc'' :=
      if original_value ≠ 0 ∧ current_value = 0 then
        rc' - gas.sstoreClearsSchedule
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
    rc + gas.sstoreClearsSchedule
  else rc

/-- A no-change write refunds nothing under the legacy schedule. -/
theorem sstoreLegacyRefundCounter_unchanged (gas : GasSchedule) (new_value : U256)
    (original_value : U256) (rc : Int) :
    sstoreLegacyRefundCounter gas new_value original_value new_value rc = rc := by
  unfold sstoreLegacyRefundCounter
  simp

/-- Clearing a non-zero slot to zero refunds the clear refund. -/
theorem sstoreLegacyRefundCounter_clear (gas : GasSchedule)
    (original_value current_value : U256) (rc : Int)
    (horig : original_value ≠ 0) (hcurr : current_value ≠ 0) :
    sstoreLegacyRefundCounter gas 0 original_value current_value rc =
      rc + gas.sstoreClearsSchedule := by
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
        rc + gas.sstoreClearsSchedule
      else
        rc
    let rc'' :=
      if original_value ≠ 0 ∧ current_value = 0 then
        rc' - gas.sstoreClearsSchedule
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
        rc + gas.sstoreClearsSchedule
      else
        rc
    let rc'' :=
      if original_value ≠ 0 ∧ current_value = 0 then
        rc' - gas.sstoreClearsSchedule
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
      (List.getElem?_eq_of_slice (List.slice_prefix h)) hk]
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
private lemma opStarts_eq_scanStarts (cd : ByteArray) : opStarts cd = scanStarts cd.toList 0 := by
  rw [opStarts, ByteArray.toList_eq_toList_data']

def opStartAt (cd : ByteArray) (k : Nat) : Bool :=
  (opStarts cd).getD k false

private inductive CompleteInstructions : List UInt8 → Prop
  | nil : CompleteInstructions []
  | step (b : UInt8) (ys rest : List UInt8)
      (hy : ys.length = pushWidth b) (hr : CompleteInstructions rest) :
      CompleteInstructions ((b :: ys) ++ rest)

private def ScanCover (xs : List UInt8) (k : Nat) : Prop :=
  ∃ pre b ys rest, xs = pre ++ (b :: ys) ++ rest ∧ CompleteInstructions pre ∧
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
          · exact CompleteInstructions.step b [] pre (by simp [hq]) hpre
          · simp only [List.length_cons, List.length_nil, List.length_append]
            omega
        · by_cases hsmall : j < pushWidth b
          · refine ⟨[], b, bs.take j, bs.drop j, ?_, CompleteInstructions.nil, ?_, ?_⟩
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
            · exact CompleteInstructions.step b (bs.take (pushWidth b)) pre htake hpre
            · simp only [List.length_cons, List.length_append]
              omega

private def ScanPrefix (xs : List UInt8) (rem k : Nat) : Prop :=
  ∃ ys pre rest, xs = ys ++ pre ++ rest ∧ ys.length = rem ∧
    rem ≤ k ∧ k < xs.length ∧ pre.length = k - rem ∧ CompleteInstructions pre

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

private lemma completeInstructions_cons_inversion {b : UInt8} {xs : List UInt8} (h : CompleteInstructions (b :: xs)) :
    ∃ ys rest, xs = ys ++ rest ∧ ys.length = pushWidth b ∧ CompleteInstructions rest := by
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

private lemma noPushBefore_completeInstructions {cd : ByteArray} {k : Nat}
    {pre rest : List UInt8}
    (hslice : List.Slice cd.toList k (pre ++ rest))
    (hb : noPushBefore cd k 32 = true) (hpre : CompleteInstructions pre) :
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
        | zero => simp [scanStarts, ScanPrefix, CompleteInstructions.nil]
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
            · exact CompleteInstructions.step b ys pre hys hinst
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
              rcases completeInstructions_cons_inversion hinst with ⟨ys', tail, htail, hq, hr'⟩
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
    simpa [opStartAt, opStarts_eq_scanStarts] using hstart
  have hp := (scanStarts_true_iff cd.toList.length cd.toList rfl 0 k hk').mp hs
  rcases hp with ⟨ys, pre, rest, heq, hys, hzero, hbound, hpre, hinst⟩
  have hys0 : ys = [] := by simpa using hys
  subst ys
  have hslice : List.Slice cd.toList 0 (pre ++ rest) := by
    have heq' : cd.toList = pre ++ rest := by simpa using heq
    rw [heq']
    simpa using List.slice_refl (pre ++ rest)
  have hno := noPushBefore_completeInstructions hslice (by rfl) hinst
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
        simpa [opStartAt, opStarts_eq_scanStarts] using hstart'
      have hc := scanStarts_false_cover cd.toList.length cd.toList rfl k hk' hs
      rcases hc with ⟨pre, b, ys, rest, heq, hpre, hlen, hys⟩
      have hslice : List.Slice cd.toList 0 (pre ++ ((b :: ys) ++ rest)) := by
        rw [heq]
        simpa [List.append_assoc] using List.slice_refl _
      have hpre_no := noPushBefore_completeInstructions (cd := cd) (k := 0) (pre := pre)
        (rest := (b :: ys) ++ rest) hslice (by rfl) hpre
      have hpre_no' : noPushBefore cd pre.length 32 = true := by
        simpa using hpre_no.1
      have hslice_p : List.Slice cd.toList pre.length (b :: ys ++ rest) := by
        rw [heq]
        simpa [List.append_assoc] using
          (List.append_slice_suffix (xs := pre) (ys := (b :: ys) ++ rest))
      have hget : cd.toList[pre.length]? = some b :=
        List.getElem?_eq_of_slice hslice_p
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
def legacyJumpDestinationsFrom (cd : ByteArray) (pc : Nat) : List Nat :=
  if h : pc < cd.size then
    let b := cd[pc]
    if b = 0x5B then pc :: legacyJumpDestinationsFrom cd (pc + 1)
    else if 0x60 ≤ b ∧ b ≤ 0x7F then legacyJumpDestinationsFrom cd (pc + (b.toNat - 0x5F) + 1)
    else legacyJumpDestinationsFrom cd (pc + 1)
  else []
termination_by cd.size - pc
decreasing_by all_goals omega

/-- The legacy walk steps off a byte that is neither `JUMPDEST` nor a
`PUSH1`–`PUSH32` without adding a destination. -/
theorem legacyJumpDestinationsFrom_skip (cd : ByteArray) (pc : Nat)
    (hj : cd.byteD pc ≠ 0x5B) (hp : ¬ (0x60 ≤ cd.byteD pc ∧ cd.byteD pc ≤ 0x7F)) :
    legacyJumpDestinationsFrom cd pc = legacyJumpDestinationsFrom cd (pc + 1) := by
  rw [legacyJumpDestinationsFrom]
  split
  · rename_i h
    have hb : cd[pc] = cd.byteD pc := by simp [ByteArray.byteD, h]
    simp only [hb]
    rw [ite_eq_right hj, ite_eq_right hp]
  · rename_i h
    rw [legacyJumpDestinationsFrom]
    rw [dite_eq_right (by omega)]

/-- The pinned Amsterdam `get_valid_jump_destinations` is the legacy walk:
only PUSH1–PUSH32 skip data. EELS #3618 removed the stack-access cases. -/
abbrev pinnedJumpDestinationsFrom := legacyJumpDestinationsFrom

/-- The pinned and legacy forward walks are now definitionally identical. -/
theorem pinnedJumpDestinationsFrom_eq_legacy (cd : ByteArray) (pc : Nat) :
    pinnedJumpDestinationsFrom cd pc = legacyJumpDestinationsFrom cd pc := rfl

def State.balance (w : State) (a : Address) : U256 := (w.get a).balance

def State.setBalance (st : State) (adr : Address) (val : U256) : State :=
  st.writeAccount .erase adr (fun ac => ac.withBalance val)

def State.addBalance (st : State) (adr : Address) (val : U256) : State :=
  st.setBalance adr <| (st.balance adr + val)

def State.subtractBalance (st : State) (adr : Address) (val : U256) : Option State :=
  if st.balance adr < val
  then .none
  else st.setBalance adr (st.balance adr - val)

@[simp] theorem pragueRules_settle_eraseEmptyOnModify :
    pragueRules.settlement.eraseEmptyOnModify = true := rfl

def MessageCall.gasCostAndChildGas
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

def computeContractAddress (sender : Address) (nonce : UInt64) : Address :=
  let LA : Bytes :=
    Rlp.Item.toBytes <| .list [.bytes sender.toBytes, .bytes nonce.toBytes.sig]
  (Bytes.keccak LA).toAddress

def create2NewAddress
  (sender : Address) (salt : U256) (initCode : Bytes): Address :=
  let LA : Bytes :=
    (0xFF : UInt8) :: (sender.toBytes ++ salt.toBytes ++ initCode.keccak.toBytes)
  (Bytes.keccak LA).toAddress

def State.incrementNonce (w : State) (a : Address) : State :=
  w.writeAccount .erase a (fun ac => {ac with nonce := ac.nonce + 1})

def State.setStorage (w : State) (a : Address) (s : Storage) : State :=
  w.writeAccount .keepIfPresent a (fun ac => {ac with storage := s})

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
  simp only [State.set, State.writeAccount, decide_eq_true_eq]
  split <;> simp_all [Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert]

/-- Presence-preserving insertion never identifies `some Acct.nil` with `none`. -/
theorem State.getElem?_setPresent (w : State) (a b : Address) (ac : Account) :
    (w.setPresent a ac)[b]? = if a = b then some ac else w[b]? := by
  simp only [State.setPresent, State.writeAccount, Bool.false_eq_true, ite_false, Std.TreeMap.getElem?_insert, Std.compare_eq_iff_eq]

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

theorem State.setStorageValue_get_self (w : State) (a : Address) (k v : U256) :
    (w.setStorageValue a k v).get a = {w.get a with storage := (w.get a).storage.set k v} := by
  rw [State.setStorageValue, State.writeAccount_keepIfPresent_eq]
  split
  · exact State.get_setPresent_self _ _ _
  · exact State.get_set_self _ _ _

theorem State.setStorageValue_get_ne (w : State) {a b : Address} (h : a ≠ b) (k v : U256) :
    (w.setStorageValue a k v).get b = w.get b := by
  rw [State.setStorageValue, State.writeAccount_keepIfPresent_eq]
  split
  · exact State.get_setPresent_ne _ h _
  · exact State.get_set_ne _ h _

/-- A storage write does not change membership or payload at another address. -/
theorem State.getElem?_setStorageValue_ne (w : State) {a b : Address} (h : a ≠ b) (k v : U256) :
    (w.setStorageValue a k v)[b]? = w[b]? := by
  rw [State.setStorageValue, State.writeAccount_keepIfPresent_eq]
  split
  · rw [State.getElem?_setPresent, ite_eq_right h]
  · rw [State.getElem?_set, ite_eq_right h]

theorem State.getElem?_setStorage_ne (w : State) {a b : Address} (h : a ≠ b) (stor : Storage) :
    (w.setStorage a stor)[b]? = w[b]? := by
  rw [State.setStorage, State.writeAccount_keepIfPresent_eq]
  split
  · rw [State.getElem?_setPresent, ite_eq_right h]
  · rw [State.getElem?_set, ite_eq_right h]

/-- Clearing storage never deletes an account that is already present. -/
theorem State.getElem?_setStorageValue_self_of_exists (w : State) (a : Address) (k v : U256)
    (h : AccountExists w a) :
    (w.setStorageValue a k v)[a]? = some {w.get a with storage := (w.get a).storage.set k v} := by
  rw [State.setStorageValue, State.writeAccount_keepIfPresent_eq, ite_eq_left h, State.getElem?_setPresent, ite_eq_left rfl]

theorem State.getElem?_setStorage_self_of_exists (w : State) (a : Address) (stor : Storage)
    (h : AccountExists w a) :
    (w.setStorage a stor)[a]? = some {w.get a with storage := stor} := by
  rw [State.setStorage, State.writeAccount_keepIfPresent_eq, ite_eq_left h, State.getElem?_setPresent, ite_eq_left rfl]

theorem State.setAccount_get_self (w : State) (a : Address) (ac : Account) :
    (w.setAccount a ac).get a = ac.clearIfEmpty := by
  rw [State.setAccount, State.writeAccount_erase_eq_clear]
  exact State.get_set_self w a ac.clearIfEmpty

theorem State.setAccount_get_ne (w : State) {a b : Address} (h : a ≠ b) (ac : Account) :
    (w.setAccount a ac).get b = w.get b := by
  rw [State.setAccount, State.writeAccount_erase_eq_clear]
  exact State.get_set_ne w h ac.clearIfEmpty

theorem State.Canonical.setAccount {w : State} (h : State.Canonical w) (a : Address)
    {ac : Account} (hs : Storage.Canonical ac.storage) :
    State.Canonical (w.setAccount a ac) := by
  rw [State.setAccount, State.writeAccount_erase_eq_clear]
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

theorem State.Canonical.setBalance {w : State} (h : State.Canonical w) (a : Address)
    (v : U256) : State.Canonical (w.setBalance a v) :=
  h.setAccount a (h.storage a)

theorem State.Canonical.addBalance {w : State} (h : State.Canonical w) (a : Address)
    (v : U256) : State.Canonical (w.addBalance a v) :=
  h.setBalance a _

theorem State.Canonical.subtractBalance {w w' : State} (h : State.Canonical w) {a : Address}
    {v : U256} (hw : w.subtractBalance a v = some w') : State.Canonical w' := by
  rw [State.subtractBalance] at hw
  split at hw
  · cases hw
  · cases hw; exact h.setBalance a _

theorem State.Canonical.incrementNonce {w : State} (h : State.Canonical w) (a : Address) :
    State.Canonical (w.incrementNonce a) :=
  h.setAccount a (h.storage a)

/-- `State.setStor` carries its real premise: the storage map handed in must
already be canonical. -/
theorem State.Canonical.setStorage {w : State} (h : State.Canonical w) (a : Address)
    {s : Storage} (hs : Storage.Canonical s) : State.Canonical (w.setStorage a s) := by
  rw [State.setStorage, State.writeAccount_keepIfPresent_eq]
  split
  · exact h.setPresent a hs
  · exact h.set a hs

theorem State.Canonical.setStorageValue {w : State} (h : State.Canonical w) (a : Address)
    (k v : U256) : State.Canonical (w.setStorageValue a k v) := by
  rw [State.setStorageValue, State.writeAccount_keepIfPresent_eq]
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

/-- A chain snapshot's state. Step 6's `ValidContext` adds the tip, root, and
retained-history conjuncts on top of this one. -/
def BlockChain.Canonical (ch : BlockChain) : Prop := State.Canonical ch.state

instance {w : World} : Decidable (World.Canonical w) := by
  unfold World.Canonical; infer_instance
instance {ch : BlockChain} : Decidable (BlockChain.Canonical ch) := by
  unfold BlockChain.Canonical; infer_instance

-- The record-surgery facts that hold by projection alone. These are not
-- interpreter theorems -- each is the observation that a setter touches exactly
-- the field its name says -- and they exist so Step 4 never has to unfold a
-- `Devm` to make progress.

--------------- CANONICALITY THROUGH EXECUTION (P0.4, STEP 4) ---------------

-- The state-helper half of the preservation corpus: result-carrier predicates
-- for the two execution carriers, and preservation through every named
-- machine-level mutator. The predicates are generic in the error-message
-- component -- the machine or saved state a failure carries is what must stay
-- canonical, never the text riding beside it -- which also means no
-- stringly-typed carrier is respelled here.

-- The lifted footprint combinators: everything routed through them keeps the
-- world untouched on both channels.

-- The named stack, gas, memory, and bookkeeping operations, each an instance
-- of the combinator facts above.

-- The world-changing machine mutators, each discharged by the Step-3 state
-- and transient-storage ladder.

-- The block-environment and message mutators used by frame construction,
-- delegation, and transaction processing.

-- Child incorporation and the settlement-to-execution bridge: the parent's
-- world is replaced wholesale, so only the incoming state's canonicality
-- matters. These are the exact joints through which a frame's result
-- re-enters its parent.

-- Checkpoint 2 of the corpus: through the instruction arms. First the intro
-- forms and the settle-carrier sequencing lemma, then a descent tactic for
-- the homogeneous machine-level `do`-chains.

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

-- The lifted footprint combinators and the named `Meta` recorders.

/-- Destroying any list of accounts preserves canonicality; transaction
settlement folds `destroyAccount` over the accounts-to-delete set. -/
theorem State.Canonical.foldl_destroyAccount {l : List Address} {w : State}
    (h : w.Canonical) : (l.foldl Jaune.destroyAccount w).Canonical := by
  induction l generalizing w with
  | nil => exact h
  | cons a l ih => exact ih (h.destroyAccount a)

end Jaune
