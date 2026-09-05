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

abbrev AccessList : Type := List (Adr × List B256)

abbrev State : Type := Std.TreeMap Adr Acct compare

-- class Authorization
structure Auth : Type where
  -- EIP-7702 authorization chain IDs are uint256 values.  A value other than
  -- the execution chain ID (or zero) makes only this tuple inapplicable.
  chainId : B256
  address : Adr
  nonce : UInt64
  yParity : Nat
  r : B256
  s : B256

inductive TxType : Type
  -- Legacy (including EIP-155)
  | zero
    (gasPrice : Nat)
    (receiver : Option Adr)
  -- EIP-2930
  | one
    (chainId : UInt64)
    (gasPrice : Nat)
    (receiver : Option Adr)
    (accessList : AccessList)
  -- EIP-1559
  | two
    (chainId : UInt64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Option Adr)
    (accessList : AccessList)
  -- EIP-4844
  | three
    (chainId : UInt64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Adr)
    (accessList : AccessList)
    (maxBlobFee : Nat)
    (blobHashes : List B256)
  | four
    (chainId : UInt64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Adr)
    (accessList : AccessList)
    (auths : List Auth)

structure Withdrawal : Type where
  (globalIndex : UInt64)
  (validatorIndex : UInt64)
  (recipient : Adr)
  (amount : B256)

structure Header : Type where
  parentHash : B256
  ommersHash : B256
  coinbase : Adr
  stateRoot : B256
  txsRoot : B256
  receiptRoot : B256
  bloom : Bytes
  difficulty : Nat
  number : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : Nat
  extraData : Bytes
  prevRandao : B256
  nonce : UInt64
  baseFeePerGas : Nat
  withdrawalsRoot : B256
  blobGasUsed : Nat
  excessBlobGas : Nat
  parentBeaconBlockRoot : B256
  requestsHash : Option B256
  /-- EIP-7928: the commitment to the block-level access list.

  Optional in the same sense `requestsHash` is: the field exists on the wire
  only at forks that define it, and `ForkRules.header.blockAccessListHash` is
  what says which those are. `none` is "this fork has no such field", never
  "the field is zero". -/
  blockAccessListHash : Option B256
  /-- EIP-7843: the consensus slot number this block was produced for, which
  `SLOTNUM` pushes. Optional on the same terms. -/
  slotNumber : Option UInt64

/-- The canonical RLP encoding of a header.

The three optional fields are emitted in nested order -- `requestsHash`, then
`blockAccessListHash`, then `slotNumber` -- which is the order upstream's
header dataclass declares them and the order the fixtures carry them. Nesting
rather than concatenating three independent options is deliberate: it makes
the encodable shapes exactly **20, 21 and 23** fields, so the 22-field
encoding that would result from an incoherent record cannot be produced at
all. `BLT.toExHeader` accepts exactly those three shapes and rejects 22, and
`validateHeader` is what rejects a record whose field presence disagrees with
the rules it is being validated under.

A header with the two new fields absent encodes exactly as it did before they
existed -- the inner `match` on an absent `blockAccessListHash` reduces to the
empty tail the old code wrote literally -- which is why `Header.hash` is
unchanged on every 21-field header by `rfl`. -/
def Header.toBLT (header : Header) : BLT :=
  BLT.list <| [
    BLT.bytes header.parentHash.toBytes,
    BLT.bytes header.ommersHash.toBytes,
    BLT.bytes header.coinbase.toBytes,
    BLT.bytes header.stateRoot.toBytes,
    BLT.bytes header.txsRoot.toBytes,
    BLT.bytes header.receiptRoot.toBytes,
    BLT.bytes header.bloom,
    BLT.bytes header.difficulty.toBytes,
    BLT.bytes header.number.toBytes,
    BLT.bytes header.gasLimit.toBytes,
    BLT.bytes header.gasUsed.toBytes,
    BLT.bytes header.timestamp.toBytes,
    BLT.bytes header.extraData,
    BLT.bytes header.prevRandao.toBytes,
    BLT.bytes header.nonce.toBytes,
    BLT.bytes header.baseFeePerGas.toBytes,
    BLT.bytes header.withdrawalsRoot.toBytes,
    BLT.bytes header.blobGasUsed.toBytes,
    BLT.bytes header.excessBlobGas.toBytes,
    BLT.bytes header.parentBeaconBlockRoot.toBytes
  ] ++
    match header.requestsHash with
    | none => []
    | some rh =>
      BLT.bytes rh.toBytes ::
        match header.blockAccessListHash with
        | none => []
        | some balHash =>
          BLT.bytes balHash.toBytes ::
            match header.slotNumber with
            | none => []
            -- A canonical scalar, like `number` and `gasLimit` above and
            -- unlike `nonce`: upstream's `slot_number` is a `U64` quantity, so
            -- it is encoded minimally and `toRlpB64` decodes it that way.
            | some slot => [BLT.bytes slot.toNat.toBytes]

/-- A header's identity: the keccak of its canonical RLP encoding.

This is the value a child block's `parentHash` names, the key a snapshot is
stored under, and the value `BLOCKHASH` returns. It is written out inline at
several older call sites; those keep their spelling, and this is the name the
checked chain vocabulary states its results about. -/
def Header.hash (header : Header) : B256 :=
  (Header.toBLT header).toBytes.keccak

structure Tx : Type where
  (nonce : UInt64)
  (gas : Nat)
    (value : Nat)
  (data : Bytes)
  (v : Nat)
  (r : Bytes)
  (s : Bytes)
  (type : TxType)

structure Block : Type where
  header : Header
  txs : List (Bytes ⊕ Tx)
  ommers : List Header
  wds : List Withdrawal

structure BlockChain : Type where
  blocks : List Block
  state : State
  chainId : UInt64

def TxType.receiver? : TxType → Option Adr
  | .zero _ receiver => receiver
  | .one _ _ receiver _ => receiver
  | .two _ _ _ receiver _ => receiver
  | .three _ _ _ receiver _ _ _ => some receiver
  | .four _ _ _ receiver _ _ => some receiver

def TxType.accessList : TxType → AccessList
  | .zero _ _ => []
  | .one _ _ _ al => al
  | .two _ _ _ _ al => al
  | .three _ _ _ _ al _ _ => al
  | .four _ _ _ _ al _ => al

def Tx.accessList (tx : Tx) : AccessList := tx.type.accessList

def Tx.auths (tx : Tx) : List Auth :=
  match tx.type with
  | .four _ _ _ _ _ auths => auths
  | _ => []

def Bytes.sig (bs : Bytes) : Bytes := List.dropWhile (· = 0) bs

def AccessList.toBLT (al : AccessList) : BLT :=
  let aux : Adr × List B256 → BLT
  | ⟨adr, words⟩ =>
    .list [.bytes adr.toBytes, .list (words.map (.bytes ∘ B256.toBytes))]
  .list (al.map aux)

def Auth.toBLT (auth : Auth) : BLT :=
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

def Tx.toBLT (tx : Tx) : BLT :=
  match tx.type with
  | .zero gasPrice receiver =>
    .list [
      .bytes tx.nonce.toNat.toBytes,
      .bytes gasPrice.toBytes,
      .bytes tx.gas.toBytes,
      .bytes <| receiver.rec [] Adr.toBytes,
      .bytes tx.value.toBytes,
      .bytes tx.data,
      .bytes tx.v.toBytes,
      .bytes (trimZero tx.r),
      .bytes (trimZero tx.s),
    ]
  | .one chainId gasPrice receiver accessList =>
    .list [
      .bytes chainId.toBytes.sig,
      .bytes tx.nonce.toNat.toBytes,
      .bytes gasPrice.toBytes,
      .bytes tx.gas.toBytes,
      .bytes <| receiver.rec [] Adr.toBytes,
      .bytes tx.value.toBytes,
      .bytes tx.data,
      accessList.toBLT,
      .bytes tx.v.toBytes,
      .bytes (trimZero tx.r),
      .bytes (trimZero tx.s)
    ]
  | .two chainId maxPriorityFee maxFee receiver accessList =>
    .list [
      .bytes chainId.toBytes.sig,
      .bytes tx.nonce.toNat.toBytes,
      .bytes maxPriorityFee.toBytes,
      .bytes maxFee.toBytes,
      .bytes tx.gas.toBytes,
      .bytes <| receiver.rec [] Adr.toBytes,
      .bytes tx.value.toBytes,
      .bytes tx.data,
      accessList.toBLT,
      .bytes tx.v.toBytes,
      .bytes (trimZero tx.r),
      .bytes (trimZero tx.s)
    ]
  | .three chainId maxPriorityFee maxFee receiver accessList maxBlobFee blobHashes =>
    .list [
      .bytes chainId.toBytes.sig,
      .bytes tx.nonce.toNat.toBytes,
      .bytes maxPriorityFee.toBytes,
      .bytes maxFee.toBytes,
      .bytes tx.gas.toBytes,
      .bytes receiver.toBytes,
      .bytes tx.value.toBytes,
      .bytes tx.data,
      accessList.toBLT,
      .bytes maxBlobFee.toBytes,
      .list <| blobHashes.map <| .bytes ∘ B256.toBytes,
      .bytes tx.v.toBytes,
      .bytes (trimZero tx.r),
      .bytes (trimZero tx.s)
    ]
  | .four chainId maxPriorityFee maxFee receiver accessList auths =>
    .list [
      .bytes chainId.toBytes.sig,
      .bytes tx.nonce.toNat.toBytes,
      .bytes maxPriorityFee.toBytes,
      .bytes maxFee.toBytes,
      .bytes tx.gas.toBytes,
      .bytes receiver.toBytes,
      .bytes tx.value.toBytes,
      .bytes tx.data,
      accessList.toBLT,
      .list <| auths.map <| Auth.toBLT,
      .bytes tx.v.toBytes,
      .bytes (trimZero tx.r),
      .bytes (trimZero tx.s)
    ]

def B8LOrTxToBLT : Bytes ⊕ Tx → BLT
  | .inl bs => BLT.bytes bs
  | .inr tx => tx.toBLT

def Withdrawal.toBLT (wd : Withdrawal) : BLT :=
  BLT.list [
    BLT.bytes wd.globalIndex.toBytes.sig,
    BLT.bytes wd.validatorIndex.toBytes.sig,
    BLT.bytes wd.recipient.toBytes,
    BLT.bytes wd.amount.toBytes.sig
  ]

def Block.toBLT (block : Block) : BLT :=
  let txBLTs : List BLT := block.txs.map B8LOrTxToBLT
  .list [
    Header.toBLT block.header,
    .list txBLTs,
    .list <| block.ommers.map Header.toBLT,
    .list <| block.wds.map Withdrawal.toBLT
  ]

def TxType.gasPrice (baseFee : Nat) : TxType → Nat
  | .zero gp _ => gp
  | .one _ gp _ _ => gp
  | .two _ mpf mf _ _ => min mf (baseFee + mpf)
  | .three _ mpf mf _ _ _ _ => min mf (baseFee + mpf)
  | .four _ mpf mf _ _ _ => min mf (baseFee + mpf)

def TxType.blobHashes : TxType → List B256
  | .zero _ _ => []
  | .one _ _ _ _ => []
  | .two _ _ _ _ _ => []
  | .three _ _ _ _ _ _ bhs => bhs
  | .four _ _ _ _ _ _ => []

def Tx.blobHashes (tx : Tx) : List B256 := tx.type.blobHashes

-- nibbles-to-bytes maps
abbrev NTB := Std.TreeMap (List UInt8) (List UInt8) (@List.compare _ ⟨UInt8.compareLows⟩)

def hpAux : Bytes → (Option UInt8 × Bytes)
  | [] => ⟨none, []⟩
  | n :: ns =>
    match hpAux ns with
    | ⟨none, bs⟩ => ⟨some n, bs⟩
    | ⟨some m, bs⟩ => ⟨none, ((n <<< 4) ||| m.lows) :: bs⟩

def hp (ns : Bytes) (t : Bool) : Bytes :=
  match hpAux ns with
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

def NTB.empty : NTB := Std.TreeMap.empty

def sansPrefix : Bytes → Bytes → Option Bytes
  | [], ns => some ns
  | _, [] => none
  | n :: ns, n' :: ns' =>
    if n = n' then sansPrefix ns ns' else none

def insertSansPrefix (pfx : Bytes) (m : NTB) (ns : Bytes) (bs : Bytes) : Option NTB := do
  (m.insert · bs) <$> sansPrefix pfx ns

def NTB.factor (m : NTB) : Option (Bytes × NTB) := do
  let ((n :: ns) :: nss) ← some (m.toList.map Prod.fst) | none
  let pfx ← commonPrefix n ns nss
  let m' ← Std.TreeMap.foldlM (insertSansPrefix pfx) NTB.empty m
  some ⟨pfx, m'⟩

structure NTBs : Type where
  (x0 : NTB) (x1 : NTB) (x2 : NTB) (x3 : NTB)
  (x4 : NTB) (x5 : NTB) (x6 : NTB) (x7 : NTB)
  (x8 : NTB) (x9 : NTB) (xA : NTB) (xB : NTB)
  (xC : NTB) (xD : NTB) (xE : NTB) (xF : NTB)

def NTBs.empty : NTBs :=
  ⟨ .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty,
    .empty, .empty, .empty, .empty ⟩

def NTBs.update (js : NTBs) (f : NTB → NTB) (k : UInt8) : NTBs :=
  match k.toBools with
  | ⟨_, _, _, _, 0, 0, 0, 0⟩ => { js with x0 := f js.x0}
  | ⟨_, _, _, _, 0, 0, 0, 1⟩ => { js with x1 := f js.x1}
  | ⟨_, _, _, _, 0, 0, 1, 0⟩ => { js with x2 := f js.x2}
  | ⟨_, _, _, _, 0, 0, 1, 1⟩ => { js with x3 := f js.x3}
  | ⟨_, _, _, _, 0, 1, 0, 0⟩ => { js with x4 := f js.x4}
  | ⟨_, _, _, _, 0, 1, 0, 1⟩ => { js with x5 := f js.x5}
  | ⟨_, _, _, _, 0, 1, 1, 0⟩ => { js with x6 := f js.x6}
  | ⟨_, _, _, _, 0, 1, 1, 1⟩ => { js with x7 := f js.x7}
  | ⟨_, _, _, _, 1, 0, 0, 0⟩ => { js with x8 := f js.x8}
  | ⟨_, _, _, _, 1, 0, 0, 1⟩ => { js with x9 := f js.x9}
  | ⟨_, _, _, _, 1, 0, 1, 0⟩ => { js with xA := f js.xA}
  | ⟨_, _, _, _, 1, 0, 1, 1⟩ => { js with xB := f js.xB}
  | ⟨_, _, _, _, 1, 1, 0, 0⟩ => { js with xC := f js.xC}
  | ⟨_, _, _, _, 1, 1, 0, 1⟩ => { js with xD := f js.xD}
  | ⟨_, _, _, _, 1, 1, 1, 0⟩ => { js with xE := f js.xE}
  | ⟨_, _, _, _, 1, 1, 1, 1⟩ => { js with xF := f js.xF}

def NTBs.insert (js : NTBs) : Bytes → Bytes → NTBs
  | [], _ => js
  | n :: ns, bs => js.update (Std.TreeMap.insert · ns bs) n

def Std.TreeMap.isSingleton {K V : Type} (cmp : K → K → Ordering)
    (m : Std.TreeMap K V cmp) : Bool :=
  m.size = 1

mutual

  def nodeComp : Nat → NTB → BLT
    | 0, _ => .bytes []
    | k + 1, j =>
      if j.isEmpty
      then .bytes []
      else let r := structComp k j
           if r.toBytes.length < 32
           then r
           else .bytes <| r.toBytes.keccak.toBytes

  def structComp : Nat → NTB → BLT
    | 0, _ => .bytes []
    | k + 1, j =>
      if j.isEmpty
            then .bytes []       else if j.isSingleton
           then match j.toList with
                | [(k, v)] => .list [.bytes (hp k 1), .bytes v]
                | _ => .bytes []            else match j.factor with
                | none =>
                  let js := Std.TreeMap.foldl NTBs.insert NTBs.empty j
                  .list [ nodeComp k js.x0, nodeComp k js.x1, nodeComp k js.x2,
                          nodeComp k js.x3, nodeComp k js.x4, nodeComp k js.x5,
                          nodeComp k js.x6, nodeComp k js.x7, nodeComp k js.x8,
                          nodeComp k js.x9, nodeComp k js.xA, nodeComp k js.xB,
                          nodeComp k js.xC, nodeComp k js.xD, nodeComp k js.xE,
                          nodeComp k js.xF, .bytes (j.getD [] []) ]
                | some (pfx, j') => .list [.bytes (hp pfx 0), nodeComp k j']

end

def NTB.maxKeyLength (j : NTB) : Nat :=
  (j.toList.map (List.length ∘ Prod.fst)).maxD 0

def collapse (j : NTB) : BLT := structComp (2 * (j.maxKeyLength + 1)) j

def trie (j : NTB) : B256 :=
  Bytes.keccak <| (collapse j).toBytes

def B256.toBLT (w : B256) : BLT := .bytes w.toBytes

def Stor.toNTB (s : Stor) : NTB :=
  let f : NTB → B256 → B256 → NTB :=
    λ j k v =>
      j.insert
        k.keccak.toNibbles
        ((BLT.toBytes <| .bytes <| Bytes.sig <| v.toBytes))
  Std.TreeMap.foldl f NTB.empty s

def B256.zerocount (x : B256) : Nat → Nat
  | 0 => 0
  | k + 1 => if x = 0 then k + 1 else B256.zerocount (x >>> 8) k

def B256.bytecount (x : B256) : Nat := 32 - (B256.zerocount x 32)

/-- Leading zero bits of one 64-bit limb; 64 for zero. -/
def UInt64.leadingZeros (x : UInt64) : Nat :=
  if x = 0 then 64 else 63 - Nat.log2 x.toNat

/-- Leading zero bits of a 256-bit word; 256 for zero.

This is EIP-7939's `256 - x.bit_length()` stated directly, and it is computed
limb by limb so that a word is never widened to a bignum to be measured. -/
def B256.leadingZeros (x : B256) : Nat :=
  if x.1.1 ≠ 0 then UInt64.leadingZeros x.1.1
  else if x.1.2 ≠ 0 then 64 + UInt64.leadingZeros x.1.2
  else if x.2.1 ≠ 0 then 128 + UInt64.leadingZeros x.2.1
  else 192 + UInt64.leadingZeros x.2.2

def accountToKeyVal (pr : Adr × Acct) : Bytes × Bytes :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨
    ad.toBytes.keccak.toNibbles,
    let val' :=
      BLT.toBytes <| .list [
        .bytes (ac.nonce.toBytes.sig),
        .bytes (ac.bal.toBytes.sig),
        B256.toBLT (trie ac.stor.toNTB),
        B256.toBLT <| (Bytes.keccak ac.code.toList)
      ]
    val'
  ⟩

-- values --

def gHigh : Nat := 10
def gJumpdest : Nat := 1
def txCreateCost : Nat := 32000
def gasInitCodeWordCost : Nat := 2
def gBase : Nat := 2
def gasCopy : Nat := 3
def gReturnDataCopy : Nat := 3
def gMemory : Nat := 3
def gKeccak256 : Nat := 30
def gasKeccak256Word : Nat := 6
def gVerylow : Nat := 3
def gLow : Nat := 5
def gMid : Nat := 8
def gExp : Nat := 10
def gExpbyte : Nat := 50
def gasColdSload : Nat := 2100
def gasStorageSet : Nat := 20000
def rSClear : Nat := 4800
def gBlockhash : Nat := 20
def gasCodeDeposit : Nat := 200
def gasCreate : Nat := 32000
def gHashopcode : Nat := 3
def gasPerBlob : Nat := 2 ^ 17
def gasStorageUpdate := 5000
def gasEcrecover : Nat := 3000
def gasP256Verify : Nat := 6900
-- `maxCodeSize` and `maxInitCodeSize` are fork rules, not global constants:
-- see `ForkRules.code` in `Jaune/Fork.lean`.
def gNewAccount : Nat := 25000
def gasSelfDestructNewAccount : Nat := 25000
def gasCallValue : Nat := 9000
def gCallStipend : Nat := 2300
def gasWarmAccess : Nat := 100
def gasColdAccountAccess : Nat := 2600
def gasSelfDestruct : Nat := 5000
def gLog : Nat := 375
def gLogdata : Nat := 8
def gLogtopic : Nat := 375
def depositContractAddress : Adr :=
  0x00000000219ab540356cbb839cbe05303d7705fa
def depositEventSignatureHash : B256 :=
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
def txAccessListAddressCost : Nat := 2400
def txAccessListStorageKeyCost : Nat := 1900
def floorCalldataCost : Nat := 10
def standardCallDataTokenCost : Nat := 4
def depositRequestType : Bytes := [0]
def withdrawalRequestType : Bytes := [1]
def consolidationRequestType : Bytes := [2]
def withdrawalRequestPredeployAddress : Adr := 0x00000961Ef480Eb55e80D19ad83579A64c007002
def consolidationRequestPredeployAddress : Adr := 0x0000BBdDc7CE488642fb579F8B00f3a590007251
def historyStorageAddress : Adr := 0x0000F90827F1C53a10cb7A02335B175320002935
def emptyOmmerHash : B256 := (BLT.list []).toBytes.keccak
def setCodeTxMagic : Bytes := [0x05]
def beaconRootsAddress : Adr := 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
def systemAddress : Adr := 0xfffffffffffffffffffffffffffffffffffffffe
def systemTransactionGas : Nat := 30000000
def versionedHashVersionKzg : UInt8 := 0x01
def eoaDelegationMarker : Bytes := [0xEF, 0x01, 0x00]
def gasBlake2PerRound : Nat := 1
def eoaDelegatedCodeLength : Nat := 23
-- The blob target, ceiling, and base-fee update fraction are fork rules, not
-- global constants: see `ForkRules.blob` in `Jaune/Fork.lean`.
def elasticityMultiplier : Nat := 2
def gasLimitAdjustmentFactor : Nat := 1024
def gasLimitMinimum : Nat := 5000
def baseFeeMaxChangeDenominator := 8
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
theorem gasPerBlob_pos : 0 < gasPerBlob := by decide

def perEmptyAccountCost := 25000
def perAuthBaseCost := 12500
def txBaseCost : Nat := 21000

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
    pragueRules.gas.coldAccountAccess = gasColdAccountAccess := rfl
@[simp] theorem pragueRules_gas_callValue :
    pragueRules.gas.callValue = gasCallValue := rfl
@[simp] theorem pragueRules_gas_createAccess :
    pragueRules.gas.createAccess = gasCreate := rfl
@[simp] theorem pragueRules_gas_storageClearRefund :
    pragueRules.gas.storageClearRefund = rSClear := rfl
@[simp] theorem pragueRules_gas_txBase :
    pragueRules.gas.txBase = txBaseCost := rfl
@[simp] theorem pragueRules_gas_txAccessListAddress :
    pragueRules.gas.txAccessListAddress = txAccessListAddressCost := rfl
@[simp] theorem pragueRules_gas_txAccessListStorageKey :
    pragueRules.gas.txAccessListStorageKey = txAccessListStorageKeyCost := rfl
@[simp] theorem pragueRules_gas_floorTokenCost :
    pragueRules.gas.floorTokenCost = floorCalldataCost := rfl
@[simp] theorem pragueRules_gas_perAuthIntrinsic :
    pragueRules.gas.perAuthIntrinsic = perEmptyAccountCost := rfl
/-- The tenth field is additive with identity `0`, so the Prague formula is
literally unchanged rather than merely equal to what it was. -/
@[simp] theorem pragueRules_gas_codeReadSurcharge :
    pragueRules.gas.codeReadSurcharge = 0 := rfl

/-- `createAccess` is one number at Prague for both of its two readers: the
`CREATE`/`CREATE2` opcode base and the creation transaction's recipient cost.
Stated so that the single field is justified rather than assumed -- EIP-8037
moves both together, and if upstream ever separated them this would fail. -/
@[simp] theorem txCreateCost_eq_gasCreate : txCreateCost = gasCreate := rfl

/-- The request contracts the rule data names are the ones this module has
always called, in the same order. -/
@[simp] theorem pragueRules_requests :
    pragueRules.requests =
      [(1, withdrawalRequestPredeployAddress),
       (2, consolidationRequestPredeployAddress)] := rfl

/-- Prague carries neither Amsterdam header field. -/
@[simp] theorem pragueRules_header :
    pragueRules.header = { blockAccessListHash := false, slotNumber := false } :=
  rfl

/-- Prague meters in one dimension.

This is the bridge every `stateGas = none` branch reduces through. The
interpreter's Amsterdam branches are `match`es on `rules.stateGas`, so a
Prague-stated goal that reaches one rewrites to `none` here and then to the
existing single-dimension code path by `match` reduction -- which is what makes
"the `none` path is textually today's path" a fact a proof can use rather than
a claim about the source. -/
@[simp] theorem pragueRules_stateGas : pragueRules.stateGas = none := rfl

/-- The two literals `GasSchedule.Valid` spells out are the globals it means.

`Jaune/Fork.lean` is upstream of this module and cannot name `gasWarmAccess` or
`gCallStipend`, so the predicate writes `100` and `2300`. This is the `rfl`
proof that those are not third copies of the numbers but the same two, which is
what lets a Sufficiency obligation stated in terms of the globals be discharged
from a `Valid` hypothesis. -/
theorem gasSchedule_valid_iff (g : GasSchedule) :
    g.Valid ↔ gasWarmAccess ≤ g.coldAccountAccess ∧ 0 < g.createAccess
      ∧ gCallStipend ≤ g.callValue := Iff.rfl

theorem GasSchedule.Valid.warmAccess_le {g : GasSchedule} (h : g.Valid) :
    gasWarmAccess ≤ g.coldAccountAccess := h.1

theorem GasSchedule.Valid.createAccess_pos {g : GasSchedule} (h : g.Valid) :
    0 < g.createAccess := h.2.1

theorem GasSchedule.Valid.stipend_le_callValue {g : GasSchedule} (h : g.Valid) :
    gCallStipend ≤ g.callValue := h.2.2

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

def initCodeCost (len : Nat) : Nat :=
  gasInitCodeWordCost * (ceilDiv len 32)

instance : Hashable Adr := ⟨fun x => x.2.2⟩
-- The storage-slot hash must depend on the key, not only the address: mix the
-- address hash with all four 64-bit limbs of the B256 key (finding 3.9). A
-- key-insensitive hash sent every same-address slot into one bucket.
instance : Hashable (Adr × B256) :=
  ⟨λ x =>
    let k := x.2
    mixHash (hash x.1) (mixHash k.1.1 (mixHash k.1.2 (mixHash k.2.1 k.2.2)))⟩

abbrev AdrSet : Type := @Std.HashSet Adr _ _
abbrev KeySet : Type := @Std.HashSet (Adr × B256) _ _

-- Regression for the key-sensitive hash above. These four keys share one
-- address but each sets a different 64-bit limb, so the old address-only hash
-- collided them into a single bucket.
private def keyHashRegressionKeys : List (Adr × B256) :=
  let a : Adr := (0x1234 : Adr)
  [ (a, Nat.toB256 1),
    (a, Nat.toB256 (2 ^ 64)),
    (a, Nat.toB256 (2 ^ 128)),
    (a, Nat.toB256 (2 ^ 192)) ]

-- distinct keys at one address must not all hash to the same value
#guard (keyHashRegressionKeys.map (fun p => hash p)).eraseDups.length = 4

-- a KeySet built from many same-address keys must still find each key
#guard
  let s : KeySet := .ofList keyHashRegressionKeys
  s.size = 4 && keyHashRegressionKeys.all s.contains

abbrev Tra : Type := Std.TreeMap Adr Stor compare

def calculateMemoryGasCost (memSize : Nat) : Nat :=
  let memWordSize := ceilDiv memSize 32
  let linearCost := gMemory * memWordSize
  let quadraticCost := (memWordSize ^ 2) / 512
  linearCost + quadraticCost

structure Mem : Type where
  data : Array UInt8
  size : Nat

def Mem.empty : Mem := ⟨.empty, 0⟩

structure Log : Type where
  (address : Adr)
  (topics : List B256)
  (data : Bytes)

structure BenvStat : Type where
  /-- The rules this block runs under.
  Carrying them here, rather than as an extra argument, is what keeps a single
  interpreter: every function that already sees a `BenvStat` -- directly, or
  through `Benv`, `Msg`, or `Sevm` -- can read the active rules without a
  signature change, and nothing anywhere needs to know which fork it is. -/
  rules : ForkRules
  chainId : UInt64
  origState : State
  blockGasLimit : Nat
  blockHashes: List B256
  coinbase : Adr
  number : Nat
  baseFeePerGas : Nat
  time : B256
  prevRandao : B256
  excessBlobGas : Nat
  parentBeaconBlockRoot : B256
  /-- EIP-7843: the consensus slot number the header carries, which `SLOTNUM`
  pushes. Defaulted so that every existing `BenvStat` literal keeps
  elaborating; under rules without `op.slotnum` nothing reads it. -/
  slotNumber : UInt64 := 0

-- class Benvironment
structure Benv : Type where
  state : State
  createdAccounts : AdrSet
  stat : BenvStat

structure TenvStat : Type where
  origin: Adr
  gasPrice: Nat
  gas: Nat
  /-- Amsterdam's state-gas reservoir beside the execution grant `gas`.
  Legacy transaction environments keep the default zero. -/
  stateGasReservoir : Nat := 0
  accessListAddresses: AdrSet
  accessListStorageKeys: KeySet
  blobVersionedHashes: List B256
  auths : List Auth
  indexInBlock : Option Nat
  txHash: Option B256

-- class TransactionEnvironment
structure Tenv : Type where
  transientStorage: Tra
  stat : TenvStat

-- class Message
structure Msg : Type where
  benv: Benv
  tenv: Tenv
  caller: Adr
  target: Option Adr
  currentTarget: Adr
  gas: Nat
  value: B256
  data: Bytes
  codeAddress: Option Adr
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

def Msg.withBenv (msg : Msg) (benv : Benv) : Msg :=
  {msg with benv := benv}

def Benv.withState (benv : Benv) (st : State) : Benv :=
  {benv with state := st}

-- `origState` is the original state of a *transaction*, not of a block: it is
-- what `SSTORE` compares against to tell a clean update from a dirty one
-- (finding 3.8). Every normal and system transaction must open with this so
-- that its own input state, rather than the block prestate, is the original
-- state. Everything else about the environment is preserved.
def Benv.beginTransaction (benv : Benv) : Benv :=
  {benv with stat := {benv.stat with origState := benv.state}}

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
def emptyAuthorizationListTag : String := "EmptyAuthorizationListError"

def transactionExceptionTags : List String :=
  [ gasPriceProductOverflowTag, gasAllowanceExceededTag,
    initcodeSizeExceededTag, insufficientAccountFundsTag,
    insufficientMaxFeePerGasTag, insufficientMaxFeePerBlobGasTag,
    transactionGasLimitExceededTag,
    intrinsicGasTooLowTag, invalidChainIdTag, nonceIsMaxTag, nonceMismatchTooHighTag,
    nonceMismatchTooLowTag,
    priorityGreaterThanMaxFeeTag, senderNotEoaTag,
    type3BlobCountExceededTag, type3BlobCountLimitExceededTag,
    type3ContractCreationTag,
    type3InvalidBlobVersionedHashTag, type3ZeroBlobsTag,
    type4ContractCreationTag, emptyAuthorizationListTag ]

#guard transactionExceptionTags.length = 21
#guard transactionExceptionTags.eraseDups.length = 21
#guard transactionExceptionTags.all fun t =>
  (transactionExceptionTags.filter fun u => t.isPrefixOf u).length = 1

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

/-- Every block-rejection tag. The single source of truth for the distinctness
checks and the whole-list constructor/tag pin. -/
def blockExceptionTags : List String :=
  [ gasLimitTooBigTag, gasLimitAdjustmentTag, gasUsedOverflowTag,
    gasUsedMismatchTag, timestampOlderThanParentTag, blockNumberTag,
    baseFeePerGasTag, difficultyOverParisTag, ommersOverParisTag,
    extraDataTooBigTag, unknownParentTag, unknownParentZeroTag,
    stateRootTag, transactionsRootTag, receiptsRootTag, logBloomTag,
    withdrawalsRootTag, headerNonceTag, excessBlobGasTag, blobGasUsedTag,
    requestsHashTag, depositEventLayoutTag, systemContractCallFailedTag,
    systemContractEmptyTag,
    blockRlpSizeExceededTag, headerFieldPresenceTag, blockAccessListHashTag,
    blockAccessListContentTag, blockAccessListFormatTag,
    blockAccessListGasLimitTag ]

-- The tags are distinct, and none is a prefix of another, so no rendered
-- reason can be read as another by any " : "-delimited reader -- and none is
-- the broad category the vocabulary replaced.
#guard blockExceptionTags.length = 30
#guard blockExceptionTags.eraseDups.length = 30
#guard blockExceptionTags.all fun t =>
  (blockExceptionTags.filter fun u => t.isPrefixOf u).length = 1
#guard blockExceptionTags.all fun t => t ≠ "InvalidBlock"

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

--------------- TYPED SEMANTIC REASONS: CODEC AND VM ---------------

-- Declarations, renderers, and golden guards only; no producer is migrated
-- here and no rendered message changes. Steps 9 and 10 move the producers.
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

/-- The diagnostic payload of a decode reason. -/
def DecodeError.detail : DecodeError → ErrorDetail
  | .rlpStructure d | .fixedWidth d | .fieldOverflow64 d
  | .fieldOverflow256 d | .leadingZeros d | .withdrawalsNotRead d
  | .roundTrip d => d

/-- The one renderer for `DecodeError`. -/
def DecodeError.render (e : DecodeError) : String :=
  renderTagged e.tag e.detail

/-- Every decode reason, for the completeness guards. -/
def DecodeError.all : List DecodeError :=
  [ .rlpStructure .none, .fixedWidth .none, .fieldOverflow64 .none,
    .fieldOverflow256 .none, .leadingZeros .none,
    .withdrawalsNotRead .none, .roundTrip .none ]

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

-- Golden guards, one representative per renderer constructor. Each pins the
-- exact rendered bytes of a message this executable emits today.
#guard DecodeError.all.map DecodeError.tag
  = [ "RlpStructureError", "RlpFixedWidthError", "RlpFieldOverflow64Error",
      "RlpFieldOverflow256Error", "RlpLeadingZerosError",
      "RlpWithdrawalsNotReadError", "RlpRoundTripError" ]
#guard DecodeError.all.length = 7
#guard DecodeError.render (.rlpStructure (.text "withdrawals : expected a list"))
  = "RlpStructureError : withdrawals : expected a list"
#guard DecodeError.render (.fixedWidth (.text "root must be exactly 32 bytes, but is 31"))
  = "RlpFixedWidthError : root must be exactly 32 bytes, but is 31"
#guard DecodeError.render (.fieldOverflow64 .none) = "RlpFieldOverflow64Error"
#guard DecodeError.render (.fieldOverflow256 .none) = "RlpFieldOverflow256Error"
#guard DecodeError.render (.leadingZeros .none) = "RlpLeadingZerosError"
#guard DecodeError.render (.withdrawalsNotRead .none) = "RlpWithdrawalsNotReadError"
#guard DecodeError.render (.roundTrip .none) = "RlpRoundTripError"

#guard ExceptionalHalt.all.map ExceptionalHalt.tag
  = [ "StackUnderflowError", "StackOverflowError", "OutOfGasError",
      "ModexpInputLimitExceeded", "InvalidOpcode", "InvalidJumpDestError",
      "StackDepthLimitError", "WriteInStaticContext", "OutOfBoundsRead",
      "InvalidParameter", "InvalidContractPrefix", "AddressCollision",
      "KZGProofError" ]
#guard ExceptionalHalt.all.length = 13
#guard ExceptionalHalt.all.eraseDups.length = 13
#guard ExceptionalHalt.render (.outOfGas .none) = "OutOfGasError"
#guard ExceptionalHalt.render (.invalidParameter (.text "invalid field element"))
  = "InvalidParameter : invalid field element"
#guard ExceptionalHalt.render (.writeInStaticContext (.text "SSTORE"))
  = "WriteInStaticContext : SSTORE"

#guard CryptoError.render (.invalidSignature .none) = "InvalidSignatureError"
#guard CryptoError.render (.invalidSignature (.text "bad s"))
  = "InvalidSignatureError : bad s"
#guard CryptoError.render (.pointCompression .none) = "bCompress failed"
#guard CryptoError.render (.value .none) = "ValueError"

#guard InternalError.render (.assertion .none) = "AssertionError"
#guard InternalError.render (.invariant (.text "refund counter is negative"))
  = "ERROR : refund counter is negative"
#guard InternalError.render (.invariant (.text "block hashes is empty"))
  = "ERROR : block hashes is empty"

#guard EvmError.render .revert = "Revert"
#guard EvmError.render (.halt (.stackUnderflow .none)) = "StackUnderflowError"
#guard EvmError.render (.crypto (.value .none)) = "ValueError"
#guard EvmError.render (.internal (.assertion .none)) = "AssertionError"

#guard SettledHalt.render .revert = "Revert"
#guard SettledHalt.render (.halt (.outOfGas .none)) = "OutOfGasError"
#guard SettledHalt.render (.halt (.invalidJumpDest .none)) = "InvalidJumpDestError"
#guard SettledHalt.render (.halt (.addressCollision .none)) = "AddressCollision"

-- The seven decode tags the typed reasons render under are exactly the seven
-- the strict decoders emit today, in the order the vocabulary declares them.
#guard DecodeError.all.map DecodeError.tag
  = [ rlpStructureTag, rlpFixedWidthTag, rlpFieldOverflow64Tag,
      rlpFieldOverflow256Tag, rlpLeadingZerosTag, rlpWithdrawalsNotReadTag,
      rlpRoundTripTag ]


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
def Bytes.toRlpHash (name : String) (xs : Bytes) : Except DecodeError B256 :=
  xs.toB256?.toExcept
    (.fixedWidth (.text s!"{name} must be exactly 32 bytes, but is {xs.length}"))

/-- A fixed-width 8-byte field, as a `UInt64`. Like `toRlpHash`, this is bytes
rather than a scalar: the header nonce is eight bytes of zeroes, not empty. -/
def Bytes.toRlpFixedB64 (name : String) (xs : Bytes) : Except DecodeError UInt64 :=
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
def Bytes.toRlpB64 (name : String) (xs : Bytes) : Except DecodeError UInt64 := do
  let xs ← rlpScalarBytes .fieldOverflow64 name 8 xs
  .ok xs.toUInt64

/-- A canonical 256-bit scalar: at most thirty-two bytes, converted without
truncation. -/
def Bytes.toRlpB256 (name : String) (xs : Bytes) : Except DecodeError B256 := do
  let xs ← rlpScalarBytes .fieldOverflow256 name 32 xs
  .ok xs.toB256

/-- An address field: exactly twenty bytes. -/
def Bytes.toRlpAdr (name : String) (xs : Bytes) : Except DecodeError Adr :=
  xs.toAdr?.toExcept
    (.fixedWidth (.text s!"{name} must be exactly 20 bytes, but is {xs.length}"))

/-- An optional contract-creation receiver: empty, or exactly twenty bytes. -/
def Bytes.toRlpReceiver (name : String) (xs : Bytes) :
    Except DecodeError (Option Adr) :=
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
theorem Bytes.toRlpB256_eq_ok {name : String} {xs : Bytes} {v : B256}
    (h : xs.toRlpB256 name = .ok v) : Bytes.CanonicalScalar 32 xs := by
  unfold Bytes.toRlpB256 at h
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
  h.bloom.length = 256 ∧
  h.difficulty < 2 ^ 256 ∧
  h.number < 2 ^ 256 ∧
  h.gasLimit < 2 ^ 256 ∧
  h.gasUsed < 2 ^ 256 ∧
  h.timestamp < 2 ^ 256 ∧
  h.baseFeePerGas < 2 ^ 256 ∧
  h.blobGasUsed < 2 ^ 64 ∧
  h.excessBlobGas < 2 ^ 64

instance (h : Header) : Decidable (Header.WireWellFormed h) := by
  unfold Header.WireWellFormed; infer_instance

/-- EIP-7702 authorisation tuples arrive inside type-4 transactions, so their
fields are untrusted in exactly the way a transaction's are. `yParity` is the
only one `BLT.toExAuth` reads as an unbounded scalar. -/
def Auth.WireWellFormed (a : Auth) : Prop := a.yParity < 2 ^ 256

instance (a : Auth) : Decidable (Auth.WireWellFormed a) := by
  unfold Auth.WireWellFormed; infer_instance

/-- The per-type half of transaction well-formedness: the fee scalars each
envelope carries, and the recursive obligation on type-4 authorisations.
Access-list and blob-hash material is already width-exact by type. -/
def TxType.WireWellFormed : TxType → Prop
  | .zero gasPrice _ => gasPrice < 2 ^ 256
  | .one _ gasPrice _ _ => gasPrice < 2 ^ 256
  | .two _ maxPriorityFee maxFee _ _ =>
    maxPriorityFee < 2 ^ 256 ∧ maxFee < 2 ^ 256
  | .three _ maxPriorityFee maxFee _ _ maxBlobFee _ =>
    maxPriorityFee < 2 ^ 256 ∧ maxFee < 2 ^ 256 ∧ maxBlobFee < 2 ^ 256
  | .four _ maxPriorityFee maxFee _ _ auths =>
    maxPriorityFee < 2 ^ 256 ∧ maxFee < 2 ^ 256 ∧
      ∀ a ∈ auths, Auth.WireWellFormed a

instance (t : TxType) : Decidable (TxType.WireWellFormed t) := by
  cases t <;> (unfold TxType.WireWellFormed; infer_instance)

/-- Whether a transaction is a legacy (untyped) one. A typed transaction's
canonical block encoding is its envelope byte followed by its payload, never
the legacy list, so this is the discriminator the checked ingress needs. -/
def TxType.isLegacy : TxType → Bool
  | .zero _ _ => true
  | _ => false

/-- Wire well-formedness of a transaction: the `U256` scalars every envelope
shares, canonical signature scalar bytes, and the per-type obligations.
`nonce` is already a `UInt64` and `data` is unconstrained on the wire. -/
def Tx.WireWellFormed (tx : Tx) : Prop :=
  tx.gas < 2 ^ 256 ∧
  tx.value < 2 ^ 256 ∧
  tx.v < 2 ^ 256 ∧
  Bytes.CanonicalScalar 32 tx.r ∧
  Bytes.CanonicalScalar 32 tx.s ∧
  tx.type.WireWellFormed

instance (tx : Tx) : Decidable (Tx.WireWellFormed tx) := by
  unfold Tx.WireWellFormed; infer_instance

/-- EIP-4895's withdrawal amount is a 64-bit Gwei scalar on the wire even
though `Withdrawal.amount` stores 256 bits for balance arithmetic, so a
decoded withdrawal always has its upper 192 bits clear. Design report §7 names
this as the one place a semantic field is wider than its wire type. -/
def Withdrawal.WireWellFormed (w : Withdrawal) : Prop :=
  w.amount.1 = ((0, 0) : B128) ∧ w.amount.2.1 = (0 : UInt64)

instance (w : Withdrawal) : Decidable (Withdrawal.WireWellFormed w) := by
  unfold Withdrawal.WireWellFormed; infer_instance

/-- Widening a `UInt64` to a `B256` leaves the upper 192 bits clear. This is
what makes `Withdrawal.WireWellFormed` a genuine lift of
`BLT.toExWithdrawal`, which reads the amount with the 64-bit scalar
decoder and then widens it. -/
theorem UInt64.toNat_toB256_high (x : UInt64) :
    (x.toNat.toB256).1 = ((0, 0) : B128) ∧ (x.toNat.toB256).2.1 = (0 : UInt64) := by
  have hx : x.toNat < 2 ^ 64 := x.toNat_lt
  have h128 : x.toNat >>> 128 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt
      (Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by norm_num) (by norm_num)))
  have h64 : x.toNat >>> 64 = 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.div_eq_of_lt hx
  constructor
  · simp [Nat.toB256, h128, Nat.toB128]
  · simp [Nat.toB256, Nat.toB128, h64]

/-- A transaction slot inside a block body. `BLT.toExBlock` turns a list
item into a decoded legacy transaction and a byte-string item into opaque
typed-envelope bytes, so the two sides carry genuinely different obligations:
the decoded side must be a well-formed legacy transaction, while typed bytes
stay opaque until the existing decode point inside `applyBody`. Eagerly
decoding them here would change which error wins (fixed decision 5). -/
def TxEntry.WireWellFormed : Bytes ⊕ Tx → Prop
  | .inl _ => True
  | .inr tx => Tx.WireWellFormed tx ∧ tx.type.isLegacy = true

instance (e : Bytes ⊕ Tx) : Decidable (TxEntry.WireWellFormed e) := by
  cases e <;> (unfold TxEntry.WireWellFormed; infer_instance)

/-- Structural canonicality of a decoded block: the header, every ommer
header, every withdrawal, and every transaction slot are wire-well-formed.
This is the componentwise lift of `BLT.toExBlock`; the byte-for-byte
re-encoding obligation is carried separately, by `CanonicalBlock`. -/
def Block.RlpCanonical (b : Block) : Prop :=
  b.header.WireWellFormed ∧
  (∀ o ∈ b.ommers, Header.WireWellFormed o) ∧
  (∀ w ∈ b.wds, Withdrawal.WireWellFormed w) ∧
  (∀ e ∈ b.txs, TxEntry.WireWellFormed e)

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
  stack : List B256
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

@[ext]
structure World : Type where
  state : State
  transientStorage : Tra

@[ext]
structure Devm : Type where
  mach : Mach
  «meta» : Meta
  world : World

def Devm.stack (devm : Devm) : List B256 := devm.mach.stack
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
def Devm.transientStorage (devm : Devm) : Tra := devm.world.transientStorage

def Devm.setMach (devm : Devm) (mach : Mach) : Devm :=
  { devm with mach := mach }

def Devm.setMeta (devm : Devm) (view : Meta) : Devm :=
  { devm with «meta» := view }

def Devm.setWorld (devm : Devm) (world : World) : Devm :=
  { devm with world := world }

structure Sevm : Type where
  caller : Adr
  target : Option Adr
  currentTarget : Adr
  gas : Nat
  value : B256
  data : Bytes
  codeAddress : Option Adr
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

def Devm.withStack (devm : Devm) (stack : List B256) : Devm :=
  devm.setMach {devm.mach with stack := stack}

def Devm.withMemory (devm : Devm) (memory : Mem) : Devm :=
  devm.setMach {devm.mach with memory := memory}

def Devm.withGasLeft (devm : Devm) (gasLeft : Nat) : Devm :=
  devm.setMach {devm.mach with gasLeft := gasLeft}

def Devm.withLogs (devm : Devm) (logs : List Log) : Devm :=
  devm.setMeta {devm.meta with logs := logs}

def Devm.withRefundCounter (devm : Devm) (refundCounter : Int) : Devm :=
  devm.setMeta {devm.meta with refundCounter := refundCounter}

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

def Devm.withTransientStorage (devm : Devm) (transientStorage : Tra) : Devm :=
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

/-- A fuel-bounded computation.  The outer `Option` records whether the
computation exhausted its recursion fuel; the inner `Except` is the ordinary
semantic result. -/
abbrev Fueled (ε α : Type) : Type := ExceptT ε Option α

namespace Fueled

/-- The distinguished result for recursion-fuel exhaustion. -/
def exhausted : Fueled ε α := ExceptT.mk none

/-- Lift an ordinary semantic result into a completed fueled computation. -/
def ofExcept (x : Except ε α) : Fueled ε α := liftM x

/-- A completed successful computation. -/
def ok (x : α) : Fueled ε α := pure x

/-- A completed computation that produced an ordinary semantic error. -/
def error (e : ε) : Fueled ε α := throw e

/-- The fueled analogue of `Except.assert`; failure is a semantic error, not
fuel exhaustion. -/
def assert (p : Prop) [Decidable p] (e : ε) : Fueled ε Unit :=
  if p then pure () else throw e

/-- Apply a transformation to a completed semantic result while propagating
fuel exhaustion unchanged.  This is used where the old interpreter converted
between its two semantic error-state types. -/
def mapResult (f : Except ε α → Except ζ β) (x : Fueled ε α) : Fueled ζ β :=
  ExceptT.mk <| x.run.map f

/-- Reconstitute the legacy `Except` API at a public boundary. -/
def toExcept (onExhausted : ε) (x : Fueled ε α) : Except ε α :=
  match x.run with
  | none => .error onExhausted
  | some result => result

@[simp] lemma exhausted_run : (exhausted : Fueled ε α).run = none := rfl

@[simp] lemma ofExcept_run (x : Except ε α) : (ofExcept x).run = some x := rfl

@[simp] lemma ok_run (x : α) : (ok x : Fueled ε α).run = some (.ok x) := rfl

@[simp] lemma error_run (e : ε) :
    (error e : Fueled ε α).run = some (.error e) := rfl

@[simp] lemma mapResult_run (f : Except ε α → Except ζ β) (x : Fueled ε α) :
    (mapResult f x).run = x.run.map f := rfl

@[simp] lemma toExcept_exhausted (e : ε) :
    toExcept e (exhausted : Fueled ε α) = .error e := rfl

@[simp] lemma toExcept_ofExcept (e : ε) (x : Except ε α) :
    toExcept e (ofExcept x) = x := rfl

end Fueled

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

/-- `repay_state_gas_spill`, new at the pinned revision (`7341820`, #3478).

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
`Xinst.step` then only have to say which operations they perform.

`Jaune.DualGasProbe` proved these same five shapes on a bounded model before any
of this existed, and its `executionGas_alone_can_increase` is why the measure
is not simply `gasLeft`. -/

theorem Mach.chargeGas_gasMeasure {cost : Nat} {mach mach' : Mach} {u : Unit}
    (h : Mach.chargeGas cost mach = .ok (u, mach')) :
    mach'.gasMeasure + cost = mach.gasMeasure := by
  unfold Mach.chargeGas safeSub at h
  by_cases hle : cost ≤ mach.gasLeft
  · simp only [if_pos hle, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    simp only [Mach.gasMeasure]
    omega
  · exact absurd h (by simp [if_neg hle])

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

/-- The v8.1.4 repay-on-merge rule moves gas from the reservoir to `gasLeft`
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

inductive Ninst : Type
  | reg : Rinst → Ninst
  | exec : Xinst → Ninst
  | push : ∀ bs : Bytes, bs.length ≤ 32 → Ninst
  /-- EIP-8024 `DUPN` (0xE6) with its one immediate byte, undecoded: decoding
  happens at execution, where a forbidden immediate is an exceptional halt. -/
  | dupn : UInt8 → Ninst
  /-- EIP-8024 `SWAPN` (0xE7) with its immediate byte. -/
  | swapn : UInt8 → Ninst
  /-- EIP-8024 `EXCHANGE` (0xE8) with its immediate byte. -/
  | exchange : UInt8 → Ninst

def Ninst.toOpString : Ninst → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push bs _ => "PUSH" ++ bs.length.repr
  | dupn _ => "DUPN"
  | swapn _ => "SWAPN"
  | exchange _ => "EXCHANGE"

def Ninst.toString : Ninst → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push [] _ => "PUSH0"
  | push bs _ => "PUSH" ++ bs.length.repr ++ " " ++ Bytes.toHex bs
  | dupn i => "DUPN " ++ Bytes.toHex [i]
  | swapn i => "SWAPN " ++ Bytes.toHex [i]
  | exchange i => "EXCHANGE " ++ Bytes.toHex [i]

instance : ToString Ninst := ⟨Ninst.toString⟩
instance : Repr Ninst := ⟨λ i _ => i.toString⟩

lemma Ninst.push_ext {xs ys : Bytes}
    (le : xs.length ≤ 32) (le' : ys.length ≤ 32) (eq : xs = ys) :
    Ninst.push xs le = Ninst.push ys le' := by
  revert le le'; rw [eq]; simp

inductive Inst : Type
  | last : Linst → Inst
  | next : Ninst → Inst
  | jump : Jinst → Inst

inductive InstType
  | R | X | J | L | P

def UInt8.toInstType (b : UInt8) : InstType :=
  match b.highs with
  | 0x00 => if b.lows = 0x00 then .L else .R
  | 0x05 =>
    match b.lows with
    | 0x06 => .J
    | 0x07 => .J
    | 0x0B => .J
    | 0x0F => .P
    | _ => .R
  | 0x06 => .P
  | 0x07 => .P
  | 0x0F =>
    match b.lows with
    | 0x03 => .L
    | 0x0D => .L
    | 0x0F => .L
    | _ => .X
  | _ => .R

lemma Linst.toInstType_toUInt8 (l : Linst) : l.toUInt8.toInstType = .L := by
  cases l <;> rfl

lemma Jinst.toInstType_toUInt8 (j : Jinst) : j.toUInt8.toInstType = .J := by
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

lemma le_of_toInstType_eq_p (b : UInt8) (h : b.toInstType = .P) :
    b.toNat ≤ 127 := by
  apply Nat.le_of_lt_succ
  apply (@UInt8.lt_iff_toNat_lt b 0x80).mp
  apply UInt8.lt_of_highs_lt_highs
  simp [UInt8.toInstType] at h; split at h
  · split at h <;> cases h
  · rename (UInt8.highs _ =  _) => heq; rw [heq]
    apply (@UInt8.lt_iff_toNat_lt 5 8).mpr; simp
  · rename (UInt8.highs _ =  _) => heq; rw [heq]
    apply (@UInt8.lt_iff_toNat_lt 6 8).mpr; simp
  · rename (UInt8.highs _ =  _) => heq; rw [heq]
    apply (@UInt8.lt_iff_toNat_lt 7 8).mpr; simp
  · split at h <;> cases h
  · cases h

def ByteArray.getInst (code : ByteArray) (pc : Nat) : Option Inst :=
  if hpc : pc < code.size
  then
    let b : UInt8 := code[pc]
    match h : b.toInstType with
    | .R =>
      -- EIP-8024's three stack-access instructions carry one immediate byte
      -- and are sized here, fork-independently, exactly as `push` is (D8):
      -- whether they are *defined* is `rules.op.stackAccess`, checked where
      -- they run. The immediate is read zero-filled past the end of code.
      match b with
      | 0xE6 => some (.next (.dupn (code.byteD (pc + 1))))
      | 0xE7 => some (.next (.swapn (code.byteD (pc + 1))))
      | 0xE8 => some (.next (.exchange (code.byteD (pc + 1))))
      | _ => b.toRinst <&> (.next ∘ .reg)
    | .X => b.toXinst <&> (.next ∘ .exec)
    | .J => b.toJinst <&> .jump
    | .L => b.toLinst <&> .last
    | .P =>
      let le := le_of_toInstType_eq_p b h
      let bs : Bytes := code.sliceD (pc + 1) (b.toNat - 95) 0
      let le' : bs.length ≤ 32 := by
        simp [bs, ByteArray.length_sliceD, le]
      some <| .next <| .push bs le'
  else
    some (.last .stop)

def Evm.getInst (evm : Evm) : Option Inst :=
  ByteArray.getInst evm.sta.code evm.pc

-- The EIP-8024 decode tables at every boundary the jump-destination argument
-- depends on (goal C, Appendix D), against the pinned `decode_single` and
-- `decode_pair`.
#guard decodeSingle 0x00 = some 145
#guard decodeSingle 0x5A = some 235
#guard decodeSingle 0x80 = some 17
#guard decodeSingle 0xFF = some 144
#guard decodeSingle 0x5B = none
#guard decodeSingle 0x5F = none
#guard decodeSingle 0x60 = none
#guard decodeSingle 0x7F = none
#guard decodePair 0x00 = some (9, 16)
#guard decodePair 0x51 = some (14, 15)
#guard decodePair 0x80 = some (1, 16)
#guard decodePair 0xFF = some (1, 22)
#guard decodePair 0x52 = none
#guard decodePair 0x5B = none
#guard decodePair 0x7F = none
-- Every accepted single decodes into `17 ≤ n ≤ 235`; every accepted pair into
-- `1 ≤ n ≤ 14` and `n < m ≤ 30 - n`; the forbidden ranges are exactly
-- `0x5B–0x7F` and `0x52–0x7F`, and both contain `JUMPDEST` and `PUSH1`–`PUSH32`.
#guard (List.range 256).all fun x =>
  match decodeSingle x.toUInt8 with
  | none => 0x5B ≤ x ∧ x ≤ 0x7F
  | some n => (x < 0x5B ∨ 0x80 ≤ x) ∧ 17 ≤ n ∧ n ≤ 235
#guard (List.range 256).all fun x =>
  match decodePair x.toUInt8 with
  | none => 0x52 ≤ x ∧ x ≤ 0x7F
  | some (n, m) => (x < 0x52 ∨ 0x80 ≤ x) ∧ 1 ≤ n ∧ n ≤ 14 ∧ n < m ∧ m ≤ 30 - n
#guard (decodeSingle 0x5B).isNone ∧ (decodePair 0x5B).isNone -- JUMPDEST
#guard (List.range' 0x60 32).all fun x =>
  (decodeSingle x.toUInt8).isNone ∧ (decodePair x.toUInt8).isNone -- PUSH1–PUSH32
-- Sizing and the zero-filled immediate, fork-independently.
#guard ByteArray.getInst ⟨#[0xE6, 0x80]⟩ 0 matches some (.next (.dupn 0x80))
#guard ByteArray.getInst ⟨#[0xE7, 0x00]⟩ 0 matches some (.next (.swapn 0x00))
#guard ByteArray.getInst ⟨#[0xE8, 0xFF]⟩ 0 matches some (.next (.exchange 0xFF))
#guard ByteArray.getInst ⟨#[0xE6]⟩ 0 matches some (.next (.dupn 0x00))
#guard ByteArray.getInst ⟨#[0x4B]⟩ 0 matches some (.next (.reg .slotnum))

/-- EELS `taylor_exponential`'s accumulator loop as a *well-founded* recursion
(P0.6 item 1): `fakeExpAux num den i numAcc` is the sum of the series continued
from state `(i, numAcc)`. There is no fuel and no failure branch.

Termination is by the lexicographic measure `(num + 1 - i, numAcc)`: while
`i ≤ num` the first component falls; once `i > num`, either `den * i = 0` (a
zero denominator — excluded from the semantic domain by `BlobSchedule.Valid` —
zeroes the accumulator immediately under `Nat` division) or `num < den * i`
strictly shrinks a positive accumulator. -/
def fakeExpAux (num den i numAcc : Nat) : Nat :=
  if _h : numAcc = 0 then 0
  else numAcc + fakeExpAux num den (i + 1) (numAcc * num / (den * i))
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

@[simp] theorem fakeExpAux_zero (num den i : Nat) :
    fakeExpAux num den i 0 = 0 := by
  unfold fakeExpAux
  simp

/-- The EELS recurrence equation — for *every* `Nat` numerator, including the
U64 maximum; nothing here evaluates the series. -/
theorem fakeExpAux_succ {numAcc : Nat} (h : numAcc ≠ 0) (num den i : Nat) :
    fakeExpAux num den i numAcc
      = numAcc + fakeExpAux num den (i + 1) (numAcc * num / (den * i)) := by
  conv_lhs => unfold fakeExpAux
  simp [h]

/-- The EELS accumulator recurrence as a predicate on candidate functions:
`f i numAcc` plays the role of the series sum continued from `(i, numAcc)`. -/
def FakeExpSpec (num den : Nat) (f : Nat → Nat → Nat) : Prop :=
  (∀ i, f i 0 = 0) ∧
  ∀ i numAcc, numAcc ≠ 0 →
    f i numAcc = numAcc + f (i + 1) (numAcc * num / (den * i))

/-- `fakeExpAux` satisfies the recurrence. -/
theorem fakeExpAux_spec (num den : Nat) :
    FakeExpSpec num den (fakeExpAux num den) :=
  ⟨fakeExpAux_zero num den,
   fun i numAcc h => fakeExpAux_succ (numAcc := numAcc) h num den i⟩

/-- Uniqueness: the recurrence has exactly one solution, so `fakeExpAux` is
*the* EELS accumulator function. -/
theorem fakeExpAux_spec_unique {num den : Nat} {f : Nat → Nat → Nat}
    (hf : FakeExpSpec num den f) : f = fakeExpAux num den := by
  funext i numAcc
  induction i, numAcc using fakeExpAux.induct num den with
  | case1 i => rw [hf.1, fakeExpAux_zero]
  | case2 i numAcc h ih => rw [hf.2 i numAcc h, ih, ← fakeExpAux_succ h]

/-- The pre-integrity fuelled worker as a *total* `Option`-valued reference:
`none` exactly where the old implementation exhausted its guessed fuel bound.
This is the only sanctioned old/new bridge; nothing executes it. -/
def fakeExpAuxRef? (num den i : Nat) : Nat → Nat → Option Nat
  | _, 0 => none
  | 0, _ => some 0
  | numAcc, fuel + 1 =>
    (fakeExpAuxRef? num den (i + 1) (numAcc * num / (den * i)) fuel).map
      (numAcc + ·)

/-- The accumulator sequence from `(i, numAcc)` reaches zero strictly before
the fuel runs out — the precise domain on which the old worker answered. -/
def reachesZeroBeforeFuel (num den : Nat) : Nat → Nat → Nat → Bool
  | _, _, 0 => false
  | _, 0, _ => true
  | i, numAcc, fuel + 1 =>
    reachesZeroBeforeFuel num den (i + 1) (numAcc * num / (den * i)) fuel

/-- The reference worker answers exactly on `reachesZeroBeforeFuel`. -/
theorem fakeExpAuxRef?_isSome (num den : Nat) :
    ∀ fuel i numAcc, (fakeExpAuxRef? num den i numAcc fuel).isSome
      = reachesZeroBeforeFuel num den i numAcc fuel := by
  intro fuel
  induction fuel with
  | zero => intro i numAcc; cases numAcc <;> rfl
  | succ fuel ih =>
    intro i numAcc
    cases numAcc with
    | zero => rfl
    | succ n => simp [fakeExpAuxRef?, reachesZeroBeforeFuel, ih]

/-- Wherever the old fuelled computation completed, it computed exactly the
total well-founded value. -/
theorem fakeExpAuxRef?_eq_some {num den : Nat} :
    ∀ {fuel i numAcc}, reachesZeroBeforeFuel num den i numAcc fuel = true →
      fakeExpAuxRef? num den i numAcc fuel
        = some (fakeExpAux num den i numAcc) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i numAcc h
    cases numAcc <;> simp [reachesZeroBeforeFuel] at h
  | succ fuel ih =>
    intro i numAcc h
    cases numAcc with
    | zero => simp [fakeExpAuxRef?]
    | succ n =>
      rw [fakeExpAux_succ (Nat.succ_ne_zero n)]
      simp only [fakeExpAuxRef?]
      rw [ih (by simpa [reachesZeroBeforeFuel] using h)]
      rfl

/-- EELS `taylor_exponential`: approximates `fac * e ^ (num / den)`. Total for
every input; the semantic domain additionally demands a positive denominator
through `BlobSchedule.Valid`. -/
def fakeExp (fac num den : Nat) : Nat :=
  fakeExpAux num den 1 (fac * den) / den

def calculateBlobGasPrice (blob : BlobSchedule) (excessBlobGas : Nat) : Nat :=
  fakeExp 1 excessBlobGas blob.baseFeeUpdateFraction

/-- The public EELS `calculate_blob_gas_price` equation, through the
recurrence function rather than through evaluation (`MIN_BLOB_GASPRICE = 1`). -/
theorem calculateBlobGasPrice_eq (blob : BlobSchedule) (excess : Nat) :
    calculateBlobGasPrice blob excess
      = fakeExpAux excess blob.baseFeeUpdateFraction 1
          (1 * blob.baseFeeUpdateFraction) / blob.baseFeeUpdateFraction := rfl

/-- Under a validated schedule the denominator is positive and the price is
the value of the *unique* solution of the EELS recurrence — for every `Nat`
excess. Nothing here evaluates the series. -/
theorem calculateBlobGasPrice_spec (blob : BlobSchedule) (hv : blob.Valid)
    (excess : Nat) :
    0 < blob.baseFeeUpdateFraction ∧
    ∀ f, FakeExpSpec excess blob.baseFeeUpdateFraction f →
      calculateBlobGasPrice blob excess
        = f 1 (1 * blob.baseFeeUpdateFraction) / blob.baseFeeUpdateFraction := by
  refine ⟨hv.1, fun f hf => ?_⟩
  rw [calculateBlobGasPrice_eq, fakeExpAux_spec_unique hf]

/-- The U64-maximum numerator, pinned explicitly: the acceptance case the plan
forbids executing is covered by the non-evaluating theorem above. -/
theorem calculateBlobGasPrice_spec_u64max (blob : BlobSchedule)
    (hv : blob.Valid) :
    0 < blob.baseFeeUpdateFraction ∧
    ∀ f, FakeExpSpec (2 ^ 64 - 1) blob.baseFeeUpdateFraction f →
      calculateBlobGasPrice blob (2 ^ 64 - 1)
        = f 1 (1 * blob.baseFeeUpdateFraction) / blob.baseFeeUpdateFraction :=
  calculateBlobGasPrice_spec blob hv (2 ^ 64 - 1)

/-- The maximum `excessBlobGas` present in the pinned current-mainnet fixture
corpus (`0xfffffffffffe0000`, reached only by invalid-header fixtures that are
rejected before any price calculation), likewise pinned non-evaluatingly. -/
theorem calculateBlobGasPrice_spec_corpusMax (blob : BlobSchedule)
    (hv : blob.Valid) :
    0 < blob.baseFeeUpdateFraction ∧
    ∀ f, FakeExpSpec 0xfffffffffffe0000 blob.baseFeeUpdateFraction f →
      calculateBlobGasPrice blob 0xfffffffffffe0000
        = f 1 (1 * blob.baseFeeUpdateFraction) / blob.baseFeeUpdateFraction :=
  calculateBlobGasPrice_spec blob hv 0xfffffffffffe0000

-- Reference points computed from the pinned EELS `taylor_exponential`
-- (execution-specs 4198b9c5…, byte-identical at the current-mainnet source
-- commit 87aba1a3…). The committed differential grid is
-- scripts/vectors/fake-exp.json, checked by scripts/check-fake-exp.sh.
#guard fakeExp 1 0 5007716 = 1                    -- numerator zero
#guard fakeExp 1 1 5007716 = 1
#guard fakeExp 1 5007715 5007716 = 2
#guard fakeExp 1 5007716 5007716 = 2              -- e^1
#guard fakeExp 1 (3 * 5007716) 5007716 = 20       -- e^3
#guard fakeExp 1 (10 * 5007716) 5007716 = 22026   -- e^10
#guard fakeExp 2 5 1 = 287                        -- 2e^5
#guard fakeExp 1 50 1 = 5184612586559446279969    -- e^50
-- The maximum *feasible* corpus excess, 0xe760000 = 1851 blobs' worth of gas,
-- against all three canonical fraction values (Prague and Osaka share one).
#guard fakeExp 1 0xe760000 5007716 = 1098342643171911460576
#guard fakeExp 1 0xe760000 8346193 = 4211562125831
#guard fakeExp 1 0xe760000 11684671 = 1041019391

def Mach.push (x : B256) (mach : Mach) : Footprint.Outcome Mach Unit :=
  if mach.stack.length < 1024
  then .ok ⟨(), {mach with stack := x :: mach.stack}⟩
  else .error ⟨.halt (.stackOverflow .none), mach⟩

def Devm.push (x : B256) (devm : Devm) : Execution :=
  liftMachExecution (Mach.push x) devm

theorem Devm.push_def (x : B256) (devm : Devm) : Devm.push x devm = (do
    .assert
      (devm.stack.length < 1024)
      ⟨.halt (.stackOverflow .none), devm⟩
    .ok (devm.setMach {devm.mach with stack := x :: devm.stack})) := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  simp only [Devm.push, Mach.push, liftMachExecution, liftMach, Footprint.toExecution,
    Footprint.liftOutcome, Devm.stack, Devm.setMach, Except.assert, bind, Except.bind]
  split_ifs <;> rfl

def Mach.pop (mach : Mach) : Footprint.Outcome Mach B256 :=
  match mach.stack with
  | [] => .error ⟨.halt (.stackUnderflow .none), mach⟩
  | x :: xs => .ok ⟨x, {mach with stack := xs}⟩

def Devm.pop (devm : Devm) : Except (EvmError × Devm) (B256 × Devm) :=
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
    devm.popToNat = (devm.pop <&> Prod.mapFst B256.toNat) := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  cases stack <;> rfl

def Mach.popToAdr (mach : Mach) : Footprint.Outcome Mach Adr :=
  match mach.pop with
  | .error err => .error err
  | .ok ⟨x, mach'⟩ => .ok ⟨x.toAdr, mach'⟩

def Devm.popToAdr (devm : Devm) : Except (EvmError × Devm) (Adr × Devm) :=
  liftMach Mach.popToAdr devm

theorem Devm.popToAdr_def (devm : Devm) :
    devm.popToAdr = (devm.pop <&> Prod.mapFst B256.toAdr) := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  cases stack <;> rfl

def Mach.popN (mach : Mach) : Nat → Footprint.Outcome Mach (List B256)
  | 0 => .ok ⟨[], mach⟩
  | n + 1 =>
    match mach.pop with
    | .error err => .error err
    | .ok ⟨x, mach'⟩ =>
      match mach'.popN n with
      | .error err => .error err
      | .ok ⟨xs, mach''⟩ => .ok ⟨x :: xs, mach''⟩

def Devm.popN (devm : Devm) (n : Nat) :
    Except (EvmError × Devm) (List B256 × Devm) :=
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

def Mach.pushItem (x : B256) (c : Nat) (mach : Mach) : Footprint.Outcome Mach Unit :=
  match Mach.chargeGas c mach with
  | .error err => .error err
  | .ok ⟨_, mach'⟩ => Mach.push x mach'

def pushItem (x : B256) (c : Nat) (devm : Devm) : Execution :=
  liftMachExecution (Mach.pushItem x c) devm

theorem pushItem_def (x : B256) (c : Nat) (devm : Devm) :
    pushItem x c devm = (chargeGas c devm >>= Devm.push x) := by
  rcases devm with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  simp only [pushItem, Mach.pushItem, Mach.chargeGas, Mach.push, chargeGas, Devm.push,
    liftMachExecution, liftMach, Footprint.toExecution, Footprint.liftOutcome,
    Devm.setMach, bind, Except.bind]
  cases safeSub gasLeft c with
  | none => rfl
  | some gas => dsimp only

def accessCost (x : Adr) (a : AdrSet) : Nat :=
  if x ∈ a then gasWarmAccess else gasColdAccountAccess

/-- The warm/cold account-access cost under a *fork's own* schedule.

A sibling rather than a third parameter on `accessCost`. EIP-8038 reprices the
cold half (2,600 to 3,000) and leaves the warm half alone, so the interpreter
has to read the number from `rules.gas` -- but `accessCost` is named 121 times
downstream, and widening its arity would move every one of those statements for
a reason that has nothing to do with what they say. Instead the schedule-carrying
form is the one the interpreter calls, `accessCost` stays exactly what it was,
and the `rfl` lemma below says they are the same function at Prague. -/
def GasSchedule.accessCost (gas : GasSchedule) (x : Adr) (a : AdrSet) : Nat :=
  if x ∈ a then gasWarmAccess else gas.coldAccountAccess

@[simp] theorem pragueGasSchedule_accessCost (x : Adr) (a : AdrSet) :
    pragueGasSchedule.accessCost x a = accessCost x a := rfl

@[simp] theorem pragueRules_gas_accessCost (x : Adr) (a : AdrSet) :
    pragueRules.gas.accessCost x a = accessCost x a := rfl

/-- The warm cost is the floor at every schedule, because only the cold half
moves. The Sufficiency family needs this, and needs it to hold of an arbitrary
schedule rather than of Prague's. -/
theorem GasSchedule.gasWarmAccess_le_accessCost (gas : GasSchedule)
    (x : Adr) (a : AdrSet) (h : gasWarmAccess ≤ gas.coldAccountAccess) :
    gasWarmAccess ≤ gas.accessCost x a := by
  unfold GasSchedule.accessCost
  split
  · exact Nat.le_refl _
  · exact h

/-- The account-access cost is positive under any usable schedule -- the shape
`access_cost_pos` had at Prague, now stated of the schedule the interpreter
actually reads. -/
theorem GasSchedule.Valid.accessCost_pos {g : GasSchedule} (h : g.Valid)
    (x : Adr) (a : AdrSet) : 0 < g.accessCost x a := by
  unfold GasSchedule.accessCost
  have hw := h.warmAccess_le
  unfold gasWarmAccess at *
  split <;> omega

theorem GasSchedule.Valid.warmAccess_le_accessCost {g : GasSchedule}
    (h : g.Valid) (x : Adr) (a : AdrSet) : gasWarmAccess ≤ g.accessCost x a :=
  g.gasWarmAccess_le_accessCost x a h.warmAccess_le

def Meta.addAccessedAddress (view : Meta) (a : Adr) : Meta :=
  {view with accessedAddresses := view.accessedAddresses.insert a}

def addAccessedAddress (devm : Devm) (a : Adr) : Devm :=
  liftMachMetaPure (fun mach view => (mach, view.addAccessedAddress a)) devm

def Meta.addAccessedStorageKey (view : Meta) (a : Adr) (k : B256) : Meta :=
  {view with accessedStorageKeys := view.accessedStorageKeys.insert ⟨a, k⟩}

def addAccessedStorageKey (devm : Devm) (a : Adr) (k : B256) : Devm :=
  liftMachMetaPure (fun mach view => (mach, view.addAccessedStorageKey a k)) devm

/-- EIP-7928: record an account read (`state_tracker.get_account_optional`
and every accessor built on it). -/
def Meta.readAccount (view : Meta) (a : Adr) : Meta :=
  {view with accountReads := view.accountReads.insert a}

/-- EIP-7928: record a storage read (`state_tracker.get_storage`). -/
def Meta.readStorage (view : Meta) (a : Adr) (k : B256) : Meta :=
  {view with storageReads := view.storageReads.insert ⟨a, k⟩}

/-- Record an account read for the block-level access list, under rules that
carry one; the identity under `rules.bal = none`, so that nothing a Prague–BPO2
frame does can observe the read set (goal C, fixed decision 2). Placed at the
interpreter sites where the pinned code calls a state accessor -- after the
charge that precedes the access, so an out-of-gas frame records nothing the
pinned frame would not. -/
def Devm.balReadAccount (rules : ForkRules) (a : Adr) (devm : Devm) : Devm :=
  -- The switch sits inside `setMeta` so that `mach` and `world` are preserved
  -- *definitionally* in both branches: every existing proof that reads through
  -- a meta-only update by `rfl` keeps doing so.
  devm.setMeta (if rules.bal.isSome then devm.meta.readAccount a else devm.meta)

/-- The storage-read twin of `Devm.balReadAccount`. -/
def Devm.balReadStorage (rules : ForkRules) (a : Adr) (k : B256) (devm : Devm) :
    Devm :=
  devm.setMeta (if rules.bal.isSome then devm.meta.readStorage a k else devm.meta)

-- The recorders touch `meta` and nothing else; every measure, machine field
-- and world projection sees through them, and under `bal = none` they vanish.
@[simp] theorem Devm.balReadAccount_mach (rules : ForkRules) (a : Adr) (devm : Devm) :
    (devm.balReadAccount rules a).mach = devm.mach := by
  rfl
@[simp] theorem Devm.balReadAccount_world (rules : ForkRules) (a : Adr) (devm : Devm) :
    (devm.balReadAccount rules a).world = devm.world := by
  rfl
@[simp] theorem Devm.balReadAccount_gasLeft (rules : ForkRules) (a : Adr) (devm : Devm) :
    (devm.balReadAccount rules a).gasLeft = devm.gasLeft := by
  rfl
@[simp] theorem Devm.balReadAccount_gasMeasure (rules : ForkRules) (a : Adr) (devm : Devm) :
    (devm.balReadAccount rules a).gasMeasure = devm.gasMeasure := by
  rfl
@[simp] theorem Devm.balReadAccount_stack (rules : ForkRules) (a : Adr) (devm : Devm) :
    (devm.balReadAccount rules a).stack = devm.stack := by
  rfl
@[simp] theorem Devm.balReadAccount_state (rules : ForkRules) (a : Adr) (devm : Devm) :
    (devm.balReadAccount rules a).state = devm.state := by
  rfl
@[simp] theorem Devm.balReadAccount_stateGas (rules : ForkRules) (a : Adr) (devm : Devm) :
    (devm.balReadAccount rules a).stateGas = devm.stateGas := by
  rfl
@[simp] theorem Devm.balReadAccount_stateGasLeft (rules : ForkRules) (a : Adr) (devm : Devm) :
    (devm.balReadAccount rules a).stateGasLeft = devm.stateGasLeft := by
  rfl
@[simp] theorem Devm.balReadAccount_accessedAddresses (rules : ForkRules) (a : Adr)
    (devm : Devm) :
    (devm.balReadAccount rules a).accessedAddresses = devm.accessedAddresses := by
  unfold Devm.balReadAccount Meta.readAccount; split <;> rfl
@[simp] theorem Devm.balReadAccount_accessedStorageKeys (rules : ForkRules) (a : Adr)
    (devm : Devm) :
    (devm.balReadAccount rules a).accessedStorageKeys = devm.accessedStorageKeys := by
  unfold Devm.balReadAccount Meta.readAccount; split <;> rfl
@[simp] theorem Devm.balReadAccount_createdAccounts (rules : ForkRules) (a : Adr)
    (devm : Devm) :
    (devm.balReadAccount rules a).createdAccounts = devm.createdAccounts := by
  unfold Devm.balReadAccount Meta.readAccount; split <;> rfl
@[simp] theorem Devm.balReadAccount_refundCounter (rules : ForkRules) (a : Adr)
    (devm : Devm) :
    (devm.balReadAccount rules a).refundCounter = devm.refundCounter := by
  unfold Devm.balReadAccount Meta.readAccount; split <;> rfl
@[simp] theorem Devm.balReadAccount_logs (rules : ForkRules) (a : Adr) (devm : Devm) :
    (devm.balReadAccount rules a).logs = devm.logs := by
  unfold Devm.balReadAccount Meta.readAccount; split <;> rfl
@[simp] theorem Devm.balReadAccount_transientStorage (rules : ForkRules) (a : Adr)
    (devm : Devm) :
    (devm.balReadAccount rules a).transientStorage = devm.transientStorage := by
  rfl
theorem Devm.balReadAccount_none {rules : ForkRules} (h : rules.bal = none) (a : Adr)
    (devm : Devm) : devm.balReadAccount rules a = devm := by
  unfold Devm.balReadAccount; simp [h, Devm.setMeta]

@[simp] theorem Devm.balReadStorage_mach (rules : ForkRules) (a : Adr) (k : B256)
    (devm : Devm) : (devm.balReadStorage rules a k).mach = devm.mach := by
  rfl
@[simp] theorem Devm.balReadStorage_world (rules : ForkRules) (a : Adr) (k : B256)
    (devm : Devm) : (devm.balReadStorage rules a k).world = devm.world := by
  rfl
@[simp] theorem Devm.balReadStorage_gasLeft (rules : ForkRules) (a : Adr) (k : B256)
    (devm : Devm) : (devm.balReadStorage rules a k).gasLeft = devm.gasLeft := by
  rfl
@[simp] theorem Devm.balReadStorage_gasMeasure (rules : ForkRules) (a : Adr) (k : B256)
    (devm : Devm) : (devm.balReadStorage rules a k).gasMeasure = devm.gasMeasure := by
  rfl
@[simp] theorem Devm.balReadStorage_stack (rules : ForkRules) (a : Adr) (k : B256)
    (devm : Devm) : (devm.balReadStorage rules a k).stack = devm.stack := by
  rfl
@[simp] theorem Devm.balReadStorage_state (rules : ForkRules) (a : Adr) (k : B256)
    (devm : Devm) : (devm.balReadStorage rules a k).state = devm.state := by
  rfl
@[simp] theorem Devm.balReadStorage_stateGas (rules : ForkRules) (a : Adr) (k : B256)
    (devm : Devm) : (devm.balReadStorage rules a k).stateGas = devm.stateGas := by
  rfl
@[simp] theorem Devm.balReadStorage_stateGasLeft (rules : ForkRules) (a : Adr) (k : B256)
    (devm : Devm) : (devm.balReadStorage rules a k).stateGasLeft = devm.stateGasLeft := by
  rfl
@[simp] theorem Devm.balReadStorage_accessedAddresses (rules : ForkRules) (a : Adr)
    (k : B256) (devm : Devm) :
    (devm.balReadStorage rules a k).accessedAddresses = devm.accessedAddresses := by
  unfold Devm.balReadStorage Meta.readStorage; split <;> rfl
@[simp] theorem Devm.balReadStorage_accessedStorageKeys (rules : ForkRules) (a : Adr)
    (k : B256) (devm : Devm) :
    (devm.balReadStorage rules a k).accessedStorageKeys = devm.accessedStorageKeys := by
  unfold Devm.balReadStorage Meta.readStorage; split <;> rfl
@[simp] theorem Devm.balReadStorage_createdAccounts (rules : ForkRules) (a : Adr)
    (k : B256) (devm : Devm) :
    (devm.balReadStorage rules a k).createdAccounts = devm.createdAccounts := by
  unfold Devm.balReadStorage Meta.readStorage; split <;> rfl
@[simp] theorem Devm.balReadStorage_refundCounter (rules : ForkRules) (a : Adr)
    (k : B256) (devm : Devm) :
    (devm.balReadStorage rules a k).refundCounter = devm.refundCounter := by
  unfold Devm.balReadStorage Meta.readStorage; split <;> rfl
@[simp] theorem Devm.balReadStorage_transientStorage (rules : ForkRules) (a : Adr)
    (k : B256) (devm : Devm) :
    (devm.balReadStorage rules a k).transientStorage = devm.transientStorage := by
  rfl
theorem Devm.balReadStorage_none {rules : ForkRules} (h : rules.bal = none) (a : Adr)
    (k : B256) (devm : Devm) : devm.balReadStorage rules a k = devm := by
  unfold Devm.balReadStorage; simp [h, Devm.setMeta]


def addAccountToDelete (devm : Devm) (a : Adr) : Devm :=
  devm.withAccountsToDelete (devm.accountsToDelete.insert a)

def addCreatedAccount (benv : Benv) (adr : Adr) : Benv :=
  {benv with createdAccounts := benv.createdAccounts.insert adr}

def Acct.nil : Acct :=
  {
    nonce := 0
    bal := 0
    stor := .empty
    code := ByteArray.mk #[]
  }

lemma Std.TreeMap.eq_empty_iff_isEmpty {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} :
    t = Std.TreeMap.empty ↔ t.isEmpty = true := by
  refine' ⟨_, eq_empty_of_isEmpty⟩; intro h; cases h; rfl

instance {stor : Stor} : Decidable (stor = .empty) := by
  simp only [Stor.empty]
  rw [show (stor = Std.TreeMap.empty) ↔ (stor.isEmpty = true) from
        Std.TreeMap.eq_empty_iff_isEmpty]
  infer_instance

instance {ac : Acct} : Decidable (ac = .nil) := by
  rw [Acct.ext_iff, Acct.nil]; apply instDecidableAnd

def State.get (w : State) (a : Adr) : Acct :=
  w.getD a .nil

def State.set (w : State) (a : Adr) (ac : Acct) : State :=
  if ac = .nil then w.erase a else w.insert a ac

def Acct.Empty (a : Acct) : Prop :=
  a.code.size = 0 ∧ a.nonce = 0 ∧ a.bal = 0

instance {a : Acct} : Decidable a.Empty := by
 apply instDecidableAnd

def destroyAccount (w : State) (a : Adr) : State := w.erase a

abbrev AccountExists (wor : State) (adr : Adr) : Prop :=
  let acct := wor.get adr
  ¬ (acct.Empty ∧ acct.stor.isEmpty)

-- dedicated function for 'destroying touched empty accounts' is
-- not necessary for this implementation, as all functions for
-- modifying world state are designed to immediately destroy any
-- account if it becomes empty as a result of the modification

def Tra.set (τ : Tra) (a : Adr) (s : Stor) : Tra :=
  if s.isEmpty then τ.erase a else τ.insert a s

def State.setCode (ω : State) (a : Adr) (cd : ByteArray) : State :=
  let ac := ω.get a
  ω.set a {ac with code := cd}

def getOrigAcct (sevm : Sevm) (a : Adr) : Acct :=
  sevm.benvStat.origState.get a

def Devm.getAcct (devm : Devm) (a : Adr) : Acct :=
  devm.state.get a

def Devm.getBal (devm : Devm) (a : Adr) : B256 := (devm.getAcct a).bal
def Devm.getCode (devm : Devm) (a : Adr) : ByteArray := (devm.getAcct a).code
def Devm.getStorVal (devm : Devm) (adr : Adr) (key : B256) : B256 :=
  (devm.getAcct adr).stor.get key

def Stor.set (s : Stor) (k v : B256) : Stor :=
  if v = 0 then s.erase k else s.insert k v

def State.setStorVal (wor : State) (adr : Adr) (key val : B256) : State :=
  let acct : Acct := wor.get adr
  wor.set adr {acct with stor := acct.stor.set key val}

def Benv.setStorVal (benv : Benv) (adr : Adr) (key val : B256) : Benv :=
  {benv with state := benv.state.setStorVal adr key val}

def Devm.setStorVal (devm : Devm) (adr : Adr) (key val : B256) : Devm :=
  devm.withState (devm.state.setStorVal adr key val)

def Tra.setStorVal (tra : Tra) (adr : Adr) (key val : B256) : Tra :=
  let stor : Stor := tra.getD adr .empty
  tra.set adr <| stor.set key val

def Tenv.setTransVal (tenv : Tenv) (adr : Adr) (key val : B256) : Tenv :=
  {tenv with transientStorage := tenv.transientStorage.setStorVal adr key val}

def Devm.setTransVal (devm : Devm) (adr : Adr) (key val : B256) : Devm :=
  devm.withTransientStorage (devm.transientStorage.setStorVal adr key val)

def getOrigStorVal (sevm : Sevm) (adr : Adr) (key : B256) : B256 :=
  (getOrigAcct sevm adr).stor.get key

def Devm.getTransVal (devm : Devm) (adr : Adr) (key : B256) : B256 :=
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

def Dead (w : State) (a : Adr) : Prop :=
  match w[a]? with
  | none => True
  | some x => x.Empty

def Mach.memWrite (mach : Mach) (idx : Nat) (val : Bytes) : Mach :=
  {mach with memory := mach.memory.write idx val}

def Devm.memWrite (devm : Devm) (idx : Nat) (val : Bytes) : Devm :=
  liftMachPure (Mach.memWrite · idx val) devm

def Devm.memRead (devm : Devm) (index size : Nat) : Bytes × Devm :=
  let ⟨val, mem⟩ := devm.memory.read index size
  ⟨val, devm.withMemory mem⟩

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
def transferLogAddress : Adr := 0xfffffffffffffffffffffffffffffffffffffffe

/-- `TRANSFER_TOPIC`, `keccak256("Transfer(address,address,uint256)")`. Stated
as the literal so that no site hashes; `transferTopic_keccak` below pins it to
the hash. -/
def transferTopic : B256 :=
  0xddf252ad1be2c89b69c2b068fc378daa952ba7f163c4a11628f55a4df523b3ef

/-- The log one non-zero ETH transfer between distinct accounts emits: the two
addresses left-padded to words as the indexed topics, the amount as the data. -/
def transferLog (sender recipient : Adr) (amount : B256) : Log :=
  { address := transferLogAddress
    topics := [transferTopic, sender.toB256, recipient.toB256]
    data := amount.toBytes }

/-- `emit_transfer_log`, with both of upstream's guards folded in: a self
transfer and a zero transfer emit nothing. -/
def Devm.emitTransferLog (devm : Devm) (sender recipient : Adr) (amount : B256) :
    Devm :=
  if sender = recipient ∨ amount = 0 then devm
  else devm.addLog (transferLog sender recipient amount)

#guard transferTopic = Bytes.keccak "Transfer(address,address,uint256)".toUTF8.toList

def Mach.applyUnary (f : B256 → B256) (cost : Nat) (mach : Mach) :
    Footprint.Outcome Mach Unit :=
  match mach.pop with
  | .error err => .error err
  | .ok ⟨x, mach'⟩ => Mach.pushItem (f x) cost mach'

def Mach.applyBinary (f : B256 → B256 → B256) (cost : Nat) (mach : Mach) :
    Footprint.Outcome Mach Unit :=
  match mach.pop with
  | .error err => .error err
  | .ok ⟨x, mach'⟩ =>
    match mach'.pop with
    | .error err => .error err
    | .ok ⟨y, mach''⟩ => Mach.pushItem (f x y) cost mach''

def Mach.applyTernary (f : B256 → B256 → B256 → B256) (cost : Nat)
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

def applyUnary (f : B256 → B256) (cost : Nat) (devm : Devm) : Execution :=
  liftMachExecution (Mach.applyUnary f cost) devm

def applyBinary (f : B256 → B256 → B256)
  (cost : Nat) (devm : Devm) : Execution :=
  liftMachExecution (Mach.applyBinary f cost) devm

def applyTernary (f : B256 → B256 → B256 → B256)
  (cost : Nat) (devm : Devm) : Execution :=
  liftMachExecution (Mach.applyTernary f cost) devm

theorem applyUnary_def (f : B256 → B256) (cost : Nat) (devm : Devm) :
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

theorem applyBinary_def (f : B256 → B256 → B256) (cost : Nat) (devm : Devm) :
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

#guard List.exchange [1, 2, 3, 4] 1 3 = some [1, 4, 3, 2]
#guard List.exchange [1, 2, 3, 4] 0 4 = none
#guard List.exchange ([] : List Nat) 0 0 = none

def Evm.contract (evm : Evm) : Adr := evm.sta.currentTarget

def assertDynamic (sevm : Sevm) (devm : Devm) : Except (EvmError × Devm) Unit :=
  Except.assert (!sevm.isStatic) ⟨.halt (.writeInStaticContext .none), devm⟩

/-- The refund a single `SSTORE` adds to or removes from the counter.

The clear refund arrives through `gas.storageClearRefund` rather than through
the `rSClear` global, because Amsterdam reprices it inside this same formula.
Every other number here -- `gasStorageSet`, `gasStorageUpdate`, `gasColdSload`,
`gasWarmAccess` -- is a legacy-only value the supported chain shares, and stays
a global for that reason. `pragueRules_gas_storageClearRefund` below is the
`rfl` proof that no Prague caller can tell the difference. -/
def sstoreNewRefundCounter (gas : GasSchedule) (new_value : B256)
    (original_value : B256) (current_value : B256) (rc : Int) : Int :=
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
        rc'' + (gasStorageSet - gasWarmAccess)
      else
        rc'' + (gasStorageUpdate - gasColdSload - gasWarmAccess)
    else
      rc''
  else rc

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
    (new_value original_value current_value : B256) (rc : Int) : Int :=
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
    (new_value original_value current_value : B256) (cold : Bool) : Nat :=
  (if cold then gasColdSload else gasWarmAccess) +
    (if original_value = current_value ∧ current_value ≠ new_value then
      state.storageWrite
    else
      0)

/-- The *state* gas one `SSTORE` charges: `STORAGE_SET` on a first-time set of a
zero slot, and nothing otherwise. The credit-back when such a slot is cleared
again in the same transaction is a refund rather than a negative charge, so it
goes through `creditStateGasRefund` at the site. -/
def sstoreAmsterdamStateGas (state : StateGasRules)
    (new_value original_value current_value : B256) : Nat :=
  if original_value = current_value ∧ current_value ≠ new_value
      ∧ original_value = 0 then
    state.storageSet
  else
    0

/-- Whether this `SSTORE` returns the slot to a zero original, which refills the
`STORAGE_SET` an earlier set in the same transaction charged. -/
def sstoreAmsterdamStateRefund (state : StateGasRules)
    (new_value original_value current_value : B256) : Nat :=
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
@[simp] theorem Devm.balReadAccount_getAcct (rules : ForkRules) (a x : Adr) (devm : Devm) :
    (devm.balReadAccount rules a).getAcct x = devm.getAcct x := rfl
@[simp] theorem Devm.balReadAccount_getBal (rules : ForkRules) (a x : Adr) (devm : Devm) :
    (devm.balReadAccount rules a).getBal x = devm.getBal x := rfl
@[simp] theorem Devm.balReadAccount_getCode (rules : ForkRules) (a x : Adr) (devm : Devm) :
    (devm.balReadAccount rules a).getCode x = devm.getCode x := rfl
@[simp] theorem Devm.balReadAccount_getStorVal (rules : ForkRules) (a x : Adr) (k : B256)
    (devm : Devm) : (devm.balReadAccount rules a).getStorVal x k = devm.getStorVal x k := rfl
@[simp] theorem Devm.balReadStorage_getAcct (rules : ForkRules) (a x : Adr) (k : B256)
    (devm : Devm) : (devm.balReadStorage rules a k).getAcct x = devm.getAcct x := rfl
@[simp] theorem Devm.balReadStorage_getStorVal (rules : ForkRules) (a x : Adr) (k k' : B256)
    (devm : Devm) : (devm.balReadStorage rules a k).getStorVal x k' = devm.getStorVal x k' := rfl

def Rinst.balanceCore (rules : ForkRules) (world : World) (mach : Mach)
    (view : Meta) : Footprint.Outcome (Mach × Meta) Unit :=
  match mach.pop with
  | .error (err, mach') => .error (err, (mach', view))
  | .ok (x, mach') =>
    let a := x.toAdr
    let warm := a ∈ view.accessedAddresses
    let view' := if warm then view else view.addAccessedAddress a
    let cost := if warm then gasWarmAccess else rules.gas.coldAccountAccess
    match Mach.chargeGas cost mach' with
    | .error (err, mach'') => .error (err, (mach'', view'))
    | .ok (_, mach'') =>
      -- `environment.py` `balance`: `charge_gas` then `get_account(address)`;
      -- the read is recorded after the charge and before the push (EIP-7928).
      let view'' := if rules.bal.isSome then view'.readAccount a else view'
      match Mach.push (world.state.get a).bal mach'' with
      | .error (err, mach''') => .error (err, (mach''', view''))
      | .ok (_, mach''') => .ok ((), (mach''', view''))

def Rinst.runCore
  (pc : Nat)
  (devm : Devm)
  (sevm : Sevm) : Rinst → Execution
  | .address => pushItem sevm.currentTarget.toB256 gBase devm
  | .basefee => pushItem sevm.benvStat.baseFeePerGas.toB256 gBase devm
  | .blobhash => do
    let ⟨x, devm⟩ ← devm.pop
    let y : B256 := sevm.tenvStat.blobVersionedHashes.getD x.toNat 0
    chargeGas gHashopcode devm >>= Devm.push y
  | .blobbasefee => do
    let fee :=
      calculateBlobGasPrice sevm.benvStat.rules.blob sevm.benvStat.excessBlobGas
    pushItem fee.toB256 gBase devm
  | .balance =>
    liftMachMetaWorldExecution (Rinst.balanceCore sevm.benvStat.rules) devm
  | .origin => pushItem sevm.tenvStat.origin.toB256 gBase devm
  | .caller => pushItem sevm.caller.toB256 gBase devm
  | .callvalue => pushItem sevm.value gBase devm
  | .calldataload => do
    let ⟨start_index, devm⟩ ← devm.pop
    let devm' ← chargeGas gVerylow devm
    let value := Bytes.toB256 <| sevm.data.sliceD start_index.toNat 32 0
    devm'.push value
  | .calldatasize => pushItem sevm.data.length.toB256 gBase devm
  | .calldatacopy => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨data_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gasCopy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) devm
    let value := sevm.data.sliceD data_start_index size 0
    .ok <| devm.memWrite memory_start_index value
  | .codesize => pushItem sevm.code.size.toB256 gBase devm
  | .codecopy => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨code_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gasCopy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) devm
    let value := sevm.code.sliceD code_start_index size (Linst.toUInt8 .stop)
    .ok (devm.memWrite memory_start_index value)
  | .gasprice => pushItem sevm.tenvStat.gasPrice.toB256 gBase devm
  -- EIP-8038 adds a code-reading surcharge to `EXTCODESIZE` and `EXTCODECOPY`,
  -- and reprices the cold half of the access. Both arrive through `rules.gas`;
  -- the surcharge is *additive with identity zero*, so the Prague formula here
  -- is literally the formula it was rather than merely equal to it.
  | .extcodesize => do
    let ⟨adr, devm⟩ ← devm.popToAdr
    let gas := sevm.benvStat.rules.gas
    let devm ←
      if adr ∈ devm.accessedAddresses
      then chargeGas (gasWarmAccess + gas.codeReadSurcharge) devm
      else
        chargeGas (gas.coldAccountAccess + gas.codeReadSurcharge)
          (addAccessedAddress devm adr)
    -- `get_account(address)` after the charge (EIP-7928).
    let devm := devm.balReadAccount sevm.benvStat.rules adr
    let codesize := (devm.getCode adr).size.toB256
    devm.push codesize
  | .extcodecopy => do
    let ⟨adr, devm⟩ ← devm.popToAdr
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨code_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gasCopy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let gas := sevm.benvStat.rules.gas
    let devm ←
      if adr ∈ devm.accessedAddresses
      then
        chargeGas
          (gasWarmAccess + gas.codeReadSurcharge + copy_gas_cost
            + extend_memory_cost)
          devm
      else
        chargeGas
          (gas.coldAccountAccess + gas.codeReadSurcharge + copy_gas_cost
            + extend_memory_cost)
          (addAccessedAddress devm adr)
    -- `get_account(address)` after the charge (EIP-7928).
    let devm := devm.balReadAccount sevm.benvStat.rules adr
    let code := devm.getCode adr
    let value := code.sliceD code_start_index size (Linst.toUInt8 .stop)
    .ok (devm.memWrite memory_start_index value)
  | .returndatasize => pushItem devm.returnData.length.toB256 gBase devm
  | .returndatacopy => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨return_data_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gReturnDataCopy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) devm
    if (devm.returnData.length < return_data_start_index + size) then
      .error ⟨.halt (.outOfBoundsRead .none), devm⟩
    let value :=
      devm.returnData.sliceD return_data_start_index size 0
    .ok (devm.memWrite memory_start_index value)
  -- `EXTCODEHASH` takes the repriced cold access and *no* surcharge: upstream
  -- adds the code-reading cost at `EXTCODESIZE` and `EXTCODECOPY` only, which
  -- is a fact about those two arms rather than about reading code.
  | .extcodehash => do
    let ⟨adr, devm⟩ ← devm.popToAdr
    let devm ←
      if adr ∈ devm.accessedAddresses then
        chargeGas gasWarmAccess devm
      else
        chargeGas sevm.benvStat.rules.gas.coldAccountAccess
          (addAccessedAddress devm adr)
    -- `get_account(address)` after the charge (EIP-7928).
    let devm := devm.balReadAccount sevm.benvStat.rules adr
    let account := devm.getAcct adr
    let codehash : B256 :=
      if account.Empty then 0
      else ByteArray.keccak 0 account.code.size account.code
    devm.push codehash
  -- `environment.py` `self_balance`: `charge_gas(LOW)`, then `get_account`
  -- on the current target -- recorded for EIP-7928 -- then the push.
  | .selfbalance => do
    let devm ← chargeGas gLow devm
    (devm.balReadAccount sevm.benvStat.rules sevm.currentTarget).push
      (devm.getBal sevm.currentTarget)
  | .chainid => pushItem sevm.benvStat.chainId.toB256 gBase devm
  | .number => pushItem sevm.benvStat.number.toB256 gBase devm
  | .timestamp => pushItem sevm.benvStat.time gBase devm
  | .gaslimit => pushItem sevm.benvStat.blockGasLimit.toB256 gBase devm
  | .prevrandao => pushItem sevm.benvStat.prevRandao gBase devm
  | .coinbase => pushItem sevm.benvStat.coinbase.toB256 gBase devm
  | .msize => pushItem devm.memory.size.toB256 gBase devm
  | .mload => do
    let ⟨start_index, devm⟩ ← devm.popToNat
    let extend_memory_cost := devm.extCost [⟨start_index, 32⟩]
    let devm ← chargeGas (gVerylow + extend_memory_cost) devm
    let ⟨value, devm⟩ := devm.memRead start_index 32
    devm.push (Bytes.toB256 value)
  | .mstore => do
    let ⟨start_index, devm⟩ ← devm.popToNat
    let ⟨value, devm⟩ ← devm.pop
    let extend_memory_cost := devm.extCost [⟨start_index, 32⟩]
    let devm ← chargeGas (gVerylow + extend_memory_cost) devm
    .ok <| devm.memWrite start_index value.toBytes
  | .mstore8 => do
    let ⟨start_index, devm⟩ ← devm.popToNat
    let ⟨value, devm⟩ ← devm.pop
    let extend_memory_cost := devm.extCost [⟨start_index, 1⟩]
    let devm ← chargeGas (gVerylow + extend_memory_cost) devm
    .ok <| devm.memWrite start_index [value.2.2.toUInt8]
  | .gas => do
    let devm ← chargeGas gBase devm
    devm.push devm.gasLeft.toB256
  | .eq => applyBinary .eqCheck gVerylow devm
  | .lt => applyBinary .ltCheck gVerylow devm
  | .gt => applyBinary .gtCheck gVerylow devm
  | .slt => applyBinary .sltCheck gVerylow devm
  | .sgt => applyBinary .sgtCheck gVerylow devm
  | .iszero => applyUnary (.eqCheck · 0) gVerylow devm
  | .not => applyUnary (~~~ ·) gVerylow devm
  | .and => applyBinary B256.and gVerylow devm
  | .or => applyBinary B256.or gVerylow devm
  | .xor => applyBinary B256.xor gVerylow devm
  | .signextend => applyBinary B256.signext gLow devm
  | .pop => (devm.pop <&> Prod.snd) >>= chargeGas gBase
  | .byte =>
    applyBinary (λ x y => (List.getD y.toBytes x.toNat 0).toB256) gVerylow devm
  | .shl => applyBinary (fun x y => y <<< x.toNat) gVerylow devm
  | .shr => applyBinary (fun x y => y >>> x.toNat) gVerylow devm
  | .sar => applyBinary (fun x y => B256.arithShiftRight y x.toNat) gVerylow devm
  | .clz =>
    -- The availability check comes before the pop, so under rules without
    -- EIP-7939 a `CLZ` byte behaves exactly like any other undefined opcode:
    -- an invalid instruction regardless of what the stack holds.
    if sevm.benvStat.rules.op.clz then
      applyUnary (fun x => (B256.leadingZeros x).toB256) gLow devm
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  | .keccak256 => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let word_gas_cost := gasKeccak256Word * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (gKeccak256 + word_gas_cost + extend_memory_cost) devm
    let ⟨arg, devm⟩ := devm.memRead memory_start_index size
    devm.push arg.keccak
  | .sub => applyBinary (· - ·) gVerylow devm
  | .mul => applyBinary (· * ·) gLow devm
  | .exp => do
    let ⟨base, devm⟩ ← devm.pop
    let ⟨exponent, devm⟩ ← devm.pop
    let devm ← chargeGas (gExp + (gExpbyte * exponent.bytecount)) devm
    devm.push (B256.bexp base exponent)
  | .div => applyBinary (· / ·) gLow devm
  | .sdiv => applyBinary B256.sdiv gLow devm
  | .mod => applyBinary (· % ·) gLow devm
  | .smod => applyBinary B256.smod gLow devm
  | .add => applyBinary (· + ·) gVerylow devm
  | .addmod => applyTernary B256.addmod gMid devm
  | .mulmod => applyTernary B256.mulmod gMid devm
  | .swap n => do
    let devm ← chargeGas gVerylow devm
    match List.swap devm.stack n with
    | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
    | some stack => .ok (devm.withStack stack)
  -- `vm/instructions/block.py` `slot_number`: `charge_gas(OPCODE_SLOTNUM)`,
  -- where `OPCODE_SLOTNUM = BASE`, then push `U256(block_env.slot_number)`.
  -- The availability check comes first, exactly as for `CLZ`: under rules
  -- without EIP-7843 the byte is an undefined instruction.
  | .slotnum =>
    if sevm.benvStat.rules.op.slotnum then
      pushItem sevm.benvStat.slotNumber.toNat.toB256 gBase devm
    else
      .error ⟨.halt (.invalidOpcode .none), devm⟩
  | .dup n => do
    let devm ← chargeGas gVerylow devm
    match devm.stack[n]? with
    | none => .error ⟨.halt (.stackUnderflow .none), devm⟩
    | some word => devm.push word
  | .sload => do
    let ⟨key, devm⟩ ← devm.pop
    let ct := sevm.currentTarget
    let devm ←
      if ⟨ct, key⟩ ∈ devm.accessedStorageKeys then
        chargeGas gasWarmAccess devm
      else
        chargeGas gasColdSload
          (addAccessedStorageKey devm ct key)
    -- `get_storage` after the charge (EIP-7928).
    let devm := devm.balReadStorage sevm.benvStat.rules ct key
    devm.push (devm.getStorVal ct key)
  | .tload => do
    let ⟨key, devm⟩ ← devm.pop
    pushItem (devm.getTransVal sevm.currentTarget key) gasWarmAccess devm
  | .pc => pushItem pc.toB256 gBase devm
  -- `vm/instructions/storage.py` `sstore`. The two shapes differ in more than
  -- numbers, so this is a `match` on the switch rather than a schedule read:
  -- Amsterdam moves the static check ahead of the pops, replaces the EIP-2200
  -- stipend sentry with an explicit `check_gas`, re-derives the charge as
  -- access plus `STORAGE_WRITE`, and moves the state creation into the second
  -- dimension. Under `none` the body below is the body it has always been.
  | .sstore =>
    match sevm.benvStat.rules.stateGas with
    | none => do
      let ⟨key, devm⟩ ← devm.pop
      let ⟨new_value, devm⟩ ← devm.pop
      .assert
        (gCallStipend < devm.gasLeft)
        ⟨.halt (.outOfGas .none), devm⟩
      let ct := sevm.currentTarget
      let original_value := getOrigStorVal sevm ct key
      -- `get_storage_original` records nothing; `get_storage` records the
      -- slot (EIP-7928).
      let devm := devm.balReadStorage sevm.benvStat.rules ct key
      let current_value := devm.getStorVal ct key
      let ⟨devm, gasCost2⟩ ← .ok <|
        if ⟨ct, key⟩ ∉ devm.accessedStorageKeys then
          ( ⟨ addAccessedStorageKey devm ct key,
              gasColdSload ⟩ : Devm × Nat )
        else
          ⟨devm, 0⟩
      let gasCost3 ← .ok <|
        if original_value = current_value ∧ current_value ≠ new_value then
          if original_value = 0 then
            gasCost2 + gasStorageSet
          else
            gasCost2 + (gasStorageUpdate - gasColdSload)
        else
          gasCost2 + gasWarmAccess
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
      let accessGas := if cold then gasColdSload else gasWarmAccess
      .assert
        (max accessGas (gCallStipend + 1) ≤ devm.gasLeft)
        ⟨.halt (.outOfGas .none), devm⟩
      -- STATE ACCESS. Only now is the slot read, and only now is it warmed.
      let devm := if cold then addAccessedStorageKey devm ct key else devm
      let original_value := getOrigStorVal sevm ct key
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
  | .tstore =>
    match sevm.benvStat.rules.stateGas with
    | none => do
      let ⟨key, devm⟩ ← devm.pop
      let ⟨new_value, devm⟩ ← devm.pop
      let devm ← chargeGas gasWarmAccess devm
      assertDynamic sevm devm
      .ok (devm.setTransVal sevm.currentTarget key new_value)
    | some _ => do
      -- `storage.py.tstore` at the pin: static execution is rejected before
      -- stack access or charging, so failure preserves both stack and gas.
      assertDynamic sevm devm
      let ⟨key, devm⟩ ← devm.pop
      let ⟨new_value, devm⟩ ← devm.pop
      let devm ← chargeGas gasWarmAccess devm
      .ok (devm.setTransVal sevm.currentTarget key new_value)
  | .mcopy => do
    let ⟨destination, devm⟩ ← devm.popToNat
    let ⟨source, devm⟩ ← devm.popToNat
    let ⟨length, devm⟩ ← devm.popToNat
    let words := ceilDiv length 32
    let copy_gas_cost := gasCopy * words
    let extend_memory_cost :=
      devm.extCost [⟨source, length⟩, ⟨destination, length⟩]
    let devm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) devm
    let ⟨value, devm⟩ := devm.memRead source length
    .ok (devm.memWrite destination value)
  | .log n => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let ⟨topics, devm⟩ ← devm.popN n
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ←
      chargeGas
        (gLog + (gLogdata * size) + (gLogtopic * n) + extend_memory_cost)
        devm
    assertDynamic sevm devm
    let ⟨data, devm⟩ := devm.memRead memory_start_index size
    let log : Log := ⟨sevm.currentTarget, topics, data⟩
    .ok (devm.addLog log)
  | .blockhash => do
    let ⟨blockNumberWord, devm⟩ ← devm.pop
    let blockNumber := blockNumberWord.toNat
    let devm ← chargeGas gBlockhash devm
    let maxBlockNumber := blockNumber + 256
    let hash : B256 :=
      if sevm.benvStat.number ≤ blockNumber ∨ maxBlockNumber < sevm.benvStat.number
      then 0
      else
        sevm.benvStat.blockHashes.getD
          (sevm.benvStat.blockHashes.length - (sevm.benvStat.number - blockNumber))
          0
    devm.push hash

def Rinst.run (evm : Evm) := Rinst.runCore evm.pc evm.dyna evm.sta

instance : Inhabited BenvStat := ⟨
  {
    rules := pragueRules
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

-- Regression for the transaction-scoped `origState` reset (finding 3.8). Slot
-- `(a, k)` already holds a nonzero value in the block prestate. The first
-- transaction sees that prestate value as its original value and overwrites the
-- slot; the second must then see the *first transaction's output* -- its own
-- input -- as the original value. Reusing the block prestate here is what made
-- `SSTORE` charge a dirty-update 100 rather than a clean-update 2900, the
-- 2,800-gas deficit of `extcodehashEmptySuicide`.
private def origStateRegressionOrigVals : B256 × B256 :=
  let a : Adr := (0x5678 : Adr)
  let k : B256 := Nat.toB256 7
  let prestate : State := State.setStorVal .empty a k (Nat.toB256 11)
  let benv0 : Benv := {(default : Benv) with state := prestate}
  -- transaction 1: open the boundary, read the original value, write the slot
  let benv1 : Benv := benv0.beginTransaction
  let orig1 : B256 := (benv1.stat.origState.get a).stor.get k
  let benv1 : Benv := benv1.setStorVal a k (Nat.toB256 22)
  -- transaction 2: open the boundary, read the original value
  let benv2 : Benv := benv1.beginTransaction
  let orig2 : B256 := (benv2.stat.origState.get a).stor.get k
  ⟨orig1, orig2⟩

#guard origStateRegressionOrigVals = ⟨Nat.toB256 11, Nat.toB256 22⟩

-- The same slot, with the boundary opened only once per block, is the defect:
-- the second transaction would have kept reading the block prestate value 11.
#guard origStateRegressionOrigVals.2 ≠ origStateRegressionOrigVals.1

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

-- EIP-7939 `CLZ` guards.

-- The counted quantity is `256 - x.bit_length()`, so every limb boundary and
-- both extremes are pinned rather than left to the fixture corpus.
#guard B256.leadingZeros (Nat.toB256 0) = 256
#guard B256.leadingZeros (Nat.toB256 1) = 255
#guard B256.leadingZeros (Nat.toB256 2) = 254
#guard B256.leadingZeros (Nat.toB256 3) = 254
#guard B256.leadingZeros (Nat.toB256 255) = 248
#guard B256.leadingZeros (Nat.toB256 256) = 247
#guard B256.leadingZeros (Nat.toB256 (2 ^ 63)) = 192
#guard B256.leadingZeros (Nat.toB256 (2 ^ 64)) = 191
#guard B256.leadingZeros (Nat.toB256 (2 ^ 127)) = 128
#guard B256.leadingZeros (Nat.toB256 (2 ^ 128)) = 127
#guard B256.leadingZeros (Nat.toB256 (2 ^ 191)) = 64
#guard B256.leadingZeros (Nat.toB256 (2 ^ 192)) = 63
#guard B256.leadingZeros (Nat.toB256 (2 ^ 255)) = 0
#guard B256.leadingZeros B256.max = 0
-- A power of two and the all-ones word below it are the two words with the
-- same bit length, so they must count the same number of leading zeros.
#guard (List.range 256).all
  (fun n => B256.leadingZeros (Nat.toB256 (2 ^ n)) = 255 - n)
#guard (List.range 256).all
  (fun n => B256.leadingZeros (Nat.toB256 (2 ^ (n + 1) - 1)) = 255 - n)

private def guardSevmWith (rules : ForkRules) : Sevm :=
  { (default : Sevm) with
    benvStat := { (default : BenvStat) with rules := rules } }

private def guardClz (rules : ForkRules) (gasLeft : Nat) (stack : List B256) :
    Execution :=
  Rinst.runCore 0 (((default : Devm).withGasLeft gasLeft).withStack stack)
    (guardSevmWith rules) .clz

private def guardClzErr (e : Execution) : String :=
  match e with
  | .error ⟨err, _⟩ => err.render
  | .ok _ => "unexpected success"

-- Under Osaka the opcode pops one word, charges `LOW`, and pushes the count.
#guard (guardClz osakaRules 100 [0]).toOption.map Devm.stack
  = some [Nat.toB256 256]
#guard (guardClz osakaRules 100 [1]).toOption.map Devm.stack
  = some [Nat.toB256 255]
#guard (guardClz osakaRules 100 [B256.max]).toOption.map Devm.stack
  = some [Nat.toB256 0]
#guard (guardClz osakaRules 100 [0]).toOption.map Devm.gasLeft = some (100 - gLow)
#guard gLow = 5

-- The rest of the stack is untouched and only the top word is consumed.
#guard (guardClz osakaRules 100 [0, 7]).toOption.map Devm.stack
  = some [Nat.toB256 256, Nat.toB256 7]

-- Under Prague 0x1E is an unassigned byte, so it is an invalid instruction
-- whatever the stack and gas hold -- not a stack or gas failure, and not a
-- silent success.
#guard guardClzErr (guardClz pragueRules 100 [0]) = "InvalidOpcode"
#guard guardClzErr (guardClz pragueRules 100 []) = "InvalidOpcode"
#guard guardClzErr (guardClz pragueRules 0 [0]) = "InvalidOpcode"

-- EIP-7843 `SLOTNUM` (goal C, G3): under Amsterdam it charges `BASE` (2) and
-- pushes the block environment's slot number zero-extended to 256 bits; under
-- BPO2 the byte 0x4B is unassigned, so it is an invalid instruction whatever
-- the stack and gas hold.
private def guardSlotnum (rules : ForkRules) (slot : UInt64) (gasLeft : Nat)
    (stack : List B256) : Execution :=
  Rinst.runCore 0 (((default : Devm).withGasLeft gasLeft).withStack stack)
    { guardSevmWith rules with
      benvStat := { (default : BenvStat) with rules := rules, slotNumber := slot } }
    .slotnum

#guard gBase = 2
#guard (guardSlotnum amsterdamRules 12345 100 []).toOption.map Devm.stack
  = some [Nat.toB256 12345]
#guard (guardSlotnum amsterdamRules 12345 100 []).toOption.map Devm.gasLeft
  = some (100 - gBase)
#guard (guardSlotnum amsterdamRules (2 ^ 64 - 1) 100 [7]).toOption.map Devm.stack
  = some [Nat.toB256 (2 ^ 64 - 1), Nat.toB256 7]
#guard (guardSlotnum amsterdamRules 0 2 []).toOption.map Devm.gasLeft = some 0
#guard guardClzErr (guardSlotnum amsterdamRules 12345 1 []) = "OutOfGasError"
#guard guardClzErr (guardSlotnum bpo2Rules 12345 100 []) = "InvalidOpcode"
#guard guardClzErr (guardSlotnum bpo2Rules 12345 0 []) = "InvalidOpcode"
#guard guardClzErr (guardSlotnum pragueRules 0 100 [1]) = "InvalidOpcode"
-- `UInt8.toRinst` decodes 0x4B at every fork and round-trips its mnemonic.
#guard (0x4B : UInt8).toRinst matches some .slotnum
#guard ((0x4B : UInt8).toRinst.map Rinst.toString) = some "SLOTNUM"
#guard (0x4B : UInt8).toInstType matches .R

-- Under Osaka the same two degenerate inputs reach the real failures instead.
#guard guardClzErr (guardClz osakaRules 100 []) = "StackUnderflowError"
#guard guardClzErr (guardClz osakaRules (gLow - 1) [0]) = "OutOfGasError"
#guard (guardClz osakaRules gLow [0]).toOption.map Devm.gasLeft = some 0

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
    if cd[k] = (Jinst.toUInt8 .jumpdest)
    then noPushBefore cd k 32
    else false
  else false

-- P0.6 item 2: an out-of-range jump destination is *semantically* unjumpable.
-- The read is total and proof-indexed; out of range means `false`, never a
-- host-level partial read. In range, behaviour is unchanged.
#guard jumpable ⟨#[0x5B]⟩ 0 = true
#guard jumpable ⟨#[0x5B]⟩ 1 = false
#guard jumpable ⟨#[0x5B]⟩ (2 ^ 64) = false
#guard jumpable ⟨#[]⟩ 0 = false

--------------- EIP-8024 AND THE JUMP-DESTINATION SET ---------------

-- The pinned `get_valid_jump_destinations` (`vm/runtime.py` at Amsterdam) is
-- *not* the pre-Amsterdam walk: at a `DUPN`, `SWAPN` or `EXCHANGE` byte it
-- skips the following immediate unless that immediate lies in the opcode's
-- forbidden range, in which case the byte stays at an instruction boundary.
-- So "the jump-destination set is unchanged" is a theorem to discharge, not an
-- observation, and here it is: both walks are written out as forward passes
-- listing every destination at or after `pc`, and `pinnedJumpDestsFrom_eq_legacy`
-- proves them equal on every byte array. The argument is exactly that both
-- forbidden ranges (`0x5B–0x7F` and `0x52–0x7F`) contain `JUMPDEST` (0x5B) and
-- every `PUSH1`–`PUSH32` byte (`0x60–0x7F`): an *accepted* immediate is
-- therefore never a destination and never a push, so the legacy walk, which
-- steps onto it, adds nothing and steps off again, landing where the pinned
-- walk landed in one step; a *forbidden* immediate is deliberately not
-- skipped, so both walks step onto it alike.
--
-- `jumpable`/`noPushBefore` -- the backward scan the interpreter runs -- keep
-- their definitions. The programme's random-blob control (`scripts/check-jumpdest.sh`)
-- compares `jumpable` against `pinnedJumpDestsFrom` on 64 KiB blobs, as the
-- falsifier for this theorem's *statement*; the theorem is what makes the
-- unchanged definitions correct on adversarial code, not just sampled code.

/-- The pinned Amsterdam `get_valid_jump_destinations`, from `pc`: `JUMPDEST`
is a destination; `PUSH1`–`PUSH32` skip their data; `DUPN`/`SWAPN` skip their
immediate unless it is in `0x5B–0x7F`, `EXCHANGE` unless it is in `0x52–0x7F`;
every other byte -- `PUSH0` and undefined opcodes included -- advances one.
An immediate past the end of code reads as `0`, which is accepted, so the
last-byte case skips past the end exactly as the pinned `pc + 1 < len(code)`
guard does. -/
def pinnedJumpDestsFrom (cd : ByteArray) (pc : Nat) : List Nat :=
  if h : pc < cd.size then
    let b := cd[pc]
    if b = 0x5B then pc :: pinnedJumpDestsFrom cd (pc + 1)
    else if 0x60 ≤ b ∧ b ≤ 0x7F then pinnedJumpDestsFrom cd (pc + (b.toNat - 0x5F) + 1)
    else if b = 0xE6 ∨ b = 0xE7 then
      if 0x5B ≤ cd.byteD (pc + 1) ∧ cd.byteD (pc + 1) ≤ 0x7F then
        pinnedJumpDestsFrom cd (pc + 1)
      else pinnedJumpDestsFrom cd (pc + 2)
    else if b = 0xE8 then
      if 0x52 ≤ cd.byteD (pc + 1) ∧ cd.byteD (pc + 1) ≤ 0x7F then
        pinnedJumpDestsFrom cd (pc + 1)
      else pinnedJumpDestsFrom cd (pc + 2)
    else pinnedJumpDestsFrom cd (pc + 1)
  else []
termination_by cd.size - pc
decreasing_by all_goals omega

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
    rw [if_neg hj, if_neg hp]
  · rename_i h
    rw [legacyJumpDestsFrom]
    rw [dif_neg (by omega)]

/-- Appendix D of goal C: the pinned Amsterdam walk and the pre-Amsterdam walk
compute the same destinations on every byte array. -/
theorem pinnedJumpDestsFrom_eq_legacy (cd : ByteArray) (pc : Nat) :
    pinnedJumpDestsFrom cd pc = legacyJumpDestsFrom cd pc := by
  rw [pinnedJumpDestsFrom, legacyJumpDestsFrom]
  split
  · rename_i h
    -- An immediate outside a forbidden range `[lo, 0x7F]` with `lo ≤ 0x5B` is
    -- neither `JUMPDEST` nor a `PUSH1`–`PUSH32` byte, so the legacy walk steps
    -- off it without adding a destination.
    have key : ∀ lo : UInt8, lo ≤ 0x5B →
        ¬ (lo ≤ cd.byteD (pc + 1) ∧ cd.byteD (pc + 1) ≤ 0x7F) →
        legacyJumpDestsFrom cd (pc + 1) = legacyJumpDestsFrom cd (pc + 2) := by
      intro lo hlo hnot
      apply legacyJumpDestsFrom_skip
      · intro heq
        apply hnot
        rw [heq]
        exact ⟨hlo, by decide⟩
      · intro ⟨h1, h2⟩
        apply hnot
        exact ⟨UInt8.le_trans hlo (UInt8.le_trans (by decide) h1), h2⟩
    dsimp only
    split_ifs <;> first
      | exact congrArg _ (pinnedJumpDestsFrom_eq_legacy cd (pc + 1))
      | exact pinnedJumpDestsFrom_eq_legacy cd (pc + 1)
      | exact pinnedJumpDestsFrom_eq_legacy cd _
      | (rw [pinnedJumpDestsFrom_eq_legacy cd (pc + 2)]
         exact (key 0x5B (by decide) (by assumption)).symm)
      | (rw [pinnedJumpDestsFrom_eq_legacy cd (pc + 2)]
         exact (key 0x52 (by decide) (by assumption)).symm)
  · rfl
termination_by cd.size - pc
decreasing_by all_goals omega

-- The guard points of Appendix D, on both walks and on `jumpable`.
-- `[0xE6, 0x5B]` / `[0xE8, 0x5B]`: a forbidden immediate is not skipped, so
-- `1` is a destination; `[0xE6, 0x80, 0x5B]` / `[0xE8, 0x00, 0x5B]`: an
-- accepted immediate is skipped, `2` is a destination and `1` is not.
#guard pinnedJumpDestsFrom ⟨#[0xE6, 0x5B]⟩ 0 = [1]
#guard pinnedJumpDestsFrom ⟨#[0xE8, 0x5B]⟩ 0 = [1]
#guard pinnedJumpDestsFrom ⟨#[0xE6, 0x80, 0x5B]⟩ 0 = [2]
#guard pinnedJumpDestsFrom ⟨#[0xE8, 0x00, 0x5B]⟩ 0 = [2]
-- 0x7F is forbidden, so it is not skipped -- and it is PUSH32, which eats the
-- JUMPDEST behind it: the set is empty on both walks and for `jumpable`.
#guard pinnedJumpDestsFrom ⟨#[0xE7, 0x7F, 0x5B]⟩ 0 = []
#guard (List.range 3).filter (jumpable ⟨#[0xE7, 0x7F, 0x5B]⟩) = []
#guard pinnedJumpDestsFrom ⟨#[0xE7, 0x5B, 0x5B]⟩ 0 = [1, 2]
#guard pinnedJumpDestsFrom ⟨#[0x60, 0x5B, 0x5B]⟩ 0 = [2]
#guard pinnedJumpDestsFrom ⟨#[0xE6]⟩ 0 = []
#guard jumpable ⟨#[0xE6, 0x5B]⟩ 1 = true
#guard jumpable ⟨#[0xE8, 0x5B]⟩ 1 = true
#guard jumpable ⟨#[0xE6, 0x80, 0x5B]⟩ 2 = true
#guard jumpable ⟨#[0xE6, 0x80, 0x5B]⟩ 1 = false
#guard jumpable ⟨#[0xE8, 0x00, 0x5B]⟩ 2 = true
#guard jumpable ⟨#[0xE8, 0x00, 0x5B]⟩ 1 = false
#guard (List.range 3).filter (jumpable ⟨#[0xE7, 0x5B, 0x5B]⟩) = [1, 2]
#guard (List.range 3).filter (jumpable ⟨#[0x60, 0x5B, 0x5B]⟩) = [2]

def Jinst.runCore (pc : Nat) (devm : Devm) (sevm : Sevm) :
    Jinst → Except (EvmError × Devm) (Nat × Devm)
  | .jumpdest => do
    let devm' ← chargeGas gJumpdest devm
    .ok ⟨pc + 1, devm'⟩
  | .jump => do
    let ⟨jump_dest, devm'⟩ ← devm.pop
    let devm'' ← chargeGas gMid devm'
    .assert
      (jumpable sevm.code jump_dest.toNat)
      ⟨.halt (.invalidJumpDest .none), devm''⟩
    .ok ⟨jump_dest.toNat, devm''⟩
  | .jumpi => do
    let ⟨dest, devm'⟩ ← devm.pop
    let ⟨cond, devm''⟩ ← devm'.pop
    let devm''' ← chargeGas gHigh devm''
    let pc' : Nat ←
      if cond = 0
      then .ok <| pc + 1
      else
        .assert
          (jumpable sevm.code dest.toNat)
          ⟨.halt (.invalidJumpDest .none), devm'''⟩
        .ok dest.toNat
    .ok ⟨pc', devm'''⟩

def Jinst.run (evm : Evm) (j : Jinst) : Except (EvmError × Devm) (Nat × Devm) :=
  Jinst.runCore evm.pc evm.dyna evm.sta j

def State.bal (w : State) (a : Adr) : B256 := (w.get a).bal

def State.setBal (st : State) (adr : Adr) (val : B256) : State :=
  st.set adr <| (st.get adr).withBal val

def State.addBal (st : State) (adr : Adr) (val : B256) : State :=
  st.setBal adr <| (st.bal adr + val)


def State.subBal (st : State) (adr : Adr) (val : B256) : Option State :=
  if st.bal adr < val
  then .none
  else st.setBal adr (st.bal adr - val)

def Benv.setBal (benv : Benv) (adr : Adr) (val : B256) : Benv :=
  {benv with state := benv.state.setBal adr val}

def Benv.subBal (benv : Benv) (adr : Adr) (val : B256) : Option Benv := do
  let wor ← benv.state.subBal adr val
  some <| benv.withState wor

def Benv.addBal (benv : Benv) (adr : Adr) (val : B256) : Benv :=
  benv.withState (benv.state.addBal adr val)

def Devm.setBal (devm : Devm) (adr : Adr) (val : B256) : Devm :=
  devm.withState (devm.state.setBal adr val)

def Devm.subBal (devm : Devm) (adr : Adr) (val : B256) : Option Devm := do
  let state ← devm.state.subBal adr val
  some <| devm.withState state

def Devm.addBal (devm : Devm) (adr : Adr) (val : B256) : Devm :=
  devm.withState (devm.state.addBal adr val)

def Linst.run (sevm : Sevm) (devm : Devm) :
    Linst → Except (EvmError × Devm) Devm
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
      let donorBal ← .ok (devm.getAcct sevm.currentTarget).bal
      let ⟨devm, gasCost2⟩ ← .ok <|
        if donee ∉ devm.accessedAddresses
          then
            ( ⟨ addAccessedAddress devm donee,
                gasSelfDestruct + sevm.benvStat.rules.gas.coldAccountAccess ⟩ : Devm × Nat )
          else
            ⟨devm, gasSelfDestruct⟩
      let gasCost3 ← .ok <|
        if (devm.getAcct donee).Empty ∧ donorBal ≠ 0 then
          gasCost2 + gasSelfDestructNewAccount
        else
          gasCost2
      let devm ← chargeGas gasCost3 devm
      assertDynamic sevm devm
      let devm ←
        (devm.subBal donor donorBal).toExcept
          ⟨.internal (.invariant (.text "InsufficientBalanceError")), devm⟩
      let devm ← .ok <| devm.addBal donee donorBal
      if donor ∈ devm.createdAccounts then
        .ok (addAccountToDelete (devm.setBal donor 0) donor)
      else
        .ok devm
    | some state => do
      assertDynamic sevm devm
      let donor := sevm.currentTarget
      let ⟨donee, devm⟩ ← devm.popToAdr
      -- GAS (state-independent), checked before the beneficiary is warmed.
      let cold := donee ∉ devm.accessedAddresses
      let gasCost :=
        gasSelfDestruct +
          (if cold then sevm.benvStat.rules.gas.coldAccountAccess else 0)
      .assert (gasCost ≤ devm.gasLeft) ⟨.halt (.outOfGas .none), devm⟩
      -- STATE ACCESS: the beneficiary is warmed, then `is_account_alive` reads
      -- it and `get_account` reads the originator (EIP-7928), before the
      -- charges below.
      let devm := if cold then addAccessedAddress devm donee else devm
      let devm := (devm.balReadAccount sevm.benvStat.rules donee).balReadAccount
        sevm.benvStat.rules donor
      let donorBal := (devm.getAcct donor).bal
      -- STATE GAS. A sweep that will create the beneficiary pays the account
      -- write and the creation. Execution gas before state gas.
      let creating := (devm.getAcct donee).Empty ∧ donorBal ≠ 0
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
  (cs : Nat := gCallStipend) : Nat × Nat :=
  let call_stipend : Nat := if value = 0 then 0 else cs
  if gas_left < extra_gas + memory_cost
  then ⟨gas + extra_gas, gas + call_stipend⟩
  else
    let gas' := min gas (except64th (gas_left - memory_cost - extra_gas))
    ⟨gas' + extra_gas, gas' + call_stipend⟩

def incorporateChildOnError (parent child : Devm) (returnData : Bytes) : Devm :=
  let parent := parent.setMach
    {parent.mach with gasLeft := parent.gasLeft + child.gasLeft}
  let parent := parent.setMeta
    {parent.meta with
      createdAccounts := child.createdAccounts
      returnData := returnData
      -- EIP-7928: a failed child's reads survive (the pinned snapshot shares
      -- the read sets by reference and rolls back only the writes).
      accountReads := parent.meta.accountReads.union child.meta.accountReads
      storageReads := parent.meta.storageReads.union child.meta.storageReads}
  parent.setWorld
    {parent.world with
      state := child.state
      transientStorage := child.transientStorage}

def incorporateChildOnSuccess (parent child : Devm) (returnData : Bytes) : Devm :=
  let parent := parent.setMach
    {parent.mach with gasLeft := parent.gasLeft + child.gasLeft}
  let parent := parent.setMeta
    {parent.meta with
      createdAccounts := child.createdAccounts
      logs := parent.logs ++ child.logs
      refundCounter := parent.refundCounter + child.refundCounter
      accountsToDelete := parent.accountsToDelete.union child.accountsToDelete
      returnData := returnData
      accessedAddresses := parent.accessedAddresses.union child.accessedAddresses
      accessedStorageKeys := parent.accessedStorageKeys.union child.accessedStorageKeys
      accountReads := parent.meta.accountReads.union child.meta.accountReads
      storageReads := parent.meta.storageReads.union child.meta.storageReads}
  parent.setWorld
    {parent.world with
      state := child.state
      transientStorage := child.transientStorage}

/-! ### Child incorporation under the two-dimensional meter

Upstream's `incorporate_child` is one function with an `if` inside; Jaune's is
two functions chosen by the caller, and the Amsterdam siblings keep that shape
so that `Resume.run`'s two branches stay the two branches they are.

The rule the pin states, and what these transcribe: **gas returns to the parent
regardless of the child's fate**, because a failed child arrives already
settled -- rolled back to its baseline, its spill refilled, its refunds
discarded -- so absorbing its meter unconditionally reclaims exactly what it
gives back. Everything else -- logs, scheduled self-destructs, warmed access
sets -- survives only on success, dying with the reverted state. A successful
merge then ends with `repayStateGasSpill`, the rule new at `7341820` (#3478).

Committed spill is not absorbed, because a child never has any: only the top
frame commits, and it commits after `set_delegation`, which no child runs.
Upstream states that as an `assert`; `Resume.run` enforces the same invariant at
both actual Amsterdam incorporation sites, so a malformed child becomes a
typed internal invariant error instead of silently losing gas. -/

/-- The invariant every successfully settled Amsterdam child must satisfy
before its meter can be incorporated into its parent. -/
def Devm.AmsterdamChildUncommitted (child : Devm) : Prop :=
  child.mach.stateGas.committedSpill = 0

instance {child : Devm} : Decidable child.AmsterdamChildUncommitted := by
  unfold Devm.AmsterdamChildUncommitted
  infer_instance

/-- The additional settlement facts required before incorporating a failed
Amsterdam child: rollback has restored the reservoir baseline, cleared the
outstanding spill, and discarded the child's refund counter. -/
def Devm.AmsterdamFailedChildSettled (child : Devm) : Prop :=
  child.AmsterdamChildUncommitted ∧
    child.mach.stateGas.spilled = 0 ∧
    child.refundCounter = 0 ∧
    child.stateGasLeft = child.mach.stateGas.baseline

instance {child : Devm} : Decidable child.AmsterdamFailedChildSettled := by
  unfold Devm.AmsterdamFailedChildSettled
  infer_instance

/-- `incorporate_child` on a failed child, under `stateGas = some _`.

The child's execution gas, reservoir and outstanding spill all come back; so do
its refunds, which the child's own frame settlement has already zeroed. Nothing
it accumulated survives. -/
def incorporateChildAmsterdamOnError (parent child : Devm) (returnData : Bytes) :
    Devm :=
  let parent := parent.setMach
    {parent.mach with
      gasLeft := parent.gasLeft + child.gasLeft
      stateGas := {parent.mach.stateGas with
        left := parent.mach.stateGas.left + child.mach.stateGas.left
        spilled := parent.mach.stateGas.spilled + child.mach.stateGas.spilled}}
  let parent := parent.setMeta
    {parent.meta with
      createdAccounts := child.createdAccounts
      refundCounter := parent.refundCounter + child.refundCounter
      returnData := returnData
      -- EIP-7928: a failed child's reads survive (the pinned snapshot shares
      -- the read sets by reference and rolls back only the writes).
      accountReads := parent.meta.accountReads.union child.meta.accountReads
      storageReads := parent.meta.storageReads.union child.meta.storageReads}
  parent.setWorld
    {parent.world with
      state := child.state
      transientStorage := child.transientStorage}

/-- `incorporate_child` on a successful child, under `stateGas = some _`.

The same unconditional absorption, then the merged meter repays `gasLeft` from
the reservoir up to the spill still outstanding: a refund can land in a
different frame than the charge it undoes, and this merge is where the claim
and the credit first share one meter. -/
def incorporateChildAmsterdamOnSuccess (parent child : Devm) (returnData : Bytes) :
    Devm :=
  let parent := parent.setMach
    ((({parent.mach with
        gasLeft := parent.gasLeft + child.gasLeft
        stateGas := {parent.mach.stateGas with
          left := parent.mach.stateGas.left + child.mach.stateGas.left
          spilled :=
            parent.mach.stateGas.spilled + child.mach.stateGas.spilled}}
      : Mach)).repayStateGasSpill)
  let parent := parent.setMeta
    {parent.meta with
      createdAccounts := child.createdAccounts
      logs := parent.logs ++ child.logs
      refundCounter := parent.refundCounter + child.refundCounter
      accountsToDelete := parent.accountsToDelete.union child.accountsToDelete
      returnData := returnData
      accessedAddresses := parent.accessedAddresses.union child.accessedAddresses
      accessedStorageKeys := parent.accessedStorageKeys.union child.accessedStorageKeys
      accountReads := parent.meta.accountReads.union child.meta.accountReads
      storageReads := parent.meta.storageReads.union child.meta.storageReads}
  parent.setWorld
    {parent.world with
      state := child.state
      transientStorage := child.transientStorage}

/-- Absorbing a failed child conserves the measure, up to the committed spill a
child cannot have. -/
theorem incorporateChildAmsterdamOnError_gasMeasure
    (parent child : Devm) (rd : Bytes) :
    (incorporateChildAmsterdamOnError parent child rd).gasMeasure
        + child.mach.stateGas.committedSpill
      = parent.gasMeasure + child.gasMeasure := by
  simp only [incorporateChildAmsterdamOnError, Devm.gasMeasure, Mach.gasMeasure,
    Devm.setMach, Devm.setMeta, Devm.setWorld, Devm.gasLeft]
  omega

/-- The same for a successful child. The repayment moves gas between two pools
the measure adds together, so it cancels. -/
theorem incorporateChildAmsterdamOnSuccess_gasMeasure
    (parent child : Devm) (rd : Bytes) :
    (incorporateChildAmsterdamOnSuccess parent child rd).gasMeasure
        + child.mach.stateGas.committedSpill
      = parent.gasMeasure + child.gasMeasure := by
  simp only [incorporateChildAmsterdamOnSuccess, Mach.repayStateGasSpill,
    Devm.gasMeasure, Mach.gasMeasure, Devm.setMach, Devm.setMeta, Devm.setWorld,
    Devm.gasLeft]
  have h :
      min (parent.mach.stateGas.left + child.mach.stateGas.left)
          (parent.mach.stateGas.spilled + child.mach.stateGas.spilled)
        ≤ parent.mach.stateGas.spilled + child.mach.stateGas.spilled :=
    Nat.min_le_right _ _
  omega

/-- A child that carries no committed spill hands its whole measure back. -/
theorem incorporateChildAmsterdamOnSuccess_gasMeasure_of_child_uncommitted
    {parent child : Devm} {rd : Bytes}
    (h : child.AmsterdamChildUncommitted) :
    (incorporateChildAmsterdamOnSuccess parent child rd).gasMeasure
      = parent.gasMeasure + child.gasMeasure := by
  have e := incorporateChildAmsterdamOnSuccess_gasMeasure parent child rd
  unfold Devm.AmsterdamChildUncommitted at h
  omega

theorem incorporateChildAmsterdamOnError_gasMeasure_of_child_uncommitted
    {parent child : Devm} {rd : Bytes}
    (h : child.AmsterdamChildUncommitted) :
    (incorporateChildAmsterdamOnError parent child rd).gasMeasure
      = parent.gasMeasure + child.gasMeasure := by
  have e := incorporateChildAmsterdamOnError_gasMeasure parent child rd
  unfold Devm.AmsterdamChildUncommitted at h
  omega

/-- The exact conservation equation available at the failed-child
incorporation site after its executable settlement check succeeds. -/
theorem incorporateChildAmsterdamOnError_gasMeasure_of_child_settled
    {parent child : Devm} {rd : Bytes}
    (h : child.AmsterdamFailedChildSettled) :
    (incorporateChildAmsterdamOnError parent child rd).gasMeasure
      = parent.gasMeasure + child.gasMeasure :=
  incorporateChildAmsterdamOnError_gasMeasure_of_child_uncommitted h.1

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

theorem Mach.push_stateGas_eq (x : B256) (mach : Mach) :
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

theorem Mach.pushItem_stateGas_eq (x : B256) (cost : Nat) (mach : Mach) :
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

theorem Mach.applyUnary_stateGas_eq (f : B256 → B256) (cost : Nat) (mach : Mach) :
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

theorem Mach.applyBinary_stateGas_eq (f : B256 → B256 → B256) (cost : Nat)
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

theorem Mach.applyTernary_stateGas_eq (f : B256 → B256 → B256 → B256)
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

theorem Devm.push_stateGasZero (x : B256) {devm : Devm}
    (h : devm.StateGasZero) : (devm.push x).StateGasZero :=
  liftMachExecution_stateGasZero h (Mach.push_stateGas_eq x devm.mach)

theorem pushItem_stateGasZero (x : B256) (cost : Nat) {devm : Devm}
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

theorem applyUnary_stateGasZero (f : B256 → B256) (cost : Nat) {devm : Devm}
    (h : devm.StateGasZero) : (applyUnary f cost devm).StateGasZero :=
  liftMachExecution_stateGasZero h
    (Mach.applyUnary_stateGas_eq f cost devm.mach)

theorem applyBinary_stateGasZero (f : B256 → B256 → B256) (cost : Nat)
    {devm : Devm} (h : devm.StateGasZero) :
    (applyBinary f cost devm).StateGasZero :=
  liftMachExecution_stateGasZero h
    (Mach.applyBinary_stateGas_eq f cost devm.mach)

theorem applyTernary_stateGasZero (f : B256 → B256 → B256 → B256) (cost : Nat)
    {devm : Devm} (h : devm.StateGasZero) :
    (applyTernary f cost devm).StateGasZero :=
  liftMachExecution_stateGasZero h
    (Mach.applyTernary_stateGas_eq f cost devm.mach)

theorem Devm.memRead_stateGasZero {devm : Devm} (index size : Nat)
    (h : devm.StateGasZero) :
    (devm.memRead index size).2.StateGasZero := h

theorem Devm.subBal_stateGasZero {devm devm' : Devm}
    (h : devm.StateGasZero) {adr : Adr} {value : B256}
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
    (adr : Adr) (value : B256) : (devm.addBal adr value).StateGasZero := h

theorem Devm.setBal_stateGasZero {devm : Devm} (h : devm.StateGasZero)
    (adr : Adr) (value : B256) : (devm.setBal adr value).StateGasZero := h

theorem Devm.withRefundCounter_stateGasZero {devm : Devm}
    (h : devm.StateGasZero) (refund : Int) :
    (devm.withRefundCounter refund).StateGasZero := h

theorem addAccountToDelete_stateGasZero {devm : Devm} (h : devm.StateGasZero)
    (adr : Adr) : (addAccountToDelete devm adr).StateGasZero := h

theorem Rinst.balanceCore_stateGas_eq (rules : ForkRules) (world : World)
    (mach : Mach) (view : Meta) :
    Footprint.MachMetaStateGasEq mach (Rinst.balanceCore rules world mach view) := by
  unfold Rinst.balanceCore
  cases hp : mach.pop with
  | error e =>
    have hm := Mach.pop_stateGas_eq mach
    rw [hp] at hm
    simpa [hp, Footprint.StateGasEq, Footprint.MachMetaStateGasEq] using hm
  | ok a =>
    have hm := Mach.pop_stateGas_eq mach
    rw [hp] at hm
    cases hc : a.2.chargeGas (if a.1.toAdr ∈ view.accessedAddresses
        then gasWarmAccess else rules.gas.coldAccountAccess) with
    | error e =>
      have hc' := Mach.chargeGas_stateGas_eq
        (if a.1.toAdr ∈ view.accessedAddresses
          then gasWarmAccess else rules.gas.coldAccountAccess) a.2
      rw [hc] at hc'
      simpa [hp, hc, Footprint.MachMetaStateGasEq] using hc'.trans hm
    | ok b =>
      have hc' := Mach.chargeGas_stateGas_eq
        (if a.1.toAdr ∈ view.accessedAddresses
          then gasWarmAccess else rules.gas.coldAccountAccess) a.2
      rw [hc] at hc'
      have hpush := Mach.push_stateGas_eq (world.state.get a.1.toAdr).bal b.2
      cases hq : b.2.push (world.state.get a.1.toAdr).bal <;> rw [hq] at hpush
      · simpa [hp, hc, hq, Footprint.MachMetaStateGasEq] using
          hpush.trans (hc'.trans hm)
      · simpa [hp, hc, hq, Footprint.MachMetaStateGasEq] using
          hpush.trans (hc'.trans hm)

theorem Rinst.balance_stateGasZero (rules : ForkRules) {devm : Devm}
    (h : devm.StateGasZero) :
    (liftMachMetaWorldExecution (Rinst.balanceCore rules) devm).StateGasZero :=
  liftMachMetaExecution_stateGasZero h
    (Rinst.balanceCore_stateGas_eq rules devm.world devm.mach devm.meta)

/-- Every register instruction preserves a zero meter when the state-gas
switch is absent.  The switch hypothesis rules out only the `SSTORE`
Amsterdam sibling; all other register operations are meter-blind. -/
theorem Rinst.run_stateGasZero {evm : Evm} (h : evm.dyna.StateGasZero)
    (hrules : evm.sta.benvStat.rules.stateGas = none) (r : Rinst) :
    (r.run evm).StateGasZero := by
  unfold Rinst.run
  cases r <;> simp only [Rinst.runCore]
  case iszero | not => exact applyUnary_stateGasZero _ _ h
  case add | mul | sub | div | sdiv | mod | smod | signextend | lt | gt | slt |
      sgt | eq | and | or | xor | byte | shl | shr | sar =>
    exact applyBinary_stateGasZero _ _ h
  case addmod | mulmod => exact applyTernary_stateGasZero _ _ h
  case address | basefee | blobbasefee | origin | caller | callvalue |
      calldatasize | codesize | gasprice | returndatasize |
      chainid | number | timestamp | gaslimit | prevrandao | coinbase | msize |
      pc =>
    exact pushItem_stateGasZero _ _ h
  case selfbalance =>
    exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h)
      fun d hd => Devm.push_stateGasZero _ hd
  case balance => exact Rinst.balance_stateGasZero _ h
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
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h) ?_
    rintro ⟨dest, d1⟩ h1
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h1) ?_
    rintro ⟨src, d2⟩ h2
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero h2) ?_
    rintro ⟨len, d3⟩ h3
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ h3) ?_
    intro d4 h4
    exact Except.stateGasZeroOn_ok (Devm.memRead_stateGasZero src len h4)
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
    split <;>
      exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ ha)
        fun _ hd => Devm.push_stateGasZero _ hd
  case extcodecopy =>
    refine Except.StateGasZeroOn.bind (Devm.popToAdr_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero ha) fun b hb => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hb) fun c hc => ?_
    refine Except.StateGasZeroOn.bind (Devm.popToNat_stateGasZero hc) fun e he => ?_
    split <;>
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
    refine Except.StateGasZeroOn.bind (Devm.popToAdr_stateGasZero h) fun a ha => ?_
    split <;>
      exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ ha)
        fun _ hd => Devm.push_stateGasZero _ hd
  case blockhash =>
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ ha)
      fun _ hd => Devm.push_stateGasZero _ hd
  case blobhash =>
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ ha)
      fun _ hd => Devm.push_stateGasZero _ hd
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
    split <;>
      exact Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ ha)
        fun _ hd => Devm.push_stateGasZero _ hd
  case sstore =>
    rw [hrules]
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
  case tload =>
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    exact pushItem_stateGasZero _ _ ha
  case tstore =>
    rw [hrules]
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero h) fun a ha => ?_
    refine Except.StateGasZeroOn.bind (Devm.pop_stateGasZero ha) fun b hb => ?_
    refine Except.StateGasZeroOn.bind (chargeGas_stateGasZero _ hb) fun d hd => ?_
    refine Except.StateGasZeroOn.bind (Except.stateGasZeroOn_assert hd) fun _ _ => ?_
    exact Except.stateGasZeroOn_ok hd
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

theorem Jinst.run_stateGasZero {evm : Evm} (h : evm.dyna.StateGasZero)
    (j : Jinst) :
    (j.run evm).StateGasZeroOn (fun a => a.2.StateGasZero) := by
  unfold Jinst.run
  cases j <;> simp only [Jinst.runCore]
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

theorem Linst.run_stateGasZero {sevm : Sevm} {devm : Devm}
    (h : devm.StateGasZero) (hrules : sevm.benvStat.rules.stateGas = none)
    (l : Linst) : Execution.StateGasZero (l.run sevm devm) := by
  cases l <;> simp only [Linst.run]
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
    · exact Except.stateGasZeroOn_ok (by split <;> exact h1)
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
        (Except.stateGasZeroOn_ok (Devm.addBal_stateGasZero h6 _ _)) ?_
      intro d5 h7
      split
      · exact Except.stateGasZeroOn_ok
          (addAccountToDelete_stateGasZero (Devm.setBal_stateGasZero h7 _ _) _)
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

/-- Prague's child incorporation cannot break it either: both siblings rebuild
`Mach` from the parent's, leaving `stateGas` alone. -/
theorem incorporateChildOnError_stateGasZero {parent child : Devm} {rd : Bytes}
    (h : parent.StateGasZero) :
    (incorporateChildOnError parent child rd).StateGasZero := h

theorem incorporateChildOnSuccess_stateGasZero {parent child : Devm} {rd : Bytes}
    (h : parent.StateGasZero) :
    (incorporateChildOnSuccess parent child rd).StateGasZero := h

def computeContractAddress (sender : Adr) (nonce : UInt64) : Adr :=
  let LA : Bytes :=
    BLT.toBytes <| .list [.bytes sender.toBytes, .bytes nonce.toBytes.sig]
  (Bytes.keccak LA).toAdr

def create2NewAddress
  (sender : Adr) (salt : B256) (initCode : Bytes): Adr :=
  let LA : Bytes :=
    (0xFF : UInt8) :: (sender.toBytes ++ salt.toBytes ++ initCode.keccak.toBytes)
  (Bytes.keccak LA).toAdr

def State.incrNonce (w : State) (a : Adr) : State :=
  let ac := w.get a
  let ac' : Acct := {ac with nonce := ac.nonce + 1}
  w.set a ac'

def Msg.incrNonce (msg : Msg) (adr : Adr) : Msg :=
  {
    msg with
    benv := {
      msg.benv with
      state := msg.benv.state.incrNonce adr
    }
  }

def Devm.incrNonce (devm : Devm) (adr : Adr) : Devm :=
  devm.withState (devm.state.incrNonce adr)

def Benv.incrNonce (benv : Benv) (adr : Adr) : Benv :=
  {benv with state := benv.state.incrNonce adr}

def State.setStor (w : State) (a : Adr) (s : Stor) : State :=
  let ac := (w.get a)
  w.set a {ac with stor := s}

def Benv.setStor (benv : Benv) (adr : Adr) (stor : Stor) : Benv :=
  {benv with state := benv.state.setStor adr stor}

def Msg.setCode (msg : Msg) (adr : Adr) (code : ByteArray) : Msg :=
  {msg with benv := {msg.benv with state := msg.benv.state.setCode adr code}}

def Devm.setCode (devm : Devm) (adr : Adr) (code : ByteArray) : Devm :=
  devm.withState (devm.state.setCode adr code)

def Devm.rollback (devm : Devm) (wor : State) (tra : Tra) : Devm :=
  devm.setWorld {devm.world with state := wor, transientStorage := tra}

def liftToExecution (devm : Devm)
  (f : Except (EvmError × State × AdrSet × Tra) Devm) : Execution := do
  match f with
  | .error ⟨err, state, createdAccounts, tra⟩ =>
    let devm' := (devm.withCreatedAccounts createdAccounts).setWorld
      {devm.world with state := state, transientStorage := tra}
    .error ⟨err, devm'⟩
  | .ok devm' => .ok devm'

--------------- CANONICAL STATE AND STORAGE (P0.4) ---------------

-- `State` and `Stor` are raw `Std.TreeMap`s, so nothing in their *types* stops
-- a map from storing a zero slot or an exact `Acct.nil`. Every mutator below
-- erases such an entry instead of storing it, but direct map construction
-- bypasses all of them. `State.root` serialises whatever the map holds, so two
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
-- Note the predicate is `≠ Acct.nil`, never `¬ Acct.Empty`: an account holding
-- storage is not the representational default even at zero code, nonce, and
-- balance, so erasing it would lose state.

/-- A storage slot's own optional lookup.

`Stor.get` answers an absent slot with `0`, which is correct for the EVM and
useless for stating canonicality -- the whole point is to tell "absent" from
"present and zero" apart. `Stor` is a `def` rather than an `abbrev`, so the
`GetElem?` notation `s[k]?` does not apply to it; this is that notation. -/
def Stor.find? (s : Stor) (k : B256) : Option B256 := Std.TreeMap.get? s k

theorem Stor.find?_empty (k : B256) : Stor.empty.find? k = none := rfl

theorem Stor.find?_erase (s : Stor) (k a : B256) :
    Stor.find? (s.erase k) a = if k = a then none else s.find? a := by
  rw [Stor.find?, Stor.find?, Std.TreeMap.get?_eq_getElem?,
      Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_erase]
  simp only [Std.compare_eq_iff_eq]

theorem Stor.find?_insert (s : Stor) (k a v : B256) :
    Stor.find? (s.insert k v) a = if k = a then some v else s.find? a := by
  rw [Stor.find?, Stor.find?, Std.TreeMap.get?_eq_getElem?,
      Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert]
  simp only [Std.compare_eq_iff_eq]

/-- The defining equation of `Stor.set`, as a lookup: writing zero *erases*. -/
theorem Stor.find?_set (s : Stor) (k a v : B256) :
    (s.set k v).find? a
      = if k = a then (if v = 0 then none else some v) else s.find? a := by
  rw [Stor.set]; split <;> simp_all [Stor.find?_erase, Stor.find?_insert]

theorem Stor.get_eq_getD_find? (s : Stor) (k : B256) :
    s.get k = (s.find? k).getD 0 := by
  rw [Stor.get, Stor.find?, Std.TreeMap.get?_eq_getElem?,
      Std.TreeMap.getD_eq_getD_getElem?]

theorem Stor.get_set_self (s : Stor) (k v : B256) : (s.set k v).get k = v := by
  rw [Stor.get_eq_getD_find?, Stor.find?_set, if_pos rfl]
  split <;> simp_all

theorem Stor.get_set_ne (s : Stor) {k a : B256} (h : k ≠ a) (v : B256) :
    (s.set k v).get a = s.get a := by
  rw [Stor.get_eq_getD_find?, Stor.get_eq_getD_find?, Stor.find?_set, if_neg h]

/-- A storage map is canonical when it stores no zero-valued slot.

Stated as a finite traversal of the map's `toList`, so it is decidable by
construction. -/
def Stor.Canonical (s : Stor) : Prop := ∀ e ∈ s.toList, e.2 ≠ 0

instance {s : Stor} : Decidable (Stor.Canonical s) := List.decidableBAll _ _

theorem Stor.mem_toList_iff {s : Stor} {k v : B256} :
    (k, v) ∈ s.toList ↔ s.find? k = some v := by
  rw [Stor.find?, Std.TreeMap.get?_eq_getElem?]
  exact Std.TreeMap.mem_toList_iff_getElem?_eq_some

/-- The lookup characterisation: the finite traversal and the pointwise
statement semantic proofs use are the same property. -/
theorem Stor.canonical_iff {s : Stor} :
    Stor.Canonical s ↔ ∀ (k v : B256), s.find? k = some v → v ≠ 0 := by
  constructor
  · intro h k v hv; exact h (k, v) (Stor.mem_toList_iff.mpr hv)
  · intro h e he; exact h e.1 e.2 (Stor.mem_toList_iff.mp (by simpa using he))

theorem Stor.canonical_empty : Stor.Canonical .empty := by
  rw [Stor.canonical_iff]; intro k v hv; cases hv

theorem Stor.Canonical.set {s : Stor} (h : Stor.Canonical s) (k v : B256) :
    Stor.Canonical (s.set k v) := by
  rw [Stor.canonical_iff] at h ⊢
  intro a w hw; rw [Stor.find?_set] at hw
  split at hw
  · split at hw
    · cases hw
    · cases hw; assumption
  · exact h a w hw

theorem Stor.Canonical.erase {s : Stor} (h : Stor.Canonical s) (k : B256) :
    Stor.Canonical (s.erase k) := by
  rw [Stor.canonical_iff] at h ⊢
  intro a v hv; rw [Stor.find?_erase] at hv
  split at hv
  · cases hv
  · exact h a v hv

/-- On a canonical map, reading zero and being absent are the same thing.

This is the property the trie commitment depends on, and the reason an
explicitly stored zero slot is not merely redundant. -/
theorem Stor.Canonical.get_eq_zero_iff {s : Stor} (h : Stor.Canonical s)
    (k : B256) : s.get k = 0 ↔ s.find? k = none := by
  rw [Stor.get_eq_getD_find?]
  cases hk : s.find? k with
  | none => simp
  | some v => simp [Stor.canonical_iff.mp h k v hk]

/-- The canonical smart constructor for storage: fold the pairs through
`Stor.set`, which drops the zero-valued ones instead of storing them. -/
def Stor.ofList (l : List (B256 × B256)) : Stor :=
  l.foldl (fun s e => s.set e.1 e.2) .empty

theorem Stor.canonical_foldl (l : List (B256 × B256)) :
    ∀ {s : Stor}, Stor.Canonical s →
      Stor.Canonical (l.foldl (fun s e => s.set e.1 e.2) s) := by
  induction l with
  | nil => intro s h; exact h
  | cons e l ih => intro s h; exact ih (h.set e.1 e.2)

/-- Smart-constructor soundness: the result is canonical whatever it was
given. -/
theorem Stor.canonical_ofList (l : List (B256 × B256)) :
    Stor.Canonical (Stor.ofList l) :=
  Stor.canonical_foldl l Stor.canonical_empty

theorem Stor.ofList_nil : Stor.ofList [] = .empty := rfl

theorem Stor.ofList_concat (l : List (B256 × B256)) (k v : B256) :
    Stor.ofList (l ++ [(k, v)]) = (Stor.ofList l).set k v := by
  rw [Stor.ofList, Stor.ofList, List.foldl_append, List.foldl_cons,
      List.foldl_nil]

/-- Smart-constructor soundness, read side: the last value written for a key is
the value read back, so canonicalisation never changes an EVM-level read. -/
theorem Stor.get_ofList_concat (l : List (B256 × B256)) (k v : B256) :
    (Stor.ofList (l ++ [(k, v)])).get k = v := by
  rw [Stor.ofList_concat, Stor.get_set_self]

theorem State.get_eq_getD (w : State) (a : Adr) :
    w.get a = (w[a]?).getD .nil := by
  rw [State.get, Std.TreeMap.getD_eq_getD_getElem?]

/-- The defining equation of `State.set`, as a lookup: writing `Acct.nil`
*erases*. -/
theorem State.getElem?_set (w : State) (a b : Adr) (ac : Acct) :
    (w.set a ac)[b]?
      = if a = b then (if ac = .nil then none else some ac) else w[b]? := by
  rw [State.set]
  split <;> simp_all [Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert]

theorem State.getElem?_erase (w : State) (a b : Adr) :
    (w.erase a)[b]? = if a = b then none else w[b]? := by
  simp [Std.TreeMap.getElem?_erase]

/-- A world state is canonical when it stores no `Acct.nil` and every account
it stores has canonical storage.

`≠ Acct.nil`, deliberately, and not `¬ Acct.Empty`: an account with storage is
not the representational default even at zero code, nonce, and balance. -/
def State.Canonical (w : State) : Prop :=
  ∀ e ∈ w.toList, e.2 ≠ Acct.nil ∧ Stor.Canonical e.2.stor

instance {w : State} : Decidable (State.Canonical w) := List.decidableBAll _ _

theorem State.mem_toList_iff {w : State} {a : Adr} {ac : Acct} :
    (a, ac) ∈ w.toList ↔ w[a]? = some ac :=
  Std.TreeMap.mem_toList_iff_getElem?_eq_some

/-- The lookup characterisation for world states. -/
theorem State.canonical_iff {w : State} :
    State.Canonical w
      ↔ ∀ (a : Adr) (ac : Acct),
          w[a]? = some ac → ac ≠ Acct.nil ∧ Stor.Canonical ac.stor := by
  constructor
  · intro h a ac hac; exact h (a, ac) (State.mem_toList_iff.mpr hac)
  · intro h e he; exact h e.1 e.2 (State.mem_toList_iff.mp (by simpa using he))

theorem State.canonical_empty : State.Canonical .empty := by
  rw [State.canonical_iff]; intro a ac hac; simp at hac

theorem Acct.canonical_nil_stor : Stor.Canonical Acct.nil.stor :=
  Stor.canonical_empty

/-- `State.set` preserves canonicality **given its real premise**: the account
being inserted must itself have canonical storage. Without that hypothesis the
statement is false, and it is not weakened here to make it look primitive. -/
theorem State.Canonical.set {w : State} (h : State.Canonical w) (a : Adr)
    {ac : Acct} (hs : Stor.Canonical ac.stor) :
    State.Canonical (w.set a ac) := by
  rw [State.canonical_iff] at h ⊢
  intro b ac' hb; rw [State.getElem?_set] at hb
  split at hb
  · split at hb
    · cases hb
    · cases hb; exact ⟨by assumption, hs⟩
  · exact h b ac' hb

theorem State.Canonical.erase {w : State} (h : State.Canonical w) (a : Adr) :
    State.Canonical (w.erase a) := by
  rw [State.canonical_iff] at h ⊢
  intro b ac hb; rw [State.getElem?_erase] at hb
  split at hb
  · cases hb
  · exact h b ac hb

/-- On a canonical state, reading `Acct.nil` and being absent are the same
thing. This is the account-level counterpart of `Stor.Canonical.get_eq_zero_iff`
and the regression an explicitly stored `Acct.nil` violates. -/
theorem State.Canonical.get_eq_nil_iff {w : State} (h : State.Canonical w)
    (a : Adr) : w.get a = .nil ↔ w[a]? = none := by
  rw [State.get_eq_getD]
  cases ha : w[a]? with
  | none => simp
  | some ac => simp [(State.canonical_iff.mp h a ac ha).1]

/-- Every account *read* out of a canonical state has canonical storage --
including an absent one, whose `Acct.nil` carries the empty map. This is what
lets the derived mutators below discharge `State.Canonical.set`'s premise
without assuming anything new. -/
theorem State.Canonical.stor {w : State} (h : State.Canonical w) (a : Adr) :
    Stor.Canonical (w.get a).stor := by
  rw [State.get_eq_getD]
  cases ha : w[a]? with
  | none => exact Acct.canonical_nil_stor
  | some ac => exact (State.canonical_iff.mp h a ac ha).2

theorem State.get_set_self (w : State) (a : Adr) (ac : Acct) :
    (w.set a ac).get a = ac := by
  rw [State.get_eq_getD, State.getElem?_set, if_pos rfl]
  split <;> simp_all

theorem State.get_set_ne (w : State) {a b : Adr} (h : a ≠ b) (ac : Acct) :
    (w.set a ac).get b = w.get b := by
  rw [State.get_eq_getD, State.get_eq_getD, State.getElem?_set, if_neg h]

--------------- CANONICALITY OF THE PRIMITIVE MUTATORS ---------------

-- One theorem per named state mutator. Each derives its `State.set` premise
-- from `State.Canonical.stor` rather than assuming it, except `setStor`, whose
-- storage argument comes from the caller and therefore carries a hypothesis.

theorem State.Canonical.destroyAccount {w : State} (h : State.Canonical w)
    (a : Adr) : State.Canonical (destroyAccount w a) :=
  h.erase a

theorem State.Canonical.setCode {w : State} (h : State.Canonical w) (a : Adr)
    (cd : ByteArray) : State.Canonical (w.setCode a cd) :=
  h.set a (h.stor a)

theorem State.Canonical.setBal {w : State} (h : State.Canonical w) (a : Adr)
    (v : B256) : State.Canonical (w.setBal a v) :=
  h.set a (h.stor a)

theorem State.Canonical.addBal {w : State} (h : State.Canonical w) (a : Adr)
    (v : B256) : State.Canonical (w.addBal a v) :=
  h.setBal a _

theorem State.Canonical.subBal {w w' : State} (h : State.Canonical w) {a : Adr}
    {v : B256} (hw : w.subBal a v = some w') : State.Canonical w' := by
  rw [State.subBal] at hw
  split at hw
  · cases hw
  · cases hw; exact h.setBal a _

theorem State.Canonical.incrNonce {w : State} (h : State.Canonical w) (a : Adr) :
    State.Canonical (w.incrNonce a) :=
  h.set a (h.stor a)

/-- `State.setStor` carries its real premise: the storage map handed in must
already be canonical. -/
theorem State.Canonical.setStor {w : State} (h : State.Canonical w) (a : Adr)
    {s : Stor} (hs : Stor.Canonical s) : State.Canonical (w.setStor a s) :=
  h.set a hs

theorem State.Canonical.setStorVal {w : State} (h : State.Canonical w) (a : Adr)
    (k v : B256) : State.Canonical (w.setStorVal a k v) :=
  h.set a ((h.stor a).set k v)

/-- The canonical smart constructor for world states. Its premise is the honest
one: the accounts handed in must have canonical storage, which `Stor.ofList`
supplies for anything the fixture parser builds. -/
def State.ofList (l : List (Adr × Acct)) : State :=
  l.foldl (fun w e => w.set e.1 e.2) .empty

theorem State.canonical_foldl (l : List (Adr × Acct))
    (hl : ∀ e ∈ l, Stor.Canonical e.2.stor) :
    ∀ {w : State}, State.Canonical w →
      State.Canonical (l.foldl (fun w e => w.set e.1 e.2) w) := by
  induction l with
  | nil => intro w h; exact h
  | cons e l ih =>
    intro w h
    exact ih (fun x hx => hl x (List.mem_cons_of_mem _ hx))
      (h.set e.1 (hl e List.mem_cons_self))

theorem State.canonical_ofList {l : List (Adr × Acct)}
    (hl : ∀ e ∈ l, Stor.Canonical e.2.stor) :
    State.Canonical (State.ofList l) :=
  State.canonical_foldl l hl State.canonical_empty

theorem State.ofList_nil : State.ofList [] = .empty := rfl

theorem State.ofList_concat (l : List (Adr × Acct)) (a : Adr) (ac : Acct) :
    State.ofList (l ++ [(a, ac)]) = (State.ofList l).set a ac := by
  rw [State.ofList, State.ofList, List.foldl_append, List.foldl_cons,
      List.foldl_nil]

theorem State.get_ofList_concat (l : List (Adr × Acct)) (a : Adr) (ac : Acct) :
    (State.ofList (l ++ [(a, ac)])).get a = ac := by
  rw [State.ofList_concat, State.get_set_self]

--------------- CANONICAL TRANSIENT STORAGE ---------------

-- `Tra.set` erases an empty map rather than storing it, exactly as `Stor.set`
-- erases a zero slot, so transient storage has its own canonicality with the
-- same shape. It is separate from `Stor.Canonical` because the default it
-- erases is a different one.

def Tra.Canonical (τ : Tra) : Prop :=
  ∀ e ∈ τ.toList, e.2 ≠ Stor.empty ∧ Stor.Canonical e.2

instance {τ : Tra} : Decidable (Tra.Canonical τ) := List.decidableBAll _ _

theorem Tra.mem_toList_iff {τ : Tra} {a : Adr} {s : Stor} :
    (a, s) ∈ τ.toList ↔ τ[a]? = some s :=
  Std.TreeMap.mem_toList_iff_getElem?_eq_some

theorem Tra.canonical_iff {τ : Tra} :
    Tra.Canonical τ
      ↔ ∀ (a : Adr) (s : Stor),
          τ[a]? = some s → s ≠ Stor.empty ∧ Stor.Canonical s := by
  constructor
  · intro h a s hs; exact h (a, s) (Tra.mem_toList_iff.mpr hs)
  · intro h e he; exact h e.1 e.2 (Tra.mem_toList_iff.mp (by simpa using he))

theorem Tra.canonical_empty : Tra.Canonical .empty := by
  rw [Tra.canonical_iff]; intro a s hs; simp at hs

theorem Tra.getElem?_set (τ : Tra) (a b : Adr) (s : Stor) :
    (τ.set a s)[b]?
      = if a = b then (if s.isEmpty then none else some s) else τ[b]? := by
  rw [Tra.set]
  split <;> simp_all [Std.TreeMap.getElem?_erase, Std.TreeMap.getElem?_insert]

theorem Tra.Canonical.set {τ : Tra} (h : Tra.Canonical τ) (a : Adr) {s : Stor}
    (hs : Stor.Canonical s) : Tra.Canonical (τ.set a s) := by
  rw [Tra.canonical_iff] at h ⊢
  intro b s' hb; rw [Tra.getElem?_set] at hb
  split at hb
  · split at hb
    · cases hb
    · cases hb
      exact ⟨fun he =>
        absurd (Std.TreeMap.eq_empty_iff_isEmpty.mp he) (by assumption), hs⟩
  · exact h b s' hb

/-- Every transient map *read* out of a canonical `Tra` is canonical, the
absent case included. -/
theorem Tra.Canonical.getD {τ : Tra} (h : Tra.Canonical τ) (a : Adr) :
    Stor.Canonical (τ.getD a .empty) := by
  rw [Std.TreeMap.getD_eq_getD_getElem?]
  cases ha : τ[a]? with
  | none => exact Stor.canonical_empty
  | some s => exact (Tra.canonical_iff.mp h a s ha).2

theorem Tra.Canonical.setStorVal {τ : Tra} (h : Tra.Canonical τ) (a : Adr)
    (k v : B256) : Tra.Canonical (τ.setStorVal a k v) :=
  h.set a ((h.getD a).set k v)

--------------- THE EXECUTION-STATE INVARIANT VOCABULARY ---------------

-- Statements only. This is the vocabulary Step 4 of `~/plans/integrity.md`
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
--   3. every saved parent state, which in this interpreter lives in the frame's
--      `Msg` -- `msg.benv.state` and `msg.tenv.transientStorage` are exactly the
--      pair `Devm.rollback` restores at `processMessage.settle` and
--      `processCreateMessage.settle`.
--
-- Transient storage is carried alongside the world state everywhere, so each
-- predicate below pairs `State.Canonical` with `Tra.Canonical` rather than
-- treating transient storage as an afterthought.

/-- A machine world -- current state and transient storage -- is canonical. -/
def World.Canonical (w : World) : Prop :=
  State.Canonical w.state ∧ Tra.Canonical w.transientStorage

/-- The dynamic machine's world is canonical. -/
def Devm.Canonical (devm : Devm) : Prop := World.Canonical devm.world

/-- The block environment's *original* state is canonical. Separate from the
current one because it outlives it. -/
def BenvStat.Canonical (stat : BenvStat) : Prop := State.Canonical stat.origState

/-- A block environment: its current state and its original state. -/
def Benv.Canonical (benv : Benv) : Prop :=
  State.Canonical benv.state ∧ BenvStat.Canonical benv.stat

def Tenv.Canonical (tenv : Tenv) : Prop := Tra.Canonical tenv.transientStorage

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
      ↔ State.Canonical devm.state ∧ Tra.Canonical devm.transientStorage :=
  Iff.rfl

theorem Devm.Canonical.withState {devm : Devm} (h : Devm.Canonical devm)
    {w : State} (hw : State.Canonical w) : Devm.Canonical (devm.withState w) :=
  ⟨hw, h.2⟩

theorem Devm.Canonical.withTransientStorage {devm : Devm}
    (h : Devm.Canonical devm) {τ : Tra} (hτ : Tra.Canonical τ) :
    Devm.Canonical (devm.withTransientStorage τ) :=
  ⟨h.1, hτ⟩

/-- Restoring a saved parent state is canonical exactly when what was saved
was. The current world is irrelevant, which is the point of a rollback. -/
theorem Devm.canonical_rollback {devm : Devm} {w : State} {τ : Tra}
    (hw : State.Canonical w) (hτ : Tra.Canonical τ) :
    Devm.Canonical (devm.rollback w τ) :=
  ⟨hw, hτ⟩

/-- A message's saved pair is exactly what `Devm.rollback` is fed at both
settlement sites, so a canonical message restores a canonical machine. -/
theorem Msg.Canonical.rollback {msg : Msg} (h : Msg.Canonical msg)
    (devm : Devm) :
    Devm.Canonical (devm.rollback msg.benv.state msg.tenv.transientStorage) :=
  ⟨h.1.1, h.2⟩

--------------- NEGATIVE REGRESSIONS ---------------

-- An absent account and an explicitly stored `Acct.nil` read alike and must
-- not both count as canonical; the same for an absent and an explicitly stored
-- zero storage slot. These are the exact cases P0.4 names.

/-- A world state holding an explicit `Acct.nil`, which no mutator can build. -/
private def nilStoredState : State :=
  Std.TreeMap.empty.insert (0 : Adr) Acct.nil

/-- A storage map holding an explicit zero slot, likewise unreachable. -/
private def zeroStoredStor : Stor :=
  (Std.TreeMap.empty : Stor).insert (0 : B256) 0

-- The reads agree with the empty map ...
#guard State.get nilStoredState 0 = Acct.nil
#guard State.get (Std.TreeMap.empty : State) 0 = Acct.nil
#guard zeroStoredStor.get 0 = 0
#guard Stor.empty.get 0 = 0
-- ... and canonicality tells them apart.
#guard ¬ State.Canonical nilStoredState
#guard State.Canonical (Std.TreeMap.empty : State)
#guard ¬ Stor.Canonical zeroStoredStor
#guard Stor.Canonical Stor.empty
-- The canonicalising mutator and the smart constructor both refuse to store it.
#guard Stor.Canonical (Stor.empty.set 0 0)
#guard Stor.Canonical (Stor.ofList [(0, 0), (1, 7), (2, 0)])
#guard (Stor.ofList [(0, 0), (1, 7), (2, 0)]).get 1 = 7
#guard (Stor.ofList [(0, 0), (1, 7), (2, 0)]).get 0 = 0
#guard State.Canonical (State.ofList [((0 : Adr), Acct.nil)])
-- An `Acct.nil` handed to the smart constructor is dropped, not stored.
#guard (State.ofList [((0 : Adr), Acct.nil)]).isEmpty
#guard ¬ nilStoredState.isEmpty

/-! ### Site table: the account-access sites, at both metering shapes

G3 of `jaune-amsterdam-metering-v1`. For each site the interpreter reads a
repriced number at, one guard reproducing today's Prague number and one
reproducing the pinned target's Amsterdam number, both through the same
expression the arm evaluates. A repricing that reached only one of the two
shapes fails here.

`gasWarmAccess` is a global on both sides on purpose: no fork moves it, so the
warm rows say "still 100" rather than restating a rule that did not change. -/

private def guardAdr : Adr := 0x1000
private def guardCold : AdrSet := .emptyWithCapacity
private def guardWarm : AdrSet := guardCold.insert guardAdr

private def pragueGas : GasSchedule := pragueRules.gas
private def amsterdamGas : GasSchedule := amsterdamRules.gas

-- `accessCost`, the shape `BALANCE`, `EXTCODE*` and the whole CALL family read.
#guard pragueGas.accessCost guardAdr guardCold = 2600
#guard amsterdamGas.accessCost guardAdr guardCold = 3000
#guard pragueGas.accessCost guardAdr guardWarm = 100
#guard amsterdamGas.accessCost guardAdr guardWarm = 100
-- and the sibling is the old function at Prague, definitionally.
#guard pragueGas.accessCost guardAdr guardCold = accessCost guardAdr guardCold
#guard pragueGas.accessCost guardAdr guardWarm = accessCost guardAdr guardWarm

-- `EXTCODESIZE` / `EXTCODECOPY`: the access half plus EIP-8038's code-reading
-- surcharge, which is `0` at Prague and 100 at Amsterdam.
#guard pragueGas.coldAccountAccess + pragueGas.codeReadSurcharge = 2600
#guard amsterdamGas.coldAccountAccess + amsterdamGas.codeReadSurcharge = 3100
#guard gasWarmAccess + pragueGas.codeReadSurcharge = 100
#guard gasWarmAccess + amsterdamGas.codeReadSurcharge = 200

-- `EXTCODEHASH` takes the repriced access and no surcharge.
#guard pragueGas.coldAccountAccess = 2600
#guard amsterdamGas.coldAccountAccess = 3000

-- The value-bearing call surcharge and the `CREATE`/`CREATE2` base, the other
-- two numbers goal A left on the globals for this goal to route.
#guard pragueGas.callValue = 9000
#guard amsterdamGas.callValue = 11300
#guard pragueGas.createAccess = 32000
#guard amsterdamGas.createAccess = 12000
#guard pragueGas.callValue = gasCallValue
#guard pragueGas.createAccess = gasCreate

-- The stipend a value-bearing call hands its child is covered by the surcharge
-- at both shapes. This is the inequality the Sufficiency family needs, checked
-- as data here so a repricing that broke it fails before any proof does.
#guard gCallStipend < pragueGas.callValue
#guard gCallStipend < amsterdamGas.callValue

/-! ### Site table: `SSTORE` over the (original, current, new) lattice

The arm's two shapes charge different *terms*, not just different numbers, so
the rows below name the terms. Prague's are the globals it has always used;
Amsterdam's come from the two records and are computed by the sibling
definitions the arm calls, so a guard here is a guard on the code path.

`amsterdamState` is the vehicle's state-gas record; a vehicle without one would
not be a metering vehicle, and the `Option` match is discharged by `rfl`. -/

private def amsterdamState : StateGasRules := amsterdamStateGasRules

-- Prague: the whole cost of a first-time set of a zero slot, cold, is the
-- cold-load charge plus `gasStorageSet`; an update to a non-zero slot is the
-- cold-load charge plus the difference; a change to an already-warm slot that
-- is not the first this transaction costs the warm access alone.
#guard gasColdSload + gasStorageSet = 22100
#guard gasColdSload + (gasStorageUpdate - gasColdSload) = 5000
#guard gasWarmAccess = 100

-- Amsterdam: access plus `STORAGE_WRITE` on the slot's first change, and
-- nothing but the access otherwise. EIP-8038 re-derives the lattice above as
-- exactly these two terms.
#guard sstoreAmsterdamGasCost amsterdamState 1 0 0 true = 2100 + 10000
#guard sstoreAmsterdamGasCost amsterdamState 1 0 0 false = 100 + 10000
#guard sstoreAmsterdamGasCost amsterdamState 2 1 1 true = 2100 + 10000
#guard sstoreAmsterdamGasCost amsterdamState 2 1 1 false = 100 + 10000
-- current ≠ original: the write was already paid for this transaction.
#guard sstoreAmsterdamGasCost amsterdamState 3 1 2 true = 2100
#guard sstoreAmsterdamGasCost amsterdamState 3 1 2 false = 100
-- new = current: no change at all, so no write either.
#guard sstoreAmsterdamGasCost amsterdamState 1 1 1 true = 2100
#guard sstoreAmsterdamGasCost amsterdamState 1 1 1 false = 100

-- The state dimension: a first-time set of a *zero* slot creates state and
-- pays `STORAGE_SET`; nothing else does.
#guard sstoreAmsterdamStateGas amsterdamState 1 0 0 = 97920
#guard sstoreAmsterdamStateGas amsterdamState 2 1 1 = 0
#guard sstoreAmsterdamStateGas amsterdamState 3 1 2 = 0
#guard sstoreAmsterdamStateGas amsterdamState 0 0 0 = 0
-- and the same slot cleared again in the same transaction refills it.
#guard sstoreAmsterdamStateRefund amsterdamState 0 0 1 = 97920
#guard sstoreAmsterdamStateRefund amsterdamState 0 1 1 = 0
#guard sstoreAmsterdamStateRefund amsterdamState 1 0 0 = 0

-- Refunds. The clear refund is the one number both shapes take from
-- `GasSchedule`, at each fork's own value; the restore refund is
-- `gasStorageSet - gasWarmAccess` at Prague and `STORAGE_WRITE` at Amsterdam.
#guard sstoreNewRefundCounter pragueGas 0 1 1 0 = 4800
#guard sstoreAmsterdamRefundCounter amsterdamGas amsterdamState 0 1 1 0 = 11616
#guard sstoreNewRefundCounter pragueGas 1 1 0 0
  = -4800 + (5000 - 2100 - 100)
#guard sstoreAmsterdamRefundCounter amsterdamGas amsterdamState 1 1 0 0
  = -11616 + 10000
#guard sstoreNewRefundCounter pragueGas 0 0 1 0 = 20000 - 100
#guard sstoreAmsterdamRefundCounter amsterdamGas amsterdamState 0 0 1 0 = 10000
#guard sstoreNewRefundCounter pragueGas 1 1 1 0 = 0
#guard sstoreAmsterdamRefundCounter amsterdamGas amsterdamState 1 1 1 0 = 0

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

/-- Canonicality of a frame-settlement result.

The settlement carrier's error channel holds the saved state and transient
storage the parent will be rolled back to or rebuilt from
(`liftToExecution`), so both components must be canonical; a settled machine
is obliged outright. -/
def Except.CanonicalSettle {ρ : Type} :
    Except (ρ × State × AdrSet × Tra) Devm → Prop
  | .ok devm => devm.Canonical
  | .error e => State.Canonical e.2.1 ∧ Tra.Canonical e.2.2.2

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

theorem Except.CanonicalOn.map {ρ α β : Type} {P : α → Prop} {Q : β → Prop}
    {x : Except (ρ × Devm) α} {f : α → β}
    (hx : x.CanonicalOn P) (hf : ∀ a, P a → Q (f a)) :
    (x <&> f).CanonicalOn Q := by
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

theorem liftMachMetaWorldExecution_canonical
    {core : World → Mach → Meta → Footprint.Outcome (Mach × Meta) Unit}
    {devm : Devm} (h : devm.Canonical) :
    (liftMachMetaWorldExecution core devm).Canonical :=
  liftMachMetaExecution_canonical h

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

theorem Devm.push_canonical {x : B256} {devm : Devm} (h : devm.Canonical) :
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

theorem pushItem_canonical {x : B256} {c : Nat} {devm : Devm}
    (h : devm.Canonical) : (pushItem x c devm).Canonical :=
  liftMachExecution_canonical h

theorem applyUnary_canonical {f : B256 → B256} {c : Nat} {devm : Devm}
    (h : devm.Canonical) : (applyUnary f c devm).Canonical :=
  liftMachExecution_canonical h

theorem applyBinary_canonical {f : B256 → B256 → B256} {c : Nat} {devm : Devm}
    (h : devm.Canonical) : (applyBinary f c devm).Canonical :=
  liftMachExecution_canonical h

theorem applyTernary_canonical {f : B256 → B256 → B256 → B256} {c : Nat}
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

theorem Devm.emitTransferLog_canonical {devm : Devm} {sender recipient : Adr}
    {amount : B256} (h : devm.Canonical) :
    (devm.emitTransferLog sender recipient amount).Canonical := by
  unfold Devm.emitTransferLog
  split
  · exact h
  · exact Devm.addLog_canonical h

theorem addAccessedAddress_canonical {devm : Devm} {a : Adr}
    (h : devm.Canonical) : (addAccessedAddress devm a).Canonical :=
  h.of_world_eq rfl

theorem addAccessedStorageKey_canonical {devm : Devm} {a : Adr} {k : B256}
    (h : devm.Canonical) : (addAccessedStorageKey devm a k).Canonical :=
  h.of_world_eq rfl

theorem addAccountToDelete_canonical {devm : Devm} {a : Adr}
    (h : devm.Canonical) : (addAccountToDelete devm a).Canonical :=
  h.of_world_eq rfl

theorem assertDynamic_canonicalOn {sevm : Sevm} {devm : Devm}
    (h : devm.Canonical) :
    (assertDynamic sevm devm).CanonicalOn (fun _ => True) :=
  Except.canonicalOn_assert h

-- The world-changing machine mutators, each discharged by the Step-3 state
-- and transient-storage ladder.

theorem Devm.Canonical.setStorVal {devm : Devm} (h : devm.Canonical)
    (adr : Adr) (k v : B256) : (devm.setStorVal adr k v).Canonical :=
  h.withState (State.Canonical.setStorVal h.1 adr k v)

theorem Devm.Canonical.setTransVal {devm : Devm} (h : devm.Canonical)
    (adr : Adr) (k v : B256) : (devm.setTransVal adr k v).Canonical :=
  h.withTransientStorage (Tra.Canonical.setStorVal h.2 adr k v)

theorem Devm.Canonical.setBal {devm : Devm} (h : devm.Canonical)
    (adr : Adr) (v : B256) : (devm.setBal adr v).Canonical :=
  h.withState (State.Canonical.setBal h.1 adr v)

theorem Devm.Canonical.addBal {devm : Devm} (h : devm.Canonical)
    (adr : Adr) (v : B256) : (devm.addBal adr v).Canonical :=
  h.withState (State.Canonical.addBal h.1 adr v)

theorem Devm.Canonical.subBal {devm devm' : Devm} (h : devm.Canonical)
    {adr : Adr} {v : B256} (hs : devm.subBal adr v = some devm') :
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
    (adr : Adr) : (devm.incrNonce adr).Canonical :=
  h.withState (State.Canonical.incrNonce h.1 adr)

theorem Devm.Canonical.setCode {devm : Devm} (h : devm.Canonical)
    (adr : Adr) (cd : ByteArray) : (devm.setCode adr cd).Canonical :=
  h.withState (State.Canonical.setCode h.1 adr cd)

-- The block-environment and message mutators used by frame construction,
-- delegation, and transaction processing.

theorem Benv.Canonical.withState {benv : Benv} (h : benv.Canonical)
    {st : State} (hs : st.Canonical) : (benv.withState st).Canonical :=
  ⟨hs, h.2⟩

theorem Benv.Canonical.setBal {benv : Benv} (h : benv.Canonical)
    (adr : Adr) (v : B256) : (benv.setBal adr v).Canonical :=
  ⟨State.Canonical.setBal h.1 adr v, h.2⟩

theorem Benv.Canonical.addBal {benv : Benv} (h : benv.Canonical)
    (adr : Adr) (v : B256) : (benv.addBal adr v).Canonical :=
  ⟨State.Canonical.addBal h.1 adr v, h.2⟩

theorem Benv.Canonical.subBal {benv benv' : Benv} (h : benv.Canonical)
    {adr : Adr} {v : B256} (hs : benv.subBal adr v = some benv') :
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
    (adr : Adr) : (benv.incrNonce adr).Canonical :=
  ⟨State.Canonical.incrNonce h.1 adr, h.2⟩

theorem Benv.Canonical.setStor {benv : Benv} (h : benv.Canonical)
    (adr : Adr) {s : Stor} (hs : Stor.Canonical s) :
    (benv.setStor adr s).Canonical :=
  ⟨State.Canonical.setStor h.1 adr hs, h.2⟩

theorem Benv.Canonical.setStorVal {benv : Benv} (h : benv.Canonical)
    (adr : Adr) (k v : B256) : (benv.setStorVal adr k v).Canonical :=
  ⟨State.Canonical.setStorVal h.1 adr k v, h.2⟩

/-- Opening a transaction saves the current state as the transaction-original
state, so a canonical environment stays canonical on both components. -/
theorem Benv.Canonical.beginTransaction {benv : Benv} (h : benv.Canonical) :
    benv.beginTransaction.Canonical :=
  ⟨h.1, h.1⟩

theorem Benv.Canonical.addCreatedAccount {benv : Benv} (h : benv.Canonical)
    (adr : Adr) : (addCreatedAccount benv adr).Canonical :=
  ⟨h.1, h.2⟩

theorem Tenv.Canonical.setTransVal {tenv : Tenv} (h : tenv.Canonical)
    (adr : Adr) (k v : B256) : (tenv.setTransVal adr k v).Canonical :=
  Tra.Canonical.setStorVal h adr k v

theorem Msg.Canonical.withBenv {msg : Msg} (h : msg.Canonical)
    {benv : Benv} (hb : benv.Canonical) : (msg.withBenv benv).Canonical :=
  ⟨hb, h.2⟩

theorem Msg.Canonical.incrNonce {msg : Msg} (h : msg.Canonical)
    (adr : Adr) : (msg.incrNonce adr).Canonical :=
  ⟨⟨State.Canonical.incrNonce h.1.1 adr, h.1.2⟩, h.2⟩

theorem Msg.Canonical.setCode {msg : Msg} (h : msg.Canonical)
    (adr : Adr) (cd : ByteArray) : (msg.setCode adr cd).Canonical :=
  ⟨⟨State.Canonical.setCode h.1.1 adr cd, h.1.2⟩, h.2⟩

-- Child incorporation and the settlement-to-execution bridge: the parent's
-- world is replaced wholesale, so only the incoming state's canonicality
-- matters. These are the exact joints through which a frame's result
-- re-enters its parent.

theorem incorporateChildOnError_canonical {parent child : Devm}
    (hc : child.Canonical) (rd : Bytes) :
    (incorporateChildOnError parent child rd).Canonical :=
  ⟨hc.1, hc.2⟩

theorem incorporateChildOnSuccess_canonical {parent child : Devm}
    (hc : child.Canonical) (rd : Bytes) :
    (incorporateChildOnSuccess parent child rd).Canonical :=
  ⟨hc.1, hc.2⟩

/-- The Amsterdam siblings take the child's world wholesale too. -/
theorem incorporateChildAmsterdamOnError_canonical {parent child : Devm}
    (hc : child.Canonical) (rd : Bytes) :
    (incorporateChildAmsterdamOnError parent child rd).Canonical :=
  ⟨hc.1, hc.2⟩

theorem incorporateChildAmsterdamOnSuccess_canonical {parent child : Devm}
    (hc : child.Canonical) (rd : Bytes) :
    (incorporateChildAmsterdamOnSuccess parent child rd).Canonical :=
  ⟨hc.1, hc.2⟩

theorem liftToExecution_canonical {devm : Devm} {r}
    (hr : Except.CanonicalSettle r) : (liftToExecution devm r).Canonical := by
  cases r with
  | error e => exact ⟨hr.1, hr.2⟩
  | ok devm' => exact hr

-- Checkpoint 2 of the corpus: through the instruction arms. First the intro
-- forms and the settle-carrier sequencing lemma, then a descent tactic for
-- the homogeneous machine-level `do`-chains.

theorem Except.canonicalOn_ok {ρ α : Type} {P : α → Prop} {a : α} (h : P a) :
    (Except.ok a : Except (ρ × Devm) α).CanonicalOn P := h

theorem Except.canonicalOn_error {ρ α : Type} {P : α → Prop} {e : ρ × Devm}
    (h : e.2.Canonical) :
    (Except.error e : Except (ρ × Devm) α).CanonicalOn P := h

/-- `.ok a >>= f` is `f a` by iota, so sequencing after a pure binding needs
no case split. Stated so the descent tactic can skip the abstraction. -/
theorem Except.canonicalOn_bind_ok {ρ α β : Type} {P : β → Prop} {a : α}
    {f : α → Except (ρ × Devm) β} (h : (f a).CanonicalOn P) :
    ((Except.ok a : Except (ρ × Devm) α) >>= f).CanonicalOn P := h

/-- Sequencing on the settlement carrier: the error channel passes through
unchanged, an ok machine feeds the continuation. -/
theorem Except.CanonicalSettle.bind {ρ : Type}
    {x : Except (ρ × State × AdrSet × Tra) Devm}
    {f : Devm → Except (ρ × State × AdrSet × Tra) Devm}
    (hx : x.CanonicalSettle) (hf : ∀ d, d.Canonical → (f d).CanonicalSettle) :
    (x >>= f).CanonicalSettle := by
  cases x with
  | error e => exact hx
  | ok d => exact hf d hx

/-- The eq-conditioned form of `Devm.memRead_canonical`, matching the
hypothesis a `split` on the destructuring `let` leaves behind. -/
theorem Devm.memRead_eq_canonical {devm d' : Devm} {i s : Nat} {val : Bytes}
    (h : devm.Canonical) (heq : devm.memRead i s = (val, d')) :
    d'.Canonical := by
  have hm := Devm.memRead_canonical (index := i) (size := s) h
  rw [heq] at hm
  exact hm

/-- Canonicality through every register-instruction arm. Only `SSTORE` and
`TSTORE` change the world, each through its named mutator; every other arm is
world-preserving by construction. The four arms that destructure `memRead`
with an irrefutable `let` are walked by hand, because that match does not
reduce over an opaque scrutinee. -/
theorem Rinst.runCore_canonical (pc : Nat) {devm : Devm} (sevm : Sevm)
    (h : devm.Canonical) (r : Rinst) :
    (Rinst.runCore pc devm sevm r).Canonical := by
  cases r <;> simp only [Rinst.runCore]
  case mload =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) ?_
    rintro ⟨start, d1⟩ h1
    refine Except.CanonicalOn.bind (liftMachExecution_canonical h1) ?_
    intro d2 h2
    rcases hread : d2.memRead start 32 with ⟨val, d3⟩
    exact liftMachExecution_canonical (Devm.memRead_eq_canonical h2 hread)
  case keccak256 =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) ?_
    rintro ⟨start, d1⟩ h1
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h1) ?_
    rintro ⟨size, d2⟩ h2
    refine Except.CanonicalOn.bind (liftMachExecution_canonical h2) ?_
    intro d3 h3
    rcases hread : d3.memRead start size with ⟨arg, d4⟩
    exact liftMachExecution_canonical (Devm.memRead_eq_canonical h3 hread)
  case mcopy =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) ?_
    rintro ⟨dest, d1⟩ h1
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h1) ?_
    rintro ⟨src, d2⟩ h2
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h2) ?_
    rintro ⟨len, d3⟩ h3
    refine Except.CanonicalOn.bind (liftMachExecution_canonical h3) ?_
    intro d4 h4
    rcases hread : d4.memRead src len with ⟨val, d5⟩
    exact (Devm.memRead_eq_canonical h4 hread).of_world_eq rfl
  case log =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) ?_
    rintro ⟨start, d1⟩ h1
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h1) ?_
    rintro ⟨size, d2⟩ h2
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h2) ?_
    rintro ⟨topics, d3⟩ h3
    refine Except.CanonicalOn.bind (liftMachExecution_canonical h3) ?_
    intro d4 h4
    refine Except.CanonicalOn.bind (Except.canonicalOn_assert h4) ?_
    intro u _
    rcases hread : d4.memRead start size with ⟨data, d5⟩
    exact (Devm.memRead_eq_canonical h4 hread).of_world_eq rfl
  all_goals try exact liftMachExecution_canonical h
  all_goals try exact liftMachMetaWorldExecution_canonical h
  case exp =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    exact Except.CanonicalOn.bind (liftMachExecution_canonical hb)
      fun d hd => liftMachExecution_canonical hd
  case clz =>
    split
    · exact liftMachExecution_canonical h
    · exact h
  case slotnum =>
    split
    · exact liftMachExecution_canonical h
    · exact h
  case selfbalance =>
    exact Except.CanonicalOn.bind (liftMachExecution_canonical h)
      fun d hd => liftMachExecution_canonical hd
  case calldataload =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    exact Except.CanonicalOn.bind (liftMachExecution_canonical ha)
      fun d hd => liftMachExecution_canonical hd
  case calldatacopy =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
    exact Except.CanonicalOn.bind (liftMachExecution_canonical hc)
      fun d hd => Devm.Canonical.of_world_eq hd rfl
  case codecopy =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
    exact Except.CanonicalOn.bind (liftMachExecution_canonical hc)
      fun d hd => Devm.Canonical.of_world_eq hd rfl
  case extcodesize =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    split <;>
      exact Except.CanonicalOn.bind
        (liftMachExecution_canonical (Devm.Canonical.of_world_eq ha rfl))
        fun d hd => liftMachExecution_canonical hd
  case extcodecopy =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hc) fun e he => ?_
    split <;>
      exact Except.CanonicalOn.bind
        (liftMachExecution_canonical (Devm.Canonical.of_world_eq he rfl))
        fun d hd => Devm.Canonical.of_world_eq hd rfl
  case returndatacopy =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn hb) fun c hc => ?_
    refine Except.CanonicalOn.bind (liftMachExecution_canonical hc) fun d hd => ?_
    split
    · exact Except.CanonicalOn.bind
        (Except.canonicalOn_error (P := fun _ => True) hd)
        fun _ _ => Devm.Canonical.of_world_eq hd rfl
    · exact Devm.Canonical.of_world_eq hd rfl
  case extcodehash =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    split <;>
      exact Except.CanonicalOn.bind
        (liftMachExecution_canonical (Devm.Canonical.of_world_eq ha rfl))
        fun d hd => liftMachExecution_canonical hd
  case blockhash =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    exact Except.CanonicalOn.bind (liftMachExecution_canonical ha)
      fun d hd => liftMachExecution_canonical hd
  case blobhash =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    exact Except.CanonicalOn.bind (liftMachExecution_canonical ha)
      fun d hd => liftMachExecution_canonical hd
  case pop =>
    exact Except.CanonicalOn.bind
      (Except.CanonicalOn.map (liftMach_canonicalOn h) fun _ ha => ha)
      fun d hd => liftMachExecution_canonical hd
  case mstore =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    exact Except.CanonicalOn.bind (liftMachExecution_canonical hb)
      fun d hd => Devm.Canonical.of_world_eq hd rfl
  case mstore8 =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    exact Except.CanonicalOn.bind (liftMachExecution_canonical hb)
      fun d hd => Devm.Canonical.of_world_eq hd rfl
  case sload =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    split <;>
      exact Except.CanonicalOn.bind
        (liftMachExecution_canonical (Devm.Canonical.of_world_eq ha rfl))
        fun d hd => liftMachExecution_canonical hd
  case sstore =>
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
  case tload =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    exact liftMachExecution_canonical ha
  case tstore =>
    split
    · refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (liftMachExecution_canonical hb) fun d hd => ?_
      refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd) fun _ _ => ?_
      exact Devm.Canonical.setTransVal hd _ _ _
    · refine Except.CanonicalOn.bind (assertDynamic_canonicalOn h) fun _ _ => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
      refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
      refine Except.CanonicalOn.bind (liftMachExecution_canonical hb) fun d hd => ?_
      exact Devm.Canonical.setTransVal hd _ _ _
  case gas =>
    exact Except.CanonicalOn.bind (liftMachExecution_canonical h)
      fun d hd => liftMachExecution_canonical hd
  case dup =>
    refine Except.CanonicalOn.bind (liftMachExecution_canonical h) fun d hd => ?_
    split
    · exact hd
    · exact liftMachExecution_canonical hd
  case swap =>
    refine Except.CanonicalOn.bind (liftMachExecution_canonical h) fun d hd => ?_
    split
    · exact hd
    · exact Devm.Canonical.of_world_eq hd rfl

theorem Rinst.run_canonical {evm : Evm} (h : evm.dyna.Canonical) (r : Rinst) :
    (Rinst.run evm r).Canonical :=
  Rinst.runCore_canonical evm.pc evm.sta h r

/-- Destroying any list of accounts preserves canonicality; transaction
settlement folds `destroyAccount` over the accounts-to-delete set. -/
theorem State.Canonical.foldl_destroyAccount {l : List Adr} {w : State}
    (h : w.Canonical) : (l.foldl Jaune.destroyAccount w).Canonical := by
  induction l generalizing w with
  | nil => exact h
  | cons a l ih => exact ih (h.destroyAccount a)

/-- Jump instructions never touch the world; the payload carries the new
program counter beside the machine. -/
theorem Jinst.runCore_canonicalOn (pc : Nat) {devm : Devm} (sevm : Sevm)
    (h : devm.Canonical) (j : Jinst) :
    (Jinst.runCore pc devm sevm j).CanonicalOn (fun a => a.2.Canonical) := by
  cases j <;> simp only [Jinst.runCore]
  case jumpdest =>
    refine Except.CanonicalOn.bind (liftMachExecution_canonical h)
      fun d hd => ?_
    exact hd
  case jump =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMachExecution_canonical ha) fun d hd => ?_
    refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd) fun _ _ => ?_
    exact hd
  case jumpi =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMachExecution_canonical hb) fun d hd => ?_
    split
    · exact Except.canonicalOn_bind_ok hd
    · refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd) fun _ _ => ?_
      exact Except.canonicalOn_bind_ok hd

theorem Jinst.run_canonicalOn {evm : Evm} (h : evm.dyna.Canonical) (j : Jinst) :
    (Jinst.run evm j).CanonicalOn (fun a => a.2.Canonical) :=
  Jinst.runCore_canonicalOn evm.pc evm.sta h j

/-- Canonicality through the halting instructions. `SELFDESTRUCT` is the one
world-changing arm, and it factors through `subBal`/`addBal`/`setBal`. -/
theorem Linst.run_canonical {sevm : Sevm} {devm : Devm}
    (h : devm.Canonical) (l : Linst) :
    Execution.Canonical (Linst.run sevm devm l) := by
  cases l <;> simp only [Linst.run]
  case stop => exact h
  case revert =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMachExecution_canonical hb) fun d hd => ?_
    rcases hread : d.memRead a.1 b.1 with ⟨out, d'⟩
    exact (Devm.memRead_eq_canonical hd hread).of_world_eq rfl
  case return_ =>
    refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
    refine Except.CanonicalOn.bind (liftMach_canonicalOn ha) fun b hb => ?_
    refine Except.CanonicalOn.bind (liftMachExecution_canonical hb) fun d hd => ?_
    rcases hread : d.memRead a.1 b.1 with ⟨out, d'⟩
    exact (Devm.memRead_eq_canonical hd hread).of_world_eq rfl
  case selfdestruct =>
    split
    · -- Prague: the body it has always been.
      refine Except.CanonicalOn.bind (liftMach_canonicalOn h) fun a ha => ?_
      refine Except.canonicalOn_bind_ok ?_
      refine Except.canonicalOn_bind_ok ?_
      split <;>
        (refine Except.canonicalOn_bind_ok ?_
         refine Except.CanonicalOn.bind
           (liftMachExecution_canonical (Devm.Canonical.of_world_eq ha rfl))
           fun d hd => ?_
         refine Except.CanonicalOn.bind (Except.canonicalOn_assert hd) fun _ _ => ?_
         -- The EIP-7928 read recorders are meta-only: read the balance through them.
         simp only [Devm.balReadAccount_getAcct]
         refine Except.CanonicalOn.bind (P := Devm.Canonical) ?_ fun d' hd' => ?_
         · cases hs : d.subBal sevm.currentTarget (a.2.getAcct sevm.currentTarget).bal with
           | none => exact hd
           | some d1 => exact Devm.Canonical.subBal hd hs
         · refine Except.canonicalOn_bind_ok ?_
           split
           · exact Devm.Canonical.of_world_eq
               (Devm.Canonical.setBal (Devm.Canonical.addBal hd' a.1 _) _ 0) rfl
           · exact Devm.Canonical.addBal hd' a.1 _)
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

end Jaune
