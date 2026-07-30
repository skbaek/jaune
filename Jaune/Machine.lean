import Jaune.Types
import Jaune.Fork
import Jaune.EC
import Jaune.BLS
import Jaune.Hash

/-
Design note #1: primitive signatures of the form

  `Devm → Except (String × Devm) (α × Devm)`

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
    | some rh => [BLT.bytes rh.toBytes]

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
def perEmptyAccountCost := 25000
def perAuthBaseCost := 12500
def txBaseCost : Nat := 21000
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

instance {a b : Adr} : Decidable (a = b) := by
  rw [show (a = b) ↔ (a.1 = b.1 ∧ a.2 = b.2) from Prod.ext_iff]
  apply instDecidableAnd

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

-- class Benvironment
structure Benv : Type where
  state : State
  createdAccounts : AdrSet
  stat : BenvStat

structure TenvStat : Type where
  origin: Adr
  gasPrice: Nat
  gas: Nat
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

def hasErrorType (err errType : String) : Bool :=
  err = errType || String.isPrefixOf (errType ++ " : ") err

-- EIP-7823 rejects an oversized `MODEXP` length header with a bare
-- `ExceptionalHalt` rather than one of the specification's named subclasses.
-- It is given its own tag here because every other exceptional halt this build
-- can report is already distinguishable by name, and reusing `OutOfGasError`
-- for a check that never inspects the gas counter would misreport it.
def modexpInputLimitTag : String := "ModexpInputLimitExceeded"

abbrev isExceptionalHalt (err : String) : Prop :=
  List.any [
    "StackUnderflowError",
    "StackOverflowError",
    "OutOfGasError",
    modexpInputLimitTag,
    "InvalidOpcode",
    "InvalidJumpDestError",
    "StackDepthLimitError",
    "WriteInStaticContext",
    "OutOfBoundsRead",
    "InvalidParameter",
    "InvalidContractPrefix",
    "AddressCollision",
    "KZGProofError"
  ] (hasErrorType err)

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
    insufficientMaxFeePerGasTag, transactionGasLimitExceededTag,
    intrinsicGasTooLowTag, invalidChainIdTag, nonceIsMaxTag, nonceMismatchTooHighTag,
    nonceMismatchTooLowTag,
    priorityGreaterThanMaxFeeTag, senderNotEoaTag,
    type3BlobCountExceededTag, type3BlobCountLimitExceededTag,
    type3ContractCreationTag,
    type3InvalidBlobVersionedHashTag, type3ZeroBlobsTag,
    type4ContractCreationTag, emptyAuthorizationListTag ]

#guard transactionExceptionTags.length = 20
#guard transactionExceptionTags.eraseDups.length = 20
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
-- Tags follow the `hasErrorType` convention: a bare tag, or a tag opening
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
def blockRlpSizeExceededTag : String := "BlockRlpSizeExceededError"

/-- Every block-rejection tag. The single source of truth for the distinctness
checks, and for `isBlockException`. -/
def blockExceptionTags : List String :=
  [ gasLimitTooBigTag, gasLimitAdjustmentTag, gasUsedOverflowTag,
    gasUsedMismatchTag, timestampOlderThanParentTag, blockNumberTag,
    baseFeePerGasTag, difficultyOverParisTag, ommersOverParisTag,
    extraDataTooBigTag, unknownParentTag, unknownParentZeroTag,
    stateRootTag, transactionsRootTag, receiptsRootTag, logBloomTag,
    withdrawalsRootTag, headerNonceTag, excessBlobGasTag, blobGasUsedTag,
    requestsHashTag, depositEventLayoutTag, systemContractCallFailedTag,
    blockRlpSizeExceededTag ]

/-- Is this error one of the precise block-rejection reasons? -/
def isBlockException (err : String) : Bool :=
  List.any blockExceptionTags (hasErrorType err)

-- The tags are distinct, and none is a prefix of another. `hasErrorType` reads
-- a tag up to a fixed " : ", so a tag that prefixed another could be read as
-- the wrong reason -- and one reason read as another is precisely the defect
-- this vocabulary exists to remove.
#guard blockExceptionTags.length = 24
#guard blockExceptionTags.eraseDups.length = 24
#guard blockExceptionTags.all fun t =>
  (blockExceptionTags.filter fun u => t.isPrefixOf u).length = 1

-- No tag is readable as the broad category it replaces, in either direction.
#guard blockExceptionTags.all fun t => ¬ hasErrorType t "InvalidBlock"
#guard ¬ isBlockException "InvalidBlock"
#guard ¬ isBlockException "InvalidBlock : gas limit is wrong"

------------------- STRICT CONSENSUS-FIELD DECODERS --------------------

-- The `Except`-level face of the strict shape checks in `Jaune/Types.lean`.
-- Each helper names one precise reason a consensus field can be malformed, in
-- the `hasErrorType` tag convention the rest of the executable uses: a bare tag,
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

/-- The error for an RLP item whose structure is not what the field requires.
Kept here so structure failures read the same at every call site. -/
def rlpStructureError (name : String) (detail : String) : String :=
  s!"{rlpStructureTag} : {name} : {detail}"

/-- A fixed-width field: exactly `n` bytes, no more and no fewer. -/
def Bytes.toRlpFixed (name : String) (n : Nat) (xs : Bytes) : Except String Bytes :=
  (xs.toFixed? n).toExcept
    s!"{rlpFixedWidthTag} : {name} must be exactly {n} bytes, but is {xs.length}"

/-- A fixed-width 32-byte hash or root, as a `B256`. `Bytes.toB256?` is already an
exact-width decoder, so this adds the precise reason rather than a check. Note
these fields are *bytes*, not scalars: a root may legitimately begin with a zero
byte, so the canonical-scalar rule must not be applied to them. -/
def Bytes.toRlpHash (name : String) (xs : Bytes) : Except String B256 :=
  xs.toB256?.toExcept
    s!"{rlpFixedWidthTag} : {name} must be exactly 32 bytes, but is {xs.length}"

/-- A fixed-width 8-byte field, as a `UInt64`. Like `toRlpHash`, this is bytes
rather than a scalar: the header nonce is eight bytes of zeroes, not empty. -/
def Bytes.toRlpFixedB64 (name : String) (xs : Bytes) : Except String UInt64 :=
  xs.toUInt64?.toExcept
    s!"{rlpFixedWidthTag} : {name} must be exactly 8 bytes, but is {xs.length}"

/-- The canonicality half of scalar checking, shared by every width. The
overflow tag is a parameter because the width is what the official vocabulary
distinguishes, while non-canonical encoding is one reason at every width. -/
private def rlpScalarBytes (overflowTag name : String) (n : Nat) (xs : Bytes) :
  Except String Bytes := do
  if xs.length > n then
    .error
      s!"{overflowTag} : {name} scalar is {xs.length} bytes, \
         exceeding its {n}-byte width"
  if xs.head? = some (0 : UInt8) then
    .error
      s!"{rlpLeadingZerosTag} : {name} scalar 0x{Bytes.toHex xs} \
         is not canonically encoded (leading zero byte)"
  .ok xs

/-- A canonical unsigned scalar of at most `n` bytes, as a `Nat`. Overflow is
reported against the 256-bit identity, this being the widest scalar the
consensus fields have; a field modelled as 64 bits must use `toRlpB64`. -/
def Bytes.toRlpNat (name : String) (n : Nat) (xs : Bytes) : Except String Nat := do
  let xs ← rlpScalarBytes rlpFieldOverflow256Tag name n xs
  .ok xs.toNat

/-- A canonical 64-bit scalar: at most eight bytes, converted without
truncation. -/
def Bytes.toRlpB64 (name : String) (xs : Bytes) : Except String UInt64 := do
  let xs ← rlpScalarBytes rlpFieldOverflow64Tag name 8 xs
  .ok xs.toUInt64

/-- A canonical 256-bit scalar: at most thirty-two bytes, converted without
truncation. -/
def Bytes.toRlpB256 (name : String) (xs : Bytes) : Except String B256 := do
  let xs ← rlpScalarBytes rlpFieldOverflow256Tag name 32 xs
  .ok xs.toB256

/-- An address field: exactly twenty bytes. -/
def Bytes.toRlpAdr (name : String) (xs : Bytes) : Except String Adr :=
  xs.toAdr?.toExcept
    s!"{rlpFixedWidthTag} : {name} must be exactly 20 bytes, but is {xs.length}"

/-- An optional contract-creation receiver: empty, or exactly twenty bytes. -/
def Bytes.toRlpReceiver (name : String) (xs : Bytes) : Except String (Option Adr) :=
  xs.toReceiver?.toExcept
    s!"{rlpFixedWidthTag} : {name} must be empty or exactly 20 bytes, \
       but is {xs.length}"

--------------- STRICT DECODER REGRESSION CHECKS ----------------

-- Each reason is reported under its own tag, and each tag is recognized by the
-- `hasErrorType` convention the classifier reads -- an exact tag, or a tag
-- opening detail text at " : ". Accepted values are checked too: the point of
-- rejecting a nine-byte index is to keep the eight-byte ones exact.


@[ext]
structure Mach : Type where
  stack : List B256
  memory : Mem
  gasLeft : Nat

@[ext]
structure Meta : Type where
  logs : List Log
  refundCounter : Int
  output : Bytes
  accountsToDelete : AdrSet
  returnData : Bytes
  error : Option String
  accessedAddresses : AdrSet
  accessedStorageKeys : KeySet
  createdAccounts : AdrSet

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
def Devm.logs (devm : Devm) : List Log := devm.meta.logs
def Devm.refundCounter (devm : Devm) : Int := devm.meta.refundCounter
def Devm.output (devm : Devm) : Bytes := devm.meta.output
def Devm.accountsToDelete (devm : Devm) : AdrSet := devm.meta.accountsToDelete
def Devm.returnData (devm : Devm) : Bytes := devm.meta.returnData
def Devm.error (devm : Devm) : Option String := devm.meta.error
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

def Devm.withAccountsToDelete (devm : Devm) (accountsToDelete : AdrSet) : Devm :=
  devm.setMeta {devm.meta with accountsToDelete := accountsToDelete}

def Devm.withReturnData (devm : Devm) (returnData : Bytes) : Devm :=
  devm.setMeta {devm.meta with returnData := returnData}

def Devm.withError (devm : Devm) (error : Option String) : Devm :=
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

abbrev Execution : Type := Except (String × Devm) Devm

/-- A normalized result for a footprint-restricted core.  Both branches retain
    the core mutable state so a lift can reattach changes made before an error. -/
abbrev Footprint.Outcome (σ α : Type) : Type :=
  Except (String × σ) (α × σ)

namespace Footprint

/-- Lift a normalized core outcome by projecting and reattaching its mutable
    state to the original flat `Devm`. -/
def liftOutcome (get : Devm → σ) (set : Devm → σ → Devm)
    (core : σ → Outcome σ α) (devm : Devm) :
    Except (String × Devm) (α × Devm) :=
  match core (get devm) with
  | .error (err, view) => .error (err, set devm view)
  | .ok (value, view) => .ok (value, set devm view)

/-- Forget the unit payload of a lifted normalized outcome. -/
def toExecution (outcome : Except (String × Devm) (Unit × Devm)) : Execution :=
  match outcome with
  | .error err => .error err
  | .ok (_, devm) => .ok devm

end Footprint

/-- Lift a Mach-only payload core. -/
def liftMach (core : Mach → Footprint.Outcome Mach α) (devm : Devm) :
    Except (String × Devm) (α × Devm) :=
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
    (devm : Devm) : Except (String × Devm) (α × Devm) :=
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
  | none => .error ("OutOfGasError", mach)
  | some gas => .ok ((), {mach with gasLeft := gas})

def chargeGas (cost : Nat) (devm : Devm) : Execution :=
  liftMachExecution (Mach.chargeGas cost) devm

theorem chargeGas_def (cost : Nat) (devm : Devm) :
    chargeGas cost devm = (do
      match safeSub devm.gasLeft cost with
      | none => .error ⟨"OutOfGasError", devm⟩
      | some gas => .ok (devm.setMach {devm.mach with gasLeft := gas})) := by
  rcases devm with ⟨⟨stack, memory, gasLeft⟩, view, world⟩
  simp only [chargeGas, Mach.chargeGas, liftMachExecution, liftMach,
    Footprint.toExecution, Footprint.liftOutcome, Devm.setMach, Devm.gasLeft]
  cases safeSub gasLeft cost <;> rfl

inductive Ninst : Type
  | reg : Rinst → Ninst
  | exec : Xinst → Ninst
  | push : ∀ bs : Bytes, bs.length ≤ 32 → Ninst

def Ninst.toOpString : Ninst → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push bs _ => "PUSH" ++ bs.length.repr

def Ninst.toString : Ninst → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push [] _ => "PUSH0"
  | push bs _ => "PUSH" ++ bs.length.repr ++ " " ++ Bytes.toHex bs

instance : ToString Ninst := ⟨Ninst.toString⟩
instance : Repr Ninst := ⟨λ i _ => i.toString⟩

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

lemma Nat.hi_le (a b : Nat) : a ↿ b ≤ a := by
  rw [hi, shiftLeft_eq, shiftRight_eq_div_pow]
  apply Nat.div_mul_le_self

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
  if pc < code.size
  then
    let b : UInt8 := code.get! pc
    match h : b.toInstType with
    | .R => b.toRinst <&> (.next ∘ .reg)
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

def fakeExpAux (num den i : Nat) : Nat → Nat → Nat
  | _, 0 => panic! "error : fuel exhausted in fake exponentiation"
  | 0, _ => 0
  | numAcc, fuel + 1 =>
    let numAcc' := (numAcc * num) / (den * i)
    numAcc + fakeExpAux num den (i + 1) numAcc' fuel

def fakeExp (fac num den : Nat) : Nat :=
  let fuel := (max (fac * num) <| num * num) + 2
  let out := fakeExpAux num den 1 (fac * den) fuel
  out / den

def calculateBlobGasPrice (blob : BlobSchedule) (excessBlobGas : Nat) : Nat :=
  fakeExp 1 excessBlobGas blob.baseFeeUpdateFraction

def Mach.push (x : B256) (mach : Mach) : Footprint.Outcome Mach Unit :=
  if mach.stack.length < 1024
  then .ok ⟨(), {mach with stack := x :: mach.stack}⟩
  else .error ⟨"StackOverflowError", mach⟩

def Devm.push (x : B256) (devm : Devm) : Execution :=
  liftMachExecution (Mach.push x) devm

theorem Devm.push_def (x : B256) (devm : Devm) : Devm.push x devm = (do
    .assert
      (devm.stack.length < 1024)
      ⟨"StackOverflowError", devm⟩
    .ok (devm.setMach {devm.mach with stack := x :: devm.stack})) := by
  rcases devm with ⟨⟨stack, memory, gasLeft⟩, view, world⟩
  simp only [Devm.push, Mach.push, liftMachExecution, liftMach, Footprint.toExecution,
    Footprint.liftOutcome, Devm.stack, Devm.setMach, Except.assert, bind, Except.bind]
  split_ifs <;> rfl

def Mach.pop (mach : Mach) : Footprint.Outcome Mach B256 :=
  match mach.stack with
  | [] => .error ⟨"StackUnderflowError", mach⟩
  | x :: xs => .ok ⟨x, {mach with stack := xs}⟩

def Devm.pop (devm : Devm) : Except (String × Devm) (B256 × Devm) :=
  liftMach Mach.pop devm

theorem Devm.pop_def (devm : Devm) : Devm.pop devm = (do
    match devm.stack with
    | [] => .error ⟨"StackUnderflowError", devm⟩
    | x :: xs => .ok ⟨x, devm.setMach {devm.mach with stack := xs}⟩) := by
  rcases devm with ⟨⟨stack, memory, gasLeft⟩, view, world⟩
  cases stack <;> rfl

def Prod.mapFst {α₁ : Type u₁} {α₂ : Type u₂} {β : Type v} (f : α₁ → α₂) : α₁ × β → α₂ × β :=
  Prod.map f id

def Mach.popToNat (mach : Mach) : Footprint.Outcome Mach Nat :=
  match mach.pop with
  | .error err => .error err
  | .ok ⟨x, mach'⟩ => .ok ⟨x.toNat, mach'⟩

def Devm.popToNat (devm : Devm) : Except (String × Devm) (Nat × Devm) :=
  liftMach Mach.popToNat devm

theorem Devm.popToNat_def (devm : Devm) :
    devm.popToNat = (devm.pop <&> Prod.mapFst B256.toNat) := by
  rcases devm with ⟨⟨stack, memory, gasLeft⟩, view, world⟩
  cases stack <;> rfl

def Mach.popToAdr (mach : Mach) : Footprint.Outcome Mach Adr :=
  match mach.pop with
  | .error err => .error err
  | .ok ⟨x, mach'⟩ => .ok ⟨x.toAdr, mach'⟩

def Devm.popToAdr (devm : Devm) : Except (String × Devm) (Adr × Devm) :=
  liftMach Mach.popToAdr devm

theorem Devm.popToAdr_def (devm : Devm) :
    devm.popToAdr = (devm.pop <&> Prod.mapFst B256.toAdr) := by
  rcases devm with ⟨⟨stack, memory, gasLeft⟩, view, world⟩
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
    Except (String × Devm) (List B256 × Devm) :=
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
    rcases devm with ⟨⟨stack, memory, gasLeft⟩, view, world⟩
    cases stack with
    | nil => rfl
    | cons x xs =>
      cases h : Mach.popN { stack := xs, memory := memory, gasLeft := gasLeft } n with
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
  rcases devm with ⟨⟨stack, memory, gasLeft⟩, view, world⟩
  simp only [pushItem, Mach.pushItem, Mach.chargeGas, Mach.push, chargeGas, Devm.push,
    liftMachExecution, liftMach, Footprint.toExecution, Footprint.liftOutcome,
    Devm.setMach, bind, Except.bind]
  cases safeSub gasLeft c with
  | none => rfl
  | some gas => dsimp only

def accessCost (x : Adr) (a : AdrSet) : Nat :=
  if x ∈ a then gasWarmAccess else gasColdAccountAccess

def Meta.addAccessedAddress (view : Meta) (a : Adr) : Meta :=
  {view with accessedAddresses := view.accessedAddresses.insert a}

def addAccessedAddress (devm : Devm) (a : Adr) : Devm :=
  liftMachMetaPure (fun mach view => (mach, view.addAccessedAddress a)) devm

def Meta.addAccessedStorageKey (view : Meta) (a : Adr) (k : B256) : Meta :=
  {view with accessedStorageKeys := view.accessedStorageKeys.insert ⟨a, k⟩}

def addAccessedStorageKey (devm : Devm) (a : Adr) (k : B256) : Devm :=
  liftMachMetaPure (fun mach view => (mach, view.addAccessedStorageKey a k)) devm

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

def Mach.memExtends (mach : Mach) (pairs : List (Nat × Nat)) : Mach :=
  {mach with memory := mach.memory.extends pairs}

def Devm.memExtends (devm : Devm) (pairs : List (Nat × Nat)) : Devm :=
  liftMachPure (Mach.memExtends · pairs) devm

def Meta.addLog (view : Meta) (log : Log) : Meta :=
  {view with logs := view.logs ++ [log]}

def Devm.addLog (devm : Devm) (log : Log) : Devm :=
  liftMachMetaPure (fun mach view => (mach, view.addLog log)) devm

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
  rcases devm with ⟨⟨stack, memory, gasLeft⟩, view, world⟩
  cases stack with
  | nil => rfl
  | cons x xs =>
    cases h : Mach.pushItem (f x) cost { stack := xs, memory := memory, gasLeft := gasLeft } with
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
  rcases devm with ⟨⟨stack, memory, gasLeft⟩, view, world⟩
  cases stack with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      cases h : Mach.pushItem (f x y) cost { stack := ys, memory := memory, gasLeft := gasLeft } with
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

def Evm.contract (evm : Evm) : Adr := evm.sta.currentTarget

def assertDynamic (sevm : Sevm) (devm : Devm) : Except (String × Devm) Unit :=
  Except.assert (!sevm.isStatic) ⟨s!"WriteInStaticContext", devm⟩

def sstoreNewRefundCounter (new_value : B256)
    (original_value : B256) (current_value : B256) (rc : Int) : Int :=
  if current_value ≠ new_value then
    let rc' :=
      if original_value ≠ 0 ∧ current_value ≠ 0 ∧ new_value = 0 then
        rc + rSClear
      else
        rc
    let rc'' :=
      if original_value ≠ 0 ∧ current_value = 0 then
        rc' - rSClear
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

/-- The read-only-World core of `BALANCE`.  Its mutable result contains only
    `Mach` and `Meta`: it pops the address operand, charges the warm/cold
    account-access cost, records a cold access, and pushes the balance read
    from `World`. -/
def Rinst.balanceCore (world : World) (mach : Mach) (view : Meta) :
    Footprint.Outcome (Mach × Meta) Unit :=
  match mach.pop with
  | .error (err, mach') => .error (err, (mach', view))
  | .ok (x, mach') =>
    let a := x.toAdr
    let warm := a ∈ view.accessedAddresses
    let view' := if warm then view else view.addAccessedAddress a
    let cost := if warm then gasWarmAccess else gasColdAccountAccess
    match Mach.chargeGas cost mach' with
    | .error (err, mach'') => .error (err, (mach'', view'))
    | .ok (_, mach'') =>
      match Mach.push (world.state.get a).bal mach'' with
      | .error (err, mach''') => .error (err, (mach''', view'))
      | .ok (_, mach''') => .ok ((), (mach''', view'))

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
  | .balance => liftMachMetaWorldExecution Rinst.balanceCore devm
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
  | .extcodesize => do
    let ⟨adr, devm⟩ ← devm.popToAdr
    let devm ←
      if adr ∈ devm.accessedAddresses
      then chargeGas gasWarmAccess devm
      else chargeGas gasColdAccountAccess (addAccessedAddress devm adr)
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
    let devm ←
      if adr ∈ devm.accessedAddresses
      then chargeGas (gasWarmAccess + copy_gas_cost + extend_memory_cost) devm
      else
        chargeGas
          (gasColdAccountAccess + copy_gas_cost + extend_memory_cost)
          (addAccessedAddress devm adr)
    let code := devm.getCode adr
    let value := code.sliceD code_start_index size (Linst.toUInt8 .stop)
    .ok (devm.memWrite memory_start_index value)
  | .retdatasize => pushItem devm.returnData.length.toB256 gBase devm
  | .retdatacopy => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨return_data_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let words := ceilDiv size 32
    let copy_gas_cost := gReturnDataCopy * words
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas (gVerylow + copy_gas_cost + extend_memory_cost) devm
    if (devm.returnData.length < return_data_start_index + size) then
      .error ⟨"OutOfBoundsRead", devm⟩
    let value :=
      devm.returnData.sliceD return_data_start_index size 0
    .ok (devm.memWrite memory_start_index value)
  | .extcodehash => do
    let ⟨adr, devm⟩ ← devm.popToAdr
    let devm ←
      if adr ∈ devm.accessedAddresses then
        chargeGas gasWarmAccess devm
      else
        chargeGas gasColdAccountAccess (addAccessedAddress devm adr)
    let account := devm.getAcct adr
    let codehash : B256 :=
      if account.Empty then 0
      else ByteArray.keccak 0 account.code.size account.code
    devm.push codehash
  | .selfbalance => pushItem (devm.getBal sevm.currentTarget) gLow devm
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
      .error ⟨"InvalidOpcode", devm⟩
  | .kec => do
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
    | none => .error ⟨"StackUnderflowError", devm⟩
    | some stack => .ok (devm.withStack stack)
  | .dup n => do
    let devm ← chargeGas gVerylow devm
    match devm.stack[n]? with
    | none => .error ⟨"StackUnderflowError", devm⟩
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
    devm.push (devm.getStorVal ct key)
  | .tload => do
    let ⟨key, devm⟩ ← devm.pop
    pushItem (devm.getTransVal sevm.currentTarget key) gasWarmAccess devm
  | .pc => pushItem pc.toB256 gBase devm
  | .sstore => do
    let ⟨key, devm⟩ ← devm.pop
    let ⟨new_value, devm⟩ ← devm.pop
    .assert
      (gCallStipend < devm.gasLeft)
      ⟨"OutOfGasError", devm⟩
    let ct := sevm.currentTarget
    let original_value := getOrigStorVal sevm ct key
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
        new_value
        original_value
        current_value
        devm.refundCounter
    let devm ← chargeGas gasCost3 devm
    assertDynamic sevm devm
    .ok (devm.setStorVal sevm.currentTarget key new_value)
  | .tstore => do
    let ⟨key, devm⟩ ← devm.pop
    let ⟨new_value, devm⟩ ← devm.pop
    let devm ← chargeGas gasWarmAccess devm
    assertDynamic sevm devm
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
  | .error ⟨err, _⟩ => err
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

-- Under Osaka the same two degenerate inputs reach the real failures instead.
#guard guardClzErr (guardClz osakaRules 100 []) = "StackUnderflowError"
#guard guardClzErr (guardClz osakaRules (gLow - 1) [0]) = "OutOfGasError"
#guard (guardClz osakaRules gLow [0]).toOption.map Devm.gasLeft = some 0

instance : Inhabited Execution := ⟨.ok default⟩

def noPushBefore (cd : ByteArray) : Nat → Nat → Bool
  | 0, _ => true
  | _, 0 => true
  | k + 1, m + 1 =>
    if k < cd.size
    then let b := cd.get! k
         if (b < (0x7F - m.toUInt8) || 0x7F < b)
         then noPushBefore cd k m
         else if noPushBefore cd k 32
              then false
              else noPushBefore cd k m
    else noPushBefore cd k m

def jumpable (cd : ByteArray) (k : Nat) : Bool :=
  if cd.get! k = (Jinst.toUInt8 .jumpdest)
  then noPushBefore cd k 32
  else false

def Jinst.runCore (pc : Nat) (devm : Devm) (sevm : Sevm) :
    Jinst → Except (String × Devm) (Nat × Devm)
  | .jumpdest => do
    let devm' ← chargeGas gJumpdest devm
    .ok ⟨pc + 1, devm'⟩
  | .jump => do
    let ⟨jump_dest, devm'⟩ ← devm.pop
    let devm'' ← chargeGas gMid devm'
    .assert
      (jumpable sevm.code jump_dest.toNat)
      ⟨"InvalidJumpDestError", devm''⟩
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
          ⟨"InvalidJumpDestError", devm'''⟩
        .ok dest.toNat
    .ok ⟨pc', devm'''⟩

def Jinst.run (evm : Evm) (j : Jinst) : Except (String × Devm) (Nat × Devm) :=
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
    Linst → Except (String × Devm) Devm
  | .stop => .ok devm
  | .rev => do
    let ⟨memory_start_index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let extend_memory_cost := devm.extCost [⟨memory_start_index, size⟩]
    let devm ← chargeGas extend_memory_cost devm
    let ⟨output, devm⟩ := devm.memRead memory_start_index size
    let devm := devm.withOutput output
    .error ⟨"Revert", devm⟩
  | .ret => do
    let ⟨index, devm⟩ ← devm.popToNat
    let ⟨size, devm⟩ ← devm.popToNat
    let cost := devm.extCost [⟨index, size⟩]
    let devm ← chargeGas cost devm
    let ⟨output, devm⟩ := devm.memRead index size
    .ok (devm.withOutput output)
  | .dest => do
    let donor := sevm.currentTarget
    let ⟨donee, devm⟩ ← devm.popToAdr
    let donorBal ← .ok (devm.getAcct sevm.currentTarget).bal
    let ⟨devm, gasCost2⟩ ← .ok <|
      if donee ∉ devm.accessedAddresses
        then
          ( ⟨ addAccessedAddress devm donee,
              gasSelfDestruct + gasColdAccountAccess ⟩ : Devm × Nat )
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
        ⟨"ERROR : InsufficientBalanceError", devm⟩
    let devm ← .ok <| devm.addBal donee donorBal
    if donor ∈ devm.createdAccounts then
      .ok (addAccountToDelete (devm.setBal donor 0) donor)
    else
      .ok devm

def except64th (n : Nat) : Nat := n - (n / 64)

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
      returnData := returnData}
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
      accessedStorageKeys := parent.accessedStorageKeys.union child.accessedStorageKeys}
  parent.setWorld
    {parent.world with
      state := child.state
      transientStorage := child.transientStorage}

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
  (f : Except (String × State × AdrSet × Tra) Devm) : Execution := do
  match f with
  | .error ⟨err, state, createdAccounts, tra⟩ =>
    let devm' := (devm.withCreatedAccounts createdAccounts).setWorld
      {devm.world with state := state, transientStorage := tra}
    .error ⟨err, devm'⟩
  | .ok devm' => .ok devm'
