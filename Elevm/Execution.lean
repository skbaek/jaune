import Elevm.Types
import Elevm.Fork
import Elevm.EC
import Elevm.BLS
import Elevm.Hash

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
verificaiton work. It should be considered a style contract between `elevm`
and the projects which depend on it, including `blanc`.
-/

abbrev AccessList : Type := List (Adr × List B256)

instance : ToString AccessList := ⟨@List.toString _ _⟩

abbrev State : Type := Std.TreeMap Adr Acct compare

def State.toStrings (w : State) : List String :=
  let kvs := w.toArray.toList
  let kvToStrings : Adr × Acct → List String :=
    fun x => Acct.toStrings ("0x" ++ x.fst.toHex.dropZeroes) x.snd
  fork "STATE" (kvs.map kvToStrings)

def AccessItem.toStrings : (Adr × List B256) → List String
  | ⟨a, ks⟩ => fork a.toHex <| ks.map <| fun k => [k.toHex]

def AccessList.toStrings (al : AccessList) : List String :=
    fork "ACCESS LIST" <| al.map <| AccessItem.toStrings

-- class Authorization
structure Auth : Type where
  -- EIP-7702 authorization chain IDs are uint256 values.  A value other than
  -- the execution chain ID (or zero) makes only this tuple inapplicable.
  chainId : B256
  address : Adr
  nonce : B64
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
    (chainId : B64)
    (gasPrice : Nat)
    (receiver : Option Adr)
    (accessList : AccessList)
  -- EIP-1559
  | two
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Option Adr)
    (accessList : AccessList)
  -- EIP-4844
  | three
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Adr)
    (accessList : AccessList)
    (maxBlobFee : Nat)
    (blobHashes : List B256)
  | four
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Adr)
    (accessList : AccessList)
    (auths : List Auth)

structure Withdrawal : Type where
  (globalIndex : B64)
  (validatorIndex : B64)
  (recipient : Adr)
  (amount : B256)

structure Header : Type where
  parentHash : B256
  ommersHash : B256
  coinbase : Adr
  stateRoot : B256
  txsRoot : B256
  receiptRoot : B256
  bloom : B8L
  difficulty : Nat
  number : Nat
  gasLimit : Nat
  gasUsed : Nat
  timestamp : Nat
  extraData : B8L
  prevRandao : B256
  nonce : B64
  baseFeePerGas : Nat
  withdrawalsRoot : B256
  blobGasUsed : Nat
  excessBlobGas : Nat
  parentBeaconBlockRoot : B256
  requestsHash : Option B256

def Header.toStrings (header : Header) : List String :=
  fork "header" [
    [s!"parent hash : {header.parentHash}"],
    [s!"ommers hash : {header.ommersHash}"],
    [s!"coinbase : {header.coinbase}"],
    [s!"stateRoot : {header.stateRoot}"],
    [s!"transactions root : {header.txsRoot}"],
    [s!"receipt root : {header.receiptRoot}"],
    [s!"bloom : {header.bloom.toHex}"],
    [s!"difficulty : {header.difficulty}"],
    [s!"number : {header.number}"],
    [s!"gas limit : {header.gasLimit}"],
    [s!"gas used : {header.gasUsed}"],
    [s!"timestamp : {header.timestamp}"],
    [s!"extra data : {header.extraData.toHex}"],
    [s!"prevRandao : {header.prevRandao}"],
    [s!"nonce : {header.nonce}"],
    [s!"base fee per gas : {header.baseFeePerGas}"],
    [s!"withdrawals root : {header.withdrawalsRoot}"],
    [s!"blob gas used : {header.blobGasUsed}"],
    [s!"excess blob gas : {header.excessBlobGas}"],
    [s!"parent beacon block root : {header.parentBeaconBlockRoot}"],
    [s!"requests Hash : {header.requestsHash}"],
  ]

instance : ToString Header := ⟨String.joinln ∘ Header.toStrings⟩

def Header.toBLT (header : Header) : BLT :=
  BLT.list <| [
    BLT.b8s header.parentHash.toB8L,
    BLT.b8s header.ommersHash.toB8L,
    BLT.b8s header.coinbase.toB8L,
    BLT.b8s header.stateRoot.toB8L,
    BLT.b8s header.txsRoot.toB8L,
    BLT.b8s header.receiptRoot.toB8L,
    BLT.b8s header.bloom,
    BLT.b8s header.difficulty.toB8L,
    BLT.b8s header.number.toB8L,
    BLT.b8s header.gasLimit.toB8L,
    BLT.b8s header.gasUsed.toB8L,
    BLT.b8s header.timestamp.toB8L,
    BLT.b8s header.extraData,
    BLT.b8s header.prevRandao.toB8L,
    BLT.b8s header.nonce.toB8L,
    BLT.b8s header.baseFeePerGas.toB8L,
    BLT.b8s header.withdrawalsRoot.toB8L,
    BLT.b8s header.blobGasUsed.toB8L,
    BLT.b8s header.excessBlobGas.toB8L,
    BLT.b8s header.parentBeaconBlockRoot.toB8L
  ] ++
    match header.requestsHash with
    | none => []
    | some rh => [BLT.b8s rh.toB8L]

structure Tx : Type where
  (nonce : B64)
  (gas : Nat)
    (value : Nat)
  (data : B8L)
  (v : Nat)
  (r : B8L)
  (s : B8L)
  (type : TxType)

structure Block : Type where
  header : Header
  txs : List (B8L ⊕ Tx)
  ommers : List Header
  wds : List Withdrawal

structure BlockChain : Type where
  blocks : List Block
  state : State
  chainId : B64

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

def B8L.sig (bs : B8L) : B8L := List.dropWhile (· = 0) bs

def AccessList.toBLT (al : AccessList) : BLT :=
  let aux : Adr × List B256 → BLT
  | ⟨adr, words⟩ =>
    .list [.b8s adr.toB8L, .list (words.map (.b8s ∘ B256.toB8L))]
  .list (al.map aux)

def Auth.toBLT (auth : Auth) : BLT :=
  .list [
    .b8s auth.chainId.toB8L.sig,
    .b8s <| auth.address.toB8L,
    .b8s auth.nonce.toNat.toB8L,
    .b8s auth.yParity.toB8L,
    -- `r` and `s` are RLP scalars, so they must re-encode minimally: a fixed
    -- 32-byte encoding diverges from the canonical bytes whenever a signature
    -- scalar has a leading zero byte, corrupting both the type-4 signing hash
    -- and the transactions trie.
    .b8s auth.r.toB8L.sig,
    .b8s auth.s.toB8L.sig,
  ]

def Tx.toBLT (tx : Tx) : BLT :=
  match tx.type with
  | .zero gasPrice receiver =>
    .list [
      .b8s tx.nonce.toNat.toB8L,
      .b8s gasPrice.toB8L,
      .b8s tx.gas.toB8L,
      .b8s <| receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      .b8s tx.v.toB8L,
      .b8s (trimZero tx.r),
      .b8s (trimZero tx.s),
    ]
  | .one chainId gasPrice receiver accessList =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8L,
      .b8s gasPrice.toB8L,
      .b8s tx.gas.toB8L,
      .b8s <| receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      accessList.toBLT,
      .b8s tx.v.toB8L,
      .b8s (trimZero tx.r),
      .b8s (trimZero tx.s)
    ]
  | .two chainId maxPriorityFee maxFee receiver accessList =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8L,
      .b8s maxPriorityFee.toB8L,
      .b8s maxFee.toB8L,
      .b8s tx.gas.toB8L,
      .b8s <| receiver.rec [] Adr.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      accessList.toBLT,
      .b8s tx.v.toB8L,
      .b8s (trimZero tx.r),
      .b8s (trimZero tx.s)
    ]
  | .three chainId maxPriorityFee maxFee receiver accessList maxBlobFee blobHashes =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8L,
      .b8s maxPriorityFee.toB8L,
      .b8s maxFee.toB8L,
      .b8s tx.gas.toB8L,
      .b8s receiver.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      accessList.toBLT,
      .b8s maxBlobFee.toB8L,
      .list <| blobHashes.map <| .b8s ∘ B256.toB8L,
      .b8s tx.v.toB8L,
      .b8s (trimZero tx.r),
      .b8s (trimZero tx.s)
    ]
  | .four chainId maxPriorityFee maxFee receiver accessList auths =>
    .list [
      .b8s chainId.toB8L.sig,
      .b8s tx.nonce.toNat.toB8L,
      .b8s maxPriorityFee.toB8L,
      .b8s maxFee.toB8L,
      .b8s tx.gas.toB8L,
      .b8s receiver.toB8L,
      .b8s tx.value.toB8L,
      .b8s tx.data,
      accessList.toBLT,
      .list <| auths.map <| Auth.toBLT,
      .b8s tx.v.toB8L,
      .b8s (trimZero tx.r),
      .b8s (trimZero tx.s)
    ]

def Auth.toStrings (auth : Auth) : List String :=
  fork
    "auth"
    [
      [s!"chain ID : {auth.chainId}"],
      [s!"address : {auth.address}"],
      [s!"nonce : {auth.nonce.toHex}"],
      [s!"y parity : {auth.yParity}"],
      [s!"r : {auth.r.toHex}"],
      [s!"s : {auth.s.toHex}"]
    ]

def Auths.toStrings (al : List Auth) : List String :=
    fork "auth list" <| al.map <| Auth.toStrings

def TxType.toStrings : TxType → List String
  | zero
    (gasPrice : Nat)
    (receiver : Option Adr) =>
    fork "Type-0" [
      [s!"gas price : {gasPrice.repr}"],
      [s!"receiver : {toString receiver}"]
    ]
  | one
    (chainId : B64)
    (gasPrice : Nat)
    (receiver : Option Adr)
    (accessList : AccessList) =>
    fork "Type-1" [
      [s!"chain ID : {chainId}"],
      [s!"gas price : {gasPrice.repr}"],
      [s!"receiver : {toString receiver}"],
      accessList.toStrings
    ]
  | two
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Option Adr)
    (accessList : AccessList) =>
    fork "Type-2" [
      [s!"chain ID : {chainId}"],
      [s!"max priority fee : {maxPriorityFee.repr}"],
      [s!"max fee : {maxFee.repr}"],
      [s!"receiver : {toString receiver}"],
      accessList.toStrings
    ]
  | three
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Adr)
    (accessList : AccessList)
    (maxBlobFee : Nat)
    (blobHashes : List B256) =>
    fork "Type-3" [
      [s!"chain ID : {chainId}"],
      [s!"max priority fee : {maxPriorityFee.repr}"],
      [s!"max fee : {maxFee.repr}"],
      [s!"receiver : {toString receiver}"],
      accessList.toStrings,
      [s!"max blob fee : {maxBlobFee.repr}"],
      fork "blob hashes" (blobHashes.map <| fun bh => [bh.toHex])
    ]
  | four
    (chainId : B64)
    (maxPriorityFee : Nat)
    (maxFee : Nat)
    (receiver : Adr)
    (accessList : AccessList)
    (auths : List Auth) =>
    fork "Type-4" [
      [s!"chain ID : {chainId}"],
      [s!"max priority fee : {maxPriorityFee.repr}"],
      [s!"max fee : {maxFee.repr}"],
      [s!"receiver : {toString receiver}"],
      accessList.toStrings,
      Auths.toStrings auths
    ]

instance : ToString TxType := ⟨String.joinln ∘ TxType.toStrings⟩

def Tx.toStrings (tx : Tx) : List String :=
  fork "tx" [
    [s!"nonce : {tx.nonce.toHex}"],
    [s!"gas limit : {tx.gas}"],
    [s!"value : {tx.value.repr}"],
    [s!"calldata : {tx.data.toHex}"],
    [s!"v : {tx.v}"],
    [s!"r : {tx.r.toHex}"],
    [s!"s : {tx.s.toHex}"],
    tx.type.toStrings
  ]

instance : ToString Tx := ⟨String.joinln ∘ Tx.toStrings⟩

def B8LOrTxToBLT : B8L ⊕ Tx → BLT
  | .inl bs => BLT.b8s bs
  | .inr tx => tx.toBLT

def Withdrawal.toBLT (wd : Withdrawal) : BLT :=
  BLT.list [
    BLT.b8s wd.globalIndex.toB8L.sig,
    BLT.b8s wd.validatorIndex.toB8L.sig,
    BLT.b8s wd.recipient.toB8L,
    BLT.b8s wd.amount.toB8L.sig
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
abbrev NTB := Std.TreeMap (List B8) (List B8) (@List.compare _ ⟨B8.compareLows⟩)

def NTB.toStrings (s : NTB) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B8L × B8L → List String :=
    λ nb => [s!"{B4L.toHex (nb.fst.map B8.lows)} : {nb.snd.toHex}"]
  fork "NTB" (kvs.map kvToStrings)

def hpAux : B8L → (Option B8 × B8L)
  | [] => ⟨none, []⟩
  | n :: ns =>
    match hpAux ns with
    | ⟨none, bs⟩ => ⟨some n, bs⟩
    | ⟨some m, bs⟩ => ⟨none, ((n <<< 4) ||| m.lows) :: bs⟩

def hp (ns : B8L) (t : Bool) : B8L :=
  match hpAux ns with
  | ⟨none, bs⟩ => (cond t (0x20) 0) :: bs
  | ⟨some n, bs⟩ => ((cond t 0x30 0x10) ||| n.lows) :: bs

def commonPrefixCore : B8L → B8L → B8L
  | [], _ => []
  | _, [] => []
  | n :: ns, n' :: ns' =>
    if n = n' then n :: commonPrefixCore ns ns'
    else []

def commonPrefix (n : B8) (ns : B8L) : List B8L → Option B8L
  | [] => some (n :: ns)
  | ns' :: nss =>
    match commonPrefixCore (n :: ns) ns' with
    | [] => none
    | (n' :: ns'') => commonPrefix n' ns'' nss

def NTB.empty : NTB := Std.TreeMap.empty

def sansPrefix : B8L → B8L → Option B8L
  | [], ns => some ns
  | _, [] => none
  | n :: ns, n' :: ns' =>
    if n = n' then sansPrefix ns ns' else none

def insertSansPrefix (pfx : B8L) (m : NTB) (ns : B8L) (bs : B8L) : Option NTB := do
  (m.insert · bs) <$> sansPrefix pfx ns

def NTB.factor (m : NTB) : Option (B8L × NTB) := do
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

def NTBs.update (js : NTBs) (f : NTB → NTB) (k : B8) : NTBs :=
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

def NTBs.insert (js : NTBs) : B8L → B8L → NTBs
  | [], _ => js
  | n :: ns, bs => js.update (Std.TreeMap.insert · ns bs) n

def Std.TreeMap.isSingleton {K V : Type} (cmp : K → K → Ordering)
    (m : Std.TreeMap K V cmp) : Bool :=
  m.size = 1

mutual

  def nodeComp : Nat → NTB → BLT
    | 0, _ => .b8s []
    | k + 1, j =>
      if j.isEmpty
      then .b8s []
      else let r := structComp k j
           if r.toB8L.length < 32
           then r
           else .b8s <| r.toB8L.keccak.toB8L

  def structComp : Nat → NTB → BLT
    | 0, _ => .b8s []
    | k + 1, j =>
      if j.isEmpty
            then .b8s []       else if j.isSingleton
           then match j.toList with
                | [(k, v)] => .list [.b8s (hp k 1), .b8s v]
                | _ => .b8s []            else match j.factor with
                | none =>
                  let js := Std.TreeMap.foldl NTBs.insert NTBs.empty j
                  .list [ nodeComp k js.x0, nodeComp k js.x1, nodeComp k js.x2,
                          nodeComp k js.x3, nodeComp k js.x4, nodeComp k js.x5,
                          nodeComp k js.x6, nodeComp k js.x7, nodeComp k js.x8,
                          nodeComp k js.x9, nodeComp k js.xA, nodeComp k js.xB,
                          nodeComp k js.xC, nodeComp k js.xD, nodeComp k js.xE,
                          nodeComp k js.xF, .b8s (j.getD [] []) ]
                | some (pfx, j') => .list [.b8s (hp pfx 0), nodeComp k j']

end

def NTB.maxKeyLength (j : NTB) : Nat :=
  (j.toList.map (List.length ∘ Prod.fst)).maxD 0

def collapse (j : NTB) : BLT := structComp (2 * (j.maxKeyLength + 1)) j

def trie (j : NTB) : B256 :=
  B8L.keccak <| (collapse j).toB8L

def B256.toBLT (w : B256) : BLT := .b8s w.toB8L

def Stor.toNTB (s : Stor) : NTB :=
  let f : NTB → B256 → B256 → NTB :=
    λ j k v =>
      j.insert
        k.keccak.toB4s
        ((BLT.toB8L <| .b8s <| B8L.sig <| v.toB8L))
  Std.TreeMap.foldl f NTB.empty s

def B256.zerocount (x : B256) : Nat → Nat
  | 0 => 0
  | k + 1 => if x = 0 then k + 1 else B256.zerocount (x >>> 8) k

def B256.bytecount (x : B256) : Nat := 32 - (B256.zerocount x 32)

def toKeyVal (pr : Adr × Acct) : B8L × B8L :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨
    ad.toB8L.keccak.toB4s,
    let val' :=
      BLT.toB8L <| .list [
        .b8s (ac.nonce.toB8L.sig),
        .b8s (ac.bal.toB8L.sig),
        B256.toBLT (trie ac.stor.toNTB),
        B256.toBLT <| (B8L.keccak ac.code.toList)
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
-- `maxCodeSize` and `maxInitCodeSize` are fork rules, not global constants:
-- see `ForkRules.code` in `Elevm/Fork.lean`.
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
def depositRequestType : B8L := [0]
def withdrawalRequestType : B8L := [1]
def consolidationRequestType : B8L := [2]
def withdrawalRequestPredeployAddress : Adr := 0x00000961Ef480Eb55e80D19ad83579A64c007002
def consolidationRequestPredeployAddress : Adr := 0x0000BBdDc7CE488642fb579F8B00f3a590007251
def historyStorageAddress : Adr := 0x0000F90827F1C53a10cb7A02335B175320002935
def emptyOmmerHash : B256 := (BLT.list []).toB8L.keccak
def setCodeTxMagic : B8L := [0x05]
def beaconRootsAddress : Adr := 0x000F3df6D732807Ef1319fB7B8bB8522d0Beac02
def systemAddress : Adr := 0xfffffffffffffffffffffffffffffffffffffffe
def systemTransactionGas : Nat := 30000000
def versionedHashVersionKzg : B8 := 0x01
def eoaDelegationMarker : B8L := [0xEF, 0x01, 0x00]
def gasBlake2PerRound : Nat := 1
def eoaDelegatedCodeLength : Nat := 23
-- The blob target, ceiling, and base-fee update fraction are fork rules, not
-- global constants: see `ForkRules.blob` in `Elevm/Fork.lean`.
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
  data : Array B8
  size : Nat

def Mem.empty : Mem := ⟨.empty, 0⟩

structure Log : Type where
  (address : Adr)
  (topics : List B256)
  (data : B8L)

structure BenvStat : Type where
  /-- The rules this block runs under.
  Carrying them here, rather than as an extra argument, is what keeps a single
  interpreter: every function that already sees a `BenvStat` -- directly, or
  through `Benv`, `Msg`, or `Sevm` -- can read the active rules without a
  signature change, and nothing anywhere needs to know which fork it is. -/
  rules : ForkRules
  chainId : B64
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
  data: B8L
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
def intrinsicGasTooLowTag : String := "IntrinsicGasTooLowError"
def invalidChainIdTag : String := "InvalidChainIdError"
def nonceIsMaxTag : String := "NonceIsMaxError"
def nonceMismatchTooHighTag : String := "NonceMismatchTooHighError"
def nonceMismatchTooLowTag : String := "NonceMismatchTooLowError"
def priorityGreaterThanMaxFeeTag : String := "PriorityGreaterThanMaxFeeError"
def senderNotEoaTag : String := "SenderNotEoaError"
def type3BlobCountExceededTag : String := "Type3BlobCountExceededError"
def type3ContractCreationTag : String := "Type3ContractCreationError"
def type3InvalidBlobVersionedHashTag : String :=
  "Type3InvalidBlobVersionedHashError"
def type3ZeroBlobsTag : String := "Type3ZeroBlobsError"
def type4ContractCreationTag : String := "Type4ContractCreationError"
def emptyAuthorizationListTag : String := "EmptyAuthorizationListError"

def transactionExceptionTags : List String :=
  [ gasPriceProductOverflowTag, gasAllowanceExceededTag,
    initcodeSizeExceededTag, insufficientAccountFundsTag,
    insufficientMaxFeePerGasTag, intrinsicGasTooLowTag, invalidChainIdTag, nonceIsMaxTag,
    nonceMismatchTooHighTag, nonceMismatchTooLowTag,
    priorityGreaterThanMaxFeeTag, senderNotEoaTag,
    type3BlobCountExceededTag, type3ContractCreationTag,
    type3InvalidBlobVersionedHashTag, type3ZeroBlobsTag,
    type4ContractCreationTag, emptyAuthorizationListTag ]

#guard transactionExceptionTags.length = 18
#guard transactionExceptionTags.eraseDups.length = 18
#guard transactionExceptionTags.all fun t =>
  (transactionExceptionTags.filter fun u => t.isPrefixOf u).length = 1

def isInvalidTransaction (err : String) : Bool :=
  List.any transactionExceptionTags (hasErrorType err) ||
  List.any [
    "InvalidSignatureError",
    "TransactionTypeError",
    "InsufficientMaxFeePerBlobGasError",
    emptyAuthorizationListTag
  ] (hasErrorType err)

------------------- BLOCK-REJECTION REASONS --------------------

-- One tag per reason a header or a post-transition check can reject a block.
-- A bare `"InvalidBlock"` says only that *some* consensus rule failed, which is
-- exactly what let a block be rejected for the wrong reason and still be scored
-- as a pass: the official fixture vocabulary names ~17 distinct block
-- identities, and one string cannot be mapped to them. Each tag below is the
-- sole producer of its reason, so `Elevm/FixtureException.lean` can route it to
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

/-- Every block-rejection tag. The single source of truth for the distinctness
checks, and for `isBlockException`. -/
def blockExceptionTags : List String :=
  [ gasLimitTooBigTag, gasLimitAdjustmentTag, gasUsedOverflowTag,
    gasUsedMismatchTag, timestampOlderThanParentTag, blockNumberTag,
    baseFeePerGasTag, difficultyOverParisTag, ommersOverParisTag,
    extraDataTooBigTag, unknownParentTag, unknownParentZeroTag,
    stateRootTag, transactionsRootTag, receiptsRootTag, logBloomTag,
    withdrawalsRootTag, headerNonceTag, excessBlobGasTag, blobGasUsedTag,
    requestsHashTag, depositEventLayoutTag, systemContractCallFailedTag ]

/-- Is this error one of the precise block-rejection reasons? -/
def isBlockException (err : String) : Bool :=
  List.any blockExceptionTags (hasErrorType err)

-- The tags are distinct, and none is a prefix of another. `hasErrorType` reads
-- a tag up to a fixed " : ", so a tag that prefixed another could be read as
-- the wrong reason -- and one reason read as another is precisely the defect
-- this vocabulary exists to remove.
#guard blockExceptionTags.length = 23
#guard blockExceptionTags.eraseDups.length = 23
#guard blockExceptionTags.all fun t =>
  (blockExceptionTags.filter fun u => t.isPrefixOf u).length = 1

-- No tag is readable as the broad category it replaces, in either direction.
#guard blockExceptionTags.all fun t => ¬ hasErrorType t "InvalidBlock"
#guard ¬ isBlockException "InvalidBlock"
#guard ¬ isBlockException "InvalidBlock : gas limit is wrong"

------------------- STRICT CONSENSUS-FIELD DECODERS --------------------

-- The `Except`-level face of the strict shape checks in `Elevm/Types.lean`.
-- Each helper names one precise reason a consensus field can be malformed, in
-- the `hasErrorType` tag convention the rest of the executable uses: a bare tag,
-- or a tag followed by " : " and free diagnostic text. The tags are separate
-- because the official fixture identities are separate -- a scalar wider than
-- 64 bits is `RLP_INVALID_FIELD_OVERFLOW_64`, a wrong list shape is
-- `RLP_STRUCTURES_ENCODING` -- so one generic `"DecodingError"` covering both
-- cannot be classified. `Elevm/FixtureException.lean` routes these exact tags;
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
def B8L.toRlpFixed (name : String) (n : Nat) (xs : B8L) : Except String B8L :=
  (xs.toFixed? n).toExcept
    s!"{rlpFixedWidthTag} : {name} must be exactly {n} bytes, but is {xs.length}"

/-- A fixed-width 32-byte hash or root, as a `B256`. `B8L.toB256?` is already an
exact-width decoder, so this adds the precise reason rather than a check. Note
these fields are *bytes*, not scalars: a root may legitimately begin with a zero
byte, so the canonical-scalar rule must not be applied to them. -/
def B8L.toRlpHash (name : String) (xs : B8L) : Except String B256 :=
  xs.toB256?.toExcept
    s!"{rlpFixedWidthTag} : {name} must be exactly 32 bytes, but is {xs.length}"

/-- A fixed-width 8-byte field, as a `B64`. Like `toRlpHash`, this is bytes
rather than a scalar: the header nonce is eight bytes of zeroes, not empty. -/
def B8L.toRlpFixedB64 (name : String) (xs : B8L) : Except String B64 :=
  xs.toB64?.toExcept
    s!"{rlpFixedWidthTag} : {name} must be exactly 8 bytes, but is {xs.length}"

/-- The canonicality half of scalar checking, shared by every width. The
overflow tag is a parameter because the width is what the official vocabulary
distinguishes, while non-canonical encoding is one reason at every width. -/
private def rlpScalarBytes (overflowTag name : String) (n : Nat) (xs : B8L) :
  Except String B8L := do
  if xs.length > n then
    .error
      s!"{overflowTag} : {name} scalar is {xs.length} bytes, \
         exceeding its {n}-byte width"
  if xs.head? = some (0 : B8) then
    .error
      s!"{rlpLeadingZerosTag} : {name} scalar 0x{B8L.toHex xs} \
         is not canonically encoded (leading zero byte)"
  .ok xs

/-- A canonical unsigned scalar of at most `n` bytes, as a `Nat`. Overflow is
reported against the 256-bit identity, this being the widest scalar the
consensus fields have; a field modelled as 64 bits must use `toRlpB64`. -/
def B8L.toRlpNat (name : String) (n : Nat) (xs : B8L) : Except String Nat := do
  let xs ← rlpScalarBytes rlpFieldOverflow256Tag name n xs
  .ok xs.toNat

/-- A canonical 64-bit scalar: at most eight bytes, converted without
truncation. -/
def B8L.toRlpB64 (name : String) (xs : B8L) : Except String B64 := do
  let xs ← rlpScalarBytes rlpFieldOverflow64Tag name 8 xs
  .ok xs.toB64

/-- A canonical 256-bit scalar: at most thirty-two bytes, converted without
truncation. -/
def B8L.toRlpB256 (name : String) (xs : B8L) : Except String B256 := do
  let xs ← rlpScalarBytes rlpFieldOverflow256Tag name 32 xs
  .ok xs.toB256

/-- An address field: exactly twenty bytes. -/
def B8L.toRlpAdr (name : String) (xs : B8L) : Except String Adr :=
  xs.toAdr?.toExcept
    s!"{rlpFixedWidthTag} : {name} must be exactly 20 bytes, but is {xs.length}"

/-- An optional contract-creation receiver: empty, or exactly twenty bytes. -/
def B8L.toRlpReceiver (name : String) (xs : B8L) : Except String (Option Adr) :=
  xs.toReceiver?.toExcept
    s!"{rlpFixedWidthTag} : {name} must be empty or exactly 20 bytes, \
       but is {xs.length}"

--------------- STRICT DECODER REGRESSION CHECKS ----------------

-- Each reason is reported under its own tag, and each tag is recognized by the
-- `hasErrorType` convention the classifier reads -- an exact tag, or a tag
-- opening detail text at " : ". Accepted values are checked too: the point of
-- rejecting a nine-byte index is to keep the eight-byte ones exact.

private def rlpTags : List String :=
  [ rlpStructureTag, rlpFixedWidthTag, rlpFieldOverflow64Tag,
    rlpFieldOverflow256Tag, rlpLeadingZerosTag,
    rlpWithdrawalsNotReadTag, rlpRoundTripTag ]

-- The tags are distinct, and none is a prefix of another: `hasErrorType` reads
-- a tag up to a fixed " : ", so one tag must never be readable as another.
#guard rlpTags.eraseDups.length = 7
#guard rlpTags.all fun t => (rlpTags.filter fun u => t.isPrefixOf u).length = 1

-- The strict tags are not readable as either of the old generic categories.
#guard rlpTags.all fun t => ¬ hasErrorType t "DecodingError"
#guard rlpTags.all fun t => ¬ hasErrorType t "EncodingError"
#guard rlpTags.all fun t => ¬ hasErrorType t "InvalidBlock"
#guard rlpTags.all fun t => ¬ hasErrorType t "InvalidTransaction"

private def errOf {α : Type} : Except String α → String
  | .error e => e
  | .ok _ => "unexpected success"

private def hasTag {α : Type} (tag : String) (e : Except String α) : Bool :=
  hasErrorType (errOf e) tag

-- Fixed-width fields: both the short and the long side are width errors.
#guard (B8L.toRlpFixed "root" 32 (List.replicate 32 (0x11 : B8))).toOption.isSome
#guard hasTag rlpFixedWidthTag (B8L.toRlpFixed "root" 32 (List.replicate 31 (0x11 : B8)))
#guard hasTag rlpFixedWidthTag (B8L.toRlpFixed "root" 32 (List.replicate 33 (0x11 : B8)))

-- 64-bit scalars: accepted widths convert exactly, nine bytes is an overflow
-- rather than a truncation, and a leading zero is a distinct reason from an
-- overflow. This is the withdrawal-index case.
#guard (B8L.toRlpB64 "index" []).toOption.map B64.toNat = some 0
#guard (B8L.toRlpB64 "index" (List.replicate 8 (0xFF : B8))).toOption.map B64.toNat
  = some (2 ^ 64 - 1)
#guard hasTag rlpFieldOverflow64Tag
  (B8L.toRlpB64 "index" (0x01 :: List.replicate 8 (0x00 : B8)))
#guard hasTag rlpLeadingZerosTag (B8L.toRlpB64 "index" [0x00, 0x01])
#guard ¬ hasTag rlpFieldOverflow64Tag (B8L.toRlpB64 "index" [0x00, 0x01])
#guard ¬ hasTag rlpLeadingZerosTag
  (B8L.toRlpB64 "index" (0x01 :: List.replicate 8 (0x00 : B8)))

-- 256-bit scalars: same reasons, one width up, under the 256-bit overflow tag.
#guard (B8L.toRlpB256 "amount" (List.replicate 32 (0xFF : B8))).toOption.map B256.toNat
  = some (2 ^ 256 - 1)
#guard hasTag rlpFieldOverflow256Tag
  (B8L.toRlpB256 "amount" (List.replicate 33 (0x01 : B8)))
#guard hasTag rlpLeadingZerosTag (B8L.toRlpB256 "amount" [0x00, 0x01])
#guard (B8L.toRlpNat "value" 32 (List.replicate 32 (0xFF : B8))).toOption
  = some (2 ^ 256 - 1)
#guard hasTag rlpFieldOverflow256Tag (B8L.toRlpNat "value" 32 (List.replicate 33 (0x01 : B8)))

-- Addresses and optional receivers: a width error, never a silent creation.
#guard (B8L.toRlpAdr "recipient" (List.replicate 20 (0x11 : B8))).toOption.isSome
#guard hasTag rlpFixedWidthTag (B8L.toRlpAdr "recipient" (List.replicate 19 (0x11 : B8)))
#guard hasTag rlpFixedWidthTag (B8L.toRlpAdr "recipient" (List.replicate 21 (0x11 : B8)))
#guard hasTag rlpFixedWidthTag (B8L.toRlpAdr "recipient" [])
#guard (B8L.toRlpReceiver "receiver" []).toOption = some none
#guard (B8L.toRlpReceiver "receiver" (List.replicate 20 (0x11 : B8))).toOption.isSome
#guard hasTag rlpFixedWidthTag (B8L.toRlpReceiver "receiver" (List.replicate 21 (0x11 : B8)))

-- A structure failure is its own reason, not a width or overflow one.
#guard hasErrorType (rlpStructureError "block" "expected a 4-item list") rlpStructureTag
#guard ¬ hasErrorType (rlpStructureError "block" "expected a 4-item list") rlpFixedWidthTag

@[ext]
structure Mach : Type where
  stack : List B256
  memory : Mem
  gasLeft : Nat

@[ext]
structure Meta : Type where
  logs : List Log
  refundCounter : Int
  output : B8L
  accountsToDelete : AdrSet
  returnData : B8L
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
def Devm.output (devm : Devm) : B8L := devm.meta.output
def Devm.accountsToDelete (devm : Devm) : AdrSet := devm.meta.accountsToDelete
def Devm.returnData (devm : Devm) : B8L := devm.meta.returnData
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
  data : B8L
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

def Devm.withOutput (devm : Devm) (output : B8L) : Devm :=
  devm.setMeta {devm.meta with output := output}

def Devm.withAccountsToDelete (devm : Devm) (accountsToDelete : AdrSet) : Devm :=
  devm.setMeta {devm.meta with accountsToDelete := accountsToDelete}

def Devm.withReturnData (devm : Devm) (returnData : B8L) : Devm :=
  devm.setMeta {devm.meta with returnData := returnData}

def Devm.withError (devm : Devm) (error : Option String) : Devm :=
  devm.setMeta {devm.meta with error := error}

def Devm.withAccessedAddresses (devm : Devm) (accessedAddresses : AdrSet) : Devm :=
  devm.setMeta {devm.meta with accessedAddresses := accessedAddresses}

def Devm.withAccessedStorageKeys (devm : Devm) (accessedStorageKeys : KeySet) : Devm :=
  devm.setMeta {devm.meta with accessedStorageKeys := accessedStorageKeys}

def Devm.withCreatedAccounts (devm : Devm) (createdAccounts : AdrSet) : Devm :=
  devm.setMeta {devm.meta with createdAccounts := createdAccounts}

def Devm.withState (devm : Devm) (state : State) : Devm :=
  devm.setWorld {devm.world with state := state}

def Devm.withTransientStorage (devm : Devm) (transientStorage : Tra) : Devm :=
  devm.setWorld {devm.world with transientStorage := transientStorage}

def Stack.toStrings (stack : List B256) : List String :=
  fork "STACK" [
    ["-------------------------- STACK TOP ---------------------------"] ++
    stack.map B256.toHex ++
    ["------------------------- STACK BOTTOM -------------------------"]
  ]

def Mem.toStrings (mem : Mem) : List String :=
  fork "MEM" [
    String.chunks 64 <| B8L.toHex mem.data.toList
  ]

def mkSingleton {ξ : Type u} : ξ → List ξ
  | x => [x]

def Log.toStrings (l : Log) : List String :=
  fork "log" [
    [s!"address : {l.address.toHex}"],
    fork "topics" (l.topics.map (mkSingleton ∘ B256.toHex)),
    fork "data" [String.chunks 64 l.data.toHex]
  ]

def Tra.toStrings (tra : Tra) : List String :=
  fork "TRANSIENT STORAGE" <| tra.toList.map <|
    fun kv =>
      fork kv.fst.toHex <| kv.snd.toList.map <|
        mkSingleton ∘ fun kv' => s!"{kv'.fst.toHex} : {B256.toHex kv'.snd}"

def Msg.toStrings (msg : Msg) : List String  :=
  fork "MESSAGE" [
    [s!"caller : {msg.caller.toHex}"],
    [s!"target : {(msg.target.rec "NONE" Adr.toHex : String)}"],
    [s!"current target : {msg.currentTarget.toHex}"],
    [s!"gas : {msg.gas}"],
    [s!"value : {msg.value.toHex}"],
    [s!"data : {msg.data.toHex}"],
    [s!"code address : {(msg.codeAddress.rec "None" Adr.toHex : String)}"],
    fork "CODE" [String.chunks 64 <| B8L.toHex msg.code.toList],
    [s!"depth : {msg.depth}"],
    [s!"should transfer value : {msg.shouldTransferValue}"],
    [s!"is static : {msg.isStatic}"],
    fork "ACCESSED ADDRESSES"
      (msg.accessedAddresses.toList.map (mkSingleton ∘ Adr.toHex)),
    fork "ACCESSED STORAGE KEYS"
      (msg.accessedStorageKeys.toList.map (fun kv => [s!"{kv.fst.toHex} : {B256.toHex kv.snd}"]))
  ]

def BenvStat.toStrings (bs : BenvStat) : List String :=
  fork "BLOCK ENVIRONMENT" [
    [s!"FORK : {bs.rules.fork}"],
    [s!"CHAIN ID : {bs.chainId}"],
    [s!"BLOCK GAS LIMIT : {bs.blockGasLimit}"],
    fork "BLOCK HASHES" (bs.blockHashes.map (mkSingleton ∘ B256.toHex)),
    [s!"COINBASE : {bs.coinbase}"],
    [s!"BASE FEE PER GAS : {bs.baseFeePerGas}"],
    [s!"TIME : {bs.time.toHex}"],
    [s!"PREVRANDAO : {bs.prevRandao.toHex}"],
    [s!"EXCESS BLOB GAS : {bs.excessBlobGas}"],
    [s!"PARENT BEACON BLOCK ROOT : {bs.parentBeaconBlockRoot.toHex}"]
  ]

def Benv.toStrings (benv : Benv) : List String :=
  fork "BLOCK ENVIRONMENT" [
    fork "STATE" [State.toStrings benv.state],
    fork "STAT" [benv.stat.toStrings]
  ]

def Evm.toStrings (evm : Evm) : List String :=
  let mach := evm.dyna.mach
  let metaView := evm.dyna.meta
  fork "EVM" [
    [s!"PC : {evm.pc}"],
    Stack.toStrings mach.stack,
    Mem.toStrings mach.memory,
    [s!"CODE : {B8L.toHex evm.sta.code.toList}"],
    [s!"GAS LEFT : {mach.gasLeft}"],
    fork "LOGS" (metaView.logs.map Log.toStrings),
    [s!"REFUND COUNTER : {metaView.refundCounter}"],
    ["MSG : *print unimplemented*"], --Msg.toStrings evm.msg,
    [s!"output : {metaView.output.toHex}"],
    fork "ACCOUNTS TO DELETE"
      (metaView.accountsToDelete.toList.map (mkSingleton ∘ Adr.toHex)),
    [s!"return data : {metaView.returnData.toHex}"],
    fork "ACCESSED ADDRESSES"
      (metaView.accessedAddresses.toList.map (mkSingleton ∘ Adr.toHex)),
    fork "ACCESSED STORAGE KEYS"
      (metaView.accessedStorageKeys.toList.map (fun kv => [s!"{kv.fst.toHex} : {B256.toHex kv.snd}"]))
  ]

-- Precompile activation is a fork rule and lives with the rules:
-- `ForkRules.isPrecomp` in `Elevm/Fork.lean` replaces what used to be a
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
  | push : ∀ bs : B8L, bs.length ≤ 32 → Ninst

def Ninst.toOpString : Ninst → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push bs _ => "PUSH" ++ bs.length.repr

def Ninst.toString : Ninst → String
  | reg o => Rinst.toString o
  | exec o => Xinst.toString o
  | push [] _ => "PUSH0"
  | push bs _ => "PUSH" ++ bs.length.repr ++ " " ++ B8L.toHex bs

instance : ToString Ninst := ⟨Ninst.toString⟩
instance : Repr Ninst := ⟨λ i _ => i.toString⟩

inductive Inst : Type
  | last : Linst → Inst
  | next : Ninst → Inst
  | jump : Jinst → Inst

inductive InstType
  | R | X | J | L | P

def B8.toInstType (b : B8) : InstType :=
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

lemma B8.shl_highs_or_lows_eq_self (x : B8) : (x.highs <<< 4) ||| x.lows = x := by
  apply UInt8.toNat_inj.mp
  unfold B8.lows
  rw [UInt8.toNat_or]
  rw [UInt8.toNat_and]
  have rw : UInt8.toNat 15 = 15 := by rfl
  rw [rw]; clear rw
  rw [Nat.and_two_pow_sub_one_eq_mod _ 4]
  have hh := Nat.hi_or_lo
  rw [UInt8.toNat_shiftLeft]
  unfold B8.highs
  rw [UInt8.toNat_shiftRight]
  have rw : (UInt8.toNat 4 % 8) = 4 := by rfl
  rw [rw]; clear rw
  have hh := Nat.hi_le x.toNat 4
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt _ (UInt8.toNat_lt x))]
  · apply Nat.hi_or_lo
  · apply Nat.hi_le

lemma B8.lt_of_highs_lt_highs (x y : B8) (lt : x.highs < y.highs) : x < y := by
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

lemma le_of_toInstType_eq_p (b : B8) (h : b.toInstType = .P) :
    b.toNat ≤ 127 := by
  apply Nat.le_of_lt_succ
  apply (@UInt8.lt_iff_toNat_lt b 0x80).mp
  apply B8.lt_of_highs_lt_highs
  simp [B8.toInstType] at h; split at h
  · split at h <;> cases h
  · rename (B8.highs _ =  _) => heq; rw [heq]
    apply (@UInt8.lt_iff_toNat_lt 5 8).mpr; simp
  · rename (B8.highs _ =  _) => heq; rw [heq]
    apply (@UInt8.lt_iff_toNat_lt 6 8).mpr; simp
  · rename (B8.highs _ =  _) => heq; rw [heq]
    apply (@UInt8.lt_iff_toNat_lt 7 8).mpr; simp
  · split at h <;> cases h
  · cases h

def ByteArray.getInst (code : ByteArray) (pc : Nat) : Option Inst :=
  if pc < code.size
  then
    let b : B8 := code.get! pc
    match h : b.toInstType with
    | .R => b.toRinst <&> (.next ∘ .reg)
    | .X => b.toXinst <&> (.next ∘ .exec)
    | .J => b.toJinst <&> .jump
    | .L => b.toLinst <&> .last
    | .P =>
      let le := le_of_toInstType_eq_p b h
      let bs : B8L := code.sliceD (pc + 1) (b.toNat - 95) 0
      let le' : bs.length ≤ 32 := by
        simp [bs, ByteArray.length_sliceD, le]
      some <| .next <| .push bs le'
  else
    some (.last .stop)

def Evm.getInst (evm : Evm) : Option Inst :=
  ByteArray.getInst evm.sta.code evm.pc

def fakeExpAux (num den i : Nat) : Nat → Nat → Nat
  | _, 0 => panic! "error : recursion limit reached for fake exponentiation"
  | 0, _ => 0
  | numAcc, lim + 1 =>
    let numAcc' := (numAcc * num) / (den * i)
    numAcc + fakeExpAux num den (i + 1) numAcc' lim

def fakeExp (fac num den : Nat) : Nat :=
  let lim := (max (fac * num) <| num * num) + 2
  let out := fakeExpAux num den 1 (fac * den) lim
  out / den

def calculate_blob_gas_price (blob : BlobSchedule) (excessBlobGas : Nat) : Nat :=
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

def access_cost (x : Adr) (a : AdrSet) : Nat :=
  if x ∈ a then gasWarmAccess else gasColdAccountAccess

def Meta.addAccessedAddress (view : Meta) (a : Adr) : Meta :=
  {view with accessedAddresses := view.accessedAddresses.insert a}

def addAccessedAddress (devm : Devm) (a : Adr) : Devm :=
  liftMachMetaPure (fun mach view => (mach, view.addAccessedAddress a)) devm

theorem addAccessedAddress_def (devm : Devm) (a : Adr) :
    addAccessedAddress devm a =
      devm.withAccessedAddresses (devm.accessedAddresses.insert a) := rfl

def Meta.addAccessedStorageKey (view : Meta) (a : Adr) (k : B256) : Meta :=
  {view with accessedStorageKeys := view.accessedStorageKeys.insert ⟨a, k⟩}

def addAccessedStorageKey (devm : Devm) (a : Adr) (k : B256) : Devm :=
  liftMachMetaPure (fun mach view => (mach, view.addAccessedStorageKey a k)) devm

theorem addAccessedStorageKey_def (devm : Devm) (a : Adr) (k : B256) :
    addAccessedStorageKey devm a k =
      devm.withAccessedStorageKeys (devm.accessedStorageKeys.insert ⟨a, k⟩) := rfl

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
  --devm.withBenv (devm.benv.setStorVal adr key val)
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

def Mem.write (μ : Mem) (n : ℕ) : B8L → Mem
  | [] => μ
  | xs@(_ :: _) =>
    if n + xs.length ≤ μ.size
    then
      if n + xs.length ≤ μ.data.size
      then
        ⟨Array.writeD μ.data n xs, μ.size⟩
      else
        let blank : Array B8 := Array.replicate (n + xs.length) 0x00
        ⟨Array.writeD (Array.copyD μ.data blank) n xs, μ.size⟩

    else
      let newSize := ceil32 (n + xs.length)
      let blank : Array B8 := Array.replicate newSize 0x00
      ⟨Array.writeD (Array.copyD μ.data blank) n xs, newSize⟩

def Mem.extend (μ : Mem) (index size : Nat) : Mem :=
  ⟨μ.data, memExtSize μ.size index size⟩

def Mem.extends (μ : Mem) (pairs : List (Nat × Nat)) : Mem :=
  ⟨μ.data, memExtsSize μ.size pairs⟩

def Mem.read (μ : Mem) (index size : ℕ) : B8L × Mem :=
  ⟨μ.data.sliceD index size 0, μ.extend index size⟩

def Dead (w : State) (a : Adr) : Prop :=
  match w[a]? with
  | none => True
  | some x => x.Empty

def Mach.memWrite (mach : Mach) (idx : Nat) (val : B8L) : Mach :=
  {mach with memory := mach.memory.write idx val}

def Devm.memWrite (devm : Devm) (idx : Nat) (val : B8L) : Devm :=
  liftMachPure (Mach.memWrite · idx val) devm

def Devm.memRead (devm : Devm) (index size : Nat) : B8L × Devm :=
  let ⟨val, mem⟩ := devm.memory.read index size
  ⟨val, devm.withMemory mem⟩

def Mach.memExtends (mach : Mach) (pairs : List (Nat × Nat)) : Mach :=
  {mach with memory := mach.memory.extends pairs}

def Devm.memExtends (devm : Devm) (pairs : List (Nat × Nat)) : Devm :=
  liftMachPure (Mach.memExtends · pairs) devm

theorem Devm.memExtends_def (devm : Devm) (pairs : List (Nat × Nat)) :
    devm.memExtends pairs = (devm.withMemory <| devm.memory.extends pairs) := rfl

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

def sstore_new_refund_counter (new_value : B256)
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
      calculate_blob_gas_price sevm.benvStat.rules.blob sevm.benvStat.excessBlobGas
    pushItem fee.toB256 gBase devm
  | .balance => liftMachMetaWorldExecution Rinst.balanceCore devm
  | .origin => pushItem sevm.tenvStat.origin.toB256 gBase devm
  | .caller => pushItem sevm.caller.toB256 gBase devm
  | .callvalue => pushItem sevm.value gBase devm
  | .calldataload => do
    let ⟨start_index, devm⟩ ← devm.pop
    let devm' ← chargeGas gVerylow devm
    let value := B8L.toB256 <| sevm.data.sliceD start_index.toNat 32 0
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
    let value := sevm.code.sliceD code_start_index size (Linst.toB8 .stop)
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
    let value := code.sliceD code_start_index size (Linst.toB8 .stop)
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
    devm.push (B8L.toB256 value)
  | .mstore => do
    let ⟨start_index, devm⟩ ← devm.popToNat
    let ⟨value, devm⟩ ← devm.pop
    let extend_memory_cost := devm.extCost [⟨start_index, 32⟩]
    let devm ← chargeGas (gVerylow + extend_memory_cost) devm
    .ok <| devm.memWrite start_index value.toB8L
  | .mstore8 => do
    let ⟨start_index, devm⟩ ← devm.popToNat
    let ⟨value, devm⟩ ← devm.pop
    let extend_memory_cost := devm.extCost [⟨start_index, 1⟩]
    let devm ← chargeGas (gVerylow + extend_memory_cost) devm
    .ok <| devm.memWrite start_index [value.2.2.toUInt8]
  | .gas => do
    let devm ← chargeGas gBase devm
    devm.push devm.gasLeft.toB256
  | .eq => applyBinary .eq_check gVerylow devm
  | .lt => applyBinary .lt_check gVerylow devm
  | .gt => applyBinary .gt_check gVerylow devm
  | .slt => applyBinary .slt_check gVerylow devm
  | .sgt => applyBinary .sgt_check gVerylow devm
  | .iszero => applyUnary (.eq_check · 0) gVerylow devm
  | .not => applyUnary (~~~ ·) gVerylow devm
  | .and => applyBinary B256.and gVerylow devm
  | .or => applyBinary B256.or gVerylow devm
  | .xor => applyBinary B256.xor gVerylow devm
  | .signextend => applyBinary B256.signext gLow devm
  | .pop => (devm.pop <&> Prod.snd) >>= chargeGas gBase
  | .byte =>
    applyBinary (λ x y => (List.getD y.toB8L x.toNat 0).toB256) gVerylow devm
  | .shl => applyBinary (fun x y => y <<< x.toNat) gVerylow devm
  | .shr => applyBinary (fun x y => y >>> x.toNat) gVerylow devm
  | .sar => applyBinary (fun x y => B256.arithShiftRight y x.toNat) gVerylow devm
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
      sstore_new_refund_counter
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
  if cd.get! k = (Jinst.toB8 .jumpdest)
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
  -- let acct := wor.get adr
  --wor.set adr {acct with bal := val}
  st.set adr <| (st.get adr).withBal val

def State.addBal (st : State) (adr : Adr) (val : B256) : State :=
  -- let acct := wor.get adr
  -- wor.set adr {acct with bal := acct.bal + val}
  st.setBal adr <| (st.bal adr + val)


def State.subBal (st : State) (adr : Adr) (val : B256) : Option State :=
  -- let acct := wor.get adr
  -- if acct.bal < val
  -- else wor.set adr {acct with bal := acct.bal - val}
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

-- def Msg.setBal (msg : Msg) (adr : Adr) (val : B256) : Msg :=
--   {msg with benv := msg.benv.setBal adr val}

def Devm.setBal (devm : Devm) (adr : Adr) (val : B256) : Devm :=
  --{devm with benv := devm.benv.setBal adr val}
  devm.withState (devm.state.setBal adr val)

-- def Msg.subBal (msg : Msg) (adr : Adr) (val : B256) : Option Msg := do
--   let benv ← msg.benv.subBal adr val
--   some {msg with benv := benv}

def Devm.subBal (devm : Devm) (adr : Adr) (val : B256) : Option Devm := do
  -- let benv ← devm.benv.subBal adr val
  -- some {devm with benv := benv}
  let state ← devm.state.subBal adr val
  some <| devm.withState state

--def Msg.addBal (msg : Msg) (adr : Adr) (val : B256) : Msg :=
--  {msg with benv := msg.benv.addBal adr val}

def Devm.addBal (devm : Devm) (adr : Adr) (val : B256) : Devm :=
  --{devm with benv := devm.benv.addBal adr val}
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

def incorporateChildOnError (parent child : Devm) (returnData : B8L) : Devm :=
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

def incorporateChildOnSuccess (parent child : Devm) (returnData : B8L) : Devm :=
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

def compute_contract_address (sender : Adr) (nonce : B64) : Adr :=
  let LA : B8L :=
    BLT.toB8L <| .list [.b8s sender.toB8L, .b8s nonce.toB8L.sig]
  (B8L.keccak LA).toAdr

def create2NewAddress
  (sender : Adr) (salt : B256) (initCode : B8L): Adr :=
  let LA : B8L :=
    (0xFF : B8) :: (sender.toB8L ++ salt.toB8L ++ initCode.keccak.toB8L)
  (B8L.keccak LA).toAdr

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

-- def Evm.setBenv (evm : Evm) (benv : Benv) : Evm :=
--   {evm with msg := {evm.msg with benv := benv}}
--
-- def Msg.setStor (msg : Msg) (adr : Adr) (stor : Stor) : Msg :=
--   {msg with benv := msg.benv.setStor adr stor}

def Msg.setCode (msg : Msg) (adr : Adr) (code : ByteArray) : Msg :=
  {msg with benv := {msg.benv with state := msg.benv.state.setCode adr code}}

def Devm.setCode (devm : Devm) (adr : Adr) (code : ByteArray) : Devm :=
  --{devm with benv := {devm.benv with state := devm.benv.state.setCode adr code}}
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

inductive PrecompResult
| error (msg : String) (cost : Nat)
| ok (cost : Nat) (output : B8L)

def PrecompResult.chargeGas (cost : Nat) (evm : Evm)
    (pr : Unit → PrecompResult) : PrecompResult :=
  if cost ≤ evm.dyna.gasLeft then pr () else .error "OutOfGasError" 0

def executeEcrecover (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  PrecompResult.chargeGas gasEcrecover evm fun () =>
    let h := B8L.toB256 <| data.sliceD 0 32 (0x00 : B8)
    let v_opt := match (B8L.toB256 <| data.sliceD 32 32 (0x00 : B8)) with
                 | 0x1B => some false
                 | 0x1C => some true
                 | _ => none
    match v_opt with
    | none => .ok gasEcrecover []
    | some v =>
      let r := B8L.toB256 <| data.sliceD 64 32 (0x00 : B8)
      let s := B8L.toB256 <| data.sliceD 96 32 (0x00 : B8)
      if r = 0 ∨ s = 0 ∨
         r ≥ secp256k1.curveOrder.toB256 ∨
         s ≥ secp256k1.curveOrder.toB256 then
        .ok gasEcrecover []
      else
        match secp256k1.recover h v r s with
        | .none => .ok gasEcrecover []
        | some adr => .ok gasEcrecover adr.toB256.toB8L

def executeSha256 (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  let cost : Nat := 60 + (12 * (ceilDiv data.length 32))
  PrecompResult.chargeGas cost evm fun () => .ok cost (B8L.sha256 data).toB8L

def executeRipemd160 (evm : Evm) : PrecompResult :=
  let data : B8L := evm.sta.data
  let cost : Nat := 600 + (120 * (ceilDiv data.length 32))
  PrecompResult.chargeGas cost evm fun () =>
    let hash : B8L := data.ripemd160
    let output : B8L := B256.toB8L <| (B8L.toB256 <| hash)
    .ok cost output

def executeId (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  let cost := 15 + (3 * (ceilDiv data.length 32))
  PrecompResult.chargeGas cost evm fun () => .ok cost data

def B8L.sliceToNat (data : B8L) (start : Nat) (length : Nat) : Nat :=
  match data.drop start with
  | [] => 0
  | tail@(_ :: _)=>
    if tail.length < length
    then
      if tail.all (· = 0)
      then 0
      else B8L.toNat <| tail.takeD length (0 : B8)
    else B8L.toNat <| tail.take length

-- def complexity
def modexpComplexity
  (m : ModexpRules) (baseLength modulusLength : Nat) : Nat :=
  let maxLength := max baseLength modulusLength
  let words := ceilDiv maxLength 8
  match m.flatComplexity with
  | some flat => if maxLength ≤ 32 then flat else m.complexityCoeff * words ^ 2
  | none => m.complexityCoeff * words ^ 2

-- def iterations
def modexpIterations (m : ModexpRules) (expLength : Nat) (expHead : Nat) : Nat :=
  let bitsPart : Nat := (Nat.log2 expHead)
  let count :=
    if expLength ≤ 32
    then
      if expHead = 0
      then 0
      else
        bitsPart
    else
      let lengthPart := m.iterationCoeff * (expLength - 32)
      lengthPart + bitsPart

  max count 1

-- def gas_cost
def modexpGascost
  (m : ModexpRules) (baseLength modulusLength expLength expHead : Nat) : Nat :=
  let mulComplexity := modexpComplexity m baseLength modulusLength
  let iterationCount := modexpIterations m expLength expHead
  let cost := (mulComplexity * iterationCount) / m.gasDivisor
  max m.minGas cost

/-- EIP-7823's bound on the three `MODEXP` length headers.

The check is part of the gas phase and precedes charging, so an oversized
header is an exceptional halt that consumes the frame's gas rather than a
priced computation. `none` reproduces the pre-Osaka behaviour of accepting any
header. -/
def modexpLengthsInBounds
    (m : ModexpRules) (baseLength expLength modulusLength : Nat) : Bool :=
  match m.maxLength with
  | none => true
  | some bound =>
    baseLength ≤ bound && expLength ≤ bound && modulusLength ≤ bound

def executeModexp (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  let m : ModexpRules := evm.sta.benvStat.rules.modexp
  let baseLength : Nat := B8L.sliceToNat data 0 32
  let expLength : Nat := B8L.sliceToNat data 32 32
  let modulusLength : Nat := B8L.sliceToNat data 64 32
  if ¬ modexpLengthsInBounds m baseLength expLength modulusLength then
    .error modexpInputLimitTag 0
  else
  let expHead : Nat := B8L.sliceToNat data (96 + baseLength) (min 32 expLength)
  let cost : Nat := modexpGascost m baseLength modulusLength expLength expHead
  PrecompResult.chargeGas cost evm fun () =>
    if baseLength = 0 ∧ modulusLength = 0 then .ok cost []
    else
      let base : Nat := B8L.sliceToNat data 96 baseLength
      let exp : Nat := B8L.sliceToNat data (96 + baseLength) expLength
      let modulus : Nat := B8L.sliceToNat data (96 + baseLength + expLength) modulusLength
      let output :=
        if modulus = 0 then List.replicate modulusLength (0x00 : B8)
        else (Nat.powMod base exp modulus).toB8L.pack modulusLength
      .ok cost output

-- MODEXP boundary guards.  The schedules themselves are checked against
-- authoritative upstream vectors (`modexp_eip2565.json` for Prague and
-- `modexp_eip7883.json` for Osaka); these pin the points where EIP-7883 and
-- EIP-7823 change behaviour, which a vector corpus can silently stop covering.

-- The multiplication complexity agrees at the 32-byte boundary and diverges
-- immediately above it, where Osaka charges the doubled quadratic term.
#guard modexpComplexity pragueModexpRules 32 32 = 16
#guard modexpComplexity osakaModexpRules 32 32 = 16
#guard modexpComplexity pragueModexpRules 33 0 = 25
#guard modexpComplexity osakaModexpRules 33 0 = 50
#guard modexpComplexity osakaModexpRules 0 32 = 16
#guard modexpComplexity osakaModexpRules 0 33 = 50
-- Below the boundary the flat term is what Osaka charges, not the quadratic
-- one Prague would have used.
#guard modexpComplexity pragueModexpRules 8 8 = 1
#guard modexpComplexity osakaModexpRules 8 8 = 16

-- The exponent-length term doubles above 32 bytes; at or below it, both forks
-- read the same `bit_length - 1` of the exponent head.
#guard modexpIterations pragueModexpRules 32 0 = 1
#guard modexpIterations osakaModexpRules 32 0 = 1
#guard modexpIterations pragueModexpRules 33 0 = 8
#guard modexpIterations osakaModexpRules 33 0 = 16
#guard modexpIterations osakaModexpRules 64 0 = 512
#guard modexpIterations pragueModexpRules 8 255 = 7
#guard modexpIterations osakaModexpRules 8 255 = 7

-- The floor rises from 200 to 500.
#guard modexpGascost pragueModexpRules 32 32 32 0 = 200
#guard modexpGascost osakaModexpRules 32 32 32 0 = 500

-- EIP-7823 bounds every header at 1024 and only from Osaka.
#guard modexpLengthsInBounds pragueModexpRules 1025 1025 1025
#guard modexpLengthsInBounds osakaModexpRules 1024 1024 1024
#guard ¬ modexpLengthsInBounds osakaModexpRules 1025 0 0
#guard ¬ modexpLengthsInBounds osakaModexpRules 0 1025 0
#guard ¬ modexpLengthsInBounds osakaModexpRules 0 0 1025

def executeEcadd (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  PrecompResult.chargeGas 150 evm fun () =>
    let x0 : Nat := B8L.toNat <| data.sliceD 0 32 (0 : B8)
    let y0 : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
    let x1 : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)
    let y1 : Nat := B8L.toNat <| data.sliceD 96 32 (0 : B8)
    if ¬ (x0 < altBn128Prime ∧ y0 < altBn128Prime ∧ x1 < altBn128Prime ∧ y1 < altBn128Prime) then
      .error "OutOfGasError" 150
    else
      match BNP.mk? x0 y0 with
      | none => .error "OutOfGasError" 150
      | some p0 =>
        match BNP.mk? x1 y1 with
        | none => .error "OutOfGasError" 150
        | some p1 => .ok 150 (BNP.toB8L (p0 + p1))

def executeEcmul (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  PrecompResult.chargeGas 6000 evm fun () =>
    let x : Nat := B8L.toNat <| data.sliceD 0 32 (0 : B8)
    let y : Nat := B8L.toNat <| data.sliceD 32 32 (0 : B8)
    let n : Nat := B8L.toNat <| data.sliceD 64 32 (0 : B8)
    if ¬ (x < altBn128Prime ∧ y < altBn128Prime) then
      .error "OutOfGasError" 6000
    else
      match BNP.mk? x y with
      | none => .error "OutOfGasError" 6000
      | some p => .ok 6000 (BNP.toB8L (p * n))

def b2R1 : B64 := 32
def b2R2 : B64 := 24
def b2R3 : B64 := 16
def b2R4 : B64 := 63
def b2MaskBits : B64 := 0xFFFFFFFFFFFFFFFF

def blake2IV : List B64 :=
  [
    0x6A09E667F3BCC908,
    0xBB67AE8584CAA73B,
    0x3C6EF372FE94F82B,
    0xA54FF53A5F1D36F1,
    0x510E527FADE682D1,
    0x9B05688C2B3E6C1F,
    0x1F83D9ABFB41BD6B,
    0x5BE0CD19137E2179
  ]

-- Reference for the word indices unrolled into `Blake2.round`: row `i` is the
-- `(a, b, c, d)` quadruple mixed by the `i`th `Blake2.g` call of a round.
def blake2MixTable : Array (Array Nat) :=
  #[
    #[0, 4, 8, 12],
    #[1, 5, 9, 13],
    #[2, 6, 10, 14],
    #[3, 7, 11, 15],
    #[0, 5, 10, 15],
    #[1, 6, 11, 12],
    #[2, 7, 8, 13],
    #[3, 4, 9, 14]
  ]

def blake2Sigma : Array (Array Nat) :=
  #[
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    #[14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    #[11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    #[7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    #[9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    #[2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    #[12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    #[13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    #[6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    #[10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0]
  ]

-- def spit_le_to_uint
def spit_le_to_B64 (data : B8L) : Nat → Nat → List B64
  | _, 0 => []
  | start, num_words + 1 =>
    let wordBytes := data.sliceD start 8 (0x00 : B8)
    let word := B8L.toB64 wordBytes.reverse
    word :: spit_le_to_B64 data (start + 8) num_words

-- def get_blake2_parameters
def getBlake2Parameters (data : B8L) :
  Nat × List B64 × List B64 × B64 × B64 × Nat :=
  let rounds := B8L.sliceToNat data 0 4
  let h := spit_le_to_B64 data 4 8
  let m := spit_le_to_B64 data 68 16
  let t := spit_le_to_B64 data 196 2
  let f := B8L.toNat <| data.drop 212
  ⟨rounds, h, m, t.getD 0 0, t.getD 1 0, f⟩

def b2wR1 : B64 := 32
def b2wR2 : B64 := 40
def b2wR3 : B64 := 48
def b2wR4 : B64 := 1

-- def G
-- The four touched words are read once, mixed entirely in local scalars, and
-- written back once: the intermediate `set!`/`get!` round trips of the
-- transcribed reference version are redundant, since every word re-read is
-- the value just computed.
def Blake2.g (v : Array B64) (a b c d : Nat) (x y : B64) : Array B64 :=
  let va : B64 := v[a]!
  let vb : B64 := v[b]!
  let vc : B64 := v[c]!
  let vd : B64 := v[d]!
  let va : B64 := va + vb + x
  let s : B64 := vd ^^^ va
  let vd : B64 := (s >>> b2R1) ^^^ (s <<< b2wR1)
  let vc : B64 := vc + vd
  let s : B64 := vb ^^^ vc
  let vb : B64 := (s >>> b2R2) ^^^ (s <<< b2wR2)
  let va : B64 := va + vb + y
  let s : B64 := vd ^^^ va
  let vd : B64 := (s >>> b2R3) ^^^ (s <<< b2wR3)
  let vc : B64 := vc + vd
  let s : B64 := vb ^^^ vc
  let vb : B64 := (s >>> b2R4) ^^^ (s <<< b2wR4)
  (((v.set! a va).set! b vb).set! c vc).set! d vd

-- One full mixing round, with `blake2MixTable` unrolled into literal word
-- indices; `m` is an `Array` so the message words are indexed rather than
-- walked as a list.
def Blake2.round (m : Array B64) (s : Array Nat) (v : Array B64) : Array B64 :=
  let v := Blake2.g v 0 4 8 12 (m[s[0]!]!) (m[s[1]!]!)
  let v := Blake2.g v 1 5 9 13 (m[s[2]!]!) (m[s[3]!]!)
  let v := Blake2.g v 2 6 10 14 (m[s[4]!]!) (m[s[5]!]!)
  let v := Blake2.g v 3 7 11 15 (m[s[6]!]!) (m[s[7]!]!)
  let v := Blake2.g v 0 5 10 15 (m[s[8]!]!) (m[s[9]!]!)
  let v := Blake2.g v 1 6 11 12 (m[s[10]!]!) (m[s[11]!]!)
  let v := Blake2.g v 2 7 8 13 (m[s[12]!]!) (m[s[13]!]!)
  Blake2.g v 3 4 9 14 (m[s[14]!]!) (m[s[15]!]!)

-- `n` counts rounds remaining out of `k`, so the round index is `k - n`.
def Blake2.rounds (m : Array B64) (k : Nat) : Nat → Array B64 → Array B64
  | 0, v => v
  | n + 1, v =>
    let r := k - (n + 1)
    Blake2.rounds m k n (Blake2.round m (blake2Sigma[r % blake2Sigma.size]!) v)

-- compress
def bCompress (numRounds : Nat)
  (h m : List B64) (t0 t1 : B64) (f : Bool) : Option B8L := do
  let v14 : B64 := blake2IV.getD 6 0
  let v : List B64 :=
    h.take 8 ++
    (blake2IV).take 4 ++ [
      .xor t0 (blake2IV.getD 4 0),
      .xor t1 (blake2IV.getD 5 0),
      if f then .xor v14 b2MaskBits else v14,
      (blake2IV.getD 7 0),
      0
    ]

  let arr := Blake2.rounds ⟨m⟩ numRounds numRounds ⟨v⟩
  let v := arr.toList
  let resultMsgWords :=
    (List.range 8).map <| fun i => h[i]! ^^^ v[i]! ^^^ v[(i + 8)]!
  List.flatten <| resultMsgWords.map (fun n => n.toB8L.reverse.takeD 8 (0x00 : B8))

-- blake2f
def executeBlake2F (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 213 then .error "InvalidParameter" 0
  else
    let ⟨rounds, h, m, t0, t1, fn⟩ := getBlake2Parameters data
    let cost := gasBlake2PerRound * rounds
    PrecompResult.chargeGas cost evm fun () =>
      match fn with
      | 0 =>
        match bCompress rounds h m t0 t1 false with
        | some output => .ok cost output
        | none => .error "bCompress failed" cost
      | 1 =>
        match bCompress rounds h m t0 t1 true with
        | some output => .ok cost output
        | none => .error "bCompress failed" cost
      | _ => .error "InvalidParameter" cost

def gasPointEval : Nat := 50000

-- def point_evaluation(evm : Evm) -> None:
def executePointEval (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 192 then .error "KZGProofError" 0
  else
    PrecompResult.chargeGas gasPointEval evm fun () =>
      let versionedHash := data.take 32
      let z := (data.drop 32).take 32
      let y := (data.drop 64).take 32
      let commitment := (data.drop 96).take 48
      let proof := (data.drop 144).take 48
      if kzgCommitmentToVersionedHash commitment ≠ versionedHash then
        .error "KZGProofError" gasPointEval
      else
        match verifyKzgProof commitment z y proof with
        | .ok true =>
          .ok gasPointEval ((4096 : Nat).toB256.toB8L ++ blsModulus.toB256.toB8L)
        | _ => .error "KZGProofError" gasPointEval

def gasBlsG1Add : Nat := 375
def gasBlsG1Mul : Nat := 12000
def gasBlsG1Map : Nat := 5500
def gasBlsG2Add : Nat := 600
def gasBlsG2Mul : Nat := 22500
def gasBlsG2Map : Nat := 23800

-- bls12_g1_add
def executeBls12G1Add (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 256 then .error "InvalidParameter" 0
  else
    PrecompResult.chargeGas gasBlsG1Add evm fun () =>
      match B8L.toExStrBLSP (data.take 128), B8L.toExStrBLSP (data.drop 128) with
      | .ok p1, .ok p2 => .ok gasBlsG1Add (BLSP.toB8L (p1 + p2))
      | _, _ => .error "OutOfGasError" gasBlsG1Add

-- bls12_g1_msm
def executeBls12G1Msm (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length = 0 ∨ data.length % g1MsmLengthPerPair ≠ 0 then
    .error s!"InvalidParameter : {data.length} is not a valid input length" 0
  else
    let k := data.length / g1MsmLengthPerPair
    let discount := List.getD g1KDiscount (k - 1) g1MaxDiscount
    let gasCost := (k * gasBlsG1Mul * discount) / 1000
    PrecompResult.chargeGas gasCost evm fun () =>
      match decodeG1MsmPairs data with
      | .ok pairs => .ok gasCost (g1MsmSum pairs).toB8L
      | .error _ => .error "OutOfGasError" gasCost

-- bls12_g2_add
def executeBls12G2Add (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 512 then .error "InvalidParameter" 0
  else
    PrecompResult.chargeGas gasBlsG2Add evm fun () =>
      match B8L.toExStrBLSP2 (data.take 256), B8L.toExStrBLSP2 (data.drop 256) with
      | .ok p1, .ok p2 => .ok gasBlsG2Add (BLSP2.toB8L (p1 + p2))
      | _, _ => .error "OutOfGasError" gasBlsG2Add

-- def bls12_g2_msm
def executeBls12G2Msm (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length = 0 ∨ data.length % g2MsmLengthPerPair ≠ 0 then
    .error s!"InvalidParameter : {data.length} is not a valid input length" 0
  else
    let k := data.length / g2MsmLengthPerPair
    let discount := List.getD g2KDiscount (k - 1) g2MaxDiscount
    let gasCost := (k * gasBlsG2Mul * discount) / 1000
    PrecompResult.chargeGas gasCost evm fun () =>
      match decodeG2MsmPairs data with
      | .ok pairs => .ok gasCost (g2MsmSum pairs).toB8L
      | .error _ => .error "OutOfGasError" gasCost

-- def bls12_map_fp_to_g1(evm : Evm) -> None :
def executeBls12MapFpToG1 (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 64 then .error "InvalidParameter" 0
  else
    PrecompResult.chargeGas gasBlsG1Map evm fun () =>
      match B8L.toExStrBLSF data with
      | .ok fp => .ok gasBlsG1Map (BLSP.toB8L (blsMapFpToG1 fp))
      | .error _ => .error "OutOfGasError" gasBlsG1Map

def catchWithOOG {ξ : Type U} (devm : Devm) (cond : String → Bool) :
  Except String ξ → Except (String × Devm) ξ
  | .ok v => .ok v
  | .error e =>
    if cond e then
      .error ⟨"OutOfGasError", devm⟩
    else
      .error ⟨e, devm⟩

-- def bytes_to_g1(data : Bytes) -> Point3D[FQ]:
def B8L.toExStrBNP (data : B8L) : Except String BNP := do
  if data.length ≠ 64 then
    .error "InvalidParameter : input should be 64 bytes long"
  let x := data.sliceToNat 0 32
  let y := data.sliceToNat 32 32
  if x >= altBn128Prime then
    .error "InvalidParameter : invalid field element"
  if y >= altBn128Prime then
    .error "InvalidParameter : invalid field element"
  (EllipticCurve.mk? (FinField.ofNat x) (FinField.ofNat y)).toExcept
    "InvalidParameter : point is not on curve"

-- def bytes_to_g2(data : Bytes) -> Point3D[FQ2]:
def B8L.toExStrBNP2 (data : B8L) : Except String BNP2 := do
  if data.length ≠ 128 then
    .error "InvalidParameter : input should be 128 bytes long"
  let x0 := data.sliceToNat 0 32
  let x1 := data.sliceToNat 32 32
  let y0 := data.sliceToNat 64 32
  let y1 := data.sliceToNat 96 32
  if (
    x0 ≥ altBn128Prime ∨
    x1 ≥ altBn128Prime ∨
    y0 ≥ altBn128Prime ∨
    y1 ≥ altBn128Prime
  ) then
    .error "InvalidParameter : invalid field element"
  (EllipticCurve.mk? (BNF2.mk x0 x1) (BNF2.mk y0 y1)).toExcept
    "InvalidParameter : point is not on curve"

def catchWithOOGPrecomp {ξ} (cost : Nat) (cond : String → Bool) :
  Except String ξ → Except (String × Nat) ξ
  | .ok v => .ok v
  | .error e => if cond e then .error ⟨"OutOfGasError", cost⟩ else .error ⟨e, cost⟩

-- def bls12_map_fp2_to_g2(evm : Evm) -> None :
def executeBls12MapFp2ToG2 (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length ≠ 128 then .error "InvalidParameter" 0
  else
    PrecompResult.chargeGas gasBlsG2Map evm fun () =>
      match B8L.toExStrBLSF2 data with
      | .ok fp2 => .ok gasBlsG2Map (BLSP2.toB8L (blsMapFp2ToG2 fp2))
      | .error _ => .error "OutOfGasError" gasBlsG2Map

def executeBls12PairingInner (data : B8L) (cost : Nat) :
    Except (String × Nat) (Nat × B8L) := do
  let mut result : BLSF12 := 1
  for i in List.range (data.length / 384) do
    let p : BLSP ←
      catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
        B8L.toExStrBLSP (data.slice! (i * 384) 128) true
    let q : BLSP2 ←
      catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
        B8L.toExStrBLSP2 (data.slice! (i * 384 + 128) 256) true
    let pairResult ← match blsPairing q p with
                     | some v => pure v
                     | none => throw ⟨"ValueError", cost⟩
    result := result * pairResult
  let output : B8L :=
    if result = 1 then (1 : Nat).toB256.toB8L else (0 : Nat).toB256.toB8L
  pure (cost, output)

-- def bls12_pairing(evm : Evm) -> None :
def executeBls12Pairing (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  if data.length = 0 ∨ data.length % 384 ≠ 0 then
    .error s!"InvalidParameter : {data.length} is not a valid input length" 0
  else
    let k := data.length / 384
    let gasCost := (32600 * k + 37700)
    PrecompResult.chargeGas gasCost evm fun () =>
      match executeBls12PairingInner data gasCost with
      | .ok ⟨cost, output⟩ => .ok cost output
      | .error ⟨msg, cost⟩ => .error msg cost

def executePairingCheckInner (data : B8L) (cost : Nat) :
    Except (String × Nat) (Nat × B8L) := do
  if data.length % 192 ≠ 0 then throw ⟨"OutOfGasError", cost⟩
  let mut result : BNF12 := 1
  for i in List.range (data.length / 192) do
    let p : BNP ←
      catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
        B8L.toExStrBNP (data.slice! (i * 192) 64)
    let q : BNP2 ←
      catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
        B8L.toExStrBNP2 (data.slice! (i * 192 + 64) 128)
    if p * altBn128CurveOrder ≠ ⟨0, 0⟩ then throw ⟨"OutOfGasError", cost⟩
    if q * altBn128CurveOrder ≠ ⟨0, 0⟩ then throw ⟨"OutOfGasError", cost⟩
    let pairResult ← match pairing q p with
                     | some v => pure v
                     | none => throw ⟨"ValueError", cost⟩
    result := result * pairResult
  let output : B8L := if result = 1 then (1 : Nat).toB256.toB8L else (0 : Nat).toB256.toB8L
  pure (cost, output)

def executePairingCheck (evm : Evm) : PrecompResult :=
  let data := evm.sta.data
  let cost := (34000 * (data.length / 192)) + 45000
  PrecompResult.chargeGas cost evm fun () =>
    -- let inner : Except (String × Nat) (Nat × B8L) := do
    --   if data.length % 192 ≠ 0 then throw ⟨"OutOfGasError", cost⟩
    --   let mut result : BNF12 := 1
    --   for i in List.range (data.length / 192) do
    --     let p : BNP ←
    --       catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
    --         B8L.toExStrBNP (data.slice! (i * 192) 64)
    --     let q : BNP2 ←
    --       catchWithOOGPrecomp cost (hasErrorType · "InvalidParameter") <|
    --         B8L.toExStrBNP2 (data.slice! (i * 192 + 64) 128)
    --     if p * altBn128CurveOrder ≠ ⟨0, 0⟩ then throw ⟨"OutOfGasError", cost⟩
    --     if q * altBn128CurveOrder ≠ ⟨0, 0⟩ then throw ⟨"OutOfGasError", cost⟩
    --     let pairResult ← match pairing q p with
    --                      | some v => pure v
    --                      | none => throw ⟨"ValueError", cost⟩
    --     result := result * pairResult
    --   let output : B8L := if result = 1 then (1 : Nat).toB256.toB8L else (0 : Nat).toB256.toB8L
    --   pure (cost, output)
    let inner := executePairingCheckInner data cost
    match inner with
    | .ok ⟨cost, output⟩ => .ok cost output
    | .error ⟨msg, cost⟩ => .error msg cost

def precompileRun (evm : Evm) : Adr → PrecompResult
  | 1 => executeEcrecover evm -- 0x1
  | 2 => executeSha256 evm -- 0x2
  | 3 => executeRipemd160 evm -- 0x3
  | 4 => executeId evm -- 0x4
  | 5 => executeModexp evm -- 0x5
  | 6 => executeEcadd evm -- 0x6
  | 7 => executeEcmul evm -- 0x7
  | 8 => executePairingCheck evm --  0x8
  | 9 => executeBlake2F evm -- 0x9
  | 10 => executePointEval evm -- 0xA
  | 11 => executeBls12G1Add evm --  0xB
  | 12 => executeBls12G1Msm evm --  0xC
  | 13 => executeBls12G2Add evm --  0xD
  | 14 => executeBls12G2Msm evm --  0xE
  | 15 => executeBls12Pairing evm -- 0xF
  | 16 => executeBls12MapFpToG1 evm -- 0x10
  | 17 => executeBls12MapFp2ToG2 evm -- 0x11
  | n => .error s!"ERROR : precompiled contract {n} does not exist" 0

def applyPrecompResult (evm : Evm) (res : PrecompResult) : Execution :=
  match res with
  | .error msg cost => .error ⟨msg, evm.dyna.withGasLeft (evm.dyna.gasLeft - cost)⟩
  | .ok cost output =>
    .ok <| (evm.dyna.withGasLeft (evm.dyna.gasLeft - cost)).withOutput output

def executePrecomp (evm : Evm) (adr : Adr) : Execution :=
  applyPrecompResult evm (precompileRun evm adr)

def Inst.toOpString : Inst → String
  | .next n => n.toOpString
  | .jump j => j.toString
  | .last l => l.toString

def Inst.toString : Inst → String
  | .next n => n.toString
  | .jump j => j.toString
  | .last l => l.toString

def State.getStor (w : State) (a : Adr) : Stor := (w.get a).stor
def State.getNonce (w : State) (a : Adr) : B64 := (w.get a).nonce
def State.getCode (w : State) (a : Adr) : ByteArray := (w.get a).code

instance : ToString Log := ⟨String.joinln ∘ Log.toStrings⟩

def List.toStringSingleQuote {ξ : Type u} [inst : ToString ξ] : List ξ → String
  | [] => "[]"
  | [x] => "['" ++ toString x ++ "']"
  | x::xs => xs.foldl (· ++ ", '" ++ toString · ++ "'") ("['" ++ toString x ++ "'") |>.push ']'

def stepString (evm : Evm) (i : Inst) : String :=
  "step(" ++
    s!"pc({evm.pc}), " ++
    s!"gas({evm.dyna.gasLeft}), " ++
    s!"op(\"{i.toOpString}\"), " ++
    s!"depth({evm.sta.depth}), " ++
    s!"{List.toStringSingleQuote <| evm.dyna.stack.map (fun x => "0x" ++ x.toHex.dropZeroes)}" ++
  ")."

def showStep (evm : Evm) (i : Inst) : Except (Evm × String) Unit :=
  if verbose ()
  then do
    .print (stepString evm i)
    .ok ()
  else .ok ()

def showLim (lim : Nat) (evm : Evm) : Except (Evm × String) Unit := do
  if lim % 100000 = 0 then
    .print s!"Recursion limit = {lim}, gas left = {evm.dyna.gasLeft}"

def isValidDelegation (code: ByteArray) : Prop :=
  code.size = eoaDelegatedCodeLength ∧
  code.sliceD 0 3 (0 : B8) = eoaDelegationMarker

instance {code} : Decidable (isValidDelegation code) := instDecidableAnd

-- get_delegated_code_address
def getDelegatedCodeAddress (code : ByteArray) : Option Adr :=
  if isValidDelegation code
  then
    let adrBytes := code.sliceD eoaDelegationMarker.length 20 (0 : B8)
    adrBytes.toAdr?
  else none

instance : Inhabited Adr := ⟨0⟩

-- access_delegation
def accessDelegation (devm : Devm) (adr : Adr) :
  Bool × Adr × ByteArray × Nat × Devm :=
  let state := devm.state
  let code := state.getCode adr
  if isValidDelegation code
  then
    let adr :=
      (code.sliceD eoaDelegationMarker.length 20 (0 : B8)).toAdr?.get!
    let accessGasCost := access_cost adr devm.accessedAddresses
    let devm := addAccessedAddress devm adr
    let code := state.getCode adr
    ⟨true, adr, code, accessGasCost, devm⟩
  else ⟨false, adr, code, 0, devm⟩

def processCreateMessage.msg (msg : Msg) : Msg :=
  let adr := msg.currentTarget
  let benv := msg.benv.setStor adr .empty
  let benv := addCreatedAccount benv adr
  let benv := benv.incrNonce adr
  msg.withBenv benv

def processCreateMessage.chargeCodeGas (rules : ForkRules) (devm : Devm) :
    Execution :=
  let contractCode := devm.output
  let contractCodeGas := contractCode.length * gasCodeDeposit
  match contractCode with
  | 0xEF :: _ => .error ⟨"InvalidContractPrefix", devm⟩
  | _ => do
    let devm ← chargeGas contractCodeGas devm
    if rules.code.maxCodeSize < contractCode.length
    then .error ⟨"OutOfGasError", devm⟩
    else .ok devm

def processCreateMessage.exceptionalHalt
    (devm : Devm) (err : String) (st : State) (tra : Tra) : Devm :=
  let devm := (devm.rollback st tra).withGasLeft 0
  devm.setMeta {devm.meta with output := [], error := .some err}

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
    }
    «meta» := {
      logs := []
      refundCounter := 0
      output := []
      accountsToDelete := .emptyWithCapacity
      returnData := []
      error := .none
      accessedAddresses := msg.accessedAddresses
      accessedStorageKeys := msg.accessedStorageKeys
      createdAccounts := msg.benv.createdAccounts
    }
    world := {
      state := msg.benv.state
      transientStorage := msg.tenv.transientStorage
    }
  }

def initEvm (msg : Msg) : Evm :=
  {
    pc := 0
    sta := initSevm msg
    dyna := initDevm msg
  }

def Msg.benvAfterTransfer (msg : Msg) :
    Except (String × State × AdrSet × Tra) Benv :=
  if msg.shouldTransferValue then do
    let benv ←
      (msg.benv.subBal msg.caller msg.value).toExcept
        ⟨"AssertionError", msg.benv.state, msg.benv.createdAccounts, msg.tenv.transientStorage⟩
    .ok <| benv.addBal msg.currentTarget msg.value
  else
    .ok msg.benv

def executeCode.handleError :
    Execution → Except (String × State × AdrSet × Tra) Devm
  | .ok evm => .ok evm
  | .error ⟨err, evm⟩ =>
    if isExceptionalHalt err
    then
      let evm := evm.withGasLeft 0
      .ok (evm.setMeta {evm.meta with output := [], error := some err})
    else
      if err = "Revert"
      then .ok (evm.withError (some "Revert"))
      else .error ⟨err, evm.state, evm.createdAccounts, evm.transientStorage⟩

def Execution.withPc (pc : Nat) (exn : Execution) :
     Except (String × Devm) (Nat × Devm) := do
  let devm ← exn
  .ok ⟨pc, devm⟩

def Ninst.size : Ninst → Nat
  | reg _ => 1
  | exec _ => 1
  | push xs _ => xs.length + 1

-- the message passed to the sub-call performed by a call-type instruction.
-- factored out as a named definition to prevent context blowup in proofs.
def callMsg
    (sevm: Sevm)
    (evm1: Devm)
    (gas: Nat)
    (value: B256)
    (caller: Adr)
    (target: Adr)
    (codeAddress: Adr)
    (shouldTransferValue: Bool)
    (isStaticcall: Bool)
    (calldata: B8L)
    (code : ByteArray)
    (disablePrecompiles: Bool) : Msg :=
  {
    benv := {state := evm1.state, createdAccounts := evm1.createdAccounts, stat := sevm.benvStat}
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
  }

mutual

  /-
  BLANC MIGRATION NOTE:
  The eight mutually recursive definitions below used to encode recursion-fuel
  exhaustion as the semantic error string `"RecursionLimit"`.  They now return
  `Fueled`: `none` means fuel exhaustion, while `some (.ok ...)` and
  `some (.error ...)` are exactly the previous completed semantic results.

  Consequently, downstream correspondence proofs should replace
  `Except.Lim`/`Except.Fit` and `≠ "RecursionLimit"` plumbing with the outer
  `Option` shape.  In particular, a completed run is witnessed by an equation
  of the form `exec evm lim = some ex`.  `Fueled.mapResult` below preserves
  exhaustion while applying the pre-existing semantic error-state adapters.
  -/

  def executeCode (msg : Msg) :
    Nat → Fueled (String × State × AdrSet × Tra) Devm
    | 0 => Fueled.exhausted
    | lim + 1 => do
      let evm : Evm := initEvm msg
      match msg.codeAddress with
      | .none =>
        Fueled.mapResult executeCode.handleError <| exec evm lim
      | .some adr =>
        if !msg.disablePrecompiles && msg.benv.stat.rules.isPrecomp adr then
          Fueled.ofExcept <| executeCode.handleError <| executePrecomp evm adr
        else
          Fueled.mapResult executeCode.handleError <| exec evm lim
  termination_by lim => lim

  def processMessage (msg : Msg) :
    Nat → Fueled (String × State × AdrSet × Tra) Devm
    | 0 => Fueled.exhausted
    | lim + 1 => do
      /- In the original reference python implementation, there is a test here that
         checks the msg.depth value, and fails with a "stack depth limit error" if
         it is larger than 1024. However, due to the way processMessage is defined
         and used, there is no way msg.depth ever has a value larger than 1024, and
         the error reporting is a dead code path that never will never get used, so
         it is omitted here.  -/
      let benv ← msg.benvAfterTransfer
      let evm ← executeCode (msg.withBenv benv) lim
      if evm.error.isSome then
        Fueled.ok <| evm.rollback msg.benv.state msg.tenv.transientStorage
      else
        Fueled.ok evm
  termination_by lim => lim

  def processCreateMessage (msg : Msg) :
    Nat → Fueled (String × State × AdrSet × Tra) Devm
    | 0 => Fueled.exhausted
    | lim + 1 => do
      let evm ← processMessage (processCreateMessage.msg msg) lim
      if evm.error.isNone then
        match processCreateMessage.chargeCodeGas msg.benv.stat.rules evm with
        | .ok evm => Fueled.ok <| evm.setCode msg.currentTarget ⟨⟨evm.output⟩⟩
        | .error ⟨err, evm⟩ =>
          if isExceptionalHalt err
          then
            Fueled.ok <|
              processCreateMessage.exceptionalHalt evm err
                msg.benv.state
                msg.tenv.transientStorage
          else
            Fueled.error ⟨err, evm.state, evm.createdAccounts, evm.transientStorage⟩
      else
        Fueled.ok <| evm.rollback msg.benv.state msg.tenv.transientStorage
  termination_by lim => lim

  def genericCreate
    (sevm : Sevm)
    (devm : Devm)
    (endowment : B256)
    (newAddress : Adr)
    (memoryIndex : Nat)
    (memorySize : Nat) : Nat → Fueled (String × Devm) Devm
    | 0 => Fueled.exhausted
    | lim + 1 => do
      let calldata ← Fueled.ok <| devm.memory.data.sliceD memoryIndex memorySize 0
      Fueled.assert
        (memorySize ≤ sevm.benvStat.rules.code.maxInitCodeSize)
        ⟨"OutOfGasError", devm⟩
      let createMsgGas ← Fueled.ok <| except64th devm.gasLeft
      let devm ← Fueled.ok <| devm.withGasLeft (devm.gasLeft - createMsgGas)
      assertDynamic sevm devm
      let devm ← Fueled.ok <| devm.withReturnData []
      let sender ← Fueled.ok <| devm.state.get sevm.currentTarget
      if ( sender.bal < endowment ∨
           sender.nonce = B64.max ∨
           sevm.depth = 0 ) then
        return (← (devm.withGasLeft (devm.gasLeft + createMsgGas)).push 0)
      let devm ← Fueled.ok <| devm.incrNonce sevm.currentTarget
      let devm ← Fueled.ok <| addAccessedAddress devm newAddress
      if
        ( let target := devm.state.get newAddress
          target.nonce ≠ (0 : B64) ∨
          target.code.size ≠ 0 ∨
          target.stor.size ≠ 0 ) then
        return (← devm.push 0)
      let childMsg : Msg ← Fueled.ok <| {
        benv := Benv.mk devm.state devm.createdAccounts sevm.benvStat
        tenv := {transientStorage := devm.transientStorage, stat := sevm.tenvStat}
        caller := sevm.currentTarget
        target := .none
        gas := createMsgGas
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
      }
      let child ← Fueled.mapResult (liftToExecution devm) <|
        processCreateMessage childMsg lim
      if child.error.isSome then
        (incorporateChildOnError devm child child.output).push 0
      else
        (incorporateChildOnSuccess devm child []).push newAddress.toB256
  termination_by lim => lim

  def genericCall
    (sevm: Sevm)
    (devm: Devm)
    (gas: Nat)
    (value: B256)
    (caller: Adr)
    (target: Adr)
    (codeAddress: Adr)
    (shouldTransferValue: Bool)
    (isStaticcall: Bool)
    (input_index:  Nat)
    (input_size:   Nat)
    (output_index: Nat)
    (output_size:  Nat)
    (code : ByteArray)
    (disablePrecompiles: Bool) : Nat → Fueled (String × Devm) Devm
    | 0 => Fueled.exhausted
    | lim + 1 => do
      let evm1 ← Fueled.ok (devm.withReturnData [])
      if (sevm.depth = 0) then
        return (← (evm1.withGasLeft (evm1.gasLeft + gas)).push 0)
      let calldata ← Fueled.ok <| evm1.memory.data.sliceD input_index input_size 0
      let (childMsg : Msg) ← Fueled.ok <|
        callMsg sevm evm1 gas value caller target codeAddress
          shouldTransferValue isStaticcall calldata code disablePrecompiles
      let child ← Fueled.mapResult (liftToExecution evm1) <|
        processMessage childMsg lim
      let actualOutput := child.output.take output_size
      if child.error.isSome then
        let evm2 ← (incorporateChildOnError evm1 child child.output).push 0
        Fueled.ok <| evm2.memWrite output_index actualOutput
      else
        let evm2 ← (incorporateChildOnSuccess evm1 child child.output).push 1
        Fueled.ok <| evm2.memWrite output_index actualOutput
  termination_by lim => lim

  def Xinst.run (sevm : Sevm) (devm : Devm) :
      Xinst → Nat → Fueled (String × Devm) Devm
    |  _, 0 => Fueled.exhausted
    | .create, lim + 1 => do
      let ⟨endowment, devm⟩ ← devm.pop
      let ⟨memoryIndex, devm⟩ ← devm.popToNat
      let ⟨memorySize, devm⟩ ← devm.popToNat
      let extendCost ← Fueled.ok <| devm.extCost [⟨memoryIndex, memorySize⟩]
      let initCodeCost ← Fueled.ok <| gasInitCodeWordCost * (ceilDiv memorySize 32)
      let devm ← chargeGas (gasCreate + extendCost + initCodeCost) devm
      let devm ← Fueled.ok <| devm.memExtends [⟨memoryIndex, memorySize⟩]
      let newAddress ← Fueled.ok <|
        compute_contract_address
          sevm.currentTarget
          (devm.state.get sevm.currentTarget).nonce
      genericCreate
        sevm
        devm
        endowment
        newAddress
        memoryIndex
        memorySize
        lim
    | .create2, lim + 1 => do
      let ⟨endowment, devm⟩ ← devm.pop
      let ⟨memoryIndex, devm⟩ ← devm.popToNat
      let ⟨memorySize, devm⟩ ← devm.popToNat
      let ⟨salt, devm⟩ ← devm.pop
      let extendCost ← Fueled.ok <| devm.extCost [⟨memoryIndex, memorySize⟩]
      let initCodeHashCost ← Fueled.ok <|
        gasKeccak256Word * ceilDiv memorySize 32
      let initCodeCost ← Fueled.ok <|
        gasInitCodeWordCost * (ceilDiv memorySize 32)
      let devm ←
        chargeGas
          (gasCreate + initCodeHashCost + extendCost + initCodeCost)
          devm
      let devm ← Fueled.ok <| devm.memExtends [⟨memoryIndex, memorySize⟩]
      let newAddress ← Fueled.ok <|
        create2NewAddress
          sevm.currentTarget
          salt
          (devm.memory.data.sliceD memoryIndex memorySize 0)
      genericCreate
        sevm
        devm
        endowment
        newAddress
        memoryIndex
        memorySize
        lim
    | .call, lim + 1 => do
      let ⟨gas, devm⟩ ← devm.pop
      let ⟨callee, devm⟩ ← devm.popToAdr
      let ⟨value, devm⟩ ← devm.pop
      let ⟨inputIndex, devm⟩ ← devm.popToNat
      let ⟨inputSize, devm⟩ ← devm.popToNat
      let ⟨outputIndex, devm⟩ ← devm.popToNat
      let ⟨outputSize, devm⟩ ← devm.popToNat
      let extendCost ← Fueled.ok <|
        devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let preAccessCost ← Fueled.ok <| access_cost callee devm.accessedAddresses
      let devm ← Fueled.ok <| addAccessedAddress devm callee
      let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm⟩ ← Fueled.ok <|
        accessDelegation devm callee
      let accessCost ← Fueled.ok <| preAccessCost + delegatedAccessGasCost
      let createCost ← Fueled.ok <|
        if (¬ (devm.getAcct callee).Empty) ∨ value = 0
        then 0
        else gNewAccount
      let transferCost ← Fueled.ok <| if value = 0 then 0 else gasCallValue
      let ⟨msgCallCost, msgCallStipend⟩ ← Fueled.ok <|
        calculateMsgCallGas
          value.toNat
          gas.toNat
          devm.gasLeft
          extendCost
          (accessCost + createCost + transferCost)
      let devm ← chargeGas (msgCallCost + extendCost) devm
      Fueled.assert (!sevm.isStatic ∨ value = 0) ⟨"WriteInStaticContext", devm⟩
      let devm ← Fueled.ok <|
        devm.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let senderBal ← Fueled.ok <| (devm.getAcct sevm.currentTarget).bal
      if senderBal < value then
        let devm ← devm.push 0
        Fueled.ok ((devm.withReturnData []).withGasLeft (devm.gasLeft + msgCallStipend))
      else
        genericCall
          sevm
          devm
          msgCallStipend
          value
          sevm.currentTarget
          callee
          callee
          true
          false
          inputIndex
          inputSize
          outputIndex
          outputSize
          code
          disablePrecompiles
          lim
    | .callcode, lim + 1 => do
      let ⟨gas, devm⟩ ← devm.pop
      let ⟨codeAddress, devm⟩ ← devm.popToAdr
      let ⟨value, devm⟩ ← devm.pop
      let ⟨inputIndex, devm⟩ ← devm.popToNat
      let ⟨inputSize, devm⟩ ← devm.popToNat
      let ⟨outputIndex, devm⟩ ← devm.popToNat
      let ⟨outputSize, devm⟩ ← devm.popToNat
      let extendCost ← Fueled.ok <|
        devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let preAccessCost ← Fueled.ok <| access_cost codeAddress devm.accessedAddresses
      let devm ← Fueled.ok <| addAccessedAddress devm codeAddress
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ ← Fueled.ok <|
        accessDelegation devm codeAddress
      let accessCost ← Fueled.ok <| preAccessCost + delegatedAccessGasCost
      let transferCost ← Fueled.ok <| if value = 0 then 0 else gasCallValue
      let ⟨msgCallCost, msgCallStipend⟩ ← Fueled.ok <|
        calculateMsgCallGas
          value.toNat
          gas.toNat
          devm.gasLeft
          extendCost
          (accessCost + transferCost)
      let devm ← chargeGas (msgCallCost + extendCost) devm
      let devm ← Fueled.ok <|
        devm.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let senderBal ← Fueled.ok (devm.getAcct sevm.currentTarget).bal
      if senderBal < value
      then
        let devm ← devm.push 0
        Fueled.ok <|
          (devm.withGasLeft (devm.gasLeft + msgCallStipend)).withReturnData []
      else
        genericCall
          sevm
          devm
          msgCallStipend
          value
          sevm.currentTarget
          sevm.currentTarget
          newCodeAddress
          true
          false
          inputIndex
          inputSize
          outputIndex
          outputSize
          code
          disablePrecompiles
          lim
    | .delcall, lim + 1 => do
      let ⟨gas, devm⟩ ← devm.pop
      let ⟨codeAddress, devm⟩ ← devm.popToAdr
      let ⟨inputIndex, devm⟩ ← devm.popToNat
      let ⟨inputSize, devm⟩ ← devm.popToNat
      let ⟨outputIndex, devm⟩ ← devm.popToNat
      let ⟨outputSize, devm⟩ ← devm.popToNat
      let extendCost ← Fueled.ok <|
        devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let preAccessCost ← Fueled.ok <| access_cost codeAddress devm.accessedAddresses
      let devm ← Fueled.ok <| addAccessedAddress devm codeAddress
      let ⟨disablePrecompiles, newCodeAddress, code, delegatedAccessGasCost, devm⟩ ← Fueled.ok <|
        accessDelegation devm codeAddress
      let accessCost ← Fueled.ok <| preAccessCost + delegatedAccessGasCost
      let ⟨msgCallCost, msgCallStipend⟩ ← Fueled.ok <|
        calculateMsgCallGas
          0
          gas.toNat
          devm.gasLeft
          extendCost
          accessCost
      let devm ← chargeGas (msgCallCost + extendCost) devm
      let devm ← Fueled.ok <|
        devm.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      genericCall
        sevm
        devm
        msgCallStipend
        sevm.value
        sevm.caller
        sevm.currentTarget
        newCodeAddress
        false
        false
        inputIndex
        inputSize
        outputIndex
        outputSize
        code
        disablePrecompiles
        lim
    | .statcall, lim + 1 => do
      let ⟨gas, devm⟩ ← devm.pop
      let ⟨target, devm⟩ ← devm.popToAdr
      let ⟨inputIndex, devm⟩ ← devm.popToNat
      let ⟨inputSize, devm⟩ ← devm.popToNat
      let ⟨outputIndex, devm⟩ ← devm.popToNat
      let ⟨outputSize, devm⟩ ← devm.popToNat
      let extendCost ← Fueled.ok <|
        devm.extCost [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      let preAccessCost ← Fueled.ok <| access_cost target devm.accessedAddresses
      let devm ← Fueled.ok <| addAccessedAddress devm target
      let ⟨disablePrecompiles, _, code, delegatedAccessGasCost, devm⟩ ←
        Fueled.ok <| accessDelegation devm target
      let accessCost ← Fueled.ok <| preAccessCost + delegatedAccessGasCost
      let ⟨msgCallCost, msgCallStipend⟩ ← Fueled.ok <|
        calculateMsgCallGas
          0
          gas.toNat
          devm.gasLeft
          extendCost
          accessCost
      let devm ← chargeGas (msgCallCost + extendCost) devm
      let devm ← Fueled.ok <|
        devm.memExtends
          [⟨inputIndex, inputSize⟩, ⟨outputIndex, outputSize⟩]
      genericCall
        sevm
        devm
        msgCallStipend
        0
        sevm.currentTarget
        target
        target
        true
        true
        inputIndex
        inputSize
        outputIndex
        outputSize
        code
        disablePrecompiles
        lim
  termination_by _ lim => lim

  def Ninst.run (evm : Evm) :
      -- Completed results retain the old `Execution` payload under `some`.
      Ninst → Nat → Fueled (String × Devm) Devm
    | .push xs _, _ => do
      let evm' ← chargeGas (if xs = [] then gBase else gVerylow) evm.dyna
      -- (evm'.push xs.toB256).withPc (evm.pc + xs.length + 1)
      evm'.push xs.toB256 --).withPc (evm.pc + xs.length + 1)
    | .reg r, _ =>
      --(r.run evm).withPc (evm.pc + 1)
      Fueled.ofExcept <| r.run evm
    | .exec _, 0 => Fueled.exhausted
    | .exec x, lim + 1 =>
      -- (Xinst.run evm.sta evm.dyna x lim).withPc (evm.pc + 1)
      Xinst.run evm.sta evm.dyna x lim
  termination_by _ lim => lim

  def exec : Evm → Nat → Fueled (String × Devm) Devm
    | _, 0 => Fueled.exhausted
    | evm, lim + 1 => do
      -- let mut evm := evm
      -- showLim lim evm
      let i ← Fueled.ofExcept <|
        (evm.getInst).toExcept ⟨"InvalidOpcode", evm.dyna⟩
      -- showStep evm i
      match i with
      | .next n =>
        let devm ← n.run evm lim
        exec ⟨evm.pc + n.size, evm.sta, devm⟩ lim
      | .jump j =>
        let ⟨pc, devm⟩ ← j.run evm
        exec ⟨pc, evm.sta, devm⟩ lim
      | .last l => Fueled.ofExcept <| l.run evm.sta evm.dyna
  termination_by _ lim => lim

end

instance {w a} : Decidable (Dead w a) := by
  simp [Dead]
  cases w[a]?
  · simp; apply instDecidableTrue
  · simp [Acct.Empty]; apply instDecidableAnd

def State.code (w : State) (a : Adr) : ByteArray :=
  match w[a]? with
  | none => ByteArray.mk #[]
  | some x => x.code

def KeySet.toStrings (ks : KeySet) : List String :=
  let f : (Adr × B256) → List String :=
    fun | ⟨a, x⟩ => [s!"{a.toHex} : {x.toHex}"]
  fork "KeySet" <| ks.toList.map f

instance : ToString KeySet := ⟨λ ks => String.joinln <| ks.toStrings⟩

def correctBlobHashVersion (h : B256) : Prop :=
  h.toB8L[0]! = 0x01

instance : DecidablePred correctBlobHashVersion := by
  intro h; simp [correctBlobHashVersion]; infer_instance

def Log.toBLT (l : Log) : BLT :=
  .list [
    .b8s l.address.toB8L,
    .list (l.topics.map B256.toBLT),
    .b8s l.data
  ]

def List.putIndex {ξ : Type u} (xs : List ξ) : List (Nat × ξ) :=
  let rec aux : Nat → List ξ → List (Nat × ξ)
    | _, [] => []
    | k, x :: xs => (k, x) :: aux (k + 1) xs
  aux 0 xs

inductive ExpectedWorldState : Type
  | wor : State → ExpectedWorldState
  | root : B256 → ExpectedWorldState

structure Test where
  (name : String)
  (info : Lean.Json)
  (blocks : Lean.Json)
  (gbh : Lean.Json)
  (grlp : Lean.Json)
  (lbh : Lean.Json)
  (network : Lean.Json)
  (pre : Lean.Json)
  (post : ExpectedWorldState)
  (sealEngine : Lean.Json)

def Test.toStrings (t : Test) : List String :=
  fork "test" [
    [s!"test name : {t.name}"],
    fork "info" [t.info.toStrings],
    fork "blocks" [t.blocks.toStrings],
    fork "genesisBlockHeader" [t.gbh.toStrings],
    fork "genesisRLP" [t.grlp.toStrings],
    fork "lastblockhash" [t.lbh.toStrings],
    fork "network" [t.network.toStrings],
    fork "pre" [t.pre.toStrings],
    --[s!"postRoot {t.postRoot.toHex}"],
    fork "sealEngine" [t.sealEngine.toStrings]
  ]

instance : ToString Test := ⟨String.joinln ∘ Test.toStrings⟩

def B8L.toByteArray (xs : B8L) : ByteArray := .mk <| .mk xs

instance : ToString State := ⟨String.joinln ∘ State.toStrings⟩
instance : ToString BLT := ⟨String.joinln ∘ BLT.toStrings⟩

def toKeyVal' (pr : B8L × B8L) : B8L × B8L :=
  let ad := pr.fst
  let ac := pr.snd
  ⟨B8L.toB4s ad, ac⟩

def receiptRoot (w : List (B8L × B8L)) : B256 :=
  let keyVals : List (B8L × B8L) := (List.map toKeyVal' w)
  let finalNTB : NTB := Std.TreeMap.ofList keyVals _
  trie finalNTB

def addIndexToBloom (hash : B8L) (index : Nat) (bloom : B8L) : B8L :=
  let bitToSet : B16 :=
    (B8s.toB16 (hash.getD index 0) (hash.getD (index + 1) 0)) &&& (0x07FF : B16)
  let bitIndex : B16 := 0x07FF - bitToSet
  let byteIndex : Nat := (bitIndex / 8).toNat
  let bitValue : B8 := 0x01 <<< (0x07 - (bitIndex.lows &&& 0x07))
  let origValue : B8 := bloom.getD byteIndex 0
  bloom.set byteIndex (origValue ||| bitValue)

def addEntryToBloom (bloom : B8L) (entry : B8L) : B8L :=
  let hash := (B8L.keccak entry).toB8L
  addIndexToBloom hash 4 <|
  addIndexToBloom hash 2 <|
  addIndexToBloom hash 0 bloom

def addLogToBloom (bloom : B8L) (log : Log) : B8L :=
  let bloom' := addEntryToBloom bloom log.address.toB8L
  List.foldl addEntryToBloom bloom' (log.topics.map B256.toB8L)

def logsBloom (l : List Log) : B8L :=
  List.foldl addLogToBloom (List.replicate 256 0x00) l

def Withdrawal.toStrings (wd : Withdrawal) : List String :=
  fork "withdrawal" [
    [s!"global index : 0x{wd.globalIndex.toHex}"],
    [s!"validator index : 0x{wd.validatorIndex.toHex}"],
    [s!"recipient : 0x{wd.recipient.toHex}"],
    [s!"amount : 0x{wd.amount.toHex}"]
  ]

instance : ToString Withdrawal := ⟨String.joinln ∘ Withdrawal.toStrings⟩

def BLT.toExStrHeader : BLT → Except String Header
  | .list (
      .b8s parentHash ::
      .b8s ommersHash ::
      .b8s coinbase ::
      .b8s stateRoot ::
      .b8s txsRoot ::
      .b8s receiptRoot ::
      .b8s bloom ::
      .b8s difficulty ::
      .b8s number ::
      .b8s gasLimit ::
      .b8s gasUsed ::
      .b8s timestamp ::
      .b8s extraData ::
      .b8s prevRandao ::
      .b8s nonce ::
      .b8s baseFeePerGas ::
      .b8s withdrawalsRoot ::
      .b8s blobGasUsed ::
      .b8s excessBlobGas ::
      .b8s parentBeaconBlockRoot ::
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
      let coinbase ← coinbase.toRlpAdr "header coinbase"
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
      let nonce ← nonce.toRlpFixedB64 "header nonce"
      let baseFeePerGas ← baseFeePerGas.toRlpNat "header baseFeePerGas" 32
      let withdrawalsRoot ← withdrawalsRoot.toRlpHash "header withdrawalsRoot"
      let blobGasUsed := (← blobGasUsed.toRlpB64 "header blobGasUsed").toNat
      let excessBlobGas := (← excessBlobGas.toRlpB64 "header excessBlobGas").toNat
      let previousBeaconBlockRoot ←
        parentBeaconBlockRoot.toRlpHash "header parentBeaconBlockRoot"
      -- The requests hash is optional in shape, but exactly 32 bytes when
      -- present: an absent field and a malformed one are different failures.
      let requestsHash : Option B256 ←
        match tail with
        | [] => .ok none
        | [.b8s requestsHash] =>
          (requestsHash.toRlpHash "header requestsHash").map some
        | _ =>
          .error <| rlpStructureError "header"
            s!"expected 20 or 21 fields, but found {20 + tail.length}"
      .ok {
        parentHash := parentHash
        ommersHash := ommersHash
        coinbase := coinbase
        stateRoot := stateRoot
        txsRoot := txsRoot
        receiptRoot := receiptRoot
        bloom := bloom
        difficulty := difficulty
        number := number
        gasLimit := gasLimit
        gasUsed := gasUsed
        timestamp := timestamp
        extraData := extraData
        prevRandao := prevRandao
        nonce := nonce
        baseFeePerGas := baseFeePerGas
        withdrawalsRoot := withdrawalsRoot
        blobGasUsed := blobGasUsed
        excessBlobGas := excessBlobGas
        parentBeaconBlockRoot := previousBeaconBlockRoot
        requestsHash := requestsHash
      }
  | _ =>
    .error <| rlpStructureError "header"
      "expected a list of 20 or 21 byte-string fields"

def Block.toStrings (block : Block) : List String :=
  let aux : B8L ⊕ Tx → List String
    | .inl xs => fork "Encoded Tx" [String.chunks 80 xs.toHex]
    | .inr tx => tx.toStrings
  fork "BLOCK" [
    Header.toStrings block.header,
    fork "TXS" <| block.txs.map aux,
    fork "OMMERS" <| block.ommers.map Header.toStrings,
    fork "WDS" <| block.wds.map Withdrawal.toStrings
  ]

instance : ToString Block := ⟨String.joinln ∘ Block.toStrings⟩

/-- The child's excess blob gas. The set point is read from the *child's* blob
schedule, which is what makes a BPO transition take effect on the first block
of the new schedule rather than one block late. -/
def calculateExcessBlobGas (blob : BlobSchedule) (parentHeader : Header) : Nat :=
  let parentBlobGas : Nat :=
    parentHeader.excessBlobGas + parentHeader.blobGasUsed
  parentBlobGas - blob.target

/-- The absolute upper bound on a block gas limit. A gas limit is a 63-bit
quantity: `2 ^ 63` and above is out of range no matter what the parent's limit
was, which is why the fixtures name it separately from a limit that merely
moved too far from its parent. -/
def gasLimitMaximum : Nat := 2 ^ 63

/-- Check a block's gas limit against the absolute bound and against its
parent, reporting *which* rule failed.

The absolute bound is tested first, and that order is the point: a limit just
above `2 ^ 63` can still sit inside the parent-relative window (it does exactly
that when the parent's limit is `2 ^ 63 - 1`), so testing the window first would
report the adjustment rule for a block whose real defect is an out-of-range gas
limit -- the right verdict for the wrong reason. -/
def checkGasLimit (gasLimit parentGasLimit : Nat) : Except String Unit := do
  if gasLimit ≥ gasLimitMaximum then
    .error
      s!"{gasLimitTooBigTag} : gas limit = {gasLimit} ≥ \
         absolute maximum = {gasLimitMaximum}"
  let maxAdjustmentDelta := parentGasLimit / gasLimitAdjustmentFactor
  if gasLimit ≥ parentGasLimit + maxAdjustmentDelta then
    .error
      s!"{gasLimitAdjustmentTag} : gas limit = {gasLimit} ≥ parent gas limit \
         = {parentGasLimit} + max adjustment delta = {maxAdjustmentDelta}"
  if gasLimit ≤ parentGasLimit - maxAdjustmentDelta then
    .error
      s!"{gasLimitAdjustmentTag} : gas limit = {gasLimit} ≤ parent gas limit \
         = {parentGasLimit} - max adjustment delta = {maxAdjustmentDelta}"
  if gasLimit < gasLimitMinimum then
    .error
      s!"{gasLimitAdjustmentTag} : gas limit = {gasLimit} < \
         minimum = {gasLimitMinimum}"

--------------- GAS-LIMIT BOUNDARY CHECKS ----------------

-- The absolute bound, at its exact boundary. These are the real numbers from
-- `bcInvalidHeaderTest/GasLimitHigherThan2p63m1.json`, whose genesis gas limit
-- is `2 ^ 63 - 1` and whose block claims `2 ^ 63`. Note the parent-relative
-- window *accepts* that block -- one step up from a parent of `2 ^ 63 - 1` is
-- well within a delta of `(2 ^ 63 - 1) / 1024` -- so the absolute bound is the
-- only rule that rejects it, and it must be the one that reports.
#guard hasTag gasLimitTooBigTag (checkGasLimit (2 ^ 63) (2 ^ 63 - 1))
#guard ¬ hasTag gasLimitAdjustmentTag (checkGasLimit (2 ^ 63) (2 ^ 63 - 1))
-- One below the bound, same parent: accepted. This is the maximum gas limit any
-- valid block in the corpus carries, so the bound may not be one lower.
#guard (checkGasLimit (2 ^ 63 - 1) (2 ^ 63 - 1)).toOption.isSome
-- Far above the bound, where the window would also reject: still too big.
#guard hasTag gasLimitTooBigTag (checkGasLimit (2 ^ 64) 3141592)

-- The parent-relative window and the minimum, each at its boundary, all
-- reporting the adjustment rule rather than the absolute one.
#guard (checkGasLimit 3141592 3141592).toOption.isSome              -- unchanged
#guard hasTag gasLimitAdjustmentTag (checkGasLimit (3141592 + 3067) 3141592)
#guard (checkGasLimit (3141592 + 3066) 3141592).toOption.isSome     -- just inside
#guard hasTag gasLimitAdjustmentTag (checkGasLimit (3141592 - 3067) 3141592)
#guard (checkGasLimit (3141592 - 3066) 3141592).toOption.isSome     -- just inside
#guard hasTag gasLimitAdjustmentTag (checkGasLimit 4999 5000)       -- below minimum
#guard (checkGasLimit gasLimitMinimum 5000).toOption.isSome

def calculateBaseFeePerGas
  (blockGasLimit parentGasLimit parentGasUsed parentBaseFeePerGas : Nat) :
  Except String Nat := do
  let parentGasTarget := parentGasLimit / elasticityMultiplier
  checkGasLimit blockGasLimit parentGasLimit
  if parentGasUsed = parentGasTarget
  then .ok parentBaseFeePerGas
  else
    if parentGasUsed > parentGasTarget
    then
      let gasUsedDelta := parentGasUsed - parentGasTarget
      let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
      let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
      let baseFeePerGasDelta :=
        max (targetFeeGasDelta / baseFeeMaxChangeDenominator) 1
      .ok <| parentBaseFeePerGas + baseFeePerGasDelta
    else
      let gasUsedDelta := parentGasTarget - parentGasUsed
      let parentFeeGasDelta := parentBaseFeePerGas * gasUsedDelta
      let targetFeeGasDelta := parentFeeGasDelta / parentGasTarget
      let baseFeePerGasDelta :=
        targetFeeGasDelta / baseFeeMaxChangeDenominator
      .ok <| parentBaseFeePerGas - baseFeePerGasDelta

def validateHeader (rules : ForkRules) (chain : BlockChain) (header : Header) :
  Except String Unit := do
  let parent ← chain.blocks.getLast?.toExcept "No parent block found"
  let blockParentHash := (Header.toBLT parent.header).toB8L.keccak
  -- Parentage is settled first. Every check below reads the parent's header, so
  -- a block naming a parent this chain does not end with is not a block with a
  -- bad timestamp or a bad base fee -- it is a block that cannot be placed at
  -- all, and reporting any later rule for it would name the wrong defect. The
  -- all-zero hash is called out separately because it names no block at all,
  -- rather than naming some block this chain has not got.
  if header.parentHash ≠ blockParentHash then do
    if header.parentHash = 0 then
      .error
        s!"{unknownParentZeroTag} : parent hash is the all-zero hash, \
           which names no block"
    .error
      s!"{unknownParentTag} : parent hash = {header.parentHash} names no known \
         block; this chain ends at {blockParentHash}"
  let expectedBaseFeePerGas ←
    calculateBaseFeePerGas
      header.gasLimit
      parent.header.gasLimit
      parent.header.gasUsed
      parent.header.baseFeePerGas
  if header.excessBlobGas ≠ calculateExcessBlobGas rules.blob parent.header then do
    .error
      s!"{excessBlobGasTag} : excess blob gas = {header.excessBlobGas} ≠ \
         expected = {calculateExcessBlobGas rules.blob parent.header}"
  if header.gasUsed > header.gasLimit then do
    .error
      s!"{gasUsedOverflowTag} : gas used = {header.gasUsed} > \
         gas limit = {header.gasLimit}"
  if expectedBaseFeePerGas ≠ header.baseFeePerGas then do
    .error
      s!"{baseFeePerGasTag} : base fee per gas = {header.baseFeePerGas} ≠ \
         expected = {expectedBaseFeePerGas}"
  if header.timestamp ≤ parent.header.timestamp then do
    .error
      s!"{timestampOlderThanParentTag} : timestamp = {header.timestamp} ≤ \
         parent timestamp = {parent.header.timestamp}"
  if header.number ≠ parent.header.number + 1 then do
    .error
      s!"{blockNumberTag} : number = {header.number} ≠ \
         parent number + 1 = {parent.header.number + 1}"
  if header.extraData.length > 32 then do
    .error
      s!"{extraDataTooBigTag} : extra data is {header.extraData.length} bytes, \
         exceeding the 32-byte maximum"
  if header.difficulty ≠ 0 then do
    .error
      s!"{difficultyOverParisTag} : difficulty = {header.difficulty} ≠ 0, \
         which is impossible after Paris"
  if header.nonce ≠ 0 then do
    .error
      s!"{headerNonceTag} : nonce = {header.nonce} ≠ 0, \
         which is impossible after Paris"
  if header.ommersHash ≠ emptyOmmerHash then do
    .error
      s!"{ommersOverParisTag} : ommers hash = {header.ommersHash} ≠ \
         empty-list hash = {emptyOmmerHash}, which is impossible after Paris"

structure MsgCallOutput : Type where
  gasLeft : Nat
  refundCounter : Int
  logs : List Log
  accountsToDelete : AdrSet
  error: Option String
  returnData : B8L

def Except.bimap
  {ε : Type u0} {δ : Type u1} {ξ : Type u2} {υ : Type u3}
  (f : ε → δ) (g : ξ → υ) : Except ε ξ → Except δ υ
  | .error e => .error <| f e
  | .ok x => .ok <| g x

def accountHasCodeOrNonce (state : State) (adr : Adr) : Bool :=
  state.getNonce adr > 0 || !(state.getCode adr).isEmpty

def accountHasStorage (state : State) (adr : Adr) : Bool :=
  !(state.getStor adr).isEmpty

def Tx.signingHash (tx : Tx) : Option B256 :=
  match tx.type with
  | .zero gasPrice receiver =>
    if tx.v = 27 || tx.v = 28
    then
      -- signing_hash_pre155
      some <|
        B8L.keccak <|
          BLT.toB8L <|
            .list [
              .b8s tx.nonce.toB8L.sig,
              .b8s gasPrice.toB8L,
              .b8s tx.gas.toB8L,
              .b8s ((receiver <&> Adr.toB8L).getD []),
              .b8s tx.value.toB8L,
              .b8s tx.data
            ]
    else do
      -- signing_hash155
      let chainId : Nat := (tx.v - 35) / 2
      some <|
        B8L.keccak <|
          BLT.toB8L <|
            .list [
              .b8s tx.nonce.toB8L.sig,
              .b8s gasPrice.toB8L,
              .b8s tx.gas.toB8L,
              .b8s ((receiver <&> Adr.toB8L).getD []),
              .b8s tx.value.toB8L,
              .b8s tx.data,
              .b8s chainId.toB8L,
              .b8s [],
              .b8s []
            ]
  -- def signing_hash2930
  | .one chainId gasPrice receiver accessList =>
    B8L.keccak <|
      .cons (0x01 : B8) <|
        BLT.toB8L <|
          .list [
            .b8s chainId.toB8L.sig,
            .b8s tx.nonce.toB8L.sig,
            .b8s gasPrice.toB8L,
            .b8s tx.gas.toB8L,
            .b8s ((receiver <&> Adr.toB8L).getD []),
            .b8s tx.value.toB8L,
            .b8s tx.data,
            accessList.toBLT
          ]
  -- signing_hash1559
  | .two chainId maxPriorityFee maxFee receiver accessList =>
    B8L.keccak <|
      .cons (0x02 : B8) <|
        BLT.toB8L <|
          .list [
            .b8s chainId.toB8L.sig,
            .b8s tx.nonce.toB8L.sig,
            .b8s maxPriorityFee.toB8L,
            .b8s maxFee.toB8L,
            .b8s tx.gas.toB8L,
            .b8s ((receiver <&> Adr.toB8L).getD []),
            .b8s tx.value.toB8L,
            .b8s tx.data,
            accessList.toBLT
          ]
  -- def signing_hash4844
  | .three chainId maxPriorityFee maxFee receiver accessList maxBlobFee blobHashes =>
    B8L.keccak <|
      .cons (0x03 : B8) <|
        BLT.toB8L <|
          .list [
            .b8s chainId.toB8L.sig,
            .b8s tx.nonce.toB8L.sig,
            .b8s maxPriorityFee.toB8L,
            .b8s maxFee.toB8L,
            .b8s tx.gas.toB8L,
            .b8s receiver.toB8L,
            .b8s tx.value.toB8L,
            .b8s tx.data,
            accessList.toBLT,
            .b8s maxBlobFee.toB8L,
            .list <| blobHashes.map <| .b8s ∘ B256.toB8L
          ]
  | .four chainId maxPriorityFee maxFee receiver accessList auths =>
    B8L.keccak <|
      .cons (0x04 : B8) <|
        BLT.toB8L <|
          .list [
            .b8s chainId.toB8L.sig,
            .b8s tx.nonce.toB8L.sig,
            .b8s maxPriorityFee.toB8L,
            .b8s maxFee.toB8L,
            .b8s tx.gas.toB8L,
            .b8s receiver.toB8L,
            .b8s tx.value.toB8L,
            .b8s tx.data,
            accessList.toBLT,
            .list <| auths.map Auth.toBLT
          ]

-- recover_sender
def recoverSender (chain_id: B64) (tx: Tx) : Except String Adr := do
  let r := tx.r.toB256
  let s := tx.s.toB256
  if (r = 0 ∨ secp256k1.curveOrder.toB256 ≤ r) then
    .error "InvalidSignatureError : bad r"
  if (s = 0 ∨ secp256k1.curveOrder.toB256 / 2 < s) then
    .error "InvalidSignatureError : bad s"
  let v := tx.v
  let signingHash ←
    tx.signingHash.toExcept "InvalidSignatureError : signing hash is None"
  match tx.type with
  | .zero _ _ =>
    if v = 27 ∨ v = 28
    then
      (secp256k1.recover signingHash (v - 27).toBool r s).toExcept
        "sender recovery failed"
    else
      let chain_id_x2 := (chain_id.toNat) * (2)
      .assert (v = 35 + chain_id_x2 ∨ v = 36 + chain_id_x2) "InvalidSignatureError : bad v"
      (secp256k1.recover signingHash (v - 35 - chain_id_x2).toBool r s).toExcept
        "sender recovery failed"
  | _ =>
    .assert (v < 2) "InvalidSignatureError"
    (secp256k1.recover signingHash v.toBool r s).toExcept "sender recovery failed"

-- recover_authority
def recoverAuthority (auth : Auth) : Except String Adr := do
  let yParity := auth.yParity
  let r := auth.r
  let s := auth.s
  if (
    1 < yParity ∨
    r = 0 ∨  secp256k1.curveOrder.toB256 ≤ r ∨
    s = 0 ∨ (secp256k1.curveOrder.toB256 / 2) < s
  ) then
    .error "InvalidSignatureError"
  let signingHash : B256 :=
    B8L.keccak <|
      List.append setCodeTxMagic <|
        BLT.toB8L <| .list [
          .b8s auth.chainId.toB8L.sig,
          .b8s auth.address.toB8L,
          .b8s auth.nonce.toB8L.sig
        ]
  -- EIP-7702 invalidates an authorization tuple, not its enclosing
  -- transaction: a recovery failure is therefore handled by
  -- `setDelegationStep` exactly like the other invalid-signature forms.
  (secp256k1.recover signingHash yParity.toBool r s ).toExcept "InvalidSignatureError"

def setDelegationStep
    (auth : Auth) (msg : Msg) (refundCounter : B256) :
    Except String (Msg × B256) := do
  if auth.chainId != msg.benv.stat.chainId.toB256 && auth.chainId != 0 then
    .ok ⟨msg, refundCounter⟩
  else if auth.nonce = B64.max then
    .ok ⟨msg, refundCounter⟩
  else
    match recoverAuthority auth with
    | .error err =>
      if err = "InvalidSignatureError" then
        .ok ⟨msg, refundCounter⟩
      else
        .error err
    | .ok authority =>
      let msg := {msg with accessedAddresses := msg.accessedAddresses.insert authority}
      let authorityAccount : Acct :=
        msg.benv.state.get authority
      let authorityCode : ByteArray := authorityAccount.code
      if ¬ (authorityCode.isEmpty ∨ isValidDelegation authorityCode) then
        .ok ⟨msg, refundCounter⟩
      else if authorityAccount.nonce != auth.nonce then
        .ok ⟨msg, refundCounter⟩
      else
        let refundCounter :=
          if AccountExists msg.benv.state authority then
            refundCounter + (perEmptyAccountCost - perAuthBaseCost).toB256
          else
            refundCounter
        let codeToSet : ByteArray :=
          if auth.address = 0 then
            .empty
          else
            (eoaDelegationMarker ++ auth.address.toB8L).toByteArray
        let msg := msg.setCode authority codeToSet
        let msg := msg.incrNonce authority
        .ok ⟨msg, refundCounter⟩

def setDelegationLoop : List Auth → Msg → B256 → Except String (Msg × B256)
  | [], msg, refundCounter => .ok ⟨msg, refundCounter⟩
  | auth :: auths, msg, refundCounter => do
    let ⟨msg, refundCounter⟩ ← setDelegationStep auth msg refundCounter
    setDelegationLoop auths msg refundCounter

def setDelegation (msg : Msg) : Except String (Msg × B256) := do
  let ⟨msg, refundCounter⟩ ← setDelegationLoop msg.tenv.stat.auths msg 0
  let msg ←
    match msg.codeAddress with
    | none =>
      .error "InvalidBlock : Invalid type 4 transaction: no target"
    | some ca =>
      .ok {
        msg with
        code := msg.benv.state.getCode ca
      }
  .ok ⟨msg, refundCounter⟩

def processMessageCall.create (msg : Msg) :
  Except String (State × MsgCallOutput) := do
  let benv := msg.benv
  let isCollision : Bool :=
    accountHasCodeOrNonce benv.state msg.currentTarget || accountHasStorage benv.state msg.currentTarget
  if isCollision then
    return ⟨benv.state, ⟨0, 0, [], .emptyWithCapacity, "AddressCollision", []⟩⟩
  else
    -- Public compatibility boundary: retain the legacy observable error.
    let evm ← Except.bimap Prod.fst id <|
      Fueled.toExcept
        ⟨"RecursionLimit", msg.benv.state, msg.benv.createdAccounts,
          msg.tenv.transientStorage⟩ <|
        processCreateMessage msg (msg.gas + 50)
    let logs := if evm.error.isNone then evm.logs else []
    let accountsToDelete := if evm.error.isNone then evm.accountsToDelete else .emptyWithCapacity
    let refundCounter ←
      if evm.error.isNone then
       (Int.toNat? evm.refundCounter).toExcept "ERROR : refund counter is negative"
      else
        .ok 0
    .ok ⟨
      evm.state,
      {
        gasLeft := evm.gasLeft,
        refundCounter := refundCounter
        logs := logs,
        accountsToDelete := accountsToDelete,
        error := evm.error,
        returnData := evm.output
      }
    ⟩

def processMessageCall.call (msg : Msg) :
  Except String (State × MsgCallOutput) := do
  let (⟨msgDelegation, refundDelegation⟩ : Msg × Nat) ←
    if msg.tenv.stat.auths.isEmpty then
      .ok (⟨msg, 0⟩ : Msg × Nat)
    else do
      let ⟨msgDelegation, setDelegationValue⟩ ← setDelegation msg
      .ok ⟨msgDelegation, setDelegationValue.toNat⟩
  let msgPc :=
    match getDelegatedCodeAddress msgDelegation.code with
    | none => msgDelegation
    | some dca =>
      {
        msgDelegation with
        disablePrecompiles := true,
        accessedAddresses := msgDelegation.accessedAddresses.insert dca,
        code := msgDelegation.benv.state.getCode dca,
        codeAddress := some dca
      }
  -- Public compatibility boundary: retain the legacy observable error.
  let evm ← Except.bimap Prod.fst id <|
    Fueled.toExcept
      ⟨"RecursionLimit", msgPc.benv.state, msgPc.benv.createdAccounts,
        msgPc.tenv.transientStorage⟩ <|
      processMessage msgPc (msgPc.gas + 50)
  let refundProcessMessage ←
    if evm.error.isNone then
      (Int.toNat? evm.refundCounter).toExcept "ERROR : refund counter is negative"
    else
      .ok 0
  let logs := if evm.error.isNone then evm.logs else []
  let accountsToDelete := if evm.error.isNone then evm.accountsToDelete else .emptyWithCapacity
  .ok ⟨
    evm.state,
    {
      gasLeft := evm.gasLeft,
      refundCounter := refundDelegation + refundProcessMessage
      logs := logs,
      accountsToDelete := accountsToDelete,
      error := evm.error,
      returnData := evm.output
    }
  ⟩

def processMessageCall (msg : Msg) :
    Except String (State × MsgCallOutput) := do
  if msg.target.isNone then
    processMessageCall.create msg
  else
    processMessageCall.call msg

def Tx.isTypeThree (tx : Tx) : Bool :=
  match tx.type with
  | .three _ _ _ _ _ _ _ => true
  | _ => false

def Tx.isTypeFour (tx : Tx) : Bool :=
  match tx.type with
  | .four _ _ _ _ _ _ => true
  | _ => false

-- calculate_total_blob_gas
def calculateTotalBlobGas (tx: Tx) : Nat :=
  match tx.type with
  | .three _ _ _ _ _ _ blobHashes => gasPerBlob * blobHashes.length
  | _ => 0

structure Receipt : Type where
  succeeded : Bool
  gasUsed : Nat
  bloom : B8L
  logs : List Log

structure BlockOutput : Type where
  blockGasUsed : Nat
  transactionsTrie : Std.TreeMap B8L Tx compare
  receiptsTrie : Std.TreeMap B8L (Fin 5 × Receipt) compare
  receiptKeys : List B8L
  blockLogs : List Log
  withdrawalsTrie : Std.TreeMap B8L Withdrawal compare
  blobGasUsed : Nat
  requests : List B8L

-- The following helpers keep the checks in the same order, with the same
-- returned payloads and error strings, as the monolithic transaction checker.
-- Splitting the executable stages makes successful runs easier to invert in
-- proofs without unfolding the whole checker at once.

def checkTransactionGasLimits
    (benv : Benv) (blockOut : BlockOutput) (tx : Tx) :
    Except String Nat :=
  let gasAvailable := benv.stat.blockGasLimit - blockOut.blockGasUsed
  let blobGasAvailable := benv.stat.rules.blob.max - blockOut.blobGasUsed
  if tx.gas > gasAvailable then
    .error
      s!"{gasAllowanceExceededTag} : transaction gas = {tx.gas} > \
         block gas available = {gasAvailable}"
  else
    let txBlobGasUsed := calculateTotalBlobGas tx
    if txBlobGasUsed > blobGasAvailable then
      .error
        s!"{type3BlobCountExceededTag} : blob gas used = {txBlobGasUsed} > \
           blob gas available = {blobGasAvailable}"
    else
      .ok txBlobGasUsed

def checkTransactionDynamicGasFee
    (baseFeePerGas gas maxPriorityFee maxFee : Nat) :
    Except String (Nat × Nat) :=
  if maxFee < maxPriorityFee then
    .error
      s!"{priorityGreaterThanMaxFeeTag} : priority fee = {maxPriorityFee} > \
         max fee = {maxFee}"
  else if maxFee < baseFeePerGas then
    .error
      s!"{insufficientMaxFeePerGasTag} : max fee = {maxFee} < \
         base fee = {baseFeePerGas}"
  else
    let maxGasFee := gas * maxFee
    if maxGasFee > B256.max.toNat then
      .error
        s!"{gasPriceProductOverflowTag} : gas * max fee = {maxGasFee} > \
           2^256 - 1"
    else
      let priorityFeePerGas := min maxPriorityFee (maxFee - baseFeePerGas)
      .ok ⟨priorityFeePerGas + baseFeePerGas, maxGasFee⟩

def checkTransactionLegacyGasFee
    (baseFeePerGas gas gasPrice : Nat) :
    Except String (Nat × Nat) :=
  if gasPrice < baseFeePerGas then
    .error
      s!"{insufficientMaxFeePerGasTag} : gas price = {gasPrice} < \
         base fee = {baseFeePerGas}"
  else
    let maxGasFee := gas * gasPrice
    if maxGasFee > B256.max.toNat then
      .error
        s!"{gasPriceProductOverflowTag} : gas * gas price = {maxGasFee} > \
           2^256 - 1"
    else
      .ok ⟨gasPrice, maxGasFee⟩

def checkTransactionGasFee (benv : Benv) (tx : Tx) :
    Except String (Nat × Nat) :=
  match tx.type with
  | .zero gasPrice _ =>
    checkTransactionLegacyGasFee benv.stat.baseFeePerGas tx.gas gasPrice
  | .one _ gasPrice _ _ =>
    checkTransactionLegacyGasFee benv.stat.baseFeePerGas tx.gas gasPrice
  | .two _ maxPriorityFee maxFee _ _ =>
    checkTransactionDynamicGasFee benv.stat.baseFeePerGas tx.gas
      maxPriorityFee maxFee
  | .three _ maxPriorityFee maxFee _ _ _ _ =>
    checkTransactionDynamicGasFee benv.stat.baseFeePerGas tx.gas
      maxPriorityFee maxFee
  | .four _ maxPriorityFee maxFee _ _ _ =>
    checkTransactionDynamicGasFee benv.stat.baseFeePerGas tx.gas
      maxPriorityFee maxFee

def checkTransactionBlobData
    (benv : Benv) (tx : Tx) (maxGasFee : Nat) :
    Except String (Nat × List B256) :=
  match tx.type with
  | .three _ _ _ _ _ maxBlobFee blobHashes =>
    if blobHashes.isEmpty then
      .error s!"{type3ZeroBlobsTag} : no blob hashes in type-3 transaction"
    else if List.any blobHashes (λ bvh => bvh.toB8L[0]! ≠ versionedHashVersionKzg) then
      .error
        s!"{type3InvalidBlobVersionedHashTag} : a blob versioned hash has \
           a version byte other than {versionedHashVersionKzg}"
    else
      let blobGasPrice :=
        calculate_blob_gas_price benv.stat.rules.blob benv.stat.excessBlobGas
      if maxBlobFee < blobGasPrice then
        .error "InsufficientMaxFeePerBlobGasError : insufficient max fee per blob gas"
      else
        .ok ⟨maxGasFee + calculateTotalBlobGas tx * maxBlobFee, blobHashes⟩
  | _ => .ok ⟨maxGasFee, []⟩

def checkTransactionReceiver (tx : Tx) : Except String Unit :=
  if tx.isTypeThree then
    if tx.type.receiver?.isNone then
      .error
        s!"{type3ContractCreationTag} : type-3 transactions cannot create contracts"
    else
      .ok ()
  else
    .ok ()

def checkTransactionAuthorizationList (tx : Tx) : Except String Unit :=
  match tx.type with
  | .four _ _ _ _ _ [] =>
    .error s!"{emptyAuthorizationListTag} : empty authorization list"
  | _ => .ok ()

def checkTransactionChainId (benv : Benv) (tx : Tx) : Except String Unit :=
  match tx.type with
  | .zero _ _ =>
    if tx.v < 35 || (tx.v - 35) / 2 = benv.stat.chainId.toNat then .ok ()
    else .error s!"{invalidChainIdTag} : transaction chain ID = {(tx.v - 35) / 2}"
  | .one chainId _ _ _
  | .two chainId _ _ _ _
  | .three chainId _ _ _ _ _ _
  | .four chainId _ _ _ _ _ =>
    if chainId = benv.stat.chainId then .ok ()
    else .error s!"{invalidChainIdTag} : transaction chain ID = {chainId}"

def checkTransactionSenderCode (senderAccount : Acct) :
    Except String Unit :=
  if ¬ (senderAccount.code.isEmpty ∨ isValidDelegation senderAccount.code) then
    .error s!"{senderNotEoaTag} : sender has non-delegation code"
  else
    .ok ()

def checkTransactionSenderAccount
    (senderAccount : Acct) (tx : Tx) (maxGasFee : Nat) :
    Except String Unit :=
  if senderAccount.nonce > tx.nonce then
    .error
      s!"{nonceMismatchTooLowTag} : transaction nonce = {tx.nonce.toNat} < \
         sender nonce = {senderAccount.nonce.toNat}"
  else if senderAccount.nonce < tx.nonce then
    .error
      s!"{nonceMismatchTooHighTag} : transaction nonce = {tx.nonce.toNat} > \
         sender nonce = {senderAccount.nonce.toNat}"
  else if senderAccount.bal.toNat < maxGasFee + tx.value then
    .error
      s!"{insufficientAccountFundsTag} : sender balance = \
         {senderAccount.bal.toNat} < max gas fee = {maxGasFee} + \
         transaction value = {tx.value}"
  else
    checkTransactionSenderCode senderAccount

-- check_transaction
def checkTransaction (benv : Benv) (blockOut : BlockOutput) (tx : Tx) :
    Except String (Adr × Nat × List B256 × Nat) := do
  let txBlobGasUsed ← checkTransactionGasLimits benv blockOut tx
  checkTransactionChainId benv tx
  let senderAddress ← recoverSender benv.stat.chainId tx
  let senderAccount := benv.state.get senderAddress
  let ⟨effectiveGasPrice, maxGasFee⟩ ← checkTransactionGasFee benv tx
  let ⟨maxGasFee, blobVersionedHashes⟩ ←
    checkTransactionBlobData benv tx maxGasFee
  checkTransactionReceiver tx
  checkTransactionAuthorizationList tx
  checkTransactionSenderAccount senderAccount tx maxGasFee
  .ok ⟨
    senderAddress,
    effectiveGasPrice,
    blobVersionedHashes,
    txBlobGasUsed
  ⟩

def calculateIntrinsicCost (tx: Tx) : Nat × Nat :=
  -- `foldl` (tail-recursive) rather than `(map …).sum`: the latter's
  -- non-tail-recursive `List.map` overflows the stack on large calldata
  -- (e.g. the 1.2 MB inputs in the EIP-2537 stress fixtures).
  let tokensInCalldata : Nat :=
    tx.data.foldl (fun acc x => acc + (if x = 0 then 1 else 4)) 0
  let callDataFloorGasCost : Nat :=
    tokensInCalldata * floorCalldataCost + txBaseCost
  let dataCost : Nat :=
    tokensInCalldata * standardCallDataTokenCost
  let createCost : Nat :=
      match tx.type.receiver? with
      | none => txCreateCost + initCodeCost (tx.data).length
      | some _ => 0
  let accessListCost : Nat :=
    let accessList :=
      match tx.type with
      | .zero _ _ => []
      | .one _ _ _ accessList => accessList
      | .two _ _ _ _ accessList => accessList
      | .three _ _ _ _ accessList _ _ => accessList
      | .four _ _ _ _ accessList _ => accessList
    let accessItemCost : (Adr × List B256) → Nat
      | ⟨_, keys⟩ =>
        txAccessListAddressCost + keys.length * txAccessListStorageKeyCost
    (accessList.map accessItemCost).sum
  let authCost : Nat :=
    match tx.type with
    | .four _ _ _ _ _ auths => perEmptyAccountCost * auths.length
    | _ => 0
  ⟨
    txBaseCost + dataCost + createCost + accessListCost + authCost,
    callDataFloorGasCost
  ⟩

def checkInitcodeSize (code : CodeLimits) (receiver : Option Adr)
    (dataLength : Nat) : Except String Unit :=
  if receiver.isNone && dataLength > code.maxInitCodeSize then
    .error
      s!"{initcodeSizeExceededTag} : initcode is {dataLength} bytes, \
         exceeding the {code.maxInitCodeSize}-byte maximum"
  else
    .ok ()

-- validate_transaction
def validateTransaction (rules : ForkRules) (tx : Tx) :
    Except String (Nat × Nat) := do
  let ⟨intrinsicGas, callDataFloorGasCost⟩ := calculateIntrinsicCost tx
  if max intrinsicGas callDataFloorGasCost > tx.gas
    then
      .error
        s!"{intrinsicGasTooLowTag} : transaction gas = {tx.gas} < \
           max intrinsic/calldata floor cost = \
           {max intrinsicGas callDataFloorGasCost}"
  if tx.nonce = B64.max
    then .error s!"{nonceIsMaxTag} : transaction nonce is 2^64 - 1"
  checkInitcodeSize rules.code tx.type.receiver? tx.data.length
  .ok ⟨intrinsicGas, callDataFloorGasCost⟩

def prepareMessage (benv: Benv) (tenv: Tenv) (tx: Tx) :
  Except String Msg := do
  let ⟨currentTarget, msgData, code, codeAddress⟩ :
    Adr × B8L × ByteArray × Option Adr :=
    match tx.type.receiver? with
    | none => ⟨
        compute_contract_address
          tenv.stat.origin
          (benv.state.getNonce tenv.stat.origin - 1),
        [],
        .mk (.mk tx.data),
        none
      ⟩
    | some target => ⟨
        target,
        tx.data,
        benv.state.getCode target,
        target
      ⟩
  let accessedAddresses : AdrSet :=
    tenv.stat.accessListAddresses.insertMany
      [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, tenv.stat.origin, currentTarget]
  .ok {
    benv := benv,
    tenv := tenv,
    caller := tenv.stat.origin,
    target := tx.type.receiver?,
    gas := tenv.stat.gas,
    value := tx.value.toB256,
    data := msgData,
    code := code,
    depth := 1024,
    currentTarget := currentTarget,
    codeAddress := codeAddress
    shouldTransferValue := true,
    isStatic := false,
    accessedAddresses := accessedAddresses,
    accessedStorageKeys := tenv.stat.accessListStorageKeys,
    disablePrecompiles := false
  }

-- calculate_data_fee
def calculate_data_fee (blob : BlobSchedule) (excess_blob_gas: Nat) (tx: Tx) :
    Nat :=
  calculateTotalBlobGas tx * calculate_blob_gas_price blob excess_blob_gas

def getTxHash (tx : Tx) : B256 := tx.toBLT.toB8L.keccak

def Receipt.toStrings (r : Receipt) : List String :=
  fork "RECEIPT" [
    [s!"SUCCEEDED: {r.succeeded}"],
    [s!"GAS USED: {r.gasUsed}"],
    fork "BLOOM" [r.bloom.toHex.chunks 64],
    fork "LOGS" (r.logs.map Log.toStrings)
  ]

instance : ToString Receipt where
  toString := String.joinln ∘ Receipt.toStrings

def Receipt.toBLT (r : Receipt) : BLT :=
  .list [
    .b8s (if r.succeeded then [0x01] else []),
    .b8s r.gasUsed.toB8LPack,
    .b8s r.bloom,
    .list (r.logs.map Log.toBLT)
  ]

-- make_receipt
def makeReceipt
  (tx: Tx)
  (error: Option String)
  (gasUsed: Nat)
  (logs: List Log) : Fin 5 × Receipt :=
  let receipt : Receipt := {
    succeeded := error.isNone,
    gasUsed := gasUsed,
    bloom := logsBloom logs,
    logs := logs
  }
  let head : Fin 5 :=
    match tx.type with
    | .zero _ _ => 0
    | .one _ _ _ _ => 1
    | .two _ _ _ _ _ => 2
    | .three _ _ _ _ _ _ _ => 3
    | .four _ _ _ _ _ _ => 4
  ⟨head, receipt⟩

def BlockOutput.init : BlockOutput :=
  {
    blockGasUsed := 0
    transactionsTrie := .empty
    receiptsTrie := .empty
    receiptKeys := []
    blockLogs := []
    withdrawalsTrie := .empty
    blobGasUsed := 0
    requests := []
  }

---------------- TRANSACTION-REJECTION REGRESSION CHECKS ----------------

-- These checks exercise the real producer functions, not merely the fixture
-- classifier.  They pin the validation order and the distinctions that used
-- to be hidden behind `InvalidTransaction` and `NonceMismatchError`.

private def fixtureTestTx : Tx :=
  {
    nonce := 0
    gas := txBaseCost
    value := 0
    data := []
    v := 27
    r := []
    s := []
    type := .zero 10 (some 0)
  }

private def fixtureTestBenv (blockGasLimit : Nat := 10000000) : Benv :=
  {
    state := .empty
    createdAccounts := .emptyWithCapacity
    stat := {
      rules := pragueRules
      chainId := 1
      origState := .empty
      blockGasLimit := blockGasLimit
      blockHashes := []
      coinbase := 0
      number := 1
      baseFeePerGas := 1
      time := 0
      prevRandao := 0
      excessBlobGas := 0
      parentBeaconBlockRoot := 0
    }
  }

private def fixtureTestAccount
    (nonce : B64) (bal : B256) (code : ByteArray := .empty) : Acct :=
  { nonce := nonce, bal := bal, stor := .empty, code := code }

#guard hasTag intrinsicGasTooLowTag <|
  validateTransaction pragueRules {fixtureTestTx with gas := txBaseCost - 1}
#guard hasTag nonceIsMaxTag <|
  validateTransaction pragueRules {fixtureTestTx with nonce := B64.max}
#guard hasTag initcodeSizeExceededTag <|
  checkInitcodeSize pragueRules.code none (pragueRules.code.maxInitCodeSize + 1)

-- The initcode bound comes from the rules record, not from a global: a smaller
-- limit rejects an initcode the Prague limit accepts, at the same boundary.
private def guardTightCodeLimits : CodeLimits :=
  { maxCodeSize := 100, maxInitCodeSize := 200 }

#guard (checkInitcodeSize pragueRules.code none 200).toOption.isSome
#guard (checkInitcodeSize guardTightCodeLimits none 200).toOption.isSome
#guard hasTag initcodeSizeExceededTag <|
  checkInitcodeSize guardTightCodeLimits none 201
-- A non-creation transaction is unaffected by the limit under either schedule.
#guard (checkInitcodeSize guardTightCodeLimits (some 0) 100000).toOption.isSome

#guard hasTag priorityGreaterThanMaxFeeTag <|
  checkTransactionDynamicGasFee 1 1 2 1
#guard hasTag insufficientMaxFeePerGasTag <|
  checkTransactionDynamicGasFee 2 1 1 1
#guard hasTag gasPriceProductOverflowTag <|
  checkTransactionDynamicGasFee 0 2 0 (2 ^ 255)
#guard hasTag gasPriceProductOverflowTag <|
  checkTransactionLegacyGasFee 0 2 (2 ^ 255)

#guard hasTag gasAllowanceExceededTag <|
  checkTransactionGasLimits (fixtureTestBenv txBaseCost) .init
    {fixtureTestTx with gas := txBaseCost + 1}
#guard hasTag type3BlobCountExceededTag <|
  checkTransactionGasLimits fixtureTestBenv .init
    { fixtureTestTx with
      type := .three 1 1 10 0 [] 1 (List.replicate 10 0) }
#guard hasTag type3ZeroBlobsTag <|
  checkTransactionBlobData fixtureTestBenv
    {fixtureTestTx with type := .three 1 1 10 0 [] 1 []} 10
#guard hasTag type3InvalidBlobVersionedHashTag <|
  checkTransactionBlobData fixtureTestBenv
    {fixtureTestTx with type := .three 1 1 10 0 [] 1 [0]} 10

#guard hasTag nonceMismatchTooLowTag <|
  checkTransactionSenderAccount (fixtureTestAccount 2 100) fixtureTestTx 0
#guard hasTag nonceMismatchTooHighTag <|
  checkTransactionSenderAccount (fixtureTestAccount 0 100)
    {fixtureTestTx with nonce := 1} 0
#guard hasTag insufficientAccountFundsTag <|
  checkTransactionSenderAccount (fixtureTestAccount 0 0) fixtureTestTx 1
#guard hasTag senderNotEoaTag <|
  checkTransactionSenderAccount
    (fixtureTestAccount 0 100 (ByteArray.mk #[0x01])) fixtureTestTx 0


-- process_transaction
def processTransaction
  (benv: Benv) (bout : BlockOutput)
  (tx: Tx) (index : Nat) : Except String (State × BlockOutput) := do
  -- NOTE: linearized into a straight `let ← .ok (…)` / `let := …` chain
  -- (no `mut`/`for`) so the block inverts cleanly with `of_bind_eq_ok` and the
  -- `bout` bookkeeping stays opaque.  Definitionally equal to the previous
  -- `mut`/`for` form except that the final account-deletion `for` is expressed
  -- as `foldl`, which agrees because `destroyAccount` commutes over the
  -- distinct addresses of the `accountsToDelete` set.
  let benv := benv.beginTransaction
  let bout ← .ok {bout with
    transactionsTrie := bout.transactionsTrie.insert (BLT.b8s index.toB8L).toB8L tx}
  let ⟨intrinsicGas, calldataFloorGasCost⟩ ←
    validateTransaction benv.stat.rules tx
  let ⟨
    sender,
    effectiveGasPrice,
    blobVersionedHashes,
    txBlobGasUsed
  ⟩ ← checkTransaction benv bout tx
  let blobGasFee :=
    if tx.isTypeThree
    then calculate_data_fee benv.stat.rules.blob benv.stat.excessBlobGas tx
    else 0
  let effectiveGasFee := tx.gas * effectiveGasPrice
  let gas := tx.gas - intrinsicGas
  let state : State := benv.state.incrNonce sender
  let state ← (state.subBal sender (effectiveGasFee + blobGasFee).toB256).toExcept
    "ERROR : balance underflow"
  let preaccessedAddresses : AdrSet :=
    .ofList (benv.stat.coinbase :: tx.accessList.map Prod.fst)
  let preaccessedStorageKeys : KeySet :=
    .ofList (tx.accessList.map <| λ ⟨adr, keys⟩ => keys.map (⟨adr, ·⟩)).flatten
  let tenv : Tenv := {
    transientStorage := .empty
    stat := {
      origin := sender
      gasPrice := effectiveGasPrice
      gas := gas
      accessListAddresses := preaccessedAddresses
      accessListStorageKeys := preaccessedStorageKeys
      blobVersionedHashes := blobVersionedHashes
      auths := tx.auths
      indexInBlock := index
      txHash := getTxHash tx
    }
  }
  let msg ← prepareMessage {benv with state := state} tenv tx
  let ⟨state, txOutput⟩ ← processMessageCall msg
  let txGasUsedBeforeRefund := tx.gas - txOutput.gasLeft
  let refundCounter : Nat ←
    (Int.toNat? txOutput.refundCounter).toExcept "ERROR : refund counter is negative"
  let txGasRefund : Nat :=
    min (txGasUsedBeforeRefund / 5) refundCounter
  let txGasUsedAfterRefund : Nat :=
    max (txGasUsedBeforeRefund - txGasRefund) calldataFloorGasCost
  let txGasLeft :=
    tx.gas - txGasUsedAfterRefund
  let gasRefundAmount : Nat :=
    txGasLeft * effectiveGasPrice
  let priorityFeePerGas := effectiveGasPrice - benv.stat.baseFeePerGas
  let transactionFee := txGasUsedAfterRefund * priorityFeePerGas
  let state := state.addBal sender gasRefundAmount.toB256
  let state := state.addBal benv.stat.coinbase transactionFee.toB256
  let state := txOutput.accountsToDelete.toList.foldl destroyAccount state
  let bout ← .ok {bout with
    blockGasUsed := bout.blockGasUsed + txGasUsedAfterRefund,
    blobGasUsed := bout.blobGasUsed + txBlobGasUsed}
  let receipt :=
    makeReceipt tx txOutput.error bout.blockGasUsed txOutput.logs
  let receiptKey : B8L := BLT.toB8L <| .b8s index.toB8L
  let bout ← .ok {bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie := bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ txOutput.logs}
  .ok ⟨state, bout⟩

def BlockOutput.withWithdrawalsTrie
    (bo : BlockOutput) (tr : Std.TreeMap B8L Withdrawal compare) : BlockOutput :=
  {bo with withdrawalsTrie := tr}

def processWithdrawalsTrie (tr : Std.TreeMap B8L Withdrawal compare)
    (wds : List Withdrawal) : Std.TreeMap B8L Withdrawal compare :=
  List.foldl
    (λ acc ⟨i, wd⟩ => acc.insert (BLT.toB8L <| .b8s i.toB8L) wd)
    tr
    wds.putIndex

def processWithdrawalsState (st : State) (wds : List Withdrawal) : State :=
  List.foldl
    (λ acc wd => acc.addBal wd.recipient (wd.amount * (10 ^ 9).toB256))
    st
    wds

-- def process_withdrawal
def processWithdrawals
  (benv : Benv) (bout : BlockOutput) (wds : List Withdrawal) : State × BlockOutput :=
  let trie := processWithdrawalsTrie bout.withdrawalsTrie wds
  let state := processWithdrawalsState benv.state wds
  ⟨state, bout.withWithdrawalsTrie trie⟩

-- Access lists, blob hashes, and authorization tuples arrive inside typed
-- transactions, so their fields are untrusted in exactly the way withdrawal
-- fields are: every shape must be checked before any truncating conversion,
-- and a wrong list shape is a different reason from an oversized scalar.

def BLT.toExStrStorageKey : BLT → Except String B256
  | .b8s xs => xs.toRlpHash "access list storage key"
  | .list _ =>
    .error <| rlpStructureError "access list storage key"
      "expected a byte-string item"

def BLT.toExStrAccessItem : BLT → Except String (Adr × List B256)
  | .list [.b8s ar, .list ksr] => do
    let a ← ar.toRlpAdr "access list address"
    let ks ← List.mapM BLT.toExStrStorageKey ksr
    .ok ⟨a, ks⟩
  | _ =>
    .error <| rlpStructureError "access list item"
      "expected [address, [storage key, ...]]"

def BLT.toExStrAccessList : BLT → Except String AccessList
  | .list rs => List.mapM BLT.toExStrAccessItem rs
  | .b8s _ =>
    .error <| rlpStructureError "access list" "expected a list item"

def BLT.toExStrBlobHash : BLT → Except String B256
  | .b8s xs => xs.toRlpHash "blob versioned hash"
  | .list _ =>
    .error <| rlpStructureError "blob versioned hash"
      "expected a byte-string item"

def BLT.toExStrAuth : BLT → Except String Auth
  | .list [
      .b8s chainId,
      .b8s address,
      .b8s nonce,
      .b8s yParity,
      .b8s r,
      .b8s s
    ] => do
      let chainId ← chainId.toRlpB256 "authorization chainId"
      let address ← address.toRlpAdr "authorization address"
      let nonce ← nonce.toRlpB64 "authorization nonce"
      let yParity ← yParity.toRlpNat "authorization yParity" 32
      let r ← r.toRlpB256 "authorization r"
      let s ← s.toRlpB256 "authorization s"
      .ok {
        chainId := chainId
        address := address
        nonce := nonce
        yParity := yParity
        r := r
        s := s
      }
  | _ =>
    .error <| rlpStructureError "authorization"
      "expected a list of six byte-string fields"

def B8L.toExStrTx : B8L → Except String Tx
  | [] =>
    .error <| rlpStructureError "typed transaction"
      "cannot decode an empty byte string"
  | x :: xs =>
    -- Every scalar is bounded before conversion: `B8L.toB64` truncates modulo
    -- 2^64, so it may only see bytes returned by a strict decoder. Signature
    -- scalars keep their minimally encoded bytes once validated, so signing
    -- and trie bytes are unchanged for valid transactions.
    match x, B8L.toBLT? xs with
    | 0x01, some (.list [
        .b8s chainId,
        .b8s nonce,
        .b8s gasPrice,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .b8s yParity,
        .b8s r,
        .b8s s
      ]) => do
      let chainId ← chainId.toRlpB64 "type-1 transaction chainId"
      let nonce ← nonce.toRlpB64 "type-1 transaction nonce"
      let gasPrice ← gasPrice.toRlpNat "type-1 transaction gasPrice" 32
      let gas ← gas.toRlpNat "type-1 transaction gas" 32
      let receiver ← receiver.toRlpReceiver "type-1 transaction receiver"
      let value ← value.toRlpNat "type-1 transaction value" 32
      let accessList ← accessList.toExStrAccessList
      let yParity ← yParity.toRlpNat "type-1 transaction yParity" 32
      let _ ← r.toRlpB256 "type-1 transaction r"
      let _ ← s.toRlpB256 "type-1 transaction s"
      .ok {
        nonce := nonce,
        gas := gas,
        value := value,
        data := data,
        v := yParity,
        r := r,
        s := s,
        type := .one chainId gasPrice receiver accessList
      }
    | 0x01, _ =>
      .error <| rlpStructureError "type-1 transaction"
        "expected a list of eleven fields"
    | 0x02, some (.list [
        .b8s chainId,
        .b8s nonce,
        .b8s maxPriorityFee,
        .b8s maxFee,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .b8s yParity,
        .b8s r,
        .b8s s
      ]) => do
      let chainId ← chainId.toRlpB64 "type-2 transaction chainId"
      let nonce ← nonce.toRlpB64 "type-2 transaction nonce"
      let maxPriorityFee ← maxPriorityFee.toRlpNat "type-2 transaction maxPriorityFee" 32
      let maxFee ← maxFee.toRlpNat "type-2 transaction maxFee" 32
      let gas ← gas.toRlpNat "type-2 transaction gas" 32
      let receiver ← receiver.toRlpReceiver "type-2 transaction receiver"
      let value ← value.toRlpNat "type-2 transaction value" 32
      let accessList ← accessList.toExStrAccessList
      let yParity ← yParity.toRlpNat "type-2 transaction yParity" 32
      let _ ← r.toRlpB256 "type-2 transaction r"
      let _ ← s.toRlpB256 "type-2 transaction s"
      .ok {
        nonce := nonce,
        gas := gas,
        value := value,
        data := data,
        v := yParity,
        r := r,
        s := s,
        type := .two chainId maxPriorityFee maxFee receiver accessList
      }
    | 0x02, _ =>
      .error <| rlpStructureError "type-2 transaction"
        "expected a list of twelve fields"
    | 0x03, some (.list [
        .b8s chainId,
        .b8s nonce,
        .b8s maxPriorityFee,
        .b8s maxFee,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .b8s maxBlobFee,
        .list blobHashes,
        .b8s yParity,
        .b8s r,
        .b8s s
      ]) => do
      let chainId ← chainId.toRlpB64 "type-3 transaction chainId"
      let nonce ← nonce.toRlpB64 "type-3 transaction nonce"
      let maxPriorityFee ← maxPriorityFee.toRlpNat "type-3 transaction maxPriorityFee" 32
      let maxFee ← maxFee.toRlpNat "type-3 transaction maxFee" 32
      let gas ← gas.toRlpNat "type-3 transaction gas" 32
      -- A type-3 receiver is a mandatory address at the RLP level; the
      -- semantic contract-creation rejection downstream remains as defense
      -- in depth for transactions that arrive already decoded.  Empty is the
      -- official type-3 contract-creation failure, while a nonempty value of
      -- any width other than twenty bytes remains an RLP shape failure.
      if receiver.isEmpty then
        .error
          s!"{type3ContractCreationTag} : type-3 transaction receiver is empty"
      let receiver ← receiver.toRlpAdr "type-3 transaction receiver"
      let value ← value.toRlpNat "type-3 transaction value" 32
      let accessList ← accessList.toExStrAccessList
      let maxBlobFee ← maxBlobFee.toRlpNat "type-3 transaction maxBlobFee" 32
      let blobHashes ← List.mapM BLT.toExStrBlobHash blobHashes
      let yParity ← yParity.toRlpNat "type-3 transaction yParity" 32
      let _ ← r.toRlpB256 "type-3 transaction r"
      let _ ← s.toRlpB256 "type-3 transaction s"
      .ok {
        nonce := nonce,
        gas := gas,
        value := value,
        data := data,
        v := yParity,
        r := r,
        s := s,
        type :=
          .three chainId maxPriorityFee maxFee receiver accessList
            maxBlobFee blobHashes
      }
    | 0x03, _ =>
      .error <| rlpStructureError "type-3 transaction"
        "expected a list of fourteen fields"
    | 0x04, some (.list [
        .b8s chainId,
        .b8s nonce,
        .b8s maxPriorityFee,
        .b8s maxFee,
        .b8s gas,
        .b8s receiver,
        .b8s value,
        .b8s data,
        accessList,
        .list auths,
        .b8s yParity,
        .b8s r,
        .b8s s
      ]) => do
      let chainId ← chainId.toRlpB64 "type-4 transaction chainId"
      let nonce ← nonce.toRlpB64 "type-4 transaction nonce"
      let maxPriorityFee ← maxPriorityFee.toRlpNat "type-4 transaction maxPriorityFee" 32
      let maxFee ← maxFee.toRlpNat "type-4 transaction maxFee" 32
      let gas ← gas.toRlpNat "type-4 transaction gas" 32
      if receiver.isEmpty then
        .error s!"{type4ContractCreationTag} : type-4 transaction receiver is empty"
      let receiver ← receiver.toRlpAdr "type-4 transaction receiver"
      let value ← value.toRlpNat "type-4 transaction value" 32
      let accessList ← accessList.toExStrAccessList
      let auths ← List.mapM BLT.toExStrAuth auths
      let yParity ← yParity.toRlpNat "type-4 transaction yParity" 32
      let _ ← r.toRlpB256 "type-4 transaction r"
      let _ ← s.toRlpB256 "type-4 transaction s"
      .ok {
        nonce := nonce,
        gas := gas,
        value := value,
        data := data,
        v := yParity,
        r := r,
        s := s,
        type := .four chainId maxPriorityFee maxFee receiver accessList auths
      }
    | 0x04, _ =>
      .error <| rlpStructureError "type-4 transaction"
        "expected a list of thirteen fields"
    | x, _ => .error s!"ERROR : type-{x} txs do not exist, decoding failed"

def decodeTx : B8L ⊕ Tx → Except String Tx
  | .inl xs => xs.toExStrTx
  | .inr tx => .ok tx


def processSystemTransactionTenv (benv : Benv) : Tenv :=
  {
    transientStorage := .empty,
    stat := {
      origin := systemAddress,
      gasPrice := benv.stat.baseFeePerGas,
      gas := systemTransactionGas,
      accessListAddresses := .emptyWithCapacity
      accessListStorageKeys := .emptyWithCapacity
      blobVersionedHashes := [],
      auths := [],
      indexInBlock := none,
      txHash := none
    }
  }

def processSystemTransactionMsg (benv : Benv) (tenv : Tenv)
    (target : Adr) (data : B8L) (code : ByteArray) : Msg :=
  {
    benv := benv,
    tenv := tenv,
    caller := systemAddress,
    target := target,
    gas := systemTransactionGas,
    value := 0,
    data := data,
    code := code,
    depth := 1024,
    currentTarget := target,
    codeAddress := target,
    shouldTransferValue := false,
    isStatic := false,
    accessedAddresses := .emptyWithCapacity,
    accessedStorageKeys := .emptyWithCapacity,
    disablePrecompiles := false
  }

-- process_system_transaction
-- The single boundary shared by all four system transactions (beacon roots,
-- history storage, withdrawal requests, consolidation requests), so each takes
-- its own input state as the original state.
def processSystemTransaction (benv : Benv)
  (target : Adr) (code : ByteArray) (data : B8L) :
  Except String (State × MsgCallOutput) := do
  let benv := benv.beginTransaction
  let txEnv : Tenv := processSystemTransactionTenv benv
  let systemTxMsg : Msg :=
    processSystemTransactionMsg benv txEnv target data code
  processMessageCall systemTxMsg

def extractDepositData (data : B8L) : Except String B8L := do
  if data.length != depositEventLength then
    .error s!"{depositEventLayoutTag} : invalid deposit event data length"
  if data.sliceToNat 0 32 ≠ pubkeyOffset then
    .error s!"{depositEventLayoutTag} : invalid pubkey offset in deposit log"
  if data.sliceToNat 32 32 ≠ withdrawalCredentialsOffset then
    .error s!"{depositEventLayoutTag} : invalid withdrawal credentials offset in deposit log"
  if data.sliceToNat 64 32 ≠ amountOffset then
    .error s!"{depositEventLayoutTag} : invalid amount offset in deposit log"
  if data.sliceToNat 96 32 ≠ signatureOffset then
    .error s!"{depositEventLayoutTag} : invalid signature offset in deposit log"
  if data.sliceToNat 128 32 ≠ indexOffset then
    .error s!"{depositEventLayoutTag} : invalid index offset in deposit log"
  if data.sliceToNat pubkeyOffset 32 ≠ pubkeySize then
    .error s!"{depositEventLayoutTag} : invalid pubkey size in deposit log"
  let pubkey : B8L := data.slice! (pubkeyOffset + 32) pubkeySize
  if data.sliceToNat withdrawalCredentialsOffset 32 ≠ withdrawalCredentialsSize then
    .error s!"{depositEventLayoutTag} : invalid withdrawal credentials size in deposit log"
  let withdrawalCredentials : B8L :=
    data.slice! (withdrawalCredentialsOffset + 32) withdrawalCredentialsSize
  if data.sliceToNat amountOffset 32 ≠ amountSize then
    .error s!"{depositEventLayoutTag} : invalid amount size in deposit log"
  let amount : B8L := data.slice! (amountOffset + 32) amountSize
  if data.sliceToNat signatureOffset 32 ≠ signatureSize then
    .error s!"{depositEventLayoutTag} : invalid signature size in deposit log"
  let signature : B8L := data.slice! (signatureOffset + 32) signatureSize
  if data.sliceToNat indexOffset 32 ≠ indexSize then
    .error s!"{depositEventLayoutTag} : invalid index size in deposit log"
  let index : B8L := data.slice! (indexOffset + 32) indexSize
  .ok (pubkey ++ withdrawalCredentials ++ amount ++ signature ++ index)

-- parse_deposit_requests
def parseDepositRequests
  (bout : BlockOutput) : Except String B8L := do
  let mut depositRequests : B8L := []
  for key in bout.receiptKeys do
    let ⟨_, receipt⟩  ←
      bout.receiptsTrie[key]?.toExcept "ERROR : receipt not found"
    for log in receipt.logs do
      if (
        log.address = depositContractAddress ∧
        log.topics[0]? = some depositEventSignatureHash
      ) then
        let request ← extractDepositData log.data
        depositRequests := depositRequests ++ request
  .ok depositRequests

def processUncheckedSystemTransaction
  (benv : Benv) (target : Adr) (data : B8L) :
  Except String (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  processSystemTransaction benv target systemContractCode data

def processCheckedSystemTransaction
  (benv : Benv) (target : Adr) (data : B8L) :
  Except String (State × MsgCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  if systemContractCode.isEmpty then
    .error s!"InvalidBlock : System contract address {target.toHex} does not contain code"
  let ⟨state, systemTxOutput⟩ ←
    processSystemTransaction benv target systemContractCode data
  if systemTxOutput.error.isSome then
    .error s!"{systemContractCallFailedTag} : system contract ({target.toHex}) call failed: \
      {systemTxOutput.error.get!}"
  .ok ⟨state, systemTxOutput⟩

def processGeneralPurposeRequests
  (benv : Benv) (bout : BlockOutput) :
  Except String (State × BlockOutput) := do
  let depositRequests ← parseDepositRequests bout
  let mut requestsFromExecution : List B8L := bout.requests
  if depositRequests.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [depositRequestType ++ depositRequests]
  let ⟨state, withdrawalOutput⟩  ←
    processCheckedSystemTransaction benv
      withdrawalRequestPredeployAddress
      []
  let benv := {benv with state := state}
  if withdrawalOutput.returnData.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [withdrawalRequestType ++ withdrawalOutput.returnData]
  let ⟨state, consolidationOutput⟩  ←
    processCheckedSystemTransaction benv
      consolidationRequestPredeployAddress
      []
  if consolidationOutput.returnData.length > 0 then
    requestsFromExecution :=
      requestsFromExecution ++ [consolidationRequestType ++ consolidationOutput.returnData]
  .ok ⟨state, {bout with requests := requestsFromExecution}⟩

def applyTransactions :
    List (Nat × Tx) → Benv → BlockOutput → Except String (Benv × BlockOutput)
  | [], benv, bout => .ok (benv, bout)
  | ⟨i, tx⟩ :: txis, benv , bout => do
    let ⟨st, bout'⟩ ← processTransaction benv bout tx i
    applyTransactions txis (benv.withState st) bout'

def applyBody
  (benv : Benv) (txs : List (B8L ⊕ Tx)) (wds : List Withdrawal) :
  Except String (State × BlockOutput) := do
  cprint "\n================================ BEACON ROOTS TX ================================\n"
  let ⟨stBeacon, _⟩ ←
    processUncheckedSystemTransaction benv
      beaconRootsAddress
      benv.stat.parentBeaconBlockRoot.toB8L
  let benvBeacon : Benv := benv.withState stBeacon
  cprint "\n================================ HISTORY STORAGE TX ================================\n"
  let lastHash ←
     benvBeacon.stat.blockHashes.getLast?.toExcept "ERROR : block hashes is empty"
  let ⟨stHistory, _⟩ ←
    processUncheckedSystemTransaction benvBeacon
      historyStorageAddress
      lastHash.toB8L
  let benvHistory := benvBeacon.withState stHistory
  cprint "\n================================ MAIN TXS ================================\n"
  let ⟨benvTxs, boutTxs⟩ ←
    applyTransactions (← txs.mapM decodeTx).putIndex benvHistory .init
  cprint s!"\nSTATE AFTER TEST TXS :"
  cprint s!"{benvTxs.state}"
  cprint "\n================================ PROCESS WITHDRAWALS ================================\n"
  let ⟨stWds, boutWds⟩ :=
    processWithdrawals benvTxs boutTxs wds
  cprint "\n================================ PROCESS GENERAL PURPOSE REQUESTS ================================\n"
  processGeneralPurposeRequests (benvTxs.withState stWds) boutWds

-- get_last256_block_hashes
def getLast256BlockHashes (chain : BlockChain) : List B256 :=
  match chain.blocks.reverse.take 255 with
  | [] => []
  | block :: blocks =>
    let hash : B256 := (Header.toBLT block.header).toB8L.keccak
    let hashes : List B256 :=
      (block :: blocks).map <| fun x => x.header.parentHash
    (hash :: hashes).reverse

def computeRequestsHash (requests : List B8L) : B256 :=
  -- EIP-7685 commits the SHA-256 digest of each type-prefixed request, then
  -- hashes their concatenation once more.  This is deliberately not the EVM
  -- Keccak primitive used by transaction and trie commitments.
  let hashes := requests.map (fun r => r.sha256.toB8L)
  B8L.sha256 <| List.flatten hashes

def State.root (w : State) : B256 :=
  let keyVals := (List.map toKeyVal w.toList)
  let finalNTB : NTB := Std.TreeMap.ofList keyVals _
  trie finalNTB

def stateTransitionChecks (bout : BlockOutput) (header : Header)
    (transactionsRoot blockStateRoot receiptRoot : B256)
    (blockLogsBloom : B8L) (withdrawalsRoot requestsHash : B256) :
    Except String Unit := do
  if bout.blockGasUsed ≠ header.gasUsed then
    .error
      s!"{gasUsedMismatchTag} : computed block gas used = {bout.blockGasUsed} ≠ \
         header block gas used = {header.gasUsed}"
  if transactionsRoot ≠ header.txsRoot then
    .error
      s!"{transactionsRootTag} : computed transactions root = {transactionsRoot} \
         ≠ header transactions root = {header.txsRoot}"
  if blockStateRoot ≠ header.stateRoot then
    .error
      s!"{stateRootTag} : computed state root = {blockStateRoot} ≠ \
         header state root = {header.stateRoot}"
  if receiptRoot ≠ header.receiptRoot then
    .error
      s!"{receiptsRootTag} : computed receipts root = {receiptRoot} ≠ \
         header receipts root = {header.receiptRoot}"
  if blockLogsBloom ≠ header.bloom then
    .error
      s!"{logBloomTag} : computed logs bloom ≠ header logs bloom"
  if withdrawalsRoot ≠ header.withdrawalsRoot then
    .error
      s!"{withdrawalsRootTag} : computed withdrawals root = {withdrawalsRoot} ≠ \
         header withdrawals root = {header.withdrawalsRoot}"
  if bout.blobGasUsed ≠ header.blobGasUsed then
    .error
      s!"{blobGasUsedTag} : computed blob gas used = {bout.blobGasUsed} ≠ \
         header blob gas used = {header.blobGasUsed}"
  if some requestsHash ≠ header.requestsHash then
    .error
      s!"{requestsHashTag} : computed requests hash = {requestsHash} ≠ \
         header requests hash = {header.requestsHash}"

def initBenvStat (rules : ForkRules) (chain : BlockChain) (header : Header) :
    BenvStat :=
  {
    rules := rules,
    chainId := chain.chainId,
    origState := chain.state,
    blockGasLimit := header.gasLimit,
    blockHashes := getLast256BlockHashes chain,
    coinbase := header.coinbase,
    number := header.number,
    baseFeePerGas := header.baseFeePerGas,
    time := header.timestamp.toB256,
    prevRandao := header.prevRandao,
    excessBlobGas := header.excessBlobGas,
    parentBeaconBlockRoot := header.parentBeaconBlockRoot
  }

def initBenv (rules : ForkRules) (chain : BlockChain) (header : Header) : Benv :=
  {
    state := chain.state,
    createdAccounts := .emptyWithCapacity,
    stat := initBenvStat rules chain header
  }

def getTransactionsRoot (bout : BlockOutput) : B256 :=
  let aux (arg : B8L × Tx) : (B8L × B8L) :=
    let txPrefix : B8L :=
      match arg.snd.type with
      | .zero _ _ => []
      | .one _ _ _ _ => [0x01]
      | .two _ _ _ _ _ => [0x02]
      | .three _ _ _ _ _ _ _ => [0x03]
      | .four _ _ _ _ _ _ => [0x04]
    ⟨arg.fst.toB4s, txPrefix ++ arg.snd.toBLT.toB8L⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.transactionsTrie.toList) _

def getReceiptRoot (bout : BlockOutput) : B256 :=
  let aux : (B8L × Fin 5 × Receipt) → (B8L × B8L)
    | ⟨key, type, receipt⟩ => ⟨key.toB4s, type.val.toB8L ++ receipt.toBLT.toB8L⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.receiptsTrie.toList) _

def getWithdrawalsRoot (bout : BlockOutput) : B256 :=
  let aux (arg : B8L × Withdrawal) : B8L × B8L :=
    ⟨arg.fst.toB4s, arg.snd.toBLT.toB8L⟩
  trie <| Std.TreeMap.ofList (List.map aux bout.withdrawalsTrie.toList) _

def stateTransitionOmmersCheck (ommers : List Header) : Except String Unit := do
  if ¬ommers.isEmpty then do
    .error
      s!"{ommersOverParisTag} : block body contains {ommers.length} ommer(s), \
         which is impossible after Paris"

def appendBlock (blks : List Block) (blk : Block) : List Block :=
  (blk :: blks.reverse.take 254).reverse

/-- The block state transition under an explicit rule set.

This is the whole implementation; every other state-transition entry point
below only decides *which* rules to hand it. -/
def stateTransitionWith (rules : ForkRules) (ch : BlockChain) (block : Block) :
  Except String BlockChain := do
  validateHeader rules ch block.header
  stateTransitionOmmersCheck block.ommers
  let benv : Benv := initBenv rules ch block.header
  let ⟨st, bout⟩ ← applyBody benv block.txs block.wds
  let blockStateRoot : B256 := st.root
  let transactionsRoot : B256 := getTransactionsRoot bout
  let receiptRoot : B256 := getReceiptRoot bout
  let blockLogsBloom : B8L := logsBloom bout.blockLogs
  let withdrawalsRoot : B256 := getWithdrawalsRoot bout
  let requestsHash := computeRequestsHash bout.requests
  stateTransitionChecks bout block.header
    transactionsRoot blockStateRoot receiptRoot
    blockLogsBloom withdrawalsRoot requestsHash
  .ok ⟨appendBlock ch.blocks block, st, ch.chainId⟩

/-- The block state transition at an explicitly named fork.

This is the entry point for static fixture suites, which state their fork
rather than deriving it. A fork whose rules this build does not implement
fails here with `UnsupportedForkError`; it never falls back to Prague. -/
def stateTransitionAt (f : Fork) (ch : BlockChain) (block : Block) :
    Except String BlockChain := do
  stateTransitionWith (← f.rules) ch block

/-- The block state transition on a configured chain, deriving the active fork
from the block's timestamp and the chain's activation schedule. -/
def stateTransitionUsing (cfg : ChainConfig) (ch : BlockChain) (block : Block) :
    Except String BlockChain := do
  stateTransitionWith (← cfg.rulesAt block.header.timestamp) ch block

/-- The Prague state transition.

Retained with its original name, type, and behaviour. Prague is permanent
supported protocol, not scaffolding, and downstream proofs state their results
about this name. -/
def stateTransition (ch : BlockChain) (block : Block) :
  Except String BlockChain :=
  stateTransitionWith pragueRules ch block

def BLT.toExStrWithdrawal : BLT → Except String Withdrawal
  | .list [
      .b8s globalIndex,
      .b8s validatorIndex,
      .b8s recipient,
      .b8s amount
    ] => do
    -- Check every untrusted field before constructing the withdrawal. In
    -- particular, `B8L.toB64` truncates modulo 2^64, so it may only see the
    -- byte string returned by the at-most-eight-byte decoder.
    let globalIndex ← globalIndex.toRlpB64 "withdrawal globalIndex"
    let validatorIndex ← validatorIndex.toRlpB64 "withdrawal validatorIndex"
    let recipient ← recipient.toRlpAdr "withdrawal recipient"
    -- EIP-4895: `amount` is a 64-bit Gwei scalar on the wire, even though the
    -- `Withdrawal` field stores it as 256 bits for balance arithmetic.
    let amount ← amount.toRlpB64 "withdrawal amount"
    .ok {
      globalIndex := globalIndex,
      validatorIndex := validatorIndex,
      recipient := recipient,
      amount := amount.toNat.toB256
    }
  | _ =>
    .error <| rlpStructureError "withdrawal"
      "expected a list of four byte-string fields"

def BLT.toExStrTx : BLT → Except String Tx
  | .list [
      .b8s nonce,
      .b8s gasPrice,
      .b8s gas,
      .b8s receiver,
      .b8s value,
      .b8s data,
      .b8s v,
      .b8s r,
      .b8s s
    ] => do
    let nonce ← nonce.toRlpB64 "legacy transaction nonce"
    let gasPrice ← gasPrice.toRlpNat "legacy transaction gasPrice" 32
    let gas ← gas.toRlpNat "legacy transaction gas" 32
    let receiver ← receiver.toRlpReceiver "legacy transaction receiver"
    let value ← value.toRlpNat "legacy transaction value" 32
    let v ← v.toRlpNat "legacy transaction v" 32
    -- Validate signature scalars before sender recovery, but retain their
    -- minimally encoded byte representation so valid legacy signing and
    -- encoding behavior is unchanged.
    let _ ← r.toRlpB256 "legacy transaction r"
    let _ ← s.toRlpB256 "legacy transaction s"
    .ok {
      nonce := nonce,
      gas := gas
      value := value,
      data := data,
      v := v,
      r := r,
      s := s,
      type := .zero gasPrice receiver
    }
  | .list _ =>
    .error <| rlpStructureError "legacy transaction"
      "expected a list of nine byte-string fields"
  | .b8s xs => xs.toExStrTx

def BLT.toExStrBlock : BLT → Except String Block
  | BLT.list [
      HeaderBLT,
      .list TxBLTs,
      .list OmmerBLTs,
      .list WithdrawalBLTs
    ] => do
    let header ← HeaderBLT.toExStrHeader
    let aux : BLT → Except String (B8L ⊕ Tx)
      | blt@(.list _) => blt.toExStrTx <&> .inr
      | .b8s xs => .ok <| .inl xs
    let txs ← List.mapM aux TxBLTs
    let ommers ← List.mapM BLT.toExStrHeader OmmerBLTs
    let withdrawals ← List.mapM BLT.toExStrWithdrawal WithdrawalBLTs
    .ok {
      header := header,
      txs := txs,
      ommers := ommers,
      wds := withdrawals
    }
  | .list [_, .list _, .list _] =>
    .error
      s!"{rlpWithdrawalsNotReadTag} : post-Shanghai block body omits the withdrawals list"
  | _ =>
    .error <| rlpStructureError "block"
      "expected [header, transactions, ommers, withdrawals] lists"

/-
rlpToBlock is equivalent to json_to_block from execution-specs.
why does it accept the RLP bytes as input, and not the whole JSON?
the justification is that json_to_block expects the RLP bytes to be
always available, and always uses *only* the RLP bytes to obtain the
block, ignoring everything else in the JSON (the code path that deals
with nonexistent RLP bytes exists, but is unreachable). its return
type also omits the RLP bytes, since this is identical to the input.
-/
def rlpToBlock (rlp : B8L) : Except String (Block × B256) := do
  let block_blt ← (B8L.toBLT? rlp).toExcept <|
    rlpStructureError "block RLP" "cannot decode the outer RLP item"
  let block ← block_blt.toExStrBlock
  let canonicalRlp := block.toBLT.toB8L
  if rlp ≠ canonicalRlp then
    .error
      s!"{rlpRoundTripTag} : decoded block does not re-encode byte-for-byte"
  .ok ⟨block, (Header.toBLT block.header).toB8L.keccak⟩

--------------- STRICT BLOCK/LEGACY DECODER REGRESSION CHECKS ---------------

private def withdrawalDecoderVector
    (globalIndex validatorIndex recipient amount : B8L) : BLT :=
  .list [.b8s globalIndex, .b8s validatorIndex, .b8s recipient, .b8s amount]

private def legacyDecoderVector
    (nonce gasPrice gas receiver value v r s : B8L) : BLT :=
  .list [
    .b8s nonce, .b8s gasPrice, .b8s gas, .b8s receiver, .b8s value,
    .b8s [], .b8s v, .b8s r, .b8s s
  ]

private def nineByteScalar : B8L := 0x01 :: List.replicate 8 0x00
private def thirtyThreeByteScalar : B8L := 0x01 :: List.replicate 32 0x00
private def testRecipient : B8L := List.replicate 20 0x11

-- Both withdrawal index positions reject nine bytes at the field boundary;
-- neither can reach the truncating `B8L.toB64` conversion unchecked.
#guard hasTag rlpFieldOverflow64Tag <|
  BLT.toExStrWithdrawal <|
    withdrawalDecoderVector nineByteScalar [] testRecipient []
#guard hasTag rlpFieldOverflow64Tag <|
  BLT.toExStrWithdrawal <|
    withdrawalDecoderVector [] nineByteScalar testRecipient []
#guard (BLT.toExStrWithdrawal <|
  withdrawalDecoderVector [] [] testRecipient []).toOption.isSome
#guard hasTag rlpFixedWidthTag <|
  BLT.toExStrWithdrawal <|
    withdrawalDecoderVector [] [] (List.replicate 21 0x11) []
-- The amount is a 64-bit Gwei scalar (EIP-4895): the exact eight-byte maximum
-- decodes, and nine bytes are rejected at the field boundary rather than
-- surfacing later as a state-root mismatch.
#guard (BLT.toExStrWithdrawal <|
  withdrawalDecoderVector [] [] testRecipient (List.replicate 8 0xFF)
  ).toOption.map (fun wd => wd.amount.toNat) = some (2 ^ 64 - 1)
#guard hasTag rlpFieldOverflow64Tag <|
  BLT.toExStrWithdrawal <|
    withdrawalDecoderVector [] [] testRecipient nineByteScalar

-- A canonical legacy transaction preserves its signing/re-encoding bytes.
private def canonicalLegacyVector : BLT :=
  legacyDecoderVector [0x01] [0x02] [0x52, 0x08] testRecipient [] [0x1b] [0x01] [0x02]

#guard
  (BLT.toExStrTx canonicalLegacyVector).toOption.map (fun tx => tx.toBLT.toB8L)
    == some canonicalLegacyVector.toB8L

-- Every legacy scalar is bounded before conversion or sender recovery.
#guard hasTag rlpFieldOverflow64Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector nineByteScalar [] [] [] [] [] [] []
#guard hasTag rlpFieldOverflow256Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] thirtyThreeByteScalar [] [] [] [] [] []
#guard hasTag rlpFieldOverflow256Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] [] thirtyThreeByteScalar [] [] [] [] []
#guard hasTag rlpFieldOverflow256Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] [] [] [] thirtyThreeByteScalar [] [] []
#guard hasTag rlpFieldOverflow256Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] [] [] [] [] thirtyThreeByteScalar [] []
#guard hasTag rlpFieldOverflow256Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] [] [] [] [] [] thirtyThreeByteScalar []
#guard hasTag rlpFieldOverflow256Tag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] [] [] [] [] [] [] thirtyThreeByteScalar
#guard hasTag rlpFixedWidthTag <|
  BLT.toExStrTx <|
    legacyDecoderVector [] [] [] (List.replicate 21 0x11) [] [] [] []

-- The two block-list failures with dedicated meanings are separated before
-- header decoding; arbitrary non-list input remains a structure error.
#guard hasTag rlpWithdrawalsNotReadTag <|
  BLT.toExStrBlock (.list [.b8s [], .list [], .list []])
#guard hasTag rlpStructureTag <| BLT.toExStrBlock (.b8s [])

--------- STRICT TYPED-TRANSACTION DECODER REGRESSION CHECKS ----------

-- A typed transaction is its type byte followed by the RLP encoding of its
-- payload list. Each negative vector below is a one-field mutation of its
-- type's positive vector, so the failing field is unambiguous.

private def typedTxVector (type : B8) (fields : List BLT) : B8L :=
  type :: BLT.toB8L (.list fields)

private def testStorageKey : B8L := List.replicate 32 0x22
private def testBlobHash : B8L := 0x01 :: List.replicate 31 0x33
-- Thirty-two bytes with a nonzero leading byte: a canonical full-width
-- scalar, usable for `r`/`s` at the transaction and authorization level.
private def fullWidthScalar : B8L := 0x01 :: List.replicate 31 0x00

private def accessListOf (adr key : B8L) : BLT :=
  .list [.list [.b8s adr, .list [.b8s key]]]

private def authOf (chainId adr nonce r s : B8L) : BLT :=
  .list [.b8s chainId, .b8s adr, .b8s nonce, .b8s [0x01], .b8s r, .b8s s]

private def type1Vector (chainId nonce receiver r : B8L) (accessList : BLT) : B8L :=
  typedTxVector 0x01 [
    .b8s chainId, .b8s nonce, .b8s [0x0a], .b8s [0x52, 0x08], .b8s receiver,
    .b8s [], .b8s [], accessList, .b8s [0x01], .b8s r, .b8s [0x02]
  ]

private def type2Vector (maxFee receiver s : B8L) : B8L :=
  typedTxVector 0x02 [
    .b8s [0x01], .b8s [0x01], .b8s [0x01], .b8s maxFee, .b8s [0x52, 0x08],
    .b8s receiver, .b8s [], .b8s [], .list [], .b8s [0x01], .b8s [0x01], .b8s s
  ]

private def type3Vector (nonce receiver blobHash : B8L) : B8L :=
  typedTxVector 0x03 [
    .b8s [0x01], .b8s nonce, .b8s [0x01], .b8s [0x0a], .b8s [0x52, 0x08],
    .b8s receiver, .b8s [], .b8s [], .list [], .b8s [0x01],
    .list [.b8s blobHash], .b8s [0x01], .b8s [0x01], .b8s [0x02]
  ]

private def type4Vector (receiver : B8L) (auth : BLT) : B8L :=
  typedTxVector 0x04 [
    .b8s [0x01], .b8s [0x01], .b8s [0x01], .b8s [0x0a], .b8s [0x52, 0x08],
    .b8s receiver, .b8s [], .b8s [], .list [], .list [auth],
    .b8s [0x01], .b8s [0x01], .b8s [0x02]
  ]

private def goodAuth : BLT :=
  authOf [0x01] testRecipient [0x01] fullWidthScalar fullWidthScalar

-- One positive vector per type: it decodes, and it re-encodes to the exact
-- input bytes, so trie bytes for valid transactions are unchanged.
private def reencodes (type : B8) (v : B8L) : Bool :=
  (B8L.toExStrTx v).toOption.map (fun tx => type :: tx.toBLT.toB8L) == some v

#guard reencodes 0x01 <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf testRecipient testStorageKey)
#guard reencodes 0x02 <| type2Vector [0x0a] testRecipient [0x02]
#guard reencodes 0x03 <| type3Vector [0x01] testRecipient testBlobHash
#guard reencodes 0x04 <| type4Vector testRecipient goodAuth

-- An authorization signature scalar below 2^248 encodes canonically in fewer
-- than thirty-two bytes. It must re-encode minimally: a fixed 32-byte
-- re-encoding diverges from the canonical bytes for ~0.8% of valid
-- authorizations, corrupting the type-4 signing hash and transactions trie.
private def shortWidthScalar : B8L := 0x01 :: List.replicate 30 0x00

#guard reencodes 0x04 <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] shortWidthScalar fullWidthScalar
#guard reencodes 0x04 <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] fullWidthScalar shortWidthScalar
#guard reencodes 0x04 <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] [0x01] [0x02]

-- A type-1/type-2 receiver may be empty, meaning contract creation...
#guard (B8L.toExStrTx (type2Vector [0x0a] [] [0x02])).toOption.isSome
-- ...but an empty type-3 receiver is the semantic contract-creation identity;
-- nonempty 19/21-byte receivers still fail as malformed RLP fields.
#guard hasTag type3ContractCreationTag <|
  B8L.toExStrTx <| type3Vector [0x01] [] testBlobHash
#guard hasTag rlpFixedWidthTag <|
  B8L.toExStrTx <| type3Vector [0x01] (List.replicate 19 0x11) testBlobHash
#guard hasTag rlpFixedWidthTag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] (List.replicate 21 0x11) [0x01] (.list [])
#guard hasTag rlpFixedWidthTag <|
  B8L.toExStrTx <| type4Vector (List.replicate 19 0x11) goodAuth

-- Oversized scalars are overflows at the field boundary, not truncations.
#guard hasTag rlpFieldOverflow64Tag <| B8L.toExStrTx <|
  type1Vector [0x01] nineByteScalar testRecipient [0x01] (.list [])
#guard hasTag rlpFieldOverflow64Tag <| B8L.toExStrTx <|
  type1Vector nineByteScalar [0x01] testRecipient [0x01] (.list [])
#guard hasTag rlpFieldOverflow64Tag <|
  B8L.toExStrTx <| type3Vector nineByteScalar testRecipient testBlobHash
#guard hasTag rlpFieldOverflow256Tag <|
  B8L.toExStrTx <| type2Vector thirtyThreeByteScalar testRecipient [0x02]
-- The two fields the deleted `reverse.takeD 32` pattern used to truncate.
#guard hasTag rlpFieldOverflow256Tag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient thirtyThreeByteScalar (.list [])
#guard hasTag rlpFieldOverflow256Tag <|
  B8L.toExStrTx <| type2Vector [0x0a] testRecipient thirtyThreeByteScalar

-- Access lists: exact address and storage-key widths, and both list shapes.
#guard hasTag rlpFixedWidthTag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf (List.replicate 21 0x11) testStorageKey)
#guard hasTag rlpFixedWidthTag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf testRecipient (List.replicate 33 0x22))
#guard hasTag rlpFixedWidthTag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01]
    (accessListOf testRecipient (List.replicate 31 0x22))
#guard hasTag rlpStructureTag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01] (.list [.b8s []])
#guard hasTag rlpStructureTag <| B8L.toExStrTx <|
  type1Vector [0x01] [0x01] testRecipient [0x01] (.b8s [])

-- Blob versioned hashes: exactly thirty-two bytes, both sides.
#guard hasTag rlpFixedWidthTag <| B8L.toExStrTx <|
  type3Vector [0x01] testRecipient (0x01 :: List.replicate 32 0x33)
#guard hasTag rlpFixedWidthTag <|
  B8L.toExStrTx <| type3Vector [0x01] testRecipient (List.replicate 31 0x33)

-- Authorizations: exact address width, a uint256 chainId, bounded nonce and
-- r/s, and the six-field list shape.
#guard hasTag rlpFixedWidthTag <| B8L.toExStrTx <| type4Vector testRecipient <|
  authOf [0x01] (List.replicate 21 0x11) [0x01] fullWidthScalar fullWidthScalar
#guard (B8L.toExStrTx <| type4Vector testRecipient <|
  authOf nineByteScalar testRecipient [0x01] fullWidthScalar fullWidthScalar).toOption.isSome
#guard hasTag rlpFieldOverflow64Tag <| B8L.toExStrTx <| type4Vector testRecipient <|
  authOf [0x01] testRecipient nineByteScalar fullWidthScalar fullWidthScalar
#guard hasTag rlpFieldOverflow256Tag <| B8L.toExStrTx <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] thirtyThreeByteScalar fullWidthScalar
#guard hasTag rlpFieldOverflow256Tag <| B8L.toExStrTx <| type4Vector testRecipient <|
  authOf [0x01] testRecipient [0x01] fullWidthScalar thirtyThreeByteScalar
#guard hasTag rlpStructureTag <| B8L.toExStrTx <|
  type4Vector testRecipient (.list [.b8s [0x01], .b8s testRecipient])

-- A wrong list shape for a known type byte is a structure error; an unknown
-- type byte keeps its own failure; empty input is a structure error.
#guard hasTag rlpStructureTag <| B8L.toExStrTx (0x01 :: BLT.toB8L (.b8s []))
#guard hasTag rlpStructureTag <| B8L.toExStrTx (0x02 :: BLT.toB8L (.list []))
#guard hasTag rlpStructureTag <| B8L.toExStrTx []
#guard ¬ hasTag rlpStructureTag (B8L.toExStrTx [0x05])
#guard (B8L.toExStrTx [0x05]).toOption.isNone

/-- Block import from an already-decoded block, under an explicit rule set.

Split out so that a configured chain can read the block's timestamp to select
its rules without decoding the RLP a second time. The two failure channels are
unchanged: `.error` is a harness-level failure, `.inr` is a block this chain
rejects. -/
private def addBlockToChainCore (rules : ForkRules) (chain : BlockChain)
    (block : Block) (blockHeaderHash : B256) :
    Except String (BlockChain ⊕ String) := do
  cprint "\nSTATE BEFORE TRANSITION :"
  cprint s!"{chain.state}"
  if (Header.toBLT block.header).toB8L.keccak ≠ blockHeaderHash then do
    .error "ERROR : incorrect block header hash"
  let chain ←
    match stateTransitionWith rules chain block with
    | .error err => return (.inr err)
    | .ok chain => .ok chain
  cprint s!"\nSTATE AFTER TRANSITION :"
  cprint s!"{chain.state}"
  .ok (.inl chain)

/-- Block import under an explicit rule set. -/
def addBlockToChainWith (rules : ForkRules) (chain : BlockChain)
    (blockRlp : B8L) : Except String (BlockChain ⊕ String) := do
  let ⟨block, blockHeaderHash⟩ ← rlpToBlock blockRlp
  addBlockToChainCore rules chain block blockHeaderHash

/-- Block import at an explicitly named fork, for static fixture suites.

An unimplemented fork fails on the `.error` channel: it is a limitation of this
build, not a verdict that the block is invalid, and must never be recorded as
one. -/
def addBlockToChainAt (f : Fork) (chain : BlockChain) (blockRlp : B8L) :
    Except String (BlockChain ⊕ String) := do
  addBlockToChainWith (← f.rules) chain blockRlp

/-- Block import on a configured chain, deriving the active fork from the
block's own timestamp and the chain's activation schedule. -/
def addBlockToChainUsing (cfg : ChainConfig) (chain : BlockChain)
    (blockRlp : B8L) : Except String (BlockChain ⊕ String) := do
  let ⟨block, blockHeaderHash⟩ ← rlpToBlock blockRlp
  let rules ← cfg.rulesAt block.header.timestamp
  addBlockToChainCore rules chain block blockHeaderHash

/-- Prague block import.

Retained with its original name, type, and behaviour; downstream proofs state
their results about this name. -/
def addBlockToChain (chain : BlockChain) (blockRlp : B8L) :
  Except String (BlockChain ⊕ String) :=
  addBlockToChainWith pragueRules chain blockRlp

---------------- FORK ARCHITECTURE CHECKS ----------------

-- The Prague entry points are not merely *compatible* with the rules-explicit
-- core at Prague: they are that core, for every input. `rfl` is the point --
-- an equality on sample data would leave room for a wrapper that diverges
-- somewhere else, and downstream proofs state their results about these names.

example (ch : BlockChain) (block : Block) :
    stateTransition ch block = stateTransitionWith pragueRules ch block := rfl

example (ch : BlockChain) (block : Block) :
    stateTransitionAt .prague ch block = stateTransition ch block := rfl

example (chain : BlockChain) (blockRlp : B8L) :
    addBlockToChain chain blockRlp
      = addBlockToChainWith pragueRules chain blockRlp := rfl

example (chain : BlockChain) (blockRlp : B8L) :
    addBlockToChainAt .prague chain blockRlp = addBlockToChain chain blockRlp :=
  rfl

-- A block whose fork this build cannot run is refused, and refused *before*
-- anything is decoded or executed, so an unimplemented fork can never be
-- mistaken for a rule this build actually applied.

private def guardEmptyChain : BlockChain :=
  { blocks := [], state := .empty, chainId := 1 }

private def guardTestHeader : Header := {
  parentHash := 0
  ommersHash := emptyOmmerHash
  coinbase := 0
  stateRoot := 0
  txsRoot := 0
  receiptRoot := 0
  bloom := List.replicate 256 (0 : B8)
  difficulty := 0
  number := 1
  gasLimit := 30000000
  gasUsed := 0
  timestamp := 0
  extraData := []
  prevRandao := 0
  nonce := 0
  baseFeePerGas := 7
  withdrawalsRoot := 0
  blobGasUsed := 0
  excessBlobGas := 0
  parentBeaconBlockRoot := 0
  requestsHash := none
}

private def guardBlockAt (timestamp : Nat) : Block :=
  {
    header := { guardTestHeader with timestamp := timestamp }
    txs := []
    ommers := []
    wds := []
  }

#guard hasTag unsupportedForkTag <|
  stateTransitionAt .bpo1 guardEmptyChain (guardBlockAt 0)
#guard hasTag unsupportedForkTag <|
  stateTransitionAt .bpo2 guardEmptyChain (guardBlockAt 0)

-- Prague and Osaka reach the real checks instead: this chain has no parent
-- block, so the verdict is a header failure, not a missing implementation.
#guard ¬ hasTag unsupportedForkTag
  (stateTransitionAt .prague guardEmptyChain (guardBlockAt 0))
#guard ¬ hasTag unsupportedForkTag
  (stateTransitionAt .osaka guardEmptyChain (guardBlockAt 0))

-- On the block-import API an unsupported fork is a harness failure (`.error`),
-- never a block-rejection verdict (`.ok (.inr _)`): a fork this build has not
-- implemented says nothing about whether the block is valid.
#guard hasTag unsupportedForkTag <| addBlockToChainAt .bpo1 guardEmptyChain []
#guard (addBlockToChainAt .bpo1 guardEmptyChain []).toOption.isNone
#guard errOf (addBlockToChainAt .bpo1 guardEmptyChain [])
  = errOf (addBlockToChainAt .bpo1 guardEmptyChain (List.replicate 64 (0xFF : B8)))

-- A configured chain selects rules from the block's own timestamp. On this
-- schedule the only difference between the two blocks is the timestamp, and it
-- alone decides which rules are applied.

private def guardOsakaAt100 : ChainConfig :=
  ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 100⟩]

private def guardBpo1At100 : ChainConfig :=
  ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.bpo1, 100⟩]

#guard ¬ hasTag unsupportedForkTag
  (stateTransitionUsing guardBpo1At100 guardEmptyChain (guardBlockAt 99))
#guard hasTag unsupportedForkTag <|
  stateTransitionUsing guardBpo1At100 guardEmptyChain (guardBlockAt 100)

-- Both sides of an implemented activation run; neither is refused for want of
-- rules.
#guard ¬ hasTag unsupportedForkTag
  (stateTransitionUsing guardOsakaAt100 guardEmptyChain (guardBlockAt 99))
#guard ¬ hasTag unsupportedForkTag
  (stateTransitionUsing guardOsakaAt100 guardEmptyChain (guardBlockAt 100))

-- A Prague-only configuration is the Prague wrapper, at every timestamp.
#guard errOf (stateTransitionUsing (ChainConfig.pragueOnly 1) guardEmptyChain
    (guardBlockAt 0))
  = errOf (stateTransition guardEmptyChain (guardBlockAt 0))
#guard errOf (stateTransitionUsing (ChainConfig.pragueOnly 1) guardEmptyChain
    (guardBlockAt 999999999))
  = errOf (stateTransition guardEmptyChain (guardBlockAt 999999999))

-- An unusable schedule fails before it selects anything.
#guard hasTag invalidChainConfigTag <|
  stateTransitionUsing (ChainConfig.mk 1 []) guardEmptyChain (guardBlockAt 0)
