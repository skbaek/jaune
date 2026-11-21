import Jaune.Basic

/-!
# A kernel-evaluable twin of the RLP decoder

`Bytes.toBLTDiff?` and `Bytes.toBLTs?` (in `Jaune.Basic`) are a mutual pair
compiled by well-founded recursion: `toBLTs? (k + 1)` calls
`toBLTDiff? (k + 1)` at the same fuel, so neither call is structural. The
kernel cannot unfold `WellFounded.fix`, so `decide +kernel` never evaluates the
public decoder.

This module restates the same pair by structural recursion on the fuel. The
only recursive function is `Bytes.toBLTsS`; one decoding step,
`Bytes.toBLTDiffStep`, takes the list decoder at the smaller fuel as an
argument, exactly as `toBLTDiff? (k + 1)` calls `toBLTs? k`. The bridge
theorems state that the twin equals the public decoder on every input, so a
consumer evaluates a concrete decode with

```
rw [Bytes.toBLT?_eq_toBLTS]; decide +kernel
```

(or `Bytes.toBLTDiff?_eq_toBLTDiffS` / `Bytes.toBLTs?_eq_toBLTsS` at a fuel of
its choice). Nothing here changes the public definitions or their equation
lemmas.
-/

namespace Jaune

/-- Decidable equality of `BLT`, by structural recursion over the nested
inductive, so that the kernel can evaluate it. (The `deriving` handler does not
apply to this nested inductive.) -/
def Rlp.Item.decEq : (a b : Rlp.Item) → Decidable (a = b)
  | .bytes x, .bytes y =>
    if h : x = y then isTrue (h ▸ rfl) else isFalse (fun e => by cases e; exact h rfl)
  | .list xs, .list ys =>
    match Rlp.Item.decEq.decEqList xs ys with
    | isTrue h => isTrue (h ▸ rfl)
    | isFalse h => isFalse (fun e => by cases e; exact h rfl)
  | .bytes _, .list _ => isFalse (fun e => by cases e)
  | .list _, .bytes _ => isFalse (fun e => by cases e)
termination_by structural a => a
where
  /-- Decidable equality of `List BLT`, mutual with `BLT.decEq`. -/
  decEqList : (xs ys : List Rlp.Item) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | x :: xs, y :: ys =>
    match Rlp.Item.decEq x y, Rlp.Item.decEq.decEqList xs ys with
    | isTrue h1, isTrue h2 => isTrue (h1 ▸ h2 ▸ rfl)
    | isFalse h1, _ => isFalse (fun e => by cases e; exact h1 rfl)
    | _, isFalse h2 => isFalse (fun e => by cases e; exact h2 rfl)
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
  termination_by structural xs => xs

instance : DecidableEq Rlp.Item := Rlp.Item.decEq

/-- One step of `Bytes.toBLTDiff?` at fuel `k + 1`, with the list decoder at
fuel `k` passed as `ts`. The body is `Bytes.toBLTDiff?`'s, verbatim. -/
def Bytes.toRlpItemDiffStep (ts : Bytes → Option (List Rlp.Item)) :
    Bytes → Option (Rlp.Item × Bytes)
  | [] => none
  | b :: bs =>
    match Jaune.UInt8.toBits b with
    | ⟨0, _, _, _, _, _, _, _⟩ => some (.bytes [b], bs)
    | ⟨1, 0, 1, 1, 1, _, _, _⟩ => do
      let (lbs, bs') ← List.splitAt? (b - 0xB7).toNat bs
      let (rbs, bs'') ← List.splitAt? (Bytes.toNat lbs) bs'
      return ⟨.bytes rbs, bs''⟩
    | ⟨1, 0, _, _, _, _, _, _⟩ =>
      .map .bytes id <$> List.splitAt? (b - 0x80).toNat bs
    | ⟨1, 1, 1, 1, 1, _, _, _⟩ => do
      let (lbs, bs') ← List.splitAt? (b - 0xF7).toNat bs
      let (rbs, bs'') ← List.splitAt? (Bytes.toNat lbs) bs'
      let rs ← ts rbs
      return ⟨.list rs, bs''⟩
    | ⟨1, 1, _, _, _, _, _, _⟩ => do
      let (rbs, bs') ← List.splitAt? (b - 0xC0).toNat bs
      let rs ← ts rbs
      return ⟨.list rs, bs'⟩

/-- Structural twin of `Bytes.toBLTs?`. -/
def Bytes.toRlpItemsStructural : Nat → Bytes → Option (List Rlp.Item)
  | _, [] => some []
  | 0, _ :: _ => none
  | k + 1, bs@(_ :: _) => do
    let (r, bs') ← Bytes.toRlpItemDiffStep (Bytes.toRlpItemsStructural k) bs
    let rs ← Bytes.toRlpItemsStructural k bs'
    return (r :: rs)

/-- Structural twin of `Bytes.toBLTDiff?`. -/
def Bytes.toRlpItemDiffStructural : Nat → Bytes → Option (Rlp.Item × Bytes)
  | 0, _ => none
  | k + 1, bs => Bytes.toRlpItemDiffStep (Bytes.toRlpItemsStructural k) bs

/-- Structural twin of `Bytes.toBLT?`. -/
def Bytes.toRlpItemStructural (bs : Bytes) : Option Rlp.Item :=
  match Bytes.toRlpItemDiffStructural bs.length bs with
  | some (r, []) => some r
  | _ => none

theorem Bytes.toRlpItemDiff?_succ (k : Nat) (bs : Bytes) :
    Bytes.toRlpItemDiff? (k + 1) bs = Bytes.toRlpItemDiffStep (Bytes.toRlpItems? k) bs := by
  cases bs with
  | nil => simp [Bytes.toRlpItemDiff?, Bytes.toRlpItemDiffStep]
  | cons b bs => rw [Bytes.toRlpItemDiff?]; rfl

private theorem Bytes.toRlpItems?_eq_toRlpItemsStructural_functions :
    ∀ k, Bytes.toRlpItems? k = Bytes.toRlpItemsStructural k := by
  intro k
  induction k with
  | zero =>
    funext bs
    cases bs <;> simp [Bytes.toRlpItems?, Bytes.toRlpItemsStructural]
  | succ k ih =>
    funext bs
    cases bs with
    | nil => simp [Bytes.toRlpItems?, Bytes.toRlpItemsStructural]
    | cons b bs =>
      rw [Bytes.toRlpItems?, Bytes.toRlpItemsStructural, Bytes.toRlpItemDiff?_succ, ih]

/-- The public list decoder equals its structural twin at every fuel. -/
theorem Bytes.toRlpItems?_eq_toRlpItemsStructural (k : Nat) (bs : Bytes) :
    Bytes.toRlpItems? k bs = Bytes.toRlpItemsStructural k bs := by
  rw [Bytes.toRlpItems?_eq_toRlpItemsStructural_functions]

/-- The public item decoder equals its structural twin at every fuel. -/
theorem Bytes.toRlpItemDiff?_eq_toRlpItemDiffStructural (k : Nat) (bs : Bytes) :
    Bytes.toRlpItemDiff? k bs = Bytes.toRlpItemDiffStructural k bs := by
  cases k with
  | zero => cases bs <;> simp [Bytes.toRlpItemDiff?, Bytes.toRlpItemDiffStructural]
  | succ k =>
    rw [Bytes.toRlpItemDiff?_succ, Bytes.toRlpItemDiffStructural, Bytes.toRlpItems?_eq_toRlpItemsStructural_functions]

/-- The public decoder equals its structural twin on every input; rewrite with
this, then `decide +kernel`. -/
theorem Bytes.toRlpItem?_eq_toRlpItemStructural (bs : Bytes) : Bytes.toRlpItem? bs = Bytes.toRlpItemStructural bs := by
  unfold Bytes.toRlpItem? Bytes.toRlpItemStructural
  rw [Bytes.toRlpItemDiff?_eq_toRlpItemDiffStructural]
  rfl

/-! ### The encoder

`Nat.toBytes` recurses on `n / 256` and the `BLT.toBytes` triple on the nested
inductive through a non-structural call (`BLTs.toBytes rs` re-reads `rs`), so
both are compiled by well-founded recursion and neither reduces in the kernel.
The twins below are structural (`Nat.toBytesS` on a fuel equal to the input),
and `BLT.toBytes_eq_toBytesS` lets a consumer write
`rw [BLT.toBytes_eq_toBytesS]; decide +kernel`. -/

/-- Structural twin of `Nat.toBytes.aux`, with a fuel argument first. -/
def Nat.toBytesStructural.go : Nat → Bytes → Nat → Bytes
  | 0, acc, _ => acc
  | _ + 1, acc, 0 => acc
  | f + 1, acc, n@(_ + 1) => Nat.toBytesStructural.go f ((n % 256).toUInt8 :: acc) (n / 256)

/-- Structural twin of `Nat.toBytes`: the fuel is the input itself. -/
def Nat.toBytesStructural (n : Nat) : Bytes := Nat.toBytesStructural.go n [] n

private theorem Nat.toBytesStructural.go_eq :
    ∀ (f : Nat) (acc : Bytes) (n : Nat), n ≤ f →
      Nat.toBytesStructural.go f acc n = Nat.toBytes.go acc n := by
  intro f
  induction f with
  | zero =>
    intro acc n h
    have : n = 0 := by omega
    subst this
    simp [Nat.toBytesStructural.go, Nat.toBytes.go]
  | succ f ih =>
    intro acc n h
    cases n with
    | zero => simp [Nat.toBytesStructural.go, Nat.toBytes.go]
    | succ m =>
      rw [Nat.toBytesStructural.go, Nat.toBytes.go, ih _ _ (by omega)]

/-- `Nat.toBytes` equals its structural twin. -/
theorem Nat.toBytes_eq_toBytesStructural (n : Nat) : Nat.toBytes n = Nat.toBytesStructural n := by
  unfold Nat.toBytes Nat.toBytesStructural
  rw [Nat.toBytesStructural.go_eq _ _ _ (Nat.le_refl n)]

/-- `Nat.toBytesPack` through the structural `Nat.toBytesS`. -/
def Nat.toBytesPackStructural : Nat → Bytes
  | 0 => [0]
  | n@(_ + 1) => Nat.toBytesStructural n

theorem Nat.toBytesPack_eq_toBytesPackStructural (n : Nat) :
    Nat.toBytesPack n = Nat.toBytesPackStructural n := by
  cases n with
  | zero => rfl
  | succ m => rw [Nat.toBytesPack, Nat.toBytesPackStructural, Nat.toBytes_eq_toBytesStructural]

/-- The byte-string branch of `BLT.toBytes`, through `Nat.toBytesPackS`. -/
def Rlp.Item.bytesToBytesStructural : Bytes → Bytes
  | [b] => if b < (0x80) then [b] else [0x81, b]
  | bs =>
    if bs.length < 56
    then (0x80 + bs.length.toUInt8) :: bs
    else let lbs : Bytes := Nat.toBytesPackStructural bs.length
         (0xB7 + lbs.length.toUInt8) :: (lbs ++ bs)

/-- The list header `BLTs.toBytes` puts before a joined payload, through
`Nat.toBytesPackS`. -/
def Rlp.Items.wrapStructural (bs : Bytes) : Bytes :=
  let len := bs.length
  if len < 56
  then (0xC0 + len.toUInt8) :: bs
  else let lbs : Bytes := Nat.toBytesPackStructural len
       (0xF7 + lbs.length.toUInt8) :: (lbs ++ bs)

mutual

  /-- Structural twin of `BLT.toBytes`. -/
  def Rlp.Item.toBytesStructural : Rlp.Item → Bytes
    | .bytes bs => Rlp.Item.bytesToBytesStructural bs
    | .list rs => Rlp.Items.wrapStructural (Rlp.Items.toBytesJoinStructural rs)

  /-- Structural twin of `BLTs.toBytesJoin`. -/
  def Rlp.Items.toBytesJoinStructural : List Rlp.Item → Bytes
    | [] => []
    | r :: rs => Rlp.Item.toBytesStructural r ++ Rlp.Items.toBytesJoinStructural rs

end

/-- Structural twin of `BLTs.toBytes`. -/
def Rlp.Items.toBytesStructural (rs : List Rlp.Item) : Bytes := Rlp.Items.wrapStructural (Rlp.Items.toBytesJoinStructural rs)

theorem Rlp.Item.toBytes_bytes_eq_bytesToBytesStructural (bs : Bytes) :
    Rlp.Item.toBytes (.bytes bs) = Rlp.Item.bytesToBytesStructural bs := by
  match bs with
  | [b] => simp [Rlp.Item.toBytes, Rlp.Item.bytesToBytesStructural]
  | [] => simp [Rlp.Item.toBytes, Rlp.Item.bytesToBytesStructural]
  | b :: c :: bs =>
    simp only [Rlp.Item.toBytes, Rlp.Item.bytesToBytesStructural, Nat.toBytesPack_eq_toBytesPackStructural]

theorem Rlp.Items.toBytes_eq_wrapStructural (rs : List Rlp.Item) :
    Rlp.Items.toBytes rs = Rlp.Items.wrapStructural (Rlp.Items.toBytesJoin rs) := by
  simp only [Rlp.Items.toBytes, Rlp.Items.wrapStructural, Nat.toBytesPack_eq_toBytesPackStructural]

mutual

  /-- The public encoder equals its structural twin; rewrite with this, then
  `decide +kernel`. -/
  theorem Rlp.Item.toBytes_eq_toBytesStructural : (r : Rlp.Item) → Rlp.Item.toBytes r = Rlp.Item.toBytesStructural r
    | .bytes bs => by rw [Rlp.Item.toBytes_bytes_eq_bytesToBytesStructural, Rlp.Item.toBytesStructural]
    | .list rs => by
      rw [Rlp.Item.toBytes, Rlp.Items.toBytes_eq_wrapStructural, Rlp.Items.toBytesJoin_eq_toBytesJoinStructural rs, Rlp.Item.toBytesStructural]

  theorem Rlp.Items.toBytesJoin_eq_toBytesJoinStructural :
      (rs : List Rlp.Item) → Rlp.Items.toBytesJoin rs = Rlp.Items.toBytesJoinStructural rs
    | [] => by rw [Rlp.Items.toBytesJoin, Rlp.Items.toBytesJoinStructural]
    | r :: rs => by
      rw [Rlp.Items.toBytesJoin, Rlp.Items.toBytesJoinStructural, Rlp.Item.toBytes_eq_toBytesStructural r,
        Rlp.Items.toBytesJoin_eq_toBytesJoinStructural rs]

end

theorem Rlp.Items.toBytes_eq_toBytesStructural (rs : List Rlp.Item) : Rlp.Items.toBytes rs = Rlp.Items.toBytesStructural rs := by
  rw [Rlp.Items.toBytes_eq_wrapStructural, Rlp.Items.toBytesJoin_eq_toBytesJoinStructural, Rlp.Items.toBytesStructural]

end Jaune
