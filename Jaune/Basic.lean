-- Basic.lean : generic definitions and lemmas (e.g. for Booleans, lists,
-- bit vectors and bytes) that are useful for but not specific to Blanc

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Data.List.TakeDrop
-- `List.length_dropWhile_le` (used in `EC.lean`) reached us transitively from
-- another `Mathlib.Data.List` module before mathlib v4.32.1; import it directly.
import Mathlib.Data.List.TakeWhile
import Mathlib.Data.UInt
import Mathlib.Tactic.NormNum

namespace Jaune

open Jaune _root_.List _root_.Nat

instance : @Zero Bool := ⟨false⟩
instance : @One Bool := ⟨true⟩

abbrev Bytes : Type := List UInt8

instance : LinearOrder UInt8 where
  lt_iff_le_not_ge a b := Nat.lt_iff_le_and_not_ge
  le_refl a := Nat.le_refl _
  le_trans a b c h1 h2 := Nat.le_trans h1 h2
  le_antisymm a b h1 h2 := by
    rw [← UInt8.toNat_inj]
    apply Nat.le_antisymm h1 h2
  le_total a b := Nat.le_total (a.toNat) (b.toNat)
  toDecidableLE := λ a b => Nat.decLe _ _

instance : LinearOrder UInt16 where
  lt_iff_le_not_ge a b := Nat.lt_iff_le_and_not_ge
  le_refl a := Nat.le_refl _
  le_trans a b c h1 h2 := Nat.le_trans h1 h2
  le_antisymm a b h1 h2 := by
    rw [← UInt16.toNat_inj]
    apply Nat.le_antisymm h1 h2
  le_total a b := Nat.le_total (a.toNat) (b.toNat)
  toDecidableLE := λ a b => Nat.decLe _ _

instance : LinearOrder UInt32 where
  lt_iff_le_not_ge a b := Nat.lt_iff_le_and_not_ge
  le_refl a := Nat.le_refl _
  le_trans a b c h1 h2 := Nat.le_trans h1 h2
  le_antisymm a b h1 h2 := by
    rw [← UInt32.toNat_inj]
    apply Nat.le_antisymm h1 h2
  le_total a b := Nat.le_total (a.toNat) (b.toNat)
  toDecidableLE := λ a b => Nat.decLe _ _

instance : LinearOrder UInt64 where
  lt_iff_le_not_ge a b := Nat.lt_iff_le_and_not_ge
  le_refl a := Nat.le_refl _
  le_trans a b c h1 h2 := Nat.le_trans h1 h2
  le_antisymm a b h1 h2 := by
    rw [← UInt64.toNat_inj]
    apply Nat.le_antisymm h1 h2
  le_total a b := Nat.le_total (a.toNat) (b.toNat)
  toDecidableLE := λ a b => Nat.decLe _ _

def UInt8.highBit (x : UInt8) : Bool := (x &&& 0x80) != 0
def UInt8.lowBit (x : UInt8) : Bool := (x &&& 0x01) != 0

def UInt16.highBit (x : UInt16) : Bool := (x &&& 0x8000) != 0
def UInt16.lowBit  (x : UInt16) : Bool := (x &&& 0x0001) != 0

def UInt32.highBit (x : UInt32) : Bool := (x &&& 0x80000000) != 0
def UInt32.lowBit  (x : UInt32) : Bool := (x &&& 0x00000001) != 0

def UInt64.highBit (x : UInt64) : Bool := (x &&& 0x8000000000000000) != 0
def UInt64.lowBit  (x : UInt64) : Bool := (x &&& 0x0000000000000001) != 0

def U128 : Type := UInt64 × UInt64
deriving DecidableEq

instance : Inhabited U128 := ⟨⟨0, 0⟩⟩

def U256 : Type := BitVec 256

instance : DecidableEq U256 := inferInstanceAs (DecidableEq (BitVec 256))

private abbrev U256.asBV (x : U256) : BitVec 256 := x
private abbrev U256.ofBV (v : BitVec 256) : U256 := v

def U256.toNat (x : U256) : Nat := BitVec.toNat x
def Nat.toU256 (n : Nat) : U256 := BitVec.ofNat 256 n

instance {n} : OfNat U256 n := ⟨n.toU256⟩

def U256.zero : U256 := BitVec.ofNat 256 0
instance : Zero U256 := ⟨.zero⟩
def U256.one : U256 := BitVec.ofNat 256 1
instance : One U256 := ⟨.one⟩

instance : Inhabited U256 := ⟨0⟩

def U128.highBit (x : U128) : Bool := x.1.highBit
def U128.lowBit  (x : U128) : Bool := x.2.lowBit

def U256.highBit (x : U256) : Bool := (U256.asBV x).msb
def U256.lowBit  (x : U256) : Bool := (x.toNat &&& 1) != 0

def UInt64.max : UInt64 := 0xFFFFFFFFFFFFFFFF
def U128.max : U128 := ⟨.max, .max⟩
def U256.max : U256 := BitVec.allOnes 256

def U128.LT (x y : U128) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)
instance : @LT U128 := ⟨U128.LT⟩
instance {x y : U128} : Decidable (x < y) := instDecidableOr

instance : LT U256 := inferInstanceAs (LT (BitVec 256))
instance {x y : U256} : Decidable (x < y) := inferInstanceAs (Decidable ((U256.asBV x) < (U256.asBV y)))

def Nat.toU128 (n : Nat) : U128 :=
  ⟨(n >>> 64).toUInt64, n.toUInt64⟩

instance {n} : OfNat U128 n := ⟨n.toU128⟩

theorem U256.kernel_decidable_comparisons :
    ((0x06fdde03 : U256) < (0x095ea7b3 : U256)) ∧
    ((0x095ea7b3 : U256) = (0x095ea7b3 : U256)) ∧
    ¬ ((0x095ea7b3 : U256) < (0x06fdde03 : U256)) := by
  decide +kernel

def UInt8.toHexit : UInt8 → Char
  | 0x0 => '0'
  | 0x1 => '1'
  | 0x2 => '2'
  | 0x3 => '3'
  | 0x4 => '4'
  | 0x5 => '5'
  | 0x6 => '6'
  | 0x7 => '7'
  | 0x8 => '8'
  | 0x9 => '9'
  | 0xA => 'a' -- 'A'
  | 0xB => 'b' -- 'B'
  | 0xC => 'c' -- 'C'
  | 0xD => 'd' -- 'D'
  | 0xE => 'e' -- 'E'
  | 0xF => 'f' -- 'F'
  | _   => 'x' -- 'X'

def UInt8.highs (x : UInt8) : UInt8 := (x >>> 4)
def UInt8.lows (x : UInt8) : UInt8 := (x &&& 0x0F)

def UInt8.toHex (x : UInt8) : String :=
  String.ofList [x.highs.toHexit, x.lows.toHexit]

def Bytes.toHex (bs : Bytes) : String :=
  List.foldr (λ b s => UInt8.toHex b ++ s) "" bs

def UInt16.highs (x : UInt16) : UInt8 := (x >>> 8).toUInt8
def UInt16.lows : UInt16 → UInt8 := UInt16.toUInt8
def UInt16.toHex (x : UInt16) : String := x.highs.toHex ++ x.lows.toHex

def UInt32.highs (x : UInt32) : UInt16 := (x >>> 16).toUInt16
def UInt32.lows : UInt32 → UInt16 := UInt32.toUInt16
def UInt32.toHex (x : UInt32) : String := x.highs.toHex ++ x.lows.toHex

def UInt64.highs (x : UInt64) : UInt32 := (x >>> 32).toUInt32
def UInt64.lows : UInt64 → UInt32 := UInt64.toUInt32
def UInt64.toHex (x : UInt64) : String := x.highs.toHex ++ x.lows.toHex

def U256.toBytes.go : Nat → Nat → Bytes → Bytes
  | 0, _, acc => acc
  | k + 1, n, acc => U256.toBytes.go k (n >>> 8) (n.toUInt8 :: acc)

def U256.toBytes (x : U256) : Bytes := U256.toBytes.go 32 x.toNat []

def U128.toHex (x : U128) : String := x.1.toHex ++ x.2.toHex
def U256.toHex (x : U256) : String := Bytes.toHex x.toBytes

instance : ToString UInt8 := ⟨UInt8.toHex⟩
instance : ToString UInt16 := ⟨UInt16.toHex⟩
instance : ToString UInt32 := ⟨UInt32.toHex⟩
instance : ToString UInt64 := ⟨UInt64.toHex⟩
instance : ToString U128 := ⟨U128.toHex⟩
instance : ToString U256 := ⟨U256.toHex⟩

def U128.LE (x y : U128) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
instance : @LE U128 := ⟨U128.LE⟩
instance {x y : U128} : Decidable (x ≤ y) := instDecidableOr

instance : LE U256 := inferInstanceAs (LE (BitVec 256))
instance {x y : U256} : Decidable (x ≤ y) := inferInstanceAs (Decidable ((U256.asBV x) ≤ (U256.asBV y)))

def U128.shiftLeft : U128 → Nat → U128
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else if os < 64
         then ⟨ (xs <<< os.toUInt64) ||| (ys >>> (64 - os).toUInt64),
                ys <<< os.toUInt64 ⟩
         else if os < 128
              then ⟨ys <<< (os - 64).toUInt64, 0⟩
              else ⟨0, 0⟩
instance : HShiftLeft U128 Nat U128 := ⟨U128.shiftLeft⟩

def U128.shiftRight : U128 → Nat → U128
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else if os < 64
         then ⟨ xs >>> os.toUInt64,
                (xs <<< (64 - os).toUInt64) ||| (ys >>> os.toUInt64) ⟩
         else if os < 128
              then ⟨0, xs >>> (os - 64).toUInt64⟩
              else ⟨0, 0⟩
instance : HShiftRight U128 Nat U128 := ⟨U128.shiftRight⟩

def U128.or : U128 → U128 → U128
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ||| yh, xl ||| yl⟩
instance : HOr U128 U128 U128 := ⟨U128.or⟩

def U128.and : U128 → U128 → U128
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh &&& yh, xl &&& yl⟩
instance : HAnd U128 U128 U128 := ⟨U128.and⟩

def U256.or (x y : U256) : U256 := (U256.asBV x) ||| (U256.asBV y)
instance : HOr U256 U256 U256 := ⟨U256.or⟩
def U256.and (x y : U256) : U256 := (U256.asBV x) &&& (U256.asBV y)
instance : HAnd U256 U256 U256 := ⟨U256.and⟩

def U128.xor : U128 → U128 → U128
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ^^^ yh, xl ^^^ yl⟩
instance : HXor U128 U128 U128 := ⟨U128.xor⟩
def U256.xor (x y : U256) : U256 := (U256.asBV x) ^^^ (U256.asBV y)
instance : HXor U256 U256 U256 := ⟨U256.xor⟩

def U256.shiftRight (x : U256) (n : Nat) : U256 :=
  if n < 256 then BitVec.ushiftRight x n else 0
instance : HShiftRight U256 Nat U256 := ⟨U256.shiftRight⟩

def U256.shiftLeft (x : U256) (n : Nat) : U256 :=
  if n < 256 then BitVec.shiftLeft x n else 0
instance : HShiftLeft U256 Nat U256 := ⟨U256.shiftLeft⟩

def U256.isNeg : U256 → Bool := U256.highBit

def U256.arithShiftRight (xs : U256) (os : Nat) : U256 :=
  BitVec.sshiftRight xs (min os 256)

def U256.SignedLt (xs ys : U256) : Prop := (U256.asBV xs).slt (U256.asBV ys) = true
instance {xs ys : U256} : Decidable (U256.SignedLt xs ys) := inferInstanceAs (Decidable ((U256.asBV xs).slt (U256.asBV ys) = true))

def U256.SignedGt (xs ys : U256) : Prop := U256.SignedLt ys xs
instance {xs ys : U256} : Decidable (U256.SignedGt xs ys) := inferInstanceAs (Decidable (U256.SignedLt ys xs))

def U128.complement : U128 → U128
  | ⟨xs, ys⟩ => ⟨~~~ xs, ~~~ ys⟩
instance : Complement U128 := ⟨U128.complement⟩

def U256.complement (x : U256) : U256 := BitVec.xor x (BitVec.allOnes 256)
instance : Complement U256 := ⟨U256.complement⟩

def UInt8.toU256  (x : UInt8)  : U256 := BitVec.ofNat 256 x.toNat
def UInt16.toU256 (x : UInt16) : U256 := BitVec.ofNat 256 x.toNat
def UInt32.toU256 (x : UInt32) : U256 := BitVec.ofNat 256 x.toNat
def UInt64.toU256 (x : UInt64) : U256 := BitVec.ofNat 256 x.toNat

def U128.zero : U128 := ⟨0, 0⟩
instance : Zero U128 := ⟨.zero⟩
def U128.one : U128 := ⟨0, 1⟩
instance : One U128 := ⟨.one⟩

def U128.sub (x y : U128) : U128 :=
  let l := x.2 - y.2
  let c : UInt64 := if x.2 < y.2 then 1 else 0
  ⟨(x.1 - y.1) - c, l⟩
instance : HSub U128 U128 U128 := ⟨U128.sub⟩

def U128.add (x y : U128) : U128 :=
  let l := x.2 + y.2
  let c : UInt64 := if l < x.2 then 1 else 0
  ⟨x.1 + y.1 + c, l⟩
instance : HAdd U128 U128 U128 := ⟨U128.add⟩

def U256.add (x y : U256) : U256 := (U256.asBV x) + (U256.asBV y)
instance : HAdd U256 U256 U256 := ⟨U256.add⟩

def U256.sub (x y : U256) : U256 := (U256.asBV x) - (U256.asBV y)
instance : HSub U256 U256 U256 := ⟨U256.sub⟩
instance : Sub U256 := ⟨U256.sub⟩

def U256.neg (xs : U256) : U256 := - (U256.asBV xs)

-- minimum possible value in 2's complement
def UInt64.signedMin : UInt64 := 0x8000000000000000
def U128.signedMin : U128 := ⟨.signedMin, 0⟩
def U256.signedMin : U256 := BitVec.intMin 256

def UInt64.negOne  : UInt64  := .max
def U128.negOne : U128 := .max
def U256.negOne : U256 := BitVec.allOnes 256

def Nat.toBool : Nat → Bool
  | 0 => 0
  | _ => 1

def UInt16.toBytes (x : UInt16) : Bytes :=
  [(x >>> 8).toUInt8, x.toUInt8]

def UInt32.toBytes (x : UInt32) : Bytes :=
  UInt16.toBytes (x >>> 16).toUInt16 ++ UInt16.toBytes x.toUInt16

def UInt64.toBytes (x : UInt64) : Bytes :=
  UInt32.toBytes (x >>> 32).toUInt32 ++ UInt32.toBytes x.toUInt32

def UInt64.byteswap (w : UInt64) : UInt64 :=
  ((w <<< 56) &&& (0xFF00000000000000 : UInt64)) |||
  ((w <<< 40) &&& (0x00FF000000000000 : UInt64)) |||
  ((w <<< 24) &&& (0x0000FF0000000000 : UInt64)) |||
  ((w <<< 8)  &&& (0x000000FF00000000 : UInt64)) |||
  ((w >>> 8)  &&& (0x00000000FF000000 : UInt64)) |||
  ((w >>> 24) &&& (0x0000000000FF0000 : UInt64)) |||
  ((w >>> 40) &&& (0x000000000000FF00 : UInt64)) |||
  ((w >>> 56) &&& (0x00000000000000FF : UInt64))

def U128.toBytes (x : U128) : Bytes := x.1.toBytes ++ x.2.toBytes

def List.ekat {ξ : Type u} (n : Nat) (xs : List ξ) : List ξ :=
  (xs.reverse.take n).reverse

def List.takeRightD {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) : List ξ :=
  (xs.reverse.takeD n x).reverse

theorem List.length_takeRightD {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) :
    (List.takeRightD n xs x).length = n := by
  simp [List.takeRightD]

/-- `List.takeRightD` carrying its width in the type: exactly `n` entries, the
last `n` of `xs`, left-padded with `x` when `xs` is shorter.

This is the reader for a fixed-width vector held as a list whose leading zeros
have been trimmed — a coefficient of a field extension, say. A missing leading
entry there is a zero, not an absent one, so padding on the left is the
arithmetically correct completion rather than a defensive default, and the
width being a type rules out reading past the end of a short list. -/
def List.takeRightV {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) : Vector ξ n :=
  ⟨(List.takeRightD n xs x).toArray, by simp [List.length_takeRightD]⟩

@[simp] theorem List.takeRightV_toList {ξ : Type u}
    (n : Nat) (xs : List ξ) (x : ξ) :
    (List.takeRightV n xs x).toList = List.takeRightD n xs x := rfl

def Bytes.pack (xs : Bytes) (n : Nat) : Bytes := List.takeRightD n xs 0

/-- `Bytes.pack` with its width in the type. -/
def Bytes.packV (xs : Bytes) (n : Nat) : Vector UInt8 n := List.takeRightV n xs 0

@[simp] theorem Bytes.packV_toList (xs : Bytes) (n : Nat) :
    (Bytes.packV xs n).toList = Bytes.pack xs n := rfl

theorem Bytes.getElem_packV (xs : Bytes) (n i : Nat) (h : i < n) :
    (Bytes.packV xs n)[i] = (Bytes.pack xs n).getD i 0 := by
  have hlen : i < (List.takeRightD n xs 0).length := by
    rw [List.length_takeRightD]; exact h
  simp [Bytes.packV, Bytes.pack, List.takeRightV,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]

def U128.toNat (x : U128) : Nat := (x.1.toNat <<< 64) ||| x.2.toNat

def U256.addmod (x y z : U256) : U256 :=
  if z = 0
  then 0
  else ((x.toNat + y.toNat) % z.toNat).toU256 -- (x + y) % z

def U256.mulmod (x y z : U256) : U256 :=
  if z = 0
  then 0
  else ((x.toNat * y.toNat) % z.toNat).toU256 -- (x + y) % z

def U256.signext (x y : U256) : U256 :=
  if x.toNat < 31 then
    ((U256.asBV y).setWidth (8 * (x.toNat + 1))).signExtend 256
  else y

instance {ξ : Type u} {ρ : ξ → Prop} {xs : List ξ}
    [d : ∀ x : ξ, Decidable (ρ x)] : Decidable (xs.Forall ρ) := by
  induction xs with
  | nil => apply instDecidableTrue
  | cons x xs ih => simp; apply instDecidableAnd

-- Option helpers, used by the partial list operations below.

lemma of_bind_eq_some {ξ υ} {f : Option ξ} {g : ξ → Option υ} {y} :
    f >>= g = some y → ∃ x, f = some x ∧ g x = some y := by
  intro h; cases f with
  | none => cases h
  | some x => refine ⟨x, rfl, h⟩

lemma of_pure_eq_some {ξ} {x y : ξ} : pure x = some y → x = y := by intro h; cases h; rfl

lemma of_guard_eq_some {p : Prop} [hd : Decidable p] {ξ} {ox : Option ξ} {x} :
    (do guard p; ox) = some x → p ∧ ox = some x := by
  intro h
  cases em p with
  | inl hp => simp [hp] at h; constructor <;> assumption
  | inr hp => simp [guard, ite_eq_right hp] at h

def List.drop? {ξ : Type u} : Nat → List ξ → Option (List ξ)
  | 0, xs => some xs
  | _ + 1, [] => none
  | n + 1, _ :: xs => drop? n xs

def List.take? {ξ : Type u} : Nat → List ξ → Option (List ξ)
  | 0, _ => some []
  | _ + 1, [] => none
  | n + 1, x :: xs => (x :: ·) <$> take? n xs

def List.slice? {ξ : Type u} (xs : List ξ) (m n : Nat) : Option (List ξ) :=
  drop? m xs >>= take? n

def List.sliceD {ξ : Type u} (xs : List ξ) (m n : Nat) (x : ξ) : List ξ :=
  takeD n (drop m xs) x

def List.slice! {ξ : Type u} [Inhabited ξ] (xs : List ξ) (m n : Nat) : List ξ :=
  takeD n (drop m xs) default

-- Lemma API for the partial list operations above.

theorem List.drop?_add {ξ : Type u} (m n : Nat) (xs : List ξ) :
    drop? (m + n) xs = drop? n xs >>= drop? m := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs <;> simp only [drop?]
    · rfl
    · apply ih

theorem List.get?_eq_drop?_head? {ξ : Type u} {xs : List ξ} {n : Nat} :
    xs[n]? = drop? n xs >>= List.head? := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [drop?]
  | succ n ih =>
    cases xs
    · simp [drop?]
    · simp [drop?]; apply ih

def List.Slice {ξ : Type u} (xs : List ξ) (m : Nat) (ys : List ξ) : Prop :=
  ∃ n, xs.slice? m n = some ys

theorem List.slice?_cons {ξ : Type u} (x) (xs : List ξ) (m n : Nat) :
    slice? (x :: xs) (m + 1) n = slice? xs m n := rfl

theorem List.slice?_eq_cons_iff {ξ : Type u} {xs : List ξ} {m n : Nat} {y} {ys} :
    slice? xs m (n + 1) = some (y :: ys) ↔
      (xs[m]? = some y ∧ slice? xs (m + 1) n = some ys) := by
  induction m generalizing xs with
  | zero =>
    match xs with
    | [] => simp [slice?, drop?, Bind.bind, Option.bind, take?]
    | x :: xs =>
      simp only
        [slice?, drop?, Bind.bind, Option.bind, take?]
      cases take? n xs <;> simp
  | succ m ih =>
    match xs with
    | [] => simp [slice?, drop?, Bind.bind, Option.bind]
    | x :: xs =>
      rw [List.slice?_cons, ih]; rfl

theorem List.slice_cons_iff {ξ : Type u} {xs : List ξ} {m : Nat} {y} {ys} :
    List.Slice xs m (y :: ys) ↔
      (xs[m]? = some y ∧ List.Slice xs (m + 1) ys) := by
  simp only [Slice]
  constructor <;> intro h
  · rcases h with ⟨_ | n, h⟩
    · revert h; unfold slice?
      cases xs.drop? m with
      | none => simp
      | some xs' => simp [take?]
    · rw [slice?_eq_cons_iff] at h
      refine' ⟨h.left, _, h.right⟩
  · rcases h with ⟨h, n, h'⟩
    refine ⟨_, slice?_eq_cons_iff.mpr ⟨h, h'⟩⟩

theorem List.length_take? {ξ : Type u} {n : Nat} {xs ys : List ξ} :
    take? n xs = some ys → n = ys.length := by
  induction n generalizing xs ys with
  | zero => simp [take?]; intro h; simp [h]
  | succ n ih =>
    cases xs <;> simp [take?]
    intro ys' h h'; rw [ih h, ← h']; rfl

theorem List.length_slice? {ξ : Type u} {xs} {m n : Nat} {ys : List ξ} :
    slice? xs m n = some ys → n = ys.length := by
  unfold slice?; cases xs.drop? m <;> simp; apply length_take?

theorem List.get?_eq_of_slice {ξ : Type u} {xs : List ξ} {m : Nat} {y} {ys} :
    Slice xs m (y :: ys) → xs[m]? = some y := by
  rw [List.slice_cons_iff]; apply And.left

theorem List.of_take?_eq_append {ξ : Type u} {xs : List ξ}
    {n : Nat} {ys zs : List ξ} (h : take? n xs = some (ys ++ zs)) :
    take? ys.length xs = some ys ∧ xs.slice? ys.length zs.length = some zs := by
  induction ys generalizing n xs with
  | nil => simp [slice?, drop?] at *; rw [← length_take? h]; refine' ⟨rfl, h⟩
  | cons y ys ih =>
    cases n <;> simp [take?] at h
    cases xs <;> simp [take?] at h
    rcases h with ⟨h, ⟨_⟩⟩; constructor
    · rw [List.length_cons]; unfold take?; rw [(ih h).left]; rfl
    · apply (ih h).right

theorem List.of_slice?_eq_append {ξ : Type u} {xs : List ξ}
    {m n : Nat} {ys zs} (h : slice? xs m n = some (ys ++ zs)) :
    slice? xs m ys.length = some ys ∧
    slice? xs (m + ys.length) zs.length = some zs := by
  revert h; unfold slice?; rw [Nat.add_comm, drop?_add]
  cases xs.drop? m <;> simp; rename List ξ => xs'; apply of_take?_eq_append

theorem List.slice_prefix {ξ : Type u} {xs : List ξ}
    {m : Nat} {ys zs} (h : Slice xs m (ys ++ zs)) : Slice xs m ys := by
  rcases h with ⟨n, h⟩; refine ⟨_, (of_slice?_eq_append h).left⟩

theorem List.slice_suffix {ξ : Type u} {xs : List ξ} {m : Nat} {ys zs}
    (h : Slice xs m (ys ++ zs)) : Slice xs (m + ys.length) zs := by
  rcases h with ⟨n, h⟩; refine ⟨_, (of_slice?_eq_append h).right⟩

theorem List.get?_length_ne_some {ξ : Type y} {xs : List ξ} {y} :
    xs[xs.length]? ≠ some y := by simp

theorem List.take?_length {ξ : Type u} (xs : List ξ) :
    take? xs.length xs = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [take?, ih]

theorem List.slice_refl {ξ : Type u} (xs : List ξ) : List.Slice xs 0 xs := by
  refine' ⟨xs.length, _⟩; simp [slice?, drop?, take?_length]

theorem List.append_slice_suffix {ξ : Type y} {xs ys : List ξ} :
    Slice (xs ++ ys) xs.length ys := by
  have h := slice_suffix <| slice_refl <| xs ++ ys
  rw [Nat.zero_add] at h; exact h

lemma List.sliceD_succ {ξ} (xs : List ξ) (m n : Nat) (d : ξ) :
    xs.sliceD m (n + 1) d = xs.getD m d :: xs.sliceD (m + 1) n d := by
  cases m <;> cases xs <;> simp [List.sliceD, takeD, List.getD, List.drop]

lemma List.getD_eq_default {ξ} {xs : List ξ} {i : Nat} {d : ξ}
    (le : xs.length ≤ i) : xs.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none_iff.mpr le]; rfl

lemma List.drop_eq_of_drop?_eq_some {ξ} {xs ys : List ξ} {m : Nat} :
    xs.drop? m = some ys → xs.drop m = ys := by
  induction m generalizing xs ys
  case zero => simp [List.drop?]
  case succ m ih => cases xs <;> simp [List.drop?]; apply ih

lemma List.takeD_eq_of_take?_eq_some {ξ} {xs ys : List ξ} {m : Nat} {d} :
    xs.take? m = some ys → xs.takeD m d = ys := by
  induction m generalizing xs ys
  case zero => simp [List.take?]
  case succ m ih =>
    cases xs <;> simp [List.take?]
    intro _ eq eq'; cases ys; {cases eq'}
    cases eq'; simp [ih eq]

lemma List.sliceD_eq_of_slice?_eq_some {ξ} {xs ys : List ξ} {m n : Nat} {d} :
    xs.slice? m n = some ys → xs.sliceD m n d = ys := by
  intro eq; simp only [List.slice?] at eq; simp only [List.sliceD]
  rcases of_bind_eq_some eq with ⟨zs, rw, rw'⟩
  rw [drop_eq_of_drop?_eq_some rw, takeD_eq_of_take?_eq_some rw']

lemma List.of_get?_succ_eq_some {X} {l : List X} {k : ℕ} {x} :
    l[k + 1]? = some x → ∃ y, l[k]? = some y := by
  induction k generalizing l x with
  | zero =>
    match l with
    | [] => simp
    | [_] => simp
    | (y :: _ :: _) => intro _; refine' ⟨y, rfl⟩
  | succ k ih =>
    match l with
    | [] => simp
    | y :: l' =>
      intro h; simp at h
      rcases ih h with ⟨y', h'⟩
      exact ⟨y', h'⟩

def U256.mul (x y : U256) : U256 := (U256.asBV x) * (U256.asBV y)
instance : HMul U256 U256 U256 := ⟨U256.mul⟩

def U256.div (x y : U256) : U256 :=
  if y = 0 then 0 else BitVec.udiv x y

def U256.mod (x y : U256) : U256 :=
  if y = 0 then 0 else BitVec.umod x y

def U256.divMod (x y : U256) : U256 × U256 :=
  if y = 0
  then ⟨0, 0⟩
  else ⟨BitVec.udiv x y, BitVec.umod x y⟩

instance : HDiv U256 U256 U256 := ⟨U256.div⟩
instance : HMod U256 U256 U256 := ⟨U256.mod⟩

def U256.sdiv (xs ys : U256) : U256 :=
  BitVec.sdiv xs ys

def U256.abs (xs : U256) : U256 := if isNeg xs then neg xs else xs

def U256.smod (xs ys : U256) : U256 :=
  if ys = 0
  then 0
  else BitVec.srem xs ys

def UInt64.testBit (xs : UInt64) (n : Nat) : Bool :=
  ((xs >>> n.toUInt64) &&& 0x0000000000000001) != 0

def U128.testBit (xs : U128) (n : Nat) : Bool :=
  if n < 64
  then xs.2.testBit n
  else xs.1.testBit (n - 64)

def U256.testBit (xs : U256) (n : Nat) : Bool :=
  (U256.asBV xs).getLsbD n

/-- Efficient modular exponentiation with the EVM convention at modulus zero.
Lean's kernel definition specifies the result; its runtime implementation uses
native modular exponentiation. Keep the zero/one branch explicit: Lean's
`Nat.powMod` follows natural-number remainder at zero instead. -/
def Nat.powMod (base exp m : Nat) : Nat :=
  if m ≤ 1 then 0 else _root_.Nat.powMod base exp m

/-- EVM modular exponentiation, including its zero result for modulus zero. -/
theorem Nat.powMod_eq (base exp m : Nat) :
    Nat.powMod base exp m = if m ≤ 1 then 0 else base ^ exp % m := by
  simp only [Nat.powMod, _root_.Nat.powMod_def]

def U256.exp (xs ys : U256) : U256 :=
  (Nat.powMod xs.toNat ys.toNat (2 ^ 256)).toU256

/-- Reason about word exponentiation without unfolding its implementation. -/
theorem U256.exp_eq (x y : U256) :
    U256.exp x y = (x.toNat ^ y.toNat % (2 ^ 256)).toU256 := by
  simp only [U256.exp, Nat.powMod_eq, show ¬ (2 : Nat) ^ 256 ≤ 1 by decide,
    ite_false]

/-- The zero exponent is independent of the base word. -/
theorem U256.exp_zero (x : U256) : U256.exp x 0 = 1 := by
  rw [U256.exp_eq, show (0 : U256).toNat = 0 from rfl, Nat.pow_zero]
  rfl

instance : HPow U256 U256 U256 := ⟨U256.exp⟩

def String.joinln : List String → String :=
  String.intercalate "\n"

def Hexit.toNibble : Char → Option UInt8
  | '0' => some 0x00
  | '1' => some 0x01
  | '2' => some 0x02
  | '3' => some 0x03
  | '4' => some 0x04
  | '5' => some 0x05
  | '6' => some 0x06
  | '7' => some 0x07
  | '8' => some 0x08
  | '9' => some 0x09
  | 'a' => some 0x0A
  | 'b' => some 0x0B
  | 'c' => some 0x0C
  | 'd' => some 0x0D
  | 'e' => some 0x0E
  | 'f' => some 0x0F
  | 'A' => some 0x0A
  | 'B' => some 0x0B
  | 'C' => some 0x0C
  | 'D' => some 0x0D
  | 'E' => some 0x0E
  | 'F' => some 0x0F
  |  _  => none

-- Tail-recursive: inputs are whole transaction payloads, so the naive
-- `(xy :: ·) <$> toBytes xs` shape overflows the stack past ~64 KB.
def Nibbles.toBytes.go : Bytes → Bytes → Option Bytes
  | acc, [] => some acc.reverse
  | _, [_] => none
  | acc, x :: y :: xs => Nibbles.toBytes.go (((x <<< 4) ||| y) :: acc) xs

def Nibbles.toBytes (xs : Bytes) : Option Bytes := Nibbles.toBytes.go [] xs

def Hex.toBytes (s : String) : Option Bytes :=
  s.toList.mapM Hexit.toNibble >>= Nibbles.toBytes

def List.compare {ξ : Type u} [Ord ξ] : List ξ → List ξ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match Ord.compare x y with
    | .eq => List.compare xs ys
    | o => o
instance {ξ : Type u} [Ord ξ] : Ord (List ξ) := ⟨List.compare⟩

/-- Jaune's list comparator is core's lexicographic one. -/
theorem List.jauneCompare_eq_compareLex {ξ : Type u} [Ord ξ] (xs ys : _root_.List ξ) :
    Jaune.List.compare xs ys = _root_.List.compareLex (Ord.compare : ξ → ξ → Ordering) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> rfl
  | cons x xs ih =>
      cases ys with
      | nil => rfl
      | cons y ys =>
          cases h : (Ord.compare x y : Ordering) <;>
            simp [Jaune.List.compare, _root_.List.compareLex, h, ih]

instance {ξ : Type u} [Ord ξ] [Std.TransCmp (Ord.compare : ξ → ξ → Ordering)] :
    Std.TransCmp (Ord.compare : _root_.List ξ → _root_.List ξ → Ordering) := by
  rw [show (Ord.compare : _root_.List ξ → _root_.List ξ → Ordering) =
      _root_.List.compareLex (Ord.compare : ξ → ξ → Ordering) by
    funext xs ys
    exact List.jauneCompare_eq_compareLex xs ys]
  infer_instance

instance {ξ : Type u} [Ord ξ] [Std.LawfulEqCmp (Ord.compare : ξ → ξ → Ordering)] :
    Std.LawfulEqCmp (Ord.compare : _root_.List ξ → _root_.List ξ → Ordering) := by
  rw [show (Ord.compare : _root_.List ξ → _root_.List ξ → Ordering) =
      _root_.List.compareLex (Ord.compare : ξ → ξ → Ordering) by
    funext xs ys
    exact List.jauneCompare_eq_compareLex xs ys]
  infer_instance

def UInt8.compareLows (x y : UInt8) : Ordering :=
  Ord.compare x.lows y.lows

def Nibbles.toHex : Bytes → String
  | [] => ""
  | [b] => String.ofList [b.toHexit]
  | b :: bs => String.ofList ([b.toHexit] ++ (toHex bs).toList)
def remove0x (s : String) : String :=
  match s.toList with
  | '0' :: 'x' :: cs => String.ofList cs
  | _ => s

def UInt16.ofBytes (a b : UInt8) : UInt16 :=
  let high : UInt16 := a.toUInt16
  let low : UInt16 := b.toUInt16
  (high <<< 8) ||| low

def UInt32.ofBytes (a b c d : UInt8) : UInt32 :=
  let a32 : UInt32 := a.toUInt32
  let b32 : UInt32 := b.toUInt32
  let c32 : UInt32 := c.toUInt32
  let d32 : UInt32 := d.toUInt32
  (a32 <<< 24) ||| (b32 <<< 16) ||| (c32 <<< 8) ||| d32

def UInt64.ofBytes (a b c d e f g h : UInt8) : UInt64 :=
  let a64 : UInt64 := a.toUInt64
  let b64 : UInt64 := b.toUInt64
  let c64 : UInt64 := c.toUInt64
  let d64 : UInt64 := d.toUInt64
  let e64 : UInt64 := e.toUInt64
  let f64 : UInt64 := f.toUInt64
  let g64 : UInt64 := g.toUInt64
  let h64 : UInt64 := h.toUInt64
  (a64 <<< 56) |||
  (b64 <<< 48) |||
  (c64 <<< 40) |||
  (d64 <<< 32) |||
  (e64 <<< 24) |||
  (f64 <<< 16) |||
  (g64 <<< 8)  |||
  h64

-- `packV` is `pack` with its width in the type, so the two byte reads below
-- are total: padding a short input on the left with zeros is what `pack`
-- always did, and it is now the type that says the result has two bytes.
def Bytes.toUInt16 (xs : Bytes) : UInt16 :=
  let v := xs.packV 2
  let high : UInt16 := v[0].toUInt16
  let low : UInt16 := v[1].toUInt16
  (high <<< 8) ||| low

def Bytes.toUInt32 (xs : Bytes) : UInt32 :=
  let v := xs.pack 4
  let high : UInt32 := (Bytes.toUInt16 (v.take 2)).toUInt32
  let low  : UInt32 := (Bytes.toUInt16 (v.drop 2)).toUInt32
  (high <<< 16) ||| low

def Bytes.toUInt64 (xs : Bytes) : UInt64 :=
  let v := xs.pack 8
  let high : UInt64 := (Bytes.toUInt32 (v.take 4)).toUInt64
  let low  : UInt64 := (Bytes.toUInt32 (v.drop 4)).toUInt64
  (high <<< 32) ||| low

def UInt16.concat (x y : UInt16) : UInt32 :=
  x.toUInt32 <<< 16 ||| y.toUInt32

def UInt32.concat (x y : UInt32) : UInt64 :=
  x.toUInt64 <<< 32 ||| y.toUInt64

def Bytes.toUInt64? (xs : Bytes) : Option UInt64 :=
  if xs.length = 8 then some (Bytes.toUInt64 xs) else none

def Bytes.toU128Diff : Bytes → Option (U128 × Bytes)
  | x0 :: x1 :: x2 :: x3 ::
    x4 :: x5 :: x6 :: x7 ::
    y0 :: y1 :: y2 :: y3 ::
    y4 :: y5 :: y6 :: y7 :: xs =>
    some
      ⟨
        ⟨ UInt64.ofBytes x0 x1 x2 x3 x4 x5 x6 x7,
          UInt64.ofBytes y0 y1 y2 y3 y4 y5 y6 y7 ⟩,
        xs
      ⟩
  | _ => none

def Bytes.toU256 (xs : Bytes) : U256 :=
  let xs' := if xs.length ≤ 32 then xs else xs.drop (xs.length - 32)
  Nat.toU256 (xs'.foldl (fun n b => n * 256 + b.toNat) 0)

def Bytes.toU256? (xs : Bytes) : Option U256 :=
  if xs.length = 32 then some (Bytes.toU256 xs) else none

def Hex.toUInt64? (hx : String) : Option UInt64 := do
  Hex.toBytes hx >>= Bytes.toUInt64?

def Hex.toU256? (hx : String) : Option U256 := do
  Hex.toBytes hx >>= Bytes.toU256?

lemma UInt16.length_toBytes (x : UInt16) : x.toBytes.length = 2 := rfl
lemma UInt32.length_toBytes (x : UInt32) : x.toBytes.length = 4 := rfl
lemma UInt64.length_toBytes (x : UInt64) : x.toBytes.length = 8 := rfl
lemma U128.length_toBytes (x : U128) : x.toBytes.length = 16 := rfl
lemma U256.length_toBytes (w : U256) : w.toBytes.length = 32 := rfl

theorem List.takeD_eq_self {ξ : Type u} {n : ℕ} {xs : List ξ} (x : ξ)
    (h : n = xs.length) : List.takeD n xs x = xs := by
  rw [takeD_eq_take x <| le_of_eq h, take_of_length_le <| le_of_eq h.symm]

lemma Bytes.pack_eq_self {xs n} (h : xs.length = n) : Bytes.pack xs n = xs := by
  simp only [pack, List.takeRightD]
  rw [List.takeD_eq_self]
  · apply List.reverse_reverse
  · rw [List.length_reverse, h]

lemma List.take_length_append {ξ} {xs ys : List ξ} :
    List.take xs.length (xs ++ ys) = xs := by
  apply Eq.trans <| List.take_length_add_append 0
  simp [take_zero]

lemma List.take_length_append' {ξ} {n} {xs ys : List ξ} (h : n = xs.length) :
    List.take n (xs ++ ys) = xs := by
  rw [h]; apply List.take_length_append

lemma List.drop_length_append {ξ} {xs ys : List ξ} :
    List.drop xs.length (xs ++ ys) = ys := by
  apply Eq.trans <| List.drop_length_add_append 0
  simp [drop_zero]

lemma List.drop_length_append' {ξ} {n} {xs ys : List ξ} (h : n = xs.length) :
    List.drop n (xs ++ ys) = ys := by
  rw [h]; apply List.drop_length_append

def Nat.lo (n m : ℕ) : ℕ := n % (2 ^ m)
def Nat.hi (n m : ℕ) : ℕ := n >>> m <<< m

infix:70 " ↾ " => Nat.lo
infix:70 " ↿ " => Nat.hi

lemma Nat.lo_eq (m n : Nat) : m ↾ n = m % (2 ^ n) := rfl
lemma Nat.hi_eq (m n : Nat) : m ↿ n = (m >>> n) <<< n := rfl

lemma Nat.hi_le (a b : Nat) : a ↿ b ≤ a := by
  rw [hi, shiftLeft_eq, shiftRight_eq_div_pow]
  apply Nat.div_mul_le_self

lemma Nat.add_sub_mod_eq_sub {k m n : Nat}
    (hm : m < k) (h : n ≤ m) : (k + m - n) % k = m - n := by
  rw [Nat.add_sub_assoc h, Nat.add_mod_left, Nat.mod_eq_of_lt]
  apply lt_of_le_of_lt (Nat.sub_le _ _) hm

lemma two_le_32 : (2 : Nat) ≤ 32 := by omega

lemma Nat.mod_two_pow_succ {k m} :
    (k % (2 ^ (m + 1))) = (k / 2) % (2 ^ m) * 2 + k % 2 := by
  rw [Nat.pow_succ, Nat.mul_comm, Nat.mod_mul]
  rw [Nat.add_comm, Nat.mul_comm]

lemma Nat.mod_two_pow_add {k m n : ℕ} :
   k % 2 ^ (m + n) = k / 2 ^ n % 2 ^ m * 2 ^ n + k % 2 ^ n := by
 induction n generalizing k m with
 | zero => simp [Nat.mod_one]
 | succ n ih =>
   rw [← Nat.add_assoc]
   rw [Nat.mod_two_pow_succ, ih]
   rw [Nat.div_div_eq_div_mul]
   rw [← Nat.pow_succ']
   rw [Nat.add_mul]
   rw [Nat.pow_succ]
   rw [Nat.mul_assoc]
   rw [Nat.add_assoc]
   apply congr_arg₂ _ rfl
   rw [← Nat.pow_succ]
   rw [Nat.mod_two_pow_succ]

lemma Nat.mod_two_pow_mul_two_pow {k m n : Nat} :
    (k % 2 ^ m) * 2 ^ n = (k * 2 ^ n) % 2 ^ (m + n) := by
  rw [Nat.mod_two_pow_add, Nat.mul_div_cancel]
  · simp [Nat.mul_mod_left]
  · apply Nat.pow_pos; omega

lemma Nat.lo_shl {k m n : Nat} :
    (k ↾ m) <<< n = (k <<< n) ↾ (m + n) := by
  rw [Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  apply Nat.mod_two_pow_mul_two_pow

lemma Nat.shl_lo_eq_zero_of_le {k m n : Nat} (h : m ≤ n) :
    (k <<< n) ↾ m = 0 := by
  rw [Nat.shiftLeft_eq]
  apply Nat.mod_eq_zero_of_dvd
  apply Nat.dvd_mul_left_of_dvd
  apply Nat.pow_dvd_pow _ h

lemma Nat.exists_eq_shiftLeft_of_dvd {n x} (hx : 2 ^ n ∣ x) :
    ∃ y, x = y <<< n := by
  rcases hx with ⟨y, ⟨_⟩⟩
  rw [Nat.mul_comm, ← Nat.shiftLeft_eq]
  refine ⟨y, rfl⟩

lemma Nat.add_eq_or {n x y} (hx : 2 ^ n ∣ x) (hy : y < 2 ^ n) :
    x + y = x ||| y := by
  rcases exists_eq_shiftLeft_of_dvd hx with ⟨z, ⟨_⟩⟩
  rw [Nat.shiftLeft_add_eq_or_of_lt hy]

lemma Nat.two_pow_dvd_shl {k m : Nat} : 2 ^ k ∣ m <<< k := by
  rw [Nat.shiftLeft_eq]; apply Nat.dvd_mul_left

lemma Nat.lo_add {k m n : ℕ} :
    k ↾ (m + n) = (((k >>> n) ↾ m) <<< n) ||| k ↾ n := by
  apply Eq.trans mod_two_pow_add
  rw [← Nat.shiftLeft_eq, ← Nat.shiftRight_eq_div_pow]
  apply add_eq_or two_pow_dvd_shl (Nat.mod_lt _ (Nat.pow_pos (by omega)))

lemma Nat.lo_lt {x y : Nat} : x ↾ y < 2 ^ y :=
  Nat.mod_lt _ (Nat.pow_pos (by omega))

lemma Nat.lo_add_shr {k m n : ℕ} :
    (k ↾ (m + n)) >>> n = (k >>> n) ↾ m := by
  rw [lo_add, shiftRight_eq_div_pow, or_div_two_pow]
  have rw : k ↾ n / 2 ^ n = 0 := by
    rw [div_eq_zero_iff_lt (Nat.pow_pos (by omega))]; apply lo_lt
  rw [rw, or_zero, ← shiftRight_eq_div_pow, shiftLeft_shiftRight]

lemma Nat.add_mod_two_pow_distrib
    {m n x y : Nat} (hx : 2 ^ m ∣ x) (hy : y < 2 ^ m) :
    (x + y) % (2 ^ n) = x % (2 ^ n) + y % (2 ^ n) := by
  rw [add_eq_or hx hy, or_mod_two_pow]
  by_cases h : m ≤ n
  · rw [add_eq_or _ (@Nat.mod_lt_of_lt _ (2 ^ n) _ hy)]
    apply (@Nat.dvd_mod_iff (2 ^ m) x (2 ^ n) _).mpr hx
    apply Nat.pow_dvd_pow _ h
  · rw [not_le] at h
    have h' := Nat.pow_dvd_pow 2 (Nat.le_of_lt h)
    simp [@Nat.mod_eq_zero_of_dvd (2 ^ n) x (Nat.dvd_trans h' hx)]

lemma Nat.concat_modadd_concat {m n x x' y y' : Nat}
    (hx' : x' < 2 ^ n) (hy' : y' < 2 ^ n) :
    ((x * 2 ^ n + x') + (y * 2 ^ n + y')) % 2 ^ (m + n)
      = (((x + y + (if x' + y' < 2 ^ n then 0 else 1)) % 2 ^ m) * 2 ^ n)
      + ((x' + y') % 2 ^ n) := by
  have rw :
      (x * 2 ^ n + x' + (y * 2 ^ n + y')) = (x + y) * 2 ^ n + x' + y' := by
    rw [Nat.add_add_add_comm, ← Nat.add_mul, Nat.add_assoc]
  rw [rw]; clear rw
  have pow_le : 2 ^ n ≤ 2 ^ (m + n) := by
    apply Nat.pow_le_pow_right <;> omega
  by_cases h : x' + y' < 2 ^ n
  · rw [ite_eq_left h, Nat.add_zero, Nat.add_assoc]
    rw [Nat.add_mod_two_pow_distrib (Nat.dvd_mul_left _ _) h]
    apply congr_arg₂
    · rw [← Nat.mod_two_pow_mul_two_pow]
    · rw [Nat.mod_eq_of_lt h]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h pow_le)]
  · rw [ite_eq_right h]
    have rw :
        (x + y) * 2 ^ n + x' + y' =
        (x + y + 1) * 2 ^ n + ((x' + y') % 2 ^ n) := by
      rw [Nat.add_mul _ 1, Nat.add_assoc, Nat.add_assoc]
      apply congr_arg₂ _ rfl
      apply Eq.trans (Nat.mod_add_div' (x' + y') (2 ^ n)).symm
      rw [Nat.add_comm]
      apply congr_arg₂ _ (congr_arg₂ _ _ rfl) rfl
      rw [Nat.div_eq_iff (Nat.pow_pos (by omega)), Nat.one_mul]
      refine' ⟨le_of_not_gt h, Nat.le_pred_of_lt _⟩
      apply Nat.add_lt_add_of_lt_of_le hx' (le_of_lt hy')
    rw [rw]; clear rw h
    rw [Nat.add_mod_two_pow_distrib (Nat.dvd_mul_left _ _)]
    · apply congr_arg₂
      · rw [← Nat.mod_two_pow_mul_two_pow]
      · rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos (by omega))) pow_le)]
    · apply Nat.mod_lt _ <| Nat.pow_pos (by omega)

lemma Nat.mul_two_pow_add_eq_shl_or {n x y : ℕ} (lt : y < 2 ^ n) :
    x * 2 ^ n + y = x <<< n ||| y := by
  rw [← shiftLeft_eq]; apply add_eq_or two_pow_dvd_shl lt

lemma Nat.shl_or_add_shl_or_lo_add {m n x x' y y' : Nat}
    (x'_lt : x' < 2 ^ n) (y'_lt : y' < 2 ^ n) :
    ((x <<< n ||| x') + (y <<< n ||| y')) ↾ (m + n)
      = ( ((x + y + if x' + y' < 2 ^ n then 0 else 1) ↾ m) <<< n) |||
            ((x' + y') ↾ n ) := by
  apply
    Eq.trans (Eq.trans _ <| Nat.concat_modadd_concat x'_lt y'_lt)
      (mul_two_pow_add_eq_shl_or lo_lt)
  rw [mul_two_pow_add_eq_shl_or x'_lt, mul_two_pow_add_eq_shl_or y'_lt]; rfl

lemma Nat.concat_modsub_concat {m n x x' y y' : Nat}
    (hx' : x' < 2 ^ n) (hy : y < 2 ^ m) (hy' : y' < 2 ^ n) :
    (2 ^ (m + n) + (x * 2 ^ n + x') - (y * 2 ^ n + y')) % 2 ^ (m + n) =
    (((2 ^ m + x - y - (if x' < y' then 1 else 0)) % 2 ^ m) * 2 ^ n)
    + ((2 ^ n + x' - y') % 2 ^ n) := by
  have h :
      2 ^ (m + n) + (x * 2 ^ n + x') - (y * 2 ^ n + y') =
        (2 ^ m + x - y) * 2 ^ n + x' - y' := by
    have h : y * 2 ^ n ≤ 2 ^ (m + n) + x * 2 ^ n := by
      apply le_trans _ (Nat.le_add_right _ _); rw [Nat.pow_add]
      apply _root_.Nat.mul_le_mul_right; apply Nat.le_of_lt hy
    rw [← Nat.add_assoc, ← Nat.sub_sub, Nat.sub_add_comm h]
    rw [Nat.mul_sub_right_distrib, Nat.add_mul, Nat.pow_add]
  rw [h]; clear h
  have h_le : 2 ^ n ≤ 2 ^ (m + n) := by
    apply Nat.pow_le_pow_right <;> omega
  by_cases h : x' < y'
  · rw [ite_eq_left h]
    have h' :
        (2 ^ m + x - y) * 2 ^ n + x' - y' =
        (2 ^ m + x - y - 1) * 2 ^ n + (2 ^ n + x' - y') := by
      rw [← Nat.add_sub_assoc (by omega)]
      rw [Nat.mul_sub_right_distrib _ 1, Nat.one_mul]
      rw [← Nat.add_assoc, Nat.sub_add_cancel]
      apply Nat.le_mul_of_pos_left; omega
    rw [h']; clear h'
    have h_lt : (2 ^ n + x' - y') < 2 ^ n := by omega
    rw [Nat.add_mod_two_pow_distrib (Nat.dvd_mul_left _ _) h_lt]
    apply congr_arg₂
    · rw [← Nat.mod_two_pow_mul_two_pow]
    · rw [Nat.mod_eq_of_lt h_lt]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_lt h_le)]
  · rw [ite_eq_right h]; rw [not_lt] at h
    rw [Nat.add_sub_assoc h, Nat.add_sub_assoc h]
    rw [Nat.sub_zero, Nat.add_mod_left]
    have h_lt : x' - y' < 2 ^ n :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) hx'
    rw [Nat.add_mod_two_pow_distrib (Nat.dvd_mul_left _ _) h_lt]
    apply congr_arg₂
    · rw [← Nat.mod_two_pow_mul_two_pow]
    · rw [Nat.mod_eq_of_lt h_lt]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_lt h_le)]

lemma Nat.add_shl_or_sub_shl_or_lo_add {m n x x' y y' : Nat}
    (x'_lt : x' < 2 ^ n) (y_lt : y < 2 ^ m) (y'_lt : y' < 2 ^ n) :
    (2 ^ (m + n) + (x <<< n ||| x') - (y <<< n ||| y')) ↾ (m + n) =
      (((2 ^ m + x - y - (if x' < y' then 1 else 0)) ↾ m) <<< n) |||
        ((2 ^ n + x' - y') ↾ n) := by
  apply
    Eq.trans (Eq.trans _ <| Nat.concat_modsub_concat x'_lt y_lt y'_lt)
      (mul_two_pow_add_eq_shl_or lo_lt)
  rw [mul_two_pow_add_eq_shl_or x'_lt, mul_two_pow_add_eq_shl_or y'_lt]; rfl

lemma high_or_low_eq_self (n o : Nat) (h : n < 2 ^ (o + o)) :
    (n >>> o % (2 ^ o)) <<< o % (2 ^ (o + o)) ||| n % (2 ^ o) = n := by
  have h_lt : (n >>> o) < 2 ^ o := by
    rw [Nat.shiftRight_eq_div_pow]
    have h_dvd := @Nat.pow_dvd_pow o (o + o) 2 (by omega)
    have h_lt := @Nat.div_lt_div_of_lt_of_dvd n (2 ^ (o + o)) (2 ^ o) h_dvd h
    have h_div := @Nat.pow_div 2 (o + o) o (by omega) (by omega)
    rw [h_div] at h_lt
    simp at h_lt
    apply h_lt
  rw [Nat.mod_eq_of_lt h_lt]
  rw [Nat.shiftRight_eq_div_pow]
  rw [Nat.shiftLeft_eq]

  have h_lt' : n / (2 ^ o) * (2 ^ o) < 2 ^ (o + o) := by
    apply lt_of_le_of_lt _ h
    rw [Nat.mul_comm]; apply Nat.mul_div_le
  rw [Nat.mod_eq_of_lt h_lt']

  have lt'' := @Nat.mod_lt n (2 ^ o) (Nat.pow_pos (by omega))

  have h_rw :=
    @Nat.shiftLeft_add_eq_or_of_lt o (n % (2 ^ o)) lt'' (n / (2 ^ o))

  rw [← Nat.shiftLeft_eq, ← h_rw]
  rw [Nat.shiftLeft_eq]
  rw [Nat.add_comm, Nat.mul_comm]
  apply Nat.mod_add_div

lemma toUInt16_toUInt8 (n : UInt16) : n.toUInt8.toUInt16 = n % 256 :=
  UInt16.toUInt16_toUInt8 _

-- `↾`-oriented restatements of the core shift lemmas: the codec proofs below
-- normalize widths with `Nat.lo`, so they rewrite with these forms.
lemma UInt16.toNat_shiftLeft_lo (a b : UInt16) :
    (a <<< b).toNat = a.toNat <<< (b.toNat % 16) ↾ 16 :=
  UInt16.toNat_shiftLeft _ _
lemma UInt32.toNat_shiftLeft_lo (a b : UInt32) :
    (a <<< b).toNat = a.toNat <<< (b.toNat % 32) ↾ 32 :=
  UInt32.toNat_shiftLeft _ _
lemma UInt64.toNat_shiftLeft_lo (a b : UInt64) :
    (a <<< b).toNat = a.toNat <<< (b.toNat % 64) ↾ 64 :=
  UInt64.toNat_shiftLeft _ _

lemma toUInt16_toBytes (x : UInt16) : x.toBytes.toUInt16 = x := by
  simp only [UInt16.toBytes, Bytes.toUInt16, Bytes.getElem_packV]
  rw [Bytes.pack_eq_self (by rfl)]
  simp
  rw [← UInt16.toNat_inj, UInt16.toNat_or, UInt16.toNat_shiftLeft_lo,
    UInt16.toNat_mod, UInt16.toNat_shiftRight, UInt16.toNat_mod]
  apply high_or_low_eq_self _ _ (UInt16.toNat_lt _)

lemma toUInt32_toUInt16 (n : UInt32) : n.toUInt16.toUInt32 = n % 65536 := UInt32.toUInt32_toUInt16 _
lemma toUInt64_toUInt32 (n : UInt64) : n.toUInt32.toUInt64 = n % 4294967296 := UInt64.toUInt64_toUInt32 _

lemma toUInt32_toBytes (x : UInt32) : x.toBytes.toUInt32 = x := by
  simp only [UInt32.toBytes, Bytes.toUInt32]
  have h_len : ∀ {a b : UInt16}, List.length (a.toBytes ++ b.toBytes) = 4 := by
    intros; rw [List.length_append, UInt16.length_toBytes, UInt16.length_toBytes]
  rw [Bytes.pack_eq_self h_len]
  rw [ List.take_length_append' (UInt16.length_toBytes _).symm,
       List.drop_length_append' (UInt16.length_toBytes _).symm ]
  rw [toUInt16_toBytes, toUInt16_toBytes]
  rw [toUInt32_toUInt16, toUInt32_toUInt16]
  rw [← UInt32.toNat_inj]
  rw [UInt32.toNat_or]
  rw [UInt32.toNat_shiftLeft]
  rw [UInt32.toNat_mod]
  rw [UInt32.toNat_shiftRight]
  apply high_or_low_eq_self
  apply UInt32.toNat_lt

lemma UInt64.toUInt64_toBytes (x : UInt64) : x.toBytes.toUInt64 = x := by
  simp only [UInt64.toBytes, Bytes.toUInt64]
  have h_len : ∀ {a b : UInt32}, List.length (a.toBytes ++ b.toBytes) = 8 := by
    intros; rw [List.length_append, UInt32.length_toBytes, UInt32.length_toBytes]
  rw [Bytes.pack_eq_self h_len]
  rw [ List.take_length_append' (UInt32.length_toBytes _).symm,
       List.drop_length_append' (UInt32.length_toBytes _).symm ]
  rw [toUInt32_toBytes, toUInt32_toBytes]
  rw [toUInt64_toUInt32, toUInt64_toUInt32]
  rw [← UInt64.toNat_inj]
  rw [UInt64.toNat_or]
  rw [UInt64.toNat_shiftLeft]
  rw [UInt64.toNat_mod]
  rw [UInt64.toNat_shiftRight]
  apply high_or_low_eq_self
  apply UInt64.toNat_lt

def Bytes.toU128 (xs : Bytes) : U128 :=
  let xs' := xs.pack 16
  let xh := xs'.take 8
  let xl := xs'.drop 8
  ⟨Bytes.toUInt64 xh, Bytes.toUInt64 xl⟩

private lemma Bytes.foldl_toU256_zero_cons (xs : Bytes) :
    (0 :: xs).foldl (fun n b => n * 256 + b.toNat) 0 =
      xs.foldl (fun n b => n * 256 + b.toNat) 0 := rfl

lemma Bytes.toU256_zero_cons (xs : Bytes) : Bytes.toU256 (0 :: xs) = Bytes.toU256 xs := by
  unfold Bytes.toU256
  dsimp only
  by_cases h1 : xs.length < 32
  · rw [ite_eq_left (by simp; omega), ite_eq_left (by omega)]
    rfl
  · by_cases h2 : xs.length = 32
    · rw [ite_eq_right (by simp [h2]), ite_eq_left (by omega)]
      simp [h2]
    · rw [ite_eq_right (by simp; omega), ite_eq_right (by omega)]
      rw [show (0 :: xs).length - 32 = (xs.length - 32) + 1 by simp; omega, List.drop_succ_cons]

lemma Bytes.toU256_pair (b0 b1 : UInt8) :
    Bytes.toU256 [b0, b1] = Nat.toU256 ((b0.toNat <<< 8) ||| b1.toNat) := by
  simp only [Bytes.toU256, List.length_cons, List.length_nil, Nat.reduceLeDiff, ↓reduceIte,
    List.foldl_cons, List.foldl_nil, Nat.zero_mul, Nat.zero_add]
  congr 1
  have hb1 : b1.toNat < 256 := b1.toNat_lt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (by simpa using hb1), Nat.shiftLeft_eq,
    show (2 : Nat) ^ 8 = 256 from rfl]

private lemma Nat.lo_lo_of_le_codec {x m n : Nat} (h : n ≤ m) :
    (x ↾ m) ↾ n = x ↾ n := by
  unfold Nat.lo
  rw [Nat.mod_mod_of_dvd]
  exact Nat.pow_dvd_pow 2 h

private lemma Nat.lo_or_codec (a b n : Nat) :
    (a ||| b) ↾ n = (a ↾ n) ||| (b ↾ n) :=
  Nat.or_mod_two_pow

private lemma Nat.lo_64_shr_56_codec (x : Nat) :
    (x ↾ 64) >>> 56 = (x >>> 56) ↾ 8 := by
  simpa using (Nat.lo_add_shr (k := x) (m := 8) (n := 56))

private lemma Nat.shl_shr_of_le_codec (x k n : Nat) (h : k ≤ n) :
    x <<< k >>> n = x >>> (n - k) := by
  conv_lhs => rw [show n = k + (n - k) by omega]
  rw [Nat.shiftRight_add, Nat.shiftLeft_shiftRight]

private lemma UInt64.small_shr_codec (x : UInt64) (hx : x.toNat < 2 ^ 8)
    (n : Nat) (h : 8 ≤ n) : x.toNat >>> n = 0 := by
  apply Nat.shiftRight_eq_zero
  exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) h)

private lemma Nat.lo_shl_eight_codec {x n w : Nat}
    (hx : x < 2 ^ 8) (h : 8 + n ≤ w) : (x <<< n) ↾ w = x <<< n := by
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt]
  rw [Nat.shiftLeft_eq]
  calc
    x * 2 ^ n < 2 ^ 8 * 2 ^ n :=
      Nat.mul_lt_mul_of_pos_right hx (Nat.pow_pos (by omega))
    _ = 2 ^ (8 + n) := (Nat.pow_add _ _ _).symm
    _ ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) h

private lemma Nat.lo_chunk_shl_codec {x n w : Nat} (h : 8 + n ≤ w) :
    ((x ↾ 8) <<< n) ↾ w = (x ↾ 8) <<< n :=
  Nat.lo_shl_eight_codec Nat.lo_lt h

private lemma Nat.lo_zero_codec (n : Nat) : 0 ↾ n = 0 := Nat.zero_mod _

private lemma UInt64.toNat_shr56_lo (y : UInt64) :
    y.toNat >>> 56 = (y.toNat >>> 56) ↾ 8 := by
  rw [← Nat.lo_64_shr_56_codec]
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt (UInt64.toNat_lt y)]

lemma UInt64.spill_eight (x y a b c d e f g h : UInt64)
    (ha : a.toNat < 2 ^ 8) (hb : b.toNat < 2 ^ 8)
    (hc : c.toNat < 2 ^ 8) (hd : d.toNat < 2 ^ 8)
    (he : e.toNat < 2 ^ 8) (hf : f.toNat < 2 ^ 8)
    (hg : g.toNat < 2 ^ 8) :
    let step (p : UInt64 × UInt64) (b : UInt64) :=
      ((p.1 <<< 8) ||| (p.2 >>> 56), (p.2 <<< 8) ||| b)
    (List.foldl step (x, y) [a, b, c, d, e, f, g, h]).1 = y := by
  dsimp only [List.foldl]
  have n8 : UInt64.toNat 8 % 64 = 8 := rfl
  have n56 : UInt64.toNat 56 % 64 = 56 := rfl
  rw [← UInt64.toNat_inj]
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft_lo, UInt64.toNat_shiftRight,
    n8, n56]
  simp only [Nat.lo_shl, Nat.shiftLeft_or_distrib, Nat.shiftRight_or_distrib]
  simp only [Nat.lo_or_codec]
  simp (disch := omega) only [Nat.lo_lo_of_le_codec]
  simp only [← Nat.shiftLeft_add]
  norm_num
  simp only [Nat.lo_64_shr_56_codec, Nat.shiftRight_or_distrib]
  simp (disch := omega) only [Nat.shl_shr_of_le_codec, UInt64.small_shr_codec,
    Nat.zero_shiftLeft, Nat.or_zero]
  norm_num
  rw [Nat.shl_lo_eq_zero_of_le (by omega), Nat.zero_or]
  rw [UInt64.toNat_shr56_lo]
  simp only [Nat.lo_zero_codec, Nat.or_zero]
  simp (disch := omega) only [Nat.lo_chunk_shl_codec]
  rw [Nat.or_assoc, Nat.or_assoc, Nat.or_assoc, Nat.or_assoc,
      Nat.or_assoc, Nat.or_assoc]
  rw [← Nat.lo_add, ← Nat.lo_add, ← Nat.lo_add, ← Nat.lo_add,
      ← Nat.lo_add, ← Nat.lo_add, ← Nat.lo_add]
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt (UInt64.toNat_lt _)]

private lemma UInt64.shr56_lt (x : UInt64) : (x >>> 56).toNat < 2 ^ 8 := by
  rw [UInt64.toNat_shiftRight]
  change x.toNat >>> 56 < 2 ^ 8
  rw [UInt64.toNat_shr56_lo]
  exact Nat.lo_lt

lemma UInt64.shiftIn_eight (x : UInt64) (a b c d e f g h : UInt8) :
    ((((((((x <<< 8) ||| a.toUInt64) <<< 8 ||| b.toUInt64) <<< 8 ||| c.toUInt64)
       <<< 8 ||| d.toUInt64) <<< 8 ||| e.toUInt64) <<< 8 ||| f.toUInt64)
       <<< 8 ||| g.toUInt64) <<< 8 ||| h.toUInt64 =
      UInt64.ofBytes a b c d e f g h := by
  have widen (z : UInt8) : z.toUInt64.toNat = z.toNat := rfl
  have n8 : UInt64.toNat 8 % 64 = 8 := rfl
  have n16 : UInt64.toNat 16 % 64 = 16 := rfl
  have n24 : UInt64.toNat 24 % 64 = 24 := rfl
  have n32 : UInt64.toNat 32 % 64 = 32 := rfl
  have n40 : UInt64.toNat 40 % 64 = 40 := rfl
  have n48 : UInt64.toNat 48 % 64 = 48 := rfl
  have n56 : UInt64.toNat 56 % 64 = 56 := rfl
  rw [← UInt64.toNat_inj]
  simp only [UInt64.ofBytes, UInt64.toNat_or, UInt64.toNat_shiftLeft_lo,
    widen, n8, n16, n24, n32, n40, n48, n56]
  simp only [Nat.lo_shl, Nat.shiftLeft_or_distrib]
  simp only [Nat.lo_or_codec]
  simp (disch := omega) only [Nat.lo_lo_of_le_codec]
  simp only [← Nat.shiftLeft_add]
  norm_num
  rw [Nat.shl_lo_eq_zero_of_le (by omega)]
  simp

private lemma UInt8.toNat_toUInt16_shift8 (x : UInt8) :
    (x.toUInt16 <<< 8).toNat = x.toNat <<< 8 := by
  rw [UInt16.toNat_shiftLeft]
  change (x.toNat <<< 8) ↾ 16 = x.toNat <<< 8
  unfold UInt8.toNat
  exact Nat.lo_shl_eight_codec (UInt8.toNat_lt x) (by omega)

private lemma UInt16.toNat_toUInt32_shift16 (x : UInt16) :
    (x.toUInt32 <<< 16).toNat = x.toNat <<< 16 := by
  rw [UInt32.toNat_shiftLeft]
  change (x.toNat <<< 16) ↾ 32 = x.toNat <<< 16
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt, Nat.shiftLeft_eq]
  have hx := UInt16.toNat_lt (n := x)
  norm_num at hx ⊢
  omega

private lemma UInt32.toNat_toUInt64_shift32 (x : UInt32) :
    (x.toUInt64 <<< 32).toNat = x.toNat <<< 32 := by
  rw [UInt64.toNat_shiftLeft]
  change (x.toNat <<< 32) ↾ 64 = x.toNat <<< 32
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt, Nat.shiftLeft_eq]
  have hx := UInt32.toNat_lt (n := x)
  norm_num at hx ⊢
  omega

private lemma UInt16.ofBytes_nat (a b : UInt8) :
    (UInt16.ofBytes a b).toNat = (a.toNat <<< 8) ||| b.toNat := by
  simp only [UInt16.ofBytes, UInt16.toNat_or, UInt8.toNat_toUInt16_shift8]
  rfl

lemma UInt32.ofBytes_eq_halves (a b c d : UInt8) :
    UInt32.ofBytes a b c d =
      ((UInt16.ofBytes a b).toUInt32 <<< 16) ||| (UInt16.ofBytes c d).toUInt32 := by
  have widen8 (z : UInt8) : z.toUInt32.toNat = z.toNat := rfl
  have widen16 (z : UInt16) : z.toUInt32.toNat = z.toNat := rfl
  have n8 : UInt32.toNat 8 % 32 = 8 := rfl
  have n16 : UInt32.toNat 16 % 32 = 16 := rfl
  have n24 : UInt32.toNat 24 % 32 = 24 := rfl
  rw [← UInt32.toNat_inj]
  simp only [UInt32.ofBytes, UInt32.toNat_or]
  rw [UInt16.toNat_toUInt32_shift16]
  simp only [widen16, UInt16.ofBytes_nat, UInt32.toNat_shiftLeft_lo,
    widen8, n8, n16, n24]
  rw [Nat.lo_shl_eight_codec (UInt8.toNat_lt a) (by omega),
      Nat.lo_shl_eight_codec (UInt8.toNat_lt b) (by omega),
      Nat.lo_shl_eight_codec (UInt8.toNat_lt c) (by omega)]
  rw [Nat.shiftLeft_or_distrib]
  simp only [← Nat.shiftLeft_add]
  norm_num
  simp only [Nat.or_assoc]

private lemma UInt32.ofBytes_nat (a b c d : UInt8) :
    (UInt32.ofBytes a b c d).toNat =
      (a.toNat <<< 24) ||| (b.toNat <<< 16) ||| (c.toNat <<< 8) ||| d.toNat := by
  rw [UInt32.ofBytes_eq_halves]
  simp only [UInt32.toNat_or, UInt16.toNat_toUInt32_shift16]
  have widen16 (z : UInt16) : z.toUInt32.toNat = z.toNat := rfl
  simp only [widen16, UInt16.ofBytes_nat]
  rw [Nat.shiftLeft_or_distrib]
  simp only [← Nat.shiftLeft_add]
  norm_num
  simp only [Nat.or_assoc]

lemma UInt64.ofBytes_eq_halves (a b c d e f g h : UInt8) :
    UInt64.ofBytes a b c d e f g h =
      ((UInt32.ofBytes a b c d).toUInt64 <<< 32) ||| (UInt32.ofBytes e f g h).toUInt64 := by
  have widen8 (z : UInt8) : z.toUInt64.toNat = z.toNat := rfl
  have widen32 (z : UInt32) : z.toUInt64.toNat = z.toNat := rfl
  have n8 : UInt64.toNat 8 % 64 = 8 := rfl
  have n16 : UInt64.toNat 16 % 64 = 16 := rfl
  have n24 : UInt64.toNat 24 % 64 = 24 := rfl
  have n32 : UInt64.toNat 32 % 64 = 32 := rfl
  have n40 : UInt64.toNat 40 % 64 = 40 := rfl
  have n48 : UInt64.toNat 48 % 64 = 48 := rfl
  have n56 : UInt64.toNat 56 % 64 = 56 := rfl
  rw [← UInt64.toNat_inj]
  simp only [UInt64.ofBytes, UInt64.toNat_or]
  rw [UInt32.toNat_toUInt64_shift32]
  simp only [widen32, UInt32.ofBytes_nat, UInt64.toNat_shiftLeft_lo,
    widen8, n8, n16, n24, n32, n40, n48, n56]
  rw [Nat.lo_shl_eight_codec (UInt8.toNat_lt a) (by omega),
      Nat.lo_shl_eight_codec (UInt8.toNat_lt b) (by omega),
      Nat.lo_shl_eight_codec (UInt8.toNat_lt c) (by omega),
      Nat.lo_shl_eight_codec (UInt8.toNat_lt d) (by omega),
      Nat.lo_shl_eight_codec (UInt8.toNat_lt e) (by omega),
      Nat.lo_shl_eight_codec (UInt8.toNat_lt f) (by omega),
      Nat.lo_shl_eight_codec (UInt8.toNat_lt g) (by omega)]
  simp only [Nat.shiftLeft_or_distrib, ← Nat.shiftLeft_add]
  norm_num
  simp only [Nat.or_assoc]

lemma UInt64.ofBytes_eq_toUInt64 (a b c d e f g h : UInt8) :
    UInt64.ofBytes a b c d e f g h = Bytes.toUInt64 [a, b, c, d, e, f, g, h] := by
  rw [UInt64.ofBytes_eq_halves]
  change
    ((UInt32.ofBytes a b c d).toUInt64 <<< 32) ||| (UInt32.ofBytes e f g h).toUInt64 =
      ((Bytes.toUInt32 [a, b, c, d]).toUInt64 <<< 32) |||
        (Bytes.toUInt32 [e, f, g, h]).toUInt64
  rw [UInt32.ofBytes_eq_halves, UInt32.ofBytes_eq_halves]
  rfl

private lemma U256.toBytes_go_length (k n : Nat) (acc : Bytes) :
    (U256.toBytes.go k n acc).length = k + acc.length := by
  induction k generalizing n acc with
  | zero => simp [U256.toBytes.go]
  | succ k ih => simp [U256.toBytes.go, ih]; omega

private lemma U256.toBytes_go_foldl (k n : Nat) (acc : Bytes) :
    (U256.toBytes.go k n acc).foldl (fun m b => m * 256 + b.toNat) 0 =
      acc.foldl (fun m b => m * 256 + b.toNat) (n % 256 ^ k) := by
  induction k generalizing n acc with
  | zero => simp [U256.toBytes.go, Nat.mod_one]
  | succ k ih =>
    simp only [U256.toBytes.go]
    rw [ih, List.foldl_cons]
    congr 1
    rw [UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow, show (2 : Nat) ^ 8 = 256 from rfl]
    rw [Nat.pow_succ', Nat.mod_mul]
    rw [Nat.mul_comm (n / 256 % 256 ^ k) 256]
    omega

lemma U256.toU256_toBytes (x : U256) : x.toBytes.toU256 = x := by
  unfold Bytes.toU256 U256.toBytes
  dsimp only
  have hlen : (U256.toBytes.go 32 x.toNat []).length = 32 :=
    U256.toBytes_go_length 32 x.toNat []
  rw [ite_eq_left (Nat.le_of_eq hlen), U256.toBytes_go_foldl, List.foldl_nil]
  have hx : x.toNat < 256 ^ 32 := BitVec.isLt x
  rw [Nat.mod_eq_of_lt hx]
  exact BitVec.eq_of_toNat_eq ((BitVec.toNat_ofNat _ _).trans (Nat.mod_eq_of_lt (BitVec.isLt x)))

def Array.writeD {ξ : Type u} (xs : Array ξ) (n : ℕ) : List ξ → Array ξ
  | [] => xs
  | y :: ys =>
    if h : n < xs.size
    then let xs' := xs.set n y h
         writeD xs' (n + 1) ys
    else xs

/-- Overwrite the front of `ys` with `xs`, keeping `ys`'s length: entries of
`xs` past the end of `ys` are dropped. That "what fits" contract is
`Array.setIfInBounds`'s, so the write is total by the function it calls rather
than by a convention about the caller, and `Array.size_copyD` states the length
half of it. -/
def Array.copyD {ξ : Type u} (xs ys : Array ξ) : Array ξ :=
  let f : (Array ξ × Nat) → ξ → (Array ξ × Nat) :=
    λ ysn x => ⟨Array.setIfInBounds ysn.fst ysn.snd x, ysn.snd + 1⟩
  (Array.foldl f ⟨ys, 0⟩ xs).fst

theorem Array.size_copyD {ξ : Type u} (xs ys : Array ξ) :
    (Array.copyD xs ys).size = ys.size := by
  have key : ∀ (l : List ξ) (a : Array ξ) (n : Nat),
      (List.foldl
        (fun (ysn : Array ξ × Nat) x => (ysn.fst.setIfInBounds ysn.snd x, ysn.snd + 1))
        (a, n) l).fst.size = a.size := by
    intro l
    induction l with
    | nil => intro a n; rfl
    | cons x l ih => intro a n; simp [ih]
  simpa [Array.copyD, Array.foldl_toList] using key xs.toList ys 0

def ByteArray.sliceD (xs : ByteArray) : Nat → Nat → UInt8 → Bytes
  | _, 0, _ => []
  | m, n + 1, d =>
    if h : m < xs.size
    then xs[m] :: ByteArray.sliceD xs (m + 1) n d
    else List.replicate (n + 1) d

lemma ByteArray.length_sliceD (xs : ByteArray) (m n : Nat) (d : UInt8) :
    (ByteArray.sliceD xs m n d).length = n := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    simp [ByteArray.sliceD]
    by_cases h : m < xs.size <;> simp [h, ih]

def Array.sliceD {ξ : Type u} (xs : Array ξ) : Nat → Nat → ξ → List ξ :=
  let rec aux (xs : Array ξ) : List ξ → Nat → Nat → ξ → List ξ
    | Acc, _, 0, _ => Acc
    | Acc, m, n + 1, d =>
      aux xs (xs.getD (m + n) d :: Acc) m n d
  aux xs []

def U256.min : U256 → U256 → U256
  | xs, ys => if xs ≤ ys then xs else ys
instance : Min U256 := ⟨.min⟩

def UInt8.toNibbles (x : UInt8) : List UInt8 := [x.highs, x.lows]
def UInt16.toNibbles (x : UInt16) : List UInt8 := x.highs.toNibbles ++ x.lows.toNibbles
def UInt32.toNibbles (x : UInt32) : List UInt8 := x.highs.toNibbles ++ x.lows.toNibbles
def UInt64.toNibbles (x : UInt64) : List UInt8 := x.highs.toNibbles ++ x.lows.toNibbles
def U128.toNibbles (x : U128) : List UInt8 := x.1.toNibbles ++ x.2.toNibbles
def U256.toNibbles.go : Nat → Nat → Bytes → Bytes
  | 0, _, acc => acc
  | k + 1, n, acc => U256.toNibbles.go k (n >>> 4) ((n &&& 0xF).toUInt8 :: acc)

def U256.toNibbles (x : U256) : List UInt8 := U256.toNibbles.go 64 x.toNat []

def Bytes.toNibbles : Bytes → Bytes
  | [] => []
  | x :: xs => x.toNibbles ++ Bytes.toNibbles xs

def List.splitAt? {ξ : Type u} (n : Nat) (xs : List ξ) : Option (List ξ × List ξ) :=
  let rec aux : Nat → List ξ →  List ξ → Option (List ξ × List ξ)
    | 0, xs, ys => some (xs.reverse, ys)
    | _ + 1, _, [] => none
    | n + 1, xs, y :: ys => aux n (y :: xs) ys
  aux n [] xs

def Bytes.toNat (bs : Bytes) : Nat :=
  let rec aux (acc : Nat) : Bytes → Nat
    | [] => acc
    | b :: bs => aux ((acc * 256) + b.toNat) bs
  aux 0 bs

/-- The width bound every strict scalar decoder relies on: a byte string of `n`
bytes denotes a value below `256 ^ n`. Stated on the accumulator so the
induction carries; the accumulator is the value read so far, and each further
byte multiplies its bound by 256. -/
theorem Bytes.toNat.aux_lt (bs : Bytes) (acc : Nat) :
    Bytes.toNat.aux acc bs < (acc + 1) * 256 ^ bs.length := by
  induction bs generalizing acc with
  | nil => simp [Bytes.toNat.aux]
  | cons b bs ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    have hstep := ih (acc * 256 + b.toNat)
    have hmono : (acc * 256 + b.toNat + 1) * 256 ^ bs.length
        ≤ (acc + 1) * (256 * 256 ^ bs.length) := by
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul_right _ (by omega)
    have hlt : Bytes.toNat.aux (acc * 256 + b.toNat) bs
        < (acc + 1) * (256 * 256 ^ bs.length) := Nat.lt_of_lt_of_le hstep hmono
    simpa [Bytes.toNat.aux, List.length_cons, Nat.pow_succ'] using hlt

/-- A byte string of `n` bytes denotes a value below `256 ^ n`. -/
theorem Bytes.toNat_lt (bs : Bytes) : bs.toNat < 256 ^ bs.length := by
  simpa [Bytes.toNat] using Bytes.toNat.aux_lt bs 0

/-- The form the field decoders use: an at-most-`n`-byte string is below
`256 ^ n`. -/
theorem Bytes.toNat_lt_of_length_le {bs : Bytes} {n : Nat} (h : bs.length ≤ n) :
    bs.toNat < 256 ^ n :=
  Nat.lt_of_lt_of_le bs.toNat_lt (Nat.pow_le_pow_right (by omega) h)

def Nat.toBytes (n : Nat) : Bytes :=
  let rec aux (acc : Bytes) : Nat → Bytes
  | 0 => acc
  | n@(_ + 1) => aux ((n % 256).toUInt8 :: acc) (n / 256)
  aux [] n

def Nat.toBytesPack : Nat → Bytes
  | 0 => [0]
  | n@(_ + 1) => n.toBytes

def Except.assert (p : Prop) [inst : Decidable p]
  {ξ : Type u} (x : ξ) : Except ξ Unit :=
  if p then .ok () else .error x

def Option.toExcept {ξ : Type u} {υ : Type v} (x : ξ) : Option υ → Except ξ υ
  | .none => .error x
  | .some y => .ok y

inductive Except.IsOk {ξ υ} : Except ξ υ → Prop
  | intro {x : υ} : Except.IsOk (Except.ok x)

inductive Rlp.Item : Type
  | bytes : Bytes → Rlp.Item
  | list : List Rlp.Item → Rlp.Item

def UInt8.toBools (x0 : UInt8) :
    Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool :=
  let x1 := x0 <<< 1
  let x2 := x1 <<< 1
  let x3 := x2 <<< 1
  let x4 := x3 <<< 1
  let x5 := x4 <<< 1
  let x6 := x5 <<< 1
  let x7 := x6 <<< 1
  ⟨ x0.highBit, x1.highBit, x2.highBit, x3.highBit,
    x4.highBit, x5.highBit, x6.highBit, x7.highBit ⟩

mutual

  def Bytes.toRlpItemDiff? : Nat → Bytes → Option (Rlp.Item × Bytes)
    | _, [] => none
    | 0, _ :: _ => none
    | k + 1, b :: bs =>
      match b.toBools with
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
      let rs ← Bytes.toRlpItems? k rbs
      return ⟨.list rs, bs''⟩
    | ⟨1, 1, _, _, _, _, _, _⟩ => do
      let (rbs, bs') ← List.splitAt? (b - 0xC0).toNat bs
      let rs ← Bytes.toRlpItems? k rbs
      return ⟨.list rs, bs'⟩

  def Bytes.toRlpItems? : Nat → Bytes → Option (List Rlp.Item)
    | _, [] => some []
    | 0, _ :: _ => none
    | k + 1, bs@(_ :: _) => do
      let (r, bs') ← Bytes.toRlpItemDiff? (k + 1) bs
      let rs ← Bytes.toRlpItems? k bs'
      return (r :: rs)

end

def Bytes.toRlpItem? (bs : Bytes) : Option Rlp.Item :=
  match Bytes.toRlpItemDiff? bs.length bs with
  | some (r, []) => some r
  | _ => none

mutual

  def Rlp.Item.toBytes : Rlp.Item → Bytes
    | .bytes [b] => if b < (0x80) then [b] else [0x81, b]
    | .bytes bs =>
      if bs.length < 56
      then (0x80 + bs.length.toUInt8) :: bs
      else let lbs : Bytes := bs.length.toBytesPack
           (0xB7 + lbs.length.toUInt8) :: (lbs ++ bs)
    | .list rs => Rlp.Items.toBytes rs

  def Rlp.Items.toBytesJoin : List Rlp.Item → Bytes
    | .nil => []
    | .cons r rs => r.toBytes ++ Rlp.Items.toBytesJoin rs

  def Rlp.Items.toBytes (rs : List Rlp.Item) : Bytes :=
    let bs := Rlp.Items.toBytesJoin rs
    let len := bs.length
    if len < 56
    then (0xC0 + len.toUInt8) :: bs
    else let lbs : Bytes := len.toBytesPack
         (0xF7 + lbs.length.toUInt8) :: (lbs ++ bs)

end

def List.chunks.go {ξ} (m : Nat) : Nat → List ξ → List (List ξ)
  | _, [] => []
  | 0, x :: xs =>
    match List.chunks.go m m xs with
    | [] => [[], [x]]
    | ys :: yss => [] :: (x :: ys) :: yss
  | n + 1, x :: xs =>
    match List.chunks.go m n xs with
    | [] => [[x]]
    | ys :: yss => (x :: ys) :: yss

def List.chunks {ξ} (m : Nat) : List ξ → List (List ξ) := List.chunks.go m (m + 1)

def String.chunks : Nat → String → List String
  | 0, _ => []
  | m + 1, s => (List.chunks m s.toList).map String.ofList

def U256.ltCheck  (x y : U256) : U256 := if x < y then 1 else 0
def U256.gtCheck  (x y : U256) : U256 := if x > y then 1 else 0
def U256.sltCheck (x y : U256) : U256 := if U256.SignedLt x y then 1 else 0
def U256.sgtCheck (x y : U256) : U256 := if U256.SignedGt x y then 1 else 0
def U256.eqCheck  (x y : U256) : U256 := if x = y then 1 else 0

def ceilDiv (m n : Nat) := m / n + if m % n = 0 then 0 else 1

-- Inlined: these are three instructions each and sit in the SHA-256 and
-- RIPEMD-160 round loops, where the call overhead dominated the work.
@[inline] def UInt32.rol (x n : UInt32) : UInt32 :=
  x <<< n ||| (x >>> (32 - n))
@[inline] def UInt32.ror (x n : UInt32): UInt32 :=
  x >>> n ||| (x <<< (32 - n))

def UInt32s.toUInt64 (x y : UInt32) : UInt64 :=
  x.toUInt64 <<< 32 ||| y.toUInt64

def UInt32s.toU128 (x0 x1 y0 y1 : UInt32) : U128 :=
  ⟨UInt32s.toUInt64 x0 x1, UInt32s.toUInt64 y0 y1⟩

def UInt32s.toU256 (x0 x1 x2 x3 y0 y1 y2 y3 : UInt32) : U256 :=
  let w0 := UInt32s.toUInt64 x0 x1
  let w1 := UInt32s.toUInt64 x2 x3
  let w2 := UInt32s.toUInt64 y0 y1
  let w3 := UInt32s.toUInt64 y2 y3
  Nat.toU256 ((w0.toNat <<< 192) ||| (w1.toNat <<< 128) ||| (w2.toNat <<< 64) ||| w3.toNat)

/-- Take the first `sz` entries of `xs` into an array of exactly `sz` slots,
padded with `x`, and return the rest of the list.

The worker carries `idx + sz = array.size`: the slots still to be written are
exactly the ones still to be filled. That equation is what makes each write
proof-indexed — the invariant used to live in the shape of the recursion and
be trusted. -/
def List.splitToArray {ξ : Type u}
  (sz : Nat) (xs : List ξ) (x : ξ) : Array ξ × List ξ :=
  let rec aux : (idx : Nat) → (array : Array ξ) → (sz : Nat) →
      idx + sz = array.size → List ξ → Array ξ × List ξ
    | _, array, _, _, [] => ⟨array, []⟩
    | _, array, 0, _, list => ⟨array, list⟩
    | idx, array, sz + 1, h, item :: list =>
      aux (idx + 1) (array.set idx item (by omega)) sz
        (by rw [Array.size_set]; omega) list
  aux 0 (.replicate sz x) sz (by simp) xs

def Nat.toHexit : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | 10 => 'A'
  | 11 => 'B'
  | 12 => 'C'
  | 13 => 'D'
  | 14 => 'E'
  | 15 => 'F'
  | _   => 'X'

def Nat.toHex (n : Nat) : String :=
  let rec aux : Nat → List Char
    | 0 => []
    | n@(_ + 1) =>
      if n < 16
      then [n.toHexit]
      else (n % 16).toHexit :: aux (n / 16)
  String.ofList <| .reverse <| aux n

def List.maxD {ξ} [Max ξ] : List ξ → ξ → ξ
  | [], y => y
  | x :: xs, y => maxD xs (max x y)

end Jaune
