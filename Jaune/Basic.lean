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
import Std.Tactic.BVDecide

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

def B128 : Type := UInt64 × UInt64
deriving DecidableEq

instance : Inhabited B128 := ⟨⟨0, 0⟩⟩

def B256 : Type := B128 × B128
deriving DecidableEq

instance : Inhabited B256 := ⟨⟨Inhabited.default, Inhabited.default⟩⟩

def B128.highBit (x : B128) : Bool := x.1.highBit
def B128.lowBit  (x : B128) : Bool := x.2.lowBit

def B256.highBit (x : B256) : Bool := x.1.highBit
def B256.lowBit  (x : B256) : Bool := x.2.lowBit

def UInt64.max : UInt64 := 0xFFFFFFFFFFFFFFFF
def B128.max : B128 := ⟨.max, .max⟩
def B256.max : B256 := ⟨.max, .max⟩

def B128.LT (x y : B128) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)
instance : @LT B128 := ⟨B128.LT⟩
instance {x y : B128} : Decidable (x < y) := instDecidableOr

def B256.LT (x y : B256) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

instance : @LT B256 := ⟨B256.LT⟩
instance {x y : B256} : Decidable (x < y) := instDecidableOr

def Nat.toB128 (n : Nat) : B128 :=
  ⟨(n >>> 64).toUInt64, n.toUInt64⟩

def Nat.toB256 (n : Nat) : B256 :=
  ⟨(n >>> 128).toB128, n.toB128⟩

instance {n} : OfNat B128 n := ⟨n.toB128⟩
instance {n} : OfNat B256 n := ⟨n.toB256⟩

theorem B256.kernel_decidable_comparisons :
    ((0x06fdde03 : B256) < (0x095ea7b3 : B256)) ∧
    ((0x095ea7b3 : B256) = (0x095ea7b3 : B256)) ∧
    ¬ ((0x095ea7b3 : B256) < (0x06fdde03 : B256)) := by
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

def B128.toHex (x : B128) : String := x.1.toHex ++ x.2.toHex
def B256.toHex (x : B256) : String := x.1.toHex ++ x.2.toHex

instance : ToString UInt8 := ⟨UInt8.toHex⟩
instance : ToString UInt16 := ⟨UInt16.toHex⟩
instance : ToString UInt32 := ⟨UInt32.toHex⟩
instance : ToString UInt64 := ⟨UInt64.toHex⟩
instance : ToString B128 := ⟨B128.toHex⟩
instance : ToString B256 := ⟨B256.toHex⟩

def B128.LE (x y : B128) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
instance : @LE B128 := ⟨B128.LE⟩
instance {x y : B128} : Decidable (x ≤ y) := instDecidableOr

def B256.LE (x y : B256) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
instance : @LE B256 := ⟨B256.LE⟩
instance {x y : B256} : Decidable (x ≤ y) := instDecidableOr

def B128.shiftLeft : B128 → Nat → B128
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else if os < 64
         then ⟨ (xs <<< os.toUInt64) ||| (ys >>> (64 - os).toUInt64),
                ys <<< os.toUInt64 ⟩
         else if os < 128
              then ⟨ys <<< (os - 64).toUInt64, 0⟩
              else ⟨0, 0⟩
instance : HShiftLeft B128 Nat B128 := ⟨B128.shiftLeft⟩

def B128.shiftRight : B128 → Nat → B128
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else if os < 64
         then ⟨ xs >>> os.toUInt64,
                (xs <<< (64 - os).toUInt64) ||| (ys >>> os.toUInt64) ⟩
         else if os < 128
              then ⟨0, xs >>> (os - 64).toUInt64⟩
              else ⟨0, 0⟩
instance : HShiftRight B128 Nat B128 := ⟨B128.shiftRight⟩

def B128.or : B128 → B128 → B128
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ||| yh, xl ||| yl⟩
instance : HOr B128 B128 B128 := ⟨B128.or⟩

def B128.and : B128 → B128 → B128
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh &&& yh, xl &&& yl⟩
instance : HAnd B128 B128 B128 := ⟨B128.and⟩

def B256.or : B256 → B256 → B256
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ||| yh, xl ||| yl⟩
instance : HOr B256 B256 B256 := ⟨B256.or⟩
def B256.and : B256 → B256 → B256
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh &&& yh, xl &&& yl⟩
instance : HAnd B256 B256 B256 := ⟨B256.and⟩

def B128.xor : B128 → B128 → B128
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ^^^ yh, xl ^^^ yl⟩
instance : HXor B128 B128 B128 := ⟨B128.xor⟩
def B256.xor : B256 → B256 → B256
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ^^^ yh, xl ^^^ yl⟩
instance : HXor B256 B256 B256 := ⟨B256.xor⟩

def B256.shiftRight : B256 → Nat → B256
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else if os < 128
         then ⟨ xs >>> os,
                (xs <<< (128 - os)) ||| (ys >>> os) ⟩
         else if os < 256
              then ⟨0, xs >>> (os - 128)⟩
              else ⟨0, 0⟩
instance : HShiftRight B256 Nat B256 := ⟨B256.shiftRight⟩


def B256.shiftLeft : B256 → Nat → B256
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else  if os < 128
         then ⟨(xs <<< os) ||| (ys >>> (128 - os)), ys <<< os⟩
         else if os < 256
              then ⟨ys <<< (os - 128), 0⟩
              else ⟨0, 0⟩
instance : HShiftLeft B256 Nat B256 := ⟨B256.shiftLeft⟩

def B256.isNeg : B256 → Bool := B256.highBit

def B256.arithShiftRight (xs : B256) (os : Nat) : B256 :=
  let xs' := xs >>> os
  if xs.isNeg
  then
    let mask := B256.max <<< (256 - os)
    xs' ||| mask
  else xs'

def B256.Slt (xs ys : B256) : Prop :=
  let x := xs.highBit
  let y := ys.highBit
  let xs' : B256 := xs &&& (B256.max >>> 1)
  let ys' : B256 := ys &&& (B256.max >>> 1)
  y < x ∨ (x = y ∧ xs' < ys')
instance {xs ys : B256} : Decidable (B256.Slt xs ys) := instDecidableOr

def B256.Sgt (xs ys : B256) : Prop := B256.Slt ys xs
instance {xs ys : B256} : Decidable (B256.Sgt xs ys) := instDecidableOr

def B128.complement : B128 → B128
  | ⟨xs, ys⟩ => ⟨~~~ xs, ~~~ ys⟩
instance : Complement B128 := ⟨B128.complement⟩

def B256.complement : B256 → B256
  | ⟨xs, ys⟩ => ⟨~~~ xs, ~~~ ys⟩
instance : Complement B256 := ⟨B256.complement⟩

def UInt8.toB256  (x : UInt8)  : B256 := ⟨0, ⟨0, x.toUInt64⟩⟩
def UInt16.toB256 (x : UInt16) : B256 := ⟨0, ⟨0, x.toUInt64⟩⟩
def UInt32.toB256 (x : UInt32) : B256 := ⟨0, ⟨0, x.toUInt64⟩⟩
def UInt64.toB256 (x : UInt64) : B256 := ⟨0, ⟨0, x⟩⟩

def B128.zero : B128 := ⟨0, 0⟩
instance : Zero B128 := ⟨.zero⟩
def B128.one : B128 := ⟨0, 1⟩
instance : One B128 := ⟨.one⟩
def B256.zero : B256 := ⟨0, 0⟩
instance : Zero B256 := ⟨.zero⟩
def B256.one : B256 := ⟨0, 1⟩
instance : One B256 := ⟨.one⟩

def B128.sub (x y : B128) : B128 :=
  let l := x.2 - y.2
  let c : UInt64 := if x.2 < y.2 then 1 else 0
  ⟨(x.1 - y.1) - c, l⟩
instance : HSub B128 B128 B128 := ⟨B128.sub⟩

def B128.add (x y : B128) : B128 :=
  let l := x.2 + y.2
  let c : UInt64 := if l < x.2 then 1 else 0
  ⟨x.1 + y.1 + c, l⟩
instance : HAdd B128 B128 B128 := ⟨B128.add⟩

def B256.add (x y : B256) : B256 :=
  let l := x.2 + y.2
  let c : B128 := if l < x.2 then 1 else 0
  ⟨x.1 + y.1 + c, l⟩
instance : HAdd B256 B256 B256 := ⟨B256.add⟩

def B256.sub (x y : B256) : B256 :=
  let l := x.2 - y.2
  let c : B128 := if x.2 < y.2 then 1 else 0
  ⟨(x.1 - y.1) - c, l⟩
instance : HSub B256 B256 B256 := ⟨B256.sub⟩
instance : Sub B256 := ⟨B256.sub⟩

def B256.neg (xs : B256) : B256 := (~~~ xs) + B256.one

-- minimum possible value in 2's complement
def UInt64.smin : UInt64 := 0x8000000000000000
def B128.smin : B128 := ⟨.smin, 0⟩
def B256.smin : B256 := ⟨.smin, 0⟩

def UInt64.negOne  : UInt64  := .max
def B128.negOne : B128 := .max
def B256.negOne : B256 := .max

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

def B128.toBytes (x : B128) : Bytes := x.1.toBytes ++ x.2.toBytes
def B256.toBytes (x : B256) : Bytes := x.1.toBytes ++ x.2.toBytes

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

def B128.toNat (x : B128) : Nat := (x.1.toNat <<< 64) ||| x.2.toNat
def B256.toNat (x : B256) : Nat := (x.1.toNat <<< 128) ||| x.2.toNat

def B256.addmod (x y z : B256) : B256 :=
  if z = 0
  then 0
  else ((x.toNat + y.toNat) % z.toNat).toB256 -- (x + y) % z

def B256.mulmod (x y z : B256) : B256 :=
  if z = 0
  then 0
  else ((x.toNat * y.toNat) % z.toNat).toB256 -- (x + y) % z

def B256.signext (x y : B256) : B256 :=
  if h : x < 31 then
    have h : (32 - (x.toNat + 1)) < 32 := by omega
    let z : UInt8 := (Bytes.pack y.toBytes 32)[32 - (x.toNat + 1)]
    cond z.highBit
      ((B256.max <<< (8 * (x.toNat + 1))) ||| y)
      ((B256.max >>> (256 - (8 * (x.toNat + 1)))) &&& y)
  else y

instance {ξ : Type u} {ρ : ξ → Prop} {xs : List ξ}
    [d : ∀ x : ξ, Decidable (ρ x)] : Decidable (xs.Forall ρ) := by
  induction xs with
  | nil => apply instDecidableTrue
  | cons x xs ih => simp; apply instDecidableAnd

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


def B256.mul (x y : B256) : B256 := (x.toNat * y.toNat).toB256
instance : HMul B256 B256 B256 := ⟨B256.mul⟩

def B256.divMod (x y : B256) : B256 × B256 :=
  if y = 0
  then ⟨0, 0⟩
  else ⟨(x.toNat / y.toNat).toB256, (x.toNat % y.toNat).toB256⟩

instance : HDiv B256 B256 B256 := ⟨λ x y => (B256.divMod x y).fst⟩
instance : HMod B256 B256 B256 := ⟨λ x y => (B256.divMod x y).snd⟩

def B256.sdiv (xs ys : B256) : B256 :=
  if ys = 0
  then 0
  else if xs = smin ∧ ys = negOne
       then smin
       else match (isNeg xs, isNeg ys) with
            | (0, 0) => xs / ys
            | (1, 0) => neg ((neg xs) / ys)
            | (0, 1) => neg (xs / (neg ys))
            | (1, 1) => (neg xs) / (neg ys)

def B256.abs (xs : B256) : B256 := if isNeg xs then neg xs else xs

def B256.smod (xs ys : B256) : B256 :=
  if ys = 0
  then 0
  else let mod := (abs xs) % (abs ys)
       if isNeg xs then neg mod else mod

def UInt64.testBit (xs : UInt64) (n : Nat) : Bool :=
  ((xs >>> n.toUInt64) &&& 0x0000000000000001) != 0

def B128.testBit (xs : B128) (n : Nat) : Bool :=
  if n < 64
  then xs.2.testBit n
  else xs.1.testBit (n - 64)

def B256.testBit (xs : B256) (n : Nat) : Bool :=
  if n < 128
  then xs.2.testBit n
  else xs.1.testBit (n - 128)

/-- Efficient modular exponentiation using the square-and-multiply algorithm -/
def Nat.powMod (base exp m : Nat) : Nat :=
  if m ≤ 1 then 0 else
    let rec go (e : Nat) (b : Nat) (res : Nat) : Nat :=
      match e with
      | 0 => res
      | e@(_ + 1) =>
        let res' := if e % 2 = 1 then (res * b) % m else res
        let b' := (b * b) % m
        go (e / 2) b' res'
    go exp base 1

def B256.bexp (xs ys : B256) : B256 :=
  (Nat.powMod xs.toNat ys.toNat (2 ^ 256)).toB256

instance : HPow B256 B256 B256 := ⟨B256.bexp⟩

def String.joinln : List String → String :=
  String.intercalate "\n"

def Hexit.toB4 : Char → Option UInt8
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
def B4L.toBytes.go : Bytes → Bytes → Option Bytes
  | acc, [] => some acc.reverse
  | _, [_] => none
  | acc, x :: y :: xs => B4L.toBytes.go (((x <<< 4) ||| y) :: acc) xs

def B4L.toBytes (xs : Bytes) : Option Bytes := B4L.toBytes.go [] xs

def Hex.toBytes (s : String) : Option Bytes :=
  s.toList.mapM Hexit.toB4 >>= B4L.toBytes

def Option.toIO {ξ} (o : Option ξ)
  (msg : String := "error : option-to-IO lift failed, input is 'none'") :
  IO ξ := do
  match o with
  | none => throw (IO.Error.userError msg)
  | some x => pure x

def List.compare {ξ : Type u} [Ord ξ] : List ξ → List ξ → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | x :: xs, y :: ys =>
    match Ord.compare x y with
    | .eq => List.compare xs ys
    | o => o
instance {ξ : Type u} [Ord ξ] : Ord (List ξ) := ⟨List.compare⟩

def UInt8.compareLows (x y : UInt8) : Ordering :=
  Ord.compare x.lows y.lows

def B4L.toHex : Bytes → String
  | [] => ""
  | [b] => String.ofList [b.toHexit]
  | b :: bs => String.ofList ([b.toHexit] ++ (toHex bs).toList)
def IO.throw {ξ} (s : String) : IO ξ := MonadExcept.throw <| IO.Error.userError s

def IO.remove0x (s : String) : IO String :=
  match s.toList with
  | '0' :: 'x' :: cs => return String.ofList cs
  | _ => IO.throw "prefix not 0x"

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

def Bytes.toUInt64? (xs : Bytes) : Option UInt64 :=
  if xs.length = 8 then some (Bytes.toUInt64 xs) else none

def Bytes.toB128Diff : Bytes → Option (B128 × Bytes)
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

def Bytes.toB256? (xs : Bytes) : Option B256 := do
  let ⟨h, xs'⟩ ← xs.toB128Diff
  let ⟨l, []⟩ ← xs'.toB128Diff | none
  some ⟨h, l⟩

def Hex.toUInt64? (hx : String) : Option UInt64 := do
  Hex.toBytes hx >>= Bytes.toUInt64?

def Hex.toB256? (hx : String) : Option B256 := do
  Hex.toBytes hx >>= Bytes.toB256?

lemma UInt16.length_toBytes (x : UInt16) : x.toBytes.length = 2 := rfl
lemma UInt32.length_toBytes (x : UInt32) : x.toBytes.length = 4 := rfl
lemma UInt64.length_toBytes (x : UInt64) : x.toBytes.length = 8 := rfl
lemma B128.length_toBytes (x : B128) : x.toBytes.length = 16 := rfl
lemma B256.length_toBytes (w : B256) : w.toBytes.length = 32 := rfl

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
  · rw [if_pos h, Nat.add_zero, Nat.add_assoc]
    rw [Nat.add_mod_two_pow_distrib (Nat.dvd_mul_left _ _) h]
    apply congr_arg₂
    · rw [← Nat.mod_two_pow_mul_two_pow]
    · rw [Nat.mod_eq_of_lt h]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h pow_le)]
  · rw [if_neg h]
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
  · rw [if_pos h]
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
  · rw [if_neg h]; rw [not_lt] at h
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

def Bytes.toB128 (xs : Bytes) : B128 :=
  let xs' := xs.pack 16
  let xh := xs'.take 8
  let xl := xs'.drop 8
  ⟨Bytes.toUInt64 xh, Bytes.toUInt64 xl⟩

-- Big-endian byte-list → word, as a single left-to-right pass over the four
-- 64-bit limbs: each byte is shifted into the low limb and the overflow of
-- every limb spills into the next. Bytes beyond the 32 most recent ones fall
-- off the top, so this agrees with the old `pack 32`-then-split codec on both
-- of its behaviors: left zero-extension of short lists, and truncation to the
-- last 32 bytes of long ones. No `pack`, `take`, `drop`, or reversal.
def Bytes.toB256.go (l3 l2 l1 l0 : UInt64) : Bytes → B256
  | [] => ⟨⟨l3, l2⟩, ⟨l1, l0⟩⟩
  | b :: bs =>
    go ((l3 <<< 8) ||| (l2 >>> 56))
       ((l2 <<< 8) ||| (l1 >>> 56))
       ((l1 <<< 8) ||| (l0 >>> 56))
       ((l0 <<< 8) ||| b.toUInt64)
       bs

def Bytes.toB256 (xs : Bytes) : B256 := Bytes.toB256.go 0 0 0 0 xs

-- Equation lemmas for the codec: leading zero bytes are inert, and the short
-- concrete case that downstream proofs unfold. These replace the `pack`/`take`/
-- `drop` reasoning the old definition invited.
lemma Bytes.toB256_zero_cons (xs : Bytes) : Bytes.toB256 (0 :: xs) = Bytes.toB256 xs :=
  rfl

lemma Bytes.toB256_pair (b0 b1 : UInt8) :
    Bytes.toB256 [b0, b1] = ⟨⟨0, 0⟩, ⟨0, (b0.toUInt64 <<< 8) ||| b1.toUInt64⟩⟩ := by
  simp only [Bytes.toB256, Bytes.toB256.go]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;> bv_decide

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

lemma Bytes.toB256_go_eight (l3 l2 l1 l0 : UInt64) (a b c d e f g h : UInt8) :
    Bytes.toB256.go l3 l2 l1 l0 [a, b, c, d, e, f, g, h] =
      ⟨⟨l2, l1⟩, ⟨l0, UInt64.ofBytes a b c d e f g h⟩⟩ := by
  simp only [Bytes.toB256.go]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · apply UInt64.spill_eight (h := 0)
    all_goals apply UInt64.shr56_lt
  · apply UInt64.spill_eight (h := 0)
    all_goals apply UInt64.shr56_lt
  · apply UInt64.spill_eight (h := 0)
    all_goals first | apply UInt64.shr56_lt | exact UInt8.toNat_lt _
  · exact UInt64.shiftIn_eight l0 a b c d e f g h

lemma Bytes.toB256_go_eight_cons (l3 l2 l1 l0 : UInt64) (a b c d e f g h : UInt8)
    (tail : Bytes) :
    Bytes.toB256.go l3 l2 l1 l0 (a :: b :: c :: d :: e :: f :: g :: h :: tail) =
      Bytes.toB256.go l2 l1 l0 (UInt64.ofBytes a b c d e f g h) tail := by
  have hs := Bytes.toB256_go_eight l3 l2 l1 l0 a b c d e f g h
  simp only [Bytes.toB256.go] at hs ⊢
  rcases Prod.mk.inj hs with ⟨hhi, hlo⟩
  rcases Prod.mk.inj hhi with ⟨h3, h2⟩
  rcases Prod.mk.inj hlo with ⟨h1, h0⟩
  rw [h3, h2, h1, h0]

lemma Bytes.toB256_go_append_toBytes (l3 l2 l1 l0 y : UInt64) (tail : Bytes) :
    Bytes.toB256.go l3 l2 l1 l0 (y.toBytes ++ tail) =
      Bytes.toB256.go l2 l1 l0 y tail := by
  simp only [UInt64.toBytes, UInt32.toBytes, UInt16.toBytes, List.cons_append, List.nil_append]
  rw [Bytes.toB256_go_eight_cons, UInt64.ofBytes_eq_toUInt64]
  exact congrArg (fun z => Bytes.toB256.go l2 l1 l0 z tail) (UInt64.toUInt64_toBytes y)

lemma B256.toB256_toBytes (x : B256) : x.toBytes.toB256 = x := by
  show Bytes.toB256.go 0 0 0 0 (B256.toBytes x) = ((x.1.1, x.1.2), (x.2.1, x.2.2))
  simp only [B256.toBytes, B128.toBytes, List.append_assoc]
  rw [Bytes.toB256_go_append_toBytes, Bytes.toB256_go_append_toBytes,
      Bytes.toB256_go_append_toBytes]
  rw [show x.2.2.toBytes = x.2.2.toBytes ++ [] by simp]
  rw [Bytes.toB256_go_append_toBytes]
  rfl

def IO.guard (φ : Prop) [Decidable φ] (msg : String) : IO Unit :=
  if φ then return () else IO.throw msg

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

def B256.min : B256 → B256 → B256
  | xs, ys => if xs ≤ ys then xs else ys
instance : Min B256 := ⟨.min⟩

def UInt8.toNibbles (x : UInt8) : List UInt8 := [x.highs, x.lows]
def UInt16.toNibbles (x : UInt16) : List UInt8 := x.highs.toNibbles ++ x.lows.toNibbles
def UInt32.toNibbles (x : UInt32) : List UInt8 := x.highs.toNibbles ++ x.lows.toNibbles
def UInt64.toNibbles (x : UInt64) : List UInt8 := x.highs.toNibbles ++ x.lows.toNibbles
def B128.toNibbles (x : B128) : List UInt8 := x.1.toNibbles ++ x.2.toNibbles
def B256.toNibbles (x : B256) : List UInt8 := x.1.toNibbles ++ x.2.toNibbles

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

lemma of_bind_eq_some {ξ υ} {f : Option ξ} {g : ξ → Option υ} {y} :
    f >>= g = some y → ∃ x, f = some x ∧ g x = some y := by
  intro h; cases f with
  | none => cases h
  | some x => refine ⟨x, rfl, h⟩

lemma of_pure_eq_some {ξ} {x y : ξ} : pure x = some y → x = y := by intro h; cases h; rfl

inductive Except.IsOk {ξ υ} : Except ξ υ → Prop
  | intro {x : υ} : Except.IsOk (Except.ok x)

inductive BLT : Type
  | bytes : Bytes → BLT
  | list : List BLT → BLT

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

  def Bytes.toBLTDiff? : Nat → Bytes → Option (BLT × Bytes)
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
      let rs ← Bytes.toBLTs? k rbs
      return ⟨.list rs, bs''⟩
    | ⟨1, 1, _, _, _, _, _, _⟩ => do
      let (rbs, bs') ← List.splitAt? (b - 0xC0).toNat bs
      let rs ← Bytes.toBLTs? k rbs
      return ⟨.list rs, bs'⟩

  def Bytes.toBLTs? : Nat → Bytes → Option (List BLT)
    | _, [] => some []
    | 0, _ :: _ => none
    | k + 1, bs@(_ :: _) => do
      let (r, bs') ← Bytes.toBLTDiff? (k + 1) bs
      let rs ← Bytes.toBLTs? k bs'
      return (r :: rs)

end

def Bytes.toBLT? (bs : Bytes) : Option BLT :=
  match Bytes.toBLTDiff? bs.length bs with
  | some (r, []) => some r
  | _ => none

mutual

  def BLT.toBytes : BLT → Bytes
    | .bytes [b] => if b < (0x80) then [b] else [0x81, b]
    | .bytes bs =>
      if bs.length < 56
      then (0x80 + bs.length.toUInt8) :: bs
      else let lbs : Bytes := bs.length.toBytesPack
           (0xB7 + lbs.length.toUInt8) :: (lbs ++ bs)
    | .list rs => BLTs.toBytes rs

  def BLTs.toBytesJoin : List BLT → Bytes
    | .nil => []
    | .cons r rs => r.toBytes ++ BLTs.toBytesJoin rs

  def BLTs.toBytes (rs : List BLT) : Bytes :=
    let bs := BLTs.toBytesJoin rs
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

def readJsonFile (filename : System.FilePath) : IO Lean.Json := do
  let contents ← IO.FS.readFile filename
  match Lean.Json.parse contents with
  | .ok json => pure json
  | .error err => throw (IO.userError err)

def B256.ltCheck  (x y : B256) : B256 := if x < y then 1 else 0
def B256.gtCheck  (x y : B256) : B256 := if x > y then 1 else 0
def B256.sltCheck (x y : B256) : B256 := if B256.Slt x y then 1 else 0
def B256.sgtCheck (x y : B256) : B256 := if B256.Sgt x y then 1 else 0
def B256.eqCheck  (x y : B256) : B256 := if x = y then 1 else 0

def ceilDiv (m n : Nat) := m / n + if m % n = 0 then 0 else 1

-- Inlined: these are three instructions each and sit in the SHA-256 and
-- RIPEMD-160 round loops, where the call overhead dominated the work.
@[inline] def UInt32.rol (x n : UInt32) : UInt32 :=
  x <<< n ||| (x >>> (32 - n))
@[inline] def UInt32.ror (x n : UInt32): UInt32 :=
  x >>> n ||| (x <<< (32 - n))

def B32s.toUInt64 (x y : UInt32) : UInt64 :=
  x.toUInt64 <<< 32 ||| y.toUInt64

def B32s.toB128 (x0 x1 y0 y1 : UInt32) : B128 :=
  ⟨B32s.toUInt64 x0 x1, B32s.toUInt64 y0 y1⟩

def B32s.toB256 (x0 x1 x2 x3 y0 y1 y2 y3: UInt32) : B256 :=
  ⟨B32s.toB128 x0 x1 x2 x3, B32s.toB128 y0 y1 y2 y3⟩

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
