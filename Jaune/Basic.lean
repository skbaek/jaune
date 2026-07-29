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

instance : @Zero Bool := ⟨false⟩
instance : @One Bool := ⟨true⟩

abbrev B8 : Type := UInt8
abbrev B16 : Type := UInt16
abbrev B32 : Type := UInt32
abbrev B64 : Type := UInt64
abbrev B8L : Type := List B8
abbrev B8A : Type := Array B8

instance : LinearOrder B8 where
  lt_iff_le_not_ge a b := Nat.lt_iff_le_and_not_ge
  le_refl a := Nat.le_refl _
  le_trans a b c h1 h2 := Nat.le_trans h1 h2
  le_antisymm a b h1 h2 := by
    rw [← UInt8.toNat_inj]
    apply Nat.le_antisymm h1 h2
  le_total a b := Nat.le_total (a.toNat) (b.toNat)
  toDecidableLE := λ a b => Nat.decLe _ _

instance : LinearOrder B16 where
  lt_iff_le_not_ge a b := Nat.lt_iff_le_and_not_ge
  le_refl a := Nat.le_refl _
  le_trans a b c h1 h2 := Nat.le_trans h1 h2
  le_antisymm a b h1 h2 := by
    rw [← UInt16.toNat_inj]
    apply Nat.le_antisymm h1 h2
  le_total a b := Nat.le_total (a.toNat) (b.toNat)
  toDecidableLE := λ a b => Nat.decLe _ _

instance : LinearOrder B32 where
  lt_iff_le_not_ge a b := Nat.lt_iff_le_and_not_ge
  le_refl a := Nat.le_refl _
  le_trans a b c h1 h2 := Nat.le_trans h1 h2
  le_antisymm a b h1 h2 := by
    rw [← UInt32.toNat_inj]
    apply Nat.le_antisymm h1 h2
  le_total a b := Nat.le_total (a.toNat) (b.toNat)
  toDecidableLE := λ a b => Nat.decLe _ _

instance : LinearOrder B64 where
  lt_iff_le_not_ge a b := Nat.lt_iff_le_and_not_ge
  le_refl a := Nat.le_refl _
  le_trans a b c h1 h2 := Nat.le_trans h1 h2
  le_antisymm a b h1 h2 := by
    rw [← UInt64.toNat_inj]
    apply Nat.le_antisymm h1 h2
  le_total a b := Nat.le_total (a.toNat) (b.toNat)
  toDecidableLE := λ a b => Nat.decLe _ _

def B8.highBit (x : B8) : Bool := (x &&& 0x80) != 0
def B8.lowBit (x : B8) : Bool := (x &&& 0x01) != 0

def B16.highBit (x : B16) : Bool := (x &&& 0x8000) != 0
def B16.lowBit  (x : B16) : Bool := (x &&& 0x0001) != 0

def B32.highBit (x : B32) : Bool := (x &&& 0x80000000) != 0
def B32.lowBit  (x : B32) : Bool := (x &&& 0x00000001) != 0

def B64.highBit (x : B64) : Bool := (x &&& 0x8000000000000000) != 0
def B64.lowBit  (x : B64) : Bool := (x &&& 0x0000000000000001) != 0

def B128 : Type := B64 × B64
deriving DecidableEq

instance : Inhabited B128 := ⟨⟨0, 0⟩⟩

def B256 : Type := B128 × B128
deriving DecidableEq

instance : Inhabited B256 := ⟨⟨Inhabited.default, Inhabited.default⟩⟩

def B128.highBit (x : B128) : Bool := x.1.highBit
def B128.lowBit  (x : B128) : Bool := x.2.lowBit

def B256.highBit (x : B256) : Bool := x.1.highBit
def B256.lowBit  (x : B256) : Bool := x.2.lowBit

def B64.max : B64 := 0xFFFFFFFFFFFFFFFF
def B128.max : B128 := ⟨.max, .max⟩
def B256.max : B256 := ⟨.max, .max⟩

instance {x y : B128} : Decidable (x = y) := by
  rw [show (x = y) ↔ (x.1 = y.1 ∧ x.2 = y.2) from Prod.ext_iff]
  apply instDecidableAnd

instance {x y : B256} : Decidable (x = y) := by
  rw [show (x = y) ↔ (x.1 = y.1 ∧ x.2 = y.2) from Prod.ext_iff]
  apply instDecidableAnd

def B128.LT (x y : B128) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)
instance : @LT B128 := ⟨B128.LT⟩
instance {x y : B128} : Decidable (x < y) := instDecidableOr

def B256.LT (x y : B256) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

instance : @LT B256 := ⟨B256.LT⟩
instance {x y : B256} : Decidable (x < y) := instDecidableOr

def Nat.toB32 : Nat → B32 := Nat.toUInt32
def Nat.toB64 : Nat → B64 := Nat.toUInt64
def B64.toNat : B64 → Nat := UInt64.toNat
def B32.toNat : B32 → Nat := UInt32.toNat

def Nat.toB128 (n : Nat) : B128 :=
  ⟨(n >>> 64).toB64, n.toB64⟩

def Nat.toB256 (n : Nat) : B256 :=
  ⟨(n >>> 128).toB128, n.toB128⟩

instance {n} : OfNat B128 n := ⟨n.toB128⟩
instance {n} : OfNat B256 n := ⟨n.toB256⟩

def B8.toHexit : B8 → Char
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

def B8.highs (x : B8) : B8 := (x >>> 4)
def B8.lows (x : B8) : B8 := (x &&& 0x0F)

def B8.toHex (x : B8) : String :=
  String.ofList [x.highs.toHexit, x.lows.toHexit]

def B8L.toHex (bs : B8L) : String :=
  List.foldr (λ b s => B8.toHex b ++ s) "" bs

def B8.toB16 (x : B8) : B16 := x.toUInt16
def B8.toB32 (x : B8) : B32 := x.toUInt32
def B8.toB64 (x : B8) : B64 := x.toUInt64

def B16.toB8 (x : B16) : B8 := x.toUInt8
def B16.toB32 (x : B16) : B32 := x.toUInt32
def B16.toB64 (x : B16) : B64 := x.toUInt64

def B32.toB8 (x : B32) : B8 := x.toUInt8
def B32.toB16 (x : B32) : B16 := x.toUInt16
def B32.toB64 (x : B32) : B64 := x.toUInt64

def B64.toB8 (x : B64) : B8 := x.toUInt8
def B64.toB16 (x : B64) : B16 := x.toUInt16
def B64.toB32 (x : B64) : B32 := x.toUInt32

def B16.highs (x : B16) : B8 := (x >>> 8).toB8
def B16.lows : B16 → B8 := B16.toB8
def B16.toHex (x : B16) : String := x.highs.toHex ++ x.lows.toHex

def B32.highs (x : B32) : B16 := (x >>> 16).toB16
def B32.lows : B32 → B16 := B32.toB16
def B32.toHex (x : B32) : String := x.highs.toHex ++ x.lows.toHex

def B64.highs (x : B64) : B32 := (x >>> 32).toB32
def B64.lows : B64 → B32 := B64.toB32
def B64.toHex (x : B64) : String := x.highs.toHex ++ x.lows.toHex

def B128.toHex (x : B128) : String := x.1.toHex ++ x.2.toHex
def B256.toHex (x : B256) : String := x.1.toHex ++ x.2.toHex

instance : ToString B8 := ⟨B8.toHex⟩
instance : ToString B16 := ⟨B16.toHex⟩
instance : ToString B32 := ⟨B32.toHex⟩
instance : ToString B64 := ⟨B64.toHex⟩
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
         then ⟨ (xs <<< os.toB64) ||| (ys >>> (64 - os).toB64),
                ys <<< os.toB64 ⟩
         else if os < 128
              then ⟨ys <<< (os - 64).toB64, 0⟩
              else ⟨0, 0⟩
instance : HShiftLeft B128 Nat B128 := ⟨B128.shiftLeft⟩

def B128.shiftRight : B128 → Nat → B128
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else if os < 64
         then ⟨ xs >>> os.toB64,
                (xs <<< (64 - os).toB64) ||| (ys >>> os.toB64) ⟩
         else if os < 128
              then ⟨0, xs >>> (os - 64).toB64⟩
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

def B8.toB256  (x : B8)  : B256 := ⟨0, ⟨0, x.toB64⟩⟩
def B16.toB256 (x : B16) : B256 := ⟨0, ⟨0, x.toB64⟩⟩
def B32.toB256 (x : B32) : B256 := ⟨0, ⟨0, x.toB64⟩⟩
def B64.toB256 (x : B64) : B256 := ⟨0, ⟨0, x⟩⟩

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
  let c : B64 := if x.2 < y.2 then 1 else 0
  ⟨(x.1 - y.1) - c, l⟩
instance : HSub B128 B128 B128 := ⟨B128.sub⟩

def B128.add (x y : B128) : B128 :=
  let l := x.2 + y.2
  let c : B64 := if l < x.2 then 1 else 0
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
def B64.smin : B64 := 0x8000000000000000
def B128.smin : B128 := ⟨.smin, 0⟩
def B256.smin : B256 := ⟨.smin, 0⟩

def B64.negOne  : B64  := .max
def B128.negOne : B128 := .max
def B256.negOne : B256 := .max

def Nat.toBool : Nat → Bool
  | 0 => 0
  | _ => 1

def B16.toB8L (x : B16) : B8L :=
  [(x >>> 8).toB8, x.toB8]

def B32.toB8L (x : B32) : B8L :=
  B16.toB8L (x >>> 16).toB16 ++ B16.toB8L x.toB16

def B64.toB8L (x : B64) : B8L :=
  B32.toB8L (x >>> 32).toB32 ++ B32.toB8L x.toB32

def B64.reverse (w : B64) : B64 :=
  ((w <<< 56) &&& (0xFF00000000000000 : B64)) |||
  ((w <<< 40) &&& (0x00FF000000000000 : B64)) |||
  ((w <<< 24) &&& (0x0000FF0000000000 : B64)) |||
  ((w <<< 8)  &&& (0x000000FF00000000 : B64)) |||
  ((w >>> 8)  &&& (0x00000000FF000000 : B64)) |||
  ((w >>> 24) &&& (0x0000000000FF0000 : B64)) |||
  ((w >>> 40) &&& (0x000000000000FF00 : B64)) |||
  ((w >>> 56) &&& (0x00000000000000FF : B64))

def B128.toB8L (x : B128) : B8L := x.1.toB8L ++ x.2.toB8L
def B256.toB8L (x : B256) : B8L := x.1.toB8L ++ x.2.toB8L

def List.ekat {ξ : Type u} (n : Nat) (xs : List ξ) : List ξ :=
  (xs.reverse.take n).reverse

def List.ekatD {ξ : Type u} (n : Nat) (xs : List ξ) (x : ξ) : List ξ :=
  (xs.reverse.takeD n x).reverse

def B8L.pack (xs : B8L) (n : Nat) : B8L := List.ekatD n xs 0

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
    let z : B8 := (B8L.pack y.toB8L 32)[32 - (x.toNat + 1)]
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
  | n + 1, _ :: xs => xs.drop? n

def List.take? {ξ : Type u} : Nat → List ξ → Option (List ξ)
  | 0, _ => some []
  | _ + 1, [] => none
  | n + 1, x :: xs => (x :: ·) <$> xs.take? n

def List.slice? {ξ : Type u} (xs : List ξ) (m n : Nat) : Option (List ξ) :=
  drop? m xs >>= take? n

def List.sliceD {ξ : Type u} (xs : List ξ) (m n : Nat) (x : ξ) : List ξ :=
  takeD n (drop m xs) x

def List.slice! {ξ : Type u} [Inhabited ξ] (xs : List ξ) (m n : Nat) : List ξ :=
  takeD n (drop m xs) default

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

def B64.teg (xs : B64) (n : Nat) : Bool :=
  ((xs >>> n.toB64) &&& 0x0000000000000001) != 0

def B128.teg (xs : B128) (n : Nat) : Bool :=
  if n < 64
  then xs.2.teg n
  else xs.1.teg (n - 64)

def B256.teg (xs : B256) (n : Nat) : Bool :=
  if n < 128
  then xs.2.teg n
  else xs.1.teg (n - 128)

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

def Hexit.toB4 : Char → Option B8
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
-- `(xy :: ·) <$> toB8L xs` shape overflows the stack past ~64 KB.
def B4L.toB8L.go : B8L → B8L → Option B8L
  | acc, [] => some acc.reverse
  | _, [_] => none
  | acc, x :: y :: xs => B4L.toB8L.go (((x <<< 4) ||| y) :: acc) xs

def B4L.toB8L (xs : B8L) : Option B8L := B4L.toB8L.go [] xs

def Hex.toB8L (s : String) : Option B8L :=
  s.toList.mapM Hexit.toB4 >>= B4L.toB8L

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

def B8.compareLows (x y : B8) : Ordering :=
  Ord.compare x.lows y.lows

def pad : String → String
  | s => "  " ++ s

def padMid : String -> String
  | s => "│ " ++ s

def padsMid : List String → List String
  | [] => []
  | s :: ss => ("├─" ++ s) :: ss.map padMid

def padsEnd : List String → List String
  | [] => []
  | s :: ss => ("└─" ++ s) :: ss.map pad

def padss : List (List String) -> List String
  | [] => []
  | [ss] => padsEnd ss
  | ss :: sss => padsMid ss ++ padss sss

def addComma (ss : List String) : Option (List String) :=
  let rec aux (s : String) : List String -> List String
    | [] => [s ++ ","]
    | s' :: ss' => s :: (aux s' ss')
  match ss with
  | [] => none
  | s :: ss' => some <| aux s ss'

def addCommas  (ss : List String) : List (List String) -> Option (List String)
  | [] => ss
  | ss' :: sss' => do
    let ssc ← addComma ss
    let ssc' ← addCommas ss' sss'
    ssc ++ ssc'

def fork (s : String) : List (List String) → List String
  | [[s']] => [s ++ "──" ++ s']
  | sss => s :: padss sss

def encloseStrings : List String → List String
  | [] => ["[]"]
  | [s] => ["[" ++ s ++ "]"]
  | ss => "┌─" :: ss.map padMid ++ ["└─"]

def List.toStrings {ξ} (f : ξ -> List String) (xs : List ξ) : List String :=
  encloseStrings (xs.map f).flatten

def B4L.toHex : B8L → String
  | [] => ""
  | [b] => String.ofList [b.toHexit]
  | b :: bs => String.ofList ([b.toHexit] ++ (toHex bs).toList)
def IO.throw {ξ} (s : String) : IO ξ := MonadExcept.throw <| IO.Error.userError s

def IO.remove0x (s : String) : IO String :=
  match s.toList with
  | '0' :: 'x' :: cs => return String.ofList cs
  | _ => IO.throw "prefix not 0x"

def Option.remove0x (s : String) : Option String :=
  match s.toList with
  | '0' :: 'x' :: cs => return String.ofList cs
  | _ => .none

def remove0x (s : String) : String :=
  match s.toList with
  | '0' :: 'x' :: cs => String.ofList cs
  | _ => s

def B8s.toB16 (a b : B8) : B16 :=
  let high : B16 := a.toB16
  let low : B16 := b.toB16
  (high <<< 8) ||| low

def B8s.toB32 (a b c d : B8) : B32 :=
  let a32 : B32 := a.toB32
  let b32 : B32 := b.toB32
  let c32 : B32 := c.toB32
  let d32 : B32 := d.toB32
  (a32 <<< 24) ||| (b32 <<< 16) ||| (c32 <<< 8) ||| d32

def B8s.toB64 (a b c d e f g h : B8) : B64 :=
  let a64 : B64 := a.toB64
  let b64 : B64 := b.toB64
  let c64 : B64 := c.toB64
  let d64 : B64 := d.toB64
  let e64 : B64 := e.toB64
  let f64 : B64 := f.toB64
  let g64 : B64 := g.toB64
  let h64 : B64 := h.toB64
  (a64 <<< 56) |||
  (b64 <<< 48) |||
  (c64 <<< 40) |||
  (d64 <<< 32) |||
  (e64 <<< 24) |||
  (f64 <<< 16) |||
  (g64 <<< 8)  |||
  h64



def B8L.toB16 (xs : B8L) : B16 :=
  let v := xs.pack 2
  let high : B16 := v[0]!.toB16
  let low : B16 := v[1]!.toB16
  (high <<< 8) ||| low

def B8L.toB32 (xs : B8L) : B32 :=
  let v := xs.pack 4
  let high : B32 := (B8L.toB16 (v.take 2)).toB32
  let low  : B32 := (B8L.toB16 (v.drop 2)).toB32
  (high <<< 16) ||| low

def B8L.toB64 (xs : B8L) : B64 :=
  let v := xs.pack 8
  let high : B64 := (B8L.toB32 (v.take 4)).toB64
  let low  : B64 := (B8L.toB32 (v.drop 4)).toB64
  (high <<< 32) ||| low

def B8L.toB64? (xs : B8L) : Option B64 :=
  if xs.length = 8 then some (B8L.toB64 xs) else none

def B8L.toB128Diff : B8L → Option (B128 × B8L)
  | x0 :: x1 :: x2 :: x3 ::
    x4 :: x5 :: x6 :: x7 ::
    y0 :: y1 :: y2 :: y3 ::
    y4 :: y5 :: y6 :: y7 :: xs =>
    some
      ⟨
        ⟨ B8s.toB64 x0 x1 x2 x3 x4 x5 x6 x7,
          B8s.toB64 y0 y1 y2 y3 y4 y5 y6 y7 ⟩,
        xs
      ⟩
  | _ => none

def B8L.toB256? (xs : B8L) : Option B256 := do
  let ⟨h, xs'⟩ ← xs.toB128Diff
  let ⟨l, []⟩ ← xs'.toB128Diff | none
  some ⟨h, l⟩

def Hex.toB64? (hx : String) : Option B64 := do
  Hex.toB8L hx >>= B8L.toB64?

def Hex.toB256? (hx : String) : Option B256 := do
  Hex.toB8L hx >>= B8L.toB256?

lemma B16.length_toB8L (x : B16) : x.toB8L.length = 2 := rfl
lemma B32.length_toB8L (x : B32) : x.toB8L.length = 4 := rfl
lemma B64.length_toB8L (x : B64) : x.toB8L.length = 8 := rfl
lemma B128.length_toB8L (x : B128) : x.toB8L.length = 16 := rfl
lemma B256.length_toB8L (w : B256) : w.toB8L.length = 32 := rfl

theorem List.takeD_eq_self {ξ : Type u} {n : ℕ} {xs : List ξ} (x : ξ)
    (h : n = xs.length) : List.takeD n xs x = xs := by
  rw [takeD_eq_take x <| le_of_eq h, take_of_length_le <| le_of_eq h.symm]

lemma B8L.pack_eq_self {xs n} (h : xs.length = n) : B8L.pack xs n = xs := by
  simp only [pack, List.ekatD]
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
      apply mul_le_mul_right; apply Nat.le_of_lt hy
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

def B8.toNat : B8 → Nat := UInt8.toNat
def B16.toNat : B16 → Nat := UInt16.toNat

lemma B16.toNat_inj {a b : B16} : a.toNat = b.toNat ↔ a = b := UInt16.toNat_inj
lemma B32.toNat_inj {a b : B32} : a.toNat = b.toNat ↔ a = b := UInt32.toNat_inj
lemma B64.toNat_inj {a b : B64} : a.toNat = b.toNat ↔ a = b := UInt64.toNat_inj

lemma B16.toNat_or (a b : B16) : (a ||| b).toNat = a.toNat ||| b.toNat := UInt16.toNat_or _ _
lemma B32.toNat_or (a b : B32) : (a ||| b).toNat = a.toNat ||| b.toNat := UInt32.toNat_or _ _
lemma B64.toNat_or (a b : B64) : (a ||| b).toNat = a.toNat ||| b.toNat := UInt64.toNat_or _ _

lemma B16.toNat_shiftRight (a b : B16) :
    (a >>> b).toNat = a.toNat >>> (b.toNat % 16) :=
  UInt16.toNat_shiftRight _ _
lemma B32.toNat_shiftRight (a b : B32) :
    (a >>> b).toNat = a.toNat >>> (b.toNat % 32) :=
  UInt32.toNat_shiftRight _ _
lemma B64.toNat_shiftRight (a b : B64) :
    (a >>> b).toNat = a.toNat >>> (b.toNat % 64) :=
  UInt64.toNat_shiftRight _ _

lemma B16.toNat_shiftLeft (a b : B16) :
    (a <<< b).toNat = a.toNat <<< (b.toNat % 16) ↾ 16 :=
  UInt16.toNat_shiftLeft _ _
lemma B32.toNat_shiftLeft (a b : B32) :
    (a <<< b).toNat = a.toNat <<< (b.toNat % 32) ↾ 32 :=
  UInt32.toNat_shiftLeft _ _

lemma B64.toNat_shiftLeft (a b : B64) :
    (a <<< b).toNat = a.toNat <<< (b.toNat % 64) ↾ 64 :=
  UInt64.toNat_shiftLeft _ _

lemma B16.toNat_mod (a b : B16) : (a % b).toNat = a.toNat % b.toNat := UInt16.toNat_mod _ _
lemma B32.toNat_mod (a b : B32) : (a % b).toNat = a.toNat % b.toNat := UInt32.toNat_mod _ _

lemma B64.toNat_mod (a b : B64) : (a % b).toNat = a.toNat % b.toNat := UInt64.toNat_mod _ _

lemma B16.toNat_lt {n : B16} : n.toNat < 2 ^ 16 :=
  UInt16.toNat_lt _

lemma toB16_toB8 (n : B16) : n.toB8.toB16 = n % 256 :=
  UInt16.toUInt16_toUInt8 _

lemma toB16_toB8L (x : B16) : x.toB8L.toB16 = x := by
  simp only [B16.toB8L, B8L.toB16]
  rw [B8L.pack_eq_self (by rfl)]

  simp


  rw [toB16_toB8]
  rw [toB16_toB8]

  rw [← B16.toNat_inj]
  rw [B16.toNat_or]
  rw [B16.toNat_shiftLeft]
  rw [B16.toNat_mod]
  rw [B16.toNat_shiftRight]

  apply high_or_low_eq_self _ _ B16.toNat_lt

lemma toB32_toB16 (n : B32) : n.toB16.toB32 = n % 65536 := UInt32.toUInt32_toUInt16 _
lemma toB64_toB32 (n : B64) : n.toB32.toB64 = n % 4294967296 := UInt64.toUInt64_toUInt32 _

lemma B32.toNat_lt {n : B32} : n.toNat < 2 ^ 32 := UInt32.toNat_lt _
lemma B64.toNat_lt {n : B64} : n.toNat < 2 ^ 64 := UInt64.toNat_lt _

lemma toB32_toB8L (x : B32) : x.toB8L.toB32 = x := by
  simp only [B32.toB8L, B8L.toB32]
  have h_len : ∀ {a b : B16}, List.length (a.toB8L ++ b.toB8L) = 4 := by
    intros; rw [List.length_append, B16.length_toB8L, B16.length_toB8L]
  rw [B8L.pack_eq_self h_len]
  rw [ List.take_length_append' (B16.length_toB8L _).symm,
       List.drop_length_append' (B16.length_toB8L _).symm ]
  rw [toB16_toB8L, toB16_toB8L]
  rw [toB32_toB16, toB32_toB16]
  rw [← B32.toNat_inj]
  rw [B32.toNat_or]
  rw [B32.toNat_shiftLeft]
  rw [B32.toNat_mod]
  rw [B32.toNat_shiftRight]
  apply high_or_low_eq_self
  apply B32.toNat_lt

lemma B64.toB64_toB8L (x : B64) : x.toB8L.toB64 = x := by
  simp only [B64.toB8L, B8L.toB64]
  have h_len : ∀ {a b : B32}, List.length (a.toB8L ++ b.toB8L) = 8 := by
    intros; rw [List.length_append, B32.length_toB8L, B32.length_toB8L]
  rw [B8L.pack_eq_self h_len]
  rw [ List.take_length_append' (B32.length_toB8L _).symm,
       List.drop_length_append' (B32.length_toB8L _).symm ]
  rw [toB32_toB8L, toB32_toB8L]
  rw [toB64_toB32, toB64_toB32]
  rw [← B64.toNat_inj]
  rw [B64.toNat_or]
  rw [B64.toNat_shiftLeft]
  rw [B64.toNat_mod]
  rw [B64.toNat_shiftRight]
  apply high_or_low_eq_self
  apply B64.toNat_lt

def B8L.toB128 (xs : B8L) : B128 :=
  let xs' := xs.pack 16
  let xh := xs'.take 8
  let xl := xs'.drop 8
  ⟨B8L.toB64 xh, B8L.toB64 xl⟩

-- Big-endian byte-list → word, as a single left-to-right pass over the four
-- 64-bit limbs: each byte is shifted into the low limb and the overflow of
-- every limb spills into the next. Bytes beyond the 32 most recent ones fall
-- off the top, so this agrees with the old `pack 32`-then-split codec on both
-- of its behaviors: left zero-extension of short lists, and truncation to the
-- last 32 bytes of long ones. No `pack`, `take`, `drop`, or reversal.
def B8L.toB256.go (l3 l2 l1 l0 : B64) : B8L → B256
  | [] => ⟨⟨l3, l2⟩, ⟨l1, l0⟩⟩
  | b :: bs =>
    go ((l3 <<< 8) ||| (l2 >>> 56))
       ((l2 <<< 8) ||| (l1 >>> 56))
       ((l1 <<< 8) ||| (l0 >>> 56))
       ((l0 <<< 8) ||| b.toB64)
       bs

def B8L.toB256 (xs : B8L) : B256 := B8L.toB256.go 0 0 0 0 xs

-- Equation lemmas for the codec: leading zero bytes are inert, and the short
-- concrete case that downstream proofs unfold. These replace the `pack`/`take`/
-- `drop` reasoning the old definition invited.
lemma B8L.toB256_zero_cons (xs : B8L) : B8L.toB256 (0 :: xs) = B8L.toB256 xs :=
  rfl

lemma B8L.toB256_pair (b0 b1 : B8) :
    B8L.toB256 [b0, b1] = ⟨⟨0, 0⟩, ⟨0, (b0.toB64 <<< 8) ||| b1.toB64⟩⟩ := by
  simp only [B8L.toB256, B8L.toB256.go, B8.toB64]
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

private lemma B64.small_shr_codec (x : B64) (hx : x.toNat < 2 ^ 8)
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

private lemma B64.toNat_shr56_lo (y : B64) :
    y.toNat >>> 56 = (y.toNat >>> 56) ↾ 8 := by
  rw [← Nat.lo_64_shr_56_codec]
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt B64.toNat_lt]

lemma B64.spill_eight (x y a b c d e f g h : B64)
    (ha : a.toNat < 2 ^ 8) (hb : b.toNat < 2 ^ 8)
    (hc : c.toNat < 2 ^ 8) (hd : d.toNat < 2 ^ 8)
    (he : e.toNat < 2 ^ 8) (hf : f.toNat < 2 ^ 8)
    (hg : g.toNat < 2 ^ 8) :
    let step (p : B64 × B64) (b : B64) :=
      ((p.1 <<< 8) ||| (p.2 >>> 56), (p.2 <<< 8) ||| b)
    (List.foldl step (x, y) [a, b, c, d, e, f, g, h]).1 = y := by
  dsimp only [List.foldl]
  have n8 : B64.toNat 8 % 64 = 8 := rfl
  have n56 : B64.toNat 56 % 64 = 56 := rfl
  rw [← B64.toNat_inj]
  simp only [B64.toNat_or, B64.toNat_shiftLeft, B64.toNat_shiftRight,
    n8, n56]
  simp only [Nat.lo_shl, Nat.shiftLeft_or_distrib, Nat.shiftRight_or_distrib]
  simp only [Nat.lo_or_codec]
  simp (disch := omega) only [Nat.lo_lo_of_le_codec]
  simp only [← Nat.shiftLeft_add]
  norm_num
  simp only [Nat.lo_64_shr_56_codec, Nat.shiftRight_or_distrib]
  simp (disch := omega) only [Nat.shl_shr_of_le_codec, B64.small_shr_codec,
    Nat.zero_shiftLeft, Nat.or_zero]
  norm_num
  rw [Nat.shl_lo_eq_zero_of_le (by omega), Nat.zero_or]
  rw [B64.toNat_shr56_lo]
  simp only [Nat.lo_zero_codec, Nat.or_zero]
  simp (disch := omega) only [Nat.lo_chunk_shl_codec]
  rw [Nat.or_assoc, Nat.or_assoc, Nat.or_assoc, Nat.or_assoc,
      Nat.or_assoc, Nat.or_assoc]
  rw [← Nat.lo_add, ← Nat.lo_add, ← Nat.lo_add, ← Nat.lo_add,
      ← Nat.lo_add, ← Nat.lo_add, ← Nat.lo_add]
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt B64.toNat_lt]

private lemma B64.shr56_lt (x : B64) : (x >>> 56).toNat < 2 ^ 8 := by
  rw [B64.toNat_shiftRight]
  change x.toNat >>> 56 < 2 ^ 8
  rw [B64.toNat_shr56_lo]
  exact Nat.lo_lt

lemma B64.shiftIn_eight (x : B64) (a b c d e f g h : B8) :
    ((((((((x <<< 8) ||| a.toB64) <<< 8 ||| b.toB64) <<< 8 ||| c.toB64)
       <<< 8 ||| d.toB64) <<< 8 ||| e.toB64) <<< 8 ||| f.toB64)
       <<< 8 ||| g.toB64) <<< 8 ||| h.toB64 =
      B8s.toB64 a b c d e f g h := by
  have widen (z : B8) : z.toB64.toNat = z.toNat := rfl
  have n8 : B64.toNat 8 % 64 = 8 := rfl
  have n16 : B64.toNat 16 % 64 = 16 := rfl
  have n24 : B64.toNat 24 % 64 = 24 := rfl
  have n32 : B64.toNat 32 % 64 = 32 := rfl
  have n40 : B64.toNat 40 % 64 = 40 := rfl
  have n48 : B64.toNat 48 % 64 = 48 := rfl
  have n56 : B64.toNat 56 % 64 = 56 := rfl
  rw [← B64.toNat_inj]
  simp only [B8s.toB64, B64.toNat_or, B64.toNat_shiftLeft,
    widen, n8, n16, n24, n32, n40, n48, n56]
  simp only [Nat.lo_shl, Nat.shiftLeft_or_distrib]
  simp only [Nat.lo_or_codec]
  simp (disch := omega) only [Nat.lo_lo_of_le_codec]
  simp only [← Nat.shiftLeft_add]
  norm_num
  rw [Nat.shl_lo_eq_zero_of_le (by omega)]
  simp

private lemma B8.toNat_toB16_shift8 (x : B8) :
    (x.toB16 <<< 8).toNat = x.toNat <<< 8 := by
  rw [B16.toNat_shiftLeft]
  change (x.toNat <<< 8) ↾ 16 = x.toNat <<< 8
  unfold B8.toNat
  exact Nat.lo_shl_eight_codec (UInt8.toNat_lt x) (by omega)

private lemma B16.toNat_toB32_shift16 (x : B16) :
    (x.toB32 <<< 16).toNat = x.toNat <<< 16 := by
  rw [B32.toNat_shiftLeft]
  change (x.toNat <<< 16) ↾ 32 = x.toNat <<< 16
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt, Nat.shiftLeft_eq]
  have hx := B16.toNat_lt (n := x)
  norm_num at hx ⊢
  omega

private lemma B32.toNat_toB64_shift32 (x : B32) :
    (x.toB64 <<< 32).toNat = x.toNat <<< 32 := by
  rw [B64.toNat_shiftLeft]
  change (x.toNat <<< 32) ↾ 64 = x.toNat <<< 32
  unfold Nat.lo
  rw [Nat.mod_eq_of_lt, Nat.shiftLeft_eq]
  have hx := B32.toNat_lt (n := x)
  norm_num at hx ⊢
  omega

private lemma B8s.toB16_nat (a b : B8) :
    (B8s.toB16 a b).toNat = (a.toNat <<< 8) ||| b.toNat := by
  simp only [B8s.toB16, B16.toNat_or, B8.toNat_toB16_shift8]
  rfl

lemma B8s.toB32_eq_halves (a b c d : B8) :
    B8s.toB32 a b c d =
      ((B8s.toB16 a b).toB32 <<< 16) ||| (B8s.toB16 c d).toB32 := by
  have widen8 (z : B8) : z.toB32.toNat = z.toNat := rfl
  have widen16 (z : B16) : z.toB32.toNat = z.toNat := rfl
  have n8 : B32.toNat 8 % 32 = 8 := rfl
  have n16 : B32.toNat 16 % 32 = 16 := rfl
  have n24 : B32.toNat 24 % 32 = 24 := rfl
  rw [← B32.toNat_inj]
  simp only [B8s.toB32, B32.toNat_or]
  rw [B16.toNat_toB32_shift16]
  simp only [widen16, B8s.toB16_nat, B32.toNat_shiftLeft,
    widen8, n8, n16, n24]
  unfold B8.toNat
  rw [Nat.lo_shl_eight_codec (UInt8.toNat_lt a) (by omega),
      Nat.lo_shl_eight_codec (UInt8.toNat_lt b) (by omega),
      Nat.lo_shl_eight_codec (UInt8.toNat_lt c) (by omega)]
  rw [Nat.shiftLeft_or_distrib]
  simp only [← Nat.shiftLeft_add]
  norm_num
  simp only [Nat.or_assoc]

private lemma B8s.toB32_nat (a b c d : B8) :
    (B8s.toB32 a b c d).toNat =
      (a.toNat <<< 24) ||| (b.toNat <<< 16) ||| (c.toNat <<< 8) ||| d.toNat := by
  rw [B8s.toB32_eq_halves]
  simp only [B32.toNat_or, B16.toNat_toB32_shift16]
  have widen16 (z : B16) : z.toB32.toNat = z.toNat := rfl
  simp only [widen16, B8s.toB16_nat]
  rw [Nat.shiftLeft_or_distrib]
  simp only [← Nat.shiftLeft_add]
  norm_num
  simp only [Nat.or_assoc]

lemma B8s.toB64_eq_halves (a b c d e f g h : B8) :
    B8s.toB64 a b c d e f g h =
      ((B8s.toB32 a b c d).toB64 <<< 32) ||| (B8s.toB32 e f g h).toB64 := by
  have widen8 (z : B8) : z.toB64.toNat = z.toNat := rfl
  have widen32 (z : B32) : z.toB64.toNat = z.toNat := rfl
  have n8 : B64.toNat 8 % 64 = 8 := rfl
  have n16 : B64.toNat 16 % 64 = 16 := rfl
  have n24 : B64.toNat 24 % 64 = 24 := rfl
  have n32 : B64.toNat 32 % 64 = 32 := rfl
  have n40 : B64.toNat 40 % 64 = 40 := rfl
  have n48 : B64.toNat 48 % 64 = 48 := rfl
  have n56 : B64.toNat 56 % 64 = 56 := rfl
  rw [← B64.toNat_inj]
  simp only [B8s.toB64, B64.toNat_or]
  rw [B32.toNat_toB64_shift32]
  simp only [widen32, B8s.toB32_nat, B64.toNat_shiftLeft,
    widen8, n8, n16, n24, n32, n40, n48, n56]
  unfold B8.toNat
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

lemma B8s.toB64_eq_toB64 (a b c d e f g h : B8) :
    B8s.toB64 a b c d e f g h = B8L.toB64 [a, b, c, d, e, f, g, h] := by
  rw [B8s.toB64_eq_halves]
  change
    ((B8s.toB32 a b c d).toB64 <<< 32) ||| (B8s.toB32 e f g h).toB64 =
      ((B8L.toB32 [a, b, c, d]).toB64 <<< 32) |||
        (B8L.toB32 [e, f, g, h]).toB64
  rw [B8s.toB32_eq_halves, B8s.toB32_eq_halves]
  rfl

lemma B8L.toB256_go_eight (l3 l2 l1 l0 : B64) (a b c d e f g h : B8) :
    B8L.toB256.go l3 l2 l1 l0 [a, b, c, d, e, f, g, h] =
      ⟨⟨l2, l1⟩, ⟨l0, B8s.toB64 a b c d e f g h⟩⟩ := by
  simp only [B8L.toB256.go]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_)
  · apply B64.spill_eight (h := 0)
    all_goals apply B64.shr56_lt
  · apply B64.spill_eight (h := 0)
    all_goals apply B64.shr56_lt
  · apply B64.spill_eight (h := 0)
    all_goals first | apply B64.shr56_lt | exact UInt8.toNat_lt _
  · exact B64.shiftIn_eight l0 a b c d e f g h

lemma B8L.toB256_go_eight_cons (l3 l2 l1 l0 : B64) (a b c d e f g h : B8)
    (tail : B8L) :
    B8L.toB256.go l3 l2 l1 l0 (a :: b :: c :: d :: e :: f :: g :: h :: tail) =
      B8L.toB256.go l2 l1 l0 (B8s.toB64 a b c d e f g h) tail := by
  have hs := B8L.toB256_go_eight l3 l2 l1 l0 a b c d e f g h
  simp only [B8L.toB256.go] at hs ⊢
  rcases Prod.mk.inj hs with ⟨hhi, hlo⟩
  rcases Prod.mk.inj hhi with ⟨h3, h2⟩
  rcases Prod.mk.inj hlo with ⟨h1, h0⟩
  rw [h3, h2, h1, h0]

lemma B8L.toB256_go_append_toB8L (l3 l2 l1 l0 y : B64) (tail : B8L) :
    B8L.toB256.go l3 l2 l1 l0 (y.toB8L ++ tail) =
      B8L.toB256.go l2 l1 l0 y tail := by
  simp only [B64.toB8L, B32.toB8L, B16.toB8L, List.cons_append, List.nil_append]
  rw [B8L.toB256_go_eight_cons, B8s.toB64_eq_toB64]
  exact congrArg (fun z => B8L.toB256.go l2 l1 l0 z tail) (B64.toB64_toB8L y)

lemma B256.toB256_toB8L (x : B256) : x.toB8L.toB256 = x := by
  show B8L.toB256.go 0 0 0 0 (B256.toB8L x) = ((x.1.1, x.1.2), (x.2.1, x.2.2))
  simp only [B256.toB8L, B128.toB8L, List.append_assoc]
  rw [B8L.toB256_go_append_toB8L, B8L.toB256_go_append_toB8L,
      B8L.toB256_go_append_toB8L]
  rw [show x.2.2.toB8L = x.2.2.toB8L ++ [] by simp]
  rw [B8L.toB256_go_append_toB8L]
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

def Array.copyD {ξ : Type u} (xs ys : Array ξ) : Array ξ :=
  let f : (Array ξ × Nat) → ξ → (Array ξ × Nat) :=
    λ ysn x => ⟨Array.set! ysn.fst ysn.snd x, ysn.snd + 1⟩
  (Array.foldl f ⟨ys, 0⟩ xs).fst

def ByteArray.sliceD (xs : ByteArray) : Nat → Nat → B8 → B8L
  | _, 0, _ => []
  | m, n + 1, d =>
    if m < xs.size
    then xs.get! m :: ByteArray.sliceD xs (m + 1) n d
    else List.replicate (n + 1) d

lemma ByteArray.length_sliceD (xs : ByteArray) (m n : Nat) (d : B8) :
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

def B8.toB4s (x : B8) : List B8 := [x.highs, x.lows]
def B16.toB4s (x : B16) : List B8 := x.highs.toB4s ++ x.lows.toB4s
def B32.toB4s (x : B32) : List B8 := x.highs.toB4s ++ x.lows.toB4s
def B64.toB4s (x : B64) : List B8 := x.highs.toB4s ++ x.lows.toB4s
def B128.toB4s (x : B128) : List B8 := x.1.toB4s ++ x.2.toB4s
def B256.toB4s (x : B256) : List B8 := x.1.toB4s ++ x.2.toB4s

def B8L.toB4s : B8L → B8L
  | [] => []
  | x :: xs => x.toB4s ++ B8L.toB4s xs

abbrev B32L : Type := List B32
abbrev B32A : Type := Array B32

def List.splitAt? {ξ : Type u} (n : Nat) (xs : List ξ) : Option (List ξ × List ξ) :=
  let rec aux : Nat → List ξ →  List ξ → Option (List ξ × List ξ)
    | 0, xs, ys => some (xs.reverse, ys)
    | _ + 1, _, [] => none
    | n + 1, xs, y :: ys => aux n (y :: xs) ys
  aux n [] xs

def B8L.toNat (bs : B8L) : Nat :=
  let rec aux (acc : Nat) : B8L → Nat
    | [] => acc
    | b :: bs => aux ((acc * 256) + b.toNat) bs
  aux 0 bs

def Nat.toB8 (n : Nat) : B8 := n.toUInt8
def Nat.toB16 (n : Nat) : B16 := n.toUInt16

def Nat.toB8L (n : Nat) : B8L :=
  let rec aux (acc : B8L) : Nat → B8L
  | 0 => acc
  | n@(_ + 1) => aux ((n % 256).toB8 :: acc) (n / 256)
  aux [] n

def Nat.toB8LPack : Nat → B8L
  | 0 => [0]
  | n@(_ + 1) => n.toB8L

def Except.assert (p : Prop) [inst : Decidable p]
  {ξ : Type u} (x : ξ) : Except ξ Unit :=
  if p then .ok () else .error x

def Option.toExcept {ξ : Type u} {υ : Type v} (x : ξ) : Option υ → Except ξ υ
  | .none => .error x
  | .some y => .ok y

inductive BLT : Type
  | b8s : B8L → BLT
  | list : List BLT → BLT

def B8.toBools (x0 : B8) :
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

  def B8L.toBLTDiff? : Nat → B8L → Option (BLT × B8L)
    | _, [] => none
    | 0, _ :: _ => none
    | k + 1, b :: bs =>
      match b.toBools with
    | ⟨0, _, _, _, _, _, _, _⟩ => some (.b8s [b], bs)
    | ⟨1, 0, 1, 1, 1, _, _, _⟩ => do
      let (lbs, bs') ← List.splitAt? (b - 0xB7).toNat bs
      let (rbs, bs'') ← List.splitAt? (B8L.toNat lbs) bs'
      return ⟨.b8s rbs, bs''⟩
    | ⟨1, 0, _, _, _, _, _, _⟩ =>
      .map .b8s id <$> List.splitAt? (b - 0x80).toNat bs
    | ⟨1, 1, 1, 1, 1, _, _, _⟩ => do
      let (lbs, bs') ← List.splitAt? (b - 0xF7).toNat bs
      let (rbs, bs'') ← List.splitAt? (B8L.toNat lbs) bs'
      let rs ← B8L.toBLTs? k rbs
      return ⟨.list rs, bs''⟩
    | ⟨1, 1, _, _, _, _, _, _⟩ => do
      let (rbs, bs') ← List.splitAt? (b - 0xC0).toNat bs
      let rs ← B8L.toBLTs? k rbs
      return ⟨.list rs, bs'⟩

  def B8L.toBLTs? : Nat → B8L → Option (List BLT)
    | _, [] => some []
    | 0, _ :: _ => none
    | k + 1, bs@(_ :: _) => do
      let (r, bs') ← B8L.toBLTDiff? (k + 1) bs
      let rs ← B8L.toBLTs? k bs'
      return (r :: rs)

end

def B8L.toBLT? (bs : B8L) : Option BLT :=
  match B8L.toBLTDiff? bs.length bs with
  | some (r, []) => some r
  | _ => none

mutual

  def BLT.toB8L : BLT → B8L
    | .b8s [b] => if b < (0x80) then [b] else [0x81, b]
    | .b8s bs =>
      if bs.length < 56
      then (0x80 + bs.length.toB8) :: bs
      else let lbs : B8L := bs.length.toB8LPack
           (0xB7 + lbs.length.toB8) :: (lbs ++ bs)
    | .list rs => BLTs.toB8L rs

  def BLTs.toB8LsJoin : List BLT → B8L
    | .nil => []
    | .cons r rs => r.toB8L ++ BLTs.toB8LsJoin rs

  def BLTs.toB8L (rs : List BLT) : B8L :=
    let bs := BLTs.toB8LsJoin rs
    let len := bs.length
    if len < 56
    then (0xC0 + len.toB8) :: bs
    else let lbs : B8L := len.toB8LPack
         (0xF7 + lbs.length.toB8) :: (lbs ++ bs)

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

mutual

  def BLT.toStrings : BLT → List String
    | .b8s bs => fork "[B8L]" [(List.chunks 31 bs).map B8L.toHex]
    | .list rs => fork "[LIST]" (BLTs.toStringss rs)

  def BLTs.toStringss : List BLT → List (List String)
    | [] => []
    | r :: rs => r.toStrings :: BLTs.toStringss rs

end

instance : ToString BLT := ⟨String.joinln ∘ BLT.toStrings⟩

def readJsonFile (filename : System.FilePath) : IO Lean.Json := do
  let contents ← IO.FS.readFile filename
  match Lean.Json.parse contents with
  | .ok json => pure json
  | .error err => throw (IO.userError err)

mutual

  partial def StringJson.toStrings : (String × Lean.Json) → List String
    | ⟨n, j⟩ =>
      (fork n [Lean.Json.toStrings j])

  partial def StringJsons.toStrings : List ((_ : String) × Lean.Json) → List String
    | [] => []
    | ⟨n, j⟩ :: njs =>
      (fork n [Lean.Json.toStrings j]) ++ StringJsons.toStrings njs

  partial def Lean.Jsons.toStrings : List Lean.Json → List String
    | [] => []
    | j :: js => Lean.Json.toStrings j ++ Lean.Jsons.toStrings js

  partial def Lean.Json.toStrings : Lean.Json → List String
    | .null => ["NULL"]
    | .bool b => [s!"BOOL : {b}"]
    | .num n => [s!"NUM : {n}"]
    | .str s =>
       fork "STR" [s.chunks 80]
    | .arr js =>
      fork "ARR" (js.toList.map Lean.Json.toStrings)
    | .obj m => do
      let kvs := m.toArray.toList
      fork "OBJ" (kvs.map StringJson.toStrings)

end

def Lean.Json.toString (j : Lean.Json) : String := String.joinln j.toStrings

def B256.lt_check  (x y : B256) : B256 := if x < y then 1 else 0
def B256.gt_check  (x y : B256) : B256 := if x > y then 1 else 0
def B256.slt_check (x y : B256) : B256 := if B256.Slt x y then 1 else 0
def B256.sgt_check (x y : B256) : B256 := if B256.Sgt x y then 1 else 0
def B256.eq_check  (x y : B256) : B256 := if x = y then 1 else 0

def ceilDiv (m n : Nat) := m / n + if m % n = 0 then 0 else 1

-- Inlined: these are three instructions each and sit in the SHA-256 and
-- RIPEMD-160 round loops, where the call overhead dominated the work.
@[inline] def B32.rol (x n : B32) : B32 :=
  x <<< n ||| (x >>> (32 - n))
@[inline] def B32.ror (x n : B32): B32 :=
  x >>> n ||| (x <<< (32 - n))

def B32s.toB64 (x y : B32) : B64 :=
  x.toB64 <<< 32 ||| y.toB64

def B32s.toB128 (x0 x1 y0 y1 : B32) : B128 :=
  ⟨B32s.toB64 x0 x1, B32s.toB64 y0 y1⟩

def B32s.toB256 (x0 x1 x2 x3 y0 y1 y2 y3: B32) : B256 :=
  ⟨B32s.toB128 x0 x1 x2 x3, B32s.toB128 y0 y1 y2 y3⟩

def List.splitToArray {ξ : Type u}
  (sz : Nat) (xs : List ξ) (x : ξ) : Array ξ × List ξ :=
  let rec aux : Nat → Array ξ → Nat → List ξ → Array ξ × List ξ
    | _, array, _, [] => ⟨array, []⟩
    | _, array, 0, list => ⟨array, list⟩
    | idx, array, sz + 1, item :: list =>
      aux (idx + 1) (array.set! idx item) sz list
  aux 0 (.replicate sz x) sz xs

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

/-- Global verbosity flag, set once at startup (see `main`). Threading a `vb :
Bool` through every execution definition was noise, so it lives here instead. -/
initialize verbosityRef : IO.Ref Bool ← IO.mkRef false

@[never_extract] unsafe def verboseImpl (_ : Unit) : Bool :=
  unsafeBaseIO verbosityRef.get

/-- Ambient verbosity flag. Logically the constant `false`; at runtime it reads
`verbosityRef`, which `main` sets once from `--verbose` before any execution
runs. Three precautions keep the read from being evaluated before `main` sets
the flag (which would lock in the `mkRef` default forever):

1. The `Unit` argument — a nullary `def` would be a CAF, forced once at
   module-load time.
2. `@[never_extract]` on `verboseImpl` — otherwise the compiler lifts the
   closed term `verboseImpl ()` out of function bodies into a module-init
   constant (closed-term extraction), evaluating it at load time.
3. `@[never_extract]` on `verbose` and `cprint` — same protection at the
   source level, e.g. for the closed subterm `cprint "some literal"`.

Note `never_extract` is shallow: it protects terms that *directly mention* the
marked constant. A fully-closed application further up the call chain (e.g.
`f 42` where `f` transitively calls `cprint`) would still be extracted and
init-evaluated with verbosity off. Fine here, since every execution call takes
runtime data. Also keep the set-once discipline: do not mutate `verbosityRef`
after startup, or pure readers see inconsistent values. -/
@[never_extract, implemented_by verboseImpl] def verbose (_ : Unit) : Bool :=
  false

@[never_extract]
def cprint {m : Type → Type v}  [inst : Monad m] (msg : String) : m Unit := do
  if verbose () then do
    dbg_trace msg

def Except.print {ξ : Type} (msg : String) : Except ξ Unit := do
  dbg_trace msg
