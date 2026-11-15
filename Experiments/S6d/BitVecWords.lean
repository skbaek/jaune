import Jaune.WordFacts
import Experiments.S6d.Timing

/-!
# jsn-s6d: EVM words as `BitVec 256` (experiment; never lands)

`W := BitVec 256` with EVM-exact operations, and the S6d theorem set restated over it.
Each theorem `S6d.V.<name>` mirrors a `B256` theorem (`S6d.B.<name>` in
`Experiments/S6d/B256Words.lean`, which is the current Jaune proof or a fresh one).

EVM-exactness of the operations is checked against the u256 oracle vectors by
`Experiments/S6d/Bench.lean` (`s6d-bench`), not proved here.

Where `BitVec`'s own operator is not the EVM operation, the EVM one is a named wrapper:
`BitVec`'s `x % 0 = x` and `srem x 0 = x`, while EVM `MOD`/`SMOD` give `0`.
-/

set_option linter.unusedSimpArgs false
set_option Elab.async false

namespace S6d

abbrev W := BitVec 256

namespace W

def ofNat (n : Nat) : W := BitVec.ofNat 256 n

/-- EVM `MOD`: zero divisor gives zero (`BitVec.umod x 0 = x`). -/
def mod (x y : W) : W := if y = 0 then 0 else x % y
/-- EVM `SDIV`: `BitVec.sdiv` already gives `0` at a zero divisor and `intMin` at `intMin / -1`. -/
def sdiv (x y : W) : W := BitVec.sdiv x y
/-- EVM `SMOD`: sign of the dividend, zero divisor gives zero. -/
def smod (x y : W) : W := if y = 0 then 0 else BitVec.srem x y
def addmod (x y z : W) : W := if z = 0 then 0 else ofNat ((x.toNat + y.toNat) % z.toNat)
def mulmod (x y z : W) : W := if z = 0 then 0 else ofNat ((x.toNat * y.toNat) % z.toNat)
def exp (x y : W) : W := ofNat (Jaune.Nat.powMod x.toNat y.toNat (2 ^ 256))
/-- EVM `SIGNEXTEND b y`: sign-extend from byte `b` (counted from the low end). -/
def signext (b y : W) : W :=
  if b.toNat < 31 then (y.setWidth (8 * (b.toNat + 1))).signExtend 256 else y
def isNeg (x : W) : Bool := x.msb
def smin : W := BitVec.intMin 256
def negOne : W := BitVec.allOnes 256
def sar (x : W) (n : Nat) : W := x.sshiftRight n
def eqCheck (x y : W) : W := if x = y then 1 else 0
def ltCheck (x y : W) : W := if x < y then 1 else 0
def gtCheck (x y : W) : W := if x > y then 1 else 0
def sltCheck (x y : W) : W := if x.slt y then 1 else 0
def sgtCheck (x y : W) : W := if y.slt x then 1 else 0

/-- The `k` low base-256 digits of `n`, most significant first. -/
def digits : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => digits k (n / 256) ++ [(n % 256).toUInt8]

/-- Big-endian 32-byte encoding. -/
def toBytes (x : W) : List UInt8 := digits 32 x.toNat

/-- No-overflow predicates, as in Jaune. -/
def Nof (x y : W) : Prop := x.toNat + y.toNat < 2 ^ 256
def Nofm (x y : W) : Prop := x.toNat * y.toNat < 2 ^ 256

end W

/-- Big-endian decoding; bytes beyond the last 32 fall off the top, as in `Bytes.toB256`. -/
def bytesToW (xs : List UInt8) : W := W.ofNat (xs.foldl (fun n b => n * 256 + b.toNat) 0)

namespace V
open W

/-! ## A. Nat bridge -/

s6d_time theorem toNat_lt (x : W) : x.toNat < 2 ^ 256 := x.isLt

s6d_time theorem toNat_inj (xs ys : W) (eq : xs.toNat = ys.toNat) : xs = ys := BitVec.eq_of_toNat_eq eq

s6d_time theorem toNat_ofNat (n : Nat) : (W.ofNat n).toNat = n % 2 ^ 256 := BitVec.toNat_ofNat _ _

s6d_time theorem toNat_ofNat_of_lt {n : Nat} (h : n < 2 ^ 256) : (W.ofNat n).toNat = n := by
  rw [toNat_ofNat, Nat.mod_eq_of_lt h]

s6d_time theorem toNat_mul (x y : W) : (x * y).toNat = (x.toNat * y.toNat) % 2 ^ 256 :=
  BitVec.toNat_mul _ _

s6d_time theorem toNat_mod {x y : W} (h : y ≠ 0) : (W.mod x y).toNat = x.toNat % y.toNat := by
  rw [W.mod, if_neg h, BitVec.toNat_umod]

s6d_time theorem toNat_add (x y : W) : (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 256 :=
  BitVec.toNat_add _ _

s6d_time theorem toNat_add_eq_of_nof (x y : W) (h : W.Nof x y) : (x + y).toNat = x.toNat + y.toNat := by
  rw [toNat_add, Nat.mod_eq_of_lt h]

s6d_time theorem toNat_sub_eq_of_le (xs ys : W) (h : ys ≤ xs) : (xs - ys).toNat = xs.toNat - ys.toNat := by
  rw [BitVec.le_def] at h
  rw [BitVec.toNat_sub]
  have := ys.isLt
  rw [show 2 ^ 256 - ys.toNat + xs.toNat = (xs.toNat - ys.toNat) + 2 ^ 256 by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by have := xs.isLt; omega)]

s6d_time theorem toNat_div {x y : W} (_h : y ≠ 0) : (x / y).toNat = x.toNat / y.toNat :=
  BitVec.toNat_udiv

/-! ## B. Order -/

s6d_time theorem toNat_lt_toNat {a b : W} (h : a < b) : a.toNat < b.toNat := BitVec.lt_def.mp h

s6d_time theorem lt_iff_toNat_lt_toNat {a b : W} : a < b ↔ a.toNat < b.toNat := BitVec.lt_def

s6d_time theorem le_iff_toNat_le_toNat {a b : W} : a ≤ b ↔ a.toNat ≤ b.toNat := BitVec.le_def

/-! ## C. Comparison flags -/

s6d_time theorem one_ne_zero : (1 : W) ≠ 0 := by decide

s6d_time theorem eqCheck_ne_zero_iff {x y : W} : W.eqCheck x y ≠ 0 ↔ x = y := by
  unfold W.eqCheck
  by_cases h : x = y <;> simp [h]

s6d_time theorem ltCheck_ne_zero_iff {x y : W} : W.ltCheck x y ≠ 0 ↔ x < y := by
  unfold W.ltCheck
  by_cases h : x < y <;> simp [h]

s6d_time theorem gtCheck_eq_zero_iff {x y : W} : W.gtCheck x y = 0 ↔ ¬ y < x := by
  unfold W.gtCheck
  by_cases h : y < x <;> simp [h]

s6d_time theorem ltCheck_eq_zero_of_toNat_le {x y : W} (h : y.toNat ≤ x.toNat) : W.ltCheck x y = 0 := by
  simp [W.ltCheck, BitVec.lt_def]; omega

s6d_time theorem gtCheck_ne_zero_of_toNat_lt {x y : W} (h : y.toNat < x.toNat) : W.gtCheck x y ≠ 0 := by
  simp [W.gtCheck, BitVec.lt_def, h]

/-! ## D. Bytes -/

s6d_time theorem length_digits (k n : Nat) : (W.digits k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [W.digits, ih]

s6d_time theorem length_toBytes (x : W) : (W.toBytes x).length = 32 := length_digits _ _

s6d_time theorem foldl_digits (k n : Nat) :
    (W.digits k n).foldl (fun n b => n * 256 + b.toNat) 0 = n % 256 ^ k := by
  induction k generalizing n with
  | zero => simp [W.digits, Nat.mod_one]
  | succ k ih =>
    simp only [W.digits, List.foldl_append, ih, List.foldl_cons, List.foldl_nil,
      Nat.toUInt8, UInt8.toNat_ofNat']
    rw [show (2 : Nat) ^ 8 = 256 from rfl, Nat.mod_mod, Nat.pow_succ,
      Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]
    omega

s6d_time theorem toW_toBytes (x : W) : bytesToW (W.toBytes x) = x := by
  apply BitVec.eq_of_toNat_eq
  have hx : x.toNat < 256 ^ 32 := x.isLt
  rw [bytesToW, W.toBytes, foldl_digits, toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt x.isLt]

s6d_time theorem toW_pair (n : Nat) (n_lt : n < 2 ^ 16) :
    bytesToW [(n >>> 8).toUInt8, n.toUInt8] = W.ofNat n := by
  simp only [bytesToW, List.foldl_cons, List.foldl_nil, Nat.toUInt8, UInt8.toNat_ofNat',
    Nat.shiftRight_eq_div_pow]
  congr 1
  omega

/-! ## E. Bit and sign -/

s6d_time theorem toNat_shiftRight (x : W) (n : Nat) : (x >>> n).toNat = x.toNat / 2 ^ n := by
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

s6d_time theorem toNat_shiftLeft (x : W) (n : Nat) : (x <<< n).toNat = x.toNat * 2 ^ n % 2 ^ 256 := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

s6d_time theorem sdiv_smin_negOne : W.sdiv W.smin W.negOne = W.smin := by
  have : W.negOne = -1#256 := by decide
  rw [W.sdiv, this, W.smin, BitVec.intMin_sdiv_neg_one]

s6d_time theorem sdiv_of_nonneg {x y : W} (hx : W.isNeg x = false) (hy : W.isNeg y = false) :
    W.sdiv x y = x / y := by
  simp only [W.isNeg] at hx hy
  rw [W.sdiv, BitVec.sdiv_eq, hx, hy]; rfl

s6d_time theorem sar_of_nonneg {x : W} (hx : W.isNeg x = false) (n : Nat) : W.sar x n = x >>> n :=
  BitVec.sshiftRight_eq_of_msb_false hx

/-! ## F. MulDiv word bridges -/

s6d_time theorem toNat_ne_zero {z : W} (h : z ≠ 0) : z.toNat ≠ 0 := by
  intro hz; exact h (BitVec.eq_of_toNat_eq (by simp [hz]))

s6d_time theorem nofm_iff_le_div {y : W} (hy : y ≠ 0) (x : W) :
    W.Nofm x y ↔ x.toNat ≤ (2 ^ 256 - 1) / y.toNat := by
  rw [W.Nofm, Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero (toNat_ne_zero hy))]
  omega

s6d_time theorem toNat_mul_eq_of_nofm {x y : W} (h : W.Nofm x y) : (x * y).toNat = x.toNat * y.toNat := by
  rw [toNat_mul, Nat.mod_eq_of_lt h]

s6d_time theorem toNat_mulmod {x y z : W} (h : z ≠ 0) :
    (W.mulmod x y z).toNat = x.toNat * y.toNat % z.toNat := by
  rw [W.mulmod, if_neg h, toNat_ofNat_of_lt
    (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero (toNat_ne_zero h))) z.isLt)]

s6d_time theorem toNat_addmod {x y z : W} (h : z ≠ 0) :
    (W.addmod x y z).toNat = (x.toNat + y.toNat) % z.toNat := by
  rw [W.addmod, if_neg h, toNat_ofNat_of_lt
    (Nat.lt_trans (Nat.mod_lt _ (Nat.pos_of_ne_zero (toNat_ne_zero h))) z.isLt)]

end V
end S6d
