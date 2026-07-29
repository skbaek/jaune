-- Types.lean : types used by both executable and abstract semantics of EVM and Blanc.

import Jaune.Basic
import Std.Data.TreeMap.Lemmas



def Adr : Type := B32 × B128

def Adr.toNat (x : Adr) : Nat :=
  (x.1.toNat <<< 128) ||| x.2.toNat

def Nat.toAdr (n : Nat) : Adr :=
  ⟨(n >>> 128).toB32, n.toB128⟩

instance {n} : OfNat Adr n := ⟨n.toAdr⟩

lemma toNat_toB16 {n : ℕ} : B16.toNat n.toB16 = n ↾ 16 := UInt16.toNat_ofNat
lemma toNat_toB32 {n : ℕ} : B32.toNat n.toB32 = n ↾ 32 := UInt32.toNat_ofNat
lemma toNat_toB64 {n : ℕ} : B64.toNat (n.toB64) = n ↾ 64 := UInt64.toNat_ofNat

lemma Nat.lo_lo_of_le {k m n : Nat} (le : m ≤ n) :
    (k ↾ m) ↾ n = k ↾ m := mod_mod_of_dvd' <| Nat.pow_dvd_pow _ le

lemma Nat.lo_lo_of_ge {k m n : Nat} (ge : m ≥ n) :
    (k ↾ m) ↾ n = k ↾ n := mod_mod_of_dvd _ <| Nat.pow_dvd_pow _ ge

lemma Nat.hi_or_lo (a b : Nat) : a ↿ b ||| a ↾ b = a := by
  simp only [Nat.hi, Nat.lo]
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  rw [← @Nat.add_eq_or b, Nat.div_add_mod']
  · apply Nat.dvd_mul_left
  · apply Nat.mod_lt _ (Nat.pow_pos _); omega

lemma Nat.or_eq_lo_add {k m n : Nat} :
    (k >>> n ↾ m) <<< n ||| k ↾ n = k ↾ (m + n) := by
  rw [← @Nat.lo_add_shr k m n]
  rw [← @Nat.lo_lo_of_ge k (m + n) n (by omega)]
  apply Nat.hi_or_lo

lemma toNat_toB128 (n : Nat) : n.toB128.toNat = n ↾ 128 := by
  simp only [Nat.toB128, B128.toNat]; rw [toNat_toB64, toNat_toB64]
  apply Nat.or_eq_lo_add

lemma Nat.div_two_pow_mod_two_pow (k m n : Nat) :
    (k / (2 ^ m)) % (2 ^ n) = (k % (2 ^ (m + n))) / (2 ^ m) := by
  induction m generalizing k n with
  | zero => simp
  | succ m ih =>
    have h : (k / 2 ^ (m + 1)) = ((k / 2) / 2 ^ m) := by
      rw [Nat.pow_succ, Nat.mul_comm, Nat.div_div_eq_div_mul]
    rw [h, ih]; clear h
    rw [Nat.pow_succ, Nat.mul_comm, ← Nat.div_div_eq_div_mul]
    have h : m + 1 + n = m + n + 1 := by omega
    rw [h]; clear h
    apply congr_arg₂ _ _ rfl
    rw [Nat.mod_two_pow_succ]
    rw [@Nat.add_div _ _ 2 (by omega), if_neg]
    · rw [Nat.mod_div_self, Nat.mul_div_cancel _ (by omega)]; rfl
    · simp [Nat.mul_mod_left, Nat.mod_lt]

lemma Nat.toNat_toAdr (n : Nat) : n.toAdr.toNat = n ↾ 160 := by
  simp only [Nat.toAdr, Adr.toNat]; rw [toNat_toB32, toNat_toB128]
  apply Nat.or_eq_lo_add
--
-- lemma B64.toNat_mul_add_toNat_lt_size (x y : B64) :
--     x.toNat * (2 ^ 64) + y.toNat < 2 ^ 128 := by
--   have h : 2 ^ 128 = (UInt64.size - 1) * (2 ^ 64) + UInt64.size := by rfl
--   rw [h]; clear h
--   apply Nat.add_lt_add_of_le_of_lt _ (UInt64.toNat_lt_size _)
--   apply Nat.mul_le_mul_right
--   apply @Nat.le_pred_of_lt _ (UInt64.size) <| UInt64.toNat_lt_size _


lemma toB32_toNat {x : B32} : x.toNat.toB32 = x := UInt32.ofNat_toNat

lemma toB32_or (a b : Nat) : (a ||| b).toB32 = a.toB32 ||| b.toB32 :=
  UInt32.ofNat_or a b

lemma toB64_or (a b : Nat) : (a ||| b).toB64 = a.toB64 ||| b.toB64 :=
  UInt64.ofNat_or a b

lemma B128.or_eq (x y : B128) :
  x ||| y = ⟨x.1 ||| y.1, x.2 ||| y.2⟩ := rfl

lemma toB128_or (a b : Nat) : (a ||| b).toB128 = a.toB128 ||| b.toB128 := by
  simp only [Nat.toB128]
  rw [B128.or_eq, toB64_or, Nat.shiftRight_or_distrib, toB64_or]

lemma Nat.shiftLeft_lt_of_lt {a b n : Nat} (h : a < 2 ^ n) :
    (a <<< b) < (2 ^ (n + b)) := by
  rw [Nat.shiftLeft_eq, Nat.pow_add]
  apply Nat.mul_lt_mul_of_pos_right h (Nat.pow_pos (by omega))

lemma B128.toNat_lt {x : B128} : x.toNat < 2 ^ 128 := by
  simp only [B128.toNat]; apply Nat.or_lt_two_pow
  · apply Nat.shiftLeft_lt_of_lt B64.toNat_lt
  · apply lt_trans B64.toNat_lt; omega

lemma B256.toNat_lt (x : B256) : x.toNat < 2 ^ 256 := by
  simp only [B256.toNat]; apply Nat.or_lt_two_pow
  · apply Nat.shiftLeft_lt_of_lt B128.toNat_lt
  · apply lt_trans B128.toNat_lt; omega

lemma B64.zero_or {x : B64} : (0 ||| x) = x := UInt64.zero_or

lemma B128.zero_or {x : B128} : (0 ||| x) = x := by
  rw [B128.or_eq]; apply Prod.ext <;> exact B64.zero_or

lemma Nat.add_div_of_dvd {a b c : Nat} (c_pos : 0 < c) (c_dvd : c ∣ a)  :
    (a + b) / c = a / c + b / c := by
  rw [Nat.add_div c_pos, if_neg, Nat.add_zero]
  rw [not_le, Nat.mod_eq_zero_of_dvd c_dvd, Nat.zero_add]
  apply Nat.mod_lt _ c_pos

lemma Nat.div_eq_zero_of_lt {k x : Nat} (h : x < k) : x / k = 0 := by
  rw [Nat.div_eq_zero_iff_lt (by omega)]; apply h

lemma Nat.add_div_of_dvd_of_lt' {a b c : Nat} (c_dvd : c ∣ a) (b_lt : b < c) :
    (a + b) / c = a / c := by
  rw [Nat.add_div_of_dvd (zero_lt_of_lt b_lt) c_dvd]
  simp [Nat.div_eq_zero_of_lt b_lt]

lemma toB64_add (a b : Nat) :
    (a + b).toB64 = a.toB64 + b.toB64 := UInt64.ofNat_add a b

lemma B64.lt_iff_toNat_lt {a b : B64} : a < b ↔ a.toNat < b.toNat :=
  UInt64.lt_iff_toNat_lt

lemma B8.toNat_add (a b : B8) : (a + b).toNat = (a.toNat + b.toNat) ↾ 8 :=
  UInt8.toNat_add a b

lemma B64.toNat_add (a b : B64) : (a + b).toNat = (a.toNat + b.toNat) ↾ 64 :=
  UInt64.toNat_add a b

lemma Nat.lo_eq_of_lt {a b : ℕ} (h : a < (2 ^ b)) : a ↾ b = a :=
  Nat.mod_eq_of_lt h

lemma Nat.add_mod_eq_add_sub {k m n : Nat} (m_lt : m < k)
    (n_lt : n < k) (k_le : k ≤ m + n) : (m + n) % k = m + n - k := by
  rcases Nat.exists_eq_add_of_le k_le with ⟨d, eq⟩
  rw [eq, Nat.add_mod_left]
  have d_lt : d < k := by
    rw [← @Nat.add_lt_add_iff_left k, ← eq]
    apply Nat.add_lt_add m_lt n_lt
  simp [Nat.mod_eq_of_lt d_lt]

lemma B64.toNat_overflow {x y : B64} :
    x + y < x ↔ 2 ^ 64 ≤ x.toNat + y.toNat := by
  rw [B64.lt_iff_toNat_lt, B64.toNat_add]
  by_cases h : x.toNat + y.toNat < 2 ^ 64
  · rw [Nat.lo_eq_of_lt h]
    apply iff_of_false <;> omega
  · rw [not_lt] at h; apply iff_of_true _ h
    have x_lt := @B64.toNat_lt x
    have y_lt := @B64.toNat_lt y
    rw [Nat.lo, Nat.add_mod_eq_add_sub x_lt y_lt h]
    omega

lemma ite_distrib {α β} {f : α → β} {p : Prop} [Decidable p] {a b : α} :
    f (if p then a else b) = if p then f a else f b := by
  by_cases h : p <;> simp [h]

lemma ite_eq_ite_of_iff {α} {p q : Prop} [Decidable p] [Decidable q]
    {a b c d : α} (pq : p ↔ q) (ac : a = c) (bd : b = d) :
    (if p then a else b) = (if q then c else d) := by
  rw [ac, bd]; by_cases h : p
  · rw [if_pos h, if_pos (pq.mp h)]
  · rw [if_neg h, if_neg (mt pq.mpr h)]

lemma toB128_add (a b : Nat) : (a + b).toB128 = a.toB128 + b.toB128 := by
  simp only [Nat.toB128, Nat.shiftRight_eq_div_pow]
  rw [Nat.add_div (by omega)]; apply congr_arg₂ _ _ (toB64_add _ _)
  simp only [toB64_add]; apply congr_arg₂ _ rfl
  apply Eq.trans ite_distrib <| ite_eq_ite_of_iff _ rfl rfl
  rw [← Nat.lo, ← Nat.lo, B64.toNat_overflow, toNat_toB64, toNat_toB64]

lemma toB64_toNat (x : B64) : x.toNat.toB64 = x :=
  UInt64.ofNat_toNat

lemma B64.ofNat_eq_iff_mod_eq_toNat (a : Nat) (b : B64) :
    a.toB64 = b ↔ a ↾ 64 = b.toNat :=
  UInt64.ofNat_eq_iff_mod_eq_toNat a b

lemma Nat.lo_lo {m n : Nat} : (m ↾ n) ↾ n = m ↾ n :=
  Nat.mod_mod _ _

lemma lo_toB64 (n : Nat) : (n ↾ 64).toB64 = n.toB64 := by
  rw [← B64.toNat_inj, toNat_toB64, toNat_toB64, Nat.lo_lo]

lemma Nat.or_lo {k m n : Nat} : (m ||| n) ↾ k = (m ↾ k) ||| (n ↾ k) :=
  Nat.or_mod_two_pow

lemma toB128_toNat (x : B128) : x.toNat.toB128 = x := by
  simp only [B128.toNat, Nat.toB128]
  apply congr_arg₂
  · rw [Nat.shiftRight_or_distrib, Nat.shiftLeft_shiftRight]
    rw [Nat.shiftRight_eq_zero _ _ B64.toNat_lt, Nat.or_zero, toB64_toNat]
  · rw [← lo_toB64, Nat.or_lo, Nat.shl_lo_eq_zero_of_le (by omega)]
    rw [Nat.zero_or, lo_toB64, toB64_toNat]

lemma B128.toNat_inj (xs ys : B128) : xs.toNat = ys.toNat ↔ xs = ys := by
  constructor <;> intro h
  · rw [← toB128_toNat xs, ← toB128_toNat ys, h]
  · simp [h]

lemma lo_toB128 (n : Nat) : (n ↾ 128).toB128 = n.toB128 := by
  rw [← B128.toNat_inj, toNat_toB128, toNat_toB128, Nat.lo_lo]

--lemma toB128_eq_iff_mod_eq_toNat (a : Nat) (b : B128) :
lemma toB128_eq_iff_lo_eq_toNat (a : Nat) (b : B128) :
    a.toB128 = b ↔ a ↾ 128 = b.toNat := by
  constructor <;> intro h
  · rw [← h, toNat_toB128]
  · rw [← B128.toNat_inj, ← h, toNat_toB128]

lemma B128.zero_1 : (0 : B128).1 = 0 := rfl
lemma B128.zero_2 : (0 : B128).2 = 0 := rfl

lemma B128.sub_eq (x y : B128) :
  x - y = ⟨(x.1 - y.1) - (if x.2 < y.2 then 1 else 0), x.2 - y.2⟩ := rfl

lemma B256.sub_eq (x y : B256) :
  x - y = ⟨(x.1 - y.1) - (if x.2 < y.2 then 1 else 0), x.2 - y.2⟩ := rfl

lemma B128.add_eq (x y : B128) :
  x + y = ⟨x.1 + y.1 + if x.2 + y.2 < x.2 then 1 else 0, x.2 + y.2⟩ := rfl

lemma B256.add_eq (x y : B256) :
  x + y = ⟨x.1 + y.1 + if x.2 + y.2 < x.2 then 1 else 0, x.2 + y.2⟩ := rfl

lemma B128.zero_add (n : B128) : 0 + n = n := by
  rw [B128.add_eq];
  simp only [
    show ((0 : B128).1) = 0 from rfl, _root_.zero_add,
    show ((0 : B128).2) = 0 from rfl,
    UInt64.not_lt_zero, ↓reduceIte, add_zero, Prod.mk.eta
  ]

lemma toB256_toNat (x : B256) : x.toNat.toB256 = x := by
  simp only [B256.toNat, Nat.toB256]
  apply congr_arg₂
  · rw [Nat.shiftRight_or_distrib, Nat.shiftLeft_shiftRight]
    rw [Nat.shiftRight_eq_zero _ _ B128.toNat_lt, Nat.or_zero, toB128_toNat]
  · rw [← lo_toB128, Nat.or_lo, Nat.shl_lo_eq_zero_of_le (by omega)]
    rw [Nat.zero_or, lo_toB128, toB128_toNat]

theorem B256.toNat_inj (xs ys : B256) (eq : xs.toNat = ys.toNat) : xs = ys := by
  rw [← toB256_toNat xs, ← toB256_toNat ys, eq]

/-
The `toNat` characterization of the `Nat`-routed word operations: the
interface downstream developments consume instead of unfolding definitions.
-/

theorem B256.toNat_toB256 (n : Nat) : (Nat.toB256 n).toNat = n ↾ 256 := by
  simp only [Nat.toB256, B256.toNat]; rw [toNat_toB128, toNat_toB128]
  apply Nat.or_eq_lo_add

theorem B256.toNat_toB256_of_lt {n : Nat} (h : n < 2 ^ 256) :
    (Nat.toB256 n).toNat = n := by rw [B256.toNat_toB256, Nat.lo_eq_of_lt h]

theorem B256.toNat_mul (x y : B256) :
    (x * y).toNat = (x.toNat * y.toNat) ↾ 256 := B256.toNat_toB256 _

theorem B256.div_zero (x : B256) : x / 0 = 0 := by
  show (B256.divMod x 0).fst = 0; rw [B256.divMod, if_pos rfl]

theorem B256.mod_zero (x : B256) : x % 0 = 0 := by
  show (B256.divMod x 0).snd = 0; rw [B256.divMod, if_pos rfl]

theorem B256.toNat_div {x y : B256} (h : y ≠ 0) :
    (x / y).toNat = x.toNat / y.toNat := by
  show (B256.divMod x y).fst.toNat = _
  rw [B256.divMod, if_neg h]
  exact B256.toNat_toB256_of_lt
    (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (B256.toNat_lt x))

theorem B256.toNat_mod {x y : B256} (h : y ≠ 0) :
    (x % y).toNat = x.toNat % y.toNat := by
  show (B256.divMod x y).snd.toNat = _
  rw [B256.divMod, if_neg h]
  exact B256.toNat_toB256_of_lt
    (Nat.lt_of_le_of_lt (Nat.mod_le _ _) (B256.toNat_lt x))

theorem Nat.powMod.go_eq {m : Nat} (hm : 1 < m) :
    ∀ e b res, res < m → Nat.powMod.go m e b res = res * b ^ e % m := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro b res hres
    match e with
    | 0 => rw [Nat.powMod.go]; rw [Nat.pow_zero, Nat.mul_one, Nat.mod_eq_of_lt hres]
    | n + 1 =>
      rw [Nat.powMod.go]
      have hlt : (n + 1) / 2 < n + 1 := Nat.div_lt_self (by omega) (by omega)
      have hres' : (if (n + 1) % 2 = 1 then res * b % m else res) < m := by
        split
        · exact Nat.mod_lt _ (by omega)
        · exact hres
      rw [ih _ hlt _ _ hres']
      rw [Nat.mul_mod _ (((b * b) % m) ^ ((n + 1) / 2)), ← Nat.pow_mod]
      rw [show b * b = b ^ 2 from (Nat.pow_two b).symm, ← Nat.pow_mul]
      rw [← Nat.mul_mod]
      rcases Nat.mod_two_eq_zero_or_one n with he | he
      · -- n even, so n + 1 is odd
        have hpar : (n + 1) % 2 = 1 := by omega
        have hk : 2 * ((n + 1) / 2) = n := by omega
        rw [if_pos hpar, hk, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]
        rw [Nat.mul_assoc, ← Nat.pow_succ']
      · -- n odd, so n + 1 is even
        have hpar : ¬ ((n + 1) % 2 = 1) := by omega
        have hk : 2 * ((n + 1) / 2) = n + 1 := by omega
        rw [if_neg hpar, hk]

theorem Nat.powMod_eq {b e m : Nat} (hm : 1 < m) :
    Nat.powMod b e m = b ^ e % m := by
  unfold Nat.powMod
  rw [if_neg (by omega), Nat.powMod.go_eq hm _ _ _ hm, Nat.one_mul]

theorem B256.toNat_bexp (x y : B256) :
    (x ^ y).toNat = (x.toNat ^ y.toNat) ↾ 256 := by
  show (B256.bexp x y).toNat = _
  rw [B256.bexp, B256.toNat_toB256, Nat.powMod_eq (by omega)]
  exact Nat.mod_mod _ _

lemma B128.lt_or_eq_of_le {n m : B128} (h : n ≤ m) : n < m ∨ n = m := by
  rcases h with h | h
  · left; left; apply h
  · rcases UInt64.lt_or_eq_of_le h.2 with h' | h'
    · left; right; refine ⟨h.1, h'⟩
    · right; apply Prod.ext h.1 h'

lemma B256.lt_or_eq_of_le {n m : B256} (h : n ≤ m) : n < m ∨ n = m := by
  rcases h with h | h
  · left; left; apply h
  · rcases B128.lt_or_eq_of_le h.2 with h' | h'
    · left; right; refine ⟨h.1, h'⟩
    · right; apply Prod.ext h.1 h'

lemma B64.le_of_lt {a b : B64} : a < b → a ≤ b := UInt64.le_of_lt

lemma B128.le_refl (x : B128) : x ≤ x := by
  right; refine ⟨rfl, UInt64.le_refl _⟩

lemma B256.le_refl (x : B256) : x ≤ x := by
  right; refine ⟨rfl, B128.le_refl _⟩

lemma B128.le_of_lt_or_eq {n m : B128} (h : n < m ∨ n = m) : n ≤ m := by
  rcases h with (h | ⟨h, h'⟩) | h
  · left; apply h
  · right; refine' ⟨h, B64.le_of_lt h'⟩
  · rw [h]; apply le_refl

lemma B128.lt_iff (x y : B128) :
  x < y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)) := Iff.refl _

lemma B256.lt_iff (x y : B256) :
  x < y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)) := Iff.refl _

lemma B128.le_iff (x y : B128) :
    x ≤ y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)) := Iff.refl _

lemma B256.le_iff (x y : B256) :
    x ≤ y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)) := Iff.refl _

lemma B128.le_iff_lt_or_eq {n m : B128} : n ≤ m ↔ (n < m ∨ n = m) :=
  ⟨B128.lt_or_eq_of_le, B128.le_of_lt_or_eq⟩

lemma B128.le_or_gt (a b : B128) : a ≤ b ∨ a > b := by
  simp [GT.gt]; rw [B128.le_iff, B128.lt_iff];
  rcases UInt64.le_or_lt a.1 b.1 with h | h
  · rcases UInt64.lt_or_eq_of_le h with h' | h'
    · left; left; apply h'
    · rcases UInt64.le_or_lt a.2 b.2 with h'' | h''
      · left; right; refine ⟨h', h''⟩
      · right; right; refine ⟨h'.symm, h''⟩
  · right; left; apply h

lemma B128.lt_or_ge (a b : B128) : a < b ∨ a ≥ b :=
  Or.symm <| B128.le_or_gt _ _

lemma B256.le_or_gt (a b : B256) : a ≤ b ∨ a > b := by
  simp [GT.gt]; rw [B256.le_iff, B128.lt_iff];
  rcases B128.le_or_gt a.1 b.1 with h | h
  · rcases B128.lt_or_eq_of_le h with h' | h'
    · left; left; apply h'
    · rcases B128.le_or_gt a.2 b.2 with h'' | h''
      · left; right; refine ⟨h', h''⟩
      · right; right; refine ⟨h'.symm, h''⟩
  · right; left; apply h

lemma Nat.lt_of_lt_high {sz high low high' low' : Nat}
    (h_high : high < high') (h_low : low < sz) :
    high * sz + low < high' * sz + low' := by
  rcases high' with _ | high'
  · cases Nat.not_lt_zero _ h_high
  · have h_le := Nat.le_of_lt_succ h_high
    rw [Nat.succ_mul, Nat.add_assoc]
    apply @Nat.add_lt_add_of_le_of_lt
    · apply Nat.mul_le_mul_right _ h_le
    · apply Nat.lt_add_right _ h_low

lemma Nat.shl_or_lt_shl_or_of_left {k m n m' n' : Nat}
    (m_lt_m' : m < m') (n_lt : n < 2 ^ k) (n'_lt : n' < 2 ^ k) :
    m <<< k ||| n < m' <<< k ||| n' := by
  rw [← Nat.add_eq_or two_pow_dvd_shl n_lt]
  rw [← Nat.add_eq_or two_pow_dvd_shl n'_lt]
  simp only [Nat.shiftLeft_eq]
  apply lt_of_lt_high m_lt_m' n_lt

lemma Nat.shl_or_lt_shl_or_of_right {k m n n' : Nat}
    (n_lt : n < n') (n'_lt : n' < 2 ^ k) :
    m <<< k ||| n < m <<< k ||| n' := by
  rw [← Nat.add_eq_or two_pow_dvd_shl (lt_trans n_lt n'_lt)]
  rw [← Nat.add_eq_or two_pow_dvd_shl n'_lt]
  simp only [Nat.shiftLeft_eq]
  rw [Nat.add_lt_add_iff_left]; apply n_lt

lemma B128.toNat_lt_toNat {a b : B128} (h : a < b) :
    a.toNat < b.toNat := by
  rcases a with ⟨_, _⟩; rcases b with ⟨_, _⟩
  rcases h with h | h <;> simp at h
  · rw [B64.lt_iff_toNat_lt] at h
    apply Nat.shl_or_lt_shl_or_of_left h B64.toNat_lt B64.toNat_lt
  · rw [h.1]; apply Nat.shl_or_lt_shl_or_of_right _ B64.toNat_lt
    rw [← B64.lt_iff_toNat_lt]; apply h.2

lemma B128.toNat_le_toNat {a b : B128} (h : a ≤ b) : a.toNat ≤ b.toNat := by
  rcases B128.lt_or_eq_of_le h with h | h
  · apply Nat.le_of_lt <| B128.toNat_lt_toNat h
  · rw [h]

lemma B128.lt_of_toNat_lt_toNat {a b : B128} (lt : a.toNat < b.toNat) : a < b := by
  rcases B128.le_or_gt b a with h | h
  · cases not_le_of_gt lt <| B128.toNat_le_toNat h
  · apply h

lemma B128.lt_iff_toNat_lt_toNat {a b : B128} : a < b ↔ a.toNat < b.toNat := by
  constructor
  · apply B128.toNat_lt_toNat
  · apply B128.lt_of_toNat_lt_toNat

lemma B256.toNat_lt_toNat {a b : B256} (h : a < b) :
    a.toNat < b.toNat := by
  rcases a with ⟨_, _⟩; rcases b with ⟨_, _⟩
  rcases h with h | h <;> simp at h
  · rw [B128.lt_iff_toNat_lt_toNat] at h
    apply Nat.shl_or_lt_shl_or_of_left h B128.toNat_lt B128.toNat_lt
  · rw [h.1]; apply Nat.shl_or_lt_shl_or_of_right _ B128.toNat_lt
    rw [← B128.lt_iff_toNat_lt_toNat]; apply h.2

lemma B128.le_of_lt {a b : B128} (h : a < b) : a ≤ b := by
  rcases h with h | h
  · left; apply h
  · right; refine' ⟨h.1, UInt64.le_of_lt h.2⟩

lemma B256.le_of_lt {a b : B256} (h : a < b) : a ≤ b := by
  rcases h with h | h
  · left; apply h
  · right; refine' ⟨h.1, B128.le_of_lt h.2⟩

lemma B256.le_of_lt_or_eq {n m : B256} (h : n < m ∨ n = m) : n ≤ m := by
  rcases h with (h | ⟨h, h'⟩) | h
  · left; apply h
  · right; refine' ⟨h, B128.le_of_lt h'⟩
  · rw [h]; apply le_refl

lemma B256.le_iff_lt_or_eq {n m : B256} : n ≤ m ↔ (n < m ∨ n = m) :=
  ⟨B256.lt_or_eq_of_le, B256.le_of_lt_or_eq⟩

lemma B256.toNat_le_toNat {a b : B256} (h : a ≤ b) : a.toNat ≤ b.toNat := by
  rcases B256.lt_or_eq_of_le h with h | h
  · apply Nat.le_of_lt <| B256.toNat_lt_toNat h
  · rw [h]

lemma B256.lt_of_toNat_lt_toNat {a b : B256} (lt : a.toNat < b.toNat) : a < b := by
  rcases B256.le_or_gt b a with h | h
  · cases not_le_of_gt lt <| B256.toNat_le_toNat h
  · apply h

lemma B256.lt_iff_toNat_lt_toNat {a b : B256} : a < b ↔ a.toNat < b.toNat := by
  constructor
  · apply B256.toNat_lt_toNat
  · apply B256.lt_of_toNat_lt_toNat

lemma B128.not_lt {a b : B128} : ¬ a < b ↔ b ≤ a := by
  simp [B128.lt_iff, B128.le_iff]
  rw [@Eq.comm _ a.1 b.1, @UInt64.le_iff_lt_or_eq b.1 a.1]
  aesop

lemma B128.lt_irrefl (x : B128) : ¬ x < x := by
  intro h; rcases h with h | h <;> simp at h

lemma B256.lt_irrefl (x : B256) : ¬ x < x := by
  intro h; rcases h with h | h <;> simp [B128.lt_irrefl] at h

lemma B256.not_lt {a b : B256} : ¬ a < b ↔ b ≤ a := by
  simp [B256.lt_iff, B256.le_iff, B128.not_lt]
  rw [@Eq.comm _ a.1 b.1, @B128.le_iff_lt_or_eq b.1 a.1]
  by_cases h : b.1 < a.1 <;> simp [h] <;> intro h'
  · rw [h'] at h; cases B128.lt_irrefl _ h
  · apply Or.inl h'

lemma B128.not_le {a b : B128} : ¬ a ≤ b ↔ b < a := by
  rw [not_iff_comm, B128.not_lt]

lemma B256.not_le {a b : B256} : ¬ a ≤ b ↔ b < a := by
  rw [not_iff_comm, B256.not_lt]

lemma B128.le_iff_toNat_le_toNat {a b : B128} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [← not_iff_not, not_le, Nat.not_le, lt_iff_toNat_lt_toNat]

lemma B256.le_iff_toNat_le_toNat {a b : B256} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [← not_iff_not, not_le, Nat.not_le, lt_iff_toNat_lt_toNat]

lemma B128.le_of_toNat_le_toNat {a b : B128} : a.toNat ≤ b.toNat → a ≤ b :=
  B128.le_iff_toNat_le_toNat.mpr

lemma B256.le_of_toNat_le_toNat {a b : B256} : a.toNat ≤ b.toNat → a ≤ b :=
  B256.le_iff_toNat_le_toNat.mpr

lemma Nat.lo_add_lo (m n k : ℕ) : (m ↾ k + n) ↾ k = (m + n) ↾ k :=
  Nat.mod_add_mod _ _ _

lemma B128.toNat_add (x y : B128) :
    (x + y).toNat = (x.toNat + y.toNat) ↾ 128 := by
  rw [B128.add_eq]; simp only [B128.toNat]
  rw [Nat.shl_or_add_shl_or_lo_add B64.toNat_lt B64.toNat_lt]
  apply congr_arg₂ _ (congr_arg₂ _ _ rfl) (B64.toNat_add _ _)
  rw [B64.toNat_add, B64.toNat_add, Nat.lo_add_lo]
  apply congr_arg₂ _ (congr_arg₂ _ rfl _) rfl
  rw [← ite_not, @ite_distrib _ _ B64.toNat]
  apply ite_eq_ite_of_iff _ rfl rfl
  simp [B64.toNat_overflow]

lemma B128.toNat_overflow {x y : B128} :
    x + y < x ↔ 2 ^ 128 ≤ x.toNat + y.toNat := by
  rw [B128.lt_iff_toNat_lt_toNat, B128.toNat_add]
  by_cases h : x.toNat + y.toNat < 2 ^ 128
  · rw [Nat.lo_eq_of_lt h]
    apply iff_of_false <;> omega
  · rw [_root_.not_lt] at h; apply iff_of_true _ h
    have x_lt := @B128.toNat_lt x
    have y_lt := @B128.toNat_lt y
    rw [Nat.lo, Nat.add_mod_eq_add_sub x_lt y_lt h]
    omega

lemma toB256_add (a b : Nat) : (a + b).toB256 = a.toB256 + b.toB256 := by
  simp only [Nat.toB256, Nat.shiftRight_eq_div_pow]
  rw [Nat.add_div (by omega)]; apply congr_arg₂ _ _ (toB128_add _ _)
  simp only [toB128_add]; apply congr_arg₂ _ rfl
  apply Eq.trans ite_distrib <| ite_eq_ite_of_iff _ rfl rfl
  rw [← Nat.lo, ← Nat.lo, B128.toNat_overflow, toNat_toB128, toNat_toB128]

lemma B256.toNat_add (x y : B256) :
    (x + y).toNat = (x.toNat + y.toNat) ↾ 256 := by
  rw [B256.add_eq]; simp only [B256.toNat]
  rw [Nat.shl_or_add_shl_or_lo_add B128.toNat_lt B128.toNat_lt]
  apply congr_arg₂ _ (congr_arg₂ _ _ rfl) (B128.toNat_add _ _)
  rw [B128.toNat_add, B128.toNat_add, Nat.lo_add_lo]
  apply congr_arg₂ _ (congr_arg₂ _ rfl _) rfl
  rw [← ite_not, @ite_distrib _ _ B128.toNat]
  apply ite_eq_ite_of_iff _ rfl rfl
  simp [B128.toNat_overflow]

theorem B256.add_comm {xs ys : B256} : xs + ys = ys + xs := by
  apply B256.toNat_inj
  rw [B256.toNat_add, B256.toNat_add, Nat.add_comm]

lemma toB32_toB64 (n : B32) : n.toB64.toB32 = n :=
  UInt32.toUInt32_toUInt64 n

def B256.toAdr (x : B256) : Adr := ⟨x.1.2.toB32, x.2⟩

def Adr.toB256 (a : Adr) : B256 := ⟨⟨0, a.1.toB64⟩, a.2⟩

lemma toAdr_toB256 (a : Adr) : a.toB256.toAdr = a := by
  simp [Adr.toB256, B256.toAdr, toB32_toB64]

theorem Adr.toB256_inj {x y : Adr} (eq : x.toB256 = y.toB256) : x = y := by
  rw [← toAdr_toB256 x, ← toAdr_toB256 y, eq]


lemma B64.toNat_sub {a b : B64} :
    (a - b).toNat = (2 ^ 64 + a.toNat - b.toNat) ↾ 64 := by
  apply Eq.trans (UInt64.toNat_sub _ _)
  apply congr_arg₂ _ _ rfl
  rw [Nat.sub_add_comm <| Nat.le_of_lt B64.toNat_lt]
  rfl

-- lemma Nat.add_sub_mod_eq_sub {k m n : Nat}
--     (hm : m < k) (h : n ≤ m) : (k + m - n) % k = m - n := by
--   rw [Nat.add_sub_assoc h, Nat.add_mod_left, Nat.mod_eq_of_lt]
--   apply lt_of_le_of_lt (Nat.sub_le _ _) hm
--
-- lemma Nat.add_sub_mod_eq_add_sub {k m n : Nat}
--     (hn : n ≤ k) (h : m < n) : (k + m - n) % k = k + m - n := by
--   rw [Nat.mod_eq_of_lt]
--   apply Nat.sub_lt_right_of_lt_add (by omega)
--   apply Nat.add_lt_add_left h

lemma Nat.add_mul_self_mod (x y z : ℕ) : (x + y * z) % z = x % z := by
  induction y with
  | zero => simp
  | succ y ih => rw [succ_mul, ← Nat.add_assoc, add_mod_right, ih]

lemma Nat.sub_mod_eq_sub_mod_right {a d c b : Nat}
    (eq : a % d = b % d) (le_a : c ≤ a) (le_b : c ≤ b) :
    (a - c) % d = (b - c) % d := by
  rcases d with _ | d
  · simp at *; rw [eq]
  · rw [← add_mul_self_mod _ c, ← add_mul_self_mod (b - c) c]
    rw [← Nat.sub_add_comm le_a, ← Nat.sub_add_comm le_b]
    rw [Nat.add_sub_assoc (Nat.le_mul_of_pos_right _ (by omega))]
    rw [Nat.add_sub_assoc (Nat.le_mul_of_pos_right _ (by omega))]
    apply Nat.add_mod_eq_add_mod_right _ eq


  -- by_cases h : d = 0
  -- · simp [h] at eq; rw [eq]
  -- · rw [← add_mul_self_mod _ c d]
  --   rw [← add_mul_self_mod (b - c) c d]
  --   rw [← Nat.sub_add_comm le_a]
  --   rw [← Nat.sub_add_comm le_b]
  --   have hd : 0 < d := by
  --     cases d
  --     · cases h rfl
  --     · simp
  --   rw [Nat.add_sub_assoc (Nat.le_mul_of_pos_right _ hd)]
  --   rw [Nat.add_sub_assoc (Nat.le_mul_of_pos_right _ hd)]
  --   apply Nat.add_mod_eq_add_mod_right _ eq

lemma B64.toNat_zero : B64.toNat 0 = 0 := rfl
lemma B64.toNat_one : B64.toNat 1 = 1 := rfl

lemma Nat.two_pow_add_lo (x y : Nat) : (2 ^ x + y) ↾ x = y ↾ x :=
  Nat.add_mod_left _ _

lemma B128.toNat_sub {a b : B128} :
    (a - b).toNat = (2 ^ 128 + a.toNat - b.toNat) ↾ 128 := by
  rw [B128.sub_eq]; simp only [B128.toNat]
  rw [Nat.add_shl_or_sub_shl_or_lo_add B64.toNat_lt B64.toNat_lt B64.toNat_lt]
  apply congr_arg₂ _ (congr_arg₂ _ _ rfl) B64.toNat_sub
  simp only [B64.toNat_sub]
  rw [@ite_distrib _ _ B64.toNat, B64.toNat_one, B64.toNat_zero]
  rw [← ite_eq_ite_of_iff B64.lt_iff_toNat_lt rfl rfl]
  apply Nat.sub_mod_eq_sub_mod_right
  · rw [Nat.add_mod_left]; apply Nat.lo_lo
  · split <;> omega
  · have _ := @B64.toNat_lt b.1; split <;> omega

lemma B128.toNat_zero : B128.toNat 0 = 0 := rfl
lemma B128.toNat_one : B128.toNat 1 = 1 := rfl

lemma B256.toNat_sub (a b : B256) :
    (a - b).toNat = (2 ^ 256 + a.toNat - b.toNat) ↾ 256 := by
  rw [B256.sub_eq]; simp only [B256.toNat]
  rw [Nat.add_shl_or_sub_shl_or_lo_add B128.toNat_lt B128.toNat_lt B128.toNat_lt]
  apply congr_arg₂ _ (congr_arg₂ _ _ rfl) B128.toNat_sub
  simp only [B128.toNat_sub]
  rw [@ite_distrib _ _ B128.toNat, B128.toNat_one, B128.toNat_zero]
  rw [← ite_eq_ite_of_iff B128.lt_iff_toNat_lt_toNat rfl rfl]
  apply Nat.sub_mod_eq_sub_mod_right
  · rw [Nat.add_mod_left]; apply Nat.lo_lo
  · split <;> omega
  · have _ := @B128.toNat_lt b.1; split <;> omega

lemma B128.lt_asymm {a b : B128} (h : a < b) : ¬ b < a := by
  intro h'; rcases h with h | h <;> rcases h' with h' | h'
  · cases UInt64.lt_asymm h h'
  · rw [h'.1] at h; cases UInt64.lt_irrefl _ h
  · rw [h.1] at h'; cases UInt64.lt_irrefl _ h'
  · cases UInt64.lt_asymm h.2 h'.2

lemma B256.lt_asymm {a b : B256} (h : a < b) : ¬ b < a := by
  intro h'; rcases h with h | h <;> rcases h' with h' | h'
  · cases B128.lt_asymm h h'
  · rw [h'.1] at h; cases B128.lt_irrefl _ h
  · rw [h.1] at h'; cases B128.lt_irrefl _ h'
  · cases B128.lt_asymm h.2 h'.2

lemma B128.lt_iff_le_not_ge {a b : B128} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [not_le, ← not_lt]; simp; apply lt_asymm

lemma B256.lt_iff_le_not_ge {a b : B256} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [not_le, ← not_lt]; simp; apply lt_asymm

lemma B128.lt_trans {a b c : B128} (ab : a < b) (bc : b < c) : a < c := by
  rcases ab with ab | ab <;> rcases bc with bc | bc
  · left; apply UInt64.lt_trans ab bc
  · left; rw [← bc.1]; exact ab
  · left; rw [ab.1]; exact bc
  · right; refine ⟨Eq.trans ab.1 bc.1, UInt64.lt_trans ab.2 bc.2⟩

lemma B128.le_trans {a b c : B128} (ab : a ≤ b) (bc : b ≤ c) : a ≤ c := by
  rcases ab with ab | ab <;> rcases bc with bc | bc
  · left; apply UInt64.lt_trans ab bc
  · left; rw [← bc.1]; exact ab
  · left; rw [ab.1]; exact bc
  · right; refine ⟨Eq.trans ab.1 bc.1, UInt64.le_trans ab.2 bc.2⟩

lemma B256.le_trans {a b c : B256} (ab : a ≤ b) (bc : b ≤ c) : a ≤ c := by
  rcases ab with ab | ab <;> rcases bc with bc | bc
  · left; apply B128.lt_trans ab bc
  · left; rw [← bc.1]; exact ab
  · left; rw [ab.1]; exact bc
  · right; refine ⟨Eq.trans ab.1 bc.1, B128.le_trans ab.2 bc.2⟩

instance : Preorder B128 where
  le_refl := B128.le_refl
  le_trans _ _ _ := B128.le_trans
  lt := B128.LT
  lt_iff_le_not_ge _ _ := B128.lt_iff_le_not_ge

instance : Preorder B256 where
  le_refl := B256.le_refl
  le_trans _ _ _ := B256.le_trans
  lt := B256.LT
  lt_iff_le_not_ge _ _ := B256.lt_iff_le_not_ge

lemma B128.le_antisymm {a b : B128} : a ≤ b → b ≤ a → a = b := by
  intro h₁ h₂; rw [le_iff_lt_or_eq] at h₁ h₂
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · cases B128.lt_asymm h₁ h₂
    · exact h₂.symm
  · exact h₁

lemma B256.le_antisymm {a b : B256} : a ≤ b → b ≤ a → a = b := by
  intro h₁ h₂; rw [le_iff_lt_or_eq] at h₁ h₂
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · cases B256.lt_asymm h₁ h₂
    · exact h₂.symm
  · exact h₁

instance : PartialOrder B128 where
  le_antisymm _ _ := B128.le_antisymm

instance : PartialOrder B256 where
  le_antisymm _ _ := B256.le_antisymm

lemma B128.le_total (m n : B128) : m ≤ n ∨ n ≤ m := by
  rcases B128.le_or_gt m n with h | h
  · left; apply h
  · right; simp [GT.gt] at h; apply B128.le_of_lt h

lemma B256.le_total (m n : B256) : m ≤ n ∨ n ≤ m := by
  rcases B256.le_or_gt m n with h | h
  · left; apply h
  · right; simp [GT.gt] at h; apply B256.le_of_lt h

instance : DecidableLT B128 :=
  fun a b => by rw [B128.lt_iff]; infer_instance

instance : DecidableLE B128 :=
  fun a b => by rw [B128.le_iff]; infer_instance

instance : DecidableEq B128 :=
  fun a b => by
    rw [show (a = b) ↔ (a.1 = b.1 ∧ a.2 = b.2) from Prod.ext_iff]; infer_instance

instance : DecidableLT B256 :=
  fun a b => by rw [B256.lt_iff]; infer_instance

instance : DecidableLE B256 :=
  fun a b => by rw [B256.le_iff]; infer_instance

instance : DecidableEq B256 :=
  fun a b => by
    rw [show (a = b) ↔ (a.1 = b.1 ∧ a.2 = b.2) from Prod.ext_iff]; infer_instance

instance : Ord B128 where
  compare a b := compareOfLessAndEq a b

instance : Ord B256 where
  compare a b := compareOfLessAndEq a b

instance : LinearOrder B128 where
  le_total := B128.le_total
  toDecidableLE := instDecidableLEB128

instance : LinearOrder B256 where
  le_total := B256.le_total
  toDecidableLE := instDecidableLEB256
  -- `Min B256` resolves to the pre-existing `B256.min` instance from
  -- `Basic.lean` (used by execution's fee/gas clamping), not this class's
  -- default `min` field. `B256.min a b` is literally `if a ≤ b then a else b`,
  -- but unfolding it needs default transparency, which the `min_def` auto-param
  -- tactic does not use — so discharge the field explicitly.
  min_def a b := rfl

def Adr.LE (x y : Adr) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
instance : @LE Adr := ⟨Adr.LE⟩
instance {x y : Adr} : Decidable (x ≤ y) := instDecidableOr

lemma Adr.le_iff (x y : Adr) :
  x ≤ y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)) := Iff.refl _

lemma Adr.le_refl (x : Adr) : x ≤ x := by
  right; refine ⟨rfl, B128.le_refl _⟩

lemma Adr.le_trans {a b c : Adr} (ab : a ≤ b) (bc : b ≤ c) : a ≤ c := by
  rcases ab with ab | ab <;> rcases bc with bc | bc
  · left; apply UInt32.lt_trans ab bc
  · left; rw [← bc.1]; exact ab
  · left; rw [ab.1]; exact bc
  · right; refine ⟨Eq.trans ab.1 bc.1, B128.le_trans ab.2 bc.2⟩

def Adr.LT (x y : Adr) : Prop := x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)
instance : @LT Adr := ⟨Adr.LT⟩
instance {x y : Adr} : Decidable (x < y) := instDecidableOr

lemma Adr.lt_iff (x y : Adr) :
  x < y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)) := Iff.refl _

lemma Adr.lt_iff_le_not_ge {a b : Adr} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  constructor <;> intro h
  · rcases h with h | h
    · refine' ⟨.inl h, not_or_intro (UInt32.lt_asymm h) _⟩
      apply not_and_of_not_left _ <| Ne.symm <| UInt32.ne_of_lt h
    · refine' ⟨.inr ⟨h.1, B128.le_of_lt h.2⟩, not_or_intro _ _⟩
      · rw [h.1]; apply UInt32.lt_irrefl
      · apply not_and_of_not_right; rw [B128.not_le]; apply h.2
  · rcases h with ⟨h | ⟨h1, h2⟩, h'⟩
    · apply Or.inl h
    · rcases not_or.mp h' with ⟨h1', h2'⟩
      right; refine' ⟨h1, B128.lt_iff_le_not_ge.mpr ⟨h2, not_and.mp h2' h1.symm⟩⟩

instance : Preorder Adr where
  le_refl := Adr.le_refl
  le_trans _ _ _ := Adr.le_trans
  lt := Adr.LT
  lt_iff_le_not_ge _ _ := Adr.lt_iff_le_not_ge

lemma Adr.le_antisymm {a b : Adr} : a ≤ b → b ≤ a → a = b := by
  intro h₁ h₂
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂
  · cases lt_asymm h₁ h₂
  · cases UInt32.ne_of_lt h₁ h₂.1.symm
  · cases UInt32.ne_of_lt h₂ h₁.1.symm
  · exact Prod.ext h₁.1 <| B128.le_antisymm h₁.2 h₂.2

instance : PartialOrder Adr where
  le_antisymm _ _ := Adr.le_antisymm

lemma Adr.le_total (m n : Adr) : m ≤ n ∨ n ≤ m := by
  by_cases h : m.1 < n.1
  · left; left; exact h
  · rw [not_lt, UInt32.le_iff_lt_or_eq] at h
    rcases h with h | h
    · right; left; exact h
    · rcases B128.le_total m.2 n.2 with h' | h'
      · left; right; refine ⟨h.symm, h'⟩
      · right; right; refine ⟨h, h'⟩

instance : DecidableLT Adr :=
  fun a b => by rw [Adr.lt_iff]; infer_instance

instance : DecidableLE Adr :=
  fun a b => by rw [Adr.le_iff]; infer_instance

instance : DecidableEq Adr :=
  fun a b => by
    rw [show (a = b) ↔ (a.1 = b.1 ∧ a.2 = b.2) from Prod.ext_iff]; infer_instance

instance : Ord Adr where
  compare a b := compareOfLessAndEq a b

instance : LinearOrder Adr where
  le_total := Adr.le_total
  toDecidableLE := by infer_instance

lemma Adr.lt_asymm {a b : Adr} (h : a < b) : ¬ b < a := by
  intro h'; rcases h with h | h <;> rcases h' with h' | h'
  · cases UInt32.lt_asymm h h'
  · rw [h'.1] at h; cases UInt32.lt_irrefl _ h
  · rw [h.1] at h'; cases UInt32.lt_irrefl _ h'
  · cases B128.lt_asymm h.2 h'.2

lemma Adr.lt_irrefl (x : Adr) : ¬ x < x := by
  intro h; rcases h with h | h <;> simp at h


-- lemma B128.toNat_sub (a b : B128) :
--     (a - b).toNat = (2 ^ 128 + a.toNat - b.toNat) % 2 ^ 128 := by
--   rw [B128.sub_eq]; simp only [B128.toNat]
--   rw [
--     @Nat.concat_modsub_concat 64 64 a.1.toNat a.2.toNat b.1.toNat b.2.toNat
--       (UInt64.toNat_lt_size _)
--       (UInt64.toNat_lt_size _)
--       (UInt64.toNat_lt_size _)
--   ]
--   apply congr_arg₂ _ _ (by rw [UInt64.toNat_sub'])
--   apply congr_arg₂ _ _ rfl
--   by_cases h : a.2 < b.2
--   · rw [if_pos h, if_pos (UInt64.lt_iff_toNat_lt.mp h)]; clear h
--     rw [UInt64.toNat_sub', UInt64.toNat_one, UInt64.toNat_sub']
--     rcases _root_.le_or_gt b.1.toNat a.1.toNat with h | h
--     · rw [Nat.add_sub_mod_eq_sub (UInt64.toNat_lt_pow _) h]
--       rw [← Nat.add_sub_assoc h]
--     · rw [Nat.add_sub_mod_eq_add_sub (Nat.le_of_lt (UInt64.toNat_lt_pow b.1)) h]
--       have h' : 2 ^ 64 + UInt64.toNat a.1 - UInt64.toNat b.1 < 2 ^ 64 := by
--         apply Nat.sub_lt_right_of_lt_add
--         · apply Nat.le_of_lt
--           apply lt_of_lt_of_le (UInt64.toNat_lt_size _) (Nat.le_add_right _ _)
--         · apply Nat.add_lt_add_left h
--       have h'' : 1 ≤ 2 ^ 64 + UInt64.toNat a.1 - UInt64.toNat b.1 := by
--         apply Nat.succ_le_of_lt
--         apply
--           lt_of_lt_of_le
--             (Nat.zero_lt_sub_of_lt (UInt64.toNat_lt_pow b.1))
--             (by omega)
--       rw [Nat.add_sub_mod_eq_sub h' h'']
--       rw [← Nat.sub_add_eq, Nat.add_sub_mod_eq_add_sub]
--       · apply Nat.succ_le_of_lt <| UInt64.toNat_lt_pow _
--       · apply lt_trans h <| Nat.lt_succ_self _
--   · rw [if_neg h, if_neg (mt UInt64.lt_iff_toNat_lt.mpr h)]
--     rw [Nat.sub_zero, UInt64.sub_zero, UInt64.toNat_sub']

theorem B256.sub_add_cancel {x y : B256} : x - y + y = x := by
  apply B256.toNat_inj
  simp only [B256.toNat_add, B256.toNat_sub]
  have x_lt : x.toNat < 2 ^ 256 := B256.toNat_lt _
  have y_lt : y.toNat < 2 ^ 256 := B256.toNat_lt _
  revert x_lt; revert y_lt
  generalize x.toNat = x, y.toNat = y
  intros y_lt x_lt
  by_cases h : x < y
  · rw [@Nat.lo_eq_of_lt (2 ^ 256 + x - y) _ (by omega)]
    rw [Nat.sub_add_cancel (by omega)]
    rw [Nat.two_pow_add_lo, Nat.lo_eq_of_lt x_lt]
  · rw [Nat.not_lt] at h
    rw [Nat.add_sub_assoc h, Nat.two_pow_add_lo]
    rw [Nat.lo_eq_of_lt (by {rw [Nat.lo]; omega})]
    rw [Nat.lo_eq_of_lt (by omega)]
    apply Nat.sub_add_cancel h

lemma toAdr_toNat (a : Adr) : a.toNat.toAdr = a := by
  simp only [Nat.toAdr, Adr.toNat]
  apply Prod.ext <;> simp
  · rw [Nat.shiftRight_or_distrib, Nat.shiftLeft_shiftRight]
    rw [Nat.shiftRight_eq_zero _ _ B128.toNat_lt, Nat.or_zero]
    apply toB32_toNat
  · rw [toB128_or]
    have eq : (a.1.toNat <<< 128).toB128 = 0 := by
      rw [toB128_eq_iff_lo_eq_toNat]
      rw [Nat.shl_lo_eq_zero_of_le (by omega)]
      rfl
    rw [eq, B128.zero_or]
    apply toB128_toNat

-- lemma Adr'.toAdr_toNat (a : Adr') : a.toNat.toAdr' = a := by
--   have aux : ∀ x : Nat, x * (2 ^ 128) = x * (2 ^ 64) * (2 ^ 64) := by
--     intro x; rw [Nat.mul_assoc]
--   simp only [Nat.toAdr', Adr'.toNat]
--   have h_high :
--       ((a.high.toNat * 2 ^ 128 + a.mid.toNat * 2 ^ 64 + a.low.toNat) / 2 ^ 128).toUInt32 = a.high := by
--   -- rw [Nat.add_assoc, Nat.add_div_of_dvd_of_lt]
--   -- · have h_lt := B64.toNat_mul_add_toNat_lt_size a.mid a.low
--   --   rw [Nat.div_eq_of_lt h_lt, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
--   --   apply UInt32.ofNat_toNat
--   -- · apply Nat.dvd_mul_left
--   -- · apply B64.toNat_mul_add_toNat_lt_size
--     sorry
--   rw [h_high]; clear h_high
--   have h_mid :
--       ((a.high.toNat * 2 ^ 128 + a.mid.toNat * 2 ^ 64 + a.low.toNat) / 2 ^ 64).toUInt64 = a.mid := by
--     rw [Nat.add_div_of_dvd_of_lt _ (UInt64.toNat_lt_size _)]
--
--
--     · rw [Nat.div_eq_of_lt <| UInt64.toNat_lt_size a.low, Nat.add_zero]
--       have h_dvd : 2 ^ 64 ∣ UInt32.toNat a.high * 2 ^ 128 := by
--         rw [aux]; apply Nat.dvd_mul_left
--       rw [Nat.add_div_of_dvd_of_dvd h_dvd (Nat.dvd_mul_left _ _) (Nat.two_pow_pos _)]
--       rw [Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
--
--       rw [aux, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
--
--       simp
--
--     · rw [aux]; apply Nat.dvd_add <;> apply Nat.dvd_mul_left
--   rw [h_mid]; clear h_mid
--   simp

-- def Adr.compare (a b : Adr) : Ordering :=
--   match Ord.compare a.1 b.1 with
--   | .eq => Ord.compare a.2 b.2
--   | o => o

-- def Adr.compare : Adr → Adr → Ordering
--   | ⟨xh, xm, xl⟩, ⟨yh, ym, yl⟩ =>
--     match Ord.compare xh yh with
--     | .eq =>
--       match Ord.compare xm ym with
--       | .eq => Ord.compare xl yl
--       | o => o
--     | o => o

--instance : Ord Adr := {compare := Adr.compare}

def Adr.toHex (a : Adr) : String := a.1.toHex ++ a.2.toHex

instance : ToString Adr := ⟨Adr.toHex⟩

def String.dropZeroes (s : String) : String :=
  match String.ofList (s.toList.dropWhile (· == '0')) with
  | "" => "0"
  | s => s

def Stor := Std.TreeMap B256 B256 compare

def Stor.get (s : Stor) (k : B256) : B256 := s.getD k 0
def Stor.empty : Stor := Std.TreeMap.empty

lemma Std.TreeMap.eq_empty_of_isEmpty {α : Type u} {β : Type v}
    {cmp : α → α → Ordering} {t : Std.TreeMap α β cmp} (h : t.isEmpty = true) :
    t = Std.TreeMap.empty := by
  rcases t with ⟨⟨dt, wf⟩⟩
  simp [Std.TreeMap.isEmpty, Std.DTreeMap.isEmpty] at h
  cases dt
  · simp [Std.DTreeMap.Internal.Impl.isEmpty] at h
  · rfl

def Stor.toStrings (s : Stor) : List String :=
  let kvs := s.toArray.toList
  let kvToStrings : B256 × B256 → List String :=
    λ nb => [s!"0x{(B256.toHex nb.fst).dropZeroes} : 0x{(B256.toHex nb.snd).dropZeroes}"]
  fork "STOR" (kvs.map kvToStrings)

instance : ToString Stor := ⟨String.joinln ∘ Stor.toStrings⟩

@[ext]
structure Acct where
  (nonce : B64)
  (bal : B256)
  (stor : Stor)
  (code : ByteArray)

def Acct.withBal (a : Acct) (bal : B256) : Acct :=
  {a with bal := bal}

def Acct.toStrings (s : String) (a : Acct) : List String :=
  let codeStrings : List String :=
    let xs := a.code.toList
    let sz := xs.length
    if sz = 0 then
      []
    else if sz ≤ 32 then
      [s!"{B8L.toHex xs} ({sz} bytes)"]
    else
      [s!"{B8L.toHex (xs.take 32)}... ({sz} bytes)"]

  fork s [
    [s!"BAL : 0x{a.bal.toHex.dropZeroes}"],
    [s!"NONCE : 0x{a.nonce.toHex.dropZeroes}"],
    --longB8LToStrings "code" a.code.toList,
    --fork "CODE" [String.chunks 64 <| B8L.toHex a.code.toList],
    fork "CODE" [codeStrings],
    a.stor.toStrings
  ]

instance : ToString Acct := ⟨fun a => String.joinln (Acct.toStrings "account" a)⟩
-- An address is exactly twenty bytes. The trailing `[]` is load-bearing: a
-- twenty-one-byte list is a malformed address, not an address with a tail to
-- ignore. Accepting the prefix let an overlong RLP field survive decoding and
-- be rejected later, if at all, for the wrong reason (finding 3.6). Every
-- caller already supplies exactly twenty bytes -- `ByteArray.sliceD _ 20`, the
-- low twenty bytes of a keccak hash, or a checked consensus field -- so the
-- rejection is new only for untrusted input.
def B8L.toAdr? : B8L → Option Adr
  | x0 :: x1 :: x2 :: x3 ::
    y0 :: y1 :: y2 :: y3 ::
    y4 :: y5 :: y6 :: y7 ::
    z0 :: z1 :: z2 :: z3 ::
    z4 :: z5 :: z6 :: z7 :: [] =>
    some ⟨
      B8s.toB32 x0 x1 x2 x3,
      B8s.toB64 y0 y1 y2 y3 y4 y5 y6 y7,
      B8s.toB64 z0 z1 z2 z3 z4 z5 z6 z7,
    ⟩
  | _ => none

def Hex.toAdr? (hx : String) : Option Adr := Hex.toB8L hx >>= B8L.toAdr?

------------------- STRICT CONSENSUS-FIELD DECODING --------------------

-- RLP bytes are untrusted consensus input, so a field's *shape* must be
-- checked before its value is converted, never after. The conversions
-- themselves (`B8L.toB64`, `B8L.toB256`) pad or truncate to a fixed width
-- through `B8L.pack`, which silently turns a nine-byte withdrawal index into a
-- plausible eight-byte one; the encode-and-compare round trip then reports the
-- corruption as a generic RLP mismatch, long after the value was lost.
--
-- The helpers below are the pure shape checks, one per shape the consensus
-- fields actually have. They are deliberately value-level and error-free:
-- `Jaune/Execution.lean` wraps each one with the tagged error naming the
-- precise reason, which is what a fixture exception identity is mapped from.

/-- A fixed-width field: the length must equal `n` exactly. -/
def B8L.toFixed? (n : Nat) (xs : B8L) : Option B8L :=
  if xs.length = n then some xs else none

/-- Is this a canonical unsigned scalar of at most `n` bytes?

Two independent conditions, both required by RLP: the width must fit, and the
encoding must be canonical -- zero is the empty byte string, and a nonempty
scalar never begins with a zero byte. `Execution.lean` distinguishes the two
failures, since only one of them is a field-overflow. -/
def B8L.isCanonicalScalar (n : Nat) (xs : B8L) : Bool :=
  (xs.length ≤ n) && (xs.head? != some (0 : B8))

/-- A canonical unsigned scalar of at most `n` bytes, as a `Nat`. -/
def B8L.toScalarNat? (n : Nat) (xs : B8L) : Option Nat :=
  if xs.isCanonicalScalar n then some xs.toNat else none

/-- A canonical 64-bit scalar: at most eight bytes, hence converted without
truncation. Note this is *not* `B8L.toB64?`, which demands exactly eight bytes
and so rejects every valid small integer. -/
def B8L.toScalarB64? (xs : B8L) : Option B64 :=
  if xs.isCanonicalScalar 8 then some xs.toB64 else none

/-- A canonical 256-bit scalar: at most thirty-two bytes, hence converted
without truncation. -/
def B8L.toScalarB256? (xs : B8L) : Option B256 :=
  if xs.isCanonicalScalar 32 then some xs.toB256 else none

/-- An optional contract-creation receiver: either empty, meaning creation, or
exactly twenty bytes. Anything else is malformed rather than a creation. -/
def B8L.toReceiver? : B8L → Option (Option Adr)
  | [] => some none
  | xs => xs.toAdr?.map some

--------------- STRICT-SHAPE BOUNDARY CHECKS ----------------

-- Boundaries at 0, 1, n, and n+1 bytes for each shape, plus canonicality, plus
-- the 19/20/21-byte address cases.

-- Fixed width: only the exact length is accepted, on both sides.
#guard (B8L.toFixed? 0 []).isSome
#guard (B8L.toFixed? 0 [0x00]).isNone
#guard (B8L.toFixed? 4 [0x01, 0x02, 0x03]).isNone                    -- n-1
#guard (B8L.toFixed? 4 [0x01, 0x02, 0x03, 0x04]).isSome              -- n
#guard (B8L.toFixed? 4 [0x01, 0x02, 0x03, 0x04, 0x05]).isNone        -- n+1
-- A fixed-width field is bytes, not a number: leading zeroes are content.
#guard (B8L.toFixed? 4 [0x00, 0x00, 0x00, 0x00]).isSome

-- Canonical scalars: the empty string is zero, a leading zero byte is not.
#guard B8L.toScalarNat? 8 [] = some 0                                -- 0 bytes
#guard B8L.toScalarNat? 8 [0x01] = some 1                            -- 1 byte
#guard B8L.toScalarNat? 8 (List.replicate 8 (0xFF : B8)) = some (2 ^ 64 - 1)
#guard (B8L.toScalarNat? 8 (List.replicate 9 (0xFF : B8))).isNone    -- n+1
#guard (B8L.toScalarNat? 8 [0x00]).isNone                            -- zero, not empty
#guard (B8L.toScalarNat? 8 [0x00, 0x01]).isNone                      -- leading zero
#guard B8L.toScalarNat? 8 [0x01, 0x00] = some 256                    -- trailing zero is fine

-- 64-bit scalars convert every accepted width without truncating.
#guard (B8L.toScalarB64? []).map B64.toNat = some 0
#guard (B8L.toScalarB64? [0x01]).map B64.toNat = some 1
#guard (B8L.toScalarB64? [0x01, 0x00]).map B64.toNat = some 256
#guard (B8L.toScalarB64? (List.replicate 8 (0xFF : B8))).map B64.toNat
  = some (2 ^ 64 - 1)                                                -- n
#guard (B8L.toScalarB64? (0x01 :: List.replicate 8 (0x00 : B8))).isNone  -- n+1
-- The nine-byte withdrawal-index case: rejected outright, and emphatically not
-- accepted as the eight-byte value `B8L.toB64` would have truncated it to.
#guard (B8L.toB64 (0x01 :: List.replicate 8 (0x00 : B8))).toNat = 0
#guard (B8L.toScalarB64? [0x00]).isNone

-- 256-bit scalars, same shape one width up.
#guard (B8L.toScalarB256? []).map B256.toNat = some 0
#guard (B8L.toScalarB256? [0x01]).map B256.toNat = some 1
#guard (B8L.toScalarB256? (List.replicate 32 (0xFF : B8))).map B256.toNat
  = some (2 ^ 256 - 1)                                               -- n
#guard (B8L.toScalarB256? (List.replicate 33 (0xFF : B8))).isNone     -- n+1
#guard (B8L.toScalarB256? [0x00, 0x01]).isNone

-- Addresses: exactly twenty bytes, with 19 and 21 both rejected.
#guard (B8L.toAdr? (List.replicate 19 (0x11 : B8))).isNone
#guard (B8L.toAdr? (List.replicate 20 (0x11 : B8))).isSome
#guard (B8L.toAdr? (List.replicate 21 (0x11 : B8))).isNone
#guard (B8L.toAdr? []).isNone
-- The twenty accepted bytes are the address, in order.
#guard (B8L.toAdr? (List.replicate 20 (0x11 : B8))).map Adr.toHex
  = some (String.join <| List.replicate 20 "11")
-- The overlong case used to decode to the address of its twenty-byte prefix.
#guard (B8L.toAdr? (List.replicate 20 (0x11 : B8) ++ [0x22])).isNone

-- Optional creation receivers: empty is creation, twenty bytes is a call, and
-- every other width is malformed rather than silently one of the two.
#guard (B8L.toReceiver? []) = some none
#guard ((B8L.toReceiver? (List.replicate 20 (0x11 : B8))).map (Option.map Adr.toHex))
  = some (some (String.join <| List.replicate 20 "11"))
#guard (B8L.toReceiver? (List.replicate 19 (0x11 : B8))).isNone
#guard (B8L.toReceiver? (List.replicate 21 (0x11 : B8))).isNone
#guard (B8L.toReceiver? [0x00]).isNone

def Adr.toB8L (a : Adr) : B8L := a.1.toB8L ++ a.2.toB8L

inductive Rinst : Type
  | add -- 0x01 / 2 / 1 / addition operation.
  | mul -- 0x02 / 2 / 1 / multiplication operation.
  | sub -- 0x03 / 2 / 1 / subtraction operation.
  | div -- 0x04 / 2 / 1 / integer division operation.
  | sdiv -- 0x05 / 2 / 1 / signed integer division operation.
  | mod -- 0x06 / 2 / 1 / modulo operation.
  | smod -- 0x07 / 2 / 1 / signed modulo operation.
  | addmod -- 0x08 / 3 / 1 / modulo addition operation.
  | mulmod -- 0x09 / 3 / 1 / modulo multiplication operation.
  | exp -- 0x0A / 2 / 1 / exponentiation operation.
  | signextend -- 0x0B / 2 / 1 / sign extend operation.
  | lt -- 0x10 / 2 / 1 / less-than comparison.
  | gt -- 0x11 / 2 / 1 / greater-than comparison.
  | slt -- 0x12 / 2 / 1 / signed less-than comparison.
  | sgt -- 0x13 / 2 / 1 / signed greater-than comparison.
  | eq -- 0x14 / 2 / 1 / equality comparison.
  | iszero -- 0x15 / 1 / 1 / tests if the input is zero.
  | and -- 0x16 / 2 / 1 / bitwise and operation.
  | or -- 0x17 / 2 / 1 / bitwise or operation.
  | xor -- 0x18 / 2 / 1 / bitwise xor operation.
  | not -- 0x19 / 1 / 1 / bitwise not operation.
  | byte -- 0x1A / 2 / 1 / retrieve a single Byte from a Word.
  | shl -- 0x1B / 2 / 1 / logical shift left operation.
  | shr -- 0x1C / 2 / 1 / logical shift right operation.
  | sar -- 0x1D / 2 / 1 / arithmetic (signed) shift right operation.
  | clz -- 0x1E / 1 / 1 / count leading zero bits (Osaka and later only).
  | kec -- 0x20 / 2 / 1 / compute Keccak-256 hash.
  | address -- 0x30 / 0 / 1 / Get the Addr of the currently executing account.
  | balance -- 0x31 / 1 / 1 / Get the balance of the specified account.
  | origin -- 0x32 / 0 / 1 / Get the Addr that initiated the current transaction.
  | caller -- 0x33 / 0 / 1 / Get the Addr that directly called the currently executing contract.
  | callvalue -- 0x34 / 0 / 1 / Get the value (in wei) sent with the current transaction.
  | calldataload -- 0x35 / 1 / 1 / Load input data from the current transaction.
  | calldatasize -- 0x36 / 0 / 1 / Get the size of the input data from the current transaction.
  | calldatacopy -- 0x37 / 3 / 0 / Copy input data from the current transaction to Memory.
  | codesize -- 0x38 / 0 / 1 / Get the size of the code of the currently executing contract.
  | codecopy -- 0x39 / 3 / 0 / Copy the code of the currently executing contract to memory.
  | gasprice -- 0x3a / 0 / 1 / Get the gas price of the current transaction.
  | extcodesize -- 0x3B / 1 / 1 / Get the size of the code of an external account.
  | extcodecopy -- 0x3C / 4 / 0 / Copy the code of an external account to memory.
  | retdatasize -- 0x3D / 0 / 1 / Get the size of the output data from the previous call.
  | retdatacopy -- 0x3E / 3 / 0 / Copy output data from the previous call to memory.
  | extcodehash -- 0x3F / 1 / 1 / Get the code hash of an external account.
  | blockhash -- 0x40 / 1 / 1 / get the hash of the specified block.
  | coinbase -- 0x41 / 0 / 1 / get the Addr of the current block's miner.
  | timestamp -- 0x42 / 0 / 1 / get the timestamp of the current block.
  | number -- 0x43 / 0 / 1 / get the current block number.
  | prevrandao -- 0x44 / 0 / 1 / get the latest RANDAO mix of the post beacon state of the previous block.
  | gaslimit -- 0x45 / 0 / 1 / get the gas limit of the current block.
  | chainid -- 0x46 / 0 / 1 / get the chain id of the current blockchain.
  | selfbalance -- 0x47 / 0 / 1 / get the balance of the currently executing account.
  | basefee -- 0x48 / 0 / 1 / get the current block's base fee.
  | blobhash -- 0x49 / 1 / 1 /
  | blobbasefee -- 0x4A / 0 / 1 / get the current block's blob base fee.
  | pop -- 0x50 / 1 / 0 / Remove an item from the Stack.
  | mload -- 0x51 / 1 / 1 / Load a Word from memory.
  | mstore -- 0x52 / 2 / 0 / Store a Word in memory.
  | mstore8 -- 0x53 / 2 / 0 / store a Byte in memory.
  | sload -- 0x54 / 1 / 1 / load a word from storage.
  | sstore -- 0x55 / 2 / 0 / store a word in storage.
  | tload -- 0x5C / 1 / 1 / load a word from transient storage.
  | tstore -- 0x5D / 2 / 0 / store a word in transient storage.
  | mcopy -- 0x5E / 3 / 0 /
  | pc -- 0x58 / 0 / 1 / Get the current program counter value.
  | msize -- 0x59 / 0 / 1 / Get the size of the memory.
  | gas -- 0x5a / 0 / 1 / Get the amount of remaining gas.
  | dup : Fin 16 → Rinst
  | swap : Fin 16 → Rinst
  | log : Fin 5 → Rinst

inductive Jinst : Type
  | jump -- 0x56 / 1 / 0 / Unconditional jump.
  | jumpi -- 0x57 / 2 / 0 / Conditional jump.
  | jumpdest -- 0x5b / 0 / 0 / Mark a valid jump destination.
deriving DecidableEq

inductive Xinst : Type
  | create -- 0xf0 / 3 / 1 / Create a new contract account.
  | call -- 0xf1 / 7 / 1 / Call an existing account, which can be either a contract or a non-contract account.
  | callcode -- 0xf2 / 7 / 1 / Call an existing contract's code using the current contract's Storage and Addr.
  | delcall -- 0xf4 / 6 / 1 / Call an existing contract's code using the current contract's Storage and the calling contract's Addr and value.
  | create2 -- 0xf5 / 4 / 1 / Create a new contract account at a deterministic Addr using a salt value.
  | statcall -- 0xfa / 6 / 1 / Perform a read-only call to an existing contract.
deriving DecidableEq

inductive Linst : Type
  | stop -- 0x00 / 0 / 0 / halts execution.
  | ret -- 0xf3 / 2 / 0 / Halt execution and return output data.
  | rev -- 0xfd / 2 / 0 / Halt execution and revert State changes, returning output data.
  | dest -- 0xff / 1 / 0 / Halt execution and destroy the current contract, transferring remaining Ether to a specified Addr.
  -- | invalid -- 0xFE / 0 / 0 / Designated invalid instruction.
deriving DecidableEq


def Rinst.toString : Rinst → String
  | add => "ADD"
  | mul => "MUL"
  | sub => "SUB"
  | div => "DIV"
  | sdiv => "SDIV"
  | mod => "MOD"
  | smod => "SMOD"
  | addmod => "ADDMOD"
  | mulmod => "MULMOD"
  | exp => "EXP"
  | signextend => "SIGNEXTEND"
  | lt => "LT"
  | gt => "GT"
  | slt => "SLT"
  | sgt => "SGT"
  | eq => "EQ"
  | iszero => "ISZERO"
  | and => "AND"
  | or => "OR"
  | xor => "XOR"
  | not => "NOT"
  | byte => "BYTE"
  | shr => "SHR"
  | shl => "SHL"
  | sar => "SAR"
  | clz => "CLZ"
  | kec => "KEC"
  | address => "ADDRESS"
  | balance => "BALANCE"
  | origin => "ORIGIN"
  | caller => "CALLER"
  | callvalue => "CALLVALUE"
  | calldataload => "CALLDATALOAD"
  | calldatasize => "CALLDATASIZE"
  | calldatacopy => "CALLDATACOPY"
  | codesize => "CODESIZE"
  | codecopy => "CODECOPY"
  | gasprice => "GASPRICE"
  | extcodesize => "EXTCODESIZE"
  | extcodecopy => "EXTCODECOPY"
  | retdatasize => "RETDATASIZE"
  | retdatacopy => "RETDATACOPY"
  | extcodehash => "EXTCODEHASH"
  | blockhash => "BLOCKHASH"
  | coinbase => "COINBASE"
  | timestamp => "TIMESTAMP"
  | number => "NUMBER"
  | prevrandao => "PREVRANDAO"
  | gaslimit => "GASLIMIT"
  | chainid => "CHAINID"
  | selfbalance => "SELFBALANCE"
  | basefee => "BASEFEE"
  | blobhash => "BLOBHASH"
  | blobbasefee => "BLOBBASEFEE"
  | pop => "POP"
  | mload => "MLOAD"
  | mstore => "MSTORE"
  | mstore8 => "MSTORE8"
  | sload => "SLOAD"
  | sstore => "SSTORE"
  | tload => "TLOAD"
  | tstore => "TSTORE"
  | mcopy => "MCOPY"
  | pc => "PC"
  | msize => "MSIZE"
  | gas => "GAS"
  | dup n => "DUP" ++ (n.val + 1).repr
  | swap n => "SWAP" ++ (n.val + 1).repr
  | log n => "LOG" ++ n.val.repr

def Xinst.toString : Xinst → String
  | create => "CREATE"
  | call => "CALL"
  | callcode => "CALLCODE"
  | delcall => "DELEGATECALL"
  | create2 => "CREATE2"
  | statcall => "STATICCALL"

def Linst.toString : Linst → String
  | .stop => "STOP"
  | .dest => "SELFDESTRUCT"
  | .rev => "REVERT"
  | .ret => "RETURN"
  -- | .invalid => "INVALID"

def B8.toRinst : B8 → Option Rinst
  | 0x01 => some .add -- 0x01 / 2 / 1 / addition operation.
  | 0x02 => some .mul -- 0x02 / 2 / 1 / multiplication operation.
  | 0x03 => some .sub -- 0x03 / 2 / 1 / subtraction operation.
  | 0x04 => some .div -- 0x04 / 2 / 1 / integer division operation.
  | 0x05 => some .sdiv -- 0x05 / 2 / 1 / signed integer division operation.
  | 0x06 => some .mod -- 0x06 / 2 / 1 / modulo operation.
  | 0x07 => some .smod -- 0x07 / 2 / 1 / signed modulo operation.
  | 0x08 => some .addmod -- 0x08 / 3 / 1 / modulo addition operation.
  | 0x09 => some .mulmod -- 0x09 / 3 / 1 / modulo multiplication operation.
  | 0x0a => some .exp -- 0x0a / 2 / 1 / exponentiation operation.
  | 0x0b => some .signextend -- 0x0b / 2 / 1 / sign extend operation.
  | 0x10 => some .lt -- 0x10 / 2 / 1 / less-than comparison.
  | 0x11 => some .gt -- 0x11 / 2 / 1 / greater-than comparison.
  | 0x12 => some .slt -- 0x12 / 2 / 1 / signed less-than comparison.
  | 0x13 => some .sgt -- 0x13 / 2 / 1 / signed greater-than comparison.
  | 0x14 => some .eq -- 0x14 / 2 / 1 / equality comparison.
  | 0x15 => some .iszero -- 0x15 / 1 / 1 / tests if the input is zero.
  | 0x16 => some .and -- 0x16 / 2 / 1 / bitwise and operation.
  | 0x17 => some .or -- 0x17 / 2 / 1 / bitwise or operation.
  | 0x18 => some .xor -- 0x18 / 2 / 1 / bitwise xor operation.
  | 0x19 => some .not -- 0x19 / 1 / 1 / bitwise not operation.
  | 0x1a => some .byte -- 0x1a / 2 / 1 / retrieve a single byte from a word.
  | 0x1b => some .shl -- 0x1b / 2 / 1 / logical shift left operation.
  | 0x1c => some .shr -- 0x1c / 2 / 1 / logical shift right operation.
  | 0x1d => some .sar -- 0x1d / 2 / 1 / arithmetic (signed) shift right operation.
  -- 0x1e decodes at every fork; whether it is a defined instruction is a rule,
  -- checked by `Rinst.runCore` against `ForkRules.op`.  Decoding stays
  -- fork-independent so that instruction positions -- and every downstream
  -- statement about them -- do not depend on which rules are running.
  | 0x1e => some .clz -- 0x1e / 1 / 1 / count leading zero bits.
  | 0x20 => some .kec -- 0x20 / 2 / 1 / compute Keccak-256 hash.
  | 0x30 => some .address -- 0x30 / 0 / 1 / Get the address of the currently executing account.
  | 0x31 => some .balance -- 0x31 / 1 / 1 / Get the balance of the specified account.
  | 0x32 => some .origin -- 0x32 / 0 / 1 / Get the address that initiated the current transaction.
  | 0x33 => some .caller -- 0x33 / 0 / 1 / Get the address that directly called the currently executing contract.
  | 0x34 => some .callvalue -- 0x34 / 0 / 1 / Get the value (in wei) sent with the current transaction.
  | 0x35 => some .calldataload -- 0x35 / 1 / 1 / Load input data from the current transaction.
  | 0x36 => some .calldatasize -- 0x36 / 0 / 1 / Get the size of the input data from the current transaction.
  | 0x37 => some .calldatacopy -- 0x37 / 3 / 0 / Copy input data from the current transaction to memory.
  | 0x38 => some .codesize -- 0x38 / 0 / 1 / Get the size of the code of the currently executing contract.
  | 0x39 => some .codecopy -- 0x39 / 3 / 0 / Copy the code of the currently executing contract to memory.
  | 0x3a => some .gasprice -- 0x3a / 0 / 1 / Get the gas price of the current transaction.
  | 0x3b => some .extcodesize -- 0x3b / 1 / 1 / Get the size of the code of an external account.
  | 0x3c => some .extcodecopy -- 0x3c / 4 / 0 / Copy the code of an external account to memory.
  | 0x3d => some .retdatasize -- 0x3d / 0 / 1 / Get the size of the output data from the previous call.
  | 0x3e => some .retdatacopy -- 0x3e / 3 / 0 / Copy output data from the previous call to memory.
  | 0x3f => some .extcodehash -- 0x3f / 1 / 1 / Get the code hash of an external account.
  | 0x40 => some .blockhash -- 0x40 / 1 / 1 / get the hash of the specified block.
  | 0x41 => some .coinbase -- 0x41 / 0 / 1 / get the address of the current block's miner.
  | 0x42 => some .timestamp -- 0x42 / 0 / 1 / get the timestamp of the current block.
  | 0x43 => some .number -- 0x43 / 0 / 1 / get the current block number.
  | 0x44 => some .prevrandao -- 0x44 / 0 / 1 / get the difficulty of the current block.
  | 0x45 => some .gaslimit -- 0x45 / 0 / 1 / get the gas limit of the current block.
  | 0x46 => some .chainid -- 0x46 / 0 / 1 / get the chain id of the current blockchain.
  | 0x47 => some .selfbalance
  | 0x48 => some .basefee -- 0x48 / 0 / 1 /
  | 0x49 => some .blobhash -- 0x49 / 1 / 1 /
  | 0x4A => some .blobbasefee -- 0x4A / 0 / 1 /
  | 0x50 => some .pop -- 0x50 / 1 / 0 / Remove an item from the stack.
  | 0x51 => some .mload -- 0x51 / 1 / 1 / Load a word from memory.
  | 0x52 => some .mstore -- 0x52 / 2 / 0 / Store a word in memory.
  | 0x53 => some .mstore8 -- 0x53 / 2 / 0 / Store a byte in memory.
  | 0x54 => some .sload -- 0x54 / 1 / 1 / Load a word from storage.
  | 0x55 => some .sstore -- 0x55 / 2 / 0 / Store a word in storage.
  | 0x58 => some .pc -- 0x58 / 0 / 1 / Get the current program counter value.
  | 0x59 => some .msize -- 0x59 / 0 / 1 / Get the size of the memory.
  | 0x5a => some .gas -- 0x5a / 0 / 1 / Get the amount of remaining gas.
  | 0x5C => some .tload
  | 0x5D => some .tstore
  | 0x5E => some .mcopy
  | 0x80 => some (.dup 0)
  | 0x81 => some (.dup 1)
  | 0x82 => some (.dup 2)
  | 0x83 => some (.dup 3)
  | 0x84 => some (.dup 4)
  | 0x85 => some (.dup 5)
  | 0x86 => some (.dup 6)
  | 0x87 => some (.dup 7)
  | 0x88 => some (.dup 8)
  | 0x89 => some (.dup 9)
  | 0x8A => some (.dup 10)
  | 0x8B => some (.dup 11)
  | 0x8C => some (.dup 12)
  | 0x8D => some (.dup 13)
  | 0x8E => some (.dup 14)
  | 0x8F => some (.dup 15)
  | 0x90 => some (.swap 0)
  | 0x91 => some (.swap 1)
  | 0x92 => some (.swap 2)
  | 0x93 => some (.swap 3)
  | 0x94 => some (.swap 4)
  | 0x95 => some (.swap 5)
  | 0x96 => some (.swap 6)
  | 0x97 => some (.swap 7)
  | 0x98 => some (.swap 8)
  | 0x99 => some (.swap 9)
  | 0x9A => some (.swap 10)
  | 0x9B => some (.swap 11)
  | 0x9C => some (.swap 12)
  | 0x9D => some (.swap 13)
  | 0x9E => some (.swap 14)
  | 0x9F => some (.swap 15)
  | 0xA0 => some (.log 0)
  | 0xA1 => some (.log 1)
  | 0xA2 => some (.log 2)
  | 0xA3 => some (.log 3)
  | 0xA4 => some (.log 4)
  | _ => none

def B8.toXinst : B8 → Option Xinst
  | 0xF0 => some .create
  | 0xF1 => some .call
  | 0xF2 => some .callcode
  | 0xF4 => some .delcall
  | 0xF5 => some .create2
  | 0xFA => some .statcall
  | _    => none

def B8.toJinst : B8 → Option Jinst
  | 0x56 => some .jump
  | 0x57 => some .jumpi
  | 0x5B => some .jumpdest
  | _    => none

def B8.toLinst : B8 → Option Linst
  | 0x00 => some .stop
  | 0xF3 => some .ret
  | 0xFD => some .rev
  | 0xFF => some .dest
  | _ => none

def Linst.toB8 : Linst → B8
  | .stop => 0x00
  | .ret => 0xF3
  | .rev => 0xFD
  | .dest => 0xFF

def Jinst.toB8 : Jinst → B8
  | jump => 0x56     -- 0x56 / 1 / 0 / Unconditional jump.
  | jumpi => 0x57    -- 0x57 / 2 / 0 / Conditional jump.
  | jumpdest => 0x5B -- 0x5b / 0 / 0 / Mark a valid jump destination.

instance : Repr Rinst := ⟨λ o _ => o.toString⟩
instance : Repr Xinst := ⟨λ o _ => o.toString⟩

def Jinst.toString : Jinst → String
  | .jump => "JUMP"
  | .jumpdest => "JUMPDEST"
  | .jumpi => "JUMPI"
