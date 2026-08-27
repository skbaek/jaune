import Jaune.Hash

/-!
# SHA-256 as published, and the kernel's equivalence to it

`Jaune/Hash.lean`'s `SHA256` namespace is an optimized hash: the eight working
variables are carried as scalars, the sixty-four-entry message schedule is
folded onto sixteen live words updated in place, and padding is fused into the
chunk walk so the message is never materialized twice. None of that is visible
in FIPS 180-4, and none of it should be: the standard defines SHA-256 with a
sixty-four-entry schedule `W`, six named functions, and a padded message parsed
into 512-bit blocks.

This module is that definition, transcribed from **NIST FIPS 180-4** (*Secure
Hash Standard*, August 2015) — section numbers are cited at each declaration —
and `SHA256.FIPS.hash_eq` at the end proves the kernel computes it, for every
input.

The transcription is written from the standard, never read back out of the
kernel: the constants are the standard's tables, the schedule is the standard's
sixty-four entries, the round is the standard's `T₁`/`T₂` assignment, and the
padding is the standard's `l + 1 + k ≡ 448 mod 512`. Where the kernel and this
module disagree in shape they are meant to — that gap is what the theorem is
about. Where they would disagree in *value*, this module is right by definition
and the kernel is wrong.

Nothing here is on any execution path. The hash Jaune computes is
`Bytes.sha256`; these declarations exist to be read against the standard and to
give that function something to be equal to.
-/

namespace Jaune

open Jaune

namespace SHA256.FIPS

/-! ## §4.1.2 — the six logical functions -/

/-- FIPS 180-4 §4.1.2: `Ch(x, y, z) = (x ∧ y) ⊕ (¬x ∧ z)`. -/
def Ch (x y z : UInt32) : UInt32 := (x &&& y) ^^^ ((~~~ x) &&& z)

/-- FIPS 180-4 §4.1.2: `Maj(x, y, z) = (x ∧ y) ⊕ (x ∧ z) ⊕ (y ∧ z)`. -/
def Maj (x y z : UInt32) : UInt32 := (x &&& y) ^^^ (x &&& z) ^^^ (y &&& z)

/-- FIPS 180-4 §4.1.2: `Σ₀{256}(x) = ROTR²(x) ⊕ ROTR¹³(x) ⊕ ROTR²²(x)`. -/
def Sigma0 (x : UInt32) : UInt32 :=
  UInt32.ror x 2 ^^^ UInt32.ror x 13 ^^^ UInt32.ror x 22

/-- FIPS 180-4 §4.1.2: `Σ₁{256}(x) = ROTR⁶(x) ⊕ ROTR¹¹(x) ⊕ ROTR²⁵(x)`. -/
def Sigma1 (x : UInt32) : UInt32 :=
  UInt32.ror x 6 ^^^ UInt32.ror x 11 ^^^ UInt32.ror x 25

/-- FIPS 180-4 §4.1.2: `σ₀{256}(x) = ROTR⁷(x) ⊕ ROTR¹⁸(x) ⊕ SHR³(x)`. -/
def sigma0 (x : UInt32) : UInt32 :=
  UInt32.ror x 7 ^^^ UInt32.ror x 18 ^^^ (x >>> 3)

/-- FIPS 180-4 §4.1.2: `σ₁{256}(x) = ROTR¹⁷(x) ⊕ ROTR¹⁹(x) ⊕ SHR¹⁰(x)`. -/
def sigma1 (x : UInt32) : UInt32 :=
  UInt32.ror x 17 ^^^ UInt32.ror x 19 ^^^ (x >>> 10)

/-! ## §4.2.2 and §5.3.3 — the constants -/

/-- FIPS 180-4 §4.2.2: the sixty-four constant 32-bit words `K₀{256} … K₆₃{256}`,
the first thirty-two bits of the fractional parts of the cube roots of the first
sixty-four prime numbers, in the order the standard tabulates them. -/
def K : Vector UInt32 64 :=
  #v[ 0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5,
      0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
      0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3,
      0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
      0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc,
      0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
      0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
      0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
      0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13,
      0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
      0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3,
      0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
      0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5,
      0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
      0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208,
      0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2 ]

/-- FIPS 180-4 §5.3.3: the initial hash value `H{0}` for SHA-256, the first
thirty-two bits of the fractional parts of the square roots of the first eight
prime numbers. -/
def H0 : Vector UInt32 8 :=
  #v[ 0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
      0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19 ]

/-! ## §5.1.1 and §5.2.1 — padding and parsing -/

/-- FIPS 180-4 §5.1.1: the number of zero *bytes* between the appended `1` bit
and the 64-bit length, for a message of `len` bytes.

The standard states it in bits: append the bit `1`, then `k` zero bits, where
`k` is the smallest non-negative solution of `l + 1 + k ≡ 448 mod 512`. Every
quantity there is a whole number of bytes for a byte-oriented message, so the
same condition reads: pad to `56 mod 64` bytes. -/
def padZeros (len : Nat) : Nat := (119 - len % 64) % 64

/-- FIPS 180-4 §5.1.1: the padded message — the message, the bit `1` as the byte
`0x80`, `k` zero bits, then `l` as a 64-bit big-endian block. -/
def pad (m : List UInt8) : List UInt8 :=
  m ++ ((0x80 : UInt8) ::
    (List.replicate (padZeros m.length) (0x00 : UInt8) ++
      UInt64.toBytes (8 * m.length).toUInt64))

/-- FIPS 180-4 §5.2.1: the padded message is parsed into `N` 512-bit blocks. -/
def blocksN : Nat → List UInt8 → List (List UInt8)
  | 0, _ => []
  | n + 1, m => m.take 64 :: blocksN n (m.drop 64)

/-- FIPS 180-4 §5.2.1: the `N = ℓ / 512` blocks of the padded message. -/
def blocks (m : List UInt8) : List (List UInt8) := blocksN (m.length / 64) m

/-- FIPS 180-4 §5.2.1: a 512-bit block is parsed as sixteen 32-bit words,
big-endian — `M₀{i} … M₁₅{i}`. -/
def toWords (b : List UInt8) : Vector UInt32 16 :=
  Vector.ofFn fun i =>
    UInt32.ofBytes
      (b.getD (4 * i.val) 0)
      (b.getD (4 * i.val + 1) 0)
      (b.getD (4 * i.val + 2) 0)
      (b.getD (4 * i.val + 3) 0)

/-! ## §6.2.2 — the message schedule and the sixty-four rounds -/

/-- FIPS 180-4 §6.2.2, step 1, second case: given `W₀ … W_{t-1}`, the next
schedule entry is `Wₜ = σ₁(W_{t-2}) + W_{t-7} + σ₀(W_{t-15}) + W_{t-16}`. -/
def scheduleStep (W : Array UInt32) (t : Nat) : Array UInt32 :=
  W.push (sigma1 (W.getD (t - 2) 0) + W.getD (t - 7) 0 +
    sigma0 (W.getD (t - 15) 0) + W.getD (t - 16) 0)

/-- FIPS 180-4 §6.2.2, step 1: the sixty-four-entry message schedule of a block.
`Wₜ = Mₜ{i}` for `0 ≤ t ≤ 15`, and the recurrence above for `16 ≤ t ≤ 63`. -/
def schedule (M : Vector UInt32 16) : Array UInt32 :=
  (List.range' 16 48).foldl scheduleStep M.toArray

/-- The eight working variables `a, b, c, d, e, f, g, h` of FIPS 180-4 §6.2.2,
step 2. -/
structure Vars where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

/-- FIPS 180-4 §6.2.2, step 3: one round `t` of the compression function.

    T₁ = h + Σ₁{256}(e) + Ch(e, f, g) + Kₜ{256} + Wₜ
    T₂ = Σ₀{256}(a) + Maj(a, b, c)
    h = g;  g = f;  f = e;  e = d + T₁;  d = c;  c = b;  b = a;  a = T₁ + T₂
-/
def step (W : Array UInt32) (v : Vars) (t : Nat) : Vars :=
  let T₁ : UInt32 :=
    v.h + Sigma1 v.e + Ch v.e v.f v.g + K.getD t 0 + W.getD t 0
  let T₂ : UInt32 := Sigma0 v.a + Maj v.a v.b v.c
  { a := T₁ + T₂, b := v.a, c := v.b, d := v.c,
    e := v.d + T₁, f := v.e, g := v.f, h := v.g }

/-- FIPS 180-4 §6.2.2: the compression function on one block — initialize the
working variables with the current hash value (step 2), run rounds `t = 0` to
`63` (step 3), and compute the next hash value by adding the working variables
into it (step 4). -/
def compress (H : Vector UInt32 8) (M : Vector UInt32 16) : Vector UInt32 8 :=
  let v : Vars :=
    (List.range 64).foldl (step (schedule M))
      { a := H[0], b := H[1], c := H[2], d := H[3],
        e := H[4], f := H[5], g := H[6], h := H[7] }
  #v[ H[0] + v.a, H[1] + v.b, H[2] + v.c, H[3] + v.d,
      H[4] + v.e, H[5] + v.f, H[6] + v.g, H[7] + v.h ]

/-- FIPS 180-4 §6.2: SHA-256 — pad and parse the message (§5.1.1, §5.2.1), then
run the compression function over the blocks in order starting from `H{0}`
(§5.3.3). -/
def hashWords (m : List UInt8) : Vector UInt32 8 :=
  (blocks (pad m)).foldl (fun H b => compress H (toWords b)) H0

/-- FIPS 180-4 §6.2.2: the resulting 256-bit message digest is
`H₀{N} ‖ H₁{N} ‖ H₂{N} ‖ H₃{N} ‖ H₄{N} ‖ H₅{N} ‖ H₆{N} ‖ H₇{N}`. -/
def hash (m : List UInt8) : B256 :=
  let H : Vector UInt32 8 := hashWords m
  B32s.toB256 H[0] H[1] H[2] H[3] H[4] H[5] H[6] H[7]

end SHA256.FIPS

namespace SHA256

open SHA256.FIPS

/-! ## The kernel computes it

Everything below is the bridge from `Jaune/Hash.lean`'s optimized kernel to the
transcription above. -/

/-! ### The message schedule

The kernel never materializes the sixty-four-entry schedule: it keeps sixteen
live words and overwrites `w[t % 16]` with `Wₜ` at round `t`, which is sound
exactly because the recurrence reaches back no further than sixteen entries.
The three lemmas here give the reference schedule the two properties that
bridge needs — that folding only ever appends, and that entry `t` satisfies the
standard's recurrence. -/

/-- Folding `scheduleStep` appends one entry per index. -/
theorem size_schedFold (a : Array UInt32) (s n : Nat) :
    ((List.range' s n).foldl scheduleStep a).size = a.size + n := by
  induction n generalizing a s with
  | zero => simp
  | succ n ih =>
    rw [show List.range' s (n + 1) = s :: List.range' (s + 1) n from rfl]
    rw [List.foldl_cons, ih]
    simp [scheduleStep]
    omega

/-- Pushing never disturbs an entry already present. -/
theorem getD_push_lt (a : Array UInt32) (x : UInt32) (i : Nat) (h : i < a.size) :
    (a.push x).getD i 0 = a.getD i 0 := by
  simp [Array.getD, h, Nat.lt_succ_of_lt, Array.getElem_push_lt]

/-- Folding `scheduleStep` never disturbs an entry already present. -/
theorem getD_schedFold (a : Array UInt32) (s n i : Nat) (h : i < a.size) :
    ((List.range' s n).foldl scheduleStep a).getD i 0 = a.getD i 0 := by
  induction n generalizing a s with
  | zero => simp
  | succ n ih =>
    rw [show List.range' s (n + 1) = s :: List.range' (s + 1) n from rfl]
    rw [List.foldl_cons, ih _ _ (by simp [scheduleStep]; omega)]
    rw [scheduleStep, getD_push_lt _ _ _ h]

/-- The entry a push adds. -/
theorem getD_push_self (a : Array UInt32) (x : UInt32) :
    (a.push x).getD a.size 0 = x := by
  simp [Array.getD]

/-- One more fold step computes the schedule recurrence at the array's own end. -/
theorem getD_schedFold_self (a : Array UInt32) (n : Nat) (hn : 0 < n) :
    ((List.range' a.size n).foldl scheduleStep a).getD a.size 0 =
      sigma1 (a.getD (a.size - 2) 0) + a.getD (a.size - 7) 0 +
        sigma0 (a.getD (a.size - 15) 0) + a.getD (a.size - 16) 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [show List.range' a.size (m + 1) = a.size :: List.range' (a.size + 1) m from rfl,
    List.foldl_cons]
  simp only [scheduleStep]
  rw [getD_schedFold _ _ _ _ (by simp)]
  exact getD_push_self _ _

/-- The schedule has the sixty-four entries FIPS 180-4 §6.2.2 gives it. -/
theorem size_schedule (M : Vector UInt32 16) : (schedule M).size = 64 := by
  simp [schedule, size_schedFold]

/-- FIPS 180-4 §6.2.2, step 1, first case: `Wₜ = Mₜ` for `0 ≤ t ≤ 15`. -/
theorem getD_schedule_lt (M : Vector UInt32 16) (t : Nat) (h : t < 16) :
    (schedule M).getD t 0 = M.toArray.getD t 0 :=
  getD_schedFold _ _ _ _ (by simpa using h)

/-- FIPS 180-4 §6.2.2, step 1, second case: the schedule recurrence, as an
equation about the sixty-four-entry schedule rather than about a rolling
window. -/
theorem getD_schedule_rec (M : Vector UInt32 16) (t : Nat)
    (h16 : 16 ≤ t) (h64 : t < 64) :
    (schedule M).getD t 0 =
      sigma1 ((schedule M).getD (t - 2) 0) + (schedule M).getD (t - 7) 0 +
        sigma0 ((schedule M).getD (t - 15) 0) + (schedule M).getD (t - 16) 0 := by
  have hAsize : ((List.range' 16 (t - 16)).foldl scheduleStep M.toArray).size = t := by
    rw [size_schedFold]; simp; omega
  have hsplit : List.range' 16 48
      = List.range' 16 (t - 16) ++ List.range' t (64 - t) := by
    conv_lhs => rw [show (48 : Nat) = (t - 16) + (64 - t) by omega]
    rw [← List.range'_append_1]
    congr 2
    omega
  have hfold : schedule M = (List.range' t (64 - t)).foldl scheduleStep
      ((List.range' 16 (t - 16)).foldl scheduleStep M.toArray) := by
    rw [schedule, hsplit, List.foldl_append]
  have hpres : ∀ i, i < t → (schedule M).getD i 0
      = ((List.range' 16 (t - 16)).foldl scheduleStep M.toArray).getD i 0 := by
    intro i hi
    rw [hfold]
    exact getD_schedFold _ _ _ _ (by omega)
  rw [hpres (t - 2) (by omega), hpres (t - 7) (by omega), hpres (t - 15) (by omega),
    hpres (t - 16) (by omega), hfold]
  clear hpres hfold hsplit
  generalize (List.range' 16 (t - 16)).foldl scheduleStep M.toArray = A at hAsize ⊢
  subst hAsize
  exact getD_schedFold_self A (64 - A.size) (by omega)

/-! ### The sixty-four rounds

The kernel counts rounds down (`n` remaining, so the round index is
`t = 64 - n`) and carries its working variables as eight scalars; the reference
counts up over `List.range 64` and carries a record. `List.range'` peels one
index per kernel step, which is what lets a single induction on `n` line the
two up. -/

/-- The kernel's eight scalar working variables, as the reference's record. -/
def varsVec (v : FIPS.Vars) : Vector UInt32 8 :=
  #v[v.a, v.b, v.c, v.d, v.e, v.f, v.g, v.h]

/-- The kernel's round-constant table is the standard's `K{256}`.

This is `rfl` and it is still worth stating: the two tables were transcribed
from FIPS 180-4 §4.2.2 independently, so had either drifted, this would not
close. -/
theorem roundConstants_eq : roundConstants = FIPS.K := rfl

/-- The rolling window invariant. At round `t` the kernel's sixteen live words
hold exactly the last sixteen entries of the reference's sixty-four-entry
schedule: `W_{t-k}` sits at index `(t - k) % 16`, for every `k` in range. -/
def WindowOk (M : Vector UInt32 16) (t : Nat) (w : Vector UInt32 16) : Prop :=
  ∀ k, 1 ≤ k → k ≤ 16 → k ≤ t →
    w.getD ((t - k) % 16) 0 = (FIPS.schedule M).getD (t - k) 0

/-- Reading back the word a schedule write just placed. -/
theorem getD_vset_self (w : Vector UInt32 16) (i : Nat) (x : UInt32) (h : i < 16) :
    (w.set i x h).getD i 0 = x := by
  simp [Vector.getD, Array.getD, h]

/-- A schedule write leaves the other fifteen words alone. -/
theorem getD_vset_ne (w : Vector UInt32 16) (i j : Nat) (x : UInt32) (h : i < 16)
    (hj : j < 16) (hne : j ≠ i) :
    (w.set i x h).getD j 0 = w.getD j 0 := by
  have hne' : i ≠ j := Ne.symm hne
  simp [Vector.getD, Array.getD, hj, hne']

theorem rounds_eq (p : Array UInt8) (n : Nat) :
    ∀ (hn : n ≤ 64) (w : Vector UInt32 16) (v : FIPS.Vars),
      WindowOk (FIPS.toWords p.toList) (64 - n) w →
      rounds p n hn w v.a v.b v.c v.d v.e v.f v.g v.h
        = varsVec (List.foldl (FIPS.step (FIPS.schedule (FIPS.toWords p.toList)))
            v (List.range' (64 - n) n)) := by
  induction n with
  | zero => intro hn w v _; rfl
  | succ n ih =>
    intro hn w v hw
    have hKg : ∀ (i : Nat) (h : i < 64), (FIPS.K[i]'h) = FIPS.K.getD i 0 := by
      intro i h; simp [Vector.getD, h]
    simp only [rounds, roundConstants_eq, hKg]
    set t := 64 - (n + 1) with ht
    simp only [← ht]
    have htlt : t < 64 := by omega
    have htn : 64 - n = t + 1 := by omega
    rw [htn] at ih
    rw [show List.range' t (n + 1) = t :: List.range' (t + 1) n from rfl, List.foldl_cons]
    set M := FIPS.toWords p.toList with hM
    set W := FIPS.schedule M with hW
    -- Keep `t`, `M` and `W` opaque from here: `W` is a forty-eight-step fold,
    -- and any tactic that whnf's it pays for the whole schedule.
    clear_value W M
    have hwj :
        (if t < 16 then
            UInt32.ofBytes (p.getD (4 * (t % 16)) 0) (p.getD (4 * (t % 16) + 1) 0)
              (p.getD (4 * (t % 16) + 2) 0) (p.getD (4 * (t % 16) + 3) 0)
          else
            w.getD (t % 16) 0 +
                  (UInt32.ror (w.getD ((t % 16 + 1) % 16) 0) 7 ^^^
                      UInt32.ror (w.getD ((t % 16 + 1) % 16) 0) 18 ^^^
                    w.getD ((t % 16 + 1) % 16) 0 >>> 3) +
                w.getD ((t % 16 + 9) % 16) 0 +
              (UInt32.ror (w.getD ((t % 16 + 14) % 16) 0) 17 ^^^
                  UInt32.ror (w.getD ((t % 16 + 14) % 16) 0) 19 ^^^
                w.getD ((t % 16 + 14) % 16) 0 >>> 10))
          = W.getD t 0 := by
      by_cases hlt : t < 16
      · rw [if_pos hlt, hW, getD_schedule_lt _ _ hlt, hM]
        simp [FIPS.toWords, Nat.mod_eq_of_lt hlt, hlt]
      · rw [if_neg hlt]
        have h16 : 16 ≤ t := by omega
        rw [hW, getD_schedule_rec _ _ h16 htlt]
        rw [show t % 16 = (t - 16) % 16 by omega,
          show ((t - 16) % 16 + 1) % 16 = (t - 15) % 16 by omega,
          show ((t - 16) % 16 + 9) % 16 = (t - 7) % 16 by omega,
          show ((t - 16) % 16 + 14) % 16 = (t - 2) % 16 by omega]
        rw [hw 16 (by omega) (by omega) (by omega), hw 15 (by omega) (by omega) (by omega),
          hw 7 (by omega) (by omega) (by omega), hw 2 (by omega) (by omega) (by omega)]
        -- Both sides now read the same four schedule entries; abstract them so
        -- the reassociation below cannot descend into the schedule fold.
        generalize (FIPS.schedule M).getD (t - 2) 0 = w2
        generalize (FIPS.schedule M).getD (t - 7) 0 = w7
        generalize (FIPS.schedule M).getD (t - 15) 0 = w15
        generalize (FIPS.schedule M).getD (t - 16) 0 = w16
        simp only [FIPS.sigma0, FIPS.sigma1]
        ac_rfl
    rw [hwj]
    refine ih (by omega) _ (FIPS.step W v t) ?_
    intro k hk1 hk16 hkt
    rcases Nat.eq_or_lt_of_le hk1 with hk | hk
    · subst hk
      simp only [Nat.add_sub_cancel]
      rw [getD_vset_self, hW]
    · have hne : (t + 1 - k) % 16 ≠ t % 16 := by omega
      rw [getD_vset_ne _ _ _ _ _ (by omega) hne]
      have := hw (k - 1) (by omega) (by omega) (by omega)
      rw [show t - (k - 1) = t + 1 - k by omega] at this
      exact this

/-- `rounds_eq` with the working variables as the eight scalars the kernel
actually carries, so that it matches `consumeChunk` on the nose. -/
theorem rounds_eq' (p : Array UInt8) (n : Nat) (hn : n ≤ 64) (w : Vector UInt32 16)
    (a b c d e f g h : UInt32)
    (hw : WindowOk (FIPS.toWords p.toList) (64 - n) w) :
    rounds p n hn w a b c d e f g h
      = varsVec (List.foldl (FIPS.step (FIPS.schedule (FIPS.toWords p.toList)))
          ⟨a, b, c, d, e, f, g, h⟩ (List.range' (64 - n) n)) :=
  rounds_eq p n hn w ⟨a, b, c, d, e, f, g, h⟩ hw

/-- All sixty-four rounds, from the kernel's zeroed window: the invariant is
vacuous at round 0, so no hypothesis survives. -/
theorem rounds_eq_full (p : Array UInt8) (a b c d e f g h : UInt32) :
    rounds p 64 (by omega) (Vector.replicate 16 0) a b c d e f g h
      = varsVec (List.foldl (FIPS.step (FIPS.schedule (FIPS.toWords p.toList)))
          ⟨a, b, c, d, e, f, g, h⟩ (List.range 64)) := by
  rw [List.range_eq_range']
  exact rounds_eq' p 64 (by omega) _ a b c d e f g h (by intro k hk1 _ hkt; omega)

/-- The kernel's compression of one 64-byte chunk is the standard's, on the
sixteen words that chunk parses to. -/
theorem consumeChunk_eq (H : Vector UInt32 8) (p : Array UInt8) :
    consumeChunk H p = FIPS.compress H (FIPS.toWords p.toList) := by
  have key := rounds_eq_full p H[0] H[1] H[2] H[3] H[4] H[5] H[6] H[7]
  simp only [consumeChunk, FIPS.compress, key]
  rfl

end SHA256

end Jaune
