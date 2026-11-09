import Jaune.Hash

/-!
# Keccak-256 as published, and the kernel's equivalence to it

`Jaune/Hash.lean`'s `KECCAK` namespace is an optimized hash, ported from a C
implementation: the state is twenty-five 64-bit lanes, the permutation is
twenty-four unrolled rounds with the ρ and π steps fused into one table-driven
pass, the round constants are a table, and padding is fused into the
eight-byte absorb loop. None of that is visible in FIPS 202, and none of it
should be: the standard defines Keccak with a 1600-bit state string, five step
mappings written in `(x, y, z)` coordinates, ρ offsets and round constants
*computed* by small algorithms, and a sponge over a bit string padded with
pad10*1.

This module is that definition, transcribed from **NIST FIPS 202** (*SHA-3
Standard: Permutation-Based Hash and Extendable-Output Functions*, August
2015) — section and algorithm numbers are cited at each declaration — and
`Bytes.keccak_eq_fips` at the end proves the kernel computes it, for every
input.

The transcription is written from the standard, never read back out of the
kernel: the state is the standard's bit string `S` with its array view
`A[x, y, z] = S[w(5y + x) + z]`, the ρ offsets come from Algorithm 2's
`t`-loop, the round constants from Algorithm 5's linear feedback shift
register, and the padding is Algorithm 9's `1 ‖ 0^j ‖ 1`. Nothing here
mentions a lane table, a rotation table, a round-constant table, or a byte
pattern. Where the kernel and this module disagree in *value*, this module is
right by definition and the kernel is wrong.

Ethereum's Keccak-256 is `KECCAK[512](M, 256)` (§5.2) with no domain
separation suffix. SHA3-256 (§6.1) is `KECCAK[512](M ‖ 01, 256)`, a different
function, and is not defined here.

Nothing here is on any execution path. The hash Jaune computes is
`Bytes.keccak`; these declarations exist to be read against the standard and to
give that function something to be equal to.
-/

namespace Jaune

open Jaune

namespace Keccak.FIPS

/-! ## §3.1 — the state -/

/-- FIPS 202 §3.1, Table 1: for `b = 1600`, the lane size `w = b / 25 = 64` and
`ℓ = log₂ w = 6`. -/
def w : Nat := 64

/-- FIPS 202 §3.1, Table 1: `ℓ = log₂(w) = 6`. -/
def ℓ : Nat := 6

/-- FIPS 202 §3.1: the state of Keccak-p[1600, nᵣ] is a string `S` of
`b = 1600` bits, `S[0] … S[1599]`. -/
abbrev State := Vector Bool 1600

/-- FIPS 202 §3.1.2 (converting strings to state arrays): the state array view
of the string `S`, `A[x, y, z] = S[w(5y + x) + z]` for `0 ≤ x < 5`, `0 ≤ y < 5`,
`0 ≤ z < w`. -/
def A (S : State) (x y : Fin 5) (z : Fin 64) : Bool :=
  S[w * (5 * y.val + x.val) + z.val]'(by
    have := x.isLt; have := y.isLt; have := z.isLt; unfold w; omega)

/-- FIPS 202 §3.1.3 (converting state arrays to strings): the string of a state
array `a`, `S = Plane(0) ‖ … ‖ Plane(4)` with `Plane(j) = Lane(0, j) ‖ … ‖
Lane(4, j)` and `Lane(i, j) = a[i, j, 0] ‖ … ‖ a[i, j, w − 1]`. Bit `n` of that
concatenation lies in plane `n / 320`, lane `(n / 64) mod 5` of the plane, at
position `n mod 64` of the lane; written per bit, this is the inverse of
`A`. -/
def toState (a : Fin 5 → Fin 5 → Fin 64 → Bool) : State :=
  Vector.ofFn fun n =>
    a ⟨n.val / 64 % 5, Nat.mod_lt _ (by decide)⟩
      ⟨n.val / 320, by have := n.isLt; omega⟩
      ⟨n.val % 64, Nat.mod_lt _ (by decide)⟩

/-! ## §3.2 — the step mappings -/

/-- FIPS 202 §3.2.1, Algorithm 1, θ(A):
1. `C[x, z] = A[x, 0, z] ⊕ A[x, 1, z] ⊕ A[x, 2, z] ⊕ A[x, 3, z] ⊕ A[x, 4, z]`;
2. `D[x, z] = C[(x − 1) mod 5, z] ⊕ C[(x + 1) mod 5, (z − 1) mod w]`;
3. `A′[x, y, z] = A[x, y, z] ⊕ D[x, z]`.
Arithmetic on `Fin 5` and `Fin 64` is modulo 5 and modulo `w`. -/
def θ (S : State) : State :=
  let C (x : Fin 5) (z : Fin 64) : Bool :=
    A S x 0 z ^^ A S x 1 z ^^ A S x 2 z ^^ A S x 3 z ^^ A S x 4 z
  let D (x : Fin 5) (z : Fin 64) : Bool := C (x - 1) z ^^ C (x + 1) (z - 1)
  toState fun x y z => A S x y z ^^ D x z

/-- FIPS 202 §3.2.2, Algorithm 2, step 3: the coordinates visited by ρ's loop,
starting from `(x, y) = (1, 0)` and updated by `(x, y) = (y, (2x + 3y) mod 5)`
after each of the 24 iterations. `ρPos t` is `(x, y)` at iteration `t`. -/
def ρPos : Nat → Fin 5 × Fin 5
  | 0 => (1, 0)
  | t + 1 => let p := ρPos t; (p.2, 2 * p.1 + 3 * p.2)

/-- FIPS 202 §3.2.2, Algorithm 2, ρ(A):
1. for all `z`, `A′[0, 0, z] = A[0, 0, z]`;
2. let `(x, y) = (1, 0)`;
3. for `t` from 0 to 23: (a) for all `z`, `A′[x, y, z] = A[x, y, (z − (t + 1)(t + 2)/2) mod w]`;
   (b) let `(x, y) = (y, (2x + 3y) mod 5)`.
The array `A′` is built by the same sequence of assignments: lane `(0, 0)`
first (the other lanes start unassigned, written `false`, and every one of
them is assigned by the loop), then one lane per iteration of the loop. -/
def ρ (S : State) : State :=
  let A₀ : Fin 5 → Fin 5 → Fin 64 → Bool :=
    fun x y z => if x = 0 ∧ y = 0 then A S 0 0 z else false
  let step (A' : Fin 5 → Fin 5 → Fin 64 → Bool) (t : Nat) :
      Fin 5 → Fin 5 → Fin 64 → Bool :=
    let p := ρPos t
    fun x y z =>
      if x = p.1 ∧ y = p.2 then A S p.1 p.2 (z - Fin.ofNat 64 ((t + 1) * (t + 2) / 2))
      else A' x y z
  toState ((List.range 24).foldl step A₀)

/-- FIPS 202 §3.2.3, Algorithm 3, π(A): `A′[x, y, z] = A[(x + 3y) mod 5, x, z]`. -/
def π (S : State) : State :=
  toState fun x y z => A S (x + 3 * y) x z

/-- FIPS 202 §3.2.4, Algorithm 4, χ(A):
`A′[x, y, z] = A[x, y, z] ⊕ ((A[(x + 1) mod 5, y, z] ⊕ 1) ⋅ A[(x + 2) mod 5, y, z])`. -/
def χ (S : State) : State :=
  toState fun x y z => A S x y z ^^ ((A S (x + 1) y z ^^ true) && A S (x + 2) y z)

/-- FIPS 202 §3.2.5, Algorithm 5, one iteration of step 3 on the eight-bit
register `R = R[0] … R[7]`:
(a) `R = 0 ‖ R`; (b) `R[0] = R[0] ⊕ R[8]`; (c) `R[4] = R[4] ⊕ R[8]`;
(d) `R[5] = R[5] ⊕ R[8]`; (e) `R[6] = R[6] ⊕ R[8]`; (f) `R = Trunc₈[R]`. -/
def rcStep (R : List Bool) : List Bool :=
  let R := false :: R
  let r8 := R.getD 8 false
  let R := R.set 0 (R.getD 0 false ^^ r8)
  let R := R.set 4 (R.getD 4 false ^^ r8)
  let R := R.set 5 (R.getD 5 false ^^ r8)
  let R := R.set 6 (R.getD 6 false ^^ r8)
  R.take 8

/-- FIPS 202 §3.2.5, Algorithm 5, rc(t):
1. if `t mod 255 = 0`, return 1;
2. let `R = 10000000`;
3. for `i` from 1 to `t mod 255`, apply the register step;
4. return `R[0]`. -/
def rc (t : Nat) : Bool :=
  if t % 255 = 0 then true
  else ((List.range (t % 255)).foldl (fun R _ => rcStep R)
    [true, false, false, false, false, false, false, false]).getD 0 false

/-- FIPS 202 §3.2.5, Algorithm 6, steps 2–3: the round constant `RC`, a string
of `w` zero bits in which `RC[2^j − 1] = rc(j + 7iᵣ)` for `j` from 0 to `ℓ`. -/
def RC (ir : Nat) : List Bool :=
  (List.range (ℓ + 1)).foldl (fun RC j => RC.set (2 ^ j - 1) (rc (j + 7 * ir)))
    (List.replicate w false)

/-- FIPS 202 §3.2.5, Algorithm 6, ι(A, iᵣ):
1. `A′[x, y, z] = A[x, y, z]` for all triples;
2.–3. the round constant `RC` (see `RC`);
4. for all `z`, `A′[0, 0, z] = A′[0, 0, z] ⊕ RC[z]`. -/
def ι (S : State) (ir : Nat) : State :=
  toState fun x y z =>
    if x = 0 ∧ y = 0 then A S x y z ^^ (RC ir).getD z.val false else A S x y z

/-! ## §3.3 — Keccak-p[1600, nᵣ] -/

/-- FIPS 202 §3.3: `Rnd(A, iᵣ) = ι(χ(π(ρ(θ(A)))), iᵣ)`. -/
def Rnd (S : State) (ir : Nat) : State := ι (χ (π (ρ (θ S)))) ir

/-- FIPS 202 §3.3, Algorithm 7, Keccak-p[1600, nᵣ](S):
1. convert `S` into a state array `A` (§3.1.2);
2. for `iᵣ` from `12 + 2ℓ − nᵣ` to `12 + 2ℓ − 1`, let `A = Rnd(A, iᵣ)`;
3. convert `A` into a string `S′` (§3.1.3).
The state is kept as the string throughout, read through `A`; steps 1 and 3
are the views `A` and `toState` inside each step mapping. -/
def keccakP (nr : Nat) (S : State) : State :=
  (List.range' (12 + 2 * ℓ - nr) nr).foldl Rnd S

/-- FIPS 202 §3.4: Keccak-f[1600] = Keccak-p[1600, 24]. -/
def keccakF (S : State) : State := keccakP 24 S

/-! ## §4, §5 — the sponge, pad10*1, and KECCAK[c] -/

/-- FIPS 202 §4: `S ⊕ T` for a string `T` of length `b` (here, `Pᵢ ‖ 0^c`). -/
def xorState (S : State) (T : List Bool) : State :=
  Vector.ofFn fun n => S[n] ^^ T.getD n.val false

/-- FIPS 202 §4, Algorithm 8, the squeezing loop, steps 7–10:
7. let `Z` be the empty string; 8. let `Z = Z ‖ Truncᵣ(S)`;
9. if `d ≤ |Z|`, return `Trunc_d(Z)`; else 10. let `S = f(S)` and continue
with step 8. `fuel` bounds the number of passes (each adds `r` bits, so `d + 1`
passes suffice whenever `r ≥ 1`). -/
def squeeze (f : State → State) (r d : Nat) : Nat → State → List Bool → List Bool
  | 0, _, Z => Z.take d
  | fuel + 1, S, Z =>
    let Z := Z ++ S.toList.take r
    if d ≤ Z.length then Z.take d else squeeze f r d fuel (f S) Z

/-- FIPS 202 §4, Algorithm 8, SPONGE[f, pad, r](N, d):
1. `P = N ‖ pad(r, len(N))`; 2. `n = len(P)/r`; 3. `c = b − r`;
4. `P₀, …, Pₙ₋₁` the strings of length `r` with `P = P₀ ‖ … ‖ Pₙ₋₁`;
5. `S = 0^b`; 6. for `i` from 0 to `n − 1`, `S = f(S ⊕ (Pᵢ ‖ 0^c))`;
7.–10. squeeze (see `squeeze`). -/
def sponge (f : State → State) (pad : Nat → Nat → List Bool) (r : Nat)
    (N : List Bool) (d : Nat) : List Bool :=
  let P := N ++ pad r N.length
  let n := P.length / r
  let c := 1600 - r
  let Ps := (List.range n).map fun i => (P.drop (i * r)).take r
  let S := Ps.foldl (fun S Pi => f (xorState S (Pi ++ List.replicate c false)))
    (Vector.replicate 1600 false)
  squeeze f r d (d + 1) S []

/-- FIPS 202 §5.1, Algorithm 9, pad10*1(x, m):
1. `j = (−m − 2) mod x`; 2. return `P = 1 ‖ 0^j ‖ 1`. -/
def pad101 (x m : Nat) : List Bool :=
  let j := ((-(m : Int) - 2) % (x : Int)).toNat
  true :: List.replicate j false ++ [true]

/-- FIPS 202 §5.2: `KECCAK[c] = SPONGE[Keccak-p[1600, 24], pad10*1, 1600 − c]`,
so `KECCAK[c](N, d) = SPONGE[Keccak-p[1600, 24], pad10*1, 1600 − c](N, d)`. -/
def KECCAK (c : Nat) (N : List Bool) (d : Nat) : List Bool :=
  sponge (keccakP 24) pad101 (1600 - c) N d

/-! ## Appendix B.1 — bytes and bit strings -/

/-- FIPS 202 Appendix B.1, Algorithm 10 (h2b): the bit string of a byte
string. Byte `i` contributes bits `8i … 8i + 7`, least significant bit first:
`T[8i + j]` is bit `j` of the byte, so that the byte's value is
`Σⱼ T[8i + j] ⋅ 2^j`. -/
def h2b (M : List UInt8) : List Bool :=
  M.flatMap fun h => (List.range 8).map fun j => h.toNat.testBit j

/-- FIPS 202 Appendix B.1, Algorithm 11 (b2h): the byte string of a bit string
`S` (here of length a multiple of 8): byte `i` has value
`Σⱼ S[8i + j] ⋅ 2^j` for `j` from 0 to 7. -/
def b2h (S : List Bool) : List UInt8 :=
  (List.range ((S.length + 7) / 8)).map fun i =>
    UInt8.ofNat ((List.range 8).map fun j =>
      if S.getD (8 * i + j) false then 2 ^ j else 0).sum

/-! ## Keccak-256 -/

/-- Keccak-256 of a byte string, as the 32-byte digest:
`b2h(KECCAK[512](h2b(M), 256))` (FIPS 202 §5.2 with `c = 512`, `d = 256`;
Appendix B.1 for the byte/bit conversions). -/
def keccak256Digest (M : Bytes) : Bytes := b2h (KECCAK 512 (h2b M) 256)

/-- Keccak-256 as a 256-bit word: the 32-byte digest read big-endian, digest
byte 0 most significant (the Ethereum convention for hash words). -/
def keccak256 (M : Bytes) : B256 :=
  let d := keccak256Digest M
  ⟨⟨UInt64.ofBytes (d.getD 0 0) (d.getD 1 0) (d.getD 2 0) (d.getD 3 0)
      (d.getD 4 0) (d.getD 5 0) (d.getD 6 0) (d.getD 7 0),
    UInt64.ofBytes (d.getD 8 0) (d.getD 9 0) (d.getD 10 0) (d.getD 11 0)
      (d.getD 12 0) (d.getD 13 0) (d.getD 14 0) (d.getD 15 0)⟩,
   ⟨UInt64.ofBytes (d.getD 16 0) (d.getD 17 0) (d.getD 18 0) (d.getD 19 0)
      (d.getD 20 0) (d.getD 21 0) (d.getD 22 0) (d.getD 23 0),
    UInt64.ofBytes (d.getD 24 0) (d.getD 25 0) (d.getD 26 0) (d.getD 27 0)
      (d.getD 28 0) (d.getD 29 0) (d.getD 30 0) (d.getD 31 0)⟩⟩

/- Known answer: Keccak-256 of the empty string is
`c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470`, the code
hash of every account without code. Source: the official Ethereum test
fixtures, e.g. EEST `constantinople/eip1052_extcodehash/extcodehash/
extcodehash_of_empty` and ethereum/tests `GeneralStateTests/stExtCodeHash/
codeCopyZero` (the `EXTCODEHASH` of a codeless account, stored as the expected
post-state value). This evaluates the transcription alone; it does not touch
the kernel. -/
#guard keccak256Digest [] ==
    [0xc5, 0xd2, 0x46, 0x01, 0x86, 0xf7, 0x23, 0x3c, 0x92, 0x7e, 0x7d, 0xb2,
     0xdc, 0xc7, 0x03, 0xc0, 0xe5, 0x00, 0xb6, 0x53, 0xca, 0x82, 0x27, 0x3b,
     0x7b, 0xfa, 0xd8, 0x04, 0x5d, 0x85, 0xa4, 0x70]

/-! ## The kernel computes it -/

section Proof

/-- The state string of the kernel's 25 lanes: lane `(x, y)` is
`ws[x + 5y]`, and bit `z` of the lane is `A[x, y, z]`. -/
def ofLanes (ws : Vector UInt64 25) : State :=
  toState fun x y z => (ws[x.val + 5 * y.val]'(by omega)).toBitVec.getLsbD z.val

theorem A_toState (a : Fin 5 → Fin 5 → Fin 64 → Bool) (x y : Fin 5) (z : Fin 64) :
    A (toState a) x y z = a x y z := by
  simp only [A, toState, w, Vector.getElem_ofFn]
  congr 1 <;> [skip; skip; skip] <;> ext <;> simp <;> omega

theorem rol_getLsbD (v : UInt64) (n : Nat) (hn : n < 64) (z : Fin 64) :
    (KECCAK.UInt64.rol v n).toBitVec.getLsbD z.val =
      v.toBitVec.getLsbD (z - Fin.ofNat 64 n).val := by
  obtain ⟨z, hz⟩ := z
  simp only [KECCAK.UInt64.rol, Fin.sub_def, Fin.ofNat]
  simp [Nat.mod_eq_of_lt hn, hz]
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp [Nat.mod_eq_of_lt hz, BitVec.getLsbD_eq_getElem hz]
  · rw [Nat.mod_eq_of_lt (by omega : 64 - n < 64)]
    by_cases hzn : z < n
    · simp [hzn, Nat.mod_eq_of_lt (by omega : 64 - n + z < 64)]
    · have h1 : (64 - n + z) % 64 = z - n := by omega
      simp [hzn, h1, BitVec.getLsbD_of_ge v.toBitVec (64 - n + z) (by omega),
        BitVec.getLsbD_eq_getElem (by omega : z - n < 64)]

theorem rol_getElem (v : UInt64) (n : Nat) (hn : n < 64) (z : Fin 64) :
    (KECCAK.UInt64.rol v n).toBitVec[z.val] =
      v.toBitVec[(z - Fin.ofNat 64 n).val] := by
  have := rol_getLsbD v n hn z
  simpa [BitVec.getLsbD_eq_getElem] using this

theorem A_ofLanes (v : Vector UInt64 25) (x y : Fin 5) (z : Fin 64) :
    A (ofLanes v) x y z = (v[x.val + 5 * y.val]'(by omega)).toBitVec.getLsbD z.val :=
  A_toState _ x y z

theorem ofLanes_eq (u : Vector UInt64 25) (g : Fin 5 → Fin 5 → Fin 64 → Bool)
    (h : ∀ x y z, (u[x.val + 5 * y.val]'(by omega)).toBitVec.getLsbD z.val = g x y z) :
    ofLanes u = toState g :=
  congrArg toState (funext fun x => funext fun y => funext fun z => h x y z)

theorem theta_ofLanes (v : Vector UInt64 25) :
    ofLanes (KECCAK.θ KECCAK.UInt64.rol v) = θ (ofLanes v) := by
  have h := KECCAK.theta_lit v[0] v[1] v[2] v[3] v[4] v[5] v[6] v[7] v[8] v[9] v[10] v[11] v[12] v[13] v[14] v[15] v[16] v[17] v[18] v[19] v[20] v[21] v[22] v[23] v[24]
  rw [← KECCAK.vec_eta v] at h
  rw [h, θ]
  clear h
  refine ofLanes_eq _ _ ?_
  intro x y z
  simp only [A_ofLanes]
  rcases x with ⟨_ | _ | _ | _ | _ | x, hx⟩ <;>
    rcases y with ⟨_ | _ | _ | _ | _ | y, hy⟩ <;> try omega
  all_goals simp [UInt64.toBitVec_xor, rol_getElem]
  all_goals rfl

theorem fin64_sub_zero (z : Fin 64) : z - 0 = z := by
  ext; simp

/-- The ρ offsets of FIPS 202 Table 2, reduced mod 64, indexed by `x + 5y`.
Proof-side only: the specification computes them with Algorithm 2's loop, and
`ρ_eq` checks that loop against this table. -/
def ρOff (x y : Fin 5) : Fin 64 :=
  (#v[0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8,
      18, 2, 61, 56, 14] : Vector (Fin 64) 25)[x.val + 5 * y.val]'(by omega)

theorem ρ_eq (S : State) : ρ S = toState fun x y z => A S x y (z - ρOff x y) := by
  unfold ρ
  refine congrArg toState (funext fun x => funext fun y => funext fun z => ?_)
  rcases x with ⟨_ | _ | _ | _ | _ | x, hx⟩ <;>
    rcases y with ⟨_ | _ | _ | _ | _ | y, hy⟩ <;> try omega
  all_goals first
    | rfl
    | exact (congrArg (A S _ _) (fin64_sub_zero z)).symm

theorem rhopi_ofLanes (v : Vector UInt64 25) :
    ofLanes (KECCAK.ρπ KECCAK.UInt64.rol v) = π (ρ (ofLanes v)) := by
  have h := KECCAK.rhopi_lit v[0] v[1] v[2] v[3] v[4] v[5] v[6] v[7] v[8] v[9] v[10] v[11] v[12] v[13] v[14] v[15] v[16] v[17] v[18] v[19] v[20] v[21] v[22] v[23] v[24]
  rw [← KECCAK.vec_eta v] at h
  rw [h, π, ρ_eq]
  clear h
  refine ofLanes_eq _ _ ?_
  intro x y z
  simp only [A_toState, A_ofLanes]
  rcases x with ⟨_ | _ | _ | _ | _ | x, hx⟩ <;>
    rcases y with ⟨_ | _ | _ | _ | _ | y, hy⟩ <;> try omega
  all_goals simp [rol_getElem, ρOff]
  all_goals rfl

theorem chi_ofLanes (v : Vector UInt64 25) :
    ofLanes (KECCAK.χ v) = χ (ofLanes v) := by
  have h := KECCAK.chi_lit v[0] v[1] v[2] v[3] v[4] v[5] v[6] v[7] v[8] v[9] v[10] v[11] v[12] v[13] v[14] v[15] v[16] v[17] v[18] v[19] v[20] v[21] v[22] v[23] v[24]
  rw [← KECCAK.vec_eta v] at h
  rw [h, χ]
  clear h
  refine ofLanes_eq _ _ ?_
  intro x y z
  simp only [A_ofLanes]
  rcases x with ⟨_ | _ | _ | _ | _ | x, hx⟩ <;>
    rcases y with ⟨_ | _ | _ | _ | _ | y, hy⟩ <;> try omega
  all_goals simp

/-- Algorithm 5 and 6's round constants agree, bit for bit, with the kernel's
`rndc` table. Decided by evaluating the LFSR in the kernel. -/
theorem RC_eq : ∀ r : Fin 24,
    RC r.val = (List.range 64).map fun z => (KECCAK.rndc[r.val]).toBitVec.getLsbD z := by
  decide +kernel

theorem RC_getD (r : Nat) (h : r < 24) (z : Fin 64) :
    (RC r).getD z.val false = (KECCAK.rndc[r]).toBitVec[z.val] := by
  have := RC_eq ⟨r, h⟩
  simp only at this
  rw [this]
  simp [BitVec.getLsbD_eq_getElem]

theorem iota_ofLanes (r : Nat) (h : r < 24) (v : Vector UInt64 25) :
    ofLanes (KECCAK.ι r h KECCAK.rndc v) = ι (ofLanes v) r := by
  rw [ι]
  refine ofLanes_eq _ _ ?_
  intro x y z
  simp only [A_ofLanes]
  by_cases hxy : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := hxy
    simp [KECCAK.ι, KECCAK.xorLane]
    rw [← List.getD_eq_getElem?_getD, RC_getD r h z]
  · have hne : x.val + 5 * y.val ≠ 0 := by
      intro h0; apply hxy; constructor <;> ext <;> simp <;> omega
    simp [KECCAK.ι, KECCAK.xorLane, Ne.symm hne, hxy]

theorem round_ofLanes (r : Nat) (h : r < 24) (v : Vector UInt64 25) :
    ofLanes (KECCAK.ι r h KECCAK.rndc
        (KECCAK.χ (KECCAK.ρπ KECCAK.UInt64.rol (KECCAK.θ KECCAK.UInt64.rol v)))) =
      Rnd (ofLanes v) r := by
  rw [iota_ofLanes, chi_ofLanes, rhopi_ofLanes, theta_ofLanes, Rnd]

theorem f_aux_ofLanes (n : Nat) (hn : n ≤ 24) (v : Vector UInt64 25) :
    ofLanes (KECCAK.f.aux KECCAK.rndc KECCAK.UInt64.rol n hn v) =
      (List.range' (24 - n) n).foldl Rnd (ofLanes v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [KECCAK.f.aux, ih, round_ofLanes,
      show 24 - (n + 1) = 23 - n by omega, List.range'_succ,
      show 23 - n + 1 = 24 - n by omega, List.foldl_cons]

/-- **The kernel's permutation is Keccak-p[1600, 24].** Under the §3.1.2
packing of the 25 lanes into the state string (`ofLanes`), `KECCAK.f1600`
computes FIPS 202's Keccak-p[1600, 24] (Algorithm 7) on every state. -/
theorem f1600_eq_keccakP (ws : Vector UInt64 25) :
    ofLanes (KECCAK.f1600 ws) = keccakP 24 (ofLanes ws) := by
  rw [KECCAK.f1600_eq, KECCAK.f, f_aux_ofLanes]
  rfl

end Proof

end Keccak.FIPS

end Jaune
