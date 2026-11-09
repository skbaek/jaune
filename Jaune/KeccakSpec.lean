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

/-- Bytes `8i … 8i + 7` of a digest as a big-endian 64-bit word. -/
def word (d : Bytes) (i : Nat) : UInt64 :=
  UInt64.ofBytes (d.getD (8 * i) 0) (d.getD (8 * i + 1) 0) (d.getD (8 * i + 2) 0)
    (d.getD (8 * i + 3) 0) (d.getD (8 * i + 4) 0) (d.getD (8 * i + 5) 0)
    (d.getD (8 * i + 6) 0) (d.getD (8 * i + 7) 0)

/-- Keccak-256 as a 256-bit word: the 32-byte digest read big-endian, digest
byte 0 most significant (the Ethereum convention for hash words). -/
def keccak256 (M : Bytes) : B256 :=
  let d := keccak256Digest M
  ⟨⟨word d 0, word d 1⟩, ⟨word d 2, word d 3⟩⟩

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

/-! ### Bytes, bits, and lanes -/

/-- Bit `n` of a byte string in Appendix B.1 order: bit `n mod 8` of byte
`n / 8`, and `false` past the end. -/
def bbit (B : List UInt8) (n : Nat) : Bool := (B.getD (n / 8) 0).toNat.testBit (n % 8)

theorem h2b_getD (B : List UInt8) (n : Nat) : (h2b B).getD n false = bbit B n := by
  induction B generalizing n with
  | nil => simp [h2b, bbit]
  | cons b B ih =>
    have ih' := ih (n - 8)
    simp only [h2b, List.flatMap_cons] at ih' ⊢
    by_cases hn : n < 8
    · simp only [List.getD_eq_getElem?_getD] at ih' ⊢
      rw [List.getElem?_append_left (by simpa using hn)]
      simp [bbit, Nat.div_eq_of_lt hn, Nat.mod_eq_of_lt hn, hn]
    · simp only [List.getD_eq_getElem?_getD] at ih' ⊢
      rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_map, List.length_range, ih', bbit]
      have h1 : n / 8 = (n - 8) / 8 + 1 := by omega
      have h2 : n % 8 = (n - 8) % 8 := by omega
      rw [h1, h2]
      simp

theorem length_h2b (B : List UInt8) : (h2b B).length = 8 * B.length := by
  induction B with
  | nil => rfl
  | cons b B ih => simp [h2b] at ih ⊢; rw [ih]; omega

theorem ofLanes_getElem (u : Vector UInt64 25) (n : Nat) (hn : n < 1600) :
    (ofLanes u)[n] = (u[n / 64]'(by omega)).toBitVec.getLsbD (n % 64) := by
  simp only [ofLanes, toState, Vector.getElem_ofFn]
  have h : n / 64 % 5 + 5 * (n / 320) = n / 64 := by omega
  simp only [h]

theorem xorState_getElem (S : State) (T : List Bool) (n : Nat) (hn : n < 1600) :
    (xorState S T)[n] = (S[n] ^^ T.getD n false) := by
  simp [xorState]

theorem ofBytes_getLsbD (a0 a1 a2 a3 a4 a5 a6 a7 : UInt8) (z : Nat) (hz : z < 64) :
    (UInt64.ofBytes a7 a6 a5 a4 a3 a2 a1 a0).toBitVec.getLsbD z =
      bbit [a0, a1, a2, a3, a4, a5, a6, a7] z := by
  have hc : z / 8 = 0 ∨ z / 8 = 1 ∨ z / 8 = 2 ∨ z / 8 = 3 ∨ z / 8 = 4 ∨ z / 8 = 5 ∨
      z / 8 = 6 ∨ z / 8 = 7 := by omega
  simp only [UInt64.ofBytes, bbit]
  simp [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft]
  rcases hc with h | h | h | h | h | h | h | h <;>
    simp (disch := omega) [h, decide_eq_true, decide_eq_false] <;>
    simp [BitVec.getElem_eq_testBit_toNat] <;> congr 1 <;> omega

theorem bbit_of_le (P : List UInt8) (n : Nat) (h : P.length ≤ n / 8) : bbit P n = false := by
  simp [bbit, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem bbit_append (P Q : List UInt8) (n : Nat) :
    bbit (P ++ Q) n = if n / 8 < P.length then bbit P n else bbit Q (n - 8 * P.length) := by
  unfold bbit
  split
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    have h1 : n / 8 - P.length = (n - 8 * P.length) / 8 := by omega
    have h2 : n % 8 = (n - 8 * P.length) % 8 := by omega
    rw [h1, h2]

theorem getElem_xorLane (ws : Vector UInt64 25) (k : Nat) (hk : k < 25) (t : UInt64)
    (l : Nat) (hl : l < 25) :
    (KECCAK.xorLane ws k hk t)[l] = if k = l then ws[k] ^^^ t else ws[l] := by
  simp only [KECCAK.xorLane, Vector.getElem_set]

/-- Absorbing eight bytes into lane `wc` XORs their Appendix B.1 bits into the
state string at bits `64·wc … 64·wc + 63`. -/
theorem ofLanes_xorLane_bytes (ws : Vector UInt64 25) (S : State) (pend : Bytes)
    (wc : Nat) (hwc : wc < 17) (hp : pend.length = 8 * wc)
    (h : ofLanes ws = xorState S (h2b pend)) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    ofLanes (KECCAK.xorLane ws wc (by omega) (UInt64.ofBytes b7 b6 b5 b4 b3 b2 b1 b0)) =
      xorState S (h2b (pend ++ [b0, b1, b2, b3, b4, b5, b6, b7])) := by
  apply Vector.ext
  intro n hn
  have hn' := congrArg (·[n]'hn) h
  simp only [ofLanes_getElem, xorState_getElem, h2b_getD] at hn' ⊢
  rw [getElem_xorLane, bbit_append, hp]
  by_cases hl : wc = n / 64
  · subst hl
    have hc : ¬ (n / 8 < 8 * (n / 64)) := by omega
    simp only [↓reduceIte, hc, UInt64.toBitVec_xor, BitVec.getLsbD_xor]
    rw [hn', ofBytes_getLsbD _ _ _ _ _ _ _ _ _ (Nat.mod_lt _ (by decide)),
      bbit_of_le _ _ (by omega)]
    have h1 : n % 64 / 8 = (n - 8 * (8 * (n / 64))) / 8 := by omega
    have h2 : n % 64 % 8 = (n - 8 * (8 * (n / 64))) % 8 := by omega
    simp [bbit, h1, h2]
  · simp only [hl, ↓reduceIte]
    rw [hn']
    by_cases hlt : n / 64 < wc
    · have hc : n / 8 < 8 * wc := by omega
      simp only [hc, ↓reduceIte]
    · have hc : ¬ (n / 8 < 8 * wc) := by omega
      simp only [hc, ↓reduceIte]
      rw [bbit_of_le _ _ (by omega), bbit_of_le _ _ (by simp; omega)]

theorem pad101_eq (m : Nat) (hm : m ≤ 1086) :
    pad101 1088 m = true :: List.replicate (1086 - m) false ++ [true] := by
  simp only [pad101]
  congr 3
  omega

theorem pad_getD (j k : Nat) :
    (true :: List.replicate j false ++ [true]).getD k false =
      (decide (k = 0) || decide (k = j + 1)) := by
  rcases k with _ | k
  · simp
  · simp only [List.cons_append, List.getD_eq_getElem?_getD, List.getElem?_cons_succ]
    by_cases hk : k < j
    · rw [List.getElem?_append_left (by simpa using hk)]
      simp [hk]; omega
    · rw [List.getElem?_append_right (by simp; omega)]
      by_cases hk' : k = j
      · subst hk'; simp
      · rw [List.getElem?_eq_none (by simp; omega)]; simp; omega

theorem shift_getLsbD : ∀ z, z < 64 → ((8 : UInt64) <<< 60).toBitVec.getLsbD z = decide (z = 63) := by
  decide

theorem bbit_single_one (i : Nat) : bbit [1] i = decide (i = 0) := by
  rcases Nat.lt_or_ge i 8 with h | h
  · have key : ∀ i, i < 8 → bbit [1] i = decide (i = 0) := by decide
    exact key i h
  · rw [bbit_of_le _ _ (by simp; omega)]; simp; omega

theorem bbit_one (bs : Bytes) (k : Nat) :
    bbit (bs ++ [1]) k =
      if k / 8 < bs.length then bbit bs k else decide (k = 8 * bs.length) := by
  rw [bbit_append]
  split
  · rfl
  · rw [bbit_single_one]; simp; omega

theorem getD_append' {α : Type} (l₁ l₂ : List α) (n : Nat) (d : α) :
    (l₁ ++ l₂).getD n d = if n < l₁.length then l₁.getD n d else l₂.getD (n - l₁.length) d := by
  simp only [List.getD_eq_getElem?_getD]
  split
  · rw [List.getElem?_append_left (by omega)]
  · rw [List.getElem?_append_right (by omega)]

/-- The final absorb: the kernel's last lane (the remaining bytes, then the
byte `0x01`, zero-filled) and its top bit of lane 16 are exactly pad10*1 of
the whole message under Appendix B.1's bit order. -/
theorem ofLanes_final (ws : Vector UInt64 25) (S : State) (pend bs : Bytes)
    (wc : Nat) (hwc : wc < 17) (hp : pend.length = 8 * wc) (hb : bs.length < 8)
    (h : ofLanes ws = xorState S (h2b pend)) (u0 u1 u2 u3 u4 u5 u6 u7 : UInt8)
    (hu : ∀ k, k < 8 → [u0, u1, u2, u3, u4, u5, u6, u7].getD k 0 = (bs ++ [1]).getD k 0) :
    ofLanes (KECCAK.xorLane
        (KECCAK.xorLane ws wc (by omega) (UInt64.ofBytes u7 u6 u5 u4 u3 u2 u1 u0))
        16 (by omega) ((8 : UInt64) <<< 60)) =
      xorState S (h2b (pend ++ bs) ++ pad101 1088 (8 * (pend ++ bs).length)) := by
  have hL : (pend ++ bs).length = 8 * wc + bs.length := by simp [hp]
  have hu' : ∀ k, k < 64 → bbit [u0, u1, u2, u3, u4, u5, u6, u7] k = bbit (bs ++ [1]) k := by
    intro k hk; simp only [bbit]; rw [hu _ (by omega)]
  apply Vector.ext
  intro n hn
  have hn' := congrArg (·[n]'hn) h
  simp only [ofLanes_getElem, xorState_getElem, h2b_getD] at hn' ⊢
  rw [getElem_xorLane, getElem_xorLane, getElem_xorLane, hL, pad101_eq _ (by omega),
    getD_append', length_h2b, hL, h2b_getD, pad_getD, bbit_append, hp]
  have hz := Nat.mod_lt n (by decide : 64 > 0)
  by_cases h16 : 16 = n / 64 <;> by_cases hw : wc = n / 64 <;>
    simp only [h16, hw, ↓reduceIte, UInt64.toBitVec_xor, BitVec.getLsbD_xor, hn',
      ofBytes_getLsbD _ _ _ _ _ _ _ _ _ hz, hu' _ hz, bbit_one, shift_getLsbD _ hz]
  all_goals
    split_ifs <;>
    simp (disch := omega) [bbit_of_le, decide_eq_true, decide_eq_false]
  all_goals first
    | omega
    | (congr 1; omega)
    | (rw [Bool.eq_iff_iff]; simp; omega)

/-! ### The kernel's absorb loop, one step at a time -/

theorem run_cons8 (wc : Fin 17) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) (bs : Bytes)
    (ws : Vector UInt64 25) :
    KECCAK.Bytes.run wc (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs) ws =
      KECCAK.Bytes.run (wc + 1) bs
        (if wc = 16 then
          KECCAK.f1600 (KECCAK.xorLane ws wc.val (by omega)
            (UInt64.ofBytes b7 b6 b5 b4 b3 b2 b1 b0))
        else KECCAK.xorLane ws wc.val (by omega) (UInt64.ofBytes b7 b6 b5 b4 b3 b2 b1 b0)) :=
  rfl

/-- The body of `KECCAK.Bytes.run`'s final case, restated so that it can be
named: fewer than eight bytes remain. -/
def runTail (wc : Fin 17) (bs : Bytes) (ws : Vector UInt64 25) : B256 :=
  let us : Vector UInt8 8 :=
    ⟨((bs ++ [(1 : UInt8)]).takeD 8 (0 : UInt8)).toArray, by simp⟩
  let t : UInt64 :=
    UInt64.ofBytes (us[7]) (us[6]) (us[5]) (us[4]) (us[3]) (us[2]) (us[1]) (us[0])
  let s : UInt64 := (8 : UInt64) <<< 60
  let temp0 := KECCAK.xorLane ws wc.val (by omega) t
  let temp1 := KECCAK.xorLane temp0 16 (by omega) s
  let ws' := KECCAK.f1600 temp1
  ⟨ ⟨UInt64.byteswap (ws'[0]), UInt64.byteswap (ws'[1])⟩,
    ⟨UInt64.byteswap (ws'[2]), UInt64.byteswap (ws'[3])⟩ ⟩

theorem run_short (wc : Fin 17) (bs : Bytes) (ws : Vector UInt64 25) (h : bs.length < 8) :
    KECCAK.Bytes.run wc bs ws = runTail wc bs ws := by
  rcases bs with _ | ⟨a0, _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, _ | ⟨a5, _ | ⟨a6, _ | ⟨a7, bs⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals first | rfl | (simp at h; omega)

/-! ### Squeezing: the digest bytes are the byte-swapped first four lanes -/

theorem byte_testBit (f : Nat → Bool) (j : Nat) (hj : j < 8) :
    (UInt8.ofNat ((List.range 8).map fun j => if f j then 2 ^ j else 0).sum).toNat.testBit j =
      f j := by
  have key : ∀ b0 b1 b2 b3 b4 b5 b6 b7 : Bool, ∀ j, j < 8 →
      (UInt8.ofNat ((if b0 then 1 else 0) + ((if b1 then 2 else 0) + ((if b2 then 4 else 0) +
        ((if b3 then 8 else 0) + ((if b4 then 16 else 0) + ((if b5 then 32 else 0) +
        ((if b6 then 64 else 0) + ((if b7 then 128 else 0) + 0))))))))).toNat.testBit j =
      [b0, b1, b2, b3, b4, b5, b6, b7].getD j false := by decide
  have h8 : List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] := rfl
  rw [h8]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  refine (key (f 0) (f 1) (f 2) (f 3) (f 4) (f 5) (f 6) (f 7) j hj).trans ?_
  rcases j with _ | _ | _ | _ | _ | _ | _ | _ | j <;> first | rfl | omega

theorem byteswap_getLsbD (w : UInt64) (z : Nat) (hz : z < 64) :
    (UInt64.byteswap w).toBitVec.getLsbD z = w.toBitVec.getLsbD (8 * (7 - z / 8) + z % 8) := by
  have m0 : ∀ z, z < 64 → (0xFF00000000000000 : UInt64).toBitVec.getLsbD z = decide (z / 8 = 7) := by
    decide
  have m1 : ∀ z, z < 64 → (0x00FF000000000000 : UInt64).toBitVec.getLsbD z = decide (z / 8 = 6) := by
    decide
  have m2 : ∀ z, z < 64 → (0x0000FF0000000000 : UInt64).toBitVec.getLsbD z = decide (z / 8 = 5) := by
    decide
  have m3 : ∀ z, z < 64 → (0x000000FF00000000 : UInt64).toBitVec.getLsbD z = decide (z / 8 = 4) := by
    decide
  have m4 : ∀ z, z < 64 → (0x00000000FF000000 : UInt64).toBitVec.getLsbD z = decide (z / 8 = 3) := by
    decide
  have m5 : ∀ z, z < 64 → (0x0000000000FF0000 : UInt64).toBitVec.getLsbD z = decide (z / 8 = 2) := by
    decide
  have m6 : ∀ z, z < 64 → (0x000000000000FF00 : UInt64).toBitVec.getLsbD z = decide (z / 8 = 1) := by
    decide
  have m7 : ∀ z, z < 64 → (0x00000000000000FF : UInt64).toBitVec.getLsbD z = decide (z / 8 = 0) := by
    decide
  simp only [UInt64.byteswap, UInt64.toBitVec_or, UInt64.toBitVec_and, BitVec.getLsbD_or,
    BitVec.getLsbD_and, m0 z hz, m1 z hz, m2 z hz, m3 z hz, m4 z hz, m5 z hz, m6 z hz, m7 z hz]
  have hc : z / 8 = 0 ∨ z / 8 = 1 ∨ z / 8 = 2 ∨ z / 8 = 3 ∨ z / 8 = 4 ∨ z / 8 = 5 ∨
      z / 8 = 6 ∨ z / 8 = 7 := by omega
  rcases hc with h | h | h | h | h | h | h | h <;>
    simp (disch := omega) [h, decide_eq_true, decide_eq_false] <;> congr 1 <;> omega

theorem b2h_getD (L : List Bool) (i : Nat) (hi : i < (L.length + 7) / 8) :
    (b2h L).getD i 0 =
      UInt8.ofNat ((List.range 8).map fun j => if L.getD (8 * i + j) false then 2 ^ j else 0).sum := by
  simp [b2h, List.getD_eq_getElem?_getD, hi]

theorem digest_bit (u : Vector UInt64 25) (i j : Nat) (hi : i < 32) (hj : j < 8) :
    ((b2h ((ofLanes u).toList.take 256)).getD i 0).toNat.testBit j =
      (u[i / 8]'(by omega)).toBitVec.getLsbD (8 * (i % 8) + j) := by
  rw [b2h_getD _ _ (by simp; omega), byte_testBit _ _ hj]
  have hk : 8 * i + j < 256 := by omega
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hk, Vector.getElem?_toList]
  rw [Vector.getElem?_eq_getElem (by omega), Option.getD_some, ofLanes_getElem]
  have h1 : (8 * i + j) / 64 = i / 8 := by omega
  have h2 : (8 * i + j) % 64 = 8 * (i % 8) + j := by omega
  simp only [h1, h2]

theorem word_digest (u : Vector UInt64 25) (l : Nat) (hl : l < 4) :
    word (b2h ((ofLanes u).toList.take 256)) l = UInt64.byteswap (u[l]'(by omega)) := by
  apply UInt64.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro z hz
  rw [word, ofBytes_getLsbD _ _ _ _ _ _ _ _ _ hz, byteswap_getLsbD _ _ hz]
  simp only [bbit]
  have hc : z / 8 = 0 ∨ z / 8 = 1 ∨ z / 8 = 2 ∨ z / 8 = 3 ∨ z / 8 = 4 ∨ z / 8 = 5 ∨
      z / 8 = 6 ∨ z / 8 = 7 := by omega
  have e : ∀ k, k < 8 → ∀ j, j < 8 →
      ((b2h ((ofLanes u).toList.take 256)).getD (8 * l + k) 0).toNat.testBit j =
        (u[l]'(by omega)).toBitVec.getLsbD (8 * k + j) := by
    intro k hk j hj
    rw [digest_bit _ _ _ (by omega) hj]
    simp only [show (8 * l + k) / 8 = l by omega, show (8 * l + k) % 8 = k by omega]
  have e0 := e 0 (by decide)
  simp only [Nat.add_zero, Nat.mul_zero, Nat.zero_add] at e0
  have hz8 := Nat.mod_lt z (by decide : 8 > 0)
  rcases hc with h | h | h | h | h | h | h | h <;>
    simp only [h, List.getD_cons_zero, List.getD_cons_succ, e0 _ hz8]
  all_goals try rw [e _ (by decide) _ hz8]
  all_goals simp

/-! ### The sponge, block by block -/

/-- Steps 4–6 of Algorithm 8 at rate 1088 (`c = 512`): absorb every
1088-bit block of `P` into `S`. -/
def absorb (S : State) (P : List Bool) : State :=
  ((List.range (P.length / 1088)).map fun i => (P.drop (i * 1088)).take 1088).foldl
    (fun S Pi => keccakP 24 (xorState S (Pi ++ List.replicate 512 false))) S

/-- The 256-bit word squeezed from a state: the first 256 bits, as bytes
(Appendix B.1), read big-endian. -/
def out (T : State) : B256 :=
  let d := b2h (T.toList.take 256)
  ⟨⟨word d 0, word d 1⟩, ⟨word d 2, word d 3⟩⟩

theorem out_ofLanes (u : Vector UInt64 25) :
    out (ofLanes u) = ⟨⟨UInt64.byteswap u[0], UInt64.byteswap u[1]⟩,
      ⟨UInt64.byteswap u[2], UInt64.byteswap u[3]⟩⟩ := by
  simp only [out, word_digest u 0 (by decide), word_digest u 1 (by decide),
    word_digest u 2 (by decide), word_digest u 3 (by decide)]
  rfl

theorem xorState_append_replicate (S : State) (T : List Bool) (k : Nat) :
    xorState S (T ++ List.replicate k false) = xorState S T := by
  apply Vector.ext
  intro n hn
  simp only [xorState_getElem, getD_append']
  split
  · rfl
  · rw [List.getD_eq_getElem?_getD (l := T), List.getElem?_eq_none (by omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> simp

theorem xorState_nil (S : State) : xorState S [] = S :=
  Vector.ext fun n hn => by simp [xorState_getElem]

theorem absorb_nil (S : State) : absorb S [] = S := rfl

theorem absorb_block (S : State) (Q R : List Bool) (hQ : Q.length = 1088) :
    absorb S (Q ++ R) = absorb (keccakP 24 (xorState S Q)) R := by
  unfold absorb
  have hl : (Q ++ R).length / 1088 = R.length / 1088 + 1 := by simp [hQ]
  have h0 : ((Q ++ R).drop (0 * 1088)).take 1088 = Q := by
    rw [Nat.zero_mul, List.drop_zero, List.take_left' hQ]
  have h1 : (List.range (R.length / 1088)).map
        ((fun i => ((Q ++ R).drop (i * 1088)).take 1088) ∘ Nat.succ) =
      (List.range (R.length / 1088)).map fun i => (R.drop (i * 1088)).take 1088 := by
    apply List.map_congr_left
    intro i _
    simp only [Function.comp, Nat.succ_mul]
    rw [Nat.add_comm, ← List.drop_drop, List.drop_left' hQ]
  rw [hl, List.range_succ_eq_map, List.map_cons, List.foldl_cons, List.map_map, h0, h1,
    xorState_append_replicate]

theorem absorb_last (S : State) (P : List Bool) (hP : P.length = 1088) :
    absorb S P = keccakP 24 (xorState S P) := by
  have := absorb_block S P [] hP
  rw [List.append_nil] at this
  rw [this, absorb_nil]

theorem pad101_shift (m : Nat) : pad101 1088 (m + 1088) = pad101 1088 m := by
  unfold pad101
  rw [show (-((m + 1088 : Nat) : Int) - 2) % ((1088 : Nat) : Int) =
    (-(m : Int) - 2) % ((1088 : Nat) : Int) by omega]

theorem h2b_append (A B : List UInt8) : h2b (A ++ B) = h2b A ++ h2b B := by
  simp [h2b]

theorem takeD_getElem' {α : Type} (d : α) : ∀ (n : Nat) (l : List α) (i : Nat) (h),
    ((l.takeD n d)[i]'h) = l.getD i d := by
  intro n
  induction n with
  | zero => intro l i h; simp at h
  | succ n ih =>
    intro l i h
    simp only [List.takeD_succ] at h ⊢
    rcases i with _ | i
    · cases l <;> simp
    · rw [List.getElem_cons_succ, ih]
      cases l <;> simp

theorem takeD_getElem (l : List UInt8) (i : Nat) (h) :
    ((l.takeD 8 0)[i]'h) = l.getD i 0 := takeD_getElem' 0 8 l i h

theorem run_short_eq (bs : Bytes) (hb : bs.length < 8) (wc : Fin 17)
    (ws : Vector UInt64 25) (S : State) (pend : Bytes) (hp : pend.length = 8 * wc.val)
    (h : ofLanes ws = xorState S (h2b pend)) :
    KECCAK.Bytes.run wc bs ws =
      out (absorb S (h2b (pend ++ bs) ++ pad101 1088 (8 * (pend ++ bs).length))) := by
  have hL : (pend ++ bs).length = 8 * wc.val + bs.length := by simp [hp]
  have hP : (h2b (pend ++ bs) ++ pad101 1088 (8 * (pend ++ bs).length)).length = 1088 := by
    rw [List.length_append, length_h2b, hL, pad101_eq _ (by omega)]
    simp; omega
  rw [run_short _ _ _ hb, runTail, absorb_last _ _ hP]
  let us : Vector UInt8 8 := ⟨((bs ++ [(1 : UInt8)]).takeD 8 (0 : UInt8)).toArray, by simp⟩
  have hu : ∀ k, k < 8 → [us[0], us[1], us[2], us[3], us[4], us[5], us[6], us[7]].getD k 0 =
      (bs ++ [1]).getD k 0 := by
    intro k hk
    rcases k with _ | _ | _ | _ | _ | _ | _ | _ | k <;>
      first | omega | (simp only [List.getD_cons_succ, List.getD_cons_zero, us,
        Vector.getElem_mk, List.getElem_toArray]; rw [takeD_getElem])
  rw [← ofLanes_final ws S pend bs wc.val wc.isLt hp hb h _ _ _ _ _ _ _ _ hu,
    ← f1600_eq_keccakP, out_ofLanes]

/-- The kernel's absorb loop computes the sponge: from any lane counter `wc`
whose `8·wc` already-absorbed bytes `pend` sit XORed into the state over a
sponge state `S`, the rest of the run is the squeezed word of `S` absorbing
`pend ++ bs` followed by pad10*1. -/
theorem run_eq (n : Nat) : ∀ (bs : Bytes), bs.length ≤ n → ∀ (wc : Fin 17)
    (ws : Vector UInt64 25) (S : State) (pend : Bytes), pend.length = 8 * wc.val →
    ofLanes ws = xorState S (h2b pend) →
    KECCAK.Bytes.run wc bs ws =
      out (absorb S (h2b (pend ++ bs) ++ pad101 1088 (8 * (pend ++ bs).length))) := by
  induction n with
  | zero =>
    intro bs hbs wc ws S pend hp h
    exact run_short_eq bs (by omega) wc ws S pend hp h
  | succ n ih =>
    intro bs hbs wc ws S pend hp h
    by_cases hb : bs.length < 8
    · exact run_short_eq bs hb wc ws S pend hp h
    rcases bs with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, rest⟩⟩⟩⟩⟩⟩⟩⟩
    all_goals try (simp at hb)
    have hrest : rest.length ≤ n := by simp at hbs; omega
    have hstep := ofLanes_xorLane_bytes ws S pend wc.val wc.isLt hp h b0 b1 b2 b3 b4 b5 b6 b7
    have hsplit : pend ++ b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =
        (pend ++ [b0, b1, b2, b3, b4, b5, b6, b7]) ++ rest := by simp
    rw [run_cons8, hsplit]
    by_cases hw : wc = 16
    · subst hw
      simp only [↓reduceIte]
      have hS : ofLanes (KECCAK.f1600 (KECCAK.xorLane ws (16 : Fin 17).val (by omega)
          (UInt64.ofBytes b7 b6 b5 b4 b3 b2 b1 b0))) =
          xorState (keccakP 24 (xorState S (h2b (pend ++ [b0, b1, b2, b3, b4, b5, b6, b7]))))
            (h2b []) := by
        rw [f1600_eq_keccakP, hstep]
        exact (xorState_nil _).symm
      rw [ih rest hrest _ _ _ [] rfl hS]
      have hQ : (h2b (pend ++ [b0, b1, b2, b3, b4, b5, b6, b7])).length = 1088 := by
        rw [length_h2b]; simp [hp]
      have hlen : 8 * ((pend ++ [b0, b1, b2, b3, b4, b5, b6, b7]) ++ rest).length =
          8 * ([] ++ rest).length + 1088 := by simp [hp]; omega
      rw [hlen, pad101_shift, h2b_append (pend ++ _), List.append_assoc, absorb_block _ _ _ hQ,
        List.nil_append]
    · simp only [hw, ↓reduceIte]
      have hwc : (wc + 1).val = wc.val + 1 := by
        have : wc.val ≠ 16 := fun h' => hw (Fin.ext h')
        rw [Fin.val_add]; simp; omega
      rw [ih rest hrest (wc + 1) _ S (pend ++ [b0, b1, b2, b3, b4, b5, b6, b7])
        (by simp [hp, hwc]; omega) hstep]

/-- At rate 1088 and `d = 256`, KECCAK[512] is one absorb pass over the padded
message followed by the first 256 bits of the state (one squeeze). -/
theorem KECCAK_512_256 (N : List Bool) :
    KECCAK 512 N 256 =
      (absorb (Vector.replicate 1600 false) (N ++ pad101 1088 N.length)).toList.take 256 := by
  show squeeze (keccakP 24) 1088 256 (256 + 1)
    (absorb (Vector.replicate 1600 false) (N ++ pad101 1088 N.length)) [] = _
  generalize absorb (Vector.replicate 1600 false) (N ++ pad101 1088 N.length) = T
  have hl : (256 ≤ (T.toList.take 1088).length) = True := by simp
  rw [squeeze]
  simp only [List.nil_append, List.take_take]
  simp only [hl, ↓reduceIte]
  rfl

theorem ofLanes_zero :
    ofLanes (Vector.replicate 25 0) = xorState (Vector.replicate 1600 false) (h2b []) := by
  apply Vector.ext
  intro n hn
  simp [ofLanes_getElem, xorState_getElem, h2b]

end Proof

end Keccak.FIPS

/-- **Jaune's Keccak-256 is Keccak-256 as published.**

`Bytes.keccak` — the optimized kernel in `Jaune/Hash.lean`, its unrolled
permutation and its fused byte-level padding included — computes exactly
`b2h(KECCAK[512](h2b(M), 256))` as FIPS 202 defines it, read as a big-endian
word, on every input.

Read the right-hand side against the standard rather than against the kernel:
that is what it is for, and checking it is the one thing this theorem cannot do
for a reader. `TRUSTED.md` states what the theorem does and does not claim. -/
theorem Bytes.keccak_eq_fips (m : Bytes) : Bytes.keccak m = Keccak.FIPS.keccak256 m := by
  show KECCAK.Bytes.run 0 m (Vector.replicate 25 0) = _
  rw [Keccak.FIPS.run_eq m.length m le_rfl 0 _ _ [] rfl Keccak.FIPS.ofLanes_zero]
  simp only [List.nil_append, Keccak.FIPS.keccak256, Keccak.FIPS.keccak256Digest,
    Keccak.FIPS.KECCAK_512_256, Keccak.FIPS.length_h2b]
  rfl

end Jaune
