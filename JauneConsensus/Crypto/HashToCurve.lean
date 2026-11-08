-- RFC 9380 hash-to-curve for BLS12-381 G2, suite BLS12381G2_XMD:SHA-256_SSWU_RO_
-- (RFC 9380 section 8.8.2), the hash the consensus BLS ciphersuite
-- BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_ uses for messages.
--
-- Transcribed from RFC 9380: section 5.3.1 (expand_message_xmd), section 5.2
-- (hash_to_field), section 3 (hash_to_curve). The field arithmetic, the
-- simplified SWU map onto the 3-isogenous curve, the isogeny map and the
-- effective cofactor are Jaune's (`Jaune/BLS.lean`, `Jaune/BLSConst.lean`),
-- extended here, not duplicated. SHA-256 is `Bytes.sha256` (`Jaune/Hash.lean`).
--
-- Failure model at this layer: `Except String`. The consensus `Reject` type
-- (JauneConsensus/Error.lean, on the SSZ branch) is not imported yet; the master
-- maps these strings to `Reject.crypto` when the branches merge.

import Jaune.BLS
import JauneConsensus.Crypto.G2Subgroup

namespace JauneConsensus

open Jaune

/-- `strxor` (RFC 9380 section 4): bytewise XOR of two equal-length strings. -/
def strxor (a b : Bytes) : Bytes := List.zipWith (· ^^^ ·) a b

/-- `I2OSP(x, n)` (RFC 8017, cited by RFC 9380 section 4): `x` as `n` big-endian
bytes. Callers only pass `x < 256 ^ n`. -/
def i2osp (x n : Nat) : Bytes := (Nat.toBytes x).pack n

/-- `OS2IP` (RFC 9380 section 4): big-endian bytes to an integer. -/
def os2ip (bs : Bytes) : Nat := Bytes.toNat bs

/-- RFC 9380 section 5.3.1, `expand_message_xmd(msg, DST, len_in_bytes)` with
`H` = SHA-256, so `b_in_bytes` = 32 and `s_in_bytes` = 64. -/
def expandMessageXmd (msg dst : Bytes) (lenInBytes : Nat) : Except String Bytes := do
  -- 1. ell = ceil(len_in_bytes / b_in_bytes)
  let ell := (lenInBytes + 31) / 32
  -- 2. ABORT if ell > 255 or len_in_bytes > 65535 or len(DST) > 255
  if ell > 255 ∨ lenInBytes > 65535 ∨ dst.length > 255 then
    throw "expand_message_xmd: length out of range"
  -- 3. DST_prime = DST || I2OSP(len(DST), 1)
  let dstPrime := dst ++ i2osp dst.length 1
  -- 4. Z_pad = I2OSP(0, s_in_bytes)
  let zPad := i2osp 0 64
  -- 5. l_i_b_str = I2OSP(len_in_bytes, 2)
  let libStr := i2osp lenInBytes 2
  -- 6. msg_prime = Z_pad || msg || l_i_b_str || I2OSP(0, 1) || DST_prime
  let msgPrime := zPad ++ msg ++ libStr ++ i2osp 0 1 ++ dstPrime
  -- 7. b_0 = H(msg_prime)
  let b0 := (Bytes.sha256 msgPrime).toBytes
  -- 8. b_1 = H(b_0 || I2OSP(1, 1) || DST_prime)
  let b1 := (Bytes.sha256 (b0 ++ i2osp 1 1 ++ dstPrime)).toBytes
  -- 9.-10. for i in (2, ..., ell): b_i = H(strxor(b_0, b_(i - 1)) || I2OSP(i, 1) || DST_prime)
  -- The fold carries b_(i - 1) and the blocks so far, newest first.
  let (_, blocks) := (List.range (ell - 1)).foldl
    (fun (acc : Bytes × List Bytes) j =>
      let bi := (Bytes.sha256 (strxor b0 acc.1 ++ i2osp (j + 2) 1 ++ dstPrime)).toBytes
      (bi, bi :: acc.2))
    (b1, [b1])
  -- 11. uniform_bytes = b_1 || ... || b_ell
  let uniformBytes := blocks.reverse.flatten
  -- 12. return substr(uniform_bytes, 0, len_in_bytes)
  return uniformBytes.take lenInBytes

/-- `L` for BLS12381G2_XMD:SHA-256_SSWU_RO_ (RFC 9380 section 8.8.2):
`ceil((ceil(log2(p)) + k) / 8)` with `k` = 128, which is 64. -/
def hashToFieldL : Nat := 64

/-- RFC 9380 section 5.2, `hash_to_field(msg, count)` for `F = GF(p^2)`, `m` = 2,
`L` = 64, `expand_message` = `expand_message_xmd` with SHA-256. Each output is
`e_0 + e_1 * I`. -/
def hashToFieldFp2 (msg dst : Bytes) (count : Nat) : Except String (List BLSF2) := do
  let m := 2
  -- 1. len_in_bytes = count * m * L
  let lenInBytes := count * m * hashToFieldL
  -- 2. uniform_bytes = expand_message(msg, DST, len_in_bytes)
  let uniformBytes ← expandMessageXmd msg dst lenInBytes
  -- 3.-8. u_i = (e_0, e_1), e_j = OS2IP(substr(uniform_bytes, L * (j + i * m), L)) mod p
  let e (i j : Nat) : Nat :=
    let elmOffset := hashToFieldL * (j + i * m)
    os2ip ((uniformBytes.drop elmOffset).take hashToFieldL) % blsPrime
  -- 9. return (u_0, ..., u_(count - 1))
  return (List.range count).map fun i => BLSF2.mk (e i 0) (e i 1)

/-- `map_to_curve` for the suite (RFC 9380 section 6.6.3): the simplified SWU map
onto the 3-isogenous curve `E'`, then the isogeny map onto `E` (Appendix E.3),
both Jaune's. No cofactor clearing here; `hashToG2` clears once, after adding
the two mapped points. -/
def mapToCurveG2 (u : BLSF2) : BLSP2 := isoMapG2 (optimizedSwuG2 u)

/-- `clear_cofactor` for the suite as section 8.8.2 defines it: scalar multiplication by
`h_eff`. The reference for `clearCofactorG2`. -/
def clearCofactorG2Ref (q : BLSP2) : BLSP2 := q.mulBy BLSConst.hEffG2

/-- `clear_cofactor_bls12381_g2(P)` (RFC 9380 Appendix G.3, after Budroni and Pintore): the
same point `h_eff * P` from two 64-bit scalar multiplications and the endomorphism `psi`
(`g2Psi`, whose constants are G.3's `c1`, `c2`; `psi2` is `psi` applied twice). Differential
`#guard`s against `clearCofactorG2Ref` in HashToCurveVectors.lean. -/
def clearCofactorG2 (p : BLSP2) : BLSP2 :=
  -- c1 = -0xd201000000010000, so c1 * X = -(|c1| * X)
  let mulC1 (x : BLSP2) : BLSP2 := -(x.mulBy blsAteLoopCount)
  let t1 := mulC1 p                       -- 1. t1 = c1 * P
  let t2 := g2Psi p                       -- 2. t2 = psi(P)
  let t3 := p + p                         -- 3. t3 = 2 * P
  let t3 := g2Psi (g2Psi t3)              -- 4. t3 = psi2(t3)
  let t3 := t3 + -t2                      -- 5. t3 = t3 - t2
  let t2 := t1 + t2                       -- 6. t2 = t1 + t2
  let t2 := mulC1 t2                      -- 7. t2 = c1 * t2
  let t3 := t3 + t2                       -- 8. t3 = t3 + t2
  let t3 := t3 + -t1                      -- 9. t3 = t3 - t1
  t3 + -p                                 -- 10. Q = t3 - P

/-- RFC 9380 section 3, `hash_to_curve(msg)` for BLS12381G2_XMD:SHA-256_SSWU_RO_
with domain separation tag `dst`:
`clear_cofactor(map_to_curve(u_0) + map_to_curve(u_1))`.

Clearing the cofactor of each mapped point and then adding (which
`blsMapFp2ToG2` twice would do) gives the same point, since scalar multiplication
distributes over addition: `h * Q0 + h * Q1 = h * (Q0 + Q1)`. Clearing once after
the addition, as the RFC writes it, is a cost choice: one 636-bit scalar
multiplication instead of two. -/
def hashToG2 (msg dst : Bytes) : Except String BLSP2 := do
  -- 1. u = hash_to_field(msg, 2)
  match ← hashToFieldFp2 msg dst 2 with
  | [u0, u1] =>
    -- 2. Q0 = map_to_curve(u[0]); 3. Q1 = map_to_curve(u[1])
    let q0 := mapToCurveG2 u0
    let q1 := mapToCurveG2 u1
    -- 4. R = Q0 + Q1; 5. P = clear_cofactor(R)
    return clearCofactorG2 (q0 + q1)
  | _ => throw "hash_to_field: wrong output count"

end JauneConsensus
