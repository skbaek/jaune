-- The consensus BLS signature scheme: draft-irtf-cfrg-bls-signature-04 (the version
-- specs/phase0/beacon-chain.md cites) with ciphersuite
-- BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_ (section 4.2.3: proof of possession,
-- minimal-pubkey-size, hash_to_point = BLS12381G2_XMD:SHA-256_SSWU_RO_), plus the
-- Ethereum extensions of specs/altair/bls.md (`eth_aggregate_pubkeys`,
-- `eth_fast_aggregate_verify`).
--
-- Predicates return `Bool`: pyspec's `bls` wrappers (eth2spec/utils/bls.py) turn
-- every decoding exception inside Verify, AggregateVerify and FastAggregateVerify
-- into `False`. Producers (Sign, Aggregate, eth_aggregate_pubkeys) return
-- `Except String`, since pyspec raises there.
--
-- One deviation from the draft text, by the version rule (the vectors' tag wins):
-- `fastAggregateVerify` runs KeyValidate on every input key. Draft-04 section
-- 3.3.4 validates only the aggregate (inside CoreVerify), but the v1.6.1 vector
-- `general/altair/bls/eth_fast_aggregate_verify/bls/eth_fast_aggregate_verify_infinity_pubkey`
-- appends the identity key to valid keys with their valid aggregate signature and
-- expects `false`, which only per-key validation yields.
--
-- The bls switch (`bls_setting`) is not modelled here: it belongs to the state
-- transition's verify predicate, not to the scheme.

import JauneConsensus.Crypto.Codec

namespace JauneConsensus

open Jaune

/-- The ciphersuite's domain separation tag for `hash_to_point` (section 4.2.3). -/
def blsSigDst : Bytes :=
  "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_".toUTF8.toList

/-- `hash_to_point` of the ciphersuite. -/
def hashToPoint (message : Bytes) : Except String BLSP2 := hashToG2 message blsSigDst

/-- `G2_POINT_AT_INFINITY` (specs/altair/bls.md). -/
def g2PointAtInfinity : Bytes := (0xc0 : UInt8) :: List.replicate 95 0

/-- Section 2.5, `KeyValidate(PK)`. -/
def keyValidate (pk : Bytes) : Bool :=
  match pubkeyToPoint pk with
  | .error _ => false                         -- 2. xP INVALID
  | .ok xP => xP ≠ g1Identity                 -- 3. identity
              && g1SubgroupCheck xP           -- 4. pubkey_subgroup_check

/-- Section 2.4, `SkToPk(SK)`: `SK` is an integer in `[1, r-1]`, so `0` and `r` and
above are rejected (`blsCurveOrder` is `r`; `skToPk r` would otherwise wrap to infinity). -/
def skToPk (sk : Nat) : Except String Bytes := do
  if sk = 0 ∨ blsCurveOrder ≤ sk then throw "SkToPk: secret key not in [1, r-1]"
  return g1Compress (blsG1Generator.mulBy sk)

/-- Section 2.6, `CoreSign(SK, message)`; `Sign` of the proof-of-possession scheme
(section 3.3), with the same `[1, r-1]` secret-key precondition as `SkToPk`. -/
def sign (sk : Nat) (message : Bytes) : Except String Bytes := do
  if sk = 0 ∨ blsCurveOrder ≤ sk then throw "Sign: secret key not in [1, r-1]"
  let q ← hashToPoint message                  -- 1. Q = hash_to_point(message)
  return g2Compress (q.mulBy sk)               -- 2.-3. R = SK * Q; point_to_signature(R)

/-- Section 2.7, `CoreVerify(PK, message, signature)`; `Verify` of the scheme.
Step 9 (`pairing(Q, xP) == pairing(R, P)`) is evaluated as the pairing-product
check `e(xP, Q) * e(-P, R) = 1`, which is equivalent by bilinearity. -/
def coreVerify (pk message signature : Bytes) : Bool :=
  match signatureToPoint signature with
  | .error _ => false                          -- 1.-2. R INVALID
  | .ok r =>
    if !g2SubgroupCheck r then false           -- 3. signature_subgroup_check
    else if !keyValidate pk then false         -- 4. KeyValidate(PK)
    else
      match pubkeyToPoint pk, hashToPoint message with   -- 5. xP; 6. Q
      | .ok xP, .ok q => pairingCheck [(xP, q), (-blsG1Generator, r)]   -- 7.-9.
      | _, _ => false

/-- `Verify` (section 3.3: identical to CoreVerify). -/
def verify (pk message signature : Bytes) : Bool := coreVerify pk message signature

/-- Section 2.8, `Aggregate((signature_1, ..., signature_n))`. -/
def aggregate (signatures : List Bytes) : Except String Bytes := do
  match signatures with
  | [] => throw "Aggregate: no signatures"     -- precondition n >= 1
  | s :: ss =>
    let first ← signatureToPoint s              -- 1.-2.
    let agg ← ss.foldlM (fun acc si => do       -- 3.-6.
      let next ← signatureToPoint si
      return acc + next) first
    return g2Compress agg                       -- 7.-8.

/-- Section 2.9, `CoreAggregateVerify`; `AggregateVerify` of the scheme (section
3.3). Steps 9-11 are one pairing-product check, as in `coreVerify`. Lists of
different lengths are INVALID. -/
def aggregateVerify (pks messages : List Bytes) (signature : Bytes) : Bool :=
  if pks.isEmpty ∨ pks.length ≠ messages.length then false   -- precondition n >= 1
  else
    match signatureToPoint signature with
    | .error _ => false                                       -- 1.-2.
    | .ok r =>
      if !g2SubgroupCheck r then false                        -- 3.
      else
        let pairs : Option (List (BLSP × BLSP2)) :=           -- 5.-9.
          (pks.zip messages).mapM fun (pk, m) =>
            if !keyValidate pk then none                      -- 6.
            else match pubkeyToPoint pk, hashToPoint m with   -- 7.-8.
              | .ok xP, .ok q => some (xP, q)
              | _, _ => none
        match pairs with
        | some ps => pairingCheck ((-blsG1Generator, r) :: ps)   -- 10.-11.
        | none => false

/-- Section 3.3.4, `FastAggregateVerify((PK_1, ..., PK_n), message, signature)`,
with KeyValidate on each input key (see the module header). -/
def fastAggregateVerify (pks : List Bytes) (message signature : Bytes) : Bool :=
  match pks with
  | [] => false                                               -- precondition n >= 1
  | _ =>
    if !pks.all keyValidate then false                        -- vector-driven, see header
    else
      match pks.mapM pubkeyToPoint with
      | .error _ => false
      | .ok points =>
        let agg := points.foldl (· + ·) g1Identity            -- 1.-4.
        coreVerify (g1Compress agg) message signature         -- 5.-6.

/-- specs/altair/bls.md, `eth_aggregate_pubkeys(pubkeys)`. -/
def ethAggregatePubkeys (pubkeys : List Bytes) : Except String Bytes := do
  if pubkeys.isEmpty then throw "eth_aggregate_pubkeys: empty"          -- assert len > 0
  if !pubkeys.all keyValidate then throw "eth_aggregate_pubkeys: invalid pubkey"
  let points ← pubkeys.mapM pubkeyToPoint
  return g1Compress (points.foldl (· + ·) g1Identity)

/-- specs/altair/bls.md, `eth_fast_aggregate_verify(pubkeys, message, signature)`. -/
def ethFastAggregateVerify (pubkeys : List Bytes) (message signature : Bytes) : Bool :=
  if pubkeys.isEmpty ∧ signature = g2PointAtInfinity then true
  else fastAggregateVerify pubkeys message signature

-- Secret keys outside `[1, r-1]` are rejected; `1` is accepted.
#guard (skToPk 0).toOption.isNone
#guard (skToPk blsCurveOrder).toOption.isNone
#guard (skToPk 1).isOk
#guard (sign 0 []).toOption.isNone
#guard (sign blsCurveOrder []).toOption.isNone

end JauneConsensus
