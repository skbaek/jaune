-- Checks for JauneConsensus/Crypto/Codec.lean and BLSSig.lean. The compressed points
-- are entries of the pinned consensus-specs v1.6.1 KZG setup
-- (presets/mainnet/trusted_setups/trusted_setup_4096.json): g1_monomial[0] and
-- g2_monomial[0] are the generators, and g2_monomial[1] decompresses to Jaune's
-- independently decoded `kzgSetupG2Monomial1P`. Kept out of the codec modules so
-- their importers do not evaluate these.

import JauneConsensus.Crypto.BLSSig

namespace JauneConsensus.CodecVectors

open Jaune JauneConsensus

def hexNat (x n : Nat) : Bytes := i2osp x n

def g1m0 : Bytes := hexNat 0x97f1d3a73197d7942695638c4fa9ac0fc3688c4f9774b905a14e3a3f171bac586c55e83ff97a1aeffb3af00adb22c6bb 48
def g1m1 : Bytes := hexNat 0xad3eb50121139aa34db1d545093ac9374ab7bca2c0f3bf28e27c8dcd8fc7cb42d25926fc0c97b336e9f0fb35e5a04c81 48
def g2m0 : Bytes := hexNat 0x93e02b6052719f607dacd3a088274f65596bd0d09920b61ab5da61bbdc7f5049334cf11213945d57e5ac7d055d042b7e024aa2b2f08f0a91260805272dc51051c6e47ad4fa403b02b4510b647ae3d1770bac0326a805bbefd48056c8c121bdb8 96
def g2m1 : Bytes := hexNat 0xb5bfd7dd8cdeb128843bc287230af38926187075cbfbefa81009a2ce615ac53d2914e5870cb452d2afaaab24f3499f72185cbfee53492714734429b7b38608e23926c911cceceac9a36851477ba4c60b087041de621000edc98edada20c1def2 96

-- Generators and the setup point: decode, encode, and agree with Jaune's constants.
#guard pubkeyToPoint g1m0 = .ok blsG1Generator
#guard g1Compress blsG1Generator = g1m0
#guard (pubkeyToPoint g1m1).map g1Compress = .ok g1m1
#guard signatureToPoint g2m0 = .ok blsG2Generator
#guard g2Compress blsG2Generator = g2m0
#guard signatureToPoint g2m1 = .ok kzgSetupG2Monomial1P
#guard g2Compress kzgSetupG2Monomial1P = g2m1
-- Both signs of y round-trip.
#guard signatureToPoint (g2Compress (-blsG2Generator)) = .ok (-blsG2Generator)
#guard pubkeyToPoint (g1Compress (-blsG1Generator)) = .ok (-blsG1Generator)
#guard g1Compress (-blsG1Generator) ≠ g1m0

-- Infinity and malformed metadata (pairing-friendly-curves draft C.2).
#guard signatureToPoint g2PointAtInfinity = .ok g2Identity
#guard g2Compress g2Identity = g2PointAtInfinity
#guard pubkeyToPoint ((0xc0 : UInt8) :: List.replicate 47 0) = .ok g1Identity
#guard (signatureToPoint ((0xe0 : UInt8) :: List.replicate 95 0)).toOption = none
#guard (signatureToPoint ((0x20 : UInt8) :: g2m0.tail)).toOption = none
#guard (signatureToPoint ((0xc0 : UInt8) :: List.replicate 94 0 ++ [1])).toOption = none
#guard (signatureToPoint (List.replicate 96 0)).toOption = none
#guard (signatureToPoint g2m0.tail).toOption = none
-- x_1 = p is not a field element.
#guard (signatureToPoint (let x := i2osp blsPrime 48 ++ List.replicate 48 0
                          (match x with | b :: rest => (b ||| 0x80) :: rest | [] => []))).toOption = none

-- Subgroup checks.
#guard g1SubgroupCheck blsG1Generator
#guard g2SubgroupCheck blsG2Generator
#guard keyValidate g1m0
#guard !keyValidate ((0xc0 : UInt8) :: List.replicate 47 0)

end JauneConsensus.CodecVectors
