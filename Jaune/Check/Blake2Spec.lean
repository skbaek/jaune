-- Check/Blake2Spec.lean : executable checks of `Jaune/Blake2Spec.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/Blake2Spec.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.Blake2Spec

namespace Jaune.Blake2.Spec

open Jaune

/-- EIP-152, Specification: the precompile input is exactly 213 bytes — rounds
(4 bytes, big-endian) ‖ h (64 bytes, eight little-endian u64) ‖ m (128 bytes,
sixteen little-endian u64) ‖ t (16 bytes, two little-endian u64) ‖ f (1 byte,
must be 0 or 1) — and the output is the 64-byte little-endian `h'`. Returns
`none` on a wrong length or `f ∉ {0, 1}`. -/
def blake2f (data : Bytes) : Option Bytes :=
  if data.length ≠ 213 then none
  else
    let n := Bytes.toNat (data.sliceD 0 4 (0x00 : UInt8))
    let h := readLittleEndianWords data 4 8
    let m := readLittleEndianWords data 68 16
    let t0 := getLittleEndianWord data 196
    let t1 := getLittleEndianWord data 204
    let f := data.getD 212 (0x00 : UInt8)
    if f == 0 then some (outBytes (F h m t0 t1 false n))
    else if f == 1 then some (outBytes (F h m t0 t1 true n))
    else none

/-! ## Agreement with the production precompile -/

/-- The production entry path for one 213-byte EIP-152 input: `executeBlake2F`
(`Jaune/Precompiles.lean`, reached by the EIP-152 dispatch) parses the input
with `getBlake2Parameters` and compresses with `bCompress`, charging gas around
it. This is that path without the gas, so `#guard`s below can compare values:
`executeBlake2F` itself returns a `PrecompResult` (cost plus output or error),
not bare bytes. -/
def productionBlake2f (data : Bytes) : Option Bytes :=
  if data.length ≠ 213 then none
  else
    let ⟨n, h, m, t0, t1, fn⟩ := Jaune.getBlake2Parameters data
    match fn with
    | 0 => Jaune.Blake2.compress n h m t0 t1 false
    | 1 => Jaune.Blake2.compress n h m t0 t1 true
    | _ => none

/-! ## Test vectors -/

/-- Parse hex from the vector corpus. -/
private def hex (s : String) : Bytes := (Hex.toBytes s).getD []

/-- EIP-152 "Test Cases": all five committed vectors share one chaining value.
Bytes are EIP-152's, as committed in `scripts/vectors/blake2F.json`. -/
private def eip152StateVector : Bytes :=
  hex ("48c9bdf267e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
    "d182e6ad7f520e511f6c3e2b8c68059b6bbd41fbabd9831f79217e1319cde05b")

/-- EIP-152 "Test Cases": all five committed vectors share the message `"abc"`
(zero-padded to one block). Bytes are EIP-152's, as committed in
`scripts/vectors/blake2F.json`. -/
private def eip152MessageBlock : Bytes := [0x61, 0x62, 0x63] ++ List.replicate 125 (0x00 : UInt8)

/-- EIP-152 "Test Cases": all five committed vectors share the counter `t = 3`.
Bytes are EIP-152's, as committed in `scripts/vectors/blake2F.json`. -/
private def eip152OffsetCounters : Bytes := [0x03] ++ List.replicate 15 (0x00 : UInt8)

/-- EIP-152, Specification: the 213-byte layout from a rounds header, the shared
corpus parts above, and a final flag byte. -/
private def eip152Input (r0 r1 r2 r3 f : UInt8) : Bytes :=
  [r0, r1, r2, r3] ++ eip152StateVector ++ eip152MessageBlock ++ eip152OffsetCounters ++ [f]

/-- EIP-152 "Test Cases", vector 4: rounds 0, `f = 1`. -/
private def vector4Input : Bytes := eip152Input 0x00 0x00 0x00 0x00 0x01
/-- EIP-152 "Test Cases", vector 5: rounds 12, `f = 1`. -/
private def vector5Input : Bytes := eip152Input 0x00 0x00 0x00 0x0c 0x01
/-- EIP-152 "Test Cases", vector 6: rounds 12, `f = 0`. -/
private def vector6Input : Bytes := eip152Input 0x00 0x00 0x00 0x0c 0x00
/-- EIP-152 "Test Cases", vector 7: rounds 1, `f = 1`. -/
private def vector7Input : Bytes := eip152Input 0x00 0x00 0x00 0x01 0x01

/-- EIP-152 "Test Cases", vector 4 output. Value is EIP-152's, as committed in
`scripts/vectors/blake2F.json`. -/
private def vector4Output : Bytes :=
  hex ("08c9bcf367e6096a3ba7ca8485ae67bb2bf894fe72f36e3cf1361d5f3af54fa5" ++
    "d282e6ad7f520e511f6c3e2b8c68059b9442be0454267ce079217e1319cde05b")

/-- EIP-152 "Test Cases", vector 5 output. Value is EIP-152's, as committed in
`scripts/vectors/blake2F.json`. -/
private def vector5Output : Bytes :=
  hex ("ba80a53f981c4d0d6a2797b69f12f6e94c212f14685ac4b74b12bb6fdbffa2d1" ++
    "7d87c5392aab792dc252d5de4533cc9518d38aa8dbf1925ab92386edd4009923")

/-- EIP-152 "Test Cases", vector 6 output. Value is EIP-152's, as committed in
`scripts/vectors/blake2F.json`. -/
private def vector6Output : Bytes :=
  hex ("75ab69d3190a562c51aef8d88f1c2775876944407270c42c9844252c26d287529" ++
    "8743e7f6d5ea2f2d3e8d226039cd31b4e426ac4f2d3d666a610c2116fde4735")

/-- EIP-152 "Test Cases", vector 7 output. Value is EIP-152's, as committed in
`scripts/vectors/blake2F.json`. -/
private def vector7Output : Bytes :=
  hex ("b63a380cb2897d521994a85234ee2c181b5f844d2c624c002677e9703449d2fb" ++
    "a551b3a8333bcdf5f2f7e08993d53923de3d64fcc68c034e717b9293fed7a421")

-- The constructed inputs really are 213 bytes and the outputs 64.
#guard vector4Input.length == 213
#guard vector5Input.length == 213
#guard vector6Input.length == 213
#guard vector7Input.length == 213
#guard vector4Output.length == 64
#guard vector5Output.length == 64
#guard vector6Output.length == 64
#guard vector7Output.length == 64

-- EIP-152 "Test Cases": vectors 0-3 are framing failures (wrong length or flag).
-- They are not present in `scripts/vectors/blake2F.json`, which starts at
-- vector 4, so the three inputs below are representative malformed inputs of
-- the same classes: empty, short, long, and a valid-length input with `f = 2`.
#guard blake2f [] == none
#guard blake2f (List.replicate 212 (0x00 : UInt8)) == none
#guard blake2f (vector5Input ++ [(0x00 : UInt8)]) == none
#guard blake2f (vector5Input.take 212 ++ [(0x02 : UInt8)]) == none
-- The production path fails them the same way.
#guard productionBlake2f [] == none
#guard productionBlake2f (vector5Input ++ [(0x00 : UInt8)]) == none
#guard productionBlake2f (vector5Input.take 212 ++ [(0x02 : UInt8)]) == none

-- EIP-152 "Test Cases", vectors 4-7: the spec returns the published outputs.
#guard blake2f vector4Input == some vector4Output
#guard blake2f vector5Input == some vector5Output
#guard blake2f vector6Input == some vector6Output
#guard blake2f vector7Input == some vector7Output

-- EIP-152 "Test Cases", vectors 4-7: the production `bCompress` path (via
-- `getBlake2Parameters`, as `executeBlake2F` calls them) returns the same
-- published outputs.
#guard productionBlake2f vector4Input == some vector4Output
#guard productionBlake2f vector5Input == some vector5Output
#guard productionBlake2f vector6Input == some vector6Output
#guard productionBlake2f vector7Input == some vector7Output

-- Vectors 4-7: production and spec agree with each other directly.
#guard productionBlake2f vector4Input == blake2f vector4Input
#guard productionBlake2f vector5Input == blake2f vector5Input
#guard productionBlake2f vector6Input == blake2f vector6Input
#guard productionBlake2f vector7Input == blake2f vector7Input

-- Vector 8 (rounds `0x007A1200` = 8000000) is deliberately not guarded: eight
-- million rounds cannot be kernel-evaluated. Its input and output are EIP-152's,
-- as committed in `scripts/vectors/blake2F.json`, and are not repeated here.
-- No committed vector beyond the EIP's has a round count ≤ 20, so there is no
-- further cheap agreement case to add.

-- RFC 7693 Appendix A: BLAKE2b-512("abc"). The bytes below are EIP-152 vector 5's
-- published output from `scripts/vectors/blake2F.json`, which is the same
-- single-block computation (parameter block for `nn = 64`, message `"abc"`,
-- `t = 3`, `f` set, twelve rounds) the appendix publishes for `"abc"`.
#guard blake2b512SingleBlock [0x61, 0x62, 0x63] == some vector5Output

end Jaune.Blake2.Spec

