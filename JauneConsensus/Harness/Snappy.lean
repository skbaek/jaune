/-!
# Snappy raw-block decoder (conformance harness)

The consensus test vectors store every SSZ value as `<name>.ssz_snappy`: the SSZ bytes
compressed in Snappy's *raw block* format (Google Snappy, `format_description.txt`). No file in
the pinned `v1.6.1` tarballs uses the framing format (`framing_format.txt`, stream identifier
`ff 06 00 00 73 4e 61 50 70 59`): all 128,364 `.ssz_snappy` files were checked, so this module
decodes raw blocks only and rejects a framed stream as a raw block would (its first byte is not a
valid length preamble for the data that follows).

Format (`format_description.txt`):

* a preamble: the uncompressed length as a little-endian base-128 varint (at most 32 bits, so at
  most five bytes);
* then a sequence of elements, each starting with a tag byte whose low two bits select the kind:
  * `00` literal: the upper six bits `m` give `len - 1` when `m < 60`; otherwise `m - 59`
    (one to four) little-endian bytes follow holding `len - 1`; then `len` literal bytes;
  * `01` copy with a one-byte offset: `len = 4 + ((tag >> 2) & 7)`, `offset = ((tag >> 5) << 8) |
    next byte`;
  * `10` copy with a two-byte offset: `len = (tag >> 2) + 1`, offset little-endian 16 bits;
  * `11` copy with a four-byte offset: `len = (tag >> 2) + 1`, offset little-endian 32 bits.

  A copy repeats `len` bytes starting `offset` bytes back from the end of the output; the source
  may overlap the bytes being written (a run). An offset of zero, or one reaching before the start
  of the output, is an error.

The decoder is fail-closed: a truncated element, a bad offset, output beyond the declared length,
or a final length different from the preamble is an error, never a partial result. It is total by
fuel: every element consumes at least one input byte, so the input length bounds the iterations.

This is harness code, outside the semantics: it reads vector files, it does not define consensus
behaviour.
-/

namespace JauneConsensus.Harness.Snappy

/-- Why a raw Snappy block failed to decode. -/
inductive Error where
  /-- The length preamble is truncated or longer than five bytes, or exceeds 32 bits. -/
  | preamble
  /-- An element runs past the end of the input. -/
  | truncated (pos : Nat)
  /-- A copy offset is zero or reaches before the start of the output. -/
  | offset (pos offset outLen : Nat)
  /-- An element would write past the declared uncompressed length. -/
  | overrun (pos declared : Nat)
  /-- The input ended with fewer bytes produced than declared. -/
  | short (declared produced : Nat)
  /-- Internal: the iteration bound was exhausted (unreachable for well-formed fuel). -/
  | fuel
  deriving Repr, BEq, DecidableEq

instance : ToString Error where
  toString
    | .preamble => "snappy: bad length preamble"
    | .truncated p => s!"snappy: element truncated at input byte {p}"
    | .offset p o n => s!"snappy: bad copy offset {o} at input byte {p} (output length {n})"
    | .overrun p d => s!"snappy: output past declared length {d} at input byte {p}"
    | .short d n => s!"snappy: declared length {d}, produced {n}"
    | .fuel => "snappy: iteration bound exhausted"

/-- Read the byte at `i`, or report truncation at `i`. -/
@[inline] def byteAt (src : ByteArray) (i : Nat) : Except Error UInt8 :=
  match src[i]? with
  | some b => .ok b
  | none => .error (.truncated i)

/-- Little-endian unsigned integer of `n` bytes at `pos` (`n ≤ 4` at every call site). -/
def readLE (src : ByteArray) (pos : Nat) : Nat → Except Error Nat
  | 0 => .ok 0
  | n + 1 => do
    let lo ← byteAt src pos
    let hi ← readLE src (pos + 1) n
    return lo.toNat + 256 * hi

/-- The varint preamble: `(value, bytes consumed)`. At most five bytes, value below `2^32`. -/
def readVarint (src : ByteArray) : Except Error (Nat × Nat) :=
  go 0 0 0 5
where
  go (pos acc shift : Nat) : Nat → Except Error (Nat × Nat)
    | 0 => .error .preamble
    | fuel + 1 =>
      match src[pos]? with
      | none => .error .preamble
      | some b =>
        let acc := acc + (b &&& 0x7f).toNat <<< shift
        if b &&& 0x80 == 0 then
          if acc < 2 ^ 32 then .ok (acc, pos + 1) else .error .preamble
        else go (pos + 1) acc (shift + 7) fuel

/-- Append `n` bytes copied from `out[start ...]`, one at a time, so that an overlapping source
(a run) sees the bytes this copy has already written. -/
def copyBytes (out : ByteArray) (start : Nat) : Nat → Except Error ByteArray
  | 0 => .ok out
  | n + 1 =>
    match out[start]? with
    | some b => copyBytes (out.push b) (start + 1) n
    | none => .error .fuel

/-- The element loop. `fuel` bounds the iterations; each element consumes at least one input
byte, so `src.size` suffices. -/
def loop (src : ByteArray) (declared : Nat) : Nat → Nat → ByteArray → Except Error ByteArray
  | 0, pos, out => if pos < src.size then .error .fuel else .ok out
  | fuel + 1, pos, out =>
    if pos ≥ src.size then .ok out else do
    let tag ← byteAt src pos
    let kind := tag &&& 3
    if kind == 0 then
      -- literal
      let m := (tag >>> 2).toNat
      let (len, start) ←
        if m < 60 then pure (m + 1, pos + 1)
        else do
          let extra := m - 59
          let v ← readLE src (pos + 1) extra
          pure (v + 1, pos + 1 + extra)
      if start + len > src.size then throw (.truncated pos)
      if out.size + len > declared then throw (.overrun pos declared)
      loop src declared fuel (start + len) (out ++ src.extract start (start + len))
    else
      let (len, offset, next) ←
        if kind == 1 then do
          let b ← byteAt src (pos + 1)
          pure (4 + ((tag >>> 2) &&& 7).toNat, ((tag >>> 5).toNat <<< 8) ||| b.toNat, pos + 2)
        else if kind == 2 then do
          let o ← readLE src (pos + 1) 2
          pure ((tag >>> 2).toNat + 1, o, pos + 3)
        else do
          let o ← readLE src (pos + 1) 4
          pure ((tag >>> 2).toNat + 1, o, pos + 5)
      if offset == 0 || offset > out.size then throw (.offset pos offset out.size)
      if out.size + len > declared then throw (.overrun pos declared)
      let start := out.size - offset
      let out ←
        if offset ≥ len then pure (out ++ out.extract start (start + len))
        else copyBytes out start len
      loop src declared fuel next out

/-- Decode one raw Snappy block. -/
def decompress (src : ByteArray) : Except Error ByteArray := do
  let (declared, pos) ← readVarint src
  let out ← loop src declared src.size pos (ByteArray.emptyWithCapacity declared)
  if out.size == declared then pure out else throw (.short declared out.size)

/-! ## Tests

Hand-assembled blocks following `format_description.txt`, one per element kind, plus the
rejections. -/

private def bytes (xs : List UInt8) : ByteArray := ⟨xs.toArray⟩
private def ok? (src : List UInt8) (want : List UInt8) : Bool :=
  match decompress (bytes src) with
  | .ok out => out.toList == want
  | .error _ => false
private def err? (src : List UInt8) (e : Error) : Bool :=
  match decompress (bytes src) with
  | .ok _ => false
  | .error e' => e' == e

-- empty input: length 0, no elements
#guard ok? [0x00] []
-- literal "abc": length 3, tag (3-1)<<2 = 0x08
#guard ok? [0x03, 0x08, 0x61, 0x62, 0x63] [0x61, 0x62, 0x63]
-- literal with one extra length byte (m = 60): 61 bytes of 0x07
#guard ok? ([61, 0xf0, 60] ++ List.replicate 61 (7 : UInt8)) (List.replicate 61 7)
-- copy-1 run: "a" then copy len 4+3=7 offset 1 -> eight 'a'; tag = 1 | (3<<2) | (0<<5) = 0x0d
#guard ok? [0x08, 0x00, 0x61, 0x0d, 0x01] (List.replicate 8 0x61)
-- copy-2 non-overlapping: "abcd" then copy len 4 offset 4: tag = 2 | (3<<2) = 0x0e
#guard ok? [0x08, 0x0c, 0x61, 0x62, 0x63, 0x64, 0x0e, 0x04, 0x00]
  [0x61, 0x62, 0x63, 0x64, 0x61, 0x62, 0x63, 0x64]
-- copy-4 overlapping: "ab" then copy len 4 offset 2: tag = 3 | (3<<2) = 0x0f
#guard ok? [0x06, 0x04, 0x61, 0x62, 0x0f, 0x02, 0x00, 0x00, 0x00]
  [0x61, 0x62, 0x61, 0x62, 0x61, 0x62]
-- two-byte varint preamble: 200 = 0xc8 0x01, then literal of 200 via m = 60 (one byte, 199)
#guard ok? ([0xc8, 0x01, 0xf0, 199] ++ List.replicate 200 (9 : UInt8)) (List.replicate 200 9)
-- rejections
#guard err? [] .preamble
#guard err? [0x80, 0x80, 0x80, 0x80, 0x80, 0x01] .preamble
#guard err? [0x03, 0x08, 0x61, 0x62] (.truncated 1)
#guard err? [0x04, 0x08, 0x61, 0x62, 0x63] (.short 4 3)
#guard err? [0x02, 0x08, 0x61, 0x62, 0x63] (.overrun 1 2)
#guard err? [0x08, 0x00, 0x61, 0x0d, 0x00] (.offset 3 0 1)
#guard err? [0x08, 0x00, 0x61, 0x0d, 0x02] (.offset 3 2 1)
#guard err? [0x08, 0x00, 0x61, 0x0d] (.truncated 4)
-- a framing-format stream identifier is not a valid raw block
#guard (decompress (bytes [0xff, 0x06, 0x00, 0x00, 0x73, 0x4e, 0x61, 0x50, 0x70, 0x59])).toBool == false

end JauneConsensus.Harness.Snappy
