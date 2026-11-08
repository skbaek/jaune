/-!
# Snappy raw-block decoder (harness only)

The consensus vectors store SSZ bytes as `*.ssz_snappy`: one Snappy block in the raw (unframed)
format. This decoder is harness code, outside the semantics. It is pure and total: every step
consumes at least one input byte, so the loop runs on input-length fuel.

Format: a little-endian base-128 varint giving the uncompressed length (at most `2^32 - 1`),
then elements whose tag byte's low two bits select
* `00` literal: length `(tag >> 2) + 1`, or for `tag >> 2 ≥ 60` a length minus one in the next
  `(tag >> 2) - 59` bytes (little-endian);
* `01` copy with a 1-byte offset: length `4 + ((tag >> 2) & 7)`, offset `((tag >> 5) << 8) | b`;
* `10` copy with a 2-byte little-endian offset: length `(tag >> 2) + 1`;
* `11` copy with a 4-byte little-endian offset: length `(tag >> 2) + 1`.
A copy's offset must be in `[1, bytes produced so far]`; copies may overlap their output. The
output must have exactly the declared length.

Written from the format description, not from any implementation's source. Temporary home:
the harness worker's branch (`claude/consensus-harness`) owns the shared decoder; this copy
is to be merged into it.
-/

namespace JauneConsensus.Harness

/-- Why a Snappy block failed to decode. -/
inductive SnappyError where
  | truncated (pos : Nat)
  | badVarint
  | badOffset (pos offset produced : Nat)
  | overrun (declared : Nat)
  | lengthMismatch (declared actual : Nat)
  deriving Repr

/-- Little-endian unsigned integer of `k` bytes at `pos`. -/
def readLE (input : ByteArray) (pos k : Nat) : Except SnappyError Nat :=
  (List.range k).foldlM (fun acc i =>
    match input[pos + i]? with
    | some b => pure (acc + b.toNat * 256 ^ i)
    | none => throw (.truncated (pos + i))) 0

/-- The uncompressed-length varint: returns the value and the position after it. -/
def readVarint (input : ByteArray) : Except SnappyError (Nat × Nat) :=
  let rec go : Nat → Nat → Nat → Except SnappyError (Nat × Nat)
    | 0, _, _ => throw .badVarint
    | fuel + 1, pos, acc =>
      match input[pos]? with
      | none => throw (.truncated pos)
      | some b =>
        let acc := acc + (b.toNat % 128) * 128 ^ pos
        if b.toNat < 128 then pure (acc, pos + 1) else go fuel (pos + 1) acc
  do
    let (v, p) ← go 5 0 0
    if v < 2 ^ 32 then pure (v, p) else throw .badVarint

/-- Append `len` bytes copied from `offset` bytes back (byte by byte, so overlap repeats). -/
def copyBack (out : ByteArray) (offset len : Nat) : ByteArray :=
  (List.range len).foldl (fun o _ =>
    match o[o.size - offset]? with
    | some b => o.push b
    | none => o) out

/-- Decode one raw Snappy block. -/
def decompress (input : ByteArray) : Except SnappyError ByteArray := do
  let (declared, start) ← readVarint input
  let rec go : Nat → Nat → ByteArray → Except SnappyError ByteArray
    | 0, _, out => pure out
    | fuel + 1, pos, out =>
      match input[pos]? with
      | none => pure out
      | some tag =>
        let t := tag.toNat
        let hi := t / 4
        match t % 4 with
        | 0 => do
          let (len, p) ←
            if hi < 60 then pure (hi + 1, pos + 1)
            else do
              let k := hi - 59
              let l ← readLE input (pos + 1) k
              pure (l + 1, pos + 1 + k)
          if p + len > input.size then throw (.truncated input.size)
          if out.size + len > declared then throw (.overrun declared)
          go fuel (p + len) (out ++ input.extract p (p + len))
        | kind => do
          let (len, offset, p) ←
            if kind = 1 then do
              let b ← readLE input (pos + 1) 1
              pure (4 + hi % 8, (hi / 8) * 256 + b, pos + 2)
            else if kind = 2 then do
              let o ← readLE input (pos + 1) 2
              pure (hi + 1, o, pos + 3)
            else do
              let o ← readLE input (pos + 1) 4
              pure (hi + 1, o, pos + 5)
          if offset = 0 ∨ offset > out.size then throw (.badOffset pos offset out.size)
          if out.size + len > declared then throw (.overrun declared)
          go fuel p (copyBack out offset len)
  let out ← go (input.size + 1) start ByteArray.empty
  if out.size = declared then pure out else throw (.lengthMismatch declared out.size)

end JauneConsensus.Harness
