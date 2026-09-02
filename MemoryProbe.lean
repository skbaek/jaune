import Jaune.Sufficiency

open Jaune

namespace Jaune.MemoryProbe

private def byte3 (n : Nat) : Bytes :=
  [(n / 65536).toUInt8, (n / 256).toUInt8, n.toUInt8]

/-- The Prague `d1g0v0` memory-counter program, parameterized only by the
STATICCALL output-region size. Its counter is frame-local, so recursion ends at
the EVM call-depth boundary rather than at the storage-counter branch used by
the companion `d0g0v0` program. -/
def recursiveStaticCallCode (target : Adr) (outputSize : Nat) : ByteArray :=
  Bytes.toByteArray <|
    [ 0x60, 0x01, 0x60, 0x00, 0x51, 0x01, 0x60, 0x00, 0x52,
      0x61, 0x04, 0x00, 0x60, 0x00, 0x51, 0x10, 0x60, 0x1b,
      0x57, 0x60, 0x01, 0x60, 0x40, 0x52, 0x60, 0x45, 0x56,
      0x5b, 0x60, 0x00, 0x60, 0x00, 0x62 ] ++
    byte3 outputSize ++
    [0x60, 0x00, 0x73] ++ target.toBytes ++
    [0x62, 0x0f, 0x55, 0xc8, 0x5a, 0x03, 0xfa, 0x60, 0x20,
     0x52, 0x5b, 0x00]

def probeMsg (depth outputSize : Nat) : Msg :=
  let target : Adr := 0xcbbf5374fce5edbc8e2a8697c15331677e6ebf0b
  let code := recursiveStaticCallCode target outputSize
  let state := State.setCode .empty target code
  let benv : Benv := {(default : Benv) with state := state}
  {
    (default : Msg) with
    benv := benv
    caller := target
    target := some target
    currentTarget := target
    gas := 1000000000000
    codeAddress := some target
    code := code
    depth := depth
  }

def run (depth outputSize : Nat) : Except String (Nat × Nat × B256) :=
  match processMessage (probeMsg depth outputSize) with
  | .error _ => .error "frame settlement failed"
  | .ok devm =>
    if devm.error.isSome then
      .error "execution ended with a settled halt"
    else
      let success := Bytes.toB256 (devm.memory.data.sliceD 32 32 0)
      .ok (devm.memory.size, devm.memory.data.size, success)

private def parseArgs (args : List String) : IO (Nat × Nat) := do
  match args with
  | [depth, outputSize] =>
    match depth.toNat?, outputSize.toNat? with
    | some depth, some outputSize =>
      if depth = 0 then throw (IO.userError "depth must be positive")
      else if 0xffffff < outputSize then
        throw (IO.userError "output size must fit PUSH3")
      else pure (depth, outputSize)
    | _, _ => throw (IO.userError "depth and output size must be decimal naturals")
  | _ => throw (IO.userError "usage: jaune-memory-probe DEPTH OUTPUT_SIZE")

def main (args : List String) : IO UInt32 := do
  let (depth, outputSize) ← parseArgs args
  match run depth outputSize with
  | .error message =>
    IO.eprintln s!"FAIL depth={depth} output={outputSize}: {message}"
    pure 1
  | .ok (logicalSize, materializedSize, success) =>
    IO.println
      s!"PASS depth={depth} output={outputSize} logical={logicalSize} materialized={materializedSize} success={success.toNat}"
    if success = 1 then pure 0 else pure 1

end Jaune.MemoryProbe

def main (args : List String) : IO UInt32 := Jaune.MemoryProbe.main args
