import Jaune.Sufficiency

/-!
# Bounded call-depth / calldata-size memory probe

A native executable that runs one deeply nested EVM call program at a chosen
depth and input-region size, with no fixture file, no corpus and no harness.
It exists so the memory property Jaune fixed in goal `jaune-linux-16gb-memory-v1`
— that a one-megabyte calldata region driven through a 1,024-deep call path is
not retained once per frame — is exercised by an ordinary automated gate rather
than only by a 16 GB Linux acceptance campaign.

`scripts/check-memory-probe.sh` is that gate: it runs the points below under an
asserted peak. This file is built by the ordinary `lake build` (it is a Lake
`@[default_target]`) and is inside `scripts/check-hygiene.sh`'s and
`scripts/check-integrity.sh`'s scanned scope, so it cannot rot unnoticed.

Two call families are covered. `STATICCALL` is the family the original
pathological fixture uses and the family `Xinst.stepCached` specializes; `CALL`
is the analogue that shares the same `genericCall.step` retention mechanism and
takes the unspecialized path. Measuring both alone is what distinguishes "the
corpus passes" from "this code path is cheap".
-/

open Jaune

namespace Jaune.MemoryProbe

/-- The call family a probe program uses. Both drive the same
`genericCall.step` calldata evaluation; they differ in the opcode, in one extra
stack operand (`CALL` carries a value) and therefore in the program's length. -/
inductive Family where
  /-- `0xfa` — the family of the original `static_Call1MB1024Calldepth` fixture,
  and the one `Xinst.stepCached` specializes. -/
  | staticcall
  /-- `0xf1` — the unspecialized analogue, shape-matched to
  `call1_mb1024_calldepth`. -/
  | call
  deriving DecidableEq, Repr

def Family.opcode : Family → UInt8
  | .staticcall => 0xfa
  | .call => 0xf1

def Family.name : Family → String
  | .staticcall => "staticcall"
  | .call => "call"

/-- `CALL` pushes one extra operand (`value`), so its program is two bytes
longer and its terminal `JUMPDEST` sits two bytes later. -/
def Family.valuePush : Family → Bytes
  | .staticcall => []
  | .call => [0x60, 0x00]

def Family.endOffset : Family → UInt8
  | .staticcall => 0x45
  | .call => 0x47

private def byte3 (n : Nat) : Bytes :=
  [(n / 65536).toUInt8, (n / 256).toUInt8, n.toUInt8]

/-- The Prague `d1g0v0` memory-counter program, parameterized by the call
family and by the call's input-region size. Its counter is frame-local, so
recursion ends at the EVM call-depth boundary rather than at the storage-counter
branch used by the companion `d0g0v0` program. -/
def recursiveCallCode (family : Family) (target : Adr) (inputSize : Nat) : ByteArray :=
  Bytes.toByteArray <|
    [ 0x60, 0x01, 0x60, 0x00, 0x51, 0x01, 0x60, 0x00, 0x52,
      0x61, 0x04, 0x00, 0x60, 0x00, 0x51, 0x10, 0x60, 0x1b,
      0x57, 0x60, 0x01, 0x60, 0x40, 0x52, 0x60, family.endOffset, 0x56,
      0x5b, 0x60, 0x00, 0x60, 0x00, 0x62 ] ++
    byte3 inputSize ++
    [0x60, 0x00] ++ family.valuePush ++ [0x73] ++ target.toBytes ++
    [0x62, 0x0f, 0x55, 0xc8, 0x5a, 0x03, family.opcode, 0x60, 0x20,
     0x52, 0x5b, 0x00]

/-- The original spelling, retained so the historical evidence records and the
goal documents that name it still resolve. -/
def recursiveStaticCallCode (target : Adr) (inputSize : Nat) : ByteArray :=
  recursiveCallCode .staticcall target inputSize

/-- Number of `cbb…` frames exercised by `recursiveCallCode` from an initial
remaining-depth value.  The counter is frame-local and therefore equals one in
every frame; the exact fixture program keeps spawning until the depth-zero
call refusal. -/
def recursiveFrameCount (initialDepth : Nat) : Nat := initialDepth + 1

#guard recursiveFrameCount 0 = 1
#guard recursiveFrameCount 1023 = 1024

-- The terminal `JUMPDEST` each family jumps to is the last byte but one of its
-- own program, so the two `endOffset` literals are the program lengths minus
-- two rather than free parameters.
#guard (recursiveCallCode .staticcall 0 1000000).size = 71
#guard (recursiveCallCode .call 0 1000000).size = 73
#guard (recursiveCallCode .staticcall 0 1000000).data.getD 0x45 0 = 0x5b
#guard (recursiveCallCode .call 0 1000000).data.getD 0x47 0 = 0x5b

/-- Why a probe run produced no measurement. A typed carrier rather than a
`String`, so this file sits inside `scripts/check-integrity.sh`'s R4 scope with
no allowlist row. -/
inductive ProbeError where
  /-- The initial message could not be settled into a frame. -/
  | frameSettlement
  /-- Execution ended in a settled halt rather than an ordinary stop. -/
  | settledHalt
  deriving DecidableEq, Repr

def ProbeError.render : ProbeError → String
  | .frameSettlement => "frame settlement failed"
  | .settledHalt => "execution ended with a settled halt"

def probeMsg (family : Family) (depth inputSize : Nat) : Msg :=
  let target : Adr := 0xcbbf5374fce5edbc8e2a8697c15331677e6ebf0b
  let code := recursiveCallCode family target inputSize
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

def run (family : Family) (depth inputSize : Nat) :
    Except ProbeError (Nat × Nat × B256) :=
  match processMessage (probeMsg family depth inputSize) with
  | .error _ => .error .frameSettlement
  | .ok devm =>
    if devm.error.isSome then
      .error .settledHalt
    else
      let success := Bytes.toB256 (devm.memory.data.sliceD 32 32 0)
      .ok (devm.memory.size, devm.memory.data.size, success)

private def parseFamily (text : String) : Option Family :=
  if text = "--staticcall" then some .staticcall
  else if text = "--call" then some .call
  else none

private def usage : String :=
  "usage: jaune-memory-probe [--staticcall|--call] DEPTH INPUT_SIZE"

private def parseSizes (depth inputSize : String) : IO (Nat × Nat) := do
  match depth.toNat?, inputSize.toNat? with
  | some depth, some inputSize =>
    if 0xffffff < inputSize then
      throw (IO.userError "input size must fit PUSH3")
    else pure (depth, inputSize)
  | _, _ => throw (IO.userError "depth and input size must be decimal naturals")

private def parseArgs (args : List String) : IO (Family × Nat × Nat) := do
  match args with
  | [depth, inputSize] =>
    let (depth, inputSize) ← parseSizes depth inputSize
    pure (.staticcall, depth, inputSize)
  | [familyText, depth, inputSize] =>
    match parseFamily familyText with
    | none => throw (IO.userError usage)
    | some family =>
      let (depth, inputSize) ← parseSizes depth inputSize
      pure (family, depth, inputSize)
  | _ => throw (IO.userError usage)

def main (args : List String) : IO UInt32 := do
  let (family, depth, inputSize) ← parseArgs args
  match run family depth inputSize with
  | .error error =>
    IO.eprintln
      s!"FAIL family={family.name} depth={depth} input={inputSize}: {error.render}"
    pure 1
  | .ok (logicalSize, materializedSize, success) =>
    IO.println
      s!"PASS family={family.name} depth={depth} frames={recursiveFrameCount depth} input={inputSize} logical={logicalSize} materialized={materializedSize} success={success.toNat}"
    if success = 1 then pure 0 else pure 1

end Jaune.MemoryProbe

def main (args : List String) : IO UInt32 := Jaune.MemoryProbe.main args
