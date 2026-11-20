import Jaune.MessageCall.CheckedTraceEvent
import Jaune.T8n

/-!
# The checked tracer's serialiser (goal `jaune-shape-and-names-v1`, G2b, Neon review finding 2)

The JSON readers over the events of `Jaune.MessageCall.CheckedTraceEvent`; the tracer
(`TraceMain`) writes its rows through them.

Where each value is read:

* an instruction row reads the running frame before the step: its program counter, machine and
  refund; the opcode and its name from the frame's message's code;
* at a spawn, the saved caller's gas and refund come from the child's checkpoint, the child's
  grant from its message, and call or create from the pending return target;
* the root summary reads the settled `Frame.Result`: its output and gas, the world after the
  frame, and whether it failed; a root fault renders through `EvmError.render`.

`Jaune.Bridge.G2b.CheckedTrace` proves that these rows are byte for byte the rows the `Devm`
tracer's serialiser writes for the projected events. This module sits outside `Jaune.lean`'s
import closure.
-/

namespace Jaune.Checked.TraceJson

open Lean Jaune

structure Config where
  runId : String
  memory : Bool := false
  deferSummary : Bool := false
  maxDataBytes : Nat := 1048576
  maxSteps : Option Nat := none
  maxRowBytes : Nat := 1048576

/-- The opcode byte at the running frame's program counter. -/
def opcode (msg : Message) (before : Frame.Running) : Nat :=
  (msg.context.code.byteD before.pc).toNat

structure OpenFrame where
  id : Nat
  refundBase : Int

structure State where
  frames : List OpenFrame := []
  childRefundBase : Option Int := none
  rootRefund : Nat := 0
  steps : Nat := 0
  started : Bool := false
  closed : Bool := false

def number (n : Nat) : Json := toJson n
def quantity (n : Nat) : Json := .str (T8n.hexQuantity n)
def bytes (bs : Bytes) : Json := .str (T8n.hexBytes bs)
def textBytes (s : String) : Json := bytes s.toUTF8.data.toList

/-- The gas cost of a step, if the row reports one. At a spawn the saved caller is the child's
checkpoint, the child's grant its message's gas, and the kind its pending return target. -/
def gasCost? (msg : Message) (before : Frame.Running) (step : Except Fault Step) : Option Nat :=
  if msg.context.block.rules.stateGas.isSome then none else
  match step with
  | .ok (.next _ after) =>
    if [0xf0, 0xf1, 0xf2, 0xf4, 0xf5, 0xfa].contains (opcode msg before) then none
    else safeSub before.state.machine.gasLeft after.machine.gasLeft
  | .ok (.exit (.finished _ after)) | .ok (.exit (.reverted _ after)) =>
    safeSub before.state.machine.gasLeft after.machine.gasLeft
  | .ok (.exit (.halted ..)) | .error _ => none
  | .ok (.spawn child pending _) =>
    match pending.target with
    | .call .. => safeSub before.state.machine.gasLeft child.checkpoint.machine.gasLeft
    | .create _ =>
      safeSub before.state.machine.gasLeft (child.checkpoint.machine.gasLeft + child.message.gas)

/-- The error a stopping step reports: a fault, a revert or an exceptional halt. -/
def error? : Except Fault Step → Option EvmError
  | .error fault => some fault.toEvmError
  | .ok (.exit (.reverted ..)) => some .revert
  | .ok (.exit (.halted reason _)) => some (.halt reason)
  | _ => none

/-- The pre-operation row of a step. -/
def instruction (cfg : Config) (context : Trace.Context) (refundBase : Int) (msg : Message)
    (before : Frame.Running) (step : Except Fault Step) : Except String Json := do
  if before.state.machine.returnData.length > cfg.maxDataBytes then
    throw "return data exceeds maxDataBytes"
  if cfg.memory && before.state.machine.memory.size > cfg.maxDataBytes then
    throw "memory observation exceeds maxDataBytes"
  let refund := refundBase + before.state.substate.refund
  let mut fields := [
    ("pc", number before.pc), ("op", number (opcode msg before)),
    ("depth", number context.depth), ("gas", quantity before.state.machine.gasLeft),
    ("memSize", number before.state.machine.memory.size),
    ("stack", .arr (before.state.machine.stack.reverse.map (quantity ∘ U256.toNat)).toArray),
    ("returnData", bytes before.state.machine.returnData)]
  if let some cost := gasCost? msg before step then
    fields := fields ++ [("gasCost", quantity cost)]
  if refund ≥ 0 then fields := fields ++ [("refund", number refund.toNat)]
  if let some inst := ByteArray.getOp msg.context.code before.pc then
    fields := fields ++ [("opName", .str inst.toOpString)]
  if cfg.memory then
    let memory := before.state.machine.memory
    if memory.size % 32 != 0 then throw "memory size is not word aligned"
    let words := (List.range (memory.size / 32)).map fun i =>
      bytes (memory.data.sliceD (i * 32) 32 0)
    fields := fields ++ [("memory", .arr words.toArray)]
  if let some error := error? step then
    fields := fields ++ [("error", textBytes error.render)]
  return Json.mkObj fields

def lifecycle (context : Trace.Context) (event : String)
    (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("runId", .str context.runId), ("frame", number context.frame),
    ("depth", number context.depth), ("event", .str event)] ++ extra)

def current (cfg : Config) (state : State) (ctx : Trace.Context) :
    Except String OpenFrame := do
  if ctx.runId != cfg.runId then throw "event run identity differs"
  match state.frames with
  | [] => throw "event outside an open frame"
  | frame :: _ =>
    if frame.id != ctx.frame || ctx.depth != state.frames.length then
      throw "event frame identity or depth differs"
    return frame

/-- The root summary over the settled result: the frame's grant is its message's gas, the state
root is the world after the frame (the result's on success, the checkpoint's otherwise), and the
pass flag is "did not fail". -/
def rootSummary (cfg : Config) (frame : Frame) (result : Frame.Result) :
    Except String Json := do
  if result.output.length > cfg.maxDataBytes then throw "output exceeds maxDataBytes"
  let some used := safeSub frame.message.gas result.gasLeft
    | throw "settled gas exceeds root grant"
  let world := match result with
    | .success _ _ _ world _ _ => world
    | _ => frame.checkpoint.world
  return Json.mkObj [
    ("stateRoot", .str (T8n.hexU256 world.state.root)),
    ("output", bytes result.output), ("gasUsed", quantity used),
    ("pass", .bool !result.failed)]

/-- Consume one trace event. -/
def consume (cfg : Config) (state : State) (event : Trace.Event) :
    Except String (State × Option Json × Json) := do
  if cfg.runId.isEmpty then throw "runId must be nonempty"
  if state.closed then throw "event after root settlement"
  match event with
  | .entered ctx _ _ =>
    if ctx.runId != cfg.runId || ctx.depth != state.frames.length + 1 then
      throw "entry identity or depth differs"
    let base ←
      if state.frames.isEmpty then do
        if state.started || ctx.frame != 0 then throw "invalid root entry"
        pure (Int.ofNat state.rootRefund)
      else state.childRefundBase.toExcept "child entry has no spawn observation"
    let parent := state.frames.head?.map fun f => ("parent", number f.id)
    let state := { state with
      frames := ⟨ctx.frame, base⟩ :: state.frames
      childRefundBase := none
      started := true }
    return (state, none, lifecycle ctx "entered" parent.toList)
  | .instruction ctx msg before step =>
    let frame ← current cfg state ctx
    if msg.context.code.size == 0 && before.pc == 0 then
      if let .ok (.exit (.finished ..)) := step then
        return (state, none, lifecycle ctx "empty-code")
    if let some limit := cfg.maxSteps then
      if state.steps ≥ limit then throw "instruction limit exceeded"
    let row ← instruction cfg ctx frame.refundBase msg before step
    let childBase := match step with
      | .ok (.spawn child _ _) => some (frame.refundBase + child.checkpoint.substate.refund)
      | _ => none
    return ({ state with steps := state.steps + 1, childRefundBase := childBase },
      some row, lifecycle ctx "instruction" [("step", number state.steps)])
  | .exited ctx outcome =>
    let _ ← current cfg state ctx
    if outcome.isNone then throw "fuel exhausted before complete execution"
    return (state, none, lifecycle ctx "exited")
  | .resumed ctx child _ =>
    let _ ← current cfg state ctx
    return (state, none, lifecycle ctx "resumed" [("child", number child)])
  | .settled ctx frame result =>
    let _ ← current cfg state ctx
    let tail := state.frames.tail
    let row ← if tail.isEmpty && !cfg.deferSummary then do
      match result with
      | .error fault => throw ("root execution failed: " ++ fault.toEvmError.render)
      | .ok result => some <$> rootSummary cfg frame result
      else pure none
    return ({ state with frames := tail, closed := tail.isEmpty }, row,
      lifecycle ctx "settled" [("root", .bool tail.isEmpty)])

/-- The `IO` sink over the trace events, reading and writing the serialiser state through `get`
and `set`: rows are written, flushed and bounded by `Config`'s limits. -/
def sinkWith (cfg : Config) (get : IO State) (set : State → IO Unit)
    (trace frames : IO.FS.Handle) : Trace.Sink IO := fun event => do
  let (next, row, frameRow) ← match consume cfg (← get) event with
    | .ok result => pure result
    | .error message => throw (IO.userError ("trace: " ++ message))
  let frameLine := frameRow.compress ++ "\n"
  let traceLine := row.map fun j => j.compress ++ "\n"
  if frameLine.utf8ByteSize > cfg.maxRowBytes ||
      (traceLine.map fun line => decide (line.utf8ByteSize > cfg.maxRowBytes)).getD false then
    throw (IO.userError "trace: row byte limit exceeded")
  frames.putStr frameLine
  frames.flush
  if let some line := traceLine then
    trace.putStr line
    trace.flush
  set next

/-- The `IO` sink over the trace events, with its state in a reference. -/
def sink (cfg : Config) (state : IO.Ref State) (trace frames : IO.FS.Handle) : Trace.Sink IO :=
  sinkWith cfg state.get state.set trace frames

end Jaune.Checked.TraceJson
