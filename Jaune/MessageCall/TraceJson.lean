import Jaune.MessageCall.Trace
import Jaune.T8n

/-!
# The four-part message call: the trace serialiser (goal `jaune-shape-and-names-v1`, W1 unit K1)

Today's readers (`Jaune.TraceJson`) over the staged events of `Jaune.MessageCall.Trace`. Staged under a namespace of its own until the switch commit, which gave it its final names; the switch (unit K2) moved the tracer onto it.

What changes is where each value is read (the W1 design note, second revision, §6.5):

* at a spawn, the saved caller's gas and refund come from the child's checkpoint, the child's
  grant from its message, and call or create from the pending return target;
* the root summary reads the settled `Frame.Result`: its output and gas, the world after the
  frame, and whether it failed; a root fault renders through today's renderer.

The configuration, the serialiser state and the rendering helpers are today's or copies of
today's private ones; they move here with the switch.
-/

namespace Jaune

namespace TraceJson

open Lean Jaune

structure Config where
  runId : String
  memory : Bool := false
  deferSummary : Bool := false
  maxDataBytes : Nat := 1048576
  maxSteps : Option Nat := none
  maxRowBytes : Nat := 1048576

def opcode (before : Evm) : Nat := (before.sta.code.byteD before.pc).toNat

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

/-- Today's `gasCost?` over the staged step. At a spawn the saved caller is the child's
checkpoint, the child's grant its message's gas, and the kind its pending return target. -/
def gasCost? (before : Evm) (step : Step) : Option Nat :=
  if before.sta.benvStat.rules.stateGas.isSome then none else
  match step with
  | .next _ after =>
    if [0xf0, 0xf1, 0xf2, 0xf4, 0xf5, 0xfa].contains (opcode before) then none
    else safeSub before.dyna.gasLeft after.gasLeft
  | .halt (.ok after) | .halt (.error ⟨.revert, after⟩) =>
    safeSub before.dyna.gasLeft after.gasLeft
  | .halt (.error _) => none
  | .spawn child pending _ =>
    match pending.target with
    | .call .. => safeSub before.dyna.gasLeft child.checkpoint.machine.gasLeft
    | .create _ =>
      safeSub before.dyna.gasLeft (child.checkpoint.machine.gasLeft + child.message.gas)

/-- Today's pre-operation row over the staged step. -/
def instruction (cfg : Config) (context : Trace.Context) (refundBase : Int)
    (before : Evm) (step : Step) : Except String Json := do
  if before.dyna.returnData.length > cfg.maxDataBytes then
    throw "return data exceeds maxDataBytes"
  if cfg.memory && before.dyna.memory.size > cfg.maxDataBytes then
    throw "memory observation exceeds maxDataBytes"
  let refund := refundBase + before.dyna.refundCounter
  let mut fields := [
    ("pc", number before.pc), ("op", number (opcode before)),
    ("depth", number context.depth), ("gas", quantity before.dyna.gasLeft),
    ("memSize", number before.dyna.memory.size),
    ("stack", .arr (before.dyna.stack.reverse.map (quantity ∘ U256.toNat)).toArray),
    ("returnData", bytes before.dyna.returnData)]
  if let some cost := gasCost? before step then
    fields := fields ++ [("gasCost", quantity cost)]
  if refund ≥ 0 then fields := fields ++ [("refund", number refund.toNat)]
  if let some inst := before.getInst then
    fields := fields ++ [("opName", .str inst.toOpString)]
  if cfg.memory then
    let memory := before.dyna.memory
    if memory.size % 32 != 0 then throw "memory size is not word aligned"
    let words := (List.range (memory.size / 32)).map fun i =>
      bytes (memory.data.sliceD (i * 32) 32 0)
    fields := fields ++ [("memory", .arr words.toArray)]
  if let .halt (.error ⟨error, _⟩) := step then
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

/-- Today's root summary over the staged settled result: the frame's grant is its message's gas,
the state root is the world after the frame, and the pass flag is "did not fail". -/
def rootSummary (cfg : Config) (frame : Frame) (result : Frame.Result) :
    Except String Json := do
  if result.output.length > cfg.maxDataBytes then throw "output exceeds maxDataBytes"
  let some used := safeSub frame.message.gas result.gasLeft
    | throw "settled gas exceeds root grant"
  return Json.mkObj [
    ("stateRoot", .str (T8n.hexU256 (frame.worldAfter result).state.root)),
    ("output", bytes result.output), ("gasUsed", quantity used),
    ("pass", .bool !result.failed)]

/-- Today's `consume` over the staged events. -/
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
  | .instruction ctx before step =>
    let frame ← current cfg state ctx
    if before.sta.code.size == 0 && before.pc == 0 then
      if let .halt (.ok _) := step then
        return (state, none, lifecycle ctx "empty-code")
    if let some limit := cfg.maxSteps then
      if state.steps ≥ limit then throw "instruction limit exceeded"
    let row ← instruction cfg ctx frame.refundBase before step
    let childBase := match step with
      | .spawn child _ _ => some (frame.refundBase + child.checkpoint.substate.refund)
      | _ => none
    return ({ state with steps := state.steps + 1, childRefundBase := childBase },
      some row, lifecycle ctx "instruction" [("step", number state.steps)])
  | .exited ctx raw =>
    let _ ← current cfg state ctx
    if raw.isNone then throw "fuel exhausted before complete execution"
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

/-- Today's `IO` sink over the staged events: the same writes, flushes and limits. -/
def sink (cfg : Config) (state : IO.Ref State)
    (trace frames : IO.FS.Handle) : Trace.Sink IO := fun event => do
  let (next, row, frameRow) ← match consume cfg (← state.get) event with
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
  state.set next

end TraceJson

end Jaune

