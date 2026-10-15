import Jaune.Trace
import Jaune.T8n

/-!
Runner-side observations over the proof-carrying driver. Gas costs that the
existing step result does not retain stay absent. No instruction is rerun.
The separate lifecycle stream preserves run/frame identity without extending
the comparator's instruction schema. Retention is bounded by active depth.
-/
namespace Jaune.TraceJson
open Lean Jaune

structure Config where
  runId : String
  memory : Bool := false
  deferSummary : Bool := false
  maxDataBytes : Nat := 1048576
  maxSteps : Option Nat := none
  maxRowBytes : Nat := 1048576

private def number (n : Nat) : Json := toJson n
private def quantity (n : Nat) : Json := .str (T8n.hexQuantity n)
private def bytes (bs : Bytes) : Json := .str (T8n.hexBytes bs)
private def textBytes (s : String) : Json := bytes s.toUTF8.data.toList

def opcode (before : Evm) : Nat := (before.sta.code.byteD before.pc).toNat

private def resumeParent : Resume → Devm
  | .create parent _ | .call parent _ _ => parent
  | .createAmsterdam _ parent _ _ | .callAmsterdam _ parent _ _ _ => parent

/-- Non-spawning CALL/CREATE may already have returned or consumed a grant;
exceptional steps can discard a failed charge. Neither is a reliable delta.
Amsterdam's two-dimensional pricing needs its own observation convention. -/
def gasCost? (before : Evm) (step : Step) : Option Nat :=
  if before.sta.benvStat.rules.stateGas.isSome then none else
  match step with
  | .cont _ after =>
    if [0xf0, 0xf1, 0xf2, 0xf4, 0xf5, 0xfa].contains (opcode before) then none
    else safeSub before.dyna.gasLeft after.gasLeft
  | .halt (.ok after) | .halt (.error ⟨.revert, after⟩) =>
    safeSub before.dyna.gasLeft after.gasLeft
  | .halt (.error _) => none
  | .spawn frame resume _ =>
    match resume with
    | .call parent _ _ => safeSub before.dyna.gasLeft parent.gasLeft
    | .create parent _ => safeSub before.dyna.gasLeft (parent.gasLeft + frame.inner.gas)
    | .callAmsterdam .. | .createAmsterdam .. => none

/-- Encode pre-operation state. The refund base is the sum of suspended
ancestors' local counters, not the last emitted child's counter. -/
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
    ("stack", .arr (before.dyna.stack.reverse.map (quantity ∘ B256.toNat)).toArray),
    ("returnData", bytes before.dyna.returnData)]
  if let some cost := gasCost? before step then
    fields := fields ++ [("gasCost", quantity cost)]
  -- The supported wire field is unsigned. A negative global counter is
  -- unavailable, never clamped to a fabricated zero.
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

private def lifecycle (context : Trace.Context) (event : String)
    (extra : List (String × Json) := []) : Json :=
  Json.mkObj ([("runId", .str context.runId), ("frame", number context.frame),
    ("depth", number context.depth), ("event", .str event)] ++ extra)

private def current (cfg : Config) (state : State) (ctx : Trace.Context) :
    Except String OpenFrame := do
  if ctx.runId != cfg.runId then throw "event run identity differs"
  match state.frames with
  | [] => throw "event outside an open frame"
  | frame :: _ =>
    if frame.id != ctx.frame || ctx.depth != state.frames.length then
      throw "event frame identity or depth differs"
    return frame

private def rootSummary (cfg : Config) (frame : Frame) (result : Devm) :
    Except String Json := do
  if result.output.length > cfg.maxDataBytes then throw "output exceeds maxDataBytes"
  let some used := safeSub frame.inner.gas result.gasLeft
    | throw "settled gas exceeds root grant"
  return Json.mkObj [
    ("stateRoot", .str (T8n.hexB256 result.state.root)),
    ("output", bytes result.output), ("gasUsed", quantity used),
    ("pass", .bool result.error.isNone)]

/-- One event produces at most one trace row and one lifecycle row. Internal
errors and exhausted fuel fail without a completing summary. -/
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
    -- The total interpreter models empty code by a synthetic STOP transition.
    -- The bytecode trace convention has no instruction for an empty frame.
    if before.sta.code.size == 0 && before.pc == 0 then
      if let .halt (.ok _) := step then
        return (state, none, lifecycle ctx "empty-code")
    if let some limit := cfg.maxSteps then
      if state.steps ≥ limit then throw "instruction limit exceeded"
    let row ← instruction cfg ctx frame.refundBase before step
    let childBase := match step with
      | .spawn _ resume _ => some (frame.refundBase + (resumeParent resume).refundCounter)
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
      | .error ⟨error, _⟩ => throw ("root execution failed: " ++ error.render)
      | .ok result => some <$> rootSummary cfg frame result
      else pure none
    return ({ state with frames := tail, closed := tail.isEmpty }, row,
      lifecycle ctx "settled" [("root", .bool tail.isEmpty)])

/-- The caller owns both handles. Lifecycle is written before its trace row;
every write is flushed, and I/O/limit errors propagate through the driver. -/
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

end Jaune.TraceJson
