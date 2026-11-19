import Jaune.MessageCall.Trace
import Jaune.MessageCall.CheckedExec
import Jaune.Bridge.G2b.CheckedFrame
import Jaune.Run.CheckedMessage

/-!
# The staged message-level tracer over the checked interpreter (goal `jaune-shape-and-names-v1`, G2b, F1e)

The streaming driver of `Jaune.MessageCall.Trace`, run over the checked interpreter
(`Checked.step`, `Checked.enter`, `Checked.settle`, `Checked.resume`, `Checked.exec` and
`Checked.Frame.runTop`) instead of the `Devm` one. It emits the same `Trace.Event`s through the
same `Trace.Sink`, in the same order, so the serialiser `Jaune.MessageCall.TraceJson` and its
runners read it unchanged.

The event type still names the `Devm` vocabulary (`Evm`, `Devm`, `Step`, `Frame`, `Frame.Entry`,
`Pending`, `Execution`). Each event is the projection of the checked state onto it:

* a running frame is `Trace.evm`: its program counter, its message's static record and its state
  as a `Devm` with no output and no stored error;
* a frame is `Trace.frame`, with its checkpoint's memory as a `Mem`;
* how a frame stopped is `Trace.exitRaw`, a fault `Trace.faultRaw`: the fault's `EvmError`, with
  the default `Devm` as its state, which neither the serialiser nor any caller reads;
* a spawn's pending return is `Trace.pending`, with no passed-through output and no stored error.

`Jaune.Bridge.G2b.CheckedTrace` proves that, from related starts, these events are the `Devm`
tracer's events normalised by exactly what the projection forgets, and that the serialiser reads
nothing it forgets, so the serialised output is identical.

Each successful return carries a kernel-checked projection onto the checked driver, as the `Devm`
tracer's returns do onto its driver. This module sits outside `Jaune.lean`'s import closure.
-/

namespace Jaune.Checked.Trace

variable [LegacyTransaction]

open Jaune

/-! ### Projections onto the trace's event vocabulary -/

/-- A checked memory as the event's memory. -/
def mem (m : Memory) : Mem := ⟨m.data, m.size⟩

/-- A checked state as the event's lifetime-grouped state. -/
def state (s : Frame.State) : Jaune.Frame.State :=
  ⟨⟨s.machine.stack, mem s.machine.memory, s.machine.gasLeft, s.machine.stateGas,
    s.machine.returnData⟩, s.world, s.substate, s.trail⟩

/-- A checked state as a `Devm`, with no output and no stored error. -/
def devm (s : Frame.State) : Devm := (state s).toDevm

/-- A checked frame as the event's frame. -/
def frame (f : Frame) : Jaune.Frame := f.toLegacy

/-- A running frame of the message `msg` as the event's running machine. -/
def evm (msg : Jaune.Message) (r : Frame.Running) : Evm := ⟨r.pc, msg.sevm, devm r.state⟩

/-- How a frame stopped, as the event's raw result. -/
def exitRaw : Frame.Exit → Execution
  | .finished output s => .ok ((devm s).withOutput output)
  | .reverted output s => .error (.revert, (devm s).withOutput output)
  | .halted reason s => .error (.halt reason, devm s)

/-- A fault as the event's raw result. Its state is never read. -/
def faultRaw (fault : Fault) : Execution := .error (fault.toEvmError, default)

/-- A frame's raw result or fault, as the event's raw result. -/
def raw : Except Fault Frame.Exit → Execution
  | .error fault => faultRaw fault
  | .ok exit => exitRaw exit

/-- A pending return as the event's, with no passed-through output and no stored error. -/
def pending (p : Staging.Pending) : Pending := ⟨p.target, p.newAccountCharged, [], none⟩

/-- One checked step as the event's step. A fault is shown as the raw result it ends the run
with. -/
def step (result : Except Fault Step) : Jaune.Step :=
  match result with
  | .error fault => .halt (faultRaw fault)
  | .ok (.exit e) => .halt (exitRaw e)
  | .ok (.next pc s) => .next pc (devm s)
  | .ok (.spawn child p pc) => .spawn (frame child) (pending p) pc

/-- The top-level frame of a message, with the checked memory: `Frame.ofTop`'s, whose checkpoint
memory is empty. -/
def topFrame (msg : Msg) (isCreate : Bool) : Frame :=
  let top := Jaune.Frame.ofTop msg isCreate
  let s := top.checkpoint
  ⟨Message.ofLegacy top.message,
    ⟨⟨s.machine.stack, Memory.empty, s.machine.gasLeft, s.machine.stateGas, s.machine.returnData⟩,
      s.world, s.substate, s.trail⟩⟩

/-- An entry of a frame of the message `msg` as the event's entry. -/
def entry (msg : Jaune.Message) : Frame.Entry → Jaune.Frame.Entry
  | .done result => .done result
  | .run r => .run (evm msg r)

/-! ### The caller after its child -/

/-- The caller after its child has settled: a fault, in settlement or in resumption, a halt or
the resumed state. -/
def resumed (rules : ForkRules) (child : Frame) (p : Staging.Pending) :
    Except Fault Frame.Result → Except Fault (Except (ExceptionalHalt × Frame.State) Frame.State)
  | .error fault => .error fault
  | .ok result => resume rules p child.checkpoint result

/-- The caller after its child, as the event's raw result. -/
def resumedRaw : Except Fault (Except (ExceptionalHalt × Frame.State) Frame.State) → Execution
  | .error fault => faultRaw fault
  | .ok (.error (reason, s)) => .error (.halt reason, devm s)
  | .ok (.ok s) => .ok (devm s)

/-- How the driver goes on after a resumption. -/
def continueWith (context : CallContext) (pc fuel : Nat) :
    Except Fault (Except (ExceptionalHalt × Frame.State) Frame.State) → Fueled Fault Frame.Exit
  | .error fault => Fueled.ofExcept (.error fault)
  | .ok (.error (reason, s)) => Fueled.ofExcept (.ok (.halted reason s))
  | .ok (.ok s) => Checked.execFueled ⟨pc, context, s⟩ fuel

/-- The driver's spawn tail, read through `resumed`. -/
theorem execFueled_tail (context : CallContext) (rules : ForkRules) (child : Frame)
    (p : Staging.Pending) (pc fuel : Nat) (settled : Except Fault Frame.Result) :
    (match (generalizing := false) some settled with
      | none => Fueled.exhausted
      | some (.error fault) => Fueled.ofExcept (.error fault)
      | some (.ok result) =>
        match (generalizing := false) resume rules p child.checkpoint result with
        | .error fault => Fueled.ofExcept (.error fault)
        | .ok (.error (reason, s)) => Fueled.ofExcept (.ok (Frame.Exit.halted reason s))
        | .ok (.ok s) => Checked.execFueled ⟨pc, context, s⟩ fuel :
        Fueled Fault Frame.Exit)
      = continueWith context pc fuel (resumed rules child p settled) := by
  rcases settled with fault | result
  · rfl
  · simp only [resumed]
    rcases resume rules p child.checkpoint result with fault | ⟨reason, s⟩ | s <;> rfl

/-- The checked driver at a spawn, read through `resumed`. -/
theorem execFueled_spawn {r : Frame.Running} {fuel : Nat} {child : Frame} {p : Staging.Pending}
    {pc : Nat} (hstep : Checked.step r = .ok (.spawn child p pc)) :
    Checked.execFueled r (fuel + 1)
      = match (match enter child with
          | .done result => some result
          | .run cr => ((Checked.execFueled cr fuel).run).map (· >>= settle child)) with
        | none => Fueled.exhausted
        | some settled =>
          continueWith r.context pc fuel (resumed r.context.block.rules child p settled) := by
  rw [Checked.execFueled, hstep]
  dsimp only
  cases enter child with
  | done x => exact execFueled_tail r.context _ child p pc fuel x
  | run cr =>
    dsimp only
    cases (Checked.execFueled cr fuel).run with
    | none => rfl
    | some x => exact execFueled_tail r.context _ child p pc fuel _

/-! ### The traced driver -/

/-- Proof fields are erased at runtime. `nextFrame` is the next unused frame number. -/
structure CertifiedResult (expected : Fueled Fault Frame.Exit) where
  value : Fueled Fault Frame.Exit
  nextFrame : Nat
  erases : value = expected

/-- Index by the checked driver's result, so that proof transport erases to runtime identity. -/
abbrev Result (r : Frame.Running) (fuel : Nat) := CertifiedResult (Checked.execFueled r fuel)

/-- The checked driver with an arbitrary monadic streaming sink, over step, entry, settlement and
resumption, for a running frame of the message `msg`. The events and their order are those of
`Jaune.Trace.execFueled`: fuel zero emits no instruction; child events precede the parent's next
instruction. -/
def execFueled {m : Type → Type} [Monad m] (sink : Jaune.Trace.Sink m) (msg : Jaune.Message) :
    (r : Frame.Running) → (fuel : Nat) → Jaune.Trace.Context → Nat → m (Result r fuel)
  | _, 0, context, nextFrame => do
    sink (.exited context none)
    pure ⟨Fueled.exhausted, nextFrame, by simp only [Checked.execFueled]⟩
  | r, fuel + 1, context, nextFrame => do
    match hstep : Checked.step r with
    | .error fault =>
      sink (.instruction context (evm msg r) (step (.error fault)))
      sink (.exited context (some (faultRaw fault)))
      pure ⟨Fueled.ofExcept (.error fault), nextFrame, by simp only [Checked.execFueled, hstep]⟩
    | .ok (.exit e) =>
      sink (.instruction context (evm msg r) (step (.ok (.exit e))))
      sink (.exited context (some (exitRaw e)))
      pure ⟨Fueled.ofExcept (.ok e), nextFrame, by simp only [Checked.execFueled, hstep]⟩
    | .ok (.next pc s) =>
      sink (.instruction context (evm msg r) (step (.ok (.next pc s))))
      cast (congrArg (fun expected => m (CertifiedResult expected)) (by
        simp only [Checked.execFueled, hstep]))
        (execFueled sink msg ⟨pc, r.context, s⟩ fuel context nextFrame)
    | .ok (.spawn child p pc) =>
      sink (.instruction context (evm msg r) (step (.ok (.spawn child p pc))))
      let childContext := { context with frame := nextFrame, depth := context.depth + 1 }
      let rules := r.context.block.rules
      match hentry : enter child with
      | .done settled =>
        sink (.entered childContext (frame child) (.done settled))
        sink (.settled childContext (frame child) settled)
        match hresume : resumed rules child p settled with
        | .ok (.ok s) =>
          sink (.resumed context nextFrame (resumedRaw (.ok (.ok s))))
          cast (congrArg (fun expected => m (CertifiedResult expected)) (by
            rw [execFueled_spawn hstep, hentry]; dsimp only; rw [hresume]; rfl))
            (execFueled sink msg ⟨pc, r.context, s⟩ fuel context (nextFrame + 1))
        | .ok (.error (reason, s)) =>
          sink (.resumed context nextFrame (resumedRaw (.ok (.error (reason, s)))))
          sink (.exited context (some (resumedRaw (.ok (.error (reason, s))))))
          pure ⟨Fueled.ofExcept (.ok (.halted reason s)), nextFrame + 1, by
            rw [execFueled_spawn hstep, hentry]; dsimp only; rw [hresume]; rfl⟩
        | .error fault =>
          sink (.resumed context nextFrame (resumedRaw (.error fault)))
          sink (.exited context (some (resumedRaw (.error fault))))
          pure ⟨Fueled.ofExcept (.error fault), nextFrame + 1, by
            rw [execFueled_spawn hstep, hentry]; dsimp only; rw [hresume]; rfl⟩
      | .run cr =>
        sink (.entered childContext (frame child) (.run (evm child.toLegacy.message cr)))
        let childResult ← execFueled sink child.toLegacy.message cr fuel childContext (nextFrame + 1)
        match hchild : childResult.value.run with
        | none =>
          sink (.exited context none)
          pure ⟨Fueled.exhausted, childResult.nextFrame, by
            rw [execFueled_spawn hstep, hentry]; dsimp only
            rw [← childResult.erases, hchild]; rfl⟩
        | some x =>
          let settled := x >>= settle child
          sink (.settled childContext (frame child) settled)
          match hresume : resumed rules child p settled with
          | .ok (.ok s) =>
            sink (.resumed context nextFrame (resumedRaw (.ok (.ok s))))
            cast (congrArg (fun expected => m (CertifiedResult expected)) (by
              rw [execFueled_spawn hstep, hentry]; dsimp only
              rw [← childResult.erases, hchild]; dsimp only [Option.map]; rw [hresume]; rfl))
              (execFueled sink msg ⟨pc, r.context, s⟩ fuel context childResult.nextFrame)
          | .ok (.error (reason, s)) =>
            sink (.resumed context nextFrame (resumedRaw (.ok (.error (reason, s)))))
            sink (.exited context (some (resumedRaw (.ok (.error (reason, s))))))
            pure ⟨Fueled.ofExcept (.ok (.halted reason s)), childResult.nextFrame, by
              rw [execFueled_spawn hstep, hentry]; dsimp only
              rw [← childResult.erases, hchild]; dsimp only [Option.map]; rw [hresume]; rfl⟩
          | .error fault =>
            sink (.resumed context nextFrame (resumedRaw (.error fault)))
            sink (.exited context (some (resumedRaw (.error fault))))
            pure ⟨Fueled.ofExcept (.error fault), childResult.nextFrame, by
              rw [execFueled_spawn hstep, hentry]; dsimp only
              rw [← childResult.erases, hchild]; dsimp only [Option.map]; rw [hresume]; rfl⟩
  termination_by _ fuel _ _ => fuel

/-- The exact execution projection of every successfully returned result. -/
theorem execFueled_erasure {r : Frame.Running} {fuel : Nat} (result : Result r fuel) :
    result.value = Checked.execFueled r fuel := result.erases

/-- Successful total executions agree with the total checked interpreter. -/
structure ExecutionResult (r : Frame.Running) where
  value : Except Fault Frame.Exit
  nextFrame : Nat
  erases : value = Checked.exec r

/-- Seed exactly the same sufficient fuel as the total interpreter. Exhaustion gives the
interpreter's own internal invariant fault, with no further event. -/
def exec {m : Type → Type} [Monad m] (sink : Jaune.Trace.Sink m) (msg : Jaune.Message)
    (r : Frame.Running) (context : Jaune.Trace.Context) (nextFrame : Nat) :
    m (ExecutionResult r) := do
  let result ← execFueled sink msg r (sufficientFuel r.state.machine.gasMeasure) context nextFrame
  match hrun : result.value.run with
  | some x =>
    pure ⟨x, result.nextFrame, by simp only [Checked.exec, ← result.erases, hrun]⟩
  | none =>
    pure ⟨.error (.internal (.invariant .none)), result.nextFrame, by
      simp only [Checked.exec, ← result.erases, hrun]⟩

/-- The total traced driver returns exactly the total checked interpreter's result. -/
theorem exec_erasure {r : Frame.Running} (result : ExecutionResult r) :
    result.value = Checked.exec r := result.erases

structure FrameResult (f : Frame) where
  run : Except Fault Frame.TopRun
  nextFrame : Nat
  run_erases : run = f.runTopWithRoot

/-- The settled result delivered to a caller that does not need the entered root. -/
def FrameResult.value {f : Frame} (result : FrameResult f) : Except Fault Jaune.Frame.Result :=
  result.run.map Frame.TopRun.result

theorem FrameResult.erases {f : Frame} (result : FrameResult f) :
    result.value = f.runTop := by
  unfold FrameResult.value Frame.runTop
  rw [result.run_erases]

/-- The top-level frame boundary. A root precompile or failed transfer has no instruction
events, but still has entry and settlement events. One invocation represents one identified
run. -/
def runFrame {m : Type → Type} [Monad m] (sink : Jaune.Trace.Sink m) (f : Frame)
    (runId : String) : m (FrameResult f) := do
  let context : Jaune.Trace.Context := ⟨runId, 0, 1⟩
  match hentry : enterWith f f.checkpoint with
  | .done settled =>
    sink (.entered context (frame f) (.done settled))
    sink (.settled context (frame f) settled)
    pure ⟨settled.map (fun value => ⟨none, value⟩), 1, by
      simp only [Checked.Frame.runTopWithRoot, hentry]⟩
  | .run r =>
    sink (.entered context (frame f) (.run (evm f.toLegacy.message r)))
    let result ← exec sink f.toLegacy.message r context 1
    let settled := result.value >>= settle f
    sink (.settled context (frame f) settled)
    pure ⟨settled.map (fun value => ⟨some r, value⟩), result.nextFrame, by
      simp only [Checked.Frame.runTopWithRoot, hentry, settled, result.erases]⟩

/-- Exact connection to the checked top-level frame's settled result. -/
theorem runFrame_erasure {f : Frame} (result : FrameResult f) :
    result.value = Checked.Frame.runTop f := result.erases

structure PreparedResult (preparation : TopLevel.Preparation) where
  run : Except Fault TopLevel.Run
  erases : run = preparation.run

/-- Trace the same prepared run as the interpreter. A refusal emits no frame
event. On entry the caller's refund hook precedes the first frame event. -/
def runPrepared {m : Type → Type} [Monad m] (sink : Jaune.Trace.Sink m)
    (reportRefund : Nat → m Unit) (preparation : TopLevel.Preparation) (runId : String)
    : m (PreparedResult preparation) := do
  match hprep : preparation with
  | .refused reason => pure ⟨.ok (.refused reason), by rw [hprep]; rfl⟩
  | .frame f refund =>
    reportRefund refund
    let result ← runFrame sink f runId
    pure ⟨result.run.map (.frame f refund), by
      rw [result.run_erases, hprep]
      rfl⟩

structure InputResult (input : TopLevel.Input) where
  run : Except Fault TopLevel.Run
  erases : run = TopLevel.runNative input

/-- Prepare a native input once and trace the same frame execution as the untraced runner. -/
def runInput {m : Type → Type} [Monad m] (sink : Jaune.Trace.Sink m)
    (reportRefund : Nat → m Unit) (input : TopLevel.Input) (runId : String) : m (InputResult input) := do
  match h : TopLevel.prepareNative input with
  | .error fault => pure ⟨.error fault, by rw [TopLevel.runNative, h]; rfl⟩
  | .ok prepared =>
    let result ← runPrepared sink reportRefund prepared.toPreparation runId
    pure ⟨result.run, by rw [result.erases, TopLevel.runNative, h]; rfl⟩

end Jaune.Checked.Trace
