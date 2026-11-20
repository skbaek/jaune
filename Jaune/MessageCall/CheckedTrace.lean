import Jaune.MessageCall.CheckedTraceEvent
import Jaune.Run.CheckedTransaction

/-!
# The message-level tracer over the checked interpreter (goal `jaune-shape-and-names-v1`, G2b)

The streaming driver over the checked interpreter (`Checked.step`, `Checked.enter`,
`Checked.settle`, `Checked.resume`, `Checked.exec` and `Checked.Frame.runTop`). It emits the
events of `Jaune.MessageCall.CheckedTraceEvent`, over the checked types themselves, through a
`Trace.Sink`; the serialiser `Jaune.MessageCall.CheckedTraceJson` reads them.

At the `gate/g2b` tag the bridge `Jaune.Bridge.G2b.CheckedTrace` projected each event onto the
`Devm` tracer's event vocabulary and proved that, from related starts, the projected events were
the `Devm` tracer's events normalised by exactly what the projection forgets, and that the
serialised output was identical; the bridge was deleted with the `Devm` tracer after the tag
(bridge ledger, gate G2b).

Each successful return carries a kernel-checked projection onto the checked driver. This module
sits outside `Jaune.lean`'s import closure.
-/

namespace Jaune.Checked.Trace

open Jaune

/-! ### The caller after its child -/

/-- The caller after its child has settled: a fault, in settlement or in resumption, a halt or
the resumed state. -/
def resumed (rules : ForkRules) (child : Frame) (p : Staging.Pending) :
    Except Fault Frame.Result → Except Fault (Except (ExceptionalHalt × Frame.State) Frame.State)
  | .error fault => .error fault
  | .ok result => resume rules p child.checkpoint result

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
resumption, for a running frame of the message `msg`. Fuel zero emits no instruction; child
events precede the parent's next instruction. -/
def execFueled {m : Type → Type} [Monad m] (sink : Sink m) (msg : Message) :
    (r : Frame.Running) → (fuel : Nat) → Context → Nat → m (Result r fuel)
  | _, 0, context, nextFrame => do
    sink (.exited context none)
    pure ⟨Fueled.exhausted, nextFrame, by simp only [Checked.execFueled]⟩
  | r, fuel + 1, context, nextFrame => do
    match hstep : Checked.step r with
    | .error fault =>
      sink (.instruction context msg r (.error fault))
      sink (.exited context (some (.error fault)))
      pure ⟨Fueled.ofExcept (.error fault), nextFrame, by simp only [Checked.execFueled, hstep]⟩
    | .ok (.exit e) =>
      sink (.instruction context msg r (.ok (.exit e)))
      sink (.exited context (some (.ok e)))
      pure ⟨Fueled.ofExcept (.ok e), nextFrame, by simp only [Checked.execFueled, hstep]⟩
    | .ok (.next pc s) =>
      sink (.instruction context msg r (.ok (.next pc s)))
      cast (congrArg (fun expected => m (CertifiedResult expected)) (by
        simp only [Checked.execFueled, hstep]))
        (execFueled sink msg ⟨pc, r.context, s⟩ fuel context nextFrame)
    | .ok (.spawn child p pc) =>
      sink (.instruction context msg r (.ok (.spawn child p pc)))
      let childContext := { context with frame := nextFrame, depth := context.depth + 1 }
      let rules := r.context.block.rules
      match hentry : enter child with
      | .done settled =>
        sink (.entered childContext child (.done settled))
        sink (.settled childContext child settled)
        match hresume : resumed rules child p settled with
        | .ok (.ok s) =>
          sink (.resumed context nextFrame (.ok (.ok s)))
          cast (congrArg (fun expected => m (CertifiedResult expected)) (by
            rw [execFueled_spawn hstep, hentry]; dsimp only; rw [hresume]; rfl))
            (execFueled sink msg ⟨pc, r.context, s⟩ fuel context (nextFrame + 1))
        | .ok (.error (reason, s)) =>
          sink (.resumed context nextFrame (.ok (.error (reason, s))))
          sink (.exited context (some (.ok (.halted reason s))))
          pure ⟨Fueled.ofExcept (.ok (.halted reason s)), nextFrame + 1, by
            rw [execFueled_spawn hstep, hentry]; dsimp only; rw [hresume]; rfl⟩
        | .error fault =>
          sink (.resumed context nextFrame (.error fault))
          sink (.exited context (some (.error fault)))
          pure ⟨Fueled.ofExcept (.error fault), nextFrame + 1, by
            rw [execFueled_spawn hstep, hentry]; dsimp only; rw [hresume]; rfl⟩
      | .run cr =>
        sink (.entered childContext child (.run cr))
        let childResult ← execFueled sink child.message cr fuel childContext (nextFrame + 1)
        match hchild : childResult.value.run with
        | none =>
          sink (.exited context none)
          pure ⟨Fueled.exhausted, childResult.nextFrame, by
            rw [execFueled_spawn hstep, hentry]; dsimp only
            rw [← childResult.erases, hchild]; rfl⟩
        | some x =>
          let settled := x >>= settle child
          sink (.settled childContext child settled)
          match hresume : resumed rules child p settled with
          | .ok (.ok s) =>
            sink (.resumed context nextFrame (.ok (.ok s)))
            cast (congrArg (fun expected => m (CertifiedResult expected)) (by
              rw [execFueled_spawn hstep, hentry]; dsimp only
              rw [← childResult.erases, hchild]; dsimp only [Option.map]; rw [hresume]; rfl))
              (execFueled sink msg ⟨pc, r.context, s⟩ fuel context childResult.nextFrame)
          | .ok (.error (reason, s)) =>
            sink (.resumed context nextFrame (.ok (.error (reason, s))))
            sink (.exited context (some (.ok (.halted reason s))))
            pure ⟨Fueled.ofExcept (.ok (.halted reason s)), childResult.nextFrame, by
              rw [execFueled_spawn hstep, hentry]; dsimp only
              rw [← childResult.erases, hchild]; dsimp only [Option.map]; rw [hresume]; rfl⟩
          | .error fault =>
            sink (.resumed context nextFrame (.error fault))
            sink (.exited context (some (.error fault)))
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
def exec {m : Type → Type} [Monad m] (sink : Sink m) (msg : Message)
    (r : Frame.Running) (context : Context) (nextFrame : Nat) :
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
def runFrame {m : Type → Type} [Monad m] (sink : Sink m) (f : Frame)
    (runId : String) : m (FrameResult f) := do
  let context : Context := ⟨runId, 0, 1⟩
  match hentry : enterWith f f.checkpoint with
  | .done settled =>
    sink (.entered context f (.done settled))
    sink (.settled context f settled)
    pure ⟨settled.map (fun value => ⟨none, value⟩), 1, by
      simp only [Checked.Frame.runTopWithRoot, hentry]⟩
  | .run r =>
    sink (.entered context f (.run r))
    let result ← exec sink f.message r context 1
    let settled := result.value >>= settle f
    sink (.settled context f settled)
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
def runPrepared {m : Type → Type} [Monad m] (sink : Sink m)
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
def runInput {m : Type → Type} [Monad m] (sink : Sink m)
    (reportRefund : Nat → m Unit) (input : TopLevel.Input) (runId : String) : m (InputResult input) := do
  match h : TopLevel.prepareNative input with
  | .error fault => pure ⟨.error fault, by rw [TopLevel.runNative, h]; rfl⟩
  | .ok prepared =>
    let result ← runPrepared sink reportRefund prepared.toPreparation runId
    pure ⟨result.run, by rw [result.erases, TopLevel.runNative, h]; rfl⟩

/-- The traced transaction settles through the same Checked runner as an untraced one. -/
structure TransactionResult (block : BlockContext) (state : State) (bout : BlockOutput)
    (tx : Jaune.Transaction) (index : Nat) where
  value : Except TransitionError (TransactionRun × BlockOutput)
  erases : value = Transaction.run block state bout tx index

/-- Trace an admitted signed transaction once, then settle the typed message. Ordinary calls
report the authorization refund before entry. A preparation refusal emits no frame events. -/
def runTransaction {m : Type → Type} [Monad m] (sink : Sink m)
    (authorizationRefund : Nat → m Unit) (block : BlockContext) (state : State) (bout : BlockOutput)
    (tx : Jaune.Transaction) (index : Nat) (runId : String) :
    m (TransactionResult block state bout tx index) := do
  match ha : Transaction.admit block state bout tx index with
  | .error error =>
    pure ⟨.error error, by simp only [Transaction.run, ha, bind, Except.bind]⟩
  | .ok admitted =>
    match hp : Transaction.prepare block state admitted tx with
    | .error error =>
      pure ⟨.error error, by simp only [Transaction.run, ha, hp, bind, Except.bind]⟩
    | .ok prepared =>
      let message := prepared.input.message
      let reportRefund := if message.context.block.rules.stateGas.isNone && message.target.isSome
        then authorizationRefund else fun _ => pure ()
      let result ← runInput sink reportRefund prepared.input runId
      let value := do
        let run ← result.run.mapError (fun fault => TransitionError.vm fault.toEvmError)
        Transaction.settleRun admitted prepared tx index run
      pure ⟨value, by simp only [value, result.erases, Transaction.run, ha, hp, bind, Except.bind]⟩

end Jaune.Checked.Trace
