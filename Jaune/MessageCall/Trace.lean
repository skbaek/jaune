import Jaune.MessageCall.Top

/-!
# The four-part message call: the trace driver (goal `jaune-shape-and-names-v1`, W1 unit K1)

Today's streaming driver (`Jaune.Trace`) over the staged `Step`, `Frame`, `Frame.Entry` and
settled `Frame.Result`. Staged under a namespace of its own until the switch commit, which gave it its final names; the switch
(units I and K2) moved the tracer onto it. Like today's, this module sits outside `Jaune.lean`'s import closure.

The driver delivers the same events in the same order as today's, with the staged payloads. A
caller's raw result after its child (`resumedRaw`) is the staged driver's own tail: a settlement
fault, a resumption fault, a halt or the resumed machine. Each successful return carries a
kernel-checked projection onto the staged driver, `execFueled`, as today's does onto
today's.

The run identity `Context` and the certificate `CertifiedResult` mention no message-call type;
the switch moved them here from today's tracer, which now reads them from this module.
-/

namespace Jaune

namespace Trace

/-- Explicit run identity plus a unique frame number and observed call depth.
The depth here counts entered frames, unlike Sevm.depth's remaining allowance. -/
structure Context where
  runId : String
  frame : Nat
  depth : Nat
  deriving Repr

/-- Proof fields are erased at runtime. `nextFrame` is the next unused number,
threaded across child execution and subsequent parent execution. -/
structure CertifiedResult (expected : Fueled (EvmError × Devm) Devm) where
  value : Fueled (EvmError × Devm) Devm
  nextFrame : Nat
  erases : value = expected

/-- Today's events with the staged payloads. `instruction` carries the pre-state and the staged
step; `entered` the staged frame and entry; `settled` the staged settled result. -/
inductive Event where
  | instruction (context : Context) (before : Evm) (step : Step)
  | entered (context : Context) (frame : Frame) (entry : Frame.Entry)
  | exited (context : Context) (raw : Option Execution)
  | settled (context : Context) (frame : Frame) (result : Except Fault Frame.Result)
  | resumed (parent : Context) (childFrame : Nat) (raw : Execution)

abbrev Sink (m : Type → Type) := Event → m Unit

/-- Index by the staged driver's result, so that proof transport erases to runtime identity. -/
abbrev Result (evm : Evm) (fuel : Nat) := CertifiedResult (Jaune.execFueled evm fuel)

/-- The caller's raw result once its child has settled: the staged driver's tail. A fault, in
settlement or in resumption, carries the child's checkpoint as its (unread) state. -/
def resumedRaw (rules : ForkRules) (child : Frame) (pending : Pending) :
    Except Fault Frame.Result → Execution
  | .error fault => .error (fault.toEvmError, child.checkpoint.toDevm)
  | .ok result =>
    match resume rules pending child.checkpoint result with
    | .error fault => .error (fault.toEvmError, child.checkpoint.toDevm)
    | .ok (.error (reason, devm)) => .error (.halt reason, devm)
    | .ok (.ok devm) => .ok devm

/-- The staged driver's spawn tail, read through `resumedRaw`. -/
theorem execFueled_tail (rules : ForkRules) (child : Frame) (pending : Pending) (pc : Nat)
    (sta : Sevm) (fuel : Nat) (settled : Except Fault Frame.Result) :
    (match (generalizing := false) some settled with
      | none => Fueled.exhausted
      | some (.error fault) => Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
      | some (.ok result) =>
        match (generalizing := false) resume rules pending child.checkpoint result with
        | .error fault => Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
        | .ok (.error (reason, devm)) => Fueled.ofExcept (.error (.halt reason, devm))
        | .ok (.ok devm) => Jaune.execFueled ⟨pc, sta, devm⟩ fuel :
        Fueled (EvmError × Devm) Devm)
      = match resumedRaw rules child pending settled with
        | .error error => Fueled.ofExcept (.error error)
        | .ok devm => Jaune.execFueled ⟨pc, sta, devm⟩ fuel := by
  rcases settled with fault | result
  · rfl
  · simp only [resumedRaw]
    rcases resume rules pending child.checkpoint result with fault | ⟨reason, devm⟩ | devm <;> rfl

/-- The staged driver at a spawn, read through `resumedRaw`. -/
theorem execFueled_spawn {evm : Evm} {fuel : Nat} {child : Frame} {pending : Pending} {pc : Nat}
    (hstep : Evm.step evm = .spawn child pending pc) :
    Jaune.execFueled evm (fuel + 1)
      = match (match enter child with
          | .done result => some result
          | .run childEvm => ((Jaune.execFueled childEvm fuel).run).map (settle child)) with
        | none => Fueled.exhausted
        | some settled =>
          match resumedRaw evm.sta.benvStat.rules child pending settled with
          | .error error => Fueled.ofExcept (.error error)
          | .ok devm => Jaune.execFueled ⟨pc, evm.sta, devm⟩ fuel := by
  rw [Jaune.execFueled, hstep]
  dsimp only
  cases enter child with
  | done r => exact execFueled_tail _ child pending pc evm.sta fuel r
  | run childEvm =>
    dsimp only
    cases (Jaune.execFueled childEvm fuel).run with
    | none => rfl
    | some raw => exact execFueled_tail _ child pending pc evm.sta fuel _

/-- The staged production driver with an arbitrary monadic streaming sink: today's
`Trace.execFueled` over the staged step, entry, settlement and resumption. Fuel zero emits no
instruction; child events precede the parent's next instruction. Each branch builds its erasure
proof from the child certificate, and parent continuations `cast` the whole monadic result. -/
def execFueled {m : Type → Type} [Monad m] (sink : Sink m) :
    (evm : Evm) → (fuel : Nat) → Context → Nat → m (Result evm fuel)
  | evm, 0, context, nextFrame => do
    sink (.exited context none)
    pure ⟨Fueled.exhausted, nextFrame, by simp only [Jaune.execFueled]⟩
  | evm, fuel + 1, context, nextFrame => do
    match hstep : Evm.step evm with
    | .halt raw =>
      sink (.instruction context evm (.halt raw))
      sink (.exited context (some raw))
      pure ⟨Fueled.ofExcept raw, nextFrame, by simp only [Jaune.execFueled, hstep]⟩
    | .next pc devm =>
      sink (.instruction context evm (.next pc devm))
      cast (congrArg (fun expected => m (CertifiedResult expected)) (by
        simp only [Jaune.execFueled, hstep]))
        (execFueled sink ⟨pc, evm.sta, devm⟩ fuel context nextFrame)
    | .spawn child pending pc =>
      sink (.instruction context evm (.spawn child pending pc))
      let childContext := { context with frame := nextFrame, depth := context.depth + 1 }
      match hentry : enter child with
      | .done settled =>
        sink (.entered childContext child (.done settled))
        sink (.settled childContext child settled)
        match hresume : resumedRaw evm.sta.benvStat.rules child pending settled with
        | .error error =>
          sink (.resumed context nextFrame (.error error))
          sink (.exited context (some (.error error)))
          pure ⟨Fueled.ofExcept (.error error), nextFrame + 1, by
            rw [execFueled_spawn hstep, hentry]; dsimp only; rw [hresume]⟩
        | .ok devm =>
          sink (.resumed context nextFrame (.ok devm))
          cast (congrArg (fun expected => m (CertifiedResult expected)) (by
            rw [execFueled_spawn hstep, hentry]; dsimp only; rw [hresume]))
            (execFueled sink ⟨pc, evm.sta, devm⟩ fuel context (nextFrame + 1))
      | .run childEvm =>
        sink (.entered childContext child (.run childEvm))
        let childResult ← execFueled sink childEvm fuel childContext (nextFrame + 1)
        match hchild : childResult.value.run with
        | none =>
          sink (.exited context none)
          pure ⟨Fueled.exhausted, childResult.nextFrame, by
            rw [execFueled_spawn hstep, hentry]; dsimp only
            rw [← childResult.erases, hchild]; rfl⟩
        | some raw =>
          let settled := settle child raw
          sink (.settled childContext child settled)
          match hresume : resumedRaw evm.sta.benvStat.rules child pending settled with
          | .error error =>
            sink (.resumed context nextFrame (.error error))
            sink (.exited context (some (.error error)))
            pure ⟨Fueled.ofExcept (.error error), childResult.nextFrame, by
              rw [execFueled_spawn hstep, hentry]; dsimp only
              rw [← childResult.erases, hchild, Option.map_some]; dsimp only
              exact (congrArg (fun r : Execution => (match r with
                | .error error => Fueled.ofExcept (.error error)
                | .ok devm => Jaune.execFueled ⟨pc, evm.sta, devm⟩ fuel :
                  Fueled (EvmError × Devm) Devm)) hresume).symm⟩
          | .ok devm =>
            sink (.resumed context nextFrame (.ok devm))
            cast (congrArg (fun expected => m (CertifiedResult expected)) (by
              rw [execFueled_spawn hstep, hentry]; dsimp only
              rw [← childResult.erases, hchild, Option.map_some]; dsimp only
              exact (congrArg (fun r : Execution => (match r with
                | .error error => Fueled.ofExcept (.error error)
                | .ok devm => Jaune.execFueled ⟨pc, evm.sta, devm⟩ fuel :
                  Fueled (EvmError × Devm) Devm)) hresume).symm))
              (execFueled sink ⟨pc, evm.sta, devm⟩ fuel context childResult.nextFrame)
  termination_by _ fuel _ _ => fuel

/-- The exact execution projection of every successfully returned staged result. -/
theorem execFueled_erasure {evm : Evm} {fuel : Nat} (result : Result evm fuel) :
    result.value = Jaune.execFueled evm fuel := result.erases

/-- Successful total executions agree with the staged total interpreter. -/
structure ExecutionResult (evm : Evm) where
  value : Execution
  nextFrame : Nat
  erases : value = Jaune.exec evm

/-- Seed exactly the same sufficient fuel as the staged total interpreter. Exhaustion gives the
interpreter's own internal invariant error, with no further event. -/
def exec {m : Type → Type} [Monad m] (sink : Sink m) (evm : Evm)
    (context : Context) (nextFrame : Nat) : m (ExecutionResult evm) := do
  let result ← execFueled sink evm (sufficientFuel evm.dyna.gasMeasure) context nextFrame
  match hrun : result.value.run with
  | some raw =>
    pure ⟨raw, result.nextFrame, by
      simp only [Jaune.exec, ← result.erases, hrun]⟩
  | none =>
    pure ⟨.error ⟨.internal (.invariant .none), evm.dyna⟩, result.nextFrame, by
      simp only [Jaune.exec, ← result.erases, hrun]⟩

/-- The total driver returns exactly the staged total interpreter's result. -/
theorem exec_erasure {evm : Evm} (result : ExecutionResult evm) :
    result.value = Jaune.exec evm := result.erases

structure FrameResult (frame : Frame) where
  value : Except Fault Frame.Result
  nextFrame : Nat
  erases : value = Frame.runTop frame

/-- The top-level frame boundary. A root precompile or failed transfer has no instruction
events, but still has entry and settlement events. One invocation represents one identified
run. -/
def runFrame {m : Type → Type} [Monad m] (sink : Sink m) (frame : Frame)
    (runId : String) : m (FrameResult frame) := do
  let context : Context := ⟨runId, 0, 1⟩
  match hentry : enterWith frame frame.checkpoint.toDevm with
  | .done settled =>
    sink (.entered context frame (.done settled))
    sink (.settled context frame settled)
    pure ⟨settled, 1, by simp only [Frame.runTop, hentry]⟩
  | .run evm =>
    sink (.entered context frame (.run evm))
    let result ← exec sink evm context 1
    let settled := settle frame result.value
    sink (.settled context frame settled)
    pure ⟨settled, result.nextFrame, by
      simp only [Frame.runTop, hentry, settled, result.erases]⟩

/-- Exact connection to the top-level frame's settled result. -/
theorem runFrame_erasure {frame : Frame} (result : FrameResult frame) :
    result.value = Frame.runTop frame := result.erases

end Trace

end Jaune

