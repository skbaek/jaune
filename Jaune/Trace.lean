import Jaune.Sufficiency

/-!
Streaming observations over the existing fueled interpreter. This module is
outside `Jaune.lean`'s import closure. It deliberately calls the existing step,
entry, settlement, and resume operations instead of modifying their semantics.

A sink may fail (for example, `IO` writing to a closed stream). Every successful
return carries a kernel-checked execution projection; this says nothing about
sink success, trace serialization, or gas-observation conventions.
-/
namespace Jaune.Trace

/-- Explicit run identity plus a unique frame number and observed call depth.
The depth here counts entered frames, unlike Sevm.depth's remaining allowance. -/
structure Context where
  runId : String
  frame : Nat
  depth : Nat
  deriving Repr

/-- Events are delivered synchronously. The driver retains no event history.
`instruction` supplies the pre-state and the actual step result; serializers
must interpret gas at spawn separately for CALL and CREATE. `entered` covers
both code and zero-instruction/precompile/preparation-failure boundaries. -/
inductive Event where
  | instruction (context : Context) (before : Evm) (step : Step)
  | entered (context : Context) (frame : Frame) (entry : FrameEntry)
  | exited (context : Context) (raw : Option Execution)
  | settled (context : Context) (frame : Frame)
      (result : Except (EvmError × State × AdrSet × Tra) Devm)
  | resumed (parent : Context) (childFrame : Nat) (raw : Execution)

abbrev Sink (m : Type → Type) := Event → m Unit

/-- Proof fields are erased at runtime. `nextFrame` is the next unused number,
threaded across child execution and subsequent parent execution. -/
structure Result (evm : Evm) (fuel : Nat) where
  value : Fueled (EvmError × Devm) Devm
  nextFrame : Nat
  erases : value = Jaune.execFueled evm fuel

/-- A production driver with an arbitrary monadic streaming sink. Fuel zero
emits no instruction. Child events precede the parent's next instruction.
The recursive computation never reruns the original executor to certify its
answer: each branch constructs its erasure proof from the child certificate. -/
def execFueled {m : Type → Type} [Monad m] (sink : Sink m) :
    (evm : Evm) → (fuel : Nat) → Context → Nat → m (Result evm fuel)
  | evm, 0, context, nextFrame => do
    sink (.exited context none)
    pure ⟨Fueled.exhausted, nextFrame, by simp only [Jaune.execFueled]⟩
  | evm, fuel + 1, context, nextFrame => do
    match hstep : evm.step with
    | .halt raw =>
      sink (.instruction context evm (.halt raw))
      sink (.exited context (some raw))
      pure ⟨Fueled.ofExcept raw, nextFrame, by simp only [Jaune.execFueled, hstep]⟩
    | .cont pc devm =>
      sink (.instruction context evm (.cont pc devm))
      let result ← execFueled sink ⟨pc, evm.sta, devm⟩ fuel context nextFrame
      pure ⟨result.value, result.nextFrame, by
        simpa only [Jaune.execFueled, hstep] using result.erases⟩
    | .spawn frame rsm pc =>
      sink (.instruction context evm (.spawn frame rsm pc))
      let childContext := { context with frame := nextFrame, depth := context.depth + 1 }
      match hentry : frame.enter with
      | .done settled =>
        sink (.entered childContext frame (.done settled))
        sink (.settled childContext frame settled)
        match hresume : rsm.run settled with
        | .error error =>
          sink (.resumed context nextFrame (.error error))
          sink (.exited context (some (.error error)))
          pure ⟨Fueled.ofExcept (.error error), nextFrame + 1, by
            simp only [Jaune.execFueled, hstep, hentry, hresume]⟩
        | .ok devm =>
          sink (.resumed context nextFrame (.ok devm))
          let result ← execFueled sink ⟨pc, evm.sta, devm⟩ fuel context (nextFrame + 1)
          pure ⟨result.value, result.nextFrame, by
            simpa only [Jaune.execFueled, hstep, hentry, hresume] using result.erases⟩
      | .run child =>
        sink (.entered childContext frame (.run child))
        let childResult ← execFueled sink child fuel childContext (nextFrame + 1)
        match hchild : childResult.value.run with
        | none =>
          sink (.exited context none)
          pure ⟨Fueled.exhausted, childResult.nextFrame, by
            simp only [Jaune.execFueled, hstep, hentry, ← childResult.erases, hchild]⟩
        | some raw =>
          let settled := frame.settle raw
          sink (.settled childContext frame settled)
          match hresume : rsm.run settled with
          | .error error =>
            sink (.resumed context nextFrame (.error error))
            sink (.exited context (some (.error error)))
            pure ⟨Fueled.ofExcept (.error error), childResult.nextFrame, by
              dsimp only [settled] at hresume
              simp only [Jaune.execFueled, hstep, hentry, ← childResult.erases,
                hchild, hresume]⟩
          | .ok devm =>
            sink (.resumed context nextFrame (.ok devm))
            let result ← execFueled sink ⟨pc, evm.sta, devm⟩ fuel context childResult.nextFrame
            pure ⟨result.value, result.nextFrame, by
              dsimp only [settled] at hresume
              simpa only [Jaune.execFueled, hstep, hentry, ← childResult.erases,
                hchild, hresume] using result.erases⟩
  termination_by _ fuel _ _ => fuel

/-- The exact execution projection of every successfully returned production
result, independent of the sink's effects. -/
theorem execFueled_erasure {evm : Evm} {fuel : Nat} (result : Result evm fuel) :
    result.value = Jaune.execFueled evm fuel := result.erases

/-- Successful total executions agree with the public executor. -/
structure ExecutionResult (evm : Evm) where
  value : Execution
  nextFrame : Nat
  erases : value = Jaune.exec evm

/-- Seed exactly the same sufficient fuel as the public executor. -/
def exec {m : Type → Type} [Monad m] (sink : Sink m) (evm : Evm)
    (context : Context) (nextFrame : Nat) : m (ExecutionResult evm) := do
  let result ← execFueled sink evm (sufficientFuel evm.dyna.gasMeasure) context nextFrame
  match hrun : result.value.run with
  | some raw =>
    pure ⟨raw, result.nextFrame, by
      have h := execFueled_run_sufficientFuel evm
      rw [← result.erases, hrun] at h
      exact Option.some.inj h⟩
  | none =>
    have h : (none : Option Execution) = some (Jaune.exec evm) := by
      have h := execFueled_run_sufficientFuel evm
      rw [← result.erases, hrun] at h
      exact h
    nomatch h

/-- The total driver returns exactly the public executor's result. -/
theorem exec_erasure {evm : Evm} (result : ExecutionResult evm) :
    result.value = Jaune.exec evm := result.erases

structure FrameResult (frame : Frame) where
  value : Except (EvmError × State × AdrSet × Tra) Devm
  nextFrame : Nat
  erases : value = Jaune.runFrame frame

/-- The frame boundary used by processMessage/processCreateMessage. A root
precompile or preparation failure has no instruction events, but still has
entry and settlement events. One invocation represents one identified run. -/
def runFrame {m : Type → Type} [Monad m] (sink : Sink m) (frame : Frame)
    (runId : String) : m (FrameResult frame) := do
  let context : Context := ⟨runId, 0, 1⟩
  match hentry : frame.enter with
  | .done settled =>
    sink (.entered context frame (.done settled))
    sink (.settled context frame settled)
    pure ⟨settled, 1, by simp only [Jaune.runFrame, hentry]⟩
  | .run evm =>
    sink (.entered context frame (.run evm))
    let result ← exec sink evm context 1
    let settled := frame.settle result.value
    sink (.settled context frame settled)
    pure ⟨settled, result.nextFrame, by
      simp only [Jaune.runFrame, hentry, settled, result.erases]⟩

/-- Exact connection to the public runner's frame operation. -/
theorem runFrame_erasure {frame : Frame} (result : FrameResult frame) :
    result.value = Jaune.runFrame frame := result.erases

/-- CALL message entry uses the same settled result as the public operation. -/
theorem processMessage_erasure {msg : Msg} (result : FrameResult (Frame.ofCall msg)) :
    result.value = Jaune.processMessage msg := result.erases

/-- CREATE message entry uses the same settled result as the public operation. -/
theorem processCreateMessage_erasure {msg : Msg}
    (result : FrameResult (Frame.ofCreate msg)) :
    result.value = Jaune.processCreateMessage msg := result.erases

/-- Direct equation on the actual production driver, instantiated with any
pure sink. Effects retained by a pure state sink are not part of the execution
projection. -/
theorem execFueled_id_erasure (sink : Sink Id) (evm : Evm) (fuel : Nat)
    (context : Context) (nextFrame : Nat) :
    (execFueled sink evm fuel context nextFrame).value = Jaune.execFueled evm fuel :=
  (execFueled sink evm fuel context nextFrame).erases

theorem exec_id_erasure (sink : Sink Id) (evm : Evm)
    (context : Context) (nextFrame : Nat) :
    (exec sink evm context nextFrame).value = Jaune.exec evm :=
  (exec sink evm context nextFrame).erases

theorem runFrame_id_erasure (sink : Sink Id) (frame : Frame) (runId : String) :
    (runFrame sink frame runId).value = Jaune.runFrame frame :=
  (runFrame sink frame runId).erases

end Jaune.Trace
