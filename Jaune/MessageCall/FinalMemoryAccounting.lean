import Jaune.MessageCall.FinalExec
import Jaune.MessageCall.FinalMemoryCosts

/-! # Call input and return windows on the lifetime-grouped machine -/

namespace Jaune.Staging
open Jaune

private theorem push_done_ne_spawn (d : Frame.State) (c : Frame) (p : Pending) :
    MessageOp.Outcome.ofExcept (do
      let devm ← d.push 0
      return MessageOp.Outcome.done (.ok devm)) ≠ .spawn c p := by
  cases d.push 0 <;> simp [MessageOp.Outcome.ofExcept, bind, Except.bind, pure, Except.pure]

/-- A call's spawn: the child's gas is the grant, the checkpoint is the caller with its return
data cleared, and the caller waits on its output window. -/
theorem genericCall.step_spawn_call {ctx : CallContext} {parent : Frame.State} {gas : Nat}
    {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (h : genericCall.step ctx parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending) :
    child.message.gas = gas ∧
      child.checkpoint = parent.withReturnData [] ∧
      pending = ⟨.call outputIndex outputSize, false⟩ := by
  unfold genericCall.step at h
  split at h
  · exact absurd h (push_done_ne_spawn _ _ _)
  · cases h
    exact ⟨rfl, rfl, rfl⟩

/-- A call's child runs under its caller's block and transaction records. -/
theorem genericCall.step_spawn_context {ctx : CallContext} {parent : Frame.State} {gas : Nat}
    {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (h : genericCall.step ctx parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending) :
    child.message.context.block = ctx.block ∧ child.message.context.tx = ctx.tx := by
  unfold genericCall.step at h
  split at h
  · exact absurd h (push_done_ne_spawn _ _ _)
  · cases h
    exact ⟨rfl, rfl⟩

/-- A call's child receives the requested input window of its caller's memory. -/
theorem genericCall.step_spawn_data {ctx : CallContext} {parent : Frame.State} {gas : Nat}
    {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (h : genericCall.step ctx parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending) :
    child.message.context.calldata =
      Jaune.Array.sliceD (parent.withReturnData []).memory.data inputIndex inputSize 0 := by
  unfold genericCall.step at h
  split at h
  · exact absurd h (push_done_ne_spawn _ _ _)
  · cases h
    rfl

/-- The spawned call's input has the requested length, even when reading beyond the caller's
materialized memory. -/
theorem genericCall.step_spawn_data_length {ctx : CallContext} {parent : Frame.State} {gas : Nat}
    {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (h : genericCall.step ctx parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending) :
    child.message.context.calldata.length = inputSize := by
  rw [genericCall.step_spawn_data h]
  exact memory_slice_length _ _ _ _

private theorem resume_shape {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (h : resume rules p saved r = .ok x) :
    ∃ s : Frame.State, s.machine = absorbMeters rules p saved.machine r ∧
      (x = .ok { s with machine := p.target.finish r s.machine } ∨
        x = .error (.stackOverflow .none, s)) := by
  unfold resume at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨⟨_, _, _, _⟩, rfl, Or.inl rfl⟩)
    | (cases h; exact ⟨⟨_, _, _, _⟩, rfl, Or.inr rfl⟩)
    | cases h

private theorem absorbMeters_memory (rules : ForkRules) (p : Pending) (m : Machine)
    (r : Frame.Result) : (absorbMeters rules p m r).memory = m.memory := by
  unfold absorbMeters Machine.creditStateGasRefund Machine.repayStateGasSpill
  repeat' split
  all_goals rfl

private theorem absorbMeters_returnData (rules : ForkRules) (p : Pending) (m : Machine)
    (r : Frame.Result) :
    (absorbMeters rules p m r).returnData = match p.target, r.failed with
      | .create _, false => []
      | _, _ => r.output := by
  unfold absorbMeters Machine.creditStateGasRefund Machine.repayStateGasSpill
  rcases ht : p.target with ⟨outputIndex, outputSize⟩ | address <;>
    cases hf : r.failed <;> simp only [hf] <;> split <;> (try split) <;> (try split) <;> rfl

private theorem finish_returnData (target : ReturnTarget) (r : Frame.Result) (m : Machine) :
    (target.finish r m).returnData = m.returnData := by
  cases target <;> rfl

private theorem finish_memory (target : ReturnTarget) (r : Frame.Result) (m : Machine) :
    (target.finish r m).memory = match target with
      | .call outputIndex outputSize => m.memory.write outputIndex (r.output.take outputSize)
      | .create _ => m.memory := by
  cases target <;> rfl


/-- Resuming a call on a non-full stack copies at most the requested window. -/
theorem resume_call_ok_memory {rules : ForkRules} {p : Pending} {saved resumed : Frame.State}
    {r : Frame.Result} {outputIndex outputSize : Nat}
    (htarget : p.target = .call outputIndex outputSize)
    (h : resume rules p saved r = .ok (.ok resumed)) :
    resumed.memory = saved.machine.memory.write outputIndex (r.output.take outputSize) := by
  obtain ⟨s, hs, he | he⟩ := resume_shape h
  · cases he
    change (p.target.finish r s.machine).memory = _
    rw [finish_memory, htarget, hs, absorbMeters_memory]
  · cases he

/-- The caller receives the child's output, except after a successful creation. -/
theorem resume_returnData {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (h : resume rules p saved r = .ok x) :
    (match x with | .ok s => s.returnData | .error (_, s) => s.returnData) =
      match p.target, r.failed with | .create _, false => [] | _, _ => r.output := by
  obtain ⟨s, hs, he | he⟩ := resume_shape h <;> subst x
  · change (p.target.finish r s.machine).returnData = _
    rw [finish_returnData, hs, absorbMeters_returnData]
  · change s.machine.returnData = _
    rw [hs, absorbMeters_returnData]

/-- A full caller stack halts with the same memory and the child's return data installed. -/
theorem resume_stackOverflow_memory {rules : ForkRules} {p : Pending} {saved resumed : Frame.State}
    {r : Frame.Result} {reason : ExceptionalHalt}
    (h : resume rules p saved r = .ok (.error (reason, resumed))) :
    reason = .stackOverflow .none ∧ resumed.memory = saved.memory ∧
    resumed.returnData = match p.target, r.failed with
      | .create _, false => []
      | _, _ => r.output := by
  obtain ⟨s, hs, he | he⟩ := resume_shape h
  · cases he
  · cases he
    change _ ∧ resumed.machine.memory = _ ∧ resumed.machine.returnData = _
    rw [hs, absorbMeters_memory, absorbMeters_returnData]
    exact ⟨rfl, rfl, rfl⟩

theorem enter_transfer_error {f : Frame} {fault : Fault}
    (h : f.message.transfer f.enteredWorld = .error fault) :
    enter f = .done (.error fault) := by
  simp only [enter, enterWith, h]

theorem enter_precompile {f : Frame} {world : World} {adr : Address}
    (htransfer : f.message.transfer f.enteredWorld = .ok world)
    (hcode : f.message.codeAddress = some adr)
    (hdispatch : (!f.message.disablePrecompiles &&
      f.message.context.block.rules.isPrecompile adr) = true) :
    enter f = .done (runPrecompile (Frame.entered f f.startState world) adr >>= settle f) := by
  simp only [enter, enterWith, htransfer, hcode, hdispatch, ite_true]


/-- A successful precompile reply at entry obeys the native bound, including identity and modexp. -/
theorem enter_native_ok_output_length_lt_two_pow_160 {f : Frame} {world : World} {adr : Address}
    {exit : Frame.Exit} (h : runPrecompile (Frame.entered f f.startState world) adr = .ok exit)
    (hdata : f.message.context.calldata.length < 2 ^ 160)
    (hgas : f.message.gas < 2 ^ 256 + Gas.callStipend) : exit.output.length < 2 ^ 160 := by
  unfold runPrecompile at h
  cases hp : precompileRun (Frame.entered f f.startState world).precompileEvm adr with
  | ok cost output =>
    rw [hp] at h; cases h
    exact precompileRun_ok_output_length_lt_two_pow_160 hp hdata hgas
  | error reason cost =>
    rw [hp] at h
    cases reason <;> cases h <;> exact (by decide : 0 < 2 ^ 160)

/-- A rejected precompile that returns an exit has no output. -/
theorem enter_native_error_output_nil {f : Frame} {world : World} {adr : Address} {cost : Nat}
    {reason : EvmError} {e : Frame.Exit}
    (hp : precompileRun (Frame.entered f f.startState world).precompileEvm adr = .error reason cost)
    (h : runPrecompile (Frame.entered f f.startState world) adr = .ok e) : e.output = [] := by
  unfold runPrecompile at h
  rw [hp] at h
  cases reason <;> cases h <;> rfl

/-- Settlement keeps the output length or clears the output on a failed creation deposit. -/
theorem settle_output_length_le {f : Frame} {e : Frame.Exit} {r : Frame.Result}
    (h : settle f e = .ok r) : r.output.length ≤ e.output.length := by
  cases e with
  | halted reason s => cases h; exact Nat.le_refl _
  | reverted output s => cases h; exact Nat.le_refl _
  | finished output s =>
    simp only [settle] at h
    split at h
    · cases h; exact Nat.le_refl _
    · split at h
      · cases h; exact Nat.le_refl _
      · cases h; exact Nat.zero_le _

end Jaune.Staging
