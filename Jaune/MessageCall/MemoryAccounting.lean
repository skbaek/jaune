import Jaune.MessageCall.Totality
import Jaune.MessageCall.MessageMemory
import Jaune.PrecompileInputFacts

/-! # Memory and output accounting for message calls

The paid expansion covers the input and output windows of a call, even on a full caller
stack. The driver induction charges the caller for child gas and keeps each completed frame
within its initial gas and memory budget. Child code and precompiles both obey the resulting
return-data width bound.
-/

namespace Jaune

/-- A copy into a prepaid window does not expand memory. Empty copies need
no restriction on their index. (`Mem.write_size_of_prepaid` restated over `Memory`.) -/
theorem Memory.write_size_of_prepaid (mem : Memory) (index : Nat) (bytes : Bytes)
    (h : bytes ≠ [] → index + bytes.length ≤ mem.size) :
    (mem.write index bytes).size = mem.size := by
  cases bytes with
  | nil => rfl
  | cons b bs =>
    have hb : b :: bs ≠ [] := by intro heq; contradiction
    simp only [Memory.write, h hb, ↓reduceDIte]
    split <;> rfl

private theorem push_done_ne_spawn (d : Frame.State) (c : Frame) (p : Pending) :
    MessageOp.Outcome.ofExcept (do
      let devm ← d.push 0
      return MessageOp.Outcome.done (.ok devm)) ≠ .spawn c p := by
  cases d.push 0 <;> simp [MessageOp.Outcome.ofExcept, bind, Except.bind, pure, Except.pure]

/-- A call's spawn: the child's gas is the grant, the checkpoint is the caller with its return
data cleared, and the caller waits on its output window. -/
theorem prepareCall.step_spawn_call {ctx : CallContext} {parent : Frame.State} {gas : Nat}
    {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (h : prepareCall.step ctx parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending) :
    child.message.gas = gas ∧
      child.checkpoint = parent.withReturnData [] ∧
      pending = ⟨.call outputIndex outputSize, false⟩ := by
  unfold prepareCall.step at h
  split at h
  · exact absurd h (push_done_ne_spawn _ _ _)
  · cases h
    exact ⟨rfl, rfl, rfl⟩

/-- A call's child runs under its caller's block and transaction records. -/
theorem prepareCall.step_spawn_context {ctx : CallContext} {parent : Frame.State} {gas : Nat}
    {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (h : prepareCall.step ctx parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending) :
    child.message.context.block = ctx.block ∧ child.message.context.tx = ctx.tx := by
  unfold prepareCall.step at h
  split at h
  · exact absurd h (push_done_ne_spawn _ _ _)
  · cases h
    exact ⟨rfl, rfl⟩

/-- A call's child receives the requested input window of its caller's memory. -/
theorem prepareCall.step_spawn_data {ctx : CallContext} {parent : Frame.State} {gas : Nat}
    {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (h : prepareCall.step ctx parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending) :
    child.message.context.calldata =
      Jaune.Array.sliceD (parent.withReturnData []).memory.data inputIndex inputSize 0 := by
  unfold prepareCall.step at h
  split at h
  · exact absurd h (push_done_ne_spawn _ _ _)
  · cases h
    rfl

/-- The spawned call's input has the requested length, even when reading beyond the caller's
materialized memory. -/
theorem prepareCall.step_spawn_data_length {ctx : CallContext} {parent : Frame.State} {gas : Nat}
    {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (h : prepareCall.step ctx parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending) :
    child.message.context.calldata.length = inputSize := by
  rw [prepareCall.step_spawn_data h]
  exact memory_slice_length _ _ _ _

private theorem resume_shape {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (h : resume rules p saved r = .ok x) :
    ∃ s : Frame.State, s.machine = absorbMeters rules p saved.machine r ∧
      (x = .ok { s with machine := finishTarget p.target r s.machine } ∨
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
    cases hf : r.failed <;> simp only [] <;> split <;> (try split) <;> (try split) <;> rfl

private theorem finish_returnData (target : ReturnTarget) (r : Frame.Result) (m : Machine) :
    (finishTarget target r m).returnData = m.returnData := by
  cases target <;> rfl

private theorem finish_memory (target : ReturnTarget) (r : Frame.Result) (m : Machine) :
    (finishTarget target r m).memory = match target with
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
    change (finishTarget p.target r s.machine).memory = _
    rw [finish_memory, htarget, hs, absorbMeters_memory]
  · cases he

/-- The caller receives the child's output, except after a successful creation. -/
theorem resume_returnData {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (h : resume rules p saved r = .ok x) :
    (match x with | .ok s => s.returnData | .error (_, s) => s.returnData) =
      match p.target, r.failed with | .create _, false => [] | _, _ => r.output := by
  obtain ⟨s, hs, he | he⟩ := resume_shape h <;> subst x
  · change (finishTarget p.target r s.machine).returnData = _
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

/-- A precompile exit at entry obeys the native output bound, including identity and modexp. -/
theorem enter_native_ok_output_length_lt_two_pow_160 {f : Frame} {world : World} {adr : Address}
    {exit : Frame.Exit} (h : runPrecompile (Frame.entered f f.startState world) adr = .ok exit)
    (hdata : f.message.context.calldata.length < 2 ^ 160)
    (hgas : f.message.gas < 2 ^ 256 + Gas.callStipend) : exit.output.length < 2 ^ 160 := by
  unfold runPrecompile at h
  cases hp : Precompile.run (Frame.entered f f.startState world).precompileInput adr with
  | ok cost output =>
    rw [hp] at h; cases h
    exact Precompile.run_ok_output_length_lt_two_pow_160 hp hdata hgas
  | error reason cost =>
    rw [hp] at h
    cases reason <;> cases h <;> exact (by decide : 0 < 2 ^ 160)

/-- A rejected precompile that returns an exit has no output. -/
theorem enter_native_error_output_nil {f : Frame} {world : World} {adr : Address} {cost : Nat}
    {reason : EvmError} {e : Frame.Exit}
    (hp : Precompile.run (Frame.entered f f.startState world).precompileInput adr = .error reason cost)
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

/-- The full return data is independent of the caller's prepaid output window. Its copy
never changes the recorded size of the caller's memory. -/
theorem resume_memory_size {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (h : resume rules p saved r = .ok x) (hw : ReturnTarget.MemoryPaid p.target saved.memory.size) :
    (match x with | .error (_, t) | .ok t => t.memory.size) = saved.memory.size := by
  obtain ⟨t, ht, he | he⟩ := resume_shape h <;> subst x
  · change (finishTarget p.target r t.machine).memory.size = _
    rw [finish_memory]
    rcases htarg : p.target with ⟨i, n⟩ | a
    · dsimp only
      rw [ht, absorbMeters_memory]
      apply Memory.write_size_of_prepaid
      intro hbytes
      rw [htarg] at hw
      have hn : n ≠ 0 := by
        rintro rfl
        exact hbytes rfl
      exact (Nat.add_le_add_left (List.length_take_le _ _) i).trans (hw hn)
    · rw [ht, absorbMeters_memory]
  · change t.machine.memory.size = _
    rw [ht, absorbMeters_memory]

/-- Without state gas, resuming in a prepaid window returns exactly the child's unspent gas
to the caller's memory and gas budget, including a halt on a full caller stack. -/
theorem resume_prepaid_memoryPotential {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (hn : rules.stateGas = none) (h : resume rules p saved r = .ok x)
    (hw : ReturnTarget.MemoryPaid p.target saved.memory.size) :
    (match x with | .error (_, t) | .ok t => Machine.memoryPotential t.machine) =
      Machine.memoryPotential saved.machine + r.gasLeft := by
  have hsize := resume_memory_size h hw
  obtain ⟨t, ht, he | he⟩ := resume_shape h <;> subst x
  · change (finishTarget p.target r t.machine).memory.size = _ at hsize
    change (finishTarget p.target r t.machine).gasMeasure + calculateMemoryGasCost (finishTarget p.target r t.machine).memory.size = _
    rw [hsize]
    have hgas : (finishTarget p.target r t.machine).gasMeasure = t.machine.gasMeasure := by cases p.target <;> rfl
    rw [hgas, ht]
    simp only [absorbMeters, hn, Machine.gasMeasure, Machine.memoryPotential, Frame.State.memory]
    omega
  · change t.machine.memory.size = _ at hsize
    change t.machine.gasMeasure + calculateMemoryGasCost t.machine.memory.size = _
    rw [hsize, ht]
    simp only [absorbMeters, hn, Machine.gasMeasure, Machine.memoryPotential, Frame.State.memory]
    omega

private theorem output_length_with_stipend {n grant : Nat} (hcost : calculateMemoryGasCost n ≤ grant)
    (hgrant : grant < 2 ^ 256 + Gas.callStipend) : n < 2 ^ 160 := by
  by_contra hn
  have hm := calculateMemoryGasCost_mono (Nat.le_of_not_gt hn)
  have hlarge : 2 ^ 256 + Gas.callStipend ≤ calculateMemoryGasCost (2 ^ 160) := by decide
  omega

/-- A charged call's input size fits in 160 bits when its caller's initial potential fits in a word. -/
theorem charged_call_input_length_lt_two_pow_160 {before charged : Frame.State}
    (base ii il oi ol : Nat) (hc : before.chargeGas (base + before.memoryExpansionCost [(ii, il), (oi, ol)]) = .ok charged)
    (hpotential : Machine.memoryPotential before.machine < 2 ^ 256) : il < 2 ^ 160 := by
  have hw := Frame.State.chargeGas_extend_memoryPotential [(ii, il), (oi, ol)] base (Nat.le_refl (Machine.memoryPotential before.machine))
  rw [hc] at hw
  have hsize : il ≤ (charged.extendMemoryForAccesses [(ii, il), (oi, ol)]).memory.size := by
    by_cases hz : il = 0
    · rw [hz]; exact Nat.zero_le _
    · have ha := memorySizeAfterAccess_access_le charged.memory.size ii il hz
      exact (Nat.le_add_left il ii).trans (ha.trans (memorySizeAfterAccess_ge _ oi ol))
  have hcost := calculateMemoryGasCost_mono hsize
  apply output_length_with_stipend (grant := Machine.memoryPotential before.machine)
  · exact (hcost.trans (Nat.le_add_left _ _)).trans ((Nat.le_add_right _ _).trans hw)
  · omega

theorem call_spawn_transfer_error_reply_bound {ctx : CallContext} {s : Frame.State} {gas : Nat}
    {value : U256} {caller target codeAddress : Address} {transfer staticCall : Bool}
    {ii il oi ol : Nat} {code : ByteArray} {disabled : Bool} {child : Frame} {p : Pending} {fault : Fault}
    (hspawn : prepareCall.step ctx s gas value caller target codeAddress transfer staticCall ii il oi ol code disabled =
      .spawn child p) (he : child.message.transfer child.enteredWorld = .error fault) :
    enter child = .done (.error fault) ∧ child.checkpoint.returnData = [] := by
  refine ⟨enter_transfer_error he, ?_⟩
  rw [(prepareCall.step_spawn_call hspawn).2.1]
  rfl

private theorem call_settle_resume_bound {f : Frame} {p : Pending} {e : Frame.Exit}
    {rules : ForkRules} {x : Except (ExceptionalHalt × Frame.State) Frame.State} {i n : Nat}
    (hp : p.target = .call i n) (houtput : e.output.length < 2 ^ 160)
    (h : (settle f e >>= resume rules p f.checkpoint) = .ok x) :
    (match x with | .ok t | .error (_, t) => t.returnData.length) < 2 ^ 160 := by
  obtain ⟨r, hs, hr⟩ := Except.bind_eq_ok h
  have hout := resume_returnData hr
  rw [hp] at hout
  cases x with
  | ok t => exact (congrArg List.length hout).le.trans_lt ((settle_output_length_le hs).trans_lt houtput)
  | error pair =>
    cases pair
    exact (congrArg List.length hout).le.trans_lt ((settle_output_length_le hs).trans_lt houtput)

/-- A native result at call entry bounds the caller's return data on both resume channels. -/
theorem call_spawn_native_enter_success {child : Frame} {p : Pending} {rules : ForkRules} {i n : Nat}
    {world : World} {adr : Address} {e : Frame.Exit}
    (hp : p.target = .call i n) (htransfer : child.message.transfer child.enteredWorld = .ok world)
    (hcode : child.message.codeAddress = some adr)
    (hdispatch : (!child.message.disablePrecompiles && child.message.context.block.rules.isPrecompile adr) = true)
    (hrun : runPrecompile (Frame.entered child child.startState world) adr = .ok e)
    (hdata : child.message.context.calldata.length < 2 ^ 160)
    (hgas : child.message.gas < 2 ^ 256 + Gas.callStipend) :
    enter child = .done (settle child e) ∧ e.output.length < 2 ^ 160 ∧
      ∀ x, (settle child e >>= resume rules p child.checkpoint) = .ok x →
        (match x with | .ok t | .error (_, t) => t.returnData.length) < 2 ^ 160 := by
  have he := enter_precompile htransfer hcode hdispatch
  rw [hrun] at he
  have hout := enter_native_ok_output_length_lt_two_pow_160 hrun hdata hgas
  exact ⟨he, hout, fun _ h => call_settle_resume_bound hp hout h⟩

private theorem enter_run_memory {f : Frame} {r : Frame.Running} (h : enter f = .run r) :
    r.context = f.message.context ∧ Machine.memoryPotential r.state.machine = f.message.gas := by
  unfold enter enterWith at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h; exact ⟨rfl, by simp [Machine.memoryPotential, Frame.entered, Frame.startState,
          Machine.gasMeasure, Memory.empty, show calculateMemoryGasCost 0 = 0 from rfl]⟩
    · cases h; exact ⟨rfl, by simp [Machine.memoryPotential, Frame.entered, Frame.startState,
        Machine.gasMeasure, Memory.empty, show calculateMemoryGasCost 0 = 0 from rfl]⟩

/-- The primitive rejection leaves no data for the caller to resume with. -/
theorem call_spawn_native_enter_error {child : Frame} {p : Pending} {rules : ForkRules} {i n : Nat}
    {world : World} {adr : Address} {e : Frame.Exit} {reason : EvmError} {cost : Nat}
    (hp : p.target = .call i n) (htransfer : child.message.transfer child.enteredWorld = .ok world)
    (hcode : child.message.codeAddress = some adr)
    (hdispatch : (!child.message.disablePrecompiles && child.message.context.block.rules.isPrecompile adr) = true)
    (herror : Precompile.run (Frame.entered child child.startState world).precompileInput adr = .error reason cost)
    (hrun : runPrecompile (Frame.entered child child.startState world) adr = .ok e) :
    enter child = .done (settle child e) ∧ ∀ x,
      (settle child e >>= resume rules p child.checkpoint) = .ok x →
        (match x with | .ok t | .error (_, t) => t.returnData.length) < 2 ^ 160 := by
  have he := enter_precompile htransfer hcode hdispatch
  rw [hrun] at he
  have hout := enter_native_error_output_nil herror hrun
  have hb : e.output.length < 2 ^ 160 := by rw [hout]; decide
  exact ⟨he, fun _ h => call_settle_resume_bound hp hb h⟩

private theorem accounted_of_le {n m : Nat} {e : Frame.Exit} (hm : n ≤ m) (he : Frame.Exit.MemoryAccounted n e) :
    Frame.Exit.MemoryAccounted m e := ⟨he.1.trans hm, he.2.trans hm⟩

private theorem gasLeft_at_most_result_gasMeasure (r : Frame.Result) : r.gasLeft ≤ r.gasMeasure := by
  change r.gasLeft ≤ r.gasLeft + r.stateGas.spilled + r.stateGas.committedSpill
  omega

/-- A completed execution pays for its exit state and for its entire output, including reverts. -/
theorem execFueled_memory_accounting_output :
    ∀ (fuel : Nat) (run : Frame.Running) {e : Frame.Exit}, run.context.block.rules.stateGas = none →
      (execFueled run fuel).run = some (.ok e) → Frame.Exit.MemoryAccounted (Machine.memoryPotential run.state.machine) e := by
  intro fuel
  induction fuel with
  | zero => intro r e hn hr; cases hr
  | succ fuel ih =>
    intro r e hn hr
    rw [execFueled] at hr
    cases hstep : step r with
    | error f => rw [hstep] at hr; cases hr
    | ok next =>
      have ha := step_memory_accounting_output r hn hstep
      rw [hstep] at hr
      cases next with
      | exit raw => cases hr; exact ha
      | next pc s => exact accounted_of_le ha (ih ⟨pc, r.context, s⟩ hn hr)
      | spawn child p pc =>
        dsimp only at hr
        split at hr
        · cases hr
        · cases hr
        · next result hs =>
          have hg : result.gasLeft ≤ child.message.gas := by
            cases hent : enter child with
            | done re =>
              rw [hent] at hs
              cases hs; exact (gasLeft_at_most_result_gasMeasure _).trans (enter_done_gasLe hent)
            | run cr =>
              simp only [hent] at hs
              cases hc : (execFueled cr fuel).run with
              | none => rw [hc] at hs; cases hs
              | some xr =>
                rw [hc] at hs
                cases xr with
                | error f => cases hs
                | ok ex =>
                  have hsettle : settle child ex = .ok result := Option.some.inj hs
                  have hchild := execFueled_settledGasLe fuel cr hc
                  rw [enter_run_gasMeasure hent] at hchild
                  exact (gasLeft_at_most_result_gasMeasure _).trans (settle_gasLe hchild hsettle)
          split at hr
          · cases hr
          · next reason s hres =>
            cases hr
            have hbudget := resume_prepaid_memoryPotential hn hres ha.2
            refine ⟨hbudget.le.trans ((Nat.add_le_add_left hg _).trans ha.1), ?_⟩
            change calculateMemoryGasCost 0 ≤ _
            rw [show calculateMemoryGasCost 0 = 0 from rfl]
            exact Nat.zero_le _
          · next s hres =>
            have hbudget := resume_prepaid_memoryPotential hn hres ha.2
            exact accounted_of_le (hbudget.le.trans ((Nat.add_le_add_left hg _).trans ha.1))
              (ih ⟨pc, r.context, s⟩ hn hr)

private theorem seeded_run_of_ok {run : Frame.Running} {e : Frame.Exit} (h : exec run = .ok e) :
    (execFueled run (sufficientFuel run.state.machine.gasMeasure)).run = some (.ok e) := by
  rw [execFueled_run_sufficientFuel, h]

/-- Each observable exit of the total machine is accounted from its incoming potential. -/
theorem exec_memory_accounting_output (run : Frame.Running) {e : Frame.Exit}
    (hn : run.context.block.rules.stateGas = none) (he : exec run = .ok e) :
    Frame.Exit.MemoryAccounted (Machine.memoryPotential run.state.machine) e :=
  execFueled_memory_accounting_output _ run hn (seeded_run_of_ok he)

/-- A code frame pays for its full output from its own message gas, including a reverted output. -/
theorem entered_code_output_cost {child : Frame} {run : Frame.Running} {e : Frame.Exit}
    (hn : child.message.context.block.rules.stateGas = none)
    (henter : enter child = .run run) (hrun : exec run = .ok e) :
    calculateMemoryGasCost e.output.length ≤ child.message.gas := by
  obtain ⟨hctx, hp⟩ := enter_run_memory henter
  exact hp ▸ (exec_memory_accounting_output run (hctx ▸ hn) hrun).2

private theorem settle_exec_gasLe {f : Frame} {run : Frame.Running} {e : Frame.Exit} {r : Frame.Result}
    (he : enter f = .run run) (hx : exec run = .ok e) (hs : settle f e = .ok r) : r.gasMeasure ≤ f.message.gas := by
  have hbound := execFueled_settledGasLe _ run (seeded_run_of_ok hx)
  rw [enter_run_gasMeasure he] at hbound
  exact settle_gasLe hbound hs

private theorem enter_done_output_bound {f : Frame} {r : Frame.Result} (h : enter f = .done (.ok r))
    (hdata : f.message.context.calldata.length < 2 ^ 160) (hgas : f.message.gas < 2 ^ 256 + Gas.callStipend) :
    r.output.length < 2 ^ 160 := by
  unfold enter enterWith at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · simp only [Frame.Entry.done.injEq] at h
        obtain ⟨e, hr, hs⟩ := Except.bind_eq_ok h
        exact (settle_output_length_le hs).trans_lt (enter_native_ok_output_length_lt_two_pow_160 hr hdata hgas)
      · cases h
    · cases h

private def childResult (f : Frame) : Except Fault Frame.Result :=
  match enter f with
  | .done result => result
  | .run r => exec r >>= settle f

private theorem child_result_output_bound
    {child : Frame} {result : Frame.Result} (hn : child.message.context.block.rules.stateGas = none)
    (hdata : child.message.context.calldata.length < 2 ^ 160)
    (hgas : child.message.gas < 2 ^ 256 + Gas.callStipend) (h : childResult child = .ok result) :
    result.output.length < 2 ^ 160 := by
  unfold childResult at h
  cases he : enter child with
  | done re => rw [he] at h; cases h; exact enter_done_output_bound he hdata hgas
  | run r =>
    simp only [he] at h
    obtain ⟨e, hx, hs⟩ := Except.bind_eq_ok h
    have hc := entered_code_output_cost hn he hx
    exact (settle_output_length_le hs).trans_lt (output_length_with_stipend hc hgas)

/-- An immediate child result or an executed child bounds return data on both caller resume channels. -/
theorem call_spawn_enter_reply_bound
    {child : Frame} {p : Pending} {rules : ForkRules} {i n : Nat}
    (ht : p.target = .call i n) (hn : child.message.context.block.rules.stateGas = none)
    (hdata : child.message.context.calldata.length < 2 ^ 160)
    (hgas : child.message.gas < 2 ^ 256 + Gas.callStipend)
    {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (h : ((match enter child with | .done result => result | .run run => exec run >>= settle child) >>=
      resume rules p child.checkpoint) = .ok x) :
    (match x with | .ok s | .error (_, s) => s.returnData.length) < 2 ^ 160 := by
  change (childResult child >>= resume rules p child.checkpoint) = .ok x at h
  obtain ⟨r, hc, hr⟩ := Except.bind_eq_ok h
  have hout := resume_returnData hr
  rw [ht] at hout
  have hlen := child_result_output_bound hn hdata hgas hc
  cases x with
  | ok s => exact (congrArg List.length hout).le.trans_lt hlen
  | error p => cases p; exact (congrArg List.length hout).le.trans_lt hlen

private def CallReplyBound (rules : ForkRules) : MessageOp.Outcome → Prop
  | .done x => ∀ t, x = .ok t → t.returnData.length < 2 ^ 160
  | .spawn child p => ∀ t, (childResult child >>= resume rules p child.checkpoint) = .ok (.ok t) →
      t.returnData.length < 2 ^ 160

private theorem ofExcept_reply {rules : ForkRules} {x} (h : Walk (fun _ => True) (CallReplyBound rules) x) :
    CallReplyBound rules (MessageOp.Outcome.ofExcept x) := by
  cases x with
  | error e => intro t ht; cases ht
  | ok result => exact h

private theorem push_returnData {s t : Frame.State} {w : U256} (h : s.push w = .ok t) :
    t.returnData = s.returnData := by
  unfold Frame.State.push Frame.State.liftMachine Machine.push at h
  by_cases hs : s.machine.stack.length < 1024 <;> simp only [hs, ite_true, ite_false, Except.ok.injEq, reduceCtorEq] at h
  subst t
  rfl

private theorem prepareCall_reply
    (ctx : CallContext) (s : Frame.State) (gas : Nat) (value : U256) (caller target codeAddress : Address)
    (transfer staticCall : Bool) (ii il oi ol : Nat) (code : ByteArray) (disabled : Bool)
    (hn : ctx.block.rules.stateGas = none) (hgas : gas < 2 ^ 256 + Gas.callStipend) (hi : il < 2 ^ 160) :
    CallReplyBound ctx.block.rules (prepareCall.step ctx s gas value caller target codeAddress transfer staticCall
      ii il oi ol code disabled) := by
  unfold prepareCall.step
  split
  · apply ofExcept_reply
    apply Walk.bind (P := fun t => t.returnData = [])
    · cases hp : ((s.withReturnData []).withGasLeft ((s.withReturnData []).gasLeft + gas)).push 0 with
      | error f => trivial
      | ok t => exact push_returnData hp
    · intro t ht post hpost
      cases hpost
      rw [ht]
      decide
  · intro post hpost
    apply call_spawn_enter_reply_bound (x := .ok post) (i := oi) (n := ol) (ht := rfl) hn _ hgas hpost
    change (Jaune.Array.sliceD _ ii il 0).length < _
    rwa [memory_slice_length]

private theorem refund_call_reply (s : Frame.State) (grant : Nat) (rules : ForkRules) :
    Walk (fun _ => True) (CallReplyBound rules) (do
      let t ← s.push 0
      return .done (.ok ((t.withReturnData []).withGasLeft (t.gasLeft + grant)))) := by
  apply Walk.bind (P := fun _ => True)
  · cases s.push 0 <;> trivial
  · intro t _ post hpost
    cases hpost
    exact (by decide : 0 < 2 ^ 160)

private theorem charge_reply {s t : Frame.State} (cost ii il oi ol : Nat) (hm : t.machine = s.machine)
    (hsource : Machine.memoryPotential s.machine < 2 ^ 256 ∨ il < 2 ^ 160) :
    Walk (fun _ => True) (fun _ => il < 2 ^ 160)
      (t.chargeGas (cost + s.memoryExpansionCost [(ii, il), (oi, ol)])) := by
  have he := congrArg (fun m : Machine => m.memoryExpansionCost [(ii, il), (oi, ol)]) hm
  change t.memoryExpansionCost _ = s.memoryExpansionCost _ at he
  rw [← he]
  cases hc : t.chargeGas (cost + t.memoryExpansionCost [(ii, il), (oi, ol)]) with
  | error e => trivial
  | ok charged =>
    cases hsource with
    | inr hi => exact hi
    | inl hp => exact charged_call_input_length_lt_two_pow_160 _ _ _ _ _ hc (hm ▸ hp)

local macro "reply_stack_simp" : tactic => `(tactic|
  simp only [Frame.State.pop, Frame.State.popToAddress, Frame.State.popToNat,
    Frame.State.liftMachineValue, Machine.popToNat, Machine.popToAddress, Machine.pop,
    Frame.State.withMachine, bind, Except.bind, Pure.pure, Except.pure, MessageOp.Outcome.ofExcept])

private theorem call_reply_fixed
    (ctx : CallContext) (s : Frame.State) (gas callee value ii il oi ol : U256) (rest : List U256)
    (hs : s.stack = gas :: callee :: value :: ii :: il :: oi :: ol :: rest)
    (hn : ctx.block.rules.stateGas = none) (hsource : Machine.memoryPotential s.machine < 2 ^ 256 ∨ il.toNat < 2 ^ 160) :
    CallReplyBound ctx.block.rules (MessageOp.step ctx s .call) := by
  rcases s with ⟨⟨stack, mem, left, meter, rd⟩, world, sub, trail⟩
  change stack = _ at hs
  subst stack
  simp only [MessageOp.step, hn]
  apply ofExcept_reply
  reply_stack_simp
  refine Walk.bind (charge_reply _ _ _ _ _ ?_ ?_) ?_
  · rw [ForkRules.accessDelegation_machine]; split <;> rfl
  · exact hsource
  · intro charged bound
    refine Walk.bind (Walk.assert (H := fun _ => True) True.intro) ?_
    intro _ _
    split
    · exact refund_call_reply _ _ _
    · apply prepareCall_reply
      · exact hn
      · exact MessageCall.gasCostAndChildGas_child_below_word_limit_plus_stipend ..
      · exact bound

private theorem call_reply_paid
    (ctx : CallContext) (s : Frame.State) (hn : ctx.block.rules.stateGas = none)
    (hpot : Machine.memoryPotential s.machine < 2 ^ 256) :
    CallReplyBound ctx.block.rules (MessageOp.step ctx s .call) := by
  rcases s with ⟨⟨stack, mem, left, meter, rd⟩, world, sub, trail⟩
  rcases stack with _ | ⟨gas, _ | ⟨callee, _ | ⟨value, _ | ⟨ii, _ | ⟨il, _ | ⟨oi, _ | ⟨ol, rest⟩⟩⟩⟩⟩⟩⟩
  all_goals first
    | exact call_reply_fixed _ _ _ _ _ _ _ _ _ _ rfl hn (Or.inl hpot)
    | (simp only [MessageOp.step, hn]; reply_stack_simp; intro t ht; cases ht)

/-- MODEXP's output is below the call return-data bound using the gas grant alone. -/
theorem call_spawn_modexp_reply_bound {child : Frame} {world : World} {e : Frame.Exit}
    (hg : child.message.gas < 2 ^ 256 + Gas.callStipend)
    (h : runPrecompile (Frame.entered child child.startState world) 5 = .ok e) : e.output.length < 2 ^ 160 := by
  let run := Frame.entered child child.startState world
  change Frame.Exit.ofPrecompileResult _ (Precompile.modexp run.precompileInput) = .ok e at h
  cases hr : Precompile.modexp run.precompileInput with
  | ok cost output => rw [hr] at h; cases h; exact Precompile.modexp_ok_output_length_lt_two_pow_160 hr hg
  | error reason cost => rw [hr] at h; cases reason <;> cases h <;> exact (by decide : 0 < 2 ^ 160)

/-- Identity's output is below the call return-data bound using the input size alone. -/
theorem call_spawn_id_reply_bound {child : Frame} {world : World} {e : Frame.Exit}
    (hi : child.message.context.calldata.length < 2 ^ 160)
    (h : runPrecompile (Frame.entered child child.startState world) 4 = .ok e) : e.output.length < 2 ^ 160 := by
  let run := Frame.entered child child.startState world
  change Frame.Exit.ofPrecompileResult _ (Precompile.identity run.precompileInput) = .ok e at h
  cases hr : Precompile.identity run.precompileInput with
  | ok cost output =>
    rw [hr] at h; cases h
    change output.length < _
    rw [(Precompile.identity_ok_output_and_cost hr).1]
    exact hi
  | error reason cost => rw [hr] at h; cases reason <;> cases h <;> exact (by decide : 0 < 2 ^ 160)

private theorem charge_memory {s t : Frame.State} {c : Nat} (h : s.chargeGas c = .ok t) : t.memory = s.memory := by
  unfold Frame.State.chargeGas Frame.State.liftMachine Machine.chargeGas at h
  cases hs : safeSub s.gasLeft c with
  | none => simp only [Frame.State.gasLeft] at hs; simp only [hs, reduceCtorEq] at h
  | some gas =>
    simp only [Frame.State.gasLeft] at hs
    simp only [hs, Except.ok.injEq] at h
    subst t; rfl

private theorem zero_call_step_cost {s charged : Frame.State} {gas : U256} {extra cs ii il oi ol : Nat}
    (hc : s.chargeGas ((MessageCall.gasCostAndChildGas 0 gas.toNat s.gasLeft (s.memoryExpansionCost [(ii, il), (oi, ol)]) extra cs).1 +
      s.memoryExpansionCost [(ii, il), (oi, ol)]) = .ok charged) :
    Machine.memoryPotential (charged.extendMemoryForAccesses [(ii, il), (oi, ol)]).machine +
      (MessageCall.gasCostAndChildGas 0 gas.toNat s.gasLeft (s.memoryExpansionCost [(ii, il), (oi, ol)]) extra cs).2 + extra ≤
      Machine.memoryPotential s.machine := by
  have hp := Frame.State.chargeGas_extend_memoryPotential [(ii, il), (oi, ol)]
    (MessageCall.gasCostAndChildGas 0 gas.toNat s.gasLeft (s.memoryExpansionCost [(ii, il), (oi, ol)]) extra cs).1
    (Nat.le_refl (Machine.memoryPotential s.machine))
  rw [hc] at hp
  have hg := MessageCall.gasCostAndChildGas_cost_of_zero_value gas.toNat s.gasLeft (s.memoryExpansionCost [(ii, il), (oi, ol)]) extra cs
  simp only [Walk.ok_iff] at hp
  rw [Nat.add_assoc, ← hg]
  exact hp

private theorem zero_call_resume_bounds
    {ctx : CallContext} {before charged : Frame.State} {gas : U256} {extra cs ii il oi ol : Nat}
    {caller target codeAddress : Address} {transfer staticCall : Bool} {code : ByteArray} {disabled : Bool}
    {child : Frame} {p : Pending} {r : Frame.Result} {rules : ForkRules}
    {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (hc : before.chargeGas ((MessageCall.gasCostAndChildGas 0 gas.toNat before.gasLeft
      (before.memoryExpansionCost [(ii, il), (oi, ol)]) extra cs).1 + before.memoryExpansionCost [(ii, il), (oi, ol)]) = .ok charged)
    (hspawn : prepareCall.step ctx (charged.extendMemoryForAccesses [(ii, il), (oi, ol)])
      (MessageCall.gasCostAndChildGas 0 gas.toNat before.gasLeft (before.memoryExpansionCost [(ii, il), (oi, ol)]) extra cs).2
      0 caller target codeAddress transfer staticCall ii il oi ol code disabled = .spawn child p)
    (hr : r.gasMeasure ≤ child.message.gas) (hres : resume rules p child.checkpoint r = .ok x) :
    let post := match x with | .ok t | .error (_, t) => t
    r.gasMeasure ≤ gas.toNat ∧ post.memory.size = memorySizeAfterAccesses before.memory.size [(ii, il), (oi, ol)] ∧
      Machine.memoryPotential post.machine + extra ≤ Machine.memoryPotential before.machine := by
  obtain ⟨grant, checkpoint, pending⟩ := prepareCall.step_spawn_call hspawn
  have hcap := MessageCall.gasCostAndChildGas_child_at_most_requested_of_zero_value gas.toNat before.gasLeft
    (before.memoryExpansionCost [(ii, il), (oi, ol)]) extra cs
  rw [grant] at hr
  have hwin : ReturnTarget.MemoryPaid p.target child.checkpoint.memory.size := by
    rw [pending, checkpoint]
    exact memorySizeAfterAccess_access_le _ _ _
  have hs := resume_memory_size hres hwin
  have hg := resume_gasLe hres
  have hcharge := zero_call_step_cost hc
  have hm := charge_memory hc
  have size : child.checkpoint.memory.size = memorySizeAfterAccesses before.memory.size [(ii, il), (oi, ol)] := by
    rw [checkpoint]
    change memorySizeAfterAccesses charged.memory.size _ = memorySizeAfterAccesses before.memory.size _
    rw [hm]
  have hparent : Machine.memoryPotential child.checkpoint.machine =
      Machine.memoryPotential (charged.extendMemoryForAccesses [(ii, il), (oi, ol)]).machine := by rw [checkpoint]; rfl
  rw [← hparent] at hcharge
  rcases x with ⟨_, t⟩ | t
  all_goals
    refine ⟨hr.trans hcap, hs.trans size, ?_⟩
    change t.machine.gasMeasure ≤ child.checkpoint.machine.gasMeasure + r.gasMeasure at hg
    change t.memory.size = child.checkpoint.memory.size at hs
    change t.machine.gasMeasure + calculateMemoryGasCost t.memory.size + extra ≤ _
    rw [hs]
    change child.checkpoint.machine.gasMeasure + calculateMemoryGasCost child.checkpoint.memory.size + _ + extra ≤ _ at hcharge
    omega

/-- A child that runs code bounds its raw output, its settled output and the caller’s return data. -/
theorem call_spawn_code_reply_bound
    {child : Frame} {p : Pending} {run : Frame.Running} {rules : ForkRules} {e : Frame.Exit}
    {oi ol : Nat} (ht : p.target = .call oi ol)
    (hn : child.message.context.block.rules.stateGas = none) (hgas : child.message.gas < 2 ^ 256 + Gas.callStipend)
    (henter : enter child = .run run) (hrun : exec run = .ok e) :
    e.output.length < 2 ^ 160 ∧ (∀ r, settle child e = .ok r → r.output.length < 2 ^ 160) ∧
      ∀ x, (settle child e >>= resume rules p child.checkpoint) = .ok x →
        (match x with | .ok t | .error (_, t) => t.returnData.length) < 2 ^ 160 := by
  have hout := output_length_with_stipend (entered_code_output_cost hn henter hrun) hgas
  exact ⟨hout, fun _ hs => (settle_output_length_le hs).trans_lt hout, fun _ hx => call_settle_resume_bound ht hout hx⟩

/-- The actual grant and input of a spawned native call bound its raw output. -/
theorem call_spawn_native_reply_bound
    {ctx : CallContext} {before charged : Frame.State} {gas value : U256} {extra ii il oi ol : Nat}
    {caller target codeAddress : Address} {transfer staticCall : Bool} {code : ByteArray} {disabled : Bool}
    {child : Frame} {p : Pending} {world : World} {adr : Address} {e : Frame.Exit} (base : Nat)
    (hc : before.chargeGas (base + before.memoryExpansionCost [(ii, il), (oi, ol)]) = .ok charged)
    (hs : prepareCall.step ctx (charged.extendMemoryForAccesses [(ii, il), (oi, ol)])
      (MessageCall.gasCostAndChildGas value.toNat gas.toNat before.gasLeft (before.memoryExpansionCost [(ii, il), (oi, ol)]) extra).2 value
      caller target codeAddress transfer staticCall ii il oi ol code disabled = .spawn child p)
    (hsource : Machine.memoryPotential before.machine < 2 ^ 256 ∨ il < 2 ^ 160)
    (hr : runPrecompile (Frame.entered child child.startState world) adr = .ok e) :
    e.output.length < 2 ^ 160 := by
  apply enter_native_ok_output_length_lt_two_pow_160 hr
  · rw [prepareCall.step_spawn_data_length hs]
    exact hsource.elim (charged_call_input_length_lt_two_pow_160 _ _ _ _ _ hc) id
  · rw [(prepareCall.step_spawn_call hs).1]
    exact MessageCall.gasCostAndChildGas_child_below_word_limit_plus_stipend ..

private theorem zero_call_resume_size {ctx : CallContext} {before charged post : Frame.State}
    {gas value : U256} {extra cs ii il oi ol : Nat} {caller target codeAddress : Address}
    {transfer staticCall : Bool} {code : ByteArray} {disabled : Bool} {child : Frame} {p : Pending}
    {rules : ForkRules} {r : Frame.Result}
    (hs : prepareCall.step ctx (charged.extendMemoryForAccesses [(ii, il), (oi, ol)])
      (MessageCall.gasCostAndChildGas 0 gas.toNat before.gasLeft (before.memoryExpansionCost [(ii, il), (oi, ol)]) extra cs).2 value
      caller target codeAddress transfer staticCall ii il oi ol code disabled = .spawn child p)
    (hres : resume rules p child.checkpoint r = .ok (.ok post)) :
    post.memory = (charged.extendMemoryForAccesses [(ii, il), (oi, ol)]).memory.write oi (r.output.take ol) := by
  obtain ⟨_, checkpoint, pending⟩ := prepareCall.step_spawn_call hs
  have hm := resume_call_ok_memory (p := p) (outputIndex := oi) (outputSize := ol) (by rw [pending]) hres
  rw [checkpoint] at hm
  exact hm

/-- A caller with a word-sized potential receives fewer than 2^160 bytes after CALL. -/
theorem MessageOp.step_call_returnData_length_lt_two_pow_160 (ctx : CallContext) (s : Frame.State)
    (hn : ctx.block.rules.stateGas = none) (hpot : Machine.memoryPotential s.machine < 2 ^ 256) :
    match MessageOp.step ctx s .call with
    | .done x => ∀ post, x = .ok post → post.returnData.length < 2 ^ 160
    | .spawn child p => ∀ post, ((match enter child with
        | .done result => result | .run cr => exec cr >>= settle child) >>=
        resume ctx.block.rules p child.checkpoint) = .ok (.ok post) → post.returnData.length < 2 ^ 160 := by
  exact call_reply_paid ctx s hn hpot

/-- A word-sized gas operand and a 160-bit input length bound the return data of CALL. -/
theorem MessageOp.step_call_returnData_length_lt_two_pow_160_of_input_size (ctx : CallContext) (s : Frame.State)
    (gas callee value ii il oi ol : U256) (rest : List U256)
    (hs : s.stack = gas :: callee :: value :: ii :: il :: oi :: ol :: rest)
    (hn : ctx.block.rules.stateGas = none) (hi : il.toNat < 2 ^ 160) :
    match MessageOp.step ctx s .call with
    | .done x => ∀ post, x = .ok post → post.returnData.length < 2 ^ 160
    | .spawn child p => ∀ post, ((match enter child with
        | .done result => result | .run cr => exec cr >>= settle child) >>=
        resume ctx.block.rules p child.checkpoint) = .ok (.ok post) → post.returnData.length < 2 ^ 160 := by
  exact call_reply_fixed ctx s gas callee value ii il oi ol rest hs hn (Or.inr hi)

/-- For a zero-value spawn, settlement and resume account for child gas, caller memory and the copy window. -/
theorem zero_call_spawn_resume_raw_accounting
    {ctx : CallContext} {before charged : Frame.State} {gas : U256} {extra cs ii il oi ol : Nat}
    {caller target codeAddress : Address} {transfer staticCall : Bool} {code : ByteArray} {disabled : Bool}
    {child : Frame} {p : Pending} {rules : ForkRules} {run : Frame.Running}
    {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (hc : before.chargeGas ((MessageCall.gasCostAndChildGas 0 gas.toNat before.gasLeft
      (before.memoryExpansionCost [(ii, il), (oi, ol)]) extra cs).1 + before.memoryExpansionCost [(ii, il), (oi, ol)]) = .ok charged)
    (hspawn : prepareCall.step ctx (charged.extendMemoryForAccesses [(ii, il), (oi, ol)])
      (MessageCall.gasCostAndChildGas 0 gas.toNat before.gasLeft (before.memoryExpansionCost [(ii, il), (oi, ol)]) extra cs).2
      0 caller target codeAddress transfer staticCall ii il oi ol code disabled = .spawn child p)
    (henter : enter child = .run run)
    (hres : ((exec run >>= settle child) >>= resume rules p child.checkpoint) = .ok x) :
    ∃ r : Frame.Result, (exec run >>= settle child) = .ok r ∧ r.gasMeasure ≤ gas.toNat ∧
      let post := match x with | .ok t | .error (_, t) => t
      post.memory.size = memorySizeAfterAccesses before.memory.size [(ii, il), (oi, ol)] ∧
      Machine.memoryPotential post.machine + extra ≤ Machine.memoryPotential before.machine ∧
      (∀ t, x = .ok t → t.memory = (charged.extendMemoryForAccesses [(ii, il), (oi, ol)]).memory.write oi (r.output.take ol)) := by
  obtain ⟨r, hsettled, hx⟩ := Except.bind_eq_ok hres
  obtain ⟨e, hrun, hs⟩ := Except.bind_eq_ok hsettled
  have hb := zero_call_resume_bounds hc hspawn (settle_exec_gasLe henter hrun hs) hx
  refine ⟨r, hsettled, hb.1, hb.2.1, hb.2.2, ?_⟩
  intro t ht; subst x
  exact zero_call_resume_size hspawn hx

end Jaune
