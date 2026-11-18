import Jaune.MessageCall.FinalStateGasOps

/-!
# Disabled state gas at a frame boundary

When a fork has no state gas, entering and settling a frame preserve the zero meter.
Resuming a caller preserves its meter independently of its child's result.
-/

namespace Jaune

open Jaune

def Frame.State.StateGasZero (s : Frame.State) : Prop := s.machine.stateGas = .zero

def Frame.Running.StateGasZero (r : Frame.Running) : Prop :=
  r.context.block.rules.stateGas = none ∧ r.state.StateGasZero

end Jaune

namespace Jaune.Staging

open Jaune

def Frame.Entry.StateGasZero : Frame.Entry → Prop
  | .run r => r.StateGasZero
  | .done x => ∀ r, x = .ok r → r.stateGas = .zero

theorem Frame.State.chargeGas_stateGasZero (cost : Nat) {s : Frame.State} (h : s.StateGasZero) :
    Walk Frame.State.StateGasZero Frame.State.StateGasZero (s.chargeGas cost) := by
  apply Walk.liftMachine (Hm := fun m => m.stateGas = .zero) (Pm := fun m => m.stateGas = .zero)
  unfold Machine.chargeGas
  split <;> exact h

theorem chargeDeposit_stateGasZero {rules : ForkRules} {code : Bytes} {s : Frame.State}
    (hrules : rules.stateGas = none) (h : s.StateGasZero) :
    Walk Frame.State.StateGasZero Frame.State.StateGasZero (chargeDeposit rules code s) := by
  have hthen : Walk Frame.State.StateGasZero Frame.State.StateGasZero (do
      let s ← s.chargeGas (code.length * Gas.codeDeposit)
      if rules.code.maxCodeSize < code.length then .error (.outOfGas .none, s) else .ok s) := by
    apply Walk.bind (Frame.State.chargeGas_stateGasZero _ h)
    intro s' hs'
    split <;> exact hs'
  unfold chargeDeposit
  rw [hrules]
  dsimp only
  split
  · split
    · exact h
    · exact hthen
  · exact hthen

theorem depositCode_stateGasZero {rules : ForkRules} (recipient : Address) (code : Bytes)
    {s : Frame.State} (hrules : rules.stateGas = none) (h : s.StateGasZero) :
    Walk Frame.State.StateGasZero Frame.State.StateGasZero (depositCode rules recipient code s) := by
  have hc := chargeDeposit_stateGasZero (code := code) hrules h
  unfold depositCode
  cases he : chargeDeposit rules code s with
  | error e => rw [he] at hc; exact hc
  | ok s' => rw [he] at hc; exact hc

theorem settle_stateGasZero {f : Frame} {exit : Frame.Exit} {r : Frame.Result}
    (hrules : f.message.context.block.rules.stateGas = none) (h : exit.state.StateGasZero)
    (hs : settle f exit = .ok r) : r.stateGas = .zero := by
  cases exit with
  | halted reason s => simp only [settle, hrules, Except.ok.injEq] at hs; subst r; exact h
  | reverted output s => simp only [settle, hrules, Except.ok.injEq] at hs; subst r; exact h
  | finished output s =>
    let touched := s.recordTouch f.message.context.block.rules true f.message.context.recipient
    have ht : touched.StateGasZero := h
    simp only [settle, hrules] at hs
    split at hs
    · cases hs; exact ht
    · have hd := depositCode_stateGasZero f.message.context.recipient output hrules ht
      split at hs
      · next s' he =>
          change depositCode _ _ _ touched = _ at he
          rw [he] at hd
          cases hs
          exact hd
      · next reason s' he =>
          change depositCode _ _ _ touched = _ at he
          rw [he] at hd
          cases hs
          exact hd

theorem runPrecompile_stateGasZero {running : Frame.Running} (address : Address)
    {exit : Frame.Exit} (h : running.state.StateGasZero)
    (hr : runPrecompile running address = .ok exit) : exit.state.StateGasZero := by
  unfold runPrecompile at hr
  cases hp : precompileRun running.precompileEvm address with
  | ok cost output => rw [hp] at hr; cases hr; exact h
  | error reason cost => rw [hp] at hr; cases reason <;> cases hr <;> exact h

theorem enterWith_stateGasZero {f : Frame} {start : Frame.State}
    (hrules : f.message.context.block.rules.stateGas = none) (h : start.StateGasZero) :
    (enterWith f start).StateGasZero := by
  unfold enterWith
  dsimp only
  split
  · intro r hr; cases hr
  · next world _ =>
    have hrun : (Frame.entered f start world).StateGasZero := ⟨hrules, h⟩
    split
    · split
      · intro r hr
        obtain ⟨exit, he, hs⟩ := Except.bind_eq_ok hr
        exact settle_stateGasZero hrules (runPrecompile_stateGasZero _ hrun.2 he) hs
      · exact hrun
    · exact hrun

theorem enter_stateGasZero {f : Frame} (hrules : f.message.context.block.rules.stateGas = none)
    (hgrant : f.message.stateGasGrant = 0) : (enter f).StateGasZero := by
  apply enterWith_stateGasZero hrules
  simp only [Frame.State.StateGasZero, Frame.startState, hgrant]
  rfl

theorem resume_stateGasZero {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (hrules : rules.stateGas = none) (hsaved : saved.StateGasZero)
    (h : resume rules p saved r = .ok x) : Walk Frame.State.StateGasZero Frame.State.StateGasZero x := by
  unfold resume at h
  simp only [hrules, Option.isSome_none, Bool.false_eq_true, ite_false] at h
  cases r <;> dsimp only at h <;> split at h <;> cases h <;>
    cases p.target <;> simpa [Walk, Frame.State.StateGasZero, ReturnTarget.finish, absorbMeters, hrules]
      using hsaved


/-- A completed execution returns with state gas disabled on each observable exit. -/
theorem execFueled_run_stateGasZero (fuel : Nat) (running : Frame.Running)
    (h : running.StateGasZero) {exit : Frame.Exit}
    (hr : (execFueled running fuel).run = some (.ok exit)) : exit.state.StateGasZero := by
  induction fuel generalizing running with
  | zero => simp [execFueled] at hr
  | succ fuel ih =>
    rw [execFueled] at hr
    cases hs : step running with
    | error fault => rw [hs] at hr; cases hr
    | ok next =>
      have hstep := step_stateGasZero h.1 h.2 hs
      rw [hs] at hr
      cases next with
      | exit e => cases hr; exact hstep
      | next pc s => exact ih ⟨pc, running.context, s⟩ ⟨h.1, hstep⟩ hr
      | spawn child pending pc =>
        dsimp only at hr
        split at hr
        · cases hr
        · cases hr
        · split at hr
          · cases hr
          · next reason s hres =>
            cases hr
            exact resume_stateGasZero h.1 hstep.2.2 hres
          · next s hres =>
            exact ih ⟨pc, running.context, s⟩
              ⟨h.1, resume_stateGasZero h.1 hstep.2.2 hres⟩ hr

/-- With no state gas the execution gas alone measures the frame at exit. -/
theorem execFueled_run_gasMeasure_eq_gasLeft {fuel : Nat} {running : Frame.Running}
    (h : running.StateGasZero) {exit : Frame.Exit} (hr : (execFueled running fuel).run = some (.ok exit)) :
    exit.state.machine.gasMeasure = exit.state.machine.gasLeft := by
  have hz := execFueled_run_stateGasZero fuel running h hr
  simp only [Frame.State.StateGasZero] at hz
  simp [Jaune.Machine.gasMeasure, hz, StateGasMeter.zero]

theorem exec_stateGasZero {running : Frame.Running} (h : running.StateGasZero)
    {exit : Frame.Exit} (hr : exec running = .ok exit) : exit.state.StateGasZero := by
  unfold exec at hr
  split at hr
  · next result he =>
    subst result
    exact execFueled_run_stateGasZero _ _ h he
  · cases hr

end Jaune.Staging
