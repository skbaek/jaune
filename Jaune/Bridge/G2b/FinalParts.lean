import Jaune.MessageCall.FinalParts
import Jaune.Bridge.G2b.Control
import Jaune.Bridge.G2b.MessageOps

/-!
# Bridge: the staged `enter`, `settle` and `resume` against the `Devm` ones (G2b, unit W3-3)

Old side: `Jaune.enterWith`, `Jaune.enter`, `Jaune.settle`, `Jaune.depositCode`,
`Jaune.chargeDeposit`, `Jaune.absorbMeters` and `Jaune.resume` (`Jaune/MessageCall/Enter.lean`,
`Settle.lean`, `Resume.lean`) at `bba27e95`, unedited. New side: the `Jaune.Staging` forms in
`Jaune.MessageCall.FinalParts`.

* `settle_eq`: for every frame and every raw result, the old `settle` is the new one after
  `Frame.Exit.ofExecution` (a fault short-circuits). No premise: neither side reads the stored
  error, and a halted frame's output, which `ofExecution` forgets, is read by neither.
* `depositCode_ofDevm`: the deposit, both channels, every rule set.
* `Frame.Entry.observe_enterWith`: entry from a start state with no output (the premise of W3-2d's
  precompile square); `enter_observe` for a spawned child, unconditionally.
* `resume_eq`: the old `resume` is the new one with the caller rebuilt through `Pending.restore`;
  `resume_ofDevm`: the new one is the old one grouped, for a saved caller whose RIPEMD-160 flag is
  down (every checkpoint a step produces: it is `Frame.State.ofDevm` of the caller).

Everything here goes with `Devm` after G2b's tag.
-/

namespace Jaune

open Frame.State

/-! ### Outcome maps over binds -/

/-- `mapResultState` through a bind whose continuation commutes. -/
theorem Except.mapResultState_bind {ε σ τ : Type} {f : σ → τ} {x : Except (ε × σ) σ}
    {g : σ → Except (ε × σ) σ} {h : τ → Except (ε × τ) τ}
    (hg : ∀ a, Except.mapResultState f (g a) = h (f a)) :
    Except.mapResultState f (x >>= g) = Except.mapResultState f x >>= h := by
  cases x with
  | error e => rcases e with ⟨e, s⟩; rfl
  | ok a => exact hg a

/-! ### `settle` -/

theorem chargeDeposit_ofDevm (rules : ForkRules) (code : Bytes) (d : Devm) :
    Except.mapResultState ofDevm (chargeDeposit rules code d) =
      Staging.chargeDeposit rules code (ofDevm d) := by
  have hthen : Except.mapResultState ofDevm
      (Devm.chargeGas (code.length * Gas.codeDeposit) d >>= fun d =>
        if rules.code.maxCodeSize < code.length then .error (.outOfGas .none, d) else .ok d) =
      ((ofDevm d).chargeGas (code.length * Gas.codeDeposit) >>= fun s =>
        if rules.code.maxCodeSize < code.length then .error (.outOfGas .none, s) else .ok s) := by
    rw [Except.mapResultState_bind (h := fun s =>
      if rules.code.maxCodeSize < code.length then .error (.outOfGas .none, s) else .ok s),
      mapResultState_devmChargeGas]
    intro a; split <;> rfl
  have hsome : ∀ state : StateGasRules, Except.mapResultState ofDevm
      (if rules.code.maxCodeSize < code.length then .error (.outOfGas .none, d) else
        Devm.chargeGas (Gas.keccak256Word * ceilDiv code.length 32) d >>= fun d =>
          Devm.chargeStateGas (code.length * state.costPerStateByte) d) =
      (if rules.code.maxCodeSize < code.length then .error (.outOfGas .none, ofDevm d) else
        (ofDevm d).chargeGas (Gas.keccak256Word * ceilDiv code.length 32) >>= fun s =>
          s.chargeStateGas (code.length * state.costPerStateByte)) := by
    intro state
    split
    · rfl
    · rw [Except.mapResultState_bind
        (h := fun s => s.chargeStateGas (code.length * state.costPerStateByte)),
        mapResultState_devmChargeGas]
      intro a; exact mapResultState_devmChargeStateGas _ a
  unfold chargeDeposit Staging.chargeDeposit
  rcases rules.stateGas with _ | state <;> dsimp only <;> rcases code with _ | ⟨b, t⟩
  · exact hthen
  · by_cases hb : b = 239
    · subst hb
      by_cases hr : rules.creation.rejectEf = true
      · simp [hr, Except.mapResultState]
      · simpa [hr] using hthen
    · simpa [hb] using hthen
  · exact hsome state
  · by_cases hb : b = 239
    · subst hb
      simp [Except.mapResultState]
    · simpa [hb] using hsome state

theorem depositCode_ofDevm (rules : ForkRules) (a : Address) (code : Bytes) (d : Devm) :
    Except.mapResultState ofDevm (depositCode rules a code d) =
      Staging.depositCode rules a code (ofDevm d) := by
  unfold depositCode Staging.depositCode
  rw [← chargeDeposit_ofDevm]
  rcases chargeDeposit rules code d with ⟨e, d'⟩ | d' <;> rfl

/-- The square for `settle`: for every frame and every raw result, the old settlement is the new
one of the raw result's exit; a fault short-circuits on both sides. -/
theorem settle_eq (f : Frame) (raw : Execution) :
    settle f raw = Frame.Exit.ofExecution raw >>= Staging.settle f := by
  rcases raw with ⟨e, d⟩ | d
  · rcases e with r | _ | r | r <;>
      simp only [settle, Staging.settle, Frame.Exit.ofExecution, bind, Except.bind] <;>
      (try cases f.message.context.block.rules.stateGas) <;> rfl
  · simp only [settle, Staging.settle, Frame.Exit.ofExecution, bind, Except.bind,
      Devm.recordTouch_output]
    rw [← ofDevm_recordTouch]
    cases f.message.kind with
    | call => rfl
    | create =>
      dsimp only
      rw [← depositCode_ofDevm]
      rcases depositCode _ _ _ _ with ⟨r, s⟩ | s
      · cases f.message.context.block.rules.stateGas <;> rfl
      · rfl

/-! ### `enter` -/

/-- An old entry, observed as a new one. -/
def Frame.Entry.observe : Frame.Entry → Staging.Frame.Entry
  | .run evm => .run (Frame.Running.ofEvm evm)
  | .done result => .done result

/-- The square for `enterWith`, from a start state with no output. -/
theorem Frame.Entry.observe_enterWith (f : Frame) {start : Devm} (ho : start.output = []) :
    (enterWith f start).observe = Staging.enterWith f (ofDevm start) := by
  unfold enterWith Staging.enterWith
  dsimp only
  cases f.message.transfer f.enteredWorld with
  | error fault => rfl
  | ok world =>
    dsimp only
    cases f.message.codeAddress with
    | none => rfl
    | some address =>
      dsimp only
      by_cases hp : (!f.message.disablePrecompiles &&
          f.message.context.block.rules.isPrecompile address) = true
      · simp only [hp, ↓reduceIte]
        simp only [observe]
        rw [settle_eq, ofExecution_executePrecompile _ ho]
        rfl
      · simp only [hp, Bool.false_eq_true, ↓reduceIte]
        rfl

/-- The square for entering a spawned child. -/
theorem Frame.Entry.observe_enter (f : Frame) :
    (enter f).observe = Staging.enter f := by
  unfold enter Staging.enter Frame.start
  rw [observe_enterWith f rfl]
  unfold Staging.enterWith Staging.Frame.entered
  rcases f with ⟨m, cp⟩
  rfl

/-- The new entry reads nothing of the start state's RIPEMD-160 flag. -/
theorem Staging.enterWith_ofDevm_toDevm (f : Frame) (s : Frame.State) :
    Staging.enterWith f (ofDevm s.toDevm) = Staging.enterWith f s := by
  have h : ∀ w, Staging.Frame.entered f (ofDevm s.toDevm) w = Staging.Frame.entered f s w := by
    intro w
    rcases s with ⟨⟨⟩, ⟨⟩, ⟨⟩, ⟨⟩⟩
    rfl
  unfold Staging.enterWith
  simp only [h]

/-! ### `resume` -/

theorem absorbMeters_ofLegacy (rules : ForkRules) (p : Pending) (saved : Machine)
    (r : Frame.Result) :
    Staging.absorbMeters rules (.ofLegacy p) saved r = absorbMeters rules p saved r := rfl

/-- The old `resume` is the new one with the caller rebuilt as a `Devm` through
`Pending.restore`. -/
theorem resume_eq (rules : ForkRules) (p : Pending) (saved : Frame.State) (r : Frame.Result) :
    resume rules p saved r =
      (Staging.resume rules (.ofLegacy p) saved r).map (Except.mapResultState p.restore) := by
  unfold resume Staging.resume
  simp only [absorbMeters_ofLegacy]
  simp only [bind, Except.bind, pure, Except.pure]
  split_ifs <;> (try simp only [*, ↓reduceIte]) <;> rfl

/-- A rebuilt caller grouped again is the caller, when its RIPEMD-160 flag is down. -/
theorem ofDevm_restore (p : Pending) {s : Frame.State} (h : s.trail.touchedRIPEMD160 = false) :
    ofDevm (p.restore s) = s := by
  rw [← ofDevm_toDevm h]
  rfl

/-- The square for `resume`: the new `resume` is the old one grouped, for a saved caller whose
RIPEMD-160 flag is down. -/
theorem resume_ofDevm (rules : ForkRules) (p : Pending) (saved : Frame.State) (r : Frame.Result)
    (h : saved.trail.touchedRIPEMD160 = false) :
    (resume rules p saved r).map (Except.mapResultState ofDevm) =
      Staging.resume rules (.ofLegacy p) saved r := by
  rw [resume_eq]
  rcases saved with ⟨m, w, u, ⟨c, ar, sr, flag⟩⟩
  simp only at h
  subst h
  unfold Staging.resume
  simp only [bind, Except.bind, pure, Except.pure]
  split <;> (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

end Jaune
