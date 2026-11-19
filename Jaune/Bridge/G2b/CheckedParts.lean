import Jaune.Bridge.G2b.CheckedOutcomes
import Jaune.MessageCall.FinalParts
import Jaune.Bridge.G2b.CheckedSimulation
import Jaune.Bridge.G2b.PrecompileInput

/-! Entry, settlement and resumption preserve each observable field when memory is forgotten. -/

namespace Jaune.Checked

variable [LegacyTransaction]

private theorem Frame.legacyKind (f : Frame) : f.toLegacy.message.kind = f.message.kind := rfl
private theorem Frame.legacyCodeAddress (f : Frame) : f.toLegacy.message.codeAddress = f.message.codeAddress := rfl
private theorem Frame.legacyDisablePrecompiles (f : Frame) :
    f.toLegacy.message.disablePrecompiles = f.message.disablePrecompiles := rfl
private theorem Frame.legacyRules (f : Frame) : f.toLegacy.message.context.block.rules = f.message.context.block.rules := rfl
private theorem Frame.legacyRecipient (f : Frame) : f.toLegacy.message.context.recipient = f.message.context.recipient := rfl
private theorem Frame.legacyTransfer (f : Frame) (w : World) :
    f.toLegacy.message.transfer w = f.message.transfer w := rfl

private theorem Frame.legacyAvailable (f : Frame) (a : Address) :
    (!f.toLegacy.message.disablePrecompiles && decide (f.toLegacy.message.context.block.rules.isPrecompile a)) =
      (!f.message.disablePrecompiles && decide (f.message.context.block.rules.isPrecompile a)) := rfl

local macro "frame_fields" : tactic => `(tactic| simp only [Frame.legacyKind, Frame.legacyCodeAddress,
  Frame.legacyDisablePrecompiles, Frame.legacyRules, Frame.legacyRecipient, Frame.legacyTransfer])

theorem Frame.startState_toLegacy (f : Frame) : f.startState.toLegacy = f.toLegacy.startState := rfl

theorem Frame.enteredWorld_toLegacy (f : Frame) : f.toLegacy.enteredWorld = f.enteredWorld := by
  unfold Jaune.Frame.enteredWorld Checked.Frame.enteredWorld
  frame_fields
  cases f.message.kind <;> rfl

theorem Frame.entered_toLegacy (f : Frame) (s : Frame.State) (w : World) :
    Staging.Frame.entered f.toLegacy s.toLegacy w = (Frame.entered f s w).toLegacy := by
  unfold Frame.entered Staging.Frame.entered Jaune.Frame.enteredCreatedAccounts Frame.enteredCreatedAccounts
  frame_fields
  cases f.message.kind <;> rfl

theorem runPrecompile_toLegacy (r : Frame.Running) (a : Address) :
    Jaune.runPrecompile r.toLegacy a = (runPrecompile r a).map Frame.Exit.toLegacy := by
  have hp : precompileRun r.toLegacy.precompileEvm a = Precompile.run r.precompileInput a :=
    Precompile.run_ofEvm _ a
  unfold Jaune.runPrecompile runPrecompile
  rw [hp]
  cases Precompile.run r.precompileInput a with
  | ok cost output => rfl
  | error reason cost => cases reason <;> rfl

private theorem chargeDeposit_toLegacy (rules : ForkRules) (code : Bytes) (s : Frame.State) :
    MemorySimulation.Square (chargeDeposit rules code s) (Staging.chargeDeposit rules code s.toLegacy) := by
  unfold chargeDeposit Staging.chargeDeposit
  cases hs : rules.stateGas <;> cases code <;> dsimp only
  all_goals repeat' first
    | rfl
    | exact MemorySimulation.Frame.State.chargeStateGas _ _
    | (refine MemorySimulation.Square.bind (MemorySimulation.Frame.State.chargeGas _ _) ?_; intro t)
    | (refine MemorySimulation.Square.ite rfl ?_ ?_ <;> intro _)
    | (split <;> try contradiction <;> try (exfalso; simp_all only [List.cons.injEq, exists_prop, and_true, exists_eq_right]))
  all_goals first | (exfalso; solve_by_elim) | (exfalso; exact (by assumption : ∀ tail, _ :: _ = 239 :: tail → False) _ (by assumption))

private theorem depositCode_toLegacy (rules : ForkRules) (a : Address) (code : Bytes) (s : Frame.State) :
    Staging.depositCode rules a code s.toLegacy = ResumeResult.toLegacy (depositCode rules a code s) := by
  unfold Staging.depositCode depositCode
  rw [← (show MemorySimulation.erase (chargeDeposit rules code s) = _ from chargeDeposit_toLegacy rules code s)]
  cases chargeDeposit rules code s with
  | ok s => rfl
  | error e => cases e; rfl

theorem settle_toLegacy (f : Frame) (e : Frame.Exit) :
    Staging.settle f.toLegacy e.toLegacy = settle f e := by
  cases e with
  | reverted out s | halted out s =>
    simp only [Staging.settle, Frame.Exit.toLegacy, settle, Frame.enteredWorld_toLegacy]
    frame_fields
    cases f.message.context.block.rules.stateGas <;> rfl
  | finished out s =>
    simp only [Staging.settle, Frame.Exit.toLegacy, settle, Frame.enteredWorld_toLegacy]
    frame_fields
    change (match f.message.kind with | .call => _ | .create => _) = _
    cases f.message.kind with
    | call => rfl
    | create =>
      change (match Staging.depositCode _ _ out (Frame.State.recordTouch _ _ _ s).toLegacy with
        | .ok t => _ | .error (reason, t) => _) = _
      rw [depositCode_toLegacy]
      cases hd : depositCode _ _ out _ with
      | ok s => rfl
      | error e => cases e; cases f.message.context.block.rules.stateGas <;> rfl

theorem enterWith_toLegacy (f : Frame) (s : Frame.State) :
    Staging.enterWith f.toLegacy s.toLegacy = (enterWith f s).toLegacy := by
  unfold Staging.enterWith enterWith
  simp only [Frame.enteredWorld_toLegacy, Frame.entered_toLegacy, Frame.legacyTransfer,
    Frame.legacyCodeAddress, Frame.legacyAvailable]
  cases htransfer : f.message.transfer f.enteredWorld with
  | error fault => rfl
  | ok world =>
    cases haddress : f.message.codeAddress with
    | none => rfl
    | some a =>
      by_cases available : (!f.message.disablePrecompiles && decide (f.message.context.block.rules.isPrecompile a)) = true
      · simp only [available, Bool.false_eq_true, ↓reduceIte, Frame.Entry.toLegacy, runPrecompile_toLegacy]
        cases runPrecompile (Frame.entered f s world) a with
        | error fault => rfl
        | ok e => exact congrArg Staging.Frame.Entry.done (settle_toLegacy f e)
      · simp only [available, Bool.false_eq_true, ↓reduceIte, Frame.Entry.toLegacy]

theorem enter_toLegacy (f : Frame) : Staging.enter f.toLegacy = (enter f).toLegacy := by
  unfold Staging.enter enter
  rw [← Frame.startState_toLegacy, enterWith_toLegacy]

theorem absorbMeters_toLegacy (rules : ForkRules) (p : Staging.Pending) (m : Machine)
    (r : Frame.Result) : Staging.absorbMeters rules p m.toLegacy r = (absorbMeters rules p m r).toLegacy := by
  cases ht : p.target <;> cases hf : r.failed <;> cases hs : rules.stateGas <;> cases hn : p.newAccountCharged <;>
    simp only [Staging.absorbMeters, absorbMeters, ht, hf, hs, hn, Bool.false_eq_true, ↓reduceIte]
  all_goals first | rfl | (unfold Jaune.Machine.repayStateGasSpill Machine.repayStateGasSpill; split <;> rfl)

theorem finishTarget_toLegacy (t : ReturnTarget) (r : Frame.Result) (m : Machine) :
    t.finish r m.toLegacy = (finishTarget t r m).toLegacy := by
  cases t with
  | call i n => simp only [ReturnTarget.finish, finishTarget, Machine.toLegacy, Memory.write_toMem]
  | create a => rfl

theorem resume_toLegacy (rules : ForkRules) (p : Staging.Pending) (saved : Frame.State) (r : Frame.Result) :
    Staging.resume rules p saved.toLegacy r = (resume rules p saved r).map ResumeResult.toLegacy := by
  unfold Staging.resume resume
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure,
    show saved.toLegacy.machine = saved.machine.toLegacy from rfl, absorbMeters_toLegacy, finishTarget_toLegacy,
    show saved.toLegacy.world = saved.world from rfl, show saved.toLegacy.trail = saved.trail from rfl,
    show saved.toLegacy.substate = saved.substate from rfl]
  cases r <;> cases hs : rules.stateGas <;> simp only [hs, Option.isSome, Bool.false_eq_true, ↓reduceIte]
  all_goals repeat' split <;> try contradiction <;> try rfl
  all_goals simp_all [Except.map, ResumeResult.toLegacy, Frame.State.toLegacy, Machine.toLegacy]

end Jaune.Checked
