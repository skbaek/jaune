import Jaune.MessageCall.RunInvariants
import Jaune.MessageCall.Driver

/-!
# The run invariants through the driver (goal `jaune-shape-and-names-v1`, S3)

`Jaune.MessageCall.RunInvariants` walks every instruction; this module carries its invariant
`Inv c n` (committed spill `c`, room for `n` more words) through the message-opcode dispatch,
`Evm.step`, `resume` and the driver `execFueled`, by one induction on fuel (`execFueled_inv`).
From it:

* **The stack bound.** Every machine a run reaches holds at most 1024 words before its step
  (`Evm.Reaches.stack_le`), and a reached spawn saves a caller with room for the calling opcode's
  push (`Evm.Reaches.room`).
* **An uncommitted child.** A spawned child starts with no committed spill and nothing in its
  run commits any, so the result it returns has none, and a failed one under state gas is
  settled (`Frame.Returns.inv`, `settled_of_enter_run`, `committed_of_enter_run`).

`Evm.Reaches.resume_failed` and `Evm.Reaches.resume_success` are the S3 lemmas at a reached spawn
with a result its child returns, `room` and `settled` discharged by these invariants: a client
names the run by its premises and unfolds no interpreter step.
-/

namespace Jaune

namespace RunInvariants

theorem ForkRules.accessDelegation_mach (rules : ForkRules) (d : Devm) (a : Address) :
    (rules.accessDelegation d a).2.2.2.2.mach = d.mach := by
  unfold ForkRules.accessDelegation GasSchedule.accessDelegation
  split
  · dsimp only; split
    · exact addAccessedAddress_mach _ _
    · rfl
  · rfl

theorem completeDelegationAccess_mach (d : Devm) (b : Bool) (a : Address) :
    (completeDelegationAccess d b a).2.mach = d.mach := by
  unfold completeDelegationAccess
  split
  · exact addAccessedAddress_mach _ _
  · rfl

open Lean Elab Tactic Meta in
/-- `inv_close_core` through the delegation-access helpers of the message opcodes. -/
elab "inv_close_msg" : tactic => withMainContext do
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    unless ty.isAppOf ``Inv do continue
    let h ← Term.exprToSyntax (mkFVar decl.fvarId)
    let s ← saveState
    let ok ← (focusAndDone do
        evalTactic (← `(tactic| apply Inv.of_mach $h))
        evalTactic (← `(tactic| all_goals try (simp only [ForkRules.accessDelegation_mach,
          completeDelegationAccess_mach, Jaune.Devm.balReadAccount_mach, addAccessedAddress_mach]; done)))
        evalTactic (← `(tactic| all_goals first | rfl | exact Nat.le_refl _ | omega))
        pure true) <|>
      (do s.restore; pure false)
    if ok then return
  throwError "inv_close_msg: no hypothesis closes the goal"

macro_rules
  | `(tactic| inv_close) => `(tactic| inv_close_msg)

macro_rules
  | `(tactic| inv_step) => `(tactic| first
  | (with_reducible apply genericCreate.step_inv; inv_close)
  | (with_reducible apply genericCall.step_inv; inv_close)
  | (with_reducible apply genericCallAmsterdam.step_inv; inv_close)
  | (with_reducible apply genericCreateAmsterdam.step_inv; inv_close))

theorem MessageOp.step_inv_create (sevm : Sevm) (devm : Devm) {c : Nat} (h : Inv c 0 devm) :
    OutcomeInv sevm.benvStat.rules c (MessageOp.step sevm devm .create) := by
  simp only [MessageOp.step]; inv_walk

theorem MessageOp.step_inv_create2 (sevm : Sevm) (devm : Devm) {c : Nat} (h : Inv c 0 devm) :
    OutcomeInv sevm.benvStat.rules c (MessageOp.step sevm devm .create2) := by
  simp only [MessageOp.step]; inv_walk

theorem MessageOp.step_inv_call (sevm : Sevm) (devm : Devm) {c : Nat} (h : Inv c 0 devm) :
    OutcomeInv sevm.benvStat.rules c (MessageOp.step sevm devm .call) := by
  simp only [MessageOp.step]
  cases hac : sevm.benvStat.rules.access <;> inv_walk

theorem MessageOp.step_inv_callcode (sevm : Sevm) (devm : Devm) {c : Nat} (h : Inv c 0 devm) :
    OutcomeInv sevm.benvStat.rules c (MessageOp.step sevm devm .callcode) := by
  simp only [MessageOp.step]
  cases hac : sevm.benvStat.rules.access <;> inv_walk

theorem MessageOp.step_inv_delegatecall (sevm : Sevm) (devm : Devm) {c : Nat} (h : Inv c 0 devm) :
    OutcomeInv sevm.benvStat.rules c (MessageOp.step sevm devm .delegatecall) := by
  simp only [MessageOp.step]
  cases hac : sevm.benvStat.rules.access <;> inv_walk

theorem MessageOp.step_inv_staticcall (sevm : Sevm) (devm : Devm) {c : Nat} (h : Inv c 0 devm) :
    OutcomeInv sevm.benvStat.rules c (MessageOp.step sevm devm .staticcall) := by
  simp only [MessageOp.step]
  cases hac : sevm.benvStat.rules.access <;> inv_walk

/-- Every message opcode keeps the invariant. -/
theorem MessageOp.step_inv (sevm : Sevm) (devm : Devm) {c : Nat} (h : Inv c 0 devm)
    (x : MessageOp) : OutcomeInv sevm.benvStat.rules c (MessageOp.step sevm devm x) := by
  cases x
  · exact MessageOp.step_inv_create sevm devm h
  · exact MessageOp.step_inv_call sevm devm h
  · exact MessageOp.step_inv_callcode sevm devm h
  · exact MessageOp.step_inv_delegatecall sevm devm h
  · exact MessageOp.step_inv_create2 sevm devm h
  · exact MessageOp.step_inv_staticcall sevm devm h

/-- What a step keeps: a raw result on both channels, the next machine, or a spawn's saved
caller with room for one more word and its child under the caller's rules. -/
def StepInv (rules : ForkRules) (c : Nat) : Step → Prop
  | .halt ex => Both c (Inv c 0) ex
  | .next _ devm => Inv c 0 devm
  | .spawn child _ _ =>
    Inv c 1 child.checkpoint.toDevm ∧ child.message.context.block.rules = rules

theorem StepInv.ofExecution {rules : ForkRules} {c pc : Nat} {ex : Execution}
    (h : Both c (Inv c 0) ex) : StepInv rules c (Step.ofExecution pc ex) := by
  cases ex <;> exact h

theorem StepInv.ofOutcome {rules : ForkRules} {c pc : Nat} {o : MessageOp.Outcome}
    (h : OutcomeInv rules c o) : StepInv rules c (o.toStep pc) := by
  cases o with
  | done ex => exact StepInv.ofExecution h
  | spawn child p => exact h

theorem NextOp.step_inv (evm : Evm) {c : Nat} (h : Inv c 0 evm.dyna) (n : NextOp) :
    StepInv evm.sta.benvStat.rules c (NextOp.step evm n) := by
  cases n with
  | plain r => exact StepInv.ofExecution (PlainOp.run_inv evm h r)
  | message x => exact StepInv.ofOutcome (MessageOp.step_inv evm.sta evm.dyna h x)
  | push xs _ =>
    simp only [NextOp.step]
    split
    · exact StepInv.ofExecution (Both.error (Inv.weaken h (Nat.le_refl _)))
    · apply StepInv.ofExecution; inv_walk
  | _ => simp only [NextOp.step]; apply StepInv.ofExecution; inv_walk

/-- Every step keeps the invariant. -/
theorem Evm.step_inv (evm : Evm) {c : Nat} (h : Inv c 0 evm.dyna) :
    StepInv evm.sta.benvStat.rules c (Evm.step evm) := by
  unfold Evm.step
  split
  · exact (Both.error (P := Inv c 0) h : Both c (Inv c 0) (Except.error _ : Execution))
  · exact NextOp.step_inv evm h _
  · rename_i j _
    have hx := JumpOp.run_inv evm h j
    revert hx; generalize j.run evm = x
    intro hx; cases x with
    | error e => exact hx
    | ok a => exact hx
  · exact HaltOp.run_inv evm.sta evm.dyna h _

/-! ## `resume` -/

theorem Machine.creditStateGasRefund_committedSpill (amount : Nat) (m : Machine) :
    (m.creditStateGasRefund amount).stateGas.committedSpill = m.stateGas.committedSpill := rfl

theorem Machine.repayStateGasSpill_committedSpill (m : Machine) :
    m.repayStateGasSpill.stateGas.committedSpill = m.stateGas.committedSpill := rfl

/-- Absorbing a child's meters keeps the caller's committed spill. -/
theorem absorbMeters_committedSpill (rules : ForkRules) (p : Pending) (saved : Machine)
    (r : Frame.Result) :
    (absorbMeters rules p saved r).stateGas.committedSpill = saved.stateGas.committedSpill := by
  unfold absorbMeters
  cases rules.stateGas with
  | none => rfl
  | some state =>
    dsimp only
    split
    · split <;> rfl
    · rfl

theorem ReturnTarget.finish_stack (t : ReturnTarget) (r : Frame.Result) (m : Machine) :
    (t.finish r m).stack = t.status r :: m.stack := by
  unfold ReturnTarget.finish; cases t <;> rfl

theorem ReturnTarget.finish_stateGas (t : ReturnTarget) (r : Frame.Result) (m : Machine) :
    (t.finish r m).stateGas = m.stateGas := by
  unfold ReturnTarget.finish; cases t <;> rfl

/-- A resumed caller that did not fault is the merged state, given room for the push. -/
theorem resume_ok_of_room {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} (room : saved.machine.stack.length < 1024)
    {out : Except (ExceptionalHalt × Devm) Devm} (hr : resume rules p saved r = .ok out) :
    out = .ok (p.restore (resumedState rules p saved r)) := by
  have hroom : (absorbMeters rules p saved.machine r).stack.length < 1024 := by
    rw [absorbMeters_stack]; exact room
  unfold resume at hr
  cases hs : rules.stateGas with
  | none =>
    cases r <;>
      simp_all [Option.isSome_none, resumedState, returnedMachine, pure, Except.pure]
  | some state =>
    cases r <;> simp_all [Frame.Result.failed, resumedState, returnedMachine, pure,
        Except.pure, bind, Except.bind] <;> split at hr <;> simp_all [throw, throwThe, MonadExceptOf.throw]

/-- `resume` keeps the invariant: a saved caller with room for the push comes back, if the run
does not fault, as the merged state, with committed spill unchanged and the stack bound. -/
theorem resume_inv {rules : ForkRules} {p : Pending} {saved : Frame.State} {r : Frame.Result}
    {c : Nat} (h : Inv c 1 saved.toDevm) {out : Except (ExceptionalHalt × Devm) Devm}
    (hr : resume rules p saved r = .ok out) :
    out = .ok (p.restore (resumedState rules p saved r)) ∧
      Inv c 0 (p.restore (resumedState rules p saved r)) := by
  obtain ⟨h1, h2⟩ := h
  have room : saved.machine.stack.length < 1024 := by
    have : saved.machine.stack.length + 1 ≤ 1024 := h2
    omega
  refine ⟨resume_ok_of_room room hr, ?_, ?_⟩
  · show (returnedMachine rules p saved.machine r).stateGas.committedSpill = c
    rw [returnedMachine, ReturnTarget.finish_stateGas, absorbMeters_committedSpill]; exact h1
  · show (returnedMachine rules p saved.machine r).stack.length + 0 ≤ 1024
    rw [returnedMachine, ReturnTarget.finish_stack, absorbMeters_stack, List.length_cons]
    omega

/-! ## The driver -/

/-- A frame's run keeps the invariant: from a machine with committed spill `c` and at most 1024
words, every raw result the driver hands back, on both channels, has committed spill `c` and at
most 1024 words. -/
theorem execFueled_inv {c : Nat} :
    ∀ (fuel : Nat) (evm : Evm), Inv c 0 evm.dyna →
      ∀ {raw : Execution}, (execFueled evm fuel).run = some raw → Both c (Inv c 0) raw := by
  intro fuel
  induction fuel with
  | zero => intro evm _ raw h; nomatch h
  | succ fuel ih =>
    intro evm hevm raw h
    have hst := Evm.step_inv evm hevm
    rw [execFueled] at h
    rcases hs : Evm.step evm with ex | ⟨pc, devm⟩ | ⟨child, pending, pc⟩ <;>
      rw [hs] at h hst <;> dsimp only at h
    · simp only [Fueled.ofExcept_run, Option.some.injEq] at h
      rw [← h]; exact hst
    · exact ih ⟨pc, evm.sta, devm⟩ hst h
    · have hcp : Inv c 0 child.checkpoint.toDevm := Inv.weaken hst.1 (Nat.zero_le _)
      split at h
      · simp only [Fueled.exhausted_run, reduceCtorEq] at h
      · simp only [Fueled.ofExcept_run, Option.some.injEq] at h
        rw [← h]; exact hcp
      · split at h
        · simp only [Fueled.ofExcept_run, Option.some.injEq] at h
          rw [← h]; exact hcp
        · rename_i reason devm hr
          simp only [Fueled.ofExcept_run, Option.some.injEq] at h
          rw [← h]
          obtain ⟨heq, hinv⟩ := resume_inv hst.1 hr
          cases heq
        · rename_i devm hr
          obtain ⟨heq, hinv⟩ := resume_inv hst.1 hr
          cases heq
          exact ih ⟨pc, evm.sta, _⟩ hinv h

/-- `exec` keeps the invariant. -/
theorem exec_inv {c : Nat} {evm : Evm} (h : Inv c 0 evm.dyna) : Both c (Inv c 0) (exec evm) := by
  unfold exec
  cases hr : (execFueled evm (sufficientFuel evm.dyna.gasMeasure)).run with
  | none => exact h
  | some raw => exact execFueled_inv _ evm h hr

/-! ## Settlement -/

/-- What a child's result owes its caller under the caller's rules `rules`: no committed spill,
and, failed under state gas, a settled meter. -/
def ResultInv (rules : ForkRules) (r : Frame.Result) : Prop :=
  r.stateGas.committedSpill = 0 ∧ (rules.stateGas.isSome → r.failed = true → r.stateGas.Settled)

/-- A machine with committed spill `k`, on both channels of a halt-only computation. -/
def CS {ε : Type} (k : Nat) : Except (ε × Devm) Devm → Prop
  | .ok d => d.mach.stateGas.committedSpill = k
  | .error e => e.2.mach.stateGas.committedSpill = k

/-- A deposit charge keeps the committed spill, on both channels. -/
theorem chargeDeposit_committed (rules : ForkRules) (code : Bytes) {d : Devm} {k : Nat}
    (h : d.mach.stateGas.committedSpill = k) : CS k (chargeDeposit rules code d) := by
  unfold chargeDeposit Devm.chargeGas Devm.chargeStateGas
  cases rules.stateGas <;> dsimp only <;> (repeat' split) <;>
    (try simp only [bind, Except.bind]) <;> (repeat' split) <;>
    simp_all [CS, Devm.withGasLeft, Devm.setMach]

theorem Devm.setCode_mach (d : Devm) (a : Address) (code : ByteArray) :
    (d.setCode a code).mach = d.mach := rfl

/-- A deposit keeps the committed spill, on both channels. -/
theorem depositCode_committed (rules : ForkRules) (a : Address) (code : Bytes) {d : Devm}
    {k : Nat} (h : d.mach.stateGas.committedSpill = k) : CS k (depositCode rules a code d) := by
  have hc := chargeDeposit_committed rules code h
  unfold depositCode
  revert hc
  cases chargeDeposit rules code d with
  | ok d' => intro hc; simp only [Except.map, CS, Devm.setCode_mach]; exact hc
  | error e => intro hc; exact hc

theorem Devm.restoreStateGas_stateGas (d : Devm) :
    d.restoreStateGas.mach.stateGas =
      { d.mach.stateGas with left := d.mach.stateGas.baseline, spilled := 0 } := rfl

theorem Devm.forfeitRemainingGas_stateGas (d : Devm) :
    d.forfeitRemainingGas.mach.stateGas = d.mach.stateGas := rfl

/-- `settle` hands back what a child owes its caller: a raw result with no committed spill
settles to a result with none, and a failed one under state gas to a settled meter. -/
theorem settle_inv {f : Frame} {raw : Execution} (h : Both 0 (Inv 0 0) raw) {r : Frame.Result}
    (hs : settle f raw = .ok r) : ResultInv f.message.context.block.rules r := by
  unfold settle at hs
  split at hs
  · cases hs
  · cases hs
  · rename_i d
    cases hs
    have h1 : d.mach.stateGas.committedSpill = 0 := h.1
    refine ⟨?_, fun hsg _ => ?_⟩
    · show (match f.message.context.block.rules.stateGas with
          | none => d | some _ => d.restoreStateGas).mach.stateGas.committedSpill = 0
      split <;> exact h1
    · show (match f.message.context.block.rules.stateGas with
          | none => d | some _ => d.restoreStateGas).mach.stateGas.Settled
      split
      · rename_i hn; rw [hn] at hsg; cases hsg
      · exact ⟨h1, rfl, rfl⟩
  · rename_i reason d
    cases hs
    have h1 : d.mach.stateGas.committedSpill = 0 := h.1
    refine ⟨?_, fun hsg _ => ?_⟩
    · show (match f.message.context.block.rules.stateGas with
          | none => d.withGasLeft 0
          | some _ => d.restoreStateGas.forfeitRemainingGas).mach.stateGas.committedSpill = 0
      split
      · exact h1
      · exact h1
    · show (match f.message.context.block.rules.stateGas with
          | none => d.withGasLeft 0
          | some _ => d.restoreStateGas.forfeitRemainingGas).mach.stateGas.Settled
      split
      · rename_i hn; rw [hn] at hsg; cases hsg
      · exact ⟨h1, rfl, rfl⟩
  · rename_i d
    have h1 : d.mach.stateGas.committedSpill = 0 := h.1
    have hdep := depositCode_committed f.message.context.block.rules f.message.context.recipient
      (d.recordTouch f.message.context.block.rules true f.message.context.recipient).output
      (d := d.recordTouch f.message.context.block.rules true f.message.context.recipient) h1
    dsimp only at hs
    split at hs
    · cases hs
      exact ⟨h1, fun _ hf => by cases hf⟩
    · split at hs
      · rename_i s heq
        rw [heq] at hdep
        cases hs
        exact ⟨hdep, fun _ hf => by cases hf⟩
      · rename_i reason s heq
        rw [heq] at hdep
        cases hs
        have h2 : s.mach.stateGas.committedSpill = 0 := hdep
        refine ⟨?_, fun hsg _ => ?_⟩
        · show (match f.message.context.block.rules.stateGas with
              | none => s.withGasLeft 0
              | some _ => s.restoreStateGas.forfeitRemainingGas).mach.stateGas.committedSpill = 0
          split
          · exact h2
          · exact h2
        · show (match f.message.context.block.rules.stateGas with
              | none => s.withGasLeft 0
              | some _ => s.restoreStateGas.forfeitRemainingGas).mach.stateGas.Settled
          split
          · rename_i hn; rw [hn] at hsg; cases hsg
          · exact ⟨h2, rfl, rfl⟩

/-! ## Entry -/

/-- A precompile keeps the invariant: it only charges gas and sets the output. -/
theorem executePrecompile_inv {c : Nat} {evm : Evm} (h : Inv c 0 evm.dyna) (adr : Address) :
    Both c (Inv c 0) (executePrecompile evm adr) := by
  unfold executePrecompile applyPrecompileResult
  split
  · exact Inv.keep h rfl rfl (Nat.le_refl _)
  · exact Inv.keep h rfl rfl (Nat.le_refl _)

/-- The machine a frame is entered with is its start machine. -/
theorem enterWith_run_mach {f : Frame} {start : Devm} {evm : Evm}
    (he : enterWith f start = .run evm) : evm.dyna.mach = start.mach := by
  unfold enterWith at he
  dsimp only at he
  split at he
  · cases he
  · split at he
    · split at he
      · cases he
      · cases he; rfl
    · cases he; rfl

theorem enterWith_run_inv {c : Nat} {f : Frame} {start : Devm} {evm : Evm} (h : Inv c 0 start)
    (he : enterWith f start = .run evm) : Inv c 0 evm.dyna :=
  Inv.of_mach h (enterWith_run_mach he) (Nat.le_refl _)

/-- A frame finished at entry (a precompile) hands back what a child owes its caller. -/
theorem enterWith_done_inv {f : Frame} {start : Devm} {r : Frame.Result} (h : Inv 0 0 start)
    (he : enterWith f start = .done (.ok r)) : ResultInv f.message.context.block.rules r := by
  unfold enterWith at he
  dsimp only at he
  split at he
  · cases he
  · split at he
    · split at he
      · have hset := Frame.Entry.done.inj he
        exact settle_inv (executePrecompile_inv (Inv.of_mach h rfl (Nat.le_refl _)) _) hset
      · cases he
    · cases he

/-- A spawned child starts with an empty stack and no committed spill. -/
theorem Frame.start_inv (f : Frame) : Inv 0 0 f.start := ⟨rfl, Nat.zero_le _⟩

end RunInvariants

open RunInvariants

/-! ## A child's result, as the driver names it -/

/-- `r` is a result `child` hands back to its caller in the driver: finished at entry (a
precompile), or run from its entered machine and settled. -/
inductive Frame.Returns (child : Frame) : Frame.Result → Prop
  | done {r : Frame.Result} : enter child = .done (.ok r) → Frame.Returns child r
  | run {r : Frame.Result} {cevm : Evm} {fuel : Nat} {raw : Execution} :
      enter child = .run cevm → (execFueled cevm fuel).run = some raw → settle child raw = .ok r →
      Frame.Returns child r

/-- What the driver resumes a caller with is a result its child returns. -/
theorem Frame.Returns.of_driver {child : Frame} {fuel : Nat} {r : Frame.Result}
    (h : (match enter child with
      | .done result => some result
      | .run childEvm => ((execFueled childEvm fuel).run).map (settle child)) = some (.ok r)) :
    Frame.Returns child r := by
  rcases he : enter child with cevm | result <;> rw [he] at h <;> dsimp only at h
  · rcases hc : (execFueled cevm fuel).run with _ | raw <;> rw [hc] at h
    · nomatch h
    · simp only [Option.map, Option.some.injEq] at h
      exact .run he hc h
  · cases h; exact .done he

/-- A child run through `exec` and settled returns that result. -/
theorem Frame.Returns.of_exec {child : Frame} {cevm : Evm} {r : Frame.Result}
    (he : enter child = .run cevm) (hs : settle child (exec cevm) = .ok r) :
    Frame.Returns child r := by
  unfold exec at hs
  rcases hc : (execFueled cevm (sufficientFuel cevm.dyna.gasMeasure)).run with _ | raw <;>
    rw [hc] at hs
  · simp only [settle] at hs; cases hs
  · exact .run he hc hs

/-- One nonterminal instruction run to its next machine on the four-part message call, with any
child it needs: the step goes on in place, or it spawns a child that returns a result and the
caller resumes with it. The four-part counterpart of `NextOp.Run`. -/
def NextOp.Run (sevm : Sevm) (devm : Devm) (n : NextOp) (devm' : Devm) : Prop :=
  ∃ pc pc', NextOp.step ⟨pc, sevm, devm⟩ n = .next pc' devm' ∨
    ∃ child pending r, NextOp.step ⟨pc, sevm, devm⟩ n = .spawn child pending pc' ∧
      Frame.Returns child r ∧
      resume sevm.benvStat.rules pending child.checkpoint r = .ok (.ok devm')

/-- A returned result owes its caller what `resume` checks: no committed spill, and, failed under
the child's state-gas rules, a settled meter. -/
theorem Frame.Returns.inv {child : Frame} {r : Frame.Result} (h : Frame.Returns child r) :
    ResultInv child.message.context.block.rules r := by
  cases h with
  | done he => exact enterWith_done_inv (Frame.start_inv child) he
  | run he hrun hs =>
    exact settle_inv (execFueled_inv _ _ (enterWith_run_inv (Frame.start_inv child) he) hrun) hs

/-- The uncommitted-child invariant, for a child entered and run: a failed result under state gas
is settled. -/
theorem settled_of_enter_run {child : Frame} {cevm : Evm} {r : Frame.Result}
    (he : enter child = .run cevm) (hs : settle child (exec cevm) = .ok r)
    (failed : r.failed = true) :
    child.message.context.block.rules.stateGas.isSome → r.stateGas.Settled :=
  fun h => ((Frame.Returns.of_exec he hs).inv).2 h failed

/-- The uncommitted-child invariant, for a child entered and run: no committed spill. -/
theorem committed_of_enter_run {child : Frame} {cevm : Evm} {r : Frame.Result}
    (he : enter child = .run cevm) (hs : settle child (exec cevm) = .ok r) :
    r.stateGas.committedSpill = 0 :=
  ((Frame.Returns.of_exec he hs).inv).1

/-! ## Reached machines -/

/-- The machines a run from `start` passes through before a step: the start, the machine after a
step that goes on, a spawned child's entered machine, and the caller resumed with a result its
child returns. -/
inductive Evm.Reaches (start : Evm) : Evm → Prop
  | refl : Evm.Reaches start start
  | next {evm : Evm} {pc : Nat} {devm : Devm} :
      Evm.Reaches start evm → Evm.step evm = .next pc devm →
      Evm.Reaches start ⟨pc, evm.sta, devm⟩
  | enter {evm cevm : Evm} {child : Frame} {p : Pending} {pc : Nat} :
      Evm.Reaches start evm → Evm.step evm = .spawn child p pc → enter child = .run cevm →
      Evm.Reaches start cevm
  | resume {evm : Evm} {child : Frame} {p : Pending} {pc : Nat} {r : Frame.Result}
      {devm : Devm} :
      Evm.Reaches start evm → Evm.step evm = .spawn child p pc → Frame.Returns child r →
      resume evm.sta.benvStat.rules p child.checkpoint r = .ok (.ok devm) →
      Evm.Reaches start ⟨pc, evm.sta, devm⟩

/-- Every reached machine satisfies the invariant for some committed spill. -/
theorem Evm.Reaches.inv {start evm : Evm} (h0 : start.dyna.stack.length ≤ 1024)
    (h : start.Reaches evm) : ∃ c, Inv c 0 evm.dyna := by
  induction h with
  | refl => exact ⟨_, rfl, h0⟩
  | next _ hs ih =>
    obtain ⟨c, hc⟩ := ih
    have := Evm.step_inv _ hc
    rw [hs] at this
    exact ⟨c, this⟩
  | enter _ _ he _ => exact ⟨0, enterWith_run_inv (Frame.start_inv _) he⟩
  | resume _ hs _ hres ih =>
    obtain ⟨c, hc⟩ := ih
    have := Evm.step_inv _ hc
    rw [hs] at this
    obtain ⟨heq, hinv⟩ := resume_inv this.1 hres
    cases heq
    exact ⟨c, hinv⟩

/-- **The stack bound.** Every machine a run reaches, from a start with at most 1024 words, holds
at most 1024 words before its step. -/
theorem Evm.Reaches.stack_le {start evm : Evm} (h0 : start.dyna.stack.length ≤ 1024)
    (h : start.Reaches evm) : evm.dyna.stack.length ≤ 1024 := by
  obtain ⟨c, _, hs⟩ := h.inv h0
  exact hs

/-- `room`, derived: a reached machine that spawns saves a caller with room for the push. -/
theorem Evm.Reaches.room {start evm : Evm} (h0 : start.dyna.stack.length ≤ 1024)
    (h : start.Reaches evm) {child : Frame} {p : Pending} {pc : Nat}
    (hs : Evm.step evm = .spawn child p pc) : child.checkpoint.machine.stack.length < 1024 := by
  obtain ⟨c, hc⟩ := h.inv h0
  have := Evm.step_inv _ hc
  rw [hs] at this
  have h2 : child.checkpoint.machine.stack.length + 1 ≤ 1024 := this.1.2
  omega

/-- A spawned child runs under its caller's rules. -/
theorem Evm.Reaches.child_rules {start evm : Evm} (h0 : start.dyna.stack.length ≤ 1024)
    (h : start.Reaches evm) {child : Frame} {p : Pending} {pc : Nat}
    (hs : Evm.step evm = .spawn child p pc) :
    child.message.context.block.rules = evm.sta.benvStat.rules := by
  obtain ⟨c, hc⟩ := h.inv h0
  have := Evm.step_inv _ hc
  rw [hs] at this
  exact this.2

/-- `resume_failed` at a reached spawn, with `room` and `settled` discharged by the run
invariants. -/
theorem Evm.Reaches.resume_failed {start evm : Evm} (h0 : start.dyna.stack.length ≤ 1024)
    (h : start.Reaches evm) {child : Frame} {p : Pending} {pc : Nat}
    (hs : Evm.step evm = .spawn child p pc) {r : Frame.Result} (hr : Frame.Returns child r)
    (failed : r.failed = true) :
    Jaune.resume evm.sta.benvStat.rules p child.checkpoint r = .ok (.ok (p.restore
      { machine := returnedMachine evm.sta.benvStat.rules p child.checkpoint.machine r
        world := child.checkpoint.world
        substate := match evm.sta.benvStat.rules.stateGas with
          | none => child.checkpoint.substate.keepTouch r.trail
          | some _ => child.checkpoint.substate
        trail := child.checkpoint.trail.absorb r.trail })) := by
  have hrules := h.child_rules h0 hs
  have hinv := hr.inv
  rw [hrules] at hinv
  exact Jaune.resume_failed _ p child.checkpoint r failed (h.room h0 hs) (fun hg => hinv.2 hg failed)

/-- `resume_success` at a reached spawn, with `room` and `committed` discharged by the run
invariants. -/
theorem Evm.Reaches.resume_success {start evm : Evm} (h0 : start.dyna.stack.length ≤ 1024)
    (h : start.Reaches evm) {child : Frame} {p : Pending} {pc : Nat}
    (hs : Evm.step evm = .spawn child p pc) {output : Bytes} {gasLeft : Nat}
    {stateGas : StateGasMeter} {world : World} {substate : Substate} {trail : Trail}
    (hr : Frame.Returns child (.success output gasLeft stateGas world substate trail)) :
    Jaune.resume evm.sta.benvStat.rules p child.checkpoint
        (.success output gasLeft stateGas world substate trail) =
      .ok (.ok (p.restore
        { machine := returnedMachine evm.sta.benvStat.rules p child.checkpoint.machine
            (.success output gasLeft stateGas world substate trail)
          world := world
          substate := child.checkpoint.substate.absorb evm.sta.benvStat.rules substate
          trail := child.checkpoint.trail.absorb trail })) :=
  Jaune.resume_success _ p child.checkpoint output gasLeft stateGas world substate trail
    (h.room h0 hs) (fun _ => hr.inv.1)


end Jaune
