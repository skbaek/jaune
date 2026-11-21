import Jaune.MessageCall.RunInvariants
import Jaune.MessageCall.ResumeFacts
import Jaune.MessageCall.SpawnFacts
import Jaune.MessageCall.Totality

/-! The stack and committed-spill invariants through child entry, execution, settlement and
resumption. -/
namespace Jaune

open Jaune

namespace RunInvariants

/-- Resuming a valid caller with room for the return push gives the successful merge whenever
the child has passed the meter checks. -/
theorem resume_ok_of_room {rules : ForkRules} {p : Pending} {saved : Frame.State} {r : Frame.Result}
    (room : saved.machine.stack.length < 1024) {x} (hr : resume rules p saved r = .ok x) :
    x = .ok (resumedState rules p saved r) := by
  have valid (hg : rules.stateGas.isSome) :
      ¬ (if r.failed then ¬r.stateGas.Settled else r.stateGas.committedSpill ≠ 0) := by
    intro bad
    obtain ⟨_, hf⟩ := resume_unsettled p saved r hg bad
    rw [hr] at hf
    cases hf
  have ok := resume_of_room rules p saved r room
    (fun hg hf => by simpa [hf] using valid hg)
    (fun hg hf => by simpa [hf] using valid hg)
  exact Except.ok.inj (hr.symm.trans ok)

theorem absorbMeters_committedSpill (rules : ForkRules) (p : Pending) (saved : Machine)
    (r : Frame.Result) :
    (absorbMeters rules p saved r).stateGas.committedSpill = saved.stateGas.committedSpill := by
  unfold absorbMeters
  cases rules.stateGas with
  | none => rfl
  | some state => dsimp only; split <;> first | rfl | (split <;> rfl)

theorem resume_invariant {rules : ForkRules} {p : Pending} {saved : Frame.State} {r : Frame.Result}
    {c : Nat} (h : StateInvariant c 1 saved) {x} (hr : resume rules p saved r = .ok x) :
    x = .ok (resumedState rules p saved r) ∧ StateInvariant c 0 (resumedState rules p saved r) := by
  have hl := h.2
  have room : saved.machine.stack.length < 1024 := by omega
  refine ⟨resume_ok_of_room room hr, ?_⟩
  change MachineInvariant c 0 (finishTarget p.target r (absorbMeters rules p saved.machine r))
  have hm := absorbMeters_committedSpill rules p saved.machine r
  have hs := absorbMeters_stack rules p saved.machine r
  cases p.target <;> constructor
  all_goals first
    | exact hm.trans h.1
    | (change (_ :: (absorbMeters rules p saved.machine r).stack).length + 0 ≤ 1024
       rw [hs, List.length_cons]; omega)

/-- A bounded execution that returns an exit preserves the original frame's invariant. -/
theorem execFueled_invariant (fuel : Nat) (run : Frame.Running) {c : Nat} (hi : StateInvariant c 0 run.state)
    {e : Frame.Exit} (h : (execFueled run fuel).run = some (.ok e)) : StateInvariant c 0 e.state := by
  induction fuel generalizing run with
  | zero => nomatch h
  | succ fuel ih =>
    rw [execFueled] at h
    rcases hs : step run with fault | exit | ⟨pc, s⟩ | ⟨child, p, pc⟩ <;> rw [hs] at h
    · cases h
    · cases h; exact step_invariant hi hs
    · exact ih ⟨pc, run.context, s⟩ (step_invariant hi hs) h
    · have saved : StateInvariant c 1 child.checkpoint := step_invariant hi hs
      dsimp only at h
      split at h
      · cases h
      · cases h
      · split at h
        · cases h
        · rename_i _ s hr
          obtain ⟨heq, _⟩ := resume_invariant saved hr
          cases heq
        · rename_i s hr
          obtain ⟨heq, hinv⟩ := resume_invariant saved hr
          cases heq
          exact ih ⟨pc, run.context, _⟩ hinv h

theorem exec_invariant {run : Frame.Running} {c : Nat} (h : StateInvariant c 0 run.state)
    {e : Frame.Exit} (he : exec run = .ok e) : StateInvariant c 0 e.state :=
  execFueled_invariant _ run h ((execFueled_run_sufficientFuel run).trans (congrArg some he))

/-- A child promises its caller zero committed spill, and a settled failure under state gas. -/
def ResultInvariant (rules : ForkRules) (r : Frame.Result) : Prop :=
  r.stateGas.committedSpill = 0 ∧ (rules.stateGas.isSome → r.failed → r.stateGas.Settled)

private theorem chargeDeposit_invariant (rules : ForkRules) (code : Bytes) {s : Frame.State} (h : StateInvariant 0 0 s) :
    Walk (StateInvariant 0 0) (StateInvariant 0 0) (chargeDeposit rules code s) := by
  have chargeSize (bytes : Bytes) : Walk (StateInvariant 0 0) (StateInvariant 0 0) (do
      let t ← s.chargeGas (bytes.length * Gas.codeDeposit)
      if rules.code.maxCodeSize < bytes.length then .error (.outOfGas .none, t) else .ok t) := by
    refine Walk.bind (State.chargeGas_invariant _ h) ?_
    intro t ht
    split <;> exact ht
  unfold chargeDeposit
  dsimp only
  repeat' (first | exact h | apply chargeSize | split)
  all_goals
    refine Walk.bind (State.chargeGas_invariant _ h) ?_
    intro t ht
    exact State.chargeStateGas_invariant _ ht

private theorem depositCode_invariant (rules : ForkRules) (recipient : Address) (code : Bytes)
    {s : Frame.State} (h : StateInvariant 0 0 s) : Walk (StateInvariant 0 0) (StateInvariant 0 0) (depositCode rules recipient code s) := by
  have hc := chargeDeposit_invariant rules code h
  unfold depositCode
  cases he : chargeDeposit rules code s <;> rw [he] at hc <;> exact hc

private theorem haltedResult_invariant (rules : ForkRules) (s : Frame.State) (reason : ExceptionalHalt)
    (trail : Trail) (h : StateInvariant 0 0 s) : ResultInvariant rules (.halt reason (match rules.stateGas with
      | none => s.machine.forfeitRemainingGas
      | some _ => s.machine.restoreStateGas.forfeitRemainingGas).stateGas trail) := by
  cases hs : rules.stateGas with
  | none => exact ⟨h.1, fun hg => by simp [hs] at hg⟩
  | some _ => exact ⟨h.1, fun _ _ => ⟨h.1, rfl, rfl⟩⟩

theorem settle_invariant {f : Frame} {e : Frame.Exit} (hi : StateInvariant 0 0 e.state) {r : Frame.Result}
    (h : settle f e = .ok r) : ResultInvariant f.message.context.block.rules r := by
  cases e with
  | halted reason s => cases h; exact haltedResult_invariant _ _ _ _ hi
  | reverted bytes s =>
    cases h
    cases hs : f.message.context.block.rules.stateGas with
    | none => exact ⟨hi.1, fun hg => by simp [hs] at hg⟩
    | some _ => exact ⟨hi.1, fun _ _ => ⟨hi.1, rfl, rfl⟩⟩
  | finished bytes s =>
    simp only [settle] at h
    split at h
    · cases h; exact ⟨hi.1, fun _ h => by cases h⟩
    · have dep := depositCode_invariant f.message.context.block.rules f.message.context.recipient bytes
        (s := s.recordTouch f.message.context.block.rules true f.message.context.recipient) hi
      split at h
      · rename_i t ht; rw [ht] at dep; cases h
        exact ⟨(show StateInvariant 0 0 t from dep).1, fun _ h => by cases h⟩
      · rename_i reason t ht; rw [ht] at dep; cases h
        exact haltedResult_invariant _ _ _ _ dep

theorem enterWith_run_invariant {f : Frame} {start : Frame.State} {r : Frame.Running} {c : Nat}
    (hi : StateInvariant c 0 start) (h : enterWith f start = .run r) : StateInvariant c 0 r.state := by
  unfold enterWith at h
  dsimp only at h
  repeat' split at h
  all_goals cases h
  all_goals exact hi

private theorem runPrecompile_invariant {r : Frame.Running} (a : Address) {e : Frame.Exit} {c : Nat}
    (hi : StateInvariant c 0 r.state) (h : runPrecompile r a = .ok e) : StateInvariant c 0 e.state := by
  unfold runPrecompile Frame.Exit.ofPrecompileResult at h
  split at h
  · cases h; exact hi
  · split at h <;> cases h <;> exact hi

theorem enterWith_done_invariant {f : Frame} {start : Frame.State} {r : Frame.Result} (hi : StateInvariant 0 0 start)
    (h : enterWith f start = .done (.ok r)) : ResultInvariant f.message.context.block.rules r := by
  unfold enterWith at h
  dsimp only at h
  cases hw : f.message.transfer f.enteredWorld with
  | error fault => rw [hw] at h; cases h
  | ok world =>
    rw [hw] at h
    cases ha : f.message.codeAddress with
    | none => rw [ha] at h; contradiction
    | some a =>
      rw [ha] at h
      dsimp only at h
      split at h
      · simp only [Frame.Entry.done.injEq] at h
        cases hp : runPrecompile (Frame.entered f start world) a with
        | error fault => rw [hp] at h; contradiction
        | ok e => rw [hp] at h; exact settle_invariant (runPrecompile_invariant _ hi hp) h
      · contradiction

theorem Frame.start_invariant (f : Frame) : StateInvariant 0 0 f.startState := ⟨rfl, Nat.zero_le _⟩

end RunInvariants

open RunInvariants

/-- Results a spawned child can hand back to the native driver. -/
inductive Frame.Returns (child : Frame) : Frame.Result → Prop
  | done {r} : enter child = .done (.ok r) → Frame.Returns child r
  | run {r} {cr : Frame.Running} {fuel : Nat} {e : Frame.Exit} :
      enter child = .run cr → (execFueled cr fuel).run = some (.ok e) →
      settle child e = .ok r → Frame.Returns child r

theorem Frame.Returns.of_driver {child : Frame} {fuel : Nat} {r : Frame.Result}
    (h : (match enter child with
      | .done result => some result
      | .run cr => (execFueled cr fuel).run.map (· >>= settle child)) = some (.ok r)) :
    Frame.Returns child r := by
  cases he : enter child with
  | done result => rw [he] at h; cases h; exact .done he
  | run cr =>
    simp only [he] at h
    cases hx : (execFueled cr fuel).run with
    | none => rw [hx] at h; cases h
    | some x =>
      rw [hx] at h
      cases x with
      | error fault => cases h
      | ok e => exact .run he hx (Option.some.inj h)

theorem Frame.Returns.of_exec {child : Frame} {cr : Frame.Running} {r : Frame.Result}
    (he : enter child = .run cr) (hr : (exec cr >>= settle child) = .ok r) : Frame.Returns child r := by
  apply of_driver (fuel := sufficientFuel cr.state.machine.gasMeasure)
  rw [he]
  simp only [execFueled_run_sufficientFuel, Option.map_some, hr]

theorem Frame.Returns.resultInvariant {child : Frame} {r : Frame.Result} (h : Frame.Returns child r) :
    ResultInvariant child.message.context.block.rules r := by
  cases h with
  | done he => exact enterWith_done_invariant (RunInvariants.Frame.start_invariant child) he
  | run he hx hs => exact settle_invariant (execFueled_invariant _ _ (enterWith_run_invariant (RunInvariants.Frame.start_invariant child) he) hx) hs

theorem settled_of_enter_run {child : Frame} {cr : Frame.Running} {r : Frame.Result}
    (he : enter child = .run cr) (hr : (exec cr >>= settle child) = .ok r) (failed : r.failed) :
    child.message.context.block.rules.stateGas.isSome → r.stateGas.Settled :=
  fun hg => (Frame.Returns.resultInvariant (Frame.Returns.of_exec he hr)).2 hg failed

theorem committed_of_enter_run {child : Frame} {cr : Frame.Running} {r : Frame.Result}
    (he : enter child = .run cr) (hr : (exec cr >>= settle child) = .ok r) :
    r.stateGas.committedSpill = 0 :=
  (Frame.Returns.resultInvariant (Frame.Returns.of_exec he hr)).1

/-- A nonterminal instruction running directly or through a completed child. -/
def NextOp.Run (ctx : CallContext) (s : Frame.State) (n : Jaune.NextOp) (t : Frame.State) : Prop :=
  ∃ pc pc', NextOp.step ⟨pc, ctx, s⟩ n = .next pc' t ∨
    ∃ child p r, NextOp.step ⟨pc, ctx, s⟩ n = .spawn child p pc' ∧ Frame.Returns child r ∧
      resume ctx.block.rules p child.checkpoint r = .ok (.ok t)

/-- Running frames reached by local steps, child entries or caller resumptions. -/
inductive Frame.Running.Reaches (start : Frame.Running) : Frame.Running → Prop
  | refl : Frame.Running.Reaches start start
  | next {run : Frame.Running} {pc : Nat} {s : Frame.State} :
      Frame.Running.Reaches start run → step run = .ok (.next pc s) →
      Frame.Running.Reaches start ⟨pc, run.context, s⟩
  | enter {run cr : Frame.Running} {child : Frame} {p : Pending} {pc : Nat} :
      Frame.Running.Reaches start run → step run = .ok (.spawn child p pc) → enter child = .run cr →
      Frame.Running.Reaches start cr
  | resume {run : Frame.Running} {child : Frame} {p : Pending} {pc : Nat} {r : Frame.Result}
      {s : Frame.State} : Frame.Running.Reaches start run → step run = .ok (.spawn child p pc) →
      Frame.Returns child r → resume run.context.block.rules p child.checkpoint r = .ok (.ok s) →
      Frame.Running.Reaches start ⟨pc, run.context, s⟩

theorem Frame.Running.Reaches.stateInvariant {start run : Frame.Running} (h0 : start.state.stack.length ≤ 1024)
    (h : Frame.Running.Reaches start run) : ∃ c, StateInvariant c 0 run.state := by
  induction h with
  | refl => exact ⟨_, rfl, h0⟩
  | next _ hs ih => obtain ⟨c, hc⟩ := ih; exact ⟨c, step_invariant hc hs⟩
  | enter _ _ he _ => exact ⟨0, enterWith_run_invariant (RunInvariants.Frame.start_invariant _) he⟩
  | resume _ hs _ hr ih =>
    obtain ⟨c, hc⟩ := ih
    have saved := step_invariant hc hs
    obtain ⟨heq, hinv⟩ := resume_invariant saved hr
    cases heq
    exact ⟨c, hinv⟩

theorem Frame.Running.Reaches.stack_le {start run : Frame.Running} (h0 : start.state.stack.length ≤ 1024)
    (h : Frame.Running.Reaches start run) : run.state.stack.length ≤ 1024 := by
  obtain ⟨_, _, hl⟩ := h.stateInvariant h0
  exact hl

theorem Frame.Running.Reaches.room {start run : Frame.Running} (h0 : start.state.stack.length ≤ 1024)
    (h : Frame.Running.Reaches start run) {child : Frame} {p : Pending} {pc : Nat}
    (hs : step run = .ok (.spawn child p pc)) : child.checkpoint.machine.stack.length < 1024 := by
  obtain ⟨_, hc⟩ := h.stateInvariant h0
  have saved := step_invariant hc hs
  have hl := (show StateInvariant _ 1 child.checkpoint from saved).2
  omega

/-- Every spawned child inherits the caller's rules. This depends only on the spawning step. -/
theorem step_spawn_rules {run : Frame.Running} {child : Frame} {p : Pending} {pc : Nat}
    (hs : step run = .ok (.spawn child p pc)) :
    child.message.context.block.rules = run.context.block.rules := by
  obtain ⟨_, hx⟩ := step_spawn_message hs
  rw [(MessageOp.step_spawn_context hx).1]

/-- S3 for a returned failure at a reached spawn. Both the room and meter premises follow from
the execution. -/
theorem Frame.Running.Reaches.resume_failed {start run : Frame.Running} (h0 : start.state.stack.length ≤ 1024)
    (h : Frame.Running.Reaches start run) {child : Frame} {p : Pending} {pc : Nat}
    (hs : step run = .ok (.spawn child p pc)) {r : Frame.Result} (hr : Frame.Returns child r)
    (failed : r.failed) :
    Jaune.resume run.context.block.rules p child.checkpoint r = .ok (.ok
      { machine := returnedMachine run.context.block.rules p child.checkpoint.machine r
        world := child.checkpoint.world
        substate := match run.context.block.rules.stateGas with
          | none => child.checkpoint.substate.keepTouch r.trail
          | some _ => child.checkpoint.substate
        trail := child.checkpoint.trail.absorb r.trail }) := by
  have hi := hr.resultInvariant
  rw [step_spawn_rules hs] at hi
  exact Jaune.resume_failed _ _ _ _ failed (h.room h0 hs) (fun hg => hi.2 hg failed)

/-- S3 for a returned success at a reached spawn. Both the room and meter premises follow from
the execution. -/
theorem Frame.Running.Reaches.resume_success {start run : Frame.Running} (h0 : start.state.stack.length ≤ 1024)
    (h : Frame.Running.Reaches start run) {child : Frame} {p : Pending} {pc : Nat}
    (hs : step run = .ok (.spawn child p pc)) {output : Bytes} {gasLeft : Nat}
    {sg : StateGasMeter} {world : World} {sub : Substate} {trail : Trail}
    (hr : Frame.Returns child (.success output gasLeft sg world sub trail)) :
    Jaune.resume run.context.block.rules p child.checkpoint (.success output gasLeft sg world sub trail) =
      .ok (.ok
        { machine := returnedMachine run.context.block.rules p child.checkpoint.machine
            (.success output gasLeft sg world sub trail)
          world := world
          substate := child.checkpoint.substate.absorb run.context.block.rules sub
          trail := child.checkpoint.trail.absorb trail }) :=
  Jaune.resume_success _ _ _ _ _ _ _ _ _ (h.room h0 hs) (fun _ => hr.resultInvariant.1)

end Jaune
