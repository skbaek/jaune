import Jaune.Exec
import Jaune.MessageCall.DriverInvariants

/-! Stack and bounded output-window effects of the actual STATICCALL instruction, on every fork. -/

namespace Jaune

private theorem push_effects {pre post : Devm} {flag : U256} (h : pre.push flag = .ok post) :
    post.stack = flag :: pre.stack ∧ post.memory = pre.memory := by
  rw [Devm.push_def] at h
  by_cases room : pre.stack.length < 1024
  · simp only [Except.assert, ite_eq_left room, bind, Except.bind, Except.ok.injEq] at h
    subst post
    exact ⟨rfl, rfl⟩
  · simp only [Except.assert, ite_eq_right room, bind, Except.bind] at h
    contradiction

private def CallEffects (pre post : Devm) (oi os : Nat) : Prop :=
  (∃ flag, post.stack = flag :: pre.stack) ∧
    ∃ bytes : Bytes, bytes.length ≤ os ∧ post.memory = pre.memory.write oi bytes

private theorem charge_effects {pre post : Devm} {cost : Nat} (h : chargeGas cost pre = .ok post) :
    post.stack = pre.stack ∧ post.memory = pre.memory := by
  rw [chargeGas_def] at h
  unfold safeSub at h
  split at h
  · cases h
  · cases h
    exact ⟨rfl, rfl⟩

private theorem delegation_effects (rules : ForkRules) (pre : Devm) (target : Address) :
    (rules.accessDelegation pre target).2.2.2.2.stack = pre.stack ∧
      (rules.accessDelegation pre target).2.2.2.2.memory = pre.memory := by
  unfold ForkRules.accessDelegation
  split
  · unfold GasSchedule.accessDelegation
    dsimp only
    split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem complete_delegation_effects (pre : Devm) (delegated : Bool) (target : Address) :
    (completeDelegationAccess pre delegated target).2.stack = pre.stack ∧
      (completeDelegationAccess pre delegated target).2.memory = pre.memory := by
  cases delegated <;> exact ⟨rfl, rfl⟩

/-! ### Over the four-part message call

The effects for a STATICCALL run under `NextOp.Run`: the step goes on in place, or it
spawns a child whose returned result the caller resumes with. -/

/-- A message opcode's outcome brings the caller to `post`: finished in place, or a spawned child
returns a result and the caller resumes. -/
private def OutcomeRuns (rules : ForkRules) (o : MessageOp.Outcome) (post : Devm) : Prop :=
  o = .done (.ok post) ∨
    ∃ child pending r, o = .spawn child pending ∧
      resume rules pending child.checkpoint r = .ok (.ok post)

private theorem absorbMeters_memory_eq (rules : ForkRules) (p : Pending) (m : Machine)
    (r : Frame.Result) : (absorbMeters rules p m r).memory = m.memory := by
  unfold absorbMeters Machine.creditStateGasRefund Machine.repayStateGasSpill
  repeat' split
  all_goals rfl

/-- A caller that resumes without halting has the status pushed on its saved stack and, for a
call, the reply written into its saved memory. -/
private theorem resume_ok_effects {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {post : Devm} (h : resume rules p saved r = .ok (.ok post)) :
    post.stack = p.target.status r :: saved.machine.stack ∧
      post.memory = (p.target.finish r saved.machine).memory := by
  by_cases room : saved.machine.stack.length < 1024
  · cases RunInvariants.resume_ok_of_room room h
    refine ⟨?_, ?_⟩
    · show (returnedMachine rules p saved.machine r).stack = _
      rw [returnedMachine, RunInvariants.ReturnTarget.finish_stack, absorbMeters_stack]
    · show (returnedMachine rules p saved.machine r).memory = _
      unfold returnedMachine ReturnTarget.finish
      cases p.target <;> simp only [absorbMeters_memory_eq]
  · exfalso
    have hroom : ¬ (absorbMeters rules p saved.machine r).stack.length < 1024 := by
      rw [absorbMeters_stack]; exact room
    unfold resume at h
    simp only [absorbMeters_stack, room, ↓reduceIte, pure, Except.pure, bind, Except.bind] at h
    repeat' split at h
    all_goals simp_all [throw, throwThe, MonadExceptOf.throw]

private theorem generic_call_runs_effects {sevm : Sevm} {pre post : Devm} {gas reservoir : Nat}
    {value : U256} {caller target codeAddress : Address} {transfer static : Bool}
    {ii size oi os : Nat} {code : ByteArray} {disable charged insufficient : Bool}
    (state : Option StateGasRules)
    (h : OutcomeRuns sevm.benvStat.rules (match state with
      | none => genericCall.step sevm pre gas value caller target codeAddress transfer static
          ii size oi os code disable
      | some state => genericCallAmsterdam.step sevm state pre gas reservoir value caller target
          codeAddress transfer static ii size oi os code disable charged insufficient) post) :
    CallEffects pre post oi os := by
  rcases h with h | ⟨child, pending, r, h, hr⟩
  · cases state with
    | none =>
      simp only [genericCall.step] at h
      split at h
      · simp only [MessageOp.Outcome.ofExcept, bind, Except.bind] at h
        split at h
        · cases h
        · rename_i hp
          split at hp
          · cases hp
          · rename_i pushed hpush
            cases hp; cases h
            obtain ⟨stack, memory⟩ := push_effects hpush
            exact ⟨⟨0, stack⟩, ⟨[], Nat.zero_le _, memory⟩⟩
      · cases h
    | some state =>
      simp only [genericCallAmsterdam.step] at h
      split at h
      · simp only [MessageOp.Outcome.ofExcept, bind, Except.bind] at h
        split at h
        · cases h
        · rename_i hp
          split at hp
          · cases hp
          · rename_i pushed hpush
            cases hp; cases h
            obtain ⟨stack, memory⟩ := push_effects hpush
            cases charged <;> exact ⟨⟨0, stack⟩, ⟨[], Nat.zero_le _, memory⟩⟩
      · cases h
  · have spawn : pending.target = .call oi os ∧
        child.checkpoint = Frame.State.ofDevm (pre.withReturnData []) := by
      cases state with
      | none =>
        simp only [genericCall.step] at h
        split at h
        · simp only [MessageOp.Outcome.ofExcept, bind, Except.bind] at h
          split at h
          · cases h
          · rename_i hp
            split at hp <;> cases hp
            cases h
        · cases h; exact ⟨rfl, rfl⟩
      | some state =>
        simp only [genericCallAmsterdam.step] at h
        split at h
        · simp only [MessageOp.Outcome.ofExcept, bind, Except.bind] at h
          split at h
          · cases h
          · rename_i hp
            split at hp <;> cases hp
            cases h
        · cases h; exact ⟨rfl, rfl⟩
    obtain ⟨htarget, hcp⟩ := spawn
    obtain ⟨hstack, hmemory⟩ := resume_ok_effects hr
    rw [hcp, htarget] at *
    refine ⟨⟨_, hstack⟩, ⟨r.output.take os, List.length_take_le _ _, ?_⟩⟩
    rw [hmemory]
    rfl

/-- Every STATICCALL run on the four-part message call consumes its six operands, pushes one
status word and writes only a bounded reply to the prepaid output window, on every fork. -/
theorem NextOp.staticcall_run_effects {sevm : Sevm} {pre post : Devm}
    {gas target ii size oi os : U256} {rest : List U256}
    (stack : pre.stack = gas :: target :: ii :: size :: oi :: os :: rest)
    (run : NextOp.Run sevm pre (.message .staticcall) post) :
    (∃ flag, post.stack = flag :: rest) ∧
      ∃ bytes : Bytes, bytes.length ≤ os.toNat ∧
        post.memory = (pre.memory.extends [(ii.toNat, size.toNat), (oi.toNat, os.toNat)]).write oi.toNat bytes := by
  have run : OutcomeRuns sevm.benvStat.rules (MessageOp.step sevm pre .staticcall) post := by
    obtain ⟨pc, pc', h | ⟨child, pending, r, h, -, hr⟩⟩ := run
    · simp only [NextOp.step] at h
      rcases ho : MessageOp.step sevm pre .staticcall with ex | ⟨child, pending⟩ <;>
        rw [ho] at h
      · cases ex <;> simp only [MessageOp.Outcome.toStep, Step.ofExecution, reduceCtorEq,
          Step.next.injEq] at h
        exact .inl (by rw [h.2])
      · cases h
    · simp only [NextOp.step] at h
      rcases ho : MessageOp.step sevm pre .staticcall with ex | ⟨child', pending'⟩ <;>
        rw [ho] at h
      · cases ex <;> cases h
      · cases h
        exact .inr ⟨child, pending, r, rfl, hr⟩
  rcases pre with ⟨⟨operands, memory, gasLeft, stateGasLeft⟩, metadata, world⟩
  change operands = _ at stack
  subst operands
  simp only [MessageOp.step] at run
  cases stateGas : sevm.benvStat.rules.stateGas with
  | none =>
    simp only [stateGas, bind, Except.bind, Devm.popToNat_def, Devm.popToAdr_def,
      Devm.pop_def, Prod.mapFst, Devm.stack, Devm.setMach, Functor.mapRev,
      Except.map_ok, Prod.map, id_eq] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · rename_i charged charge
      simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
      have effects := generic_call_runs_effects (state := none) (reservoir := 0)
        (charged := false) (insufficient := false) run
      obtain ⟨chargedStack, chargedMemory⟩ := charge_effects charge
      obtain ⟨delegatedStack, delegatedMemory⟩ := delegation_effects sevm.benvStat.rules
        (match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress ⟨⟨rest, memory, gasLeft, stateGasLeft⟩, metadata, world⟩ target.toAddress
        | .flat _ => ⟨⟨rest, memory, gasLeft, stateGasLeft⟩, metadata, world⟩) target.toAddress
      have baseStack : charged.stack = rest := by
        apply chargedStack.trans
        apply delegatedStack.trans
        cases sevm.benvStat.rules.access <;> rfl
      have baseMemory : charged.memory = memory := by
        apply chargedMemory.trans
        apply delegatedMemory.trans
        cases sevm.benvStat.rules.access <;> rfl
      change (∃ flag, post.stack = flag :: charged.stack) ∧
        ∃ bytes, bytes.length ≤ os.toNat ∧ post.memory =
          (charged.memory.extends [(ii.toNat, size.toNat), (oi.toNat, os.toNat)]).write oi.toNat bytes at effects
      rw [baseStack, baseMemory] at effects
      exact effects
  | some state =>
    simp only [stateGas, bind, Except.bind, Devm.popToNat_def, Devm.popToAdr_def,
      Devm.pop_def, Prod.mapFst, Devm.stack, Devm.setMach, Functor.mapRev,
      Except.map_ok, Prod.map, id_eq] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · split at run
      · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
      · split at run
        · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
        · rename_i charged charge
          simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
          have effects := generic_call_runs_effects (state := some state) run
          obtain ⟨chargedStack, chargedMemory⟩ := charge_effects charge
          have baseStack : charged.stack = rest := by
            apply chargedStack.trans
            apply (complete_delegation_effects _ _ _).1.trans
            simp only [Devm.balReadAccount_stack]
            rfl
          have baseMemory : charged.memory = memory := by
            apply chargedMemory.trans
            apply (complete_delegation_effects _ _ _).2.trans
            change (Devm.balReadAccount _ _ (Devm.balReadAccount _ _ _)).mach.memory = _
            rw [Devm.balReadAccount_mach, Devm.balReadAccount_mach]
            rfl
          change (∃ flag, post.stack = flag :: charged.stack) ∧
            ∃ bytes, bytes.length ≤ os.toNat ∧ post.memory =
              (charged.memory.extends [(ii.toNat, size.toNat), (oi.toNat, os.toNat)]).write oi.toNat bytes at effects
          rw [baseStack, baseMemory] at effects
          exact effects

end Jaune
