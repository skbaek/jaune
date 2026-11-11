import Jaune.Exec

/-! Stack and bounded output-window effects of the actual STATICCALL instruction, on every fork. -/

namespace Jaune

private theorem push_effects {pre post : Devm} {flag : B256} (h : pre.push flag = .ok post) :
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

private theorem delegation_effects (rules : ForkRules) (pre : Devm) (target : Adr) :
    (rules.accessDelegation pre target).2.2.2.2.stack = pre.stack ∧
      (rules.accessDelegation pre target).2.2.2.2.memory = pre.memory := by
  unfold ForkRules.accessDelegation
  split
  · unfold GasSchedule.accessDelegation
    dsimp only
    split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

private theorem complete_delegation_effects (pre : Devm) (delegated : Bool) (target : Adr) :
    (completeDelegationAccess pre delegated target).2.stack = pre.stack ∧
      (completeDelegationAccess pre delegated target).2.memory = pre.memory := by
  cases delegated <;> exact ⟨rfl, rfl⟩

private theorem resume_call_effects {parent post : Devm} {oi os : Nat} (state : Option StateGasRules)
    (charged : Bool) {raw : Except (EvmError × State × AdrSet × Tra) Devm}
    (h : (match state with
      | none => Resume.call parent oi os
      | some state => Resume.callAmsterdam state parent oi os charged).run raw = .ok post) :
    CallEffects parent post oi os := by
  cases raw with
  | error error => cases state <;> cases h
  | ok child =>
    cases state with
    | none =>
      simp only [Resume.run, liftToExecution, bind, Except.bind] at h
      split at h
      all_goals
        obtain ⟨pushed, hp, h⟩ := Except.bind_eq_ok h
        cases h
        obtain ⟨stack, memory⟩ := push_effects hp
        refine ⟨⟨_, stack⟩, ⟨child.output.take os, List.length_take_le _ _, ?_⟩⟩
        change pushed.memory.write oi _ = _
        rw [memory]
        rfl
    | some state =>
      simp only [Resume.run, liftToExecution, bind, Except.bind] at h
      split at h
      all_goals
        obtain ⟨_, guard, h⟩ := Except.bind_eq_ok h
        obtain ⟨pushed, hp, h⟩ := Except.bind_eq_ok h
        cases h
        obtain ⟨stack, memory⟩ := push_effects hp
        cases charged <;>
          refine ⟨⟨_, stack⟩, ⟨child.output.take os, List.length_take_le _ _, ?_⟩⟩
        all_goals
          change pushed.memory.write oi _ = _
          rw [memory]
          rfl

private theorem generic_call_effects {sevm : Sevm} {pre post : Devm} {gas reservoir : Nat} {value : B256}
    {caller target codeAddress : Adr} {transfer static : Bool} {ii size oi os : Nat}
    {code : ByteArray} {disable charged insufficient : Bool} {xl : Xlot} (state : Option StateGasRules)
    (h : XStep.Run (match state with
      | none => genericCall.step sevm pre gas value caller target codeAddress transfer static
          ii size oi os code disable
      | some state => genericCallAmsterdam.step sevm state pre gas reservoir value caller target codeAddress
          transfer static ii size oi os code disable charged insufficient) xl (.ok post)) :
    CallEffects pre post oi os := by
  cases state with
  | none =>
    simp only [genericCall.step] at h
    split at h
    · simp only [bind, Except.bind] at h
      split at h
      · cases h.2
      · rename_i pushed hp
        cases h.2
        obtain ⟨stack, memory⟩ := push_effects hp
        exact ⟨⟨0, stack⟩, ⟨[], Nat.zero_le _, memory⟩⟩
    · obtain ⟨raw, _, resume⟩ := h
      exact resume_call_effects (parent := pre.withReturnData []) none false resume.symm
  | some state =>
    simp only [genericCallAmsterdam.step] at h
    split at h
    · simp only [bind, Except.bind] at h
      split at h
      · cases h.2
      · rename_i pushed hp
        cases h.2
        obtain ⟨stack, memory⟩ := push_effects hp
        cases charged <;> exact ⟨⟨0, stack⟩, ⟨[], Nat.zero_le _, memory⟩⟩
    · obtain ⟨raw, _, resume⟩ := h
      exact resume_call_effects (parent := pre.withReturnData []) (some state) charged resume.symm

/-- Every successful STATICCALL consumes its six operands, pushes one status word and writes only a bounded
reply to the prepaid output window. The premise is the original instruction run, with no fork restriction. -/
theorem Ninst.staticcall_run_effects {sevm : Sevm} {pre post : Devm}
    {gas target ii size oi os : B256} {rest : List B256}
    (stack : pre.stack = gas :: target :: ii :: size :: oi :: os :: rest)
    (run : Ninst.Run sevm pre (.exec .staticcall) post) :
    (∃ flag, post.stack = flag :: rest) ∧
      ∃ bytes : Bytes, bytes.length ≤ os.toNat ∧
        post.memory = (pre.memory.extends [(ii.toNat, size.toNat), (oi.toNat, os.toNat)]).write oi.toNat bytes := by
  obtain ⟨xl, _, pc, run⟩ := run
  rcases pre with ⟨⟨operands, memory, gasLeft, stateGasLeft⟩, metadata, world⟩
  change operands = _ at stack
  subst operands
  simp only [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep, Xinst.step] at run
  cases stateGas : sevm.benvStat.rules.stateGas with
  | none =>
    simp only [stateGas, bind, Except.bind, Devm.popToNat_def, Devm.popToAdr_def,
      Devm.pop_def, Prod.mapFst, Devm.stack, Devm.setMach, Functor.mapRev,
      Except.map_ok, Prod.map, id_eq] at run
    split at run
    · cases run.2
    · rename_i charged charge
      simp only [pure, Except.pure, XStep.ofExcept] at run
      have effects := generic_call_effects (state := none) (reservoir := 0) (charged := false)
        (insufficient := false) run
      obtain ⟨chargedStack, chargedMemory⟩ := charge_effects charge
      obtain ⟨delegatedStack, delegatedMemory⟩ := delegation_effects sevm.benvStat.rules
        (match sevm.benvStat.rules.access with
        | .eip2929 => addAccessedAddress ⟨⟨rest, memory, gasLeft, stateGasLeft⟩, metadata, world⟩ target.toAdr
        | .flat _ => ⟨⟨rest, memory, gasLeft, stateGasLeft⟩, metadata, world⟩) target.toAdr
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
    · cases run.2
    · split at run
      · cases run.2
      · split at run
        · cases run.2
        · rename_i charged charge
          simp only [pure, Except.pure, XStep.ofExcept] at run
          have effects := generic_call_effects (state := some state) run
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
