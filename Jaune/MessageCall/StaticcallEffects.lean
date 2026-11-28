import Jaune.MessageCall.DriverInvariants

/-! Stack and bounded output-window effects of the actual STATICCALL instruction over the checked
frame, on every fork (goal `jaune-shape-and-names-v1`, G2b, unit jsn-u97): the checked
counterpart of the original-run `Jaune.NextOp.staticcall_run_effects`. The same effects of CALL,
whose seventh operand is the value, follow (`Jaune.NextOp.call_run_effects`). -/

namespace Jaune

open Jaune

/-- A message opcode's outcome brings the caller to `post`: finished in place, or a spawned child
returns a result and the caller resumes. -/
private def OutcomeRuns (rules : ForkRules) (o : MessageOp.Outcome) (post : Frame.State) : Prop :=
  o = .done (.ok post) ∨
    ∃ child pending r, o = .spawn child pending ∧
      resume rules pending child.checkpoint r = .ok (.ok post)

private def CallEffects (pre post : Frame.State) (oi os : Nat) : Prop :=
  (∃ flag, post.stack = flag :: pre.stack) ∧
    ∃ bytes : Bytes, bytes.length ≤ os ∧ post.memory = pre.memory.write oi bytes

private theorem absorbMeters_memory_eq (rules : ForkRules) (p : Pending) (m : Machine)
    (r : Frame.Result) : (absorbMeters rules p m r).memory = m.memory := by
  unfold absorbMeters Machine.creditStateGasRefund Machine.repayStateGasSpill
  repeat' split
  all_goals rfl

/-- A caller that resumes without halting has the status pushed on its saved stack and, for a
call, the reply written into its saved memory. -/
private theorem resume_ok_effects {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {post : Frame.State} (h : resume rules p saved r = .ok (.ok post)) :
    post.stack = p.target.status r :: saved.stack ∧
      post.memory = (finishTarget p.target r saved.machine).memory := by
  by_cases room : saved.machine.stack.length < 1024
  · cases RunInvariants.resume_ok_of_room room h
    refine ⟨?_, ?_⟩
    · show (finishTarget p.target r (absorbMeters rules p saved.machine r)).stack = _
      unfold finishTarget
      cases p.target <;> simp only [absorbMeters_stack]
    · show (finishTarget p.target r (absorbMeters rules p saved.machine r)).memory = _
      unfold finishTarget
      cases p.target <;> simp only [absorbMeters_memory_eq]
  · exfalso
    unfold resume at h
    simp only [absorbMeters_stack, room, ↓reduceIte, pure, Except.pure, bind, Except.bind] at h
    repeat' split at h
    all_goals simp_all [throw, throwThe, MonadExceptOf.throw]

private theorem push_effects {pre post : Frame.State} {flag : U256} (h : pre.push flag = .ok post) :
    post.stack = flag :: pre.stack ∧ post.memory = pre.memory := by
  unfold Frame.State.push Frame.State.liftMachine Machine.push at h
  by_cases room : pre.machine.stack.length < 1024
  · simp only [room, ↓reduceIte, Except.ok.injEq] at h
    subst post
    exact ⟨rfl, rfl⟩
  · simp only [room, ↓reduceIte, reduceCtorEq] at h

private theorem charge_effects {pre post : Frame.State} {cost : Nat}
    (h : pre.chargeGas cost = .ok post) :
    post.machine.stack = pre.machine.stack ∧ post.machine.memory = pre.machine.memory := by
  unfold Frame.State.chargeGas Frame.State.liftMachine Machine.chargeGas at h
  split at h
  · cases h
  · rename_i m hc
    cases h
    split at hc
    · cases hc
    · cases hc
      exact ⟨rfl, rfl⟩

private theorem accessDelegation_machine (rules : ForkRules) (s : Frame.State) (a : Address) :
    (ForkRules.accessDelegation rules s a).2.2.2.2.machine = s.machine := by
  unfold ForkRules.accessDelegation GasSchedule.accessDelegation
  split
  · dsimp only
    split <;> rfl
  · rfl

private theorem completeDelegation_machine (s : Frame.State) (b : Bool) (a : Address) :
    (completeDelegationAccess s b a).2.machine = s.machine := by
  cases b <;> rfl

private theorem generic_call_runs_effects {ctx : CallContext} {s post : Frame.State}
    {gas reservoir : Nat} {value : U256} {caller target codeAddress : Address}
    {transfer static : Bool} {ii size oi os : Nat} {code : ByteArray}
    {disable charged insufficient : Bool}
    (state : Option StateGasRules)
    (h : OutcomeRuns ctx.block.rules (match state with
      | none => prepareCall.step ctx s gas value caller target codeAddress transfer static
          ii size oi os code disable
      | some state => prepareCallAmsterdam.step ctx state s gas reservoir value caller target
          codeAddress transfer static ii size oi os code disable charged insufficient) post) :
    CallEffects s post oi os := by
  rcases h with h | ⟨child, pending, r, h, hr⟩
  · cases state with
    | none =>
      simp only [prepareCall.step] at h
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
      simp only [prepareCallAmsterdam.step] at h
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
  · have spawn : pending.target = .call oi os ∧ child.checkpoint = s.withReturnData [] := by
      cases state with
      | none =>
        simp only [prepareCall.step] at h
        split at h
        · simp only [MessageOp.Outcome.ofExcept, bind, Except.bind] at h
          split at h
          · cases h
          · rename_i hp
            split at hp <;> cases hp
            cases h
        · cases h; exact ⟨rfl, rfl⟩
      | some state =>
        simp only [prepareCallAmsterdam.step] at h
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

/-- Every STATICCALL run over the checked frame consumes its six operands, pushes one status word
and writes only a bounded reply to the prepaid output window, on every fork. The checked
counterpart of `Jaune.NextOp.staticcall_run_effects`. -/
theorem NextOp.staticcall_run_effects {ctx : CallContext} {pre post : Frame.State}
    {gas target ii size oi os : U256} {rest : List U256}
    (stack : pre.stack = gas :: target :: ii :: size :: oi :: os :: rest)
    (run : NextOp.Run ctx pre (.message .staticcall) post) :
    (∃ flag, post.stack = flag :: rest) ∧
      ∃ bytes : Bytes, bytes.length ≤ os.toNat ∧
        post.memory = (pre.memory.extends [(ii.toNat, size.toNat), (oi.toNat, os.toNat)]).write
          oi.toNat bytes := by
  have run : OutcomeRuns ctx.block.rules (MessageOp.step ctx pre .staticcall) post := by
    obtain ⟨pc, pc', h | ⟨child, pending, r, h, -, hr⟩⟩ := run
    · simp only [NextOp.step] at h
      rcases ho : MessageOp.step ctx pre .staticcall with ex | ⟨child, pending⟩ <;>
        rw [ho] at h
      · cases ex <;> simp only [MessageOp.Outcome.toStep, Step.ofHalt, reduceCtorEq,
          Step.next.injEq] at h
        exact .inl (by rw [h.2])
      · cases h
    · simp only [NextOp.step] at h
      rcases ho : MessageOp.step ctx pre .staticcall with ex | ⟨child', pending'⟩ <;>
        rw [ho] at h
      · cases ex <;> cases h
      · cases h
        exact .inr ⟨child, pending, r, rfl, hr⟩
  rcases pre with ⟨⟨operands, memory, gasLeft, stateGas, returnData⟩, world, substate, trail⟩
  change operands = _ at stack
  subst operands
  simp only [MessageOp.step, bind, Except.bind, Frame.State.pop, Frame.State.popToNat,
    Frame.State.popToAddress, Frame.State.liftMachineValue, Machine.popToNat,
    Machine.popToAddress, Machine.pop, Frame.State.withMachine] at run
  cases stateGas : ctx.block.rules.stateGas with
  | none =>
    simp only [stateGas] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · rename_i v charge
      simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
      obtain ⟨⟨flag, hs⟩, bytes, hlen, hm⟩ := generic_call_runs_effects (state := none)
        (reservoir := 0) (charged := false) (insufficient := false) run
      obtain ⟨chargedStack, chargedMemory⟩ := charge_effects charge
      rw [accessDelegation_machine] at chargedStack chargedMemory
      refine ⟨⟨flag, hs.trans ?_⟩, bytes, hlen, hm.trans ?_⟩
      · show flag :: v.machine.stack = _
        rw [chargedStack]
        cases ctx.block.rules.access <;> rfl
      · show (v.machine.memory.extends _).write _ _ = _
        rw [chargedMemory]
        cases ctx.block.rules.access <;> rfl
  | some state =>
    simp only [stateGas] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · split at run
      · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
      · split at run
        · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
        · rename_i v charge
          simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
          obtain ⟨⟨flag, hs⟩, bytes, hlen, hm⟩ :=
            generic_call_runs_effects (state := some state) run
          obtain ⟨chargedStack, chargedMemory⟩ := charge_effects charge
          rw [completeDelegation_machine] at chargedStack chargedMemory
          refine ⟨⟨flag, hs.trans ?_⟩, bytes, hlen, hm.trans ?_⟩
          · show flag :: v.machine.stack = _
            rw [chargedStack]
            rfl
          · show (v.machine.memory.extends _).write _ _ = _
            rw [chargedMemory]
            rfl

/-- A run of a message operation is one of its outcomes reaching `post`. -/
private theorem outcomeRuns_of_run {ctx : CallContext} {pre post : Frame.State} {op : MessageOp}
    (run : NextOp.Run ctx pre (.message op) post) :
    OutcomeRuns ctx.block.rules (MessageOp.step ctx pre op) post := by
  obtain ⟨pc, pc', h | ⟨child, pending, r, h, -, hr⟩⟩ := run
  · simp only [NextOp.step] at h
    rcases ho : MessageOp.step ctx pre op with ex | ⟨child, pending⟩ <;>
      rw [ho] at h
    · cases ex <;> simp only [MessageOp.Outcome.toStep, Step.ofHalt, reduceCtorEq,
        Step.next.injEq] at h
      exact .inl (by rw [h.2])
    · cases h
  · simp only [NextOp.step] at h
    rcases ho : MessageOp.step ctx pre op with ex | ⟨child', pending'⟩ <;>
      rw [ho] at h
    · cases ex <;> cases h
    · cases h
      exact .inr ⟨child, pending, r, rfl, hr⟩

private theorem chargeStateGas_effects {pre post : Frame.State} {cost : Nat}
    (h : pre.chargeStateGas cost = .ok post) :
    post.machine.stack = pre.machine.stack ∧ post.machine.memory = pre.machine.memory := by
  unfold Frame.State.chargeStateGas Frame.State.liftMachine Machine.chargeStateGas at h
  split at h
  · cases h
  · rename_i m hc
    cases h
    split at hc
    · cases hc
      exact ⟨rfl, rfl⟩
    · split at hc
      · cases hc
        exact ⟨rfl, rfl⟩
      · cases hc

/-- Every CALL run over the checked frame consumes its seven operands, pushes one status word
and writes only a bounded reply to the prepaid output window, on every fork: the CALL
counterpart of `Jaune.NextOp.staticcall_run_effects`. -/
theorem NextOp.call_run_effects {ctx : CallContext} {pre post : Frame.State}
    {gas target value ii size oi os : U256} {rest : List U256}
    (stack : pre.stack = gas :: target :: value :: ii :: size :: oi :: os :: rest)
    (run : NextOp.Run ctx pre (.message .call) post) :
    (∃ flag, post.stack = flag :: rest) ∧
      ∃ bytes : Bytes, bytes.length ≤ os.toNat ∧
        post.memory = (pre.memory.extends [(ii.toNat, size.toNat), (oi.toNat, os.toNat)]).write
          oi.toNat bytes := by
  have run := outcomeRuns_of_run run
  rcases pre with ⟨⟨operands, memory, gasLeft, stateGas, returnData⟩, world, substate, trail⟩
  change operands = _ at stack
  subst operands
  simp only [MessageOp.step, bind, Except.bind, Frame.State.pop, Frame.State.popToNat,
    Frame.State.popToAddress, Frame.State.liftMachineValue, Machine.popToNat,
    Machine.popToAddress, Machine.pop, Frame.State.withMachine] at run
  cases stateGas : ctx.block.rules.stateGas with
  | none =>
    simp only [stateGas] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · rename_i v charge
      obtain ⟨chargedStack, chargedMemory⟩ := charge_effects charge
      rw [accessDelegation_machine] at chargedStack chargedMemory
      replace chargedStack : v.machine.stack = rest := by
        rw [chargedStack]; cases ctx.block.rules.access <;> rfl
      replace chargedMemory : v.machine.memory = memory := by
        rw [chargedMemory]; cases ctx.block.rules.access <;> rfl
      split at run
      · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
      · split at run
        · split at run
          · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
          · rename_i pushed hpush
            obtain ⟨pushedStack, pushedMemory⟩ := push_effects hpush
            rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
            refine ⟨⟨0, ?_⟩, [], Nat.zero_le _, ?_⟩
            · show pushed.machine.stack = _
              exact pushedStack.trans (congrArg _ chargedStack)
            · show pushed.machine.memory = _
              refine pushedMemory.trans ?_
              show v.machine.memory.extends _ = _
              rw [chargedMemory]
              rfl
        · simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
          obtain ⟨⟨flag, hs⟩, bytes, hlen, hm⟩ := generic_call_runs_effects (state := none)
            (reservoir := 0) (charged := false) (insufficient := false) run
          refine ⟨⟨flag, hs.trans ?_⟩, bytes, hlen, hm.trans ?_⟩
          · show flag :: v.machine.stack = _
            rw [chargedStack]
          · show (v.machine.memory.extends _).write _ _ = _
            rw [chargedMemory]
  | some state =>
    simp only [stateGas] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · split at run
      · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
      · split at run
        · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
        · split at run
          · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
          · rename_i v charge
            obtain ⟨chargedStack, chargedMemory⟩ := charge_effects charge
            rw [completeDelegation_machine] at chargedStack chargedMemory
            replace chargedStack : v.machine.stack = rest := chargedStack
            replace chargedMemory : v.machine.memory = memory := chargedMemory
            split at run
            on_goal 1 =>
              split at run
              · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
              rename_i w stateCharge
              obtain ⟨hs, hm⟩ := chargeStateGas_effects stateCharge
              replace hs := hs.trans chargedStack
              replace hm := hm.trans chargedMemory
            on_goal 2 =>
              have hs := chargedStack
              have hm := chargedMemory
            all_goals
              split at run
              · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
              · rename_i u callCharge
                obtain ⟨calledStack, calledMemory⟩ := charge_effects callCharge
                simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
                obtain ⟨⟨flag, hs'⟩, bytes, hlen, hm'⟩ :=
                  generic_call_runs_effects (state := some state) run
                refine ⟨⟨flag, hs'.trans ?_⟩, bytes, hlen, hm'.trans ?_⟩
                · show flag :: u.machine.stack = _
                  rw [calledStack, hs]
                · show (u.machine.memory.extends _).write _ _ = _
                  rw [calledMemory, hm]

/-- Every CALL run over the checked frame leaves the stack below its seven operands unchanged and
pushes one status word, on every fork: the stack half of `Jaune.NextOp.call_run_effects`. -/
theorem NextOp.call_run_stack {ctx : CallContext} {pre post : Frame.State}
    {gas target value ii size oi os : U256} {rest : List U256}
    (stack : pre.stack = gas :: target :: value :: ii :: size :: oi :: os :: rest)
    (run : NextOp.Run ctx pre (.message .call) post) : ∃ flag, post.stack = flag :: rest :=
  (NextOp.call_run_effects stack run).1

/-- Every CALLCODE run over the checked frame leaves the stack below its seven operands unchanged
and pushes one status word, on every fork: the CALLCODE counterpart of
`Jaune.NextOp.call_run_stack`. -/
theorem NextOp.callcode_run_stack {ctx : CallContext} {pre post : Frame.State}
    {gas target value ii size oi os : U256} {rest : List U256}
    (stack : pre.stack = gas :: target :: value :: ii :: size :: oi :: os :: rest)
    (run : NextOp.Run ctx pre (.message .callcode) post) : ∃ flag, post.stack = flag :: rest := by
  have run := outcomeRuns_of_run run
  rcases pre with ⟨⟨operands, memory, gasLeft, stateGas, returnData⟩, world, substate, trail⟩
  change operands = _ at stack
  subst operands
  simp only [MessageOp.step, bind, Except.bind, Frame.State.pop, Frame.State.popToNat,
    Frame.State.popToAddress, Frame.State.liftMachineValue, Machine.popToNat,
    Machine.popToAddress, Machine.pop, Frame.State.withMachine] at run
  cases stateGas : ctx.block.rules.stateGas with
  | none =>
    simp only [stateGas] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · rename_i v charge
      obtain ⟨chargedStack, -⟩ := charge_effects charge
      rw [accessDelegation_machine] at chargedStack
      replace chargedStack : v.machine.stack = rest := by
        rw [chargedStack]; cases ctx.block.rules.access <;> rfl
      split at run
      · split at run
        · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
        · rename_i pushed hpush
          obtain ⟨pushedStack, -⟩ := push_effects hpush
          rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
          exact ⟨0, pushedStack.trans (congrArg _ chargedStack)⟩
      · simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
        obtain ⟨⟨flag, hs⟩, -⟩ := generic_call_runs_effects (state := none)
          (reservoir := 0) (charged := false) (insufficient := false) run
        exact ⟨flag, hs.trans (congrArg _ chargedStack)⟩
  | some state =>
    simp only [stateGas] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · split at run
      · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
      · split at run
        · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
        · rename_i v charge
          obtain ⟨chargedStack, -⟩ := charge_effects charge
          rw [completeDelegation_machine] at chargedStack
          simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
          obtain ⟨⟨flag, hs⟩, -⟩ := generic_call_runs_effects (state := some state) run
          exact ⟨flag, hs.trans (congrArg _ chargedStack)⟩

/-- Every DELEGATECALL run over the checked frame leaves the stack below its six operands
unchanged and pushes one status word, on every fork: the DELEGATECALL counterpart of
`Jaune.NextOp.call_run_stack`. -/
theorem NextOp.delegatecall_run_stack {ctx : CallContext} {pre post : Frame.State}
    {gas target ii size oi os : U256} {rest : List U256}
    (stack : pre.stack = gas :: target :: ii :: size :: oi :: os :: rest)
    (run : NextOp.Run ctx pre (.message .delegatecall) post) :
    ∃ flag, post.stack = flag :: rest := by
  have run := outcomeRuns_of_run run
  rcases pre with ⟨⟨operands, memory, gasLeft, stateGas, returnData⟩, world, substate, trail⟩
  change operands = _ at stack
  subst operands
  simp only [MessageOp.step, bind, Except.bind, Frame.State.pop, Frame.State.popToNat,
    Frame.State.popToAddress, Frame.State.liftMachineValue, Machine.popToNat,
    Machine.popToAddress, Machine.pop, Frame.State.withMachine] at run
  cases stateGas : ctx.block.rules.stateGas with
  | none =>
    simp only [stateGas] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · rename_i v charge
      obtain ⟨chargedStack, -⟩ := charge_effects charge
      rw [accessDelegation_machine] at chargedStack
      replace chargedStack : v.machine.stack = rest := by
        rw [chargedStack]; cases ctx.block.rules.access <;> rfl
      simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
      obtain ⟨⟨flag, hs⟩, -⟩ := generic_call_runs_effects (state := none)
        (reservoir := 0) (charged := false) (insufficient := false) run
      exact ⟨flag, hs.trans (congrArg _ chargedStack)⟩
  | some state =>
    simp only [stateGas] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · split at run
      · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
      · split at run
        · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
        · rename_i v charge
          obtain ⟨chargedStack, -⟩ := charge_effects charge
          rw [completeDelegation_machine] at chargedStack
          simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
          obtain ⟨⟨flag, hs⟩, -⟩ := generic_call_runs_effects (state := some state) run
          exact ⟨flag, hs.trans (congrArg _ chargedStack)⟩

/-- A creation tail that brings the creator to `post` pushes one word on the stack it was given:
a refused or colliding creation pushes zero in place, a spawned child resumes the creator with
its status. -/
private theorem create_runs_stack {ctx : CallContext} {s post : Frame.State} {endowment : U256}
    {newAddress : Address} {memoryIndex memorySize : Nat} (state : Option StateGasRules)
    (h : OutcomeRuns ctx.block.rules (match state with
      | none => prepareCreate.step ctx s endowment newAddress memoryIndex memorySize
      | some state =>
        prepareCreateAmsterdam.step ctx state s endowment newAddress memoryIndex memorySize)
      post) :
    ∃ w, post.stack = w :: s.stack := by
  rcases h with h | ⟨child, pending, r, h, hr⟩
  · cases state with
    | none =>
      simp only [prepareCreate.step, MessageOp.Outcome.ofExcept, bind, Except.bind, pure,
        Except.pure] at h
      split at h
      · cases h
      · rename_i hp
        subst h
        repeat' split at hp
        all_goals
          first
          | (cases hp; done)
          | (rename_i hpush; cases hp; exact ⟨0, (push_effects hpush).1⟩)
    | some state =>
      simp only [prepareCreateAmsterdam.step, MessageOp.Outcome.ofExcept, bind, Except.bind, pure,
        Except.pure] at h
      split at h
      · cases h
      · rename_i hp
        subst h
        repeat' split at hp
        all_goals
          first
          | (cases hp; done)
          | (rename_i hpush; cases hp; exact ⟨0, (push_effects hpush).1⟩)
          | (rename_i hcharge _ _ _ hpush
             cases hp
             exact ⟨0, (push_effects hpush).1.trans (congrArg _ (chargeStateGas_effects hcharge).1)⟩)
  · obtain ⟨hstack, -⟩ := resume_ok_effects hr
    refine ⟨_, hstack.trans (congrArg _ ?_)⟩
    cases state with
    | none =>
      simp only [prepareCreate.step, MessageOp.Outcome.ofExcept, bind, Except.bind, pure,
        Except.pure] at h
      split at h
      · cases h
      · rename_i hp
        subst h
        repeat' split at hp
        all_goals first | (cases hp; done) | (cases hp; rfl)
    | some state =>
      simp only [prepareCreateAmsterdam.step, MessageOp.Outcome.ofExcept, bind, Except.bind, pure,
        Except.pure] at h
      split at h
      · cases h
      · rename_i hp
        subst h
        repeat' split at hp
        all_goals
          first
          | (cases hp; done)
          | (cases hp; rfl)
          | (rename_i hcharge _
             cases hp
             exact (chargeStateGas_effects hcharge).1)

/-- Every CREATE run over the checked frame leaves the stack below its three operands unchanged
and pushes one word (the new address, or zero), on every fork: the CREATE counterpart of
`Jaune.NextOp.call_run_stack`. -/
theorem NextOp.create_run_stack {ctx : CallContext} {pre post : Frame.State}
    {endowment ii size : U256} {rest : List U256}
    (stack : pre.stack = endowment :: ii :: size :: rest)
    (run : NextOp.Run ctx pre (.message .create) post) : ∃ w, post.stack = w :: rest := by
  have run := outcomeRuns_of_run run
  rcases pre with ⟨⟨operands, memory, gasLeft, stateGas, returnData⟩, world, substate, trail⟩
  change operands = _ at stack
  subst operands
  simp only [MessageOp.step, bind, Except.bind, Frame.State.pop, Frame.State.popToNat,
    Frame.State.liftMachineValue, Machine.popToNat, Machine.pop, Frame.State.withMachine] at run
  cases stateGas : ctx.block.rules.stateGas with
  | none =>
    simp only [stateGas] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · rename_i v charge
      simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
      obtain ⟨w, hs⟩ := create_runs_stack (state := none) run
      exact ⟨w, hs.trans (congrArg _ (charge_effects charge).1)⟩
  | some state =>
    simp only [stateGas] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · split at run
      · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
      · rename_i v charge
        split at run
        · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
        · simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
          obtain ⟨w, hs⟩ := create_runs_stack (state := some state) run
          exact ⟨w, hs.trans (congrArg _ (charge_effects charge).1)⟩

/-- Every CREATE2 run over the checked frame leaves the stack below its four operands unchanged
and pushes one word (the new address, or zero), on every fork: the CREATE2 counterpart of
`Jaune.NextOp.call_run_stack`. -/
theorem NextOp.create2_run_stack {ctx : CallContext} {pre post : Frame.State}
    {endowment ii size salt : U256} {rest : List U256}
    (stack : pre.stack = endowment :: ii :: size :: salt :: rest)
    (run : NextOp.Run ctx pre (.message .create2) post) : ∃ w, post.stack = w :: rest := by
  have run := outcomeRuns_of_run run
  rcases pre with ⟨⟨operands, memory, gasLeft, stateGas, returnData⟩, world, substate, trail⟩
  change operands = _ at stack
  subst operands
  simp only [MessageOp.step, bind, Except.bind, Frame.State.pop, Frame.State.popToNat,
    Frame.State.liftMachineValue, Machine.popToNat, Machine.pop, Frame.State.withMachine] at run
  split at run
  on_goal 2 => rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
  cases stateGas : ctx.block.rules.stateGas with
  | none =>
    simp only [stateGas] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · rename_i v charge
      simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
      obtain ⟨w, hs⟩ := create_runs_stack (state := none) run
      exact ⟨w, hs.trans (congrArg _ (charge_effects charge).1)⟩
  | some state =>
    simp only [stateGas] at run
    split at run
    · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
    · split at run
      · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
      · rename_i v charge
        split at run
        · rcases run with h | ⟨_, _, _, h, _⟩ <;> cases h
        · simp only [pure, Except.pure, MessageOp.Outcome.ofExcept] at run
          obtain ⟨w, hs⟩ := create_runs_stack (state := some state) run
          exact ⟨w, hs.trans (congrArg _ (charge_effects charge).1)⟩

end Jaune
