import Jaune.MessageCall.FinalPlainMemory

/-! # Memory and gas reserved across a message operation -/

namespace Jaune.Staging
open Jaune

/-- A call's output window has already been paid for. Creation installs no output in memory. -/
def ReturnTarget.MemoryPaid (target : ReturnTarget) (size : Nat) : Prop :=
  match target with
  | .call index count => count ≠ 0 → index + count ≤ size
  | .create _ => True

/-- Each message operation keeps the potential within the available budget. When a child is
spawned the budget includes its gas grant and the saved caller covers its return window. -/
def MessageOp.Outcome.MemoryAccounted (n : Nat) : MessageOp.Outcome → Prop
  | .done x => Walk (fun s => Machine.memoryPotential s.machine ≤ n)
      (fun s => Machine.memoryPotential s.machine ≤ n) x
  | .spawn child pending => Machine.memoryPotential child.checkpoint.machine + child.message.gas ≤ n ∧
      ReturnTarget.MemoryPaid pending.target child.checkpoint.memory.size

private theorem outcome_memory {n : Nat} {x} (h : Walk (fun s => Machine.memoryPotential s.machine ≤ n)
    (MessageOp.Outcome.MemoryAccounted n) x) : (MessageOp.Outcome.ofExcept x).MemoryAccounted n := by
  cases x <;> exact h

private theorem refund_potential (s : Frame.State) (gas : Nat) :
    Machine.memoryPotential ((s.withReturnData []).withGasLeft (s.gasLeft + gas)).machine =
      Machine.memoryPotential s.machine + gas := by
  change s.gasLeft + gas + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill +
      calculateMemoryGasCost s.memory.size = s.gasLeft + s.machine.stateGas.spilled +
      s.machine.stateGas.committedSpill + calculateMemoryGasCost s.memory.size + gas
  omega

theorem genericCall.step_memoryAccounted (ctx : CallContext) (s : Frame.State) (gas : Nat)
    (value : U256) (caller target codeAddress : Address) (transfer staticCall : Bool)
    (ii il oi ol : Nat) (code : ByteArray) (disabled : Bool) {n : Nat}
    (h : Machine.memoryPotential s.machine + gas ≤ n)
    (hw : ol ≠ 0 → oi + ol ≤ s.memory.size) :
    (genericCall.step ctx s gas value caller target codeAddress transfer staticCall ii il oi ol code disabled).MemoryAccounted n := by
  unfold genericCall.step
  split
  · apply outcome_memory
    refine Walk.bind (Frame.State.push_memoryPotential _ ?_) ?_
    · exact (refund_potential s gas).le.trans h
    · intro _ hs; exact hs
  · exact ⟨h, hw⟩

theorem genericCreate.step_memoryAccounted (ctx : CallContext) (s : Frame.State) (value : U256)
    (address : Address) (start size : Nat) {n : Nat} (h : Machine.memoryPotential s.machine ≤ n) :
    (genericCreate.step ctx s value address start size).MemoryAccounted n := by
  have grant : except64th s.gasLeft ≤ s.gasLeft := Nat.sub_le _ _
  have hgrant : Machine.memoryPotential (s.withGasLeft (s.gasLeft - except64th s.gasLeft)).machine +
      except64th s.gasLeft = Machine.memoryPotential s.machine := by
    unfold Machine.memoryPotential Jaune.Machine.gasMeasure
    change s.gasLeft - except64th s.gasLeft + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill + calculateMemoryGasCost s.memory.size + except64th s.gasLeft = s.gasLeft + s.machine.stateGas.spilled + s.machine.stateGas.committedSpill + calculateMemoryGasCost s.memory.size
    omega
  have held : Machine.memoryPotential (s.withGasLeft (s.gasLeft - except64th s.gasLeft)).machine ≤ n :=
    (Nat.le_add_right _ _).trans (hgrant.le.trans h)
  unfold genericCreate.step
  apply outcome_memory
  refine Walk.bind (Walk.assert (H := fun s => Machine.memoryPotential s.machine ≤ n) h) ?_
  intro _ _
  refine Walk.bind (Walk.assert (H := fun s => Machine.memoryPotential s.machine ≤ n) held) ?_
  intro _ _
  dsimp only
  split
  · refine Walk.bind (Frame.State.push_memoryPotential _ ?_) ?_
    · exact (refund_potential _ _).le.trans (hgrant.le.trans h)
    · intro _ hp; exact hp
  · split
    · refine Walk.bind (Frame.State.push_memoryPotential _ held) ?_
      intro _ hp; exact hp
    · exact ⟨hgrant.le.trans h, True.intro⟩


private theorem charge_create_memory (s : Frame.State) (i l base extra n : Nat)
    (h : Machine.memoryPotential s.machine ≤ n) :
    Walk (fun t => Machine.memoryPotential t.machine ≤ n)
      (fun t => Machine.memoryPotential (t.memExtends [(i, l)]).machine ≤ n)
      (s.chargeGas (base + s.extCost [(i, l)] + extra)) := by
  rw [Nat.add_right_comm base (s.extCost [(i, l)]) extra]
  apply Walk.mono (Frame.State.chargeGas_extend_memoryPotential [(i, l)] (base + extra) h)
  intro t ht
  exact (Nat.le_add_right _ _).trans ht

local macro "pop_message_operands" : tactic => `(tactic| repeat' first
  | (refine Walk.bind (Frame.State.pop_memoryPotential (by first | assumption | exact Nat.le_refl _)) ?_;
      intro ⟨_, _⟩ _)
  | (refine Walk.bind (Frame.State.popToAddress_memoryPotential (by first | assumption | exact Nat.le_refl _)) ?_;
      intro ⟨_, _⟩ _)
  | (refine Walk.bind (Frame.State.popToNat_memoryPotential (by first | assumption | exact Nat.le_refl _)) ?_;
      intro ⟨_, _⟩ _))

private theorem create_memory (ctx : CallContext) (s : Frame.State) (hn : ctx.block.rules.stateGas = none) :
    (MessageOp.step ctx s .create).MemoryAccounted (Machine.memoryPotential s.machine) := by
  simp only [MessageOp.step, hn]
  apply outcome_memory
  pop_message_operands
  refine Walk.bind (charge_create_memory _ _ _ _ _ _ (by assumption)) ?_
  intro t ht
  apply genericCreate.step_memoryAccounted
  exact ht

private theorem create2_memory (ctx : CallContext) (s : Frame.State) (hn : ctx.block.rules.stateGas = none) :
    (MessageOp.step ctx s .create2).MemoryAccounted (Machine.memoryPotential s.machine) := by
  simp only [MessageOp.step, hn]
  split
  · apply outcome_memory
    pop_message_operands
    refine Walk.bind (charge_create_memory _ _ _ _ _ _ (by assumption)) ?_
    intro t ht
    apply genericCreate.step_memoryAccounted
    exact ht
  · exact Nat.le_refl _

private theorem delegation_machine (rules : ForkRules) (s : Frame.State) (a : Address) :
    (ForkRules.accessDelegation rules s a).2.2.2.2.machine = s.machine := by
  unfold ForkRules.accessDelegation
  split
  · unfold GasSchedule.accessDelegation
    dsimp only
    split <;> rfl
  · rfl

private theorem charged_call_memory {s t : Frame.State} {n : Nat} (pairs : List (Nat × Nat))
    (cost grant : Nat) (hprice : grant ≤ cost) (ht : t.machine = s.machine) (h : Machine.memoryPotential s.machine ≤ n) :
    Walk (fun post => Machine.memoryPotential post.machine ≤ n)
      (fun post => Machine.memoryPotential (post.memExtends pairs).machine + grant ≤ n)
      (t.chargeGas (cost + s.extCost pairs)) := by
  have he : s.extCost pairs = t.extCost pairs := congrArg (fun m : Machine => m.extCost pairs) ht.symm
  rw [he]
  apply Walk.mono (Frame.State.chargeGas_extend_memoryPotential pairs cost (ht ▸ h : Machine.memoryPotential t.machine ≤ n))
  intro post hp
  exact (Nat.add_le_add_left hprice _).trans hp

private theorem grant_le_cost (value gas left ext extra : Nat)
    (hs : (if value = 0 then 0 else Gas.callStipend) ≤ extra) :
    (calculateMsgCallGas value gas left ext extra).2 ≤ (calculateMsgCallGas value gas left ext extra).1 := by
  simp only [calculateMsgCallGas]
  split <;> omega

private theorem value_stipend_le_transfer (ctx : CallContext) (value : U256) (extra : Nat) :
    (if value.toNat = 0 then 0 else Gas.callStipend) ≤ extra + (if value = 0 then 0 else ctx.block.rules.gas.callValue) := by
  by_cases hv : value = 0
  · subst value
    exact Nat.zero_le _
  · rw [ite_eq_right hv]
    split
    · exact Nat.zero_le _
    · exact (GasSchedule.Valid.stipend_le_callValue ctx.block.rules_valid.gas).trans (Nat.le_add_left _ _)

private theorem call_output_covered (s : Frame.State) (ii il oi ol : Nat) (hn : ol ≠ 0) :
    oi + ol ≤ (s.memExtends [(ii, il), (oi, ol)]).memory.size :=
  memExtSize_access_le _ _ _ hn

private theorem refund_failed_call {s : Frame.State} {n grant : Nat}
    (h : Machine.memoryPotential s.machine + grant ≤ n) :
    Walk (fun t => Machine.memoryPotential t.machine ≤ n)
      (MessageOp.Outcome.MemoryAccounted n) (do
        let t ← s.push 0
        return .done (.ok ((t.withReturnData []).withGasLeft (t.gasLeft + grant)))) := by
  have hp := Frame.State.push_memoryPotential (s := s) 0 (Nat.le_refl _)
  cases he : s.push 0 with
  | error e =>
    rw [he] at hp
    exact hp.trans ((Nat.le_add_right _ _).trans h)
  | ok t =>
    rw [he] at hp
    exact (refund_potential _ grant).le.trans ((Nat.add_le_add_right hp _).trans h)


local macro "call_charge" : tactic => `(tactic| (
  apply outcome_memory
  pop_message_operands
  dsimp only at *
  refine Walk.bind (charged_call_memory _ _ _ (grant_le_cost _ _ _ _ _ ?_) ?_ ?_) ?_
  · first | exact Nat.zero_le _ | apply value_stipend_le_transfer
  · rw [delegation_machine]; split <;> rfl
  · assumption
  · intro t ht
    try (refine Walk.bind (Walk.assert (H := fun post => Machine.memoryPotential post.machine ≤ _) ((Machine.memoryPotential_le_extended _ _).trans ((Nat.le_add_right _ _).trans ht))) ?_; intro _ _)
    first
    | (apply genericCall.step_memoryAccounted <;> first | exact ht | exact call_output_covered _ _ _ _ _)
    | (split
       · exact refund_failed_call ht
       · apply genericCall.step_memoryAccounted <;> first | exact ht | exact call_output_covered _ _ _ _ _)))

local macro "call_memory_fact " name:ident " for " op:term : command =>
  `(private theorem $name (ctx : CallContext) (s : Frame.State) (hn : ctx.block.rules.stateGas = none) :
      (MessageOp.step ctx s $op).MemoryAccounted (Machine.memoryPotential s.machine) := by
      simp only [MessageOp.step, hn]
      call_charge)

call_memory_fact call_memory for .call
call_memory_fact callcode_memory for .callcode
call_memory_fact staticcall_memory for .staticcall
call_memory_fact delegatecall_memory for .delegatecall

/-- The charged memory ranges cover the return target and the child grant remains inside the original potential. -/
theorem MessageOp.step_memoryAccounted (ctx : CallContext) (s : Frame.State) (op : Jaune.MessageOp)
    (hn : ctx.block.rules.stateGas = none) :
    (MessageOp.step ctx s op).MemoryAccounted (Machine.memoryPotential s.machine) := by
  cases op with
  | create => exact create_memory ctx s hn
  | create2 => exact create2_memory ctx s hn
  | call => exact call_memory ctx s hn
  | callcode => exact callcode_memory ctx s hn
  | staticcall => exact staticcall_memory ctx s hn
  | delegatecall => exact delegatecall_memory ctx s hn


/-- The next instruction either pays its output, continues within the budget, or reserves
the child grant and the caller's output window. -/
def Step.MemoryAccounted (n : Nat) : Step → Prop
  | .exit e => Frame.Exit.MemoryAccounted n e
  | .next _ s => Machine.memoryPotential s.machine ≤ n
  | .spawn child pending _ => (MessageOp.Outcome.spawn child pending).MemoryAccounted n

private theorem halted_memory {n : Nat} (reason : ExceptionalHalt) {s : Frame.State}
    (h : Machine.memoryPotential s.machine ≤ n) : Frame.Exit.MemoryAccounted n (.halted reason s) := by
  refine ⟨h, ?_⟩
  have hzero : calculateMemoryGasCost 0 = 0 := by decide
  change calculateMemoryGasCost 0 ≤ n
  rw [hzero]
  exact Nat.zero_le _

private theorem ofHalt_memory (pc : Nat) {x} {n : Nat} (h : Walk
    (fun s => Machine.memoryPotential s.machine ≤ n) (fun s => Machine.memoryPotential s.machine ≤ n) x) :
    (Step.ofHalt pc x).MemoryAccounted n := by
  cases x with
  | error e => cases e; exact halted_memory _ h
  | ok s => exact h

private theorem ofJump_memory (r : Frame.Running) (op : Jaune.JumpOp) :
    (Step.ofJump (JumpOp.run r op)).MemoryAccounted (Machine.memoryPotential r.state.machine) := by
  have hj := JumpOp.runCore_memoryPotential r.pc r.context r.state op
  unfold JumpOp.run
  split
  · rename_i e he
    rw [he] at hj; cases e
    exact halted_memory _ hj
  · rename_i pc s he
    rw [he] at hj; exact hj

private theorem toStep_memory (pc : Nat) {x : MessageOp.Outcome} {n : Nat} (h : x.MemoryAccounted n) :
    (x.toStep pc).MemoryAccounted n := by
  cases x with
  | done _ => exact ofHalt_memory pc h
  | spawn _ _ => exact h

theorem NextOp.step_memoryAccounted (r : Frame.Running) (op : Jaune.NextOp)
    (hn : r.context.block.rules.stateGas = none) :
    (NextOp.step r op).MemoryAccounted (Machine.memoryPotential r.state.machine) := by
  cases op with
  | plain p => exact ofHalt_memory _ (PlainOp.runCore_memoryPotential _ _ _ p hn)
  | message m => exact toStep_memory _ (MessageOp.step_memoryAccounted _ _ m hn)
  | push xs h =>
    simp only [NextOp.step]
    split
    · exact halted_memory _ (Nat.le_refl _)
    · apply ofHalt_memory
      refine Walk.bind (Frame.State.chargeGas_memoryPotential _ (Nat.le_refl _)) ?_
      intro t ht; exact Frame.State.push_memoryPotential _ ht
  | dupn imm | swapn imm | exchange imm =>
    apply ofHalt_memory
    split
    · refine Walk.bind (Frame.State.chargeGas_memoryPotential _ (Nat.le_refl _)) ?_
      intro t ht
      split
      · exact ht
      · split <;> first | exact ht | exact Frame.State.push_memoryPotential _ ht
    · exact Nat.le_refl _

theorem step_memory_accounting_output (r : Frame.Running) (hn : r.context.block.rules.stateGas = none)
    {next : Step} (h : step r = .ok next) : next.MemoryAccounted (Machine.memoryPotential r.state.machine) := by
  unfold step at h
  split at h
  · cases h; exact halted_memory _ (Nat.le_refl _)
  · cases h; exact NextOp.step_memoryAccounted r _ hn
  · cases h; exact ofJump_memory r _
  · rename_i op _
    cases he : HaltOp.run r.context r.state op with
    | error e => rw [he] at h; cases h
    | ok e =>
      rw [he] at h; cases h
      exact HaltOp.run_memory_accounting_output _ _ op hn he

end Jaune.Staging
