import Jaune.MessageCall.MemoryCosts
import Jaune.Instructions.WordFacts
import Jaune.Instructions.ShuffleFacts
import Jaune.Instructions.LogFacts
import Jaune.Instructions.MemoryFacts
import Jaune.Instructions.ReadFacts
import Jaune.Instructions.StoreFacts

/-! # The memory potential during a plain instruction -/

namespace Jaune
open Jaune

private abbrev Within (n : Nat) (m : Machine) := Machine.memoryPotential m ≤ n
private abbrev StateWithin (n : Nat) (s : Frame.State) := Within n s.machine

private theorem Machine.charge_within (c : Nat) {m : Machine} {n : Nat} (h : Within n m) :
    Machine.Walk (Within n) (Within n) (m.chargeGas c) := by
  unfold Machine.chargeGas safeSub
  split
  · exact h
  · rename_i gas he
    split at he
    · cases he
      change m.gasLeft - c + m.stateGas.spilled + m.stateGas.committedSpill + calculateMemoryGasCost m.memory.size ≤ n
      change m.gasLeft + m.stateGas.spilled + m.stateGas.committedSpill + calculateMemoryGasCost m.memory.size ≤ n at h
      omega
    · cases he

local macro "next_stack" name:ident fact:term : tactic => `(tactic| (
  have result := $fact
  split <;> rename_i he <;> rw [he] at result
  all_goals first | exact result | (simp only [Machine.Walk.ok_iff] at result; have $name := result)))

private theorem Machine.popToAddress_within  {m : Machine} {n : Nat} (h : Within n m) :
    Machine.Walk (Within n) (fun p => Within n p.2) (m.popToAddress) := by
  unfold Machine.popToAddress
  have hp := Machine.pop_memoryPotential h
  split <;> rename_i he <;> rw [he] at hp <;> exact hp

private theorem Machine.popList_within (k : Nat) {m : Machine} {n : Nat} (h : Within n m) :
    Machine.Walk (Within n) (fun p => Within n p.2) (m.popList k) := by
  induction k generalizing m with
  | zero => exact h
  | succ k ih =>
    unfold Machine.popList
    next_stack hp (Machine.pop_memoryPotential h)
    have hp' := ih hp
    split <;> rename_i he <;> rw [he] at hp' <;> exact hp'

private theorem Machine.push_within (x : U256) {m : Machine} {n : Nat} (h : Within n m) :
    Machine.Walk (Within n) (Within n) (m.push x) := by
  unfold Machine.push
  split <;> exact h

theorem Frame.State.push_memoryPotential (x : U256) {s : Frame.State} {n : Nat}
    (h : Machine.memoryPotential s.machine ≤ n) :
    Walk (fun t => Machine.memoryPotential t.machine ≤ n) (fun t => Machine.memoryPotential t.machine ≤ n) (s.push x) :=
  Walk.liftMachine (core := fun m => m.push x) (Machine.push_within x h)

private theorem Machine.charge_extend_within (pairs : List (Nat × Nat)) (base : Nat)
    {m : Machine} {n : Nat} (h : Within n m) :
    Machine.Walk (Within n) (fun t => Within n (t.extendMemoryForAccesses pairs)) (m.chargeGas (base + m.memoryExpansionCost pairs)) := by
  have hc := Machine.chargeGas_memoryPotential m pairs base
  cases he : m.chargeGas (base + m.memoryExpansionCost pairs) with
  | error e => rw [he] at hc; change e.2 = m at hc; change Within n e.2; rwa [hc]
  | ok t =>
    rw [he] at hc
    change Machine.memoryPotential (t.extendMemoryForAccesses pairs) + base = Machine.memoryPotential m at hc
    change Machine.memoryPotential (t.extendMemoryForAccesses pairs) ≤ n
    exact (Nat.le_add_right _ _).trans (hc.le.trans h)

private theorem list_slice_length (bytes : List UInt8) (index size : Nat)
    (defaultByte : UInt8) : (List.sliceD bytes index size defaultByte).length = size := by
  induction size generalizing index with
  | zero => rfl
  | succ size ih => rw [List.sliceD_succ, List.length_cons, ih]

private theorem write_within (m : Machine) (i size : Nat) (bs : Bytes) (n : Nat)
    (hs : bs.length = size) (h : Within n (m.extendMemoryForAccesses [(i, size)])) : Within n (m.writeMemory i bs) := by
  subst size
  exact (Machine.writeMemory_memoryPotential m i bs).trans h

private theorem copy_within (m : Machine) (src dst size n : Nat)
    (h : Within n (m.extendMemoryForAccesses [(src, size), (dst, size)])) :
    Within n ((m.readMemory src size).2.writeMemory dst (m.readMemory src size).1) := by
  apply write_within (size := size)
  · exact memory_slice_length _ _ _ _
  · exact h

/-! ### One potential walk per family (S4) -/

private theorem within_of {m out : Machine} (hmem : out.memory = m.memory)
    (hg : out.gasMeasure ≤ m.gasMeasure) : Within (Machine.memoryPotential m) out := by
  unfold Within Machine.memoryPotential
  rw [hmem]
  omega

private theorem Machine.popWords_within {n : Nat} {m : Machine} (a : Fin 4) (h : Within n m) :
    Machine.Walk (Within n) (fun p => Within n p.2) (m.popWords a) := by
  match a with
  | 0 => exact h
  | 1 => exact Machine.pop_memoryPotential h
  | 2 =>
    refine Machine.Walk.bind (Machine.pop_memoryPotential h) ?_
    rintro ⟨x, m₁⟩ h₁
    refine Machine.Walk.bind (Machine.pop_memoryPotential h₁) ?_
    rintro ⟨y, m₂⟩ h₂
    exact h₂
  | 3 =>
    refine Machine.Walk.bind (Machine.pop_memoryPotential h) ?_
    rintro ⟨x, m₁⟩ h₁
    refine Machine.Walk.bind (Machine.pop_memoryPotential h₁) ?_
    rintro ⟨y, m₂⟩ h₂
    refine Machine.Walk.bind (Machine.pop_memoryPotential h₂) ?_
    rintro ⟨z, m₃⟩ h₃
    exact h₃

private theorem WordRow.step_within (row : WordRow) (o : OpcodeRules) (e : Word.Env) (m : Machine) :
    Machine.Walk (Within (Machine.memoryPotential m)) (Within (Machine.memoryPotential m)) (row.step o e m) := by
  have hmem := WordRow.step_memory row o e m
  have hg := WordRow.step_gasMeasure_le row o e m
  cases he : row.step o e m with
  | ok out => rw [he] at hmem hg; exact within_of hmem hg
  | error p => obtain ⟨r, out⟩ := p; rw [he] at hmem hg; exact within_of hmem hg

private theorem ShuffleRow.step_within (row : ShuffleRow) (o : OpcodeRules) (m : Machine) :
    Machine.Walk (Within (Machine.memoryPotential m)) (Within (Machine.memoryPotential m)) (row.step o m) := by
  have hf := ShuffleRow.step_frame row o m
  cases he : row.step o m with
  | ok out =>
    rw [he] at hf; obtain ⟨_, _, hg, rfl⟩ := hf
    exact within_of rfl (by simp only [Machine.gasMeasure]; omega)
  | error p =>
    obtain ⟨r, out⟩ := p
    rw [he] at hf; obtain ⟨_, _, hg, rfl⟩ := hf
    exact within_of rfl (by simp only [Machine.gasMeasure]; omega)

/-- An effect's new memory costs no more than the extension of its ranges, which the step has paid. -/
private theorem MemoryEffect.apply_within {a : Fin 4} (eff : MemoryEffect a) (calldata : Bytes)
    (code : ByteArray) (returnData : Bytes) (args : Words a) {t : Machine} {n : Nat}
    {mem : Memory} {pushed : Option U256}
    (happ : eff.apply calldata code returnData args t.memory = some (mem, pushed))
    (h : Within n (t.extendMemoryForAccesses (eff.ranges args))) : Within n { t with memory := mem } := by
  cases eff with
  | copy src =>
    obtain ⟨d, o, k⟩ := args
    cases src <;> simp only [MemoryEffect.apply] at happ
    · cases happ
      exact write_within t d.toNat k.toNat _ n (list_slice_length ..) h
    · cases happ
      exact write_within t d.toNat k.toNat _ n (Jaune.ByteArray.length_sliceD ..) h
    · split at happ
      · cases happ
      · cases happ
        exact write_within t d.toNat k.toNat _ n (list_slice_length ..) h
  | move =>
    obtain ⟨d, src, k⟩ := args
    simp only [MemoryEffect.apply] at happ
    cases happ
    exact copy_within t src.toNat d.toNat k.toNat n h
  | storeWord =>
    obtain ⟨i, x⟩ := args
    simp only [MemoryEffect.apply] at happ
    cases happ
    exact write_within t i.toNat 32 _ n rfl h
  | storeByte =>
    obtain ⟨i, x⟩ := args
    simp only [MemoryEffect.apply] at happ
    cases happ
    exact write_within t i.toNat 1 _ n rfl h
  | load =>
    simp only [MemoryEffect.apply] at happ
    cases happ
    exact h
  | digest =>
    obtain ⟨i, k⟩ := args
    simp only [MemoryEffect.apply] at happ
    cases happ
    exact h

private theorem MemoryRow.step_within (row : MemoryRow) (o : OpcodeRules) (ctx : CallContext)
    (m : Machine) :
    Machine.Walk (Within (Machine.memoryPotential m)) (Within (Machine.memoryPotential m))
      (row.step o ctx m) := by
  unfold MemoryRow.step
  cases ha : row.available o
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact Nat.le_refl _
  · simp only [↓reduceIte]
    refine Machine.Walk.bind (Machine.popWords_within row.arity (Nat.le_refl _)) ?_
    rintro ⟨args, m₁⟩ h₁
    refine Machine.Walk.bind (Machine.charge_extend_within (row.effect.ranges args) (row.base args) h₁) ?_
    intro m₂ h₂
    split
    · exact (Machine.memoryPotential_at_most_extended _ _).trans h₂
    · rename_i mem happ
      exact MemoryEffect.apply_within row.effect _ _ _ args happ h₂
    · rename_i mem x happ
      exact Machine.push_within x (MemoryEffect.apply_within row.effect _ _ _ args happ h₂)

private theorem LogRow.step_within (row : LogRow) (ctx : CallContext) (m : Machine) :
    Machine.Walk (Within (Machine.memoryPotential m)) (fun p => Within (Machine.memoryPotential m) p.1)
      (row.step ctx m) := by
  unfold LogRow.step LogRow.cost
  refine Machine.Walk.bind (Machine.popToNat_memoryPotential (Nat.le_refl _)) ?_
  intro ⟨start, m₁⟩ h₁
  refine Machine.Walk.bind (Machine.popToNat_memoryPotential h₁) ?_
  intro ⟨size, m₂⟩ h₂
  refine Machine.Walk.bind (Machine.popList_within _ h₂) ?_
  intro ⟨topics, m₃⟩ h₃
  refine Machine.Walk.bind (Machine.charge_extend_within [(start, size)] _ h₃) ?_
  intro m₄ h₄
  refine Machine.Walk.bind (Machine.Walk.assert (H := Within _) ((Machine.memoryPotential_at_most_extended _ _).trans h₄)) ?_
  intro _ _; exact h₄

private def TouchWithin {τ : Type} (n : Nat) : Except (ExceptionalHalt × Machine × τ) (Machine × τ) → Prop
  | .error (_, m, _) => Within n m
  | .ok (m, _) => Within n m

private theorem ReadTarget.pop_within (t : ReadTarget) (m : Machine) :
    Machine.Walk (Within (Machine.memoryPotential m)) (fun p => Within (Machine.memoryPotential m) p.2)
      (t.pop m) := by
  cases t with
  | account => exact Machine.popToAddress_within (Nat.le_refl _)
  | slot => exact Machine.pop_memoryPotential (Nat.le_refl _)
  | transient => exact Machine.pop_memoryPotential (Nat.le_refl _)
  | recipient => exact Nat.le_refl _

private theorem ReadRow.step_within (row : ReadRow) (rules : ForkRules) (ctx : CallContext)
    (v : ReadView) (m : Machine) :
    TouchWithin (Machine.memoryPotential m) (row.step rules ctx v m) := by
  rcases row with ⟨avail, target, price, result⟩
  unfold ReadRow.step
  dsimp only
  split
  · exact Nat.le_refl _
  · have hpop := Machine.Walk.cases (ReadTarget.pop_within target m)
    split
    · rename_i e m' hp; exact hpop.1 _ _ hp
    · rename_i key m₁ hp
      have h₁ := hpop.2 _ hp
      cases result with
      | push f =>
        simp only [ReadResult.finish]
        have hc := Machine.Walk.cases (Machine.charge_within (price.quote rules ctx v key).1 h₁)
        split
        · rename_i e m' he; exact hc.1 _ _ he
        · rename_i m₂ he
          have hq := Machine.Walk.cases (Machine.push_within (f ctx v.world key) (hc.2 _ he))
          split
          · rename_i e m' he'; exact hq.1 _ _ he'
          · rename_i m₃ he'; exact hq.2 _ he'
      | copyCode perWord =>
        simp only [ReadResult.finish]
        have p1 := Machine.Walk.cases (Machine.popToNat_memoryPotential h₁)
        split
        · rename_i e m' he; exact p1.1 _ _ he
        · rename_i d m₂ he
          have p2 := Machine.Walk.cases (Machine.popToNat_memoryPotential (p1.2 _ he))
          split
          · rename_i e m' he'; exact p2.1 _ _ he'
          · rename_i o m₃ he'
            have p3 := Machine.Walk.cases (Machine.popToNat_memoryPotential (p2.2 _ he'))
            split
            · rename_i e m' he''; exact p3.1 _ _ he''
            · rename_i k m₄ he''
              have h₄ := p3.2 _ he''
              have hc := Machine.Walk.cases (Machine.charge_extend_within [(d, k)]
                ((price.quote rules ctx v key).1 + perWord * ceilDiv k 32) h₄)
              split
              · rename_i e m' h5
                exact hc.1 _ _ h5
              · rename_i m₅ h5
                have h₅ := hc.2 _ h5
                apply write_within (size := k)
                · exact Jaune.ByteArray.length_sliceD ..
                · exact h₅

/-- A family step spends at most the frame's potential: the gas it charges pays for the memory it
extends; a state-gas credit or charge only moves gas between the meters. -/
theorem Family.run_memoryPotential (f : Family) (x : Frame.Running) :
    Walk (fun t => Machine.memoryPotential t.machine ≤ Machine.memoryPotential x.state.machine)
      (fun t => Machine.memoryPotential t.machine ≤ Machine.memoryPotential x.state.machine)
      (f.run x) := by
  cases f with
  | word row => exact Walk.liftMachine (Hm := Within _) (Pm := Within _) (WordRow.step_within row _ _ _)
  | shuffle row => exact Walk.liftMachine (Hm := Within _) (Pm := Within _) (ShuffleRow.step_within row _ _)
  | memory row => exact Walk.liftMachine (Hm := Within _) (Pm := Within _) (MemoryRow.step_within row _ _ _)
  | log row =>
    have core := LogRow.step_within row x.context x.state.machine
    show Walk _ _ (x.state.liftLog (row.step x.context x.state.machine))
    unfold Frame.State.liftLog
    split <;> rename_i he <;> rw [he] at core <;> exact core
  | read row =>
    have hr := ReadRow.step_within row x.context.block.rules x.context x.state.readView x.state.machine
    show Walk _ _ (x.state.liftRead _ _)
    unfold Frame.State.liftRead
    split <;> rename_i he <;> rw [he] at hr
    all_goals
      show Machine.memoryPotential (Frame.State.machine _) ≤ _
      rw [(Frame.State.applyReadTouch_keeps _ _ _).1]
      exact hr
  | store kind =>
    cases kind with
    | persistent =>
      show Walk _ _ (x.state.liftStore _ _ _)
      unfold Frame.State.liftStore
      split <;> rename_i he
      · show Machine.memoryPotential (Frame.State.machine _) ≤ _
        rw [Frame.State.applyStoreTouch_machine]
        obtain ⟨_, hmem, _, hg, _⟩ := SstoreRow.step_error he
        exact within_of hmem hg
      · show Machine.memoryPotential (Frame.State.machine _) ≤ _
        rw [Frame.State.applyStoreTouch_machine]
        obtain ⟨key, v, rest, _, _, _, _, _, hmem, _, hg, _⟩ := SstoreRow.step_ok he
        exact within_of hmem (by simp only [Frame.State.withMachine_machine] at hg ⊢; rw [hg]; omega)
    | transient =>
      show Walk _ _ (x.state.liftStore _ _ _)
      unfold Frame.State.liftStore
      split <;> rename_i he
      · show Machine.memoryPotential (Frame.State.machine _) ≤ _
        rw [Frame.State.applyStoreTouch_machine]
        obtain ⟨_, hmem, _, _, hg, _⟩ := TstoreRow.step_error he
        exact within_of hmem hg
      · show Machine.memoryPotential (Frame.State.machine _) ≤ _
        rw [Frame.State.applyStoreTouch_machine]
        obtain ⟨key, v, rest, _, _, _, _, rfl, _⟩ := TstoreRow.step_ok he
        exact within_of rfl (by simp only [Frame.State.withMachine_machine, Machine.gasMeasure]; omega)

/-- A plain instruction can spend the frame’s gas and expand memory up to its original potential. -/
theorem PlainOp.runCore_memoryPotential (pc : Nat) (ctx : CallContext) (s : Frame.State) (op : Jaune.PlainOp)
    (_hn : ctx.block.rules.stateGas = none) :
    Walk (fun t => Machine.memoryPotential t.machine ≤ Machine.memoryPotential s.machine)
      (fun t => Machine.memoryPotential t.machine ≤ Machine.memoryPotential s.machine)
      (PlainOp.runCore pc ctx s op) :=
  Family.run_memoryPotential (PlainOp.family op) ⟨pc, ctx, s⟩

end Jaune
