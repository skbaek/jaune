import Jaune.CheckedSufficiencyWalk
import Jaune.MemoryAccounting
import Jaune.GasFacts

/-! # Memory expansion paid by the staged machine

The potential combines execution gas, recoverable gas and the price of the current
memory size. Charging an access pays for the full extension before any byte is read or written.
-/

namespace Jaune.Checked
open Jaune

def Machine.memoryPotential (m : Machine) : Nat :=
  m.gasMeasure + calculateMemoryGasCost m.memory.size

/-- The charge for an access pays its complete rounded expansion on success.
A failure leaves the machine and its potential untouched. -/
theorem Machine.chargeGas_memoryPotential (m : Machine) (pairs : List (Nat × Nat))
    (base : Nat) :
    MWalk (· = m) (fun m' => Machine.memoryPotential (m'.memExtends pairs) + base =
      Machine.memoryPotential m) (m.chargeGas (base + m.extCost pairs)) := by
  have hmono := calculateMemoryGasCost_mono (memExtsSize_ge m.memory.size pairs)
  unfold Machine.chargeGas safeSub
  split
  · rfl
  · rename_i gas hg
    split at hg
    · cases hg
      simp only [MWalk.ok_iff]
      change (m.gasLeft - (base + (calculateMemoryGasCost (memExtsSize m.memory.size pairs) -
        calculateMemoryGasCost m.memory.size)) + m.stateGas.spilled + m.stateGas.committedSpill +
        calculateMemoryGasCost (memExtsSize m.memory.size pairs)) + base =
        m.gasLeft + m.stateGas.spilled + m.stateGas.committedSpill + calculateMemoryGasCost m.memory.size
      simp only [Machine.extCost] at *
      omega
    · cases hg

theorem Machine.memRead_memoryPotential (m : Machine) (i n : Nat) :
    Machine.memoryPotential (m.memRead i n).2 = Machine.memoryPotential (m.memExtends [(i, n)]) := rfl

private theorem ceil32_eq_ceilDiv32 (n : Nat) : ceil32 n = 32 * ceilDiv n 32 := by
  by_cases hz : n % 32 = 0
  · simp only [ceil32, ceilDiv, hz, ite_true, Nat.add_zero]
    omega
  · simp only [ceilDiv, ite_eq_right hz]
    unfold ceil32
    split
    · contradiction
    · omega

private theorem memory_write_size_le_ext (memory : Memory) (index : Nat) (bytes : Bytes) :
    (memory.write index bytes).size ≤ memExtSize memory.size index bytes.length := by
  cases bytes with
  | nil => exact Nat.le_refl _
  | cons byte bytes =>
      simp only [Memory.write]
      split
      · split <;> exact memExtSize_ge memory.size index (byte :: bytes).length
      · change ceil32 (index + (byte :: bytes).length) ≤
          memExtSize memory.size index (byte :: bytes).length
        have hn : (byte :: bytes).length ≠ 0 := by
          simp only [List.length_cons]
          omega
        rw [ceil32_eq_ceilDiv32]
        simp only [memExtSize, ite_eq_right hn]
        exact Nat.mul_le_mul_left 32 (Nat.le_max_right _ _)

theorem Machine.memWrite_memoryPotential (m : Machine) (i : Nat) (bs : Bytes) :
    Machine.memoryPotential (m.memWrite i bs) ≤ Machine.memoryPotential (m.memExtends [(i, bs.length)]) :=
  Nat.add_le_add_left (calculateMemoryGasCost_mono (memory_write_size_le_ext _ _ _)) _

theorem Machine.memoryPotential_le_extended (m : Machine) (pairs : List (Nat × Nat)) :
    Machine.memoryPotential m ≤ Machine.memoryPotential (m.memExtends pairs) :=
  Nat.add_le_add_left (calculateMemoryGasCost_mono (memExtsSize_ge _ _)) _


/-- Erasing or converting a popped word leaves the potential unchanged. -/
theorem Machine.pop_memoryPotential {m : Machine} {n : Nat} (h : Machine.memoryPotential m ≤ n) :
    MWalk (fun s => Machine.memoryPotential s ≤ n) (fun p => Machine.memoryPotential p.2 ≤ n) m.pop := by
  unfold Machine.pop
  split <;> exact h

theorem Frame.State.pop_memoryPotential {s : Frame.State} {n : Nat} (h : Machine.memoryPotential s.machine ≤ n) :
    Walk (fun s => Machine.memoryPotential s.machine ≤ n) (fun p => Machine.memoryPotential p.2.machine ≤ n)
      s.pop := Walk.liftMachineValue (Machine.pop_memoryPotential h)

theorem Machine.popToNat_memoryPotential {m : Machine} {n : Nat} (h : Machine.memoryPotential m ≤ n) :
    MWalk (fun s => Machine.memoryPotential s ≤ n) (fun p => Machine.memoryPotential p.2 ≤ n) m.popToNat := by
  unfold Machine.popToNat
  have hp := Machine.pop_memoryPotential h
  split <;> rename_i he <;> rw [he] at hp <;> exact hp

theorem Frame.State.popToNat_memoryPotential {s : Frame.State} {n : Nat}
    (h : Machine.memoryPotential s.machine ≤ n) :
    Walk (fun s => Machine.memoryPotential s.machine ≤ n) (fun p => Machine.memoryPotential p.2.machine ≤ n)
      s.popToNat := Walk.liftMachineValue (Machine.popToNat_memoryPotential h)

theorem Frame.State.popToAddress_memoryPotential {s : Frame.State} {n : Nat}
    (h : Machine.memoryPotential s.machine ≤ n) :
    Walk (fun s => Machine.memoryPotential s.machine ≤ n) (fun p => Machine.memoryPotential p.2.machine ≤ n)
      s.popToAddress := by
  apply Walk.liftMachineValue (Hm := fun m => Machine.memoryPotential m ≤ n)
    (Pm := fun p => Machine.memoryPotential p.2 ≤ n)
  unfold Machine.popToAddress
  have hp := Machine.pop_memoryPotential h
  split <;> rename_i he <;> rw [he] at hp <;> exact hp

/-- Charging a base cost and an expansion keeps the extended machine within the initial budget. -/
theorem Frame.State.chargeGas_extend_memoryPotential {s : Frame.State} {n : Nat}
    (pairs : List (Nat × Nat)) (base : Nat) (h : Machine.memoryPotential s.machine ≤ n) :
    Walk (fun t => Machine.memoryPotential t.machine ≤ n)
      (fun t => Machine.memoryPotential (t.machine.memExtends pairs) + base ≤ n)
      (s.chargeGas (base + s.extCost pairs)) := by
  have hc := @Walk.liftMachine ExceptionalHalt (· = s.machine)
    (fun m => Machine.memoryPotential (m.memExtends pairs) + base = Machine.memoryPotential s.machine)
    (fun m => m.chargeGas (base + s.extCost pairs)) s (Machine.chargeGas_memoryPotential s.machine pairs base)
  apply Walk.mono' hc
  · intro t ht; rwa [ht]
  · intro t ht; rwa [ht]

theorem Frame.State.chargeGas_memoryPotential {s : Frame.State} {n : Nat} (base : Nat)
    (h : Machine.memoryPotential s.machine ≤ n) :
    Walk (fun t => Machine.memoryPotential t.machine ≤ n) (fun t => Machine.memoryPotential t.machine ≤ n)
      (s.chargeGas base) := by
  have hp := Frame.State.chargeGas_extend_memoryPotential [] base h
  have hzero : s.extCost [] = 0 := Nat.sub_self _
  rw [hzero, Nat.add_zero] at hp
  apply Walk.mono hp
  intro t ht
  change Machine.memoryPotential t.machine + base ≤ n at ht
  omega


theorem memory_slice_length (xs : Array UInt8) (index size : Nat)
    (defaultByte : UInt8) : (Array.sliceD xs index size defaultByte).length = size := by
  have aux (acc : List UInt8) (n : Nat) :
      (Array.sliceD.aux xs acc index n defaultByte).length = acc.length + n := by
    induction n generalizing acc with
    | zero => rfl
    | succ n ih =>
      change (Array.sliceD.aux xs (xs.getD (index + n) defaultByte :: acc)
        index n defaultByte).length = _
      rw [ih, List.length_cons]
      omega
  simpa only [Array.sliceD, List.length_nil, Nat.zero_add] using aux [] size


/-- A halt returns within the starting potential and the cost of its output fits that potential. -/
def Frame.Exit.MemoryAccounted (n : Nat) (e : Frame.Exit) : Prop :=
  Machine.memoryPotential e.state.machine ≤ n ∧ calculateMemoryGasCost e.output.length ≤ n

private def exitMemory (n : Nat) : Except Fault Frame.Exit → Prop
  | .error _ => True
  | .ok exit => Frame.Exit.MemoryAccounted n exit

private theorem zeroOutputCost (n : Nat) : calculateMemoryGasCost 0 ≤ n := by
  change 0 ≤ n
  exact Nat.zero_le _

private theorem catchHalt_memory {n : Nat} {x} (hx : Walk (fun s => Machine.memoryPotential s.machine ≤ n)
    (exitMemory n) x) : exitMemory n (Frame.Exit.catchHalt x) := by
  cases x with
  | error e => cases e; exact ⟨hx, zeroOutputCost _⟩
  | ok result => exact hx

private theorem memRead_output_cost (m : Machine) (start size : Nat) :
    calculateMemoryGasCost (m.memRead start size).1.length ≤ Machine.memoryPotential (m.memExtends [(start, size)]) := by
  change calculateMemoryGasCost (Jaune.Array.sliceD m.memory.data start size 0).length ≤ _
  rw [memory_slice_length]
  apply Nat.le_trans (calculateMemoryGasCost_mono (b := memExtSize m.memory.size start size) ?_)
    (Nat.le_add_left _ _)
  by_cases hn : size = 0
  · rw [hn]; exact Nat.zero_le _
  · exact Nat.le_trans (Nat.le_add_left _ _) (memExtSize_access_le _ _ _ hn)

private theorem Frame.State.chargeGas_read {s : Frame.State} {n start size : Nat}
    (h : Machine.memoryPotential s.machine ≤ n) :
    Walk (fun t => Machine.memoryPotential t.machine ≤ n)
      (fun t => Machine.memoryPotential (t.memRead start size).2.machine ≤ n ∧
        calculateMemoryGasCost (t.memRead start size).1.length ≤ n)
      (s.chargeGas (s.extCost [(start, size)])) := by
  have hc := Frame.State.chargeGas_extend_memoryPotential [(start, size)] 0 h
  simp only [Nat.zero_add, Nat.add_zero] at hc
  apply Walk.mono hc
  intro t ht
  exact ⟨ht, (memRead_output_cost t.machine start size).trans ht⟩

private theorem creditBeneficiary_memoryPotential (rules : ForkRules) (a : Address) (v : U256) (s : Frame.State) :
    Machine.memoryPotential (s.creditBeneficiary rules a v).machine = Machine.memoryPotential s.machine := by
  unfold Frame.State.creditBeneficiary
  split <;> rfl

private theorem selfdestruct_memory (ctx : CallContext) (s : Frame.State)
    (hn : ctx.block.rules.stateGas = none) :
    exitMemory (Machine.memoryPotential s.machine) (HaltOp.run ctx s .selfdestruct) := by
  simp only [HaltOp.run, hn]
  apply catchHalt_memory
  refine Walk.bind (Frame.State.popToAddress_memoryPotential (Nat.le_refl _)) ?_
  intro ⟨donee, s₁⟩ h₁
  dsimp only at *
  refine Walk.bind (Frame.State.chargeGas_memoryPotential _ ?_) ?_
  · split <;> first | exact h₁ | (split <;> exact h₁)
  · intro s₂ h₂
    refine Walk.bind (Walk.assert (H := fun t => Machine.memoryPotential t.machine ≤ _) h₂) ?_
    intro _ _
    unfold Frame.State.subtractBalance
    cases hs : s₂.world.subtractBalance ctx.recipient _ with
    | none => trivial
    | some world =>
      dsimp only [Option.map]
      split
      · unfold Frame.State.creditSelfdestructRefund
        split <;> exact ⟨le_of_eq_of_le (creditBeneficiary_memoryPotential _ _ _ _) h₂, zeroOutputCost _⟩
      · exact ⟨le_of_eq_of_le (creditBeneficiary_memoryPotential _ _ _ _) h₂, zeroOutputCost _⟩

theorem HaltOp.run_memory_accounting_output (ctx : CallContext) (s : Frame.State) (op : Jaune.HaltOp)
    (hn : ctx.block.rules.stateGas = none) {e : Frame.Exit} (h : HaltOp.run ctx s op = .ok e) :
    Frame.Exit.MemoryAccounted (Machine.memoryPotential s.machine) e := by
  suffices hp : exitMemory (Machine.memoryPotential s.machine) (HaltOp.run ctx s op) by
    rw [h] at hp
    exact hp
  cases op with
  | stop => exact ⟨Nat.le_refl _, zeroOutputCost _⟩
  | selfdestruct => exact selfdestruct_memory ctx s hn
  | return_ | revert =>
    unfold HaltOp.run
    apply catchHalt_memory
    refine Walk.bind (Frame.State.popToNat_memoryPotential (Nat.le_refl _)) ?_
    intro ⟨start, s₁⟩ h₁
    refine Walk.bind (Frame.State.popToNat_memoryPotential h₁) ?_
    intro ⟨size, s₂⟩ h₂
    refine Walk.bind (Frame.State.chargeGas_read h₂) ?_
    intro s₃ h₃
    exact h₃


/-- Jumps can only spend execution gas. Any halt along the way stays within the same potential. -/
theorem JumpOp.runCore_memoryPotential (pc : Nat) (ctx : CallContext) (s : Frame.State) (op : Jaune.JumpOp) :
    Walk (fun t => Machine.memoryPotential t.machine ≤ Machine.memoryPotential s.machine)
      (fun p => Machine.memoryPotential p.2.machine ≤ Machine.memoryPotential s.machine)
      (JumpOp.runCore pc ctx s op) := by
  cases op <;> simp only [JumpOp.runCore]
  case jumpdest =>
    refine Walk.bind (Frame.State.chargeGas_memoryPotential _ (Nat.le_refl _)) ?_
    intro _ h; exact h
  case jump =>
    refine Walk.bind (Frame.State.pop_memoryPotential (Nat.le_refl _)) ?_
    intro ⟨dest, s₁⟩ h₁
    refine Walk.bind (Frame.State.chargeGas_memoryPotential _ h₁) ?_
    intro s₂ h₂
    refine Walk.bind (Walk.assert (H := fun t => Machine.memoryPotential t.machine ≤ _) h₂) ?_
    intro _ _; exact h₂
  case jumpi =>
    refine Walk.bind (Frame.State.pop_memoryPotential (Nat.le_refl _)) ?_
    intro ⟨dest, s₁⟩ h₁
    refine Walk.bind (Frame.State.pop_memoryPotential h₁) ?_
    intro ⟨cond, s₂⟩ h₂
    refine Walk.bind (Frame.State.chargeGas_memoryPotential _ h₂) ?_
    intro s₃ h₃
    split
    · exact h₃
    · refine Walk.bind (Walk.assert (H := fun t => Machine.memoryPotential t.machine ≤ _) h₃) ?_
      intro _ _; exact h₃

end Jaune.Checked
