import Jaune.MessageCall.CheckedMemoryCosts

/-! # The memory potential during a plain instruction -/

namespace Jaune.Checked
open Jaune

private abbrev Within (n : Nat) (m : Machine) := Machine.memoryPotential m ≤ n
private abbrev StateWithin (n : Nat) (s : Frame.State) := Within n s.machine

private theorem Machine.charge_within (c : Nat) {m : Machine} {n : Nat} (h : Within n m) :
    MWalk (Within n) (Within n) (m.chargeGas c) := by
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
  all_goals first | exact result | (simp only [MWalk.ok_iff] at result; have $name := result)))

private theorem Machine.popToAddress_within  {m : Machine} {n : Nat} (h : Within n m) :
    MWalk (Within n) (fun p => Within n p.2) (m.popToAddress) := by
  unfold Machine.popToAddress
  have hp := Machine.pop_memoryPotential h
  split <;> rename_i he <;> rw [he] at hp <;> exact hp

private theorem Machine.popN_within (k : Nat) {m : Machine} {n : Nat} (h : Within n m) :
    MWalk (Within n) (fun p => Within n p.2) (m.popN k) := by
  induction k generalizing m with
  | zero => exact h
  | succ k ih =>
    unfold Machine.popN
    next_stack hp (Machine.pop_memoryPotential h)
    have hp' := ih hp
    split <;> rename_i he <;> rw [he] at hp' <;> exact hp'

private theorem Frame.State.popN_within (k : Nat) {s : Frame.State} {n : Nat} (h : StateWithin n s) :
    Walk (StateWithin n) (fun p => StateWithin n p.2) (s.popN k) :=
  Walk.liftMachineValue (core := fun m => m.popN k) (Machine.popN_within k h)

private theorem Machine.push_within (x : U256) {m : Machine} {n : Nat} (h : Within n m) :
    MWalk (Within n) (Within n) (m.push x) := by
  unfold Machine.push
  split <;> exact h

theorem Frame.State.push_memoryPotential (x : U256) {s : Frame.State} {n : Nat}
    (h : Machine.memoryPotential s.machine ≤ n) :
    Walk (fun t => Machine.memoryPotential t.machine ≤ n) (fun t => Machine.memoryPotential t.machine ≤ n) (s.push x) :=
  Walk.liftMachine (core := fun m => m.push x) (Machine.push_within x h)

private theorem Machine.pushItem_within (x : U256) (c : Nat) {m : Machine} {n : Nat} (h : Within n m) :
    MWalk (Within n) (Within n) (m.pushItem x c) := by
  unfold Machine.pushItem
  next_stack hp (Machine.charge_within c h)
  exact Machine.push_within x hp

private theorem Frame.State.pushItem_within (x : U256) (c : Nat) {s : Frame.State} {n : Nat} (h : StateWithin n s) :
    Walk (StateWithin n) (StateWithin n) (s.pushItem x c) :=
  Walk.liftMachine (core := fun m => m.pushItem x c) (Machine.pushItem_within x c h)

private theorem Machine.applyUnary_within (f : U256 → U256) (c : Nat) {m : Machine} {n : Nat} (h : Within n m) :
    MWalk (Within n) (Within n) (m.applyUnary f c) := by
  unfold Machine.applyUnary
  next_stack hp (Machine.pop_memoryPotential h)
  exact Machine.pushItem_within _ _ hp

private theorem Frame.State.applyUnary_within (f : U256 → U256) (c : Nat) {s : Frame.State} {n : Nat} (h : StateWithin n s) :
    Walk (StateWithin n) (StateWithin n) (s.applyUnary f c) :=
  Walk.liftMachine (core := fun m => m.applyUnary f c) (Machine.applyUnary_within f c h)

private theorem Machine.applyBinary_within (f : U256 → U256 → U256) (c : Nat) {m : Machine} {n : Nat} (h : Within n m) :
    MWalk (Within n) (Within n) (m.applyBinary f c) := by
  unfold Machine.applyBinary
  next_stack hp (Machine.pop_memoryPotential h)
  next_stack hp (Machine.pop_memoryPotential hp)
  exact Machine.pushItem_within _ _ hp

private theorem Frame.State.applyBinary_within (f : U256 → U256 → U256) (c : Nat) {s : Frame.State} {n : Nat} (h : StateWithin n s) :
    Walk (StateWithin n) (StateWithin n) (s.applyBinary f c) :=
  Walk.liftMachine (core := fun m => m.applyBinary f c) (Machine.applyBinary_within f c h)

private theorem Machine.applyTernary_within (f : U256 → U256 → U256 → U256) (c : Nat) {m : Machine} {n : Nat} (h : Within n m) :
    MWalk (Within n) (Within n) (m.applyTernary f c) := by
  unfold Machine.applyTernary
  next_stack hp (Machine.pop_memoryPotential h)
  next_stack hp (Machine.pop_memoryPotential hp)
  next_stack hp (Machine.pop_memoryPotential hp)
  exact Machine.pushItem_within _ _ hp

private theorem Frame.State.applyTernary_within (f : U256 → U256 → U256 → U256) (c : Nat) {s : Frame.State} {n : Nat} (h : StateWithin n s) :
    Walk (StateWithin n) (StateWithin n) (s.applyTernary f c) :=
  Walk.liftMachine (core := fun m => m.applyTernary f c) (Machine.applyTernary_within f c h)


private theorem Machine.charge_extend_within (pairs : List (Nat × Nat)) (base : Nat)
    {m : Machine} {n : Nat} (h : Within n m) :
    MWalk (Within n) (fun t => Within n (t.memExtends pairs)) (m.chargeGas (base + m.extCost pairs)) := by
  have hc := Machine.chargeGas_memoryPotential m pairs base
  cases he : m.chargeGas (base + m.extCost pairs) with
  | error e => rw [he] at hc; change e.2 = m at hc; change Within n e.2; rwa [hc]
  | ok t =>
    rw [he] at hc
    change Machine.memoryPotential (t.memExtends pairs) + base = Machine.memoryPotential m at hc
    change Machine.memoryPotential (t.memExtends pairs) ≤ n
    exact (Nat.le_add_right _ _).trans (hc.le.trans h)

private theorem list_slice_length (bytes : List UInt8) (index size : Nat)
    (defaultByte : UInt8) : (List.sliceD bytes index size defaultByte).length = size := by
  induction size generalizing index with
  | zero => rfl
  | succ size ih => rw [List.sliceD_succ, List.length_cons, ih]

private theorem write_within (m : Machine) (i size : Nat) (bs : Bytes) (n : Nat)
    (hs : bs.length = size) (h : Within n (m.memExtends [(i, size)])) : Within n (m.memWrite i bs) := by
  subst size
  exact (Machine.memWrite_memoryPotential m i bs).trans h

private theorem copy_within (m : Machine) (src dst size n : Nat)
    (h : Within n (m.memExtends [(src, size), (dst, size)])) :
    Within n ((m.memRead src size).2.memWrite dst (m.memRead src size).1) := by
  apply write_within (size := size)
  · exact memory_slice_length _ _ _ _
  · exact h

local macro "potential_leaf" : tactic => `(tactic| first
  | assumption
  | exact Nat.le_refl _
  | (apply write_within <;> first | assumption | rfl | exact list_slice_length .. | exact Jaune.ByteArray.length_sliceD ..)
  | (apply copy_within; assumption)
  | (exact (Machine.memoryPotential_le_extended ..).trans (by assumption))
  | (solve | simp only [Walk.ok_iff, Walk.error_iff, MWalk.ok_iff, MWalk.error_iff] at * <;> assumption))

local macro "potential_known" : tactic => `(tactic| first
  | (apply Machine.charge_extend_within; potential_leaf)
  | (apply Machine.push_within; potential_leaf)
  | (apply Machine.pushItem_within; potential_leaf)
  | (apply Machine.applyUnary_within; potential_leaf)
  | (apply Machine.applyBinary_within; potential_leaf)
  | (apply Machine.applyTernary_within; potential_leaf)
  | (apply Machine.pop_memoryPotential; potential_leaf)
  | (apply Machine.popToNat_memoryPotential; potential_leaf)
  | (apply Machine.popToAddress_within; potential_leaf)
  | (apply Machine.popN_within; potential_leaf)
  | (apply Machine.charge_within; potential_leaf)
  | (apply Frame.State.push_memoryPotential; potential_leaf)
  | (apply Frame.State.pushItem_within; potential_leaf)
  | (apply Frame.State.applyUnary_within; potential_leaf)
  | (apply Frame.State.applyBinary_within; potential_leaf)
  | (apply Frame.State.applyTernary_within; potential_leaf)
  | (apply Frame.State.pop_memoryPotential; potential_leaf)
  | (apply Frame.State.popToNat_memoryPotential; potential_leaf)
  | (apply Frame.State.popToAddress_memoryPotential; potential_leaf)
  | (apply Frame.State.popN_within; potential_leaf)
  | (apply Frame.State.chargeGas_memoryPotential; potential_leaf)
  | (apply MWalk.assert (H := Within _); potential_leaf)
  | (apply Walk.assert (H := StateWithin _); potential_leaf))

local macro "potential_walk" : tactic => `(tactic| repeat' first
  | potential_leaf
  | potential_known
  | (apply MWalk.bind (by potential_known); first | intro ⟨_, _⟩ _ | intro _ _; try dsimp only at *)
  | (apply Walk.bind (by potential_known); first | intro ⟨_, _⟩ _ | intro _ _; try dsimp only at *)
  | (apply Walk.liftMachine (Hm := Within _) (Pm := Within _))
  | split)

private theorem mload_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .mload) := by
  simp only [PlainOp.runCore]
  potential_walk

private theorem mstore_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .mstore) := by
  simp only [PlainOp.runCore]
  potential_walk

private theorem mstore8_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .mstore8) := by
  simp only [PlainOp.runCore]
  potential_walk

local macro "copy_operands" dst:ident src:ident size:ident bound:ident : tactic => `(tactic| (
  refine MWalk.bind (Machine.popToNat_memoryPotential (Nat.le_refl _)) ?_
  intro ⟨$dst, m₁⟩ h₁
  refine MWalk.bind (Machine.popToNat_memoryPotential h₁) ?_
  intro ⟨$src, m₂⟩ h₂
  refine MWalk.bind (Machine.popToNat_memoryPotential h₂) ?_
  intro ⟨$size, m₃⟩ $bound))

private theorem calldatacopy_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .calldatacopy) := by
  simp only [PlainOp.runCore]
  apply Walk.liftMachine (Hm := Within _) (Pm := Within _)
  copy_operands dst src size h₃
  refine MWalk.bind (Machine.charge_extend_within [(dst, size)] _ h₃) ?_
  intro m₄ h₄
  exact write_within _ _ size _ _ (list_slice_length ..) h₄

private theorem codecopy_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .codecopy) := by
  simp only [PlainOp.runCore]
  apply Walk.liftMachine (Hm := Within _) (Pm := Within _)
  copy_operands dst src size h₃
  refine MWalk.bind (Machine.charge_extend_within [(dst, size)] _ h₃) ?_
  intro m₄ h₄
  exact write_within _ _ size _ _ (Jaune.ByteArray.length_sliceD ..) h₄

private theorem returndatacopy_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .returndatacopy) := by
  simp only [PlainOp.runCore]
  apply Walk.liftMachine (Hm := Within _) (Pm := Within _)
  copy_operands dst src size h₃
  refine MWalk.bind (Machine.charge_extend_within [(dst, size)] _ h₃) ?_
  intro m₄ h₄
  split
  · exact (Machine.memoryPotential_le_extended _ _).trans h₄
  · exact write_within _ _ size _ _ (list_slice_length ..) h₄

private theorem mcopy_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .mcopy) := by
  simp only [PlainOp.runCore]
  apply Walk.liftMachine (Hm := Within _) (Pm := Within _)
  split
  case isFalse => exact Nat.le_refl _
  copy_operands dst src size h₃
  refine MWalk.bind (Machine.charge_extend_within [(src, size), (dst, size)] _ h₃) ?_
  intro m₄ h₄
  exact copy_within _ _ _ _ _ h₄

private theorem keccak256_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .keccak256) := by
  simp only [PlainOp.runCore]
  potential_walk

private theorem sstoreBerlin_memory (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.sstoreBerlin ctx s) := by
  unfold PlainOp.sstoreBerlin
  refine Walk.bind (Frame.State.pop_memoryPotential (Nat.le_refl _)) ?_
  intro ⟨key, s₁⟩ h₁
  refine Walk.bind (Frame.State.pop_memoryPotential h₁) ?_
  intro ⟨value, s₂⟩ h₂
  refine Walk.bind (Walk.assert (H := (StateWithin (Machine.memoryPotential s.machine))) h₂) ?_
  intro _ _
  dsimp only at *
  refine Walk.bind (Frame.State.chargeGas_memoryPotential _ ?_) ?_
  · split <;> exact h₂
  · intro s₃ h₃
    refine Walk.bind (Walk.assert (H := (StateWithin (Machine.memoryPotential s.machine))) h₃) ?_
    intro _ _
    exact h₃

private theorem sstoreLegacy_memory (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.sstoreLegacy ctx s) := by
  unfold PlainOp.sstoreLegacy
  refine Walk.bind (Frame.State.pop_memoryPotential (Nat.le_refl _)) ?_
  intro ⟨key, s₁⟩ h₁
  refine Walk.bind (Frame.State.pop_memoryPotential h₁) ?_
  intro ⟨value, s₂⟩ h₂
  refine Walk.bind (Walk.assert (H := (StateWithin (Machine.memoryPotential s.machine))) h₂) ?_
  intro _ _
  dsimp only at *
  refine Walk.bind (Frame.State.chargeGas_memoryPotential _ ?_) ?_
  · split <;> first | exact h₂ | (split <;> exact h₂)
  · intro s₃ h₃
    refine Walk.bind (Walk.assert (H := (StateWithin (Machine.memoryPotential s.machine))) h₃) ?_
    intro _ _
    exact h₃



private theorem log_memory (k : Fin 5) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.liftLog (PlainOp.logStep k ctx) s) := by
  have core : MWalk (Within (Machine.memoryPotential s.machine)) (fun p => Within (Machine.memoryPotential s.machine) p.1)
      (PlainOp.logStep k ctx s.machine) := by
    unfold PlainOp.logStep
    refine MWalk.bind (Machine.popToNat_memoryPotential (Nat.le_refl _)) ?_
    intro ⟨start, m₁⟩ h₁
    refine MWalk.bind (Machine.popToNat_memoryPotential h₁) ?_
    intro ⟨size, m₂⟩ h₂
    refine MWalk.bind (Machine.popN_within _ h₂) ?_
    intro ⟨topics, m₃⟩ h₃
    refine MWalk.bind (Machine.charge_extend_within [(start, size)] _ h₃) ?_
    intro m₄ h₄
    refine MWalk.bind (MWalk.assert (H := Within _) ((Machine.memoryPotential_le_extended _ _).trans h₄)) ?_
    intro _ _; exact h₄
  unfold PlainOp.liftLog
  split <;> rename_i he <;> rw [he] at core <;> exact core

private theorem extcodecopy_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .extcodecopy) := by
  unfold PlainOp.runCore
  refine Walk.bind (Frame.State.popToAddress_memoryPotential (Nat.le_refl _)) ?_
  intro ⟨adr, s₁⟩ h₁
  refine Walk.bind (Frame.State.popToNat_memoryPotential h₁) ?_
  intro ⟨dst, s₂⟩ h₂
  refine Walk.bind (Frame.State.popToNat_memoryPotential h₂) ?_
  intro ⟨src, s₃⟩ h₃
  refine Walk.bind (Frame.State.popToNat_memoryPotential h₃) ?_
  intro ⟨size, s₄⟩ h₄
  dsimp only
  split <;> try split
  all_goals
    first
    | refine Walk.bind (Frame.State.chargeGas_extend_memoryPotential [(dst, size)] _ h₄) ?_
    | refine Walk.bind (Frame.State.chargeGas_extend_memoryPotential (s := s₄.addAccessedAddress adr) [(dst, size)] _ h₄) ?_
    intro s₅ h₅
    apply write_within (size := size)
    · exact Jaune.ByteArray.length_sliceD ..
    · exact (Nat.le_add_right _ _).trans h₅


local macro "plain_memory " name:ident " for " op:term : command =>
  `(private theorem $name (pc : Nat) (ctx : CallContext) (s : Frame.State) (hn : ctx.block.rules.stateGas = none) :
      Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
        (PlainOp.runCore pc ctx s $op) := by
      simp only [PlainOp.runCore, hn]
      potential_walk)

plain_memory calldataload_memory for .calldataload
plain_memory blockhash_memory for .blockhash
plain_memory pop_memory for .pop
plain_memory gas_memory for .gas
plain_memory exp_memory for .exp
plain_memory blobhash_memory for .blobhash

local macro "access_charge_push" bound:term : tactic => `(tactic| (
  dsimp only
  split <;> try split
  all_goals
    refine Walk.bind (Frame.State.chargeGas_memoryPotential _ ?_) ?_
    · exact $bound
    · intro u hu
      apply Frame.State.push_memoryPotential
      exact hu))

private theorem balance_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .balance) := by
  simp only [PlainOp.runCore]
  refine Walk.bind (Frame.State.popToAddress_memoryPotential (Nat.le_refl _)) ?_
  intro ⟨k, t⟩ ht
  access_charge_push ht

private theorem extcodesize_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .extcodesize) := by
  simp only [PlainOp.runCore]
  refine Walk.bind (Frame.State.popToAddress_memoryPotential (Nat.le_refl _)) ?_
  intro ⟨k, t⟩ ht
  access_charge_push ht

private theorem extcodehash_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .extcodehash) := by
  simp only [PlainOp.runCore]
  split
  case isFalse => exact Nat.le_refl _
  refine Walk.bind (Frame.State.popToAddress_memoryPotential (Nat.le_refl _)) ?_
  intro ⟨k, t⟩ ht
  access_charge_push ht

plain_memory selfbalance_memory for .selfbalance
private theorem sload_memory (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    Walk (StateWithin (Machine.memoryPotential s.machine)) (StateWithin (Machine.memoryPotential s.machine))
      (PlainOp.runCore pc ctx s .sload) := by
  simp only [PlainOp.runCore]
  refine Walk.bind (Frame.State.pop_memoryPotential (Nat.le_refl _)) ?_
  intro ⟨k, t⟩ ht
  access_charge_push ht

plain_memory tload_memory for .tload
plain_memory tstore_memory for .tstore

/-- A plain instruction can spend the frame’s gas and expand memory up to its original potential. -/
theorem PlainOp.runCore_memoryPotential (pc : Nat) (ctx : CallContext) (s : Frame.State) (op : Jaune.PlainOp)
    (hn : ctx.block.rules.stateGas = none) :
    Walk (fun t => Machine.memoryPotential t.machine ≤ Machine.memoryPotential s.machine)
      (fun t => Machine.memoryPotential t.machine ≤ Machine.memoryPotential s.machine)
      (PlainOp.runCore pc ctx s op) := by
  cases op
  case mload => exact mload_memory pc ctx s
  case mstore => exact mstore_memory pc ctx s
  case mstore8 => exact mstore8_memory pc ctx s
  case calldatacopy => exact calldatacopy_memory pc ctx s
  case codecopy => exact codecopy_memory pc ctx s
  case returndatacopy => exact returndatacopy_memory pc ctx s
  case mcopy => exact mcopy_memory pc ctx s
  case keccak256 => exact keccak256_memory pc ctx s
  case extcodecopy => exact extcodecopy_memory pc ctx s
  case calldataload => exact calldataload_memory pc ctx s hn
  case blockhash => exact blockhash_memory pc ctx s hn
  case pop => exact pop_memory pc ctx s hn
  case gas => exact gas_memory pc ctx s hn
  case exp => exact exp_memory pc ctx s hn
  case blobhash => exact blobhash_memory pc ctx s hn
  case balance => exact balance_memory pc ctx s
  case extcodesize => exact extcodesize_memory pc ctx s
  case extcodehash => exact extcodehash_memory pc ctx s
  case selfbalance => exact selfbalance_memory pc ctx s hn
  case sload => exact sload_memory pc ctx s
  case tload => exact tload_memory pc ctx s hn
  case tstore => exact tstore_memory pc ctx s hn
  case sstore =>
    simp only [PlainOp.runCore, hn]
    split <;> first | apply sstoreBerlin_memory | apply sstoreLegacy_memory
  case log => apply log_memory
  case dup n | swap n =>
    simp only [PlainOp.runCore]
    apply Walk.liftMachine (Hm := Within _) (Pm := Within _)
    refine MWalk.bind (Machine.charge_within _ (Nat.le_refl _)) ?_
    intro m h; split <;> first | exact h | exact Machine.push_within _ h
  all_goals simp only [PlainOp.runCore]
  all_goals first
    | exact Frame.State.pushItem_within _ _ (Nat.le_refl _)
    | exact Frame.State.applyUnary_within _ _ (Nat.le_refl _)
    | exact Frame.State.applyBinary_within _ _ (Nat.le_refl _)
    | exact Frame.State.applyTernary_within _ _ (Nat.le_refl _)
    | (apply Walk.liftMachine (Hm := Within _) (Pm := Within _)
       split <;> first
       | exact Nat.le_refl _
       | exact Machine.pushItem_within _ _ (Nat.le_refl _)
       | exact Machine.applyBinary_within _ _ (Nat.le_refl _)
       | exact Machine.applyUnary_within _ _ (Nat.le_refl _))

end Jaune.Checked
