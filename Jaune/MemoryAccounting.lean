import Jaune.Exec

namespace Jaune

/-! Exact accounting for memory charged before a legacy zero-value CALL.
These facts do not bound arbitrary initial parent gas or complete the recursive
memory/output invariant. -/

theorem calculateMsgCallGas_zero_child_le (gas gasLeft memoryCost extraGas cs : Nat) :
    (calculateMsgCallGas 0 gas gasLeft memoryCost extraGas cs).2 ≤ gas := by
  simp only [calculateMsgCallGas]
  split
  · exact Nat.le_refl gas
  · exact Nat.min_le_left _ _

theorem calculateMsgCallGas_zero_word_child_lt (gas : B256)
    (gasLeft memoryCost extraGas cs : Nat) :
    (calculateMsgCallGas 0 gas.toNat gasLeft memoryCost extraGas cs).2 < 2 ^ 256 :=
  Nat.lt_of_le_of_lt
    (calculateMsgCallGas_zero_child_le gas.toNat gasLeft memoryCost extraGas cs)
    (B256.toNat_lt gas)

private theorem ceilDiv32_le {a b : Nat} (h : a ≤ b) :
    ceilDiv a 32 ≤ ceilDiv b 32 := by
  simp only [ceilDiv]
  split <;> split <;> omega

private theorem le_ceilDiv32_mul (n : Nat) : n ≤ 32 * ceilDiv n 32 := by
  simp only [ceilDiv]
  split <;> omega

theorem memExtSize_ge (current index size : Nat) :
    current ≤ memExtSize current index size := by
  simp only [memExtSize]
  split
  · exact Nat.le_refl _
  · have h := le_ceilDiv32_mul current
    have hm := Nat.le_max_left (ceilDiv current 32) (ceilDiv (index + size) 32)
    omega

theorem memExtsSize_ge (current : Nat) (pairs : List (Nat × Nat)) :
    current ≤ memExtsSize current pairs := by
  induction pairs generalizing current with
  | nil => exact Nat.le_refl _
  | cons pair pairs ih =>
    exact Nat.le_trans (memExtSize_ge current pair.1 pair.2) (ih _)

theorem calculateMemoryGasCost_mono {a b : Nat} (h : a ≤ b) :
    calculateMemoryGasCost a ≤ calculateMemoryGasCost b := by
  have hw := ceilDiv32_le h
  have hq := Nat.div_le_div_right (c := 512) (Nat.pow_le_pow_left hw 2)
  simp only [calculateMemoryGasCost, gMemory]
  omega

theorem chargeGas_memory_size {cost : Nat} {before after : Devm}
    (h : chargeGas cost before = .ok after) : after.memory.size = before.memory.size := by
  rw [chargeGas_def] at h
  by_cases hc : cost ≤ before.gasLeft
  · simp only [safeSub, ite_eq_left hc, Except.ok.injEq] at h
    subst after
    rfl
  · simp only [safeSub, ite_eq_right hc] at h
    contradiction

/-- A successful charge retains the exact expansion cost; extending afterward
changes neither the gas meter nor the already charged cost. Zero-size accesses
are included by the actual `memExtSize` definition. -/
theorem charged_memExtends_accounting {before charged : Devm}
    (pairs : List (Nat × Nat)) (baseCost : Nat)
    (hcharge : chargeGas (baseCost + before.extCost pairs) before = .ok charged) :
    (charged.memExtends pairs).gasMeasure + baseCost +
        calculateMemoryGasCost (charged.memExtends pairs).memory.size =
      before.gasMeasure + calculateMemoryGasCost before.memory.size := by
  have hg := chargeGas_gasMeasure hcharge
  have hm := chargeGas_memory_size hcharge
  have hmono := calculateMemoryGasCost_mono (memExtsSize_ge before.memory.size pairs)
  have hs : (charged.memExtends pairs).memory.size =
      memExtsSize before.memory.size pairs := by
    change memExtsSize charged.memory.size pairs = _
    rw [hm]
  rw [Devm.memExtends_gasMeasure, hs]
  simp only [Devm.extCost] at hg
  omega

/-- A nonempty access is covered by the actual rounded expansion. -/
theorem memExtSize_access_le (current index size : Nat) (hsize : size ≠ 0) :
    index + size ≤ memExtSize current index size := by
  simp only [memExtSize, ite_eq_right hsize]
  have h := le_ceilDiv32_mul (index + size)
  have hm := Nat.le_max_right (ceilDiv current 32) (ceilDiv (index + size) 32)
  omega

/-- A copy into a prepaid window does not expand memory. Empty copies need
no restriction on their index. -/
theorem Mem.write_size_of_prepaid (mem : Mem) (index : Nat) (bytes : Bytes)
    (h : bytes ≠ [] → index + bytes.length ≤ mem.size) :
    (mem.write index bytes).size = mem.size := by
  cases bytes with
  | nil => rfl
  | cons b bs =>
    have hb : b :: bs ≠ [] := by intro heq; contradiction
    simp only [Mem.write, ite_eq_left (h hb)]
    split <;> rfl

theorem Devm.push_memory {word : B256} {before after : Devm}
    (h : before.push word = .ok after) : after.memory = before.memory := by
  rw [Devm.push_def] at h
  by_cases hs : before.stack.length < 1024
  · simp only [Except.assert, ite_eq_left hs, bind, Except.bind, Except.ok.injEq] at h
    subst after
    rfl
  · simp only [Except.assert, ite_eq_right hs, bind, Except.bind] at h
    contradiction

/-- Both success and revert use the actual settled child's output, truncated
by the parent's output size, and preserve the parent memory before that copy. -/
theorem Resume.call_run_ok_memory {parent child resumed : Devm}
    {outputIndex outputSize : Nat}
    (h : (Resume.call parent outputIndex outputSize).run (.ok child) = .ok resumed) :
    resumed.memory = parent.memory.write outputIndex (child.output.take outputSize) := by
  simp only [Resume.run, liftToExecution, bind, Except.bind] at h
  split at h
  · obtain ⟨pushed, hp, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst resumed
    change pushed.memory.write outputIndex _ = _
    rw [Devm.push_memory hp]
    rfl
  · obtain ⟨pushed, hp, h⟩ := Except.bind_eq_ok h
    simp only [Except.ok.injEq] at h
    subst resumed
    change pushed.memory.write outputIndex _ = _
    rw [Devm.push_memory hp]
    rfl

/-- Gas settlement for the same child derivation, using the existing total
interpreter's sufficiency proof rather than another recursive driver. -/
theorem Exec.settledGasLe {pc : Nat} {sevm : Sevm} {devm : Devm} {raw : Execution}
    (h : Exec pc sevm devm raw) : raw.SettledGasLe devm.gasMeasure := by
  have heq := (exec_iff_exec_eq pc sevm devm raw).mp ⟨h⟩
  have hs := execFueled_settledGasLe (sufficientFuel devm.gasMeasure)
    (⟨pc, sevm, devm⟩ : Evm) (execFueled_run_sufficientFuel ⟨pc, sevm, devm⟩)
  rw [heq] at hs
  exact hs

theorem calculateMsgCallGas_zero_value_cost (gas gasLeft memoryCost extraGas cs : Nat) :
    (calculateMsgCallGas 0 gas gasLeft memoryCost extraGas cs).1 =
      (calculateMsgCallGas 0 gas gasLeft memoryCost extraGas cs).2 + extraGas := by
  simp only [calculateMsgCallGas]
  split <;> rfl

/-- Invert the actual call spawn, retaining its caller and output window. -/
theorem genericCall.step_spawn_call {sevm : Sevm} {parent : Devm} {gas : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {frame : Frame} {resume : Resume}
    (h : genericCall.step sevm parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn frame resume) :
    frame.inner.gas = gas ∧
      resume = .call (parent.withReturnData []) outputIndex outputSize := by
  unfold genericCall.step at h
  split at h
  · have hx := XStep.ofExcept_spawn h
    obtain ⟨_, _, hx⟩ := Except.bind_eq_ok hx
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hx
    nomatch hx
  · simp only [XStep.spawn.injEq] at h
    rw [← h.1]
    exact ⟨rfl, h.2.symm⟩

/-- One genuine zero-value CALL spawn/run/settle/resume accounting clause.
The successful charge prepays the same input/output windows that the actual
spawn retains. The same child derivation supplies its settlement gas bound;
resumption copies exactly its truncated output without expanding parent memory.
This is a local clause, not the recursive child memory/output invariant. -/
theorem zero_call_spawn_resume_accounting
    {sevm : Sevm} {before charged resumed : Devm} (gas : B256)
    (extraGas cs inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume} {childEvm : Evm} {raw : Execution}
    (hcharge : chargeGas
      ((calculateMsgCallGas 0 gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas cs).1 +
        before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas 0 gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas cs).2 0 caller target codeAddress shouldTransferValue isStaticcall
      inputIndex inputSize outputIndex outputSize code disablePrecompiles =
        .spawn frame resume)
    (henter : frame.enter = .run childEvm)
    (hexec : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok resumed) :
    ∃ child : Devm, frame.settle raw = .ok child ∧
      child.gasMeasure ≤ gas.toNat ∧
      resumed.memory =
        (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).memory.write
          outputIndex (child.output.take outputSize) ∧
      resumed.memory.size =
        memExtsSize before.memory.size [(inputIndex, inputSize), (outputIndex, outputSize)] ∧
      resumed.gasMeasure + extraGas + calculateMemoryGasCost resumed.memory.size ≤
        before.gasMeasure + calculateMemoryGasCost before.memory.size := by
  let pairs := [(inputIndex, inputSize), (outputIndex, outputSize)]
  let costs := calculateMsgCallGas 0 gas.toNat before.gasLeft (before.extCost pairs) extraGas cs
  let parent := (charged.memExtends pairs).withReturnData []
  obtain ⟨hf, hrsm⟩ := genericCall.step_spawn_call hspawn
  change frame.inner.gas = costs.2 at hf
  change resume = .call parent outputIndex outputSize at hrsm
  have hs := hexec.settledGasLe
  rw [Frame.enter_run_gasMeasure henter] at hs
  obtain ⟨child, hsettle, hgas⟩ := Resume.run_ok_gasMeasure hresume
  have hchild := Frame.settle_gasLe hs hsettle
  rw [hf] at hchild
  have hcap := calculateMsgCallGas_zero_child_le gas.toNat before.gasLeft
    (before.extCost pairs) extraGas cs
  have hcopy := hresume
  rw [hrsm, hsettle] at hcopy
  have hmem := Resume.call_run_ok_memory hcopy
  change resumed.memory = (charged.memExtends pairs).memory.write
    outputIndex (child.output.take outputSize) at hmem
  have hprepaid : (child.output.take outputSize) ≠ [] →
      outputIndex + (child.output.take outputSize).length ≤ parent.memory.size := by
    intro hnonempty
    have hsize : outputSize ≠ 0 := by
      intro hz
      subst outputSize
      exact hnonempty rfl
    have hw := memExtSize_access_le
      (memExtSize charged.memory.size inputIndex inputSize) outputIndex outputSize hsize
    have ht := List.length_take_le outputSize child.output
    change outputIndex + (child.output.take outputSize).length ≤
      memExtSize (memExtSize charged.memory.size inputIndex inputSize) outputIndex outputSize
    omega
  have hmemsize : resumed.memory.size = (charged.memExtends pairs).memory.size := by
    rw [hmem]
    exact Mem.write_size_of_prepaid _ _ _ hprepaid
  have hcharged := chargeGas_memory_size hcharge
  have hsize : resumed.memory.size = memExtsSize before.memory.size pairs := by
    rw [hmemsize]
    change memExtsSize charged.memory.size pairs = _
    rw [hcharged]
  have hc : costs.1 = costs.2 + extraGas :=
    calculateMsgCallGas_zero_value_cost _ _ _ _ _
  have hcharge' : chargeGas ((costs.2 + extraGas) + before.extCost pairs) before =
      .ok charged := by
    rw [← hc]
    exact hcharge
  have haccount := charged_memExtends_accounting pairs (costs.2 + extraGas) hcharge'
  rw [hrsm] at hgas
  change resumed.gasMeasure ≤ parent.gasMeasure + child.gasMeasure at hgas
  have hparent : parent.gasMeasure = (charged.memExtends pairs).gasMeasure := rfl
  refine ⟨child, hsettle, Nat.le_trans hchild hcap, hmem, hsize, ?_⟩
  rw [hmemsize]
  omega

end Jaune
