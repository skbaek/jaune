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

/-- The CALL stipend adds at most its fixed amount to a word-sized requested
grant, including the underfunded branch of the gas calculator. -/
theorem calculateMsgCallGas_word_child_lt_with_stipend (value gas : B256)
    (gasLeft memoryCost extraGas : Nat) :
    (calculateMsgCallGas value.toNat gas.toNat gasLeft memoryCost extraGas
      gCallStipend).2 < 2 ^ 256 + gCallStipend := by
  have hg := B256.toNat_lt gas
  unfold calculateMsgCallGas
  by_cases hv : value.toNat = 0
  · simp only [hv, ite_true, Nat.add_zero]
    split
    · omega
    · have hm := Nat.min_le_left gas.toNat
        (except64th (gasLeft - memoryCost - extraGas))
      omega
  · simp only [hv, ite_false]
    split
    · omega
    · have hm := Nat.min_le_left gas.toNat
        (except64th (gasLeft - memoryCost - extraGas))
      omega

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

/-- The spawned CALL frame receives exactly the caller's selected input
window, including the zero-filled tail of a short memory read. -/
theorem genericCall.step_spawn_data {sevm : Sevm} {parent : Devm} {gas : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {frame : Frame} {resume : Resume}
    (h : genericCall.step sevm parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn frame resume) :
    frame.inner.data =
      Jaune.Array.sliceD (parent.withReturnData []).memory.data inputIndex inputSize 0 := by
  unfold genericCall.step at h
  split at h
  · have hx := XStep.ofExcept_spawn h
    obtain ⟨_, _, hx⟩ := Except.bind_eq_ok hx
    simp only [Pure.pure, Except.pure, Except.ok.injEq] at hx
    nomatch hx
  · simp only [XStep.spawn.injEq] at h
    rw [← h.1]
    rfl

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

private theorem memory_slice_length (xs : Array UInt8) (index size : Nat)
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

/-- The real spawned CALL input has the requested length, even when reading
beyond the caller's materialized memory. -/
theorem genericCall.step_spawn_data_length {sevm : Sevm} {parent : Devm} {gas : Nat}
    {value : B256} {caller target codeAddress : Adr}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {frame : Frame} {resume : Resume}
    (h : genericCall.step sevm parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn frame resume) :
    frame.inner.data.length = inputSize := by
  rw [genericCall.step_spawn_data h]
  exact memory_slice_length _ _ _ _

private theorem pop_memory_output (pre : Devm) :
    match pre.pop with
    | .error failure => failure.2.memory = pre.memory ∧ failure.2.output = pre.output
    | .ok result => result.2.memory = pre.memory ∧ result.2.output = pre.output := by
  rw [Devm.pop_def]
  cases pre.stack <;> exact ⟨rfl, rfl⟩

private theorem charge_memory_output (cost : Nat) (pre : Devm) :
    match chargeGas cost pre with
    | .error failure => failure.2.memory = pre.memory ∧ failure.2.output = pre.output
    | .ok post => post.memory = pre.memory ∧ post.output = pre.output := by
  rw [chargeGas_def]
  cases safeSub pre.gasLeft cost <;> exact ⟨rfl, rfl⟩

private theorem charged_read_accounting {pre charged : Devm} (index size : Nat)
    (hcharge : chargeGas (pre.extCost [(index, size)]) pre = .ok charged) :
    let post := (charged.memRead index size).2.withOutput (charged.memRead index size).1
    post.gasMeasure + calculateMemoryGasCost post.memory.size =
        pre.gasMeasure + calculateMemoryGasCost pre.memory.size ∧
      calculateMemoryGasCost post.output.length ≤
        pre.gasMeasure + calculateMemoryGasCost pre.memory.size := by
  have hc := charged_memExtends_accounting [(index, size)] 0
    (by simpa only [Nat.zero_add] using hcharge)
  let post := (charged.memRead index size).2.withOutput (charged.memRead index size).1
  have heq : post.gasMeasure + calculateMemoryGasCost post.memory.size =
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size := by
    have hs : (charged.memExtends [(index, size)]).memory.size = post.memory.size := rfl
    have hg : post.gasMeasure = charged.gasMeasure := rfl
    rw [Devm.memExtends_gasMeasure, Nat.add_zero, hs, ← hg] at hc
    exact hc
  have hlen : post.output.length = size := memory_slice_length charged.memory.data index size 0
  have hsize : size ≤ post.memory.size := by
    change size ≤ memExtSize charged.memory.size index size
    by_cases hz : size = 0
    · rw [hz]
      exact Nat.zero_le _
    · have hw := memExtSize_access_le charged.memory.size index size hz
      omega
  have hcost := calculateMemoryGasCost_mono hsize
  refine ⟨heq, ?_⟩
  rw [hlen]
  omega

/-- Terminal instructions preserve the charged memory/gas potential on both
raw outcomes; enclosing output is inherited or produced by a charged read. -/
theorem Linst.run_memory_accounting_output (sevm : Sevm) (pre : Devm) (l : Linst)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    let initial := pre.gasMeasure + calculateMemoryGasCost pre.memory.size
    let accounted := fun post : Devm =>
      post.gasMeasure + calculateMemoryGasCost post.memory.size ≤ initial ∧
        (post.output = pre.output ∨
          calculateMemoryGasCost post.output.length ≤ initial)
    match Linst.run sevm pre l with
    | .ok post => accounted post
    | .error failure => accounted failure.2 := by
  have hgas := Linst.run_gasLe sevm pre l
  cases l with
  | stop => exact ⟨Nat.le_refl _, Or.inl rfl⟩
  | return_ | revert =>
      simp only [Linst.run, Devm.popToNat_def, Bind.bind, Except.bind,
        Functor.mapRev, Functor.map, Except.map, Prod.mapFst, Prod.map] at hgas ⊢
      rcases hp1 : pre.pop with failure | ⟨index, d1⟩
      · have hf := pop_memory_output pre
        rw [hp1] at hf
        simp only [hp1, Execution.gasMeasure_error] at hgas
        dsimp only [id_eq]
        refine ⟨?_, Or.inl hf.2⟩
        rw [hf.1]
        exact Nat.add_le_add_right hgas _
      · have h1 := pop_memory_output pre
        rw [hp1] at h1
        simp only [hp1, id_eq] at hgas
        dsimp only [id_eq]
        rcases hp2 : d1.pop with failure | ⟨size, d2⟩
        · have hf := pop_memory_output d1
          rw [hp2] at hf
          simp only [hp2, Execution.gasMeasure_error] at hgas
          dsimp only [id_eq]
          refine ⟨?_, Or.inl (hf.2.trans h1.2)⟩
          rw [hf.1, h1.1]
          exact Nat.add_le_add_right hgas _
        · have h2 := pop_memory_output d1
          rw [hp2] at h2
          have hg1 := Devm.pop_gasMeasure hp1
          have hg2 := Devm.pop_gasMeasure hp2
          simp only [hp2] at hgas
          dsimp only [id_eq]
          rcases hc : chargeGas (d2.extCost [(index.toNat, size.toNat)]) d2 with failure | charged
          · have hf := charge_memory_output (d2.extCost [(index.toNat, size.toNat)]) d2
            rw [hc] at hf
            simp only [hc, Execution.gasMeasure_error] at hgas
            dsimp only
            refine ⟨?_, Or.inl (hf.2.trans (h2.2.trans h1.2))⟩
            rw [hf.1, h2.1, h1.1]
            exact Nat.add_le_add_right hgas _
          · have hb := charged_read_accounting index.toNat size.toNat hc
            rw [hg2, hg1, h2.1, h1.1] at hb
            dsimp only
            exact ⟨Nat.le_of_eq hb.1, Or.inr hb.2⟩
  | selfdestruct =>
      have hf : ∀ result : Except (EvmError × Devm) Devm,
          Linst.run sevm pre .selfdestruct = result →
            (match result with
            | .ok post => post.memory = pre.memory ∧ post.output = pre.output
            | .error failure => failure.2.memory = pre.memory ∧ failure.2.output = pre.output) := by
        intro result hrun
        clear hgas
        cases hs : pre.stack
        all_goals
          simp only [Linst.run, hstate, Devm.popToAdr_def, Devm.pop_def, hs,
            Bind.bind, Except.bind, Functor.mapRev, Functor.map, Except.map,
            Prod.mapFst, Prod.map, id_eq] at hrun
        · cases hrun
          exact ⟨rfl, rfl⟩
        · rename_i head tail
          let popped := pre.setMach {pre.mach with stack := tail}
          let read := (popped.balReadAccount sevm.benvStat.rules head.toAdr).balReadAccount
            sevm.benvStat.rules sevm.currentTarget
          let donorBal := (read.getAcct sevm.currentTarget).bal
          let plan : Devm × Nat :=
            if head.toAdr ∉ read.accessedAddresses then
              (addAccessedAddress read head.toAdr,
                gasSelfDestruct + sevm.benvStat.rules.gas.coldAccountAccess)
            else (read, gasSelfDestruct)
          let cost := if (plan.1.getAcct head.toAdr).Empty ∧ donorBal ≠ 0 then
              plan.2 + gasSelfDestructNewAccount else plan.2
          have hw : plan.1.memory = pre.memory ∧ plan.1.output = pre.output := by
            dsimp only [plan]
            split <;> constructor
            all_goals
              dsimp only [read, popped, Devm.balReadAccount]
              repeat' first | rfl | split
          change (do
            let charged ← chargeGas cost plan.1
            assertDynamic sevm charged
            let next ← Option.toExcept
              (.internal (.invariant (.text "InsufficientBalanceError")), charged)
              (charged.subBal sevm.currentTarget donorBal)
            let next := next.addBal head.toAdr donorBal
            if sevm.currentTarget ∈ next.createdAccounts then
              .ok (addAccountToDelete (next.setBal sevm.currentTarget 0) sevm.currentTarget)
            else .ok next) = result at hrun
          rcases hc : chargeGas cost plan.1 with failure | charged
          · have hf := charge_memory_output cost plan.1
            rw [hc] at hf
            simp only [hc, Bind.bind, Except.bind] at hrun
            cases hrun
            exact ⟨hf.1.trans hw.1, hf.2.trans hw.2⟩
          · have hf := charge_memory_output cost plan.1
            rw [hc] at hf
            have hcharged : charged.memory = pre.memory ∧ charged.output = pre.output :=
              ⟨hf.1.trans hw.1, hf.2.trans hw.2⟩
            simp only [hc, Bind.bind, Except.bind] at hrun
            by_cases hd : (!sevm.isStatic) = true
            · simp only [assertDynamic, Except.assert, hd, ite_true, Bind.bind,
                Devm.subBal, Option.bind, Option.toExcept] at hrun
              rcases hb : charged.state.subBal sevm.currentTarget donorBal with _ | state
              · simp only [hb] at hrun
                cases hrun
                exact hcharged
              · simp only [hb] at hrun
                split at hrun <;> cases hrun <;> exact hcharged
            · simp only [assertDynamic, Except.assert, hd] at hrun
              cases hrun
              exact hcharged
      rcases hx : Linst.run sevm pre .selfdestruct with failure | post
      · have hfields := hf _ hx
        rw [hx] at hgas
        dsimp only at hfields hgas ⊢
        refine ⟨?_, Or.inl hfields.2⟩
        rw [hfields.1]
        exact Nat.add_le_add_right hgas _
      ·
        have hfields := hf _ hx
        rw [hx] at hgas
        dsimp only at hfields hgas ⊢
        refine ⟨?_, Or.inl hfields.2⟩
        rw [hfields.1]
        exact Nat.add_le_add_right hgas _

private theorem push_memory_output (pre : Devm) (word : B256) :
    match pre.push word with
    | .error failure => failure.2.memory = pre.memory ∧ failure.2.output = pre.output
    | .ok post => post.memory = pre.memory ∧ post.output = pre.output := by
  rw [Devm.push_def]
  by_cases hs : pre.stack.length < 1024
  · simp only [Except.assert, hs, ite_true, bind, Except.bind]
    exact ⟨rfl, rfl⟩
  · simp only [Except.assert, hs, ite_false, bind, Except.bind]
    exact ⟨True.intro, True.intro⟩

private theorem call_run_memory_output (parent : Devm) (outputIndex outputSize : Nat)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    match (Resume.call parent outputIndex outputSize).run r with
    | .error failure => failure.2.memory = parent.memory ∧ failure.2.output = parent.output
    | .ok post => post.output = parent.output := by
  cases r with
  | error failure =>
      rcases failure with ⟨err, state, created, tra⟩
      exact ⟨rfl, rfl⟩
  | ok child =>
      by_cases he : child.error.isSome = true
      · simp only [Resume.run, liftToExecution, bind, Except.bind, he, ite_true]
        let incorporated := incorporateChildOnError parent child child.output
        rcases hp : incorporated.push 0 with failure | pushed
        · have hf := push_memory_output incorporated 0
          rw [hp] at hf
          dsimp only
          exact ⟨hf.1, hf.2⟩
        · have hf := push_memory_output incorporated 0
          rw [hp] at hf
          dsimp only
          exact hf.2
      · simp only [Resume.run, liftToExecution, bind, Except.bind, he]
        let incorporated := incorporateChildOnSuccess parent child child.output
        rcases hp : incorporated.push 1 with failure | pushed
        · have hf := push_memory_output incorporated 1
          rw [hp] at hf
          dsimp only
          exact ⟨hf.1, hf.2⟩
        · have hf := push_memory_output incorporated 1
          rw [hp] at hf
          dsimp only
          exact hf.2

/-- The same actual zero-value CALL charge/spawn/child derivation accounts for
both raw resume outcomes, with enclosing output inherited from the caller. -/
theorem zero_call_spawn_resume_raw_accounting
    {sevm : Sevm} {before charged : Devm} (gas : B256)
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
    (hexec : Exec childEvm.pc childEvm.sta childEvm.dyna raw) :
    let accounted := fun post : Devm =>
      post.gasMeasure + extraGas + calculateMemoryGasCost post.memory.size ≤
          before.gasMeasure + calculateMemoryGasCost before.memory.size ∧
        post.output = before.output
    match resume.run (frame.settle raw) with
    | .ok post => accounted post
    | .error failure => accounted failure.2 := by
  let pairs := [(inputIndex, inputSize), (outputIndex, outputSize)]
  let costs := calculateMsgCallGas 0 gas.toNat before.gasLeft (before.extCost pairs) extraGas cs
  let parent := (charged.memExtends pairs).withReturnData []
  obtain ⟨hf, hrsm⟩ := genericCall.step_spawn_call hspawn
  change frame.inner.gas = costs.2 at hf
  change resume = .call parent outputIndex outputSize at hrsm
  have hfields := charge_memory_output (costs.1 + before.extCost pairs) before
  rw [hcharge] at hfields
  have hparentOutput : parent.output = before.output := hfields.2
  have ho := call_run_memory_output parent outputIndex outputSize (frame.settle raw)
  rw [← hrsm] at ho
  rcases hresume : resume.run (frame.settle raw) with failure | post
  · rw [hresume] at ho
    dsimp only at ho ⊢
    refine ⟨?_, ho.2.trans hparentOutput⟩
    have hs := hexec.settledGasLe
    rw [Frame.enter_run_gasMeasure henter, hf] at hs
    have hg := Resume.run_gasLe (rsm := resume) (r := frame.settle raw)
      (m := costs.2) (fun d hd => Frame.settle_gasLe hs hd)
    rw [hresume, hrsm] at hg
    change failure.2.gasMeasure ≤ parent.gasMeasure + costs.2 at hg
    have hc : costs.1 = costs.2 + extraGas :=
      calculateMsgCallGas_zero_value_cost _ _ _ _ _
    have hcharge' : chargeGas ((costs.2 + extraGas) + before.extCost pairs) before =
        .ok charged := by
      rw [← hc]
      exact hcharge
    have haccount := charged_memExtends_accounting pairs (costs.2 + extraGas) hcharge'
    change parent.gasMeasure + (costs.2 + extraGas) +
      calculateMemoryGasCost parent.memory.size =
        before.gasMeasure + calculateMemoryGasCost before.memory.size at haccount
    rw [ho.1]
    omega
  · rw [hresume] at ho
    dsimp only at ho ⊢
    obtain ⟨child, hsettle, hchild, hmem, hsize, haccount⟩ :=
      zero_call_spawn_resume_accounting gas extraGas cs inputIndex inputSize outputIndex
        outputSize hcharge hspawn henter hexec hresume
    exact ⟨haccount, ho.trans hparentOutput⟩

private def nonspawnPreserved (pre post : Devm) : Prop :=
  post.gasMeasure + calculateMemoryGasCost post.memory.size ≤
    pre.gasMeasure + calculateMemoryGasCost pre.memory.size ∧
  post.output = pre.output

private def resultMemoryFields {α : Type} (pre : Devm) (project : α → Devm)
    (raw : Except (EvmError × Devm) α) : Prop :=
  match raw with
  | .error failure => failure.2.memory = pre.memory ∧ failure.2.output = pre.output
  | .ok value => (project value).memory = pre.memory ∧ (project value).output = pre.output

private def nonspawnResult {α : Type} (pre : Devm) (project : α → Devm)
    (raw : Except (EvmError × Devm) α) : Prop :=
  match raw with
  | .ok value => nonspawnPreserved pre (project value)
  | .error failure => nonspawnPreserved pre failure.2

private theorem resultMemoryFields_trans {α : Type} {pre middle : Devm}
    {project : α → Devm} {raw : Except (EvmError × Devm) α}
    (hm : middle.memory = pre.memory ∧ middle.output = pre.output)
    (hr : resultMemoryFields middle project raw) : resultMemoryFields pre project raw := by
  cases raw with
  | error failure => exact ⟨hr.1.trans hm.1, hr.2.trans hm.2⟩
  | ok value => exact ⟨hr.1.trans hm.1, hr.2.trans hm.2⟩

private theorem resultMemoryFields_bind {α β : Type} {pre : Devm}
    {first : Except (EvmError × Devm) α} {next : α → Except (EvmError × Devm) β}
    {projectFirst : α → Devm} {projectNext : β → Devm}
    (hf : resultMemoryFields pre projectFirst first)
    (hn : ∀ value, resultMemoryFields (projectFirst value) projectNext (next value)) :
    resultMemoryFields pre projectNext (first >>= next) := by
  cases first with
  | error failure => exact hf
  | ok value => exact resultMemoryFields_trans hf (hn value)

private theorem nonspawnResult_of_fields {α : Type} {pre : Devm}
    {project : α → Devm} {raw : Except (EvmError × Devm) α}
    (hgas : resultGas project raw ≤ pre.gasMeasure)
    (hfields : resultMemoryFields pre project raw) : nonspawnResult pre project raw := by
  cases raw with
  | error failure =>
      change failure.2.gasMeasure ≤ pre.gasMeasure at hgas
      change failure.2.memory = pre.memory ∧ failure.2.output = pre.output at hfields
      change nonspawnPreserved pre failure.2
      refine ⟨?_, hfields.2⟩
      rw [hfields.1]
      exact Nat.add_le_add_right hgas _
  | ok value =>
      change (project value).gasMeasure ≤ pre.gasMeasure at hgas
      change (project value).memory = pre.memory ∧ (project value).output = pre.output at hfields
      change nonspawnPreserved pre (project value)
      refine ⟨?_, hfields.2⟩
      rw [hfields.1]
      exact Nat.add_le_add_right hgas _

private theorem resultMemoryFields_charge (cost : Nat) (pre : Devm) :
    resultMemoryFields pre id (chargeGas cost pre) := by
  have h := charge_memory_output cost pre
  cases hc : chargeGas cost pre <;> rw [hc] at h <;> exact h

private theorem resultMemoryFields_pop (pre : Devm) :
    resultMemoryFields pre Prod.snd pre.pop := by
  have h := pop_memory_output pre
  cases hp : pre.pop <;> rw [hp] at h <;> exact h

private theorem jump_memory_accounting (pc : Nat) (pre : Devm) (sevm : Sevm) (j : Jinst) :
    nonspawnResult pre Prod.snd (Jinst.runCore pc pre sevm j) := by
  refine nonspawnResult_of_fields (Jinst.runCore_gasLe pc pre sevm j) ?_
  cases j with
  | jumpdest =>
      simp only [Jinst.runCore]
      refine resultMemoryFields_bind (resultMemoryFields_charge gJumpdest pre) ?_
      intro charged
      exact ⟨rfl, rfl⟩
  | jump =>
      simp only [Jinst.runCore]
      refine resultMemoryFields_bind (resultMemoryFields_pop pre) ?_
      intro popped
      refine resultMemoryFields_bind (resultMemoryFields_charge gMid popped.2) ?_
      intro charged
      simp only [Except.assert, bind, Except.bind]
      by_cases hj : jumpable sevm.code popped.1.toNat = true
      · simp only [ite_eq_left hj]
        exact ⟨rfl, rfl⟩
      · simp only [ite_eq_right hj]
        exact ⟨rfl, rfl⟩
  | jumpi =>
      simp only [Jinst.runCore]
      refine resultMemoryFields_bind (resultMemoryFields_pop pre) ?_
      intro popped
      refine resultMemoryFields_bind (resultMemoryFields_pop popped.2) ?_
      intro poppedAgain
      refine resultMemoryFields_bind (resultMemoryFields_charge gHigh poppedAgain.2) ?_
      intro charged
      split
      · exact ⟨rfl, rfl⟩
      · simp only [Except.assert, bind, Except.bind]
        by_cases hj : jumpable sevm.code popped.1.toNat = true
        · simp only [ite_eq_left hj]
          exact ⟨rfl, rfl⟩
        · simp only [ite_eq_right hj]
          exact ⟨rfl, rfl⟩

private theorem resultMemoryFields_push (pre : Devm) (word : B256) :
    resultMemoryFields pre id (pre.push word) := by
  have h := push_memory_output pre word
  cases hp : pre.push word <;> rw [hp] at h <;> exact h

private theorem resultMemoryFields_pushItem (word : B256) (cost : Nat) (pre : Devm) :
    resultMemoryFields pre id (pushItem word cost pre) := by
  rw [pushItem_def]
  refine resultMemoryFields_bind (resultMemoryFields_charge cost pre) ?_
  intro charged
  exact resultMemoryFields_push charged word

private theorem resultMemoryFields_unary (f : B256 → B256) (cost : Nat) (pre : Devm) :
    resultMemoryFields pre id (applyUnary f cost pre) := by
  rw [applyUnary_def]
  refine resultMemoryFields_bind (resultMemoryFields_pop pre) ?_
  intro popped
  exact resultMemoryFields_pushItem (f popped.1) cost popped.2

private theorem resultMemoryFields_binary (f : B256 → B256 → B256)
    (cost : Nat) (pre : Devm) : resultMemoryFields pre id (applyBinary f cost pre) := by
  rw [applyBinary_def]
  refine resultMemoryFields_bind (resultMemoryFields_pop pre) ?_
  intro popped
  refine resultMemoryFields_bind (resultMemoryFields_pop popped.2) ?_
  intro poppedAgain
  exact resultMemoryFields_pushItem (f popped.1 poppedAgain.1) cost poppedAgain.2

private theorem nonspawn_pushItem (word : B256) (cost : Nat) (pre : Devm) :
    nonspawnResult pre id (pushItem word cost pre) := by
  refine nonspawnResult_of_fields ?_ (resultMemoryFields_pushItem word cost pre)
  simpa only [resultGas_id] using pushItem_gasLe word cost pre

private theorem nonspawn_unary (f : B256 → B256) (cost : Nat) (pre : Devm) :
    nonspawnResult pre id (applyUnary f cost pre) := by
  refine nonspawnResult_of_fields ?_ (resultMemoryFields_unary f cost pre)
  simpa only [resultGas_id] using applyUnary_gasLe f cost pre

private theorem nonspawn_binary (f : B256 → B256 → B256) (cost : Nat) (pre : Devm) :
    nonspawnResult pre id (applyBinary f cost pre) := by
  refine nonspawnResult_of_fields ?_ (resultMemoryFields_binary f cost pre)
  simpa only [resultGas_id] using applyBinary_gasLe f cost pre

private theorem nonspawnPreserved_trans {pre middle post : Devm}
    (hm : nonspawnPreserved pre middle) (hp : nonspawnPreserved middle post) :
    nonspawnPreserved pre post :=
  ⟨hp.1.trans hm.1, hp.2.trans hm.2⟩

private theorem nonspawnResult_trans {α : Type} {pre middle : Devm}
    {project : α → Devm} {raw : Except (EvmError × Devm) α}
    (hm : nonspawnPreserved pre middle) (hr : nonspawnResult middle project raw) :
    nonspawnResult pre project raw := by
  cases raw with
  | error failure => exact nonspawnPreserved_trans hm hr
  | ok value => exact nonspawnPreserved_trans hm hr

private theorem nonspawnResult_bind {α β : Type} {pre : Devm}
    {first : Except (EvmError × Devm) α} {next : α → Except (EvmError × Devm) β}
    {projectFirst : α → Devm} {projectNext : β → Devm}
    (hf : nonspawnResult pre projectFirst first)
    (hn : ∀ value, nonspawnResult (projectFirst value) projectNext (next value)) :
    nonspawnResult pre projectNext (first >>= next) := by
  cases first with
  | error failure => exact hf
  | ok value => exact nonspawnResult_trans hf (hn value)

private theorem nonspawn_pop (pre : Devm) : nonspawnResult pre Prod.snd pre.pop := by
  exact nonspawnResult_of_fields (Nat.le_of_eq (Devm.pop_resultGas pre))
    (resultMemoryFields_pop pre)

private theorem nonspawn_charge (cost : Nat) (pre : Devm) :
    nonspawnResult pre id (chargeGas cost pre) := by
  refine nonspawnResult_of_fields ?_ (resultMemoryFields_charge cost pre)
  simpa only [resultGas_id] using chargeGas_result_gasLe cost pre

private theorem nonspawn_push (word : B256) (pre : Devm) :
    nonspawnResult pre id (pre.push word) := by
  refine nonspawnResult_of_fields ?_ (resultMemoryFields_push pre word)
  simpa only [resultGas_id] using Nat.le_of_eq (Devm.push_gasLe word pre)

private theorem nonspawn_balReadAccount (rules : ForkRules) (adr : Adr) (pre : Devm) :
    nonspawnPreserved pre (pre.balReadAccount rules adr) := by
  refine ⟨Nat.le_refl _, ?_⟩
  unfold Devm.balReadAccount
  split <;> rfl

private theorem nonspawn_popToNat (pre : Devm) :
    nonspawnResult pre Prod.snd pre.popToNat := by
  have h := nonspawn_pop pre
  cases hp : pre.pop <;> rw [hp] at h
  all_goals simpa only [Devm.popToNat_def, Functor.mapRev, Functor.map, Except.map,
    Prod.mapFst, Prod.map, nonspawnResult, id_eq, hp] using h

private theorem nonspawn_popToAdr (pre : Devm) :
    nonspawnResult pre Prod.snd pre.popToAdr := by
  have h := nonspawn_pop pre
  cases hp : pre.pop <;> rw [hp] at h
  all_goals simpa only [Devm.popToAdr_def, Functor.mapRev, Functor.map, Except.map,
    Prod.mapFst, Prod.map, nonspawnResult, id_eq, hp] using h

private theorem nonspawn_balReadStorage (rules : ForkRules) (adr : Adr) (key : B256)
    (pre : Devm) : nonspawnPreserved pre (pre.balReadStorage rules adr key) := by
  refine ⟨Nat.le_refl _, ?_⟩
  unfold Devm.balReadStorage
  split <;> rfl

private theorem nonspawn_addAccessedAddress (pre : Devm) (adr : Adr) :
    nonspawnPreserved pre (addAccessedAddress pre adr) :=
  ⟨Nat.le_refl _, rfl⟩

private theorem nonspawn_addAccessedStorageKey (pre : Devm) (adr : Adr) (key : B256) :
    nonspawnPreserved pre (addAccessedStorageKey pre adr key) :=
  ⟨Nat.le_refl _, rfl⟩

private theorem nonspawn_assertDynamic (sevm : Sevm) (pre : Devm) :
    nonspawnResult pre (fun _ : Unit => pre) (assertDynamic sevm pre) := by
  unfold assertDynamic
  by_cases hs : (!sevm.isStatic) = true
  · simp only [Except.assert, ite_eq_left hs]
    exact ⟨Nat.le_refl _, rfl⟩
  · simp only [Except.assert, ite_eq_right hs]
    exact ⟨Nat.le_refl _, rfl⟩

private theorem nonspawn_charged_memory (pairs : List (Nat × Nat)) (baseCost : Nat)
    (pre : Devm) (action : Devm → Execution)
    (hbody : ∀ charged, nonspawnResult (charged.memExtends pairs) id (action charged)) :
    nonspawnResult pre id (chargeGas (baseCost + pre.extCost pairs) pre >>= action) := by
  rcases hc : chargeGas (baseCost + pre.extCost pairs) pre with failure | charged
  · have h := nonspawn_charge (baseCost + pre.extCost pairs) pre
    rw [hc] at h
    exact h
  · have hf := charge_memory_output (baseCost + pre.extCost pairs) pre
    rw [hc] at hf
    have hp : nonspawnPreserved pre (charged.memExtends pairs) := by
      refine ⟨?_, hf.2⟩
      have ha := charged_memExtends_accounting pairs baseCost hc
      omega
    exact nonspawnResult_trans hp (hbody charged)

private theorem ceil32_eq_ceilDiv32 (n : Nat) : ceil32 n = 32 * ceilDiv n 32 := by
  by_cases hz : n % 32 = 0
  · simp only [ceil32, ceilDiv, hz, ite_true, Nat.add_zero]
    omega
  · simp only [ceilDiv, ite_eq_right hz]
    unfold ceil32
    split
    · contradiction
    · omega

private theorem memory_write_size_le_ext (memory : Mem) (index : Nat) (bytes : Bytes) :
    (memory.write index bytes).size ≤ memExtSize memory.size index bytes.length := by
  cases bytes with
  | nil => exact Nat.le_refl _
  | cons byte bytes =>
      simp only [Mem.write]
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

private theorem nonspawn_write (pre : Devm) (index : Nat) (bytes : Bytes) :
    nonspawnPreserved (pre.memExtends [(index, bytes.length)]) (pre.memWrite index bytes) := by
  refine ⟨?_, rfl⟩
  have hw := memory_write_size_le_ext pre.memory index bytes
  have hc := calculateMemoryGasCost_mono hw
  change pre.gasMeasure + calculateMemoryGasCost (pre.memory.write index bytes).size ≤
    pre.gasMeasure + calculateMemoryGasCost (memExtSize pre.memory.size index bytes.length)
  exact Nat.add_le_add_left hc _

private theorem nonspawn_read (pre : Devm) (index size : Nat) :
    nonspawnPreserved (pre.memExtends [(index, size)]) (pre.memRead index size).2 :=
  ⟨Nat.le_refl _, rfl⟩

private theorem nonspawn_before_paid (pairs : List (Nat × Nat)) (pre : Devm) :
    nonspawnPreserved (pre.memExtends pairs) pre := by
  refine ⟨?_, rfl⟩
  exact Nat.add_le_add_left
    (calculateMemoryGasCost_mono (memExtsSize_ge pre.memory.size pairs)) _

private theorem nonspawn_popN (pre : Devm) (n : Nat) :
    nonspawnResult pre Prod.snd (pre.popN n) := by
  induction n generalizing pre with
  | zero => rw [Devm.popN_def]; exact ⟨Nat.le_refl _, rfl⟩
  | succ n ih =>
      rw [Devm.popN_def]
      refine nonspawnResult_bind (nonspawn_pop pre) ?_
      intro popped
      refine nonspawnResult_bind (ih popped.2) ?_
      intro remaining
      exact ⟨Nat.le_refl _, rfl⟩

private theorem list_slice_length (bytes : List UInt8) (index size : Nat)
    (defaultByte : UInt8) : (List.sliceD bytes index size defaultByte).length = size := by
  induction size generalizing index with
  | zero => rfl
  | succ size ih => rw [List.sliceD_succ, List.length_cons, ih]

private theorem ternary_execution_eq (f : B256 → B256 → B256 → B256)
    (cost : Nat) (pre : Devm) : applyTernary f cost pre = (do
      let ⟨x, first⟩ ← pre.pop
      let ⟨y, second⟩ ← first.pop
      let ⟨z, third⟩ ← second.pop
      pushItem (f x y z) cost third) := by
  rcases pre with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  cases stack with
  | nil => rfl
  | cons x xs =>
      cases xs with
      | nil => rfl
      | cons y ys =>
          cases ys with
          | nil => rfl
          | cons z zs =>
              cases h : Mach.pushItem (f x y z) cost
                  { stack := zs, memory := memory, gasLeft := gasLeft,
                    stateGas := stateGas } with
              | error failure =>
                  rcases failure with ⟨err, mach'⟩
                  cases mach'
                  simp only [applyTernary, Mach.applyTernary, Mach.pop, pushItem,
                    liftMachExecution, liftMach, Footprint.toExecution,
                    Footprint.liftOutcome, Devm.pop_def, Devm.stack, Devm.setMach,
                    bind, Except.bind, h]
              | ok result =>
                  rcases result with ⟨_, mach'⟩
                  cases mach'
                  simp only [applyTernary, Mach.applyTernary, Mach.pop, pushItem,
                    liftMachExecution, liftMach, Footprint.toExecution,
                    Footprint.liftOutcome, Devm.pop_def, Devm.stack, Devm.setMach,
                    bind, Except.bind, h]

private theorem nonspawn_ternary (f : B256 → B256 → B256 → B256)
    (cost : Nat) (pre : Devm) : nonspawnResult pre id (applyTernary f cost pre) := by
  rw [ternary_execution_eq]
  refine nonspawnResult_bind (nonspawn_pop pre) ?_
  intro first
  refine nonspawnResult_bind (nonspawn_pop first.2) ?_
  intro second
  refine nonspawnResult_bind (nonspawn_pop second.2) ?_
  intro third
  exact nonspawn_pushItem (f first.1 second.1 third.1) cost third.2

private theorem nonspawn_external_copy (rules : ForkRules) (adr : Adr)
    (index codeIndex size : Nat) (pre : Devm) :
    nonspawnPreserved (pre.memExtends [(index, size)])
      ((pre.balReadAccount rules adr).memWrite index
        (ByteArray.sliceD ((pre.balReadAccount rules adr).getCode adr)
          codeIndex size (Linst.toUInt8 .stop))) := by
  have hb := nonspawn_balReadAccount rules adr (pre.memExtends [(index, size)])
  have hw := nonspawn_write (pre.balReadAccount rules adr) index
    (ByteArray.sliceD ((pre.balReadAccount rules adr).getCode adr)
      codeIndex size (Linst.toUInt8 .stop))
  rw [ByteArray.length_sliceD] at hw
  exact nonspawnPreserved_trans hb hw

private theorem nonspawn_assert (condition : Prop) [Decidable condition]
    (err : EvmError) (pre : Devm) :
    nonspawnResult pre (fun _ : Unit => pre) (Except.assert condition (err, pre)) := by
  by_cases hc : condition
  · simp only [Except.assert, ite_eq_left hc]
    exact ⟨Nat.le_refl _, rfl⟩
  · simp only [Except.assert, ite_eq_right hc]
    exact ⟨Nat.le_refl _, rfl⟩

private theorem resultMemoryFields_balance (rules : ForkRules) (pre : Devm) :
    resultMemoryFields pre id
      (liftMachMetaWorldExecution (Rinst.balanceCore rules) pre) := by
  rcases pre with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  cases stack with
  | nil => exact ⟨rfl, rfl⟩
  | cons word rest =>
      by_cases hw : word.toAdr ∈ view.accessedAddresses
      all_goals by_cases hb : rules.bal.isSome = true
      all_goals
        simp only [liftMachMetaWorldExecution, liftMachMetaExecution, liftMachMeta,
          Footprint.toExecution, Footprint.liftOutcome, Rinst.balanceCore, Mach.pop,
          hw, hb, ite_true, ite_false]
        cases hc : safeSub gasLeft
            (if word.toAdr ∈ view.accessedAddresses then gasWarmAccess
              else rules.gas.coldAccountAccess) with
        | none =>
            simp only [hw, ite_true, ite_false] at hc
            simp only [Mach.chargeGas, hc]
            exact ⟨rfl, rfl⟩
        | some gas =>
            simp only [hw, ite_true, ite_false] at hc
            simp only [Mach.chargeGas, hc, Mach.push]
            by_cases hp : rest.length < 1024
            · simp only [ite_eq_left hp]
              exact ⟨rfl, rfl⟩
            · simp only [ite_eq_right hp]
              exact ⟨rfl, rfl⟩

private theorem regular_memory_accounting (pc : Nat) (pre : Devm) (sevm : Sevm) (r : Rinst)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    nonspawnResult pre id (Rinst.runCore pc pre sevm r) := by
  cases r <;> simp only [Rinst.runCore]
  all_goals first
    | exact nonspawn_pushItem _ _ _
    | exact nonspawn_unary _ _ _
    | exact nonspawn_binary _ _ _
    | skip
  case exp =>
    refine nonspawnResult_bind (nonspawn_pop pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_pop popped.2) ?_
    intro poppedAgain
    rw [← pushItem_def]
    exact nonspawn_pushItem _ _ _
  case calldataload =>
    refine nonspawnResult_bind (nonspawn_pop pre) ?_
    intro popped
    rw [← pushItem_def]
    exact nonspawn_pushItem _ _ _
  case blobhash =>
    refine nonspawnResult_bind (nonspawn_pop pre) ?_
    intro popped
    rw [← pushItem_def]
    exact nonspawn_pushItem _ _ _
  case blockhash =>
    refine nonspawnResult_bind (nonspawn_pop pre) ?_
    intro popped
    rw [← pushItem_def]
    exact nonspawn_pushItem _ _ _
  case tload =>
    refine nonspawnResult_bind (nonspawn_pop pre) ?_
    intro popped
    exact nonspawn_pushItem _ _ _
  case gas =>
    refine nonspawnResult_bind (nonspawn_charge gBase pre) ?_
    intro charged
    exact nonspawn_push _ _
  case clz =>
    split
    · exact nonspawn_unary _ _ _
    · exact ⟨Nat.le_refl _, rfl⟩
  case slotnum =>
    split
    · exact nonspawn_pushItem _ _ _
    · exact ⟨Nat.le_refl _, rfl⟩
  case selfbalance =>
    refine nonspawnResult_bind (nonspawn_charge gLow pre) ?_
    intro charged
    exact nonspawnResult_trans (nonspawn_balReadAccount sevm.benvStat.rules
      sevm.currentTarget charged) (nonspawn_push _ _)
  case dup n =>
    refine nonspawnResult_bind (nonspawn_charge gVerylow pre) ?_
    intro charged
    rcases hword : charged.stack[n]? with _ | word
    · exact ⟨Nat.le_refl _, rfl⟩
    · exact nonspawn_push word charged
  case swap n =>
    refine nonspawnResult_bind (nonspawn_charge gVerylow pre) ?_
    intro charged
    rcases hstack : List.swap charged.stack n with _ | stack
    · exact ⟨Nat.le_refl _, rfl⟩
    · exact ⟨Nat.le_refl _, rfl⟩
  case pop =>
    have hf : nonspawnResult pre id (pre.pop <&> Prod.snd) := by
      have h := nonspawn_pop pre
      cases hp : pre.pop <;> rw [hp] at h
      all_goals simpa only [Functor.mapRev, Functor.map, Except.map,
        nonspawnResult, id_eq] using h
    refine nonspawnResult_bind hf ?_
    intro popped
    exact nonspawn_charge gBase popped
  case extcodesize =>
    refine nonspawnResult_bind (nonspawn_popToAdr pre) ?_
    intro popped
    split
    · refine nonspawnResult_bind (nonspawn_charge _ popped.2) ?_
      intro charged
      exact nonspawnResult_trans (nonspawn_balReadAccount sevm.benvStat.rules
        popped.1 charged) (nonspawn_push _ _)
    · refine nonspawnResult_trans (nonspawn_addAccessedAddress popped.2 popped.1) ?_
      refine nonspawnResult_bind (nonspawn_charge _ _) ?_
      intro charged
      exact nonspawnResult_trans (nonspawn_balReadAccount sevm.benvStat.rules
        popped.1 charged) (nonspawn_push _ _)
  case extcodehash =>
    refine nonspawnResult_bind (nonspawn_popToAdr pre) ?_
    intro popped
    split
    · refine nonspawnResult_bind (nonspawn_charge _ popped.2) ?_
      intro charged
      exact nonspawnResult_trans (nonspawn_balReadAccount sevm.benvStat.rules
        popped.1 charged) (nonspawn_push _ _)
    · refine nonspawnResult_trans (nonspawn_addAccessedAddress popped.2 popped.1) ?_
      refine nonspawnResult_bind (nonspawn_charge _ _) ?_
      intro charged
      exact nonspawnResult_trans (nonspawn_balReadAccount sevm.benvStat.rules
        popped.1 charged) (nonspawn_push _ _)
  case sload =>
    refine nonspawnResult_bind (nonspawn_pop pre) ?_
    intro popped
    split
    · refine nonspawnResult_bind (nonspawn_charge gasWarmAccess popped.2) ?_
      intro charged
      exact nonspawnResult_trans (nonspawn_balReadStorage sevm.benvStat.rules
        sevm.currentTarget popped.1 charged) (nonspawn_push _ _)
    · refine nonspawnResult_trans (nonspawn_addAccessedStorageKey popped.2
        sevm.currentTarget popped.1) ?_
      refine nonspawnResult_bind (nonspawn_charge gasColdSload _) ?_
      intro charged
      exact nonspawnResult_trans (nonspawn_balReadStorage sevm.benvStat.rules
        sevm.currentTarget popped.1 charged) (nonspawn_push _ _)
  case tstore =>
    simp only [hstate]
    refine nonspawnResult_bind (nonspawn_pop pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_pop popped.2) ?_
    intro poppedAgain
    refine nonspawnResult_bind (nonspawn_charge gasWarmAccess poppedAgain.2) ?_
    intro charged
    refine nonspawnResult_bind (nonspawn_assertDynamic sevm charged) ?_
    intro _
    exact ⟨Nat.le_refl _, rfl⟩
  case mload =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawn_charged_memory [(popped.1, 32)] gVerylow popped.2 _ ?_
    intro charged
    exact nonspawnResult_trans (nonspawn_read charged popped.1 32) (nonspawn_push _ _)
  case keccak256 =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_popToNat popped.2) ?_
    intro poppedAgain
    refine nonspawn_charged_memory [(popped.1, poppedAgain.1)]
      (gKeccak256 + gasKeccak256Word * ceilDiv poppedAgain.1 32) poppedAgain.2 _ ?_
    intro charged
    exact nonspawnResult_trans (nonspawn_read charged popped.1 poppedAgain.1)
      (nonspawn_push _ _)
  case mstore =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_pop popped.2) ?_
    intro poppedAgain
    refine nonspawn_charged_memory [(popped.1, 32)] gVerylow poppedAgain.2 _ ?_
    intro charged
    change nonspawnPreserved (charged.memExtends [(popped.1, 32)])
      (charged.memWrite popped.1 poppedAgain.1.toBytes)
    simpa only [B256.length_toBytes] using nonspawn_write charged popped.1 poppedAgain.1.toBytes
  case mstore8 =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_pop popped.2) ?_
    intro poppedAgain
    refine nonspawn_charged_memory [(popped.1, 1)] gVerylow poppedAgain.2 _ ?_
    intro charged
    change nonspawnPreserved (charged.memExtends [(popped.1, 1)])
      (charged.memWrite popped.1 [poppedAgain.1.2.2.toUInt8])
    simpa only [List.length_cons, List.length_nil] using
      nonspawn_write charged popped.1 [poppedAgain.1.2.2.toUInt8]
  case calldatacopy =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_popToNat popped.2) ?_
    intro dataIndex
    refine nonspawnResult_bind (nonspawn_popToNat dataIndex.2) ?_
    intro size
    refine nonspawn_charged_memory [(popped.1, size.1)]
      (gVerylow + gasCopy * ceilDiv size.1 32) size.2 _ ?_
    intro charged
    change nonspawnPreserved (charged.memExtends [(popped.1, size.1)])
      (charged.memWrite popped.1 (List.sliceD sevm.data dataIndex.1 size.1 0))
    simpa only [list_slice_length] using
      nonspawn_write charged popped.1 (List.sliceD sevm.data dataIndex.1 size.1 0)
  case codecopy =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_popToNat popped.2) ?_
    intro codeIndex
    refine nonspawnResult_bind (nonspawn_popToNat codeIndex.2) ?_
    intro size
    refine nonspawn_charged_memory [(popped.1, size.1)]
      (gVerylow + gasCopy * ceilDiv size.1 32) size.2 _ ?_
    intro charged
    change nonspawnPreserved (charged.memExtends [(popped.1, size.1)])
      (charged.memWrite popped.1 (ByteArray.sliceD sevm.code codeIndex.1 size.1 (Linst.toUInt8 .stop)))
    simpa only [ByteArray.length_sliceD] using nonspawn_write charged popped.1
      (ByteArray.sliceD sevm.code codeIndex.1 size.1 (Linst.toUInt8 .stop))
  case returndatacopy =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_popToNat popped.2) ?_
    intro dataIndex
    refine nonspawnResult_bind (nonspawn_popToNat dataIndex.2) ?_
    intro size
    refine nonspawn_charged_memory [(popped.1, size.1)]
      (gVerylow + gReturnDataCopy * ceilDiv size.1 32) size.2 _ ?_
    intro charged
    split
    · simp only [bind, Except.bind]
      exact nonspawn_before_paid [(popped.1, size.1)] charged
    · change nonspawnPreserved (charged.memExtends [(popped.1, size.1)])
        (charged.memWrite popped.1 (List.sliceD charged.returnData dataIndex.1 size.1 0))
      simpa only [list_slice_length] using
        nonspawn_write charged popped.1 (List.sliceD charged.returnData dataIndex.1 size.1 0)
  case mcopy =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro destination
    refine nonspawnResult_bind (nonspawn_popToNat destination.2) ?_
    intro source
    refine nonspawnResult_bind (nonspawn_popToNat source.2) ?_
    intro size
    refine nonspawn_charged_memory [(source.1, size.1), (destination.1, size.1)]
      (gVerylow + gasCopy * ceilDiv size.1 32) size.2 _ ?_
    intro charged
    have hw := nonspawn_write (charged.memRead source.1 size.1).2 destination.1
      (charged.memRead source.1 size.1).1
    have hl : (charged.memRead source.1 size.1).1.length = size.1 :=
      memory_slice_length charged.memory.data source.1 size.1 0
    rw [hl] at hw
    exact hw
  case log n =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_popToNat popped.2) ?_
    intro size
    refine nonspawnResult_bind (nonspawn_popN size.2 n) ?_
    intro topics
    refine nonspawn_charged_memory [(popped.1, size.1)]
      (gLog + gLogdata * size.1 + gLogtopic * n) topics.2 _ ?_
    intro charged
    unfold assertDynamic
    by_cases hs : (!sevm.isStatic) = true
    · simp only [Except.assert, ite_eq_left hs, bind, Except.bind]
      exact ⟨Nat.le_refl _, rfl⟩
    · simp only [Except.assert, ite_eq_right hs, bind, Except.bind]
      exact nonspawn_before_paid [(popped.1, size.1)] charged
  case addmod => exact nonspawn_ternary _ _ _
  case mulmod => exact nonspawn_ternary _ _ _
  case extcodecopy =>
    refine nonspawnResult_bind (nonspawn_popToAdr pre) ?_
    intro address
    refine nonspawnResult_bind (nonspawn_popToNat address.2) ?_
    intro memoryIndex
    refine nonspawnResult_bind (nonspawn_popToNat memoryIndex.2) ?_
    intro codeIndex
    refine nonspawnResult_bind (nonspawn_popToNat codeIndex.2) ?_
    intro size
    split
    · refine nonspawn_charged_memory [(memoryIndex.1, size.1)]
        (gasWarmAccess + sevm.benvStat.rules.gas.codeReadSurcharge +
          gasCopy * ceilDiv size.1 32) size.2 _ ?_
      intro charged
      exact nonspawn_external_copy sevm.benvStat.rules address.1
        memoryIndex.1 codeIndex.1 size.1 charged
    · refine nonspawnResult_trans (nonspawn_addAccessedAddress size.2 address.1) ?_
      refine nonspawn_charged_memory [(memoryIndex.1, size.1)]
        (sevm.benvStat.rules.gas.coldAccountAccess +
          sevm.benvStat.rules.gas.codeReadSurcharge + gasCopy * ceilDiv size.1 32)
        (addAccessedAddress size.2 address.1) _ ?_
      intro charged
      exact nonspawn_external_copy sevm.benvStat.rules address.1
        memoryIndex.1 codeIndex.1 size.1 charged
  case balance =>
    refine nonspawnResult_of_fields ?_ (resultMemoryFields_balance _ pre)
    simpa only [Rinst.runCore, resultGas_id] using
      Rinst.runCore_gasLe pc pre sevm .balance
  case sstore =>
    rw [hstate]
    refine nonspawnResult_bind (nonspawn_pop pre) ?_
    intro key
    refine nonspawnResult_bind (nonspawn_pop key.2) ?_
    intro value
    refine nonspawnResult_bind
      (nonspawn_assert (gCallStipend < value.2.gasLeft) (.halt (.outOfGas .none)) value.2) ?_
    intro _
    refine nonspawnResult_bind (projectFirst := Prod.fst) ?_ ?_
    · split
      · exact nonspawnPreserved_trans
          (nonspawn_balReadStorage sevm.benvStat.rules sevm.currentTarget key.1 value.2)
          (nonspawn_addAccessedStorageKey _ sevm.currentTarget key.1)
      · exact nonspawn_balReadStorage sevm.benvStat.rules sevm.currentTarget key.1 value.2
    · intro accessed
      refine nonspawnResult_bind (projectFirst := fun _ : Nat => accessed.1) ?_ ?_
      · exact ⟨Nat.le_refl _, rfl⟩
      · intro cost
        refine nonspawnResult_bind (projectFirst := id) ?_ ?_
        · exact ⟨Nat.le_refl _, rfl⟩
        · intro refunded
          refine nonspawnResult_bind (nonspawn_charge cost refunded) ?_
          intro charged
          refine nonspawnResult_bind (nonspawn_assertDynamic sevm charged) ?_
          intro _
          exact nonspawnPreserved_trans
            (nonspawn_balReadAccount sevm.benvStat.rules sevm.currentTarget charged)
            ⟨Nat.le_refl _, rfl⟩

private def accountedTerminal (pre post : Devm) : Prop :=
  post.gasMeasure + calculateMemoryGasCost post.memory.size ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size ∧
    (post.output = pre.output ∨ calculateMemoryGasCost post.output.length ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size)

private def allowancePreserved (pre : Devm) (allowance : Nat) (post : Devm) : Prop :=
  post.gasMeasure + calculateMemoryGasCost post.memory.size ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + allowance ∧
    post.output = pre.output

private def allowanceResult (pre : Devm) (allowance : Nat) (raw : Execution) : Prop :=
  match raw with
  | .ok post => allowancePreserved pre allowance post
  | .error failure => allowancePreserved pre allowance failure.2

private def xAccounting (pre : Devm) (allowance : Nat) : XStep → Prop
  | .done raw => allowanceResult pre allowance raw
  | .spawn _ _ => True

private def xResult (pre : Devm) (allowance : Nat)
    (raw : Except (EvmError × Devm) XStep) : Prop :=
  match raw with
  | .error failure => allowancePreserved pre allowance failure.2
  | .ok step => xAccounting pre allowance step

private theorem allowance_rebase {pre middle post : Devm} {inner outer : Nat}
    (hp : middle.gasMeasure + calculateMemoryGasCost middle.memory.size + inner ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + outer)
    (ho : middle.output = pre.output)
    (h : allowancePreserved middle inner post) : allowancePreserved pre outer post := by
  exact ⟨Nat.le_trans h.1 hp, h.2.trans ho⟩

private theorem xAccounting_rebase {pre middle : Devm} {inner outer : Nat} {step : XStep}
    (hp : middle.gasMeasure + calculateMemoryGasCost middle.memory.size + inner ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + outer)
    (ho : middle.output = pre.output) (h : xAccounting middle inner step) :
    xAccounting pre outer step := by
  cases step with
  | spawn _ _ => trivial
  | done raw =>
      cases raw with
      | error failure => exact allowance_rebase hp ho h
      | ok post => exact allowance_rebase hp ho h

private theorem xResult_rebase {pre middle : Devm} {inner outer : Nat}
    {raw : Except (EvmError × Devm) XStep}
    (hp : middle.gasMeasure + calculateMemoryGasCost middle.memory.size + inner ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + outer)
    (ho : middle.output = pre.output) (h : xResult middle inner raw) :
    xResult pre outer raw := by
  cases raw with
  | error failure => exact allowance_rebase hp ho h
  | ok step => exact xAccounting_rebase hp ho h

private theorem xResult_bind {α : Type} {pre : Devm} {allowance : Nat}
    {first : Except (EvmError × Devm) α} {next : α → Except (EvmError × Devm) XStep}
    {project : α → Devm}
    (hf : nonspawnResult pre project first)
    (hn : ∀ value, xResult (project value) allowance (next value)) :
    xResult pre allowance (first >>= next) := by
  cases first with
  | error failure =>
      refine ⟨?_, hf.2⟩
      have hp := hf.1
      omega
  | ok value =>
      apply xResult_rebase (ho := hf.2) (h := hn value)
      have hp := hf.1
      omega

private theorem xAccounting_ofExcept {pre : Devm} {allowance : Nat}
    {raw : Except (EvmError × Devm) XStep} (h : xResult pre allowance raw) :
    xAccounting pre allowance (XStep.ofExcept raw) := by
  cases raw with
  | error failure => exact h
  | ok step => exact h

private theorem xResult_charged_memory (pairs : List (Nat × Nat)) (baseCost : Nat)
    (pre : Devm) (action : Devm → Except (EvmError × Devm) XStep)
    (hbody : ∀ charged, xResult (charged.memExtends pairs) baseCost (action charged)) :
    xResult pre 0 (chargeGas (baseCost + pre.extCost pairs) pre >>= action) := by
  rcases hc : chargeGas (baseCost + pre.extCost pairs) pre with failure | charged
  · have h := nonspawn_charge (baseCost + pre.extCost pairs) pre
    rw [hc] at h
    exact h
  · have hf := charge_memory_output (baseCost + pre.extCost pairs) pre
    rw [hc] at hf
    refine xResult_rebase (pre := pre) (middle := charged.memExtends pairs)
      (inner := baseCost) (outer := 0) ?_ hf.2 (hbody charged)
    have ha := charged_memExtends_accounting pairs baseCost hc
    omega

private theorem calculateMsgCallGas_refund_le_base
    (value gas gasLeft memoryCost extraGas cs : Nat)
    (hstip : (if value = 0 then 0 else cs) ≤ extraGas) :
    (calculateMsgCallGas value gas gasLeft memoryCost extraGas cs).2 ≤
      (calculateMsgCallGas value gas gasLeft memoryCost extraGas cs).1 := by
  simp only [calculateMsgCallGas]
  split <;> omega

private theorem genericCall_memory_allowance
    (sevm : Sevm) (pre : Devm) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr) (transfer staticCall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disable : Bool) :
    xAccounting pre gas (genericCall.step sevm pre gas value caller target codeAddress
      transfer staticCall inputIndex inputSize outputIndex outputSize code disable) := by
  unfold genericCall.step
  split
  · apply xAccounting_ofExcept
    let refunded := (pre.withReturnData []).withGasLeft ((pre.withReturnData []).gasLeft + gas)
    have hr : xResult refunded 0 (do
        let post ← refunded.push 0
        pure (.done (.ok post))) := by
      refine xResult_bind (nonspawn_push 0 refunded) ?_
      intro post
      exact ⟨Nat.le_refl _, rfl⟩
    apply xResult_rebase (pre := pre) (middle := refunded) (outer := gas)
      (h := hr) (ho := rfl)
    dsimp only [refunded]
    simp only [Devm.withGasLeft_gasMeasure, Devm.withReturnData_gasLeft,
      Devm.withReturnData_spill]
    have hm := Devm.gasMeasure_eq pre
    change ((pre.gasLeft + gas) + pre.spill) +
      calculateMemoryGasCost pre.memory.size + 0 ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + gas
    omega
  · trivial

private theorem nonspawn_assert_at (condition : Prop) [Decidable condition]
    (err : EvmError) (actual reference : Devm)
    (ha : nonspawnPreserved reference actual) :
    nonspawnResult reference (fun _ : Unit => reference)
      (Except.assert condition (err, actual)) := by
  by_cases hc : condition
  · simp only [Except.assert, ite_eq_left hc]
    exact ⟨Nat.le_refl _, rfl⟩
  · simp only [Except.assert, ite_eq_right hc]
    exact ha

private theorem xResult_done_push (word : B256) (pre : Devm) :
    xResult pre 0 (do
      let post ← pre.push word
      pure (.done (.ok post))) := by
  refine xResult_bind (nonspawn_push word pre) ?_
  intro post
  exact ⟨Nat.le_refl _, rfl⟩

private theorem genericCreate_memory_accounting
    (sevm : Sevm) (pre : Devm) (endowment : B256)
    (newAddress : Adr) (memoryIndex memorySize : Nat) :
    xAccounting pre 0
      (genericCreate.step sevm pre endowment newAddress memoryIndex memorySize) := by
  unfold genericCreate.step
  apply xAccounting_ofExcept
  refine xResult_bind
    (nonspawn_assert (memorySize ≤ sevm.benvStat.rules.code.maxInitCodeSize)
      (.halt (.outOfGas .none)) pre) ?_
  intro _
  let grant := except64th pre.gasLeft
  let withheld := pre.withGasLeft (pre.gasLeft - grant)
  have hg : grant ≤ pre.gasLeft := except64th_le pre.gasLeft
  have hhold : nonspawnPreserved pre withheld := by
    refine ⟨?_, rfl⟩
    dsimp only [withheld]
    rw [Devm.withGasLeft_gasMeasure]
    change (pre.gasLeft - grant + pre.spill) +
      calculateMemoryGasCost pre.memory.size ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size
    have hm := Devm.gasMeasure_eq pre
    omega
  refine xResult_bind
    (nonspawn_assert_at ((!sevm.isStatic) = true)
      (.halt (.writeInStaticContext .none)) withheld pre hhold) ?_
  intro _
  let current := withheld.withReturnData []
  by_cases hfail : (current.state.get sevm.currentTarget).bal < endowment ∨
      (current.state.get sevm.currentTarget).nonce = UInt64.max ∨ sevm.depth = 0
  · dsimp only [current, withheld, grant] at hfail
    simp only [ite_eq_left hfail]
    let refunded := current.withGasLeft (current.gasLeft + grant)
    refine xResult_rebase (pre := pre) (middle := refunded)
      (inner := 0) (outer := 0) ?_ rfl (xResult_done_push 0 refunded)
    dsimp only [refunded, current, withheld]
    simp only [Devm.withGasLeft_gasMeasure, Devm.withReturnData_gasLeft,
      Devm.withGasLeft_gasLeft, Devm.withReturnData_spill, Devm.withGasLeft_spill]
    change (pre.gasLeft - grant + grant + pre.spill) +
      calculateMemoryGasCost pre.memory.size + 0 ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + 0
    have hm := Devm.gasMeasure_eq pre
    omega
  · dsimp only [current, withheld, grant] at hfail
    simp only [ite_eq_right hfail]
    let accessed := addAccessedAddress (current.incrNonce sevm.currentTarget) newAddress
    by_cases hcollision : (accessed.state.get newAddress).nonce ≠ (0 : UInt64) ∨
        (accessed.state.get newAddress).code.size ≠ 0 ∨
        (accessed.state.get newAddress).stor.size ≠ 0
    · dsimp only [accessed, current, withheld, grant] at hcollision
      simp only [ite_eq_left hcollision]
      refine xResult_rebase (pre := pre) (middle := accessed)
        (inner := 0) (outer := 0) ?_ rfl (xResult_done_push 0 accessed)
      dsimp only [accessed, current, withheld]
      simp only [addAccessedAddress_gasMeasure, Devm.incrNonce_gasMeasure,
        Devm.withReturnData_gasMeasure, Devm.withGasLeft_gasMeasure]
      change (pre.gasLeft - grant + pre.spill) +
        calculateMemoryGasCost pre.memory.size + 0 ≤
        pre.gasMeasure + calculateMemoryGasCost pre.memory.size + 0
      have hm := Devm.gasMeasure_eq pre
      omega
    · dsimp only [accessed, current, withheld, grant] at hcollision
      simp only [ite_eq_right hcollision]
      trivial

private theorem delegation_memory_output (gasRules : GasSchedule) (pre : Devm) (adr : Adr) :
    (gasRules.accessDelegation pre adr).2.2.2.2.memory = pre.memory ∧
      (gasRules.accessDelegation pre adr).2.2.2.2.output = pre.output := by
  unfold GasSchedule.accessDelegation
  cases hd : getDelegatedCodeAddress (pre.state.getCode adr) with
  | none => simp only [hd]; exact ⟨True.intro, True.intro⟩
  | some delegated => simp only [hd]; exact ⟨rfl, rfl⟩

private theorem nonspawn_delegation (gasRules : GasSchedule) (pre : Devm) (adr : Adr) :
    nonspawnPreserved pre (gasRules.accessDelegation pre adr).2.2.2.2 := by
  have hf := delegation_memory_output gasRules pre adr
  refine ⟨?_, hf.2⟩
  rw [GasSchedule.accessDelegation_gasMeasure, hf.1]

private theorem xResult_charged_call (pairs : List (Nat × Nat)) (cost refund : Nat)
    (pre : Devm) (hrefund : refund ≤ cost)
    (action : Devm → Except (EvmError × Devm) XStep)
    (hbody : ∀ charged, xResult (charged.memExtends pairs) refund (action charged)) :
    xResult pre 0 (chargeGas (cost + pre.extCost pairs) pre >>= action) := by
  refine xResult_charged_memory pairs cost pre action ?_
  intro charged
  exact xResult_rebase (pre := charged.memExtends pairs)
    (middle := charged.memExtends pairs) (inner := refund) (outer := cost)
    (Nat.add_le_add_left hrefund _) rfl (hbody charged)

private theorem value_call_refund_le_base (sevm : Sevm) (value : B256)
    (gas gasLeft memoryCost accessCost createCost : Nat) :
    (calculateMsgCallGas value.toNat gas gasLeft memoryCost
      (accessCost + createCost + if value = 0 then 0 else sevm.benvStat.rules.gas.callValue)).2 ≤
    (calculateMsgCallGas value.toNat gas gasLeft memoryCost
      (accessCost + createCost + if value = 0 then 0 else sevm.benvStat.rules.gas.callValue)).1 := by
  apply calculateMsgCallGas_refund_le_base
  by_cases hv : value = 0
  · have hz : value.toNat = 0 := by rw [hv]; rfl
    rw [ite_eq_left hz, ite_eq_left hv]
    exact Nat.zero_le _
  · rw [ite_eq_right hv]
    by_cases hz : value.toNat = 0
    · rw [ite_eq_left hz]
      exact Nat.zero_le _
    · rw [ite_eq_right hz]
      have hc := GasSchedule.Valid.stipend_le_callValue (Sevm.rules_valid sevm).gas
      omega

private theorem balance_refund_accounting (pre : Devm) (refund : Nat) :
    xResult pre refund (do
      let post ← pre.push 0
      pure (.done (.ok ((post.withReturnData []).withGasLeft (post.gasLeft + refund))))) := by
  refine xResult_bind (nonspawn_push 0 pre) ?_
  intro post
  refine ⟨?_, rfl⟩
  change ((post.withReturnData []).withGasLeft (post.gasLeft + refund)).gasMeasure +
    calculateMemoryGasCost post.memory.size ≤
    post.gasMeasure + calculateMemoryGasCost post.memory.size + refund
  rw [Devm.withGasLeft_gasMeasure, Devm.withReturnData_spill]
  have hm := Devm.gasMeasure_eq post
  omega

private theorem executable_memory_accounting (sevm : Sevm) (pre : Devm) (x : Xinst)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    xAccounting pre 0 (Xinst.step sevm pre x) := by
  cases x <;> simp only [Xinst.step, hstate]
  case create =>
    apply xAccounting_ofExcept
    refine xResult_bind (nonspawn_pop pre) ?_
    intro endowment
    refine xResult_bind (nonspawn_popToNat endowment.2) ?_
    intro memoryIndex
    refine xResult_bind (nonspawn_popToNat memoryIndex.2) ?_
    intro memorySize
    rw [Nat.add_right_comm sevm.benvStat.rules.gas.createAccess
      (memorySize.2.extCost [(memoryIndex.1, memorySize.1)])
      (gasInitCodeWordCost * ceilDiv memorySize.1 32)]
    refine xResult_charged_memory [(memoryIndex.1, memorySize.1)]
      (sevm.benvStat.rules.gas.createAccess + gasInitCodeWordCost * ceilDiv memorySize.1 32)
      memorySize.2 _ ?_
    intro charged
    refine xAccounting_rebase (pre := charged.memExtends [(memoryIndex.1, memorySize.1)])
      (inner := 0) ?_ rfl
      (genericCreate_memory_accounting sevm _ endowment.1 _ memoryIndex.1 memorySize.1)
    omega
  case create2 =>
    apply xAccounting_ofExcept
    refine xResult_bind (nonspawn_pop pre) ?_
    intro endowment
    refine xResult_bind (nonspawn_popToNat endowment.2) ?_
    intro memoryIndex
    refine xResult_bind (nonspawn_popToNat memoryIndex.2) ?_
    intro memorySize
    refine xResult_bind (nonspawn_pop memorySize.2) ?_
    intro salt
    rw [Nat.add_right_comm
      (sevm.benvStat.rules.gas.createAccess + gasKeccak256Word * ceilDiv memorySize.1 32)
      (salt.2.extCost [(memoryIndex.1, memorySize.1)])
      (gasInitCodeWordCost * ceilDiv memorySize.1 32)]
    refine xResult_charged_memory [(memoryIndex.1, memorySize.1)]
      (sevm.benvStat.rules.gas.createAccess + gasKeccak256Word * ceilDiv memorySize.1 32 +
        gasInitCodeWordCost * ceilDiv memorySize.1 32)
      salt.2 _ ?_
    intro charged
    refine xAccounting_rebase (pre := charged.memExtends [(memoryIndex.1, memorySize.1)])
      (inner := 0) ?_ rfl
      (genericCreate_memory_accounting sevm _ endowment.1 _ memoryIndex.1 memorySize.1)
    omega
  case delegatecall =>
    apply xAccounting_ofExcept
    refine xResult_bind (nonspawn_pop pre) ?_
    intro gas
    refine xResult_bind (nonspawn_popToAdr gas.2) ?_
    intro codeAddress
    refine xResult_bind (nonspawn_popToNat codeAddress.2) ?_
    intro inputIndex
    refine xResult_bind (nonspawn_popToNat inputIndex.2) ?_
    intro inputSize
    refine xResult_bind (nonspawn_popToNat inputSize.2) ?_
    intro outputIndex
    refine xResult_bind (nonspawn_popToNat outputIndex.2) ?_
    intro outputSize
    let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
    let lookup := sevm.benvStat.rules.gas.accessDelegation
      (addAccessedAddress outputSize.2 codeAddress.1) codeAddress.1
    let parent := lookup.2.2.2.2
    have hp : nonspawnPreserved outputSize.2 parent :=
      nonspawnPreserved_trans (nonspawn_addAccessedAddress outputSize.2 codeAddress.1)
        (nonspawn_delegation sevm.benvStat.rules.gas _ codeAddress.1)
    refine xResult_rebase (pre := outputSize.2) (middle := parent)
      (inner := 0) (outer := 0) hp.1 hp.2 ?_
    have hm : parent.memory = outputSize.2.memory :=
      (delegation_memory_output sevm.benvStat.rules.gas
        (addAccessedAddress outputSize.2 codeAddress.1) codeAddress.1).1
    have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
      simp only [Devm.extCost, hm]
    change xResult parent 0 (chargeGas
      ((calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (outputSize.2.extCost pairs)
        (sevm.benvStat.rules.gas.accessCost codeAddress.1 outputSize.2.accessedAddresses +
          lookup.2.2.2.1)).1 + outputSize.2.extCost pairs) parent >>= _)
    rw [hext]
    let costs := calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (parent.extCost pairs)
      (sevm.benvStat.rules.gas.accessCost codeAddress.1 outputSize.2.accessedAddresses +
        lookup.2.2.2.1)
    refine xResult_charged_call pairs costs.1 costs.2 parent ?_ _ ?_
    · exact calculateMsgCallGas_refund_le_base 0 gas.1.toNat parent.gasLeft
        (parent.extCost pairs)
        (sevm.benvStat.rules.gas.accessCost codeAddress.1 outputSize.2.accessedAddresses +
          lookup.2.2.2.1) gCallStipend (Nat.zero_le _)
    · intro charged
      exact genericCall_memory_allowance sevm (charged.memExtends pairs) costs.2
        sevm.value sevm.caller sevm.currentTarget lookup.2.1
        false false inputIndex.1 inputSize.1 outputIndex.1 outputSize.1
        lookup.2.2.1 lookup.1

  case staticcall =>
    apply xAccounting_ofExcept
    refine xResult_bind (nonspawn_pop pre) ?_
    intro gas
    refine xResult_bind (nonspawn_popToAdr gas.2) ?_
    intro target
    refine xResult_bind (nonspawn_popToNat target.2) ?_
    intro inputIndex
    refine xResult_bind (nonspawn_popToNat inputIndex.2) ?_
    intro inputSize
    refine xResult_bind (nonspawn_popToNat inputSize.2) ?_
    intro outputIndex
    refine xResult_bind (nonspawn_popToNat outputIndex.2) ?_
    intro outputSize
    let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
    let lookup := sevm.benvStat.rules.gas.accessDelegation
      (addAccessedAddress outputSize.2 target.1) target.1
    let parent := lookup.2.2.2.2
    have hp : nonspawnPreserved outputSize.2 parent :=
      nonspawnPreserved_trans (nonspawn_addAccessedAddress outputSize.2 target.1)
        (nonspawn_delegation sevm.benvStat.rules.gas _ target.1)
    refine xResult_rebase (pre := outputSize.2) (middle := parent)
      (inner := 0) (outer := 0) hp.1 hp.2 ?_
    have hm : parent.memory = outputSize.2.memory :=
      (delegation_memory_output sevm.benvStat.rules.gas
        (addAccessedAddress outputSize.2 target.1) target.1).1
    have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
      simp only [Devm.extCost, hm]
    change xResult parent 0 (chargeGas
      ((calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (outputSize.2.extCost pairs)
        (sevm.benvStat.rules.gas.accessCost target.1 outputSize.2.accessedAddresses +
          lookup.2.2.2.1)).1 + outputSize.2.extCost pairs) parent >>= _)
    rw [hext]
    let costs := calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (parent.extCost pairs)
      (sevm.benvStat.rules.gas.accessCost target.1 outputSize.2.accessedAddresses +
        lookup.2.2.2.1)
    refine xResult_charged_call pairs costs.1 costs.2 parent ?_ _ ?_
    · exact calculateMsgCallGas_refund_le_base 0 gas.1.toNat parent.gasLeft
        (parent.extCost pairs)
        (sevm.benvStat.rules.gas.accessCost target.1 outputSize.2.accessedAddresses +
          lookup.2.2.2.1) gCallStipend (Nat.zero_le _)
    · intro charged
      exact genericCall_memory_allowance sevm (charged.memExtends pairs) costs.2
        0 sevm.currentTarget target.1 lookup.2.1
        true true inputIndex.1 inputSize.1 outputIndex.1 outputSize.1
        lookup.2.2.1 lookup.1
  case call =>
    apply xAccounting_ofExcept
    refine xResult_bind (nonspawn_pop pre) ?_
    intro gas
    refine xResult_bind (nonspawn_popToAdr gas.2) ?_
    intro callee
    refine xResult_bind (nonspawn_pop callee.2) ?_
    intro value
    refine xResult_bind (nonspawn_popToNat value.2) ?_
    intro inputIndex
    refine xResult_bind (nonspawn_popToNat inputIndex.2) ?_
    intro inputSize
    refine xResult_bind (nonspawn_popToNat inputSize.2) ?_
    intro outputIndex
    refine xResult_bind (nonspawn_popToNat outputIndex.2) ?_
    intro outputSize
    let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
    let lookup := sevm.benvStat.rules.gas.accessDelegation
      (addAccessedAddress outputSize.2 callee.1) callee.1
    let parent := lookup.2.2.2.2
    have hp : nonspawnPreserved outputSize.2 parent :=
      nonspawnPreserved_trans (nonspawn_addAccessedAddress outputSize.2 callee.1)
        (nonspawn_delegation sevm.benvStat.rules.gas _ callee.1)
    refine xResult_rebase (pre := outputSize.2) (middle := parent)
      (inner := 0) (outer := 0) hp.1 hp.2 ?_
    have hm : parent.memory = outputSize.2.memory :=
      (delegation_memory_output sevm.benvStat.rules.gas
        (addAccessedAddress outputSize.2 callee.1) callee.1).1
    have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
      simp only [Devm.extCost, hm]
    let accessCost := sevm.benvStat.rules.gas.accessCost callee.1
      outputSize.2.accessedAddresses + lookup.2.2.2.1
    let createCost : Nat := if ¬(parent.getAcct callee.1).Empty ∨ value.1 = 0 then 0 else gNewAccount
    change xResult parent 0 (chargeGas
      ((calculateMsgCallGas value.1.toNat gas.1.toNat parent.gasLeft
        (outputSize.2.extCost pairs)
        (accessCost + createCost + if value.1 = 0 then 0 else sevm.benvStat.rules.gas.callValue)).1 +
          outputSize.2.extCost pairs) parent >>= _)
    rw [hext]
    let costs := calculateMsgCallGas value.1.toNat gas.1.toNat parent.gasLeft
      (parent.extCost pairs)
      (accessCost + createCost + if value.1 = 0 then 0 else sevm.benvStat.rules.gas.callValue)
    refine xResult_charged_call pairs costs.1 costs.2 parent ?_ _ ?_
    · exact value_call_refund_le_base sevm value.1 gas.1.toNat parent.gasLeft
        (parent.extCost pairs) accessCost createCost
    · intro charged
      refine xResult_bind
        (nonspawn_assert_at ((!sevm.isStatic) = true ∨ value.1 = 0)
          (.halt (.writeInStaticContext .none)) charged (charged.memExtends pairs)
          (nonspawn_before_paid pairs charged)) ?_
      intro _
      let paid := charged.memExtends pairs
      by_cases hb : (paid.getAcct sevm.currentTarget).bal < value.1
      · dsimp only [paid, pairs] at hb
        simp only [ite_eq_left hb]
        exact balance_refund_accounting paid costs.2
      · dsimp only [paid, pairs] at hb
        simp only [ite_eq_right hb]
        exact genericCall_memory_allowance sevm paid costs.2 value.1
          sevm.currentTarget callee.1 lookup.2.1 true false
          inputIndex.1 inputSize.1 outputIndex.1 outputSize.1 lookup.2.2.1 lookup.1

  case callcode =>
    apply xAccounting_ofExcept
    refine xResult_bind (nonspawn_pop pre) ?_
    intro gas
    refine xResult_bind (nonspawn_popToAdr gas.2) ?_
    intro codeAddress
    refine xResult_bind (nonspawn_pop codeAddress.2) ?_
    intro value
    refine xResult_bind (nonspawn_popToNat value.2) ?_
    intro inputIndex
    refine xResult_bind (nonspawn_popToNat inputIndex.2) ?_
    intro inputSize
    refine xResult_bind (nonspawn_popToNat inputSize.2) ?_
    intro outputIndex
    refine xResult_bind (nonspawn_popToNat outputIndex.2) ?_
    intro outputSize
    let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
    let lookup := sevm.benvStat.rules.gas.accessDelegation
      (addAccessedAddress outputSize.2 codeAddress.1) codeAddress.1
    let parent := lookup.2.2.2.2
    have hp : nonspawnPreserved outputSize.2 parent :=
      nonspawnPreserved_trans (nonspawn_addAccessedAddress outputSize.2 codeAddress.1)
        (nonspawn_delegation sevm.benvStat.rules.gas _ codeAddress.1)
    refine xResult_rebase (pre := outputSize.2) (middle := parent)
      (inner := 0) (outer := 0) hp.1 hp.2 ?_
    have hm : parent.memory = outputSize.2.memory :=
      (delegation_memory_output sevm.benvStat.rules.gas
        (addAccessedAddress outputSize.2 codeAddress.1) codeAddress.1).1
    have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
      simp only [Devm.extCost, hm]
    let accessCost := sevm.benvStat.rules.gas.accessCost codeAddress.1
      outputSize.2.accessedAddresses + lookup.2.2.2.1
    let createCost : Nat := 0
    change xResult parent 0 (chargeGas
      ((calculateMsgCallGas value.1.toNat gas.1.toNat parent.gasLeft
        (outputSize.2.extCost pairs)
        (accessCost + createCost + if value.1 = 0 then 0 else sevm.benvStat.rules.gas.callValue)).1 +
          outputSize.2.extCost pairs) parent >>= _)
    rw [hext]
    let costs := calculateMsgCallGas value.1.toNat gas.1.toNat parent.gasLeft
      (parent.extCost pairs)
      (accessCost + createCost + if value.1 = 0 then 0 else sevm.benvStat.rules.gas.callValue)
    refine xResult_charged_call pairs costs.1 costs.2 parent ?_ _ ?_
    · exact value_call_refund_le_base sevm value.1 gas.1.toNat parent.gasLeft
        (parent.extCost pairs) accessCost createCost
    · intro charged
      let paid := charged.memExtends pairs
      by_cases hb : (paid.getAcct sevm.currentTarget).bal < value.1
      · dsimp only [paid, pairs] at hb
        simp only [ite_eq_left hb]
        exact balance_refund_accounting paid costs.2
      · dsimp only [paid, pairs] at hb
        simp only [ite_eq_right hb]
        exact genericCall_memory_allowance sevm paid costs.2 value.1
          sevm.currentTarget sevm.currentTarget lookup.2.1 true false
          inputIndex.1 inputSize.1 outputIndex.1 outputSize.1 lookup.2.2.1 lookup.1

private def rawTerminalAccounted (pre : Devm) (raw : Execution) : Prop :=
  match raw with
  | .ok post => accountedTerminal pre post
  | .error failure => accountedTerminal pre failure.2

private def stepAccounted (pre : Devm) : Step → Prop
  | .cont _ post => nonspawnPreserved pre post
  | .halt raw => rawTerminalAccounted pre raw
  | .spawn _ _ _ => True

private theorem ofExecution_accounted (pc : Nat) {pre : Devm} {raw : Execution}
    (h : nonspawnResult pre id raw) : stepAccounted pre (Step.ofExecution pc raw) := by
  cases raw with
  | error failure => exact ⟨h.1, Or.inl h.2⟩
  | ok post => exact h

private theorem ofJump_accounted {pre : Devm}
    {raw : Except (EvmError × Devm) (Nat × Devm)}
    (h : nonspawnResult pre Prod.snd raw) : stepAccounted pre (Step.ofJump raw) := by
  cases raw with
  | error failure => exact ⟨h.1, Or.inl h.2⟩
  | ok value => rcases value with ⟨pc, post⟩; exact h

private theorem ofXStep_accounted (pc : Nat) {pre : Devm} {step : XStep}
    (h : xAccounting pre 0 step) : stepAccounted pre (XStep.toStep pc step) := by
  cases step with
  | spawn _ _ => trivial
  | done raw =>
      cases raw with
      | error failure => exact ⟨h.1, Or.inl h.2⟩
      | ok post => exact h

private theorem nonterminal_memory_accounting (evm : Evm) (n : Ninst)
    (hstate : evm.sta.benvStat.rules.stateGas = none) :
    stepAccounted evm.dyna (Ninst.step evm n) := by
  cases n <;> simp only [Ninst.step]
  case reg r =>
    exact ofExecution_accounted _
      (regular_memory_accounting evm.pc evm.dyna evm.sta r hstate)
  case exec x =>
    exact ofXStep_accounted _ (executable_memory_accounting evm.sta evm.dyna x hstate)
  case push bytes bound =>
    apply ofExecution_accounted
    refine nonspawnResult_bind (nonspawn_charge _ evm.dyna) ?_
    intro charged
    exact nonspawn_push bytes.toB256 charged
  case dupn imm =>
    apply ofExecution_accounted
    by_cases hf : evm.sta.benvStat.rules.op.stackAccess = true
    · simp only [ite_eq_left hf]
      refine nonspawnResult_bind (nonspawn_charge gVerylow evm.dyna) ?_
      intro charged
      cases hd : decodeSingle imm with
      | none => exact ⟨Nat.le_refl _, rfl⟩
      | some index =>
          dsimp only
          cases hs : charged.stack[index - 1]? with
          | none => exact ⟨Nat.le_refl _, rfl⟩
          | some word => exact nonspawn_push word charged
    · simp only [ite_eq_right hf]
      exact ⟨Nat.le_refl _, rfl⟩
  case swapn imm =>
    apply ofExecution_accounted
    by_cases hf : evm.sta.benvStat.rules.op.stackAccess = true
    · simp only [ite_eq_left hf]
      refine nonspawnResult_bind (nonspawn_charge gVerylow evm.dyna) ?_
      intro charged
      cases hd : decodeSingle imm with
      | none => exact ⟨Nat.le_refl _, rfl⟩
      | some index =>
          dsimp only
          cases hs : List.swap charged.stack (index - 1) with
          | none => exact ⟨Nat.le_refl _, rfl⟩
          | some stack => exact ⟨Nat.le_refl _, rfl⟩
    · simp only [ite_eq_right hf]
      exact ⟨Nat.le_refl _, rfl⟩
  case exchange imm =>
    apply ofExecution_accounted
    by_cases hf : evm.sta.benvStat.rules.op.stackAccess = true
    · simp only [ite_eq_left hf]
      refine nonspawnResult_bind (nonspawn_charge gVerylow evm.dyna) ?_
      intro charged
      cases hd : decodePair imm with
      | none => exact ⟨Nat.le_refl _, rfl⟩
      | some pair =>
          rcases pair with ⟨first, second⟩
          dsimp only
          cases hs : List.exchange charged.stack first second with
          | none => exact ⟨Nat.le_refl _, rfl⟩
          | some stack => exact ⟨Nat.le_refl _, rfl⟩
    · simp only [ite_eq_right hf]
      exact ⟨Nat.le_refl _, rfl⟩

/-- Every actual nonspawn step preserves the memory/gas potential. Continued
frames inherit output; terminal raw outcomes inherit it or account for its
complete length through the charged terminal read. Spawn is accounted separately. -/
theorem Evm.step_memory_accounting_output (evm : Evm)
    (hstate : evm.sta.benvStat.rules.stateGas = none) :
    let initial := evm.dyna.gasMeasure + calculateMemoryGasCost evm.dyna.memory.size
    let accounted := fun post : Devm =>
      post.gasMeasure + calculateMemoryGasCost post.memory.size ≤ initial ∧
        (post.output = evm.dyna.output ∨
          calculateMemoryGasCost post.output.length ≤ initial)
    match Evm.step evm with
    | .cont _ post =>
        post.gasMeasure + calculateMemoryGasCost post.memory.size ≤ initial ∧
          post.output = evm.dyna.output
    | .halt raw =>
        match raw with
        | .ok post => accounted post
        | .error failure => accounted failure.2
    | .spawn _ _ _ => True := by
  change stepAccounted evm.dyna (Evm.step evm)
  cases hi : evm.getInst with
  | none =>
      simp only [Evm.step, hi]
      exact ⟨Nat.le_refl _, Or.inl rfl⟩
  | some instruction =>
      cases instruction with
      | next n =>
          simp only [Evm.step, hi]
          exact nonterminal_memory_accounting evm n hstate
      | jump j =>
          simp only [Evm.step, hi]
          exact ofJump_accounted (jump_memory_accounting evm.pc evm.dyna evm.sta j)
      | last l =>
          simp only [Evm.step, hi]
          exact Linst.run_memory_accounting_output evm.sta evm.dyna l hstate


private theorem call_run_size_output (parent : Devm) (outputIndex outputSize : Nat)
    (r : Except (EvmError × State × AdrSet × Tra) Devm)
    (hwindow : outputSize ≠ 0 → outputIndex + outputSize ≤ parent.memory.size) :
    match (Resume.call parent outputIndex outputSize).run r with
    | .error failure =>
        failure.2.memory.size = parent.memory.size ∧ failure.2.output = parent.output
    | .ok post => post.memory.size = parent.memory.size ∧ post.output = parent.output := by
  cases r with
  | error failure => exact ⟨rfl, rfl⟩
  | ok child =>
      have ho := call_run_memory_output parent outputIndex outputSize (.ok child)
      rcases hr : (Resume.call parent outputIndex outputSize).run (.ok child) with failure | post
      · rw [hr] at ho
        exact ⟨congrArg Mem.size ho.1, ho.2⟩
      · rw [hr] at ho
        refine ⟨?_, ho⟩
        rw [Resume.call_run_ok_memory hr]
        apply Mem.write_size_of_prepaid
        intro hcopy
        have hsize : outputSize ≠ 0 := by
          intro hz
          rw [hz, List.take_zero] at hcopy
          exact hcopy rfl
        have hlength : (child.output.take outputSize).length ≤ outputSize := by
          rw [List.length_take]
          exact Nat.min_le_left _ _
        exact Nat.le_trans (Nat.add_le_add_left hlength outputIndex) (hwindow hsize)

private theorem create_run_memory_output (parent : Devm) (newAddress : Adr)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    match (Resume.create parent newAddress).run r with
    | .error failure => failure.2.memory = parent.memory ∧ failure.2.output = parent.output
    | .ok post => post.memory = parent.memory ∧ post.output = parent.output := by
  cases r with
  | error failure => exact ⟨rfl, rfl⟩
  | ok child =>
      by_cases he : child.error.isSome = true
      · simp only [Resume.run, liftToExecution, bind, Except.bind, he, ite_true]
        let incorporated := incorporateChildOnError parent child child.output
        rcases hp : incorporated.push 0 with failure | pushed
        · have hf := push_memory_output incorporated 0
          rw [hp] at hf
          exact hf
        · have hf := push_memory_output incorporated 0
          rw [hp] at hf
          exact hf
      · simp only [Resume.run, liftToExecution, bind, Except.bind, he]
        let incorporated := incorporateChildOnSuccess parent child []
        rcases hp : incorporated.push newAddress.toB256 with failure | pushed
        · have hf := push_memory_output incorporated newAddress.toB256
          rw [hp] at hf
          exact hf
        · have hf := push_memory_output incorporated newAddress.toB256
          rw [hp] at hf
          exact hf

private theorem call_run_memory_allowance (parent : Devm) (outputIndex outputSize grant : Nat)
    (r : Except (EvmError × State × AdrSet × Tra) Devm)
    (hwindow : outputSize ≠ 0 → outputIndex + outputSize ≤ parent.memory.size)
    (hchild : ∀ child, r = .ok child → child.gasMeasure ≤ grant) :
    allowanceResult parent grant ((Resume.call parent outputIndex outputSize).run r) := by
  have hf := call_run_size_output parent outputIndex outputSize r hwindow
  have hg := Resume.run_gasLe (rsm := .call parent outputIndex outputSize) hchild
  rcases hr : (Resume.call parent outputIndex outputSize).run r with failure | post
  · rw [hr] at hf hg
    change failure.2.gasMeasure ≤ parent.gasMeasure + grant at hg
    change allowancePreserved parent grant failure.2
    refine ⟨?_, hf.2⟩
    rw [hf.1]
    omega
  · rw [hr] at hf hg
    change post.gasMeasure ≤ parent.gasMeasure + grant at hg
    change allowancePreserved parent grant post
    refine ⟨?_, hf.2⟩
    rw [hf.1]
    omega

private theorem create_run_memory_allowance (parent : Devm) (newAddress : Adr) (grant : Nat)
    (r : Except (EvmError × State × AdrSet × Tra) Devm)
    (hchild : ∀ child, r = .ok child → child.gasMeasure ≤ grant) :
    allowanceResult parent grant ((Resume.create parent newAddress).run r) := by
  have hf := create_run_memory_output parent newAddress r
  have hg := Resume.run_gasLe (rsm := .create parent newAddress) hchild
  rcases hr : (Resume.create parent newAddress).run r with failure | post
  · rw [hr] at hf hg
    change failure.2.gasMeasure ≤ parent.gasMeasure + grant at hg
    change allowancePreserved parent grant failure.2
    refine ⟨?_, hf.2⟩
    rw [hf.1]
    omega
  · rw [hr] at hf hg
    change post.gasMeasure ≤ parent.gasMeasure + grant at hg
    change allowancePreserved parent grant post
    refine ⟨?_, hf.2⟩
    rw [hf.1]
    omega


private def spawnAccounting (pre : Devm) (allowance : Nat) : XStep → Prop
  | .done _ => True
  | .spawn frame resume =>
      ∀ r : Except (EvmError × State × AdrSet × Tra) Devm,
        (∀ child, r = .ok child → child.gasMeasure ≤ frame.inner.gas) →
        allowanceResult pre allowance (resume.run r)

private def spawnResult (pre : Devm) (allowance : Nat)
    (raw : Except (EvmError × Devm) XStep) : Prop :=
  match raw with
  | .error _ => True
  | .ok step => spawnAccounting pre allowance step

private theorem allowanceResult_rebase {pre middle : Devm} {inner outer : Nat}
    {raw : Execution}
    (hp : middle.gasMeasure + calculateMemoryGasCost middle.memory.size + inner ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + outer)
    (ho : middle.output = pre.output) (h : allowanceResult middle inner raw) :
    allowanceResult pre outer raw := by
  cases raw with
  | error failure => exact allowance_rebase hp ho h
  | ok post => exact allowance_rebase hp ho h

private theorem spawnAccounting_rebase {pre middle : Devm} {inner outer : Nat}
    {step : XStep}
    (hp : middle.gasMeasure + calculateMemoryGasCost middle.memory.size + inner ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + outer)
    (ho : middle.output = pre.output) (h : spawnAccounting middle inner step) :
    spawnAccounting pre outer step := by
  cases step with
  | done raw => trivial
  | spawn frame resume =>
      intro r hchild
      exact allowanceResult_rebase hp ho (h r hchild)

private theorem spawnResult_rebase {pre middle : Devm} {inner outer : Nat}
    {raw : Except (EvmError × Devm) XStep}
    (hp : middle.gasMeasure + calculateMemoryGasCost middle.memory.size + inner ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + outer)
    (ho : middle.output = pre.output) (h : spawnResult middle inner raw) :
    spawnResult pre outer raw := by
  cases raw with
  | error failure => trivial
  | ok step => exact spawnAccounting_rebase hp ho h

private theorem spawnResult_bind {α : Type} {pre : Devm} {allowance : Nat}
    {first : Except (EvmError × Devm) α} {next : α → Except (EvmError × Devm) XStep}
    {project : α → Devm}
    (hf : nonspawnResult pre project first)
    (hn : ∀ value, spawnResult (project value) allowance (next value)) :
    spawnResult pre allowance (first >>= next) := by
  cases first with
  | error failure => trivial
  | ok value =>
      apply spawnResult_rebase (ho := hf.2) (h := hn value)
      have hp := hf.1
      omega

private theorem spawnAccounting_ofExcept {pre : Devm} {allowance : Nat}
    {raw : Except (EvmError × Devm) XStep} (h : spawnResult pre allowance raw) :
    spawnAccounting pre allowance (XStep.ofExcept raw) := by
  cases raw with
  | error failure => trivial
  | ok step => exact h

private theorem spawnResult_charged_memory (pairs : List (Nat × Nat)) (baseCost : Nat)
    (pre : Devm) (action : Devm → Except (EvmError × Devm) XStep)
    (hbody : ∀ charged, spawnResult (charged.memExtends pairs) baseCost (action charged)) :
    spawnResult pre 0 (chargeGas (baseCost + pre.extCost pairs) pre >>= action) := by
  rcases hc : chargeGas (baseCost + pre.extCost pairs) pre with failure | charged
  · trivial
  · have hf := charge_memory_output (baseCost + pre.extCost pairs) pre
    rw [hc] at hf
    refine spawnResult_rebase (pre := pre) (middle := charged.memExtends pairs)
      (inner := baseCost) (outer := 0) ?_ hf.2 (hbody charged)
    have ha := charged_memExtends_accounting pairs baseCost hc
    omega

private theorem spawnResult_charged_call (pairs : List (Nat × Nat)) (cost refund : Nat)
    (pre : Devm) (hrefund : refund ≤ cost)
    (action : Devm → Except (EvmError × Devm) XStep)
    (hbody : ∀ charged, spawnResult (charged.memExtends pairs) refund (action charged)) :
    spawnResult pre 0 (chargeGas (cost + pre.extCost pairs) pre >>= action) := by
  refine spawnResult_charged_memory pairs cost pre action ?_
  intro charged
  exact spawnResult_rebase (pre := charged.memExtends pairs)
    (middle := charged.memExtends pairs) (inner := refund) (outer := cost)
    (Nat.add_le_add_left hrefund _) rfl (hbody charged)

private theorem spawnResult_done_push (word : B256) (pre : Devm) (allowance : Nat)
    (reference : Devm) :
    spawnResult reference allowance (do
      let post ← pre.push word
      pure (.done (.ok post))) := by
  cases pre.push word <;> trivial

private theorem genericCall_spawn_allowance
    (sevm : Sevm) (pre : Devm) (gas : Nat) (value : B256)
    (caller target codeAddress : Adr) (transfer staticCall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disable : Bool)
    (hwindow : outputSize ≠ 0 → outputIndex + outputSize ≤ pre.memory.size) :
    spawnAccounting pre gas (genericCall.step sevm pre gas value caller target codeAddress
      transfer staticCall inputIndex inputSize outputIndex outputSize code disable) := by
  unfold genericCall.step
  split
  · apply spawnAccounting_ofExcept
    exact spawnResult_done_push 0
      ((pre.withReturnData []).withGasLeft ((pre.withReturnData []).gasLeft + gas)) gas pre
  · intro r hchild
    exact call_run_memory_allowance (pre.withReturnData []) outputIndex outputSize gas
      r hwindow hchild

private theorem genericCreate_spawn_accounting
    (sevm : Sevm) (pre : Devm) (endowment : B256)
    (newAddress : Adr) (memoryIndex memorySize : Nat) :
    spawnAccounting pre 0
      (genericCreate.step sevm pre endowment newAddress memoryIndex memorySize) := by
  unfold genericCreate.step
  apply spawnAccounting_ofExcept
  refine spawnResult_bind
    (nonspawn_assert (memorySize ≤ sevm.benvStat.rules.code.maxInitCodeSize)
      (.halt (.outOfGas .none)) pre) ?_
  intro _
  let grant := except64th pre.gasLeft
  let withheld := pre.withGasLeft (pre.gasLeft - grant)
  have hg : grant ≤ pre.gasLeft := except64th_le pre.gasLeft
  have hhold : nonspawnPreserved pre withheld := by
    refine ⟨?_, rfl⟩
    dsimp only [withheld]
    rw [Devm.withGasLeft_gasMeasure]
    change (pre.gasLeft - grant + pre.spill) +
      calculateMemoryGasCost pre.memory.size ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size
    have hm := Devm.gasMeasure_eq pre
    omega
  refine spawnResult_bind
    (nonspawn_assert_at ((!sevm.isStatic) = true)
      (.halt (.writeInStaticContext .none)) withheld pre hhold) ?_
  intro _
  let current := withheld.withReturnData []
  by_cases hfail : (current.state.get sevm.currentTarget).bal < endowment ∨
      (current.state.get sevm.currentTarget).nonce = UInt64.max ∨ sevm.depth = 0
  · dsimp only [current, withheld, grant] at hfail
    simp only [ite_eq_left hfail]
    exact spawnResult_done_push 0 (current.withGasLeft (current.gasLeft + grant)) 0 pre
  · dsimp only [current, withheld, grant] at hfail
    simp only [ite_eq_right hfail]
    let accessed := addAccessedAddress (current.incrNonce sevm.currentTarget) newAddress
    by_cases hcollision : (accessed.state.get newAddress).nonce ≠ (0 : UInt64) ∨
        (accessed.state.get newAddress).code.size ≠ 0 ∨
        (accessed.state.get newAddress).stor.size ≠ 0
    · dsimp only [accessed, current, withheld, grant] at hcollision
      simp only [ite_eq_left hcollision]
      exact spawnResult_done_push 0 accessed 0 pre
    · dsimp only [accessed, current, withheld, grant] at hcollision
      simp only [ite_eq_right hcollision]
      intro r hchild
      have hr := create_run_memory_allowance accessed newAddress grant r hchild
      apply allowanceResult_rebase (pre := pre) (middle := accessed)
        (inner := grant) (outer := 0) ?_ rfl hr
      dsimp only [accessed, current, withheld]
      simp only [addAccessedAddress_gasMeasure, Devm.incrNonce_gasMeasure,
        Devm.withReturnData_gasMeasure, Devm.withGasLeft_gasMeasure]
      change (pre.gasLeft - grant + pre.spill) +
        calculateMemoryGasCost pre.memory.size + grant ≤
        pre.gasMeasure + calculateMemoryGasCost pre.memory.size + 0
      have hm := Devm.gasMeasure_eq pre
      omega


private theorem call_output_window (charged : Devm)
    (inputIndex inputSize outputIndex outputSize : Nat) :
    outputSize ≠ 0 →
      outputIndex + outputSize ≤
        (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).memory.size := by
  intro hsize
  change outputIndex + outputSize ≤
    memExtSize (memExtSize charged.memory.size inputIndex inputSize) outputIndex outputSize
  exact memExtSize_access_le _ outputIndex outputSize hsize

private theorem executable_spawn_accounting (sevm : Sevm) (pre : Devm) (x : Xinst)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    spawnAccounting pre 0 (Xinst.step sevm pre x) := by
  cases x <;> simp only [Xinst.step, hstate]
  case create =>
    apply spawnAccounting_ofExcept
    refine spawnResult_bind (nonspawn_pop pre) ?_
    intro endowment
    refine spawnResult_bind (nonspawn_popToNat endowment.2) ?_
    intro memoryIndex
    refine spawnResult_bind (nonspawn_popToNat memoryIndex.2) ?_
    intro memorySize
    rw [Nat.add_right_comm sevm.benvStat.rules.gas.createAccess
      (memorySize.2.extCost [(memoryIndex.1, memorySize.1)])
      (gasInitCodeWordCost * ceilDiv memorySize.1 32)]
    refine spawnResult_charged_memory [(memoryIndex.1, memorySize.1)]
      (sevm.benvStat.rules.gas.createAccess + gasInitCodeWordCost * ceilDiv memorySize.1 32)
      memorySize.2 _ ?_
    intro charged
    refine spawnAccounting_rebase (pre := charged.memExtends [(memoryIndex.1, memorySize.1)])
      (inner := 0) ?_ rfl
      (genericCreate_spawn_accounting sevm _ endowment.1 _ memoryIndex.1 memorySize.1)
    omega
  case create2 =>
    apply spawnAccounting_ofExcept
    refine spawnResult_bind (nonspawn_pop pre) ?_
    intro endowment
    refine spawnResult_bind (nonspawn_popToNat endowment.2) ?_
    intro memoryIndex
    refine spawnResult_bind (nonspawn_popToNat memoryIndex.2) ?_
    intro memorySize
    refine spawnResult_bind (nonspawn_pop memorySize.2) ?_
    intro salt
    rw [Nat.add_right_comm
      (sevm.benvStat.rules.gas.createAccess + gasKeccak256Word * ceilDiv memorySize.1 32)
      (salt.2.extCost [(memoryIndex.1, memorySize.1)])
      (gasInitCodeWordCost * ceilDiv memorySize.1 32)]
    refine spawnResult_charged_memory [(memoryIndex.1, memorySize.1)]
      (sevm.benvStat.rules.gas.createAccess + gasKeccak256Word * ceilDiv memorySize.1 32 +
        gasInitCodeWordCost * ceilDiv memorySize.1 32)
      salt.2 _ ?_
    intro charged
    refine spawnAccounting_rebase (pre := charged.memExtends [(memoryIndex.1, memorySize.1)])
      (inner := 0) ?_ rfl
      (genericCreate_spawn_accounting sevm _ endowment.1 _ memoryIndex.1 memorySize.1)
    omega
  case delegatecall =>
    apply spawnAccounting_ofExcept
    refine spawnResult_bind (nonspawn_pop pre) ?_
    intro gas
    refine spawnResult_bind (nonspawn_popToAdr gas.2) ?_
    intro codeAddress
    refine spawnResult_bind (nonspawn_popToNat codeAddress.2) ?_
    intro inputIndex
    refine spawnResult_bind (nonspawn_popToNat inputIndex.2) ?_
    intro inputSize
    refine spawnResult_bind (nonspawn_popToNat inputSize.2) ?_
    intro outputIndex
    refine spawnResult_bind (nonspawn_popToNat outputIndex.2) ?_
    intro outputSize
    let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
    let lookup := sevm.benvStat.rules.gas.accessDelegation
      (addAccessedAddress outputSize.2 codeAddress.1) codeAddress.1
    let parent := lookup.2.2.2.2
    have hp : nonspawnPreserved outputSize.2 parent :=
      nonspawnPreserved_trans (nonspawn_addAccessedAddress outputSize.2 codeAddress.1)
        (nonspawn_delegation sevm.benvStat.rules.gas _ codeAddress.1)
    refine spawnResult_rebase (pre := outputSize.2) (middle := parent)
      (inner := 0) (outer := 0) hp.1 hp.2 ?_
    have hm : parent.memory = outputSize.2.memory :=
      (delegation_memory_output sevm.benvStat.rules.gas
        (addAccessedAddress outputSize.2 codeAddress.1) codeAddress.1).1
    have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
      simp only [Devm.extCost, hm]
    change spawnResult parent 0 (chargeGas
      ((calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (outputSize.2.extCost pairs)
        (sevm.benvStat.rules.gas.accessCost codeAddress.1 outputSize.2.accessedAddresses +
          lookup.2.2.2.1)).1 + outputSize.2.extCost pairs) parent >>= _)
    rw [hext]
    let costs := calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (parent.extCost pairs)
      (sevm.benvStat.rules.gas.accessCost codeAddress.1 outputSize.2.accessedAddresses +
        lookup.2.2.2.1)
    refine spawnResult_charged_call pairs costs.1 costs.2 parent ?_ _ ?_
    · exact calculateMsgCallGas_refund_le_base 0 gas.1.toNat parent.gasLeft
        (parent.extCost pairs)
        (sevm.benvStat.rules.gas.accessCost codeAddress.1 outputSize.2.accessedAddresses +
          lookup.2.2.2.1) gCallStipend (Nat.zero_le _)
    · intro charged
      exact genericCall_spawn_allowance sevm (charged.memExtends pairs) costs.2
        sevm.value sevm.caller sevm.currentTarget lookup.2.1
        false false inputIndex.1 inputSize.1 outputIndex.1 outputSize.1
        lookup.2.2.1 lookup.1 (call_output_window charged inputIndex.1 inputSize.1 outputIndex.1 outputSize.1)

  case staticcall =>
    apply spawnAccounting_ofExcept
    refine spawnResult_bind (nonspawn_pop pre) ?_
    intro gas
    refine spawnResult_bind (nonspawn_popToAdr gas.2) ?_
    intro target
    refine spawnResult_bind (nonspawn_popToNat target.2) ?_
    intro inputIndex
    refine spawnResult_bind (nonspawn_popToNat inputIndex.2) ?_
    intro inputSize
    refine spawnResult_bind (nonspawn_popToNat inputSize.2) ?_
    intro outputIndex
    refine spawnResult_bind (nonspawn_popToNat outputIndex.2) ?_
    intro outputSize
    let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
    let lookup := sevm.benvStat.rules.gas.accessDelegation
      (addAccessedAddress outputSize.2 target.1) target.1
    let parent := lookup.2.2.2.2
    have hp : nonspawnPreserved outputSize.2 parent :=
      nonspawnPreserved_trans (nonspawn_addAccessedAddress outputSize.2 target.1)
        (nonspawn_delegation sevm.benvStat.rules.gas _ target.1)
    refine spawnResult_rebase (pre := outputSize.2) (middle := parent)
      (inner := 0) (outer := 0) hp.1 hp.2 ?_
    have hm : parent.memory = outputSize.2.memory :=
      (delegation_memory_output sevm.benvStat.rules.gas
        (addAccessedAddress outputSize.2 target.1) target.1).1
    have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
      simp only [Devm.extCost, hm]
    change spawnResult parent 0 (chargeGas
      ((calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (outputSize.2.extCost pairs)
        (sevm.benvStat.rules.gas.accessCost target.1 outputSize.2.accessedAddresses +
          lookup.2.2.2.1)).1 + outputSize.2.extCost pairs) parent >>= _)
    rw [hext]
    let costs := calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (parent.extCost pairs)
      (sevm.benvStat.rules.gas.accessCost target.1 outputSize.2.accessedAddresses +
        lookup.2.2.2.1)
    refine spawnResult_charged_call pairs costs.1 costs.2 parent ?_ _ ?_
    · exact calculateMsgCallGas_refund_le_base 0 gas.1.toNat parent.gasLeft
        (parent.extCost pairs)
        (sevm.benvStat.rules.gas.accessCost target.1 outputSize.2.accessedAddresses +
          lookup.2.2.2.1) gCallStipend (Nat.zero_le _)
    · intro charged
      exact genericCall_spawn_allowance sevm (charged.memExtends pairs) costs.2
        0 sevm.currentTarget target.1 lookup.2.1
        true true inputIndex.1 inputSize.1 outputIndex.1 outputSize.1
        lookup.2.2.1 lookup.1 (call_output_window charged inputIndex.1 inputSize.1 outputIndex.1 outputSize.1)
  case call =>
    apply spawnAccounting_ofExcept
    refine spawnResult_bind (nonspawn_pop pre) ?_
    intro gas
    refine spawnResult_bind (nonspawn_popToAdr gas.2) ?_
    intro callee
    refine spawnResult_bind (nonspawn_pop callee.2) ?_
    intro value
    refine spawnResult_bind (nonspawn_popToNat value.2) ?_
    intro inputIndex
    refine spawnResult_bind (nonspawn_popToNat inputIndex.2) ?_
    intro inputSize
    refine spawnResult_bind (nonspawn_popToNat inputSize.2) ?_
    intro outputIndex
    refine spawnResult_bind (nonspawn_popToNat outputIndex.2) ?_
    intro outputSize
    let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
    let lookup := sevm.benvStat.rules.gas.accessDelegation
      (addAccessedAddress outputSize.2 callee.1) callee.1
    let parent := lookup.2.2.2.2
    have hp : nonspawnPreserved outputSize.2 parent :=
      nonspawnPreserved_trans (nonspawn_addAccessedAddress outputSize.2 callee.1)
        (nonspawn_delegation sevm.benvStat.rules.gas _ callee.1)
    refine spawnResult_rebase (pre := outputSize.2) (middle := parent)
      (inner := 0) (outer := 0) hp.1 hp.2 ?_
    have hm : parent.memory = outputSize.2.memory :=
      (delegation_memory_output sevm.benvStat.rules.gas
        (addAccessedAddress outputSize.2 callee.1) callee.1).1
    have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
      simp only [Devm.extCost, hm]
    let accessCost := sevm.benvStat.rules.gas.accessCost callee.1
      outputSize.2.accessedAddresses + lookup.2.2.2.1
    let createCost : Nat := if ¬(parent.getAcct callee.1).Empty ∨ value.1 = 0 then 0 else gNewAccount
    change spawnResult parent 0 (chargeGas
      ((calculateMsgCallGas value.1.toNat gas.1.toNat parent.gasLeft
        (outputSize.2.extCost pairs)
        (accessCost + createCost + if value.1 = 0 then 0 else sevm.benvStat.rules.gas.callValue)).1 +
          outputSize.2.extCost pairs) parent >>= _)
    rw [hext]
    let costs := calculateMsgCallGas value.1.toNat gas.1.toNat parent.gasLeft
      (parent.extCost pairs)
      (accessCost + createCost + if value.1 = 0 then 0 else sevm.benvStat.rules.gas.callValue)
    refine spawnResult_charged_call pairs costs.1 costs.2 parent ?_ _ ?_
    · exact value_call_refund_le_base sevm value.1 gas.1.toNat parent.gasLeft
        (parent.extCost pairs) accessCost createCost
    · intro charged
      refine spawnResult_bind
        (nonspawn_assert_at ((!sevm.isStatic) = true ∨ value.1 = 0)
          (.halt (.writeInStaticContext .none)) charged (charged.memExtends pairs)
          (nonspawn_before_paid pairs charged)) ?_
      intro _
      let paid := charged.memExtends pairs
      by_cases hb : (paid.getAcct sevm.currentTarget).bal < value.1
      · dsimp only [paid, pairs] at hb
        simp only [ite_eq_left hb]
        cases hp : paid.push 0 <;> trivial
      · dsimp only [paid, pairs] at hb
        simp only [ite_eq_right hb]
        exact genericCall_spawn_allowance sevm paid costs.2 value.1
          sevm.currentTarget callee.1 lookup.2.1 true false
          inputIndex.1 inputSize.1 outputIndex.1 outputSize.1 lookup.2.2.1 lookup.1
          (call_output_window charged inputIndex.1 inputSize.1 outputIndex.1 outputSize.1)

  case callcode =>
    apply spawnAccounting_ofExcept
    refine spawnResult_bind (nonspawn_pop pre) ?_
    intro gas
    refine spawnResult_bind (nonspawn_popToAdr gas.2) ?_
    intro codeAddress
    refine spawnResult_bind (nonspawn_pop codeAddress.2) ?_
    intro value
    refine spawnResult_bind (nonspawn_popToNat value.2) ?_
    intro inputIndex
    refine spawnResult_bind (nonspawn_popToNat inputIndex.2) ?_
    intro inputSize
    refine spawnResult_bind (nonspawn_popToNat inputSize.2) ?_
    intro outputIndex
    refine spawnResult_bind (nonspawn_popToNat outputIndex.2) ?_
    intro outputSize
    let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
    let lookup := sevm.benvStat.rules.gas.accessDelegation
      (addAccessedAddress outputSize.2 codeAddress.1) codeAddress.1
    let parent := lookup.2.2.2.2
    have hp : nonspawnPreserved outputSize.2 parent :=
      nonspawnPreserved_trans (nonspawn_addAccessedAddress outputSize.2 codeAddress.1)
        (nonspawn_delegation sevm.benvStat.rules.gas _ codeAddress.1)
    refine spawnResult_rebase (pre := outputSize.2) (middle := parent)
      (inner := 0) (outer := 0) hp.1 hp.2 ?_
    have hm : parent.memory = outputSize.2.memory :=
      (delegation_memory_output sevm.benvStat.rules.gas
        (addAccessedAddress outputSize.2 codeAddress.1) codeAddress.1).1
    have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
      simp only [Devm.extCost, hm]
    let accessCost := sevm.benvStat.rules.gas.accessCost codeAddress.1
      outputSize.2.accessedAddresses + lookup.2.2.2.1
    let createCost : Nat := 0
    change spawnResult parent 0 (chargeGas
      ((calculateMsgCallGas value.1.toNat gas.1.toNat parent.gasLeft
        (outputSize.2.extCost pairs)
        (accessCost + createCost + if value.1 = 0 then 0 else sevm.benvStat.rules.gas.callValue)).1 +
          outputSize.2.extCost pairs) parent >>= _)
    rw [hext]
    let costs := calculateMsgCallGas value.1.toNat gas.1.toNat parent.gasLeft
      (parent.extCost pairs)
      (accessCost + createCost + if value.1 = 0 then 0 else sevm.benvStat.rules.gas.callValue)
    refine spawnResult_charged_call pairs costs.1 costs.2 parent ?_ _ ?_
    · exact value_call_refund_le_base sevm value.1 gas.1.toNat parent.gasLeft
        (parent.extCost pairs) accessCost createCost
    · intro charged
      let paid := charged.memExtends pairs
      by_cases hb : (paid.getAcct sevm.currentTarget).bal < value.1
      · dsimp only [paid, pairs] at hb
        simp only [ite_eq_left hb]
        cases hp : paid.push 0 <;> trivial
      · dsimp only [paid, pairs] at hb
        simp only [ite_eq_right hb]
        exact genericCall_spawn_allowance sevm paid costs.2 value.1
          sevm.currentTarget sevm.currentTarget lookup.2.1 true false
          inputIndex.1 inputSize.1 outputIndex.1 outputSize.1 lookup.2.2.1 lookup.1
          (call_output_window charged inputIndex.1 inputSize.1 outputIndex.1 outputSize.1)

private theorem step_spawn_resume_accounting
    (evm : Evm) (hstate : evm.sta.benvStat.rules.stateGas = none)
    {frame : Frame} {resume : Resume} {pc' : Nat}
    (hspawn : Evm.step evm = .spawn frame resume pc')
    (r : Except (EvmError × State × AdrSet × Tra) Devm)
    (hchild : ∀ child, r = .ok child → child.gasMeasure ≤ frame.inner.gas) :
    nonspawnResult evm.dyna id (resume.run r) := by
  cases hi : evm.getInst with
  | none =>
      simp only [Evm.step, hi] at hspawn
      cases hspawn
  | some instruction =>
      cases instruction with
      | next n =>
          simp only [Evm.step, hi] at hspawn
          obtain ⟨x, _, hs⟩ := Ninst.step_spawn_inv hspawn
          have ha := executable_spawn_accounting evm.sta evm.dyna x hstate
          rw [hs] at ha
          have hr := ha r hchild
          cases hraw : resume.run r with
          | error failure =>
              rw [hraw] at hr
              exact ⟨by simpa only [Nat.add_zero] using hr.1, hr.2⟩
          | ok post =>
              rw [hraw] at hr
              exact ⟨by simpa only [Nat.add_zero, id] using hr.1, hr.2⟩
      | jump j =>
          simp only [Evm.step, hi] at hspawn
          cases Step.ofJump_ne_spawn hspawn
      | last l =>
          simp only [Evm.step, hi] at hspawn
          cases hspawn


private theorem raw_accounting_trans {pre middle : Devm} {raw : Execution}
    (hp : nonspawnPreserved pre middle) (hr : rawTerminalAccounted middle raw) :
    rawTerminalAccounted pre raw := by
  cases raw with
  | error failure =>
      refine ⟨Nat.le_trans hr.1 hp.1, ?_⟩
      cases hr.2 with
      | inl ho => exact Or.inl (ho.trans hp.2)
      | inr hc => exact Or.inr (Nat.le_trans hc hp.1)
  | ok post =>
      refine ⟨Nat.le_trans hr.1 hp.1, ?_⟩
      cases hr.2 with
      | inl ho => exact Or.inl (ho.trans hp.2)
      | inr hc => exact Or.inr (Nat.le_trans hc hp.1)

private theorem raw_accounting_gas_le {pre : Devm} {raw : Execution}
    (hr : rawTerminalAccounted pre raw) :
    raw.gasMeasure ≤ pre.gasMeasure + calculateMemoryGasCost pre.memory.size := by
  cases raw with
  | error failure =>
      change failure.2.gasMeasure ≤ _
      have hp := hr.1
      omega
  | ok post =>
      change post.gasMeasure ≤ _
      have hp := hr.1
      omega

private theorem spawned_child_stateGas_none (evm : Evm)
    (hstate : evm.sta.benvStat.rules.stateGas = none)
    {frame : Frame} {resume : Resume} {pc' : Nat} {child : Evm}
    (hspawn : Evm.step evm = .spawn frame resume pc')
    (henter : frame.enter = .run child) :
    child.sta.benvStat.rules.stateGas = none := by
  have hs := Evm.step_gasBound evm
  rw [hspawn] at hs
  rw [Frame.enter_run_benvStat henter, hs.2]
  exact hstate

private theorem entered_child_potential {frame : Frame} {child : Evm}
    (henter : frame.enter = .run child) :
    child.dyna.gasMeasure + calculateMemoryGasCost child.dyna.memory.size = frame.inner.gas := by
  obtain ⟨benv, _, hinit⟩ := Frame.enter_run_inv henter
  have hm : child.dyna.memory.size = 0 := by
    rw [hinit]
    rfl
  have hz : calculateMemoryGasCost 0 = 0 := rfl
  rw [hm, hz, Nat.add_zero]
  exact Frame.enter_run_gasMeasure henter

private theorem exec_memory_accounting :
    ∀ (pc : Nat) (sevm : Sevm) (pre : Devm) (raw : Execution),
      Exec pc sevm pre raw →
      sevm.benvStat.rules.stateGas = none →
      rawTerminalAccounted pre raw := by
  apply Exec.rec
  · intro pc sevm pre raw hstep hstate
    have hs := Evm.step_memory_accounting_output ⟨pc, sevm, pre⟩ hstate
    rw [hstep] at hs
    exact hs
  · intro pc sevm pre pc' middle raw hstep _ ih hstate
    have hs := Evm.step_memory_accounting_output ⟨pc, sevm, pre⟩ hstate
    rw [hstep] at hs
    exact raw_accounting_trans hs (ih hstate)
  · intro pc sevm pre frame resume pc' r failure hstep henter hresume hstate
    have hs := step_spawn_resume_accounting ⟨pc, sevm, pre⟩ hstate hstep r
      (fun child hchild => Frame.enter_done_gasLe henter hchild)
    rw [hresume] at hs
    exact ⟨hs.1, Or.inl hs.2⟩
  · intro pc sevm pre frame resume pc' r middle raw hstep henter hresume _ ih hstate
    have hs := step_spawn_resume_accounting ⟨pc, sevm, pre⟩ hstate hstep r
      (fun child hchild => Frame.enter_done_gasLe henter hchild)
    rw [hresume] at hs
    exact raw_accounting_trans hs (ih hstate)
  · intro pc sevm pre frame resume pc' child childRaw failure
      hstep henter _ hresume ihChild hstate
    have hc := ihChild (spawned_child_stateGas_none ⟨pc, sevm, pre⟩ hstate hstep henter)
    have hgas := raw_accounting_gas_le hc
    rw [entered_child_potential henter] at hgas
    have hsettled := Execution.settledGasLe_of_gasLe hgas
    have hs := step_spawn_resume_accounting ⟨pc, sevm, pre⟩ hstate hstep (frame.settle childRaw)
      (fun settled hsettle => Frame.settle_gasLe hsettled hsettle)
    rw [hresume] at hs
    exact ⟨hs.1, Or.inl hs.2⟩
  · intro pc sevm pre frame resume pc' child childRaw middle raw
      hstep henter _ hresume _ ihChild ihParent hstate
    have hc := ihChild (spawned_child_stateGas_none ⟨pc, sevm, pre⟩ hstate hstep henter)
    have hgas := raw_accounting_gas_le hc
    rw [entered_child_potential henter] at hgas
    have hsettled := Execution.settledGasLe_of_gasLe hgas
    have hs := step_spawn_resume_accounting ⟨pc, sevm, pre⟩ hstate hstep (frame.settle childRaw)
      (fun settled hsettle => Frame.settle_gasLe hsettled hsettle)
    rw [hresume] at hs
    exact raw_accounting_trans hs (ihParent hstate)

/-- Complete actual execution preserves the memory/gas potential, and its full
raw output is inherited or paid by that initial potential on both channels. -/
theorem Exec.memory_accounting_output
    {pc : Nat} {sevm : Sevm} {pre : Devm} {raw : Execution}
    (h : Exec pc sevm pre raw) (hstate : sevm.benvStat.rules.stateGas = none) :
    let initial := pre.gasMeasure + calculateMemoryGasCost pre.memory.size
    let accounted := fun post : Devm =>
      post.gasMeasure + calculateMemoryGasCost post.memory.size ≤ initial ∧
        (post.output = pre.output ∨ calculateMemoryGasCost post.output.length ≤ initial)
    match raw with
    | .ok post => accounted post
    | .error failure => accounted failure.2 := by
  cases raw with
  | error failure => exact exec_memory_accounting pc sevm pre (.error failure) h hstate
  | ok post => exact exec_memory_accounting pc sevm pre (.ok post) h hstate


private theorem output_length_lt_two_pow_160 {n grant : Nat}
    (hcost : calculateMemoryGasCost n ≤ grant) (hgrant : grant < 2 ^ 256) :
    n < 2 ^ 160 := by
  by_contra hn
  have hn' : 2 ^ 160 ≤ n := Nat.le_of_not_gt hn
  have hmono := calculateMemoryGasCost_mono hn'
  have hconstant : 2 ^ 256 ≤ calculateMemoryGasCost (2 ^ 160) := by decide
  omega

/-- The fixed CALL stipend is too small to fund an output of length `2^160`,
even when added to the largest word-sized requested gas grant. -/
private theorem output_length_lt_two_pow_160_with_stipend {n grant : Nat}
    (hcost : calculateMemoryGasCost n ≤ grant)
    (hgrant : grant < 2 ^ 256 + gCallStipend) :
    n < 2 ^ 160 := by
  by_contra hn
  have hn' : 2 ^ 160 ≤ n := Nat.le_of_not_gt hn
  have hmono := calculateMemoryGasCost_mono hn'
  have hconstant : 2 ^ 256 + gCallStipend ≤
      calculateMemoryGasCost (2 ^ 160) := by decide
  omega

/-- A charged CALL input window is bounded by the parent's paid memory
potential. This is the source of the identity precompile's reply bound. -/
theorem charged_call_input_length_lt_two_pow_160
    {before charged : Devm} (baseCost inputIndex inputSize outputIndex outputSize : Nat)
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hpotential : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256) :
    inputSize < 2 ^ 160 := by
  let pairs := [(inputIndex, inputSize), (outputIndex, outputSize)]
  have hacc := charged_memExtends_accounting pairs baseCost hcharge
  have hmem : inputSize ≤ (charged.memExtends pairs).memory.size := by
    by_cases hz : inputSize = 0
    · omega
    · have ha := memExtSize_access_le charged.memory.size inputIndex inputSize hz
      have hg := memExtSize_ge
        (memExtSize charged.memory.size inputIndex inputSize) outputIndex outputSize
      change inputSize ≤
        memExtSize (memExtSize charged.memory.size inputIndex inputSize)
          outputIndex outputSize
      omega
  have hmono := calculateMemoryGasCost_mono hmem
  have hcost : calculateMemoryGasCost inputSize ≤
      before.gasMeasure + calculateMemoryGasCost before.memory.size := by omega
  exact output_length_lt_two_pow_160 hcost hpotential

private theorem entered_code_output_cost {frame : Frame} {child : Evm} {raw : Execution}
    (henter : frame.enter = .run child)
    (hexec : Exec child.pc child.sta child.dyna raw)
    (hstate : child.sta.benvStat.rules.stateGas = none) :
    match raw with
    | .ok post => calculateMemoryGasCost post.output.length ≤ frame.inner.gas
    | .error failure => calculateMemoryGasCost failure.2.output.length ≤ frame.inner.gas := by
  obtain ⟨benv, _, hinit⟩ := Frame.enter_run_inv henter
  have hout : child.dyna.output = [] := by
    rw [hinit]
    rfl
  have hinitial := entered_child_potential henter
  cases raw with
  | error failure =>
      have hc := hexec.memory_accounting_output hstate
      dsimp only at hc ⊢
      rcases hc.2 with inherited | paid
      · rw [inherited, hout]
        exact Nat.zero_le _
      · rw [hinitial] at paid
        exact paid
  | ok post =>
      have hc := hexec.memory_accounting_output hstate
      dsimp only at hc ⊢
      rcases hc.2 with inherited | paid
      · rw [inherited, hout]
        exact Nat.zero_le _
      · rw [hinitial] at paid
        exact paid


private def rawOutputLength (raw : Execution) : Nat :=
  match raw with
  | .ok post => post.output.length
  | .error failure => failure.2.output.length

private theorem handled_output_length_le (stateGas : Option StateGasRules)
    (raw : Execution) {post : Devm}
    (h : executeCode.handleErrorWith stateGas raw = .ok post) :
    post.output.length ≤ rawOutputLength raw := by
  cases stateGas <;> cases raw with
  | ok pre =>
      simp only [executeCode.handleErrorWith, executeCode.handleError,
        executeCode.handleErrorAmsterdam, Except.ok.injEq] at h
      subst post
      exact Nat.le_refl _
  | error failure =>
      rcases failure with ⟨err, pre⟩
      cases err with
      | halt reason =>
          simp only [executeCode.handleErrorWith, executeCode.handleError,
            executeCode.handleErrorAmsterdam, Except.ok.injEq] at h
          subst post
          exact Nat.zero_le _
      | revert =>
          simp only [executeCode.handleErrorWith, executeCode.handleError,
            executeCode.handleErrorAmsterdam, Except.ok.injEq] at h
          subst post
          exact Nat.le_refl _
      | crypto reason | internal reason =>
          simp only [executeCode.handleErrorWith, executeCode.handleError,
            executeCode.handleErrorAmsterdam] at h
          cases h

private theorem message_settle_output {msg : Msg}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {post : Devm}
    (h : processMessage.settle msg r = .ok post) :
    ∃ pre, r = .ok pre ∧ post.output = pre.output := by
  unfold processMessage.settle at h
  obtain ⟨pre, hr, hrest⟩ := Except.bind_eq_ok h
  refine ⟨pre, hr, ?_⟩
  split at hrest <;> cases hrest <;> rfl

private theorem create_settle_output_length_le {msg : Msg}
    {r : Except (EvmError × State × AdrSet × Tra) Devm} {post : Devm}
    (h : processCreateMessage.settle msg r = .ok post) :
    ∃ pre, r = .ok pre ∧ post.output.length ≤ pre.output.length := by
  unfold processCreateMessage.settle at h
  obtain ⟨pre, hr, hrest⟩ := Except.bind_eq_ok h
  refine ⟨pre, hr, ?_⟩
  split at hrest
  · rcases hc : processCreateMessage.chargeCodeGas msg.benv.stat.rules pre with failure | paid
    · rcases failure with ⟨err, failed⟩
      cases err with
      | halt reason =>
          simp only [hc] at hrest
          cases hs : msg.benv.stat.rules.stateGas <;>
            simp only [hs, Except.ok.injEq] at hrest
          all_goals
            subst post
            exact Nat.zero_le _
      | revert | crypto reason | internal reason =>
          simp only [hc] at hrest
          cases hrest
    · simp only [hc, Except.ok.injEq] at hrest
      subst post
      rw [processCreateMessage.chargeCodeGas_ok_eq_setMach hc]
      exact Nat.le_refl _
  · cases hrest
    exact Nat.le_refl _

private theorem frame_settle_output_length_le {frame : Frame} {raw : Execution}
    {post : Devm} (h : frame.settle raw = .ok post) :
    post.output.length ≤ rawOutputLength raw := by
  unfold Frame.settle Frame.settleMsg at h
  split at h
  · obtain ⟨middle, hm, hpost⟩ := create_settle_output_length_le h
    obtain ⟨handled, hh, hmiddle⟩ := message_settle_output hm
    rw [hmiddle] at hpost
    exact Nat.le_trans hpost (handled_output_length_le _ _ hh)
  · obtain ⟨handled, hh, hpost⟩ := message_settle_output h
    rw [hpost]
    exact handled_output_length_le _ _ hh

private theorem frame_settleMsg_error (frame : Frame)
    (failure : EvmError × State × AdrSet × Tra) :
    frame.settleMsg (.error failure) = .error failure := by
  simp only [Frame.settleMsg, processMessage.settle,
    processCreateMessage.settle, bind, Except.bind]
  split <;> rfl

private theorem push_returnData (pre : Devm) (word : B256) :
    match pre.push word with
    | .error failure => failure.2.returnData = pre.returnData
    | .ok post => post.returnData = pre.returnData := by
  rw [Devm.push_def]
  by_cases hs : pre.stack.length < 1024
  · simp only [Except.assert, hs, ite_true, bind, Except.bind]
    rfl
  · simp only [Except.assert, hs, ite_false, bind, Except.bind]

private theorem call_run_returnData (parent : Devm) (outputIndex outputSize : Nat)
    (r : Except (EvmError × State × AdrSet × Tra) Devm) :
    let expected := match r with
      | .error _ => parent.returnData
      | .ok child => child.output
    match (Resume.call parent outputIndex outputSize).run r with
    | .error failure => failure.2.returnData = expected
    | .ok post => post.returnData = expected := by
  cases r with
  | error failure =>
      rcases failure with ⟨err, state, created, tra⟩
      rfl
  | ok child =>
      by_cases he : child.error.isSome = true
      · simp only [Resume.run, liftToExecution, bind, Except.bind, he, ite_true]
        let incorporated := incorporateChildOnError parent child child.output
        rcases hp : incorporated.push 0 with failure | pushed
        · have hf := push_returnData incorporated 0
          rw [hp] at hf
          exact hf
        · have hf := push_returnData incorporated 0
          rw [hp] at hf
          exact hf
      · simp only [Resume.run, liftToExecution, bind, Except.bind, he]
        let incorporated := incorporateChildOnSuccess parent child child.output
        rcases hp : incorporated.push 1 with failure | pushed
        · have hf := push_returnData incorporated 1
          rw [hp] at hf
          exact hf
        · have hf := push_returnData incorporated 1
          rw [hp] at hf
          exact hf

private theorem call_resume_returnData_lt_two_pow_160
    (parent : Devm) (outputIndex outputSize : Nat)
    (r : Except (EvmError × State × AdrSet × Tra) Devm)
    (hparent : parent.returnData = [])
    (houtput : ∀ child, r = .ok child → child.output.length < 2 ^ 160) :
    match (Resume.call parent outputIndex outputSize).run r with
    | .ok post => post.returnData.length < 2 ^ 160
    | .error failure => failure.2.returnData.length < 2 ^ 160 := by
  have hf := call_run_returnData parent outputIndex outputSize r
  cases r with
  | error err =>
    rcases hr : (Resume.call parent outputIndex outputSize).run (.error err) with failure | post
    · rw [hr] at hf
      dsimp only at hf ⊢
      rw [hf, hparent]
      decide
    · rw [hr] at hf
      dsimp only at hf ⊢
      rw [hf, hparent]
      decide
  | ok child =>
    have hl := houtput child rfl
    rcases hr : (Resume.call parent outputIndex outputSize).run (.ok child) with failure | post
    · rw [hr] at hf
      dsimp only at hf ⊢
      rw [hf]
      exact hl
    · rw [hr] at hf
      dsimp only at hf ⊢
      rw [hf]
      exact hl


/-- The same initialized code child of an actual zero-value CALL has a paid
full output and a natural reply length below (2^160). Settlement and both raw
resume outcomes retain that full return-data bound, including push failure. -/
theorem zero_call_spawn_code_reply_bound
    {sevm : Sevm} {before charged : Devm} (gas : B256)
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
    (hstate : sevm.benvStat.rules.stateGas = none) :
    let grant := (calculateMsgCallGas 0 gas.toNat before.gasLeft
      (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      extraGas cs).2
    let fullLength := (fun result : Execution => match result with
      | .ok post => post.output.length
      | .error failure => failure.2.output.length) raw
    calculateMemoryGasCost fullLength ≤ grant ∧ fullLength < 2 ^ 160 ∧
      (∀ settled, frame.settle raw = .ok settled → settled.output.length < 2 ^ 160) ∧
      let accounted := fun post : Devm =>
        post.returnData.length < 2 ^ 160 ∧
        post.gasMeasure + extraGas + calculateMemoryGasCost post.memory.size ≤
          before.gasMeasure + calculateMemoryGasCost before.memory.size ∧
        post.output = before.output
      match resume.run (frame.settle raw) with
      | .ok post => accounted post
      | .error failure => accounted failure.2 := by
  let pairs := [(inputIndex, inputSize), (outputIndex, outputSize)]
  let costs := calculateMsgCallGas 0 gas.toNat before.gasLeft (before.extCost pairs) extraGas cs
  let parent := (charged.memExtends pairs).withReturnData []
  obtain ⟨hf, hrsm⟩ := genericCall.step_spawn_call hspawn
  change frame.inner.gas = costs.2 at hf
  change resume = .call parent outputIndex outputSize at hrsm
  have hstat := genericCall.step_spawn_stat hspawn
  have hchildState : childEvm.sta.benvStat.rules.stateGas = none := by
    rw [Frame.enter_run_benvStat henter, hstat]
    exact hstate
  have hcost : calculateMemoryGasCost (rawOutputLength raw) ≤ frame.inner.gas := by
    cases raw <;> exact entered_code_output_cost henter hexec hchildState
  rw [hf] at hcost
  have hgrant : costs.2 < 2 ^ 256 :=
    calculateMsgCallGas_zero_word_child_lt gas before.gasLeft (before.extCost pairs) extraGas cs
  have hlength := output_length_lt_two_pow_160 hcost hgrant
  have hsettled : ∀ settled, frame.settle raw = .ok settled →
      settled.output.length < 2 ^ 160 := by
    intro settled hs
    exact Nat.lt_of_le_of_lt (frame_settle_output_length_le hs) hlength
  have hreturnData :
      match resume.run (frame.settle raw) with
      | .ok post => post.returnData.length < 2 ^ 160
      | .error failure => failure.2.returnData.length < 2 ^ 160 := by
    have hfields := call_run_returnData parent outputIndex outputSize (frame.settle raw)
    rw [← hrsm] at hfields
    cases hs : frame.settle raw with
    | error failure =>
        rw [hs] at hfields
        rcases hr : resume.run (.error failure) with failure | post
        · rw [hr] at hfields
          dsimp only at hfields ⊢
          rw [hfields]
          change (0 : Nat) < 2 ^ 160
          decide
        · rw [hr] at hfields
          dsimp only at hfields ⊢
          rw [hfields]
          change (0 : Nat) < 2 ^ 160
          decide
    | ok settled =>
        have hl := hsettled settled hs
        rw [hs] at hfields
        rcases hr : resume.run (.ok settled) with failure | post
        · rw [hr] at hfields
          dsimp only at hfields ⊢
          rw [hfields]
          exact hl
        · rw [hr] at hfields
          dsimp only at hfields ⊢
          rw [hfields]
          exact hl
  have haccount := zero_call_spawn_resume_raw_accounting gas extraGas cs inputIndex inputSize
    outputIndex outputSize hcharge hspawn henter hexec
  refine ⟨hcost, hlength, hsettled, ?_⟩
  rcases hr : resume.run (frame.settle raw) with failure | post
  · rw [hr] at hreturnData haccount
    exact ⟨hreturnData, haccount⟩
  · rw [hr] at hreturnData haccount
    exact ⟨hreturnData, haccount⟩

/-- An entered code child of a word-sized CALL has a bounded full output on
both raw channels, including the value-bearing stipend case. Settlement can
only shorten that output, and either parent resume channel receives bounded
return data. The recursive execution's memory potential supplies the bound;
the caller's output window is not used as a substitute for the full reply. -/
theorem call_spawn_code_reply_bound
    {sevm : Sevm} {parent : Devm} (gas value : B256)
    (gasLeft memoryCost extraGas inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume} {childEvm : Evm} {raw : Execution}
    (hspawn : genericCall.step sevm parent
      (calculateMsgCallGas value.toNat gas.toNat gasLeft memoryCost extraGas
        gCallStipend).2 value caller target codeAddress shouldTransferValue
      isStaticcall inputIndex inputSize outputIndex outputSize code
      disablePrecompiles = .spawn frame resume)
    (henter : frame.enter = .run childEvm)
    (hexec : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    (fun result : Execution => match result with
      | .ok post => post.output.length
      | .error failure => failure.2.output.length) raw < 2 ^ 160 ∧
      (∀ settled, frame.settle raw = .ok settled → settled.output.length < 2 ^ 160) ∧
      match resume.run (frame.settle raw) with
      | .ok post => post.returnData.length < 2 ^ 160
      | .error failure => failure.2.returnData.length < 2 ^ 160 := by
  have hstat := genericCall.step_spawn_stat hspawn
  have hchildState : childEvm.sta.benvStat.rules.stateGas = none := by
    rw [Frame.enter_run_benvStat henter, hstat]
    exact hstate
  have hcost : calculateMemoryGasCost (rawOutputLength raw) ≤ frame.inner.gas := by
    cases raw <;> exact entered_code_output_cost henter hexec hchildState
  have hframe := (genericCall.step_spawn_call hspawn).1
  have hgrant := calculateMsgCallGas_word_child_lt_with_stipend value gas gasLeft
    memoryCost extraGas
  have hlength : rawOutputLength raw < 2 ^ 160 := by
    apply output_length_lt_two_pow_160_with_stipend hcost
    rw [hframe]
    exact hgrant
  have hsettled : ∀ settled, frame.settle raw = .ok settled →
      settled.output.length < 2 ^ 160 := by
    intro settled hs
    exact Nat.lt_of_le_of_lt (frame_settle_output_length_le hs) hlength
  obtain ⟨_, hrsm⟩ := genericCall.step_spawn_call hspawn
  refine ⟨hlength, hsettled, ?_⟩
  rw [hrsm]
  exact call_resume_returnData_lt_two_pow_160 (parent.withReturnData [])
    outputIndex outputSize (frame.settle raw) rfl hsettled

/-- A failed value transfer never enters code or a precompile. Its actual
CALL resume inherits the empty return-data buffer installed at spawn, even
when the parent's stack push itself fails. -/
theorem call_spawn_transfer_error_reply_bound
    {sevm : Sevm} {parent : Devm} (grant : Nat) (value : B256)
    (inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume}
    {failure : EvmError × State × AdrSet × Tra}
    (hspawn : genericCall.step sevm parent grant value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn frame resume)
    (htransfer : frame.inner.benvAfterTransfer = .error failure) :
    frame.enter = .done (.error failure) ∧
      match resume.run (.error failure) with
      | .ok post => post.returnData.length < 2 ^ 160
      | .error e => e.2.returnData.length < 2 ^ 160 := by
  have hsettle := frame_settleMsg_error frame failure
  have hentry : frame.enter = .done (.error failure) := by
    simp only [Frame.enter, htransfer, hsettle]
  obtain ⟨_, hrsm⟩ := genericCall.step_spawn_call hspawn
  refine ⟨hentry, ?_⟩
  rw [hrsm]
  exact call_resume_returnData_lt_two_pow_160 (parent.withReturnData [])
    outputIndex outputSize (.error failure) rfl (by intro child hc; cases hc)

/-- A successful native MODEXP reply has at most the modulus-header width.
This uses the selected precompile execution, including its gas and length
guards; it does not assume a caller-supplied output budget. -/
theorem executeModexp_ok_output_length_le {evm : Evm} {cost : Nat} {output : Bytes}
    (h : executeModexp evm = .ok cost output) :
    output.length ≤ Bytes.sliceToNat evm.sta.data 64 32 := by
  unfold executeModexp at h
  dsimp only at h
  split at h
  · cases h
  · unfold PrecompResult.chargeGas at h
    split at h
    · split at h
      · cases h
        exact Nat.zero_le _
      · split at h
        · cases h
          simp only [List.length_replicate]
          exact Nat.le_refl _
        · cases h
          simp only [Bytes.pack, List.length_takeRightD]
          exact Nat.le_refl _
    · cases h

/-- A successful MODEXP executes the selected fork's price and passes the
actual gas guard, including when its output is empty. -/
theorem executeModexp_ok_selected_cost {evm : Evm} {cost : Nat} {output : Bytes}
    (h : executeModexp evm = .ok cost output) :
    cost = modexpGasCost evm.sta.benvStat.rules.modexp
      (Bytes.sliceToNat evm.sta.data 0 32)
      (Bytes.sliceToNat evm.sta.data 64 32)
      (Bytes.sliceToNat evm.sta.data 32 32)
      (Bytes.sliceToNat evm.sta.data
        (96 + Bytes.sliceToNat evm.sta.data 0 32)
        (min 32 (Bytes.sliceToNat evm.sta.data 32 32))) ∧
      cost ≤ evm.dyna.gasLeft := by
  unfold executeModexp at h
  dsimp only at h
  split at h
  · cases h
  · unfold PrecompResult.chargeGas at h
    split at h
    · split at h
      · cases h
        exact ⟨rfl, ‹_›⟩
      · split at h
        · cases h
          exact ⟨rfl, ‹_›⟩
        · cases h
          exact ⟨rfl, ‹_›⟩
    · cases h

/-- Expose the priced MODEXP branch through the actual precompile selector. -/
theorem executePrecomp_modexp_ok_selected_cost {evm : Evm} {post : Devm}
    (h : executePrecomp evm 5 = .ok post) :
    ∃ cost, executeModexp evm = .ok cost post.output ∧
      cost = modexpGasCost evm.sta.benvStat.rules.modexp
        (Bytes.sliceToNat evm.sta.data 0 32)
        (Bytes.sliceToNat evm.sta.data 64 32)
        (Bytes.sliceToNat evm.sta.data 32 32)
        (Bytes.sliceToNat evm.sta.data
          (96 + Bytes.sliceToNat evm.sta.data 0 32)
          (min 32 (Bytes.sliceToNat evm.sta.data 32 32))) ∧
      cost ≤ evm.dyna.gasLeft := by
  change applyPrecompResult evm (executeModexp evm) = .ok post at h
  unfold applyPrecompResult at h
  rcases hx : executeModexp evm with ⟨reason, charged⟩ | ⟨charged, bytes⟩
  · simp only [hx] at h
    cases h
  · simp only [hx, Except.ok.injEq] at h
    subst post
    rw [Devm.withOutput_output]
    exact ⟨charged, rfl, executeModexp_ok_selected_cost hx⟩

private theorem ceilDiv8_ge_pow157_of_ge_pow160 {n : Nat}
    (hn : 2 ^ 160 ≤ n) : 2 ^ 157 ≤ ceilDiv n 8 := by
  have hceil : n ≤ 8 * ceilDiv n 8 := by
    simp only [ceilDiv]
    split <;> omega
  have hp : (2 : Nat) ^ 160 = 8 * 2 ^ 157 := by decide
  omega

/-- The Prague MODEXP schedule alone rejects a modulus header this large
within any 256-bit gas grant. -/
theorem pragueModexpGasCost_large_modulus
    {baseLength modulusLength expLength expHead : Nat}
    (hmod : 2 ^ 160 ≤ modulusLength) :
    2 ^ 256 + gCallStipend ≤ modexpGasCost pragueModexpRules
      baseLength modulusLength expLength expHead := by
  let words := ceilDiv (max baseLength modulusLength) 8
  have hw : 2 ^ 157 ≤ words :=
    ceilDiv8_ge_pow157_of_ge_pow160
      (Nat.le_trans hmod (Nat.le_max_right baseLength modulusLength))
  have hsq : (2 ^ 157) ^ 2 ≤ words ^ 2 := Nat.pow_le_pow_left hw 2
  have hiter : 1 ≤ modexpIterations pragueModexpRules expLength expHead := by
    unfold modexpIterations
    exact Nat.le_max_right _ _
  have hmul : words ^ 2 ≤ words ^ 2 *
      modexpIterations pragueModexpRules expLength expHead := by
    simpa only [mul_one] using Nat.mul_le_mul_left (words ^ 2) hiter
  have hbig : 3 * (2 ^ 256 + gCallStipend) ≤ (2 ^ 157) ^ 2 := by decide
  have hcost : 2 ^ 256 + gCallStipend ≤
      (words ^ 2 * modexpIterations pragueModexpRules expLength expHead) / 3 := by
    omega
  simp only [modexpGasCost, modexpComplexity, pragueModexpRules, Nat.one_mul]
  exact Nat.le_trans hcost (Nat.le_max_right _ _)

private theorem executeModexp_ok_lengthsInBounds {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeModexp evm = .ok cost output) :
    modexpLengthsInBounds evm.sta.benvStat.rules.modexp
      (Bytes.sliceToNat evm.sta.data 0 32)
      (Bytes.sliceToNat evm.sta.data 32 32)
      (Bytes.sliceToNat evm.sta.data 64 32) = true := by
  unfold executeModexp at h
  dsimp only at h
  split at h
  · cases h
  · rename_i hguard
    exact not_not.mp hguard

private theorem osaka_modexp_modulus_le (baseLength expLength modulusLength : Nat)
    (h : modexpLengthsInBounds osakaModexpRules
      baseLength expLength modulusLength = true) :
    modulusLength ≤ 1024 := by
  simp only [modexpLengthsInBounds, osakaModexpRules] at h
  simp only [Bool.and_eq_true_eq_eq_true_and_eq_true, decide_eq_true_eq] at h
  exact h.2

private theorem initialized_modexp_rules (evm : Evm) :
    evm.sta.benvStat.rules.modexp = pragueModexpRules ∨
      evm.sta.benvStat.rules.modexp = osakaModexpRules := by
  change (Fork.ruleSet evm.sta.benvStat.fork).modexp = pragueModexpRules ∨
    (Fork.ruleSet evm.sta.benvStat.fork).modexp = osakaModexpRules
  cases evm.sta.benvStat.fork <;>
    first | exact Or.inl rfl | exact Or.inr rfl

/-- Under a word-sized gas grant, a successful initialized MODEXP reply has
the strict size needed by CALL return-data accounting on every selected fork. -/
theorem executeModexp_ok_output_length_lt_two_pow_160
    {evm : Evm} {cost : Nat} {output : Bytes}
    (h : executeModexp evm = .ok cost output)
    (hgas : evm.dyna.gasLeft < 2 ^ 256 + gCallStipend) :
    output.length < 2 ^ 160 := by
  have hlen := executeModexp_ok_output_length_le h
  have hprice := executeModexp_ok_selected_cost h
  rcases initialized_modexp_rules evm with hprague | hosaka
  · rw [hprague] at hprice
    by_contra hnot
    have hmod : 2 ^ 160 ≤ Bytes.sliceToNat evm.sta.data 64 32 := by omega
    have hlarge := pragueModexpGasCost_large_modulus
      (baseLength := Bytes.sliceToNat evm.sta.data 0 32)
      (modulusLength := Bytes.sliceToNat evm.sta.data 64 32)
      (expLength := Bytes.sliceToNat evm.sta.data 32 32)
      (expHead := Bytes.sliceToNat evm.sta.data
        (96 + Bytes.sliceToNat evm.sta.data 0 32)
        (min 32 (Bytes.sliceToNat evm.sta.data 32 32))) hmod
    omega
  · have hbound := osaka_modexp_modulus_le
      (Bytes.sliceToNat evm.sta.data 0 32)
      (Bytes.sliceToNat evm.sta.data 32 32)
      (Bytes.sliceToNat evm.sta.data 64 32) (by
        rw [← hosaka]
        exact executeModexp_ok_lengthsInBounds h)
    have hsmall : 1024 < (2 : Nat) ^ 160 := by decide
    omega

/-- The selected MODEXP precompile inherits the strict reply bound from the
actual guarded and charged native execution. -/
theorem executePrecomp_modexp_ok_output_length_lt_two_pow_160
    {evm : Evm} {post : Devm}
    (h : executePrecomp evm 5 = .ok post)
    (hgas : evm.dyna.gasLeft < 2 ^ 256 + gCallStipend) :
    post.output.length < 2 ^ 160 := by
  obtain ⟨cost, hmodexp, _, _⟩ := executePrecomp_modexp_ok_selected_cost h
  exact executeModexp_ok_output_length_lt_two_pow_160 hmodexp hgas

/-- An initialized identity reply is exactly the paid input. -/
theorem executeId_ok_output_and_cost {evm : Evm} {cost : Nat} {output : Bytes}
    (h : executeId evm = .ok cost output) :
    output = evm.sta.data ∧
      cost = 15 + 3 * ceilDiv evm.sta.data.length 32 ∧
      cost ≤ evm.dyna.gasLeft := by
  unfold executeId PrecompResult.chargeGas at h
  dsimp only at h
  split at h
  · cases h
    exact ⟨rfl, rfl, ‹_›⟩
  · cases h

/-- The selected identity precompile returns the initialized input bytes. -/
theorem executePrecomp_id_ok_output {evm : Evm} {post : Devm}
    (h : executePrecomp evm 4 = .ok post) :
    post.output = evm.sta.data := by
  change applyPrecompResult evm (executeId evm) = .ok post at h
  unfold applyPrecompResult at h
  rcases hx : executeId evm with ⟨reason, charged⟩ | ⟨charged, bytes⟩
  · simp only [hx] at h
    cases h
  · simp only [hx, Except.ok.injEq] at h
    subst post
    rw [Devm.withOutput_output]
    exact (executeId_ok_output_and_cost hx).1

/-- The real zero-value CALL grant is a word-bounded MODEXP gas reservoir;
its selected native reply therefore meets the full return-data bound. -/
theorem zero_call_spawn_modexp_reply_bound
    {sevm : Sevm} {before charged : Devm} (gas : B256)
    (extraGas cs inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume} {benv : Benv} {post : Devm}
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas 0 gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas cs).2 0 caller target codeAddress shouldTransferValue isStaticcall
      inputIndex inputSize outputIndex outputSize code disablePrecompiles =
        .spawn frame resume)
    (hmodexp : executePrecomp (initEvm (frame.inner.withBenv benv)) 5 = .ok post) :
    post.output.length < 2 ^ 160 := by
  have hf := (genericCall.step_spawn_call hspawn).1
  have hgrant := calculateMsgCallGas_zero_word_child_lt gas before.gasLeft
    (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) extraGas cs
  have hgas : (initEvm (frame.inner.withBenv benv)).dyna.gasLeft < 2 ^ 256 := by
    change frame.inner.gas < 2 ^ 256
    rw [hf]
    exact hgrant
  exact executePrecomp_modexp_ok_output_length_lt_two_pow_160 hmodexp (by omega)

/-- An identity reply from the real spawned zero-value CALL frame is bounded
by the caller's paid input memory, even if the precompile returns all input. -/
theorem zero_call_spawn_id_reply_bound
    {sevm : Sevm} {before charged : Devm}
    (baseCost gas inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume} {benv : Benv} {post : Devm}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      gas 0 caller target codeAddress shouldTransferValue isStaticcall
      inputIndex inputSize outputIndex outputSize code disablePrecompiles =
        .spawn frame resume)
    (hpotential : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256)
    (hidentity : executePrecomp (initEvm (frame.inner.withBenv benv)) 4 = .ok post) :
    post.output.length < 2 ^ 160 := by
  have hout := executePrecomp_id_ok_output hidentity
  rw [hout]
  change frame.inner.data.length < 2 ^ 160
  rw [genericCall.step_spawn_data_length hspawn]
  exact charged_call_input_length_lt_two_pow_160
    baseCost inputIndex inputSize outputIndex outputSize hcharge hpotential

private theorem bnp_serialized_length (p : BNP) : (BNP.toBytes p).length = 64 := by
  simp only [BNP.toBytes, List.length_append, Bytes.pack, List.length_takeRightD]

private theorem blsp_serialized_length (p : BLSP) : (BLSP.toBytes p).length = 128 := by
  simp only [BLSP.toBytes, List.length_append, Bytes.pack, List.length_takeRightD]

private theorem blsf2_serialized_length (x : BLSF2) : x.toBytes.length = 128 := by
  simp only [BLSF2.toBytes, List.length_append, Bytes.pack, List.length_takeRightD]

private theorem blsp2_serialized_length (p : BLSP2) : (BLSP2.toBytes p).length = 256 := by
  simp only [BLSP2.toBytes, List.length_append, blsf2_serialized_length]

private theorem executeEcadd_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeEcadd evm = .ok cost output) :
    output.length = 64 := by
  unfold executeEcadd PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact bnp_serialized_length _

private theorem executeEcmul_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeEcmul evm = .ok cost output) :
    output.length = 64 := by
  unfold executeEcmul PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact bnp_serialized_length _

private theorem executeBls12G1Add_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeBls12G1Add evm = .ok cost output) :
    output.length = 128 := by
  unfold executeBls12G1Add PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact blsp_serialized_length _

private theorem executeBls12G1Msm_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeBls12G1Msm evm = .ok cost output) :
    output.length = 128 := by
  unfold executeBls12G1Msm PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact blsp_serialized_length _

private theorem executeBls12G2Add_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeBls12G2Add evm = .ok cost output) :
    output.length = 256 := by
  unfold executeBls12G2Add PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact blsp2_serialized_length _

private theorem executeBls12G2Msm_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeBls12G2Msm evm = .ok cost output) :
    output.length = 256 := by
  unfold executeBls12G2Msm PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact blsp2_serialized_length _

private theorem executeBls12MapFpToG1_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeBls12MapFpToG1 evm = .ok cost output) :
    output.length = 128 := by
  unfold executeBls12MapFpToG1 PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact blsp_serialized_length _

private theorem executeBls12MapFp2ToG2_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeBls12MapFp2ToG2 evm = .ok cost output) :
    output.length = 256 := by
  unfold executeBls12MapFp2ToG2 PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact blsp2_serialized_length _

private theorem executeSha256_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeSha256 evm = .ok cost output) :
    output.length = 32 := by
  unfold executeSha256 PrecompResult.chargeGas at h
  dsimp only at h
  split at h
  · cases h
    exact B256.length_toBytes _
  · cases h

private theorem executeRipemd160_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeRipemd160 evm = .ok cost output) :
    output.length = 32 := by
  unfold executeRipemd160 PrecompResult.chargeGas at h
  dsimp only at h
  split at h
  · cases h
    exact B256.length_toBytes _
  · cases h

private theorem executeP256Verify_ok_output_length_le {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeP256Verify evm = .ok cost output) :
    output.length ≤ 32 := by
  unfold executeP256Verify PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals simp only [List.length_nil, B256.length_toBytes]
  all_goals omega

private theorem executeEcrecover_ok_output_length_le {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeEcrecover evm = .ok cost output) :
    output.length ≤ 32 := by
  unfold executeEcrecover PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals simp only [List.length_nil, B256.length_toBytes]
  all_goals omega

private theorem executePointEval_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executePointEval evm = .ok cost output) :
    output.length = 64 := by
  unfold executePointEval PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals simp only [List.length_append, B256.length_toBytes]

private theorem executePairingCheckInner_ok_output_length {data : Bytes}
    {charged reported : Nat} {output : Bytes}
    (h : executePairingCheckInner data charged = .ok (reported, output)) :
    output.length = 32 := by
  unfold executePairingCheckInner at h
  dsimp only at h
  repeat split at h
  all_goals try cases h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    all_goals cases h
    all_goals simp only [B256.length_toBytes]

private theorem executeBls12PairingInner_ok_output_length {data : Bytes}
    {charged reported : Nat} {output : Bytes}
    (h : executeBls12PairingInner data charged = .ok (reported, output)) :
    output.length = 32 := by
  unfold executeBls12PairingInner at h
  dsimp only at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · split at h
    all_goals cases h
    all_goals simp only [B256.length_toBytes]

private theorem executePairingCheck_ok_output_length {evm : Evm}
    {cost : Nat} {output : Bytes}
    (h : executePairingCheck evm = .ok cost output) : output.length = 32 := by
  unfold executePairingCheck PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals try cases h
  all_goals exact executePairingCheckInner_ok_output_length ‹_›

private theorem executeBls12Pairing_ok_output_length {evm : Evm}
    {cost : Nat} {output : Bytes}
    (h : executeBls12Pairing evm = .ok cost output) : output.length = 32 := by
  unfold executeBls12Pairing PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact executeBls12PairingInner_ok_output_length ‹_›

private theorem eight_byte_chunks_length (xs : List UInt64) :
    (List.flatten (xs.map fun n => (Jaune.UInt64.toBytes n).reverse.takeD 8 (0x00 : UInt8))).length =
      xs.length * 8 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append,
      List.takeD_length, ih, List.length_cons]
    omega

private theorem bCompress_ok_output_length {rounds : Nat} {h m : List UInt64}
    {t0 t1 : UInt64} {f : Bool} {output : Bytes}
    (hok : bCompress rounds h m t0 t1 f = some output) : output.length = 64 := by
  unfold bCompress at hok
  split at hok
  · split at hok
    · simp only [Option.some.injEq] at hok
      subst output
      simp only [eight_byte_chunks_length, Vector.length_toList]
    · cases hok
  · cases hok

private theorem executeBlake2F_ok_output_length {evm : Evm}
    {cost : Nat} {output : Bytes}
    (h : executeBlake2F evm = .ok cost output) : output.length = 64 := by
  unfold executeBlake2F PrecompResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact bCompress_ok_output_length ‹_›

/-- Every successful initialized native precompile has a fixed-width reply
unless it is identity or MODEXP; those two use their paid input and gas. -/
theorem precompileRun_ok_output_length_lt_two_pow_160
    {evm : Evm} {adr : Adr} {cost : Nat} {output : Bytes}
    (h : precompileRun evm adr = .ok cost output)
    (hdata : evm.sta.data.length < 2 ^ 160)
    (hgas : evm.dyna.gasLeft < 2 ^ 256 + gCallStipend) :
    output.length < 2 ^ 160 := by
  unfold precompileRun at h
  split at h
  all_goals first
    | have := executeEcrecover_ok_output_length_le h; omega
    | have := executeSha256_ok_output_length h; omega
    | have := executeRipemd160_ok_output_length h; omega
    | have hout := (executeId_ok_output_and_cost h).1; rw [hout]; exact hdata
    | exact executeModexp_ok_output_length_lt_two_pow_160 h hgas
    | have := executeEcadd_ok_output_length h; omega
    | have := executeEcmul_ok_output_length h; omega
    | have := executePairingCheck_ok_output_length h; omega
    | have := executeBlake2F_ok_output_length h; omega
    | have := executePointEval_ok_output_length h; omega
    | have := executeBls12G1Add_ok_output_length h; omega
    | have := executeBls12G1Msm_ok_output_length h; omega
    | have := executeBls12G2Add_ok_output_length h; omega
    | have := executeBls12G2Msm_ok_output_length h; omega
    | have := executeBls12Pairing_ok_output_length h; omega
    | have := executeBls12MapFpToG1_ok_output_length h; omega
    | have := executeBls12MapFp2ToG2_ok_output_length h; omega
    | have := executeP256Verify_ok_output_length_le h; omega
    | cases h

/-- An actual selected native success obeys the full return-data width once
the initialized input and gas reservoir have their physical bounds. -/
theorem executePrecomp_ok_output_length_lt_two_pow_160
    {evm : Evm} {adr : Adr} {post : Devm}
    (h : executePrecomp evm adr = .ok post)
    (hdata : evm.sta.data.length < 2 ^ 160)
    (hgas : evm.dyna.gasLeft < 2 ^ 256 + gCallStipend) :
    post.output.length < 2 ^ 160 := by
  unfold executePrecomp applyPrecompResult at h
  rcases hrun : precompileRun evm adr with ⟨reason, charged⟩ | ⟨charged, bytes⟩
  · simp only [hrun] at h
    cases h
  · simp only [hrun, Except.ok.injEq] at h
    subst post
    rw [Devm.withOutput_output]
    exact precompileRun_ok_output_length_lt_two_pow_160 hrun hdata hgas

/-- The real zero-value CALL spawn supplies both physical premises needed by
every selected native precompile, including identity and MODEXP. -/
theorem zero_call_spawn_native_reply_bound
    {sevm : Sevm} {before charged : Devm}
    (baseCost : Nat) (gas : B256)
    (extraGas cs inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume} {benv : Benv} {adr : Adr} {post : Devm}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas 0 gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas cs).2 0 caller target codeAddress shouldTransferValue isStaticcall
      inputIndex inputSize outputIndex outputSize code disablePrecompiles =
        .spawn frame resume)
    (hpotential : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256)
    (hnative : executePrecomp (initEvm (frame.inner.withBenv benv)) adr = .ok post) :
    post.output.length < 2 ^ 160 := by
  have hdata : (initEvm (frame.inner.withBenv benv)).sta.data.length < 2 ^ 160 := by
    change frame.inner.data.length < 2 ^ 160
    rw [genericCall.step_spawn_data_length hspawn]
    exact charged_call_input_length_lt_two_pow_160
      baseCost inputIndex inputSize outputIndex outputSize hcharge hpotential
  have hgas : (initEvm (frame.inner.withBenv benv)).dyna.gasLeft < 2 ^ 256 := by
    change frame.inner.gas < 2 ^ 256
    rw [(genericCall.step_spawn_call hspawn).1]
    exact calculateMsgCallGas_zero_word_child_lt gas before.gasLeft
      (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) extraGas cs
  exact executePrecomp_ok_output_length_lt_two_pow_160 hnative hdata (by omega)

/-- The executable frame entry dispatch itself preserves the native output
bound on a successful precompile branch. -/
theorem executeCode_enter_native_ok_output_length_lt_two_pow_160
    {msg : Msg} {post : Devm}
    (henter : executeCode.enter msg = .inr (.ok post))
    (hdata : msg.data.length < 2 ^ 160)
    (hgas : msg.gas < 2 ^ 256 + gCallStipend) :
    post.output.length < 2 ^ 160 := by
  unfold executeCode.enter at henter
  cases hcode : msg.codeAddress with
  | none =>
    simp only [hcode] at henter
    cases henter
  | some adr =>
    simp only [hcode] at henter
    split at henter
    · simp only [Sum.inr.injEq] at henter
      apply executePrecomp_ok_output_length_lt_two_pow_160 henter
      · exact hdata
      · exact hgas
    · cases henter

/-- A native error carries the empty initialized output through the real
dispatch, regardless of the selected precompile's rejection reason. -/
theorem executeCode_enter_native_error_output_nil
    {msg : Msg} {failure : EvmError × Devm}
    (henter : executeCode.enter msg = .inr (.error failure)) :
    failure.2.output = [] := by
  unfold executeCode.enter at henter
  cases hcode : msg.codeAddress with
  | none =>
    simp only [hcode] at henter
    cases henter
  | some adr =>
    simp only [hcode] at henter
    split at henter
    · simp only [Sum.inr.injEq] at henter
      unfold executePrecomp applyPrecompResult at henter
      rcases hrun : precompileRun (initEvm msg) adr with ⟨reason, charged⟩ | ⟨charged, bytes⟩
      · simp only [hrun, Except.error.injEq] at henter
        cases henter
        rfl
      · simp only [hrun] at henter
        cases henter
    · cases henter

/-- A successful native branch of the actual zero-value CALL frame enters as
a settled result, and its full raw reply satisfies the natural size bound. -/
theorem zero_call_spawn_native_enter_success
    {sevm : Sevm} {before charged : Devm}
    (baseCost : Nat) (gas : B256)
    (extraGas cs inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume} {benv : Benv} {post : Devm}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas 0 gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas cs).2 0 caller target codeAddress shouldTransferValue isStaticcall
      inputIndex inputSize outputIndex outputSize code disablePrecompiles =
        .spawn frame resume)
    (hpotential : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256)
    (htransfer : frame.inner.benvAfterTransfer = .ok benv)
    (hdispatch : executeCode.enter (frame.inner.withBenv benv) = .inr (.ok post)) :
    frame.enter = .done (frame.settle (.ok post)) ∧
      post.output.length < 2 ^ 160 ∧
      match resume.run (frame.settle (.ok post)) with
      | .ok resumed => resumed.returnData.length < 2 ^ 160
      | .error failure => failure.2.returnData.length < 2 ^ 160 := by
  have hdata : (frame.inner.withBenv benv).data.length < 2 ^ 160 := by
    change frame.inner.data.length < 2 ^ 160
    rw [genericCall.step_spawn_data_length hspawn]
    exact charged_call_input_length_lt_two_pow_160
      baseCost inputIndex inputSize outputIndex outputSize hcharge hpotential
  have hgas : (frame.inner.withBenv benv).gas < 2 ^ 256 := by
    change frame.inner.gas < 2 ^ 256
    rw [(genericCall.step_spawn_call hspawn).1]
    exact calculateMsgCallGas_zero_word_child_lt gas before.gasLeft
      (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) extraGas cs
  have hraw := executeCode_enter_native_ok_output_length_lt_two_pow_160
    hdispatch hdata (by omega)
  have hsettled : ∀ settled, frame.settle (.ok post) = .ok settled →
      settled.output.length < 2 ^ 160 := by
    intro settled hs
    exact Nat.lt_of_le_of_lt (frame_settle_output_length_le hs) hraw
  obtain ⟨_, hrsm⟩ := genericCall.step_spawn_call hspawn
  refine ⟨?_, hraw, ?_⟩
  · simp only [Frame.enter, htransfer, hdispatch]
  · rw [hrsm]
    exact call_resume_returnData_lt_two_pow_160
      ((charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).withReturnData [])
      outputIndex outputSize (frame.settle (.ok post)) rfl hsettled

/-- The same initialized native-success path also covers value-bearing CALL:
its bounded requested gas plus the real fixed stipend still cannot pay for a
MODEXP result of length 2^160. The charged input controls identity replies. -/
theorem call_spawn_native_enter_success
    {sevm : Sevm} {before charged : Devm}
    (baseCost : Nat) (gas value : B256)
    (extraGas inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume} {benv : Benv} {post : Devm}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas gCallStipend).2 value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn frame resume)
    (hpotential : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256)
    (htransfer : frame.inner.benvAfterTransfer = .ok benv)
    (hdispatch : executeCode.enter (frame.inner.withBenv benv) = .inr (.ok post)) :
    frame.enter = .done (frame.settle (.ok post)) ∧
      post.output.length < 2 ^ 160 ∧
      match resume.run (frame.settle (.ok post)) with
      | .ok resumed => resumed.returnData.length < 2 ^ 160
      | .error failure => failure.2.returnData.length < 2 ^ 160 := by
  have hdata : (frame.inner.withBenv benv).data.length < 2 ^ 160 := by
    change frame.inner.data.length < 2 ^ 160
    rw [genericCall.step_spawn_data_length hspawn]
    exact charged_call_input_length_lt_two_pow_160
      baseCost inputIndex inputSize outputIndex outputSize hcharge hpotential
  have hgas : (frame.inner.withBenv benv).gas < 2 ^ 256 + gCallStipend := by
    change frame.inner.gas < 2 ^ 256 + gCallStipend
    rw [(genericCall.step_spawn_call hspawn).1]
    exact calculateMsgCallGas_word_child_lt_with_stipend value gas before.gasLeft
      (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) extraGas
  have hraw := executeCode_enter_native_ok_output_length_lt_two_pow_160
    hdispatch hdata hgas
  have hsettled : ∀ settled, frame.settle (.ok post) = .ok settled →
      settled.output.length < 2 ^ 160 := by
    intro settled hs
    exact Nat.lt_of_le_of_lt (frame_settle_output_length_le hs) hraw
  obtain ⟨_, hrsm⟩ := genericCall.step_spawn_call hspawn
  refine ⟨?_, hraw, ?_⟩
  · simp only [Frame.enter, htransfer, hdispatch]
  · rw [hrsm]
    exact call_resume_returnData_lt_two_pow_160
      ((charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).withReturnData [])
      outputIndex outputSize (frame.settle (.ok post)) rfl hsettled

/-- A rejected native precompile starts with empty output. Even when its
settlement fails or the parent's stack push fails, CALL return data stays
strictly below the natural width. This clause also covers nonzero-value CALL. -/
theorem call_spawn_native_enter_error
    {sevm : Sevm} {parent : Devm} (grant : Nat) (value : B256)
    (inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume} {benv : Benv}
    {failure : EvmError × Devm}
    (hspawn : genericCall.step sevm parent grant value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn frame resume)
    (htransfer : frame.inner.benvAfterTransfer = .ok benv)
    (hdispatch : executeCode.enter (frame.inner.withBenv benv) =
      .inr (.error failure)) :
    frame.enter = .done (frame.settle (.error failure)) ∧
      match resume.run (frame.settle (.error failure)) with
      | .ok resumed => resumed.returnData.length < 2 ^ 160
      | .error e => e.2.returnData.length < 2 ^ 160 := by
  have hraw := executeCode_enter_native_error_output_nil hdispatch
  have hsettled : ∀ settled, frame.settle (.error failure) = .ok settled →
      settled.output.length < 2 ^ 160 := by
    intro settled hs
    have hle := frame_settle_output_length_le hs
    change settled.output.length ≤ failure.2.output.length at hle
    rw [hraw] at hle
    simp only [List.length_nil] at hle
    omega
  obtain ⟨_, hrsm⟩ := genericCall.step_spawn_call hspawn
  constructor
  · simp only [Frame.enter, htransfer, hdispatch]
  · rw [hrsm]
    exact call_resume_returnData_lt_two_pow_160 (parent.withReturnData [])
      outputIndex outputSize (frame.settle (.error failure)) rfl hsettled

/-- Every actual value-bearing or zero-value word-sized CALL spawn has a
bounded parent return-data result. This combines failed value transfer,
ordinary code execution, and successful or rejected native precompiles,
including errors and both resume outcomes. The code branch quantifies over
its actual recursive execution instead of assuming an output premise. -/
theorem call_spawn_enter_reply_bound
    {sevm : Sevm} {before charged : Devm}
    (baseCost : Nat) (gas value : B256)
    (extraGas inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {frame : Frame} {resume : Resume}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas gCallStipend).2 value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn frame resume)
    (hpotential : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    match frame.enter with
    | .run child =>
        ∀ raw : Execution, Exec child.pc child.sta child.dyna raw →
          match resume.run (frame.settle raw) with
          | .ok post => post.returnData.length < 2 ^ 160
          | .error failure => failure.2.returnData.length < 2 ^ 160
    | .done settled =>
        match resume.run settled with
        | .ok post => post.returnData.length < 2 ^ 160
        | .error failure => failure.2.returnData.length < 2 ^ 160 := by
  cases ht : frame.inner.benvAfterTransfer with
  | error transferFailure =>
      have hf := call_spawn_transfer_error_reply_bound
        (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
          (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
          extraGas gCallStipend).2 value inputIndex inputSize outputIndex outputSize
        hspawn ht
      rw [hf.1]
      exact hf.2
  | ok benv =>
      cases hd : executeCode.enter (frame.inner.withBenv benv) with
      | inl child =>
          have he : frame.enter = .run child := by
            simp only [Frame.enter, ht, hd]
          rw [he]
          intro raw hexec
          exact (call_spawn_code_reply_bound gas value before.gasLeft
            (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
            extraGas inputIndex inputSize outputIndex outputSize
            hspawn he hexec hstate).2.2
      | inr result =>
          cases result with
          | ok post =>
              have hf := call_spawn_native_enter_success baseCost gas value extraGas
                inputIndex inputSize outputIndex outputSize hcharge hspawn
                hpotential ht hd
              rw [hf.1]
              exact hf.2.2
          | error failure =>
              have hf := call_spawn_native_enter_error
                (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
                  (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
                  extraGas gCallStipend).2 value inputIndex inputSize outputIndex
                outputSize hspawn ht hd
              rw [hf.1]
              exact hf.2

private def callStepReplyBound (step : XStep) : Prop :=
  ∀ (xl : Xlot) (post : Devm), xl.Filled → XStep.Run step xl (.ok post) →
    post.returnData.length < 2 ^ 160

private theorem callStepReplyBound_bind {α : Type} {pre : Devm}
    {first : Except (EvmError × Devm) α}
    {next : α → Except (EvmError × Devm) XStep} {project : α → Devm}
    (hf : nonspawnResult pre project first)
    (hn : ∀ value,
      (project value).gasMeasure + calculateMemoryGasCost (project value).memory.size < 2 ^ 256 →
      callStepReplyBound (XStep.ofExcept (next value)))
    (hpotential : pre.gasMeasure + calculateMemoryGasCost pre.memory.size < 2 ^ 256) :
    callStepReplyBound (XStep.ofExcept (first >>= next)) := by
  cases first with
  | error failure =>
      intro xl post hfilled hrun
      cases hrun.2
  | ok value => exact hn value (Nat.lt_of_le_of_lt hf.1 hpotential)

private theorem charged_genericCall_reply_bound
    {sevm : Sevm} {before charged : Devm}
    (baseCost : Nat) (gas value : B256)
    (extraGas inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Adr} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hpotential : before.gasMeasure + calculateMemoryGasCost before.memory.size < 2 ^ 256)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    callStepReplyBound (genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas gCallStipend).2 value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles) := by
  let paid := charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]
  let grant := (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
    (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
    extraGas gCallStipend).2
  intro xl post hfilled hrun
  by_cases depth : sevm.depth = 0
  · simp only [genericCall.step, depth, ite_true] at hrun
    let refunded := (paid.withReturnData []).withGasLeft (paid.gasLeft + grant)
    cases hp : refunded.push 0 with
    | error failure =>
        change XStep.Run (XStep.ofExcept (refunded.push 0 >>= _)) xl (.ok post) at hrun
        simp only [hp, bind, Except.bind, XStep.ofExcept, XStep.Run] at hrun
        cases hrun.2
    | ok pushed =>
        change XStep.Run (XStep.ofExcept (refunded.push 0 >>= _)) xl (.ok post) at hrun
        simp only [hp, bind, Except.bind, Pure.pure, Except.pure,
          XStep.ofExcept, XStep.Run] at hrun
        cases hrun.2
        have fields := push_returnData refunded 0
        rw [hp] at fields
        rw [fields]
        change (0 : Nat) < 2 ^ 160
        decide
  · have spawn : genericCall.step sevm paid grant value caller target codeAddress
        shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
        code disablePrecompiles =
        .spawn (Frame.ofCall (callMsg sevm (paid.withReturnData []) grant value caller
          target codeAddress shouldTransferValue isStaticcall
          (Jaune.Array.sliceD (paid.withReturnData []).memory.data inputIndex inputSize 0)
          code disablePrecompiles)) (.call (paid.withReturnData []) outputIndex outputSize) := by
      simp only [genericCall.step, ite_eq_right depth]
    have bounded := call_spawn_enter_reply_bound baseCost gas value extraGas
      inputIndex inputSize outputIndex outputSize hcharge spawn hpotential hstate
    rw [spawn] at hrun
    obtain ⟨settled, frameRun, resumed⟩ := hrun
    cases enter : (Frame.ofCall (callMsg sevm (paid.withReturnData []) grant value caller
        target codeAddress shouldTransferValue isStaticcall
        (Jaune.Array.sliceD (paid.withReturnData []).memory.data inputIndex inputSize 0)
        code disablePrecompiles)).enter with
    | done result =>
        simp only [RunFrame, enter] at frameRun
        rw [enter] at bounded
        dsimp only at bounded
        rw [frameRun.2] at resumed
        rw [← resumed] at bounded
        exact bounded
    | run child =>
        simp only [RunFrame, enter] at frameRun
        obtain ⟨raw, slot, result⟩ := frameRun
        rw [slot] at hfilled
        obtain ⟨execution⟩ := hfilled
        rw [enter] at bounded
        have output := bounded raw execution
        rw [result] at resumed
        rw [← resumed] at output
        exact output

private theorem xinst_call_reply_bound (sevm : Sevm) (pre : Devm)
    (hstate : sevm.benvStat.rules.stateGas = none)
    (hpotential : pre.gasMeasure + calculateMemoryGasCost pre.memory.size < 2 ^ 256) :
    callStepReplyBound (Xinst.step sevm pre .call) := by
  simp only [Xinst.step, hstate]
  refine callStepReplyBound_bind (nonspawn_pop pre) ?_ hpotential
  intro gas gasPotential
  refine callStepReplyBound_bind (nonspawn_popToAdr gas.2) ?_ gasPotential
  intro callee calleePotential
  refine callStepReplyBound_bind (nonspawn_pop callee.2) ?_ calleePotential
  intro value valuePotential
  refine callStepReplyBound_bind (nonspawn_popToNat value.2) ?_ valuePotential
  intro inputIndex inputIndexPotential
  refine callStepReplyBound_bind (nonspawn_popToNat inputIndex.2) ?_ inputIndexPotential
  intro inputSize inputSizePotential
  refine callStepReplyBound_bind (nonspawn_popToNat inputSize.2) ?_ inputSizePotential
  intro outputIndex outputIndexPotential
  refine callStepReplyBound_bind (nonspawn_popToNat outputIndex.2) ?_ outputIndexPotential
  intro outputSize outputSizePotential
  let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
  let lookup := sevm.benvStat.rules.gas.accessDelegation
    (addAccessedAddress outputSize.2 callee.1) callee.1
  let parent := lookup.2.2.2.2
  have preserved : nonspawnPreserved outputSize.2 parent :=
    nonspawnPreserved_trans (nonspawn_addAccessedAddress outputSize.2 callee.1)
      (nonspawn_delegation sevm.benvStat.rules.gas _ callee.1)
  have parentPotential : parent.gasMeasure + calculateMemoryGasCost parent.memory.size < 2 ^ 256 :=
    Nat.lt_of_le_of_lt preserved.1 outputSizePotential
  have memory : parent.memory = outputSize.2.memory :=
    (delegation_memory_output sevm.benvStat.rules.gas
      (addAccessedAddress outputSize.2 callee.1) callee.1).1
  have extension : outputSize.2.extCost pairs = parent.extCost pairs := by
    simp only [Devm.extCost, memory]
  let accessCost := sevm.benvStat.rules.gas.accessCost callee.1
    outputSize.2.accessedAddresses + lookup.2.2.2.1
  let createCost : Nat := if ¬(parent.getAcct callee.1).Empty ∨ value.1 = 0 then 0 else gNewAccount
  let extraGas := accessCost + createCost + if value.1 = 0 then 0 else sevm.benvStat.rules.gas.callValue
  change callStepReplyBound (XStep.ofExcept (chargeGas
    ((calculateMsgCallGas value.1.toNat gas.1.toNat parent.gasLeft
      (outputSize.2.extCost pairs) extraGas).1 + outputSize.2.extCost pairs) parent >>= _))
  rw [extension]
  let costs := calculateMsgCallGas value.1.toNat gas.1.toNat parent.gasLeft
    (parent.extCost pairs) extraGas
  cases charge : chargeGas (costs.1 + parent.extCost pairs) parent with
  | error failure =>
      simp only [bind, Except.bind, XStep.ofExcept]
      intro xl post hfilled hrun
      cases hrun.2
  | ok charged =>
      simp only [bind, Except.bind]
      by_cases static : (!sevm.isStatic) = true ∨ value.1 = 0
      · simp only [Except.assert, ite_eq_left static]
        let paid := charged.memExtends pairs
        by_cases balance : (paid.getAcct sevm.currentTarget).bal < value.1
        · dsimp only [paid, pairs] at balance
          simp only [ite_eq_left balance]
          intro xl post hfilled hrun
          change XStep.Run (XStep.ofExcept (paid.push 0 >>= _)) xl (.ok post) at hrun
          cases pushed : paid.push 0 with
          | error failure =>
              simp only [pushed, bind, Except.bind, XStep.ofExcept, XStep.Run] at hrun
              cases hrun.2
          | ok next =>
              simp only [pushed, bind, Except.bind, Pure.pure, Except.pure,
                XStep.ofExcept, XStep.Run] at hrun
              cases hrun.2
              change (0 : Nat) < 2 ^ 160
              decide
        · dsimp only [paid, pairs] at balance
          simp only [ite_eq_right balance, Pure.pure, Except.pure, XStep.ofExcept]
          exact charged_genericCall_reply_bound costs.1 gas.1 value.1 extraGas
            inputIndex.1 inputSize.1 outputIndex.1 outputSize.1 charge parentPotential hstate
      · simp only [Except.assert, ite_eq_right static, XStep.ofExcept]
        intro xl post hfilled hrun
        cases hrun.2

/-- A real successful legacy CALL instruction installs full returndata below
`2^160`. The filled slot supplies actual recursive child execution; no callee
output-size premise or output-copy-window bound is assumed. -/
theorem call_step_returnData_length_lt_two_pow_160
    {pc : Nat} {sevm : Sevm} {pre post : Devm} {xl : Xlot}
    (hfilled : xl.Filled)
    (hrun : Ninst.StepRun pc sevm pre (.exec .call) xl (.ok post))
    (hstate : sevm.benvStat.rules.stateGas = none)
    (hpotential : pre.gasMeasure + calculateMemoryGasCost pre.memory.size < 2 ^ 256) :
    post.returnData.length < 2 ^ 160 := by
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at hrun
  exact xinst_call_reply_bound sevm pre hstate hpotential xl post hfilled hrun

/-- The instruction-run interface retains the same strong full-reply bound. -/
theorem call_returnData_length_lt_two_pow_160
    {sevm : Sevm} {pre post : Devm}
    (hrun : Ninst.Run sevm pre (.exec .call) post)
    (hstate : sevm.benvStat.rules.stateGas = none)
    (hpotential : pre.gasMeasure + calculateMemoryGasCost pre.memory.size < 2 ^ 256) :
    post.returnData.length < 2 ^ 160 := by
  obtain ⟨xl, filled, pc, step⟩ := hrun
  exact call_step_returnData_length_lt_two_pow_160 filled step hstate hpotential

end Jaune
