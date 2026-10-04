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

end Jaune
