import Jaune.Exec
import Jaune.Memory

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

theorem calculateMsgCallGas_zero_word_child_lt (gas : U256)
    (gasLeft memoryCost extraGas cs : Nat) :
    (calculateMsgCallGas 0 gas.toNat gasLeft memoryCost extraGas cs).2 < 2 ^ 256 :=
  Nat.lt_of_le_of_lt
    (calculateMsgCallGas_zero_child_le gas.toNat gasLeft memoryCost extraGas cs)
    (U256.toNat_lt gas)

/-- The CALL stipend adds at most its fixed amount to a word-sized requested
grant, including the underfunded branch of the gas calculator. -/
theorem calculateMsgCallGas_word_child_lt_with_stipend (value gas : U256)
    (gasLeft memoryCost extraGas : Nat) :
    (calculateMsgCallGas value.toNat gas.toNat gasLeft memoryCost extraGas
      Gas.callStipend).2 < 2 ^ 256 + Gas.callStipend := by
  have hg := U256.toNat_lt gas
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

theorem calculateMemoryGasCost_mono {a b : Nat} (h : a ≤ b) :
    calculateMemoryGasCost a ≤ calculateMemoryGasCost b := by
  have hw := ceilDiv32_le h
  have hq := Nat.div_le_div_right (c := 512) (Nat.pow_le_pow_left hw 2)
  simp only [calculateMemoryGasCost, Gas.memory]
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

theorem Devm.push_memory {word : U256} {before after : Devm}
    (h : before.push word = .ok after) : after.memory = before.memory := by
  rw [Devm.push_def] at h
  by_cases hs : before.stack.length < 1024
  · simp only [Except.assert, ite_eq_left hs, bind, Except.bind, Except.ok.injEq] at h
    subst after
    rfl
  · simp only [Except.assert, ite_eq_right hs, bind, Except.bind] at h
    contradiction

theorem calculateMsgCallGas_zero_value_cost (gas gasLeft memoryCost extraGas cs : Nat) :
    (calculateMsgCallGas 0 gas gasLeft memoryCost extraGas cs).1 =
      (calculateMsgCallGas 0 gas gasLeft memoryCost extraGas cs).2 + extraGas := by
  simp only [calculateMsgCallGas]
  split <;> rfl

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
theorem HaltOp.run_memory_accounting_output (sevm : Sevm) (pre : Devm) (l : HaltOp)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    let initial := pre.gasMeasure + calculateMemoryGasCost pre.memory.size
    let accounted := fun post : Devm =>
      post.gasMeasure + calculateMemoryGasCost post.memory.size ≤ initial ∧
        (post.output = pre.output ∨
          calculateMemoryGasCost post.output.length ≤ initial)
    match HaltOp.run sevm pre l with
    | .ok post => accounted post
    | .error failure => accounted failure.2 := by
  have hgas := HaltOp.run_gasLe sevm pre l
  cases l with
  | stop => exact ⟨Nat.le_refl _, Or.inl rfl⟩
  | return_ | revert =>
      simp only [HaltOp.run, Devm.popToNat_def, Bind.bind, Except.bind,
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
          HaltOp.run sevm pre .selfdestruct = result →
            (match result with
            | .ok post => post.memory = pre.memory ∧ post.output = pre.output
            | .error failure => failure.2.memory = pre.memory ∧ failure.2.output = pre.output) := by
        intro result hrun
        clear hgas
        cases hs : pre.stack
        all_goals
          simp only [HaltOp.run, hstate, Devm.popToAdr_def, Devm.pop_def, hs,
            Bind.bind, Except.bind, Functor.mapRev, Functor.map, Except.map,
            Prod.mapFst, Prod.map, id_eq] at hrun
        · cases hrun
          exact ⟨rfl, rfl⟩
        · rename_i head tail
          let popped := pre.setMach {pre.mach with stack := tail}
          let read := (popped.balReadAccount sevm.benvStat.rules head.toAddress).balReadAccount
            sevm.benvStat.rules sevm.currentTarget
          let donorBal := (read.getAcct sevm.currentTarget).balance
          -- The access shape decides the plan: EIP-2929 warms a cold
          -- beneficiary and charges its surcharge; the flat schedule charges the
          -- base alone and leaves the set untouched. The rest is shape-blind.
          rcases hA : sevm.benvStat.rules.access with g | _ <;> rw [hA] at hrun
          on_goal 1 =>
            let plan : Devm × Nat := (read, Gas.selfdestruct)
            have hw : plan.1.memory = pre.memory ∧ plan.1.output = pre.output := by
              constructor
              all_goals
                dsimp only [plan, read, popped, Devm.balReadAccount]
                repeat' first | rfl | split
            have hplan : plan = (read, Gas.selfdestruct) := rfl
          on_goal 2 =>
            let plan : Devm × Nat :=
              if head.toAddress ∉ read.accessedAddresses then
                (addAccessedAddress read head.toAddress,
                  Gas.selfdestruct + sevm.benvStat.rules.gas.coldAccountAccess)
              else (read, Gas.selfdestruct)
            have hw : plan.1.memory = pre.memory ∧ plan.1.output = pre.output := by
              dsimp only [plan]
              split <;> constructor
              all_goals
                dsimp only [read, popped, Devm.balReadAccount]
                repeat' first | rfl | split
            have hplan : plan = (if head.toAddress ∉ read.accessedAddresses then
                (addAccessedAddress read head.toAddress,
                  Gas.selfdestruct + sevm.benvStat.rules.gas.coldAccountAccess)
                else (read, Gas.selfdestruct)) := rfl
          all_goals
            let cost := if (plan.1.getAcct head.toAddress).isEmpty ∧ donorBal ≠ 0 then
                plan.2 + Gas.selfdestructNewAccount else plan.2
            -- Fold `hrun` through the `let`s before restating it: the unfolded
            -- account reads repeat a dozen times in its type. `change` against
            -- that form elaborates the tail into the match type and thrashes;
            -- folding first and restating with `replace` keeps both sides small.
            -- (Heartbeat edge: this is the slowest defeq in the file; keep the
            -- tail and these equations in sync.)
            have hpopped : popped = pre.setMach { pre.mach with stack := tail } :=
              rfl
            have hread : read = (popped.balReadAccount sevm.benvStat.rules
              head.toAddress).balReadAccount sevm.benvStat.rules
              sevm.currentTarget := rfl
            have hdonorBal : donorBal = (read.getAcct sevm.currentTarget).balance :=
              rfl
            have hcost : cost = (if (plan.1.getAcct head.toAddress).isEmpty ∧
                donorBal ≠ 0 then plan.2 + Gas.selfdestructNewAccount
                else plan.2) := rfl
            simp only [← hpopped, ← hread, ← hdonorBal, ← hplan, ← hcost] at hrun
            replace hrun : (do
              let charged ← chargeGas cost plan.1
              assertDynamic sevm charged
              let next ← Option.toExcept
                (.internal (.invariant (.text "InsufficientBalanceError")), charged)
                (charged.subBal sevm.currentTarget donorBal)
              let next := next.creditBeneficiary sevm.benvStat.rules head.toAddress donorBal
              if sevm.currentTarget ∈ next.createdAccounts ∨
                  sevm.benvStat.rules.settlement.selfdestructOnlyCreated = false then
                .ok (creditSelfdestructRefund sevm.benvStat.rules
                  (sevm.currentTarget ∈ next.accountsToDelete)
                  (addAccountToDelete (next.setBal sevm.currentTarget 0)
                    sevm.currentTarget))
              else .ok next) = result := hrun
            -- The remaining argument depends only on the preserved fields, not
            -- on the account reads and access-cost calculation defining them.
            clear_value cost plan donorBal read popped
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
                  split at hrun
                  · cases hrun
                    dsimp only
                    simp only [creditSelfdestructRefund_memory,
                      creditSelfdestructRefund_output]
                    exact ⟨(Devm.creditBeneficiary_memory _ _ _ _).trans hcharged.1,
                      (Devm.creditBeneficiary_output _ _ _ _).trans hcharged.2⟩
                  · cases hrun
                    exact ⟨(Devm.creditBeneficiary_memory _ _ _ _).trans hcharged.1,
                      (Devm.creditBeneficiary_output _ _ _ _).trans hcharged.2⟩
              · simp only [assertDynamic, Except.assert, hd] at hrun
                cases hrun
                exact hcharged
      rcases hx : HaltOp.run sevm pre .selfdestruct with failure | post
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

private theorem output_length_lt_two_pow_160 {n grant : Nat}
    (hcost : calculateMemoryGasCost n ≤ grant) (hgrant : grant < 2 ^ 256) :
    n < 2 ^ 160 := by
  by_contra hn
  have hn' : 2 ^ 160 ≤ n := Nat.le_of_not_gt hn
  have hmono := calculateMemoryGasCost_mono hn'
  have hconstant : 2 ^ 256 ≤ calculateMemoryGasCost (2 ^ 160) := by decide
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
  · unfold PrecompileResult.chargeGas at h
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
    cost = modexpGasCost evm.sta.benvStat.rules.modexpComplexity
      evm.sta.benvStat.rules.modexp
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
  · unfold PrecompileResult.chargeGas at h
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
theorem executePrecompile_modexp_ok_selected_cost {evm : Evm} {post : Devm}
    (h : executePrecompile evm 5 = .ok post) :
    ∃ cost, executeModexp evm = .ok cost post.output ∧
      cost = modexpGasCost evm.sta.benvStat.rules.modexpComplexity
        evm.sta.benvStat.rules.modexp
        (Bytes.sliceToNat evm.sta.data 0 32)
        (Bytes.sliceToNat evm.sta.data 64 32)
        (Bytes.sliceToNat evm.sta.data 32 32)
        (Bytes.sliceToNat evm.sta.data
          (96 + Bytes.sliceToNat evm.sta.data 0 32)
          (min 32 (Bytes.sliceToNat evm.sta.data 32 32))) ∧
      cost ≤ evm.dyna.gasLeft := by
  change applyPrecompileResult evm (executeModexp evm) = .ok post at h
  unfold applyPrecompileResult at h
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
    2 ^ 256 + Gas.callStipend ≤ modexpGasCost .eip2565 pragueModexpRules
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
  have hbig : 3 * (2 ^ 256 + Gas.callStipend) ≤ (2 ^ 157) ^ 2 := by decide
  have hcost : 2 ^ 256 + Gas.callStipend ≤
      (words ^ 2 * modexpIterations pragueModexpRules expLength expHead) / 3 := by
    omega
  simp only [modexpGasCost, modexpComplexity, pragueModexpRules, Nat.one_mul]
  exact Nat.le_trans hcost (Nat.le_max_right _ _)

/-- Above 1024 bytes EIP-198 charges its third branch. -/
private theorem eip198Complexity_third
    {baseLength modulusLength : Nat}
    (h : 1024 < max baseLength modulusLength) :
    eip198Complexity baseLength modulusLength =
      (max baseLength modulusLength) ^ 2 / 16 +
        480 * (max baseLength modulusLength) - 199680 := by
  have h64 : ¬ max baseLength modulusLength ≤ 64 := by omega
  have h1024 : ¬ max baseLength modulusLength ≤ 1024 := by omega
  simp only [eip198Complexity, h64, h1024, ite_false]

/-- EIP-198's third branch alone prices a 2^160-byte modulus past any 256-bit
gas grant at divisor 20: `x ^ 2 / 16` at `x = 2 ^ 160` is already `2 ^ 316`. -/
private theorem eip198Complexity_third_large
    {baseLength modulusLength : Nat}
    (hmod : 2 ^ 160 ≤ modulusLength) :
    20 * (2 ^ 256 + Gas.callStipend) ≤
      eip198Complexity baseLength modulusLength := by
  have hX : 2 ^ 160 ≤ max baseLength modulusLength :=
    Nat.le_trans hmod (Nat.le_max_right baseLength modulusLength)
  have h1024 : 1024 < max baseLength modulusLength := by
    calc (1024 : Nat) < 2 ^ 160 := by decide
    _ ≤ max baseLength modulusLength := hX
  rw [eip198Complexity_third h1024]
  have h157 : (2 ^ 157) ^ 2 ≤ (2 ^ 160) ^ 2 := by decide
  have hsq : (2 ^ 157) ^ 2 ≤ (max baseLength modulusLength) ^ 2 :=
    Nat.le_trans h157 (Nat.pow_le_pow_left hX 2)
  have hdiv : (2 ^ 157) ^ 2 / 16 ≤ (max baseLength modulusLength) ^ 2 / 16 :=
    Nat.div_le_div_right hsq
  have hmul : 480 * 2 ^ 160 ≤ 480 * max baseLength modulusLength :=
    Nat.mul_le_mul_left 480 hX
  have hbig : 20 * (2 ^ 256 + Gas.callStipend) ≤
      (2 ^ 157) ^ 2 / 16 + 480 * 2 ^ 160 - 199680 := by decide
  have hle : (2 ^ 157) ^ 2 / 16 + 480 * 2 ^ 160 - 199680 ≤
      (max baseLength modulusLength) ^ 2 / 16 +
        480 * (max baseLength modulusLength) - 199680 :=
    Nat.sub_le_sub_right (Nat.add_le_add hdiv hmul) 199680
  exact Nat.le_trans hbig hle

/-- The EIP-198 MODEXP schedule alone rejects a modulus header this large
within any 256-bit gas grant: the divisor is 20 rather than 3, but a
2^160-byte modulus still costs far past it. -/
theorem eip198ModexpGasCost_large_modulus
    {baseLength modulusLength expLength expHead : Nat}
    (hmod : 2 ^ 160 ≤ modulusLength) :
    2 ^ 256 + Gas.callStipend ≤ modexpGasCost .eip198 eip198ModexpRules
      baseLength modulusLength expLength expHead := by
  have hiter : 1 ≤ modexpIterations eip198ModexpRules expLength expHead := by
    unfold modexpIterations
    exact Nat.le_max_right _ _
  have hbig := eip198Complexity_third_large (baseLength := baseLength) hmod
  have hmul : eip198Complexity baseLength modulusLength ≤
      eip198Complexity baseLength modulusLength *
        modexpIterations eip198ModexpRules expLength expHead := by
    simpa only [mul_one] using Nat.mul_le_mul_left _ hiter
  have hcost : 2 ^ 256 + Gas.callStipend ≤
      (eip198Complexity baseLength modulusLength *
        modexpIterations eip198ModexpRules expLength expHead) / 20 := by
    omega
  simp only [modexpGasCost, modexpComplexity, eip198ModexpRules]
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
    (evm.sta.benvStat.rules.modexpComplexity = .eip2565 ∧
      evm.sta.benvStat.rules.modexp = pragueModexpRules) ∨
    (evm.sta.benvStat.rules.modexpComplexity = .eip2565 ∧
      evm.sta.benvStat.rules.modexp = osakaModexpRules) ∨
    (evm.sta.benvStat.rules.modexpComplexity = .eip198 ∧
      evm.sta.benvStat.rules.modexp = eip198ModexpRules) := by
  change ((Fork.ruleSet evm.sta.benvStat.fork).modexpComplexity = .eip2565 ∧
      (Fork.ruleSet evm.sta.benvStat.fork).modexp = pragueModexpRules) ∨
    ((Fork.ruleSet evm.sta.benvStat.fork).modexpComplexity = .eip2565 ∧
      (Fork.ruleSet evm.sta.benvStat.fork).modexp = osakaModexpRules) ∨
    ((Fork.ruleSet evm.sta.benvStat.fork).modexpComplexity = .eip198 ∧
      (Fork.ruleSet evm.sta.benvStat.fork).modexp = eip198ModexpRules)
  cases evm.sta.benvStat.fork <;>
    first | exact Or.inl ⟨rfl, rfl⟩ | exact Or.inr (Or.inl ⟨rfl, rfl⟩) |
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- Under a word-sized gas grant, a successful initialized MODEXP reply has
the strict size needed by CALL return-data accounting on every selected fork. -/
theorem executeModexp_ok_output_length_lt_two_pow_160
    {evm : Evm} {cost : Nat} {output : Bytes}
    (h : executeModexp evm = .ok cost output)
    (hgas : evm.dyna.gasLeft < 2 ^ 256 + Gas.callStipend) :
    output.length < 2 ^ 160 := by
  have hlen := executeModexp_ok_output_length_le h
  have hprice := executeModexp_ok_selected_cost h
  rcases initialized_modexp_rules evm with ⟨hc, hm⟩ | ⟨hc, hm⟩ | ⟨hc, hm⟩
  · rw [hc, hm] at hprice
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
        rw [← hm]
        exact executeModexp_ok_lengthsInBounds h)
    have hsmall : 1024 < (2 : Nat) ^ 160 := by decide
    omega
  · rw [hc, hm] at hprice
    by_contra hnot
    have hmod : 2 ^ 160 ≤ Bytes.sliceToNat evm.sta.data 64 32 := by omega
    have hlarge := eip198ModexpGasCost_large_modulus
      (baseLength := Bytes.sliceToNat evm.sta.data 0 32)
      (modulusLength := Bytes.sliceToNat evm.sta.data 64 32)
      (expLength := Bytes.sliceToNat evm.sta.data 32 32)
      (expHead := Bytes.sliceToNat evm.sta.data
        (96 + Bytes.sliceToNat evm.sta.data 0 32)
        (min 32 (Bytes.sliceToNat evm.sta.data 32 32))) hmod
    omega

/-- The selected MODEXP precompile inherits the strict reply bound from the
actual guarded and charged native execution. -/
theorem executePrecompile_modexp_ok_output_length_lt_two_pow_160
    {evm : Evm} {post : Devm}
    (h : executePrecompile evm 5 = .ok post)
    (hgas : evm.dyna.gasLeft < 2 ^ 256 + Gas.callStipend) :
    post.output.length < 2 ^ 160 := by
  obtain ⟨cost, hmodexp, _, _⟩ := executePrecompile_modexp_ok_selected_cost h
  exact executeModexp_ok_output_length_lt_two_pow_160 hmodexp hgas

/-- An initialized identity reply is exactly the paid input. -/
theorem executeId_ok_output_and_cost {evm : Evm} {cost : Nat} {output : Bytes}
    (h : executeId evm = .ok cost output) :
    output = evm.sta.data ∧
      cost = 15 + 3 * ceilDiv evm.sta.data.length 32 ∧
      cost ≤ evm.dyna.gasLeft := by
  unfold executeId PrecompileResult.chargeGas at h
  dsimp only at h
  split at h
  · cases h
    exact ⟨rfl, rfl, ‹_›⟩
  · cases h

/-- The selected identity precompile returns the initialized input bytes. -/
theorem executePrecompile_id_ok_output {evm : Evm} {post : Devm}
    (h : executePrecompile evm 4 = .ok post) :
    post.output = evm.sta.data := by
  change applyPrecompileResult evm (executeId evm) = .ok post at h
  unfold applyPrecompileResult at h
  rcases hx : executeId evm with ⟨reason, charged⟩ | ⟨charged, bytes⟩
  · simp only [hx] at h
    cases h
  · simp only [hx, Except.ok.injEq] at h
    subst post
    rw [Devm.withOutput_output]
    exact (executeId_ok_output_and_cost hx).1

private theorem bnp_serialized_length (p : Bn254G1) : (Bn254G1.toBytes p).length = 64 := by
  simp only [Bn254G1.toBytes, List.length_append, Bytes.pack, List.length_takeRightD]

private theorem blsp_serialized_length (p : Bls12G1) : (Bls12G1.toBytes p).length = 128 := by
  simp only [Bls12G1.toBytes, List.length_append, Bytes.pack, List.length_takeRightD]

private theorem blsf2_serialized_length (x : Bls12Fp2) : x.toBytes.length = 128 := by
  simp only [Bls12Fp2.toBytes, List.length_append, Bytes.pack, List.length_takeRightD]

private theorem blsp2_serialized_length (p : Bls12G2) : (Bls12G2.toBytes p).length = 256 := by
  simp only [Bls12G2.toBytes, List.length_append, blsf2_serialized_length]

private theorem executeEcadd_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeEcadd evm = .ok cost output) :
    output.length = 64 := by
  unfold executeEcadd PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact bnp_serialized_length _

private theorem executeEcmul_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeEcmul evm = .ok cost output) :
    output.length = 64 := by
  unfold executeEcmul PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact bnp_serialized_length _

private theorem executeBls12G1Add_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeBls12G1Add evm = .ok cost output) :
    output.length = 128 := by
  unfold executeBls12G1Add PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact blsp_serialized_length _

private theorem executeBls12G1Msm_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeBls12G1Msm evm = .ok cost output) :
    output.length = 128 := by
  unfold executeBls12G1Msm PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact blsp_serialized_length _

private theorem executeBls12G2Add_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeBls12G2Add evm = .ok cost output) :
    output.length = 256 := by
  unfold executeBls12G2Add PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact blsp2_serialized_length _

private theorem executeBls12G2Msm_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeBls12G2Msm evm = .ok cost output) :
    output.length = 256 := by
  unfold executeBls12G2Msm PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact blsp2_serialized_length _

private theorem executeBls12MapFpToG1_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeBls12MapFpToG1 evm = .ok cost output) :
    output.length = 128 := by
  unfold executeBls12MapFpToG1 PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact blsp_serialized_length _

private theorem executeBls12MapFp2ToG2_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeBls12MapFp2ToG2 evm = .ok cost output) :
    output.length = 256 := by
  unfold executeBls12MapFp2ToG2 PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact blsp2_serialized_length _

private theorem executeSha256_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeSha256 evm = .ok cost output) :
    output.length = 32 := by
  unfold executeSha256 PrecompileResult.chargeGas at h
  dsimp only at h
  split at h
  · cases h
    exact U256.length_toBytes _
  · cases h

private theorem executeRipemd160_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeRipemd160 evm = .ok cost output) :
    output.length = 32 := by
  unfold executeRipemd160 PrecompileResult.chargeGas at h
  dsimp only at h
  split at h
  · cases h
    exact U256.length_toBytes _
  · cases h

private theorem executeP256Verify_ok_output_length_le {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeP256Verify evm = .ok cost output) :
    output.length ≤ 32 := by
  unfold executeP256Verify PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals simp only [List.length_nil, U256.length_toBytes]
  all_goals omega

private theorem executeEcrecover_ok_output_length_le {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executeEcrecover evm = .ok cost output) :
    output.length ≤ 32 := by
  unfold executeEcrecover PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals simp only [List.length_nil, U256.length_toBytes]
  all_goals omega

private theorem executePointEval_ok_output_length {evm : Evm} {cost : Nat}
    {output : Bytes} (h : executePointEval evm = .ok cost output) :
    output.length = 64 := by
  unfold executePointEval PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals simp only [List.length_append, U256.length_toBytes]

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
    all_goals simp only [U256.length_toBytes]

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
    all_goals simp only [U256.length_toBytes]

private theorem executePairingCheck_ok_output_length {evm : Evm}
    {cost : Nat} {output : Bytes}
    (h : executePairingCheck evm = .ok cost output) : output.length = 32 := by
  unfold executePairingCheck PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals try cases h
  all_goals exact executePairingCheckInner_ok_output_length ‹_›

private theorem executeBls12Pairing_ok_output_length {evm : Evm}
    {cost : Nat} {output : Bytes}
    (h : executeBls12Pairing evm = .ok cost output) : output.length = 32 := by
  unfold executeBls12Pairing PrecompileResult.chargeGas at h
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
  unfold executeBlake2F PrecompileResult.chargeGas at h
  dsimp only at h
  repeat split at h
  all_goals repeat split at h
  all_goals repeat split at h
  all_goals try cases h
  all_goals exact bCompress_ok_output_length ‹_›

/-- Every successful initialized native precompile has a fixed-width reply
unless it is identity or MODEXP; those two use their paid input and gas. -/
theorem precompileRun_ok_output_length_lt_two_pow_160
    {evm : Evm} {adr : Address} {cost : Nat} {output : Bytes}
    (h : precompileRun evm adr = .ok cost output)
    (hdata : evm.sta.data.length < 2 ^ 160)
    (hgas : evm.dyna.gasLeft < 2 ^ 256 + Gas.callStipend) :
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
theorem executePrecompile_ok_output_length_lt_two_pow_160
    {evm : Evm} {adr : Address} {post : Devm}
    (h : executePrecompile evm adr = .ok post)
    (hdata : evm.sta.data.length < 2 ^ 160)
    (hgas : evm.dyna.gasLeft < 2 ^ 256 + Gas.callStipend) :
    post.output.length < 2 ^ 160 := by
  unfold executePrecompile applyPrecompileResult at h
  rcases hrun : precompileRun evm adr with ⟨reason, charged⟩ | ⟨charged, bytes⟩
  · simp only [hrun] at h
    cases h
  · simp only [hrun, Except.ok.injEq] at h
    subst post
    rw [Devm.withOutput_output]
    exact precompileRun_ok_output_length_lt_two_pow_160 hrun hdata hgas

end Jaune
