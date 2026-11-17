import Jaune.MemoryAccounting
import Jaune.MessageCall.Totality
import Jaune.Exec

/-!
# Memory accounting on the four-part chain (goal `jaune-shape-and-names-v1`, W1 unit L)

The theorems of `Jaune.MemoryAccounting` that speak of the old chain, restated over `Evm.step`,
its four tails, `enter`, `settle`, `resume` and the driver `execFueled`/`exec`. The
chain-independent part (gas arithmetic, memory extension, the per-instruction walks of the
plain, jump and halt instructions, the precompile output bounds) stays in
`Jaune.MemoryAccounting` and is used from there where it is public.

The non-spawning instruction walks are a mechanical port: `MessageOp.step`, `NextOp.step` and
the four tails are textually today's apart from their result type, so the private walks of
`Jaune.MemoryAccounting` are copied with `XStep` read as `MessageOp.Outcome` and `cont` as
`next`. The spawn accounting and the driver induction are written for `resume` and `settle`.
After the delete commit the private originals in `Jaune.MemoryAccounting` have no user left.
-/

namespace Jaune

open Jaune

/-! ### Chain-independent walks, copied from `Jaune.MemoryAccounting` -/

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


private theorem push_memory_output (pre : Devm) (word : U256) :
    match pre.push word with
    | .error failure => failure.2.memory = pre.memory ∧ failure.2.output = pre.output
    | .ok post => post.memory = pre.memory ∧ post.output = pre.output := by
  rw [Devm.push_def]
  by_cases hs : pre.stack.length < 1024
  · simp only [Except.assert, hs, ite_true, bind, Except.bind]
    exact ⟨rfl, rfl⟩
  · simp only [Except.assert, hs, ite_false, bind, Except.bind]
    exact ⟨True.intro, True.intro⟩

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

private theorem jump_memory_accounting (pc : Nat) (pre : Devm) (sevm : Sevm) (j : JumpOp) :
    nonspawnResult pre Prod.snd (JumpOp.runCore pc pre sevm j) := by
  refine nonspawnResult_of_fields (JumpOp.runCore_gasLe pc pre sevm j) ?_
  cases j with
  | jumpdest =>
      simp only [JumpOp.runCore]
      refine resultMemoryFields_bind (resultMemoryFields_charge Gas.jumpdest pre) ?_
      intro charged
      exact ⟨rfl, rfl⟩
  | jump =>
      simp only [JumpOp.runCore]
      refine resultMemoryFields_bind (resultMemoryFields_pop pre) ?_
      intro popped
      refine resultMemoryFields_bind (resultMemoryFields_charge Gas.mid popped.2) ?_
      intro charged
      simp only [Except.assert, bind, Except.bind]
      by_cases hj : jumpable sevm.code popped.1.toNat = true
      · simp only [ite_eq_left hj]
        exact ⟨rfl, rfl⟩
      · simp only [ite_eq_right hj]
        exact ⟨rfl, rfl⟩
  | jumpi =>
      simp only [JumpOp.runCore]
      refine resultMemoryFields_bind (resultMemoryFields_pop pre) ?_
      intro popped
      refine resultMemoryFields_bind (resultMemoryFields_pop popped.2) ?_
      intro poppedAgain
      refine resultMemoryFields_bind (resultMemoryFields_charge Gas.high poppedAgain.2) ?_
      intro charged
      split
      · exact ⟨rfl, rfl⟩
      · simp only [Except.assert, bind, Except.bind]
        by_cases hj : jumpable sevm.code popped.1.toNat = true
        · simp only [ite_eq_left hj]
          exact ⟨rfl, rfl⟩
        · simp only [ite_eq_right hj]
          exact ⟨rfl, rfl⟩

private theorem resultMemoryFields_push (pre : Devm) (word : U256) :
    resultMemoryFields pre id (pre.push word) := by
  have h := push_memory_output pre word
  cases hp : pre.push word <;> rw [hp] at h <;> exact h

private theorem resultMemoryFields_pushItem (word : U256) (cost : Nat) (pre : Devm) :
    resultMemoryFields pre id (pushItem word cost pre) := by
  rw [pushItem_def]
  refine resultMemoryFields_bind (resultMemoryFields_charge cost pre) ?_
  intro charged
  exact resultMemoryFields_push charged word

private theorem resultMemoryFields_unary (f : U256 → U256) (cost : Nat) (pre : Devm) :
    resultMemoryFields pre id (applyUnary f cost pre) := by
  rw [applyUnary_def]
  refine resultMemoryFields_bind (resultMemoryFields_pop pre) ?_
  intro popped
  exact resultMemoryFields_pushItem (f popped.1) cost popped.2

private theorem resultMemoryFields_binary (f : U256 → U256 → U256)
    (cost : Nat) (pre : Devm) : resultMemoryFields pre id (applyBinary f cost pre) := by
  rw [applyBinary_def]
  refine resultMemoryFields_bind (resultMemoryFields_pop pre) ?_
  intro popped
  refine resultMemoryFields_bind (resultMemoryFields_pop popped.2) ?_
  intro poppedAgain
  exact resultMemoryFields_pushItem (f popped.1 poppedAgain.1) cost poppedAgain.2

private theorem nonspawn_pushItem (word : U256) (cost : Nat) (pre : Devm) :
    nonspawnResult pre id (pushItem word cost pre) := by
  refine nonspawnResult_of_fields ?_ (resultMemoryFields_pushItem word cost pre)
  simpa only [resultGas_id] using pushItem_gasLe word cost pre

private theorem nonspawn_unary (f : U256 → U256) (cost : Nat) (pre : Devm) :
    nonspawnResult pre id (applyUnary f cost pre) := by
  refine nonspawnResult_of_fields ?_ (resultMemoryFields_unary f cost pre)
  simpa only [resultGas_id] using applyUnary_gasLe f cost pre

private theorem nonspawn_binary (f : U256 → U256 → U256) (cost : Nat) (pre : Devm) :
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

private theorem nonspawn_push (word : U256) (pre : Devm) :
    nonspawnResult pre id (pre.push word) := by
  refine nonspawnResult_of_fields ?_ (resultMemoryFields_push pre word)
  simpa only [resultGas_id] using Nat.le_of_eq (Devm.push_gasLe word pre)

private theorem nonspawn_blockAccessListReadAccount (rules : ForkRules) (adr : Address) (pre : Devm) :
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

private theorem nonspawn_blockAccessListReadStorage (rules : ForkRules) (adr : Address) (key : U256)
    (pre : Devm) : nonspawnPreserved pre (pre.balReadStorage rules adr key) := by
  refine ⟨Nat.le_refl _, ?_⟩
  unfold Devm.balReadStorage
  split <;> rfl

private theorem nonspawn_addAccessedAddress (pre : Devm) (adr : Address) :
    nonspawnPreserved pre (addAccessedAddress pre adr) :=
  ⟨Nat.le_refl _, rfl⟩

private theorem nonspawn_addAccessedStorageKey (pre : Devm) (adr : Address) (key : U256) :
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

private theorem ternary_execution_eq (f : U256 → U256 → U256 → U256)
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

private theorem nonspawn_ternary (f : U256 → U256 → U256 → U256)
    (cost : Nat) (pre : Devm) : nonspawnResult pre id (applyTernary f cost pre) := by
  rw [ternary_execution_eq]
  refine nonspawnResult_bind (nonspawn_pop pre) ?_
  intro first
  refine nonspawnResult_bind (nonspawn_pop first.2) ?_
  intro second
  refine nonspawnResult_bind (nonspawn_pop second.2) ?_
  intro third
  exact nonspawn_pushItem (f first.1 second.1 third.1) cost third.2

private theorem nonspawn_external_copy (rules : ForkRules) (adr : Address)
    (index codeIndex size : Nat) (pre : Devm) :
    nonspawnPreserved (pre.memExtends [(index, size)])
      ((pre.balReadAccount rules adr).memWrite index
        (ByteArray.sliceD ((pre.balReadAccount rules adr).getCode adr)
          codeIndex size (HaltOp.toUInt8 .stop))) := by
  have hb := nonspawn_blockAccessListReadAccount rules adr (pre.memExtends [(index, size)])
  have hw := nonspawn_write (pre.balReadAccount rules adr) index
    (ByteArray.sliceD ((pre.balReadAccount rules adr).getCode adr)
      codeIndex size (HaltOp.toUInt8 .stop))
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
      (liftMachMetaWorldExecution (PlainOp.balanceCore rules) pre) := by
  rcases pre with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  cases stack with
  | nil => exact ⟨rfl, rfl⟩
  | cons word rest =>
      by_cases hw : word.toAddress ∈ view.accessedAddresses
      all_goals by_cases hb : rules.blockAccessListRules.isSome = true
      all_goals rcases hA : rules.access with g | _
      all_goals
        simp only [liftMachMetaWorldExecution, liftMachMetaExecution, liftMachMeta,
          Footprint.toExecution, Footprint.liftOutcome, PlainOp.balanceCore, Mach.pop,
          hw, hb, hA, ite_true, ite_false]
        -- The charge is one of three constants: warm, cold, or the flat price.
        first
        | (cases hc : safeSub gasLeft Gas.warmStorageReadCost with
            | none =>
                simp only [Mach.chargeGas, hc]
                exact ⟨rfl, rfl⟩
            | some gas =>
                simp only [Mach.chargeGas, hc, Mach.push]
                by_cases hp : rest.length < 1024
                · simp only [ite_eq_left hp]
                  exact ⟨rfl, rfl⟩
                · simp only [ite_eq_right hp]
                  exact ⟨rfl, rfl⟩)
        | (cases hc : safeSub gasLeft rules.gas.coldAccountAccess with
            | none =>
                simp only [Mach.chargeGas, hc]
                exact ⟨rfl, rfl⟩
            | some gas =>
                simp only [Mach.chargeGas, hc, Mach.push]
                by_cases hp : rest.length < 1024
                · simp only [ite_eq_left hp]
                  exact ⟨rfl, rfl⟩
                · simp only [ite_eq_right hp]
                  exact ⟨rfl, rfl⟩)
        | (cases hc : safeSub gasLeft g.balance with
            | none =>
                simp only [Mach.chargeGas, hc]
                exact ⟨rfl, rfl⟩
            | some gas =>
                simp only [Mach.chargeGas, hc, Mach.push]
                by_cases hp : rest.length < 1024
                · simp only [ite_eq_left hp]
                  exact ⟨rfl, rfl⟩
                · simp only [ite_eq_right hp]
                  exact ⟨rfl, rfl⟩)

private theorem regular_memory_accounting (pc : Nat) (pre : Devm) (sevm : Sevm) (r : PlainOp)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    nonspawnResult pre id (PlainOp.runCore pc pre sevm r) := by
  cases r <;> simp only [PlainOp.runCore]
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
    split
    · refine nonspawnResult_bind (nonspawn_pop pre) ?_
      intro popped
      rw [← pushItem_def]
      exact nonspawn_pushItem _ _ _
    · exact ⟨Nat.le_refl _, rfl⟩
  case blockhash =>
    refine nonspawnResult_bind (nonspawn_pop pre) ?_
    intro popped
    rw [← pushItem_def]
    exact nonspawn_pushItem _ _ _
  case tload =>
    split
    · refine nonspawnResult_bind (nonspawn_pop pre) ?_
      intro popped
      exact nonspawn_pushItem _ _ _
    · exact ⟨Nat.le_refl _, rfl⟩
  case gas =>
    refine nonspawnResult_bind (nonspawn_charge Gas.base pre) ?_
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
  case shl | shr | sar =>
    split
    · exact nonspawn_binary _ _ _
    · exact ⟨Nat.le_refl _, rfl⟩
  case chainid | basefee | blobbasefee =>
    split
    · exact nonspawn_pushItem _ _ _
    · exact ⟨Nat.le_refl _, rfl⟩
  case selfbalance =>
    split
    · refine nonspawnResult_bind (nonspawn_charge Gas.low pre) ?_
      intro charged
      exact nonspawnResult_trans (nonspawn_blockAccessListReadAccount sevm.benvStat.rules
        sevm.currentTarget charged) (nonspawn_push _ _)
    · exact ⟨Nat.le_refl _, rfl⟩
  case dup n =>
    refine nonspawnResult_bind (nonspawn_charge Gas.veryLow pre) ?_
    intro charged
    rcases hword : charged.stack[n]? with _ | word
    · exact ⟨Nat.le_refl _, rfl⟩
    · exact nonspawn_push word charged
  case swap n =>
    refine nonspawnResult_bind (nonspawn_charge Gas.veryLow pre) ?_
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
    exact nonspawn_charge Gas.base popped
  case extcodesize =>
    refine nonspawnResult_bind (nonspawn_popToAdr pre) ?_
    intro popped
    split
    · split
      · refine nonspawnResult_bind (nonspawn_charge _ popped.2) ?_
        intro charged
        exact nonspawnResult_trans (nonspawn_blockAccessListReadAccount sevm.benvStat.rules
          popped.1 charged) (nonspawn_push _ _)
      · refine nonspawnResult_trans (nonspawn_addAccessedAddress popped.2 popped.1) ?_
        refine nonspawnResult_bind (nonspawn_charge _ _) ?_
        intro charged
        exact nonspawnResult_trans (nonspawn_blockAccessListReadAccount sevm.benvStat.rules
          popped.1 charged) (nonspawn_push _ _)
    · -- Flat: one fixed price, the accessed set untouched.
      refine nonspawnResult_bind (nonspawn_charge _ popped.2) ?_
      intro charged
      exact nonspawnResult_trans (nonspawn_blockAccessListReadAccount sevm.benvStat.rules
        popped.1 charged) (nonspawn_push _ _)
  case extcodehash =>
    split
    · refine nonspawnResult_bind (nonspawn_popToAdr pre) ?_
      intro popped
      split
      · split
        · refine nonspawnResult_bind (nonspawn_charge _ popped.2) ?_
          intro charged
          exact nonspawnResult_trans (nonspawn_blockAccessListReadAccount sevm.benvStat.rules
            popped.1 charged) (nonspawn_push _ _)
        · refine nonspawnResult_trans (nonspawn_addAccessedAddress popped.2 popped.1) ?_
          refine nonspawnResult_bind (nonspawn_charge _ _) ?_
          intro charged
          exact nonspawnResult_trans (nonspawn_blockAccessListReadAccount sevm.benvStat.rules
            popped.1 charged) (nonspawn_push _ _)
      · -- Flat: one fixed price, the accessed set untouched.
        refine nonspawnResult_bind (nonspawn_charge _ popped.2) ?_
        intro charged
        exact nonspawnResult_trans (nonspawn_blockAccessListReadAccount sevm.benvStat.rules
          popped.1 charged) (nonspawn_push _ _)
    · exact ⟨Nat.le_refl _, rfl⟩
  case sload =>
    refine nonspawnResult_bind (nonspawn_pop pre) ?_
    intro popped
    split
    · split
      · refine nonspawnResult_bind (nonspawn_charge Gas.warmStorageReadCost popped.2) ?_
        intro charged
        exact nonspawnResult_trans (nonspawn_blockAccessListReadStorage sevm.benvStat.rules
          sevm.currentTarget popped.1 charged) (nonspawn_push _ _)
      · refine nonspawnResult_trans (nonspawn_addAccessedStorageKey popped.2
          sevm.currentTarget popped.1) ?_
        refine nonspawnResult_bind (nonspawn_charge Gas.coldSloadCost _) ?_
        intro charged
        exact nonspawnResult_trans (nonspawn_blockAccessListReadStorage sevm.benvStat.rules
          sevm.currentTarget popped.1 charged) (nonspawn_push _ _)
    · -- Flat: one fixed price, the accessed set untouched.
      refine nonspawnResult_bind (nonspawn_charge _ popped.2) ?_
      intro charged
      exact nonspawnResult_trans (nonspawn_blockAccessListReadStorage sevm.benvStat.rules
        sevm.currentTarget popped.1 charged) (nonspawn_push _ _)
  case tstore =>
    split
    · simp only [hstate]
      refine nonspawnResult_bind (nonspawn_pop pre) ?_
      intro popped
      refine nonspawnResult_bind (nonspawn_pop popped.2) ?_
      intro poppedAgain
      refine nonspawnResult_bind (nonspawn_charge Gas.warmStorageReadCost poppedAgain.2) ?_
      intro charged
      refine nonspawnResult_bind (nonspawn_assertDynamic sevm charged) ?_
      intro _
      exact ⟨Nat.le_refl _, rfl⟩
    · exact ⟨Nat.le_refl _, rfl⟩
  case mload =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawn_charged_memory [(popped.1, 32)] Gas.veryLow popped.2 _ ?_
    intro charged
    exact nonspawnResult_trans (nonspawn_read charged popped.1 32) (nonspawn_push _ _)
  case keccak256 =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_popToNat popped.2) ?_
    intro poppedAgain
    refine nonspawn_charged_memory [(popped.1, poppedAgain.1)]
      (Gas.keccak256 + Gas.keccak256Word * ceilDiv poppedAgain.1 32) poppedAgain.2 _ ?_
    intro charged
    exact nonspawnResult_trans (nonspawn_read charged popped.1 poppedAgain.1)
      (nonspawn_push _ _)
  case mstore =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_pop popped.2) ?_
    intro poppedAgain
    refine nonspawn_charged_memory [(popped.1, 32)] Gas.veryLow poppedAgain.2 _ ?_
    intro charged
    change nonspawnPreserved (charged.memExtends [(popped.1, 32)])
      (charged.memWrite popped.1 poppedAgain.1.toBytes)
    simpa only [U256.length_toBytes] using nonspawn_write charged popped.1 poppedAgain.1.toBytes
  case mstore8 =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_pop popped.2) ?_
    intro poppedAgain
    refine nonspawn_charged_memory [(popped.1, 1)] Gas.veryLow poppedAgain.2 _ ?_
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
      (Gas.veryLow + Gas.copy * ceilDiv size.1 32) size.2 _ ?_
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
      (Gas.veryLow + Gas.copy * ceilDiv size.1 32) size.2 _ ?_
    intro charged
    change nonspawnPreserved (charged.memExtends [(popped.1, size.1)])
      (charged.memWrite popped.1 (ByteArray.sliceD sevm.code codeIndex.1 size.1 (HaltOp.toUInt8 .stop)))
    simpa only [ByteArray.length_sliceD] using nonspawn_write charged popped.1
      (ByteArray.sliceD sevm.code codeIndex.1 size.1 (HaltOp.toUInt8 .stop))
  case returndatacopy =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_popToNat popped.2) ?_
    intro dataIndex
    refine nonspawnResult_bind (nonspawn_popToNat dataIndex.2) ?_
    intro size
    refine nonspawn_charged_memory [(popped.1, size.1)]
      (Gas.veryLow + Gas.returnDataCopy * ceilDiv size.1 32) size.2 _ ?_
    intro charged
    split
    · simp only [bind, Except.bind]
      exact nonspawn_before_paid [(popped.1, size.1)] charged
    · change nonspawnPreserved (charged.memExtends [(popped.1, size.1)])
        (charged.memWrite popped.1 (List.sliceD charged.returnData dataIndex.1 size.1 0))
      simpa only [list_slice_length] using
        nonspawn_write charged popped.1 (List.sliceD charged.returnData dataIndex.1 size.1 0)
  case mcopy =>
    split
    · refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
      intro destination
      refine nonspawnResult_bind (nonspawn_popToNat destination.2) ?_
      intro source
      refine nonspawnResult_bind (nonspawn_popToNat source.2) ?_
      intro size
      refine nonspawn_charged_memory [(source.1, size.1), (destination.1, size.1)]
        (Gas.veryLow + Gas.copy * ceilDiv size.1 32) size.2 _ ?_
      intro charged
      have hw := nonspawn_write (charged.memRead source.1 size.1).2 destination.1
        (charged.memRead source.1 size.1).1
      have hl : (charged.memRead source.1 size.1).1.length = size.1 :=
        memory_slice_length charged.memory.data source.1 size.1 0
      rw [hl] at hw
      exact hw
    · exact ⟨Nat.le_refl _, rfl⟩
  case log n =>
    refine nonspawnResult_bind (nonspawn_popToNat pre) ?_
    intro popped
    refine nonspawnResult_bind (nonspawn_popToNat popped.2) ?_
    intro size
    refine nonspawnResult_bind (nonspawn_popN size.2 n) ?_
    intro topics
    refine nonspawn_charged_memory [(popped.1, size.1)]
      (Gas.log + Gas.logData * size.1 + Gas.logTopic * n) topics.2 _ ?_
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
    · split
      · refine nonspawn_charged_memory [(memoryIndex.1, size.1)]
          (Gas.warmStorageReadCost + sevm.benvStat.rules.gas.codeReadSurcharge +
            Gas.copy * ceilDiv size.1 32) size.2 _ ?_
        intro charged
        exact nonspawn_external_copy sevm.benvStat.rules address.1
          memoryIndex.1 codeIndex.1 size.1 charged
      · refine nonspawnResult_trans (nonspawn_addAccessedAddress size.2 address.1) ?_
        refine nonspawn_charged_memory [(memoryIndex.1, size.1)]
          (sevm.benvStat.rules.gas.coldAccountAccess +
            sevm.benvStat.rules.gas.codeReadSurcharge + Gas.copy * ceilDiv size.1 32)
          (addAccessedAddress size.2 address.1) _ ?_
        intro charged
        exact nonspawn_external_copy sevm.benvStat.rules address.1
          memoryIndex.1 codeIndex.1 size.1 charged
    · -- Flat: one fixed price, the accessed set untouched.
      refine nonspawn_charged_memory [(memoryIndex.1, size.1)]
        _ size.2 _ ?_
      intro charged
      exact nonspawn_external_copy sevm.benvStat.rules address.1
        memoryIndex.1 codeIndex.1 size.1 charged
  case balance =>
    refine nonspawnResult_of_fields ?_ (resultMemoryFields_balance _ pre)
    simpa only [PlainOp.runCore, resultGas_id] using
      PlainOp.runCore_gasLe pc pre sevm .balance
  case sstore =>
    rw [hstate]
    dsimp only
    split
    · -- Prague: the body it has always been.
      refine nonspawnResult_bind (nonspawn_pop pre) ?_
      intro key
      refine nonspawnResult_bind (nonspawn_pop key.2) ?_
      intro value
      refine nonspawnResult_bind
        (nonspawn_assert (Gas.callStipend < value.2.gasLeft) (.halt (.outOfGas .none)) value.2) ?_
      intro _
      refine nonspawnResult_bind (projectFirst := Prod.fst) ?_ ?_
      · split
        · exact nonspawnPreserved_trans
            (nonspawn_blockAccessListReadStorage sevm.benvStat.rules sevm.currentTarget key.1 value.2)
            (nonspawn_addAccessedStorageKey _ sevm.currentTarget key.1)
        · exact nonspawn_blockAccessListReadStorage sevm.benvStat.rules sevm.currentTarget key.1 value.2
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
              (nonspawn_blockAccessListReadAccount sevm.benvStat.rules sevm.currentTarget charged)
              ⟨Nat.le_refl _, rfl⟩
    · -- The pre-Berlin regimes: the sentry is gated and the cold pair cases
      -- on access, then on the slot's warmth. The tail is unchanged.
      refine nonspawnResult_bind (nonspawn_pop pre) ?_
      intro key
      refine nonspawnResult_bind (nonspawn_pop key.2) ?_
      intro value
      refine nonspawnResult_bind
        (nonspawn_assert
          (sevm.benvStat.rules.sstore.stipendSentry = true → Gas.callStipend < value.2.gasLeft)
          (.halt (.outOfGas .none)) value.2) ?_
      intro _
      refine nonspawnResult_bind (projectFirst := Prod.fst) ?_ ?_
      · split
        · exact nonspawn_blockAccessListReadStorage sevm.benvStat.rules sevm.currentTarget key.1 value.2
        · split
          · exact nonspawnPreserved_trans
              (nonspawn_blockAccessListReadStorage sevm.benvStat.rules sevm.currentTarget key.1 value.2)
              (nonspawn_addAccessedStorageKey _ sevm.currentTarget key.1)
          · exact nonspawn_blockAccessListReadStorage sevm.benvStat.rules sevm.currentTarget key.1 value.2
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
              (nonspawn_blockAccessListReadAccount sevm.benvStat.rules sevm.currentTarget charged)
              ⟨Nat.le_refl _, rfl⟩


/-! ### Message opcodes that finish without a child -/

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

private def xAccounting (pre : Devm) (allowance : Nat) : MessageOp.Outcome → Prop
  | .done raw => allowanceResult pre allowance raw
  | .spawn _ _ => True

private def xResult (pre : Devm) (allowance : Nat)
    (raw : Except (EvmError × Devm) MessageOp.Outcome) : Prop :=
  match raw with
  | .error failure => allowancePreserved pre allowance failure.2
  | .ok step => xAccounting pre allowance step

private theorem allowance_rebase {pre middle post : Devm} {inner outer : Nat}
    (hp : middle.gasMeasure + calculateMemoryGasCost middle.memory.size + inner ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + outer)
    (ho : middle.output = pre.output)
    (h : allowancePreserved middle inner post) : allowancePreserved pre outer post := by
  exact ⟨Nat.le_trans h.1 hp, h.2.trans ho⟩

private theorem xAccounting_rebase {pre middle : Devm} {inner outer : Nat} {step : MessageOp.Outcome}
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
    {raw : Except (EvmError × Devm) MessageOp.Outcome}
    (hp : middle.gasMeasure + calculateMemoryGasCost middle.memory.size + inner ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + outer)
    (ho : middle.output = pre.output) (h : xResult middle inner raw) :
    xResult pre outer raw := by
  cases raw with
  | error failure => exact allowance_rebase hp ho h
  | ok step => exact xAccounting_rebase hp ho h

private theorem xResult_bind {α : Type} {pre : Devm} {allowance : Nat}
    {first : Except (EvmError × Devm) α} {next : α → Except (EvmError × Devm) MessageOp.Outcome}
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
    {raw : Except (EvmError × Devm) MessageOp.Outcome} (h : xResult pre allowance raw) :
    xAccounting pre allowance (MessageOp.Outcome.ofExcept raw) := by
  cases raw with
  | error failure => exact h
  | ok step => exact h

private theorem xResult_charged_memory (pairs : List (Nat × Nat)) (baseCost : Nat)
    (pre : Devm) (action : Devm → Except (EvmError × Devm) MessageOp.Outcome)
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
    (sevm : Sevm) (pre : Devm) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (transfer staticCall : Bool)
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

private theorem xResult_done_push (word : U256) (pre : Devm) :
    xResult pre 0 (do
      let post ← pre.push word
      pure (.done (.ok post))) := by
  refine xResult_bind (nonspawn_push word pre) ?_
  intro post
  exact ⟨Nat.le_refl _, rfl⟩

private theorem genericCreate_memory_accounting
    (sevm : Sevm) (pre : Devm) (endowment : U256)
    (newAddress : Address) (memoryIndex memorySize : Nat) :
    xAccounting pre 0
      (genericCreate.step sevm pre endowment newAddress memoryIndex memorySize) := by
  unfold genericCreate.step
  apply xAccounting_ofExcept
  refine xResult_bind
    (nonspawn_assert (sevm.benvStat.rules.creation.initCodeLimit →
        memorySize ≤ sevm.benvStat.rules.code.maxInitCodeSize)
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
  by_cases hfail : (current.state.get sevm.currentTarget).balance < endowment ∨
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
        (accessed.state.get newAddress).code.size ≠ 0
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

private theorem delegation_memory_output (gasRules : GasSchedule) (pre : Devm) (adr : Address) :
    (gasRules.accessDelegation pre adr).2.2.2.2.memory = pre.memory ∧
      (gasRules.accessDelegation pre adr).2.2.2.2.output = pre.output := by
  unfold GasSchedule.accessDelegation
  cases hd : getDelegatedCodeAddress (pre.state.getCode adr) with
  | none => simp only [hd]; exact ⟨True.intro, True.intro⟩
  | some delegated => simp only [hd]; exact ⟨rfl, rfl⟩

private theorem nonspawn_delegation (gasRules : GasSchedule) (pre : Devm) (adr : Address) :
    nonspawnPreserved pre (gasRules.accessDelegation pre adr).2.2.2.2 := by
  have hf := delegation_memory_output gasRules pre adr
  refine ⟨?_, hf.2⟩
  rw [GasSchedule.accessDelegation_gasMeasure, hf.1]

private theorem rules_delegation_memory_output (rules : ForkRules) (pre : Devm) (adr : Address) :
    (rules.accessDelegation pre adr).2.2.2.2.memory = pre.memory ∧
      (rules.accessDelegation pre adr).2.2.2.2.output = pre.output := by
  unfold ForkRules.accessDelegation
  split
  · exact delegation_memory_output rules.gas pre adr
  · exact ⟨rfl, rfl⟩

private theorem nonspawn_rules_delegation (rules : ForkRules) (pre : Devm) (adr : Address) :
    nonspawnPreserved pre (rules.accessDelegation pre adr).2.2.2.2 := by
  have hf := rules_delegation_memory_output rules pre adr
  refine ⟨?_, hf.2⟩
  rw [ForkRules.accessDelegation_gasMeasure, hf.1]

private theorem xResult_charged_call (pairs : List (Nat × Nat)) (cost refund : Nat)
    (pre : Devm) (hrefund : refund ≤ cost)
    (action : Devm → Except (EvmError × Devm) MessageOp.Outcome)
    (hbody : ∀ charged, xResult (charged.memExtends pairs) refund (action charged)) :
    xResult pre 0 (chargeGas (cost + pre.extCost pairs) pre >>= action) := by
  refine xResult_charged_memory pairs cost pre action ?_
  intro charged
  exact xResult_rebase (pre := charged.memExtends pairs)
    (middle := charged.memExtends pairs) (inner := refund) (outer := cost)
    (Nat.add_le_add_left hrefund _) rfl (hbody charged)

private theorem value_call_refund_le_base (sevm : Sevm) (value : U256)
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

private theorem executable_memory_accounting (sevm : Sevm) (pre : Devm) (x : MessageOp)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    xAccounting pre 0 (MessageOp.step sevm pre x) := by
  cases x <;> simp only [MessageOp.step, hstate]
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
      (if sevm.benvStat.rules.creation.initCodeLimit then
        Gas.initcodeWordCost * ceilDiv memorySize.1 32 else 0)]
    refine xResult_charged_memory [(memoryIndex.1, memorySize.1)]
      (sevm.benvStat.rules.gas.createAccess + if sevm.benvStat.rules.creation.initCodeLimit then
        Gas.initcodeWordCost * ceilDiv memorySize.1 32 else 0)
      memorySize.2 _ ?_
    intro charged
    refine xAccounting_rebase (pre := charged.memExtends [(memoryIndex.1, memorySize.1)])
      (inner := 0) ?_ rfl
      (genericCreate_memory_accounting sevm _ endowment.1 _ memoryIndex.1 memorySize.1)
    omega
  case create2 =>
    by_cases hf : sevm.benvStat.rules.opcodes.create2 = true
    · simp only [ite_eq_left hf]
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
        (sevm.benvStat.rules.gas.createAccess + Gas.keccak256Word * ceilDiv memorySize.1 32)
        (salt.2.extCost [(memoryIndex.1, memorySize.1)])
        (if sevm.benvStat.rules.creation.initCodeLimit then
          Gas.initcodeWordCost * ceilDiv memorySize.1 32 else 0)]
      refine xResult_charged_memory [(memoryIndex.1, memorySize.1)]
        (sevm.benvStat.rules.gas.createAccess + Gas.keccak256Word * ceilDiv memorySize.1 32 +
          if sevm.benvStat.rules.creation.initCodeLimit then
            Gas.initcodeWordCost * ceilDiv memorySize.1 32 else 0)
        salt.2 _ ?_
      intro charged
      refine xAccounting_rebase (pre := charged.memExtends [(memoryIndex.1, memorySize.1)])
        (inner := 0) ?_ rfl
        (genericCreate_memory_accounting sevm _ endowment.1 _ memoryIndex.1 memorySize.1)
      omega
    · simp only [ite_eq_right hf]
      apply xAccounting_ofExcept
      exact ⟨Nat.le_refl _, rfl⟩
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
    -- The access step of either shape: a price `price` and a recorder `dA`.
    rcases hA : sevm.benvStat.rules.access with g | _
    on_goal 1 =>
      let price := g.call
      let dA := outputSize.2
      have hdA : nonspawnPreserved outputSize.2 dA := ⟨Nat.le_refl _, rfl⟩
    on_goal 2 =>
      let price := sevm.benvStat.rules.gas.accessCost codeAddress.1 outputSize.2.accessedAddresses
      let dA := addAccessedAddress outputSize.2 codeAddress.1
      have hdA := nonspawn_addAccessedAddress outputSize.2 codeAddress.1
    all_goals
      let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
      let lookup := sevm.benvStat.rules.accessDelegation
        dA codeAddress.1
      let parent := lookup.2.2.2.2
      have hp : nonspawnPreserved outputSize.2 parent :=
        nonspawnPreserved_trans hdA
          (nonspawn_rules_delegation sevm.benvStat.rules _ codeAddress.1)
      refine xResult_rebase (pre := outputSize.2) (middle := parent)
        (inner := 0) (outer := 0) hp.1 hp.2 ?_
      have hm : parent.memory = outputSize.2.memory :=
        (rules_delegation_memory_output sevm.benvStat.rules
          dA codeAddress.1).1
      have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
        simp only [Devm.extCost, hm]
      change xResult parent 0 (chargeGas
        ((calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (outputSize.2.extCost pairs)
          (price +
            lookup.2.2.2.1)).1 + outputSize.2.extCost pairs) parent >>= _)
      rw [hext]
      let costs := calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (parent.extCost pairs)
        (price +
          lookup.2.2.2.1)
      refine xResult_charged_call pairs costs.1 costs.2 parent ?_ _ ?_
      · exact calculateMsgCallGas_refund_le_base 0 gas.1.toNat parent.gasLeft
          (parent.extCost pairs)
          (price +
            lookup.2.2.2.1) Gas.callStipend (Nat.zero_le _)
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
    -- The access step of either shape: a price `price` and a recorder `dA`.
    rcases hA : sevm.benvStat.rules.access with g | _
    on_goal 1 =>
      let price := g.call
      let dA := outputSize.2
      have hdA : nonspawnPreserved outputSize.2 dA := ⟨Nat.le_refl _, rfl⟩
    on_goal 2 =>
      let price := sevm.benvStat.rules.gas.accessCost target.1 outputSize.2.accessedAddresses
      let dA := addAccessedAddress outputSize.2 target.1
      have hdA := nonspawn_addAccessedAddress outputSize.2 target.1
    all_goals
      let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
      let lookup := sevm.benvStat.rules.accessDelegation
        dA target.1
      let parent := lookup.2.2.2.2
      have hp : nonspawnPreserved outputSize.2 parent :=
        nonspawnPreserved_trans hdA
          (nonspawn_rules_delegation sevm.benvStat.rules _ target.1)
      refine xResult_rebase (pre := outputSize.2) (middle := parent)
        (inner := 0) (outer := 0) hp.1 hp.2 ?_
      have hm : parent.memory = outputSize.2.memory :=
        (rules_delegation_memory_output sevm.benvStat.rules
          dA target.1).1
      have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
        simp only [Devm.extCost, hm]
      change xResult parent 0 (chargeGas
        ((calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (outputSize.2.extCost pairs)
          (price +
            lookup.2.2.2.1)).1 + outputSize.2.extCost pairs) parent >>= _)
      rw [hext]
      let costs := calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (parent.extCost pairs)
        (price +
          lookup.2.2.2.1)
      refine xResult_charged_call pairs costs.1 costs.2 parent ?_ _ ?_
      · exact calculateMsgCallGas_refund_le_base 0 gas.1.toNat parent.gasLeft
          (parent.extCost pairs)
          (price +
            lookup.2.2.2.1) Gas.callStipend (Nat.zero_le _)
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
    -- The access step of either shape: a price `price` and a recorder `dA`.
    rcases hA : sevm.benvStat.rules.access with g | _
    on_goal 1 =>
      let price := g.call
      let dA := outputSize.2
      have hdA : nonspawnPreserved outputSize.2 dA := ⟨Nat.le_refl _, rfl⟩
    on_goal 2 =>
      let price := sevm.benvStat.rules.gas.accessCost callee.1 outputSize.2.accessedAddresses
      let dA := addAccessedAddress outputSize.2 callee.1
      have hdA := nonspawn_addAccessedAddress outputSize.2 callee.1
    all_goals
      let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
      let lookup := sevm.benvStat.rules.accessDelegation
        dA callee.1
      let parent := lookup.2.2.2.2
      have hp : nonspawnPreserved outputSize.2 parent :=
        nonspawnPreserved_trans hdA
          (nonspawn_rules_delegation sevm.benvStat.rules _ callee.1)
      refine xResult_rebase (pre := outputSize.2) (middle := parent)
        (inner := 0) (outer := 0) hp.1 hp.2 ?_
      have hm : parent.memory = outputSize.2.memory :=
        (rules_delegation_memory_output sevm.benvStat.rules
          dA callee.1).1
      have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
        simp only [Devm.extCost, hm]
      let accessCost := price + lookup.2.2.2.1
      let createCost : Nat := if ¬(parent.getAcct callee.1).isEmpty ∨ value.1 = 0 then 0 else Gas.newAccount
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
        by_cases hb : (paid.getAcct sevm.currentTarget).balance < value.1
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
    -- The access step of either shape: a price `price` and a recorder `dA`.
    rcases hA : sevm.benvStat.rules.access with g | _
    on_goal 1 =>
      let price := g.call
      let dA := outputSize.2
      have hdA : nonspawnPreserved outputSize.2 dA := ⟨Nat.le_refl _, rfl⟩
    on_goal 2 =>
      let price := sevm.benvStat.rules.gas.accessCost codeAddress.1 outputSize.2.accessedAddresses
      let dA := addAccessedAddress outputSize.2 codeAddress.1
      have hdA := nonspawn_addAccessedAddress outputSize.2 codeAddress.1
    all_goals
      let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
      let lookup := sevm.benvStat.rules.accessDelegation
        dA codeAddress.1
      let parent := lookup.2.2.2.2
      have hp : nonspawnPreserved outputSize.2 parent :=
        nonspawnPreserved_trans hdA
          (nonspawn_rules_delegation sevm.benvStat.rules _ codeAddress.1)
      refine xResult_rebase (pre := outputSize.2) (middle := parent)
        (inner := 0) (outer := 0) hp.1 hp.2 ?_
      have hm : parent.memory = outputSize.2.memory :=
        (rules_delegation_memory_output sevm.benvStat.rules
          dA codeAddress.1).1
      have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
        simp only [Devm.extCost, hm]
      let accessCost := price + lookup.2.2.2.1
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
        by_cases hb : (paid.getAcct sevm.currentTarget).balance < value.1
        · dsimp only [paid, pairs] at hb
          simp only [ite_eq_left hb]
          exact balance_refund_accounting paid costs.2
        · dsimp only [paid, pairs] at hb
          simp only [ite_eq_right hb]
          exact genericCall_memory_allowance sevm paid costs.2 value.1
            sevm.currentTarget sevm.currentTarget lookup.2.1 true false
            inputIndex.1 inputSize.1 outputIndex.1 outputSize.1 lookup.2.2.1 lookup.1


/-! ### One step -/

private def rawTerminalAccounted (pre : Devm) (raw : Execution) : Prop :=
  match raw with
  | .ok post => accountedTerminal pre post
  | .error failure => accountedTerminal pre failure.2

private def stepAccounted (pre : Devm) : Step → Prop
  | .next _ post => nonspawnPreserved pre post
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

private theorem ofMessageOp.Outcome_accounted (pc : Nat) {pre : Devm} {step : MessageOp.Outcome}
    (h : xAccounting pre 0 step) : stepAccounted pre (MessageOp.Outcome.toStep pc step) := by
  cases step with
  | spawn _ _ => trivial
  | done raw =>
      cases raw with
      | error failure => exact ⟨h.1, Or.inl h.2⟩
      | ok post => exact h

private theorem nonterminal_memory_accounting (evm : Evm) (n : NextOp)
    (hstate : evm.sta.benvStat.rules.stateGas = none) :
    stepAccounted evm.dyna (NextOp.step evm n) := by
  cases n <;> simp only [NextOp.step]
  case plain r =>
    exact ofExecution_accounted _
      (regular_memory_accounting evm.pc evm.dyna evm.sta r hstate)
  case message x =>
    exact ofMessageOp.Outcome_accounted _ (executable_memory_accounting evm.sta evm.dyna x hstate)
  case push bytes bound =>
    by_cases hf : (decide (bytes = []) && !evm.sta.benvStat.rules.opcodes.push0) = true
    · simp only [ite_eq_left hf]
      apply ofExecution_accounted
      exact ⟨Nat.le_refl _, rfl⟩
    · simp only [ite_eq_right hf]
      apply ofExecution_accounted
      refine nonspawnResult_bind (nonspawn_charge _ evm.dyna) ?_
      intro charged
      exact nonspawn_push bytes.toU256 charged
  case dupn imm =>
    apply ofExecution_accounted
    by_cases hf : evm.sta.benvStat.rules.opcodes.stackAccess = true
    · simp only [ite_eq_left hf]
      refine nonspawnResult_bind (nonspawn_charge Gas.veryLow evm.dyna) ?_
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
    by_cases hf : evm.sta.benvStat.rules.opcodes.stackAccess = true
    · simp only [ite_eq_left hf]
      refine nonspawnResult_bind (nonspawn_charge Gas.veryLow evm.dyna) ?_
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
    by_cases hf : evm.sta.benvStat.rules.opcodes.stackAccess = true
    · simp only [ite_eq_left hf]
      refine nonspawnResult_bind (nonspawn_charge Gas.veryLow evm.dyna) ?_
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
    | .next _ post =>
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
      | halt l =>
          simp only [Evm.step, hi]
          exact HaltOp.run_memory_accounting_output evm.sta evm.dyna l hstate



/-! ### The spawn of a call, and what `resume` hands back -/

/-- A call that cannot go deeper pushes its status and spawns nothing. -/
private theorem push_done_ne_spawn (d : Devm) (c : Frame) (p : Pending) :
    MessageOp.Outcome.ofExcept (do
      let devm ← d.push 0
      return MessageOp.Outcome.done (.ok devm)) ≠ .spawn c p := by
  cases d.push 0 <;> simp [MessageOp.Outcome.ofExcept, bind, Except.bind, pure, Except.pure]

/-- A call's spawn: the child's gas is the grant, the checkpoint is the caller with its return
data cleared, and the caller waits on its output window. -/
theorem genericCall.step_spawn_call {sevm : Sevm} {parent : Devm} {gas : Nat}
    {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (h : genericCall.step sevm parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending) :
    child.message.gas = gas ∧
      child.checkpoint = Frame.State.ofDevm (parent.withReturnData []) ∧
      pending = ⟨.call outputIndex outputSize, false, (parent.withReturnData []).output,
        (parent.withReturnData []).error⟩ := by
  unfold genericCall.step at h
  split at h
  · exact absurd h (push_done_ne_spawn _ _ _)
  · cases h
    exact ⟨rfl, rfl, rfl⟩

/-- A call's child runs under its caller's block and transaction records. -/
theorem genericCall.step_spawn_context {sevm : Sevm} {parent : Devm} {gas : Nat}
    {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (h : genericCall.step sevm parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending) :
    child.message.context.block = sevm.benvStat ∧ child.message.context.tx = sevm.tenvStat := by
  unfold genericCall.step at h
  split at h
  · exact absurd h (push_done_ne_spawn _ _ _)
  · cases h
    exact ⟨rfl, rfl⟩

/-- A call's child receives the requested input window of its caller's memory. -/
theorem genericCall.step_spawn_data {sevm : Sevm} {parent : Devm} {gas : Nat}
    {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (h : genericCall.step sevm parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending) :
    child.message.context.calldata =
      Jaune.Array.sliceD (parent.withReturnData []).memory.data inputIndex inputSize 0 := by
  unfold genericCall.step at h
  split at h
  · exact absurd h (push_done_ne_spawn _ _ _)
  · cases h
    rfl

/-- The spawned call's input has the requested length, even when reading beyond the caller's
materialized memory. -/
theorem genericCall.step_spawn_data_length {sevm : Sevm} {parent : Devm} {gas : Nat}
    {value : U256} {caller target codeAddress : Address}
    {shouldTransferValue isStaticcall : Bool}
    {inputIndex inputSize outputIndex outputSize : Nat}
    {code : ByteArray} {disablePrecompiles : Bool} {child : Frame} {pending : Pending}
    (h : genericCall.step sevm parent gas value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending) :
    child.message.context.calldata.length = inputSize := by
  rw [genericCall.step_spawn_data h]
  exact memory_slice_length _ _ _ _

/-- The caller state `resume` hands back, on either channel. -/
private def resumedDevm : Except (ExceptionalHalt × Devm) Devm → Devm
  | .ok d => d
  | .error failure => failure.2

/-- `resume` merges the child into the saved caller and either pushes the status (and for a
call writes the output window) or halts on a full stack with the merged state. -/
private theorem resume_shape {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Devm) Devm}
    (h : resume rules p saved r = .ok x) :
    ∃ s : Frame.State, s.machine = absorbMeters rules p saved.machine r ∧
      (x = .ok (p.restore { s with machine := p.target.finish r s.machine }) ∨
        x = .error (.stackOverflow .none, p.restore s)) := by
  unfold resume at h
  simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; exact ⟨⟨_, _, _, _⟩, rfl, Or.inl rfl⟩)
    | (cases h; exact ⟨⟨_, _, _, _⟩, rfl, Or.inr rfl⟩)
    | cases h

private theorem resumedDevm_gasMeasure (x : Except (ExceptionalHalt × Devm) Devm) :
    (resumedDevm x).gasMeasure = haltGas x := by
  rcases x with ⟨_, d⟩ | d <;> rfl

private theorem absorbMeters_memory (rules : ForkRules) (p : Pending) (m : Machine)
    (r : Frame.Result) : (absorbMeters rules p m r).memory = m.memory := by
  unfold absorbMeters Machine.creditStateGasRefund Machine.repayStateGasSpill
  repeat' split
  all_goals rfl

private theorem absorbMeters_returnData (rules : ForkRules) (p : Pending) (m : Machine)
    (r : Frame.Result) :
    (absorbMeters rules p m r).returnData = match p.target, r.failed with
      | .create _, false => []
      | _, _ => r.output := by
  unfold absorbMeters Machine.creditStateGasRefund Machine.repayStateGasSpill
  rcases ht : p.target with ⟨outputIndex, outputSize⟩ | address <;>
    cases hf : r.failed <;> simp only [hf] <;> split <;> (try split) <;> (try split) <;> rfl

private theorem finish_returnData (target : ReturnTarget) (r : Frame.Result) (m : Machine) :
    (target.finish r m).returnData = m.returnData := by
  cases target <;> rfl

private theorem finish_memory (target : ReturnTarget) (r : Frame.Result) (m : Machine) :
    (target.finish r m).memory = match target with
      | .call outputIndex outputSize => m.memory.write outputIndex (r.output.take outputSize)
      | .create _ => m.memory := by
  cases target <;> rfl

/-- The memory, output and return data `resume` hands its caller on either channel: the saved
memory with the calling opcode's effect on a pushed caller, the output the caller had when it
spawned, and the return data the meters merge installs. -/
private theorem resume_fields {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Devm) Devm}
    (h : resume rules p saved r = .ok x) :
    (resumedDevm x).output = p.legacyOutput ∧
      (resumedDevm x).returnData = (match p.target, r.failed with
        | .create _, false => []
        | _, _ => r.output) ∧
      (∀ d, x = .ok d → d.memory = (p.target.finish r saved.machine).memory) ∧
      (∀ e d, x = .error (e, d) → d.memory = saved.machine.memory) := by
  obtain ⟨s, hs, hx | hx⟩ := resume_shape h <;> subst hx
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · change (p.target.finish r s.machine).returnData = _
      rw [finish_returnData, hs, absorbMeters_returnData]
    · intro d hd
      cases hd
      change (p.target.finish r s.machine).memory = _
      rw [finish_memory, finish_memory, hs, absorbMeters_memory]
    · intro e d hd
      cases hd
  · refine ⟨rfl, ?_, ?_, ?_⟩
    · change s.machine.returnData = _
      rw [hs, absorbMeters_returnData]
    · intro d hd
      cases hd
    · intro e d hd
      cases hd
      change s.machine.memory = _
      rw [hs, absorbMeters_memory]

/-- A pushed call writes the child's output into the caller's output window: the counterpart of
the old chain's `Resume.call_run_ok_memory`. It holds under every rule set. -/
theorem resume_call_ok_memory {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {resumed : Devm} {outputIndex outputSize : Nat}
    (htarget : p.target = .call outputIndex outputSize)
    (h : resume rules p saved r = .ok (.ok resumed)) :
    resumed.memory = saved.machine.memory.write outputIndex (r.output.take outputSize) := by
  rw [(resume_fields h).2.2.1 resumed rfl, finish_memory, htarget]

/-! ### Spawn accounting -/

/-- `resume` keeps the caller's memory size when a call's output window was paid for. -/
private theorem resume_memory_size {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Devm) Devm}
    (h : resume rules p saved r = .ok x)
    (hwindow : ∀ outputIndex outputSize, p.target = .call outputIndex outputSize →
      outputSize ≠ 0 → outputIndex + outputSize ≤ saved.machine.memory.size) :
    (resumedDevm x).memory.size = saved.machine.memory.size := by
  have hf := resume_fields h
  rcases x with ⟨e, d⟩ | d
  · exact congrArg Mem.size (hf.2.2.2 e d rfl)
  · change d.memory.size = _
    rw [hf.2.2.1 d rfl, finish_memory]
    rcases ht : p.target with ⟨outputIndex, outputSize⟩ | address
    · dsimp only
      apply Mem.write_size_of_prepaid
      intro hcopy
      have hsize : outputSize ≠ 0 := by
        intro hz
        rw [hz, List.take_zero] at hcopy
        exact hcopy rfl
      have hlength : (r.output.take outputSize).length ≤ outputSize := by
        rw [List.length_take]
        exact Nat.min_le_left _ _
      exact Nat.le_trans (Nat.add_le_add_left hlength outputIndex)
        (hwindow outputIndex outputSize ht hsize)
    · rfl

/-- What `resume` hands a caller stays within the caller's potential plus the child's
allowance, and keeps the output the caller had when it spawned. -/
private theorem resume_allowance {rules : ForkRules} {p : Pending} {parent : Devm}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Devm) Devm} {grant : Nat}
    (h : resume rules p (Frame.State.ofDevm parent) r = .ok x)
    (houtput : p.legacyOutput = parent.output)
    (hwindow : ∀ outputIndex outputSize, p.target = .call outputIndex outputSize →
      outputSize ≠ 0 → outputIndex + outputSize ≤ parent.memory.size)
    (hchild : r.gasMeasure ≤ grant) :
    allowancePreserved parent grant (resumedDevm x) := by
  have hg := resume_gasLe h
  rw [← resumedDevm_gasMeasure, Frame.State.gasMeasure_ofDevm] at hg
  have hs := resume_memory_size h hwindow
  refine ⟨?_, (resume_fields h).1.trans houtput⟩
  change (resumedDevm x).memory.size = parent.memory.size at hs
  rw [hs]
  omega

private def spawnAccounting (pre : Devm) (allowance : Nat) : MessageOp.Outcome → Prop
  | .done _ => True
  | .spawn child pending =>
      child.checkpoint.gasMeasure + calculateMemoryGasCost child.checkpoint.machine.memory.size ≤
          pre.gasMeasure + calculateMemoryGasCost pre.memory.size + allowance ∧
        ∀ (rules : ForkRules) (r : Frame.Result), r.gasMeasure ≤ child.message.gas →
          ∀ x, resume rules pending child.checkpoint r = .ok x →
            allowancePreserved pre allowance (resumedDevm x)

private def spawnResult (pre : Devm) (allowance : Nat)
    (raw : Except (EvmError × Devm) MessageOp.Outcome) : Prop :=
  match raw with
  | .error _ => True
  | .ok step => spawnAccounting pre allowance step

private theorem spawnAccounting_rebase {pre middle : Devm} {inner outer : Nat}
    {step : MessageOp.Outcome}
    (hp : middle.gasMeasure + calculateMemoryGasCost middle.memory.size + inner ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + outer)
    (ho : middle.output = pre.output) (h : spawnAccounting middle inner step) :
    spawnAccounting pre outer step := by
  cases step with
  | done raw => trivial
  | spawn child pending =>
      refine ⟨Nat.le_trans h.1 hp, ?_⟩
      intro rules r hchild x hx
      exact allowance_rebase hp ho (h.2 rules r hchild x hx)

private theorem spawnResult_rebase {pre middle : Devm} {inner outer : Nat}
    {raw : Except (EvmError × Devm) MessageOp.Outcome}
    (hp : middle.gasMeasure + calculateMemoryGasCost middle.memory.size + inner ≤
      pre.gasMeasure + calculateMemoryGasCost pre.memory.size + outer)
    (ho : middle.output = pre.output) (h : spawnResult middle inner raw) :
    spawnResult pre outer raw := by
  cases raw with
  | error failure => trivial
  | ok step => exact spawnAccounting_rebase hp ho h

private theorem spawnResult_bind {α : Type} {pre : Devm} {allowance : Nat}
    {first : Except (EvmError × Devm) α} {next : α → Except (EvmError × Devm) MessageOp.Outcome}
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
    {raw : Except (EvmError × Devm) MessageOp.Outcome} (h : spawnResult pre allowance raw) :
    spawnAccounting pre allowance (MessageOp.Outcome.ofExcept raw) := by
  cases raw with
  | error failure => trivial
  | ok step => exact h

private theorem spawnResult_charged_memory (pairs : List (Nat × Nat)) (baseCost : Nat)
    (pre : Devm) (action : Devm → Except (EvmError × Devm) MessageOp.Outcome)
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
    (action : Devm → Except (EvmError × Devm) MessageOp.Outcome)
    (hbody : ∀ charged, spawnResult (charged.memExtends pairs) refund (action charged)) :
    spawnResult pre 0 (chargeGas (cost + pre.extCost pairs) pre >>= action) := by
  refine spawnResult_charged_memory pairs cost pre action ?_
  intro charged
  exact spawnResult_rebase (pre := charged.memExtends pairs)
    (middle := charged.memExtends pairs) (inner := refund) (outer := cost)
    (Nat.add_le_add_left hrefund _) rfl (hbody charged)

private theorem spawnResult_done_push (word : U256) (pre : Devm) (allowance : Nat)
    (reference : Devm) :
    spawnResult reference allowance (do
      let post ← pre.push word
      pure (.done (.ok post))) := by
  cases pre.push word <;> trivial


private theorem genericCall_spawn_allowance
    (sevm : Sevm) (pre : Devm) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (transfer staticCall : Bool)
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
  · refine ⟨?_, ?_⟩
    · change (pre.withReturnData []).gasMeasure +
          calculateMemoryGasCost (pre.withReturnData []).memory.size ≤ _
      simp only [Devm.withReturnData_gasMeasure]
      exact Nat.le_add_right _ _
    · intro rules r hchild x hx
      refine resume_allowance (parent := pre.withReturnData []) hx rfl ?_ hchild
      intro i s ht hs
      change ReturnTarget.call outputIndex outputSize = ReturnTarget.call i s at ht
      cases ht
      exact hwindow hs

private theorem genericCreate_spawn_accounting
    (sevm : Sevm) (pre : Devm) (endowment : U256)
    (newAddress : Address) (memoryIndex memorySize : Nat) :
    spawnAccounting pre 0
      (genericCreate.step sevm pre endowment newAddress memoryIndex memorySize) := by
  unfold genericCreate.step
  apply spawnAccounting_ofExcept
  refine spawnResult_bind
    (nonspawn_assert (sevm.benvStat.rules.creation.initCodeLimit →
        memorySize ≤ sevm.benvStat.rules.code.maxInitCodeSize)
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
  by_cases hfail : (current.state.get sevm.currentTarget).balance < endowment ∨
      (current.state.get sevm.currentTarget).nonce = UInt64.max ∨ sevm.depth = 0
  · dsimp only [current, withheld, grant] at hfail
    simp only [ite_eq_left hfail]
    exact spawnResult_done_push 0 (current.withGasLeft (current.gasLeft + grant)) 0 pre
  · dsimp only [current, withheld, grant] at hfail
    simp only [ite_eq_right hfail]
    let accessed := addAccessedAddress (current.incrNonce sevm.currentTarget) newAddress
    by_cases hcollision : (accessed.state.get newAddress).nonce ≠ (0 : UInt64) ∨
        (accessed.state.get newAddress).code.size ≠ 0
    · dsimp only [accessed, current, withheld, grant] at hcollision
      simp only [ite_eq_left hcollision]
      exact spawnResult_done_push 0 accessed 0 pre
    · dsimp only [accessed, current, withheld, grant] at hcollision
      simp only [ite_eq_right hcollision]
      refine ⟨?_, ?_⟩
      · change accessed.gasMeasure + calculateMemoryGasCost accessed.memory.size ≤ _
        dsimp only [accessed, current, withheld]
        simp only [addAccessedAddress_gasMeasure, Devm.incrNonce_gasMeasure,
          Devm.withReturnData_gasMeasure, Devm.withGasLeft_gasMeasure]
        change (pre.gasLeft - grant + pre.spill) +
          calculateMemoryGasCost pre.memory.size ≤
          pre.gasMeasure + calculateMemoryGasCost pre.memory.size + 0
        have hm := Devm.gasMeasure_eq pre
        omega
      intro rules r hchild x hx
      have hr : allowancePreserved accessed grant (resumedDevm x) :=
        resume_allowance hx rfl (fun i s ht => by cases ht) hchild
      apply allowance_rebase (pre := pre) (middle := accessed)
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

private theorem executable_spawn_accounting (sevm : Sevm) (pre : Devm) (x : MessageOp)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    spawnAccounting pre 0 (MessageOp.step sevm pre x) := by
  cases x <;> simp only [MessageOp.step, hstate]
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
      (if sevm.benvStat.rules.creation.initCodeLimit then
        Gas.initcodeWordCost * ceilDiv memorySize.1 32 else 0)]
    refine spawnResult_charged_memory [(memoryIndex.1, memorySize.1)]
      (sevm.benvStat.rules.gas.createAccess + if sevm.benvStat.rules.creation.initCodeLimit then
        Gas.initcodeWordCost * ceilDiv memorySize.1 32 else 0)
      memorySize.2 _ ?_
    intro charged
    refine spawnAccounting_rebase (pre := charged.memExtends [(memoryIndex.1, memorySize.1)])
      (inner := 0) ?_ rfl
      (genericCreate_spawn_accounting sevm _ endowment.1 _ memoryIndex.1 memorySize.1)
    omega
  case create2 =>
    by_cases hf : sevm.benvStat.rules.opcodes.create2 = true
    · simp only [ite_eq_left hf]
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
        (sevm.benvStat.rules.gas.createAccess + Gas.keccak256Word * ceilDiv memorySize.1 32)
        (salt.2.extCost [(memoryIndex.1, memorySize.1)])
        (if sevm.benvStat.rules.creation.initCodeLimit then
          Gas.initcodeWordCost * ceilDiv memorySize.1 32 else 0)]
      refine spawnResult_charged_memory [(memoryIndex.1, memorySize.1)]
        (sevm.benvStat.rules.gas.createAccess + Gas.keccak256Word * ceilDiv memorySize.1 32 +
          if sevm.benvStat.rules.creation.initCodeLimit then
            Gas.initcodeWordCost * ceilDiv memorySize.1 32 else 0)
        salt.2 _ ?_
      intro charged
      refine spawnAccounting_rebase (pre := charged.memExtends [(memoryIndex.1, memorySize.1)])
        (inner := 0) ?_ rfl
        (genericCreate_spawn_accounting sevm _ endowment.1 _ memoryIndex.1 memorySize.1)
      omega
    · simp only [ite_eq_right hf]
      apply spawnAccounting_ofExcept
      trivial
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
    -- The access step of either shape: a price `price` and a recorder `dA`.
    rcases hA : sevm.benvStat.rules.access with g | _
    on_goal 1 =>
      let price := g.call
      let dA := outputSize.2
      have hdA : nonspawnPreserved outputSize.2 dA := ⟨Nat.le_refl _, rfl⟩
    on_goal 2 =>
      let price := sevm.benvStat.rules.gas.accessCost codeAddress.1 outputSize.2.accessedAddresses
      let dA := addAccessedAddress outputSize.2 codeAddress.1
      have hdA := nonspawn_addAccessedAddress outputSize.2 codeAddress.1
    all_goals
      let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
      let lookup := sevm.benvStat.rules.accessDelegation
        dA codeAddress.1
      let parent := lookup.2.2.2.2
      have hp : nonspawnPreserved outputSize.2 parent :=
        nonspawnPreserved_trans hdA
          (nonspawn_rules_delegation sevm.benvStat.rules _ codeAddress.1)
      refine spawnResult_rebase (pre := outputSize.2) (middle := parent)
        (inner := 0) (outer := 0) hp.1 hp.2 ?_
      have hm : parent.memory = outputSize.2.memory :=
        (rules_delegation_memory_output sevm.benvStat.rules
          dA codeAddress.1).1
      have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
        simp only [Devm.extCost, hm]
      change spawnResult parent 0 (chargeGas
        ((calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (outputSize.2.extCost pairs)
          (price +
            lookup.2.2.2.1)).1 + outputSize.2.extCost pairs) parent >>= _)
      rw [hext]
      let costs := calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (parent.extCost pairs)
        (price +
          lookup.2.2.2.1)
      refine spawnResult_charged_call pairs costs.1 costs.2 parent ?_ _ ?_
      · exact calculateMsgCallGas_refund_le_base 0 gas.1.toNat parent.gasLeft
          (parent.extCost pairs)
          (price +
            lookup.2.2.2.1) Gas.callStipend (Nat.zero_le _)
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
    -- The access step of either shape: a price `price` and a recorder `dA`.
    rcases hA : sevm.benvStat.rules.access with g | _
    on_goal 1 =>
      let price := g.call
      let dA := outputSize.2
      have hdA : nonspawnPreserved outputSize.2 dA := ⟨Nat.le_refl _, rfl⟩
    on_goal 2 =>
      let price := sevm.benvStat.rules.gas.accessCost target.1 outputSize.2.accessedAddresses
      let dA := addAccessedAddress outputSize.2 target.1
      have hdA := nonspawn_addAccessedAddress outputSize.2 target.1
    all_goals
      let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
      let lookup := sevm.benvStat.rules.accessDelegation
        dA target.1
      let parent := lookup.2.2.2.2
      have hp : nonspawnPreserved outputSize.2 parent :=
        nonspawnPreserved_trans hdA
          (nonspawn_rules_delegation sevm.benvStat.rules _ target.1)
      refine spawnResult_rebase (pre := outputSize.2) (middle := parent)
        (inner := 0) (outer := 0) hp.1 hp.2 ?_
      have hm : parent.memory = outputSize.2.memory :=
        (rules_delegation_memory_output sevm.benvStat.rules
          dA target.1).1
      have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
        simp only [Devm.extCost, hm]
      change spawnResult parent 0 (chargeGas
        ((calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (outputSize.2.extCost pairs)
          (price +
            lookup.2.2.2.1)).1 + outputSize.2.extCost pairs) parent >>= _)
      rw [hext]
      let costs := calculateMsgCallGas 0 gas.1.toNat parent.gasLeft (parent.extCost pairs)
        (price +
          lookup.2.2.2.1)
      refine spawnResult_charged_call pairs costs.1 costs.2 parent ?_ _ ?_
      · exact calculateMsgCallGas_refund_le_base 0 gas.1.toNat parent.gasLeft
          (parent.extCost pairs)
          (price +
            lookup.2.2.2.1) Gas.callStipend (Nat.zero_le _)
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
    -- The access step of either shape: a price `price` and a recorder `dA`.
    rcases hA : sevm.benvStat.rules.access with g | _
    on_goal 1 =>
      let price := g.call
      let dA := outputSize.2
      have hdA : nonspawnPreserved outputSize.2 dA := ⟨Nat.le_refl _, rfl⟩
    on_goal 2 =>
      let price := sevm.benvStat.rules.gas.accessCost callee.1 outputSize.2.accessedAddresses
      let dA := addAccessedAddress outputSize.2 callee.1
      have hdA := nonspawn_addAccessedAddress outputSize.2 callee.1
    all_goals
      let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
      let lookup := sevm.benvStat.rules.accessDelegation
        dA callee.1
      let parent := lookup.2.2.2.2
      have hp : nonspawnPreserved outputSize.2 parent :=
        nonspawnPreserved_trans hdA
          (nonspawn_rules_delegation sevm.benvStat.rules _ callee.1)
      refine spawnResult_rebase (pre := outputSize.2) (middle := parent)
        (inner := 0) (outer := 0) hp.1 hp.2 ?_
      have hm : parent.memory = outputSize.2.memory :=
        (rules_delegation_memory_output sevm.benvStat.rules
          dA callee.1).1
      have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
        simp only [Devm.extCost, hm]
      let accessCost := price + lookup.2.2.2.1
      let createCost : Nat := if ¬(parent.getAcct callee.1).isEmpty ∨ value.1 = 0 then 0 else Gas.newAccount
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
        by_cases hb : (paid.getAcct sevm.currentTarget).balance < value.1
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
    -- The access step of either shape: a price `price` and a recorder `dA`.
    rcases hA : sevm.benvStat.rules.access with g | _
    on_goal 1 =>
      let price := g.call
      let dA := outputSize.2
      have hdA : nonspawnPreserved outputSize.2 dA := ⟨Nat.le_refl _, rfl⟩
    on_goal 2 =>
      let price := sevm.benvStat.rules.gas.accessCost codeAddress.1 outputSize.2.accessedAddresses
      let dA := addAccessedAddress outputSize.2 codeAddress.1
      have hdA := nonspawn_addAccessedAddress outputSize.2 codeAddress.1
    all_goals
      let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
      let lookup := sevm.benvStat.rules.accessDelegation
        dA codeAddress.1
      let parent := lookup.2.2.2.2
      have hp : nonspawnPreserved outputSize.2 parent :=
        nonspawnPreserved_trans hdA
          (nonspawn_rules_delegation sevm.benvStat.rules _ codeAddress.1)
      refine spawnResult_rebase (pre := outputSize.2) (middle := parent)
        (inner := 0) (outer := 0) hp.1 hp.2 ?_
      have hm : parent.memory = outputSize.2.memory :=
        (rules_delegation_memory_output sevm.benvStat.rules
          dA codeAddress.1).1
      have hext : outputSize.2.extCost pairs = parent.extCost pairs := by
        simp only [Devm.extCost, hm]
      let accessCost := price + lookup.2.2.2.1
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
        by_cases hb : (paid.getAcct sevm.currentTarget).balance < value.1
        · dsimp only [paid, pairs] at hb
          simp only [ite_eq_left hb]
          cases hp : paid.push 0 <;> trivial
        · dsimp only [paid, pairs] at hb
          simp only [ite_eq_right hb]
          exact genericCall_spawn_allowance sevm paid costs.2 value.1
            sevm.currentTarget sevm.currentTarget lookup.2.1 true false
            inputIndex.1 inputSize.1 outputIndex.1 outputSize.1 lookup.2.2.1 lookup.1
            (call_output_window charged inputIndex.1 inputSize.1 outputIndex.1 outputSize.1)


/-! ### The driver -/

/-- Only a message opcode spawns. -/
private theorem evm_step_spawn_inv {evm : Evm} {child : Frame} {pending : Pending} {pc' : Nat}
    (h : Evm.step evm = .spawn child pending pc') :
    ∃ x, MessageOp.step evm.sta evm.dyna x = .spawn child pending := by
  have ofExecution_ne : ∀ {pc : Nat} {e : Execution}, Step.ofExecution pc e ≠ .spawn child pending pc' := by
    intro pc e
    cases e <;> simp [Step.ofExecution]
  unfold Evm.step at h
  split at h
  · cases h
  · next n _ =>
      unfold NextOp.step at h
      rcases n with r | x | ⟨xs, hxs⟩ | a | a | a <;> dsimp only at h
      · exact absurd h ofExecution_ne
      · refine ⟨x, ?_⟩
        rcases hx : MessageOp.step evm.sta evm.dyna x with ex | ⟨c, q⟩
        · rw [hx] at h
          exact absurd h ofExecution_ne
        · rw [hx] at h
          cases h
          rfl
      · split at h <;> exact absurd h ofExecution_ne
      · exact absurd h ofExecution_ne
      · exact absurd h ofExecution_ne
      · exact absurd h ofExecution_ne
  · next j _ =>
      rcases hj : j.run evm with e | ⟨pc, d⟩ <;> rw [hj] at h <;> cases h
  · cases h

private theorem step_spawn_resume_accounting
    (evm : Evm) (hstate : evm.sta.benvStat.rules.stateGas = none)
    {child : Frame} {pending : Pending} {pc' : Nat}
    (hspawn : Evm.step evm = .spawn child pending pc') :
    spawnAccounting evm.dyna 0 (.spawn child pending) := by
  obtain ⟨x, hx⟩ := evm_step_spawn_inv hspawn
  have ha := executable_spawn_accounting evm.sta evm.dyna x hstate
  rw [hx] at ha
  exact ha

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

/-- The accounting of a raw result the driver ends in after a spawn: a fault carries the
spawning frame's checkpoint, and a halted or continued caller carries what `resume` handed
back. -/
private theorem spawn_fault_accounted {pre : Devm} {child : Frame} {pending : Pending}
    (h : spawnAccounting pre 0 (.spawn child pending)) (fault : Fault) :
    rawTerminalAccounted pre (.error (fault.toEvmError, child.checkpoint.toDevm)) := by
  refine ⟨?_, Or.inr ?_⟩
  · have h1 := h.1
    change child.checkpoint.toDevm.gasMeasure +
      calculateMemoryGasCost child.checkpoint.machine.memory.size ≤ _
    rw [Frame.State.toDevm_gasMeasure]
    omega
  · change calculateMemoryGasCost 0 ≤ _
    exact Nat.zero_le _

private theorem execFueled_memory_accounting :
    ∀ (fuel : Nat) (evm : Evm), evm.sta.benvStat.rules.stateGas = none →
      ∀ {raw : Execution}, (execFueled evm fuel).run = some raw →
        rawTerminalAccounted evm.dyna raw := by
  intro fuel
  induction fuel with
  | zero =>
      intro evm _ raw hrun
      rw [execFueled] at hrun
      simp only [Fueled.exhausted_run] at hrun
      nomatch hrun
  | succ fuel ih =>
      intro evm hstate raw hrun
      have hs : stepAccounted evm.dyna (Evm.step evm) :=
        Evm.step_memory_accounting_output evm hstate
      rw [execFueled] at hrun
      rcases hstep : Evm.step evm with ex | ⟨pc, devm⟩ | ⟨child, pending, pc'⟩ <;>
        rw [hstep] at hrun hs <;> dsimp only at hrun
      · simp only [Fueled.ofExcept_run, Option.some.injEq] at hrun
        rw [← hrun]
        exact hs
      · exact raw_accounting_trans hs (ih ⟨pc, evm.sta, devm⟩ hstate hrun)
      · have hsp := step_spawn_resume_accounting evm hstate hstep
        -- What the driver does with the child's result `r`, whose measure is bounded by the
        -- child's gas.
        have hcont : ∀ r : Frame.Result, r.gasMeasure ≤ child.message.gas →
            (match resume evm.sta.benvStat.rules pending child.checkpoint r with
              | .error fault =>
                Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
              | .ok (.error (reason, devm)) => Fueled.ofExcept (.error (.halt reason, devm))
              | .ok (.ok devm) => execFueled ⟨pc', evm.sta, devm⟩ fuel).run = some raw →
            rawTerminalAccounted evm.dyna raw := by
          intro r hr hrun
          rcases hx : resume evm.sta.benvStat.rules pending child.checkpoint r with
            fault | ⟨⟨reason, devm⟩ | devm⟩ <;> rw [hx] at hrun <;> dsimp only at hrun
          · simp only [Fueled.ofExcept_run, Option.some.injEq] at hrun
            rw [← hrun]
            exact spawn_fault_accounted hsp fault
          · simp only [Fueled.ofExcept_run, Option.some.injEq] at hrun
            rw [← hrun]
            have ha : allowancePreserved evm.dyna 0 devm := hsp.2 _ r hr _ hx
            exact ⟨by simpa only [Nat.add_zero] using ha.1, Or.inl ha.2⟩
          · have ha : allowancePreserved evm.dyna 0 devm := hsp.2 _ r hr _ hx
            exact raw_accounting_trans
              ⟨by simpa only [Nat.add_zero] using ha.1, ha.2⟩
              (ih ⟨pc', evm.sta, devm⟩ hstate hrun)
        rcases he : enter child with cevm | result <;> rw [he] at hrun <;> dsimp only at hrun
        · rcases hc : (execFueled cevm fuel).run with _ | raw2 <;> rw [hc] at hrun <;>
            dsimp only [Option.map] at hrun
          · simp only [Fueled.exhausted_run] at hrun
            nomatch hrun
          · have hsettled := execFueled_settledGasLe fuel cevm hc
            rw [enter_run_gasMeasure he] at hsettled
            rcases hset : settle child raw2 with fault | r <;> rw [hset] at hrun <;>
              dsimp only at hrun
            · simp only [Fueled.ofExcept_run, Option.some.injEq] at hrun
              rw [← hrun]
              exact spawn_fault_accounted hsp fault
            · exact hcont r (settle_gasLe hsettled hset) hrun
        · rcases result with fault | r
          · simp only [Fueled.ofExcept_run, Option.some.injEq] at hrun
            rw [← hrun]
            exact spawn_fault_accounted hsp fault
          · exact hcont r (enter_done_gasLe he) hrun

/-- A run of the driver preserves the memory/gas potential, and its full raw output is
inherited or paid by the initial potential on both channels: the counterpart, over the
driver, of the old chain's `Exec.memory_accounting_output`. A fault carries the spawning
frame's checkpoint, which has no output. -/
theorem execFueled_memory_accounting_output {fuel : Nat} {evm : Evm} {raw : Execution}
    (hrun : (execFueled evm fuel).run = some raw)
    (hstate : evm.sta.benvStat.rules.stateGas = none) :
    let initial := evm.dyna.gasMeasure + calculateMemoryGasCost evm.dyna.memory.size
    let accounted := fun post : Devm =>
      post.gasMeasure + calculateMemoryGasCost post.memory.size ≤ initial ∧
        (post.output = evm.dyna.output ∨ calculateMemoryGasCost post.output.length ≤ initial)
    match raw with
    | .ok post => accounted post
    | .error failure => accounted failure.2 := by
  cases raw with
  | error failure => exact execFueled_memory_accounting fuel evm hstate hrun
  | ok post => exact execFueled_memory_accounting fuel evm hstate hrun

/-- The total interpreter preserves the memory/gas potential, and its full raw output is
inherited or paid by the initial potential on both channels. -/
theorem exec_memory_accounting_output {evm : Evm}
    (hstate : evm.sta.benvStat.rules.stateGas = none) :
    let initial := evm.dyna.gasMeasure + calculateMemoryGasCost evm.dyna.memory.size
    let accounted := fun post : Devm =>
      post.gasMeasure + calculateMemoryGasCost post.memory.size ≤ initial ∧
        (post.output = evm.dyna.output ∨ calculateMemoryGasCost post.output.length ≤ initial)
    match exec evm with
    | .ok post => accounted post
    | .error failure => accounted failure.2 := by
  have hrun := execFueled_run_sufficientFuel evm
  generalize exec evm = raw at hrun ⊢
  cases raw with
  | error failure => exact execFueled_memory_accounting _ evm hstate hrun
  | ok post => exact execFueled_memory_accounting _ evm hstate hrun


/-! ### Entering and settling a child -/

/-- An entered child runs its message from an empty machine with no output. -/
private theorem enter_run_inv {f : Frame} {evm : Evm} (h : enter f = .run evm) :
    evm.pc = 0 ∧ evm.sta = f.message.sevm ∧ evm.dyna.output = [] ∧
      evm.dyna.memory.size = 0 := by
  unfold enter enterWith at h
  cases ht : f.message.transfer f.enteredWorld with
  | error fault => simp only [ht, reduceCtorEq] at h
  | ok world =>
    simp only [ht] at h
    cases hc : f.message.codeAddress with
    | none =>
      simp only [hc, Frame.Entry.run.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl, rfl⟩
    | some a =>
      simp only [hc] at h
      split at h
      · cases h
      · simp only [Frame.Entry.run.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl, rfl⟩

/-- A failed value transfer settles the child at entry, as a fault. -/
theorem enter_transfer_error {f : Frame} {fault : Fault}
    (h : f.message.transfer f.enteredWorld = .error fault) :
    enter f = .done (.error fault) := by
  simp only [enter, enterWith, h]

/-- A precompile target is run and settled at entry, on the machine the frame is entered with. -/
theorem enter_precompile {f : Frame} {world : World} {adr : Address}
    (htransfer : f.message.transfer f.enteredWorld = .ok world)
    (hcode : f.message.codeAddress = some adr)
    (hdispatch : (!f.message.disablePrecompiles &&
      f.message.context.block.rules.isPrecompile adr) = true) :
    enter f = .done (settle f (executePrecompile
      ⟨0, f.message.sevm, (f.start.setWorld world).withCreatedAccounts f.enteredCreatedAccounts⟩
      adr)) := by
  simp only [enter, enterWith, htransfer, hcode, hdispatch, ite_true]

/-- The precompile dispatch at entry keeps the native output bound on success: the counterpart
of the old chain's `executeCode_enter_native_ok_output_length_lt_two_pow_160`, whose
`executeCode.enter` is folded into `enter`. -/
theorem enter_native_ok_output_length_lt_two_pow_160 {f : Frame} {world : World}
    {adr : Address} {post : Devm}
    (hrun : executePrecompile
      ⟨0, f.message.sevm, (f.start.setWorld world).withCreatedAccounts f.enteredCreatedAccounts⟩
      adr = .ok post)
    (hdata : f.message.context.calldata.length < 2 ^ 160)
    (hgas : f.message.gas < 2 ^ 256 + Gas.callStipend) :
    post.output.length < 2 ^ 160 :=
  executePrecompile_ok_output_length_lt_two_pow_160 hrun hdata hgas

/-- A rejected precompile at entry carries the empty initial output: the counterpart of the old
chain's `executeCode_enter_native_error_output_nil`. -/
theorem enter_native_error_output_nil {f : Frame} {world : World} {adr : Address}
    {failure : EvmError × Devm}
    (hrun : executePrecompile
      ⟨0, f.message.sevm, (f.start.setWorld world).withCreatedAccounts f.enteredCreatedAccounts⟩
      adr = .error failure) :
    failure.2.output = [] := by
  unfold executePrecompile applyPrecompileResult at hrun
  split at hrun
  · cases hrun
    rfl
  · cases hrun

private def rawOutputLength (raw : Execution) : Nat :=
  match raw with
  | .ok post => post.output.length
  | .error failure => failure.2.output.length

/-- Settling can only shorten a frame's output. -/
private theorem settle_output_length_le {f : Frame} {raw : Execution} {r : Frame.Result}
    (h : settle f raw = .ok r) : r.output.length ≤ rawOutputLength raw := by
  unfold settle at h
  rcases raw with ⟨⟨reason⟩ | ⟨⟩ | ⟨reason⟩ | ⟨reason⟩, d⟩ | d
  · cases h
    exact Nat.zero_le _
  · cases h
    exact Nat.le_refl _
  · cases h
  · cases h
  · dsimp only at h
    split at h
    · cases h
      exact Nat.le_of_eq (congrArg List.length (Devm.recordTouch_output _ _ _ _))
    · split at h
      · cases h
        exact Nat.le_of_eq (congrArg List.length (Devm.recordTouch_output _ _ _ _))
      · cases h
        exact Nat.zero_le _

/-- The output an entered child's run leaves is paid for by the child's gas. -/
private theorem entered_code_output_cost {f : Frame} {child : Evm}
    (henter : enter f = .run child)
    (hstate : f.message.context.block.rules.stateGas = none) :
    calculateMemoryGasCost (rawOutputLength (exec child)) ≤ f.message.gas := by
  obtain ⟨_, hsta, hout, hmem⟩ := enter_run_inv henter
  have hinitial := enter_run_gasMeasure henter
  have hstate' : child.sta.benvStat.rules.stateGas = none := by
    rw [hsta]
    exact hstate
  have hc := exec_memory_accounting_output (evm := child) hstate'
  rw [hmem, hinitial] at hc
  generalize exec child = raw at hc ⊢
  rcases raw with failure | post
  · rcases hc.2 with inherited | paid
    · change calculateMemoryGasCost failure.2.output.length ≤ _
      rw [inherited, hout]
      exact Nat.zero_le _
    · have hz : calculateMemoryGasCost 0 = 0 := rfl
      change calculateMemoryGasCost failure.2.output.length ≤ _
      rw [hz, Nat.add_zero] at paid
      exact paid
  · rcases hc.2 with inherited | paid
    · change calculateMemoryGasCost post.output.length ≤ _
      rw [inherited, hout]
      exact Nat.zero_le _
    · have hz : calculateMemoryGasCost 0 = 0 := rfl
      change calculateMemoryGasCost post.output.length ≤ _
      rw [hz, Nat.add_zero] at paid
      exact paid


/-- The run of an entered child settles to a result within the child's gas. -/
private theorem settle_exec_gasLe {f : Frame} {child : Evm} {r : Frame.Result}
    (henter : enter f = .run child) (hs : settle f (exec child) = .ok r) :
    r.gasMeasure ≤ f.message.gas := by
  have hsettled := execFueled_settledGasLe _ child (execFueled_run_sufficientFuel child)
  rw [enter_run_gasMeasure henter] at hsettled
  exact settle_gasLe hsettled hs

/-- A call's resumed caller has the child's output as its return data. -/
private theorem call_resume_returnData {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {r : Frame.Result} {x : Except (ExceptionalHalt × Devm) Devm}
    {outputIndex outputSize : Nat} (htarget : p.target = .call outputIndex outputSize)
    (h : resume rules p saved r = .ok x) : (resumedDevm x).returnData = r.output := by
  rw [(resume_fields h).2.1, htarget]

/-! ### Zero-value calls: the child's run and the resumed caller -/

/-- The resumed caller of a real zero-value `CALL` whose child ran code: the child's settled
result is within the requested gas, the output window is written into the paid memory, and the
caller's potential, less the call's extra gas, is not raised. The counterpart of the old
chain's `zero_call_spawn_resume_accounting`; the child's derivation is its run by `exec`. -/
theorem zero_call_spawn_resume_accounting
    {sevm : Sevm} {before charged resumed : Devm} (gas : U256)
    (extraGas cs inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {childEvm : Evm} {rules : ForkRules}
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
        .spawn child pending)
    (henter : enter child = .run childEvm)
    (hresume : (settle child (exec childEvm) >>= resume rules pending child.checkpoint) =
      .ok (.ok resumed)) :
    ∃ r : Frame.Result, settle child (exec childEvm) = .ok r ∧
      r.gasMeasure ≤ gas.toNat ∧
      resumed.memory =
        (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)]).memory.write
          outputIndex (r.output.take outputSize) ∧
      resumed.memory.size =
        memExtsSize before.memory.size [(inputIndex, inputSize), (outputIndex, outputSize)] ∧
      resumed.gasMeasure + extraGas + calculateMemoryGasCost resumed.memory.size ≤
        before.gasMeasure + calculateMemoryGasCost before.memory.size := by
  let pairs := [(inputIndex, inputSize), (outputIndex, outputSize)]
  let costs := calculateMsgCallGas 0 gas.toNat before.gasLeft (before.extCost pairs) extraGas cs
  let parent := (charged.memExtends pairs).withReturnData []
  obtain ⟨hf, hcheck, hpending⟩ := genericCall.step_spawn_call hspawn
  change child.message.gas = costs.2 at hf
  rcases hsettle : settle child (exec childEvm) with fault | r
  · rw [hsettle] at hresume
    cases hresume
  rw [hsettle] at hresume
  change resume rules pending child.checkpoint r = .ok (.ok resumed) at hresume
  have hchild := settle_exec_gasLe henter hsettle
  rw [hf] at hchild
  have hcap := calculateMsgCallGas_zero_child_le gas.toNat before.gasLeft
    (before.extCost pairs) extraGas cs
  have hmem := resume_call_ok_memory (by rw [hpending]) hresume
  rw [hcheck] at hmem
  change resumed.memory = (charged.memExtends pairs).memory.write
    outputIndex (r.output.take outputSize) at hmem
  have hprepaid : (r.output.take outputSize) ≠ [] →
      outputIndex + (r.output.take outputSize).length ≤ parent.memory.size := by
    intro hnonempty
    have hsize : outputSize ≠ 0 := by
      intro hz
      subst outputSize
      exact hnonempty rfl
    have hw := memExtSize_access_le
      (memExtSize charged.memory.size inputIndex inputSize) outputIndex outputSize hsize
    have ht := List.length_take_le outputSize r.output
    change outputIndex + (r.output.take outputSize).length ≤
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
  have hgas := resume_gasLe hresume
  rw [hcheck, Frame.State.gasMeasure_ofDevm] at hgas
  change resumed.gasMeasure ≤ parent.gasMeasure + r.gasMeasure at hgas
  have hparent : parent.gasMeasure = (charged.memExtends pairs).gasMeasure := rfl
  refine ⟨r, rfl, Nat.le_trans hchild hcap, hmem, hsize, ?_⟩
  rw [hmemsize]
  omega

/-- The same zero-value `CALL` accounts for both of the caller's resumed channels, a pushed
caller and one halted by a full stack, with the caller's output kept. The counterpart of the
old chain's `zero_call_spawn_resume_raw_accounting`. A fault is not a caller channel on the
four-part chain: it ends the run, and the state it carries is the child's checkpoint. -/
theorem zero_call_spawn_resume_raw_accounting
    {sevm : Sevm} {before charged : Devm} (gas : U256)
    (extraGas cs inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {childEvm : Evm} {rules : ForkRules}
    {x : Except (ExceptionalHalt × Devm) Devm}
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
        .spawn child pending)
    (henter : enter child = .run childEvm)
    (hresume : (settle child (exec childEvm) >>= resume rules pending child.checkpoint) =
      .ok x) :
    let accounted := fun post : Devm =>
      post.gasMeasure + extraGas + calculateMemoryGasCost post.memory.size ≤
          before.gasMeasure + calculateMemoryGasCost before.memory.size ∧
        post.output = before.output
    match (generalizing := false) x with
    | .ok post => accounted post
    | .error failure => accounted failure.2 := by
  let pairs := [(inputIndex, inputSize), (outputIndex, outputSize)]
  let costs := calculateMsgCallGas 0 gas.toNat before.gasLeft (before.extCost pairs) extraGas cs
  let parent := (charged.memExtends pairs).withReturnData []
  obtain ⟨hf, hcheck, hpending⟩ := genericCall.step_spawn_call hspawn
  have hfields := charge_memory_output (costs.1 + before.extCost pairs) before
  rw [hcharge] at hfields
  have hparentOutput : parent.output = before.output := hfields.2
  rcases hsettle : settle child (exec childEvm) with fault | r
  · rw [hsettle] at hresume
    cases hresume
  rw [hsettle] at hresume
  change resume rules pending child.checkpoint r = .ok x at hresume
  rw [hcheck] at hresume
  have hchild := settle_exec_gasLe henter hsettle
  rw [hf] at hchild
  have ha : allowancePreserved parent costs.2 (resumedDevm x) := by
    refine resume_allowance hresume (by rw [hpending]) ?_ hchild
    intro i s ht hs
    rw [hpending] at ht
    change ReturnTarget.call outputIndex outputSize = ReturnTarget.call i s at ht
    cases ht
    have hw := memExtSize_access_le
      (memExtSize charged.memory.size inputIndex inputSize) outputIndex outputSize hs
    exact hw
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
  have hgoal : (resumedDevm x).gasMeasure + extraGas +
        calculateMemoryGasCost (resumedDevm x).memory.size ≤
        before.gasMeasure + calculateMemoryGasCost before.memory.size ∧
      (resumedDevm x).output = before.output := by
    refine ⟨?_, ha.2.trans hparentOutput⟩
    have h1 := ha.1
    omega
  rcases x with failure | post
  · exact hgoal
  · exact hgoal


/-! ### Return data after a call -/

private theorem output_length_lt_two_pow_160 {n grant : Nat}
    (hcost : calculateMemoryGasCost n ≤ grant) (hgrant : grant < 2 ^ 256) :
    n < 2 ^ 160 := by
  by_contra hn
  have hn' : 2 ^ 160 ≤ n := Nat.le_of_not_gt hn
  have hmono := calculateMemoryGasCost_mono hn'
  have hconstant : 2 ^ 256 ≤ calculateMemoryGasCost (2 ^ 160) := by decide
  omega

private theorem output_length_lt_two_pow_160_with_stipend {n grant : Nat}
    (hcost : calculateMemoryGasCost n ≤ grant)
    (hgrant : grant < 2 ^ 256 + Gas.callStipend) :
    n < 2 ^ 160 := by
  by_contra hn
  have hn' : 2 ^ 160 ≤ n := Nat.le_of_not_gt hn
  have hmono := calculateMemoryGasCost_mono hn'
  have hconstant : 2 ^ 256 + Gas.callStipend ≤
      calculateMemoryGasCost (2 ^ 160) := by decide
  omega

/-- The child of a real zero-value `CALL` that ran code has a paid full output below `2^160`;
settling only shortens it, and either resumed channel of the caller has return data below
`2^160`. The counterpart of the old chain's `zero_call_spawn_code_reply_bound`. -/
theorem zero_call_spawn_code_reply_bound
    {sevm : Sevm} {before charged : Devm} (gas : U256)
    (extraGas cs inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {childEvm : Evm} {rules : ForkRules}
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
        .spawn child pending)
    (henter : enter child = .run childEvm)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    let grant := (calculateMsgCallGas 0 gas.toNat before.gasLeft
      (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      extraGas cs).2
    let fullLength := (fun result : Execution => match result with
      | .ok post => post.output.length
      | .error failure => failure.2.output.length) (exec childEvm)
    calculateMemoryGasCost fullLength ≤ grant ∧ fullLength < 2 ^ 160 ∧
      (∀ r, settle child (exec childEvm) = .ok r → r.output.length < 2 ^ 160) ∧
      ∀ x, (settle child (exec childEvm) >>= resume rules pending child.checkpoint) = .ok x →
        let accounted := fun post : Devm =>
          post.returnData.length < 2 ^ 160 ∧
          post.gasMeasure + extraGas + calculateMemoryGasCost post.memory.size ≤
            before.gasMeasure + calculateMemoryGasCost before.memory.size ∧
          post.output = before.output
        match (generalizing := false) x with
        | .ok post => accounted post
        | .error failure => accounted failure.2 := by
  let pairs := [(inputIndex, inputSize), (outputIndex, outputSize)]
  let costs := calculateMsgCallGas 0 gas.toNat before.gasLeft (before.extCost pairs) extraGas cs
  obtain ⟨hf, hcheck, hpending⟩ := genericCall.step_spawn_call hspawn
  have hblock := (genericCall.step_spawn_context hspawn).1
  have hcost : calculateMemoryGasCost (rawOutputLength (exec childEvm)) ≤ child.message.gas :=
    entered_code_output_cost henter (by rw [hblock]; exact hstate)
  rw [hf] at hcost
  have hgrant : costs.2 < 2 ^ 256 :=
    calculateMsgCallGas_zero_word_child_lt gas before.gasLeft (before.extCost pairs) extraGas cs
  have hlength := output_length_lt_two_pow_160 hcost hgrant
  have hsettled : ∀ r, settle child (exec childEvm) = .ok r → r.output.length < 2 ^ 160 := by
    intro r hs
    exact Nat.lt_of_le_of_lt (settle_output_length_le hs) hlength
  refine ⟨?_, ?_, hsettled, ?_⟩
  · change calculateMemoryGasCost (rawOutputLength (exec childEvm)) ≤ _
    exact hcost
  · change rawOutputLength (exec childEvm) < _
    exact hlength
  intro x hx
  have haccount := zero_call_spawn_resume_raw_accounting gas extraGas cs inputIndex inputSize
    outputIndex outputSize hcharge hspawn henter hx
  rcases hsettle : settle child (exec childEvm) with fault | r
  · rw [hsettle] at hx
    cases hx
  rw [hsettle] at hx
  change resume rules pending child.checkpoint r = .ok x at hx
  have hrd := call_resume_returnData (by rw [hpending]) hx
  have hl := hsettled r hsettle
  have hret : (resumedDevm x).returnData.length < 2 ^ 160 := by
    rw [hrd]
    exact hl
  rcases x with failure | post
  · exact ⟨hret, haccount⟩
  · exact ⟨hret, haccount⟩

/-- A word-sized `CALL`'s child that ran code, with or without value, has a full output below
`2^160`; settling only shortens it, and either resumed channel of the caller has return data
below `2^160`. The counterpart of the old chain's `call_spawn_code_reply_bound`. -/
theorem call_spawn_code_reply_bound
    {sevm : Sevm} {parent : Devm} (gas value : U256)
    (gasLeft memoryCost extraGas inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {childEvm : Evm} {rules : ForkRules}
    (hspawn : genericCall.step sevm parent
      (calculateMsgCallGas value.toNat gas.toNat gasLeft memoryCost extraGas
        Gas.callStipend).2 value caller target codeAddress shouldTransferValue
      isStaticcall inputIndex inputSize outputIndex outputSize code
      disablePrecompiles = .spawn child pending)
    (henter : enter child = .run childEvm)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    (fun result : Execution => match result with
      | .ok post => post.output.length
      | .error failure => failure.2.output.length) (exec childEvm) < 2 ^ 160 ∧
      (∀ r, settle child (exec childEvm) = .ok r → r.output.length < 2 ^ 160) ∧
      ∀ x, (settle child (exec childEvm) >>= resume rules pending child.checkpoint) = .ok x →
        match (generalizing := false) x with
        | .ok post => post.returnData.length < 2 ^ 160
        | .error failure => failure.2.returnData.length < 2 ^ 160 := by
  obtain ⟨hf, _, hpending⟩ := genericCall.step_spawn_call hspawn
  have hblock := (genericCall.step_spawn_context hspawn).1
  have hcost : calculateMemoryGasCost (rawOutputLength (exec childEvm)) ≤ child.message.gas :=
    entered_code_output_cost henter (by rw [hblock]; exact hstate)
  have hgrant := calculateMsgCallGas_word_child_lt_with_stipend value gas gasLeft
    memoryCost extraGas
  have hlength : rawOutputLength (exec childEvm) < 2 ^ 160 := by
    apply output_length_lt_two_pow_160_with_stipend hcost
    rw [hf]
    exact hgrant
  have hsettled : ∀ r, settle child (exec childEvm) = .ok r → r.output.length < 2 ^ 160 := by
    intro r hs
    exact Nat.lt_of_le_of_lt (settle_output_length_le hs) hlength
  refine ⟨hlength, hsettled, ?_⟩
  intro x hx
  rcases hsettle : settle child (exec childEvm) with fault | r
  · rw [hsettle] at hx
    cases hx
  rw [hsettle] at hx
  change resume rules pending child.checkpoint r = .ok x at hx
  have hrd := call_resume_returnData (by rw [hpending]) hx
  have hret : (resumedDevm x).returnData.length < 2 ^ 160 := by
    rw [hrd]
    exact hsettled r hsettle
  rcases x with failure | post
  · exact hret
  · exact hret

/-- A failed value transfer never enters code or a precompile: the child settles at entry as a
fault, which ends the run, and the checkpoint the fault carries has the empty return data the
spawn installed. The counterpart of the old chain's `call_spawn_transfer_error_reply_bound`,
whose caller resumed on the failure; on the four-part chain a fault does not resume its caller. -/
theorem call_spawn_transfer_error_reply_bound
    {sevm : Sevm} {parent : Devm} (grant : Nat) (value : U256)
    (inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {fault : Fault}
    (hspawn : genericCall.step sevm parent grant value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending)
    (htransfer : child.message.transfer child.enteredWorld = .error fault) :
    enter child = .done (.error fault) ∧ child.checkpoint.toDevm.returnData = [] := by
  obtain ⟨_, hcheck, _⟩ := genericCall.step_spawn_call hspawn
  refine ⟨enter_transfer_error htransfer, ?_⟩
  rw [hcheck]
  rfl

/-! ### Native precompile replies -/

/-- The real zero-value `CALL` grant is a word-bounded MODEXP gas reservoir; its native reply
therefore meets the full return-data bound. The counterpart of the old chain's
`zero_call_spawn_modexp_reply_bound`. -/
theorem zero_call_spawn_modexp_reply_bound
    {sevm : Sevm} {before charged : Devm} (gas : U256)
    (extraGas cs inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {world : World} {post : Devm}
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas 0 gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas cs).2 0 caller target codeAddress shouldTransferValue isStaticcall
      inputIndex inputSize outputIndex outputSize code disablePrecompiles =
        .spawn child pending)
    (hmodexp : executePrecompile
      ⟨0, child.message.sevm,
        (child.start.setWorld world).withCreatedAccounts child.enteredCreatedAccounts⟩
      5 = .ok post) :
    post.output.length < 2 ^ 160 := by
  have hf := (genericCall.step_spawn_call hspawn).1
  have hgrant := calculateMsgCallGas_zero_word_child_lt gas before.gasLeft
    (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) extraGas cs
  have hgas : child.message.gas < 2 ^ 256 := by
    rw [hf]
    exact hgrant
  exact executePrecompile_modexp_ok_output_length_lt_two_pow_160 hmodexp (by
    change child.message.gas < _
    omega)

/-- An identity reply from the real spawned zero-value `CALL` frame is bounded by the caller's
paid input memory. The counterpart of the old chain's `zero_call_spawn_id_reply_bound`. -/
theorem zero_call_spawn_id_reply_bound
    {sevm : Sevm} {before charged : Devm}
    (baseCost gas inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {world : World} {post : Devm}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      gas 0 caller target codeAddress shouldTransferValue isStaticcall
      inputIndex inputSize outputIndex outputSize code disablePrecompiles =
        .spawn child pending)
    (hpotential : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256)
    (hidentity : executePrecompile
      ⟨0, child.message.sevm,
        (child.start.setWorld world).withCreatedAccounts child.enteredCreatedAccounts⟩
      4 = .ok post) :
    post.output.length < 2 ^ 160 := by
  have hout := executePrecompile_id_ok_output hidentity
  rw [hout]
  change child.message.context.calldata.length < 2 ^ 160
  rw [genericCall.step_spawn_data_length hspawn]
  exact charged_call_input_length_lt_two_pow_160
    baseCost inputIndex inputSize outputIndex outputSize hcharge hpotential

/-- The real zero-value `CALL` spawn supplies both physical premises every native precompile
needs. The counterpart of the old chain's `zero_call_spawn_native_reply_bound`. -/
theorem zero_call_spawn_native_reply_bound
    {sevm : Sevm} {before charged : Devm}
    (baseCost : Nat) (gas : U256)
    (extraGas cs inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {world : World} {adr : Address} {post : Devm}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas 0 gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas cs).2 0 caller target codeAddress shouldTransferValue isStaticcall
      inputIndex inputSize outputIndex outputSize code disablePrecompiles =
        .spawn child pending)
    (hpotential : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256)
    (hnative : executePrecompile
      ⟨0, child.message.sevm,
        (child.start.setWorld world).withCreatedAccounts child.enteredCreatedAccounts⟩
      adr = .ok post) :
    post.output.length < 2 ^ 160 := by
  have hdata : child.message.context.calldata.length < 2 ^ 160 := by
    rw [genericCall.step_spawn_data_length hspawn]
    exact charged_call_input_length_lt_two_pow_160
      baseCost inputIndex inputSize outputIndex outputSize hcharge hpotential
  have hgas : child.message.gas < 2 ^ 256 := by
    rw [(genericCall.step_spawn_call hspawn).1]
    exact calculateMsgCallGas_zero_word_child_lt gas before.gasLeft
      (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) extraGas cs
  exact enter_native_ok_output_length_lt_two_pow_160 hnative hdata (by omega)


/-- A call's caller, resumed on a settled result with a bounded output, has bounded return data
on either channel. -/
private theorem call_bind_resume_returnData {child : Frame} {pending : Pending}
    {rules : ForkRules} {raw : Execution} {outputIndex outputSize : Nat}
    (htarget : pending.target = .call outputIndex outputSize)
    (hsettled : ∀ r, settle child raw = .ok r → r.output.length < 2 ^ 160)
    (x : Except (ExceptionalHalt × Devm) Devm)
    (hx : (settle child raw >>= resume rules pending child.checkpoint) = .ok x) :
    match (generalizing := false) x with
    | .ok post => post.returnData.length < 2 ^ 160
    | .error failure => failure.2.returnData.length < 2 ^ 160 := by
  rcases hsettle : settle child raw with fault | r
  · rw [hsettle] at hx
    cases hx
  rw [hsettle] at hx
  change resume rules pending child.checkpoint r = .ok x at hx
  have hret : (resumedDevm x).returnData.length < 2 ^ 160 := by
    rw [call_resume_returnData htarget hx]
    exact hsettled r hsettle
  rcases x with failure | post
  · exact hret
  · exact hret

/-- A native success settles the child at entry; its raw reply is below `2^160`, and so is the
caller's return data on either resumed channel. Covers value-bearing calls through the stipend;
the source of the input bound is the caller's potential or the input size itself. -/
private theorem call_spawn_native_enter_success_input_or_potential
    {sevm : Sevm} {before charged : Devm}
    (baseCost : Nat) (gas value : U256)
    (extraGas inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {rules : ForkRules}
    {world : World} {adr : Address} {post : Devm}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas Gas.callStipend).2 value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending)
    (hsource : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256 ∨ inputSize < 2 ^ 160)
    (htransfer : child.message.transfer child.enteredWorld = .ok world)
    (hcode : child.message.codeAddress = some adr)
    (hdispatch : (!child.message.disablePrecompiles &&
      child.message.context.block.rules.isPrecompile adr) = true)
    (hrun : executePrecompile
      ⟨0, child.message.sevm,
        (child.start.setWorld world).withCreatedAccounts child.enteredCreatedAccounts⟩
      adr = .ok post) :
    enter child = .done (settle child (.ok post)) ∧
      post.output.length < 2 ^ 160 ∧
      ∀ x, (settle child (.ok post) >>= resume rules pending child.checkpoint) = .ok x →
        match (generalizing := false) x with
        | .ok resumed => resumed.returnData.length < 2 ^ 160
        | .error failure => failure.2.returnData.length < 2 ^ 160 := by
  have hdata : child.message.context.calldata.length < 2 ^ 160 := by
    rw [genericCall.step_spawn_data_length hspawn]
    rcases hsource with hpotential | hinput
    · exact charged_call_input_length_lt_two_pow_160
        baseCost inputIndex inputSize outputIndex outputSize hcharge hpotential
    · exact hinput
  have hgas : child.message.gas < 2 ^ 256 + Gas.callStipend := by
    rw [(genericCall.step_spawn_call hspawn).1]
    exact calculateMsgCallGas_word_child_lt_with_stipend value gas before.gasLeft
      (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)]) extraGas
  have hraw := enter_native_ok_output_length_lt_two_pow_160 hrun hdata hgas
  have hpending := (genericCall.step_spawn_call hspawn).2.2
  have hentry := enter_precompile htransfer hcode hdispatch
  rw [hrun] at hentry
  refine ⟨hentry, hraw, ?_⟩
  exact call_bind_resume_returnData (child := child) (pending := pending) (rules := rules)
    (raw := .ok post) (by rw [hpending])
    (fun r hs => Nat.lt_of_le_of_lt (settle_output_length_le hs) hraw)

/-- A native success of a word-sized `CALL`: the counterpart of the old chain's
`call_spawn_native_enter_success`. The old dispatch premise `executeCode.enter … = .inr (.ok
post)` is the value transfer, the precompile dispatch and the precompile's run, stated
separately. -/
theorem call_spawn_native_enter_success
    {sevm : Sevm} {before charged : Devm}
    (baseCost : Nat) (gas value : U256)
    (extraGas inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {rules : ForkRules}
    {world : World} {adr : Address} {post : Devm}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas Gas.callStipend).2 value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending)
    (hpotential : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256)
    (htransfer : child.message.transfer child.enteredWorld = .ok world)
    (hcode : child.message.codeAddress = some adr)
    (hdispatch : (!child.message.disablePrecompiles &&
      child.message.context.block.rules.isPrecompile adr) = true)
    (hrun : executePrecompile
      ⟨0, child.message.sevm,
        (child.start.setWorld world).withCreatedAccounts child.enteredCreatedAccounts⟩
      adr = .ok post) :
    enter child = .done (settle child (.ok post)) ∧
      post.output.length < 2 ^ 160 ∧
      ∀ x, (settle child (.ok post) >>= resume rules pending child.checkpoint) = .ok x →
        match (generalizing := false) x with
        | .ok resumed => resumed.returnData.length < 2 ^ 160
        | .error failure => failure.2.returnData.length < 2 ^ 160 :=
  call_spawn_native_enter_success_input_or_potential baseCost gas value extraGas
    inputIndex inputSize outputIndex outputSize hcharge hspawn (Or.inl hpotential)
    htransfer hcode hdispatch hrun

/-- A native success of a real zero-value `CALL`: the counterpart of the old chain's
`zero_call_spawn_native_enter_success`. -/
theorem zero_call_spawn_native_enter_success
    {sevm : Sevm} {before charged : Devm}
    (baseCost : Nat) (gas : U256)
    (extraGas cs inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {rules : ForkRules}
    {world : World} {adr : Address} {post : Devm}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas 0 gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas cs).2 0 caller target codeAddress shouldTransferValue isStaticcall
      inputIndex inputSize outputIndex outputSize code disablePrecompiles =
        .spawn child pending)
    (hpotential : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256)
    (htransfer : child.message.transfer child.enteredWorld = .ok world)
    (hcode : child.message.codeAddress = some adr)
    (hdispatch : (!child.message.disablePrecompiles &&
      child.message.context.block.rules.isPrecompile adr) = true)
    (hrun : executePrecompile
      ⟨0, child.message.sevm,
        (child.start.setWorld world).withCreatedAccounts child.enteredCreatedAccounts⟩
      adr = .ok post) :
    enter child = .done (settle child (.ok post)) ∧
      post.output.length < 2 ^ 160 ∧
      ∀ x, (settle child (.ok post) >>= resume rules pending child.checkpoint) = .ok x →
        match (generalizing := false) x with
        | .ok resumed => resumed.returnData.length < 2 ^ 160
        | .error failure => failure.2.returnData.length < 2 ^ 160 := by
  have hraw := zero_call_spawn_native_reply_bound baseCost gas extraGas cs inputIndex inputSize
    outputIndex outputSize hcharge hspawn hpotential hrun
  have hpending := (genericCall.step_spawn_call hspawn).2.2
  have hentry := enter_precompile htransfer hcode hdispatch
  rw [hrun] at hentry
  refine ⟨hentry, hraw, ?_⟩
  exact call_bind_resume_returnData (child := child) (pending := pending) (rules := rules)
    (raw := .ok post) (by rw [hpending])
    (fun r hs => Nat.lt_of_le_of_lt (settle_output_length_le hs) hraw)

/-- A rejected native precompile starts with empty output, so the caller's return data on
either resumed channel is below `2^160`. The counterpart of the old chain's
`call_spawn_native_enter_error`. -/
theorem call_spawn_native_enter_error
    {sevm : Sevm} {parent : Devm} (grant : Nat) (value : U256)
    (inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {rules : ForkRules}
    {world : World} {adr : Address} {failure : EvmError × Devm}
    (hspawn : genericCall.step sevm parent grant value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending)
    (htransfer : child.message.transfer child.enteredWorld = .ok world)
    (hcode : child.message.codeAddress = some adr)
    (hdispatch : (!child.message.disablePrecompiles &&
      child.message.context.block.rules.isPrecompile adr) = true)
    (hrun : executePrecompile
      ⟨0, child.message.sevm,
        (child.start.setWorld world).withCreatedAccounts child.enteredCreatedAccounts⟩
      adr = .error failure) :
    enter child = .done (settle child (.error failure)) ∧
      ∀ x, (settle child (.error failure) >>= resume rules pending child.checkpoint) = .ok x →
        match (generalizing := false) x with
        | .ok resumed => resumed.returnData.length < 2 ^ 160
        | .error e => e.2.returnData.length < 2 ^ 160 := by
  have hraw := enter_native_error_output_nil hrun
  have hpending := (genericCall.step_spawn_call hspawn).2.2
  have hentry := enter_precompile htransfer hcode hdispatch
  rw [hrun] at hentry
  refine ⟨hentry, ?_⟩
  refine call_bind_resume_returnData (child := child) (pending := pending) (rules := rules)
    (raw := .error failure) (by rw [hpending]) ?_
  intro r hs
  have hle := settle_output_length_le hs
  change r.output.length ≤ failure.2.output.length at hle
  rw [hraw] at hle
  simp only [List.length_nil] at hle
  omega


/-- Every word-sized `CALL` spawn, value-bearing or not, leaves the caller bounded return data
on either resumed channel, whichever way the child is entered: a failed transfer (a fault, which
resumes nobody), code run by `exec`, or a native precompile that succeeds or rejects. -/
private theorem call_spawn_enter_reply_bound_input_or_potential
    {sevm : Sevm} {before charged : Devm}
    (baseCost : Nat) (gas value : U256)
    (extraGas inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {rules : ForkRules}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas Gas.callStipend).2 value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending)
    (hsource : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256 ∨ inputSize < 2 ^ 160)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    match enter child with
    | .run childEvm =>
        ∀ x, (settle child (exec childEvm) >>= resume rules pending child.checkpoint) = .ok x →
          match (generalizing := false) x with
          | .ok post => post.returnData.length < 2 ^ 160
          | .error failure => failure.2.returnData.length < 2 ^ 160
    | .done settled =>
        ∀ x, (settled >>= resume rules pending child.checkpoint) = .ok x →
          match (generalizing := false) x with
          | .ok post => post.returnData.length < 2 ^ 160
          | .error failure => failure.2.returnData.length < 2 ^ 160 := by
  have hcodeRun : ∀ childEvm, enter child = .run childEvm →
      ∀ x, (settle child (exec childEvm) >>= resume rules pending child.checkpoint) = .ok x →
        match (generalizing := false) x with
        | .ok post => post.returnData.length < 2 ^ 160
        | .error failure => failure.2.returnData.length < 2 ^ 160 := by
    intro childEvm he
    exact (call_spawn_code_reply_bound (rules := rules) gas value before.gasLeft
      (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      extraGas inputIndex inputSize outputIndex outputSize hspawn he hstate).2.2
  cases ht : child.message.transfer child.enteredWorld with
  | error fault =>
      rw [enter_transfer_error ht]
      intro x hx
      cases hx
  | ok world =>
      cases hc : child.message.codeAddress with
      | none =>
          have he : enter child = .run ⟨0, child.message.sevm,
              (child.start.setWorld world).withCreatedAccounts child.enteredCreatedAccounts⟩ := by
            simp only [enter, enterWith, ht, hc]
          rw [he]
          exact hcodeRun _ he
      | some adr =>
          by_cases hd : (!child.message.disablePrecompiles &&
              child.message.context.block.rules.isPrecompile adr) = true
          · rw [enter_precompile ht hc hd]
            cases hrun : executePrecompile ⟨0, child.message.sevm,
                (child.start.setWorld world).withCreatedAccounts child.enteredCreatedAccounts⟩
                adr with
            | ok post =>
                exact (call_spawn_native_enter_success_input_or_potential baseCost gas value
                  extraGas inputIndex inputSize outputIndex outputSize hcharge hspawn hsource
                  ht hc hd hrun).2.2
            | error failure =>
                exact (call_spawn_native_enter_error (rules := rules)
                  (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
                    (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
                    extraGas Gas.callStipend).2 value inputIndex inputSize outputIndex
                  outputSize hspawn ht hc hd hrun).2
          · have he : enter child = .run ⟨0, child.message.sevm,
                (child.start.setWorld world).withCreatedAccounts child.enteredCreatedAccounts⟩ := by
              simp only [enter, enterWith, ht, hc]
              simp only [hd, Bool.false_eq_true, ↓reduceIte]
            rw [he]
            exact hcodeRun _ he

/-- Every word-sized `CALL` spawn leaves the caller bounded return data on either resumed
channel: the counterpart of the old chain's `call_spawn_enter_reply_bound`. The child's
derivation is its run by `exec`. -/
theorem call_spawn_enter_reply_bound
    {sevm : Sevm} {before charged : Devm}
    (baseCost : Nat) (gas value : U256)
    (extraGas inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool}
    {child : Frame} {pending : Pending} {rules : ForkRules}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hspawn : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas Gas.callStipend).2 value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles = .spawn child pending)
    (hpotential : before.gasMeasure + calculateMemoryGasCost before.memory.size <
      2 ^ 256)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    match enter child with
    | .run childEvm =>
        ∀ x, (settle child (exec childEvm) >>= resume rules pending child.checkpoint) = .ok x →
          match (generalizing := false) x with
          | .ok post => post.returnData.length < 2 ^ 160
          | .error failure => failure.2.returnData.length < 2 ^ 160
    | .done settled =>
        ∀ x, (settled >>= resume rules pending child.checkpoint) = .ok x →
          match (generalizing := false) x with
          | .ok post => post.returnData.length < 2 ^ 160
          | .error failure => failure.2.returnData.length < 2 ^ 160 :=
  call_spawn_enter_reply_bound_input_or_potential baseCost gas value extraGas
    inputIndex inputSize outputIndex outputSize hcharge hspawn (Or.inl hpotential) hstate

/-! ### A `CALL` step: the caller's return data -/

/-- The result a spawned child hands its caller in a run: settled at entry, or settled after
its code ran to completion. -/
private def childResult (child : Frame) : Except Fault Frame.Result :=
  match enter child with
  | .done result => result
  | .run childEvm => settle child (exec childEvm)

/-- The caller goes on with `post` after a call-family outcome: the opcode finished in place
with `post`, or the caller was resumed with `post` on its child's result. -/
private def outcomeContinues (rules : ForkRules) : MessageOp.Outcome → Devm → Prop
  | .done ex, post => ex = .ok post
  | .spawn child pending, post =>
      (childResult child >>= resume rules pending child.checkpoint) = .ok (.ok post)

/-- A call-family outcome leaves its caller return data below `2^160` whenever the caller
goes on. -/
private def callStepReplyBound (rules : ForkRules) (step : MessageOp.Outcome) : Prop :=
  ∀ post, outcomeContinues rules step post → post.returnData.length < 2 ^ 160

private theorem callStepReplyBound_bind {α : Type} {rules : ForkRules} {pre : Devm}
    {first : Except (EvmError × Devm) α}
    {next : α → Except (EvmError × Devm) MessageOp.Outcome} {project : α → Devm}
    (hf : nonspawnResult pre project first)
    (hn : ∀ value,
      (project value).gasMeasure + calculateMemoryGasCost (project value).memory.size < 2 ^ 256 →
      callStepReplyBound rules (MessageOp.Outcome.ofExcept (next value)))
    (hpotential : pre.gasMeasure + calculateMemoryGasCost pre.memory.size < 2 ^ 256) :
    callStepReplyBound rules (MessageOp.Outcome.ofExcept (first >>= next)) := by
  cases first with
  | error failure =>
      intro post hpost
      cases hpost
  | ok value => exact hn value (Nat.lt_of_le_of_lt hf.1 hpotential)

private theorem push_returnData (pre : Devm) (word : U256) :
    match pre.push word with
    | .error failure => failure.2.returnData = pre.returnData
    | .ok post => post.returnData = pre.returnData := by
  rw [Devm.push_def]
  by_cases hs : pre.stack.length < 1024
  · simp only [Except.assert, hs, ite_true, bind, Except.bind]
    rfl
  · simp only [Except.assert, hs, ite_false, bind, Except.bind]

/-- An insufficient balance pushes the failure status with the return data cleared. -/
private theorem balance_reply_bound (rules : ForkRules) (paid : Devm) (refund : Nat) :
    callStepReplyBound rules (MessageOp.Outcome.ofExcept (do
      let post ← paid.push 0
      pure (.done (.ok ((post.withReturnData []).withGasLeft (post.gasLeft + refund)))))) := by
  intro post hpost
  cases pushed : paid.push 0 with
  | error failure =>
      simp only [pushed, bind, Except.bind, MessageOp.Outcome.ofExcept, outcomeContinues,
        reduceCtorEq] at hpost
  | ok next =>
      simp only [pushed, bind, Except.bind, Pure.pure, Except.pure,
        MessageOp.Outcome.ofExcept, outcomeContinues, Except.ok.injEq] at hpost
      subst hpost
      change (0 : Nat) < 2 ^ 160
      decide

/-- A call that cannot go deeper refunds its grant and pushes the failure status, with the
return data cleared. -/
private theorem push_done_returnData {d : Devm} {ex : Execution}
    (h : MessageOp.Outcome.ofExcept (do
      let devm ← d.push 0
      return MessageOp.Outcome.done (.ok devm)) = .done ex)
    (hd : d.returnData = []) :
    ∀ post, ex = .ok post → post.returnData.length < 2 ^ 160 := by
  intro post hpost
  subst hpost
  cases pushed : d.push 0 with
  | error failure =>
      simp only [pushed, bind, Except.bind, MessageOp.Outcome.ofExcept,
        MessageOp.Outcome.done.injEq, reduceCtorEq] at h
  | ok pushedState =>
      simp only [pushed, bind, Except.bind, Pure.pure, Except.pure,
        MessageOp.Outcome.ofExcept, MessageOp.Outcome.done.injEq, Except.ok.injEq] at h
      subst h
      have fields := push_returnData d 0
      rw [pushed] at fields
      rw [fields, hd]
      decide

private theorem charged_genericCall_reply_bound
    {sevm : Sevm} {before charged : Devm}
    (baseCost : Nat) (gas value : U256)
    (extraGas inputIndex inputSize outputIndex outputSize : Nat)
    {caller target codeAddress : Address} {shouldTransferValue isStaticcall : Bool}
    {code : ByteArray} {disablePrecompiles : Bool} {rules : ForkRules}
    (hcharge : chargeGas
      (baseCost + before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
      before = .ok charged)
    (hsource : before.gasMeasure + calculateMemoryGasCost before.memory.size < 2 ^ 256 ∨
      inputSize < 2 ^ 160)
    (hstate : sevm.benvStat.rules.stateGas = none) :
    callStepReplyBound rules (genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas Gas.callStipend).2 value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles) := by
  cases hstep : genericCall.step sevm
      (charged.memExtends [(inputIndex, inputSize), (outputIndex, outputSize)])
      (calculateMsgCallGas value.toNat gas.toNat before.gasLeft
        (before.extCost [(inputIndex, inputSize), (outputIndex, outputSize)])
        extraGas Gas.callStipend).2 value caller target codeAddress
      shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize
      code disablePrecompiles with
  | done ex =>
      intro post hpost
      unfold genericCall.step at hstep
      split at hstep
      · exact push_done_returnData hstep rfl post hpost
      · cases hstep
  | spawn child pending =>
      intro post hpost
      have bounded := call_spawn_enter_reply_bound_input_or_potential (rules := rules)
        baseCost gas value extraGas
        inputIndex inputSize outputIndex outputSize hcharge hstep hsource hstate
      change (childResult child >>= resume rules pending child.checkpoint) =
        .ok (.ok post) at hpost
      unfold childResult at hpost
      split at hpost
      · next result he =>
          rw [he] at bounded
          exact bounded _ hpost
      · next childEvm he =>
          rw [he] at bounded
          exact bounded _ hpost

private theorem xinst_call_reply_bound (sevm : Sevm) (pre : Devm)
    (hstate : sevm.benvStat.rules.stateGas = none)
    (hpotential : pre.gasMeasure + calculateMemoryGasCost pre.memory.size < 2 ^ 256) :
    callStepReplyBound sevm.benvStat.rules (MessageOp.step sevm pre .call) := by
  simp only [MessageOp.step, hstate]
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
  -- The access step of either shape: a price `price` and a recorder `dA`.
  rcases hA : sevm.benvStat.rules.access with g | _
  on_goal 1 =>
    let price := g.call
    let dA := outputSize.2
    have hdA : nonspawnPreserved outputSize.2 dA := ⟨Nat.le_refl _, rfl⟩
  on_goal 2 =>
    let price := sevm.benvStat.rules.gas.accessCost callee.1 outputSize.2.accessedAddresses
    let dA := addAccessedAddress outputSize.2 callee.1
    have hdA := nonspawn_addAccessedAddress outputSize.2 callee.1
  all_goals
    let pairs := [(inputIndex.1, inputSize.1), (outputIndex.1, outputSize.1)]
    let lookup := sevm.benvStat.rules.accessDelegation
      dA callee.1
    let parent := lookup.2.2.2.2
    have preserved : nonspawnPreserved outputSize.2 parent :=
      nonspawnPreserved_trans hdA
        (nonspawn_rules_delegation sevm.benvStat.rules _ callee.1)
    have parentPotential : parent.gasMeasure + calculateMemoryGasCost parent.memory.size < 2 ^ 256 :=
      Nat.lt_of_le_of_lt preserved.1 outputSizePotential
    have memory : parent.memory = outputSize.2.memory :=
      (rules_delegation_memory_output sevm.benvStat.rules
        dA callee.1).1
    have extension : outputSize.2.extCost pairs = parent.extCost pairs := by
      simp only [Devm.extCost, memory]
    let accessCost := price + lookup.2.2.2.1
    let createCost : Nat := if ¬(parent.getAcct callee.1).isEmpty ∨ value.1 = 0 then 0 else Gas.newAccount
    let extraGas := accessCost + createCost + if value.1 = 0 then 0 else sevm.benvStat.rules.gas.callValue
    change callStepReplyBound sevm.benvStat.rules (MessageOp.Outcome.ofExcept (chargeGas
      ((calculateMsgCallGas value.1.toNat gas.1.toNat parent.gasLeft
        (outputSize.2.extCost pairs) extraGas).1 + outputSize.2.extCost pairs) parent >>= _))
    rw [extension]
    let costs := calculateMsgCallGas value.1.toNat gas.1.toNat parent.gasLeft
      (parent.extCost pairs) extraGas
    cases charge : chargeGas (costs.1 + parent.extCost pairs) parent with
    | error failure =>
        simp only [bind, Except.bind, MessageOp.Outcome.ofExcept]
        intro post hpost
        cases hpost
    | ok charged =>
        simp only [bind, Except.bind]
        by_cases static : (!sevm.isStatic) = true ∨ value.1 = 0
        · simp only [Except.assert, ite_eq_left static]
          let paid := charged.memExtends pairs
          by_cases balance : (paid.getAcct sevm.currentTarget).balance < value.1
          · dsimp only [paid, pairs] at balance
            simp only [ite_eq_left balance]
            exact balance_reply_bound _ _ _
          · dsimp only [paid, pairs] at balance
            simp only [ite_eq_right balance, Pure.pure, Except.pure, MessageOp.Outcome.ofExcept]
            exact charged_genericCall_reply_bound costs.1 gas.1 value.1 extraGas
              inputIndex.1 inputSize.1 outputIndex.1 outputSize.1 charge (Or.inl parentPotential) hstate
        · simp only [Except.assert, ite_eq_right static, MessageOp.Outcome.ofExcept]
          intro post hpost
          cases hpost

/-- Fixed actual CALL operands provide the identity precompile's input bound
without any bound on the enclosing caller's initial gas or memory potential. -/
private theorem xinst_call_reply_bound_of_input_size
    (sevm : Sevm) (pre : Devm) (gas callee value inputIndex inputSize outputIndex outputSize : U256)
    (S : List U256)
    (hstack : pre.stack = gas :: callee :: value :: inputIndex :: inputSize :: outputIndex :: outputSize :: S)
    (hstate : sevm.benvStat.rules.stateGas = none)
    (hinput : inputSize.toNat < 2 ^ 160) :
    callStepReplyBound sevm.benvStat.rules (MessageOp.step sevm pre .call) := by
  rcases pre with ⟨⟨stack, memory, gasLeft, stateGas⟩, view, world⟩
  change stack = _ at hstack
  subst stack
  let base : Devm := ⟨⟨S, memory, gasLeft, stateGas⟩, view, world⟩
  simp only [MessageOp.step, hstate, Devm.popToAdr_def, Devm.popToNat_def,
    Devm.pop_def, Devm.stack, Devm.setMach, bind, Except.bind, Functor.mapRev, Functor.map, Except.map,
    Prod.mapFst, Prod.map, id_eq]
  -- The access step of either shape: a price `price` and a recorder `dA`.
  rcases hA : sevm.benvStat.rules.access with g | _
  on_goal 1 =>
    let price := g.call
    let dA := base
  on_goal 2 =>
    let price := sevm.benvStat.rules.gas.accessCost callee.toAddress base.accessedAddresses
    let dA := addAccessedAddress base callee.toAddress
  all_goals
    let pairs := [(inputIndex.toNat, inputSize.toNat), (outputIndex.toNat, outputSize.toNat)]
    let lookup := sevm.benvStat.rules.accessDelegation
      dA callee.toAddress
    let parent := lookup.2.2.2.2
    have memory : parent.memory = base.memory :=
      (rules_delegation_memory_output sevm.benvStat.rules
        dA callee.toAddress).1
    have extension : base.extCost pairs = parent.extCost pairs := by
      simp only [Devm.extCost, memory]
    let accessCost := price + lookup.2.2.2.1
    let createCost : Nat := if ¬(parent.getAcct callee.toAddress).isEmpty ∨ value = 0 then 0 else Gas.newAccount
    let extraGas := accessCost + createCost + if value = 0 then 0 else sevm.benvStat.rules.gas.callValue
    change callStepReplyBound sevm.benvStat.rules (MessageOp.Outcome.ofExcept (chargeGas
      ((calculateMsgCallGas value.toNat gas.toNat parent.gasLeft
        (base.extCost pairs) extraGas).1 + base.extCost pairs) parent >>= _))
    rw [extension]
    let costs := calculateMsgCallGas value.toNat gas.toNat parent.gasLeft
      (parent.extCost pairs) extraGas
    cases charge : chargeGas (costs.1 + parent.extCost pairs) parent with
    | error failure =>
        simp only [bind, Except.bind, MessageOp.Outcome.ofExcept]
        intro post hpost
        cases hpost
    | ok charged =>
        simp only [bind, Except.bind]
        by_cases static : (!sevm.isStatic) = true ∨ value = 0
        · simp only [Except.assert, ite_eq_left static]
          let paid := charged.memExtends pairs
          by_cases balance : (paid.getAcct sevm.currentTarget).balance < value
          · dsimp only [paid, pairs] at balance
            simp only [ite_eq_left balance]
            exact balance_reply_bound _ _ _
          · dsimp only [paid, pairs] at balance
            simp only [ite_eq_right balance, Pure.pure, Except.pure, MessageOp.Outcome.ofExcept]
            exact charged_genericCall_reply_bound costs.1 gas value extraGas
              inputIndex.toNat inputSize.toNat outputIndex.toNat outputSize.toNat charge (Or.inr hinput) hstate
        · simp only [Except.assert, ite_eq_right static, MessageOp.Outcome.ofExcept]
          intro post hpost
          cases hpost

/-- A `CALL` that finishes in place or whose caller is resumed on its child's result leaves the
caller return data below `2^160`, under rules without state gas and a word-bounded caller
potential. The child's result is its settled entry or its settled run by `exec`. This is the
four-part form of the old chain's `call_step_returnData_length_lt_two_pow_160`, whose filled
slot and `XStep.Run` relation are the child run named here. -/
theorem MessageOp.step_call_returnData_length_lt_two_pow_160 {sevm : Sevm} {pre : Devm}
    (hstate : sevm.benvStat.rules.stateGas = none)
    (hpotential : pre.gasMeasure + calculateMemoryGasCost pre.memory.size < 2 ^ 256) :
    match MessageOp.step sevm pre .call with
    | .done ex => ∀ post, ex = .ok post → post.returnData.length < 2 ^ 160
    | .spawn child pending => ∀ post,
        ((match enter child with
          | .done result => result
          | .run childEvm => settle child (exec childEvm)) >>=
            resume sevm.benvStat.rules pending child.checkpoint) = .ok (.ok post) →
          post.returnData.length < 2 ^ 160 := by
  have h := xinst_call_reply_bound sevm pre hstate hpotential
  generalize MessageOp.step sevm pre .call = step at h ⊢
  cases step with
  | done ex => exact h
  | spawn child pending => exact h

/-- The same bound from fixed `CALL` operands with a bounded input size, independent of the
caller's potential: the four-part form of the old chain's
`call_step_returnData_length_lt_two_pow_160_of_input_size`. -/
theorem MessageOp.step_call_returnData_length_lt_two_pow_160_of_input_size
    {sevm : Sevm} {pre : Devm}
    {gas callee value inputIndex inputSize outputIndex outputSize : U256} {S : List U256}
    (hstack : pre.stack =
      gas :: callee :: value :: inputIndex :: inputSize :: outputIndex :: outputSize :: S)
    (hstate : sevm.benvStat.rules.stateGas = none)
    (hinput : inputSize.toNat < 2 ^ 160) :
    match MessageOp.step sevm pre .call with
    | .done ex => ∀ post, ex = .ok post → post.returnData.length < 2 ^ 160
    | .spawn child pending => ∀ post,
        ((match enter child with
          | .done result => result
          | .run childEvm => settle child (exec childEvm)) >>=
            resume sevm.benvStat.rules pending child.checkpoint) = .ok (.ok post) →
          post.returnData.length < 2 ^ 160 := by
  have h := xinst_call_reply_bound_of_input_size sevm pre gas callee value
    inputIndex inputSize outputIndex outputSize S hstack hstate hinput
  generalize MessageOp.step sevm pre .call = step at h ⊢
  cases step with
  | done ex => exact h
  | spawn child pending => exact h

/-! ### Over the derivation -/

/-- A closed derivation's raw result settles within the frame's gas measure: the counterpart of
the old chain's `Exec.settledGasLe`, through adequacy. -/
theorem Exec.settledGasLe {pc : Nat} {sevm : Sevm} {devm : Devm} {raw : Execution}
    (h : Exec pc sevm devm raw) : raw.SettledGasLe devm.gasMeasure := by
  have heq := (exec_iff_exec_eq pc sevm devm raw).mp ⟨h⟩
  have hs := execFueled_settledGasLe _ (⟨pc, sevm, devm⟩ : Evm)
    (execFueled_run_sufficientFuel ⟨pc, sevm, devm⟩)
  rw [heq] at hs
  exact hs

/-- A complete derivation preserves the memory/gas potential, and its full raw output is
inherited or paid by the initial potential on both channels: the counterpart of the old chain's
`Exec.memory_accounting_output`, through adequacy from `exec_memory_accounting_output`. -/
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
  have heq := (exec_iff_exec_eq pc sevm pre raw).mp ⟨h⟩
  have hc := exec_memory_accounting_output (evm := ⟨pc, sevm, pre⟩) hstate
  rw [heq] at hc
  cases raw with
  | error failure => exact hc
  | ok post => exact hc

end Jaune
