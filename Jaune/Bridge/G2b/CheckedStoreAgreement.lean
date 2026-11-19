import Jaune.Bridge.G2b.CheckedContext
import Jaune.Bridge.G2b.CheckedPlainArms
import Jaune.Instructions.StoreFacts

/-!
# Bridge: the `SSTORE` and `TSTORE` rows against the arms

The agreement lemmas of W4's Store unit (`SstoreRow.ofRules_lift_eq`, `TstoreRow.ofRules_lift_eq`)
and the lemmas they use, moved here unchanged from `Jaune/Instructions/StoreFacts.lean` at
`9ce48608` into the namespace `Jaune.Checked.Arms`, where `PlainOp.runCore` and the three
`SSTORE` shapes (`PlainOp.sstoreBerlin`, `sstoreLegacy`, `sstoreAmsterdam`) name the old side
(`Jaune.Bridge.G2b.CheckedPlainArms`). For every `ForkRules`, program counter, call context and
frame state, on both channels. They go with the cut's bridge after G2b's tag.
-/

namespace Jaune.Checked.Arms

open Jaune

private theorem state_pop_eq (s : Frame.State) :
    s.pop = match s.machine.pop with
      | .error (e, m) => .error (e, s.withMachine m)
      | .ok (x, m) => .ok (x, s.withMachine m) := by
  unfold Frame.State.pop Frame.State.liftMachineValue
  cases s.machine.pop with
  | error e => rcases e with ⟨_, _⟩; rfl
  | ok p => rcases p with ⟨_, _⟩; rfl

private theorem state_chargeGas_eq (cost : Nat) (s : Frame.State) :
    s.chargeGas cost = match s.machine.chargeGas cost with
      | .error (e, m) => .error (e, s.withMachine m)
      | .ok m => .ok (s.withMachine m) := by
  unfold Frame.State.chargeGas Frame.State.liftMachine
  cases s.machine.chargeGas cost with
  | error e => rcases e with ⟨_, _⟩; rfl
  | ok _ => rfl

private theorem state_chargeStateGas_eq (amount : Nat) (s : Frame.State) :
    s.chargeStateGas amount = match s.machine.chargeStateGas amount with
      | .error (e, m) => .error (e, s.withMachine m)
      | .ok m => .ok (s.withMachine m) := by
  unfold Frame.State.chargeStateGas Frame.State.liftMachine
  cases s.machine.chargeStateGas amount with
  | error e => rcases e with ⟨_, _⟩; rfl
  | ok _ => rfl

private theorem except_assert_eq_ok {ε : Type} {p : Prop} [Decidable p] {e : ε} (h : p) :
    Except.assert p e = .ok () := by
  unfold Except.assert; simp [h]

private theorem except_assert_eq_error {ε : Type} {p : Prop} [Decidable p] {e : ε} (h : ¬ p) :
    Except.assert p e = .error e := by
  unfold Except.assert; simp [h]

private theorem assertDynamic_true {ctx : Jaune.CallContext} {s : Frame.State}
    (h : ctx.isStatic = true) :
    Frame.State.assertDynamic ctx.toChecked s = .error (.writeInStaticContext .none, s) := by
  simp [Frame.State.assertDynamic, Except.assert, Jaune.CallContext.toChecked_isStatic, h]

private theorem assertDynamic_false {ctx : Jaune.CallContext} {s : Frame.State}
    (h : ctx.isStatic = false) :
    Frame.State.assertDynamic ctx.toChecked s = .ok () := by
  simp [Frame.State.assertDynamic, Except.assert, Jaune.CallContext.toChecked_isStatic, h]

private theorem withMachine_twice (s : Frame.State) (m₁ m₂ : Machine) :
    (s.withMachine m₁).withMachine m₂ = s.withMachine m₂ := rfl

private theorem withMachine_gasLeft (s : Frame.State) (m : Machine) :
    (s.withMachine m).gasLeft = m.gasLeft := rfl

private theorem withMachine_originalStorageValue (s : Frame.State) (m : Machine)
    (o : Jaune.State) (a : Address) (k : U256) :
    (s.withMachine m).originalStorageValue o a k = s.originalStorageValue o a k := rfl

private theorem withMachine_storageValue (s : Frame.State) (m : Machine)
    (a : Address) (k : U256) :
    (s.withMachine m).storageValue a k = s.storageValue a k := rfl

private theorem withMachine_refund (s : Frame.State) (m : Machine) :
    (s.withMachine m).refund = s.refund := rfl

private theorem withMachine_accessedStorageKeys (s : Frame.State) (m : Machine) :
    (s.withMachine m).accessedStorageKeys = s.accessedStorageKeys := rfl

private theorem recordStorageRead_storageValue (rules : ForkRules) (a : Address) (k : U256)
    (s : Frame.State) (a' : Address) (k' : U256) :
    (s.recordStorageRead rules a k).storageValue a' k' = s.storageValue a' k' := rfl

private theorem recordStorageRead_accessedStorageKeys (rules : ForkRules) (a : Address) (k : U256)
    (s : Frame.State) :
    (s.recordStorageRead rules a k).accessedStorageKeys = s.accessedStorageKeys := rfl

private theorem recordStorageRead_refund (rules : ForkRules) (a : Address) (k : U256)
    (s : Frame.State) :
    (s.recordStorageRead rules a k).refund = s.refund := rfl

private theorem addAccessedStorageKey_originalStorageValue (a : Address) (k : U256)
    (s : Frame.State) (o : Jaune.State) (a' : Address) (k' : U256) :
    (s.addAccessedStorageKey a k).originalStorageValue o a' k' =
      s.originalStorageValue o a' k' := rfl

private theorem addAccessedStorageKey_storageValue (a : Address) (k : U256)
    (s : Frame.State) (a' : Address) (k' : U256) :
    (s.addAccessedStorageKey a k).storageValue a' k' = s.storageValue a' k' := rfl

private theorem addAccessedStorageKey_refund (a : Address) (k : U256) (s : Frame.State) :
    (s.addAccessedStorageKey a k).refund = s.refund := rfl

private theorem addAccessedStorageKey_machine (a : Address) (k : U256) (s : Frame.State) :
    (s.addAccessedStorageKey a k).machine = s.machine := rfl

private theorem recordStorageRead_machine (rules : ForkRules) (a : Address) (k : U256)
    (s : Frame.State) :
    (s.recordStorageRead rules a k).machine = s.machine := rfl

private theorem withRefund_machine (s : Frame.State) (r : Int) :
    (s.withRefund r).machine = s.machine := rfl

private theorem sstoreBerlin_eq_sstoreLegacy (ctx : Jaune.CallContext) (s : Frame.State)
    (hs2 : ctx.block.rules.sstore = ⟨true, true⟩)
    (hs3 : ctx.block.rules.access = .eip2929) :
    PlainOp.sstoreBerlin ctx s = PlainOp.sstoreLegacy ctx s := by
  unfold PlainOp.sstoreBerlin PlainOp.sstoreLegacy
  simp only [bind, Except.bind]
  cases hp1 : s.pop with
  | error e1 => rfl
  | ok p1 =>
    rcases p1 with ⟨key, s1⟩
    dsimp only
    cases hp2 : s1.pop with
    | error e2 => rfl
    | ok p2 =>
      rcases p2 with ⟨newVal, s2⟩
      dsimp only
      have hs_iff : (ctx.block.rules.sstore.stipendSentry = true → Gas.callStipend < s2.gasLeft) ↔
          (Gas.callStipend < s2.gasLeft) := by simp [hs2]
      by_cases hg : Gas.callStipend < s2.gasLeft
      · have hgL : (ctx.block.rules.sstore.stipendSentry = true → Gas.callStipend < s2.gasLeft) :=
          hs_iff.mpr hg
        rw [except_assert_eq_ok hg, except_assert_eq_ok hgL]
        simp only [hs2, hs3, sstoreRegimeGasCost, ↓reduceIte]
      · have hgL : ¬ (ctx.block.rules.sstore.stipendSentry = true → Gas.callStipend < s2.gasLeft) :=
          mt hs_iff.mp hg
        rw [except_assert_eq_error hg, except_assert_eq_error hgL]

private theorem liftStore_sstoreLegacy_eq (ctx : Jaune.CallContext) (s : Frame.State)
    (hs1 : ctx.block.rules.stateGas = none) :
    s.liftStore ctx.block.rules ctx.recipient
        ((SstoreRow.ofRules ctx.block.rules).step ctx.isStatic
          (s.slotView ctx.recipient ctx.block.origState)) =
      PlainOp.sstoreLegacy ctx s := by
  unfold Frame.State.liftStore SstoreRow.step SstoreRow.ofRules PlainOp.sstoreLegacy
  simp only [hs1, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false, state_pop_eq]
  cases hp1 : s.machine.pop with
  | error e1 =>
    rcases e1 with ⟨err, m'⟩
    rfl
  | ok p1 =>
    rcases p1 with ⟨key, m₁⟩
    simp only [bind, Except.bind, Frame.State.withMachine_machine]
    cases hp2 : m₁.pop with
    | error e2 =>
      rcases e2 with ⟨err, m'⟩
      rfl
    | ok p2 =>
      rcases p2 with ⟨newVal, m₂⟩
      dsimp only
      have hsentry_iff : (m₂.gasLeft <
            if ctx.block.rules.sstore.stipendSentry then Gas.callStipend + 1 else 0) ↔
          ¬ (ctx.block.rules.sstore.stipendSentry = true → Gas.callStipend < m₂.gasLeft) := by
        cases ctx.block.rules.sstore.stipendSentry <;> simp; omega
      by_cases hsentry : (ctx.block.rules.sstore.stipendSentry = true →
          Gas.callStipend < m₂.gasLeft)
      · have hlt : ¬ (m₂.gasLeft <
            if ctx.block.rules.sstore.stipendSentry then Gas.callStipend + 1 else 0) :=
          mt hsentry_iff.mp (not_not.mpr hsentry)
        have hsentry_raw : (ctx.block.rules.sstore.stipendSentry = true →
            Gas.callStipend < ((s.withMachine m₁).withMachine m₂).gasLeft) := by
          simpa [withMachine_twice, withMachine_gasLeft] using hsentry
        rw [except_assert_eq_ok hsentry_raw]
        simp only [hlt, ↓reduceIte, withMachine_twice, Machine.creditStateGasRefund_zero]
        cases hacc : ctx.block.rules.access with
        | flat g =>
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Frame.State.slotView,
            withMachine_originalStorageValue, withMachine_storageValue, withMachine_refund,
            recordStorageRead_storageValue, recordStorageRead_refund, recordStorageRead_machine,
            withRefund_machine, state_chargeGas_eq, Frame.State.withMachine_machine]
          cases hcg : m₂.chargeGas (sstoreRegimeGasCost ctx.block.rules.sstore (.flat g) 0
              newVal (s.originalStorageValue ctx.block.origState ctx.recipient key)
              (s.storageValue ctx.recipient key)) with
          | error e3 =>
            rcases e3 with ⟨err, m'⟩
            unfold Frame.State.applyStoreTouch
            cases ctx.block.rules.sstore.netMetering <;> rfl
          | ok m₄ =>
            simp only [Machine.chargeStateGas_zero]
            cases hstat : ctx.isStatic
            · rw [assertDynamic_false hstat]
              cases ctx.block.rules.sstore.netMetering <;> (unfold Frame.State.applyStoreTouch; rfl)
            · rw [assertDynamic_true hstat]
              cases ctx.block.rules.sstore.netMetering <;> (unfold Frame.State.applyStoreTouch; rfl)
        | eip2929 =>
          simp only [Bool.true_and]
          by_cases hcold : (ctx.recipient, key) ∉ s.accessedStorageKeys
          · have hdc : (s.slotView ctx.recipient ctx.block.origState key).cold = true :=
              decide_eq_true hcold
            simp only [hdc, ↓reduceIte]
            have hcold_true : ((ctx.recipient, key) ∉ s.accessedStorageKeys) = True :=
              eq_true hcold
            simp only [hcold_true, ↓reduceIte, Frame.State.slotView,
              withMachine_originalStorageValue, withMachine_storageValue,
              withMachine_accessedStorageKeys, withMachine_refund,
              recordStorageRead_storageValue, recordStorageRead_accessedStorageKeys,
              recordStorageRead_refund, recordStorageRead_machine,
              addAccessedStorageKey_refund, addAccessedStorageKey_machine, withRefund_machine,
              state_chargeGas_eq, Frame.State.withMachine_machine]
            cases hcg : m₂.chargeGas (sstoreRegimeGasCost ctx.block.rules.sstore .eip2929
                Gas.coldSloadCost newVal
                (s.originalStorageValue ctx.block.origState ctx.recipient key)
                (s.storageValue ctx.recipient key)) with
            | error e3 =>
              rcases e3 with ⟨err, m'⟩
              unfold Frame.State.applyStoreTouch
              cases ctx.block.rules.sstore.netMetering <;> rfl
            | ok m₄ =>
              simp only [Machine.chargeStateGas_zero]
              cases hstat : ctx.isStatic
              · rw [assertDynamic_false hstat]
                cases ctx.block.rules.sstore.netMetering <;> (unfold Frame.State.applyStoreTouch; rfl)
              · rw [assertDynamic_true hstat]
                cases ctx.block.rules.sstore.netMetering <;> (unfold Frame.State.applyStoreTouch; rfl)
          · have hdc : (s.slotView ctx.recipient ctx.block.origState key).cold = false :=
              decide_eq_false hcold
            simp only [hdc, Bool.false_eq_true, ↓reduceIte]
            have hcold_false : ((ctx.recipient, key) ∉ s.accessedStorageKeys) = False :=
              eq_false hcold
            simp only [hcold_false, ↓reduceIte, Frame.State.slotView,
              withMachine_originalStorageValue, withMachine_storageValue,
              withMachine_accessedStorageKeys, withMachine_refund,
              recordStorageRead_storageValue, recordStorageRead_accessedStorageKeys,
              recordStorageRead_refund, recordStorageRead_machine,
              withRefund_machine, state_chargeGas_eq, Frame.State.withMachine_machine]
            cases hcg : m₂.chargeGas (sstoreRegimeGasCost ctx.block.rules.sstore .eip2929 0
                newVal (s.originalStorageValue ctx.block.origState ctx.recipient key)
                (s.storageValue ctx.recipient key)) with
            | error e3 =>
              rcases e3 with ⟨err, m'⟩
              unfold Frame.State.applyStoreTouch
              cases ctx.block.rules.sstore.netMetering <;> rfl
            | ok m₄ =>
              simp only [Machine.chargeStateGas_zero]
              cases hstat : ctx.isStatic
              · rw [assertDynamic_false hstat]
                cases ctx.block.rules.sstore.netMetering <;> (unfold Frame.State.applyStoreTouch; rfl)
              · rw [assertDynamic_true hstat]
                cases ctx.block.rules.sstore.netMetering <;> (unfold Frame.State.applyStoreTouch; rfl)
      · have hlt : m₂.gasLeft <
            if ctx.block.rules.sstore.stipendSentry then Gas.callStipend + 1 else 0 :=
          hsentry_iff.mpr hsentry
        have hsentry_raw : ¬ (ctx.block.rules.sstore.stipendSentry = true →
            Gas.callStipend < ((s.withMachine m₁).withMachine m₂).gasLeft) := by
          simpa [withMachine_twice, withMachine_gasLeft] using hsentry
        rw [except_assert_eq_error hsentry_raw]
        simp only [hlt, ↓reduceIte, withMachine_twice]
        rfl

private theorem liftStore_sstoreBerlin_eq (ctx : Jaune.CallContext) (s : Frame.State)
    (hs1 : ctx.block.rules.stateGas = none)
    (hs2 : ctx.block.rules.sstore = ⟨true, true⟩)
    (hs3 : ctx.block.rules.access = .eip2929) :
    s.liftStore ctx.block.rules ctx.recipient
        ((SstoreRow.ofRules ctx.block.rules).step ctx.isStatic
          (s.slotView ctx.recipient ctx.block.origState)) =
      PlainOp.sstoreBerlin ctx s := by
  rw [liftStore_sstoreLegacy_eq ctx s hs1]
  exact (sstoreBerlin_eq_sstoreLegacy ctx s hs2 hs3).symm

private theorem liftStore_sstoreAmsterdam_eq (state : StateGasRules) (ctx : Jaune.CallContext)
    (s : Frame.State) (hs : ctx.block.rules.stateGas = some state) :
    s.liftStore ctx.block.rules ctx.recipient
        ((SstoreRow.ofRules ctx.block.rules).step ctx.isStatic
          (s.slotView ctx.recipient ctx.block.origState)) =
      PlainOp.sstoreAmsterdam state ctx s := by
  unfold Frame.State.liftStore SstoreRow.step SstoreRow.ofRules PlainOp.sstoreAmsterdam
  simp only [hs, Bool.true_and, Bool.not_true, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  cases hstat : ctx.isStatic
  · rw [assertDynamic_false hstat]
    simp only [bind, Except.bind, state_pop_eq]
    cases hp1 : s.machine.pop with
    | error e1 =>
      rcases e1 with ⟨err, m'⟩
      rfl
    | ok p1 =>
      rcases p1 with ⟨key, m₁⟩
      simp only [Frame.State.withMachine_machine]
      cases hp2 : m₁.pop with
      | error e2 =>
        rcases e2 with ⟨err, m'⟩
        rfl
      | ok p2 =>
        rcases p2 with ⟨newVal, m₂⟩
        by_cases hcold : (ctx.recipient, key) ∉ s.accessedStorageKeys
        · have hdc : (s.slotView ctx.recipient ctx.block.origState key).cold = true :=
            decide_eq_true hcold
          have hcold_true : ((ctx.recipient, key) ∉ s.accessedStorageKeys) = True :=
            eq_true hcold
          simp only [hdc, ↓reduceIte]
          by_cases hg : max Gas.coldSloadCost (Gas.callStipend + 1) ≤ m₂.gasLeft
          · have hlt : ¬ (m₂.gasLeft < max Gas.coldSloadCost (Gas.callStipend + 1)) := by omega
            have hg_raw :
                max (if (ctx.recipient, key) ∉ ((s.withMachine m₁).withMachine m₂).accessedStorageKeys
                      then Gas.coldSloadCost else Gas.warmStorageReadCost)
                    (Gas.callStipend + 1) ≤
                  ((s.withMachine m₁).withMachine m₂).gasLeft := by
              simpa [withMachine_twice, withMachine_gasLeft, withMachine_accessedStorageKeys,
                hcold] using hg
            rw [except_assert_eq_ok hg_raw]
            simp only [hlt, ↓reduceIte, withMachine_twice, withMachine_accessedStorageKeys]
            simp only [hcold_true, ↓reduceIte, Frame.State.slotView,
              addAccessedStorageKey_originalStorageValue, withMachine_originalStorageValue,
              recordStorageRead_storageValue, addAccessedStorageKey_storageValue,
              withMachine_storageValue, recordStorageRead_refund, addAccessedStorageKey_refund,
              withMachine_refund, addAccessedStorageKey_machine, recordStorageRead_machine,
              withRefund_machine, state_chargeGas_eq, Frame.State.creditStateGasRefund,
              Frame.State.liftMachinePure, Frame.State.withMachine_machine]
            cases hcg : (m₂.creditStateGasRefund (sstoreAmsterdamStateRefund state newVal _ _)).chargeGas
                (sstoreAmsterdamGasCost state newVal _ _ true) with
            | error e3 =>
              rcases e3 with ⟨err, m'⟩
              unfold Frame.State.applyStoreTouch
              rfl
            | ok m₄ =>
              simp only [state_chargeStateGas_eq, Frame.State.withMachine_machine]
              cases hsg : m₄.chargeStateGas (sstoreAmsterdamStateGas state newVal _ _) with
              | error e4 =>
                rcases e4 with ⟨err, m'⟩
                unfold Frame.State.applyStoreTouch
                rfl
              | ok m₅ =>
                unfold Frame.State.applyStoreTouch
                rfl
          · have hlt : m₂.gasLeft < max Gas.coldSloadCost (Gas.callStipend + 1) := by omega
            have hg_raw :
                ¬ (max (if (ctx.recipient, key) ∉
                        ((s.withMachine m₁).withMachine m₂).accessedStorageKeys
                      then Gas.coldSloadCost else Gas.warmStorageReadCost)
                    (Gas.callStipend + 1) ≤
                  ((s.withMachine m₁).withMachine m₂).gasLeft) := by
              simpa [withMachine_twice, withMachine_gasLeft, withMachine_accessedStorageKeys,
                hcold] using hg
            rw [except_assert_eq_error hg_raw]
            simp only [hlt, ↓reduceIte, withMachine_twice]
            rfl
        · have hdc : (s.slotView ctx.recipient ctx.block.origState key).cold = false :=
            decide_eq_false hcold
          have hcold_false : ((ctx.recipient, key) ∉ s.accessedStorageKeys) = False :=
            eq_false hcold
          simp only [hdc, Bool.false_eq_true, ↓reduceIte]
          by_cases hg : max Gas.warmStorageReadCost (Gas.callStipend + 1) ≤ m₂.gasLeft
          · have hlt : ¬ (m₂.gasLeft < max Gas.warmStorageReadCost (Gas.callStipend + 1)) := by
              omega
            have hg_raw :
                max (if (ctx.recipient, key) ∉ ((s.withMachine m₁).withMachine m₂).accessedStorageKeys
                      then Gas.coldSloadCost else Gas.warmStorageReadCost)
                    (Gas.callStipend + 1) ≤
                  ((s.withMachine m₁).withMachine m₂).gasLeft := by
              simpa [withMachine_twice, withMachine_gasLeft, withMachine_accessedStorageKeys,
                hcold] using hg
            rw [except_assert_eq_ok hg_raw]
            simp only [hlt, ↓reduceIte, withMachine_twice, withMachine_accessedStorageKeys]
            simp only [hcold_false, ↓reduceIte, Frame.State.slotView,
              withMachine_originalStorageValue, recordStorageRead_storageValue,
              withMachine_storageValue, recordStorageRead_refund, withMachine_refund,
              state_chargeGas_eq, Frame.State.creditStateGasRefund, Frame.State.liftMachinePure,
              Frame.State.withMachine_machine, recordStorageRead_machine, withRefund_machine]
            cases hcg : (m₂.creditStateGasRefund (sstoreAmsterdamStateRefund state newVal _ _)).chargeGas
                (sstoreAmsterdamGasCost state newVal _ _ false) with
            | error e3 =>
              rcases e3 with ⟨err, m'⟩
              unfold Frame.State.applyStoreTouch
              rfl
            | ok m₄ =>
              simp only [state_chargeStateGas_eq, Frame.State.withMachine_machine]
              cases hsg : m₄.chargeStateGas (sstoreAmsterdamStateGas state newVal _ _) with
              | error e4 =>
                rcases e4 with ⟨err, m'⟩
                unfold Frame.State.applyStoreTouch
                rfl
              | ok m₅ =>
                unfold Frame.State.applyStoreTouch
                rfl
          · have hlt : m₂.gasLeft < max Gas.warmStorageReadCost (Gas.callStipend + 1) := by omega
            have hg_raw :
                ¬ (max (if (ctx.recipient, key) ∉
                        ((s.withMachine m₁).withMachine m₂).accessedStorageKeys
                      then Gas.coldSloadCost else Gas.warmStorageReadCost)
                    (Gas.callStipend + 1) ≤
                  ((s.withMachine m₁).withMachine m₂).gasLeft) := by
              simpa [withMachine_twice, withMachine_gasLeft, withMachine_accessedStorageKeys,
                hcold] using hg
            rw [except_assert_eq_error hg_raw]
            simp only [hlt, ↓reduceIte, withMachine_twice]
            rfl
  · rw [assertDynamic_true hstat]; rfl

/-- **Bridge (`SSTORE`, all `ForkRules`):** `SstoreRow.ofRules ctx.block.rules` lifted through
`Frame.State.liftStore` equals `Checked.PlainOp.runCore pc ctx s .sstore` for every `ForkRules`
configuration, `pc`, `CallContext`, and `Frame.State`. -/
theorem SstoreRow.ofRules_lift_eq (pc : Nat) (ctx : Jaune.CallContext) (s : Frame.State) :
    s.liftStore ctx.block.rules ctx.recipient
        ((SstoreRow.ofRules ctx.block.rules).step ctx.isStatic
          (s.slotView ctx.recipient ctx.block.origState)) =
      PlainOp.runCore pc ctx s .sstore := by
  dsimp only [PlainOp.runCore]
  cases hs1 : ctx.block.rules.stateGas with
  | none =>
    cases hs2 : ctx.block.rules.sstore with
    | mk net sent =>
      cases hs3 : ctx.block.rules.access with
      | flat g =>
        cases net <;> cases sent <;> exact liftStore_sstoreLegacy_eq ctx s hs1
      | eip2929 =>
        cases net <;> cases sent
        · exact liftStore_sstoreLegacy_eq ctx s hs1
        · exact liftStore_sstoreLegacy_eq ctx s hs1
        · exact liftStore_sstoreLegacy_eq ctx s hs1
        · exact liftStore_sstoreBerlin_eq ctx s hs1 hs2 hs3
  | some state =>
    exact liftStore_sstoreAmsterdam_eq state ctx s hs1

theorem TstoreRow.ofRules_lift_eq (pc : Nat) (ctx : Jaune.CallContext) (s : Frame.State) :
    s.liftStore ctx.block.rules ctx.recipient
        ((TstoreRow.ofRules ctx.block.rules).step ctx.block.rules.opcodes ctx.isStatic) =
      PlainOp.runCore pc ctx s .tstore := by
  unfold Frame.State.liftStore TstoreRow.step TstoreRow.ofRules PlainOp.runCore
  dsimp only
  by_cases hav : ctx.block.rules.opcodes.transient
  · simp only [hav, ↓reduceIte, Bool.not_true, Bool.false_eq_true]
    cases hsg : ctx.block.rules.stateGas with
    | none =>
      dsimp only [Option.isSome, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false,
        Bool.true_and, bind, Except.bind, Frame.State.pop, Frame.State.liftMachineValue]
      cases hp1 : s.machine.pop with
      | error e1 => rcases e1 with ⟨err, m'⟩; rfl
      | ok p1 =>
        obtain ⟨key, m₁⟩ := p1
        dsimp only [Frame.State.withMachine_machine]
        cases hp2 : m₁.pop with
        | error e2 => rcases e2 with ⟨err, m'⟩; rfl
        | ok p2 =>
          obtain ⟨newVal, m₂⟩ := p2
          dsimp only [Frame.State.withMachine_machine]
          unfold Frame.State.chargeGas Frame.State.liftMachine
          dsimp only [Frame.State.withMachine_machine]
          cases hcg : m₂.chargeGas Gas.warmStorageReadCost with
          | error e3 => rcases e3 with ⟨err, m'⟩; rfl
          | ok m₃ =>
            dsimp only [Frame.State.assertDynamic, Except.assert, Jaune.CallContext.toChecked_isStatic, Frame.State.applyStoreTouch]
            by_cases hstat : ctx.isStatic <;> simp [hstat, withMachine_twice]
    | some _ =>
      dsimp only [Option.isSome, Bool.true_and, Bool.not_true, Bool.false_and, Bool.false_eq_true,
        ↓reduceIte, bind, Except.bind, Frame.State.assertDynamic, Except.assert,
        Jaune.CallContext.toChecked_isStatic]
      by_cases hstat : ctx.isStatic
      · simp [hstat]; rfl
      · simp only [hstat, Bool.not_false, ↓reduceIte]
        unfold Frame.State.pop Frame.State.liftMachineValue
        cases hp1 : s.machine.pop with
        | error e1 => rcases e1 with ⟨err, m'⟩; rfl
        | ok p1 =>
          obtain ⟨key, m₁⟩ := p1
          dsimp only [Frame.State.withMachine_machine]
          cases hp2 : m₁.pop with
          | error e2 => rcases e2 with ⟨err, m'⟩; rfl
          | ok p2 =>
            obtain ⟨newVal, m₂⟩ := p2
            dsimp only [Frame.State.withMachine_machine]
            unfold Frame.State.chargeGas Frame.State.liftMachine
            dsimp only [Frame.State.withMachine_machine]
            cases hcg : m₂.chargeGas Gas.warmStorageReadCost with
            | error e3 => rcases e3 with ⟨err, m'⟩; rfl
            | ok m₃ =>
              simp [Frame.State.applyStoreTouch, withMachine_twice]
  · simp [hav]; rfl

end Jaune.Checked.Arms
