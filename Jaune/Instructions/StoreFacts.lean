import Jaune.Instructions.Store
import Jaune.MessageCall.CheckedPlain

/-! Effect laws and semantic bridges for `SstoreRow` and `TstoreRow`.

Every theorem in this module proves that `SstoreRow.ofRules` and `TstoreRow.ofRules`, executed
through `Frame.State.liftStore`, satisfy restricted-effect laws (explicit stack pop order, sentry
bounds, gas-measure monotonicity, and exact world/substate/trail projections), and that they are
`PlainOp.run` for `SSTORE` and `TSTORE` by the dispatch's definition, across every `ForkRules`
configuration and `Fork`, without introducing any unrestricted state-transforming function. Their
agreement with the per-opcode arms is in `Jaune.Bridge.G2b.CheckedStoreAgreement`. -/

namespace Jaune.Checked

open Jaune

private theorem pop_ok {m out : Machine} {x : U256} (h : m.pop = .ok (x, out)) :
    ∃ rest, m.stack = x :: rest ∧ out = { m with stack := rest } := by
  unfold Machine.pop at h
  split at h
  · contradiction
  · rename_i first rest hs
    cases h
    exact ⟨rest, hs, rfl⟩

private theorem pop_error {m out : Machine} {e : ExceptionalHalt}
    (h : m.pop = .error (e, out)) :
    e = .stackUnderflow .none ∧ m.stack = [] ∧ out = { m with stack := [] } := by
  rcases m with ⟨stk, mem, gl, sg, rd⟩
  cases stk with
  | nil =>
    simp only [Machine.pop, Except.error.injEq, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩
    exact ⟨rfl, rfl, rfl⟩
  | cons _ _ => simp [Machine.pop] at h

private theorem charged_ok {cost : Nat} {m out : Machine}
    (h : m.chargeGas cost = .ok out) :
    cost ≤ m.gasLeft ∧ out = { m with gasLeft := m.gasLeft - cost } := by
  unfold Machine.chargeGas safeSub at h
  by_cases hle : cost ≤ m.gasLeft
  · simp only [hle, ↓reduceIte, Except.ok.injEq] at h
    exact ⟨hle, h.symm⟩
  · simp [hle] at h

private theorem charged_error {cost : Nat} {m out : Machine} {e : ExceptionalHalt}
    (h : m.chargeGas cost = .error (e, out)) :
    e = .outOfGas .none ∧ m.gasLeft < cost ∧ out = m := by
  unfold Machine.chargeGas safeSub at h
  by_cases hle : cost ≤ m.gasLeft
  · simp [hle] at h
  · simp only [hle, ↓reduceIte, Except.error.injEq, Prod.mk.injEq] at h
    exact ⟨h.1.symm, Nat.lt_of_not_le hle, h.2.symm⟩

@[simp] theorem Machine.creditStateGasRefund_zero (m : Machine) :
    m.creditStateGasRefund 0 = m := by
  rcases m with ⟨stk, mem, gl, sg, rd⟩
  simp only [Machine.creditStateGasRefund, Nat.zero_min, Nat.add_zero, Nat.sub_zero]

@[simp] theorem Machine.creditStateGasRefund_memory (amount : Nat) (m : Machine) :
    (m.creditStateGasRefund amount).memory = m.memory := rfl

@[simp] theorem Machine.creditStateGasRefund_returnData (amount : Nat) (m : Machine) :
    (m.creditStateGasRefund amount).returnData = m.returnData := rfl

@[simp] theorem Machine.chargeStateGas_zero (m : Machine) :
    m.chargeStateGas 0 = .ok m := by
  simp only [Machine.chargeStateGas, Nat.zero_le, ↓reduceIte, Nat.sub_zero]

theorem Machine.chargeStateGas_ok {amount : Nat} {m out : Machine}
    (h : m.chargeStateGas amount = .ok out) :
    out.stack = m.stack ∧ out.memory = m.memory ∧ out.returnData = m.returnData ∧
      out.gasMeasure = m.gasMeasure := by
  unfold Machine.chargeStateGas at h
  split at h
  · cases h
    exact ⟨rfl, rfl, rfl, rfl⟩
  · split at h
    · cases h
      rename_i hgt hle
      exact ⟨rfl, rfl, rfl, by simp only [Machine.gasMeasure]; omega⟩
    · cases h

theorem Machine.chargeStateGas_error {amount : Nat} {m out : Machine} {e : ExceptionalHalt}
    (h : m.chargeStateGas amount = .error (e, out)) :
    e = .outOfGas .none ∧ out = m := by
  unfold Machine.chargeStateGas at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases h
      exact ⟨rfl, rfl⟩

private def applyPrefix (rules : ForkRules) (recipient : Address)
    (touch : StoreTouch) (s : Frame.State) : Frame.State :=
  let s := match touch.readStorage with
    | none => s
    | some k => s.recordStorageRead rules recipient k
  let s := match touch.warmKey with
    | none => s
    | some k => s.addAccessedStorageKey recipient k
  let s := match touch.newRefund with
    | none => s
    | some r => s.withRefund r
  if touch.readAccount then s.recordAccountRead rules recipient else s

private theorem applyStoreTouch_eq_write (rules : ForkRules) (recipient : Address)
    (touch : StoreTouch) (s : Frame.State) :
    s.applyStoreTouch rules recipient touch =
      match touch.write with
      | none => applyPrefix rules recipient touch s
      | some (.storage k v) => (applyPrefix rules recipient touch s).setStorageValue recipient k v
      | some (.transient k v) =>
        (applyPrefix rules recipient touch s).setTransientValue recipient k v := rfl

private theorem applyStoreTouch_prefix (rules : ForkRules) (recipient : Address)
    (touch : StoreTouch) (s : Frame.State) :
    let s4 := applyPrefix rules recipient touch s
    s4.machine = s.machine ∧ s4.world = s.world ∧
      s4.logs = s.logs ∧ s4.selfDestructs = s.selfDestructs ∧
      s4.accessedAddresses = s.accessedAddresses ∧
      s4.touchedAccounts = s.touchedAccounts ∧
      s4.createdAccounts = s.createdAccounts := by
  rcases touch with ⟨rs, wk, nr, ra, wr⟩
  by_cases hbal : rules.blockAccessListRules.isSome
  · cases rs <;> cases wk <;> cases nr <;> cases ra <;>
      simp [applyPrefix, Frame.State.recordStorageRead, Frame.State.recordAccountRead,
        Frame.State.logs, Frame.State.selfDestructs, Frame.State.accessedAddresses,
        Frame.State.touchedAccounts, Frame.State.createdAccounts,
        Frame.State.addAccessedStorageKey, Frame.State.withRefund, Frame.State.withTrail,
        Frame.State.withSubstate, Substate.addAccessedStorageKey, Trail.readAccount,
        Trail.readStorage, hbal]
  · cases rs <;> cases wk <;> cases nr <;> cases ra <;>
      simp [applyPrefix, Frame.State.recordStorageRead, Frame.State.recordAccountRead,
        Frame.State.logs, Frame.State.selfDestructs, Frame.State.accessedAddresses,
        Frame.State.touchedAccounts, Frame.State.createdAccounts,
        Frame.State.addAccessedStorageKey, Frame.State.withRefund, Frame.State.withTrail,
        Frame.State.withSubstate, Substate.addAccessedStorageKey, hbal]

private theorem applyStoreTouch_world_none (rules : ForkRules) (recipient : Address)
    (touch : StoreTouch) (s : Frame.State) (hw : touch.write = none) :
    (s.applyStoreTouch rules recipient touch).world = s.world := by
  have hpre := applyStoreTouch_prefix rules recipient touch s
  rw [applyStoreTouch_eq_write, hw]
  exact hpre.2.1

private theorem applyStoreTouch_world_storage (rules : ForkRules) (recipient : Address)
    (touch : StoreTouch) (s : Frame.State) {k v : U256}
    (hw : touch.write = some (.storage k v)) :
    (s.applyStoreTouch rules recipient touch).world = (s.setStorageValue recipient k v).world := by
  have hpre := applyStoreTouch_prefix rules recipient touch s
  rw [applyStoreTouch_eq_write, hw]
  dsimp only [Frame.State.setStorageValue, Frame.State.withWorld_world]
  rw [hpre.2.1]

private theorem applyStoreTouch_world_transient (rules : ForkRules) (recipient : Address)
    (touch : StoreTouch) (s : Frame.State) {k v : U256}
    (hw : touch.write = some (.transient k v)) :
    (s.applyStoreTouch rules recipient touch).world = (s.setTransientValue recipient k v).world := by
  have hpre := applyStoreTouch_prefix rules recipient touch s
  rw [applyStoreTouch_eq_write, hw]
  dsimp only [Frame.State.setTransientValue, Frame.State.withTransientStorage,
    Frame.State.withWorld_world, Frame.State.transientStorage]
  rw [hpre.2.1]

@[simp] theorem Frame.State.applyStoreTouch_empty (rules : ForkRules) (recipient : Address)
    (s : Frame.State) :
    s.applyStoreTouch rules recipient {} = s := rfl

@[simp] theorem Frame.State.applyStoreTouch_machine (rules : ForkRules) (recipient : Address)
    (touch : StoreTouch) (s : Frame.State) :
    (s.applyStoreTouch rules recipient touch).machine = s.machine := by
  have hpre := applyStoreTouch_prefix rules recipient touch s
  unfold Frame.State.applyStoreTouch
  cases touch.write with
  | none => exact hpre.1
  | some w => cases w <;> exact hpre.1

@[simp] theorem Frame.State.applyStoreTouch_logs (rules : ForkRules) (recipient : Address)
    (touch : StoreTouch) (s : Frame.State) :
    (s.applyStoreTouch rules recipient touch).logs = s.logs := by
  have hpre := applyStoreTouch_prefix rules recipient touch s
  unfold Frame.State.applyStoreTouch Frame.State.logs
  cases touch.write with
  | none => exact hpre.2.2.1
  | some w => cases w <;> exact hpre.2.2.1

@[simp] theorem Frame.State.applyStoreTouch_selfDestructs (rules : ForkRules) (recipient : Address)
    (touch : StoreTouch) (s : Frame.State) :
    (s.applyStoreTouch rules recipient touch).selfDestructs = s.selfDestructs := by
  have hpre := applyStoreTouch_prefix rules recipient touch s
  unfold Frame.State.applyStoreTouch Frame.State.selfDestructs
  cases touch.write with
  | none => exact hpre.2.2.2.1
  | some w => cases w <;> exact hpre.2.2.2.1

@[simp] theorem Frame.State.applyStoreTouch_accessedAddresses (rules : ForkRules)
    (recipient : Address) (touch : StoreTouch) (s : Frame.State) :
    (s.applyStoreTouch rules recipient touch).accessedAddresses = s.accessedAddresses := by
  have hpre := applyStoreTouch_prefix rules recipient touch s
  unfold Frame.State.applyStoreTouch Frame.State.accessedAddresses
  cases touch.write with
  | none => exact hpre.2.2.2.2.1
  | some w => cases w <;> exact hpre.2.2.2.2.1

@[simp] theorem Frame.State.applyStoreTouch_touchedAccounts (rules : ForkRules)
    (recipient : Address) (touch : StoreTouch) (s : Frame.State) :
    (s.applyStoreTouch rules recipient touch).touchedAccounts = s.touchedAccounts := by
  have hpre := applyStoreTouch_prefix rules recipient touch s
  unfold Frame.State.applyStoreTouch Frame.State.touchedAccounts
  cases touch.write with
  | none => exact hpre.2.2.2.2.2.1
  | some w => cases w <;> exact hpre.2.2.2.2.2.1

@[simp] theorem Frame.State.applyStoreTouch_createdAccounts (rules : ForkRules)
    (recipient : Address) (touch : StoreTouch) (s : Frame.State) :
    (s.applyStoreTouch rules recipient touch).createdAccounts = s.createdAccounts := by
  have hpre := applyStoreTouch_prefix rules recipient touch s
  unfold Frame.State.applyStoreTouch Frame.State.createdAccounts
  cases touch.write with
  | none => exact hpre.2.2.2.2.2.2
  | some w => cases w <;> exact hpre.2.2.2.2.2.2

theorem Frame.State.applyStoreTouch_transientStorage_ne_transient (rules : ForkRules)
    (recipient : Address) {touch : StoreTouch}
    (hnot : ∀ k v, touch.write ≠ some (.transient k v)) (s : Frame.State) :
    (s.applyStoreTouch rules recipient touch).transientStorage = s.transientStorage := by
  unfold Frame.State.transientStorage
  cases hw : touch.write with
  | none => rw [applyStoreTouch_world_none rules recipient touch s hw]
  | some w =>
    cases w with
    | storage k v => rw [applyStoreTouch_world_storage rules recipient touch s hw]; rfl
    | transient k v => exact absurd hw (hnot k v)

theorem Frame.State.applyStoreTouch_state_ne_storage (rules : ForkRules)
    (recipient : Address) {touch : StoreTouch}
    (hnot : ∀ k v, touch.write ≠ some (.storage k v)) (s : Frame.State) :
    (s.applyStoreTouch rules recipient touch).state = s.state := by
  unfold Frame.State.state
  cases hw : touch.write with
  | none => rw [applyStoreTouch_world_none rules recipient touch s hw]
  | some w =>
    cases w with
    | transient k v => rw [applyStoreTouch_world_transient rules recipient touch s hw]; rfl
    | storage k v => exact absurd hw (hnot k v)

theorem Frame.State.applyStoreTouch_substate_of_none (rules : ForkRules) (recipient : Address)
    {touch : StoreTouch} (hwk : touch.warmKey = none) (hnr : touch.newRefund = none)
    (s : Frame.State) :
    (s.applyStoreTouch rules recipient touch).substate = s.substate := by
  unfold Frame.State.applyStoreTouch
  rcases touch with ⟨rs, wk, nr, ra, wr⟩
  dsimp only at hwk hnr
  subst hwk; subst hnr
  cases rs <;> cases ra <;>
    (cases wr with
    | none => rfl
    | some w => cases w <;> rfl)

theorem Frame.State.applyStoreTouch_trail_of_none (rules : ForkRules) (recipient : Address)
    {touch : StoreTouch} (hrs : touch.readStorage = none) (hra : touch.readAccount = false)
    (s : Frame.State) :
    (s.applyStoreTouch rules recipient touch).trail = s.trail := by
  unfold Frame.State.applyStoreTouch
  rcases touch with ⟨rs, wk, nr, ra, wr⟩
  dsimp only at hrs hra
  subst hrs; subst hra
  cases wk <;> cases nr <;>
    (cases wr with
    | none => rfl
    | some w => cases w <;> rfl)

private theorem applyStoreTouch_account_nonstorage (rules : ForkRules) (recipient : Address)
    {touch : StoreTouch} (hnot : ∀ k v, touch.write ≠ some (.transient k v))
    (s : Frame.State) (a : Address) :
    let a' := (s.applyStoreTouch rules recipient touch).account a
    let a0 := s.account a
    a'.balance = a0.balance ∧ a'.nonce = a0.nonce ∧ a'.code = a0.code := by
  dsimp only
  unfold Frame.State.account Frame.State.state
  cases hw : touch.write with
  | none =>
    rw [applyStoreTouch_world_none rules recipient touch s hw]
    exact ⟨rfl, rfl, rfl⟩
  | some w =>
    cases w with
    | transient k v => exact absurd hw (hnot k v)
    | storage k v =>
      rw [applyStoreTouch_world_storage rules recipient touch s hw]
      by_cases ha : recipient = a
      · subst ha
        dsimp only [Frame.State.setStorageValue, Frame.State.withWorld_world]
        rw [State.setStorVal_get_self]
        exact ⟨rfl, rfl, rfl⟩
      · dsimp only [Frame.State.setStorageValue, Frame.State.withWorld_world]
        rw [State.setStorVal_get_ne _ ha]
        exact ⟨rfl, rfl, rfl⟩

theorem Frame.State.applyStoreTouch_balance (rules : ForkRules) (recipient : Address)
    {touch : StoreTouch} (hnot : ∀ k v, touch.write ≠ some (.transient k v))
    (s : Frame.State) (a : Address) :
    (s.applyStoreTouch rules recipient touch).balance a = s.balance a :=
  (applyStoreTouch_account_nonstorage rules recipient hnot s a).1

theorem Frame.State.applyStoreTouch_nonce (rules : ForkRules) (recipient : Address)
    {touch : StoreTouch} (hnot : ∀ k v, touch.write ≠ some (.transient k v))
    (s : Frame.State) (a : Address) :
    ((s.applyStoreTouch rules recipient touch).account a).nonce = (s.account a).nonce :=
  (applyStoreTouch_account_nonstorage rules recipient hnot s a).2.1

theorem Frame.State.applyStoreTouch_code (rules : ForkRules) (recipient : Address)
    {touch : StoreTouch} (hnot : ∀ k v, touch.write ≠ some (.transient k v))
    (s : Frame.State) (a : Address) :
    (s.applyStoreTouch rules recipient touch).code a = s.code a :=
  (applyStoreTouch_account_nonstorage rules recipient hnot s a).2.2

theorem Frame.State.applyStoreTouch_storageValue_ne_addr (rules : ForkRules) (recipient : Address)
    {touch : StoreTouch} (hnot : ∀ k v, touch.write ≠ some (.transient k v))
    (s : Frame.State) {a : Address} (hne : recipient ≠ a) (k : U256) :
    (s.applyStoreTouch rules recipient touch).storageValue a k = s.storageValue a k := by
  unfold Frame.State.storageValue Frame.State.account Frame.State.state
  cases hw : touch.write with
  | none => rw [applyStoreTouch_world_none rules recipient touch s hw]
  | some w =>
    cases w with
    | transient _ _ => exact absurd hw (hnot _ _)
    | storage sk sv =>
      rw [applyStoreTouch_world_storage rules recipient touch s hw]
      dsimp only [Frame.State.setStorageValue, Frame.State.withWorld_world]
      rw [State.setStorVal_get_ne _ hne]

theorem Frame.State.applyStoreTouch_storageValue_ne_key (rules : ForkRules) (recipient : Address)
    {touch : StoreTouch} (s : Frame.State) {k : U256}
    (hk : ∀ v, touch.write ≠ some (.storage k v))
    (hnot : ∀ k0 v0, touch.write ≠ some (.transient k0 v0)) :
    (s.applyStoreTouch rules recipient touch).storageValue recipient k =
      s.storageValue recipient k := by
  unfold Frame.State.storageValue Frame.State.account Frame.State.state
  cases hw : touch.write with
  | none => rw [applyStoreTouch_world_none rules recipient touch s hw]
  | some w =>
    cases w with
    | transient k0 v0 => exact absurd hw (hnot k0 v0)
    | storage sk sv =>
      rw [applyStoreTouch_world_storage rules recipient touch s hw]
      dsimp only [Frame.State.setStorageValue, Frame.State.withWorld_world]
      have hne : sk ≠ k := by
        intro heq
        subst heq
        exact hk sv hw
      rw [State.setStorVal_get_self, Storage.get_set_ne _ hne]

/-! ### `SstoreRow` effect laws -/

/-- Exact effect characterization of a successful `SstoreRow.step`. -/
theorem SstoreRow.step_ok {row : SstoreRow} {isStatic : Bool} {slot : U256 → SlotView}
    {m out : Machine} {touch : StoreTouch}
    (h : row.step isStatic slot m = .ok (out, touch)) :
    ∃ key newVal rest,
      isStatic = false ∧
      m.stack = key :: newVal :: rest ∧
      row.sentry (row.tracksWarmth && (slot key).cold) ≤ m.gasLeft ∧
      row.gasCost (row.tracksWarmth && (slot key).cold)
        newVal (slot key).original (slot key).current ≤
        m.gasLeft + min (row.stateGasRefund newVal (slot key).original (slot key).current)
          m.stateGas.spilled ∧
      out.stack = rest ∧
      out.memory = m.memory ∧
      out.returnData = m.returnData ∧
      out.gasMeasure = m.gasMeasure - row.gasCost (row.tracksWarmth && (slot key).cold)
        newVal (slot key).original (slot key).current ∧
      touch =
        { readStorage := some key
          warmKey := if row.tracksWarmth && (slot key).cold then some key else none
          newRefund := some (row.refundCounter newVal (slot key).original
            (slot key).current (slot key).refund)
          readAccount := true
          write := some (.storage key newVal) } := by
  unfold SstoreRow.step at h
  split at h
  · contradiction
  · cases hp1 : m.pop with
    | error e => rw [hp1] at h; cases h
    | ok p1 =>
      rw [hp1] at h
      obtain ⟨key, m₁⟩ := p1
      dsimp only at h
      cases hp2 : m₁.pop with
      | error e => rw [hp2] at h; cases h
      | ok p2 =>
        rw [hp2] at h
        obtain ⟨newVal, m₂⟩ := p2
        dsimp only at h
        split at h
        · contradiction
        · rename_i hsf hsentry
          cases hcg : (m₂.creditStateGasRefund
              (row.stateGasRefund newVal (slot key).original (slot key).current)).chargeGas
              (row.gasCost (row.tracksWarmth && (slot key).cold) newVal
                (slot key).original (slot key).current) with
          | error e => rw [hcg] at h; cases h
          | ok m₄ =>
            rw [hcg] at h
            dsimp only at h
            cases hsg : m₄.chargeStateGas
                (row.stateGasCost newVal (slot key).original (slot key).current) with
            | error e => rw [hsg] at h; cases h
            | ok m₅ =>
              rw [hsg] at h
              dsimp only at h
              split at h
              · contradiction
              · rename_i hpost
                cases h
                have hstat : isStatic = false := by
                  cases isStatic <;> cases row.staticFirst <;> simp_all
                obtain ⟨tail, hstk1, hm1⟩ := pop_ok hp1
                obtain ⟨rest, hstk2, hm2⟩ := pop_ok hp2
                have hstk : m.stack = key :: newVal :: rest := by
                  rw [hstk1]
                  simpa [hm1] using hstk2
                obtain ⟨hle_gas, rfl⟩ := charged_ok hcg
                obtain ⟨hstk_sg, hmem_sg, hrd_sg, hgm_sg⟩ := Machine.chargeStateGas_ok hsg
                have hgm₃ : (m₂.creditStateGasRefund
                    (row.stateGasRefund newVal (slot key).original (slot key).current)).gasMeasure =
                    m₂.gasMeasure :=
                  Machine.creditStateGasRefund_gasMeasure _ _
                have hgm_out : ({ m₂.creditStateGasRefund
                    (row.stateGasRefund newVal (slot key).original (slot key).current) with
                    gasLeft := (m₂.creditStateGasRefund
                      (row.stateGasRefund newVal (slot key).original (slot key).current)).gasLeft -
                      row.gasCost (row.tracksWarmth && (slot key).cold) newVal
                        (slot key).original (slot key).current }).gasMeasure =
                    m₂.gasMeasure - row.gasCost (row.tracksWarmth && (slot key).cold) newVal
                      (slot key).original (slot key).current := by
                  simp only [Machine.gasMeasure] at hgm₃ ⊢
                  omega
                have hm2_gm : m₂.gasMeasure = m.gasMeasure := by
                  rw [hm2, hm1]; rfl
                subst hm2; subst hm1
                refine ⟨key, newVal, rest, hstat, hstk, ?_, hle_gas, hstk_sg, hmem_sg, hrd_sg, ?_,
                  rfl⟩
                · exact Nat.le_of_not_lt hsentry
                · rw [hgm_sg, hgm_out, hm2_gm]

/-- Exact failure characterization of `SstoreRow.step`: covers pre-pop static failure,
stack underflow, sentry failure, execution/state out-of-gas, and post-charge static failure. In all
error cases `out.memory = m.memory`, `out.returnData = m.returnData`, `out.gasMeasure ≤ m.gasMeasure`,
`touch.readAccount = false`, and `touch.write = none`. -/
theorem SstoreRow.step_error {row : SstoreRow} {isStatic : Bool} {slot : U256 → SlotView}
    {m out : Machine} {e : ExceptionalHalt} {touch : StoreTouch}
    (h : row.step isStatic slot m = .error (e, out, touch)) :
    (e = .writeInStaticContext .none ∨ e = .stackUnderflow .none ∨ e = .outOfGas .none) ∧
      out.memory = m.memory ∧
      out.returnData = m.returnData ∧
      out.gasMeasure ≤ m.gasMeasure ∧
      touch.readAccount = false ∧
      touch.write = none ∧
      (∀ k v, touch.write ≠ some (.transient k v)) ∧
      (∀ k, (∃ v, touch.write = some (.storage k v)) → False) := by
  unfold SstoreRow.step at h
  split at h
  · cases h
    exact ⟨Or.inl rfl, rfl, rfl, le_rfl, rfl, rfl, (fun _ _ hc => nomatch hc),
      (fun _ ⟨_, hc⟩ => nomatch hc)⟩
  · cases hp1 : m.pop with
    | error e1 =>
      rcases e1 with ⟨err1, out1⟩
      rw [hp1] at h
      cases h
      obtain ⟨rfl, _, rfl⟩ := pop_error hp1
      exact ⟨Or.inr (Or.inl rfl), rfl, rfl, le_rfl, rfl, rfl, (fun _ _ hc => nomatch hc),
        (fun _ ⟨_, hc⟩ => nomatch hc)⟩
    | ok p1 =>
      rw [hp1] at h
      obtain ⟨key, m₁⟩ := p1
      dsimp only at h
      cases hp2 : m₁.pop with
      | error e2 =>
        rcases e2 with ⟨err2, out2⟩
        rw [hp2] at h
        cases h
        obtain ⟨_, _, hm1⟩ := pop_ok hp1
        obtain ⟨rfl, _, rfl⟩ := pop_error hp2
        subst hm1
        exact ⟨Or.inr (Or.inl rfl), rfl, rfl, le_rfl, rfl, rfl, (fun _ _ hc => nomatch hc),
          (fun _ ⟨_, hc⟩ => nomatch hc)⟩
      | ok p2 =>
        rw [hp2] at h
        obtain ⟨newVal, m₂⟩ := p2
        dsimp only at h
        obtain ⟨_, _, hm1⟩ := pop_ok hp1
        obtain ⟨_, _, hm2⟩ := pop_ok hp2
        split at h
        · cases h
          subst hm2; subst hm1
          exact ⟨Or.inr (Or.inr rfl), rfl, rfl, le_rfl, rfl, rfl, (fun _ _ hc => nomatch hc),
            (fun _ ⟨_, hc⟩ => nomatch hc)⟩
        · cases hcg : (m₂.creditStateGasRefund
              (row.stateGasRefund newVal (slot key).original (slot key).current)).chargeGas
              (row.gasCost (row.tracksWarmth && (slot key).cold) newVal
                (slot key).original (slot key).current) with
          | error e3 =>
            rcases e3 with ⟨err3, out3⟩
            rw [hcg] at h
            cases h
            obtain ⟨rfl, _, rfl⟩ := charged_error hcg
            have hgm₃ := Machine.creditStateGasRefund_gasMeasure
              (row.stateGasRefund newVal (slot key).original (slot key).current) m₂
            have hm2_gm : m₂.gasMeasure = m.gasMeasure := by rw [hm2, hm1]; rfl
            subst hm2; subst hm1
            exact ⟨Or.inr (Or.inr rfl), rfl, rfl, by rw [hgm₃, hm2_gm], rfl, rfl,
              (fun _ _ hc => nomatch hc), (fun _ ⟨_, hc⟩ => nomatch hc)⟩
          | ok m₄ =>
            rw [hcg] at h
            dsimp only at h
            cases hsg : m₄.chargeStateGas
                (row.stateGasCost newVal (slot key).original (slot key).current) with
            | error e4 =>
              rcases e4 with ⟨err4, out4⟩
              rw [hsg] at h
              cases h
              obtain ⟨rfl, rfl⟩ := Machine.chargeStateGas_error hsg
              obtain ⟨hle_gas, rfl⟩ := charged_ok hcg
              have hgm₃ := Machine.creditStateGasRefund_gasMeasure
                (row.stateGasRefund newVal (slot key).original (slot key).current) m₂
              have hm2_gm : m₂.gasMeasure = m.gasMeasure := by rw [hm2, hm1]; rfl
              have hgm_le : ({ m₂.creditStateGasRefund
                  (row.stateGasRefund newVal (slot key).original (slot key).current) with
                  gasLeft := (m₂.creditStateGasRefund
                    (row.stateGasRefund newVal (slot key).original (slot key).current)).gasLeft -
                    row.gasCost (row.tracksWarmth && (slot key).cold) newVal
                      (slot key).original (slot key).current }).gasMeasure ≤ m₂.gasMeasure := by
                simp only [Machine.gasMeasure] at hgm₃ ⊢
                omega
              subst hm2; subst hm1
              exact ⟨Or.inr (Or.inr rfl), rfl, rfl, by rw [← hm2_gm]; exact hgm_le, rfl, rfl,
                (fun _ _ hc => nomatch hc), (fun _ ⟨_, hc⟩ => nomatch hc)⟩
            | ok m₅ =>
              rw [hsg] at h
              dsimp only at h
              split at h
              · cases h
                obtain ⟨hle_gas, rfl⟩ := charged_ok hcg
                obtain ⟨_, hmem_sg, hrd_sg, hgm_sg⟩ := Machine.chargeStateGas_ok hsg
                have hgm₃ := Machine.creditStateGasRefund_gasMeasure
                  (row.stateGasRefund newVal (slot key).original (slot key).current) m₂
                have hm2_gm : m₂.gasMeasure = m.gasMeasure := by rw [hm2, hm1]; rfl
                have hgm_le : ({ m₂.creditStateGasRefund
                    (row.stateGasRefund newVal (slot key).original (slot key).current) with
                    gasLeft := (m₂.creditStateGasRefund
                      (row.stateGasRefund newVal (slot key).original (slot key).current)).gasLeft -
                      row.gasCost (row.tracksWarmth && (slot key).cold) newVal
                        (slot key).original (slot key).current }).gasMeasure ≤ m₂.gasMeasure := by
                  simp only [Machine.gasMeasure] at hgm₃ ⊢
                  omega
                subst hm2; subst hm1
                refine ⟨Or.inl rfl, hmem_sg, hrd_sg, ?_, rfl, rfl,
                  (fun _ _ hc => nomatch hc), (fun _ ⟨_, hc⟩ => nomatch hc)⟩
                rw [hgm_sg, ← hm2_gm]
                exact hgm_le
              · cases h

theorem SstoreRow.step_memory (row : SstoreRow) (isStatic : Bool) (slot : U256 → SlotView)
    (m : Machine) :
    (match row.step isStatic slot m with | .ok (out, _) | .error (_, out, _) => out.memory) =
      m.memory := by
  cases hs : row.step isStatic slot m with
  | ok res => exact (SstoreRow.step_ok hs).choose_spec.choose_spec.choose_spec.2.2.2.2.2.1
  | error err => exact (SstoreRow.step_error hs).2.1

theorem SstoreRow.step_returnData (row : SstoreRow) (isStatic : Bool) (slot : U256 → SlotView)
    (m : Machine) :
    (match row.step isStatic slot m with | .ok (out, _) | .error (_, out, _) => out.returnData) =
      m.returnData := by
  cases hs : row.step isStatic slot m with
  | ok res => exact (SstoreRow.step_ok hs).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.1
  | error err => exact (SstoreRow.step_error hs).2.2.1

theorem SstoreRow.step_gasMeasure_lt_of_ok {row : SstoreRow} {isStatic : Bool}
    {slot : U256 → SlotView} {m out : Machine} {touch : StoreTouch}
    (hpos : ∀ isCold newVal origVal currVal, 0 < row.gasCost isCold newVal origVal currVal)
    (h : row.step isStatic slot m = .ok (out, touch)) :
    out.gasMeasure < m.gasMeasure := by
  obtain ⟨key, newVal, _, _, _, _, hcost_le, _, _, _, hgm, _⟩ := SstoreRow.step_ok h
  have hc := hpos (row.tracksWarmth && (slot key).cold) newVal (slot key).original (slot key).current
  have hle : m.gasLeft + min (row.stateGasRefund newVal (slot key).original (slot key).current)
      m.stateGas.spilled ≤ m.gasMeasure := by
    simp only [Machine.gasMeasure]
    have hsp : min (row.stateGasRefund newVal (slot key).original (slot key).current)
        m.stateGas.spilled ≤ m.stateGas.spilled := Nat.min_le_right _ _
    omega
  omega

theorem SstoreRow.ofRules_gasCost_pos (rules : ForkRules) (hacc : rules.access.Valid) :
    ∀ isCold newVal origVal currVal,
      0 < (SstoreRow.ofRules rules).gasCost isCold newVal origVal currVal := by
  intro isCold newVal origVal currVal
  unfold SstoreRow.ofRules
  cases hsg : rules.stateGas with
  | none =>
    dsimp only
    exact sstoreRegimeGasCost_pos rules.sstore hacc _ newVal origVal currVal
  | some state =>
    dsimp only
    unfold sstoreAmsterdamGasCost Gas.coldSloadCost Gas.warmStorageReadCost
    split_ifs <;> omega

theorem SstoreRow.ofRules_fork_gasCost_pos (f : Fork) :
    ∀ isCold newVal origVal currVal,
      0 < (SstoreRow.ofRules (Fork.ruleSet f)).gasCost isCold newVal origVal currVal := by
  apply SstoreRow.ofRules_gasCost_pos
  cases f <;> decide

/-! ### `SstoreRow` bridge across all `ForkRules` and `Fork`s -/

theorem SstoreRow.ofRules_run_eq (r : Frame.Running) :
    r.state.liftStore r.context.block.rules r.context.recipient
        ((SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
          (r.state.slotView r.context.recipient r.context.block.origState)) =
      PlainOp.run r .sstore := rfl

theorem SstoreRow.ofRules_run_fork_eq (f : Fork) (r : Frame.Running)
    (hf : r.context.block.fork = f) :
    r.state.liftStore (Fork.ruleSet f) r.context.recipient
        ((SstoreRow.ofRules (Fork.ruleSet f)).step r.context.isStatic
          (r.state.slotView r.context.recipient r.context.block.origState)) =
      PlainOp.run r .sstore := by
  have hr : r.context.block.rules = Fork.ruleSet f := by simp only [BenvStat.rules, hf]
  rw [← hr]
  exact SstoreRow.ofRules_run_eq r

/-- The exact rule projection `.sstore` reads from `ForkRules`:
`(stateGas, sstore, access, gas.storageClearRefund, blockAccessListRules.isSome)`. -/
def PlainOp.sstoreRuleReads (rules : ForkRules) :
    Option StateGasRules × SstoreRules × AccessSchedule × Nat × Bool :=
  (rules.stateGas, rules.sstore, rules.access, rules.gas.storageClearRefund,
    rules.blockAccessListRules.isSome)

private theorem applyStoreTouch_eq_of {r1 r2 : ForkRules}
    (h : r1.blockAccessListRules.isSome = r2.blockAccessListRules.isSome) (recipient : Address)
    (touch : StoreTouch) (s : Frame.State) :
    s.applyStoreTouch r1 recipient touch = s.applyStoreTouch r2 recipient touch := by
  unfold Frame.State.applyStoreTouch
  simp only [Frame.State.recordStorageRead, Frame.State.recordAccountRead, h]

private theorem sstoreRow_ofRules_eq_of {r1 r2 : ForkRules}
    (hsg : r1.stateGas = r2.stateGas)
    (hss : r1.sstore = r2.sstore)
    (hacc : r1.access = r2.access)
    (hclr : r1.gas.storageClearRefund = r2.gas.storageClearRefund) :
    SstoreRow.ofRules r1 = SstoreRow.ofRules r2 := by
  unfold SstoreRow.ofRules
  cases hs1 : r1.stateGas with
  | none =>
    have hs2 : r2.stateGas = none := by rw [← hsg, hs1]
    simp only [hs2]
    congr 1
    · rw [hacc]
    · funext _; rw [hss]
    · funext _ _ _ _; rw [hss, hacc]
    · funext _ _ _ _
      rw [hss, hacc]
      cases r2.sstore.netMetering <;> cases r2.access <;>
        simp only [sstoreLegacyRefundCounter, sstoreFlatRefundCounter, sstoreNewRefundCounter, hclr]
  | some st =>
    have hs2 : r2.stateGas = some st := by rw [← hsg, hs1]
    simp only [hs2]
    have hrf : sstoreAmsterdamRefundCounter r1.gas st = sstoreAmsterdamRefundCounter r2.gas st := by
      funext newVal origVal currVal rc
      simp only [sstoreAmsterdamRefundCounter, hclr]
    rw [hrf]

/-- Fork congruence for `SSTORE`: changing the fork while keeping `PlainOp.sstoreRuleReads`
fixed preserves `PlainOp.run r .sstore`. -/
theorem PlainOp.sstore_run_congr_fork (r : Frame.Running) (f' : Fork)
    (h : PlainOp.sstoreRuleReads (Fork.ruleSet r.context.block.fork) =
      PlainOp.sstoreRuleReads (Fork.ruleSet f')) :
    PlainOp.run { r with context := { r.context with block := { r.context.block with fork := f' } } }
        .sstore =
      PlainOp.run r .sstore := by
  rw [← SstoreRow.ofRules_run_eq, ← SstoreRow.ofRules_run_eq]
  simp only [PlainOp.sstoreRuleReads, Prod.mk.injEq] at h
  rcases h with ⟨hsg, hss, hacc, hclr, hbal⟩
  have hrow : SstoreRow.ofRules (Fork.ruleSet f') =
      SstoreRow.ofRules (Fork.ruleSet r.context.block.fork) :=
    sstoreRow_ofRules_eq_of hsg.symm hss.symm hacc.symm hclr.symm
  unfold Frame.State.liftStore
  dsimp only [BenvStat.rules] at hrow ⊢
  rw [hrow]
  cases ((SstoreRow.ofRules (Fork.ruleSet r.context.block.fork)).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine) with
  | error err =>
    rcases err with ⟨e, m', touch⟩
    dsimp only
    rw [applyStoreTouch_eq_of hbal.symm]
  | ok res =>
    rcases res with ⟨m', touch⟩
    dsimp only
    rw [applyStoreTouch_eq_of hbal.symm]

/-! ### `SSTORE` preservation corollaries -/

theorem PlainOp.sstore_run_gasMeasure_lt (r : Frame.Running) (hacc : r.context.block.rules.access.Valid)
    {s' : Frame.State} (hok : PlainOp.run r .sstore = .ok s') :
    s'.machine.gasMeasure < r.state.machine.gasMeasure := by
  rw [← SstoreRow.ofRules_run_eq] at hok
  unfold Frame.State.liftStore at hok
  cases hs : (SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine with
  | error e => simp [hs] at hok
  | ok res =>
    rcases res with ⟨m', touch⟩
    simp only [hs, Except.ok.injEq] at hok
    subst hok
    rw [Frame.State.applyStoreTouch_machine, Frame.State.withMachine_machine]
    exact SstoreRow.step_gasMeasure_lt_of_ok
      (SstoreRow.ofRules_gasCost_pos r.context.block.rules hacc) hs

theorem PlainOp.sstore_run_memory (r : Frame.Running) :
    (match PlainOp.run r .sstore with | .ok s' | .error (_, s') => s'.machine.memory) =
      r.state.machine.memory := by
  rw [← SstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  have hm := SstoreRow.step_memory (SstoreRow.ofRules r.context.block.rules) r.context.isStatic
    (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine
  cases hs : (SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine with
  | ok res => simp [hs] at hm ⊢; exact hm
  | error err => simp [hs] at hm ⊢; exact hm

theorem PlainOp.sstore_run_returnData (r : Frame.Running) :
    (match PlainOp.run r .sstore with | .ok s' | .error (_, s') => s'.machine.returnData) =
      r.state.machine.returnData := by
  rw [← SstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  have hrd := SstoreRow.step_returnData (SstoreRow.ofRules r.context.block.rules) r.context.isStatic
    (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine
  cases hs : (SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine with
  | ok res => simp [hs] at hrd ⊢; exact hrd
  | error err => simp [hs] at hrd ⊢; exact hrd

theorem PlainOp.sstore_run_logs (r : Frame.Running) :
    (match PlainOp.run r .sstore with | .ok s' | .error (_, s') => s'.logs) = r.state.logs := by
  rw [← SstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  cases (SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine <;>
    simp [Frame.State.applyStoreTouch_logs, Frame.State.logs]

theorem PlainOp.sstore_run_selfDestructs (r : Frame.Running) :
    (match PlainOp.run r .sstore with | .ok s' | .error (_, s') => s'.selfDestructs) =
      r.state.selfDestructs := by
  rw [← SstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  cases (SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine <;>
    simp [Frame.State.applyStoreTouch_selfDestructs, Frame.State.selfDestructs]

theorem PlainOp.sstore_run_accessedAddresses (r : Frame.Running) :
    (match PlainOp.run r .sstore with | .ok s' | .error (_, s') => s'.accessedAddresses) =
      r.state.accessedAddresses := by
  rw [← SstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  cases (SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine <;>
    simp [Frame.State.applyStoreTouch_accessedAddresses, Frame.State.accessedAddresses]

theorem PlainOp.sstore_run_touchedAccounts (r : Frame.Running) :
    (match PlainOp.run r .sstore with | .ok s' | .error (_, s') => s'.touchedAccounts) =
      r.state.touchedAccounts := by
  rw [← SstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  cases (SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine <;>
    simp [Frame.State.applyStoreTouch_touchedAccounts, Frame.State.touchedAccounts]

theorem PlainOp.sstore_run_createdAccounts (r : Frame.Running) :
    (match PlainOp.run r .sstore with | .ok s' | .error (_, s') => s'.createdAccounts) =
      r.state.createdAccounts := by
  rw [← SstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  cases (SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine <;>
    simp [Frame.State.applyStoreTouch_createdAccounts, Frame.State.createdAccounts]

theorem PlainOp.sstore_run_transientStorage (r : Frame.Running) :
    (match PlainOp.run r .sstore with | .ok s' | .error (_, s') => s'.transientStorage) =
      r.state.transientStorage := by
  rw [← SstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  cases hs : (SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine with
  | ok res =>
    rcases res with ⟨m', touch⟩
    have hnot : ∀ k v, touch.write ≠ some (.transient k v) := by
      have hw := (SstoreRow.step_ok hs).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.2
      rw [hw]
      intro _ _ hc
      cases hc
    exact Frame.State.applyStoreTouch_transientStorage_ne_transient _ _ hnot _
  | error err =>
    rcases err with ⟨e, m', touch⟩
    exact Frame.State.applyStoreTouch_transientStorage_ne_transient _ _
      (SstoreRow.step_error hs).2.2.2.2.2.2.1 _

theorem PlainOp.sstore_run_balance (r : Frame.Running) (a : Address) :
    (match PlainOp.run r .sstore with | .ok s' | .error (_, s') => s'.balance a) =
      r.state.balance a := by
  rw [← SstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  cases hs : (SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine with
  | ok res =>
    rcases res with ⟨m', touch⟩
    have hnot : ∀ k v, touch.write ≠ some (.transient k v) := by
      have hw := (SstoreRow.step_ok hs).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.2
      rw [hw]
      intro _ _ hc
      cases hc
    exact Frame.State.applyStoreTouch_balance _ _ hnot _ a
  | error err =>
    rcases err with ⟨e, m', touch⟩
    exact Frame.State.applyStoreTouch_balance _ _ (SstoreRow.step_error hs).2.2.2.2.2.2.1 _ a

theorem PlainOp.sstore_run_code (r : Frame.Running) (a : Address) :
    (match PlainOp.run r .sstore with | .ok s' | .error (_, s') => s'.code a) =
      r.state.code a := by
  rw [← SstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  cases hs : (SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine with
  | ok res =>
    rcases res with ⟨m', touch⟩
    have hnot : ∀ k v, touch.write ≠ some (.transient k v) := by
      have hw := (SstoreRow.step_ok hs).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.2
      rw [hw]
      intro _ _ hc
      cases hc
    exact Frame.State.applyStoreTouch_code _ _ hnot _ a
  | error err =>
    rcases err with ⟨e, m', touch⟩
    exact Frame.State.applyStoreTouch_code _ _ (SstoreRow.step_error hs).2.2.2.2.2.2.1 _ a

theorem PlainOp.sstore_run_storageValue_ne_addr (r : Frame.Running) {a : Address}
    (hne : r.context.recipient ≠ a) (k : U256) :
    (match PlainOp.run r .sstore with | .ok s' | .error (_, s') => s'.storageValue a k) =
      r.state.storageValue a k := by
  rw [← SstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  cases hs : (SstoreRow.ofRules r.context.block.rules).step r.context.isStatic
      (r.state.slotView r.context.recipient r.context.block.origState) r.state.machine with
  | ok res =>
    rcases res with ⟨m', touch⟩
    have hnot : ∀ k v, touch.write ≠ some (.transient k v) := by
      have hw := (SstoreRow.step_ok hs).choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.2
      rw [hw]
      intro _ _ hc
      cases hc
    exact Frame.State.applyStoreTouch_storageValue_ne_addr _ _ hnot _ hne k
  | error err =>
    rcases err with ⟨e, m', touch⟩
    exact Frame.State.applyStoreTouch_storageValue_ne_addr _ _
      (SstoreRow.step_error hs).2.2.2.2.2.2.1 _ hne k

/-! ### `TstoreRow` effect laws and bridge -/

theorem TstoreRow.step_ok {row : TstoreRow} {opcodes : OpcodeRules} {isStatic : Bool}
    {m out : Machine} {touch : StoreTouch}
    (h : row.step opcodes isStatic m = .ok (out, touch)) :
    ∃ key newVal rest,
      row.available opcodes = true ∧
      isStatic = false ∧
      m.stack = key :: newVal :: rest ∧
      row.gasCost ≤ m.gasLeft ∧
      out = { m with stack := rest, gasLeft := m.gasLeft - row.gasCost } ∧
      touch = { write := some (.transient key newVal) } := by
  unfold TstoreRow.step at h
  split at h
  · contradiction
  · rename_i hav
    have hav_true : row.available opcodes = true := Bool.eq_true_of_not_eq_false (by simpa using hav)
    split at h
    · contradiction
    · cases hp1 : m.pop with
      | error e => rw [hp1] at h; cases h
      | ok p1 =>
        rw [hp1] at h
        obtain ⟨key, m₁⟩ := p1
        dsimp only at h
        cases hp2 : m₁.pop with
        | error e => rw [hp2] at h; cases h
        | ok p2 =>
          rw [hp2] at h
          obtain ⟨newVal, m₂⟩ := p2
          dsimp only at h
          cases hcg : m₂.chargeGas row.gasCost with
          | error e => rw [hcg] at h; cases h
          | ok m₃ =>
            rw [hcg] at h
            dsimp only at h
            split at h
            · contradiction
            · cases h
              have hstat : isStatic = false := by
                cases isStatic <;> cases row.staticFirst <;> simp_all
              obtain ⟨tail, hstk1, rfl⟩ := pop_ok hp1
              obtain ⟨rest, hstk2, rfl⟩ := pop_ok hp2
              have hstk : m.stack = key :: newVal :: rest := by
                rw [hstk1]
                simpa using hstk2
              obtain ⟨hle, rfl⟩ := charged_ok hcg
              exact ⟨key, newVal, rest, hav_true, hstat, hstk, hle, rfl, rfl⟩

theorem TstoreRow.step_error {row : TstoreRow} {opcodes : OpcodeRules} {isStatic : Bool}
    {m out : Machine} {e : ExceptionalHalt} {touch : StoreTouch}
    (h : row.step opcodes isStatic m = .error (e, out, touch)) :
    (e = .invalidOpcode .none ∨ e = .writeInStaticContext .none ∨
        e = .stackUnderflow .none ∨ e = .outOfGas .none) ∧
      out.memory = m.memory ∧
      out.stateGas = m.stateGas ∧
      out.returnData = m.returnData ∧
      out.gasMeasure ≤ m.gasMeasure ∧
      touch = {} := by
  unfold TstoreRow.step at h
  split at h
  · cases h
    exact ⟨Or.inl rfl, rfl, rfl, rfl, le_rfl, rfl⟩
  · split at h
    · cases h
      exact ⟨Or.inr (Or.inl rfl), rfl, rfl, rfl, le_rfl, rfl⟩
    · cases hp1 : m.pop with
      | error e1 =>
        rcases e1 with ⟨err1, out1⟩
        rw [hp1] at h; cases h
        obtain ⟨rfl, _, rfl⟩ := pop_error hp1
        exact ⟨Or.inr (Or.inr (Or.inl rfl)), rfl, rfl, rfl, le_rfl, rfl⟩
      | ok p1 =>
        rw [hp1] at h; obtain ⟨key, m₁⟩ := p1; dsimp only at h
        cases hp2 : m₁.pop with
        | error e2 =>
          rcases e2 with ⟨err2, out2⟩
          rw [hp2] at h; cases h
          obtain ⟨_, _, hm1⟩ := pop_ok hp1
          obtain ⟨rfl, _, rfl⟩ := pop_error hp2
          subst hm1
          exact ⟨Or.inr (Or.inr (Or.inl rfl)), rfl, rfl, rfl, le_rfl, rfl⟩
        | ok p2 =>
          rw [hp2] at h; obtain ⟨newVal, m₂⟩ := p2; dsimp only at h
          obtain ⟨_, _, hm1⟩ := pop_ok hp1
          obtain ⟨_, _, hm2⟩ := pop_ok hp2
          cases hcg : m₂.chargeGas row.gasCost with
          | error e3 =>
            rcases e3 with ⟨err3, out3⟩
            rw [hcg] at h; cases h
            obtain ⟨rfl, _, rfl⟩ := charged_error hcg
            subst hm2; subst hm1
            exact ⟨Or.inr (Or.inr (Or.inr rfl)), rfl, rfl, rfl, le_rfl, rfl⟩
          | ok m₃ =>
            rw [hcg] at h; dsimp only at h
            obtain ⟨hle, rfl⟩ := charged_ok hcg
            split at h
            · cases h
              subst hm2; subst hm1
              exact ⟨Or.inr (Or.inl rfl), rfl, rfl, rfl, by simp only [Machine.gasMeasure]; omega, rfl⟩
            · cases h

theorem TstoreRow.ofRules_run_eq (r : Frame.Running) :
    r.state.liftStore r.context.block.rules r.context.recipient
        ((TstoreRow.ofRules r.context.block.rules).step r.context.block.rules.opcodes
          r.context.isStatic) =
      PlainOp.run r .tstore := rfl

theorem TstoreRow.ofRules_run_fork_eq (f : Fork) (r : Frame.Running)
    (hf : r.context.block.fork = f) :
    r.state.liftStore (Fork.ruleSet f) r.context.recipient
        ((TstoreRow.ofRules (Fork.ruleSet f)).step (Fork.ruleSet f).opcodes r.context.isStatic) =
      PlainOp.run r .tstore := by
  have hr : r.context.block.rules = Fork.ruleSet f := by simp only [BenvStat.rules, hf]
  rw [← hr]
  exact TstoreRow.ofRules_run_eq r

/-- The exact rule projection `.tstore` reads from `ForkRules`:
`(opcodes.transient, stateGas.isSome)`. -/
def PlainOp.tstoreRuleReads (rules : ForkRules) : Bool × Bool :=
  (rules.opcodes.transient, rules.stateGas.isSome)

private theorem applyStoreTouch_eq_of_no_trail (r1 r2 : ForkRules) (recipient : Address)
    {touch : StoreTouch} (hrs : touch.readStorage = none) (hra : touch.readAccount = false)
    (s : Frame.State) :
    s.applyStoreTouch r1 recipient touch = s.applyStoreTouch r2 recipient touch := by
  unfold Frame.State.applyStoreTouch
  rcases touch with ⟨rs, wk, nr, ra, wr⟩
  dsimp only at hrs hra
  subst hrs; subst hra
  cases wr <;> rfl

theorem PlainOp.tstore_run_congr_fork (r : Frame.Running) (f' : Fork)
    (h : PlainOp.tstoreRuleReads (Fork.ruleSet r.context.block.fork) =
      PlainOp.tstoreRuleReads (Fork.ruleSet f')) :
    PlainOp.run { r with context := { r.context with block := { r.context.block with fork := f' } } }
        .tstore =
      PlainOp.run r .tstore := by
  rw [← TstoreRow.ofRules_run_eq, ← TstoreRow.ofRules_run_eq]
  simp only [PlainOp.tstoreRuleReads, Prod.mk.injEq] at h
  rcases h with ⟨htr, hsg⟩
  have hrow : TstoreRow.ofRules (Fork.ruleSet f') =
      TstoreRow.ofRules (Fork.ruleSet r.context.block.fork) := by
    simp only [TstoreRow.ofRules, hsg]
  have hop : (TstoreRow.ofRules (Fork.ruleSet r.context.block.fork)).step
      (Fork.ruleSet f').opcodes r.context.isStatic r.state.machine =
      (TstoreRow.ofRules (Fork.ruleSet r.context.block.fork)).step
      (Fork.ruleSet r.context.block.fork).opcodes r.context.isStatic r.state.machine := by
    simp only [TstoreRow.step, TstoreRow.ofRules, htr, hsg]
  unfold Frame.State.liftStore
  dsimp only [BenvStat.rules] at hrow hop ⊢
  rw [hrow, hop]
  cases hs : ((TstoreRow.ofRules (Fork.ruleSet r.context.block.fork)).step
      (Fork.ruleSet r.context.block.fork).opcodes r.context.isStatic r.state.machine) with
  | error err =>
    rcases err with ⟨e, m', touch⟩
    have ht := (TstoreRow.step_error hs).2.2.2.2.2
    subst ht
    rfl
  | ok res =>
    rcases res with ⟨m', touch⟩
    have ht := (TstoreRow.step_ok hs).choose_spec.choose_spec.choose_spec.2.2.2.2.2
    rw [ht]
    dsimp only
    rw [applyStoreTouch_eq_of_no_trail (Fork.ruleSet f') (Fork.ruleSet r.context.block.fork)
      r.context.recipient rfl rfl]

theorem PlainOp.tstore_run_state (r : Frame.Running) :
    (match PlainOp.run r .tstore with | .ok s' | .error (_, s') => s'.state) = r.state.state := by
  rw [← TstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  cases hs : (TstoreRow.ofRules r.context.block.rules).step r.context.block.rules.opcodes
      r.context.isStatic r.state.machine with
  | ok res =>
    rcases res with ⟨m', touch⟩
    have hnot : ∀ k v, touch.write ≠ some (.storage k v) := by
      have hw := (TstoreRow.step_ok hs).choose_spec.choose_spec.choose_spec.2.2.2.2.2
      rw [hw]
      intro _ _ hc
      cases hc
    exact Frame.State.applyStoreTouch_state_ne_storage _ _ hnot _
  | error err =>
    rcases err with ⟨e, m', touch⟩
    have ht := (TstoreRow.step_error hs).2.2.2.2.2
    rw [ht]
    rfl

theorem PlainOp.tstore_run_substate (r : Frame.Running) :
    (match PlainOp.run r .tstore with | .ok s' | .error (_, s') => s'.substate) =
      r.state.substate := by
  rw [← TstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  cases hs : (TstoreRow.ofRules r.context.block.rules).step r.context.block.rules.opcodes
      r.context.isStatic r.state.machine with
  | ok res =>
    rcases res with ⟨m', touch⟩
    have ht := (TstoreRow.step_ok hs).choose_spec.choose_spec.choose_spec.2.2.2.2.2
    rw [ht]
    exact Frame.State.applyStoreTouch_substate_of_none _ _ rfl rfl _
  | error err =>
    rcases err with ⟨e, m', touch⟩
    have ht := (TstoreRow.step_error hs).2.2.2.2.2
    rw [ht]
    rfl

theorem PlainOp.tstore_run_trail (r : Frame.Running) :
    (match PlainOp.run r .tstore with | .ok s' | .error (_, s') => s'.trail) = r.state.trail := by
  rw [← TstoreRow.ofRules_run_eq]
  unfold Frame.State.liftStore
  cases hs : (TstoreRow.ofRules r.context.block.rules).step r.context.block.rules.opcodes
      r.context.isStatic r.state.machine with
  | ok res =>
    rcases res with ⟨m', touch⟩
    have ht := (TstoreRow.step_ok hs).choose_spec.choose_spec.choose_spec.2.2.2.2.2
    rw [ht]
    exact Frame.State.applyStoreTouch_trail_of_none _ _ rfl rfl _
  | error err =>
    rcases err with ⟨e, m', touch⟩
    have ht := (TstoreRow.step_error hs).2.2.2.2.2
    rw [ht]
    rfl

theorem PlainOp.tstore_run_gasMeasure_lt (r : Frame.Running) {s' : Frame.State}
    (hok : PlainOp.run r .tstore = .ok s') :
    s'.machine.gasMeasure < r.state.machine.gasMeasure := by
  rw [← TstoreRow.ofRules_run_eq] at hok
  unfold Frame.State.liftStore at hok
  cases hs : (TstoreRow.ofRules r.context.block.rules).step r.context.block.rules.opcodes
      r.context.isStatic r.state.machine with
  | error e => simp [hs] at hok
  | ok res =>
    rcases res with ⟨m', touch⟩
    simp only [hs, Except.ok.injEq] at hok
    subst hok
    obtain ⟨_, _, _, _, _, _, hle, hm', _⟩ := TstoreRow.step_ok hs
    rw [Frame.State.applyStoreTouch_machine, Frame.State.withMachine_machine, hm']
    simp only [Machine.gasMeasure, TstoreRow.ofRules, Gas.warmStorageReadCost] at hle ⊢
    omega

end Jaune.Checked
