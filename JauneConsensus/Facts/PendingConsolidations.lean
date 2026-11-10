import JauneConsensus.Facts.PendingDeposits

/-!
# Facts: what `process_pending_consolidations` does

About `JauneConsensus.processPendingConsolidations` (`JauneConsensus/Epoch.lean`), transcribed
from `v1.7.0-beta.4` `specs/electra/beacon-chain.md` (Fulu does not override it).
`pendingConsolidationStep` is one iteration of its loop, reading in the spec's order: a slashed
source is skipped (`continue`), a source not yet withdrawable at the next epoch stops the loop
(`break`), and otherwise `min(balance, effective_balance)` of the source moves to the target.
`pendingConsolidationsLoop` is the loop as a recursion over the queue, and
`processPendingConsolidations_eq` says the function is that loop followed by dropping the processed
prefix.

What the spec does not check here, stated as a fact and not as a defect: when a pending
consolidation is applied, nothing about the **target** is read except its balance. Its
compounding credential, activity and exit status were checked once, when the request was
processed (`PendingConsolidationChecks`); a target that has since exited, been slashed or changed
is credited all the same.

Nothing here edits a spec definition.
-/

namespace JauneConsensus.Facts

open JauneConsensus

variable {P : Preset} {f : CFork}

/-- One iteration of the loop of `process_pending_consolidations` on the loop state
`(state, next_pending_consolidation)`. -/
def pendingConsolidationStep (nextEpoch : U64) (pc : PendingConsolidation)
    (acc : BeaconState P f × Nat) : M (ForInStep (BeaconState P f × Nat)) := do
  let site := "process_pending_consolidations"
  let state := acc.1
  let next := acc.2
  let source ← state.validators.get pc.source_index.toNat site
  if source.slashed = true then return .yield (state, next + 1)
  if source.withdrawable_epoch > nextEpoch then return .done (state, next)
  let balance ← state.balances.get pc.source_index.toNat site
  let sourceEffective := if balance < source.effective_balance then balance
    else source.effective_balance
  let state ← decreaseBalance state pc.source_index sourceEffective
  let state ← increaseBalance state pc.target_index sourceEffective
  return .yield (state, next + 1)

/-- The loop as a recursion over the queue. -/
def pendingConsolidationsLoop (nextEpoch : U64) :
    List PendingConsolidation → BeaconState P f × Nat → M (BeaconState P f × Nat)
  | [], acc => pure acc
  | pc :: pcs, acc => do
    match ← pendingConsolidationStep nextEpoch pc acc with
    | .done a => pure a
    | .yield a => pendingConsolidationsLoop nextEpoch pcs a

/-- The recursion is the `for` loop of the step. -/
theorem pendingConsolidationsLoop_eq_forIn (nextEpoch : U64) (xs : List PendingConsolidation)
    (acc : BeaconState P f × Nat) :
    pendingConsolidationsLoop nextEpoch xs acc = forIn xs acc (pendingConsolidationStep nextEpoch) :=
  (forIn_list_eq_loop _ _ (fun _ _ => rfl) _ (fun _ => by rw [pendingConsolidationsLoop])
    (fun _ _ _ => by
      rw [pendingConsolidationsLoop]; apply bind_congr; intro r; cases r <;> rfl) xs acc).symm

/-- **The equation of `process_pending_consolidations`**: the next epoch, the queue, the loop
from `(state, 0)`, then the queue becomes its unprocessed suffix. -/
theorem processPendingConsolidations_eq (cfg : Config) (state : BeaconState P f) :
    processPendingConsolidations cfg state = (do
      let site := "process_pending_consolidations"
      let nextEpoch ← (← getCurrentEpoch state).add? U64.one site
      let pending ← state.pendingConsolidations
      let r ← pendingConsolidationsLoop nextEpoch pending.toArray.toList (state, 0)
      r.1.setPendingConsolidations
        (← SszList.ofArray (pending.toArray.extract r.2 pending.length) site)) := by
  unfold processPendingConsolidations
  dsimp only
  simp only [pendingConsolidationsLoop_eq_forIn, Array.forIn_toList]
  apply bind_congr; intro e0
  apply bind_congr; intro nextEpoch
  apply bind_congr; intro pending
  congr 1

/-- **The outcomes of one iteration**, in the spec's order: a slashed source is skipped (state
unchanged, index advanced); a source whose withdrawable epoch is after the next epoch stops the
loop; otherwise `amount = min(balance, effective_balance)` of the source is decreased at the source
and increased at the target. No property of the target is read. -/
theorem pendingConsolidationStep_spec {nextEpoch : U64} {pc : PendingConsolidation}
    {st : BeaconState P f} {n : Nat} {r : ForInStep (BeaconState P f × Nat)}
    (h : pendingConsolidationStep nextEpoch pc (st, n) = .ok r) :
    ∃ src, st.validators.toArray[pc.source_index.toNat]? = some src ∧
      ((src.slashed = true ∧ r = .yield (st, n + 1)) ∨
       (src.slashed = false ∧ src.withdrawable_epoch > nextEpoch ∧ r = .done (st, n)) ∨
       (src.slashed = false ∧ ¬ src.withdrawable_epoch > nextEpoch ∧
        ∃ bal mid st', st.balances.toArray[pc.source_index.toNat]? = some bal ∧
          decreaseBalance st pc.source_index
            (if bal < src.effective_balance then bal else src.effective_balance) = .ok mid ∧
          increaseBalance mid pc.target_index
            (if bal < src.effective_balance then bal else src.effective_balance) = .ok st' ∧
          r = .yield (st', n + 1))) := by
  unfold pendingConsolidationStep at h
  dsimp only at h
  obtain ⟨src, hsrc, h⟩ := bind_ok_elim h
  refine ⟨src, get_ok hsrc, ?_⟩
  by_cases h1 : src.slashed = true
  · rw [ite_eq_left h1] at h
    exact .inl ⟨h1, (Except.ok.inj h).symm⟩
  rw [ite_eq_right h1] at h
  have h1' : src.slashed = false := by simpa using h1
  by_cases h2 : src.withdrawable_epoch > nextEpoch
  · rw [ite_eq_left h2] at h
    exact .inr (.inl ⟨h1', h2, (Except.ok.inj h).symm⟩)
  rw [ite_eq_right h2] at h
  obtain ⟨bal, hbal, h⟩ := bind_ok_elim h
  obtain ⟨mid, hmid, h⟩ := bind_ok_elim h
  obtain ⟨st', hst', h⟩ := bind_ok_elim h
  exact .inr (.inr ⟨h1', h2, bal, mid, st', get_ok hbal, hmid, hst', (Except.ok.inj h).symm⟩)

/-- **C-S9 balance, one applied consolidation**: when source and target differ, the source's
balance decreases by exactly `amount = min(balance, effective_balance)` (no saturation, since
`amount ≤ balance`), the target's increases by exactly `amount`, and no other balance changes.
The registry is unchanged. -/
theorem consolidation_balance_moved {st mid st' : BeaconState P f} {s t : ValidatorIndex}
    {bal eff : Gwei} (hst : s ≠ t)
    (hbal : st.balances.toArray[s.toNat]? = some bal)
    (hdec : decreaseBalance st s (if bal < eff then bal else eff) = .ok mid)
    (hinc : increaseBalance mid t (if bal < eff then bal else eff) = .ok st') :
    (if bal < eff then bal else eff).toNat ≤ bal.toNat ∧
    (∃ b', st'.balances.toArray[s.toNat]? = some b' ∧
      b'.toNat = bal.toNat - (if bal < eff then bal else eff).toNat) ∧
    (∃ tb tb', st.balances.toArray[t.toNat]? = some tb ∧ st'.balances.toArray[t.toNat]? = some tb' ∧
      tb'.toNat = tb.toNat + (if bal < eff then bal else eff).toNat) ∧
    (∀ j, j ≠ s.toNat → j ≠ t.toNat → st'.balances.toArray[j]? = st.balances.toArray[j]?) ∧
    st'.validators = st.validators := by
  have hst' : s.toNat ≠ t.toNat := fun h => hst (U64.ext_toNat h)
  have hle : (if bal < eff then bal else eff).toNat ≤ bal.toNat := by
    rw [U64.toNat_min]; exact Nat.min_le_left _ _
  obtain ⟨b0, b1, hb0, hb1, hjd, hmidf⟩ := decreaseBalance_spec hdec
  rw [hbal] at hb0
  cases hb0
  obtain ⟨c0, c1, hc0, hadd, hji, hst'f⟩ := increaseBalance_spec hinc
  refine ⟨hle, ⟨b1, ?_, ?_⟩, ⟨c0, c1, ?_, ?_, U64.toNat_add? hadd⟩, ?_, ?_⟩
  · rw [hji, ite_eq_right hst', hjd, ite_eq_left rfl]
  · rw [hb1, ite_eq_right (Nat.not_lt.mpr hle)]
  · rw [← hc0, hjd, ite_eq_right (Ne.symm hst')]
  · rw [hji, ite_eq_left rfl]
  · intro j hjs hjt
    rw [hji, ite_eq_right hjt, hjd, ite_eq_right hjs]
  · rw [hst'f, hmidf]

/-! ## The fate of every pending consolidation the loop reaches -/

/-- `ConsolidationRun nextEpoch s n L s'`: starting from state `s` at index `n`, every iteration
over `L` continued (`yield`), the last one leaving `s'`. Each iteration is described by
`pendingConsolidationStep_spec`. -/
inductive ConsolidationRun (nextEpoch : U64) :
    BeaconState P f → Nat → List PendingConsolidation → BeaconState P f → Prop where
  | nil (s : BeaconState P f) (n : Nat) : ConsolidationRun nextEpoch s n [] s
  | cons {s s1 s' : BeaconState P f} {n : Nat} {pc : PendingConsolidation}
      {rest : List PendingConsolidation} :
      pendingConsolidationStep nextEpoch pc (s, n) = .ok (.yield (s1, n + 1)) →
      ConsolidationRun nextEpoch s1 (n + 1) rest s' →
      ConsolidationRun nextEpoch s n (pc :: rest) s'

/-- **The loop, consolidation by consolidation**: on success, the loop continued over the first
`k` pending consolidations (each skipped or applied, as `pendingConsolidationStep_spec` says),
and if `k` is short of the queue, the iteration at consolidation `k` stopped the loop (its source
is not yet withdrawable). -/
theorem pendingConsolidationsLoop_fate {nextEpoch : U64} :
    ∀ (L : List PendingConsolidation) (s : BeaconState P f) (n : Nat) (out : BeaconState P f × Nat),
      pendingConsolidationsLoop nextEpoch L (s, n) = .ok out →
      ∃ k, k ≤ L.length ∧ ConsolidationRun nextEpoch s n (L.take k) out.1 ∧ out.2 = n + k ∧
        (∀ hk : k < L.length,
          pendingConsolidationStep nextEpoch (L[k]'hk) out = .ok (.done out)) := by
  intro L
  induction L with
  | nil =>
    intro s n out h
    cases h
    exact ⟨0, le_refl _, .nil _ _, rfl, fun hk => absurd hk (by simp)⟩
  | cons pc pcs ih =>
    intro s n out h
    rw [pendingConsolidationsLoop] at h
    obtain ⟨r, hr, h⟩ := bind_ok_elim h
    obtain ⟨src, -, hspec⟩ := pendingConsolidationStep_spec hr
    cases r with
    | done a =>
      have hao : out = a := (Except.ok.inj h).symm
      subst hao
      have hout : out = (s, n) := by
        rcases hspec with ⟨-, hra⟩ | ⟨-, -, hra⟩ | ⟨-, -, _, _, _, _, _, _, hra⟩ <;> cases hra
        rfl
      subst hout
      exact ⟨0, Nat.zero_le _, .nil _ _, rfl, fun _ => hr⟩
    | yield a =>
      have hidx : ∃ s1, a = (s1, n + 1) := by
        rcases hspec with ⟨-, hra⟩ | ⟨-, -, hra⟩ | ⟨-, -, _, _, s1, _, _, _, hra⟩ <;> cases hra
        · exact ⟨_, rfl⟩
        · exact ⟨s1, rfl⟩
      obtain ⟨s1, rfl⟩ := hidx
      obtain ⟨k, hk, hrun, hn, hstop⟩ := ih s1 (n + 1) out h
      refine ⟨k + 1, by simp; omega, .cons hr hrun, by omega, ?_⟩
      intro hk'
      exact hstop (by simp at hk'; omega)

/-- **C-S9, the epoch pass** (Electra and Fulu): on success, `process_pending_consolidations`
continued over the first `k` pending consolidations from the input state (each skipped or applied,
`pendingConsolidationStep_spec`), and the queue becomes the unreached suffix; nothing else
changes after the loop. -/
theorem processPendingConsolidations_fate (hE : f.atLeast .electra = true) {cfg : Config}
    {state s' : BeaconState P f} (hp : processPendingConsolidations cfg state = .ok s') :
    ∃ nextEpoch k mid,
      k ≤ (Gated.get hE state.pending_consolidations).toArray.size ∧
      ConsolidationRun nextEpoch state 0
        ((Gated.get hE state.pending_consolidations).toArray.toList.take k) mid ∧
      (Gated.get hE s'.pending_consolidations).toArray =
        (Gated.get hE state.pending_consolidations).toArray.extract k
          (Gated.get hE state.pending_consolidations).toArray.size ∧
      s'.validators = mid.validators ∧ s'.balances = mid.balances := by
  rw [processPendingConsolidations_eq] at hp
  dsimp only at hp
  obtain ⟨e0, -, hp⟩ := bind_ok_elim hp
  obtain ⟨nextEpoch, -, hp⟩ := bind_ok_elim hp
  obtain ⟨pending, hpend, hp⟩ := bind_ok_elim hp
  have hpq : pending = Gated.get hE state.pending_consolidations := by
    unfold BeaconState.pendingConsolidations at hpend
    rw [gated_read_get hE] at hpend
    exact (Except.ok.inj hpend).symm
  subst hpq
  obtain ⟨out, hloop, hp⟩ := bind_ok_elim hp
  obtain ⟨k, hk, hrun, hn, -⟩ := pendingConsolidationsLoop_fate _ _ _ _ hloop
  obtain ⟨q, hq, hp⟩ := bind_ok_elim hp
  unfold BeaconState.setPendingConsolidations at hp
  obtain ⟨g, hg, hp⟩ := bind_ok_elim hp
  cases hp
  refine ⟨nextEpoch, k, out.1, by simpa using hk, hrun, ?_, rfl, rfl⟩
  have hgq : g = Gated.mk hE q := by
    rw [gated_write_eq hE] at hg; exact (Except.ok.inj hg).symm
  show (Gated.get hE g).toArray = _
  rw [hgq, Gated.get_mk]
  unfold SszList.ofArray at hq
  split at hq
  · cases hq
    show (Gated.get hE state.pending_consolidations).toArray.extract out.2
      (Gated.get hE state.pending_consolidations).length = _
    rw [hn, Nat.zero_add]
    rfl
  · cases hq

end JauneConsensus.Facts
