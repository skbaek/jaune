import JauneConsensus.Block
import JauneConsensus.Upgrade
import JauneConsensus.Epoch

/-!
# Anchor invariants of the beacon state (goal `eip7002-cross-layer-v1`, unit W2d)

Two invariants that the joint history (O3) carries through every consensus step:

* `PendingPartialsCompounding`: every pending partial withdrawal names an existing validator with a
  compounding withdrawal credential (vacuous before Electra, where the pending queue is absent);
* `ExitImpliesWithdrawable`: a validator with `exit_epoch = FAR_FUTURE_EPOCH` has
  `withdrawable_epoch = FAR_FUTURE_EPOCH`.

The file proves the single-step combinator `anchor_step`, from which each mutator's preservation
follows by stating its effect on the validator array and on the pending queue.
-/

namespace JauneConsensus.Facts
open JauneConsensus

variable {P : Preset} {f : CFork}

/-- Every pending partial withdrawal names a validator with a compounding credential. -/
def PendingPartialsCompounding (st : BeaconState P f) : Prop :=
  ∀ l, st.pendingPartialWithdrawals = .ok l → ∀ p ∈ l.toArray.toList,
    ∃ v, st.validators.toArray[p.validator_index.toNat]? = some v ∧ hasCompoundingWithdrawalCredential v

/-- A validator that has not started exiting has no withdrawable epoch yet. -/
def ExitImpliesWithdrawable (st : BeaconState P f) : Prop :=
  ∀ v ∈ st.validators.toArray.toList, v.exit_epoch = FAR_FUTURE_EPOCH →
    v.withdrawable_epoch = FAR_FUTURE_EPOCH

/-- The two anchor invariants. -/
def AnchorInv (st : BeaconState P f) : Prop :=
  PendingPartialsCompounding st ∧ ExitImpliesWithdrawable st

/-! ## Monadic plumbing -/

theorem bind_eq_ok_iff {α β : Type} {x : M α} {g : α → M β} {y : β} :
    (x >>= g) = .ok y ↔ ∃ a, x = .ok a ∧ g a = .ok y := by
  cases x with
  | error e =>
    constructor
    · intro h; cases h
    · rintro ⟨_, h, _⟩; cases h
  | ok a =>
    constructor
    · intro h; exact ⟨a, rfl, h⟩
    · rintro ⟨a', h1, h2⟩; cases h1; exact h2

/-! ## The combinator -/

/-- The pending queue of `st'` is either a pending queue of `st` or names a compounding validator
of `st'`. -/
def PendingStep (st st' : BeaconState P f) : Prop :=
  ∀ l, st'.pendingPartialWithdrawals = .ok l → ∀ p ∈ l.toArray.toList,
    (∃ l0, st.pendingPartialWithdrawals = .ok l0 ∧ p ∈ l0.toArray.toList) ∨
    (∃ v, st'.validators.toArray[p.validator_index.toNat]? = some v ∧
      hasCompoundingWithdrawalCredential v)

/-- The anchor invariants survive a step that keeps every old validator index in range, keeps
compounding credentials compounding, leaves every exiting validator's withdrawable epoch at
`FAR_FUTURE_EPOCH`, and whose pending queue is either old or names a compounding validator. -/
theorem anchor_step {st st' : BeaconState P f}
    (hsz : st.validators.toArray.size ≤ st'.validators.toArray.size)
    (hcomp : ∀ (j : Nat) (v v' : Validator), st.validators.toArray[j]? = some v →
      st'.validators.toArray[j]? = some v' →
      hasCompoundingWithdrawalCredential v → hasCompoundingWithdrawalCredential v')
    (hE : ∀ (j : Nat) (v' : Validator), st'.validators.toArray[j]? = some v' →
      v'.exit_epoch = FAR_FUTURE_EPOCH → v'.withdrawable_epoch = FAR_FUTURE_EPOCH)
    (hP : PendingStep st st')
    (h : AnchorInv st) : AnchorInv st' := by
  obtain ⟨hPPC, hEIW⟩ := h
  refine ⟨?_, ?_⟩
  · intro l hl p hp
    rcases hP l hl p hp with ⟨l0, hl0, hp0⟩ | hnew
    · obtain ⟨v, hv, hc⟩ := hPPC l0 hl0 p hp0
      have hlt : p.validator_index.toNat < st.validators.toArray.size :=
        (Array.getElem?_eq_some_iff.mp hv).1
      have hlt' : p.validator_index.toNat < st'.validators.toArray.size := by omega
      obtain ⟨v', hv'⟩ : ∃ v', st'.validators.toArray[p.validator_index.toNat]? = some v' :=
        ⟨_, Array.getElem?_eq_getElem hlt'⟩
      exact ⟨v', hv', hcomp _ v v' hv hv' hc⟩
    · exact hnew
  · intro v hv hfar
    rw [Array.mem_toList_iff] at hv
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hv
    exact hE j _ (Array.getElem?_eq_getElem hj) hfar

theorem get_ok {α : Type} {n : Nat} {xs : SszList α n} {i : Nat} {site : String} {x : α}
    (h : xs.get i site = .ok x) : xs.toArray[i]? = some x := by
  unfold SszList.get getAt at h
  split at h
  · cases h; assumption
  · cases h

theorem set_ok {α : Type} {n : Nat} {xs ys : SszList α n} {i : Nat} {v : α} {site : String}
    (h : xs.set i v site = .ok ys) :
    ∃ hi : i < xs.toArray.size, ys.toArray = xs.toArray.set i v hi := by
  unfold SszList.set at h
  split at h
  · rename_i hi
    cases h
    exact ⟨hi, rfl⟩
  · cases h

theorem exitQueue_frame (cfg : Config) (s : BeaconState P f) (b : Gwei) (p : BeaconState P f × Epoch)
    (h : computeExitEpochAndUpdateChurn cfg s b = .ok p) :
    p.1.validators = s.validators ∧ p.1.pending_partial_withdrawals = s.pending_partial_withdrawals := by
  obtain ⟨st1, q⟩ := p
  unfold computeExitEpochAndUpdateChurn at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (first | (cases h; exact ⟨rfl, rfl⟩) | cases h)

theorem set_getElem? {α : Type} (xs : Array α) (i : Nat) (v : α) (hi : i < xs.size) (j : Nat) :
    (xs.set i v hi)[j]? = if j = i then some v else xs[j]? := by
  by_cases hj : j = i
  · subst hj; simp [hi]
  · simp [hj, Array.getElem?_set_ne, Ne.symm hj]

theorem set_elem_ok {α : Type} {n : Nat} {xs ys : SszList α n} {i : Nat} {v : α} {site : String}
    (h : xs.set i v site = .ok ys) :
    ys.toArray.size = xs.toArray.size ∧
      ∀ j, ys.toArray[j]? = if j = i then some v else xs.toArray[j]? := by
  obtain ⟨hi, hys⟩ := set_ok h
  refine ⟨?_, ?_⟩
  · rw [hys]; simp
  · intro j
    rw [hys, set_getElem?]

theorem mem_of_get? {α : Type} {xs : Array α} {j : Nat} {v : α} (h : xs[j]? = some v) :
    v ∈ xs.toList := by
  rw [Array.mem_toList_iff]
  exact Array.mem_of_getElem? h

/-- The pending-queue hypothesis of `anchor_step` for a state whose pending field is unchanged. -/
theorem pending_step_of_eq {st st' : BeaconState P f}
    (hP : st'.pending_partial_withdrawals = st.pending_partial_withdrawals) : PendingStep st st' := by
  intro l hl p hp'
  left
  refine ⟨l, ?_, hp'⟩
  unfold BeaconState.pendingPartialWithdrawals at hl ⊢
  rw [← hP]; exact hl

/-- A validator-array update at index `i` that keeps the length, keeps the compounding status of
an existing compounding validator, and keeps the exit invariant, leaves the pending queue alone. -/
theorem anchor_set {st st' : BeaconState P f} {i : Nat} {v' : Validator}
    (hI : AnchorInv st)
    (hsz : st'.validators.toArray.size = st.validators.toArray.size)
    (hV : ∀ j, st'.validators.toArray[j]? =
      if j = i then some v' else st.validators.toArray[j]?)
    (hcompI : ∀ v, st.validators.toArray[i]? = some v →
      hasCompoundingWithdrawalCredential v → hasCompoundingWithdrawalCredential v')
    (hE : v'.exit_epoch = FAR_FUTURE_EPOCH → v'.withdrawable_epoch = FAR_FUTURE_EPOCH)
    (hP : st'.pending_partial_withdrawals = st.pending_partial_withdrawals) :
    AnchorInv st' := by
  refine anchor_step (st := st) (st' := st') (le_of_eq hsz.symm) ?_ ?_
    (pending_step_of_eq hP) hI
  · intro j v v' hv hv' hc
    rw [hV j] at hv'
    by_cases hj : j = i
    · subst hj
      simp only [ite_true] at hv'
      cases hv'
      exact hcompI v hv hc
    · simp only [hj, ite_false] at hv'
      rw [hv] at hv'
      cases hv'
      exact hc
  · intro j w hw hfar
    rw [hV j] at hw
    by_cases hj : j = i
    · subst hj
      simp only [ite_true] at hw
      cases hw
      exact hE hfar
    · simp only [hj, ite_false] at hw
      exact hI.2 w (mem_of_get? hw) hfar

/-- A frame: a step that leaves the validator array and the pending queue unchanged. -/
theorem anchor_frame {st st' : BeaconState P f} (hI : AnchorInv st)
    (hV : st'.validators = st.validators)
    (hP : st'.pending_partial_withdrawals = st.pending_partial_withdrawals) : AnchorInv st' := by
  refine anchor_step (st := st) (st' := st') (le_of_eq (by rw [hV])) ?_ ?_
    (pending_step_of_eq hP) hI
  · intro j v v' h1 h2 hc
    rw [hV] at h2
    have hvv : v = v' := Option.some.inj (h1.symm.trans h2)
    subst hvv
    exact hc
  · intro j w hw hfar
    rw [hV] at hw
    exact hI.2 w (mem_of_get? hw) hfar

/-- The tail of `initiate_validator_exit`: from the state `T` after the exit-queue step, the checked
withdrawable epoch and the validator write. -/
theorem initiate_tail (cfg : Config) {s : BeaconState P f} (hI : AnchorInv s) {i : ValidatorIndex} {v : Validator}
    (hv : s.validators.get i.toNat "initiate_validator_exit" = .ok v)
    {T : BeaconState P f} {q : Epoch}
    (hT : T.validators = s.validators ∧ T.pending_partial_withdrawals = s.pending_partial_withdrawals)
    {s' : BeaconState P f}
    (h : (do let d ← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY
             let w ← U64.add? q d "initiate_validator_exit"
             let V ← T.validators.set i.toNat { v with exit_epoch := q, withdrawable_epoch := w }
               "initiate_validator_exit"
             pure { T with validators := V } : M (BeaconState P f)) = .ok s') :
    AnchorInv s' := by
  obtain ⟨d, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨V, hV, h⟩ := bind_eq_ok_iff.mp h
  simp only [pure, Except.pure] at h
  cases h
  obtain ⟨hszV, hVe⟩ := set_elem_ok hV
  have hget := get_ok hv
  refine anchor_set (i := i.toNat) (v' := { v with exit_epoch := q, withdrawable_epoch := w }) hI ?_ ?_ ?_ ?_ ?_
  · rw [hszV, hT.1]
  · intro j
    rw [hVe j, hT.1]
  · intro v0 hv0 hc
    rw [hget] at hv0
    cases hv0
    exact hc
  · intro hqFar
    have hqF : q = FAR_FUTURE_EPOCH := hqFar
    rw [hqF] at hw
    exact (U64.max_add?_eq hw).2
  · exact hT.2

theorem initiate_anchor (cfg : Config) (s s' : BeaconState P f) (i : ValidatorIndex)
    (hI : AnchorInv s) (h : initiateValidatorExit cfg s i = .ok s') : AnchorInv s' := by
  unfold initiateValidatorExit at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure] at h
    cases h
    exact hI
  · split at h
    · obtain ⟨⟨st1, q⟩, hq, h⟩ := bind_eq_ok_iff.mp h
      exact initiate_tail cfg hI hv (exitQueue_frame cfg s _ _ hq) h
    · obtain ⟨e0, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨a0, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨qq, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨lim, _, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · obtain ⟨x, _, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨⟨st1, q'⟩, hq', h⟩ := bind_eq_ok_iff.mp h
        simp only [pure, Except.pure] at hq'
        cases hq'
        exact initiate_tail cfg hI hv ⟨rfl, rfl⟩ h
      · obtain ⟨⟨st1, q'⟩, hq', h⟩ := bind_eq_ok_iff.mp h
        simp only [pure, Except.pure] at hq'
        cases hq'
        exact initiate_tail cfg hI hv ⟨rfl, rfl⟩ h

end JauneConsensus.Facts
