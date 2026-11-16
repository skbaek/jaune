import JauneConsensus.Block

namespace JauneConsensus
namespace Facts

/-!
# `forIn` loop invariants in `Except`

`getExpectedWithdrawals` (`JauneConsensus/Block.lean`) runs two `for` loops in
`M := Except Reject` with mutable state: loop 1 over the pending partial
withdrawals (an `Array`), loop 2 over `[0:bound]` (a `Std.Legacy.Range`).
Both reduce to `List.forIn` (`Array.forIn_toList` for arrays; the range bridge
for ranges), so one invariant lemma for `List.forIn` in `Except` covers both:
if the invariant holds initially and each `yield`/`done` step preserves it,
a successful run ends in the invariant.
-/

section ForInInv

variable {α β ε : Type} {Inv : β → Prop}

theorem list_forIn_ok_inv {xs : List α} {init : β}
    {step : α → β → Except ε (ForInStep β)}
    (h0 : Inv init)
    (hy : ∀ x ∈ xs, ∀ b, Inv b → ∀ b', step x b = .ok (.yield b') → Inv b')
    (hd : ∀ x ∈ xs, ∀ b, Inv b → ∀ b', step x b = .ok (.done b') → Inv b')
    {final : β} (h : ForIn.forIn xs init step = .ok final) : Inv final := by
  induction xs generalizing init final with
  | nil =>
    simp only [List.forIn_nil] at h
    cases h
    exact h0
  | cons x xs ih =>
    rw [List.forIn_cons] at h
    cases he : step x init with
    | error e =>
      rw [he] at h
      have hEq : Except.error e = Except.ok final := h
      cases hEq
    | ok s =>
      cases s with
      | done b' =>
        rw [he] at h
        have hEq : Except.ok b' = Except.ok final := h
        have hB : b' = final := Except.ok.inj hEq
        rw [← hB]
        exact hd x (by simp) init h0 b' he
      | yield b' =>
        rw [he] at h
        have hEq : ForIn.forIn xs b' step = Except.ok final := h
        have hb' : Inv b' := hy x (by simp) init h0 b' he
        have hy' : ∀ y ∈ xs, ∀ b, Inv b → ∀ b'', step y b = .ok (.yield b'') → Inv b'' :=
          fun y hmem b hb b'' hs => hy y (List.mem_cons_of_mem x hmem) b hb b'' hs
        have hd' : ∀ y ∈ xs, ∀ b, Inv b → ∀ b'', step y b = .ok (.done b'') → Inv b'' :=
          fun y hmem b hb b'' hs => hd y (List.mem_cons_of_mem x hmem) b hb b'' hs
        exact ih hb' hy' hd' hEq

theorem array_forIn_ok_inv {α β ε : Type} {Inv : β → Prop}
    {xs : Array α} {init : β} {step : α → β → Except ε (ForInStep β)}
    (h0 : Inv init)
    (hy : ∀ x ∈ xs, ∀ b, Inv b → ∀ b', step x b = .ok (.yield b') → Inv b')
    (hd : ∀ x ∈ xs, ∀ b, Inv b → ∀ b', step x b = .ok (.done b') → Inv b')
    {final : β} (h : ForIn.forIn xs init step = .ok final) : Inv final := by
  have h' : ForIn.forIn xs.toList init step = .ok final := by
    rw [Array.forIn_toList]
    exact h
  have hy' : ∀ x ∈ xs.toList, ∀ b, Inv b → ∀ b', step x b = .ok (.yield b') → Inv b' := by
    intro x hx b hb b' hs
    exact hy x (by simpa using hx) b hb b' hs
  have hd' : ∀ x ∈ xs.toList, ∀ b, Inv b → ∀ b', step x b = .ok (.done b') → Inv b' := by
    intro x hx b hb b' hs
    exact hd x (by simpa using hx) b hb b' hs
  exact list_forIn_ok_inv h0 hy' hd' h'

end ForInInv

section ForInPref

variable {α β ε : Type}

/-- Prefix-tracking invariant for `forIn` over a list in `Except`.

Unlike `list_forIn_ok_inv`, the invariant is indexed by the consumed prefix:
each `yield` step must extend it by the current head element (which is fresh,
since the decomposition `xs = pref ++ x :: suff` fixes its position), and
each `done` step preserves it. A successful run therefore ends in the
invariant for some consumed prefix, which is a sublist of the input.
Loop 1 of `getExpectedWithdrawals` needs the position: an emitted withdrawal
corresponds to the pending entry at the freshly consumed index. -/
theorem list_forIn_ok_pref_inv {xs : List α} {init : β}
    {step : α → β → Except ε (ForInStep β)}
    {PInv : List α → β → Prop}
    (h0 : PInv [] init)
    (hy : ∀ pref x suff b b', xs = pref ++ x :: suff → PInv pref b →
      step x b = .ok (.yield b') → PInv (pref ++ [x]) b')
    (hd : ∀ pref x suff b b', xs = pref ++ x :: suff → PInv pref b →
      step x b = .ok (.done b') → PInv pref b')
    {final : β} (h : ForIn.forIn xs init step = .ok final) :
    ∃ pref suff, xs = pref ++ suff ∧ PInv pref final := by
  have aux : ∀ (todo : List α) (b : β), (∃ pref, xs = pref ++ todo ∧ PInv pref b) →
      ForIn.forIn todo b step = .ok final →
      ∃ pref suff, xs = pref ++ suff ∧ PInv pref final := by
    intro todo
    induction todo with
    | nil =>
      intro b hpre htodo
      obtain ⟨pref, hlpref, hInv⟩ := hpre
      simp only [List.forIn_nil] at htodo
      cases htodo
      exact ⟨pref, [], hlpref, hInv⟩
    | cons x suff ih =>
      intro b hpre htodo
      obtain ⟨pref, hlpref, hInv⟩ := hpre
      rw [List.forIn_cons] at htodo
      cases he : step x b with
      | error e =>
        rw [he] at htodo
        cases htodo
      | ok s =>
        cases s with
        | done b' =>
          rw [he] at htodo
          have hB : b' = final := Except.ok.inj htodo
          subst hB
          exact ⟨pref, x :: suff, hlpref,
            hd pref x suff b b' (by rw [hlpref]) hInv he⟩
        | yield b' =>
          rw [he] at htodo
          have hInv' : PInv (pref ++ [x]) b' :=
            hy pref x suff b b' (by rw [hlpref]) hInv he
          have hlpref' : xs = (pref ++ [x]) ++ suff := by simp [hlpref]
          exact ih b' ⟨pref ++ [x], hlpref', hInv'⟩ htodo
  exact aux xs init ⟨[], by simp, h0⟩ h

theorem array_forIn_ok_pref_inv {xs : Array α} {init : β}
    {step : α → β → Except ε (ForInStep β)}
    {PInv : List α → β → Prop}
    (h0 : PInv [] init)
    (hy : ∀ pref x suff b b', xs.toList = pref ++ x :: suff → PInv pref b →
      step x b = .ok (.yield b') → PInv (pref ++ [x]) b')
    (hd : ∀ pref x suff b b', xs.toList = pref ++ x :: suff → PInv pref b →
      step x b = .ok (.done b') → PInv pref b')
    {final : β} (h : ForIn.forIn xs init step = .ok final) :
    ∃ pref suff, xs.toList = pref ++ suff ∧ PInv pref final := by
  have h' : ForIn.forIn xs.toList init step = .ok final := by
    rw [Array.forIn_toList]
    exact h
  exact list_forIn_ok_pref_inv h0 hy hd h'

end ForInPref

/-! ## Helpers: reads, pushes, and `Except` binds -/

section Helpers

variable {P : Preset} {f : CFork}

/-- `getAt xs i site = .ok x` iff `xs[i]? = some x`. -/
theorem getAt_ok_iff {α : Type} {xs : Array α} {i : Nat} {site : String} {x : α} :
    getAt xs i site = .ok x ↔ xs[i]? = some x := by
  unfold getAt
  cases h : xs[i]? with
  | none =>
    simp only [h]
    constructor
    · intro hh
      cases hh
    · intro hh
      cases hh
  | some y =>
    simp only [h]
    constructor
    · intro hh
      cases hh
      rfl
    · intro hh
      cases hh
      rfl

/-- `SszList.get` succeeds iff the underlying array read succeeds. -/
theorem ssz_get_ok_iff {α : Type} {n : Nat} {xs : SszList α n} {i : Nat}
    {site : String} {x : α} :
    xs.get i site = .ok x ↔ xs.toArray[i]? = some x := by
  unfold SszList.get
  exact getAt_ok_iff

/-- Indexing before the appended suffix. -/
theorem getElem?_append_prefix (l₁ : List α) (l₂ : List α) (j : Nat)
    (h : j < l₁.length) : (l₁ ++ l₂)[j]? = l₁[j]? := by
  induction l₁ generalizing j with
  | nil => simp at h
  | cons a t ih =>
    cases j with
    | zero => rfl
    | succ j =>
      show (t ++ l₂)[j]? = t[j]?
      exact ih j (Nat.lt_of_succ_lt_succ h)

/-- Indexing the pushed element. -/
theorem getElem?_push_last (l : List α) (x : α) :
    (l ++ [x])[l.length]? = some x := by
  induction l with
  | nil => rfl
  | cons a t ih => exact ih

/-- A push preserves old membership. -/
theorem mem_push_of_mem {α : Type} {xs : Array α} {x y : α}
    (h : x ∈ xs.toList) : x ∈ (xs.push y).toList := by
  simp only [Array.toList_push]
  exact List.mem_append_left _ h

/-- The pushed element is a member. -/
theorem mem_push_self {α : Type} {xs : Array α} {y : α} :
    y ∈ (xs.push y).toList := by
  simp only [Array.toList_push]
  exact List.mem_append_right _ (List.mem_singleton.mpr rfl)

/-- `x >>= k = .ok y` gives a middle value. -/
theorem bind_ok_elim {α β ε : Type} {x : Except ε α} {k : α → Except ε β}
    {y : β} (h : (x >>= k) = .ok y) :
    ∃ a, x = .ok a ∧ k a = .ok y := by
  cases hx : x with
  | error e =>
    rw [hx] at h
    have hEq : Except.error e = Except.ok y := h
    cases hEq
  | ok a =>
    rw [hx] at h
    exact ⟨a, rfl, h⟩

/-- `f <$> x = .ok y` gives a middle value. -/
theorem map_ok_elim {α β ε : Type} {x : Except ε α} {f : α → β}
    {y : β} (h : (f <$> x) = .ok y) :
    ∃ a, x = .ok a ∧ f a = y := by
  cases hx : x with
  | error e =>
    rw [hx] at h
    have hEq : Except.error e = Except.ok y := h
    cases hEq
  | ok a =>
    rw [hx] at h
    have hEq : Except.ok (f a) = Except.ok y := h
    exact ⟨a, rfl, Except.ok.inj hEq⟩

end Helpers

/-! ## Recipient (P4 clause 1) -/

section Recipient

variable {P : Preset} {f : CFork}

/-- Every withdrawal in `ws` is paid to the credential address of its validator,
read in `state`. -/
def AllRecipientOk (state : BeaconState P f) (ws : Array Withdrawal) : Prop :=
  ∀ w ∈ ws.toList, ∃ v : Validator,
    state.validators.toArray[w.validator_index.toNat]? = some v ∧
      withdrawalAddress v = .ok w.address

theorem getExpected_recipient (state : BeaconState P f)
    (ws : Array Withdrawal) (processed : Nat)
    (h : getExpectedWithdrawals state = .ok (ws, processed)) :
    AllRecipientOk state ws := by
  unfold getExpectedWithdrawals at h
  dsimp at h
  obtain ⟨epoch, hepoch, h1⟩ := bind_ok_elim h
  obtain ⟨minAct, hminAct, h2⟩ := bind_ok_elim h1
  by_cases he : f.atLeast .electra = true
  · simp [he] at h2
    obtain ⟨pendingList, hpend, h3⟩ := bind_ok_elim h2
    obtain ⟨s1, hForIn1, h4⟩ := bind_ok_elim h3
    obtain ⟨s2, hForIn2, hMap⟩ := map_ok_elim h4
    have hFinal : s2.2.2 = ws ∧ s1.2.2 = processed := by
      have hPair : (s2.2.2, s1.2.2) = (ws, processed) := hMap
      exact Prod.mk.inj hPair
    have hWs1Ok : AllRecipientOk state s1.2.1 := by
      have hInit : AllRecipientOk state (#[] : Array Withdrawal) := by
        intro w hw
        simp at hw
      have hInit' : (fun s : WithdrawalIndex × Array Withdrawal × Nat =>
          AllRecipientOk state s.2.1) (state.next_withdrawal_index, #[], 0) := hInit
      refine array_forIn_ok_inv (Inv := fun s : WithdrawalIndex × Array Withdrawal × Nat =>
        AllRecipientOk state s.2.1) hInit' ?hy ?hd hForIn1
      · intro w hw b hb b' hstep
        by_cases hBreak : (epoch < w.withdrawable_epoch ∨
          b.2.1.size = min P.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP (P.MAX_WITHDRAWALS_PER_PAYLOAD - 1))
        · rw [if_pos hBreak] at hstep
          have hEq : ForInStep.done b = ForInStep.yield b' := Except.ok.inj hstep
          cases hEq
        · rw [if_neg hBreak] at hstep
          obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
          obtain ⟨bal, hbal, h2⟩ := bind_ok_elim h1
          obtain ⟨wd, hwd, h3⟩ := bind_ok_elim h2
          obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
          by_cases hEmit : ((validator.exit_epoch = FAR_FUTURE_EPOCH ∧
            minAct ≤ validator.effective_balance) ∧ minAct < balance)
          · rw [if_pos hEmit] at h4
            obtain ⟨avail, havail, h5⟩ := bind_ok_elim h4
            obtain ⟨addr, haddr, h6⟩ := bind_ok_elim h5
            obtain ⟨wid', hwid, hMapEq⟩ := map_ok_elim h6
            have hEq : (wid', b.2.1.push ⟨b.1, w.validator_index, addr,
              if avail < w.amount then avail else w.amount⟩, b.2.2 + 1) = b' :=
              ForInStep.yield.inj hMapEq
            subst hEq
            intro w0 hw0
            simp only [Array.toList_push] at hw0
            have hOr := List.mem_append.mp hw0
            cases hOr with
            | inl hOld =>
              have hOld' : w0 ∈ b.2.1.toList := hOld
              obtain ⟨v, hvArr, hvAddr⟩ := hb w0 hOld'
              exact ⟨v, hvArr, hvAddr⟩
            | inr hNew =>
              simp at hNew
              subst hNew
              have hArr : state.validators.toArray[w.validator_index.toNat]? = some validator := by
                have hIff := (ssz_get_ok_iff (xs := state.validators) (i := w.validator_index.toNat)).mp hval
                exact hIff
              exact ⟨validator, hArr, haddr⟩
          · rw [if_neg hEmit] at h4
            have hEq : (b.1, b.2.1, b.2.2 + 1) = b' := by
              have hOk : Except.ok (ForInStep.yield (b.1, b.2.1, b.2.2 + 1)) =
                Except.ok (ForInStep.yield b') := h4
              have hStep : ForInStep.yield (b.1, b.2.1, b.2.2 + 1) =
                ForInStep.yield b' := Except.ok.inj hOk
              exact ForInStep.yield.inj hStep
            subst hEq
            exact hb
      · intro w hw b hb b' hstep
        by_cases hBreak : (epoch < w.withdrawable_epoch ∨
          b.2.1.size = min P.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP (P.MAX_WITHDRAWALS_PER_PAYLOAD - 1))
        · rw [if_pos hBreak] at hstep
          have hEq : b = b' := by
            have hOk : Except.ok (ForInStep.done b) = Except.ok (ForInStep.done b') := hstep
            have hStep : ForInStep.done b = ForInStep.done b' := Except.ok.inj hOk
            exact ForInStep.done.inj hStep
          subst hEq
          exact hb
        · rw [if_neg hBreak] at hstep
          obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
          obtain ⟨bal, hbal, h2⟩ := bind_ok_elim h1
          obtain ⟨wd, hwd, h3⟩ := bind_ok_elim h2
          obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
          by_cases hEmit : ((validator.exit_epoch = FAR_FUTURE_EPOCH ∧
            minAct ≤ validator.effective_balance) ∧ minAct < balance)
          · rw [if_pos hEmit] at h4
            obtain ⟨avail, havail, h5⟩ := bind_ok_elim h4
            obtain ⟨addr, haddr, h6⟩ := bind_ok_elim h5
            obtain ⟨wid', hwid, hMapEq⟩ := map_ok_elim h6
            have hEq : ForInStep.yield (wid', b.2.1.push ⟨b.1, w.validator_index, addr,
              if avail < w.amount then avail else w.amount⟩, b.2.2 + 1) =
              ForInStep.done b' := hMapEq
            cases hEq
          · rw [if_neg hEmit] at h4
            have hEq : ForInStep.yield (b.1, b.2.1, b.2.2 + 1) =
              ForInStep.done b' := Except.ok.inj h4
            cases hEq
    have hWs2Ok : AllRecipientOk state s2.2.2 := by
      have hInit2 : (fun s : WithdrawalIndex × ValidatorIndex × Array Withdrawal =>
          AllRecipientOk state s.2.2) (s1.1, state.next_withdrawal_validator_index, s1.2.1) :=
        hWs1Ok
      refine list_forIn_ok_inv (Inv := fun s : WithdrawalIndex × ValidatorIndex × Array Withdrawal =>
        AllRecipientOk state s.2.2) hInit2 ?hy2 ?hd2 hForIn2
      · intro x hx b hb2 b' hstep
        obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
        obtain ⟨bal, hbal, h2⟩ := bind_ok_elim h1
        obtain ⟨wd, hwd, h3⟩ := bind_ok_elim h2
        obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
        by_cases hFull : isFullyWithdrawableValidator f validator balance epoch = true
        · rw [if_pos hFull] at h4
          obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
          obtain ⟨wid', hwid, h6⟩ := bind_ok_elim h5
          by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
          · rw [if_pos hCap] at h6
            have hEq : ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) =
              ForInStep.yield b' := Except.ok.inj h6
            cases hEq
          · rw [if_neg hCap] at h6
            obtain ⟨v1, hv1, h7⟩ := bind_ok_elim h6
            obtain ⟨n1, hn1, h8⟩ := bind_ok_elim h7
            obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h8
            have hEq : (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) = b' :=
              ForInStep.yield.inj hMapEq
            subst hEq
            intro w0 hw0
            simp only [Array.toList_push] at hw0
            have hOr := List.mem_append.mp hw0
            cases hOr with
            | inl hOld =>
              obtain ⟨v, hvArr, hvAddr⟩ := hb2 w0 hOld
              exact ⟨v, hvArr, hvAddr⟩
            | inr hNew =>
              simp at hNew
              subst hNew
              have hArr : state.validators.toArray[b.2.1.toNat]? = some validator := by
                have hIff := (ssz_get_ok_iff (xs := state.validators) (i := b.2.1.toNat)).mp hval
                exact hIff
              exact ⟨validator, hArr, haddr⟩
        · rw [if_neg hFull] at h4
          by_cases hPart : isPartiallyWithdrawableValidator P f validator balance = true
          · rw [if_pos hPart] at h4
            obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
            obtain ⟨maxEb, hmax, h6⟩ := bind_ok_elim h5
            obtain ⟨amt, hamt, h7⟩ := bind_ok_elim h6
            obtain ⟨wid', hwid, h8⟩ := bind_ok_elim h7
            by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
            · rw [if_pos hCap] at h8
              have hEq : ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) =
                ForInStep.yield b' := Except.ok.inj h8
              cases hEq
            · rw [if_neg hCap] at h8
              obtain ⟨v1, hv1, h9⟩ := bind_ok_elim h8
              obtain ⟨n1, hn1, h10⟩ := bind_ok_elim h9
              obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h10
              have hEq : (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) = b' :=
                ForInStep.yield.inj hMapEq
              subst hEq
              intro w0 hw0
              simp only [Array.toList_push] at hw0
              have hOr := List.mem_append.mp hw0
              cases hOr with
              | inl hOld =>
                obtain ⟨v, hvArr, hvAddr⟩ := hb2 w0 hOld
                exact ⟨v, hvArr, hvAddr⟩
              | inr hNew =>
                simp at hNew
                subst hNew
                have hArr : state.validators.toArray[b.2.1.toNat]? = some validator := by
                  have hIff := (ssz_get_ok_iff (xs := state.validators) (i := b.2.1.toNat)).mp hval
                  exact hIff
                exact ⟨validator, hArr, haddr⟩
          · rw [if_neg hPart] at h4
            by_cases hCap : b.2.2.size = P.MAX_WITHDRAWALS_PER_PAYLOAD
            · rw [if_pos hCap] at h4
              have hEq : ForInStep.done b = ForInStep.yield b' := Except.ok.inj h4
              cases hEq
            · rw [if_neg hCap] at h4
              obtain ⟨v1, hv1, h5⟩ := bind_ok_elim h4
              obtain ⟨n1, hn1, h6⟩ := bind_ok_elim h5
              obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h6
              have hEq : (b.1, vid', b.2.2) = b' := ForInStep.yield.inj hMapEq
              subst hEq
              exact hb2
      · intro x hx b hb2 b' hstep
        obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
        obtain ⟨bal, hbal, h2⟩ := bind_ok_elim h1
        obtain ⟨wd, hwd, h3⟩ := bind_ok_elim h2
        obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
        by_cases hFull : isFullyWithdrawableValidator f validator balance epoch = true
        · rw [if_pos hFull] at h4
          obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
          obtain ⟨wid', hwid, h6⟩ := bind_ok_elim h5
          by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
          · rw [if_pos hCap] at h6
            have hEq : (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) = b' := by
              have hOk : Except.ok (ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, balance⟩)) =
                Except.ok (ForInStep.done b') := h6
              exact ForInStep.done.inj (Except.ok.inj hOk)
            subst hEq
            intro w0 hw0
            simp only [Array.toList_push] at hw0
            have hOr := List.mem_append.mp hw0
            cases hOr with
            | inl hOld =>
              obtain ⟨v, hvArr, hvAddr⟩ := hb2 w0 hOld
              exact ⟨v, hvArr, hvAddr⟩
            | inr hNew =>
              simp at hNew
              subst hNew
              have hArr : state.validators.toArray[b.2.1.toNat]? = some validator := by
                have hIff := (ssz_get_ok_iff (xs := state.validators) (i := b.2.1.toNat)).mp hval
                exact hIff
              exact ⟨validator, hArr, haddr⟩
          · rw [if_neg hCap] at h6
            obtain ⟨v1, hv1, h7⟩ := bind_ok_elim h6
            obtain ⟨n1, hn1, h8⟩ := bind_ok_elim h7
            obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h8
            have hEq : ForInStep.yield (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) =
              ForInStep.done b' := hMapEq
            cases hEq
        · rw [if_neg hFull] at h4
          by_cases hPart : isPartiallyWithdrawableValidator P f validator balance = true
          · rw [if_pos hPart] at h4
            obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
            obtain ⟨maxEb, hmax, h6⟩ := bind_ok_elim h5
            obtain ⟨amt, hamt, h7⟩ := bind_ok_elim h6
            obtain ⟨wid', hwid, h8⟩ := bind_ok_elim h7
            by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
            · rw [if_pos hCap] at h8
              have hEq : (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) = b' := by
                have hOk : Except.ok (ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, amt⟩)) =
                  Except.ok (ForInStep.done b') := h8
                exact ForInStep.done.inj (Except.ok.inj hOk)
              subst hEq
              intro w0 hw0
              simp only [Array.toList_push] at hw0
              have hOr := List.mem_append.mp hw0
              cases hOr with
              | inl hOld =>
                obtain ⟨v, hvArr, hvAddr⟩ := hb2 w0 hOld
                exact ⟨v, hvArr, hvAddr⟩
              | inr hNew =>
                simp at hNew
                subst hNew
                have hArr : state.validators.toArray[b.2.1.toNat]? = some validator := by
                  have hIff := (ssz_get_ok_iff (xs := state.validators) (i := b.2.1.toNat)).mp hval
                  exact hIff
                exact ⟨validator, hArr, haddr⟩
            · rw [if_neg hCap] at h8
              obtain ⟨v1, hv1, h9⟩ := bind_ok_elim h8
              obtain ⟨n1, hn1, h10⟩ := bind_ok_elim h9
              obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h10
              have hEq : ForInStep.yield (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) =
                ForInStep.done b' := hMapEq
              cases hEq
          · rw [if_neg hPart] at h4
            by_cases hCap : b.2.2.size = P.MAX_WITHDRAWALS_PER_PAYLOAD
            · rw [if_pos hCap] at h4
              have hEq : b = b' := by
                have hOk : Except.ok (ForInStep.done b) = Except.ok (ForInStep.done b') := h4
                exact ForInStep.done.inj (Except.ok.inj hOk)
              subst hEq
              exact hb2
            · rw [if_neg hCap] at h4
              obtain ⟨v1, hv1, h5⟩ := bind_ok_elim h4
              obtain ⟨n1, hn1, h6⟩ := bind_ok_elim h5
              obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h6
              have hEq : ForInStep.yield (b.1, vid', b.2.2) =
                ForInStep.done b' := hMapEq
              cases hEq
    have hWsEq : s2.2.2 = ws := hFinal.left
    rw [←hWsEq]
    exact hWs2Ok
  · simp [he] at h2
    obtain ⟨s2, hForIn2, hMap⟩ := map_ok_elim h2
    have hFinal : s2.2.2 = ws ∧ 0 = processed := by
      have hPair : (s2.2.2, 0) = (ws, processed) := hMap
      exact Prod.mk.inj hPair
    have hWs1Ok : AllRecipientOk state (#[] : Array Withdrawal) := by
      intro w hw
      simp at hw
    have hWs2Ok : AllRecipientOk state s2.2.2 := by
      have hInit2 : (fun s : WithdrawalIndex × ValidatorIndex × Array Withdrawal =>
          AllRecipientOk state s.2.2)
          (state.next_withdrawal_index, state.next_withdrawal_validator_index, #[]) :=
        hWs1Ok
      refine list_forIn_ok_inv (Inv := fun s : WithdrawalIndex × ValidatorIndex × Array Withdrawal =>
        AllRecipientOk state s.2.2) hInit2 ?hyF ?hdF hForIn2
      · intro x hx b hb2 b' hstep
        obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
        obtain ⟨bal, hbal, h2⟩ := bind_ok_elim h1
        obtain ⟨wd, hwd, h3⟩ := bind_ok_elim h2
        obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
        by_cases hFull : isFullyWithdrawableValidator f validator balance epoch = true
        · rw [if_pos hFull] at h4
          obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
          obtain ⟨wid', hwid, h6⟩ := bind_ok_elim h5
          by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
          · rw [if_pos hCap] at h6
            have hEq : ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) =
              ForInStep.yield b' := Except.ok.inj h6
            cases hEq
          · rw [if_neg hCap] at h6
            obtain ⟨v1, hv1, h7⟩ := bind_ok_elim h6
            obtain ⟨n1, hn1, h8⟩ := bind_ok_elim h7
            obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h8
            have hEq : (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) = b' :=
              ForInStep.yield.inj hMapEq
            subst hEq
            intro w0 hw0
            simp only [Array.toList_push] at hw0
            have hOr := List.mem_append.mp hw0
            cases hOr with
            | inl hOld =>
              obtain ⟨v, hvArr, hvAddr⟩ := hb2 w0 hOld
              exact ⟨v, hvArr, hvAddr⟩
            | inr hNew =>
              simp at hNew
              subst hNew
              have hArr : state.validators.toArray[b.2.1.toNat]? = some validator := by
                have hIff := (ssz_get_ok_iff (xs := state.validators) (i := b.2.1.toNat)).mp hval
                exact hIff
              exact ⟨validator, hArr, haddr⟩
        · rw [if_neg hFull] at h4
          by_cases hPart : isPartiallyWithdrawableValidator P f validator balance = true
          · rw [if_pos hPart] at h4
            obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
            obtain ⟨maxEb, hmax, h6⟩ := bind_ok_elim h5
            obtain ⟨amt, hamt, h7⟩ := bind_ok_elim h6
            obtain ⟨wid', hwid, h8⟩ := bind_ok_elim h7
            by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
            · rw [if_pos hCap] at h8
              have hEq : ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) =
                ForInStep.yield b' := Except.ok.inj h8
              cases hEq
            · rw [if_neg hCap] at h8
              obtain ⟨v1, hv1, h9⟩ := bind_ok_elim h8
              obtain ⟨n1, hn1, h10⟩ := bind_ok_elim h9
              obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h10
              have hEq : (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) = b' :=
                ForInStep.yield.inj hMapEq
              subst hEq
              intro w0 hw0
              simp only [Array.toList_push] at hw0
              have hOr := List.mem_append.mp hw0
              cases hOr with
              | inl hOld =>
                obtain ⟨v, hvArr, hvAddr⟩ := hb2 w0 hOld
                exact ⟨v, hvArr, hvAddr⟩
              | inr hNew =>
                simp at hNew
                subst hNew
                have hArr : state.validators.toArray[b.2.1.toNat]? = some validator := by
                  have hIff := (ssz_get_ok_iff (xs := state.validators) (i := b.2.1.toNat)).mp hval
                  exact hIff
                exact ⟨validator, hArr, haddr⟩
          · rw [if_neg hPart] at h4
            by_cases hCap : b.2.2.size = P.MAX_WITHDRAWALS_PER_PAYLOAD
            · rw [if_pos hCap] at h4
              have hEq : ForInStep.done b = ForInStep.yield b' := Except.ok.inj h4
              cases hEq
            · rw [if_neg hCap] at h4
              obtain ⟨v1, hv1, h5⟩ := bind_ok_elim h4
              obtain ⟨n1, hn1, h6⟩ := bind_ok_elim h5
              obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h6
              have hEq : (b.1, vid', b.2.2) = b' := ForInStep.yield.inj hMapEq
              subst hEq
              exact hb2
      · intro x hx b hb2 b' hstep
        obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
        obtain ⟨bal, hbal, h2⟩ := bind_ok_elim h1
        obtain ⟨wd, hwd, h3⟩ := bind_ok_elim h2
        obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
        by_cases hFull : isFullyWithdrawableValidator f validator balance epoch = true
        · rw [if_pos hFull] at h4
          obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
          obtain ⟨wid', hwid, h6⟩ := bind_ok_elim h5
          by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
          · rw [if_pos hCap] at h6
            have hEq : (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) = b' := by
              have hOk : Except.ok (ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, balance⟩)) =
                Except.ok (ForInStep.done b') := h6
              exact ForInStep.done.inj (Except.ok.inj hOk)
            subst hEq
            intro w0 hw0
            simp only [Array.toList_push] at hw0
            have hOr := List.mem_append.mp hw0
            cases hOr with
            | inl hOld =>
              obtain ⟨v, hvArr, hvAddr⟩ := hb2 w0 hOld
              exact ⟨v, hvArr, hvAddr⟩
            | inr hNew =>
              simp at hNew
              subst hNew
              have hArr : state.validators.toArray[b.2.1.toNat]? = some validator := by
                have hIff := (ssz_get_ok_iff (xs := state.validators) (i := b.2.1.toNat)).mp hval
                exact hIff
              exact ⟨validator, hArr, haddr⟩
          · rw [if_neg hCap] at h6
            obtain ⟨v1, hv1, h7⟩ := bind_ok_elim h6
            obtain ⟨n1, hn1, h8⟩ := bind_ok_elim h7
            obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h8
            have hEq : ForInStep.yield (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) =
              ForInStep.done b' := hMapEq
            cases hEq
        · rw [if_neg hFull] at h4
          by_cases hPart : isPartiallyWithdrawableValidator P f validator balance = true
          · rw [if_pos hPart] at h4
            obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
            obtain ⟨maxEb, hmax, h6⟩ := bind_ok_elim h5
            obtain ⟨amt, hamt, h7⟩ := bind_ok_elim h6
            obtain ⟨wid', hwid, h8⟩ := bind_ok_elim h7
            by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
            · rw [if_pos hCap] at h8
              have hEq : (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) = b' := by
                have hOk : Except.ok (ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, amt⟩)) =
                  Except.ok (ForInStep.done b') := h8
                exact ForInStep.done.inj (Except.ok.inj hOk)
              subst hEq
              intro w0 hw0
              simp only [Array.toList_push] at hw0
              have hOr := List.mem_append.mp hw0
              cases hOr with
              | inl hOld =>
                obtain ⟨v, hvArr, hvAddr⟩ := hb2 w0 hOld
                exact ⟨v, hvArr, hvAddr⟩
              | inr hNew =>
                simp at hNew
                subst hNew
                have hArr : state.validators.toArray[b.2.1.toNat]? = some validator := by
                  have hIff := (ssz_get_ok_iff (xs := state.validators) (i := b.2.1.toNat)).mp hval
                  exact hIff
                exact ⟨validator, hArr, haddr⟩
            · rw [if_neg hCap] at h8
              obtain ⟨v1, hv1, h9⟩ := bind_ok_elim h8
              obtain ⟨n1, hn1, h10⟩ := bind_ok_elim h9
              obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h10
              have hEq : ForInStep.yield (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) =
                ForInStep.done b' := hMapEq
              cases hEq
          · rw [if_neg hPart] at h4
            by_cases hCap : b.2.2.size = P.MAX_WITHDRAWALS_PER_PAYLOAD
            · rw [if_pos hCap] at h4
              have hEq : b = b' := by
                have hOk : Except.ok (ForInStep.done b) = Except.ok (ForInStep.done b') := h4
                exact ForInStep.done.inj (Except.ok.inj hOk)
              subst hEq
              exact hb2
            · rw [if_neg hCap] at h4
              obtain ⟨v1, hv1, h5⟩ := bind_ok_elim h4
              obtain ⟨n1, hn1, h6⟩ := bind_ok_elim h5
              obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h6
              have hEq : ForInStep.yield (b.1, vid', b.2.2) =
                ForInStep.done b' := hMapEq
              cases hEq
    have hWsEq : s2.2.2 = ws := hFinal.left
    rw [←hWsEq]
    exact hWs2Ok

end Recipient

/-! ## Loop-1 shape (P4 clause 2, first half) -/

section Loop1

variable {P : Preset} {f : CFork}

/-- `ws = ws1 ++ ws2` with `ws1` from loop 1, each entry bounded by its pending
amount. `chosen` witnesses distinct pending positions in order. `pending` is
the loop-1 input array: the pending list at Electra, `#[]` before. -/
def Loop1Witness (ws1 : Array Withdrawal)
    (pending : Array PendingPartialWithdrawal) (processed : Nat) : Prop :=
  ws1.size ≤ processed ∧
  processed ≤ pending.size ∧
  ∃ chosen : List PendingPartialWithdrawal,
    chosen.Sublist (pending.toList.take processed) ∧
    chosen.length = ws1.size ∧
    ∀ (i : Nat) (w : Withdrawal) (p : PendingPartialWithdrawal),
      ws1.toList[i]? = some w → chosen[i]? = some p →
        w.validator_index = p.validator_index ∧
          w.amount.toNat ≤ p.amount.toNat

/-- Per-emission facts for loop 1: `w` was emitted for pending entry `p`,
with the loop balance read `sBalU`, the withdrawn sum `wdrawnU`, and the
result `balU`. The withdrawn sum is existentially hidden (`withdrawnFor` is
private to `Block.lean`); the state read and the floor inputs are explicit. -/
def Loop1EntryOk (state : BeaconState P f) (minAct : U64)
    (w : Withdrawal) (p : PendingPartialWithdrawal) : Prop :=
  w.validator_index = p.validator_index ∧
  w.amount.toNat ≤ p.amount.toNat ∧
  ∃ sBalU wdrawnU balU : U64,
    state.balances.get w.validator_index.toNat "get_expected_withdrawals" = .ok sBalU ∧
    U64.sub? sBalU wdrawnU "get_expected_withdrawals" = .ok balU ∧
    minAct.toNat ≤ balU.toNat ∧
    w.amount.toNat ≤ balU.toNat - minAct.toNat

/-- Each loop-1 withdrawal leaves its loop balance above the floor: for
`w ∈ ws1` the loop read `sBalU` from `state.balances` and subtracted some
`wdrawnU` (the withdrawn sum at emission, existentially hidden since
`withdrawnFor` is private to `Block.lean`) to get `balU`, and
`minAct ≤ balU.toNat - w.amount.toNat`. -/
def Loop1Floor (state : BeaconState P f) (ws1 : Array Withdrawal) (minAct : Nat) : Prop :=
  ∀ w ∈ ws1.toList, ∃ sBalU wdrawnU balU : U64,
    state.balances.get w.validator_index.toNat "get_expected_withdrawals" = .ok sBalU ∧
    U64.sub? sBalU wdrawnU "get_expected_withdrawals" = .ok balU ∧
    minAct ≤ balU.toNat - w.amount.toNat

/-- Loop-1 emissions package: the split, the shape witness, and the floor
inputs. `getExpected_loop1_shape` and `getExpected_loop1_floor` are
corollaries; the loop-1 invariant is established once, here. -/
theorem loop1_emissions (state : BeaconState P f)
    (ws : Array Withdrawal) (processed : Nat)
    (h : getExpectedWithdrawals state = .ok (ws, processed)) :
    ∃ (ws1 ws2 : Array Withdrawal) (pending : Array PendingPartialWithdrawal),
      ws.toList = ws1.toList ++ ws2.toList ∧
      (if he : f.atLeast .electra = true then
        ∃ l, state.pendingPartialWithdrawals = .ok l ∧ pending = l.toArray
        else pending = #[]) ∧
      Loop1Witness ws1 pending processed ∧
      Loop1Floor state ws1 P.MIN_ACTIVATION_BALANCE := by
  unfold getExpectedWithdrawals at h
  dsimp at h
  obtain ⟨epoch, hepoch, h1⟩ := bind_ok_elim h
  obtain ⟨minAct, hminAct, h2⟩ := bind_ok_elim h1
  by_cases he : f.atLeast .electra = true
  · simp [he] at h2
    obtain ⟨pendingList, hpend, h3⟩ := bind_ok_elim h2
    obtain ⟨s1, hForIn1, h4⟩ := bind_ok_elim h3
    obtain ⟨s2, hForIn2, hMap⟩ := map_ok_elim h4
    have hFinal : s2.2.2 = ws ∧ s1.2.2 = processed := by
      have hPair : (s2.2.2, s1.2.2) = (ws, processed) := hMap
      exact Prod.mk.inj hPair
    have hLoop1 : ∃ pref suff : List PendingPartialWithdrawal,
        pendingList.toArray.toList = pref ++ suff ∧
        s1.2.2 = pref.length ∧
        ∃ chosen : List PendingPartialWithdrawal,
          chosen.Sublist pref ∧
          chosen.length = s1.2.1.toList.length ∧
          (∀ (i : Nat) (w : Withdrawal) (p : PendingPartialWithdrawal),
            s1.2.1.toList[i]? = some w → chosen[i]? = some p →
            Loop1EntryOk state minAct w p) := by
      refine array_forIn_ok_pref_inv (PInv := fun pref b =>
        b.2.2 = pref.length ∧
        ∃ chosen : List PendingPartialWithdrawal,
          chosen.Sublist pref ∧
          chosen.length = b.2.1.toList.length ∧
          ∀ (i : Nat) (w : Withdrawal) (p : PendingPartialWithdrawal),
            b.2.1.toList[i]? = some w → chosen[i]? = some p →
            Loop1EntryOk state minAct w p) ?h0 ?hy ?hd hForIn1
      · refine ⟨rfl, [], List.Sublist.refl _, ?_, ?_⟩
        · simp
        · intro i w p h1 h2
          simp at h1
      · intro pref x suff b b' hlpref hInv hstep
        obtain ⟨hproc, chosen, hsub, hlen, hcorr⟩ := hInv
        by_cases hBreak : (epoch < x.withdrawable_epoch ∨
          b.2.1.size = min P.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP (P.MAX_WITHDRAWALS_PER_PAYLOAD - 1))
        · rw [if_pos hBreak] at hstep
          have hEq : ForInStep.done b = ForInStep.yield b' := Except.ok.inj hstep
          cases hEq
        · rw [if_neg hBreak] at hstep
          obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
          obtain ⟨bal, hbal, h2⟩ := bind_ok_elim h1
          obtain ⟨wdrawn, _hwdrawn, h3⟩ := bind_ok_elim h2
          obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
          by_cases hEmit : ((validator.exit_epoch = FAR_FUTURE_EPOCH ∧
            minAct ≤ validator.effective_balance) ∧ minAct < balance)
          · rw [if_pos hEmit] at h4
            obtain ⟨avail, havail, h5⟩ := bind_ok_elim h4
            obtain ⟨addr, haddr, h6⟩ := bind_ok_elim h5
            obtain ⟨wid', hwid, hMapEq⟩ := map_ok_elim h6
            have hEq : (wid', b.2.1.push ⟨b.1, x.validator_index, addr,
              if avail < x.amount then avail else x.amount⟩, b.2.2 + 1) = b' :=
              ForInStep.yield.inj hMapEq
            subst hEq
            refine ⟨by simp [hproc], chosen ++ [x],
              List.Sublist.append hsub (List.Sublist.refl _), ?_, ?_⟩
            · simp only [Array.toList_push, List.length_append,
                List.length_singleton, hlen]
            · intro i w p hi1 hi2
              rw [Array.toList_push] at hi1
              by_cases hj : i < b.2.1.toList.length
              · rw [getElem?_append_prefix _ _ _ hj] at hi1
                have hj' : i < chosen.length := by omega
                rw [getElem?_append_prefix _ _ _ hj'] at hi2
                exact hcorr i w p hi1 hi2
              · have hlenA : (b.2.1.toList ++ [(⟨b.1, x.validator_index, addr,
                    if avail < x.amount then avail else x.amount⟩ : Withdrawal)]).length =
                    b.2.1.toList.length + 1 := by simp
                have hiLT : i < b.2.1.toList.length + 1 := by
                  by_contra hc
                  push_neg at hc
                  have hnone : (b.2.1.toList ++ [(⟨b.1, x.validator_index, addr,
                    if avail < x.amount then avail else x.amount⟩ : Withdrawal)])[i]? = none :=
                    List.getElem?_eq_none (by omega)
                  rw [hi1] at hnone
                  cases hnone
                have hiEq : i = b.2.1.toList.length := by omega
                have hiEqC : i = chosen.length := by omega
                rw [hiEq, getElem?_push_last] at hi1
                rw [hiEqC, getElem?_push_last] at hi2
                cases hi1
                cases hi2
                refine ⟨rfl, ?_, bal, wdrawn, balance, hbal, hbal2, ?_, ?_⟩
                · show (if avail < x.amount then avail else x.amount).toNat ≤
                    x.amount.toNat
                  rw [U64.min_toNat]
                  exact Nat.min_le_right _ _
                · exact U64.sub?_ok_iff.mp ⟨avail, havail⟩
                · have hAv : avail.toNat = balance.toNat - minAct.toNat :=
                    U64.toNat_sub? havail
                  show (if avail < x.amount then avail else x.amount).toNat ≤
                    balance.toNat - minAct.toNat
                  have hAm : (if avail < x.amount then avail else x.amount).toNat ≤
                      avail.toNat := by
                    rw [U64.min_toNat]
                    exact Nat.min_le_left _ _
                  omega
          · rw [if_neg hEmit] at h4
            have hEq : (b.1, b.2.1, b.2.2 + 1) = b' := by
              have hOk : Except.ok (ForInStep.yield (b.1, b.2.1, b.2.2 + 1)) =
                Except.ok (ForInStep.yield b') := h4
              exact ForInStep.yield.inj (Except.ok.inj hOk)
            subst hEq
            refine ⟨by simp [hproc], chosen, ?_, hlen, ?_⟩
            · exact hsub.trans (by simpa using
                List.Sublist.append (List.Sublist.refl pref) List.Sublist.slnil)
            · intro i w p hi1 hi2
              exact hcorr i w p hi1 hi2
      · intro pref x suff b b' hlpref hInv hstep
        by_cases hBreak : (epoch < x.withdrawable_epoch ∨
          b.2.1.size = min P.MAX_PENDING_PARTIALS_PER_WITHDRAWALS_SWEEP (P.MAX_WITHDRAWALS_PER_PAYLOAD - 1))
        · rw [if_pos hBreak] at hstep
          have hEq : b = b' := ForInStep.done.inj (Except.ok.inj hstep)
          subst hEq
          exact hInv
        · rw [if_neg hBreak] at hstep
          obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
          obtain ⟨bal, hbal, h2⟩ := bind_ok_elim h1
          obtain ⟨wdrawn, _hwdrawn, h3⟩ := bind_ok_elim h2
          obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
          by_cases hEmit : ((validator.exit_epoch = FAR_FUTURE_EPOCH ∧
            minAct ≤ validator.effective_balance) ∧ minAct < balance)
          · rw [if_pos hEmit] at h4
            obtain ⟨avail, havail, h5⟩ := bind_ok_elim h4
            obtain ⟨addr, haddr, h6⟩ := bind_ok_elim h5
            obtain ⟨wid', hwid, hMapEq⟩ := map_ok_elim h6
            have hEq : ForInStep.yield (wid', b.2.1.push ⟨b.1, x.validator_index, addr,
              if avail < x.amount then avail else x.amount⟩, b.2.2 + 1) =
              ForInStep.done b' := hMapEq
            cases hEq
          · rw [if_neg hEmit] at h4
            have hEq : ForInStep.yield (b.1, b.2.1, b.2.2 + 1) =
              ForInStep.done b' := Except.ok.inj h4
            cases hEq
    obtain ⟨pref, suff, hlpref, hprocLen, chosen, hsub, hlen, hcorr⟩ := hLoop1
    have hprefSub : pref.Sublist pendingList.toArray.toList := by
      rw [hlpref]
      simpa using List.Sublist.append (List.Sublist.refl pref) List.Sublist.slnil
    have hLoop2 : ∃ rest : List Withdrawal,
        s2.2.2.toList = s1.2.1.toList ++ rest := by
      refine list_forIn_ok_inv (Inv := fun s : WithdrawalIndex × ValidatorIndex × Array Withdrawal =>
        ∃ rest : List Withdrawal, s.2.2.toList = s1.2.1.toList ++ rest)
        ⟨[], by simp⟩ ?hy2 ?hd2 hForIn2
      · intro x hx b hb2 b' hstep
        obtain ⟨rest, hrest⟩ := hb2
        obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
        obtain ⟨bal, hbal, h2⟩ := bind_ok_elim h1
        obtain ⟨wdrawn, _hwdrawn, h3⟩ := bind_ok_elim h2
        obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
        by_cases hFull : isFullyWithdrawableValidator f validator balance epoch = true
        · rw [if_pos hFull] at h4
          obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
          obtain ⟨wid', hwid, h6⟩ := bind_ok_elim h5
          by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
          · rw [if_pos hCap] at h6
            have hOk : Except.ok (ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, balance⟩)) =
              Except.ok (ForInStep.yield b') := h6
            have hC := Except.ok.inj hOk
            cases hC
          · rw [if_neg hCap] at h6
            obtain ⟨v1, hv1, h7⟩ := bind_ok_elim h6
            obtain ⟨n1, hn1, h8⟩ := bind_ok_elim h7
            obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h8
            have hEq : (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) = b' :=
              ForInStep.yield.inj hMapEq
            subst hEq
            exact ⟨rest ++ [⟨b.1, b.2.1, addr, balance⟩],
              by rw [Array.toList_push, hrest, List.append_assoc]⟩
        · rw [if_neg hFull] at h4
          by_cases hPart : isPartiallyWithdrawableValidator P f validator balance = true
          · rw [if_pos hPart] at h4
            obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
            obtain ⟨maxEb, hmax, h6⟩ := bind_ok_elim h5
            obtain ⟨amt, hamt, h7⟩ := bind_ok_elim h6
            obtain ⟨wid', hwid, h8⟩ := bind_ok_elim h7
            by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
            · rw [if_pos hCap] at h8
              have hOk : Except.ok (ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, amt⟩)) =
                Except.ok (ForInStep.yield b') := h8
              have hC := Except.ok.inj hOk
              cases hC
            · rw [if_neg hCap] at h8
              obtain ⟨v1, hv1, h9⟩ := bind_ok_elim h8
              obtain ⟨n1, hn1, h10⟩ := bind_ok_elim h9
              obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h10
              have hEq : (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) = b' :=
                ForInStep.yield.inj hMapEq
              subst hEq
              exact ⟨rest ++ [⟨b.1, b.2.1, addr, amt⟩],
                by rw [Array.toList_push, hrest, List.append_assoc]⟩
          · rw [if_neg hPart] at h4
            by_cases hCap : b.2.2.size = P.MAX_WITHDRAWALS_PER_PAYLOAD
            · rw [if_pos hCap] at h4
              have hOk : Except.ok (ForInStep.done b) = Except.ok (ForInStep.yield b') := h4
              have hC := Except.ok.inj hOk
              cases hC
            · rw [if_neg hCap] at h4
              obtain ⟨v1, hv1, h5⟩ := bind_ok_elim h4
              obtain ⟨n1, hn1, h6⟩ := bind_ok_elim h5
              obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h6
              have hEq : (b.1, vid', b.2.2) = b' := ForInStep.yield.inj hMapEq
              subst hEq
              exact ⟨rest, hrest⟩
      · intro x hx b hb2 b' hstep
        obtain ⟨rest, hrest⟩ := hb2
        obtain ⟨validator, hval, h1⟩ := bind_ok_elim hstep
        obtain ⟨bal, hbal, h2⟩ := bind_ok_elim h1
        obtain ⟨wdrawn, _hwdrawn, h3⟩ := bind_ok_elim h2
        obtain ⟨balance, hbal2, h4⟩ := bind_ok_elim h3
        by_cases hFull : isFullyWithdrawableValidator f validator balance epoch = true
        · rw [if_pos hFull] at h4
          obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
          obtain ⟨wid', hwid, h6⟩ := bind_ok_elim h5
          by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
          · rw [if_pos hCap] at h6
            have hEq : (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) = b' := by
              have hOk : Except.ok (ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, balance⟩)) =
                Except.ok (ForInStep.done b') := h6
              exact ForInStep.done.inj (Except.ok.inj hOk)
            subst hEq
            exact ⟨rest ++ [⟨b.1, b.2.1, addr, balance⟩],
              by rw [Array.toList_push, hrest, List.append_assoc]⟩
          · rw [if_neg hCap] at h6
            obtain ⟨v1, hv1, h7⟩ := bind_ok_elim h6
            obtain ⟨n1, hn1, h8⟩ := bind_ok_elim h7
            obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h8
            have hEq : ForInStep.yield (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, balance⟩) =
              ForInStep.done b' := hMapEq
            cases hEq
        · rw [if_neg hFull] at h4
          by_cases hPart : isPartiallyWithdrawableValidator P f validator balance = true
          · rw [if_pos hPart] at h4
            obtain ⟨addr, haddr, h5⟩ := bind_ok_elim h4
            obtain ⟨maxEb, hmax, h6⟩ := bind_ok_elim h5
            obtain ⟨amt, hamt, h7⟩ := bind_ok_elim h6
            obtain ⟨wid', hwid, h8⟩ := bind_ok_elim h7
            by_cases hCap : b.2.2.size + 1 = P.MAX_WITHDRAWALS_PER_PAYLOAD
            · rw [if_pos hCap] at h8
              have hEq : (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) = b' := by
                have hOk : Except.ok (ForInStep.done (wid', b.2.1, b.2.2.push ⟨b.1, b.2.1, addr, amt⟩)) =
                  Except.ok (ForInStep.done b') := h8
                exact ForInStep.done.inj (Except.ok.inj hOk)
              subst hEq
              exact ⟨rest ++ [⟨b.1, b.2.1, addr, amt⟩],
                by rw [Array.toList_push, hrest, List.append_assoc]⟩
            · rw [if_neg hCap] at h8
              obtain ⟨v1, hv1, h9⟩ := bind_ok_elim h8
              obtain ⟨n1, hn1, h10⟩ := bind_ok_elim h9
              obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h10
              have hEq : ForInStep.yield (wid', vid', b.2.2.push ⟨b.1, b.2.1, addr, amt⟩) =
                ForInStep.done b' := hMapEq
              cases hEq
          · rw [if_neg hPart] at h4
            by_cases hCap : b.2.2.size = P.MAX_WITHDRAWALS_PER_PAYLOAD
            · rw [if_pos hCap] at h4
              have hEq : b = b' := by
                have hOk : Except.ok (ForInStep.done b) = Except.ok (ForInStep.done b') := h4
                exact ForInStep.done.inj (Except.ok.inj hOk)
              subst hEq
              exact ⟨rest, hrest⟩
            · rw [if_neg hCap] at h4
              obtain ⟨v1, hv1, h5⟩ := bind_ok_elim h4
              obtain ⟨n1, hn1, h6⟩ := bind_ok_elim h5
              obtain ⟨vid', hvid, hMapEq⟩ := map_ok_elim h6
              have hEq : ForInStep.yield (b.1, vid', b.2.2) =
                ForInStep.done b' := hMapEq
              cases hEq
    obtain ⟨rest, hrest⟩ := hLoop2
    have htakePre : ∀ pp ss : List PendingPartialWithdrawal,
        (pp ++ ss).take pp.length = pp := by
      intro pp ss
      induction pp with
      | nil => simp
      | cons a t ih => simp [ih]
    have htake : pendingList.toArray.toList.take processed = pref := by
      rw [hlpref, ← hFinal.right, hprocLen]
      exact htakePre pref suff
    refine ⟨s1.2.1, rest.toArray, pendingList.toArray, ?_, ?_, ?_, ?_⟩
    · rw [← hFinal.left, hrest, List.toList_toArray]
    · simpa [he] using ⟨pendingList, hpend, rfl⟩
    · refine ⟨?_, ?_, chosen, ?_, ?_, ?_⟩
      · rw [Array.size_eq_length_toList]
        have hle := List.Sublist.length_le hsub
        omega
      · rw [Array.size_eq_length_toList]
        have hle := List.Sublist.length_le hprefSub
        omega
      · rw [htake]
        exact hsub
      · rw [Array.size_eq_length_toList]
        exact hlen
      · intro i w p hi1 hi2
        obtain ⟨hvi, hamt, _erest⟩ := hcorr i w p hi1 hi2
        exact ⟨hvi, hamt⟩
    · intro w hmem
      obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
      have hiLT : i < s1.2.1.toList.length := by
        by_contra hc
        push_neg at hc
        have hnone : s1.2.1.toList[i]? = none := List.getElem?_eq_none hc
        rw [hi] at hnone
        cases hnone
      have hiC : i < chosen.length := by omega
      have hc2 : chosen[i]? = some (chosen[i]'hiC) :=
        List.getElem?_eq_getElem hiC
      obtain ⟨hvi, hamt, sBalU, wdrawnU, balU, hget, hsubU, hfloor1, hfloor2⟩ :=
        hcorr i w _ hi hc2
      refine ⟨sBalU, wdrawnU, balU, hget, hsubU, ?_⟩
      have hminActNat : minAct.toNat = P.MIN_ACTIVATION_BALANCE :=
        U64.ofNat?_toNat (show U64.ofNat? _ _ = .ok minAct from hminAct)
      omega
  · simp [he] at h2
    obtain ⟨s2, hForIn2, hMap⟩ := map_ok_elim h2
    have hFinal : s2.2.2 = ws ∧ 0 = processed := by
      have hPair : (s2.2.2, 0) = (ws, processed) := hMap
      exact Prod.mk.inj hPair
    have hproc0 : processed = 0 := hFinal.right.symm
    refine ⟨#[], ws, #[], ?_, ?_, ?_, ?_⟩
    · simp
    · simpa [he]
    · rw [hproc0]
      refine ⟨?_, ?_, [], ?_, ?_, ?_⟩
      · simp
      · simp
      · exact List.nil_sublist _
      · simp
      · intro i w p h1 h2
        simp at h1
    · intro w hmem
      simp at hmem

theorem getExpected_loop1_shape (state : BeaconState P f)
    (ws : Array Withdrawal) (processed : Nat)
    (h : getExpectedWithdrawals state = .ok (ws, processed)) :
    ∃ (ws1 ws2 : Array Withdrawal) (pending : Array PendingPartialWithdrawal),
      ws.toList = ws1.toList ++ ws2.toList ∧
      (if he : f.atLeast .electra = true then
        ∃ l, state.pendingPartialWithdrawals = .ok l ∧ pending = l.toArray
        else pending = #[]) ∧
      Loop1Witness ws1 pending processed := by
  obtain ⟨ws1, ws2, pending, hsplit, hpend, hwit, _hf⟩ := loop1_emissions state ws processed h
  exact ⟨ws1, ws2, pending, hsplit, hpend, hwit⟩

end Loop1

/-! ## Floor (P4 clause 2, second half) -/

section Floor

variable {P : Preset} {f : CFork}

theorem getExpected_loop1_floor (state : BeaconState P f)
    (ws : Array Withdrawal) (processed : Nat)
    (h : getExpectedWithdrawals state = .ok (ws, processed)) :
    ∃ ws1 : Array Withdrawal,
      ws1.toList.Sublist ws.toList ∧
        Loop1Floor state ws1 P.MIN_ACTIVATION_BALANCE := by
  obtain ⟨ws1, ws2, pending, hsplit, hpend, hwit, hfloor⟩ :=
    loop1_emissions state ws processed h
  refine ⟨ws1, ?_, hfloor⟩
  rw [hsplit]
  simpa using List.Sublist.append (List.Sublist.refl _) List.Sublist.slnil

end Floor


/-! ## Processed bound and preset premises -/

section Bounds

variable {P : Preset} {f : CFork}

theorem getExpected_processed_le (state : BeaconState P f)
    (ws : Array Withdrawal) (processed : Nat)
    (h : getExpectedWithdrawals state = .ok (ws, processed)) :
    ∃ pending : Array PendingPartialWithdrawal,
      (if he : f.atLeast .electra = true then
        ∃ l, state.pendingPartialWithdrawals = .ok l ∧ pending = l.toArray
        else pending = #[]) ∧
      processed ≤ pending.size := by
  obtain ⟨ws1, ws2, pending, hsplit, hpend, hwit, _hf⟩ :=
    loop1_emissions state ws processed h
  exact ⟨pending, hpend, hwit.2.1⟩

theorem slots_per_epoch_ge_two_mainnet : 2 ≤ Preset.mainnet.SLOTS_PER_EPOCH := by
  decide

theorem slots_per_epoch_ge_two_minimal : 2 ≤ Preset.minimal.SLOTS_PER_EPOCH := by
  decide

theorem minAct_le_maxEb_mainnet :
    Preset.mainnet.MIN_ACTIVATION_BALANCE ≤ Preset.mainnet.MAX_EFFECTIVE_BALANCE_ELECTRA := by
  decide

theorem minAct_le_maxEb_minimal :
    Preset.minimal.MIN_ACTIVATION_BALANCE ≤ Preset.minimal.MAX_EFFECTIVE_BALANCE_ELECTRA := by
  decide

end Bounds

end Facts
end JauneConsensus
