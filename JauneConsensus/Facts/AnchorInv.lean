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

/-! ## Byte codec round trip (local; candidates for `Jaune/Basic.lean`) -/

theorem u16_ofBytes_toNat (a b : UInt8) :
    (Jaune.UInt16.ofBytes a b).toNat = a.toNat * 256 + b.toNat := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  simp only [Jaune.UInt16.ofBytes, UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16]
  have h8 : UInt16.toNat 8 % 16 = 8 := rfl
  rw [h8, Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
    ← Jaune.Nat.mul_two_pow_add_eq_shl_or (by omega)]
  rfl

theorem u16_toBytes_ofBytes (a b : UInt8) :
    Jaune.UInt16.toBytes (Jaune.UInt16.ofBytes a b) = [a, b] := by
  have ha := a.toNat_lt; have hb := b.toNat_lt
  have hn := u16_ofBytes_toNat a b
  simp only [Jaune.UInt16.toBytes, List.cons.injEq, and_true]
  constructor
  · apply UInt8.toNat_inj.mp
    simp only [UInt16.toNat_toUInt8, UInt16.toNat_shiftRight, hn]
    have h8 : UInt16.toNat 8 % 16 = 8 := rfl
    rw [h8, Nat.shiftRight_eq_div_pow]; omega
  · apply UInt8.toNat_inj.mp
    simp only [UInt16.toNat_toUInt8, hn]; omega

theorem u32_toBytes_halves (x y : UInt16) :
    Jaune.UInt32.toBytes ((x.toUInt32 <<< 16) ||| y.toUInt32) =
      Jaune.UInt16.toBytes x ++ Jaune.UInt16.toBytes y := by
  have hx := x.toNat_lt; have hy := y.toNat_lt
  have hn : ((x.toUInt32 <<< 16) ||| y.toUInt32).toNat = x.toNat * 2 ^ 16 + y.toNat := by
    simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt16.toNat_toUInt32]
    have h : UInt32.toNat 16 % 32 = 16 := rfl
    rw [h, Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
      ← Jaune.Nat.mul_two_pow_add_eq_shl_or (by omega)]
  simp only [Jaune.UInt32.toBytes]
  congr 2
  · apply UInt16.toNat_inj.mp
    simp only [UInt32.toNat_toUInt16, UInt32.toNat_shiftRight, hn]
    have h : UInt32.toNat 16 % 32 = 16 := rfl
    rw [h, Nat.shiftRight_eq_div_pow]; omega
  · apply UInt16.toNat_inj.mp
    simp only [UInt32.toNat_toUInt16, hn]; omega

theorem u64_toBytes_halves (x y : UInt32) :
    Jaune.UInt64.toBytes ((x.toUInt64 <<< 32) ||| y.toUInt64) =
      Jaune.UInt32.toBytes x ++ Jaune.UInt32.toBytes y := by
  have hx := x.toNat_lt; have hy := y.toNat_lt
  have hn : ((x.toUInt64 <<< 32) ||| y.toUInt64).toNat = x.toNat * 2 ^ 32 + y.toNat := by
    simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt32.toNat_toUInt64]
    have h : UInt64.toNat 32 % 64 = 32 := rfl
    rw [h, Nat.mod_eq_of_lt (by rw [Nat.shiftLeft_eq]; omega),
      ← Jaune.Nat.mul_two_pow_add_eq_shl_or (by omega)]
  simp only [Jaune.UInt64.toBytes]
  congr 2
  · apply UInt32.toNat_inj.mp
    simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, hn]
    have h : UInt64.toNat 32 % 64 = 32 := rfl
    rw [h, Nat.shiftRight_eq_div_pow]; omega
  · apply UInt32.toNat_inj.mp
    simp only [UInt64.toNat_toUInt32, hn]; omega

theorem u64_toBytes_ofBytes (a b c d e f g h : UInt8) :
    Jaune.UInt64.toBytes (Jaune.UInt64.ofBytes a b c d e f g h) = [a, b, c, d, e, f, g, h] := by
  rw [Jaune.UInt64.ofBytes_eq_halves, u64_toBytes_halves, Jaune.UInt32.ofBytes_eq_halves,
    Jaune.UInt32.ofBytes_eq_halves, u32_toBytes_halves, u32_toBytes_halves, u16_toBytes_ofBytes,
    u16_toBytes_ofBytes, u16_toBytes_ofBytes, u16_toBytes_ofBytes]
  rfl

/-- `toBytes ∘ toB256` is the identity on 32-byte lists. -/
theorem b256_toBytes_toB256 (l : Jaune.Bytes) (hl : l.length = 32) :
    (Jaune.Bytes.toB256 l).toBytes = l := by
  match l, hl with
  | [a0, a1, a2, a3, a4, a5, a6, a7, b0, b1, b2, b3, b4, b5, b6, b7,
     c0, c1, c2, c3, c4, c5, c6, c7, d0, d1, d2, d3, d4, d5, d6, d7], _ =>
    simp only [Jaune.Bytes.toB256, Jaune.Bytes.toB256_go_eight_cons]
    simp only [Jaune.Bytes.toB256.go, Jaune.B256.toBytes, Jaune.B128.toBytes, u64_toBytes_ofBytes]
    rfl

/-! ## The step relation -/

/-- `v'` keeps `v`'s compounding status and, if `v` has an execution credential, keeps one with the
same address bytes `12..32`. -/
def CredKeep (v v' : Validator) : Prop :=
  (hasCompoundingWithdrawalCredential v = true → hasCompoundingWithdrawalCredential v' = true) ∧
  (hasExecutionWithdrawalCredential v = true →
    hasExecutionWithdrawalCredential v' = true ∧
      v'.withdrawal_credentials.toBytes.drop 12 = v.withdrawal_credentials.toBytes.drop 12)

theorem CredKeep.refl (v : Validator) : CredKeep v v := ⟨id, fun h => ⟨h, rfl⟩⟩

theorem CredKeep.trans {u v w : Validator} (h1 : CredKeep u v) (h2 : CredKeep v w) : CredKeep u w :=
  ⟨fun h => h2.1 (h1.1 h), fun h =>
    have a := h1.2 h
    have b := h2.2 a.1
    ⟨b.1, b.2.trans a.2⟩⟩

theorem credKeep_of_wc {v v' : Validator}
    (h : v'.withdrawal_credentials = v.withdrawal_credentials) : CredKeep v v' := by
  unfold CredKeep hasExecutionWithdrawalCredential hasEth1WithdrawalCredential
    hasCompoundingWithdrawalCredential
  rw [h]
  exact ⟨id, fun h => ⟨h, rfl⟩⟩

/-- **Address stability** between two states: every validator of `st` with an execution credential
is a validator of `st'` with an execution credential and the same bytes `12..32`. -/
def AddrStable {f f' : CFork} (st : BeaconState P f) (st' : BeaconState P f') : Prop :=
  ∀ (j : Nat) (v : Validator), st.validators.toArray[j]? = some v →
    hasExecutionWithdrawalCredential v = true →
    ∃ v', st'.validators.toArray[j]? = some v' ∧ hasExecutionWithdrawalCredential v' = true ∧
      v'.withdrawal_credentials.toBytes.drop 12 = v.withdrawal_credentials.toBytes.drop 12

/-- Validator indices persist and every persisting validator satisfies `CredKeep`. -/
def CredStep {f f' : CFork} (st : BeaconState P f) (st' : BeaconState P f') : Prop :=
  st.validators.toArray.size ≤ st'.validators.toArray.size ∧
  ∀ (j : Nat) (v v' : Validator), st.validators.toArray[j]? = some v →
    st'.validators.toArray[j]? = some v' → CredKeep v v'

/-- The per-transition fact: `CredStep` and `AnchorInv` preservation. It composes. -/
def Pres {f f' : CFork} (st : BeaconState P f) (st' : BeaconState P f') : Prop :=
  CredStep st st' ∧ (AnchorInv st → AnchorInv st')

theorem getElem?_some_of_le {α β : Type} {xs : Array α} {ys : Array β} (h : xs.size ≤ ys.size)
    {j : Nat} {v : α} (hv : xs[j]? = some v) : ∃ w, ys[j]? = some w :=
  ⟨_, Array.getElem?_eq_getElem (Nat.lt_of_lt_of_le (Array.getElem?_eq_some_iff.mp hv).1 h)⟩

theorem CredStep.addr {f f' : CFork} {st : BeaconState P f} {st' : BeaconState P f'}
    (h : CredStep st st') : AddrStable st st' := by
  intro j v hv he
  obtain ⟨v', hv'⟩ := getElem?_some_of_le h.1 hv
  exact ⟨v', hv', (h.2 j v v' hv hv').2 he⟩

theorem Pres.addr {f f' : CFork} {st : BeaconState P f} {st' : BeaconState P f'}
    (h : Pres st st') : AddrStable st st' := h.1.addr

theorem Pres.anchor {f f' : CFork} {st : BeaconState P f} {st' : BeaconState P f'}
    (h : Pres st st') (hI : AnchorInv st) : AnchorInv st' := h.2 hI

theorem Pres.refl (st : BeaconState P f) : Pres st st :=
  ⟨⟨le_refl _, fun _ v v' h1 h2 => by rw [h1] at h2; cases h2; exact CredKeep.refl v⟩, id⟩

theorem Pres.trans {f1 f2 f3 : CFork} {s1 : BeaconState P f1} {s2 : BeaconState P f2}
    {s3 : BeaconState P f3} (h1 : Pres s1 s2) (h2 : Pres s2 s3) : Pres s1 s3 := by
  refine ⟨⟨le_trans h1.1.1 h2.1.1, ?_⟩, fun h => h2.2 (h1.2 h)⟩
  intro j u w hu hw
  obtain ⟨v, hv⟩ := getElem?_some_of_le h1.1.1 hu
  exact (h1.1.2 j u v hu hv).trans (h2.1.2 j v w hv hw)

/-! ## Introducing `Pres` -/

/-- The exit invariant of one validator. -/
def ExitOk (v : Validator) : Prop := v.exit_epoch = FAR_FUTURE_EPOCH → v.withdrawable_epoch = FAR_FUTURE_EPOCH

/-- Pointwise validator relation: each new validator either updates an old one (keeping credentials
and the exit invariant) or is new and satisfies the exit invariant. -/
def ValRel {f f' : CFork} (st : BeaconState P f) (st' : BeaconState P f') : Prop :=
  st.validators.toArray.size ≤ st'.validators.toArray.size ∧
  ∀ (j : Nat) (v' : Validator), st'.validators.toArray[j]? = some v' →
    (∃ v, st.validators.toArray[j]? = some v ∧ CredKeep v v' ∧ (ExitOk v → ExitOk v')) ∨
    (st.validators.toArray[j]? = none ∧ ExitOk v')

/-- The pending queue of `st'` is either a pending queue of `st` or names a compounding validator
of `st'`. -/
def PendingStep {f f' : CFork} (st : BeaconState P f) (st' : BeaconState P f') : Prop :=
  ∀ l, st'.pendingPartialWithdrawals = .ok l → ∀ p ∈ l.toArray.toList,
    (∃ l0, st.pendingPartialWithdrawals = .ok l0 ∧ p ∈ l0.toArray.toList) ∨
    (∃ v, st'.validators.toArray[p.validator_index.toNat]? = some v ∧
      hasCompoundingWithdrawalCredential v)

theorem pres_of_valRel {f f' : CFork} {st : BeaconState P f} {st' : BeaconState P f'}
    (hV : ValRel st st') (hP : PendingStep st st') : Pres st st' := by
  have hC : CredStep st st' := by
    refine ⟨hV.1, fun j v v' hv hv' => ?_⟩
    rcases hV.2 j v' hv' with ⟨w, hw, hk, _⟩ | ⟨hn, _⟩
    · rw [hv] at hw; cases hw; exact hk
    · rw [hv] at hn; cases hn
  refine ⟨hC, fun ⟨hPPC, hEIW⟩ => ⟨?_, ?_⟩⟩
  · intro l hl p hp
    rcases hP l hl p hp with ⟨l0, hl0, hp0⟩ | hnew
    · obtain ⟨v, hv, hc⟩ := hPPC l0 hl0 p hp0
      obtain ⟨v', hv'⟩ := getElem?_some_of_le hV.1 hv
      exact ⟨v', hv', (hC.2 _ v v' hv hv').1 hc⟩
    · exact hnew
  · intro v' hv' hfar
    rw [Array.mem_toList_iff] at hv'
    obtain ⟨j, hj, rfl⟩ := Array.getElem_of_mem hv'
    rcases hV.2 j _ (Array.getElem?_eq_getElem hj) with ⟨w, hw, _, hx⟩ | ⟨_, hx⟩
    · exact hx (hEIW w (Array.mem_toList_iff.mpr (Array.mem_of_getElem? hw))) hfar
    · exact hx hfar

theorem pendingStep_of_eq {f f' : CFork} {st : BeaconState P f} {st' : BeaconState P f'}
    (h : ∀ l, st'.pendingPartialWithdrawals = .ok l → st.pendingPartialWithdrawals = .ok l) :
    PendingStep st st' :=
  fun l hl p hp => .inl ⟨l, h l hl, hp⟩

theorem pendingStep_same {st st' : BeaconState P f}
    (h : st'.pending_partial_withdrawals = st.pending_partial_withdrawals) : PendingStep st st' :=
  pendingStep_of_eq fun l hl => by
    unfold BeaconState.pendingPartialWithdrawals at hl ⊢; rw [← h]; exact hl

theorem valRel_same {f f' : CFork} {st : BeaconState P f} {st' : BeaconState P f'}
    (h : st'.validators.toArray = st.validators.toArray) : ValRel st st' := by
  refine ⟨le_of_eq (by rw [h]), fun j v' hv' => .inl ⟨v', ?_, CredKeep.refl _, id⟩⟩
  rw [← h]; exact hv'

theorem valRel_set {st st' : BeaconState P f} {base : Array Validator} {i : Nat} {v v' : Validator}
    (hbase : base = st.validators.toArray) (hi : i < base.size)
    (h : st'.validators.toArray = base.set i v' hi)
    (hv : st.validators.toArray[i]? = some v) (hk : CredKeep v v') (hx : ExitOk v → ExitOk v') :
    ValRel st st' := by
  subst hbase
  refine ⟨le_of_eq (by rw [h, Array.size_set]), fun j w hw => .inl ?_⟩
  rw [h, Array.getElem?_set] at hw
  by_cases hj : i = j
  · subst hj
    simp only [hi, if_true] at hw
    cases hw
    exact ⟨v, hv, hk, hx⟩
  · simp only [hj, if_false] at hw
    exact ⟨w, hw, CredKeep.refl _, id⟩

theorem valRel_push {f f' : CFork} {st : BeaconState P f} {st' : BeaconState P f'} {v' : Validator}
    (h : st'.validators.toArray = st.validators.toArray.push v') (hx : ExitOk v') :
    ValRel st st' := by
  refine ⟨by rw [h, Array.size_push]; omega, fun j w hw => ?_⟩
  rw [h, Array.getElem?_push] at hw
  by_cases hj : j = st.validators.toArray.size
  · subst hj
    simp only [if_true] at hw
    cases hw
    exact .inr ⟨Array.getElem?_eq_none (le_refl _), hx⟩
  · simp only [hj, if_false] at hw
    exact .inl ⟨w, hw, CredKeep.refl _, id⟩

/-- A frame step: validators and the pending queue unchanged. -/
theorem pres_frame {st st' : BeaconState P f}
    (hV : st'.validators = st.validators)
    (hP : st'.pending_partial_withdrawals = st.pending_partial_withdrawals) : Pres st st' :=
  pres_of_valRel (valRel_same (by rw [hV])) (pendingStep_same hP)

/-- The frame relation used for loops and balance-only steps. -/
def Frame (st st' : BeaconState P f) : Prop :=
  st'.validators = st.validators ∧ st'.pending_partial_withdrawals = st.pending_partial_withdrawals

theorem Frame.refl (st : BeaconState P f) : Frame st st := ⟨rfl, rfl⟩
theorem Frame.trans {a b c : BeaconState P f} (h1 : Frame a b) (h2 : Frame b c) : Frame a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩
theorem Frame.pres {a b : BeaconState P f} (h : Frame a b) : Pres a b := pres_frame h.1 h.2

/-! ## Monadic plumbing: loops -/

/-- A `for` loop over a list preserves any reflexive-transitive relation its body step preserves. -/
theorem list_forIn_rel {α β : Type} (R : β → β → Prop) (hrefl : ∀ b, R b b)
    (htrans : ∀ a b c, R a b → R b c → R a c) (body : α → β → M (ForInStep β))
    (hb : ∀ a b r, body a b = .ok r → R b r.value) :
    ∀ (xs : List α) (init out : β), forIn xs init body = .ok out → R init out := by
  intro xs
  induction xs with
  | nil => intro init out h; cases h; exact hrefl _
  | cons a xs ih =>
    intro init out h
    rw [List.forIn_cons] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    have h1 := hb a init r hr
    cases r with
    | done b => cases h; exact h1
    | yield b => exact htrans _ _ _ h1 (ih b out h)

theorem array_forIn_rel {α β : Type} (R : β → β → Prop) (hrefl : ∀ b, R b b)
    (htrans : ∀ a b c, R a b → R b c → R a c) (body : α → β → M (ForInStep β))
    (hb : ∀ a b r, body a b = .ok r → R b r.value)
    (xs : Array α) (init out : β) (h : forIn xs init body = .ok out) : R init out := by
  rw [← Array.forIn_toList] at h
  exact list_forIn_rel R hrefl htrans body hb xs.toList init out h

/-! ## Collection lemmas -/

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

theorem push_ok {α : Type} {n : Nat} {xs ys : SszList α n} {v : α} {site : String}
    (h : xs.push v site = .ok ys) : ys.toArray = xs.toArray.push v := by
  unfold SszList.push at h
  split at h
  · cases h; rfl
  · cases h

theorem not_far_lt (w : U64) : ¬ FAR_FUTURE_EPOCH < w := by
  intro h
  have h1 : FAR_FUTURE_EPOCH.toNat < w.toNat := h
  have h2 := w.toNat_lt
  have h3 : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := rfl
  omega

/-- The withdrawable epoch written with an exit epoch by a checked add keeps the exit invariant. -/
theorem exitOk_add {v : Validator} {q d w : U64} {site : String} (hw : U64.add? q d site = .ok w) :
    ExitOk { v with exit_epoch := q, withdrawable_epoch := w } := by
  intro hq
  have hqF : q = FAR_FUTURE_EPOCH := hq
  rw [hqF] at hw
  exact (U64.max_add?_eq hw).2

/-! ## Balance-only mutators -/

theorem increaseBalance_frame {s s' : BeaconState P f} {i : ValidatorIndex} {d : Gwei}
    (h : increaseBalance s i d = .ok s') : Frame s s' := by
  unfold increaseBalance at h
  obtain ⟨b, _, h⟩ := bind_eq_ok_iff.mp h
  cases h; exact ⟨rfl, rfl⟩

theorem decreaseBalance_frame {s s' : BeaconState P f} {i : ValidatorIndex} {d : Gwei}
    (h : decreaseBalance s i d = .ok s') : Frame s s' := by
  unfold decreaseBalance at h
  obtain ⟨b, _, h⟩ := bind_eq_ok_iff.mp h
  cases h; exact ⟨rfl, rfl⟩

theorem exitChurn_frame (cfg : Config) {s : BeaconState P f} {b : Gwei} {p : BeaconState P f × Epoch}
    (h : computeExitEpochAndUpdateChurn cfg s b = .ok p) : Frame s p.1 := by
  obtain ⟨st1, q⟩ := p
  unfold computeExitEpochAndUpdateChurn at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (first | (cases h; exact ⟨rfl, rfl⟩) | cases h)

theorem consolidationChurn_frame (cfg : Config) {s : BeaconState P f} {b : Gwei}
    {p : BeaconState P f × Epoch}
    (h : computeConsolidationEpochAndUpdateChurn cfg s b = .ok p) : Frame s p.1 := by
  obtain ⟨st1, q⟩ := p
  unfold computeConsolidationEpochAndUpdateChurn at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (first | (cases h; exact ⟨rfl, rfl⟩) | cases h)

theorem consolidationChurn_frame' (cfg : Config) {s T : BeaconState P f} {b : Gwei} {q : Epoch}
    (h : computeConsolidationEpochAndUpdateChurn cfg s b = .ok (T, q)) : Frame s T :=
  consolidationChurn_frame cfg h

theorem queueExcess_frame {s s' : BeaconState P f} {i : ValidatorIndex}
    (h : queueExcessActiveBalance s i = .ok s') : Frame s s' := by
  unfold queueExcessActiveBalance at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals (first | (cases h; exact ⟨rfl, rfl⟩) | cases h)

/-! ## `initiate_validator_exit` -/

/-- The validator write of `initiate_validator_exit` from a frame state `T`. -/
theorem initiate_tail (cfg : Config) {s : BeaconState P f} {i : ValidatorIndex} {v : Validator}
    (hv : s.validators.get i.toNat "initiate_validator_exit" = .ok v)
    {T : BeaconState P f} {q : Epoch} (hT : Frame s T) {s' : BeaconState P f}
    (h : (do let d ← c64 cfg.MIN_VALIDATOR_WITHDRAWABILITY_DELAY
             let w ← U64.add? q d "initiate_validator_exit"
             let V ← T.validators.set i.toNat { v with exit_epoch := q, withdrawable_epoch := w }
               "initiate_validator_exit"
             pure { T with validators := V } : M (BeaconState P f)) = .ok s') :
    Pres s s' := by
  obtain ⟨d, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, hw, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨V, hV, h⟩ := bind_eq_ok_iff.mp h
  simp only [pure, Except.pure] at h
  cases h
  obtain ⟨hi, hVe⟩ := set_ok hV
  refine pres_of_valRel (valRel_set (v := v) (by rw [hT.1]) hi hVe (get_ok hv) (credKeep_of_wc rfl)
    (fun _ => exitOk_add hw)) (pendingStep_same hT.2)

theorem initiateValidatorExit_pres (cfg : Config) {s s' : BeaconState P f} {i : ValidatorIndex}
    (h : initiateValidatorExit cfg s i = .ok s') : Pres s s' := by
  unfold initiateValidatorExit at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  dsimp only at h
  split at h
  · simp only [pure, Except.pure] at h
    cases h
    exact Pres.refl s
  · split at h
    · obtain ⟨⟨st1, q⟩, hq, h⟩ := bind_eq_ok_iff.mp h
      exact initiate_tail cfg hv (exitChurn_frame cfg hq) h
    · obtain ⟨e0, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨a0, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨qq, _, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨lim, _, h⟩ := bind_eq_ok_iff.mp h
      split at h
      · obtain ⟨x, _, h⟩ := bind_eq_ok_iff.mp h
        obtain ⟨⟨st1, q'⟩, hq', h⟩ := bind_eq_ok_iff.mp h
        simp only [pure, Except.pure] at hq'
        cases hq'
        exact initiate_tail cfg hv (Frame.refl s) h
      · obtain ⟨⟨st1, q'⟩, hq', h⟩ := bind_eq_ok_iff.mp h
        simp only [pure, Except.pure] at hq'
        cases hq'
        exact initiate_tail cfg hv (Frame.refl s) h

/-! ## `slash_validator` -/

theorem slashValidator_pres (cfg : Config) {s s' : BeaconState P f} {i : ValidatorIndex}
    {wb : Option ValidatorIndex} (h : slashValidator cfg s i wb = .ok s') : Pres s s' := by
  unfold slashValidator at h
  obtain ⟨epoch, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨s1, h1, h⟩ := bind_eq_ok_iff.mp h
  have p1 := initiateValidatorExit_pres cfg h1
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨c, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨w, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨V, hV, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hi, hVe⟩ := set_ok hV
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨sl, _, h⟩ := bind_eq_ok_iff.mp h
  have p2 : Pres s1 { s1 with validators := V, slashings := sl } := by
    refine pres_of_valRel (valRel_set (v := v) rfl hi hVe (get_ok hv) (credKeep_of_wc rfl) ?_)
      (pendingStep_same rfl)
    intro hx hfar
    have hw' : v.withdrawable_epoch = FAR_FUTURE_EPOCH := hx hfar
    show (if v.withdrawable_epoch < w then w else v.withdrawable_epoch) = FAR_FUTURE_EPOCH
    rw [hw', if_neg (not_far_lt w)]
  refine p1.trans (p2.trans (Frame.pres ?_))
  dsimp only at h
  split at h
  all_goals
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨s3, h3, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨s4, h4, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    exact (decreaseBalance_frame h3).trans ((increaseBalance_frame h4).trans (increaseBalance_frame h))

/-! ## `switch_to_compounding_validator` -/

theorem require_ok {c : Bool} {site : String} {u : Unit} (h : require c site = .ok u) : c = true := by
  unfold require at h
  split at h
  · assumption
  · cases h

/-- The credential written by `switch_to_compounding_validator`. -/
theorem switch_bytes (wc : Bytes32) :
    (Jaune.Bytes.toB256 (COMPOUNDING_WITHDRAWAL_PREFIX :: wc.toBytes.drop 1)).toBytes =
      COMPOUNDING_WITHDRAWAL_PREFIX :: wc.toBytes.drop 1 := by
  apply b256_toBytes_toB256
  simp only [List.length_cons, List.length_drop, Jaune.B256.length_toBytes]

/-- The validator after `switch_to_compounding_validator`'s credential write. -/
def switchCred (v : Validator) : Validator :=
  { v with withdrawal_credentials :=
    Jaune.Bytes.toB256 (COMPOUNDING_WITHDRAWAL_PREFIX :: v.withdrawal_credentials.toBytes.drop 1) }

theorem switch_compounding (v : Validator) : hasCompoundingWithdrawalCredential (switchCred v) = true := by
  unfold hasCompoundingWithdrawalCredential isCompoundingWithdrawalCredential switchCred
  rw [switch_bytes, List.take_succ_cons, List.take_zero]
  exact beq_self_eq_true _

theorem switch_credKeep (v : Validator) : CredKeep v (switchCred v) := by
  refine ⟨fun _ => switch_compounding v, fun _ => ⟨?_, ?_⟩⟩
  · unfold hasExecutionWithdrawalCredential
    rw [switch_compounding, Bool.or_true]
  · show (Jaune.Bytes.toB256 (COMPOUNDING_WITHDRAWAL_PREFIX ::
      v.withdrawal_credentials.toBytes.drop 1)).toBytes.drop 12 = _
    rw [switch_bytes, List.drop_succ_cons, List.drop_drop]

theorem switchToCompoundingValidator_pres {s s' : BeaconState P f} {i : ValidatorIndex}
    (h : switchToCompoundingValidator s i = .ok s') : Pres s s' := by
  unfold switchToCompoundingValidator at h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨V, hV, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨hi, hVe⟩ := set_ok hV
  refine (pres_of_valRel (st := s) (st' := { s with validators := V })
    (valRel_set (v := v) (v' := switchCred v) rfl hi hVe (get_ok hv) (switch_credKeep v) id)
    (pendingStep_same rfl)).trans (Frame.pres (queueExcess_frame h))

/-! ## `process_bls_to_execution_change` -/

/-- A BLS credential (prefix `0x00`) is neither compounding nor execution, so any successor keeps
`CredKeep` vacuously. -/
theorem credKeep_of_bls {v : Validator} (v' : Validator)
    (hb : v.withdrawal_credentials.toBytes.take 1 = [BLS_WITHDRAWAL_PREFIX]) : CredKeep v v' := by
  have hc : hasCompoundingWithdrawalCredential v = false := by
    unfold hasCompoundingWithdrawalCredential isCompoundingWithdrawalCredential
    rw [hb]; decide
  have he : hasEth1WithdrawalCredential v = false := by
    unfold hasEth1WithdrawalCredential credentialPrefix
    generalize v.withdrawal_credentials.toBytes = bs at hb ⊢
    match bs, hb with
    | b :: _, hb =>
      simp only [List.take_succ_cons, List.take_zero, List.cons.injEq, and_true] at hb
      subst hb; rfl
  refine ⟨fun h => (by rw [hc] at h; cases h), fun h => ?_⟩
  unfold hasExecutionWithdrawalCredential at h
  rw [hc, he] at h
  cases h

theorem processBlsToExecutionChange_pres (ctx : Ctx) {s s' : BeaconState P f}
    {sac : SignedBLSToExecutionChange} (h : processBlsToExecutionChange ctx s sac = .ok s') :
    Pres s s' := by
  unfold processBlsToExecutionChange at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨v, hv, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, hb, h⟩ := bind_eq_ok_iff.mp h
  have hb := require_ok hb
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨V, hV, h⟩ := bind_eq_ok_iff.mp h
  cases h
  obtain ⟨hi, hVe⟩ := set_ok hV
  exact pres_of_valRel (valRel_set (v := v) rfl hi hVe (get_ok hv)
    (credKeep_of_bls _ (beq_iff_eq.mp hb)) id) (pendingStep_same rfl)

/-! ## A small verification-condition generator for `do` blocks over `Except` -/

/-- Every successful result of `c` satisfies `Q`. -/
def Ok {α : Type} (c : M α) (Q : α → Prop) : Prop := ∀ a, c = .ok a → Q a

theorem ok_bind {α β : Type} {x : M α} {g : α → M β} {Q : β → Prop}
    (h : ∀ a, x = .ok a → Ok (g a) Q) : Ok (x >>= g) Q := by
  intro b hb
  obtain ⟨a, ha, hg⟩ := bind_eq_ok_iff.mp hb
  exact h a ha b hg

theorem ok_ite {α : Type} {c : Prop} [Decidable c] {t e : M α} {Q : α → Prop}
    (ht : c → Ok t Q) (he : ¬c → Ok e Q) : Ok (if c then t else e) Q := by
  by_cases hc : c
  · rw [if_pos hc]; exact ht hc
  · rw [if_neg hc]; exact he hc

theorem ok_pure {α : Type} {a : α} {Q : α → Prop} (h : Q a) : Ok (pure a : M α) Q := by
  intro b hb; cases hb; exact h

theorem ok_throw {α : Type} {e : Reject} {Q : α → Prop} : Ok (throw e : M α) Q := by
  intro b hb; cases hb

theorem ok_throw_bind {α β : Type} {e : Reject} {g : α → M β} {Q : β → Prop} :
    Ok ((throw e : M α) >>= g) Q := by
  intro b hb; cases hb

theorem ok_of {α : Type} {c : M α} {Q : α → Prop} (h : ∀ a, c = .ok a → Q a) : Ok c Q := h

macro "vcg_step" : tactic => `(tactic| first
  | with_reducible exact ok_throw
  | with_reducible exact ok_throw_bind
  | with_reducible exact ok_pure (Pres.refl _)
  | (with_reducible apply ok_bind; intro _ _)
  | (with_reducible apply ok_ite <;> intro _)
  | dsimp only
  | (rename_i x _; cases x; all_goals dsimp only))

/-! ## `process_withdrawal_request` -/

theorem gated_write_read {α : Type} {c : Bool} {x : α} {g : Gated c α} {site site' : String}
    (h : Gated.write c x site = .ok g) : Gated.read g site' = .ok x := by
  cases c with
  | false => cases h
  | true => cases h; rfl

theorem setPending_ok {s s' : BeaconState P f}
    {l : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    (h : s.setPendingPartialWithdrawals l = .ok s') :
    s'.validators = s.validators ∧ s'.pendingPartialWithdrawals = .ok l := by
  unfold BeaconState.setPendingPartialWithdrawals at h
  obtain ⟨g, hg, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact ⟨rfl, gated_write_read hg⟩

/-- The partial path of `process_withdrawal_request`: one pending entry for a compounding validator. -/
theorem partial_pres {s s' T : BeaconState P f}
    {l l' : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    {e : PendingPartialWithdrawal} {v : Validator} {site site2 : String} {b1 b2 : Bool}
    (h : T.setPendingPartialWithdrawals l' = .ok s')
    (hpush : l.push e site = .ok l')
    (hl : T.pendingPartialWithdrawals = .ok l)
    (hT : Frame s T)
    (hv : s.validators.get e.validator_index.toNat site2 = .ok v)
    (hc : (hasCompoundingWithdrawalCredential v && b1 && b2) = true) : Pres s s' := by
  obtain ⟨hV', hl'⟩ := setPending_ok h
  have hc' : hasCompoundingWithdrawalCredential v = true := by
    simp only [Bool.and_eq_true] at hc; exact hc.1.1
  have hVs : s'.validators = s.validators := hV'.trans hT.1
  refine pres_of_valRel (valRel_same (by rw [hVs])) ?_
  intro m hm p hp
  rw [hl'] at hm
  cases hm
  rw [push_ok hpush, Array.toList_push, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · left
    refine ⟨l, ?_, hp⟩
    unfold BeaconState.pendingPartialWithdrawals at hl ⊢
    rw [← hT.2]; exact hl
  · right
    exact ⟨v, by rw [hVs]; exact get_ok hv, hc'⟩

theorem processWithdrawalRequest_pres (cfg : Config) {s s' : BeaconState P f} {wr : WithdrawalRequest}
    (h : processWithdrawalRequest cfg s wr = .ok s') : Pres s s' := by
  unfold processWithdrawalRequest at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | (cases h; exact Pres.refl _)
    | cases h
    | exact initiateValidatorExit_pres cfg h
    | exact partial_pres h (by assumption) (by assumption) (exitChurn_frame cfg (by assumption))
        (by assumption) (by assumption)

/-! ## `process_consolidation_request` -/

theorem setPendingConsolidations_frame {s s' : BeaconState P f}
    {l : SszList PendingConsolidation P.PENDING_CONSOLIDATIONS_LIMIT}
    (h : s.setPendingConsolidations l = .ok s') : Frame s s' := by
  unfold BeaconState.setPendingConsolidations at h
  obtain ⟨g, _, h⟩ := bind_eq_ok_iff.mp h
  cases h; exact ⟨rfl, rfl⟩

/-- The main path of `process_consolidation_request`: the source's exit and withdrawable epochs. -/
theorem consol_leaf {s T S s' : BeaconState P f} {V : SszList Validator P.VALIDATOR_REGISTRY_LIMIT}
    {pc : SszList PendingConsolidation P.PENDING_CONSOLIDATIONS_LIMIT} {i : Nat} {src : Validator}
    {q d w : U64} {site site2 site3 : String}
    (h : S.setPendingConsolidations pc = .ok s')
    (hS : S = { T with validators := V })
    (hV : T.validators.set i { src with exit_epoch := q, withdrawable_epoch := w } site = .ok V)
    (hw : U64.add? q d site2 = .ok w)
    (hsrc : T.validators.get i site3 = .ok src)
    (hT : Frame s T) : Pres s s' := by
  subst hS
  obtain ⟨hi, hVe⟩ := set_ok hV
  refine (pres_of_valRel (valRel_set (st := s) (st' := { T with validators := V }) (v := src)
    (v' := { src with exit_epoch := q, withdrawable_epoch := w }) (by rw [hT.1]) hi hVe
    (by rw [← hT.1]; exact get_ok hsrc) (credKeep_of_wc rfl) (fun _ => exitOk_add hw))
    (pendingStep_same hT.2)).trans (setPendingConsolidations_frame h).pres

theorem processConsolidationRequest_pres (cfg : Config) {s s' : BeaconState P f}
    {cr : ConsolidationRequest} (h : processConsolidationRequest cfg s cr = .ok s') : Pres s s' := by
  revert s' h
  show Ok (processConsolidationRequest cfg s cr) (Pres s)
  unfold processConsolidationRequest
  repeat (first
    | vcg_step
    | exact ok_of fun _ h => switchToCompoundingValidator_pres h
    | exact ok_of fun _ h => consol_leaf h rfl (by assumption) (by assumption) (by assumption)
        (consolidationChurn_frame cfg (by assumption)))

end JauneConsensus.Facts
