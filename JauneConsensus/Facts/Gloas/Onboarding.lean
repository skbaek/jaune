import JauneConsensus.GloasUpgrade
import JauneConsensus.Facts.Gloas.BuilderFrames

/-!
# Builder onboarding at the Fulu → Gloas fork (goal `eip8282-gloas-cross-layer-v1`, B1 fork step, B7)

Frozen statements (Plans `recon/statements.md`, B1 `OnboardingSpec` / `upgradeToGloas_onboards`,
B7 `builder_total_crossing`), with `design.md` §4 as the transcription of
`gloas-fork.md:70-120`.

`OnboardingSpec` characterises `onboard_builders_from_pending_deposits` **declaratively**: the
pending deposits `Q` are partitioned by position (`Fin Q.length`, so every `Q[t]` is in range and
"a permutation of `[0, Q.length)`" is `List.finRange`) into kept `K` (steps 1-3), registered `R`
(step 5), topped-up `T` (step 6) and dropped `X` (step 4), each class by its step's condition read
against the classes *before* the position (`regBefore` is the spec's recomputed `builder_pubkeys`,
`keptBefore` the kept-so-far queue `Q'` that `is_pending_validator` reads). That makes the
order dependence of design R8 explicit (`OnboardingSpec.later_same_pubkey_topUp`): a deposit
after a registration for the same pubkey is a top-up whatever its credentials and signature.

* `OnboardingSpec.unique`: at most one partition meets the specification;
* `upgradeToGloas_onboards`: U5's `upgradeToGloas` meets it, keeps validators and balances, and
  its builder total is the sum of the `R` and `T` amounts (`OnboardingSpec.total`,
  `upgradeToGloas_builder_total`: B7's fork term).

No preset premise is needed: a fork at epoch `FAR_FUTURE_EPOCH` (the only epoch at which
`get_index_for_new_builder` could reuse a fresh builder's slot) cannot succeed, because
`initialize_ptc_window` then calls `get_seed` at that epoch, which always rejects
(`initializePtcWindow_epoch`).
-/

namespace JauneConsensus.Facts.Gloas.Onboarding

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

local instance : LawfulBEq BLSPubkey where
  eq_of_beq h := pubkey_beq_iff.mp h
  rfl := pubkey_beq_iff.mpr rfl

/-- The Gloas beacon state. -/
abbrev GSt (P : Preset) := JauneConsensus.Gloas.BeaconState P

theorem far_toNat : FAR_FUTURE_EPOCH.toNat = 2 ^ 64 - 1 := by decide

/-- `get_seed` at `FAR_FUTURE_EPOCH` always rejects: the sum overflows unless
`EPOCHS_PER_HISTORICAL_VECTOR = 0`, and then `get_randao_mix` divides by zero. -/
theorem getSeed_far (s : GSt P) (d : DomainType) (x : Bytes32) :
    JauneConsensus.Gloas.getSeed s FAR_FUTURE_EPOCH d ≠ .ok x := by
  intro h
  unfold JauneConsensus.Gloas.getSeed at h
  obtain ⟨k, hk, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e1, he1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨k2, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e2, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨e3, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨mix, hmix, _⟩ := bind_eq_ok_iff.mp h
  have hk' := U64.toNat_ofNat? hk
  have he1' := U64.toNat_add? he1
  have := U64.toNat_lt e1
  rw [far_toNat] at he1'
  have h0 : P.EPOCHS_PER_HISTORICAL_VECTOR = 0 := by omega
  unfold JauneConsensus.Gloas.getRandaoMix at hmix
  obtain ⟨k3, hk3, hmix⟩ := bind_eq_ok_iff.mp hmix
  obtain ⟨m, hm, _⟩ := bind_eq_ok_iff.mp hmix
  have hk3' := U64.toNat_ofNat? hk3
  unfold U64.mod? at hm
  split at hm
  · cases hm
  · omega

theorem computePtc_far (s : GSt P) (slot : Slot) (hspe : P.SLOTS_PER_EPOCH = 1)
    (hs : slot.toNat = 2 ^ 64 - 1) (w : JauneConsensus.Gloas.PayloadTimelinessCommittee P) :
    JauneConsensus.Gloas.computePtc s slot ≠ .ok w := by
  intro h
  unfold JauneConsensus.Gloas.computePtc at h
  obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
  have hxf : x = FAR_FUTURE_EPOCH := by
    unfold computeEpochAtSlot at hx
    obtain ⟨k, hk, hx⟩ := bind_eq_ok_iff.mp hx
    have hk' := U64.toNat_ofNat? hk
    have hx' := U64.toNat_div? hx
    apply U64.ext_toNat
    rw [hx', hk', hspe, Nat.div_one, hs, far_toNat]
  subst hxf
  obtain ⟨sd, hsd, _⟩ := bind_eq_ok_iff.mp h
  exact getSeed_far _ _ _ hsd

theorem initializePtcWindow_epoch {s : GSt P} {w} (h : JauneConsensus.Gloas.initializePtcWindow s = .ok w)
    {e : Epoch} (he : JauneConsensus.Gloas.getCurrentEpoch s = .ok e) : e ≠ FAR_FUTURE_EPOCH := by
  intro hf
  subst hf
  unfold JauneConsensus.Gloas.initializePtcWindow at h
  rw [he] at h
  simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at h
  have hspe : P.SLOTS_PER_EPOCH ≠ 0 := by
    unfold JauneConsensus.Gloas.getCurrentEpoch computeEpochAtSlot at he
    obtain ⟨k, hk, he⟩ := bind_eq_ok_iff.mp he
    have := U64.toNat_ofNat? hk
    unfold U64.div? at he
    split at he
    · cases he
    · omega
  obtain ⟨x, hx, h⟩ := bind_eq_ok_iff.mp h
  cases hx
  obtain ⟨arr, harr, _⟩ := bind_eq_ok_iff.mp h
  have hsz : [:1 + P.MIN_SEED_LOOKAHEAD].size = P.MIN_SEED_LOOKAHEAD + 1 := by
    simp [Std.Legacy.Range.size]; omega
  rw [hsz, List.range'_succ, List.forIn_cons] at harr
  obtain ⟨st, hst, _⟩ := bind_eq_ok_iff.mp harr
  obtain ⟨z, hz, hst⟩ := bind_eq_ok_iff.mp hst
  obtain ⟨ep, hep, hst⟩ := bind_eq_ok_iff.mp hst
  obtain ⟨ss, hss, hst⟩ := bind_eq_ok_iff.mp hst
  obtain ⟨inner, hinner, _⟩ := bind_eq_ok_iff.mp hst
  have hz' := U64.toNat_ofNat? hz
  have hep' := U64.toNat_add? hep
  rw [far_toNat] at hep'
  unfold computeStartSlotAtEpoch at hss
  obtain ⟨k, hk, hss⟩ := bind_eq_ok_iff.mp hss
  have hk' := U64.toNat_ofNat? hk
  have hss' := U64.toNat_mul? hss
  have := U64.toNat_lt ss
  have h1 : P.SLOTS_PER_EPOCH = 1 := by
    rcases Nat.lt_or_ge P.SLOTS_PER_EPOCH 2 with h | h
    · omega
    · have : ep.toNat * k.toNat ≥ ep.toNat * 2 := Nat.mul_le_mul_left _ (by omega)
      omega
  have hsz2 : [:P.SLOTS_PER_EPOCH].size = 0 + 1 := by simp [Std.Legacy.Range.size, h1]
  rw [hsz2, List.range'_succ, List.forIn_cons] at hinner
  obtain ⟨st2, hst2, _⟩ := bind_eq_ok_iff.mp hinner
  obtain ⟨z2, hz2, hst2⟩ := bind_eq_ok_iff.mp hst2
  obtain ⟨sl, hsl, hst2⟩ := bind_eq_ok_iff.mp hst2
  obtain ⟨c, hc, _⟩ := bind_eq_ok_iff.mp hst2
  have := U64.toNat_ofNat? hz2
  have := U64.toNat_add? hsl
  rw [hk', h1, Nat.mul_one] at hss'
  exact computePtc_far s sl h1 (by omega) c hc

theorem forIn_yield_all {α β : Type} (l : List α)
    (f : α → Option β × Nat → M (ForInStep (Option β × Nat)))
    (hf : ∀ b ∈ l, ∀ i, f b (none, i) = pure (.yield (none, i + 1))) (i : Nat) :
    forIn l (none, i) f = pure (none, i + l.length) := by
  induction l generalizing i with
  | nil => rfl
  | cons b l ih =>
    rw [List.forIn_cons, hf b (by simp) i]
    simp only [pure, Except.pure, bind, Except.bind]
    rw [ih (fun b hb => hf b (by simp [hb]))]
    simp only [List.length_cons, pure, Except.pure]
    congr 2
    omega

/-- With every builder at `withdrawable_epoch = FAR_FUTURE_EPOCH` and the current epoch below it,
`get_index_for_new_builder` reuses no slot: the new builder is appended. -/
theorem getIndexForNewBuilder_append {s : GSt P} {idx : U64}
    (h : JauneConsensus.Gloas.getIndexForNewBuilder s = .ok idx)
    (hfar : ∀ b ∈ s.builders.toArray, b.withdrawable_epoch = FAR_FUTURE_EPOCH)
    (he : ∀ e, JauneConsensus.Gloas.getCurrentEpoch s = .ok e → e ≠ FAR_FUTURE_EPOCH) :
    idx.toNat = s.builders.toArray.size := by
  unfold JauneConsensus.Gloas.getIndexForNewBuilder at h
  obtain ⟨e, he1, h⟩ := bind_eq_ok_iff.mp h
  have hne := he e he1
  simp only [← Array.forIn_toList] at h
  rw [forIn_yield_all] at h
  · exact (U64.toNat_ofNat? h).trans rfl
  · intro b hb i
    have hb' := hfar b (Array.mem_toList_iff.mp hb)
    have hlt : ¬ b.withdrawable_epoch ≤ e := by
      intro hle
      apply hne
      apply U64.ext_toNat
      have := U64.toNat_lt e
      change b.withdrawable_epoch.toNat ≤ e.toNat at hle
      rw [hb', far_toNat] at hle
      rw [far_toNat]; omega
    simp [hlt]

/-- The five outcomes of one onboarding iteration (fork.md:80-117), read off the implementation. -/
theorem onboardBuilderDeposit_cases {ctx : Ctx} {V : Array BLSPubkey} {st st' : GSt P}
    {acc acc' : Array PendingDeposit} {d : PendingDeposit}
    (h : JauneConsensus.Gloas.onboardBuilderDeposit ctx V (st, acc) d = .ok (st', acc')) :
    (V.contains d.pubkey = true ∧ st' = st ∧ acc' = acc.push d) ∨
    (V.contains d.pubkey = false ∧ (st.builders.toArray.map (·.pubkey)).idxOf? d.pubkey = none ∧
      (JauneConsensus.Gloas.isBuilderWithdrawalCredential d.withdrawal_credentials = false ∨
        JauneConsensus.Gloas.isPendingValidator ctx acc d.pubkey = .ok true) ∧
      st' = st ∧ acc' = acc.push d) ∨
    (V.contains d.pubkey = false ∧ (st.builders.toArray.map (·.pubkey)).idxOf? d.pubkey = none ∧
      JauneConsensus.Gloas.isBuilderWithdrawalCredential d.withdrawal_credentials = true ∧
      JauneConsensus.Gloas.isPendingValidator ctx acc d.pubkey = .ok false ∧
      isValidDepositSignature ctx d.pubkey d.withdrawal_credentials d.amount d.signature = .ok false ∧
      st' = st ∧ acc' = acc) ∨
    (V.contains d.pubkey = false ∧ (st.builders.toArray.map (·.pubkey)).idxOf? d.pubkey = none ∧
      JauneConsensus.Gloas.isBuilderWithdrawalCredential d.withdrawal_credentials = true ∧
      JauneConsensus.Gloas.isPendingValidator ctx acc d.pubkey = .ok false ∧
      isValidDepositSignature ctx d.pubkey d.withdrawal_credentials d.amount d.signature = .ok true ∧
      ∃ addr, Jaune.Bytes.toAdr? (d.withdrawal_credentials.toBytes.drop 12) = some addr ∧
        JauneConsensus.Gloas.addBuilderToRegistry st d.pubkey
          JauneConsensus.Gloas.PAYLOAD_BUILDER_VERSION addr d.amount d.slot = .ok st' ∧ acc' = acc) ∨
    (V.contains d.pubkey = false ∧ ∃ i b nb bs,
      (st.builders.toArray.map (·.pubkey)).idxOf? d.pubkey = some i ∧
      st.builders.toArray[i]? = some b ∧ b.balance.add? d.amount "onboard_builders_from_pending_deposits" = .ok nb ∧
      st.builders.set i { b with balance := nb } "onboard_builders_from_pending_deposits" = .ok bs ∧
      st' = { st with builders := bs } ∧ acc' = acc) := by
  unfold JauneConsensus.Gloas.onboardBuilderDeposit at h
  simp only at h
  cases hv : V.contains d.pubkey
  · simp only [hv, Bool.false_eq_true, ↓reduceIte] at h
    right
    cases hi : (Array.map (fun x => x.pubkey) st.builders.toArray).idxOf? d.pubkey with
    | none =>
      rw [hi] at h
      simp only at h
      cases hw : JauneConsensus.Gloas.isBuilderWithdrawalCredential d.withdrawal_credentials
      · simp only [hw, Bool.not_false, ↓reduceIte] at h; cases h
        exact Or.inl ⟨rfl, rfl, Or.inl rfl, rfl, rfl⟩
      simp only [hw, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
      obtain ⟨ipv, hipv, h⟩ := bind_eq_ok_iff.mp h
      cases ipv
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        obtain ⟨sig, hsig, h⟩ := bind_eq_ok_iff.mp h
        cases sig
        · simp only [Bool.not_false, ↓reduceIte] at h; cases h
          exact Or.inr (Or.inl ⟨rfl, rfl, rfl, hipv, hsig, rfl, rfl⟩)
        · simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
          obtain ⟨addr, ha, h⟩ := bind_eq_ok_iff.mp h
          obtain ⟨st2, hst2, h⟩ := bind_eq_ok_iff.mp h
          cases h
          exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl, hipv, hsig, addr,
            addressOfCredentials_ok.mp ha, hst2, rfl⟩))
      · simp only [↓reduceIte] at h; cases h
        exact Or.inl ⟨rfl, rfl, Or.inr hipv, rfl, rfl⟩
    | some i =>
      rw [hi] at h
      simp only at h
      obtain ⟨b, hb, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨nb, hnb, h⟩ := bind_eq_ok_iff.mp h
      obtain ⟨bs, hbs, h⟩ := bind_eq_ok_iff.mp h
      cases h
      exact Or.inr (Or.inr (Or.inr ⟨rfl, i, b, nb, bs, rfl, pl_get_ok.mp hb, hnb, hbs, rfl, rfl⟩))
  · simp only [hv, ↓reduceIte] at h; cases h; exact Or.inl ⟨rfl, rfl, rfl⟩

theorem arr_idxOf?_some {a : Array BLSPubkey} {x : BLSPubkey} {i : Nat} (h : a.idxOf? x = some i) :
    ∃ hi : i < a.size, a[i] = x := by
  rw [Array.idxOf?_eq_map_finIdxOf?_val] at h
  obtain ⟨j, hj, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨j.2, (Array.finIdxOf?_eq_some_iff.mp hj).1⟩

theorem sorted_eq {m : Nat} {l1 l2 : List (Fin m)} (h1 : l1.Pairwise (· < ·))
    (h2 : l2.Pairwise (· < ·)) (h : ∀ x, x ∈ l1 ↔ x ∈ l2) : l1 = l2 :=
  List.Subset.antisymm_of_pairwise h1 h2 (fun x hx => (h x).mp hx) (fun x hx => (h x).mpr hx)

/-! ## The declarative onboarding specification (B1 fork step, design.md §4)

Queue positions are `Fin Q.length`, so every `Q[t]` is in range. -/

/-- `Bpk_t`: the pubkeys of the deposits registered (`R`) before queue position `t`. -/
def regBefore (Q : List PendingDeposit) (R : List (Fin Q.length)) (t : Nat) : List BLSPubkey :=
  (R.filter (·.val < t)).map (fun r => Q[r].pubkey)

/-- `Qk_t`: the deposits kept (`K`) before queue position `t`, in queue order (the spec's `Q'`
when deposit `t` is read). -/
def keptBefore (Q : List PendingDeposit) (K : List (Fin Q.length)) (t : Nat) :
    List PendingDeposit :=
  (K.filter (·.val < t)).map (fun s => Q[s])

/-- The step-6 top-ups credited to the builder registered at `r`: the deposits of `T` after `r`
with `r`'s pubkey. -/
def topUpTotal (Q : List PendingDeposit) (T : List (Fin Q.length)) (r : Fin Q.length) : Nat :=
  ((T.filter (fun t => decide (r < t) && Q[t].pubkey == Q[r].pubkey)).map
    (fun t => Q[t].amount.toNat)).sum

/-- Steps 1-3 (FK:80-98): kept as a pending validator deposit. -/
def KeepAt (ctx : Ctx) (V : List BLSPubkey) (Q : List PendingDeposit) (K R : List (Fin Q.length))
    (t : Fin Q.length) : Prop :=
  Q[t].pubkey ∈ V ∨
    (Q[t].pubkey ∉ regBefore Q R t ∧
      (JauneConsensus.Gloas.isBuilderWithdrawalCredential Q[t].withdrawal_credentials = false ∨
        JauneConsensus.Gloas.isPendingValidator ctx (keptBefore Q K t).toArray Q[t].pubkey = .ok true))

/-- Step 5 (FK:99-114): registered as a new builder: `0xB0` credentials, a pubkey neither a
validator's nor a builder's, no pending validator deposit for it in `Q'`, and a valid
`DOMAIN_DEPOSIT` signature. -/
def RegisterAt (ctx : Ctx) (V : List BLSPubkey) (Q : List PendingDeposit)
    (K R : List (Fin Q.length)) (t : Fin Q.length) : Prop :=
  Q[t].pubkey ∉ V ∧ Q[t].pubkey ∉ regBefore Q R t ∧
    JauneConsensus.Gloas.isBuilderWithdrawalCredential Q[t].withdrawal_credentials = true ∧
    JauneConsensus.Gloas.isPendingValidator ctx (keptBefore Q K t).toArray Q[t].pubkey = .ok false ∧
    isValidDepositSignature ctx Q[t].pubkey Q[t].withdrawal_credentials Q[t].amount
      Q[t].signature = .ok true

/-- Step 4 (FK:99-105): dropped (stake forfeited, not re-queued): as step 5 but with an invalid
signature. -/
def DropAt (ctx : Ctx) (V : List BLSPubkey) (Q : List PendingDeposit) (K R : List (Fin Q.length))
    (t : Fin Q.length) : Prop :=
  Q[t].pubkey ∉ V ∧ Q[t].pubkey ∉ regBefore Q R t ∧
    JauneConsensus.Gloas.isBuilderWithdrawalCredential Q[t].withdrawal_credentials = true ∧
    JauneConsensus.Gloas.isPendingValidator ctx (keptBefore Q K t).toArray Q[t].pubkey = .ok false ∧
    isValidDepositSignature ctx Q[t].pubkey Q[t].withdrawal_credentials Q[t].amount
      Q[t].signature = .ok false

/-- Step 6 (FK:115-117): a top-up of a builder registered earlier in the loop; credentials and
signature are not checked. -/
def TopUpAt (V : List BLSPubkey) (Q : List PendingDeposit) (R : List (Fin Q.length))
    (t : Fin Q.length) : Prop :=
  Q[t].pubkey ∉ V ∧ Q[t].pubkey ∈ regBefore Q R t

/-- The builder record onboarded for the deposit at `r ∈ R` (`add_builder_to_registry`,
CL:2300-2320), with the step-6 top-ups of `T` credited. -/
structure OnboardedRecord (P : Preset) (Q : List PendingDeposit) (T : List (Fin Q.length))
    (r : Fin Q.length) (b : JauneConsensus.Gloas.Builder) : Prop where
  pubkey : b.pubkey = Q[r].pubkey
  version : b.version = JauneConsensus.Gloas.PAYLOAD_BUILDER_VERSION
  execution_address :
    Jaune.Bytes.toAdr? (Q[r].withdrawal_credentials.toBytes.drop 12) = some b.execution_address
  deposit_epoch : computeEpochAtSlot P Q[r].slot = .ok b.deposit_epoch
  withdrawable_epoch : b.withdrawable_epoch = FAR_FUTURE_EPOCH
  balance : b.balance.toNat = Q[r].amount.toNat + topUpTotal Q T r

/-- **B1 fork step, declaratively.** The partition of the pre-state's pending deposits `Q` into
kept `K`, registered `R`, topped-up `T` and dropped `X` (`gloas-fork.md:70-120`), with `V` the
validator pubkeys, `builders` the resulting registry and `Qkept` the resulting queue. -/
structure OnboardingSpec (P : Preset) (ctx : Ctx) (V : List BLSPubkey) (Q : List PendingDeposit)
    (K R T X : List (Fin Q.length)) (builders : List JauneConsensus.Gloas.Builder)
    (Qkept : List PendingDeposit) : Prop where
  partition : (K ++ R ++ T ++ X).Perm (List.finRange Q.length)
  increasing : K.Pairwise (· < ·) ∧ R.Pairwise (· < ·) ∧ T.Pairwise (· < ·) ∧ X.Pairwise (· < ·)
  keep : ∀ t ∈ K, KeepAt ctx V Q K R t
  register : ∀ t ∈ R, RegisterAt ctx V Q K R t
  dropped : ∀ t ∈ X, DropAt ctx V Q K R t
  topUp : ∀ t ∈ T, TopUpAt V Q R t
  kept : Qkept = K.map (fun t => Q[t])
  records : List.Forall₂ (OnboardedRecord P Q T) R builders

/-! ## The partition is unique -/

section Unique

variable {ctx : Ctx} {V : List BLSPubkey} {Q : List PendingDeposit} {K R : List (Fin Q.length)}
  {t : Fin Q.length}

theorem keep_register_excl (h1 : KeepAt ctx V Q K R t) (h2 : RegisterAt ctx V Q K R t) : False := by
  obtain ⟨hv, hb, hw, hp, _⟩ := h2
  rcases h1 with h | ⟨_, h | h⟩
  · exact hv h
  · rw [hw] at h; cases h
  · rw [hp] at h; cases h

theorem keep_drop_excl (h1 : KeepAt ctx V Q K R t) (h2 : DropAt ctx V Q K R t) : False := by
  obtain ⟨hv, hb, hw, hp, _⟩ := h2
  rcases h1 with h | ⟨_, h | h⟩
  · exact hv h
  · rw [hw] at h; cases h
  · rw [hp] at h; cases h

theorem keep_topUp_excl (h1 : KeepAt ctx V Q K R t) (h2 : TopUpAt V Q R t) : False := by
  obtain ⟨hv, hb⟩ := h2
  rcases h1 with h | ⟨h, _⟩
  · exact hv h
  · exact h hb

theorem register_drop_excl (h1 : RegisterAt ctx V Q K R t) (h2 : DropAt ctx V Q K R t) : False := by
  have := h1.2.2.2.2.symm.trans h2.2.2.2.2
  cases this

theorem register_topUp_excl (h1 : RegisterAt ctx V Q K R t) (h2 : TopUpAt V Q R t) : False :=
  h1.2.1 h2.2

theorem drop_topUp_excl (h1 : DropAt ctx V Q K R t) (h2 : TopUpAt V Q R t) : False :=
  h1.2.1 h2.2

end Unique

theorem OnboardingSpec.mem_some {P : Preset} {ctx : Ctx} {V : List BLSPubkey}
    {Q : List PendingDeposit} {K R T X : List (Fin Q.length)}
    {bs : List JauneConsensus.Gloas.Builder} {q : List PendingDeposit}
    (S : OnboardingSpec P ctx V Q K R T X bs q) (t : Fin Q.length) :
    t ∈ K ∨ t ∈ R ∨ t ∈ T ∨ t ∈ X := by
  have := (S.partition.mem_iff (a := t)).mpr (List.mem_finRange t)
  simp only [List.mem_append] at this
  tauto

/-- Membership in each class is its step's condition. -/
theorem OnboardingSpec.mem_iff {P : Preset} {ctx : Ctx} {V : List BLSPubkey}
    {Q : List PendingDeposit} {K R T X : List (Fin Q.length)}
    {bs : List JauneConsensus.Gloas.Builder} {q : List PendingDeposit}
    (S : OnboardingSpec P ctx V Q K R T X bs q) (t : Fin Q.length) :
    (t ∈ K ↔ KeepAt ctx V Q K R t) ∧ (t ∈ R ↔ RegisterAt ctx V Q K R t) ∧
      (t ∈ T ↔ TopUpAt V Q R t) ∧ (t ∈ X ↔ DropAt ctx V Q K R t) := by
  have hm := S.mem_some t
  refine ⟨⟨S.keep t, fun hc => ?_⟩, ⟨S.register t, fun hc => ?_⟩, ⟨S.topUp t, fun hc => ?_⟩,
    ⟨S.dropped t, fun hc => ?_⟩⟩
  · rcases hm with h | h | h | h
    · exact h
    · exact (keep_register_excl hc (S.register t h)).elim
    · exact (keep_topUp_excl hc (S.topUp t h)).elim
    · exact (keep_drop_excl hc (S.dropped t h)).elim
  · rcases hm with h | h | h | h
    · exact (keep_register_excl (S.keep t h) hc).elim
    · exact h
    · exact (register_topUp_excl hc (S.topUp t h)).elim
    · exact (register_drop_excl hc (S.dropped t h)).elim
  · rcases hm with h | h | h | h
    · exact (keep_topUp_excl (S.keep t h) hc).elim
    · exact (register_topUp_excl (S.register t h) hc).elim
    · exact h
    · exact (drop_topUp_excl (S.dropped t h) hc).elim
  · rcases hm with h | h | h | h
    · exact (keep_drop_excl (S.keep t h) hc).elim
    · exact (register_drop_excl (S.register t h) hc).elim
    · exact (drop_topUp_excl hc (S.topUp t h)).elim
    · exact h

theorem filter_lt_eq {m : Nat} {L L' : List (Fin m)} (h : L.Pairwise (· < ·))
    (h' : L'.Pairwise (· < ·)) {t : Nat} (hm : ∀ x : Fin m, x.val < t → (x ∈ L ↔ x ∈ L')) :
    L.filter (·.val < t) = L'.filter (·.val < t) := by
  apply sorted_eq (h.filter _) (h'.filter _)
  intro x
  simp only [List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨(hm x h2).mp h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨(hm x h2).mpr h1, h2⟩

/-- **Uniqueness.** Two partitions satisfying the specification for the same queue are equal
(induction on the queue position: each position's class is fixed by the classes before it). -/
theorem OnboardingSpec.unique {P : Preset} {ctx : Ctx} {V : List BLSPubkey}
    {Q : List PendingDeposit} {K R T X K' R' T' X' : List (Fin Q.length)}
    {bs bs' : List JauneConsensus.Gloas.Builder} {q q' : List PendingDeposit}
    (S : OnboardingSpec P ctx V Q K R T X bs q) (S' : OnboardingSpec P ctx V Q K' R' T' X' bs' q') :
    (K', R', T', X') = (K, R, T, X) := by
  have key : ∀ (m : Nat) (t : Fin Q.length), t.val = m →
      (t ∈ K ↔ t ∈ K') ∧ (t ∈ R ↔ t ∈ R') ∧ (t ∈ T ↔ t ∈ T') ∧ (t ∈ X ↔ t ∈ X') := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro t ht
      subst ht
      have hR := filter_lt_eq S.increasing.2.1 S'.increasing.2.1
        (fun x hx => (ih x.val hx x rfl).2.1)
      have hK := filter_lt_eq S.increasing.1 S'.increasing.1 (fun x hx => (ih x.val hx x rfl).1)
      have hreg : regBefore Q R t = regBefore Q R' t := by unfold regBefore; rw [hR]
      have hkept : keptBefore Q K t = keptBefore Q K' t := by unfold keptBefore; rw [hK]
      obtain ⟨a1, a2, a3, a4⟩ := S.mem_iff t
      obtain ⟨b1, b2, b3, b4⟩ := S'.mem_iff t
      unfold KeepAt at a1 b1
      unfold RegisterAt at a2 b2
      unfold TopUpAt at a3 b3
      unfold DropAt at a4 b4
      rw [hreg, hkept] at a1 a2 a4
      rw [hreg] at a3
      exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm, a4.trans b4.symm⟩
  have key' := fun t => key t.val t rfl
  obtain ⟨i1, i2, i3, i4⟩ := S.increasing
  obtain ⟨j1, j2, j3, j4⟩ := S'.increasing
  rw [sorted_eq j1 i1 (fun x => (key' x).1.symm), sorted_eq j2 i2 (fun x => (key' x).2.1.symm),
    sorted_eq j3 i3 (fun x => (key' x).2.2.1.symm), sorted_eq j4 i4 (fun x => (key' x).2.2.2.symm)]

/-! ## The builder total of the specification (B7's fork term) -/

/-- The registered deposits have distinct pubkeys (each is fresh when registered). -/
theorem OnboardingSpec.pubkeys_nodup {P : Preset} {ctx : Ctx} {V : List BLSPubkey}
    {Q : List PendingDeposit} {K R T X : List (Fin Q.length)}
    {bs : List JauneConsensus.Gloas.Builder}
    {q : List PendingDeposit} (S : OnboardingSpec P ctx V Q K R T X bs q) :
    (R.map (fun r => Q[r].pubkey)).Nodup := by
  unfold List.Nodup
  rw [List.pairwise_map]
  apply S.increasing.2.1.imp_of_mem
  intro a c ha hc hac e
  apply (S.register c hc).2.1
  unfold regBefore
  rw [e.symm]
  exact List.mem_map_of_mem (List.mem_filter.mpr ⟨ha, by simpa using hac⟩)

theorem sum_ite_zero {α : Type} {R : List α} {p : α → Bool} (hp : ∀ r ∈ R, p r = false) (a : Nat) :
    (R.map (fun r => if p r = true then a else 0)).sum = 0 := by
  induction R with
  | nil => rfl
  | cons x R ih =>
    rw [List.map_cons, List.sum_cons, ite_eq_right (by rw [hp x (by simp)]; simp),
      ih (fun r hr => hp r (by simp [hr]))]

theorem sum_ite_unique {α : Type} [DecidableEq α] {R : List α} (hR : R.Nodup) {p : α → Bool}
    {r0 : α} (hr0 : r0 ∈ R)
    (hp : ∀ r ∈ R, p r = true ↔ r = r0) (a : Nat) :
    (R.map (fun r => if p r = true then a else 0)).sum = a := by
  induction R with
  | nil => cases hr0
  | cons x R ih =>
    rw [List.map_cons, List.sum_cons]
    rw [List.nodup_cons] at hR
    by_cases hx : x = r0
    · subst hx
      have hz : (R.map (fun r => if p r = true then a else 0)).sum = 0 := by
        apply sum_ite_zero
        intro r hr
        cases h : p r
        · rfl
        · exact absurd ((hp r (by simp [hr])).mp h ▸ hr) hR.1
      rw [ite_eq_left ((hp x (by simp)).mpr rfl), hz, Nat.add_zero]
    · rw [ite_eq_right (by rw [hp x (by simp)]; exact hx)]
      rw [ih hR.2 (by simpa [Ne.symm hx] using hr0) (fun r hr => hp r (by simp [hr]))]
      simp

theorem sum_map_add' {α : Type} {l : List α} {f g : α → Nat} :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; omega

theorem topUpTotal_cons (Q : List PendingDeposit) (t : Fin Q.length) (T : List (Fin Q.length))
    (r : Fin Q.length) :
    topUpTotal Q (t :: T) r =
      (if (decide (r < t) && Q[t].pubkey == Q[r].pubkey) = true then Q[t].amount.toNat else 0) +
        topUpTotal Q T r := by
  unfold topUpTotal
  rw [List.filter_cons]
  split <;> simp_all

/-- Each top-up is credited to exactly one registered builder, so the top-up totals over the
registered deposits sum to the top-up amounts. -/
theorem sum_topUpTotal {Q : List PendingDeposit} {R : List (Fin Q.length)} (hR : R.Nodup)
    (hpk : (R.map (fun r => Q[r].pubkey)).Nodup) :
    ∀ (T : List (Fin Q.length)), (∀ t ∈ T, Q[t].pubkey ∈ regBefore Q R t) →
      (R.map (topUpTotal Q T)).sum = (T.map (fun t => Q[t].amount.toNat)).sum
  | [], _ => by
    have : ∀ r, topUpTotal Q [] r = 0 := fun r => rfl
    clear hpk hR ‹∀ t ∈ [], _›
    induction R with
    | nil => rfl
    | cons x R ih => rw [List.map_cons, List.sum_cons, this, ih]; rfl
  | t :: T, hT => by
    rw [List.map_congr_left (fun r _ => topUpTotal_cons Q t T r)]
    rw [sum_map_add', sum_topUpTotal hR hpk T (fun t ht => hT t (by simp [ht])),
      List.map_cons, List.sum_cons]
    congr 1
    obtain ⟨r0, hr0, he⟩ := List.mem_map.mp (hT t (by simp))
    rw [List.mem_filter] at hr0
    apply sum_ite_unique hR hr0.1
    intro r hr
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨_, h⟩
      exact List.inj_on_of_nodup_map hpk hr hr0.1 ((pubkey_beq_iff.mp h).symm.trans he.symm)
    · rintro rfl
      exact ⟨by simpa using hr0.2, pubkey_beq_iff.mpr he.symm⟩

theorem records_balances {P : Preset} {Q : List PendingDeposit} {T : List (Fin Q.length)} :
    ∀ {R : List (Fin Q.length)} {bs : List JauneConsensus.Gloas.Builder},
      List.Forall₂ (OnboardedRecord P Q T) R bs →
      bs.map (·.balance.toNat) = R.map (fun r => Q[r].amount.toNat + topUpTotal Q T r)
  | _, _, .nil => rfl
  | _, _, .cons h hs => by rw [List.map_cons, List.map_cons, h.balance, records_balances hs]

/-- **B7's fork term, from the specification.** The registry's total balance is the sum of the
registering (`R`) and top-up (`T`) amounts. -/
theorem OnboardingSpec.total {P : Preset} {ctx : Ctx} {V : List BLSPubkey}
    {Q : List PendingDeposit} {K R T X : List (Fin Q.length)}
    {bs : List JauneConsensus.Gloas.Builder}
    {q : List PendingDeposit} (S : OnboardingSpec P ctx V Q K R T X bs q) :
    (bs.map (·.balance.toNat)).sum = ((R ++ T).map (fun t => Q[t].amount.toNat)).sum := by
  rw [records_balances S.records, sum_map_add', List.map_append, List.sum_append,
    sum_topUpTotal (S.increasing.2.1.imp ne_of_lt) S.pubkeys_nodup T
      (fun t ht => (S.topUp t ht).2)]

/-- **Order dependence (design R8).** A deposit after a registered one with the same pubkey is a
step-6 top-up, whatever its credentials and signature. -/
theorem OnboardingSpec.later_same_pubkey_topUp {P : Preset} {ctx : Ctx} {V : List BLSPubkey}
    {Q : List PendingDeposit} {K R T X : List (Fin Q.length)}
    {bs : List JauneConsensus.Gloas.Builder}
    {q : List PendingDeposit} (S : OnboardingSpec P ctx V Q K R T X bs q) {r t : Fin Q.length}
    (hr : r ∈ R) (hrt : r < t) (hpk : Q[t].pubkey = Q[r].pubkey) : t ∈ T := by
  refine (S.mem_iff t).2.2.1.mpr ⟨?_, ?_⟩
  · rw [hpk]; exact (S.register r hr).1
  · rw [hpk]
    exact List.mem_map_of_mem (List.mem_filter.mpr ⟨hr, by simpa using hrt⟩)

/-! ## The loop meets the specification -/

section Loop

theorem count_append_single {m : Nat} (L : List (Fin m)) (e x : Fin m) :
    (L ++ [e]).count x = L.count x + if x = e then 1 else 0 := by
  rw [List.count_append, List.count_singleton]
  by_cases h : x = e
  · subst h; simp
  · simp [h, Ne.symm h]

theorem pairwise_append_single {m : Nat} {L : List (Fin m)} {e : Fin m} (h : L.Pairwise (· < ·))
    (hl : ∀ x ∈ L, x.val < e.val) : (L ++ [e]).Pairwise (· < ·) := by
  rw [List.pairwise_append]
  exact ⟨h, List.pairwise_singleton _ _, fun a ha b hb => by
    rw [List.mem_singleton] at hb; subst hb; exact hl a ha⟩

theorem filter_append_single {m : Nat} {L : List (Fin m)} {e : Fin m} {t : Nat} (ht : t ≤ e.val) :
    (L ++ [e]).filter (·.val < t) = L.filter (·.val < t) := by
  rw [List.filter_append]
  simp [show ¬ e.val < t by omega]

theorem filter_all_lt {m : Nat} {L : List (Fin m)} {n : Nat} (h : ∀ x ∈ L, x.val < n) :
    L.filter (·.val < n) = L := by
  rw [List.filter_eq_self]
  intro x hx; simpa using h x hx

theorem regBefore_append {Q : List PendingDeposit} {R : List (Fin Q.length)} {e : Fin Q.length}
    {t : Nat} (ht : t ≤ e.val) : regBefore Q (R ++ [e]) t = regBefore Q R t := by
  unfold regBefore; rw [filter_append_single ht]

theorem keptBefore_append {Q : List PendingDeposit} {K : List (Fin Q.length)} {e : Fin Q.length}
    {t : Nat} (ht : t ≤ e.val) : keptBefore Q (K ++ [e]) t = keptBefore Q K t := by
  unfold keptBefore; rw [filter_append_single ht]

variable {ctx : Ctx} {V : List BLSPubkey} {Q : List PendingDeposit}

theorem KeepAt_congr {K R K' R' : List (Fin Q.length)} {t : Fin Q.length} (hK : keptBefore Q K t = keptBefore Q K' t)
    (hR : regBefore Q R t = regBefore Q R' t) : KeepAt ctx V Q K R t = KeepAt ctx V Q K' R' t := by
  unfold KeepAt; rw [hK, hR]

theorem RegisterAt_congr {K R K' R' : List (Fin Q.length)} {t : Fin Q.length} (hK : keptBefore Q K t = keptBefore Q K' t)
    (hR : regBefore Q R t = regBefore Q R' t) :
    RegisterAt ctx V Q K R t = RegisterAt ctx V Q K' R' t := by
  unfold RegisterAt; rw [hK, hR]

theorem DropAt_congr {K R K' R' : List (Fin Q.length)} {t : Fin Q.length} (hK : keptBefore Q K t = keptBefore Q K' t)
    (hR : regBefore Q R t = regBefore Q R' t) : DropAt ctx V Q K R t = DropAt ctx V Q K' R' t := by
  unfold DropAt; rw [hK, hR]

theorem TopUpAt_congr {R R' : List (Fin Q.length)} {t : Fin Q.length} (hR : regBefore Q R t = regBefore Q R' t) :
    TopUpAt V Q R t = TopUpAt V Q R' t := by
  unfold TopUpAt; rw [hR]

/-- The loop invariant after the first `n` deposits: the specification on the prefix, with the
registry `st.builders` and the accumulator `acc`. -/
structure Inv (P : Preset) (ctx : Ctx) (V : List BLSPubkey) (Q : List PendingDeposit) (st0 : GSt P)
    (n : Nat) (K R T X : List (Fin Q.length)) (st : GSt P) (acc : Array PendingDeposit) : Prop where
  count : ∀ x : Fin Q.length,
    K.count x + R.count x + T.count x + X.count x = if x.val < n then 1 else 0
  increasing : K.Pairwise (· < ·) ∧ R.Pairwise (· < ·) ∧ T.Pairwise (· < ·) ∧ X.Pairwise (· < ·)
  keep : ∀ t ∈ K, KeepAt ctx V Q K R t
  register : ∀ t ∈ R, RegisterAt ctx V Q K R t
  dropped : ∀ t ∈ X, DropAt ctx V Q K R t
  topUp : ∀ t ∈ T, TopUpAt V Q R t
  kept : acc.toList = K.map (fun t => Q[t])
  frame : st = { st0 with builders := st.builders }
  size : st.builders.toArray.size = R.length
  recs : ∀ k (h1 : k < R.length) (h2 : k < st.builders.toArray.size),
    OnboardedRecord P Q T R[k] st.builders.toArray[k]
  nodup : (R.map (fun r => Q[r].pubkey)).Nodup

variable {P : Preset} {st0 : GSt P}

theorem Inv.lt {n : Nat} {K R T X : List (Fin Q.length)} {st : GSt P} {acc : Array PendingDeposit}
    (I : Inv P ctx V Q st0 n K R T X st acc) {x : Fin Q.length} :
    (x ∈ K → x.val < n) ∧ (x ∈ R → x.val < n) ∧ (x ∈ T → x.val < n) ∧ (x ∈ X → x.val < n) := by
  have h := I.count x
  refine ⟨fun hx => ?_, fun hx => ?_, fun hx => ?_, fun hx => ?_⟩ <;>
  · have := List.count_pos_iff.mpr hx
    split at h
    · assumption
    · omega

/-- The registry's pubkeys are the registered deposits' pubkeys. -/
theorem Inv.pubkeys {n : Nat} {K R T X : List (Fin Q.length)} {st : GSt P} {acc : Array PendingDeposit}
    (I : Inv P ctx V Q st0 n K R T X st acc) :
    (st.builders.toArray.map (·.pubkey)).toList = regBefore Q R n := by
  unfold regBefore
  rw [filter_all_lt (fun x hx => I.lt.2.1 hx)]
  apply List.ext_getElem
  · simp [I.size]
  · intro k h1 h2
    simp only [Array.toList_map, List.getElem_map, Array.getElem_toList]
    simp only [List.length_map] at h2
    exact (I.recs k h2 (by rw [I.size]; exact h2)).pubkey

theorem count_push {m : Nat} {s : Fin m → Nat} {e : Fin m}
    (h : ∀ x : Fin m, s x = if x.val < e.val then 1 else 0) (x : Fin m) :
    s x + (if x = e then 1 else 0) = if x.val < e.val + 1 then 1 else 0 := by
  have := h x
  have hxe : x = e ↔ x.val = e.val := Fin.ext_iff
  by_cases hx : x.val = e.val
  · rw [ite_eq_left (hxe.mpr hx)]
    split_ifs at this ⊢ <;> omega
  · rw [ite_eq_right (fun h => hx (hxe.mp h))]
    split_ifs at this ⊢ <;> omega

/-- Appending `n` to `K` (steps 1-3). -/
theorem Inv.appendK {e : Fin Q.length} {K R T X : List (Fin Q.length)} {st : GSt P} {acc : Array PendingDeposit}
    (I : Inv P ctx V Q st0 e.val K R T X st acc) (hk : KeepAt ctx V Q K R e) :
    Inv P ctx V Q st0 (e.val + 1) (K ++ [e]) R T X st (acc.push Q[e]) := by
  refine ⟨fun x => ?_, ⟨pairwise_append_single I.increasing.1 (fun x hx => I.lt.1 hx),
      I.increasing.2⟩, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, I.topUp,
      ?_, I.frame, I.size, I.recs, I.nodup⟩
  · rw [count_append_single]
    have := count_push I.count x
    omega
  · rcases List.mem_append.mp ht with ht | ht
    · rw [KeepAt_congr (keptBefore_append (Nat.le_of_lt (I.lt.1 ht))) rfl]; exact I.keep t ht
    · rw [List.mem_singleton] at ht; subst ht
      rw [KeepAt_congr (keptBefore_append (Nat.le_refl _)) rfl]; exact hk
  · rw [RegisterAt_congr (keptBefore_append (Nat.le_of_lt (I.lt.2.1 ht))) rfl]
    exact I.register t ht
  · rw [DropAt_congr (keptBefore_append (Nat.le_of_lt (I.lt.2.2.2 ht))) rfl]
    exact I.dropped t ht
  · rw [Array.toList_push, I.kept, List.map_append]; rfl

/-- Appending `n` to `X` (step 4). -/
theorem Inv.appendX {e : Fin Q.length} {K R T X : List (Fin Q.length)} {st : GSt P} {acc : Array PendingDeposit}
    (I : Inv P ctx V Q st0 e.val K R T X st acc) (hd : DropAt ctx V Q K R e) :
    Inv P ctx V Q st0 (e.val + 1) K R T (X ++ [e]) st acc := by
  refine ⟨fun x => ?_, ⟨I.increasing.1, I.increasing.2.1, I.increasing.2.2.1,
      pairwise_append_single I.increasing.2.2.2 (fun x hx => I.lt.2.2.2 hx)⟩,
      I.keep, I.register, fun t ht => ?_, I.topUp, I.kept, I.frame, I.size, I.recs, I.nodup⟩
  · rw [count_append_single]
    have := count_push I.count x
    omega
  · rcases List.mem_append.mp ht with ht | ht
    · exact I.dropped t ht
    · rw [List.mem_singleton] at ht; subst ht; exact hd

theorem topUpTotal_append (Q : List PendingDeposit) (T : List (Fin Q.length)) (e r : Fin Q.length) :
    topUpTotal Q (T ++ [e]) r = topUpTotal Q T r +
      if (decide (r < e) && Q[e].pubkey == Q[r].pubkey) = true then Q[e].amount.toNat else 0 := by
  unfold topUpTotal
  rw [List.filter_append, List.map_append, List.sum_append]
  split <;> simp_all

theorem topUpTotal_of_lt {Q : List PendingDeposit} {T : List (Fin Q.length)} {e : Fin Q.length}
    (h : ∀ x ∈ T, x.val < e.val) : topUpTotal Q T e = 0 := by
  unfold topUpTotal
  rw [List.filter_eq_nil_iff.mpr]
  · rfl
  · intro x hx
    have := h x hx
    simp [Fin.lt_def, show ¬ e.val < x.val by omega]

/-- Appending `n` to `R` (step 5): the registry grows by the onboarded record. -/
theorem Inv.appendR {e : Fin Q.length} {K R T X : List (Fin Q.length)} {st st' : GSt P} {acc : Array PendingDeposit}
    (I : Inv P ctx V Q st0 e.val K R T X st acc) (hr : RegisterAt ctx V Q K R e)
    {b : JauneConsensus.Gloas.Builder} (hb : OnboardedRecord P Q T e b)
    (hst' : st' = { st with builders := st'.builders })
    (hbs : st'.builders.toArray = st.builders.toArray.push b) :
    Inv P ctx V Q st0 (e.val + 1) K (R ++ [e]) T X st' acc := by
  have hRlt : ∀ x ∈ R, x.val < e.val := fun x hx => I.lt.2.1 hx
  refine ⟨fun x => ?_, ⟨I.increasing.1, pairwise_append_single I.increasing.2.1 hRlt,
      I.increasing.2.2⟩, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun t ht => ?_,
      I.kept, ?_, ?_, ?_, ?_⟩
  · rw [count_append_single]
    have := count_push I.count x
    omega
  · rw [KeepAt_congr rfl (regBefore_append (Nat.le_of_lt (I.lt.1 ht)))]; exact I.keep t ht
  · rcases List.mem_append.mp ht with ht | ht
    · rw [RegisterAt_congr rfl (regBefore_append (Nat.le_of_lt (I.lt.2.1 ht)))]
      exact I.register t ht
    · rw [List.mem_singleton] at ht; subst ht
      rw [RegisterAt_congr rfl (regBefore_append (Nat.le_refl _))]; exact hr
  · rw [DropAt_congr rfl (regBefore_append (Nat.le_of_lt (I.lt.2.2.2 ht)))]
    exact I.dropped t ht
  · rw [TopUpAt_congr (regBefore_append (Nat.le_of_lt (I.lt.2.2.1 ht)))]
    exact I.topUp t ht
  · rw [hst']; rw [I.frame]
  · rw [hbs, Array.size_push, I.size, List.length_append, List.length_singleton]
  · intro k h1 h2
    simp only [hbs]
    rw [List.length_append, List.length_singleton] at h1
    by_cases hk : k < R.length
    · rw [Array.getElem_push_lt (by rw [I.size]; exact hk), List.getElem_append_left hk]
      exact I.recs k hk (by rw [I.size]; exact hk)
    · have hk' : k = R.length := by omega
      subst hk'
      rw [List.getElem_append_right (Nat.le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton]
      rw [Array.getElem_push, dite_eq_right (by rw [I.size]; omega)]
      exact hb
  · rw [List.map_append, List.nodup_append]
    refine ⟨I.nodup, List.nodup_singleton _, ?_⟩
    intro a ha c hc
    simp only [List.map_cons, List.map_nil, List.mem_singleton] at hc
    subst hc
    intro hac
    exact hr.2.1 (by unfold regBefore; rw [filter_all_lt hRlt]; exact hac ▸ ha)

/-- Appending `n` to `T` (step 6): the matching builder's balance grows by the amount. -/
theorem Inv.appendT {e : Fin Q.length} {K R T X : List (Fin Q.length)} {st st' : GSt P} {acc : Array PendingDeposit}
    (I : Inv P ctx V Q st0 e.val K R T X st acc) (ht : TopUpAt V Q R e)
    {i : Nat} {b : JauneConsensus.Gloas.Builder} {nb : U64}
    (hb : st.builders.toArray[i]? = some b) (hpk : b.pubkey = Q[e].pubkey)
    (hnb : nb.toNat = b.balance.toNat + Q[e].amount.toNat)
    (hst' : st' = { st with builders := st'.builders })
    (hsz : st'.builders.toArray.size = st.builders.toArray.size)
    (hi : st'.builders.toArray[i]? = some { b with balance := nb })
    (hoth : ∀ j, j ≠ i → st'.builders.toArray[j]? = st.builders.toArray[j]?) :
    Inv P ctx V Q st0 (e.val + 1) K R (T ++ [e]) X st' acc := by
  refine ⟨fun x => ?_, ⟨I.increasing.1, I.increasing.2.1,
      pairwise_append_single I.increasing.2.2.1 (fun x hx => I.lt.2.2.1 hx), I.increasing.2.2.2⟩,
      I.keep, I.register, I.dropped, fun t ht' => ?_, I.kept, ?_, ?_, ?_, I.nodup⟩
  · rw [count_append_single]
    have := count_push I.count x
    omega
  · rcases List.mem_append.mp ht' with ht' | ht'
    · exact I.topUp t ht'
    · rw [List.mem_singleton] at ht'; subst ht'; exact ht
  · rw [hst']; rw [I.frame]
  · rw [hsz, I.size]
  · intro k h1 h2
    have h2' : k < st.builders.toArray.size := by rw [← hsz]; exact h2
    have hrk := I.recs k h1 h2'
    have hlt : R[k] < e := I.lt.2.1 (List.getElem_mem _)
    obtain ⟨hil, hbi⟩ : ∃ h : i < st.builders.toArray.size, st.builders.toArray[i] = b :=
      ⟨(Array.getElem?_eq_some_iff.mp hb).1, (Array.getElem?_eq_some_iff.mp hb).2⟩
    have hri := I.recs i (by rw [← I.size]; exact hil) hil
    by_cases hki : k = i
    · subst hki
      have he : st'.builders.toArray[k] = { b with balance := nb } :=
        Option.some.inj ((Array.getElem?_eq_getElem h2).symm.trans hi)
      rw [he]
      rw [hbi] at hrk
      have hcond : (decide (R[k] < e) && Q[e].pubkey == Q[R[k]].pubkey) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨hlt, pubkey_beq_iff.mpr (hpk.symm.trans hrk.pubkey)⟩
      exact ⟨hrk.pubkey, hrk.version, hrk.execution_address, hrk.deposit_epoch,
        hrk.withdrawable_epoch, by
          rw [topUpTotal_append, ite_eq_left hcond]; simp only []; rw [hnb, hrk.balance]; omega⟩
    · have he : st'.builders.toArray[k] = st.builders.toArray[k] :=
        Option.some.inj ((Array.getElem?_eq_getElem h2).symm.trans
          ((hoth k hki).trans (Array.getElem?_eq_getElem h2')))
      rw [he]
      have hne : Q[e].pubkey ≠ Q[R[k]].pubkey := by
        intro e
        rw [← hpk, ← hbi, hri.pubkey] at e
        have := (List.Nodup.getElem_inj_iff I.nodup (i := i) (j := k)
          (hi := by rw [List.length_map, ← I.size]; exact hil)
          (hj := by rw [List.length_map]; exact h1)).mp (by simp only [List.getElem_map]; exact e)
        exact hki this.symm
      have hcond : ¬ (decide (R[k] < e) && Q[e].pubkey == Q[R[k]].pubkey) = true := by
        simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
        intro _ h; exact hne (pubkey_beq_iff.mp h)
      exact ⟨hrk.pubkey, hrk.version, hrk.execution_address, hrk.deposit_epoch,
        hrk.withdrawable_epoch, by rw [topUpTotal_append, ite_eq_right hcond, hrk.balance]; rfl⟩

theorem getCurrentEpoch_frame {st st0 : GSt P} (h : st = { st0 with builders := st.builders }) :
    JauneConsensus.Gloas.getCurrentEpoch st = JauneConsensus.Gloas.getCurrentEpoch st0 := by
  unfold JauneConsensus.Gloas.getCurrentEpoch
  rw [h]

/-- One iteration preserves the invariant. -/
theorem Inv.step {e : Fin Q.length} {K R T X : List (Fin Q.length)} {st st' : GSt P} {acc acc' : Array PendingDeposit}
    {Varr : Array BLSPubkey} (hV : Varr.toList = V)
    (hE : ∀ e, JauneConsensus.Gloas.getCurrentEpoch st0 = .ok e → e ≠ FAR_FUTURE_EPOCH)
    (I : Inv P ctx V Q st0 e.val K R T X st acc)
    (h : JauneConsensus.Gloas.onboardBuilderDeposit ctx Varr (st, acc) Q[e] = .ok (st', acc')) :
    ∃ K' R' T' X', Inv P ctx V Q st0 (e.val + 1) K' R' T' X' st' acc' := by
  have hpk := I.pubkeys
  have hacc : (keptBefore Q K e).toArray = acc := by
    unfold keptBefore
    rw [filter_all_lt (fun x hx => I.lt.1 hx), ← I.kept, Array.toArray_toList]
  have hmemV : ∀ x, Varr.contains x = true ↔ x ∈ V := by
    intro x; rw [Array.contains_iff_mem, ← hV, Array.mem_toList_iff]
  have hnone : (st.builders.toArray.map (·.pubkey)).idxOf? Q[e].pubkey = none →
      Q[e].pubkey ∉ regBefore Q R e := by
    intro hn hm
    rw [Array.idxOf?_eq_none_iff] at hn
    rw [← hpk, Array.mem_toList_iff] at hm
    exact hn hm
  rcases onboardBuilderDeposit_cases h with ⟨hv, rfl, rfl⟩ | ⟨hv, hi, hc, rfl, rfl⟩ |
    ⟨hv, hi, hw, hp, hs, rfl, rfl⟩ | ⟨hv, hi, hw, hp, hs, addr, ha, hadd, rfl⟩ |
    ⟨hv, i, b, nb, bs, hi, hb, hnb, hset, rfl, rfl⟩
  · exact ⟨_, _, _, _, I.appendK (Or.inl ((hmemV _).mp hv))⟩
  · refine ⟨_, _, _, _, I.appendK (Or.inr ⟨hnone hi, ?_⟩)⟩
    rw [hacc]; exact hc
  · have hvn : Q[e].pubkey ∉ V := fun hm => by rw [← hmemV] at hm; rw [hm] at hv; cases hv
    refine ⟨_, _, _, _, I.appendX ⟨hvn, hnone hi, hw, ?_, hs⟩⟩
    rw [hacc]; exact hp
  · have hvn : Q[e].pubkey ∉ V := fun hm => by rw [← hmemV] at hm; rw [hm] at hv; cases hv
    unfold JauneConsensus.Gloas.addBuilderToRegistry at hadd
    obtain ⟨idx, hidx, hadd⟩ := bind_eq_ok_iff.mp hadd
    obtain ⟨de, hde, hadd⟩ := bind_eq_ok_iff.mp hadd
    obtain ⟨bs, hbs, hadd⟩ := bind_eq_ok_iff.mp hadd
    cases hadd
    have hfar : ∀ b ∈ st.builders.toArray, b.withdrawable_epoch = FAR_FUTURE_EPOCH := by
      intro b hb
      obtain ⟨k, hk, rfl⟩ := Array.getElem_of_mem hb
      exact (I.recs k (by rw [← I.size]; exact hk) hk).withdrawable_epoch
    have hix := getIndexForNewBuilder_append hidx hfar (by rw [getCurrentEpoch_frame I.frame]; exact hE)
    unfold ProgressiveListS.setOrAppend at hbs
    rw [ite_eq_left (by simpa [ProgressiveListS.length] using hix)] at hbs
    cases hbs
    refine ⟨_, _, _, _, I.appendR (b := freshBuilder Q[e].pubkey addr Q[e].amount de)
      ⟨hvn, hnone hi, hw, by rw [hacc]; exact hp, hs⟩
      ⟨rfl, rfl, ha, hde, rfl, by rw [topUpTotal_of_lt (fun x hx => I.lt.2.2.1 hx)]; rfl⟩ rfl rfl⟩
  · have hvn : Q[e].pubkey ∉ V := fun hm => by rw [← hmemV] at hm; rw [hm] at hv; cases hv
    obtain ⟨hil, hbi⟩ := arr_idxOf?_some hi
    have hil' : i < st.builders.toArray.size := by simpa using hil
    have hbb : st.builders.toArray[i] = b :=
      Option.some.inj ((Array.getElem?_eq_getElem hil').symm.trans hb)
    have hbpk : b.pubkey = Q[e].pubkey := by
      rw [← hbi, Array.getElem_map, hbb]
    have hmem : Q[e].pubkey ∈ regBefore Q R e := by
      rw [← hpk, Array.mem_toList_iff, ← hbi]
      exact Array.getElem_mem hil
    obtain ⟨h1, h2, h3⟩ := pl_set_ok hset
    exact ⟨_, _, _, _, I.appendT ⟨hvn, hmem⟩ hb hbpk (U64.toNat_add? hnb) rfl h1 h2 h3⟩

/-- The loop over the first `n` deposits satisfies the invariant. -/
theorem fold_inv {Varr : Array BLSPubkey} (hV : Varr.toList = V)
    (hE : ∀ e, JauneConsensus.Gloas.getCurrentEpoch st0 = .ok e → e ≠ FAR_FUTURE_EPOCH)
    (hb0 : st0.builders.toArray = #[]) :
    ∀ n, n ≤ Q.length → ∀ st acc,
      (Q.take n).foldlM (JauneConsensus.Gloas.onboardBuilderDeposit ctx Varr) (st0, #[]) =
        .ok (st, acc) → ∃ K R T X, Inv P ctx V Q st0 n K R T X st acc
  | 0, _, st, acc, h => by
    cases h
    refine ⟨[], [], [], [], ⟨fun x => (by simp), ⟨.nil, .nil, .nil, .nil⟩, fun _ h => (by cases h),
      fun _ h => (by cases h), fun _ h => (by cases h), fun _ h => (by cases h), rfl, rfl,
      (by rw [hb0]; rfl), fun k h1 => absurd h1 (Nat.not_lt_zero _), List.nodup_nil⟩⟩
  | n + 1, hn, st, acc, h => by
    rw [List.take_add_one, List.getElem?_eq_getElem (by omega), Option.toList_some,
      List.foldlM_append] at h
    obtain ⟨⟨st1, acc1⟩, h1, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨K, R, T, X, I⟩ := fold_inv hV hE hb0 n (by omega) st1 acc1 h1
    rw [List.foldlM_cons] at h
    obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
    cases h
    exact I.step (e := ⟨n, by omega⟩) hV hE hr

/-- At the end of the queue the invariant is the specification. -/
theorem Inv.spec {K R T X : List (Fin Q.length)} {st : GSt P} {acc : Array PendingDeposit}
    (I : Inv P ctx V Q st0 Q.length K R T X st acc) :
    OnboardingSpec P ctx V Q K R T X st.builders.toArray.toList acc.toList := by
  refine ⟨List.perm_iff_count.mpr (fun x => ?_), I.increasing, I.keep, I.register, I.dropped,
    I.topUp, I.kept, List.forall₂_iff_get.mpr ⟨by simp [I.size], fun k h1 h2 => ?_⟩⟩
  · rw [List.count_append, List.count_append, List.count_append, I.count x,
      List.count_eq_one_of_mem (List.nodup_finRange _) (List.mem_finRange x), ite_eq_left x.isLt]
  · simp only [List.get_eq_getElem, Array.getElem_toList]
    exact I.recs k h1 (by simpa using h2)

end Loop

theorem upgradedState_fields {cfg : Config} {pre : JauneConsensus.BeaconState P .fulu} {p0 : GSt P}
    (h : JauneConsensus.Gloas.upgradedState cfg pre = .ok p0) :
    p0.validators = ProgressiveListS.ofArray pre.validators.toArray ∧
    p0.balances = ProgressiveListS.ofArray pre.balances.toArray ∧
    p0.pending_deposits = ProgressiveListS.ofArray
      (Gated.get (by decide : CFork.fulu.atLeast .electra = true) pre.pending_deposits).toArray ∧
    p0.builders = ProgressiveListS.empty := by
  unfold JauneConsensus.Gloas.upgradedState at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The Fulu pre-state's pending deposits, in queue order. -/
def fuluPendingDeposits (pre : JauneConsensus.BeaconState P .fulu) : List PendingDeposit :=
  (Gated.get (by decide : CFork.fulu.atLeast .electra = true) pre.pending_deposits).toArray.toList

/-- **B1 fork theorem (`upgradeToGloas_onboards`).** `upgrade_to_gloas` onboards builders exactly
as the declarative specification says: there is a partition `K/R/T/X` of the Fulu pending
deposits meeting `OnboardingSpec` against the resulting registry and queue; it is the only one;
validators and their balances are unchanged; and the total builder balance after the upgrade is
the sum of the registering and top-up amounts (B7's fork term). -/
theorem upgradeToGloas_onboards {ctx : Ctx} {pre : JauneConsensus.BeaconState P .fulu}
    {post : JauneConsensus.Gloas.BeaconState P}
    (h : JauneConsensus.Gloas.upgradeToGloas ctx pre = .ok post) :
    ∃ K R T X,
      OnboardingSpec P ctx (pre.validators.toArray.toList.map (·.pubkey)) (fuluPendingDeposits pre)
        K R T X post.builders.toArray.toList post.pending_deposits.toArray.toList ∧
      post.validators.toArray.toList = pre.validators.toArray.toList ∧
      post.balances.toArray.toList = pre.balances.toArray.toList ∧
      (∀ K' R' T' X', OnboardingSpec P ctx (pre.validators.toArray.toList.map (·.pubkey))
          (fuluPendingDeposits pre) K' R' T' X' post.builders.toArray.toList
          post.pending_deposits.toArray.toList → (K', R', T', X') = (K, R, T, X)) ∧
      totalBuilderBalance post =
        ((R ++ T).map (fun t => (fuluPendingDeposits pre)[t].amount.toNat)).sum := by
  unfold JauneConsensus.Gloas.upgradeToGloas at h
  obtain ⟨p0, hp0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ptc, hptc, h⟩ := bind_eq_ok_iff.mp h
  have hE : ∀ e, JauneConsensus.Gloas.getCurrentEpoch { p0 with ptc_window := ptc } = .ok e →
      e ≠ FAR_FUTURE_EPOCH := fun e he => initializePtcWindow_epoch hptc he
  unfold JauneConsensus.Gloas.onboardBuildersFromPendingDeposits at h
  obtain ⟨⟨st, acc⟩, hr, h⟩ := bind_eq_ok_iff.mp h
  cases h
  rw [← Array.foldlM_toList] at hr
  obtain ⟨hpv, hpb, hpd, hpB⟩ := upgradedState_fields hp0
  have hQ : ({ p0 with ptc_window := ptc } : GSt P).pending_deposits.toArray.toList =
      fuluPendingDeposits pre := by
    show p0.pending_deposits.toArray.toList = _
    rw [hpd]; rfl
  have hV : (({ p0 with ptc_window := ptc } : GSt P).validators.toArray.map (·.pubkey)).toList =
      pre.validators.toArray.toList.map (·.pubkey) := by
    show (p0.validators.toArray.map (·.pubkey)).toList = _
    rw [hpv, Array.toList_map]; rfl
  rw [hQ] at hr
  obtain ⟨K, R, T, X, I⟩ := fold_inv (Q := fuluPendingDeposits pre) hV hE
    (by show p0.builders.toArray = #[]; rw [hpB]; rfl) _ (Nat.le_refl _) st acc
    (by rw [List.take_length]; exact hr)
  have S := I.spec
  have hfv := congrArg (·.validators) I.frame
  have hfb := congrArg (·.balances) I.frame
  simp only at hfv hfb
  refine ⟨K, R, T, X, S, ?_, ?_, fun K' R' T' X' S' => S.unique S', ?_⟩
  · show st.validators.toArray.toList = _
    rw [hfv]; show p0.validators.toArray.toList = _; rw [hpv]; rfl
  · show st.balances.toArray.toList = _
    rw [hfb]; show p0.balances.toArray.toList = _; rw [hpb]; rfl
  · unfold totalBuilderBalance
    rw [← S.total]



/-- **B7's fork term (Jaune half of `builder_total_crossing`).** For the onboarding partition of a
successful upgrade, the total builder balance after `upgrade_to_gloas` is the sum of the
registering and top-up amounts. -/
theorem upgradeToGloas_builder_total {ctx : Ctx} {pre : JauneConsensus.BeaconState P .fulu}
    {post : JauneConsensus.Gloas.BeaconState P} {K R T X : List (Fin (fuluPendingDeposits pre).length)}
    (S : OnboardingSpec P ctx (pre.validators.toArray.toList.map (·.pubkey)) (fuluPendingDeposits pre)
      K R T X post.builders.toArray.toList post.pending_deposits.toArray.toList) :
    totalBuilderBalance post =
      ((R ++ T).map (fun t => (fuluPendingDeposits pre)[t].amount.toNat)).sum := by
  unfold totalBuilderBalance
  rw [← S.total]

end JauneConsensus.Facts.Gloas.Onboarding
