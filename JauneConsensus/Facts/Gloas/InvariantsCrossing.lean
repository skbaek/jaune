import JauneConsensus.Facts.Gloas.InvariantsWindow

/-!
# The G3 invariants at the Fulu → Gloas crossing (goal `eip8282-gloas-cross-layer-v1`, G3a)

`upgrade_to_gloas` leaves the builder queues empty, `L` the self-built bid of the fork state's
payload header (value `0`, `L.block_hash = latest_block_hash`), and a registry built by
`onboard_builders_from_pending_deposits`, which registers a pubkey only when no builder has it
(`onboard_pubkeysUnique`). So every state invariant holds on its output (`upgradeToGloas_inv`,
`crossFromFulu_inv`): G3-01 from onboarding's `pubkey ∉` test, the others trivially or vacuously.
G3-02 is a relation between two Gloas states and has no crossing obligation.
-/

namespace JauneConsensus.Facts.Gloas.Inv

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

variable {P : Preset}

local instance : LawfulBEq BLSPubkey where
  eq_of_beq h := pubkey_beq_iff.mp h
  rfl := pubkey_beq_iff.mpr rfl

/-- `add_builder_to_registry` writes one record with the given pubkey and nothing else. -/
theorem addBuilderToRegistry_post {st st' : GSt P} {pk : BLSPubkey} {v : U8}
    {addr : ExecutionAddress} {amt : Gwei} {slot : Slot}
    (h : JauneConsensus.Gloas.addBuilderToRegistry st pk v addr amt slot = .ok st') :
    st' = { st with builders := st'.builders } ∧
      ∃ (i : Nat) (b' : JauneConsensus.Gloas.Builder), st'.builders.toArray[i]? = some b' ∧
        b'.pubkey = pk ∧ st.builders.toArray.size ≤ st'.builders.toArray.size ∧
        ∀ j, j ≠ i → st'.builders.toArray[j]? = st.builders.toArray[j]? := by
  unfold JauneConsensus.Gloas.addBuilderToRegistry at h
  obtain ⟨idx, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨bs, hbs, h⟩ := bind_eq_ok_iff.mp h
  cases h
  obtain ⟨h1, h2, h3⟩ := pl_setOrAppend_ok hbs
  exact ⟨rfl, idx.toNat, _, h2, rfl, h1, h3⟩

/-- A fresh pubkey written at one index keeps the pubkeys unique. -/
theorem pubkeysUnique_of_fresh {m m' : GSt P} {pk : BLSPubkey} {i : Nat}
    {b' : JauneConsensus.Gloas.Builder} (hnot : ∀ b ∈ m.builders.toArray, b.pubkey ≠ pk)
    (hb' : m'.builders.toArray[i]? = some b') (hpk : b'.pubkey = pk)
    (hoth : ∀ j, j ≠ i → m'.builders.toArray[j]? = m.builders.toArray[j]?)
    (hu : BuilderPubkeysUnique m) : BuilderPubkeysUnique m' := by
  have hfresh : ∀ (q : Nat) (c : JauneConsensus.Gloas.Builder), q ≠ i →
      m'.builders.toArray[q]? = some c → c.pubkey ≠ pk := by
    intro q c hq hc
    rw [hoth q hq] at hc
    exact hnot c (Array.mem_of_getElem? hc)
  intro p q bp bq hpq hp hq
  by_cases hpi : p = i
  · subst hpi
    rw [hb'] at hp; cases hp
    rw [hpk]
    exact fun e => hfresh q bq (by omega) hq e.symm
  · by_cases hqi : q = i
    · subst hqi
      rw [hb'] at hq; cases hq
      rw [hpk]
      exact hfresh p bp hpi hp
    · rw [hoth p hpi] at hp
      rw [hoth q hqi] at hq
      exact hu p q bp bq hpq hp hq

theorem pk_of_set {xs ys : ProgressiveListR JauneConsensus.Gloas.Builder} {i : Nat}
    {v b0 : JauneConsensus.Gloas.Builder} {site site' : String} (hget : xs.get i site = .ok b0)
    (hset : xs.set i v site' = .ok ys) (hv : v.pubkey = b0.pubkey) :
    ∀ (j : Nat) (c : JauneConsensus.Gloas.Builder), xs.toArray[j]? = some c →
      ∃ c', ys.toArray[j]? = some c' ∧ c'.pubkey = c.pubkey := by
  obtain ⟨_, h2, h3⟩ := pl_set_ok hset
  intro j c hc
  by_cases hj : j = i
  · subst hj
    rw [pl_get_ok.mp hget] at hc; cases hc
    exact ⟨v, h2, hv⟩
  · exact ⟨c, by rw [h3 j hj]; exact hc, rfl⟩

/-- One onboarding step keeps everything but the registry, and keeps the pubkeys unique. -/
theorem onboardBuilderDeposit_post {ctx : Ctx} {vpks : Array BLSPubkey} {st st' : GSt P}
    {q q' : Array PendingDeposit} {d : PendingDeposit}
    (h : JauneConsensus.Gloas.onboardBuilderDeposit ctx vpks (st, q) d = .ok (st', q')) :
    st' = { st with builders := st'.builders } ∧ (BuilderPubkeysUnique st → BuilderPubkeysUnique st') := by
  revert h
  generalize hr : (st', q') = r
  intro h
  revert st' q' hr h
  suffices hs : Ok (JauneConsensus.Gloas.onboardBuilderDeposit ctx vpks (st, q) d)
      (fun r => r.1 = { st with builders := r.1.builders } ∧
        (BuilderPubkeysUnique st → BuilderPubkeysUnique r.1)) by
    intro st' q' hr h
    subst hr
    exact hs _ h
  unfold JauneConsensus.Gloas.onboardBuilderDeposit
  gvcg
  all_goals
    apply ok_pure
    first
    | exact ⟨rfl, id⟩
    | (rename_i hadd
       obtain ⟨hm, i, b', hb', hpk, _, hoth⟩ := addBuilderToRegistry_post hadd
       refine ⟨hm, pubkeysUnique_of_fresh (fun b hb e => ?_) hb' hpk hoth⟩
       have hnone := ‹Array.idxOf? _ d.pubkey = none›
       rw [Array.idxOf?_eq_none_iff] at hnone
       exact hnone (by rw [← e]; exact Array.mem_map_of_mem hb))
    | (rename_i hget _ _ _ hset
       exact ⟨rfl, pubkeysUnique_of_pk (pl_set_ok hset).1 (pk_of_set hget hset rfl)⟩)

theorem foldlM_inv {α β : Type} (I : β → Prop) (f : β → α → M β)
    (hf : ∀ x a y, I x → f x a = .ok y → I y) :
    ∀ (l : List α) (init out : β), l.foldlM f init = .ok out → I init → I out
  | [], init, out, h, hI => by cases h; exact hI
  | a :: l, init, out, h, hI => by
    rw [List.foldlM_cons] at h
    obtain ⟨y, hy, h⟩ := bind_eq_ok_iff.mp h
    exact foldlM_inv I f hf l y out h (hf _ _ _ hI hy)

/-- Onboarding keeps every field the invariants read but the registry, and keeps the pubkeys
unique. -/
theorem onboard_post {ctx : Ctx} {st post : GSt P}
    (h : JauneConsensus.Gloas.onboardBuildersFromPendingDeposits ctx st = .ok post) :
    InvFrame st { post with builders := st.builders } ∧
      (BuilderPubkeysUnique st → BuilderPubkeysUnique post) := by
  unfold JauneConsensus.Gloas.onboardBuildersFromPendingDeposits at h
  obtain ⟨r, hr, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨st1, q1⟩ := r
  cases h
  rw [← Array.foldlM_toList] at hr
  have hI := foldlM_inv (fun r : GSt P × Array PendingDeposit =>
      r.1 = { st with builders := r.1.builders } ∧ (BuilderPubkeysUnique st → BuilderPubkeysUnique r.1))
    _ (fun x a y hI hy => by
      obtain ⟨x1, x2⟩ := x
      obtain ⟨y1, y2⟩ := y
      obtain ⟨hm, hu⟩ := onboardBuilderDeposit_post hy
      exact ⟨by simp only [] at hI ⊢; rw [hm, hI.1], fun h0 => hu (hI.2 h0)⟩) _ _ _ hr ⟨rfl, id⟩
  obtain ⟨hm, hu⟩ := hI
  simp only [] at hm hu
  refine ⟨?_, hu⟩
  rw [hm]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **The crossing.** Every G3 state invariant (and the auxiliary ones) holds on
`upgrade_to_gloas`'s output. Needs `0 < SLOTS_PER_EPOCH` (G3-07's window index is then inside
the payments vector). -/
theorem upgradeToGloas_inv (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx}
    {pre : JauneConsensus.BeaconState P .fulu} {post : GSt P}
    (h : JauneConsensus.Gloas.upgradeToGloas ctx pre = .ok post) :
    BuilderPubkeysUnique post ∧ PendingRefsInRange post ∧ ExitedHaveNoPending post ∧
      PendingCovered post ∧ NextBuilderIndexInRange post ∧ NoLiveWeightOnLatestBid post ∧
      LatestBidCoherence post ∧ LatestBidBuilderActive post ∧ FutureEmpty post := by
  unfold JauneConsensus.Gloas.upgradeToGloas at h
  obtain ⟨p0, hp0, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨ptc, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨fr, hu⟩ := onboard_post h
  unfold JauneConsensus.Gloas.upgradedState at hp0
  obtain ⟨_, _, hp0⟩ := bind_eq_ok_iff.mp hp0
  obtain ⟨_, _, hp0⟩ := bind_eq_ok_iff.mp hp0
  cases hp0
  obtain ⟨_, hP, hW, hL, hK, hH, hS, hN⟩ := fr
  simp only [] at hP hW hL hK hH hS hN
  have hWe : post.builder_pending_withdrawals.toArray.toList = [] := by rw [hW]; rfl
  have hPa : post.builder_pending_payments.toArray =
      Array.replicate (2 * P.SLOTS_PER_EPOCH) JauneConsensus.Gloas.BuilderPendingPayment.empty := by
    rw [hP]; rfl
  have hPk : ∀ k, k < 2 * P.SLOTS_PER_EPOCH → post.builder_pending_payments.toArray[k]? =
      some JauneConsensus.Gloas.BuilderPendingPayment.empty := by
    intro k hk; rw [hPa]; simp [hk]
  have hpend : ∀ i, pend post i = 0 := by
    intro i; unfold pend; rw [hWe, hPa]; simp [pendW, pendP, wAmt_empty]
  have hval : post.latest_execution_payload_bid.value = U64.zero := by rw [hL]
  refine ⟨hu (fun _ _ _ _ _ hi => by simp [ProgressiveListS.empty] at hi), ⟨?_, ?_⟩, ?_, ?_, ?_, ?_,
    ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro w hw; rw [hWe] at hw; cases hw
  · intro p hp hne
    rw [hPa] at hp
    simp only [Array.toList_replicate, List.mem_replicate] at hp
    exact absurd hp.2 hne
  · intro i _ _ _; exact hpend i
  · intro i b _
    rw [hpend]
    have : expo post i = 0 := by
      unfold expo; rw [if_neg]; rintro ⟨_, hv, _⟩; rw [hval] at hv; exact absurd hv (by decide)
    omega
  · intro _; rw [hN]; show 0 < _; omega
  · intro k hk
    have hk' : k < 2 * P.SLOTS_PER_EPOCH := by
      unfold bidIndex at hk
      simp only [] at hk
      have := Nat.mod_lt post.latest_execution_payload_bid.slot.toNat hspe
      split at hk
      · cases hk; omega
      · split at hk
        · cases hk; omega
        · cases hk
    exact ⟨_, hPk k hk', rfl, Or.inr rfl⟩
  · rw [hL, hH]
  · exact Or.inl (by rw [hL])
  · exact Or.inr (by rw [hK, hL])
  · intro hv; rw [hval] at hv; exact absurd hv (by decide)
  · intro j hj _; exact hPk _ (by omega)
  · intro _
    have := Nat.mod_lt post.slot.toNat hspe
    exact hPk _ (by omega)

/-- **The crossing as the generators drive it** (`crossFromFulu`). -/
theorem crossFromFulu_inv (hspe : 0 < P.SLOTS_PER_EPOCH) {ctx : Ctx}
    {pre : JauneConsensus.BeaconState P .fulu} {post : GSt P}
    (h : JauneConsensus.Gloas.crossFromFulu ctx pre = .ok post) :
    BuilderPubkeysUnique post ∧ PendingRefsInRange post ∧ ExitedHaveNoPending post ∧
      PendingCovered post ∧ NextBuilderIndexInRange post ∧ NoLiveWeightOnLatestBid post ∧
      LatestBidCoherence post ∧ LatestBidBuilderActive post ∧ FutureEmpty post := by
  unfold JauneConsensus.Gloas.crossFromFulu at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  simp only [] at h
  split at h
  · obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    exact upgradeToGloas_inv hspe h
  · obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
    exact upgradeToGloas_inv hspe h

end JauneConsensus.Facts.Gloas.Inv
