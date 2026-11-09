import JauneConsensus.GloasBlock
import JauneConsensus.Facts.Gloas.Frame

/-!
# Builder request classification (goal `eip8282-gloas-cross-layer-v1`, B1/B3/B4)

The two EIP-8282 builder requests of `v1.7.0-beta.4` (`process_builder_deposit_request`,
CL:2322; `process_builder_exit_request`, CL:2365), each factored into a classification of the
request at its state (`classifyBuilderDeposit`, `classifyBuilderExit`, the spec's branches in the
spec's order) and the effect of that classification (`applyBuilderDepositOutcome`,
`applyBuilderExitOutcome`). The factoring lemmas `processBuilderDepositRequest_eq` and
`processBuilderExitRequest_eq` state that the real U4 functions (`GloasOperations.lean`) are the
classification followed by its effect, error for error. The `_meaning` theorems state each
outcome as an iff against the spec conditions (frozen statements rev 3.1, B2 and B4).
-/

namespace JauneConsensus.Facts.Gloas

open JauneConsensus JauneConsensus.Facts

variable {P : Preset}

/-! ## Shared vocabulary -/

/-- `builder_pubkeys.index(pubkey)` (CL:2338, 2373): the first builder with that pubkey. -/
def firstMatch (builders : ProgressiveListR JauneConsensus.Gloas.Builder) (pk : BLSPubkey) :
    Option Nat :=
  builders.toArray.findIdx? (·.pubkey == pk)

/-- The pubkey at index `i` changed (append or reuse). -/
def BuilderCreated (st st' : JauneConsensus.Gloas.BeaconState P) (i : Nat) : Prop :=
  (st'.builders.toArray[i]?).isSome ∧
    (st.builders.toArray[i]?).map (·.pubkey) ≠ (st'.builders.toArray[i]?).map (·.pubkey)

/-- `withdrawable_epoch` leaves `FAR_FUTURE_EPOCH` at the same incarnation. -/
def ExitInitiated (st st' : JauneConsensus.Gloas.BeaconState P) (i : Nat) : Prop :=
  ∃ b b', st.builders.toArray[i]? = some b ∧ st'.builders.toArray[i]? = some b' ∧
    b.pubkey = b'.pubkey ∧ b.withdrawable_epoch = FAR_FUTURE_EPOCH ∧
    b'.withdrawable_epoch ≠ FAR_FUTURE_EPOCH

/-- The builder-deposit signing domain: `compute_domain(DOMAIN_BUILDER_DEPOSIT)` with the default
fork version and the zero genesis root (CL:2282). -/
def builderDepositDomain (ccfg : Config) : Option Domain :=
  (computeDomainDefault ccfg JauneConsensus.Gloas.DOMAIN_BUILDER_DEPOSIT).toOption

/-- The signed message of a builder deposit (CL:2276). -/
def builderDepositMessage (r : JauneConsensus.Gloas.BuilderDepositRequest) : DepositMessage :=
  { pubkey := r.pubkey, withdrawal_credentials := r.withdrawal_credentials, amount := r.amount }

/-! ## Builder deposits -/

/-- The record `add_builder_to_registry` writes (CL:2297-2318): `version = PAYLOAD_BUILDER_VERSION`
(`0`), `withdrawable_epoch = FAR_FUTURE_EPOCH`. -/
def freshBuilder (pubkey : BLSPubkey) (addr : ExecutionAddress) (amount : Gwei) (epoch : Epoch) :
    JauneConsensus.Gloas.Builder :=
  { pubkey, version := JauneConsensus.Gloas.PAYLOAD_BUILDER_VERSION, execution_address := addr,
    balance := amount, deposit_epoch := epoch, withdrawable_epoch := FAR_FUTURE_EPOCH }

/-- One builder deposit request at its state, in the spec's order (CL:2334-2361). -/
inductive BuilderDepositOutcome
  /-- `withdrawal_credentials[:1] != BUILDER_WITHDRAWAL_PREFIX`, checked first. -/
  | ignoredPrefix
  /-- Known pubkey (first match `i`): `balance += amount`; `reset` iff the builder is exited and
  swept (`withdrawable_epoch != FAR_FUTURE_EPOCH and balance == 0`). -/
  | topUp (i : Nat) (amount : U64) (reset : Bool)
  /-- New pubkey, `not is_valid_builder_deposit_signature(request)`. -/
  | ignoredBadSignature
  /-- New pubkey, valid signature: registered at `i = get_index_for_new_builder(state)`. -/
  | register (i : Nat) (amount : U64)
  deriving DecidableEq, Repr

/-- The classification of a builder deposit request: the reads and checks of
`process_builder_deposit_request`, in its order, without its writes. -/
def classifyBuilderDeposit (ccfg : Config) (bls : Bool) (m : JauneConsensus.Gloas.BeaconState P)
    (r : JauneConsensus.Gloas.BuilderDepositRequest) : M BuilderDepositOutcome := do
  if !JauneConsensus.Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials then
    return .ignoredPrefix
  match firstMatch m.builders r.pubkey with
  | none =>
    if ← JauneConsensus.Gloas.isValidBuilderDepositSignature { cfg := ccfg, blsActive := bls } r then
      let _ ← JauneConsensus.Gloas.addressOfCredentials r.withdrawal_credentials
      return .register (← JauneConsensus.Gloas.getIndexForNewBuilder m).toNat r.amount
    else return .ignoredBadSignature
  | some i =>
    let b ← m.builders.get i "process_builder_deposit_request"
    return .topUp i r.amount (b.withdrawable_epoch != FAR_FUTURE_EPOCH && b.balance == U64.zero)

/-- The top-up branch of `process_builder_deposit_request` at index `i` (CL:2348-2361). -/
def topUpBuilder (ccfg : Config) (m : JauneConsensus.Gloas.BeaconState P) (i : Nat)
    (amount : Gwei) : M (JauneConsensus.Gloas.BeaconState P) := do
  let site := "process_builder_deposit_request"
  let builder ← m.builders.get i site
  let builder ← (if builder.withdrawable_epoch != FAR_FUTURE_EPOCH && builder.balance == U64.zero
    then do
      let epoch ← JauneConsensus.Gloas.getCurrentEpoch m
      pure { builder with
        withdrawable_epoch := ← epoch.add? (← c64 ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY) site }
    else pure builder)
  let balance ← builder.balance.add? amount site
  pure { m with builders := ← m.builders.set i { builder with balance } site }

/-- The effect of a classified builder deposit request. -/
def applyBuilderDepositOutcome (ccfg : Config) (m : JauneConsensus.Gloas.BeaconState P)
    (r : JauneConsensus.Gloas.BuilderDepositRequest) :
    BuilderDepositOutcome → M (JauneConsensus.Gloas.BeaconState P)
  | .ignoredPrefix => pure m
  | .ignoredBadSignature => pure m
  | .topUp i _ _ => topUpBuilder ccfg m i r.amount
  | .register _ _ => do
    JauneConsensus.Gloas.addBuilderToRegistry m r.pubkey JauneConsensus.Gloas.PAYLOAD_BUILDER_VERSION
      (← JauneConsensus.Gloas.addressOfCredentials r.withdrawal_credentials) r.amount m.slot

theorem isValidBuilderDepositSignature_ctx (ctx : Ctx)
    (r : JauneConsensus.Gloas.BuilderDepositRequest) :
    JauneConsensus.Gloas.isValidBuilderDepositSignature ctx r =
      JauneConsensus.Gloas.isValidBuilderDepositSignature
        { cfg := ctx.cfg, blsActive := ctx.blsActive } r := rfl

/-- `process_builder_deposit_request` is its classification followed by its effect. -/
theorem processBuilderDepositRequest_eq (ctx : Ctx) (m : JauneConsensus.Gloas.BeaconState P)
    (r : JauneConsensus.Gloas.BuilderDepositRequest) :
    JauneConsensus.Gloas.processBuilderDepositRequest ctx m r =
      classifyBuilderDeposit ctx.cfg ctx.blsActive m r >>= applyBuilderDepositOutcome ctx.cfg m r := by
  unfold JauneConsensus.Gloas.processBuilderDepositRequest classifyBuilderDeposit
  rw [isValidBuilderDepositSignature_ctx]
  by_cases hp : JauneConsensus.Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials
  · simp only [hp, Bool.not_true, Bool.false_eq_true, if_false]
    cases hfm : firstMatch m.builders r.pubkey with
    | none =>
      unfold firstMatch at hfm
      rw [hfm]
      cases hv : JauneConsensus.Gloas.isValidBuilderDepositSignature
          { cfg := ctx.cfg, blsActive := ctx.blsActive } r with
      | error e => rfl
      | ok v =>
        cases v with
        | false => rfl
        | true =>
          cases ha : JauneConsensus.Gloas.addressOfCredentials r.withdrawal_credentials with
          | error e => simp [bind, Except.bind, ha]
          | ok a =>
            cases hi : JauneConsensus.Gloas.getIndexForNewBuilder m with
            | error e =>
              simp only [bind, Except.bind, ha, hi, pure, Except.pure, applyBuilderDepositOutcome,
                JauneConsensus.Gloas.addBuilderToRegistry, if_true]
            | ok idx =>
              simp only [bind, Except.bind, ha, hi, pure, Except.pure, applyBuilderDepositOutcome,
                if_true]
    | some i =>
      unfold firstMatch at hfm
      rw [hfm]
      cases hg : m.builders.get i "process_builder_deposit_request" with
      | error e => simp [bind, Except.bind, hg]
      | ok b =>
        simp only [bind, Except.bind, hg, pure, Except.pure, applyBuilderDepositOutcome, topUpBuilder]
        by_cases hC : (b.withdrawable_epoch != FAR_FUTURE_EPOCH && b.balance == U64.zero) = true
        · simp only [hC, ↓reduceIte]
          cases JauneConsensus.Gloas.getCurrentEpoch m with
          | error e => rfl
          | ok e =>
            dsimp only
            cases c64 ctx.cfg.MIN_BUILDER_WITHDRAWABILITY_DELAY with
            | error _ => rfl
            | ok d =>
              dsimp only
              cases U64.add? e d "process_builder_deposit_request" with
              | error _ => rfl
              | ok w => rfl
        · simp only [hC, ↓reduceIte, Bool.false_eq_true]
  · simp only [Bool.not_eq_true] at hp
    simp [hp, pure, Except.pure, bind, Except.bind, applyBuilderDepositOutcome]

/-! ## Builder exits -/

/-- Why a builder is not active (CL:1054-1065, `is_active_builder`). -/
inductive NotActive
  /-- `deposit_epoch >= finalized_checkpoint.epoch`. -/
  | notFinalized
  /-- `withdrawable_epoch != FAR_FUTURE_EPOCH`. -/
  | alreadyExiting
  deriving DecidableEq, Repr

/-- One builder exit request at its state, the spec's reasons in the spec's order
(CL:2368-2384). -/
inductive BuilderExitOutcome
  | unknownPubkey
  | notActive (why : NotActive)
  | wrongSource
  | pendingBalance
  | initiate (i : Nat)
  deriving DecidableEq, Repr

/-- The classification of a builder exit request: the reads and checks of
`process_builder_exit_request`, in its order, without its write. -/
def classifyBuilderExit (_ccfg : Config) (m : JauneConsensus.Gloas.BeaconState P)
    (r : JauneConsensus.Gloas.BuilderExitRequest) : M BuilderExitOutcome := do
  let some i := firstMatch m.builders r.pubkey | return .unknownPubkey
  let builderIndex ← U64.ofNat? i "BuilderIndex"
  let builder ← m.builders.get i "process_builder_exit_request"
  if !(← JauneConsensus.Gloas.isActiveBuilder m builderIndex) then
    return .notActive (if builder.deposit_epoch < m.finalized_checkpoint.epoch then .alreadyExiting
      else .notFinalized)
  if builder.execution_address != r.source_address then return .wrongSource
  if (← JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder m builderIndex) != U64.zero then
    return .pendingBalance
  return .initiate i

/-- The effect of a classified builder exit request: only `initiate` writes. -/
def applyBuilderExitOutcome (ccfg : Config) (m : JauneConsensus.Gloas.BeaconState P)
    (_r : JauneConsensus.Gloas.BuilderExitRequest) :
    BuilderExitOutcome → M (JauneConsensus.Gloas.BeaconState P)
  | .initiate i => do
    JauneConsensus.Gloas.initiateBuilderExit ccfg m (← U64.ofNat? i "BuilderIndex")
  | _ => pure m

/-- `process_builder_exit_request` is its classification followed by its effect. -/
theorem processBuilderExitRequest_eq (ccfg : Config) (m : JauneConsensus.Gloas.BeaconState P)
    (r : JauneConsensus.Gloas.BuilderExitRequest) :
    JauneConsensus.Gloas.processBuilderExitRequest ccfg m r =
      classifyBuilderExit ccfg m r >>= applyBuilderExitOutcome ccfg m r := by
  unfold JauneConsensus.Gloas.processBuilderExitRequest classifyBuilderExit
  cases hfm : firstMatch m.builders r.pubkey with
  | none =>
    unfold firstMatch at hfm
    simp [hfm, pure, Except.pure, bind, Except.bind, applyBuilderExitOutcome]
  | some i =>
    unfold firstMatch at hfm
    simp only [hfm]
    cases hb : U64.ofNat? i "BuilderIndex" with
    | error e => rfl
    | ok bi =>
      cases hg : m.builders.get i "process_builder_exit_request" with
      | error e => simp [bind, Except.bind, hb, hg]
      | ok b =>
        cases ha : JauneConsensus.Gloas.isActiveBuilder m bi with
        | error e => simp [bind, Except.bind, hb, hg, ha]
        | ok act =>
          cases act with
          | false => simp [bind, Except.bind, hb, hg, ha, pure, Except.pure, applyBuilderExitOutcome]
          | true =>
            by_cases hs : b.execution_address = r.source_address
            · cases hpb : JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder m bi with
              | error e => simp [bind, Except.bind, hb, hg, ha, hs, hpb]
              | ok pb =>
                by_cases hz : pb = U64.zero
                · simp [bind, Except.bind, hb, hg, ha, hs, hpb, hz, pure, Except.pure,
                    applyBuilderExitOutcome]
                · simp [bind, Except.bind, hb, hg, ha, hs, hpb, hz, pure, Except.pure,
                    applyBuilderExitOutcome]
            · simp [bind, Except.bind, hb, hg, ha, hs, pure, Except.pure, applyBuilderExitOutcome]

/-! ## List and equality plumbing -/

theorem pl_get_ok {s : Spine} {α : Type} {xs : ProgressiveListS s α} {i : Nat} {site : String}
    {x : α} : xs.get i site = .ok x ↔ xs.toArray[i]? = some x := by
  unfold ProgressiveListS.get getAt
  cases h : xs.toArray[i]? with
  | none => constructor <;> intro hh <;> cases hh
  | some y => constructor <;> intro hh <;> cases hh <;> rfl

theorem pl_set_ok {s : Spine} {α : Type} {xs ys : ProgressiveListS s α} {i : Nat} {v : α}
    {site : String} (h : xs.set i v site = .ok ys) :
    ys.toArray.size = xs.toArray.size ∧ ys.toArray[i]? = some v ∧
      ∀ j, j ≠ i → ys.toArray[j]? = xs.toArray[j]? := by
  unfold ProgressiveListS.set at h
  split at h
  · rename_i hi
    cases h
    refine ⟨by simp, by simp [hi], fun j hj => ?_⟩
    simp [Array.getElem?_set, Ne.symm hj]
  · cases h

theorem pl_setOrAppend_ok {s : Spine} {α : Type} {xs ys : ProgressiveListS s α} {idx : U64}
    {v : α} {site : String} (h : xs.setOrAppend idx v site = .ok ys) :
    xs.toArray.size ≤ ys.toArray.size ∧ ys.toArray[idx.toNat]? = some v ∧
      ∀ j, j ≠ idx.toNat → ys.toArray[j]? = xs.toArray[j]? := by
  unfold ProgressiveListS.setOrAppend at h
  split at h
  · rename_i hc
    have hc' : idx.toNat = xs.toArray.size := by
      simpa [ProgressiveListS.length] using hc
    cases h
    refine ⟨by simp [ProgressiveListS.push], by simp [ProgressiveListS.push, hc'], fun j hj => ?_⟩
    simp only [ProgressiveListS.push, Array.getElem?_push]
    rw [if_neg (by omega)]
  · obtain ⟨h1, h2, h3⟩ := pl_set_ok h
    exact ⟨by omega, h2, h3⟩

theorem pubkey_beq_iff {a b : BLSPubkey} : (a == b) = true ↔ a = b := by
  change (a.toArray == b.toArray) = true ↔ a = b
  rw [beq_iff_eq]
  constructor
  · intro h
    cases a; cases b
    simp only at h
    subst h
    rfl
  · intro h; rw [h]

theorem firstMatch_none_iff {bs : ProgressiveListR JauneConsensus.Gloas.Builder} {pk : BLSPubkey} :
    firstMatch bs pk = none ↔ ∀ b ∈ bs.toArray, b.pubkey ≠ pk := by
  unfold firstMatch
  rw [Array.findIdx?_eq_none_iff]
  constructor
  · intro h b hb heq
    have := h b hb
    rw [heq] at this
    have h2 : (pk == pk) = true := pubkey_beq_iff.mpr rfl
    rw [h2] at this
    cases this
  · intro h b hb
    cases hh : (b.pubkey == pk) with
    | false => rfl
    | true => exact absurd (pubkey_beq_iff.mp hh) (h b hb)

theorem firstMatch_some {bs : ProgressiveListR JauneConsensus.Gloas.Builder} {pk : BLSPubkey}
    {i : Nat} (h : firstMatch bs pk = some i) :
    (∃ b, bs.toArray[i]? = some b ∧ b.pubkey = pk) ∧
      ∀ j, j < i → ∀ b', bs.toArray[j]? = some b' → b'.pubkey ≠ pk := by
  unfold firstMatch at h
  rw [Array.findIdx?_eq_some_iff_getElem] at h
  obtain ⟨hi, hp, hlt⟩ := h
  refine ⟨⟨bs.toArray[i], by simp [hi], pubkey_beq_iff.mp hp⟩, fun j hj b' hb' heq => ?_⟩
  have hjs : j < bs.toArray.size := Nat.lt_trans hj hi
  have hb'' : bs.toArray[j] = b' := by
    rw [Array.getElem?_eq_getElem hjs] at hb'
    exact Option.some.inj hb'
  apply hlt j hj
  rw [hb'']
  exact pubkey_beq_iff.mpr heq

theorem U64_eq_of_ofNat? {n : Nat} {site site' : String} {a b : U64}
    (ha : U64.ofNat? n site = .ok a) (hb : U64.ofNat? n site' = .ok b) : a = b := by
  unfold U64.ofNat? at ha hb
  split at ha
  · cases ha
    rw [if_pos ‹_›] at hb
    cases hb
    rfl
  · cases ha

theorem builderDepositDomain_eq_some {ccfg : Config} {dom : Domain} :
    builderDepositDomain ccfg = some dom ↔
      computeDomainDefault ccfg JauneConsensus.Gloas.DOMAIN_BUILDER_DEPOSIT = .ok dom := by
  unfold builderDepositDomain
  cases computeDomainDefault ccfg JauneConsensus.Gloas.DOMAIN_BUILDER_DEPOSIT <;>
    simp [Except.toOption]

theorem isValidBuilderDepositSignature_ok {ccfg : Config} {bls : Bool}
    {r : JauneConsensus.Gloas.BuilderDepositRequest} {v : Bool} :
    JauneConsensus.Gloas.isValidBuilderDepositSignature { cfg := ccfg, blsActive := bls } r = .ok v ↔
      ∃ dom, builderDepositDomain ccfg = some dom ∧
        blsVerify bls r.pubkey (computeSigningRoot (builderDepositMessage r) dom) r.signature = v := by
  unfold JauneConsensus.Gloas.isValidBuilderDepositSignature
  rw [bind_eq_ok_iff]
  constructor
  · rintro ⟨dom, hd, hv⟩
    cases hv
    exact ⟨dom, builderDepositDomain_eq_some.mpr hd, rfl⟩
  · rintro ⟨dom, hd, hv⟩
    exact ⟨dom, builderDepositDomain_eq_some.mp hd, by rw [← hv]; rfl⟩

theorem isActiveBuilder_of_get {m : JauneConsensus.Gloas.BeaconState P} {bi : U64}
    {b : JauneConsensus.Gloas.Builder} (h : m.builders.toArray[bi.toNat]? = some b) :
    JauneConsensus.Gloas.isActiveBuilder m bi =
      .ok (decide (b.deposit_epoch < m.finalized_checkpoint.epoch) &&
        b.withdrawable_epoch == FAR_FUTURE_EPOCH) := by
  unfold JauneConsensus.Gloas.isActiveBuilder
  rw [show m.builders.get bi.toNat "is_active_builder" = .ok b from pl_get_ok.mpr h]
  rfl

/-! ## Inversions of the classifications -/

/-- What a successful exit classification read and decided. -/
theorem classifyBuilderExit_inv {ccfg : Config} {m : JauneConsensus.Gloas.BeaconState P}
    {r : JauneConsensus.Gloas.BuilderExitRequest} {o : BuilderExitOutcome}
    (hc : classifyBuilderExit ccfg m r = .ok o) :
    (firstMatch m.builders r.pubkey = none ∧ o = .unknownPubkey) ∨
    ∃ i b bi, firstMatch m.builders r.pubkey = some i ∧ m.builders.toArray[i]? = some b ∧
      U64.ofNat? i "BuilderIndex" = .ok bi ∧
      ((¬ (b.deposit_epoch < m.finalized_checkpoint.epoch ∧
            b.withdrawable_epoch = FAR_FUTURE_EPOCH) ∧
          o = .notActive (if b.deposit_epoch < m.finalized_checkpoint.epoch then .alreadyExiting
            else .notFinalized)) ∨
       ((b.deposit_epoch < m.finalized_checkpoint.epoch ∧
            b.withdrawable_epoch = FAR_FUTURE_EPOCH) ∧ b.execution_address ≠ r.source_address ∧
          o = .wrongSource) ∨
       ((b.deposit_epoch < m.finalized_checkpoint.epoch ∧
            b.withdrawable_epoch = FAR_FUTURE_EPOCH) ∧ b.execution_address = r.source_address ∧
          ∃ p, JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder m bi = .ok p ∧
            ((p ≠ U64.zero ∧ o = .pendingBalance) ∨ (p = U64.zero ∧ o = .initiate i)))) := by
  unfold classifyBuilderExit at hc
  cases hfm : firstMatch m.builders r.pubkey with
  | none =>
    rw [hfm] at hc
    cases hc
    exact Or.inl ⟨rfl, rfl⟩
  | some i =>
    rw [hfm] at hc
    obtain ⟨bi, hbi, hc⟩ := bind_eq_ok_iff.mp hc
    obtain ⟨b, hg, hc⟩ := bind_eq_ok_iff.mp hc
    have hb := pl_get_ok.mp hg
    have hbi' : bi.toNat = i := U64.toNat_ofNat? hbi
    obtain ⟨act, hact, hc⟩ := bind_eq_ok_iff.mp hc
    rw [isActiveBuilder_of_get (hbi' ▸ hb)] at hact
    cases hact
    refine Or.inr ⟨i, b, bi, rfl, hb, hbi, ?_⟩
    by_cases ha : b.deposit_epoch < m.finalized_checkpoint.epoch ∧
        b.withdrawable_epoch = FAR_FUTURE_EPOCH
    · have hat : (decide (b.deposit_epoch < m.finalized_checkpoint.epoch) &&
          b.withdrawable_epoch == FAR_FUTURE_EPOCH) = true := by
        simp [ha.1, ha.2]
      rw [hat] at hc
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
      by_cases hs : b.execution_address = r.source_address
      · simp only [hs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hc
        obtain ⟨p, hp, hc⟩ := bind_eq_ok_iff.mp hc
        refine Or.inr (Or.inr ⟨ha, hs, p, hp, ?_⟩)
        by_cases hz : p = U64.zero
        · simp only [hz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at hc
          cases hc
          exact Or.inr ⟨hz, rfl⟩
        · have hz' : (p != U64.zero) = true := by simp [hz]
          simp only [hz', ↓reduceIte] at hc
          cases hc
          exact Or.inl ⟨hz, rfl⟩
      · have hs' : (b.execution_address != r.source_address) = true := by simp [hs]
        simp only [hs', ↓reduceIte] at hc
        cases hc
        exact Or.inr (Or.inl ⟨ha, hs, rfl⟩)
    · have haf : (decide (b.deposit_epoch < m.finalized_checkpoint.epoch) &&
          b.withdrawable_epoch == FAR_FUTURE_EPOCH) = false := by
        cases h1 : decide (b.deposit_epoch < m.finalized_checkpoint.epoch) <;>
          cases h2 : (b.withdrawable_epoch == FAR_FUTURE_EPOCH) <;> simp_all
      rw [haf] at hc
      simp only [Bool.not_false, ↓reduceIte] at hc
      cases hc
      exact Or.inl ⟨ha, rfl⟩

/-- What a successful deposit classification read and decided. -/
theorem classifyBuilderDeposit_inv {ccfg : Config} {bls : Bool}
    {m : JauneConsensus.Gloas.BeaconState P} {r : JauneConsensus.Gloas.BuilderDepositRequest}
    {o : BuilderDepositOutcome} (hc : classifyBuilderDeposit ccfg bls m r = .ok o) :
    (JauneConsensus.Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials = false ∧
      o = .ignoredPrefix) ∨
    (JauneConsensus.Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials = true ∧
      ∃ i b, firstMatch m.builders r.pubkey = some i ∧ m.builders.toArray[i]? = some b ∧
        o = .topUp i r.amount (b.withdrawable_epoch != FAR_FUTURE_EPOCH && b.balance == U64.zero)) ∨
    (JauneConsensus.Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials = true ∧
      firstMatch m.builders r.pubkey = none ∧ ∃ dom, builderDepositDomain ccfg = some dom ∧
        ((blsVerify bls r.pubkey (computeSigningRoot (builderDepositMessage r) dom) r.signature = false ∧
            o = .ignoredBadSignature) ∨
         (blsVerify bls r.pubkey (computeSigningRoot (builderDepositMessage r) dom) r.signature = true ∧
            ∃ addr idx, JauneConsensus.Gloas.addressOfCredentials r.withdrawal_credentials = .ok addr ∧
              JauneConsensus.Gloas.getIndexForNewBuilder m = .ok idx ∧
              o = .register idx.toNat r.amount))) := by
  unfold classifyBuilderDeposit at hc
  cases hp : JauneConsensus.Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials with
  | false =>
    simp only [hp, Bool.not_false, ↓reduceIte] at hc
    cases hc
    exact Or.inl ⟨rfl, rfl⟩
  | true =>
    simp only [hp, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hc
    cases hfm : firstMatch m.builders r.pubkey with
    | none =>
      rw [hfm] at hc
      obtain ⟨v, hv, hc⟩ := bind_eq_ok_iff.mp hc
      obtain ⟨dom, hd, hvd⟩ := isValidBuilderDepositSignature_ok.mp hv
      refine Or.inr (Or.inr ⟨rfl, rfl, dom, hd, ?_⟩)
      cases v with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at hc
        cases hc
        exact Or.inl ⟨hvd, rfl⟩
      | true =>
        simp only [↓reduceIte] at hc
        obtain ⟨addr, ha, hc⟩ := bind_eq_ok_iff.mp hc
        obtain ⟨idx, hi, hc⟩ := bind_eq_ok_iff.mp hc
        cases hc
        exact Or.inr ⟨hvd, addr, idx, ha, hi, rfl⟩
    | some i =>
      rw [hfm] at hc
      obtain ⟨b, hg, hc⟩ := bind_eq_ok_iff.mp hc
      cases hc
      exact Or.inr (Or.inl ⟨rfl, i, b, rfl, pl_get_ok.mp hg, rfl⟩)


/-! ## Meaning of the exit classification (B4; shared with B3) -/

/-- **`classifyBuilderExit_meaning`.** Each reason, in the spec's order (CL:2368-2384), is an iff
against the spec's conditions (`is_active_builder`, CL:1054-1065, unfolded into its two reasons).
`i` is the first match (`builder_pubkeys.index`), so an exit request resolves to the first builder
with its pubkey (G3-01's resolution clause, last conjunct). -/
theorem classifyBuilderExit_meaning {ccfg : Config} {m : JauneConsensus.Gloas.BeaconState P}
    {r : JauneConsensus.Gloas.BuilderExitRequest} {o : BuilderExitOutcome}
    (hc : classifyBuilderExit ccfg m r = .ok o) :
    (o = .unknownPubkey ↔ ∀ b ∈ m.builders.toArray, b.pubkey ≠ r.pubkey) ∧
    (o = .notActive .notFinalized ↔ ∃ i b, firstMatch m.builders r.pubkey = some i ∧
      m.builders.toArray[i]? = some b ∧ m.finalized_checkpoint.epoch ≤ b.deposit_epoch) ∧
    (o = .notActive .alreadyExiting ↔ ∃ i b, firstMatch m.builders r.pubkey = some i ∧
      m.builders.toArray[i]? = some b ∧ b.deposit_epoch < m.finalized_checkpoint.epoch ∧
      b.withdrawable_epoch ≠ FAR_FUTURE_EPOCH) ∧
    (o = .wrongSource ↔ ∃ i b bi, firstMatch m.builders r.pubkey = some i ∧
      m.builders.toArray[i]? = some b ∧ U64.ofNat? i "BuilderIndex" = .ok bi ∧
      JauneConsensus.Gloas.isActiveBuilder m bi = .ok true ∧
      b.execution_address ≠ r.source_address) ∧
    (o = .pendingBalance ↔ ∃ i b bi, firstMatch m.builders r.pubkey = some i ∧
      m.builders.toArray[i]? = some b ∧ U64.ofNat? i "BuilderIndex" = .ok bi ∧
      JauneConsensus.Gloas.isActiveBuilder m bi = .ok true ∧
      b.execution_address = r.source_address ∧
      JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder m bi ≠ .ok U64.zero) ∧
    (∀ i, o = .initiate i ↔ ∃ b bi, firstMatch m.builders r.pubkey = some i ∧
      m.builders.toArray[i]? = some b ∧ U64.ofNat? i "BuilderIndex" = .ok bi ∧
      JauneConsensus.Gloas.isActiveBuilder m bi = .ok true ∧
      b.execution_address = r.source_address ∧
      JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder m bi = .ok U64.zero) ∧
    (∀ i, o = .initiate i → ∀ j, j < i → ∀ b', m.builders.toArray[j]? = some b' →
      b'.pubkey ≠ r.pubkey) := by
  rcases classifyBuilderExit_inv hc with ⟨hfm, rfl⟩ | ⟨i, b, bi, hfm, hb, hbi, hcase⟩
  · have hall := firstMatch_none_iff.mp hfm
    refine ⟨⟨fun _ => hall, fun _ => rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact ⟨fun h => (by cases h), fun ⟨_, _, h, _⟩ => by rw [hfm] at h; cases h⟩
    · exact ⟨fun h => (by cases h), fun ⟨_, _, h, _⟩ => by rw [hfm] at h; cases h⟩
    · exact ⟨fun h => (by cases h), fun ⟨_, _, _, h, _⟩ => by rw [hfm] at h; cases h⟩
    · exact ⟨fun h => (by cases h), fun ⟨_, _, _, h, _⟩ => by rw [hfm] at h; cases h⟩
    · exact fun _ => ⟨fun h => (by cases h), fun ⟨_, _, h, _⟩ => by rw [hfm] at h; cases h⟩
    · intro _ h; cases h
  · have hbn : bi.toNat = i := U64.toNat_ofNat? hbi
    have hA := isActiveBuilder_of_get (m := m) (hbn ▸ hb)
    have hAt : JauneConsensus.Gloas.isActiveBuilder m bi = .ok true ↔
        (b.deposit_epoch < m.finalized_checkpoint.epoch ∧
          b.withdrawable_epoch = FAR_FUTURE_EPOCH) := by
      rw [hA]; simp
    obtain ⟨⟨b0, hb0, hpk0⟩, hfirst⟩ := firstMatch_some hfm
    have hb0b : b0 = b := by rw [hb] at hb0; cases hb0; rfl
    subst hb0b
    have col2 : ∀ Q : JauneConsensus.Gloas.Builder → Prop,
        (∃ i' b', firstMatch m.builders r.pubkey = some i' ∧ m.builders.toArray[i']? = some b' ∧
          Q b') ↔ Q b0 := by
      intro Q
      constructor
      · rintro ⟨i', b', h1, h2, hq⟩
        rw [hfm] at h1; cases h1; rw [hb] at h2; cases h2; exact hq
      · intro hq; exact ⟨i, b0, hfm, hb, hq⟩
    have col3 : ∀ Q : JauneConsensus.Gloas.Builder → U64 → Prop,
        (∃ i' b' bi', firstMatch m.builders r.pubkey = some i' ∧ m.builders.toArray[i']? = some b' ∧
          U64.ofNat? i' "BuilderIndex" = .ok bi' ∧ Q b' bi') ↔ Q b0 bi := by
      intro Q
      constructor
      · rintro ⟨i', b', bi', h1, h2, h3, hq⟩
        rw [hfm] at h1; cases h1; rw [hb] at h2; cases h2
        rw [hbi] at h3; cases h3; exact hq
      · intro hq; exact ⟨i, b0, bi, hfm, hb, hbi, hq⟩
    have col3i : ∀ (i' : Nat) (Q : JauneConsensus.Gloas.Builder → U64 → Prop),
        (∃ b' bi', firstMatch m.builders r.pubkey = some i' ∧ m.builders.toArray[i']? = some b' ∧
          U64.ofNat? i' "BuilderIndex" = .ok bi' ∧ Q b' bi') ↔ (i' = i ∧ Q b0 bi) := by
      intro i' Q
      constructor
      · rintro ⟨b', bi', h1, h2, h3, hq⟩
        rw [hfm] at h1; cases h1; rw [hb] at h2; cases h2
        rw [hbi] at h3; cases h3; exact ⟨rfl, hq⟩
      · rintro ⟨rfl, hq⟩; exact ⟨b0, bi, hfm, hb, hbi, hq⟩
    have hnone : ¬ ∀ b ∈ m.builders.toArray, b.pubkey ≠ r.pubkey :=
      fun hall => hall b0 (Array.mem_of_getElem? hb) hpk0
    have hlt : ∀ x y : U64, ¬ (x < y ∧ y ≤ x) := by
      intro x y h; simp only [U64.lt_iff, U64.le_iff] at h; omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · constructor
      · intro ho; exfalso
        rcases hcase with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ <;> cases ho
      · intro hall; exact absurd hall hnone
    · rw [col2 (fun b' => m.finalized_checkpoint.epoch ≤ b'.deposit_epoch)]
      try dsimp only
      rcases hcase with ⟨hna, rfl⟩ | ⟨ha, hs, rfl⟩ | ⟨ha, hs, p, hp, ⟨hz, rfl⟩ | ⟨hz, rfl⟩⟩
      · by_cases hd : b0.deposit_epoch < m.finalized_checkpoint.epoch
        · rw [if_pos hd]
          exact ⟨fun h => (by cases h), fun h => absurd ⟨hd, h⟩ (hlt _ _)⟩
        · rw [if_neg hd]
          refine ⟨fun _ => ?_, fun _ => rfl⟩
          simp only [U64.lt_iff, U64.le_iff] at hd ⊢; omega
      all_goals exact ⟨fun h => (by cases h), fun h => absurd ⟨ha.1, h⟩ (hlt _ _)⟩
    · rw [col2 (fun b' => b'.deposit_epoch < m.finalized_checkpoint.epoch ∧
        b'.withdrawable_epoch ≠ FAR_FUTURE_EPOCH)]
      try dsimp only
      rcases hcase with ⟨hna, rfl⟩ | ⟨ha, hs, rfl⟩ | ⟨ha, hs, p, hp, ⟨hz, rfl⟩ | ⟨hz, rfl⟩⟩
      · by_cases hd : b0.deposit_epoch < m.finalized_checkpoint.epoch
        · rw [if_pos hd]
          exact ⟨fun _ => ⟨hd, fun hw => hna ⟨hd, hw⟩⟩, fun _ => rfl⟩
        · rw [if_neg hd]
          exact ⟨fun h => (by cases h), fun h => absurd h.1 hd⟩
      all_goals exact ⟨fun h => (by cases h), fun h => absurd ha.2 h.2⟩
    · rw [col3 (fun b' bi' => JauneConsensus.Gloas.isActiveBuilder m bi' = .ok true ∧
        b'.execution_address ≠ r.source_address)]
      try dsimp only
      rw [hAt]
      rcases hcase with ⟨hna, rfl⟩ | ⟨ha, hs, rfl⟩ | ⟨ha, hs, p, hp, ⟨hz, rfl⟩ | ⟨hz, rfl⟩⟩
      · exact ⟨fun h => (by cases h), fun h => absurd h.1 hna⟩
      · exact ⟨fun _ => ⟨ha, hs⟩, fun _ => rfl⟩
      all_goals exact ⟨fun h => (by cases h), fun h => absurd hs h.2⟩
    · rw [col3 (fun b' bi' => JauneConsensus.Gloas.isActiveBuilder m bi' = .ok true ∧
        b'.execution_address = r.source_address ∧
        JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder m bi' ≠ .ok U64.zero)]
      try dsimp only
      rw [hAt]
      rcases hcase with ⟨hna, rfl⟩ | ⟨ha, hs, rfl⟩ | ⟨ha, hs, p, hp, ⟨hz, rfl⟩ | ⟨hz, rfl⟩⟩
      · exact ⟨fun h => (by cases h), fun h => absurd h.1 hna⟩
      · exact ⟨fun h => (by cases h), fun h => absurd h.2.1 hs⟩
      · refine ⟨fun _ => ⟨ha, hs, ?_⟩, fun _ => rfl⟩
        rw [hp]; intro he; cases he; exact hz rfl
      · refine ⟨fun h => (by cases h), fun h => absurd ?_ h.2.2⟩
        rw [hp, hz]
    · intro i'
      rw [col3i i' (fun b' bi' => JauneConsensus.Gloas.isActiveBuilder m bi' = .ok true ∧
        b'.execution_address = r.source_address ∧
        JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder m bi' = .ok U64.zero)]
      try dsimp only
      rw [hAt]
      rcases hcase with ⟨hna, rfl⟩ | ⟨ha, hs, rfl⟩ | ⟨ha, hs, p, hp, ⟨hz, rfl⟩ | ⟨hz, rfl⟩⟩
      · exact ⟨fun h => (by cases h), fun h => absurd h.2.1 hna⟩
      · exact ⟨fun h => (by cases h), fun h => absurd h.2.2.1 hs⟩
      · refine ⟨fun h => (by cases h), fun h => ?_⟩
        rw [hp] at h
        cases h.2.2.2
        exact absurd rfl hz
      · refine ⟨fun h => ?_, fun h => by rw [h.1]⟩
        cases h
        exact ⟨rfl, ha, hs, by rw [hp, hz]⟩
    · intro i' ho
      rcases hcase with ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, _, ⟨_, rfl⟩ | ⟨_, rfl⟩⟩ <;> cases ho
      exact hfirst

/-- The effect of an exit classification: only `initiate i` writes, and it writes builder `i`'s
`withdrawable_epoch := current_epoch + MIN_BUILDER_WITHDRAWABILITY_DELAY` (CL:1526-1532) and
nothing else. An ignored request leaves the state unchanged (dropped, not re-queued). -/
theorem classifyBuilderExit_effect {ccfg : Config} {m m' : JauneConsensus.Gloas.BeaconState P}
    {r : JauneConsensus.Gloas.BuilderExitRequest} {o : BuilderExitOutcome}
    (hc : classifyBuilderExit ccfg m r = .ok o)
    (hp : JauneConsensus.Gloas.processBuilderExitRequest ccfg m r = .ok m') :
    ((∀ i, o ≠ .initiate i) → m' = m) ∧
    (∀ i, o = .initiate i → ∃ b e w, m.builders.toArray[i]? = some b ∧
      JauneConsensus.Gloas.getCurrentEpoch m = .ok e ∧
      w.toNat = e.toNat + ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY ∧
      m'.builders.toArray[i]? = some { b with withdrawable_epoch := w } ∧
      m'.builders.toArray.size = m.builders.toArray.size ∧
      (∀ j, j ≠ i → m'.builders.toArray[j]? = m.builders.toArray[j]?) ∧
      m' = { m with builders := m'.builders }) := by
  have hp' : applyBuilderExitOutcome ccfg m r o = .ok m' := by
    rw [processBuilderExitRequest_eq, hc] at hp; exact hp
  refine ⟨fun hne => ?_, fun i hi => ?_⟩
  · cases o with
    | initiate i => exact absurd rfl (hne i)
    | _ => cases hp'; rfl
  · subst hi
    unfold applyBuilderExitOutcome at hp'
    obtain ⟨bi, hbi, hp'⟩ := bind_eq_ok_iff.mp hp'
    have hbn : bi.toNat = i := U64.toNat_ofNat? hbi
    unfold JauneConsensus.Gloas.initiateBuilderExit at hp'
    obtain ⟨b, hg, hp'⟩ := bind_eq_ok_iff.mp hp'
    obtain ⟨e, he, hp'⟩ := bind_eq_ok_iff.mp hp'
    obtain ⟨d, hd, hp'⟩ := bind_eq_ok_iff.mp hp'
    obtain ⟨w, hw, hp'⟩ := bind_eq_ok_iff.mp hp'
    obtain ⟨bs, hbs, hp'⟩ := bind_eq_ok_iff.mp hp'
    cases hp'
    rw [hbn] at hg hbs
    obtain ⟨h1, h2, h3⟩ := pl_set_ok hbs
    refine ⟨b, e, w, pl_get_ok.mp hg, he, ?_, h2, h1, h3, rfl⟩
    rw [U64.toNat_add? hw, U64.toNat_ofNat? hd]

/-! ## Meaning of the deposit classification (B1, B2) -/

/-- **`classifyBuilderDeposit_meaning`.** Each outcome, in the spec's order (CL:2334-2361), is an
iff against the spec's conditions: the prefix first (so a known pubkey with other credentials is
ignored too), then a known pubkey's top-up (with the exited-and-swept reset rule), then a new
pubkey's signature under `DOMAIN_BUILDER_DEPOSIT` (CL:2268-2284), then its registration at
`get_index_for_new_builder`. -/
theorem classifyBuilderDeposit_meaning {ccfg : Config} {bls : Bool}
    {m : JauneConsensus.Gloas.BeaconState P} {r : JauneConsensus.Gloas.BuilderDepositRequest}
    {o : BuilderDepositOutcome} (hc : classifyBuilderDeposit ccfg bls m r = .ok o) :
    (o = .ignoredPrefix ↔
      JauneConsensus.Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials = false) ∧
    (∀ i a reset, o = .topUp i a reset ↔
      JauneConsensus.Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials = true ∧
      firstMatch m.builders r.pubkey = some i ∧ a = r.amount ∧
      ∃ b, m.builders.toArray[i]? = some b ∧
        (reset = true ↔ b.withdrawable_epoch ≠ FAR_FUTURE_EPOCH ∧ b.balance = U64.zero)) ∧
    (o = .ignoredBadSignature ↔
      JauneConsensus.Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials = true ∧
      (∀ b ∈ m.builders.toArray, b.pubkey ≠ r.pubkey) ∧
      ∃ dom, builderDepositDomain ccfg = some dom ∧
        blsVerify bls r.pubkey (computeSigningRoot (builderDepositMessage r) dom) r.signature = false) ∧
    (∀ i a, o = .register i a ↔
      JauneConsensus.Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials = true ∧
      (∀ b ∈ m.builders.toArray, b.pubkey ≠ r.pubkey) ∧
      (∃ dom, builderDepositDomain ccfg = some dom ∧
        blsVerify bls r.pubkey (computeSigningRoot (builderDepositMessage r) dom) r.signature = true) ∧
      a = r.amount ∧
      ∃ idx, JauneConsensus.Gloas.getIndexForNewBuilder m = .ok idx ∧ idx.toNat = i) := by
  rcases classifyBuilderDeposit_inv hc with ⟨hp, rfl⟩ | ⟨hp, i, b, hfm, hb, rfl⟩ |
    ⟨hp, hfm, dom, hd, ⟨hv, rfl⟩ | ⟨hv, addr, idx, ha, hi, rfl⟩⟩
  · refine ⟨⟨fun _ => hp, fun _ => rfl⟩, fun _ _ _ => ⟨fun h => (by cases h), fun h => ?_⟩,
      ⟨fun h => (by cases h), fun h => ?_⟩, fun _ _ => ⟨fun h => (by cases h), fun h => ?_⟩⟩ <;>
      (rw [hp] at h; cases h.1)
  · refine ⟨⟨fun h => (by cases h), fun h => by rw [hp] at h; cases h⟩, fun i' a reset => ⟨?_, ?_⟩,
      ⟨fun h => (by cases h), fun h => ?_⟩, fun _ _ => ⟨fun h => (by cases h), fun h => ?_⟩⟩
    · intro h
      cases h
      refine ⟨hp, hfm, rfl, b, hb, ?_⟩
      simp
    · rintro ⟨_, h1, rfl, b', h2, hr⟩
      rw [hfm] at h1; cases h1; rw [hb] at h2; cases h2
      have : (b.withdrawable_epoch != FAR_FUTURE_EPOCH && b.balance == U64.zero) = reset := by
        rw [Bool.eq_iff_iff, hr]; simp
      rw [this]
    · rw [firstMatch_none_iff.mpr h.2.1] at hfm; cases hfm
    · rw [firstMatch_none_iff.mpr h.2.1] at hfm; cases hfm
  · refine ⟨⟨fun h => (by cases h), fun h => by rw [hp] at h; cases h⟩,
      fun _ _ _ => ⟨fun h => (by cases h), fun h => by rw [hfm] at h; cases h.2.1⟩,
      ⟨fun _ => ⟨hp, firstMatch_none_iff.mp hfm, dom, hd, hv⟩, fun _ => rfl⟩,
      fun _ _ => ⟨fun h => (by cases h), fun h => ?_⟩⟩
    obtain ⟨_, _, ⟨dom', hd', hv'⟩, _⟩ := h
    rw [hd] at hd'; cases hd'; rw [hv] at hv'; cases hv'
  · refine ⟨⟨fun h => (by cases h), fun h => by rw [hp] at h; cases h⟩,
      fun _ _ _ => ⟨fun h => (by cases h), fun h => by rw [hfm] at h; cases h.2.1⟩,
      ⟨fun h => (by cases h), fun h => ?_⟩, fun i' a => ⟨fun h => ?_, fun h => ?_⟩⟩
    · obtain ⟨_, _, dom', hd', hv'⟩ := h
      rw [hd] at hd'; cases hd'; rw [hv] at hv'; cases hv'
    · cases h
      exact ⟨hp, firstMatch_none_iff.mp hfm, ⟨dom, hd, hv⟩, rfl, idx, hi, rfl⟩
    · obtain ⟨_, _, _, ha', idx', hi', hidx⟩ := h
      rw [hi] at hi'; cases hi'
      subst ha'; subst hidx; rfl

theorem addressOfCredentials_ok {wc : Bytes32} {addr : ExecutionAddress} :
    JauneConsensus.Gloas.addressOfCredentials wc = .ok addr ↔
      Jaune.Bytes.toAdr? (wc.toBytes.drop 12) = some addr := by
  unfold JauneConsensus.Gloas.addressOfCredentials
  split
  · rename_i a ha
    rw [ha]
    exact ⟨fun h => by cases h; rfl, fun h => by cases h; rfl⟩
  · rename_i ha
    rw [ha]
    exact ⟨fun h => (by cases h), fun h => (by cases h)⟩

/-- The effect of a deposit classification (CL:2297-2361). -/
theorem classifyBuilderDeposit_effect {ctx : Ctx} {m m' : JauneConsensus.Gloas.BeaconState P}
    {r : JauneConsensus.Gloas.BuilderDepositRequest} {o : BuilderDepositOutcome}
    (hc : classifyBuilderDeposit ctx.cfg ctx.blsActive m r = .ok o)
    (hp : JauneConsensus.Gloas.processBuilderDepositRequest ctx m r = .ok m') :
    (o = .ignoredPrefix → m' = m) ∧ (o = .ignoredBadSignature → m' = m) ∧
    (∀ i a reset, o = .topUp i a reset → ∃ b b', m.builders.toArray[i]? = some b ∧
      m'.builders.toArray[i]? = some b' ∧
      m'.builders.toArray.size = m.builders.toArray.size ∧
      (∀ j, j ≠ i → m'.builders.toArray[j]? = m.builders.toArray[j]?) ∧
      b'.pubkey = b.pubkey ∧ b'.version = b.version ∧
      b'.execution_address = b.execution_address ∧ b'.deposit_epoch = b.deposit_epoch ∧
      b'.balance.toNat = b.balance.toNat + a.toNat ∧
      (reset = true → ∃ e, JauneConsensus.Gloas.getCurrentEpoch m = .ok e ∧
        b'.withdrawable_epoch.toNat = e.toNat + ctx.cfg.MIN_BUILDER_WITHDRAWABILITY_DELAY) ∧
      (reset = false → b'.withdrawable_epoch = b.withdrawable_epoch) ∧
      m' = { m with builders := m'.builders }) ∧
    (∀ i a, o = .register i a → ∃ addr e,
      Jaune.Bytes.toAdr? (r.withdrawal_credentials.toBytes.drop 12) = some addr ∧
      computeEpochAtSlot P m.slot = .ok e ∧
      m'.builders.toArray[i]? = some (freshBuilder r.pubkey addr a e) ∧
      m.builders.toArray.size ≤ m'.builders.toArray.size ∧
      (∀ j, j ≠ i → m'.builders.toArray[j]? = m.builders.toArray[j]?) ∧
      m' = { m with builders := m'.builders }) := by
  have hp' : applyBuilderDepositOutcome ctx.cfg m r o = .ok m' := by
    rw [processBuilderDepositRequest_eq, hc] at hp; exact hp
  refine ⟨fun ho => by subst ho; cases hp'; rfl, fun ho => by subst ho; cases hp'; rfl,
    fun i a reset ho => ?_, fun i a ho => ?_⟩
  · subst ho
    rcases classifyBuilderDeposit_inv hc with ⟨_, h⟩ | ⟨_, i', b, _, hb, h⟩ |
      ⟨_, _, _, _, ⟨_, h⟩ | ⟨_, _, _, _, _, h⟩⟩ <;> cases h
    unfold applyBuilderDepositOutcome topUpBuilder at hp'
    obtain ⟨b1, hg, hp'⟩ := bind_eq_ok_iff.mp hp'
    rw [pl_get_ok.mp hg] at hb; cases hb
    obtain ⟨b2, hX, hp'⟩ := bind_eq_ok_iff.mp hp'
    split at hX
    · rename_i hcond
      obtain ⟨e, he, hX⟩ := bind_eq_ok_iff.mp hX
      obtain ⟨d, hd, hX⟩ := bind_eq_ok_iff.mp hX
      obtain ⟨w, hw, hX⟩ := bind_eq_ok_iff.mp hX
      cases hX
      obtain ⟨nb, hnb, hp'⟩ := bind_eq_ok_iff.mp hp'
      obtain ⟨bs, hbs, hp'⟩ := bind_eq_ok_iff.mp hp'
      cases hp'
      obtain ⟨h1, h2, h3⟩ := pl_set_ok hbs
      refine ⟨b, _, pl_get_ok.mp hg, h2, h1, h3, rfl, rfl, rfl, rfl, U64.toNat_add? hnb,
        fun _ => ⟨e, he, ?_⟩, fun hf => ?_, rfl⟩
      · rw [U64.toNat_add? hw, U64.toNat_ofNat? hd]
      · rw [hcond] at hf; cases hf
    · rename_i hcond
      have hb12 : b = b2 := by cases hX; rfl
      subst hb12
      obtain ⟨nb, hnb, hp'⟩ := bind_eq_ok_iff.mp hp'
      obtain ⟨bs, hbs, hp'⟩ := bind_eq_ok_iff.mp hp'
      cases hp'
      obtain ⟨h1, h2, h3⟩ := pl_set_ok hbs
      refine ⟨b, _, pl_get_ok.mp hg, h2, h1, h3, rfl, rfl, rfl, rfl, U64.toNat_add? hnb,
        fun ht => ?_, fun _ => rfl, rfl⟩
      simp only [Bool.not_eq_true] at hcond
      rw [hcond] at ht; cases ht
  · subst ho
    rcases classifyBuilderDeposit_inv hc with ⟨_, h⟩ | ⟨_, _, _, _, _, h⟩ |
      ⟨_, _, _, _, ⟨_, h⟩ | ⟨_, addr, idx, ha, hi, h⟩⟩ <;> cases h
    unfold applyBuilderDepositOutcome at hp'
    obtain ⟨addr', ha', hp'⟩ := bind_eq_ok_iff.mp hp'
    rw [ha] at ha'; cases ha'
    unfold JauneConsensus.Gloas.addBuilderToRegistry at hp'
    obtain ⟨idx', hi', hp'⟩ := bind_eq_ok_iff.mp hp'
    rw [hi] at hi'; cases hi'
    obtain ⟨e, he, hp'⟩ := bind_eq_ok_iff.mp hp'
    obtain ⟨bs, hbs, hp'⟩ := bind_eq_ok_iff.mp hp'
    cases hp'
    obtain ⟨h1, h2, h3⟩ := pl_setOrAppend_ok hbs
    exact ⟨addr, e, addressOfCredentials_ok.mp ha, he, h2, h1, h3, rfl⟩

/-- `classifyBuilderDeposit_bls_indep`: with the BLS switch off the classification equals the
real (`bls = true`) one whenever the signature it would check verifies under the real BLS. -/
theorem classifyBuilderDeposit_bls_indep {ccfg : Config} {m : JauneConsensus.Gloas.BeaconState P}
    {r : JauneConsensus.Gloas.BuilderDepositRequest}
    (hv : ∀ dom, builderDepositDomain ccfg = some dom →
      blsVerify true r.pubkey (computeSigningRoot (builderDepositMessage r) dom) r.signature = true) :
    classifyBuilderDeposit ccfg false m r = classifyBuilderDeposit ccfg true m r := by
  have hs : JauneConsensus.Gloas.isValidBuilderDepositSignature { cfg := ccfg, blsActive := false } r =
      JauneConsensus.Gloas.isValidBuilderDepositSignature { cfg := ccfg, blsActive := true } r := by
    unfold JauneConsensus.Gloas.isValidBuilderDepositSignature
    cases hd : computeDomainDefault ccfg JauneConsensus.Gloas.DOMAIN_BUILDER_DEPOSIT with
    | error e => rfl
    | ok dom =>
      have h := hv dom (builderDepositDomain_eq_some.mpr hd)
      show pure true = (pure (blsVerify true r.pubkey
        (computeSigningRoot (builderDepositMessage r) dom) r.signature) : M Bool)
      rw [h]
  unfold classifyBuilderDeposit
  rw [hs]

end JauneConsensus.Facts.Gloas
