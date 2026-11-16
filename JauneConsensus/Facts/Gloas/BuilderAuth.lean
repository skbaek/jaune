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


/-! ## B1: what a created builder record carries -/

theorem head_of_isBuilderWithdrawalCredential {wc : Bytes32}
    (h : JauneConsensus.Gloas.isBuilderWithdrawalCredential wc = true) :
    wc.toBytes.head? = some 0xB0 := by
  unfold JauneConsensus.Gloas.isBuilderWithdrawalCredential credentialPrefix at h
  split at h
  · rename_i b rest hb
    rw [hb]
    have := beq_iff_eq.mp h
    rw [this]
    rfl
  · exact absurd h (by decide)

/-- **B1, function level.** A builder record that `process_builder_deposit_request` creates
(`BuilderCreated`: the pubkey at index `i` changed, by append or by reuse) comes from a request
with `0xB0` credentials and a new pubkey, whose signature verifies under the real BLS
(`bls = true`) for `DOMAIN_BUILDER_DEPOSIT` (CL:2268-2284), classified `register i`, and the record
is the fresh one: `execution_address = credentials[12:]`, `balance = amount`,
`withdrawable_epoch = FAR_FUTURE_EPOCH`. -/
theorem processBuilderDepositRequest_created {ctx : Ctx} (hbls : ctx.blsActive = true)
    {m m' : JauneConsensus.Gloas.BeaconState P} {r : JauneConsensus.Gloas.BuilderDepositRequest}
    (h : JauneConsensus.Gloas.processBuilderDepositRequest ctx m r = .ok m') {i : Nat}
    (hcr : BuilderCreated m m' i) :
    r.withdrawal_credentials.toBytes.head? = some 0xB0 ∧
    (∀ b ∈ m.builders.toArray, b.pubkey ≠ r.pubkey) ∧
    (∃ dom, builderDepositDomain ctx.cfg = some dom ∧
      blsVerify true r.pubkey (computeSigningRoot (builderDepositMessage r) dom) r.signature = true) ∧
    classifyBuilderDeposit ctx.cfg true m r = .ok (.register i r.amount) ∧
    ∃ addr e, Jaune.Bytes.toAdr? (r.withdrawal_credentials.toBytes.drop 12) = some addr ∧
      computeEpochAtSlot P m.slot = .ok e ∧
      m'.builders.toArray[i]? = some (freshBuilder r.pubkey addr r.amount e) := by
  have h0 := h
  rw [processBuilderDepositRequest_eq] at h0
  obtain ⟨o, hco, _⟩ := bind_eq_ok_iff.mp h0
  obtain ⟨hpre, hbad, htop, hreg⟩ := classifyBuilderDeposit_effect hco h
  obtain ⟨hcr1, hcr2⟩ := hcr
  cases o with
  | ignoredPrefix => exact absurd (by rw [hpre rfl]) hcr2
  | ignoredBadSignature => exact absurd (by rw [hbad rfl]) hcr2
  | topUp j a reset =>
    obtain ⟨b, b', hb, hb', _, hne, hpk, _⟩ := htop j a reset rfl
    by_cases hij : i = j
    · subst hij
      exact absurd (by rw [hb, hb']; simp [hpk]) hcr2
    · exact absurd (by rw [hne i hij]) hcr2
  | register j a =>
    obtain ⟨addr, e, haddr, he, hat, _, hne, _⟩ := hreg j a rfl
    have hij : i = j := by
      by_contra hij
      exact hcr2 (by rw [hne i hij])
    subst hij
    obtain ⟨_, _, _, hm⟩ := classifyBuilderDeposit_meaning hco
    obtain ⟨hp, hall, ⟨dom, hd, hv⟩, ha, _⟩ := (hm i a).mp rfl
    subst ha
    rw [hbls] at hv hco
    exact ⟨head_of_isBuilderWithdrawalCredential hp, hall, ⟨dom, hd, hv⟩, hco, addr, e, haddr, he, hat⟩

/-! ## B1 controls -/

/-- B1 prefix control, real side: a request whose credentials do not carry the builder prefix is
ignored whatever its pubkey (known or new) and signature: the state is unchanged. -/
theorem processBuilderDepositRequest_ignores_prefix {ctx : Ctx}
    {m : JauneConsensus.Gloas.BeaconState P} {r : JauneConsensus.Gloas.BuilderDepositRequest}
    (hp : JauneConsensus.Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials = false) :
    JauneConsensus.Gloas.processBuilderDepositRequest ctx m r = .ok m := by
  unfold JauneConsensus.Gloas.processBuilderDepositRequest
  simp only [hp, Bool.not_false, ↓reduceIte]
  rfl

/-- A signature whose first byte is `0x00` has the compression bit clear, so
`signature_to_point` rejects it before any pairing (`Crypto/Codec.lean`). -/
theorem blsVerify_true_of_head_zero (pk : BLSPubkey) (msg : Root) (sig : BLSSignature)
    (h0 : sig.toArray[0]? = some 0) : blsVerify true pk msg sig = false := by
  have hl : sig.toArray.toList.length = 96 := by simp [sig.size_eq]
  obtain ⟨t, ht⟩ : ∃ t, sig.toArray.toList = 0 :: t := by
    cases hs : sig.toArray.toList with
    | nil => rw [hs] at hl; cases hl
    | cons x t =>
      refine ⟨t, ?_⟩
      have : sig.toArray.toList[0]? = some 0 := by simpa using h0
      rw [hs] at this
      simp at this
      rw [this]
  have hl' : t.length = 95 := by rw [ht] at hl; simpa using hl
  have hsp : signatureToPoint (0 :: t) = .error "G2 signature must be compressed" := by
    simp [signatureToPoint, hl']
    rfl
  unfold blsVerify verify coreVerify
  rw [ht, hsp]
  rfl

/-- B1 signature control, real side: at `bls = true`, a new-pubkey `0xB0` request whose signature
starts `0x00` (a corrupted signature) is ignored and creates no record. -/
theorem processBuilderDepositRequest_ignores_corrupted {ctx : Ctx} (hbls : ctx.blsActive = true)
    {m : JauneConsensus.Gloas.BeaconState P} {r : JauneConsensus.Gloas.BuilderDepositRequest}
    (hnew : ∀ b ∈ m.builders.toArray, b.pubkey ≠ r.pubkey)
    (h0 : r.signature.toArray[0]? = some 0) :
    ∀ m', JauneConsensus.Gloas.processBuilderDepositRequest ctx m r = .ok m' → m' = m := by
  intro m' h
  have h0' := h
  rw [processBuilderDepositRequest_eq] at h0'
  obtain ⟨o, hco, _⟩ := bind_eq_ok_iff.mp h0'
  obtain ⟨hpre, hbad, htop, hreg⟩ := classifyBuilderDeposit_effect hco h
  obtain ⟨_, htopm, _, hregm⟩ := classifyBuilderDeposit_meaning hco
  cases o with
  | ignoredPrefix => exact hpre rfl
  | ignoredBadSignature => exact hbad rfl
  | topUp j a reset =>
    obtain ⟨_, hfm, _⟩ := (htopm j a reset).mp rfl
    rw [firstMatch_none_iff.mpr hnew] at hfm; cases hfm
  | register j a =>
    obtain ⟨_, _, ⟨dom, _, hv⟩, _⟩ := (hregm j a).mp rfl
    rw [hbls, blsVerify_true_of_head_zero _ _ _ h0] at hv
    cases hv


/-! ## Controls on closed minimal states (B1, B3)

Each mutant is a copy of the real function with one check removed, kept here and never on the
real path. On a closed minimal state (every field the functions read is fixed; the rest of the
state is an arbitrary `s`), the real function leaves the state unchanged while the mutant creates
a record (B1) or initiates an exit (B3), so the mutant falsifies the B1/B3 statements that the
real function satisfies (`processBuilderDepositRequest_created`, `classifyBuilderExit_meaning`). -/

theorem builderCreated_of_none_some {st st' : JauneConsensus.Gloas.BeaconState P} {i : Nat}
    {b : JauneConsensus.Gloas.Builder} (h : st.builders.toArray[i]? = none)
    (h' : st'.builders.toArray[i]? = some b) : BuilderCreated st st' i := by
  refine ⟨by rw [h']; rfl, ?_⟩
  rw [h, h']
  simp

/-- A 48-byte zero pubkey. -/
def ctrlPk : BLSPubkey := ⟨Array.replicate 48 0, by simp⟩

/-- A 96-byte zero signature: its compression bit is clear (a corrupted signature). -/
def ctrlSig : BLSSignature := ⟨Array.replicate 96 0, by simp⟩

/-- One registered builder: pubkey `ctrlPk`, execution address zero, deposited at epoch 0,
not exiting. -/
def ctrlBuilder : JauneConsensus.Gloas.Builder :=
  freshBuilder ctrlPk JauneConsensus.Gloas.zeroAddress U64.zero U64.zero

/-- The B3 control state: slot 0, finalized epoch 1 (so `ctrlBuilder` is active), one builder,
no pending builder payments or withdrawals. -/
def ctrlExitState (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    JauneConsensus.Gloas.BeaconState Preset.minimal :=
  { s with
    slot := U64.zero
    finalized_checkpoint := { epoch := U64.one, root := s.finalized_checkpoint.root }
    builders := ⟨#[ctrlBuilder]⟩
    builder_pending_payments :=
      ⟨Array.replicate 16 JauneConsensus.Gloas.BuilderPendingPayment.empty, by
        rw [Array.size_replicate]; rfl⟩
    builder_pending_withdrawals := ⟨#[]⟩ }

/-- An exit request for `ctrlBuilder` from another address. -/
def ctrlExitRequest : JauneConsensus.Gloas.BuilderExitRequest :=
  { source_address := ⟨0, 0, 1⟩, pubkey := ctrlPk }

/-- **B3 mutant**: `process_builder_exit_request` without the
`builder.execution_address != request.source_address` check (CL:2378-2379). -/
def processBuilderExitRequestNoSource (cfg : Config) (state : JauneConsensus.Gloas.BeaconState P)
    (request : JauneConsensus.Gloas.BuilderExitRequest) : M (JauneConsensus.Gloas.BeaconState P) := do
  let some i := state.builders.toArray.findIdx? (·.pubkey == request.pubkey) | return state
  let builderIndex ← U64.ofNat? i "BuilderIndex"
  let _builder ← state.builders.get i "process_builder_exit_request"
  if !(← JauneConsensus.Gloas.isActiveBuilder state builderIndex) then return state
  if (← JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder state builderIndex) != U64.zero then
    return state
  JauneConsensus.Gloas.initiateBuilderExit cfg state builderIndex

theorem ctrlExit_findIdx (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    (ctrlExitState s).builders.toArray.findIdx? (·.pubkey == ctrlExitRequest.pubkey) = some 0 := by
  rw [Array.findIdx?_eq_some_iff_getElem]
  exact ⟨by simp [ctrlExitState], pubkey_beq_iff.mpr rfl, fun j hj => absurd hj (Nat.not_lt_zero _)⟩

theorem ctrlExit_t1 (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    JauneConsensus.Gloas.getPendingBalanceToWithdrawForBuilder (ctrlExitState s) U64.zero =
      .ok U64.zero := rfl
theorem ctrlExit_t2 (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    JauneConsensus.Gloas.getCurrentEpoch (ctrlExitState s) = .ok U64.zero := by
  with_unfolding_all rfl
theorem ctrlExit_t4 (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    JauneConsensus.Gloas.initiateBuilderExit Config.minimal (ctrlExitState s) U64.zero =
      .ok { ctrlExitState s with
      builders := ⟨#[{ ctrlBuilder with withdrawable_epoch := U64.lit 2 }]⟩ } := by
  with_unfolding_all rfl

/-- **B3 control.** On the closed state, the real function classifies the request `wrongSource`
and leaves the state unchanged; the mutant without the source check initiates the exit
(`ExitInitiated` at builder 0). -/
theorem b3_control (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    classifyBuilderExit Config.minimal (ctrlExitState s) ctrlExitRequest = .ok .wrongSource ∧
    JauneConsensus.Gloas.processBuilderExitRequest Config.minimal (ctrlExitState s) ctrlExitRequest =
      .ok (ctrlExitState s) ∧
    ¬ ExitInitiated (ctrlExitState s) (ctrlExitState s) 0 ∧
    ∃ s', processBuilderExitRequestNoSource Config.minimal (ctrlExitState s) ctrlExitRequest =
      .ok s' ∧ ExitInitiated (ctrlExitState s) s' 0 := by
  have hc : classifyBuilderExit Config.minimal (ctrlExitState s) ctrlExitRequest = .ok .wrongSource := by
    unfold classifyBuilderExit firstMatch
    rw [ctrlExit_findIdx]
    rfl
  refine ⟨hc, ?_, ?_, ?_⟩
  · rw [processBuilderExitRequest_eq, hc]
    rfl
  · rintro ⟨b, b', hb, hb', _, hfar, hne⟩
    rw [hb] at hb'; cases hb'
    exact hne hfar
  · refine ⟨{ ctrlExitState s with
      builders := ⟨#[{ ctrlBuilder with withdrawable_epoch := U64.lit 2 }]⟩ }, ?_, ?_⟩
    · unfold processBuilderExitRequestNoSource
      rw [ctrlExit_findIdx]
      simp only [show U64.ofNat? 0 "BuilderIndex" = .ok U64.zero from rfl, bind, Except.bind,
        show (ctrlExitState s).builders.get 0 "process_builder_exit_request" = .ok ctrlBuilder
          from rfl,
        show JauneConsensus.Gloas.isActiveBuilder (ctrlExitState s) U64.zero = .ok true from rfl,
        ctrlExit_t1, ctrlExit_t4, Bool.not_true, bne_self_eq_false, Bool.false_eq_true,
        ↓reduceIte]
    · exact ⟨ctrlBuilder, { ctrlBuilder with withdrawable_epoch := U64.lit 2 }, rfl, rfl, rfl, rfl,
      by decide⟩

/-- The B1 control state: slot 0, no builders. -/
def ctrlEmptyState (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    JauneConsensus.Gloas.BeaconState Preset.minimal :=
  { s with slot := U64.zero, builders := ⟨#[]⟩ }

theorem ctrlEmpty_findIdx (s : JauneConsensus.Gloas.BeaconState Preset.minimal) (pk : BLSPubkey) :
    (ctrlEmptyState s).builders.toArray.findIdx? (·.pubkey == pk) = none := by
  rw [Array.findIdx?_eq_none_iff]
  intro x hx
  simp [ctrlEmptyState] at hx

/-- A deposit with `0x00` credentials (not the builder prefix). -/
def ctrlPrefixRequest : JauneConsensus.Gloas.BuilderDepositRequest :=
  { pubkey := ctrlPk, withdrawal_credentials := 0, amount := U64.one, signature := ctrlSig }

/-- A `0xB0` deposit for a new pubkey with a corrupted signature. -/
def ctrlCorruptRequest : JauneConsensus.Gloas.BuilderDepositRequest :=
  { pubkey := ctrlPk, withdrawal_credentials := Jaune.Bytes.toB256 (0xB0 :: List.replicate 31 0),
    amount := U64.one, signature := ctrlSig }

/-- **B1 mutant (prefix)**: `process_builder_deposit_request` without the credential-prefix check
(CL:2336-2337). -/
def processBuilderDepositRequestNoPrefix (ctx : Ctx) (state : JauneConsensus.Gloas.BeaconState P)
    (request : JauneConsensus.Gloas.BuilderDepositRequest) : M (JauneConsensus.Gloas.BeaconState P) := do
  match state.builders.toArray.findIdx? (·.pubkey == request.pubkey) with
  | none =>
    if ← JauneConsensus.Gloas.isValidBuilderDepositSignature ctx request then
      JauneConsensus.Gloas.addBuilderToRegistry state request.pubkey
        JauneConsensus.Gloas.PAYLOAD_BUILDER_VERSION
        (← JauneConsensus.Gloas.addressOfCredentials request.withdrawal_credentials) request.amount
        state.slot
    else pure state
  | some i => topUpBuilder ctx.cfg state i request.amount

/-- **B1 mutant (signature)**: `process_builder_deposit_request` without
`is_valid_builder_deposit_signature` (CL:2340). -/
def processBuilderDepositRequestNoSignature (ctx : Ctx)
    (state : JauneConsensus.Gloas.BeaconState P) (request : JauneConsensus.Gloas.BuilderDepositRequest) :
    M (JauneConsensus.Gloas.BeaconState P) := do
  if !JauneConsensus.Gloas.isBuilderWithdrawalCredential request.withdrawal_credentials then
    return state
  match state.builders.toArray.findIdx? (·.pubkey == request.pubkey) with
  | none =>
    JauneConsensus.Gloas.addBuilderToRegistry state request.pubkey
      JauneConsensus.Gloas.PAYLOAD_BUILDER_VERSION
      (← JauneConsensus.Gloas.addressOfCredentials request.withdrawal_credentials) request.amount
      state.slot
  | some i => topUpBuilder ctx.cfg state i request.amount

/-- **B1 prefix control.** A `0x00`-credential deposit for a new pubkey, with the BLS switch off so
that the signature check passes: the real function ignores it; the mutant without the prefix
check creates builder 0, whose credentials lack `0xB0`. -/
theorem b1_prefix_control (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    JauneConsensus.Gloas.isBuilderWithdrawalCredential ctrlPrefixRequest.withdrawal_credentials = false ∧
    JauneConsensus.Gloas.processBuilderDepositRequest { cfg := Config.minimal, blsActive := false }
      (ctrlEmptyState s) ctrlPrefixRequest = .ok (ctrlEmptyState s) ∧
    ∃ s', processBuilderDepositRequestNoPrefix { cfg := Config.minimal, blsActive := false }
      (ctrlEmptyState s) ctrlPrefixRequest = .ok s' ∧ BuilderCreated (ctrlEmptyState s) s' 0 := by
  have hp : JauneConsensus.Gloas.isBuilderWithdrawalCredential
      ctrlPrefixRequest.withdrawal_credentials = false := by decide
  refine ⟨hp, processBuilderDepositRequest_ignores_prefix hp, ?_⟩
  unfold processBuilderDepositRequestNoPrefix
  rw [ctrlEmpty_findIdx]
  refine ⟨_, rfl, ?_⟩
  exact builderCreated_of_none_some rfl rfl

/-- **B1 signature control.** At `bls = true`, a `0xB0` deposit for a new pubkey with a corrupted
signature: the real function ignores it (and the signature does not verify for any domain); the
mutant without the signature check creates builder 0. -/
theorem b1_signature_control (s : JauneConsensus.Gloas.BeaconState Preset.minimal) :
    (∀ dom, blsVerify true ctrlCorruptRequest.pubkey
      (computeSigningRoot (builderDepositMessage ctrlCorruptRequest) dom)
      ctrlCorruptRequest.signature = false) ∧
    (∀ m', JauneConsensus.Gloas.processBuilderDepositRequest { cfg := Config.minimal }
      (ctrlEmptyState s) ctrlCorruptRequest = .ok m' → m' = ctrlEmptyState s) ∧
    ∃ s', processBuilderDepositRequestNoSignature { cfg := Config.minimal }
      (ctrlEmptyState s) ctrlCorruptRequest = .ok s' ∧ BuilderCreated (ctrlEmptyState s) s' 0 := by
  refine ⟨fun dom => blsVerify_true_of_head_zero _ _ _ rfl,
    processBuilderDepositRequest_ignores_corrupted rfl
      (fun b hb => by simp [ctrlEmptyState] at hb) rfl, ?_⟩
  unfold processBuilderDepositRequestNoSignature
  rw [ctrlEmpty_findIdx]
  refine ⟨_, rfl, ?_⟩
  exact builderCreated_of_none_some rfl rfl


/-! ## `get_index_for_new_builder` (CL:2287-2295) -/

theorem getIndexForNewBuilder_loop (C : JauneConsensus.Gloas.Builder → Bool)
    (body : JauneConsensus.Gloas.Builder → Option U64 × Nat → M (ForInStep (Option U64 × Nat)))
    (hbody : ∀ x s, (C x = true →
        body x s = (U64.ofNat? s.2 "BuilderIndex" >>= fun v => pure (.done (some v, s.2)))) ∧
      (C x = false → body x s = pure (.yield (none, s.2 + 1)))) :
    ∀ (l : List JauneConsensus.Gloas.Builder) (k : Nat) (out : Option U64 × Nat),
      forIn l (none, k) body = .ok out →
      (∀ v, out.1 = some v → ∃ j, ∃ hj : j < l.length, v.toNat = k + j ∧ C l[j] = true) ∧
      (out.1 = none → ∀ x ∈ l, C x = false) := by
  intro l
  induction l with
  | nil =>
    intro k out h
    cases h
    refine ⟨fun v hv => ?_, fun _ x hx => ?_⟩
    · simp at hv
    · simp at hx
  | cons x l ih =>
    intro k out h
    rw [List.forIn_cons] at h
    obtain ⟨st, hst, h⟩ := bind_eq_ok_iff.mp h
    cases hc : C x with
    | true =>
      rw [(hbody x _).1 hc] at hst
      obtain ⟨v, hv, hst⟩ := bind_eq_ok_iff.mp hst
      cases hst
      cases h
      refine ⟨fun v' hv' => ?_, fun hn => by cases hn⟩
      cases hv'
      exact ⟨0, by simp, by rw [U64.toNat_ofNat? hv]; rfl, by simpa using hc⟩
    | false =>
      rw [(hbody x _).2 hc] at hst
      cases hst
      obtain ⟨h1, h2⟩ := ih (k + 1) out h
      refine ⟨fun v hv => ?_, fun hn y hy => ?_⟩
      · obtain ⟨j, hj, hvj, hcj⟩ := h1 v hv
        exact ⟨j + 1, by simp; omega, by rw [hvj]; omega, by simpa using hcj⟩
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact hc
        · exact h2 hn y hy

/-- `get_index_for_new_builder` returns the end of the registry or a slot whose builder is exited
and swept (`withdrawable_epoch <= current_epoch` and `balance == 0`). -/
theorem getIndexForNewBuilder_spec {m : JauneConsensus.Gloas.BeaconState P} {idx : U64}
    (h : JauneConsensus.Gloas.getIndexForNewBuilder m = .ok idx) :
    ∃ e, JauneConsensus.Gloas.getCurrentEpoch m = .ok e ∧
      (idx.toNat = m.builders.toArray.size ∨
        ∃ b, m.builders.toArray[idx.toNat]? = some b ∧ b.withdrawable_epoch ≤ e ∧
          b.balance = U64.zero) := by
  unfold JauneConsensus.Gloas.getIndexForNewBuilder at h
  obtain ⟨e, he, h⟩ := bind_eq_ok_iff.mp h
  refine ⟨e, he, ?_⟩
  simp only [] at h
  obtain ⟨st, hst, h⟩ := bind_eq_ok_iff.mp h
  rw [← Array.forIn_toList] at hst
  have hloop := getIndexForNewBuilder_loop
    (fun b => decide (b.withdrawable_epoch ≤ e) && b.balance == U64.zero) _
    (fun x s => ⟨fun hc => by simp only [hc, ↓reduceIte], fun hc => by
      simp only [hc, Bool.false_eq_true, ↓reduceIte]⟩) _ 0 st hst
  cases hs1 : st.1 with
  | some v =>
    rw [hs1] at h
    cases h
    obtain ⟨j, hj, hvj, hcj⟩ := hloop.1 _ hs1
    right
    refine ⟨m.builders.toArray.toList[j], ?_, ?_⟩
    · rw [hvj, Nat.zero_add]; simp
    · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcj
      exact hcj
  | none =>
    rw [hs1] at h
    left
    exact (U64.toNat_ofNat? h).trans rfl

end JauneConsensus.Facts.Gloas
