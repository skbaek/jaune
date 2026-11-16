import JauneConsensus.Facts.Gloas.BuilderAuth

/-!
# Builder request witnesses and the G3-01 control (goal `eip8282-gloas-cross-layer-v1`, B2/B4)

Function-level (F, statements.md §0.3) witnesses on closed minimal-preset Gloas states: each is
one evaluation of `classifyBuilderDeposit` or `classifyBuilderExit` (BuilderAuth.lean), with no
run and no `hash_tree_root` of a state.

* B2: the four deposit outcomes. `.ignoredBadSignature` is at `bls = true`, with a signature whose
  first byte (`0x20`) carries invalid metadata bits, so `signatureToPoint` rejects it before any
  curve arithmetic and no pairing is evaluated. `.register` is closed at `bls = false`
  (`w_register_blsOff`) and carried to `bls = true` by `classifyBuilderDeposit_bls_indep`
  (`w_register_blsOn`) for an arbitrary new key and signature under the hypothesis that the
  signature verifies, which a real key pair satisfies. `w_register_blsOn_flip` is B1's
  one-byte pair: the same key with the signature's first byte set to `0x00` is
  `.ignoredBadSignature` at `bls = true`. (B1's mutant control is `b1_signature_control` in
  `BuilderAuth.lean`.)
* B4: one witness per exit reason, the ordering witness (`notActive` before `wrongSource`), and
  `every_exit_outcome_occurs`.
* The G3-01 control (design.md §5): with `builders[0].pubkey = builders[1].pubkey`, resolution is
  first-match, so builder 1 is never initiated, and B4's frozen unique-resolution clause fails,
  while the first-match clause of `classifyBuilderExit_meaning` holds.

The base state is built from zero values by local `Inhabited` instances; only the fields the
classifiers read (`builders`, `finalized_checkpoint`, `slot`, the two builder pending queues) are
ever reduced.
-/

namespace JauneConsensus.Facts.Gloas.Witnesses

open JauneConsensus JauneConsensus.Facts JauneConsensus.Facts.Gloas

local instance {α : Type} [Inhabited α] {n : Nat} : Inhabited (SszVector α n) :=
  ⟨⟨Array.replicate n default, Array.size_replicate⟩⟩
local instance {α : Type} {n : Nat} : Inhabited (SszList α n) := ⟨⟨#[], Nat.zero_le _⟩⟩
local instance {n : Nat} : Inhabited (Bitvector n) := ⟨⟨Array.replicate n false, Array.size_replicate⟩⟩
local instance {s : Spine} {α : Type} : Inhabited (ProgressiveListOnSpine s α) := ⟨⟨#[]⟩⟩
local instance : Inhabited Fork := ⟨by constructor <;> exact default⟩
local instance : Inhabited Checkpoint := ⟨by constructor <;> exact default⟩
local instance : Inhabited Eth1Data := ⟨by constructor <;> exact default⟩
local instance : Inhabited BeaconBlockHeader := ⟨by constructor <;> exact default⟩
local instance {P : Preset} : Inhabited (SyncCommittee P) := ⟨by constructor <;> exact default⟩
local instance : Inhabited JauneConsensus.Gloas.BuilderPendingWithdrawal :=
  ⟨by constructor <;> exact default⟩
local instance : Inhabited JauneConsensus.Gloas.BuilderPendingPayment :=
  ⟨by constructor <;> exact default⟩
local instance : Inhabited JauneConsensus.Gloas.ExecutionPayloadBid :=
  ⟨by constructor <;> exact default⟩
local instance {P : Preset} : Inhabited (JauneConsensus.Gloas.PayloadTimelinessCommittee P) :=
  ⟨by unfold JauneConsensus.Gloas.PayloadTimelinessCommittee; exact default⟩

/-- The minimal-preset Gloas state. -/
abbrev MinimalGloasState := JauneConsensus.Gloas.BeaconState Preset.minimal
/-- A builder exit request. -/
abbrev ExitRequest := JauneConsensus.Gloas.BuilderExitRequest

/-- The closed minimal-preset base state: every field at its zero value. -/
def base : MinimalGloasState := by
  constructor <;> exact default

/-- A pubkey with every byte `b`. -/
def pubkey (b : UInt8) : BLSPubkey := ⟨Array.replicate 48 b, Array.size_replicate⟩

/-- An execution address with low word `n`. -/
def address (n : U64) : ExecutionAddress := match n with
  | ⟨w⟩ => ((0 : UInt32), (0, w))

/-- A builder record. -/
def builder (key : UInt8) (a bal dep wd : U64) : JauneConsensus.Gloas.Builder :=
  { pubkey := pubkey key, version := JauneConsensus.Gloas.PAYLOAD_BUILDER_VERSION,
    execution_address := address a, balance := bal, deposit_epoch := dep, withdrawable_epoch := wd }

/-- Slot 0, finalized epoch 2, the given builders. -/
def state (bs : Array JauneConsensus.Gloas.Builder) : MinimalGloasState :=
  { base with builders := ⟨bs⟩, finalized_checkpoint := { epoch := ⟨2⟩, root := default } }

/-- An exit request from address `a` for pubkey `key`. -/
def exitRequest (a : U64) (key : UInt8) : ExitRequest :=
  { source_address := address a, pubkey := pubkey key }

/-- `firstMatch` on a literal registry is `List.findIdx?` (which the kernel reduces). -/
theorem firstMatch_list (l : List JauneConsensus.Gloas.Builder) (k : BLSPubkey) :
    firstMatch ⟨l.toArray⟩ k = l.findIdx? (·.pubkey == k) := by
  unfold firstMatch
  exact List.findIdx?_toArray _ _

/-- Builder 0 active (address 1), builder 1 not finalized (address 1), builder 2 exiting. -/
def stateExit : MinimalGloasState :=
  state #[builder 1 ⟨1⟩ ⟨10⟩ ⟨0⟩ FAR_FUTURE_EPOCH, builder 2 ⟨1⟩ ⟨10⟩ ⟨5⟩ FAR_FUTURE_EPOCH,
    builder 3 ⟨1⟩ ⟨0⟩ ⟨0⟩ ⟨7⟩]

theorem witness_unknown (ccfg : Config) :
    classifyBuilderExit ccfg stateExit (exitRequest ⟨1⟩ 9) = .ok .unknownPubkey := by
  unfold classifyBuilderExit
  simp only [stateExit, state, exitRequest, firstMatch_list]
  rfl

theorem witness_notFinalized (ccfg : Config) :
    classifyBuilderExit ccfg stateExit (exitRequest ⟨1⟩ 2) = .ok (.notActive .notFinalized) := by
  unfold classifyBuilderExit
  simp only [stateExit, state, exitRequest, firstMatch_list]
  rfl

theorem witness_alreadyExiting (ccfg : Config) :
    classifyBuilderExit ccfg stateExit (exitRequest ⟨1⟩ 3) = .ok (.notActive .alreadyExiting) := by
  unfold classifyBuilderExit
  simp only [stateExit, state, exitRequest, firstMatch_list]
  rfl

theorem witness_wrongSource (ccfg : Config) :
    classifyBuilderExit ccfg stateExit (exitRequest ⟨2⟩ 1) = .ok .wrongSource := by
  unfold classifyBuilderExit
  simp only [stateExit, state, exitRequest, firstMatch_list]
  rfl

theorem witness_initiate (ccfg : Config) :
    classifyBuilderExit ccfg stateExit (exitRequest ⟨1⟩ 1) = .ok (.initiate 0) := by
  unfold classifyBuilderExit
  simp only [stateExit, state, exitRequest, firstMatch_list]
  rfl


/-! ## Pending balance -/

def pendingWithdrawal (amount : U64) : JauneConsensus.Gloas.BuilderPendingWithdrawal :=
  { fee_recipient := address ⟨7⟩, amount, builder_index := ⟨0⟩ }

/-- `sExit` with one pending withdrawal of 5 for builder 0. -/
def statePendingWithdrawal : MinimalGloasState :=
  { stateExit with builder_pending_withdrawals := ⟨#[pendingWithdrawal ⟨5⟩]⟩ }

/-- `sExit` with one pending payment of 5 for builder 0 (window slot 15). -/
def statePendingPayment : MinimalGloasState :=
  { stateExit with builder_pending_payments :=
      ⟨(List.replicate 15 default ++
          [({ weight := ⟨0⟩, withdrawal := pendingWithdrawal ⟨5⟩, proposer_index := ⟨0⟩ } :
            JauneConsensus.Gloas.BuilderPendingPayment)]).toArray,
        by decide⟩ }

theorem witness_pendingWithdrawal (ccfg : Config) :
    classifyBuilderExit ccfg statePendingWithdrawal (exitRequest ⟨1⟩ 1) = .ok .pendingBalance := by
  unfold classifyBuilderExit
  simp only [statePendingWithdrawal, stateExit, state, exitRequest, firstMatch_list]
  rfl

theorem witness_pendingPayment (ccfg : Config) :
    classifyBuilderExit ccfg statePendingPayment (exitRequest ⟨1⟩ 1) = .ok .pendingBalance := by
  unfold classifyBuilderExit
  simp only [statePendingPayment, stateExit, state, exitRequest, firstMatch_list]
  rfl

/-! ## Ordering: `notActive` before `wrongSource` -/

/-- Builder 1 (pubkey 2) is not finalized and its address is 1; the request comes from 2, so it
fails both the activity test and the source test. -/
theorem witness_order_notActive_before_wrongSource (ccfg : Config) :
    (∃ b, stateExit.builders.toArray[1]? = some b ∧ b.pubkey = (exitRequest ⟨2⟩ 2).pubkey ∧
      b.execution_address ≠ (exitRequest ⟨2⟩ 2).source_address ∧
      JauneConsensus.Gloas.isActiveBuilder stateExit ⟨1⟩ = .ok false) ∧
    classifyBuilderExit ccfg stateExit (exitRequest ⟨2⟩ 2) = .ok (.notActive .notFinalized) := by
  refine ⟨⟨builder 2 ⟨1⟩ ⟨10⟩ ⟨5⟩ FAR_FUTURE_EPOCH, rfl, rfl, by decide, rfl⟩, ?_⟩
  unfold classifyBuilderExit
  simp only [stateExit, state, exitRequest, firstMatch_list]
  rfl

/-! ## Builder deposits (B2) -/

/-- Withdrawal credentials with top word `hi` and low word `lo` (big-endian bytes). -/
def withdrawalCredentials (hi lo : U64) : Bytes32 := match hi, lo with
  | ⟨h⟩, ⟨l⟩ => ((h, 0), (0, l))

/-- Top words whose first byte is `0xB0` (the builder prefix) and `0x01`. -/
def prefixB0 : U64 := ⟨0xB000000000000000⟩
def prefix01 : U64 := ⟨0x0100000000000000⟩

/-- A signature with first byte `b0`, then zeros. -/
def signature (b0 : UInt8) : BLSSignature :=
  ⟨(b0 :: List.replicate 95 0).toArray, by simp⟩

def depositRequest (key : UInt8) (p : U64) (s0 : UInt8) : JauneConsensus.Gloas.BuilderDepositRequest :=
  { pubkey := pubkey key, withdrawal_credentials := withdrawalCredentials p ⟨3⟩, amount := ⟨1000000000⟩, signature := signature s0 }

/-- Builder 0 active with balance 10; builder 1 exited (`withdrawable_epoch = 1`) and swept
(balance 0). -/
def stateDeposit : MinimalGloasState :=
  state #[builder 1 ⟨1⟩ ⟨10⟩ ⟨0⟩ FAR_FUTURE_EPOCH, builder 2 ⟨1⟩ ⟨0⟩ ⟨0⟩ ⟨1⟩]

/-- `.ignoredPrefix` for a known pubkey (`0x01` credentials), at every `bls`. -/
theorem witness_ignoredPrefix (ccfg : Config) (bls : Bool) :
    firstMatch stateDeposit.builders (depositRequest 1 prefix01 0xc0).pubkey = some 0 ∧
    classifyBuilderDeposit ccfg bls stateDeposit (depositRequest 1 prefix01 0xc0) = .ok .ignoredPrefix := by
  refine ⟨?_, ?_⟩
  · simp only [stateDeposit, state, depositRequest, firstMatch_list]; rfl
  · rfl

/-- `.topUp` with `reset = true`: builder 1 is exited and swept. -/
theorem witness_topUp_reset (ccfg : Config) (bls : Bool) :
    classifyBuilderDeposit ccfg bls stateDeposit (depositRequest 2 prefixB0 0xc0) = .ok (.topUp 1 ⟨1000000000⟩ true) := by
  unfold classifyBuilderDeposit
  simp only [stateDeposit, state, depositRequest, firstMatch_list]
  rfl

/-- `.topUp` with `reset = false`: builder 0 is active. -/
theorem witness_topUp_noReset (ccfg : Config) (bls : Bool) :
    classifyBuilderDeposit ccfg bls stateDeposit (depositRequest 1 prefixB0 0xc0) = .ok (.topUp 0 ⟨1000000000⟩ false) := by
  unfold classifyBuilderDeposit
  simp only [stateDeposit, state, depositRequest, firstMatch_list]
  rfl

/-- `.ignoredBadSignature` at `bls = true`: the signature's first byte `0x20` carries invalid
metadata bits, so `signatureToPoint` fails before any curve or pairing work. -/
theorem witness_ignoredBadSignature :
    classifyBuilderDeposit Config.minimal true stateDeposit (depositRequest 9 prefixB0 0x20) = .ok .ignoredBadSignature := by
  unfold classifyBuilderDeposit
  simp only [stateDeposit, state, depositRequest, firstMatch_list]
  rfl

/-- `.register` at `bls = false`: a new pubkey registers at the end of the registry (index 2). -/
theorem witness_register_blsOff :
    classifyBuilderDeposit Config.minimal false stateDeposit (depositRequest 9 prefixB0 0xc0) =
      .ok (.register 2 ⟨1000000000⟩) := by
  unfold classifyBuilderDeposit
  simp only [stateDeposit, state, depositRequest, firstMatch_list]
  rfl

/-- A builder deposit for an arbitrary `key` and `signature`, otherwise `dep _ preB0 _`: `0xB0`
credentials, amount `10^9`. -/
def depositKey (key : BLSPubkey) (s : BLSSignature) : JauneConsensus.Gloas.BuilderDepositRequest :=
  { pubkey := key, withdrawal_credentials := withdrawalCredentials prefixB0 ⟨3⟩, amount := ⟨1000000000⟩, signature := s }

/-- `s` with its first byte set to `0x00` (a one-byte change of the signature). -/
def zeroHead (s : BLSSignature) : BLSSignature :=
  ⟨s.toArray.set 0 0 (by simp [s.size_eq]), by simp [s.size_eq]⟩

/-- `.register` at `bls = true` for any new `key` whose `signature` verifies, transferred from the
`bls = false` evaluation by `classifyBuilderDeposit_bls_indep`. The hypothesis is satisfiable in
principle: `key` a valid compressed G1 point (neither all-`0x01` nor all-`0x02`, the registered
keys) and `signature` its signature over the deposit message. -/
theorem witness_register_blsOn (key : BLSPubkey) (signature : BLSSignature)
    (hnew : key ≠ pubkey 1 ∧ key ≠ pubkey 2)
    (hv : ∀ dom, builderDepositDomain Config.minimal = some dom →
      blsVerify true key
        (computeSigningRoot (builderDepositMessage (depositKey key signature)) dom) signature = true) :
    classifyBuilderDeposit Config.minimal true stateDeposit (depositKey key signature) =
      .ok (.register 2 ⟨1000000000⟩) := by
  rw [← classifyBuilderDeposit_bls_independent hv]
  have h1 : (pubkey 1 == key) = false :=
    Bool.eq_false_iff.mpr fun h => hnew.1 (pubkey_beq_iff.mp h).symm
  have h2 : (pubkey 2 == key) = false :=
    Bool.eq_false_iff.mpr fun h => hnew.2 (pubkey_beq_iff.mp h).symm
  unfold classifyBuilderDeposit
  simp only [stateDeposit, state, depositKey, firstMatch_list, builder, List.findIdx?_cons, h1, h2]
  rfl

/-- **The B1 flip pair.** For the same `key` and `signature` as `w_register_blsOn`, setting the
signature's first byte to `0x00` turns the outcome at `bls = true` into `.ignoredBadSignature`:
the flipped signature fails `blsVerify true` for every key and message
(`blsVerify_true_of_head_zero`). -/
theorem witness_register_blsOn_flip (key : BLSPubkey) (signature : BLSSignature)
    (hnew : key ≠ pubkey 1 ∧ key ≠ pubkey 2) :
    classifyBuilderDeposit Config.minimal true stateDeposit (depositKey key (zeroHead signature)) =
      .ok .ignoredBadSignature := by
  have h1 : (pubkey 1 == key) = false :=
    Bool.eq_false_iff.mpr fun h => hnew.1 (pubkey_beq_iff.mp h).symm
  have h2 : (pubkey 2 == key) = false :=
    Bool.eq_false_iff.mpr fun h => hnew.2 (pubkey_beq_iff.mp h).symm
  have h0 : (zeroHead signature).toArray[0]? = some 0 := by
    simp [zeroHead, signature.size_eq]
  obtain ⟨dom, hdom⟩ : ∃ dom, computeDomainDefault Config.minimal
      JauneConsensus.Gloas.DOMAIN_BUILDER_DEPOSIT = .ok dom := ⟨_, rfl⟩
  unfold classifyBuilderDeposit JauneConsensus.Gloas.isValidBuilderDepositSignature
  simp only [stateDeposit, state, depositKey, firstMatch_list, builder, List.findIdx?_cons, h1, h2, hdom,
    blsVerify_true_of_head_zero _ _ _ h0]
  rfl

/-! ## Every exit outcome occurs (B4) -/

/-- One closed witness per exit reason, in the spec's order; `pendingBalance` twice, once from a
pending withdrawal alone (every pending payment is zero) and once from a pending payment alone
(no pending withdrawal). -/
theorem every_exit_outcome_occurs (ccfg : Config) :
    (∃ (m : MinimalGloasState) (r : ExitRequest),
      classifyBuilderExit ccfg m r = .ok .unknownPubkey) ∧
    (∃ (m : MinimalGloasState) (r : ExitRequest),
      classifyBuilderExit ccfg m r = .ok (.notActive .notFinalized)) ∧
    (∃ (m : MinimalGloasState) (r : ExitRequest),
      classifyBuilderExit ccfg m r = .ok (.notActive .alreadyExiting)) ∧
    (∃ (m : MinimalGloasState) (r : ExitRequest),
      classifyBuilderExit ccfg m r = .ok .wrongSource) ∧
    (∃ (m : MinimalGloasState) (r : ExitRequest),
      classifyBuilderExit ccfg m r = .ok .pendingBalance ∧
      (∀ p ∈ m.builder_pending_payments.toArray, p.withdrawal.amount = U64.zero) ∧
      m.builder_pending_withdrawals.toArray.size = 1) ∧
    (∃ (m : MinimalGloasState) (r : ExitRequest),
      classifyBuilderExit ccfg m r = .ok .pendingBalance ∧
      m.builder_pending_withdrawals.toArray = #[]) ∧
    (∃ (m : MinimalGloasState) (r : ExitRequest) (i : Nat),
      classifyBuilderExit ccfg m r = .ok (.initiate i)) := by
  refine ⟨⟨_, _, witness_unknown ccfg⟩, ⟨_, _, witness_notFinalized ccfg⟩, ⟨_, _, witness_alreadyExiting ccfg⟩,
    ⟨_, _, witness_wrongSource ccfg⟩, ⟨_, _, witness_pendingWithdrawal ccfg, ?_, rfl⟩,
    ⟨_, _, witness_pendingPayment ccfg, rfl⟩, ⟨_, _, _, witness_initiate ccfg⟩⟩
  intro p hp
  have hp' : p ∈ Array.replicate (2 * Preset.minimal.SLOTS_PER_EPOCH)
      (default : JauneConsensus.Gloas.BuilderPendingPayment) := hp
  rw [Array.mem_replicate] at hp'
  rw [hp'.2]
  rfl

/-! ## The G3-01 control: duplicate builder pubkeys -/

/-- Builders 0 and 1 share pubkey 1; builder 0's address is 2, builder 1's address is `A = 1`;
both active, nothing pending. -/
def stateDuplicate : MinimalGloasState :=
  state #[builder 1 ⟨2⟩ ⟨10⟩ ⟨0⟩ FAR_FUTURE_EPOCH, builder 1 ⟨1⟩ ⟨10⟩ ⟨0⟩ FAR_FUTURE_EPOCH]

/-- The control state violates G3-01 (`BuilderPubkeysUnique`), and builder 1's address is `A`. -/
theorem builderPubkeysUnique_state :
    (∃ b0 b1, stateDuplicate.builders.toArray[0]? = some b0 ∧ stateDuplicate.builders.toArray[1]? = some b1 ∧
      b0.pubkey = b1.pubkey ∧ b1.execution_address = address ⟨1⟩ ∧ b0.execution_address ≠ address ⟨1⟩) :=
  ⟨_, _, rfl, rfl, rfl, rfl, by decide⟩

/-- An exit request from `A` for the shared key resolves to builder 0 and is `wrongSource`. -/
theorem builderPubkeysUnique_wrongSource (ccfg : Config) :
    classifyBuilderExit ccfg stateDuplicate (exitRequest ⟨1⟩ 1) = .ok .wrongSource := by
  unfold classifyBuilderExit
  simp only [stateDuplicate, state, exitRequest, firstMatch_list]
  rfl

/-- Builder 1 can never be exited on this state, by any request (in particular not from its own
address `A`): resolution is first-match. -/
theorem builderPubkeysUnique_builderOne_never_initiated (ccfg : Config) (r : ExitRequest) :
    classifyBuilderExit ccfg stateDuplicate r ≠ .ok (.initiate 1) := by
  intro h
  have hm := classifyBuilderExit_meaning h
  obtain ⟨b, bi, hfm, -⟩ := (hm.2.2.2.2.2.1 1).mp rfl
  obtain ⟨⟨b1, hb1, hpk1⟩, -⟩ := firstMatch_some hfm
  exact hm.2.2.2.2.2.2 1 rfl 0 (by decide) (builder 1 ⟨2⟩ ⟨10⟩ ⟨0⟩ FAR_FUTURE_EPOCH) rfl
    (by
      have : b1 = builder 1 ⟨1⟩ ⟨10⟩ ⟨0⟩ FAR_FUTURE_EPOCH := by
        simp only [stateDuplicate, state] at hb1; simpa using hb1.symm
      rw [← hpk1, this]; rfl)

/-- The same key from builder 0's address initiates builder 0. -/
theorem builderPubkeysUnique_initiateZero (ccfg : Config) :
    classifyBuilderExit ccfg stateDuplicate (exitRequest ⟨2⟩ 1) = .ok (.initiate 0) := by
  unfold classifyBuilderExit
  simp only [stateDuplicate, state, exitRequest, firstMatch_list]
  rfl

/-- **The control bites.** Without G3-01 the frozen unique-resolution clause of B4
(`o = .initiate i → ∀ i', builders[i'].pubkey = r.pubkey → i' = i`) fails on `sDup`: the request
initiates builder 0 while builder 1 carries the same pubkey. -/
theorem builderPubkeysUnique_unique_resolution_fails (ccfg : Config) :
    ¬ ∀ (r : ExitRequest) (i : Nat),
      classifyBuilderExit ccfg stateDuplicate r = .ok (.initiate i) →
      ∀ i' b', stateDuplicate.builders.toArray[i']? = some b' → b'.pubkey = r.pubkey → i' = i := by
  intro h
  have := h (exitRequest ⟨2⟩ 1) 0 (builderPubkeysUnique_initiateZero ccfg) 1 (builder 1 ⟨1⟩ ⟨10⟩ ⟨0⟩ FAR_FUTURE_EPOCH) rfl rfl
  exact absurd this (by decide)

/-- ...while the first-match form (`classifyBuilderExit_meaning`'s last clause) holds on the same
state, as it does on every state. -/
theorem builderPubkeysUnique_first_match_holds (ccfg : Config) :
    ∀ (r : ExitRequest) (i : Nat),
      classifyBuilderExit ccfg stateDuplicate r = .ok (.initiate i) →
      ∀ j, j < i → ∀ b', stateDuplicate.builders.toArray[j]? = some b' → b'.pubkey ≠ r.pubkey :=
  fun _ i h => (classifyBuilderExit_meaning h).2.2.2.2.2.2 i rfl

end JauneConsensus.Facts.Gloas.Witnesses
