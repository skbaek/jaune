import Jaune.Transaction

/-!
# The top-level message run (goal `jaune-shape-and-names-v1`, W2 cut B1)

A top-level message call is a preparation followed by at most one frame:

* `TopLevel.prepare` builds the frame the message runs, or refuses it. Without state gas a
  creation is refused on an address collision, and a call is first authorized and its delegation
  resolved; with state gas `prepareTopLevelAmsterdam` prepares the machine, and an exceptional
  halt during preparation is a refusal. Its faults are cryptographic or internal: preparation
  never reverts (`prepareTopLevelAmsterdam_error_ne_revert`), and the ordinary authorization fails
  only by a fault (`processMessageCall.authorize_error_isFault`).
* `Message.run` runs the prepared frame by entering it from its checkpoint, running the code and
  settling, as `Frame.runTop` does, and records what it ran in a `MessageRun`.
* `MessageRun.output` renders the run as the transaction reads it, through `Frame.output`,
  `Frame.outputAmsterdam` and `settleTopLevelPreparationFailure`.

The Amsterdam preparation helpers are public here; their earlier copies in `Jaune.Transaction`
were private. Everything is staged under `Jaune.Staging` beside today's `processMessageCall`, and
nothing in today's pipeline reads it until the switch commit. The bridges are in
`Jaune.Bridge.G2a.Run`.
-/

namespace Jaune.Staging

open Jaune

/-! ### Amsterdam top-level preparation, public

The dual-gas fork prices state-dependent transaction dispatch in the top frame, before bytecode
starts. The preparation machine therefore carries the real top-frame meters and world. A
successful delegation phase commits its state gas; a later preparation failure restores the
transaction-entry reservoir and world. -/

/-- What one authorization tuple leaves behind under Amsterdam's rules: the machine, the
accounts whose write has been paid for, and the accounts a delegation has been set for. -/
abbrev AmsterdamDelegationResult := Devm × AdrSet × AdrSet

/-- Charge the new-account state gas for an authority that does not exist yet. -/
def chargeNewAuthorityAmsterdam (state : StateGasRules)
    (authority : Address) (devm : Devm) : Execution :=
  if ¬ AccountExists devm.state authority then
    chargeStateGas state.newAccount devm
  else .ok devm

/-- Charge the account-write gas for an authority once per transaction. -/
def chargePaidAccountWriteAmsterdam (state : StateGasRules)
    (authority : Address) (devm : Devm) (paidWrites : AdrSet) :
    Except (EvmError × Devm) (Devm × AdrSet) :=
  if paidWrites.contains authority then
    .ok ⟨devm, paidWrites⟩
  else do
    let devm ← chargeGas state.accountWrite devm
    .ok ⟨devm, paidWrites.insert authority⟩

/-- Charge the authorization base state gas for an authority that is neither delegated before
the transaction nor already given a delegation in it, and return the code to set. A zero target
clears the delegation and costs nothing. -/
def chargeAuthBaseAmsterdam (state : StateGasRules) (msg : Msg)
    (authority target : Address) (devm : Devm) (delegationSetFor : AdrSet) :
    Except (EvmError × Devm) (Devm × AdrSet × ByteArray) :=
  if target = 0 then
    .ok ⟨devm, delegationSetFor, .empty⟩
  else do
    let delegatedBeforeTx :=
      isValidDelegation (msg.benv.stat.origState.getCode authority)
    let devm ←
      if ¬ delegatedBeforeTx && ¬ delegationSetFor.contains authority then
        chargeStateGas state.authBase devm
      else .ok devm
    .ok ⟨devm, delegationSetFor.insert authority,
      (eoaDelegationMarker ++ target.toBytes).toByteArray⟩

/-- Apply one validated authorization tuple: charge it, set the authority's code and bump its
nonce. -/
def applyValidatedDelegationAmsterdam (state : StateGasRules)
    (msg : Msg) (authority target : Address) (devm : Devm)
    (paidWrites delegationSetFor : AdrSet) :
    Except (EvmError × Devm) AmsterdamDelegationResult := do
  let devm ← chargeNewAuthorityAmsterdam state authority devm
  let (⟨devm, paidWrites⟩ : Devm × AdrSet) ←
    chargePaidAccountWriteAmsterdam state authority devm paidWrites
  let (⟨devm, delegationSetFor, codeToSet⟩ :
      Devm × AdrSet × ByteArray) ←
    chargeAuthBaseAmsterdam state msg authority target devm delegationSetFor
  let devm := (devm.setCode authority codeToSet).incrNonce authority
  .ok ⟨devm, paidWrites, delegationSetFor⟩

/-- One authorization tuple under Amsterdam's rules: skip an invalid one, otherwise apply it. -/
def setDelegationAmsterdamStep (state : StateGasRules) (msg : Msg)
    (auth : Authorization) (devm : Devm) (paidWrites delegationSetFor : AdrSet) :
    Except (EvmError × Devm) AmsterdamDelegationResult := do
  if auth.chainId != msg.benv.stat.chainId.toU256 && auth.chainId != 0 then
    .ok ⟨devm, paidWrites, delegationSetFor⟩
  else if auth.nonce = UInt64.max then
    .ok ⟨devm, paidWrites, delegationSetFor⟩
  else
    match recoverAuthority auth with
    | .error (.invalidSignature _) =>
      .ok ⟨devm, paidWrites, delegationSetFor⟩
    | .error err => .error ⟨.crypto err, devm⟩
    | .ok authority =>
      -- Recovery warms the authority even when a later validity check skips
      -- the tuple, and `get_account(authority)` reads it (EIP-7928).
      let devm := addAccessedAddress devm authority
      let devm := devm.balReadAccount msg.benv.stat.rules authority
      let authorityAccount := devm.state.get authority
      if ¬ (authorityAccount.code.isEmpty ∨
          isValidDelegation authorityAccount.code) then
        .ok ⟨devm, paidWrites, delegationSetFor⟩
      else if authorityAccount.nonce != auth.nonce then
        .ok ⟨devm, paidWrites, delegationSetFor⟩
      else
        applyValidatedDelegationAmsterdam state msg authority auth.address
          devm paidWrites delegationSetFor

/-- The authorization tuples in order under Amsterdam's rules. -/
def setDelegationAmsterdamLoop (state : StateGasRules) (msg : Msg) :
    List Authorization → Devm → AdrSet → AdrSet →
      Except (EvmError × Devm) AmsterdamDelegationResult
  | [], devm, paidWrites, delegationSetFor =>
    .ok ⟨devm, paidWrites, delegationSetFor⟩
  | auth :: auths, devm, paidWrites, delegationSetFor => do
    let ⟨devm, paidWrites, delegationSetFor⟩ ←
      setDelegationAmsterdamStep state msg auth devm paidWrites delegationSetFor
    setDelegationAmsterdamLoop state msg auths devm paidWrites delegationSetFor

/-- The transaction's authorization list under Amsterdam's rules. The caller's write, and a
creation's or value transfer's target write, are already paid for. -/
def setDelegationAmsterdam (state : StateGasRules) (msg : Msg)
    (devm : Devm) : Execution := do
  let paidWrites := {msg.caller}
  let paidWrites :=
    if msg.target.isNone || msg.value != 0 then
      paidWrites.insert msg.currentTarget
    else paidWrites
  let ⟨devm, _, _⟩ ← setDelegationAmsterdamLoop state msg
    msg.tenv.stat.auths devm paidWrites .emptyWithCapacity
  .ok devm

/-- The top-level message on the prepared machine's world: its state, created accounts and
storage writes, its transient storage, and its accessed sets. -/
def preparedTopLevelMessage (msg : Msg) (devm : Devm) : Msg :=
  { msg with
    benv := {
      msg.benv with
      state := devm.state
      createdAccounts := devm.createdAccounts
      storageWrites := devm.world.storageWrites
    }
    tenv := {msg.tenv with transientStorage := devm.transientStorage}
    accessedAddresses := devm.accessedAddresses
    accessedStorageKeys := devm.accessedStorageKeys
  }

/-- Resolve a top-level call's delegation under Amsterdam's rules, charging its access. -/
def resolveTopLevelCallAmsterdam (msg : Msg) (devm : Devm) :
    Except (EvmError × Devm) (Msg × Devm) := do
  let ⟨delegated, codeAddress, accessCost⟩ :=
    msg.benv.stat.rules.delegationCost devm msg.currentTarget
  let devm ← chargeGas accessCost devm
  let ⟨code, devm⟩ := completeDelegationAccess devm delegated codeAddress
  -- `create_evm`: `get_account(code_address)` is a read (EIP-7928).
  let devm := devm.balReadAccount msg.benv.stat.rules codeAddress
  let msg := preparedTopLevelMessage msg devm
  .ok ⟨{
    msg with
    codeAddress := some codeAddress
    code := code
    disablePrecompiles := delegated
  }, devm⟩

/-- The creation or call dispatch `create_evm` performs under Amsterdam's rules. -/
def dispatchTopLevelAmsterdam (state : StateGasRules) (msg : Msg)
    (devm : Devm) : Except (EvmError × Devm) (Msg × Devm) := do
  -- `create_evm` reads the current target on both branches --
  -- `account_deployable`/`get_pre_state_account` for a creation,
  -- `resolve_delegated_code_address`'s `get_account(recipient)` for a call
  -- (EIP-7928).
  let devm := devm.balReadAccount msg.benv.stat.rules msg.currentTarget
  if msg.target.isNone then
    let isCollision :=
      accountHasCodeOrNonce devm.state msg.currentTarget
    if isCollision then
      .error ⟨.halt (.addressCollision .none), devm⟩
    else do
      let devm ←
        if (msg.benv.stat.origState.get msg.currentTarget).isEmpty then
          chargeStateGas state.newAccount devm
        else .ok devm
      .ok ⟨preparedTopLevelMessage msg devm, devm⟩
  else do
    let devm ←
      if msg.value != 0 && decide (devm.state.get msg.currentTarget).isEmpty then
        chargeStateGas state.newAccount devm
      else .ok devm
    resolveTopLevelCallAmsterdam msg devm

/-- Commit the delegation phase's state gas, then dispatch. -/
def finishTopLevelAmsterdam (state : StateGasRules) (msg : Msg)
    (devm : Devm) : Except (EvmError × Devm) (Msg × Devm) :=
  let devm :=
    if msg.tenv.stat.auths.isEmpty then devm else devm.commitStateGas
  dispatchTopLevelAmsterdam state msg devm

/-- Build the machine a top-level Amsterdam message call starts from: the initial `Devm`, then
the authorization tuples of an EIP-7702 transaction, then the state-gas commit and the
creation/call dispatch that `create_evm` performs. -/
def prepareTopLevelAmsterdam (state : StateGasRules) (msg : Msg) :
    Except (EvmError × Devm) (Msg × Devm) := do
  let devm := initDevm msg
  let devm ←
    if msg.tenv.stat.auths.isEmpty then .ok devm
    else setDelegationAmsterdam state msg devm
  finishTopLevelAmsterdam state msg devm

/-! ### Preparation never reverts

Every preparation error comes from a gas charge (an out-of-gas halt), the creation collision (a
halt) or authority recovery (a cryptographic failure). -/

/-- An error a top-level preparation may raise: an exceptional halt or a cryptographic failure. -/
def PreparationError : EvmError → Prop
  | .halt _ => True
  | .crypto _ => True
  | _ => False

/-- A computation whose every error is a `PreparationError`. -/
structure PreparationErrors {α : Type} (x : Except (EvmError × Devm) α) : Prop where
  of : ∀ e d, x = .error (e, d) → PreparationError e

theorem PreparationErrors.ok {α : Type} (a : α) :
    PreparationErrors (.ok a : Except (EvmError × Devm) α) :=
  ⟨fun _ _ h => by cases h⟩

theorem PreparationErrors.halt {α : Type} (reason : ExceptionalHalt) (d : Devm) :
    PreparationErrors (.error (.halt reason, d) : Except (EvmError × Devm) α) :=
  ⟨fun _ _ h => by cases h; trivial⟩

theorem PreparationErrors.crypto {α : Type} (reason : CryptoError) (d : Devm) :
    PreparationErrors (.error (.crypto reason, d) : Except (EvmError × Devm) α) :=
  ⟨fun _ _ h => by cases h; trivial⟩

theorem PreparationErrors.bind {α β : Type} {x : Except (EvmError × Devm) α}
    {f : α → Except (EvmError × Devm) β} (hx : PreparationErrors x)
    (hf : ∀ a, PreparationErrors (f a)) : PreparationErrors (x >>= f) := by
  refine ⟨fun e d h => ?_⟩
  cases hxa : x with
  | error p =>
    rw [hxa] at h
    cases h
    exact hx.of _ _ hxa
  | ok a =>
    rw [hxa] at h
    exact (hf a).of e d h

theorem PreparationErrors.ite {α : Type} {c : Prop} [Decidable c]
    {x y : Except (EvmError × Devm) α} (hx : PreparationErrors x) (hy : PreparationErrors y) :
    PreparationErrors (if c then x else y) := by
  split <;> assumption

theorem chargeGas_preparationErrors (cost : Nat) (devm : Devm) :
    PreparationErrors (chargeGas cost devm) := by
  refine ⟨fun e d h => ?_⟩
  simp only [chargeGas, liftMachExecution, Footprint.toExecution, liftMach, Footprint.liftOutcome,
    Mach.chargeGas] at h
  cases hs : safeSub devm.mach.gasLeft cost <;> simp [hs] at h
  obtain ⟨rfl, -⟩ := h
  trivial

theorem chargeStateGas_preparationErrors (amount : Nat) (devm : Devm) :
    PreparationErrors (chargeStateGas amount devm) := by
  refine ⟨fun e d h => ?_⟩
  simp only [chargeStateGas, liftMachExecution, Footprint.toExecution, liftMach,
    Footprint.liftOutcome, Mach.chargeStateGas] at h
  by_cases h1 : amount ≤ devm.mach.stateGas.left
  · simp [h1] at h
  · by_cases h2 : amount - devm.mach.stateGas.left ≤ devm.mach.gasLeft
    · simp [h1, h2] at h
    · simp [h1, h2] at h
      obtain ⟨rfl, -⟩ := h
      trivial

theorem chargeNewAuthorityAmsterdam_preparationErrors (state : StateGasRules)
    (authority : Address) (devm : Devm) :
    PreparationErrors (chargeNewAuthorityAmsterdam state authority devm) := by
  unfold chargeNewAuthorityAmsterdam
  exact .ite (chargeStateGas_preparationErrors _ _) (.ok _)

theorem chargePaidAccountWriteAmsterdam_preparationErrors (state : StateGasRules)
    (authority : Address) (devm : Devm) (paidWrites : AdrSet) :
    PreparationErrors (chargePaidAccountWriteAmsterdam state authority devm paidWrites) := by
  unfold chargePaidAccountWriteAmsterdam
  exact .ite (.ok _) (.bind (chargeGas_preparationErrors _ _) fun _ => .ok _)

theorem chargeAuthBaseAmsterdam_preparationErrors (state : StateGasRules) (msg : Msg)
    (authority target : Address) (devm : Devm) (delegationSetFor : AdrSet) :
    PreparationErrors
      (chargeAuthBaseAmsterdam state msg authority target devm delegationSetFor) := by
  unfold chargeAuthBaseAmsterdam
  dsimp only
  exact .ite (.ok _) (.ite (.bind (chargeStateGas_preparationErrors _ _) fun _ => .ok _)
    (.bind (.ok _) fun _ => .ok _))

theorem applyValidatedDelegationAmsterdam_preparationErrors (state : StateGasRules)
    (msg : Msg) (authority target : Address) (devm : Devm)
    (paidWrites delegationSetFor : AdrSet) :
    PreparationErrors (applyValidatedDelegationAmsterdam state msg authority target devm
      paidWrites delegationSetFor) := by
  unfold applyValidatedDelegationAmsterdam
  exact .bind (chargeNewAuthorityAmsterdam_preparationErrors ..) fun _ =>
    .bind (chargePaidAccountWriteAmsterdam_preparationErrors ..) fun _ =>
      .bind (chargeAuthBaseAmsterdam_preparationErrors ..) fun _ => .ok _

theorem setDelegationAmsterdamStep_preparationErrors (state : StateGasRules) (msg : Msg)
    (auth : Authorization) (devm : Devm) (paidWrites delegationSetFor : AdrSet) :
    PreparationErrors
      (setDelegationAmsterdamStep state msg auth devm paidWrites delegationSetFor) := by
  unfold setDelegationAmsterdamStep
  refine .ite (.ok _) (.ite (.ok _) ?_)
  split
  · exact .ok _
  · exact .crypto _ _
  · exact .ite (.ok _) (.ite (.ok _) (applyValidatedDelegationAmsterdam_preparationErrors ..))

theorem setDelegationAmsterdamLoop_preparationErrors (state : StateGasRules) (msg : Msg)
    (auths : List Authorization) (devm : Devm) (paidWrites delegationSetFor : AdrSet) :
    PreparationErrors
      (setDelegationAmsterdamLoop state msg auths devm paidWrites delegationSetFor) := by
  induction auths generalizing devm paidWrites delegationSetFor with
  | nil => exact .ok _
  | cons auth auths ih =>
    exact .bind (setDelegationAmsterdamStep_preparationErrors ..) fun _ => ih ..

theorem setDelegationAmsterdam_preparationErrors (state : StateGasRules) (msg : Msg)
    (devm : Devm) : PreparationErrors (setDelegationAmsterdam state msg devm) := by
  unfold setDelegationAmsterdam
  exact .bind (setDelegationAmsterdamLoop_preparationErrors ..) fun _ => .ok _

theorem resolveTopLevelCallAmsterdam_preparationErrors (msg : Msg) (devm : Devm) :
    PreparationErrors (resolveTopLevelCallAmsterdam msg devm) := by
  unfold resolveTopLevelCallAmsterdam
  exact .bind (chargeGas_preparationErrors _ _) fun _ => .ok _

theorem dispatchTopLevelAmsterdam_preparationErrors (state : StateGasRules) (msg : Msg)
    (devm : Devm) : PreparationErrors (dispatchTopLevelAmsterdam state msg devm) := by
  unfold dispatchTopLevelAmsterdam
  dsimp only
  exact .ite (.ite (.halt _ _)
      (.ite (.bind (chargeStateGas_preparationErrors _ _) fun _ => .ok _)
        (.bind (.ok _) fun _ => .ok _)))
    (.ite (.bind (chargeStateGas_preparationErrors _ _)
        fun _ => resolveTopLevelCallAmsterdam_preparationErrors _ _)
      (.bind (.ok _) fun _ => resolveTopLevelCallAmsterdam_preparationErrors _ _))

theorem prepareTopLevelAmsterdam_preparationErrors (state : StateGasRules) (msg : Msg) :
    PreparationErrors (prepareTopLevelAmsterdam state msg) := by
  unfold prepareTopLevelAmsterdam finishTopLevelAmsterdam
  dsimp only
  split
  · exact .bind (.ok _) fun _ => dispatchTopLevelAmsterdam_preparationErrors ..
  · exact .bind (setDelegationAmsterdam_preparationErrors ..) fun _ =>
      dispatchTopLevelAmsterdam_preparationErrors ..

/-- **A top-level Amsterdam preparation fails only by an exceptional halt or a cryptographic
failure.** -/
theorem prepareTopLevelAmsterdam_error {state : StateGasRules} {msg : Msg} {e : EvmError}
    {d : Devm} (h : prepareTopLevelAmsterdam state msg = .error (e, d)) :
    (∃ reason, e = .halt reason) ∨ (∃ reason, e = .crypto reason) := by
  have := (prepareTopLevelAmsterdam_preparationErrors state msg).of e d h
  cases e <;> simp_all [PreparationError]

/-- **A top-level Amsterdam preparation never reverts.** -/
theorem prepareTopLevelAmsterdam_error_ne_revert (state : StateGasRules) (msg : Msg)
    (d : Devm) : prepareTopLevelAmsterdam state msg ≠ .error (.revert, d) :=
  fun h => by simpa using prepareTopLevelAmsterdam_error h

/-! ### The ordinary top-level authorization fails only by a fault -/

/-- An `EvmError` that is a fault: cryptographic or internal. -/
def EvmError.IsFault : EvmError → Prop
  | .crypto _ => True
  | .internal _ => True
  | _ => False

/-- An `EvmError` known to be a fault, as one. -/
def EvmError.toFault : (e : EvmError) → EvmError.IsFault e → Fault
  | .crypto reason, _ => .crypto reason
  | .internal reason, _ => .internal reason
  | .halt _, h => h.elim
  | .revert, h => h.elim

@[simp] theorem EvmError.toFault_toEvmError (e : EvmError) (h : EvmError.IsFault e) :
    (EvmError.toFault e h).toEvmError = e := by
  cases e <;> first | rfl | exact h.elim

theorem setDelegationStep_error_isFault {auth : Authorization} {msg : Msg} {r : U256}
    {e : EvmError} (h : setDelegationStep auth msg r = .error e) : EvmError.IsFault e := by
  unfold setDelegationStep at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · cases h; trivial
      · dsimp only at h
        split at h
        · cases h
        · split at h <;> cases h

theorem setDelegationLoop_error_isFault {auths : List Authorization} {msg : Msg} {r : U256}
    {e : EvmError} (h : setDelegationLoop auths msg r = .error e) : EvmError.IsFault e := by
  induction auths generalizing msg r with
  | nil => cases h
  | cons auth auths ih =>
    simp only [setDelegationLoop] at h
    cases hs : setDelegationStep auth msg r with
    | error e' =>
      rw [hs] at h
      cases h
      exact setDelegationStep_error_isFault hs
    | ok p =>
      rw [hs] at h
      exact ih h

theorem setDelegation_error_isFault {msg : Msg} {e : EvmError}
    (h : setDelegation msg = .error e) : EvmError.IsFault e := by
  unfold setDelegation at h
  cases hl : setDelegationLoop msg.tenv.stat.auths msg 0 with
  | error e' =>
    rw [hl] at h
    cases h
    exact setDelegationLoop_error_isFault hl
  | ok p =>
    rw [hl] at h
    simp only [bind, Except.bind] at h
    split at h
    · cases h; trivial
    · cases h

/-- **The ordinary top-level authorization fails only by a fault.** -/
theorem processMessageCall.authorize_error_isFault {msg : Msg} {e : EvmError}
    (h : processMessageCall.authorize msg = .error e) : EvmError.IsFault e := by
  unfold processMessageCall.authorize at h
  split at h
  · cases h
  · cases hs : setDelegation msg with
    | error e' =>
      rw [hs] at h
      cases h
      exact setDelegation_error_isFault hs
    | ok p =>
      rw [hs] at h
      cases h

/-! ### The preparation and the run -/

/-- What a top-level message is prepared into: a frame to run, or a refusal before any frame. -/
inductive TopLevel.Preparation : Type
  /-- Run this frame. Its checkpoint is the state the message was prepared on: `initDevm` of the
  message (a creation without state gas), of the authorized and delegation-resolved message (a
  call without state gas), or the state `prepareTopLevelAmsterdam` returns. A call without state
  gas adds its authorization refund to the frame's. -/
  | frame (frame : Frame) (authorizationRefund : Nat)
  /-- Refused before any frame: a creation's address collision without state gas (`halted` is
  the message's initial machine, unread), or an exceptional halt during Amsterdam's preparation
  (`halted` is the machine at the halt). -/
  | refused (reason : ExceptionalHalt) (halted : Devm)

/-- Prepare a top-level message under Amsterdam's rules: a halt during preparation is a
refusal, and preparation never reverts. -/
def TopLevel.prepare.amsterdam (state : StateGasRules) (msg : Msg) (isCreate : Bool) :
    Except Fault TopLevel.Preparation :=
  match h : prepareTopLevelAmsterdam state msg with
  | .error (.halt reason, devm) => .ok (.refused reason devm)
  | .error (.revert, devm) => absurd h (prepareTopLevelAmsterdam_error_ne_revert state msg devm)
  | .error (.crypto reason, _) => .error (.crypto reason)
  | .error (.internal reason, _) => .error (.internal reason)
  | .ok (prepared, devm) =>
    .ok (.frame ⟨Message.ofTop prepared isCreate, Frame.State.ofDevm devm⟩ 0)

/-- Prepare a top-level creation. -/
def TopLevel.prepare.create (msg : Msg) : Except Fault TopLevel.Preparation :=
  match msg.benv.stat.rules.stateGas with
  | none =>
    if accountHasCodeOrNonce msg.benv.state msg.currentTarget then
      .ok (.refused (.addressCollision .none) (initDevm msg))
    else
      .ok (.frame (Frame.ofTop msg true) 0)
  | some state => TopLevel.prepare.amsterdam state msg true

/-- Prepare a top-level call. -/
def TopLevel.prepare.call (msg : Msg) : Except Fault TopLevel.Preparation :=
  match msg.benv.stat.rules.stateGas with
  | none =>
    match h : processMessageCall.authorize msg with
    | .error e => .error (EvmError.toFault e (processMessageCall.authorize_error_isFault h))
    | .ok (delegated, authorizationRefund) =>
      .ok (.frame (Frame.ofTop (Msg.resolveCodeDelegation delegated) false) authorizationRefund)
  | some state => TopLevel.prepare.amsterdam state msg false

/-- Prepare a top-level message: a creation when it has no target, otherwise a call. -/
def TopLevel.prepare (msg : Msg) : Except Fault TopLevel.Preparation :=
  if msg.target.isNone then TopLevel.prepare.create msg else TopLevel.prepare.call msg

/-- A top-level message run: the message as handed, its preparation, the machine its frame
entered the interpreter with, and the frame's result. -/
structure MessageRun : Type where
  /-- The message as handed. Its world is what a refusal reports. -/
  entry : Msg
  /-- The frame to run, or the refusal. -/
  preparation : TopLevel.Preparation
  /-- The machine the frame entered the interpreter with: none for a refusal, and for a frame
  that finished at entry (a precompile, a failed transfer or creation check). -/
  root : Option Evm
  /-- The frame's result: some exactly when the preparation is a frame. -/
  result : Option Frame.Result

/-- Run a top-level message: prepare it, then enter the frame from its checkpoint, run the code
and settle, as `Frame.runTop` does. -/
def Message.run (msg : Msg) : Except Fault MessageRun := do
  let preparation ← TopLevel.prepare msg
  match preparation with
  | .refused .. => pure ⟨msg, preparation, none, none⟩
  | .frame f _ =>
    match enterWith f f.checkpoint.toDevm with
    | .done result => do
      let r ← result
      pure ⟨msg, preparation, none, some r⟩
    | .run evm => do
      let r ← settle f (exec evm)
      pure ⟨msg, preparation, some evm, some r⟩

/-- What a top-level message run hands the transaction. A frame's result is rendered by
`Frame.output` (with its authorization refund) or, with state gas, by `Frame.outputAmsterdam`. A
refusal without state gas reports the message's state with a collision halt; with state gas it is
`settleTopLevelPreparationFailure`'s halt. -/
def MessageRun.output (run : MessageRun) : Except EvmError (State × MsgCallOutput) :=
  match run.preparation, run.result with
  | .frame f authorizationRefund, some r =>
    match run.entry.benv.stat.rules.stateGas with
    | none => f.output authorizationRefund r
    | some _ => f.outputAmsterdam r
  | .frame _ _, none =>
    -- Unreachable: `Message.run` records a result for every frame (`Message.run_result`). A
    -- breach is an internal invariant failure and fails closed.
    .error (.internal (.invariant (.text "message run: a frame without a result")))
  | .refused reason halted, _ =>
    match run.entry.benv.stat.rules.stateGas with
    | none =>
      .ok ⟨run.entry.benv.state,
        { gasLeft := 0, refundCounter := 0, logs := [],
          accountsToDelete := .emptyWithCapacity,
          error := .some (.halt reason), returnData := [] }⟩
    | some _ => settleTopLevelPreparationFailure run.entry (.halt reason) halted

/-- The top-level message call: the run, then what it hands the transaction. -/
def processMessageCall (msg : Msg) : Except EvmError (State × MsgCallOutput) := do
  let run ← (Message.run msg).mapError Fault.toEvmError
  run.output

/-- `Message.run` records a result exactly for a frame. -/
theorem Message.run_result {msg : Msg} {run : MessageRun} (h : Message.run msg = .ok run) :
    run.entry = msg ∧
      ((∃ f a, run.preparation = .frame f a) ↔ run.result.isSome) := by
  unfold Message.run at h
  obtain ⟨p, -, h⟩ := Except.bind_eq_ok h
  cases p with
  | refused reason halted =>
    cases h
    simp
  | frame f a =>
    dsimp only at h
    split at h
    · obtain ⟨r, -, h⟩ := Except.bind_eq_ok h
      cases h
      simp
    · obtain ⟨r, -, h⟩ := Except.bind_eq_ok h
      cases h
      simp

end Jaune.Staging
