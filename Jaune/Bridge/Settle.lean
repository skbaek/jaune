import Jaune.Bridge.MessageCall
import Jaune.MessageCall.Settle

/-!
# `settle`, today's and the staged one (W1 unit C, bridge)

Today's `Frame.settle` returns a settled `Devm` that stores how the frame ended in `Meta.error`;
the staged `settle` returns a `Frame.Result`. `Frame.Result.ofSettled` reads the first as the
second, and `settle_legacy` says the two agree on every clean raw result, for every frame whose
messages are paired as `Frame.ofCall` and `Frame.ofCreate` pair them and whose saved state is the
outer message's world. The two companions pin what `ofSettled` forgets: a failed settled
result's world is the outer message's, and under state gas its refund is zero.

About today's definitions, and deleted with them after the gate's tag (the W1 design note,
third revision, sections 3.1 and 3.2, unit C).
-/

namespace Jaune

namespace Legacy

/-- What a top-level frame's saved state has in common with its messages: the inner message is
the outer one, after a creation's set-up; the saved state's world, created accounts and accessed
sets are the outer message's. `Frame.ofCall msg` and `Frame.ofCreate msg` have it with
`initDevm msg`. -/
structure Frame.TopCoherent (f : Jaune.Frame) (saved : Devm) : Prop where
  /-- The inner message is the outer one, set up for a creation. -/
  paired : f.inner = if f.isCreate then processCreateMessage.msg f.outer else f.outer
  /-- The saved state is the outer message's. -/
  state : f.outer.benv.state = saved.state
  /-- The saved storage writes are the outer message's. -/
  storageWrites : f.outer.benv.storageWrites = saved.world.storageWrites
  /-- The saved transient storage is the outer message's. -/
  transient : f.outer.tenv.transientStorage = saved.transientStorage
  /-- The saved created accounts are the outer message's. -/
  created : f.outer.benv.createdAccounts = saved.createdAccounts
  /-- The saved accessed addresses are the outer message's. -/
  accessedAddresses : f.outer.accessedAddresses = saved.accessedAddresses
  /-- The saved accessed storage keys are the outer message's. -/
  accessedStorageKeys : f.outer.accessedStorageKeys = saved.accessedStorageKeys

/-- `Frame.TopCoherent`, and the outer message's inherited deletions are the saved state's,
when the rules pay a self-destruct refund. A spawned child has it with its saved caller. -/
structure Frame.Coherent (f : Jaune.Frame) (saved : Devm) : Prop
    extends Frame.TopCoherent f saved where
  /-- The inherited deletions are the saved caller's, under rules with the refund. -/
  deletions : f.outer.inheritedDeletions =
    if f.outer.benv.stat.rules.settlement.selfdestructRefund = 0 then .emptyWithCapacity
    else saved.accountsToDelete

end Legacy

namespace Staging

/-- RIPEMD-160's address after recording a touch of `t`. -/
theorem recordTouch_contains_ripemd160 (rules : ForkRules) (cond : Bool) (t : Address) (d : Devm) :
    (d.recordTouch rules cond t).meta.touchedAccounts.contains ripemd160Address
      = ((rules.settlement.touchedSweep && cond && decide (accountExistsAndIsEmpty d.state t)
          && (t == ripemd160Address)) || d.meta.touchedAccounts.contains ripemd160Address) := by
  unfold Devm.recordTouch Devm.setMeta
  dsimp only
  split
  · rename_i hc
    rw [Std.HashSet.contains_insert]
    simp only [hc, Bool.true_and]
  · rename_i hc
    simp only [Bool.not_eq_true] at hc
    simp [hc]

/-- RIPEMD-160's address after a failed frame records its own touch. -/
theorem recordTouch_self_contains_ripemd160 (rules : ForkRules) (t : Address) (d : Devm) :
    (d.recordTouch rules (t == ripemd160Address) t).meta.touchedAccounts.contains ripemd160Address
      = ((rules.settlement.touchedSweep && (t == ripemd160Address)
          && decide (accountExistsAndIsEmpty d.state t))
        || d.meta.touchedAccounts.contains ripemd160Address) := by
  rw [recordTouch_contains_ripemd160]
  cases (t == ripemd160Address) <;> simp

@[simp] theorem recordTouch_meta_error (rules : ForkRules) (cond : Bool) (t : Address)
    (d : Devm) : (d.recordTouch rules cond t).meta.error = d.meta.error := rfl
@[simp] theorem recordTouch_meta_output (rules : ForkRules) (cond : Bool) (t : Address)
    (d : Devm) : (d.recordTouch rules cond t).meta.output = d.meta.output := rfl
@[simp] theorem recordTouch_meta_createdAccounts (rules : ForkRules) (cond : Bool) (t : Address)
    (d : Devm) : (d.recordTouch rules cond t).meta.createdAccounts = d.meta.createdAccounts := rfl
@[simp] theorem recordTouch_accountReads (rules : ForkRules) (cond : Bool) (t : Address)
    (d : Devm) : (d.recordTouch rules cond t).meta.accountReads = d.meta.accountReads := rfl
@[simp] theorem recordTouch_storageReads (rules : ForkRules) (cond : Bool) (t : Address)
    (d : Devm) : (d.recordTouch rules cond t).meta.storageReads = d.meta.storageReads := rfl
@[simp] theorem recordTouch_createdAccounts (rules : ForkRules) (cond : Bool) (t : Address)
    (d : Devm) : (d.recordTouch rules cond t).createdAccounts = d.createdAccounts := rfl

/-- A halt-only result as today's raw result. -/
def ofHalting : Except (ExceptionalHalt × Devm) Devm → Execution
  | .ok d => .ok d
  | .error (reason, d) => .error (.halt reason, d)

/-- Today's execution-gas charge is the halt-only one. -/
theorem chargeGas_legacy (cost : Nat) (d : Devm) :
    chargeGas cost d = ofHalting (Devm.chargeGas cost d) := by
  unfold chargeGas liftMachExecution liftMach Footprint.liftOutcome Footprint.toExecution
    Mach.chargeGas Devm.chargeGas
  simp only [Devm.gasLeft]
  cases safeSub d.mach.gasLeft cost <;> rfl

/-- Today's state-gas charge is the halt-only one. -/
theorem chargeStateGas_legacy (amount : Nat) (d : Devm) :
    chargeStateGas amount d = ofHalting (Devm.chargeStateGas amount d) := by
  unfold chargeStateGas liftMachExecution liftMach Footprint.liftOutcome Footprint.toExecution
    Mach.chargeStateGas Devm.chargeStateGas
  by_cases h1 : amount ≤ d.mach.stateGas.left
  · simp only [h1, ite_true]; rfl
  · by_cases h2 : amount - d.mach.stateGas.left ≤ d.mach.gasLeft
    · simp only [h1, h2, ite_true, ite_false]; rfl
    · simp only [h1, h2, ite_false]; rfl

/-- Today's code-deposit charge is the halt-only one. -/
theorem chargeCodeGas_legacy (rules : ForkRules) (d : Devm) :
    processCreateMessage.chargeCodeGas rules d = ofHalting (chargeDeposit rules d.output d) := by
  unfold processCreateMessage.chargeCodeGas chargeDeposit
  cases rules.stateGas with
  | none =>
    dsimp only
    generalize d.output = code
    rw [chargeGas_legacy]
    cases h : Devm.chargeGas (code.length * Gas.codeDeposit) d with
    | error p =>
      obtain ⟨r, e⟩ := p
      split <;> (try split) <;> simp [ofHalting, bind, Except.bind]
    | ok e =>
      split <;> (try split) <;> simp [ofHalting, bind, Except.bind]
      all_goals split <;> rfl
  | some state =>
    dsimp only
    generalize d.output = code
    simp only [chargeGas_legacy, chargeStateGas_legacy]
    cases h : Devm.chargeGas (Gas.keccak256Word * ceilDiv code.length 32) d with
    | error p =>
      obtain ⟨r, e⟩ := p
      split <;> (try split) <;> (try split) <;> simp_all [ofHalting, bind, Except.bind]
    | ok e =>
      split <;> (try split) <;> (try split) <;> simp_all [ofHalting, bind, Except.bind]

/-- The deposit charge moves only the meters. -/
theorem chargeDeposit_ok_meta {rules : ForkRules} {code : Bytes} {d e : Devm}
    (h : chargeDeposit rules code d = .ok e) : e.meta = d.meta := by
  have hg : ∀ {c : Nat} {d e : Devm}, Devm.chargeGas c d = .ok e → e.meta = d.meta := by
    intro c d e h
    unfold Devm.chargeGas at h
    split at h <;> cases h
    rfl
  have hs : ∀ {c : Nat} {d e : Devm}, Devm.chargeStateGas c d = .ok e → e.meta = d.meta := by
    intro c d e h
    unfold Devm.chargeStateGas at h
    split_ifs at h <;> cases h <;> rfl
  revert h
  unfold chargeDeposit
  cases rules.stateGas with
  | none =>
    dsimp only
    cases h1 : Devm.chargeGas (code.length * Gas.codeDeposit) d with
    | error p => split <;> (try split) <;> simp [bind, Except.bind]
    | ok d1 =>
      have m1 := hg h1
      split <;> (try split) <;> (try split) <;> simp_all [bind, Except.bind] <;>
        (intro h2; subst h2; exact m1)
  | some state =>
    dsimp only
    cases h1 : Devm.chargeGas (Gas.keccak256Word * ceilDiv code.length 32) d with
    | error p => split <;> (try split) <;> simp [bind, Except.bind]
    | ok d1 =>
      have m1 := hg h1
      split <;> (try split) <;> simp [bind, Except.bind]
      intro h2
      rw [hs h2, m1]

/-- A settled `Devm` of today as a frame result: its stored error chooses the constructor; a
failed frame's machine and world are forgotten, and its trail records whether RIPEMD-160's
address is among its touches. A fault keeps its reason and loses its state. Today's settlement
never returns a revert or a halt through the error channel; those two shapes are mapped to an
assertion fault. -/
def Frame.Result.ofSettled :
    Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm → Except Fault Frame.Result
  | .error (.crypto reason, _) => .error (.crypto reason)
  | .error (.internal reason, _) => .error (.internal reason)
  | .error (.revert, _) => .error (.internal (.assertion .none))
  | .error (.halt _, _) => .error (.internal (.assertion .none))
  | .ok d =>
    let trail : Trail :=
      { (Frame.State.ofDevm d).trail with
        touchedRIPEMD160 := d.meta.touchedAccounts.contains ripemd160Address }
    match d.error with
    | none => .ok (Frame.Result.ofSuccess d.output d)
    | some .revert => .ok (.revert d.output d.gasLeft d.stateGas trail)
    | some (.halt reason) => .ok (.halt reason d.stateGas trail)

/-- **Settle.** Today's settlement, read as a frame result, is the staged one, for every clean raw
result. -/
theorem settle_legacy (f : Jaune.Frame) (saved : Devm) (h : Legacy.Frame.TopCoherent f saved)
    (raw : Execution) (clean : raw.Clean) :
    Frame.Result.ofSettled (f.settle raw)
      = settle ⟨Message.ofLegacy f.outer f.isCreate, Frame.State.ofDevm saved⟩ raw := by
  rcases f with ⟨outer, inner, isCreate⟩
  obtain ⟨paired, hstate, -, -, -, -, -⟩ := h
  cases isCreate <;> simp only [ite_true, Bool.false_eq_true, ite_false] at paired <;> subst paired
  · simp only [Devm.state] at hstate
    rcases raw with ⟨e, d⟩ | d
    · cases e <;> cases hsg : inner.benv.stat.rules.stateGas <;>
        simp [Devm.error, Devm.withError, Devm.setMeta, Devm.withGasLeft, Devm.setMach,
          Devm.rollback, Devm.setWorld, Devm.withStorageWrites, Devm.restoreStateGas,
          Devm.withRefundCounter, Devm.forfeitRemainingGas, Devm.output, Devm.gasLeft,
          Devm.stateGas, Devm.createdAccounts, Jaune.Frame.settle, settle, Jaune.Frame.settleMsg,
          executeCode.handleErrorWith, executeCode.handleError, executeCode.handleErrorAmsterdam,
          processMessage.settle,
          Frame.Result.ofSettled, Message.ofLegacy, hsg, Frame.enteredWorld, bind, Except.bind,
          recordTouch_self_contains_ripemd160, Frame.State.ofDevm, Devm.state, ← hstate]
      all_goals rfl
    · simp only [Execution.Clean, Devm.error] at clean
      cases hsg : inner.benv.stat.rules.stateGas <;>
        simp [hsg, Devm.error, Devm.output, Jaune.Frame.settle, settle, Jaune.Frame.settleMsg,
          executeCode.handleErrorWith, executeCode.handleError, executeCode.handleErrorAmsterdam,
          processMessage.settle, Frame.Result.ofSettled, Message.ofLegacy, bind, Except.bind,
          clean]
  · simp only [Devm.state] at hstate
    rcases raw with ⟨e, d⟩ | d
    · cases e <;> cases hsg : outer.benv.stat.rules.stateGas <;>
        simp [Devm.error, Devm.withError, Devm.setMeta, Devm.withGasLeft, Devm.setMach,
          Devm.rollback, Devm.setWorld, Devm.withStorageWrites, Devm.restoreStateGas,
          Devm.withRefundCounter, Devm.forfeitRemainingGas, Devm.output, Devm.gasLeft,
          Devm.stateGas, Devm.createdAccounts, Jaune.Frame.settle, settle, Jaune.Frame.settleMsg,
          executeCode.handleErrorWith, executeCode.handleError, executeCode.handleErrorAmsterdam,
          processMessage.settle, Frame.Result.ofSettled, Message.ofLegacy, Frame.enteredWorld,
          bind, Except.bind, recordTouch_self_contains_ripemd160, Frame.State.ofDevm, Devm.state,
          processCreateMessage.settle, processCreateMessage.msg, Msg.withBenv, Benv.incrNonce,
          addCreatedAccount, Benv.setStor, Benv.clearStorageWritesIfEmpty, World.createSetUp,
          World.clearStorageWritesIfEmpty, hsg, ← hstate]
      all_goals rfl
    · simp only [Execution.Clean, Devm.error] at clean
      cases hsg : outer.benv.stat.rules.stateGas <;>
        simp [hsg, Devm.error, Devm.setMeta, Devm.withGasLeft, Devm.setMach, Devm.setWorld,
          Devm.withStorageWrites, Devm.restoreStateGas,
          Devm.withRefundCounter, Devm.forfeitRemainingGas, Devm.output, Devm.gasLeft,
          Devm.stateGas, Devm.createdAccounts, Jaune.Frame.settle, settle, Jaune.Frame.settleMsg,
          executeCode.handleErrorWith, executeCode.handleError, executeCode.handleErrorAmsterdam,
          processMessage.settle, Frame.Result.ofSettled, Message.ofLegacy, bind, Except.bind,
          Frame.State.ofDevm, Devm.state, processCreateMessage.settle, processCreateMessage.msg,
          Msg.withBenv, Benv.incrNonce, addCreatedAccount, Benv.setStor,
          Benv.clearStorageWritesIfEmpty, clean, chargeCodeGas_legacy, depositCode] <;>
      cases hc : chargeDeposit outer.benv.stat.rules d.meta.output
        (Devm.recordTouch outer.benv.stat.rules true outer.currentTarget d) with
      | ok e =>
        have hm := chargeDeposit_ok_meta hc
        simp only [Devm.recordTouch, Devm.setMeta] at hm
        simp [ofHalting, Except.map, Devm.setCode, Devm.withState, Devm.setWorld,
          Devm.clearStorageWritesIfEmpty, Devm.withStorageWrites, hm, clean,
          Frame.Result.ofSuccess, Frame.State.ofDevm]
      | error p =>
        obtain ⟨r, e⟩ := p
        simp [ofHalting, Except.map, processCreateMessage.exceptionalHalt,
          processCreateMessage.exceptionalHaltAmsterdam, Devm.rollback, Devm.setWorld,
          Devm.setMeta, Devm.withGasLeft, Devm.setMach, Devm.restoreStateGas,
          Devm.withRefundCounter, Devm.forfeitRemainingGas]

end Staging

namespace Legacy

/-- A failed result of `processMessage.settle` has the message's world. -/
theorem processMessage.settle_failed_world {msg : Msg}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm} {d : Devm}
    (hs : processMessage.settle msg r = .ok d) (hf : d.error.isSome) :
    d.world = { state := msg.benv.state, transientStorage := msg.tenv.transientStorage
                storageWrites := msg.benv.storageWrites } := by
  cases r with
  | error _ => cases hs
  | ok evm =>
    simp only [processMessage.settle, bind, Except.bind] at hs
    split at hs
    · cases hs; rfl
    · rename_i hn
      cases hs
      simp only [Devm.recordTouch_error] at hf
      exact absurd hf hn

/-- A failed result of `processCreateMessage.settle` has the message's world. -/
theorem processCreateMessage.settle_failed_world {msg : Msg}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm} {d : Devm}
    (hs : processCreateMessage.settle msg r = .ok d) (hf : d.error.isSome) :
    d.world = { state := msg.benv.state, transientStorage := msg.tenv.transientStorage
                storageWrites := msg.benv.storageWrites } := by
  cases r with
  | error _ => cases hs
  | ok evm =>
    simp only [processCreateMessage.settle, bind, Except.bind] at hs
    split at hs
    · rename_i hn
      rw [Staging.chargeCodeGas_legacy] at hs
      cases hc : Staging.chargeDeposit msg.benv.stat.rules evm.output evm with
      | ok e =>
        rw [hc] at hs
        cases hs
        have hm := Staging.chargeDeposit_ok_meta hc
        simp only [Devm.error, Devm.setCode, Devm.clearStorageWritesIfEmpty, Devm.withState,
          Devm.withStorageWrites, Devm.setWorld, hm] at hf
        simp_all [Devm.error]
      | error p =>
        obtain ⟨reason, e⟩ := p
        rw [hc] at hs
        simp only [Staging.ofHalting] at hs
        cases hs
        cases msg.benv.stat.rules.stateGas <;> rfl
    · cases hs; rfl

/-- A failed settled result's world is the outer message's. -/
theorem Frame.settle_failed_world (f : Jaune.Frame)
    (paired : f.inner = if f.isCreate then processCreateMessage.msg f.outer else f.outer)
    {raw : Execution} {d : Devm} (hs : f.settle raw = .ok d) (hf : d.error.isSome) :
    d.world = { state := f.outer.benv.state, transientStorage := f.outer.tenv.transientStorage
                storageWrites := f.outer.benv.storageWrites } := by
  rcases f with ⟨outer, inner, isCreate⟩
  simp only [Jaune.Frame.settle, Jaune.Frame.settleMsg] at hs
  cases isCreate <;> simp only [ite_true, Bool.false_eq_true, ite_false] at paired hs <;>
    subst paired
  · exact processMessage.settle_failed_world hs hf
  · exact processCreateMessage.settle_failed_world hs hf

/-- `processMessage.settle` keeps the stored error and the refund of a successful input. -/
theorem processMessage.settle_ok {msg : Msg}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm} {d : Devm}
    (hs : processMessage.settle msg r = .ok d) :
    ∃ evm, r = .ok evm ∧ d.error = evm.error ∧ d.refundCounter = evm.refundCounter := by
  cases r with
  | error _ => cases hs
  | ok evm =>
    simp only [processMessage.settle, bind, Except.bind] at hs
    split at hs <;> cases hs <;> exact ⟨evm, rfl, rfl, rfl⟩

/-- Amsterdam's raw settlement leaves a failed frame no refund, given a clean raw result. -/
theorem handleErrorAmsterdam_failed_refund {raw : Execution} (clean : raw.Clean) {x : Devm}
    (h : executeCode.handleErrorAmsterdam raw = .ok x) (hf : x.error.isSome) :
    x.refundCounter = 0 := by
  rcases raw with ⟨e, d0⟩ | d0
  · cases e <;> simp [executeCode.handleErrorAmsterdam] at h <;> subst h <;> rfl
  · simp only [executeCode.handleErrorAmsterdam, Except.ok.injEq] at h
    subst h
    simp only [Execution.Clean] at clean
    simp [clean] at hf

/-- `processCreateMessage.settle` succeeds only on a successful input. -/
theorem processCreateMessage.settle_ok_input {msg : Msg}
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm} {d : Devm}
    (hs : processCreateMessage.settle msg r = .ok d) : ∃ evm, r = .ok evm := by
  cases r with
  | error _ => cases hs
  | ok evm => exact ⟨evm, rfl⟩

/-- Under state gas `processCreateMessage.settle` leaves a failed frame no refund, when its
input has none on failure. -/
theorem processCreateMessage.settle_failed_refund {msg : Msg} {sg : StateGasRules}
    (hsg : msg.benv.stat.rules.stateGas = some sg) {evm d : Devm}
    (hin : evm.error.isSome → evm.refundCounter = 0)
    (hs : processCreateMessage.settle msg (.ok evm) = .ok d) (hf : d.error.isSome) :
    d.refundCounter = 0 := by
  simp only [processCreateMessage.settle, bind, Except.bind] at hs
  split at hs
  · rename_i hn
    rw [Staging.chargeCodeGas_legacy] at hs
    cases hc : Staging.chargeDeposit msg.benv.stat.rules evm.output evm with
    | ok e =>
      rw [hc] at hs
      cases hs
      have hm := Staging.chargeDeposit_ok_meta hc
      simp only [Devm.error, Devm.setCode, Devm.clearStorageWritesIfEmpty, Devm.withState,
        Devm.withStorageWrites, Devm.setWorld, hm] at hf
      simp_all [Devm.error]
    | error p =>
      obtain ⟨reason, e⟩ := p
      rw [hc] at hs
      simp only [Staging.ofHalting, hsg] at hs
      cases hs
      rfl
  · rename_i hn
    cases hs
    simp only [Devm.error, Option.isNone_iff_eq_none] at hn
    exact hin (by simpa [Devm.error, Option.isSome_iff_ne_none] using hn)

/-- Under state gas a failed settled result has refund zero, given a clean raw result. -/
theorem Frame.settle_failed_refund (f : Jaune.Frame)
    (paired : f.inner = if f.isCreate then processCreateMessage.msg f.outer else f.outer)
    (hrules : f.outer.benv.stat.rules.stateGas.isSome) {raw : Execution} (clean : raw.Clean)
    {d : Devm} (hs : f.settle raw = .ok d) (hf : d.error.isSome) :
    d.refundCounter = 0 := by
  obtain ⟨sg, hsg⟩ := Option.isSome_iff_exists.mp hrules
  have hinner : f.inner.benv.stat.rules.stateGas = some sg := by
    rw [paired]; split <;> exact hsg
  simp only [Jaune.Frame.settle, Jaune.Frame.settleMsg, executeCode.handleErrorWith, hinner] at hs
  have key : ∀ {d : Devm}, processMessage.settle f.inner
      (executeCode.handleErrorAmsterdam raw) = .ok d → d.error.isSome → d.refundCounter = 0 := by
    intro d h hf
    obtain ⟨x, hx, he, hr⟩ := processMessage.settle_ok h
    rw [hr]
    exact handleErrorAmsterdam_failed_refund clean hx (he ▸ hf)
  split at hs
  · obtain ⟨evm, hx⟩ := processCreateMessage.settle_ok_input hs
    rw [hx] at hs
    exact processCreateMessage.settle_failed_refund hsg (key hx) hs hf
  · exact key hs hf

end Legacy

end Jaune
