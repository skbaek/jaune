import Jaune.Bridge.Settle
import Jaune.Bridge.CleanResult
import Jaune.MessageCall.Enter

/-!
# `enter`, today's and the staged one (W1 unit D, bridge)

Today's three entry paths, `Frame.enter` for a spawned child and for a top-level frame, and the
prepared Amsterdam top frame's entry (`TraceTransaction.preparedEntry`, the entry form of the
private `runPreparedTopFrame`), differ only in the `Devm` the machine starts with.
`Legacy.Frame.enterFrom` is today's entry with that `Devm` as a parameter; `enterFrom_legacy`
says it agrees with the staged `enterWith` whenever the start state, set on the world after the
value transfer, is that `Devm`. The three statements of the design note follow.

The prepared entry is defined in an adapter module, which a bridge may not import. It is
restated here verbatim as `Legacy.preparedEntry`; the two are the same function by `rfl`
(`TraceTransaction.preparedEntry = Legacy.preparedEntry`), which unit K2, where the adapter moves,
states where both are in scope.

About today's definitions, and deleted with them after the gate's tag (the W1 design note,
third revision, section 3.2, unit D).
-/

namespace Jaune

namespace Legacy

/-- A message's saved world. -/
def Msg.world (msg : Msg) : World :=
  ⟨msg.benv.state, msg.tenv.transientStorage, msg.benv.storageWrites⟩

/-- Today's frame entry, with the `Devm` the machine starts on as a function of the block
environment after the value transfer. -/
def Frame.enterFrom (f : Jaune.Legacy.Frame) (dyna : Benv → Devm) : FrameEntry :=
  match f.inner.benvAfterTransfer with
  | .error e => .done (f.settleMsg (.error e))
  | .ok benv =>
    let inner := f.inner.withBenv benv
    let evm : Evm := {pc := 0, sta := initSevm inner, dyna := dyna benv}
    match inner.codeAddress with
    | none => .run evm
    | some adr =>
      if !inner.disablePrecompiles && inner.benv.stat.rules.isPrecompile adr then
        .done (f.settle (executePrecompile evm adr))
      else .run evm

/-- `Frame.enter` starts the machine on the inner message's `initDevm`. -/
theorem Frame.enter_eq_enterFrom (f : Jaune.Legacy.Frame) :
    f.enter = Frame.enterFrom f (fun benv => initDevm (f.inner.withBenv benv)) := by
  unfold Jaune.Legacy.Frame.enter Frame.enterFrom executeCode.enter initEvm
  cases f.inner.benvAfterTransfer with
  | error e => rfl
  | ok benv =>
    dsimp only
    cases (f.inner.withBenv benv).codeAddress with
    | none => rfl
    | some adr => dsimp only; split_ifs <;> rfl

/-- The prepared top frame's entry, `TraceTransaction.preparedEntry`, restated verbatim. -/
def preparedEntry (frame : Jaune.Legacy.Frame) (prepared : Devm) : FrameEntry :=
  match frame.inner.benvAfterTransfer with
  | .error e => .done (frame.settleMsg (.error e))
  | .ok benv =>
    let inner := frame.inner.withBenv benv
    let dyna :=
      ((prepared.withState benv.state).withStorageWrites benv.storageWrites).withCreatedAccounts
        benv.createdAccounts
    let evm : Evm := {pc := 0, sta := initSevm inner, dyna := dyna}
    match inner.codeAddress with
    | none => .run evm
    | some adr =>
      if !inner.disablePrecompiles && inner.benv.stat.rules.isPrecompile adr then
        .done (frame.settle (executePrecompile evm adr))
      else .run evm

/-- The prepared entry starts the machine on the prepared state with the transferred world. -/
theorem preparedEntry_eq_enterFrom (frame : Jaune.Legacy.Frame) (prepared : Devm) :
    preparedEntry frame prepared = Frame.enterFrom frame (fun benv =>
      ((prepared.withState benv.state).withStorageWrites benv.storageWrites).withCreatedAccounts
        benv.createdAccounts) := rfl

/-- The value transfer fails only by an assertion. -/
theorem Msg.benvAfterTransfer_error {msg : Msg}
    {e : EvmError × Jaune.State × AdrSet × TransientStorage}
    (h : msg.benvAfterTransfer = .error e) : e.1 = .internal (.assertion .none) := by
  unfold Msg.benvAfterTransfer at h
  split at h
  · cases hs : msg.benv.subBal msg.caller msg.value <;>
      simp [hs, Option.toExcept, bind, Except.bind] at h
    subst h; rfl
  · cases h

/-- The value transfer keeps the static record and the created accounts. -/
theorem Msg.benvAfterTransfer_ok {msg : Msg} {benv : Benv} (h : msg.benvAfterTransfer = .ok benv) :
    benv.stat = msg.benv.stat ∧ benv.createdAccounts = msg.benv.createdAccounts := by
  unfold Msg.benvAfterTransfer at h
  split at h
  · cases hs : msg.benv.subBal msg.caller msg.value with
    | none => simp [hs, Option.toExcept, bind, Except.bind] at h
    | some b =>
      simp only [hs, Option.toExcept, bind, Except.bind, Except.ok.injEq] at h
      subst h
      unfold Benv.subBal at hs
      cases hw : msg.benv.state.subBal msg.caller msg.value <;>
        simp [hw, bind, Option.bind] at hs
      subst hs
      exact ⟨rfl, rfl⟩
  · cases h; exact ⟨rfl, rfl⟩

end Legacy

end Jaune

namespace Jaune

/-- Today's entry result as a staged one: a machine stays a machine, a settled result is read
by `Frame.Result.ofSettled`. -/
def Frame.Entry.ofLegacy : FrameEntry → Frame.Entry
  | .run evm => .run evm
  | .done r => .done (Frame.Result.ofSettled r)

/-- The staged value transfer on a message's saved world is today's. -/
theorem Message.transfer_legacy (msg : Msg) (isCreate : Bool) :
    (Message.ofLegacy msg isCreate).transfer (Legacy.Msg.world msg)
      = match msg.benvAfterTransfer with
        | .ok benv => .ok ⟨benv.state, msg.tenv.transientStorage, benv.storageWrites⟩
        | .error _ => .error (.internal (.assertion .none)) := by
  unfold Message.transfer Msg.benvAfterTransfer
  simp only [Message.ofLegacy]
  by_cases hc : msg.shouldTransferValue = true ∧ msg.value ≠ 0
  · simp only [ne_eq] at hc ⊢
    simp only [hc.1, hc.2, not_false_eq_true, and_self, ite_true]
    cases hs : msg.benv.state.subBal msg.caller msg.value with
    | none =>
      simp [World.subtractBalance, Legacy.Msg.world, Benv.subBal, hs, Option.toExcept, bind,
        Except.bind, Option.bind]
    | some st =>
      simp [World.subtractBalance, Legacy.Msg.world, Benv.subBal, hs, Option.toExcept, bind,
        Except.bind, Option.bind, World.addBalance, Benv.addBal, Benv.withState,
        World.clearStorageWritesIfEmpty, Benv.clearStorageWritesIfEmpty]
      rfl
  · simp only [ne_eq] at hc ⊢
    simp only [hc, ite_false]
    rfl

/-- The world a legacy frame is entered on is its inner message's. -/
theorem enteredWorld_legacy {f : Jaune.Legacy.Frame} {saved : Devm}
    (h : Legacy.Frame.TopCoherent f saved) :
    Frame.enteredWorld ⟨Message.ofLegacy f.outer f.isCreate, Frame.State.ofDevm saved⟩
      = Legacy.Msg.world f.inner := by
  obtain ⟨outer, inner, isCreate⟩ := f
  obtain ⟨paired, hstate, hwrites, htra, -, -, -⟩ := h
  cases isCreate <;> simp only [ite_true, Bool.false_eq_true, ite_false] at paired <;>
    subst paired <;> dsimp only at hstate hwrites htra
  · simp only [Frame.enteredWorld, Message.ofLegacy, Frame.State.ofDevm, Legacy.Msg.world,
      Bool.false_eq_true, ite_false, hstate, hwrites, htra]
    rfl
  · simp only [Frame.enteredWorld, Message.ofLegacy, Frame.State.ofDevm, Legacy.Msg.world,
      ite_true, hstate, hwrites, htra, World.createSetUp, processCreateMessage.msg,
      Msg.withBenv, Benv.incrNonce, addCreatedAccount, Benv.setStor,
      Benv.clearStorageWritesIfEmpty, World.clearStorageWritesIfEmpty]
    rfl

/-- **Entry, from a given start.** Today's entry agrees with the staged one when its start
`Devm` is the staged start state set on the world after the value transfer, and the start state
stores no error. -/
theorem enterFrom_legacy (f : Jaune.Legacy.Frame) (saved start : Devm)
    (h : Legacy.Frame.TopCoherent f saved) (dyna : Benv → Devm) (clean : start.error = none)
    (hd : ∀ benv, f.inner.benvAfterTransfer = .ok benv →
      dyna benv = (start.setWorld ⟨benv.state, f.inner.tenv.transientStorage,
        benv.storageWrites⟩).withCreatedAccounts benv.createdAccounts) :
    Frame.Entry.ofLegacy (Legacy.Frame.enterFrom f dyna)
      = enterWith ⟨Message.ofLegacy f.outer f.isCreate, Frame.State.ofDevm saved⟩ start := by
  have hw := enteredWorld_legacy h
  have hm : Message.ofLegacy f.outer f.isCreate = Message.ofLegacy f.inner f.isCreate := by
    rw [h.paired]; split <;> rfl
  have ht := Message.transfer_legacy f.inner f.isCreate
  rw [← hm] at ht
  unfold enterWith Legacy.Frame.enterFrom
  dsimp only
  rw [hw, ht]
  cases hb : f.inner.benvAfterTransfer with
  | error e =>
    have he := Legacy.Msg.benvAfterTransfer_error hb
    obtain ⟨e1, rest⟩ := e
    simp only at he
    subst he
    simp only [Frame.Entry.ofLegacy, Jaune.Legacy.Frame.settleMsg, processMessage.settle,
      processCreateMessage.settle, bind, Except.bind]
    split <;> rfl
  | ok benv =>
    obtain ⟨hstat, hcreated⟩ := Legacy.Msg.benvAfterTransfer_ok hb
    have hca : (Message.ofLegacy f.outer f.isCreate).codeAddress
        = (f.inner.withBenv benv).codeAddress := by rw [hm]; rfl
    have hdp : (Message.ofLegacy f.outer f.isCreate).disablePrecompiles
        = (f.inner.withBenv benv).disablePrecompiles := by rw [hm]; rfl
    have hru : (Message.ofLegacy f.outer f.isCreate).context.block.rules
        = (f.inner.withBenv benv).benv.stat.rules := by
      rw [hm]; simp only [Message.ofLegacy, Msg.withBenv, hstat]
    have hs : (Message.ofLegacy f.outer f.isCreate).sevm = initSevm (f.inner.withBenv benv) := by
      rw [hm]; simp only [Message.sevm, initSevm, Message.ofLegacy, Msg.withBenv, hstat]
    have hcr : Frame.enteredCreatedAccounts
        ⟨Message.ofLegacy f.outer f.isCreate, Frame.State.ofDevm saved⟩ = benv.createdAccounts := by
      rw [hcreated, h.paired]
      unfold Frame.enteredCreatedAccounts
      have hc := h.created
      cases f.isCreate <;> simp only [Message.ofLegacy, Frame.State.ofDevm, ite_true, ite_false,
        Bool.false_eq_true, processCreateMessage.msg, Msg.withBenv, Benv.incrNonce,
        addCreatedAccount, Benv.setStor, Benv.clearStorageWritesIfEmpty, hc]
    simp only [hca, hdp, hru, hs, hcr, hd benv hb]
    cases (f.inner.withBenv benv).codeAddress with
    | none => rfl
    | some adr =>
      dsimp only
      split_ifs
      · simp only [Frame.Entry.ofLegacy]
        congr 1
        rw [← hd benv hb]
        apply settle_legacy f saved h
        cases hp : executePrecompile ⟨0, initSevm (f.inner.withBenv benv), dyna benv⟩ adr with
        | error _ => trivial
        | ok d =>
          have := Legacy.executePrecompile_ok_error hp
          simp only [Execution.Clean]
          rw [this, hd benv hb]
          exact clean
      · rfl

/-- The logs a frame starts with today are the staged `transferLogs`. -/
theorem initDevm_logs (msg : Msg) (isCreate : Bool) :
    (initDevm msg).meta.logs
      = transferLogs msg.benv.stat.rules (Message.ofLegacy msg isCreate) := by
  unfold initDevm transferLogs
  cases msg.benv.stat.rules.stateGas with
  | none => rfl
  | some _ =>
    simp only [Message.ofLegacy]
    by_cases hv : msg.shouldTransferValue = true
    · simp only [hv, ite_true, true_and]
      unfold Devm.emitTransferLog
      split_ifs <;> simp_all [Devm.logs, Devm.addLog, liftMachMetaPure, Meta.addLog]
    · simp [hv]

/-- The inner message of a legacy frame reads like the outer one, except for its block
environment. -/
theorem inner_fields {f : Jaune.Legacy.Frame}
    (paired : f.inner = if f.isCreate then processCreateMessage.msg f.outer else f.outer) :
    Message.ofLegacy f.inner f.isCreate = Message.ofLegacy f.outer f.isCreate ∧
      f.inner.tenv = f.outer.tenv ∧ f.inner.benv.stat = f.outer.benv.stat ∧
      f.inner.inheritedDeletions = f.outer.inheritedDeletions ∧
      f.inner.accessedAddresses = f.outer.accessedAddresses ∧
      f.inner.accessedStorageKeys = f.outer.accessedStorageKeys := by
  rw [paired]; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Enter, a spawned child.** -/
theorem enter_legacy (f : Jaune.Legacy.Frame) (rsm : Resume) (h : Legacy.Frame.Coherent f rsm.parent) :
    Frame.Entry.ofLegacy f.enter = enter (Frame.ofLegacy f rsm) := by
  rw [Legacy.Frame.enter_eq_enterFrom]
  apply enterFrom_legacy f rsm.parent _ h.toTopCoherent _ rfl
  intro benv hb
  obtain ⟨hstat, hcreated⟩ := Legacy.Msg.benvAfterTransfer_ok hb
  obtain ⟨hm, htenv, hst, hdel, hacc, hkeys⟩ := inner_fields h.paired
  have hlogs := initDevm_logs (f.inner.withBenv benv) f.isCreate
  apply Devm.ext <;>
    simp only [Frame.start, Frame.startState, Frame.State.toDevm, Devm.setWorld,
      Devm.withCreatedAccounts, Devm.setMeta, Frame.ofLegacy, Frame.State.ofDevm, ← hm]
  · rfl
  · apply Meta.ext
    · rw [hlogs]; simp only [transferLogs, Message.ofLegacy, Msg.withBenv, hstat]; rfl
    all_goals first
      | rfl
      | simp [initDevm, Msg.withBenv, hdel, h.deletions, hst, hacc, hkeys, h.accessedAddresses,
          h.accessedStorageKeys, Devm.accountsToDelete, Devm.accessedAddresses,
          Devm.accessedStorageKeys, Message.ofLegacy]
  · rfl

/-- **Enter, a top-level frame of today.** It starts from its message's `initDevm`. -/
theorem enterWith_top (msg : Msg) (isCreate : Bool) :
    Frame.Entry.ofLegacy
        (if isCreate then Jaune.Legacy.Frame.ofCreate msg else Jaune.Legacy.Frame.ofCall msg).enter
      = enterWith (Frame.ofTop msg isCreate) (initDevm msg) := by
  cases isCreate <;> simp only [ite_true, Bool.false_eq_true, ite_false] <;>
    rw [Legacy.Frame.enter_eq_enterFrom] <;>
    refine enterFrom_legacy _ (initDevm msg) (initDevm msg)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ _ rfl ?_ <;>
    intro benv hb <;>
    obtain ⟨hstat, -⟩ := Legacy.Msg.benvAfterTransfer_ok hb <;>
    apply Devm.ext <;> (try rfl) <;> apply Meta.ext <;> (try rfl) <;>
    rw [initDevm_logs _ false, Devm.withCreatedAccounts, Devm.setMeta, Devm.setWorld] <;>
    dsimp only <;> rw [initDevm_logs _ false] <;>
    simp only [transferLogs, Message.ofLegacy, Msg.withBenv, hstat] <;> rfl

/-- **Enter, the prepared top frame.** It starts from the prepared state, which must store no
error. -/
theorem enterWith_prepared (frame : Jaune.Legacy.Frame) (prepared : Devm)
    (h : Legacy.Frame.TopCoherent frame prepared) (clean : prepared.error = none) :
    Frame.Entry.ofLegacy (Legacy.preparedEntry frame prepared)
      = enterWith ⟨Message.ofLegacy frame.outer frame.isCreate, Frame.State.ofDevm prepared⟩
          prepared := by
  rw [Legacy.preparedEntry_eq_enterFrom]
  apply enterFrom_legacy frame prepared prepared h _ clean
  intro benv _
  obtain ⟨-, htenv, -⟩ := inner_fields h.paired
  have ht := h.transient
  simp only [Devm.withState, Devm.withStorageWrites, Devm.setWorld, htenv, ht,
    Devm.transientStorage]

end Jaune

