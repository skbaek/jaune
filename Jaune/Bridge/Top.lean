import Jaune.Transaction
import Jaune.Bridge.Driver
import Jaune.Bridge.Enter
import Jaune.Bridge.CleanResult

/-!
# The top level, today against the four-part chain (W1 unit I)

The anchor of the gate: `processMessageCall msg = Legacy.processMessageCall msg` for every
message and every `Fork`, plain `Eq`. The top frame is bridged through `Frame.runTop`; the
prepared Amsterdam frame through `enterWith_prepared` and the prepared-state lemma of
`Transaction`; the two renderings field by field. The old side waits in `Jaune.Legacy` and is
deleted with this module after the gate's tag.
-/

namespace Jaune

open Jaune

namespace Legacy

/-- What today's settlement guarantees, for a frame coherent with its top-level start. -/
theorem settledFacts_top {f : Jaune.Legacy.Frame} {parent : Devm} {rules : ForkRules}
    (h : Frame.TopCoherent f parent) (hr : f.outer.benv.stat.rules = rules) {raw : Execution}
    (clean : raw.Clean) : SettledFacts parent rules (f.settle raw) where
  fault := Frame.settle_error_isFault f raw
  world := fun hs hf => by
    rw [Frame.settle_failed_world f h.paired hs hf, h.state, h.transient, h.storageWrites]
    rfl
  refund := fun hs hf hsg => Frame.settle_failed_refund f h.paired (hr ▸ hsg) clean hs hf
  halted := Frame.settle_halted f clean

/-- `Frame.enter_done_facts` for a frame coherent with its top-level start. -/
theorem Frame.enter_done_facts_top {f : Jaune.Legacy.Frame} {parent : Devm} {rules : ForkRules}
    (h : Frame.TopCoherent f parent) (hr : f.outer.benv.stat.rules = rules)
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    (he : f.enter = .done r) : SettledFacts parent rules r := by
  rw [Frame.enter_eq_enterFrom] at he
  unfold Frame.enterFrom at he
  split at he
  · rename_i e hb
    cases he
    have hfault := Msg.benvAfterTransfer_error hb
    have hs : f.settleMsg (.error e) = .error e := by
      unfold Jaune.Legacy.Frame.settleMsg processMessage.settle processCreateMessage.settle
      split <;> rfl
    rw [hs]
    refine ⟨?_, fun hs _ => (nomatch hs), fun hs _ _ => (nomatch hs), fun hs _ => (nomatch hs)⟩
    intro e' st c t he'
    cases he'
    exact .inr ⟨_, hfault⟩
  · dsimp only at he
    split at he
    · cases he
    · split at he
      · cases he
        apply settledFacts_top h hr
        show Execution.Clean _
        cases hp : executePrecompile _ _ with
        | error _ => trivial
        | ok d => exact (executePrecompile_ok_error hp).trans rfl
      · cases he

/-- The top-level frames of today are coherent with their message's start. -/
theorem Frame.top_topCoherent (msg : Msg) (isCreate : Bool) :
    Frame.TopCoherent (if isCreate then Jaune.Legacy.Frame.ofCreate msg else Jaune.Legacy.Frame.ofCall msg)
      (initDevm msg) := by
  cases isCreate <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


/-! Today's Amsterdam top level, restated over the public API (`Legacy.runPreparedTopFrame` and
`Legacy.msgCallOutputAmsterdam` are private); each restatement is today's by `rfl`. -/

def preparedFrame (frame : Legacy.Frame) (prepared : Devm) :
    Except (EvmError × State × AdrSet × TransientStorage) Devm :=
  match frame.inner.benvAfterTransfer with
  | .error e => frame.settleMsg (.error e)
  | .ok benv =>
    let inner := frame.inner.withBenv benv
    let dyna :=
      ((prepared.withState benv.state).withStorageWrites benv.storageWrites).withCreatedAccounts
        benv.createdAccounts
    let evm : Evm := {pc := 0, sta := initSevm inner, dyna := dyna}
    let raw :=
      match inner.codeAddress with
      | none => Legacy.exec evm
      | some adr =>
        if !inner.disablePrecompiles && inner.benv.stat.rules.isPrecompile adr then
          executePrecompile evm adr
        else Legacy.exec evm
    frame.settle raw

theorem preparedFrame_eq (frame : Legacy.Frame) (prepared : Devm) :
    preparedFrame frame prepared =
      match preparedEntry frame prepared with
      | .done result => result
      | .run evm => frame.settle (Legacy.exec evm) := by
  cases hb : frame.inner.benvAfterTransfer with
  | error error => simp only [preparedFrame, preparedEntry, hb]
  | ok benv =>
    simp only [preparedFrame, preparedEntry, hb]
    cases hc : (frame.inner.withBenv benv).codeAddress with
    | none => rfl
    | some adr =>
      simp only
      split <;> rfl

/-- Today's rendering of a settled top-level result. -/
def topLevelOutput (authorizationRefund : Nat)
    (result : Except (EvmError × State × AdrSet × TransientStorage) Devm) :
    Except EvmError (State × MsgCallOutput) := do
  let evm ← Except.bimap Prod.fst id result
  let refund ←
    if evm.error.isNone then
      (Int.toNat? evm.refundCounter).toExcept
        (EvmError.internal (.invariant (.text "refund counter is negative")))
    else .ok 0
  let logs := if evm.error.isNone then evm.logs else []
  let accountsToDelete :=
    if evm.error.isNone then evm.accountsToDelete else .emptyWithCapacity
  let touchedAccounts :=
    if evm.error.isNone then evm.meta.touchedAccounts else .emptyWithCapacity
  pure ⟨evm.state, {
    gasLeft := evm.gasLeft, refundCounter := authorizationRefund + refund,
    logs := logs, accountsToDelete := accountsToDelete,
    error := evm.error, returnData := evm.output,
    touchedAccounts := touchedAccounts }⟩

/-- Today's Amsterdam rendering (`msgCallOutputAmsterdam`). -/
def topLevelOutputAmsterdam (msg : Msg) (evm : Devm) :
    Except EvmError (State × MsgCallOutput) := do
  let refundCounter ←
    if evm.error.isNone then
      (Int.toNat? evm.refundCounter).toExcept
        (EvmError.internal (.invariant (.text "refund counter is negative")))
    else .ok 0
  let logs := if evm.error.isNone then evm.logs else []
  let accountsToDelete :=
    if evm.error.isNone then evm.accountsToDelete else .emptyWithCapacity
  let stateGasUsed :=
    Int.ofNat msg.stateGasGrant - Int.ofNat evm.stateGasLeft +
      Int.ofNat evm.mach.stateGas.spilled +
      Int.ofNat evm.mach.stateGas.committedSpill
  .ok ⟨evm.state, {
    accountReads := evm.meta.accountReads
    storageReads := evm.meta.storageReads
    storageWrites := evm.world.storageWrites
    gasLeft := evm.gasLeft
    refundCounter := refundCounter
    logs := logs
    accountsToDelete := accountsToDelete
    error := evm.error
    returnData := evm.output
    stateGasLeft := evm.stateGasLeft
    stateGasUsed := stateGasUsed
  }⟩

def topLevelAmsterdam (state : StateGasRules) (msg : Msg)
    (frameOf : Msg → Legacy.Frame) : Except EvmError (State × MsgCallOutput) :=
  match prepareTopLevelAmsterdam state msg with
  | .error ⟨error, devm⟩ => settleTopLevelPreparationFailure msg error devm
  | .ok ⟨msg, devm⟩ => do
    let evm ← Except.bimap Prod.fst id (preparedFrame (frameOf msg) devm)
    topLevelOutputAmsterdam msg evm

theorem topLevelAmsterdam_eq (state : StateGasRules) (msg : Msg) (frameOf : Msg → Legacy.Frame) :
    topLevelAmsterdam state msg frameOf = processTopLevelAmsterdam state msg frameOf := rfl

theorem processMessageCall.call_eq (msg : Msg) (hfork : msg.benv.stat.rules.stateGas = none) :
    processMessageCall.call msg =
      (processMessageCall.legacyAuthorization msg >>= fun pair =>
        topLevelOutput pair.2 (Jaune.processMessage pair.1.resolveCodeDelegation)) := by
  simp only [processMessageCall.call, hfork, topLevelOutput]
  cases processMessageCall.legacyAuthorization msg <;> rfl

end Legacy

open Legacy

/-- A top-level frame's checkpoint, as a start state, is its message's `initDevm`. -/
theorem Frame.ofTop_start (msg : Msg) (isCreate : Bool) :
    (Frame.ofTop msg isCreate).checkpoint.toDevm = initDevm msg :=
  Frame.State.toDevm_ofDevm _ rfl rfl

/-- A clean start: the raw result of a frame entered with no stored error is clean. -/
theorem exec_clean_of_run {F : Legacy.Frame} {child : Evm} (he : F.enter = .run child) :
    Execution.Clean (Legacy.exec child) := by
  cases hx : Legacy.exec child with
  | error _ => trivial
  | ok d =>
    exact (execFueled_ok_error _ child
      ((Legacy.execFueled_run_sufficientFuel child).trans (congrArg some hx))).trans
      (Legacy.Frame.enter_run_error he)

/-- **The top frame.** Today's top-level frame run, read as a frame result, is the staged one. -/
theorem runTop_ofTop (msg : Msg) (isCreate : Bool) :
    Frame.runTop (Frame.ofTop msg isCreate)
      = Frame.Result.ofSettled
          (Jaune.runFrame (if isCreate then Legacy.Frame.ofCreate msg else Legacy.Frame.ofCall msg)) := by
  have htop := Legacy.Frame.top_topCoherent msg isCreate
  have hmsg : (Frame.ofTop msg isCreate).message
      = Message.ofLegacy
          (if isCreate then Legacy.Frame.ofCreate msg else Legacy.Frame.ofCall msg).outer
          (if isCreate then Legacy.Frame.ofCreate msg else Legacy.Frame.ofCall msg).isCreate := by
    cases isCreate <;> rfl
  have hE := enterWith_top msg isCreate
  rw [← Frame.ofTop_start msg isCreate] at hE
  generalize (if isCreate then Legacy.Frame.ofCreate msg else Legacy.Frame.ofCall msg) = F
    at htop hmsg hE ⊢
  unfold Frame.runTop Jaune.runFrame
  rcases he : F.enter with r | child <;> rw [he] at hE <;>
    simp only [Frame.Entry.ofLegacy] at hE <;> rw [← hE]
  · dsimp only
    have hf : Frame.ofTop msg isCreate
        = ⟨Message.ofLegacy F.outer F.isCreate, Frame.State.ofDevm (initDevm msg)⟩ := by
      rw [← hmsg]; rfl
    rw [settle_observe (exec_legacy child).symm, hf,
      settle_legacy F (initDevm msg) htop _ (exec_clean_of_run he)]

theorem preparedEntry_run_error {F : Legacy.Frame} {prepared : Devm} {evm : Evm}
    (he : Legacy.preparedEntry F prepared = .run evm) : evm.dyna.error = prepared.error := by
  unfold Legacy.preparedEntry at he
  split at he
  · cases he
  · dsimp only at he
    split at he
    · cases he; rfl
    · split at he
      · cases he
      · cases he; rfl

/-- **The prepared top frame.** Today's prepared-frame run, read as a frame result, is the staged
top frame over the prepared state, given that the state stores no output and no error. -/
theorem runTop_prepared (F : Legacy.Frame) (prepared : Devm) (h : Legacy.Frame.TopCoherent F prepared)
    (hout : prepared.output = []) (herr : prepared.error = none) :
    Frame.runTop ⟨Message.ofLegacy F.outer F.isCreate, Frame.State.ofDevm prepared⟩
      = Frame.Result.ofSettled
          (match Legacy.preparedEntry F prepared with
           | .done r => r
           | .run evm => F.settle (Legacy.exec evm)) := by
  have hE := enterWith_prepared F prepared h herr
  unfold Frame.runTop
  dsimp only
  rw [Frame.State.toDevm_ofDevm prepared hout herr]
  rcases he : Legacy.preparedEntry F prepared with r | child <;> rw [he] at hE <;>
    simp only [Frame.Entry.ofLegacy] at hE <;> rw [← hE]
  dsimp only
  have hclean : Execution.Clean (Legacy.exec child) := by
    cases hx : Legacy.exec child with
    | error _ => trivial
    | ok d =>
      exact (execFueled_ok_error _ child
        ((Legacy.execFueled_run_sufficientFuel child).trans (congrArg some hx))).trans
        ((preparedEntry_run_error he).trans herr)
  rw [settle_observe (exec_legacy child).symm, settle_legacy F prepared h _ hclean]

/-! ### The top level's output -/

theorem output_legacy (f : Frame) {rules : ForkRules}
    (a : Nat) {x : Except (EvmError × State × AdrSet × TransientStorage) Devm}
    (hx : SettledFacts f.checkpoint.toDevm rules x) :
    topLevelOutput a x = ((Frame.Result.ofSettled x).mapError Fault.toEvmError >>= f.output a) := by
  rcases x with ⟨e, st, c, t⟩ | d
  · rcases hx.fault rfl with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> rfl
  · have base : Except.bimap Prod.fst id (Except.ok d :
        Except (EvmError × State × AdrSet × TransientStorage) Devm) = .ok d := rfl
    rcases herr : d.error with _ | (reason | _)
    · simp only [topLevelOutput, Frame.Result.ofSettled, herr, base, bind, Except.bind,
        Option.isNone_none, ite_true, Except.mapError, Frame.Result.ofSuccess, Frame.output,
        Frame.Result.refundCounter, Frame.worldAfter, pure, Except.pure]
      rfl
    · have hw := hx.world rfl (by simp [herr])
      obtain ⟨hg, ho⟩ := hx.halted rfl herr
      simp only [topLevelOutput, Frame.Result.ofSettled, herr, base, bind, Except.bind,
        Option.isNone_some, Except.mapError, Frame.output, Frame.Result.refundCounter,
        Frame.worldAfter, pure, Except.pure, Bool.false_eq_true, ite_false, Devm.state, hw, hg, ho]
      rfl
    · have hw := hx.world rfl (by simp [herr])
      simp only [topLevelOutput, Frame.Result.ofSettled, herr, base, bind, Except.bind,
        Option.isNone_some, Except.mapError, Frame.output, Frame.Result.refundCounter,
        Frame.worldAfter, pure, Except.pure, Bool.false_eq_true, ite_false, Devm.state, hw]
      rfl

theorem outputAmsterdam_legacy (f : Frame) (msg : Msg) {rules : ForkRules}
    (hgrant : f.message.stateGasGrant = msg.stateGasGrant)
    {x : Except (EvmError × State × AdrSet × TransientStorage) Devm}
    (hx : SettledFacts f.checkpoint.toDevm rules x) :
    (Except.bimap Prod.fst id x >>= topLevelOutputAmsterdam msg)
      = ((Frame.Result.ofSettled x).mapError Fault.toEvmError >>= f.outputAmsterdam) := by
  rcases x with ⟨e, st, c, t⟩ | d
  · rcases hx.fault rfl with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> rfl
  · have base : Except.bimap Prod.fst id (Except.ok d :
        Except (EvmError × State × AdrSet × TransientStorage) Devm) = .ok d := rfl
    rcases herr : d.error with _ | (reason | _)
    · simp only [topLevelOutputAmsterdam, Frame.Result.ofSettled, herr, base, bind, Except.bind,
        Option.isNone_none, ite_true, Except.mapError, Frame.Result.ofSuccess,
        Frame.outputAmsterdam, Frame.Result.refundCounter, Frame.worldAfter, pure, Except.pure,
        hgrant]
      rfl
    · have hw := hx.world rfl (by simp [herr])
      obtain ⟨hg, ho⟩ := hx.halted rfl herr
      simp only [topLevelOutputAmsterdam, Frame.Result.ofSettled, herr, base, bind, Except.bind,
        Option.isNone_some, Except.mapError, Frame.outputAmsterdam, Frame.Result.refundCounter,
        Frame.worldAfter, pure, Except.pure, Bool.false_eq_true, ite_false, Devm.state, hw, hg,
        ho, hgrant]
      rfl
    · have hw := hx.world rfl (by simp [herr])
      simp only [topLevelOutputAmsterdam, Frame.Result.ofSettled, herr, base, bind, Except.bind,
        Option.isNone_some, Except.mapError, Frame.outputAmsterdam, Frame.Result.refundCounter,
        Frame.worldAfter, pure, Except.pure, Bool.false_eq_true, ite_false, Devm.state, hw,
        hgrant]
      rfl

/-! ### Facts about today's top-level runs -/

theorem runFrame_facts_top (msg : Msg) (isCreate : Bool) :
    SettledFacts (initDevm msg) msg.benv.stat.rules
      (Jaune.runFrame (if isCreate then Legacy.Frame.ofCreate msg else Legacy.Frame.ofCall msg)) := by
  have htop := Legacy.Frame.top_topCoherent msg isCreate
  have hr : (if isCreate then Legacy.Frame.ofCreate msg else Legacy.Frame.ofCall msg).outer.benv.stat.rules
      = msg.benv.stat.rules := by cases isCreate <;> rfl
  generalize (if isCreate then Legacy.Frame.ofCreate msg else Legacy.Frame.ofCall msg) = F at htop hr ⊢
  unfold Jaune.runFrame
  rcases he : F.enter with r | child
  · exact Legacy.Frame.enter_done_facts_top htop hr he
  · exact Legacy.settledFacts_top htop hr (exec_clean_of_run he)

theorem preparedFrame_facts (F : Legacy.Frame) (prepared : Devm) (h : Legacy.Frame.TopCoherent F prepared)
    (herr : prepared.error = none) :
    SettledFacts prepared F.outer.benv.stat.rules
      (match Legacy.preparedEntry F prepared with
       | .done r => r
       | .run evm => F.settle (Legacy.exec evm)) := by
  rcases he : Legacy.preparedEntry F prepared with r | child
  · -- the entry settled at once: a failed transfer or a precompile
    unfold Legacy.preparedEntry at he
    split at he
    · rename_i e hb
      cases he
      have hfault := Legacy.Msg.benvAfterTransfer_error hb
      have hs : F.settleMsg (.error e) = .error e := by
        unfold Legacy.Frame.settleMsg processMessage.settle processCreateMessage.settle
        split <;> rfl
      dsimp only
      rw [hs]
      refine ⟨?_, fun hs _ => (nomatch hs), fun hs _ _ => (nomatch hs), fun hs _ => (nomatch hs)⟩
      intro e' st c t he'
      cases he'
      exact .inr ⟨_, hfault⟩
    · dsimp only at he
      split at he
      · cases he
      · split at he
        · cases he
          apply Legacy.settledFacts_top h rfl
          show Execution.Clean _
          cases hp : executePrecompile _ _ with
          | error _ => trivial
          | ok d => exact (executePrecompile_ok_error hp).trans herr
        · cases he
  · dsimp only
    exact Legacy.settledFacts_top h rfl
      (by
        cases hx : Legacy.exec child with
        | error _ => trivial
        | ok d =>
          exact (execFueled_ok_error _ child
            ((Legacy.execFueled_run_sufficientFuel child).trans (congrArg some hx))).trans
            ((preparedEntry_run_error he).trans herr))

/-! ### Bridges -/

theorem settleTopLevelPreparationFailure_legacy (msg : Msg) (error : EvmError) (devm : Devm) :
    settleTopLevelPreparationFailure msg error devm
      = Legacy.settleTopLevelPreparationFailure msg error devm := by
  cases error <;> rfl

/-- What the Amsterdam preparation guarantees of its prepared state (proved in `Transaction`). -/
def PreparedFacts (p : Msg × Devm) : Prop :=
  p.2.output = [] ∧ p.2.error = none ∧ p.1.benv.state = p.2.state ∧
    p.1.benv.storageWrites = p.2.world.storageWrites ∧
    p.1.tenv.transientStorage = p.2.transientStorage ∧
    p.1.benv.createdAccounts = p.2.createdAccounts ∧
    p.1.accessedAddresses = p.2.accessedAddresses ∧
    p.1.accessedStorageKeys = p.2.accessedStorageKeys

theorem topCoherent_of_prepared {p : Msg × Devm} (h : PreparedFacts p) (isCreate : Bool) :
    Legacy.Frame.TopCoherent
      (if isCreate then Legacy.Frame.ofCreate p.1 else Legacy.Frame.ofCall p.1) p.2 := by
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6⟩ := h
  cases isCreate
  · exact ⟨rfl, h1, h2, h3, h4, h5, h6⟩
  · exact ⟨rfl, h1, h2, h3, h4, h5, h6⟩

theorem processTopLevelAmsterdam_legacy (state : StateGasRules) (msg : Msg) (isCreate : Bool) :
    processTopLevelAmsterdam state msg isCreate
      = Legacy.processTopLevelAmsterdam state msg
          (if isCreate then Legacy.Frame.ofCreate else Legacy.Frame.ofCall) := by
  rw [← Legacy.topLevelAmsterdam_eq]
  unfold processTopLevelAmsterdam Legacy.topLevelAmsterdam
  rcases hp : prepareTopLevelAmsterdam state msg with ⟨error, devm⟩ | ⟨msg', devm⟩
  · exact settleTopLevelPreparationFailure_legacy msg error devm
  · have facts : PreparedFacts _ := prepareTopLevelAmsterdam_prepared hp
    have hcoh := topCoherent_of_prepared facts isCreate
    have hF : (if isCreate then Legacy.Frame.ofCreate else Legacy.Frame.ofCall) msg'
        = (if isCreate then Legacy.Frame.ofCreate msg' else Legacy.Frame.ofCall msg') := by
      cases isCreate <;> rfl
    have hmsg : Message.ofLegacy msg' isCreate
        = Message.ofLegacy (if isCreate then Legacy.Frame.ofCreate msg' else Legacy.Frame.ofCall msg').outer
            (if isCreate then Legacy.Frame.ofCreate msg' else Legacy.Frame.ofCall msg').isCreate := by
      cases isCreate <;> rfl
    have hrules : (if isCreate then Legacy.Frame.ofCreate msg' else Legacy.Frame.ofCall msg').outer.benv.stat.rules
        = msg'.benv.stat.rules := by cases isCreate <;> rfl
    have hout : (if isCreate then Legacy.Frame.ofCreate msg' else Legacy.Frame.ofCall msg').outer
        = msg' := by cases isCreate <;> rfl
    dsimp only
    rw [hF, Legacy.preparedFrame_eq]
    generalize (if isCreate then Legacy.Frame.ofCreate msg' else Legacy.Frame.ofCall msg') = F
      at hcoh hmsg hrules hout ⊢
    rw [hmsg, runTop_prepared F devm hcoh facts.1 facts.2.1]
    have hx : SettledFacts (Frame.State.ofDevm devm).toDevm F.outer.benv.stat.rules
        (match Legacy.preparedEntry F devm with
         | .done r => r
         | .run evm => F.settle (Legacy.exec evm)) := by
      rw [Frame.State.toDevm_ofDevm devm facts.1 facts.2.1]
      exact preparedFrame_facts F devm hcoh facts.2.1
    exact (outputAmsterdam_legacy ⟨Message.ofLegacy F.outer F.isCreate, Frame.State.ofDevm devm⟩
      msg' (congrArg Msg.stateGasGrant hout) hx).symm

theorem topOutput_legacy (msg : Msg) (isCreate : Bool) (a : Nat) :
    ((Frame.runTop (Frame.ofTop msg isCreate)).mapError Fault.toEvmError >>=
        (Frame.ofTop msg isCreate).output a)
      = topLevelOutput a
          (Jaune.runFrame (if isCreate then Legacy.Frame.ofCreate msg else Legacy.Frame.ofCall msg)) := by
  have hx := runFrame_facts_top msg isCreate
  rw [← Frame.ofTop_start msg isCreate] at hx
  rw [runTop_ofTop, output_legacy _ a hx]

/-- The ordinary authorization is today's. -/
theorem legacyAuthorization_legacy (msg : Msg) :
    Legacy.processMessageCall.legacyAuthorization msg = processMessageCall.legacyAuthorization msg :=
  rfl

/-- **The gate's anchor.** The top-level message call on the four-part chain is today's, for every
message and every `Fork`, as plain equality of the whole result. -/
theorem processMessageCall_legacy (msg : Msg) :
    processMessageCall msg = Legacy.processMessageCall msg := by
  unfold processMessageCall Legacy.processMessageCall
  split
  · unfold processMessageCall.create Legacy.processMessageCall.create
    split
    · rename_i hfork
      simp only [hfork]
      split
      · rfl
      · have h := topOutput_legacy msg true 0
        simp only [ite_true] at h
        rw [h]
        simp only [topLevelOutput, Jaune.processCreateMessage, Nat.cast_zero, zero_add]
        rfl
    · rename_i state hfork
      try simp only [hfork]
      exact processTopLevelAmsterdam_legacy state msg true
  · unfold processMessageCall.call
    split
    · rename_i hfork
      rw [Legacy.processMessageCall.call_eq msg hfork, legacyAuthorization_legacy]
      cases processMessageCall.legacyAuthorization msg with
      | error e => rfl
      | ok pair =>
        obtain ⟨delegated, refund⟩ := pair
        have h := topOutput_legacy delegated.resolveCodeDelegation false refund
        simp only [Bool.false_eq_true, ite_false] at h
        exact h
    · rename_i state hfork
      unfold Legacy.processMessageCall.call
      simp only [hfork]
      exact processTopLevelAmsterdam_legacy state msg false


/-- The anchor as an equation of functions. Every definition that reaches the message call only
through `processMessageCall` -- the transaction, the system calls, the block body and the block
transition -- is therefore today's by congruence: nothing else in their closure moved at the
switch (N4 over both relocations). -/
theorem processMessageCall_eq_legacy : processMessageCall = Legacy.processMessageCall :=
  funext processMessageCall_legacy

end Jaune
