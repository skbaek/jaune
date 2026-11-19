import Jaune.Bridge.G2b.CheckedDriver
import Jaune.Bridge.G2b.CheckedIngress
import Jaune.Bridge.G2b.CheckedReached
import Jaune.Bridge.G2b.CheckedContext
import Jaune.Implementation.CheckedCachedDriver
import Jaune.Bridge.G2b.FinalDriver
import Jaune.MessageCall.SpawnFacts
import Jaune.Run.CheckedTransaction
import Jaune.Run.Message
import Jaune.Run.SystemCall

namespace Jaune.Checked

/-- A raw running machine can be grouped exactly when its backing memory lies within its logical size. -/
def Frame.Running.ofEvm (evm : Evm) (hw : evm.dyna.memory.Wf) : Frame.Running :=
  Frame.Running.ofLegacy (Jaune.Frame.Running.ofEvm evm) hw

theorem step_ofEvm (evm : Evm) (hw : evm.dyna.memory.Wf) (ho : evm.dyna.output = []) :
    (step (Frame.Running.ofEvm evm hw)).map Step.toLegacy = (Jaune.Evm.step evm).observe := by
  rw [← MemorySimulation.step]
  exact Staging.step_ofEvm evm ho

theorem execFueled_square (fuel : Nat) (evm : Evm) (hw : evm.dyna.memory.Wf) (ho : evm.dyna.output = []) :
    (execFueled (Frame.Running.ofEvm evm hw) fuel).run.map (Except.map Frame.Exit.toLegacy) =
      (Jaune.execFueled evm fuel).run.map Jaune.Frame.Exit.ofExecution := by
  rw [← execFueled_toLegacy]
  exact Jaune.execFueled_square fuel evm ho

theorem exec_square (evm : Evm) (hw : evm.dyna.memory.Wf) (ho : evm.dyna.output = []) :
    (exec (Frame.Running.ofEvm evm hw)).map Frame.Exit.toLegacy = Jaune.Frame.Exit.ofExecution (Jaune.exec evm) := by
  rw [← exec_toLegacy]
  exact Jaune.exec_square evm ho

theorem execFueledCached_square (fuel : Nat) (evm : Evm) (hw : evm.dyna.memory.Wf) (ho : evm.dyna.output = []) :
    (execFueledCached (Frame.Running.ofEvm evm hw) fuel).run.map (Except.map Frame.Exit.toLegacy) =
      (Jaune.execFueled evm fuel).run.map Jaune.Frame.Exit.ofExecution := by
  rw [← execFueled_eq_cached]
  exact execFueled_square fuel evm hw ho

/-- Full outward result, for every checked frame and every fork. -/
theorem Frame.runTop_square (f : Frame) : Frame.runTop f = Jaune.Frame.runTop f.toLegacy := by
  rw [← Jaune.Frame.runTop_square, ← Frame.runTop_toLegacy]

/-- A top-level preparation always supplies the evidence to convert its checkpoint exactly. -/
theorem Frame.runTop_prepared {msg : Msg} {f : Jaune.Frame} {refund : Nat}
    (hp : TopLevel.prepare msg = .ok (.frame f refund)) :
    Frame.runTop (Frame.ofLegacy f (Staging.TopLevel.prepare_frame_memory_wf hp)) = Jaune.Frame.runTop f := by
  rw [Frame.runTop_square, Frame.toLegacy_ofLegacy]

/-- The checked frame entered by transaction preparation names its kind and code address
coherently, including after authorization and delegation resolution. -/
theorem Frame.ofLegacy_prepared_kindCoherent {benv : Benv} {tenv : Tenv} {tx : Transaction}
    {msg : Msg} (hm : prepareMessage benv tenv tx = .ok msg) {f : Jaune.Frame} {refund : Nat}
    (hp : Jaune.TopLevel.prepare msg = .ok (.frame f refund)) :
    (Frame.ofLegacy f (Staging.TopLevel.prepare_frame_memory_wf hp)).message.KindCoherent :=
  Jaune.TopLevel.topFrame_kindCoherent hm (Jaune.TopLevel.prepare_topFrame hp)

/-- Raw execution from a prepared frame keeps every reached current machine well formed. -/
theorem prepared_reached_memory_wf {msg : Msg} {f : Jaune.Frame} {refund : Nat} {root evm : Evm}
    (hp : TopLevel.prepare msg = .ok (.frame f refund))
    (he : Jaune.enterWith f f.checkpoint.toDevm = .run root) (hr : root.Reaches evm) : evm.dyna.memory.Wf :=
  hr.memory_wf (MemoryReachability.enterWith_run (start := f.checkpoint.toDevm)
    (Staging.TopLevel.prepare_frame_memory_wf hp) he)

/-- Every caller checkpoint saved by that execution has well-formed memory. -/
theorem prepared_checkpoint_memory_wf {msg : Msg} {f : Jaune.Frame} {refund : Nat} {root evm : Evm}
    (hp : TopLevel.prepare msg = .ok (.frame f refund))
    (he : Jaune.enterWith f f.checkpoint.toDevm = .run root) (hr : root.Reaches evm)
    {child : Jaune.Frame} {p : Pending} {pc : Nat} (hs : evm.step = .spawn child p pc) :
    child.checkpoint.machine.memory.Wf :=
  hr.checkpoint_memory_wf (MemoryReachability.enterWith_run (start := f.checkpoint.toDevm)
    (Staging.TopLevel.prepare_frame_memory_wf hp) he) hs

theorem Frame.entry_static_error {f : Jaune.Frame} {start : Devm} {evm : Evm}
    (h : Jaune.enterWith f start = .run evm) :
    evm.sta = f.message.sevm ∧ evm.dyna.error = start.error := by
  unfold Jaune.enterWith at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h; exact ⟨rfl, rfl⟩
    · cases h; exact ⟨rfl, rfl⟩

/-- The legacy entry observes the same immediate settlement or entered frame. -/
theorem Frame.enterWith_square (f : Frame) :
    (Jaune.enterWith f.toLegacy f.toLegacy.checkpoint.toDevm).observe =
      (enterWith f f.checkpoint).toLegacy := by
  rw [Jaune.Frame.Entry.observe_enterWith _ rfl, Staging.enterWith_ofDevm_toDevm,
    show f.toLegacy.checkpoint = f.checkpoint.toLegacy from rfl, enterWith_toLegacy]

/-- Observe the entered machine and settled result without entering the frame a second time. -/
private theorem Frame.runTopWithRoot_observes (f : Frame) :
    f.runTopWithRoot.map (fun run => (run.root.map (fun r => r.toLegacy.toEvm f.message), run.result)) =
      match Jaune.enterWith f.toLegacy f.toLegacy.checkpoint.toDevm with
      | .done result => result.map (fun r => (none, r))
      | .run evm => (Jaune.settle f.toLegacy (Jaune.exec evm)).map (fun r => (some evm, r)) := by
  have entry := f.enterWith_square
  unfold Frame.runTopWithRoot
  cases hw : Jaune.enterWith f.toLegacy f.toLegacy.checkpoint.toDevm with
  | done settled =>
    cases hc : enterWith f f.checkpoint with
    | done checked =>
      rw [hw, hc] at entry
      cases entry
      cases settled <;> rfl
    | run r => rw [hw, hc] at entry; cases entry
  | run evm =>
    cases hc : enterWith f f.checkpoint with
    | done settled => rw [hw, hc] at entry; cases entry
    | run r =>
      rw [hw, hc] at entry
      have hr : r.toLegacy = Jaune.Frame.Running.ofEvm evm := by
        simpa only [Jaune.Frame.Entry.observe, Frame.Entry.toLegacy, Staging.Frame.Entry.run.injEq]
          using entry.symm
      have ho := Jaune.enterWith_run_output rfl hw
      obtain ⟨hs, he⟩ := Frame.entry_static_error hw
      have hroot : r.toLegacy.toEvm f.message = evm := by
        have hm : Jaune.Message.ofSevm evm.sta f.message.kind f.message.stateGasGrant = f.message := by
          rw [hs]
          exact Jaune.Message.ofSevm_sevm f.message
        rw [hr, ← hm]
        exact Jaune.Frame.Running.toEvm_ofEvm _ _ ho he
      have hx : (exec r).map Frame.Exit.toLegacy = Jaune.Frame.Exit.ofExecution (Jaune.exec evm) := by
        rw [← exec_toLegacy, hr]
        exact Jaune.exec_square evm ho
      have hsettle : Jaune.settle f.toLegacy (Jaune.exec evm) = exec r >>= settle f := by
        rw [Jaune.settle_eq, ← hx]
        cases exec r with
        | error fault => rfl
        | ok exit => exact settle_toLegacy f exit
      dsimp only
      rw [hsettle]
      cases (exec r >>= settle f) <;> simp only [Except.map, Option.map_some, hroot]

namespace TopLevel

/-- Project the current preparation to the Checked types using the checkpoint's memory bound. -/
def ofPreparation (msg : Msg) (prepared : Jaune.TopLevel.Preparation)
    (hp : Jaune.TopLevel.prepare msg = .ok prepared) : Preparation :=
  match prepared with
  | .refused reason halted =>
    .refused (match msg.benv.stat.rules.stateGas with
      | none => .collision reason
      | some _ => .stateGas reason msg.stateGasGrant halted.meta.accountReads halted.meta.storageReads)
  | .frame f refund => .frame (Frame.ofLegacy f (Staging.TopLevel.prepare_frame_memory_wf hp)) refund

def prepare (msg : Msg) : Except Fault Preparation :=
  match hp : Jaune.TopLevel.prepare msg with
  | .error fault => .error fault
  | .ok prepared => .ok (ofPreparation msg prepared hp)

def run (msg : Msg) : Except Fault Run := prepare msg >>= Preparation.run

/-- The current settlement consumes the original preparation and the checked
frame's exact entry and result. The original halted machine is available only
through preparation. -/
def observe (msg : Msg) (prepared : Jaune.TopLevel.Preparation) : Run → TopLevelRun
  | .refused _ => ⟨msg, prepared, none, none⟩
  | .frame f _ run =>
    ⟨msg, prepared, run.root.map (fun r => r.toLegacy.toEvm f.message), some run.result⟩

theorem run_observe (msg : Msg) (prepared : Jaune.TopLevel.Preparation)
    (hp : Jaune.TopLevel.prepare msg = .ok prepared) :
    (ofPreparation msg prepared hp).run.map (observe msg prepared) = Jaune.TopLevel.run msg := by
  rw [Jaune.TopLevel.run, hp]
  simp only [bind, Except.bind]
  cases prepared with
  | refused reason halted => rfl
  | frame f refund =>
    let checked := Frame.ofLegacy f (Staging.TopLevel.prepare_frame_memory_wf hp)
    have h := congrArg (Except.map fun (root, result) =>
        (⟨msg, .frame f refund, root, some result⟩ : TopLevelRun)) (checked.runTopWithRoot_observes)
    rw [show checked.toLegacy = f from Frame.toLegacy_ofLegacy ..] at h
    change (checked.runTopWithRoot.map (.frame checked refund)).map (observe msg (.frame f refund)) = _
    cases hs : checked.runTopWithRoot <;> rw [hs] at h
    all_goals
      cases he : Jaune.enterWith f f.checkpoint.toDevm
      · rename_i evm
        cases hr : Jaune.settle f (Jaune.exec evm) <;>
          simpa only [he, hr, Except.map, observe, Except.bind, pure, Except.pure] using h
      · rename_i result
        cases result <;> simpa only [he, Except.map, observe, Except.bind, pure, Except.pure] using h

private theorem setDelegationLoop_preserves_block {auths : List Authorization} {msg : Msg}
    {refund : U256} {out : Msg × U256} (h : setDelegationLoop auths msg refund = .ok out) :
    out.1.benv.stat = msg.benv.stat := by
  induction auths generalizing msg refund with
  | nil => cases h; rfl
  | cons auth auths ih =>
    rw [setDelegationLoop] at h
    obtain ⟨⟨next, refund'⟩, hstep, hrest⟩ := Except.bind_eq_ok h
    have hblock : next.benv.stat = msg.benv.stat := by
      unfold setDelegationStep at hstep
      split at hstep
      · cases hstep; rfl
      split at hstep
      · cases hstep; rfl
      split at hstep
      · cases hstep; rfl
      · cases hstep
      · dsimp only at hstep
        split at hstep
        · cases hstep; rfl
        · split at hstep <;> cases hstep <;> rfl
    exact (ih hrest).trans hblock

private theorem authorize_preserves_block {msg : Msg} {out : Msg × Nat}
    (h : Jaune.TopLevel.applyAuthorizations msg = .ok out) : out.1.benv.stat = msg.benv.stat := by
  unfold Jaune.TopLevel.applyAuthorizations at h
  split at h
  · cases h; rfl
  · obtain ⟨⟨delegated, refund⟩, hd, h⟩ := Except.bind_eq_ok h
    cases h
    unfold setDelegation at hd
    obtain ⟨⟨next, r⟩, hn, hd⟩ := Except.bind_eq_ok hd
    dsimp only at hd
    split at hd <;> cases hd
    exact setDelegationLoop_preserves_block hn

private theorem amsterdam_preserves_block {msg : Msg} {rules : StateGasRules} {out : Msg × Devm}
    (h : prepareTopLevelAmsterdam rules msg = .ok out) : out.1.benv.stat = msg.benv.stat := by
  suffices ∀ start, Jaune.finishTopLevelAmsterdam rules msg start = .ok out →
      out.1.benv.stat = msg.benv.stat by
    unfold Jaune.prepareTopLevelAmsterdam at h
    dsimp only at h
    split at h <;> obtain ⟨start, _, h⟩ := Except.bind_eq_ok h <;> exact this start h
  intro start h
  unfold Jaune.finishTopLevelAmsterdam at h
  dsimp only at h
  generalize (if msg.tenv.stat.auths.isEmpty then start else start.commitStateGas) = committed at h
  unfold Jaune.dispatchTopLevelAmsterdam at h
  dsimp only at h
  split at h
  · split at h
    · cases h
    · split at h <;> obtain ⟨charged, _, h⟩ := Except.bind_eq_ok h <;> cases h <;> rfl
  · split at h <;> obtain ⟨charged, _, h⟩ := Except.bind_eq_ok h
    all_goals
      unfold Jaune.resolveTopLevelCallAmsterdam at h
      obtain ⟨charged', _, h⟩ := Except.bind_eq_ok h
      cases h
      rfl

private theorem prepare_frame_block {msg : Msg} {f : Jaune.Frame} {refund : Nat}
    (hp : Jaune.TopLevel.prepare msg = .ok (.frame f refund)) :
    f.message.context.block = msg.benv.stat := by
  have hframe := Jaune.TopLevel.prepare_topFrame hp
  cases hframe with
  | create => rfl
  | call _ _ ha =>
    change (Jaune.TopLevel.resolveCodeDelegation _).benv.stat = _
    unfold Jaune.TopLevel.resolveCodeDelegation
    split <;> exact authorize_preserves_block ha
  | amsterdam _ ha => exact amsterdam_preserves_block ha

/-- The frame sees the transaction's original state after all top-level preparation,
including authorization writes and delegation resolution. -/
theorem run_frame_originalState {msg : Msg} {f : Frame} {refund : Nat} {result : Frame.TopRun}
    (h : run msg = .ok (.frame f refund result)) :
    f.message.context.toChecked.tx.originalState = msg.benv.stat.origState := by
  obtain ⟨prep, hp, hr⟩ := Except.bind_eq_ok h
  unfold prepare at hp
  split at hp
  · cases hp
  · rename_i prepared hp'
    cases hp
    cases prepared with
    | refused reason halted =>
      simp only [ofPreparation, Preparation.run] at hr
      cases hr
    | frame legacy authorized =>
      simp only [ofPreparation, Preparation.run] at hr
      cases fRun : (Frame.ofLegacy legacy (Staging.TopLevel.prepare_frame_memory_wf hp')).runTopWithRoot
      all_goals rw [fRun] at hr
      · cases hr
      · cases hr
        change legacy.message.context.block.origState = msg.benv.stat.origState
        exact congrArg BenvStat.origState (prepare_frame_block hp')

/-- The typed refund is the legacy settlement input on every successful Checked run. -/
theorem refundCounter_observe {msg : Msg} {prepared : Jaune.TopLevel.Preparation} {checked : Run}
    (hp : Jaune.TopLevel.prepare msg = .ok prepared) (hr : (ofPreparation msg prepared hp).run = .ok checked) :
    checked.refundCounter = (observe msg prepared checked).refundCounter := by
  cases prepared with
  | refused reason halted =>
    simp only [ofPreparation, Preparation.run] at hr
    cases hr
    rfl
  | frame f refund =>
    simp only [ofPreparation, Preparation.run] at hr
    cases he : (Frame.ofLegacy f (Staging.TopLevel.prepare_frame_memory_wf hp)).runTopWithRoot with
    | error => rw [he] at hr; cases hr
    | ok result =>
      rw [he] at hr
      cases hr
      have block : (Frame.ofLegacy f (Staging.TopLevel.prepare_frame_memory_wf hp)).message.context.block =
          msg.benv.stat := prepare_frame_block hp
      simp only [Run.refundCounter, observe, TopLevelRun.refundCounter, TopLevelRun.stateGasRules, block]
      cases result.result <;> rfl

private def systemCallMessage (benv : Benv) (target : Address) (code : ByteArray) (data : Bytes) : Msg :=
  let started := benv.beginTransaction
  systemTransactionMessage started (systemTransactionEnvironment started) target data code

/-- Run the shared system message once and retain the Checked result and its current observation.
The refund counter can fault even though a system caller discards its value. -/
def runSystemCall (benv : Benv) (target : Address) (code : ByteArray) (data : Bytes) :
    Except Fault (Run × TopLevelRun) := do
  let msg := systemCallMessage benv target code data
  match hp : Jaune.TopLevel.prepare msg with
  | .error fault => .error fault
  | .ok prepared =>
    let checked ← (ofPreparation msg prepared hp).run
    let _ ← checked.refundCounter
    pure (checked, observe msg prepared checked)

/-- The whole observed system run, including faults and the refund check, agrees with the current run. -/
theorem runSystemCall_observe (benv : Benv) (target : Address) (code : ByteArray) (data : Bytes) :
    (runSystemCall benv target code data).map Prod.snd = processSystemTransaction benv target code data := by
  unfold runSystemCall
  dsimp only
  change _ = (do
    let observed ← Jaune.TopLevel.run (systemCallMessage benv target code data)
    let _ ← observed.refundCounter
    pure observed)
  split
  · rename_i fault hp
    rw [Jaune.TopLevel.run, hp]
    rfl
  · rename_i prepared hp
    rw [← run_observe _ _ hp]
    cases hr : (ofPreparation _ prepared hp).run with
    | error => rfl
    | ok checked =>
      simp only [bind, Except.bind, Except.map, pure, Except.pure]
      rw [refundCounter_observe hp hr]
      cases (observe _ prepared checked).refundCounter <;> rfl

/-- Every prepared system frame sees the world at the start of that system call. -/
theorem runSystemCall_frame_originalState {benv : Benv} {target : Address} {code : ByteArray}
    {data : Bytes} {f : Frame} {refund : Nat} {result : Frame.TopRun} {observed : TopLevelRun}
    (h : runSystemCall benv target code data = .ok (.frame f refund result, observed)) :
    f.message.context.toChecked.tx.originalState = benv.state := by
  unfold runSystemCall at h
  dsimp only at h
  split at h
  · cases h
  · rename_i prepared hp
    obtain ⟨checked, hrun, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    cases h
    have checkedRun : run (systemCallMessage benv target code data) = .ok (.frame f refund result) := by
      unfold run prepare
      split <;> rename_i h <;> rw [hp] at h <;> cases h
      exact hrun
    exact run_frame_originalState checkedRun

end TopLevel

/-- Map the waiting immutable message onto the Checked context supplied to the frame. -/
def Message.ofLegacy (message : Jaune.Message) : Message :=
  ⟨message.context.toChecked, message.kind, message.codeAddress, message.gas, message.stateGasGrant,
    message.transfersValue, message.disablePrecompiles⟩

private theorem initialCheckpoint_observe (msg : Msg) :
    (Message.ofLegacy (Jaune.Message.ofTop msg msg.target.isNone)).initialCheckpoint
      ⟨msg.benv.state, msg.tenv.transientStorage, msg.benv.storageWrites⟩
      msg.accessedAddresses msg.accessedStorageKeys msg.benv.createdAccounts msg.inheritedDeletions =
    Frame.State.ofLegacy (Jaune.Frame.State.ofDevm (initDevm msg)) Mem.wf_empty := by
  have rules : msg.benv.stat.toBlockContext.rules = msg.benv.stat.rules := rfl
  cases hgas : msg.benv.stat.rules.stateGas
  · simp only [Message.initialCheckpoint, Message.ofLegacy, Jaune.Message.ofTop, initDevm,
      Jaune.CallContext.toChecked, rules, hgas]
    rfl
  · simp only [Message.initialCheckpoint, Message.ofLegacy, Jaune.Message.ofTop, initDevm,
      Jaune.CallContext.toChecked, rules, hgas]
    by_cases htransfer : msg.shouldTransferValue = true
    · by_cases hlog : msg.caller = msg.currentTarget ∨ msg.value = 0 <;>
        simp only [htransfer, Devm.emitTransferLog, hlog, ↓reduceIte] <;> rfl
    · simp only [htransfer]
      rfl

/-- The full observation of a waiting top-level preparation input. -/
def TopLevel.Input.ofLegacy (msg : Msg) : TopLevel.Input :=
  ⟨Message.ofLegacy (Jaune.Message.ofTop msg msg.target.isNone),
    Frame.State.ofLegacy (Jaune.Frame.State.ofDevm (initDevm msg)) Mem.wf_empty, msg.tenv.stat.auths⟩

/-- Project the current prepared transaction onto the Checked settlement inputs. -/
def Transaction.Prepared.ofLegacy (prepared : Jaune.Transaction.Prepared) : Transaction.Prepared :=
  ⟨prepared.bout, prepared.sender, prepared.effectiveGasPrice, prepared.txBlobGasUsed,
    prepared.calldataFloorGasCost, .ofLegacy prepared.msg⟩

/-- On the admitted block and transaction snapshot, native preparation produces the full
Checked input observed from the waiting preparation, including fee failures. -/
theorem Transaction.prepare_observe (admitted : Jaune.Transaction.Admitted) (tx : Jaune.Transaction)
    (index : Nat) :
    prepare admitted.benv.stat.toBlockContext admitted.benv.stat.origState admitted tx =
      (Jaune.Transaction.prepare admitted tx index).map Prepared.ofLegacy := by
  unfold prepare Jaune.Transaction.prepare
  simp only [BenvStat.toBlockContext, BlockContext.rules, BenvStat.rules]
  let fee := if tx.isEip4844 then
    calculateDataFee (Fork.ruleSet admitted.benv.stat.fork).blob admitted.benv.stat.excessBlobGas tx else 0
  let charged := (admitted.benv.state.incrNonce admitted.sender).subBal admitted.sender
    (Jaune.Nat.toU256 (tx.gasLimit * admitted.effectiveGasPrice + fee))
  change (Jaune.Option.toExcept _ charged >>= _) =
    (Jaune.Option.toExcept _ charged >>= _).map Prepared.ofLegacy
  cases charged with
  | none => rfl
  | some state =>
    simp only [Jaune.Option.toExcept, bind, Except.bind]
    unfold prepareMessage
    cases tx.type.to? <;>
      simp only [Option.isNone, ↓reduceIte, pure, Except.pure, Except.map,
        Prepared.ofLegacy, TopLevel.Input.ofLegacy] <;>
      rw [← initialCheckpoint_observe] <;> rfl

theorem _root_.Jaune.Transaction.admit_originalState {benv : Benv} {bout : BlockOutput}
    {tx : Jaune.Transaction} {index : Nat} {admitted : Jaune.Transaction.Admitted}
    (h : Jaune.Transaction.admit benv bout tx index = .ok admitted) :
    admitted.benv.stat.origState = benv.state := by
  unfold Jaune.Transaction.admit at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨_, _⟩, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨_, _, _, _⟩, _, h⟩ := Except.bind_eq_ok h
  cases h
  rfl

/-- At the signed transaction boundary, the native message retains the world at admission. -/
theorem Transaction.prepare_originalState {benv : Benv} {bout : BlockOutput} {tx : Jaune.Transaction}
    {index : Nat} {admitted : Jaune.Transaction.Admitted} {prepared : Transaction.Prepared}
    (ha : Jaune.Transaction.admit benv bout tx index = .ok admitted)
    (hp : prepare admitted.benv.stat.toBlockContext admitted.benv.stat.origState admitted tx = .ok prepared) :
    prepared.input.message.context.tx.originalState = benv.state := by
  unfold prepare at hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases target : tx.type.to? <;> simp only [target, pure, Except.pure] at hp <;> cases hp <;>
    exact Jaune.Transaction.admit_originalState ha

end Jaune.Checked
