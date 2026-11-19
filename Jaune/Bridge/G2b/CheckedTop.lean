import Jaune.Bridge.G2b.CheckedDriver
import Jaune.Bridge.G2b.CheckedIngress
import Jaune.Bridge.G2b.CheckedReached
import Jaune.Bridge.G2b.CheckedContext
import Jaune.Implementation.CheckedCachedDriver
import Jaune.Bridge.G2b.FinalDriver
import Jaune.MessageCall.SpawnFacts
import Jaune.MessageCall.CheckedSpawnFacts
import Jaune.Run.CheckedMessage
import Jaune.Run.CheckedTransaction
import Jaune.Run.Message
import Jaune.Run.SystemCall

namespace Jaune.Checked

/-- A raw running machine can be grouped exactly when its backing memory lies within its logical size. -/
def Frame.Running.ofEvm (evm : Evm) (hw : evm.dyna.memory.Wf) : Frame.Running :=
  Frame.Running.ofLegacy (Jaune.Frame.Running.ofEvm evm) hw

private theorem Frame.Running.ofEvm_toLegacy (evm : Evm) (hw : evm.dyna.memory.Wf) :
    @Frame.Running.toLegacy (Frame.Running.ofEvm evm hw) ⟨evm.sta.tenvStat⟩ =
      Jaune.Frame.Running.ofEvm evm :=
  Frame.Running.toLegacy_ofLegacy _ _

theorem step_ofEvm (evm : Evm) (hw : evm.dyna.memory.Wf) (ho : evm.dyna.output = []) :
    letI : LegacyTransaction := ⟨evm.sta.tenvStat⟩
    (step (Frame.Running.ofEvm evm hw)).map Step.toLegacy = (Jaune.Evm.step evm).observe := by
  letI : LegacyTransaction := ⟨evm.sta.tenvStat⟩
  change (step (Frame.Running.ofEvm evm hw)).map Step.toLegacy = _
  rw [← MemorySimulation.step, Frame.Running.ofEvm_toLegacy]
  exact Staging.step_ofEvm evm ho

theorem execFueled_square (fuel : Nat) (evm : Evm) (hw : evm.dyna.memory.Wf) (ho : evm.dyna.output = []) :
    (execFueled (Frame.Running.ofEvm evm hw) fuel).run.map (Except.map Frame.Exit.toLegacy) =
      (Jaune.execFueled evm fuel).run.map Jaune.Frame.Exit.ofExecution := by
  letI : LegacyTransaction := ⟨evm.sta.tenvStat⟩
  rw [← @execFueled_toLegacy ‹LegacyTransaction›, Frame.Running.ofEvm_toLegacy]
  exact Jaune.execFueled_square fuel evm ho

theorem exec_square (evm : Evm) (hw : evm.dyna.memory.Wf) (ho : evm.dyna.output = []) :
    (exec (Frame.Running.ofEvm evm hw)).map Frame.Exit.toLegacy = Jaune.Frame.Exit.ofExecution (Jaune.exec evm) := by
  letI : LegacyTransaction := ⟨evm.sta.tenvStat⟩
  rw [← @exec_toLegacy ‹LegacyTransaction›, Frame.Running.ofEvm_toLegacy]
  exact Jaune.exec_square evm ho

theorem execFueledCached_square (fuel : Nat) (evm : Evm) (hw : evm.dyna.memory.Wf) (ho : evm.dyna.output = []) :
    (execFueledCached (Frame.Running.ofEvm evm hw) fuel).run.map (Except.map Frame.Exit.toLegacy) =
      (Jaune.execFueled evm fuel).run.map Jaune.Frame.Exit.ofExecution := by
  rw [← execFueled_eq_cached]
  exact execFueled_square fuel evm hw ho

/-- Full outward result, for every checked frame and every fork. -/
theorem Frame.runTop_square [LegacyTransaction] (f : Frame) : Frame.runTop f = Jaune.Frame.runTop f.toLegacy := by
  rw [← Jaune.Frame.runTop_square, ← Frame.runTop_toLegacy]

/-- A top-level preparation always supplies the evidence to convert its checkpoint exactly. -/
theorem Frame.runTop_prepared {msg : Msg} {f : Jaune.Frame} {refund : Nat}
    (hp : TopLevel.prepare msg = .ok (.frame f refund)) :
    Frame.runTop (Frame.ofLegacy f (Staging.TopLevel.prepare_frame_memory_wf hp)) = Jaune.Frame.runTop f := by
  letI : LegacyTransaction := ⟨f.message.context.tx⟩
  rw [@Frame.runTop_square ‹LegacyTransaction›, Frame.toLegacy_ofLegacy]

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
theorem Frame.enterWith_square [LegacyTransaction] (f : Frame) :
    (Jaune.enterWith f.toLegacy f.toLegacy.checkpoint.toDevm).observe =
      (enterWith f f.checkpoint).toLegacy := by
  rw [Jaune.Frame.Entry.observe_enterWith _ rfl, Staging.enterWith_ofDevm_toDevm,
    show f.toLegacy.checkpoint = f.checkpoint.toLegacy from rfl, enterWith_toLegacy]

/-- Observe the entered machine and settled result without entering the frame a second time. -/
private theorem Frame.runTopWithRoot_observes [LegacyTransaction] (f : Frame) :
    f.runTopWithRoot.map (fun run => (run.root.map (fun r => r.toLegacy.toEvm f.toLegacy.message), run.result)) =
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
      have hroot : r.toLegacy.toEvm f.toLegacy.message = evm := by
        have hm : Jaune.Message.ofSevm evm.sta f.message.kind f.message.stateGasGrant = f.toLegacy.message := by
          rw [hs]
          exact Jaune.Message.ofSevm_sevm f.toLegacy.message
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
    let waiting := match prepared with
      | .frame waiting _ => waiting.message
      | .refused .. => f.message.toLegacy msg.tenv.stat
    letI : LegacyTransaction := ⟨waiting.context.tx⟩
    ⟨msg, prepared, run.root.map (fun r => r.toLegacy.toEvm waiting), some run.result⟩

theorem run_observe (msg : Msg) (prepared : Jaune.TopLevel.Preparation)
    (hp : Jaune.TopLevel.prepare msg = .ok prepared) :
    (ofPreparation msg prepared hp).run.map (observe msg prepared) = Jaune.TopLevel.run msg := by
  rw [Jaune.TopLevel.run, hp]
  simp only [bind, Except.bind]
  cases prepared with
  | refused reason halted => rfl
  | frame f refund =>
    letI : LegacyTransaction := ⟨f.message.context.tx⟩
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
    f.message.context.tx.originalState = msg.benv.stat.origState := by
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
          msg.benv.stat.toBlockContext := congrArg BenvStat.toBlockContext (prepare_frame_block hp)
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
    f.message.context.tx.originalState = benv.state := by
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
private theorem initialCheckpoint_observe (msg : Msg) (isCreate : Bool) :
    (Message.ofLegacy (Jaune.Message.ofTop msg isCreate)).initialCheckpoint
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

private def legacyInput (msg : Msg) (isCreate : Bool) : TopLevel.Input :=
  let message := Message.ofLegacy (Jaune.Message.ofTop msg isCreate)
  let checkpoint := message.initialCheckpoint ⟨msg.benv.state, msg.tenv.transientStorage, msg.benv.storageWrites⟩
    msg.accessedAddresses msg.accessedStorageKeys msg.benv.createdAccounts msg.inheritedDeletions
  ⟨message, checkpoint, msg.tenv.stat.auths⟩

/-- The full observation of a waiting top-level preparation input. -/
def TopLevel.Input.ofLegacy (msg : Msg) : TopLevel.Input := legacyInput msg msg.target.isNone

/-- The mapped checkpoint is the actual initial machine on the waiting side. -/
theorem TopLevel.Input.ofLegacy_checkpoint (msg : Msg) :
    (ofLegacy msg).checkpoint =
      Frame.State.ofLegacy (Jaune.Frame.State.ofDevm (initDevm msg)) Mem.wf_empty :=
  initialCheckpoint_observe msg msg.target.isNone

namespace TopLevel

private def PreparationFailure.toEvmError : PreparationFailure → EvmError
  | .halt reason => .halt reason
  | .fault reason => Fault.toEvmError reason

/-- Compare preparation outcomes after projecting both checkpoint representations,
including the checkpoint carried by any failure. -/
private def PreparationAgrees (checked : PreparationResult α) (waiting : Except (EvmError × Devm) β)
    (seeChecked : α → γ) (seeWaiting : β → γ) : Prop :=
  ((checked.mapError fun (err, s) => (err.toEvmError, s.toLegacy)).map seeChecked) =
    ((waiting.mapError fun (err, d) => (err, Jaune.Frame.State.ofDevm d)).map seeWaiting)

private theorem PreparationAgrees.bind {checked : PreparationResult α}
    {waiting : Except (EvmError × Devm) β} {seeChecked : α → γ} {seeWaiting : β → γ}
    {nextChecked : α → PreparationResult α'} {nextWaiting : β → Except (EvmError × Devm) β'}
    {seeNextChecked : α' → γ'} {seeNextWaiting : β' → γ'}
    (head : PreparationAgrees checked waiting seeChecked seeWaiting)
    (tail : ∀ a b, seeChecked a = seeWaiting b →
      PreparationAgrees (nextChecked a) (nextWaiting b) seeNextChecked seeNextWaiting) :
    PreparationAgrees (checked >>= nextChecked) (waiting >>= nextWaiting) seeNextChecked seeNextWaiting := by
  cases checked <;> cases waiting <;>
    simp only [PreparationAgrees, Except.mapError, Except.map] at head
  · exact congrArg Except.error (Except.error.inj head)
  · contradiction
  · contradiction
  · exact tail _ _ (Except.ok.inj head)

private abbrev StateAgrees := @PreparationAgrees Frame.State Devm Jaune.Frame.State

private theorem charge_agrees (charge : Except (ExceptionalHalt × Frame.State) Frame.State)
    (execution : Execution) (s : Except (ExceptionalHalt × Jaune.Frame.State) Jaune.Frame.State)
    (native : MemorySimulation.Square charge s)
    (waiting : Jaune.Frame.State.ofExecution execution = Except.ofHalt s) :
    StateAgrees (preparationCharge charge) execution Frame.State.toLegacy Jaune.Frame.State.ofDevm := by
  rw [native.legacy_eq] at waiting
  cases charge <;> cases execution <;>
    simp only [Jaune.Frame.State.ofExecution, Except.mapResultState] at waiting
  all_goals first | contradiction | exact waiting.symm

private theorem chargeGas_agrees (gas : Nat) (s : Frame.State) (d : Devm)
    (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    StateAgrees (preparationCharge (s.chargeGas gas)) (Jaune.chargeGas gas d)
      Frame.State.toLegacy Jaune.Frame.State.ofDevm := by
  apply charge_agrees _ _ (s.toLegacy.chargeGas gas) (MemorySimulation.Frame.State.chargeGas s gas)
  rw [hs, Jaune.Frame.State.ofExecution_chargeGas]

private theorem chargeStateGas_agrees (gas : Nat) (s : Frame.State) (d : Devm)
    (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    StateAgrees (preparationCharge (s.chargeStateGas gas)) (Jaune.chargeStateGas gas d)
      Frame.State.toLegacy Jaune.Frame.State.ofDevm := by
  apply charge_agrees _ _ (s.toLegacy.chargeStateGas gas)
    (MemorySimulation.Frame.State.chargeStateGas s gas)
  rw [hs, Jaune.Frame.State.ofExecution_chargeStateGas]

private theorem chargeNewAuthority_agrees (rules : StateGasRules) (authority : Address)
    (s : Frame.State) (d : Devm) (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    StateAgrees (chargeNewAuthority rules authority s) (chargeNewAuthorityAmsterdam rules authority d)
      Frame.State.toLegacy Jaune.Frame.State.ofDevm := by
  have hw : s.world.state = d.state := congrArg (fun state : Jaune.Frame.State => state.world.state) hs
  unfold chargeNewAuthority chargeNewAuthorityAmsterdam
  rw [hw]
  split
  · exact chargeStateGas_agrees _ _ _ hs
  · exact congrArg Except.ok hs

private theorem chargeAuthorityWrite_agrees (rules : StateGasRules) (authority : Address)
    (s : Frame.State) (d : Devm) (paidWrites : AdrSet) (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    PreparationAgrees (chargeAuthorityWrite rules authority s paidWrites)
      (chargePaidAccountWriteAmsterdam rules authority d paidWrites)
      (Prod.map Frame.State.toLegacy id) (Prod.map Jaune.Frame.State.ofDevm id) := by
  unfold chargeAuthorityWrite chargePaidAccountWriteAmsterdam
  split
  · exact congrArg Except.ok (congrArg (·, paidWrites) hs)
  · apply PreparationAgrees.bind (chargeGas_agrees _ _ _ hs)
    intro _ _ h
    exact congrArg Except.ok (congrArg (·, paidWrites.insert authority) h)

private theorem chargeAuthorizationBase_agrees (rules : StateGasRules) (msg : Msg)
    (authority target : Address) (s : Frame.State) (d : Devm) (delegationSetFor : AdrSet)
    (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    PreparationAgrees (chargeAuthorizationBase rules msg.benv.stat.origState authority target s delegationSetFor)
      (chargeAuthBaseAmsterdam rules msg authority target d delegationSetFor)
      (fun (next, written) => (next.toLegacy, written,
        if target = 0 then .empty else (eoaDelegationMarker ++ target.toBytes).toByteArray))
      (fun (next, written, code) => (Jaune.Frame.State.ofDevm next, written, code)) := by
  by_cases ht : target = 0
  · simp only [chargeAuthorizationBase, chargeAuthBaseAmsterdam, ht, ↓reduceIte]
    exact congrArg Except.ok (congrArg (·, delegationSetFor, ByteArray.empty) hs)
  · simp only [chargeAuthorizationBase, chargeAuthBaseAmsterdam, ht, ↓reduceIte]
    split
    · apply PreparationAgrees.bind (chargeStateGas_agrees _ _ _ hs)
      intro _ _ h
      exact congrArg Except.ok (congrArg (·, delegationSetFor.insert authority,
        (eoaDelegationMarker ++ target.toBytes).toByteArray) h)
    · exact congrArg Except.ok (congrArg (·, delegationSetFor.insert authority,
        (eoaDelegationMarker ++ target.toBytes).toByteArray) hs)

private theorem writeDelegation_agrees (authority target : Address) (s : Frame.State) (d : Devm)
    (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    (s.writeDelegation authority target).toLegacy = Jaune.Frame.State.ofDevm
      ((d.setCode authority
        (if target = 0 then .empty else (eoaDelegationMarker ++ target.toBytes).toByteArray)).incrNonce authority) := by
  rw [Jaune.Frame.State.ofDevm_incrNonce, Jaune.Frame.State.ofDevm_setCode, ← hs]
  rfl

private theorem applyValidatedAuthorization_agrees (rules : StateGasRules) (msg : Msg) (isCreate : Bool)
    (authority target : Address) (s : Frame.State) (d : Devm) (paidWrites delegationSetFor : AdrSet)
    (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    PreparationAgrees (applyValidatedAuthorization rules (legacyInput msg isCreate).message.context
        authority target s paidWrites delegationSetFor)
      (applyValidatedDelegationAmsterdam rules msg authority target d paidWrites delegationSetFor)
      (Prod.map Frame.State.toLegacy id) (Prod.map Jaune.Frame.State.ofDevm id) := by
  unfold applyValidatedAuthorization applyValidatedDelegationAmsterdam
  apply PreparationAgrees.bind (chargeNewAuthority_agrees _ _ _ _ hs)
  intro s d h
  apply PreparationAgrees.bind (chargeAuthorityWrite_agrees _ _ _ _ _ h)
  rintro ⟨s, paid⟩ ⟨d, paid'⟩ hpaid
  change (s.toLegacy, paid) = (Jaune.Frame.State.ofDevm d, paid') at hpaid
  obtain ⟨h, rfl⟩ := Prod.mk.inj hpaid
  apply PreparationAgrees.bind (chargeAuthorizationBase_agrees _ msg _ _ _ _ _ h)
  rintro ⟨s, written⟩ ⟨d, written', code⟩ hwritten
  change (s.toLegacy, written, if target = 0 then .empty else (eoaDelegationMarker ++ target.toBytes).toByteArray) =
    (Jaune.Frame.State.ofDevm d, written', code) at hwritten
  obtain ⟨hstate, rfl, rfl⟩ := Prod.mk.inj hwritten |>.imp_right Prod.mk.inj
  exact congrArg Except.ok (congrArg (·, paid, written) (writeDelegation_agrees _ _ _ _ hstate))

private theorem recordAccountRead_agrees (rules : ForkRules) (a : Address) (s : Frame.State) (d : Devm)
    (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    (s.recordAccountRead rules a).toLegacy = Jaune.Frame.State.ofDevm (d.balReadAccount rules a) := by
  rw [Jaune.Frame.State.ofDevm_balReadAccount, ← hs]
  rfl

private theorem amsterdamAuthorizationStep_agrees (rules : StateGasRules) (msg : Msg) (isCreate : Bool)
    (auth : Authorization) (s : Frame.State) (d : Devm) (paidWrites delegationSetFor : AdrSet)
    (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    PreparationAgrees (amsterdamAuthorizationStep rules (legacyInput msg isCreate).message.context
        auth s paidWrites delegationSetFor)
      (setDelegationAmsterdamStep rules msg auth d paidWrites delegationSetFor)
      (Prod.map Frame.State.toLegacy id) (Prod.map Jaune.Frame.State.ofDevm id) := by
  have chain : (legacyInput msg isCreate).message.context.block.chainId = msg.benv.stat.chainId := rfl
  have fork : (legacyInput msg isCreate).message.context.block.rules = msg.benv.stat.rules := rfl
  unfold amsterdamAuthorizationStep setDelegationAmsterdamStep
  rw [chain, fork]
  split
  · exact congrArg Except.ok (congrArg (·, paidWrites, delegationSetFor) hs)
  split
  · exact congrArg Except.ok (congrArg (·, paidWrites, delegationSetFor) hs)
  cases recovered : recoverAuthority auth with
  | error reason =>
    cases reason with
    | invalidSignature => exact congrArg Except.ok (congrArg (·, paidWrites, delegationSetFor) hs)
    | pointCompression detail => exact congrArg Except.error (congrArg (EvmError.crypto (.pointCompression detail), ·) hs)
    | value detail => exact congrArg Except.error (congrArg (EvmError.crypto (.value detail), ·) hs)
  | ok authority =>
    have ha : (s.addAccessedAddress authority).toLegacy =
        Jaune.Frame.State.ofDevm (Jaune.addAccessedAddress d authority) := by
      rw [Jaune.Frame.State.ofDevm_addAccessedAddress, ← hs]
      rfl
    have hr := recordAccountRead_agrees msg.benv.stat.rules authority _ _ ha
    have hw := congrArg (fun state : Jaune.Frame.State => state.world.state) hr
    change ((s.addAccessedAddress authority).recordAccountRead msg.benv.stat.rules authority).world.state =
      ((Jaune.addAccessedAddress d authority).balReadAccount msg.benv.stat.rules authority).state at hw
    simp only [hw]
    split
    · exact congrArg Except.ok (congrArg (·, paidWrites, delegationSetFor) hr)
    split
    · exact congrArg Except.ok (congrArg (·, paidWrites, delegationSetFor) hr)
    · exact applyValidatedAuthorization_agrees _ _ _ _ _ _ _ _ _ hr

private theorem amsterdamAuthorizationLoop_agrees (rules : StateGasRules) (msg : Msg) (isCreate : Bool)
    (auths : List Authorization) (s : Frame.State) (d : Devm) (paidWrites delegationSetFor : AdrSet)
    (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    PreparationAgrees (amsterdamAuthorizationLoop rules (legacyInput msg isCreate).message.context
        auths s paidWrites delegationSetFor)
      (setDelegationAmsterdamLoop rules msg auths d paidWrites delegationSetFor)
      (Prod.map Frame.State.toLegacy id) (Prod.map Jaune.Frame.State.ofDevm id) := by
  induction auths generalizing s d paidWrites delegationSetFor with
  | nil => exact congrArg Except.ok (congrArg (·, paidWrites, delegationSetFor) hs)
  | cons auth rest ih =>
    unfold amsterdamAuthorizationLoop setDelegationAmsterdamLoop
    apply PreparationAgrees.bind (amsterdamAuthorizationStep_agrees _ _ _ _ _ _ _ _ hs)
    rintro ⟨s, paid, written⟩ ⟨d, paid', written'⟩ h
    change (s.toLegacy, paid, written) = (Jaune.Frame.State.ofDevm d, paid', written') at h
    obtain ⟨hstate, rfl, rfl⟩ := Prod.mk.inj h |>.imp_right Prod.mk.inj
    exact ih _ _ _ _ hstate

private theorem applyAmsterdamAuthorizations_agrees (rules : StateGasRules) (msg : Msg)
    (s : Frame.State) (d : Devm) (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    StateAgrees (applyAmsterdamAuthorizations rules { Input.ofLegacy msg with checkpoint := s })
      (setDelegationAmsterdam rules msg d) Frame.State.toLegacy Jaune.Frame.State.ofDevm := by
  have hkind : (Input.ofLegacy msg).message.isCreate = msg.target.isNone := by
    cases h : msg.target.isNone <;>
      simp only [Message.isCreate, Input.ofLegacy, legacyInput, Message.ofLegacy, Jaune.Message.ofTop, h,
        Bool.false_eq_true, ↓reduceIte]
  unfold applyAmsterdamAuthorizations setDelegationAmsterdam
  dsimp only
  rw [hkind]
  apply PreparationAgrees.bind (amsterdamAuthorizationLoop_agrees _ _ _ _ _ _ _ _ hs)
  rintro ⟨s, _, _⟩ ⟨d, _, _⟩ h
  exact congrArg Except.ok (congrArg Prod.fst h)

private theorem delegationCost_agrees (rules : ForkRules) (a : Address) (s : Frame.State) (d : Devm)
    (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    Checked.ForkRules.delegationCost rules s a = Jaune.ForkRules.delegationCost rules d a := by
  have code : s.code a = d.state.getCode a :=
    congrArg (fun state : Jaune.Frame.State => state.code a) hs
  have warm : s.accessedAddresses = d.accessedAddresses :=
    congrArg (fun state : Jaune.Frame.State => state.accessedAddresses) hs
  unfold Checked.ForkRules.delegationCost Jaune.ForkRules.delegationCost
  split
  · unfold Checked.GasSchedule.delegationCost Jaune.GasSchedule.delegationCost
    simp only [code, warm]
    rfl
  · rfl

private theorem completeDelegationAccess_agrees (s : Frame.State) (d : Devm) (delegated : Bool) (a : Address)
    (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    Prod.map id Frame.State.toLegacy (Checked.completeDelegationAccess s delegated a) =
    Prod.map id Jaune.Frame.State.ofDevm (Jaune.completeDelegationAccess d delegated a) := by
  have ha : (s.addAccessedAddress a).toLegacy = Jaune.Frame.State.ofDevm (Jaune.addAccessedAddress d a) := by
    rw [Jaune.Frame.State.ofDevm_addAccessedAddress, ← hs]
    rfl
  cases delegated
  · exact congrArg (fun state : Jaune.Frame.State => (state.code a, state)) hs
  · exact congrArg (fun state : Jaune.Frame.State => (state.code a, state)) ha

private abbrev MessageAgrees (checked : PreparationResult (Message × Frame.State))
    (waiting : Except (EvmError × Devm) (Msg × Devm)) (isCreate : Bool) :=
  PreparationAgrees checked waiting (Prod.map id Frame.State.toLegacy)
    (fun (msg, d) => (Message.ofLegacy (Jaune.Message.ofTop msg isCreate), Jaune.Frame.State.ofDevm d))

private theorem resolveAmsterdamCall_agrees (msg : Msg) (isCreate : Bool) (s : Frame.State) (d : Devm)
    (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    MessageAgrees (resolveAmsterdamCall (legacyInput msg isCreate).message s)
      (resolveTopLevelCallAmsterdam msg d) isCreate := by
  have cost : Checked.ForkRules.delegationCost (legacyInput msg isCreate).message.context.block.rules
      s (legacyInput msg isCreate).message.context.recipient =
      Jaune.ForkRules.delegationCost msg.benv.stat.rules d msg.currentTarget :=
    delegationCost_agrees msg.benv.stat.rules msg.currentTarget s d hs
  unfold resolveAmsterdamCall resolveTopLevelCallAmsterdam
  dsimp only
  rw [cost]
  rcases Jaune.ForkRules.delegationCost msg.benv.stat.rules d msg.currentTarget with ⟨delegated, address, gas⟩
  apply PreparationAgrees.bind (chargeGas_agrees _ _ _ hs)
  intro s d h
  have access := completeDelegationAccess_agrees s d delegated address h
  rcases hc : Checked.completeDelegationAccess s delegated address with ⟨code, next⟩
  rcases hd : Jaune.completeDelegationAccess d delegated address with ⟨code', next'⟩
  rw [hc, hd] at access
  change (code, next.toLegacy) = (code', Jaune.Frame.State.ofDevm next') at access
  obtain ⟨rfl, hnext⟩ := Prod.mk.inj access
  exact congrArg Except.ok (congrArg (fun state => (_, state)) (recordAccountRead_agrees _ _ _ _ hnext))

private theorem dispatchAmsterdam_agrees (rules : StateGasRules) (msg : Msg)
    (s : Frame.State) (d : Devm) (hs : s.toLegacy = Jaune.Frame.State.ofDevm d) :
    MessageAgrees (dispatchAmsterdam rules (Input.ofLegacy msg).message s)
      (dispatchTopLevelAmsterdam rules msg d) msg.target.isNone := by
  have hr := recordAccountRead_agrees msg.benv.stat.rules msg.currentTarget s d hs
  have fork : (Input.ofLegacy msg).message.context.block.rules = msg.benv.stat.rules := rfl
  have recipient : (Input.ofLegacy msg).message.context.recipient = msg.currentTarget := rfl
  have value : (Input.ofLegacy msg).message.context.value = msg.value := rfl
  have original : (Input.ofLegacy msg).message.context.tx.originalState = msg.benv.stat.origState := rfl
  have hw := congrArg (fun state : Jaune.Frame.State => state.world.state) hr
  change (s.recordAccountRead msg.benv.stat.rules msg.currentTarget).world.state =
    (d.balReadAccount msg.benv.stat.rules msg.currentTarget).state at hw
  unfold dispatchAmsterdam dispatchTopLevelAmsterdam
  dsimp only
  by_cases hcreate : msg.target.isNone = true
  · have kind : (Input.ofLegacy msg).message.kind = .create := by
      simp only [Input.ofLegacy, legacyInput, Message.ofLegacy, Jaune.Message.ofTop, hcreate, ↓reduceIte]
    have message_agrees (next : Devm) : (Input.ofLegacy msg).message =
        Message.ofLegacy (Jaune.Message.ofTop (preparedTopLevelMessage msg next) true) := by
      unfold Input.ofLegacy
      rw [hcreate]
      rfl
    simp only [kind, hcreate, ↓reduceIte, fork, recipient, original, hw]
    split
    · exact congrArg Except.error (congrArg (EvmError.halt (.addressCollision .none), ·) hr)
    · split
      · apply PreparationAgrees.bind (chargeStateGas_agrees _ _ _ hr)
        intro _ next h
        exact congrArg Except.ok (Prod.ext (message_agrees next) h)
      · exact congrArg Except.ok (Prod.ext (message_agrees _) hr)
  · have hcall : msg.target.isNone = false := Bool.eq_false_of_not_eq_true hcreate
    have kind : (Input.ofLegacy msg).message.kind = .call := by
      simp only [Input.ofLegacy, legacyInput, Message.ofLegacy, Jaune.Message.ofTop, hcall,
        Bool.false_eq_true, ↓reduceIte]
    simp only [kind, hcall, Bool.false_eq_true, ↓reduceIte, fork, recipient, value, hw]
    split
    · apply PreparationAgrees.bind (chargeStateGas_agrees _ _ _ hr)
      intro _ _ h
      simpa only [Input.ofLegacy, hcall] using resolveAmsterdamCall_agrees msg false _ _ h
    · simpa only [Input.ofLegacy, hcall, bind, Except.bind] using resolveAmsterdamCall_agrees msg false _ _ hr

/-- Amsterdam's authorization fold and dispatch agree on the prepared message and full
checkpoint, including the checkpoint at any halt or fault. -/
private theorem prepareAmsterdamFrame_agrees (rules : StateGasRules) (msg : Msg) :
    MessageAgrees (prepareAmsterdamFrame rules (Input.ofLegacy msg))
      (prepareTopLevelAmsterdam rules msg) msg.target.isNone := by
  have hs : (Input.ofLegacy msg).checkpoint.toLegacy = Jaune.Frame.State.ofDevm (initDevm msg) := by
    rw [Input.ofLegacy_checkpoint]
    exact Frame.State.toLegacy_ofLegacy _ _
  have auths : (Input.ofLegacy msg).authorizationList = msg.tenv.stat.auths := rfl
  unfold prepareAmsterdamFrame prepareTopLevelAmsterdam
  by_cases empty : msg.tenv.stat.auths.isEmpty = true
  · simp only [auths, empty, ↓reduceIte, bind, Except.bind, finishTopLevelAmsterdam]
    exact dispatchAmsterdam_agrees rules msg _ _ hs
  · simp only [auths, empty, finishTopLevelAmsterdam]
    apply PreparationAgrees.bind (applyAmsterdamAuthorizations_agrees rules msg _ _ hs)
    intro s d h
    apply dispatchAmsterdam_agrees
    change s.commitStateGas.toLegacy = Jaune.Frame.State.ofDevm d.commitStateGas
    rw [Jaune.Frame.State.ofDevm_commitStateGas, ← h]
    rfl

private theorem authorizationStep_observe (auth : Authorization) (msg : Msg) (refund : U256)
    (isCreate : Bool) :
    (authorizationStep auth (legacyInput msg isCreate) refund).mapError Fault.toEvmError =
      (setDelegationStep auth msg refund).map (fun (next, refund) => (legacyInput next isCreate, refund)) := by
  have block : (legacyInput msg isCreate).message.context.block = msg.benv.stat.toBlockContext := rfl
  have world (authority : Address) :
      ((legacyInput msg isCreate).checkpoint.addAccessedAddress authority).world.state = msg.benv.state := rfl
  unfold authorizationStep setDelegationStep
  simp only [block, world, BenvStat.toBlockContext, BlockContext.rules, BenvStat.rules]
  by_cases hchain : (auth.chainId != Jaune.UInt64.toU256 msg.benv.stat.chainId && auth.chainId != 0) = true
  · simp only [hchain, ↓reduceIte]
    rfl
  · simp only [hchain]
    by_cases hnonce : auth.nonce = UInt64.max
    · simp only [hnonce, ↓reduceIte]
      rfl
    · simp only [hnonce, ↓reduceIte]
      cases recovered : recoverAuthority auth with
      | error fault => cases fault <;> rfl
      | ok authority =>
        by_cases hcode : ¬((msg.benv.state.get authority).code.isEmpty ∨
            isValidDelegation (msg.benv.state.get authority).code)
        · simp only [hcode]
          rfl
        · simp only [hcode, ↓reduceIte]
          by_cases haccount : ((msg.benv.state.get authority).nonce != auth.nonce) = true
          · simp only [haccount, ↓reduceIte]
            rfl
          · simp only [haccount, Bool.false_eq_true, ↓reduceIte, Except.map, Except.mapError,
              Frame.State.writeDelegation, legacyInput, Message.initialCheckpoint, Message.ofLegacy,
              Jaune.Message.ofTop, Frame.State.addAccessedAddress, Substate.addAccessedAddress,
              Frame.State.withWorld, Frame.State.withSubstate, Msg.setCode, Msg.incrNonce,
              World.clearStorageWritesIfEmpty, Benv.clearStorageWritesIfEmpty]
            rfl

private theorem authorizationLoop_observe (auths : List Authorization) (msg : Msg) (refund : U256)
    (isCreate : Bool) :
    (authorizationLoop auths (legacyInput msg isCreate) refund).mapError Fault.toEvmError =
      (setDelegationLoop auths msg refund).map (fun (next, refund) => (legacyInput next isCreate, refund)) := by
  induction auths generalizing msg refund with
  | nil => rfl
  | cons auth rest ih =>
    have step := authorizationStep_observe auth msg refund isCreate
    unfold authorizationLoop setDelegationLoop
    cases ha : authorizationStep auth (legacyInput msg isCreate) refund <;>
      cases hb : setDelegationStep auth msg refund <;>
      simp only [ha, hb, Except.mapError, Except.map] at step <;>
      cases step
    · rfl
    · exact ih _ _

private theorem applyAuthorizations_observe (msg : Msg) (isCreate : Bool) :
    (applyAuthorizations (legacyInput msg isCreate)).mapError Fault.toEvmError =
      (Jaune.TopLevel.applyAuthorizations msg).map
        (fun (next, refund) => (legacyInput next isCreate, refund)) := by
  have enabled : (legacyInput msg isCreate).message.context.block.rules.delegationEnabled =
      msg.benv.stat.rules.delegationEnabled := rfl
  have auths : (legacyInput msg isCreate).authorizationList = msg.tenv.stat.auths := rfl
  unfold applyAuthorizations Jaune.TopLevel.applyAuthorizations setDelegation
  simp only [enabled, auths]
  by_cases skip : (!msg.benv.stat.rules.delegationEnabled || msg.tenv.stat.auths.isEmpty) = true
  · simp only [skip, ↓reduceIte]
    rfl
  · simp only [skip]
    have loop := authorizationLoop_observe msg.tenv.stat.auths msg 0 isCreate
    cases hn : authorizationLoop msg.tenv.stat.auths (legacyInput msg isCreate) 0 <;>
      cases ho : setDelegationLoop msg.tenv.stat.auths msg 0 <;>
      simp only [hn, ho, Except.mapError, Except.map] at loop <;>
      cases loop
    · rfl
    · rename_i pair
      obtain ⟨next, refund⟩ := pair
      have address : (legacyInput next isCreate).message.codeAddress = next.codeAddress := rfl
      simp only [bind, Except.bind, address]
      cases next.codeAddress <;> rfl

private theorem resolveCodeDelegation_observe (msg : Msg) (isCreate : Bool) :
    resolveCodeDelegation (legacyInput msg isCreate) =
      legacyInput (Jaune.TopLevel.resolveCodeDelegation msg) isCreate := by
  have destination : (legacyInput msg isCreate).message.context.block.rules.delegatedCodeAddress
      (legacyInput msg isCreate).message.context.code =
      msg.benv.stat.rules.delegatedCodeAddress msg.code := rfl
  unfold resolveCodeDelegation Jaune.TopLevel.resolveCodeDelegation
  simp only [destination]
  cases msg.benv.stat.rules.delegatedCodeAddress msg.code <;> rfl

/-- The native observation of the waiting Checked preparation. -/
def Prepared.ofWaiting : Preparation → Prepared
  | .refused reason => .refused reason
  | .frame f refund => .frame f.message f.checkpoint refund

private theorem Prepared.ofWaiting_frameOfTop (msg : Msg) (isCreate : Bool) (refund : Nat)
    (h : (Jaune.Frame.ofTop msg isCreate).checkpoint.machine.memory.Wf) :
    ofWaiting (.frame (Frame.ofLegacy (Jaune.Frame.ofTop msg isCreate) h) refund) =
      .frame (legacyInput msg isCreate).message (legacyInput msg isCreate).checkpoint refund := by
  simp only [ofWaiting, Frame.ofLegacy, Jaune.Frame.ofTop, legacyInput]
  rw [initialCheckpoint_observe]

/-- Ordinary native preparation agrees on the full refusal, fault, or prepared frame. -/
theorem prepareWithoutStateGas_observe (msg : Msg) (hgas : msg.benv.stat.rules.stateGas = none) :
    prepareWithoutStateGas (Input.ofLegacy msg) = (prepare msg).map Prepared.ofWaiting := by
  cases target : msg.target with
  | none =>
    rw [show Input.ofLegacy msg = legacyInput msg true by simp only [Input.ofLegacy, target, Option.isNone]]
    change (if accountHasCodeOrNonce msg.benv.state msg.currentTarget then
      Except.ok (Prepared.refused (.collision (.addressCollision .none)))
      else Except.ok (Prepared.frame (legacyInput msg true).message (legacyInput msg true).checkpoint 0)) = _
    by_cases collision : accountHasCodeOrNonce msg.benv.state msg.currentTarget
    · have waiting : Jaune.TopLevel.prepare msg = .ok (.refused (.addressCollision .none) (initDevm msg)) := by
        simp only [Jaune.TopLevel.prepare, target, Option.isNone, ↓reduceIte,
          Jaune.TopLevel.prepare.create, hgas, collision]
      simp only [collision, ↓reduceIte]
      unfold prepare
      split <;> rename_i h <;> rw [waiting] at h <;> cases h
      simp only [Except.map, ofPreparation, hgas, Prepared.ofWaiting]
    · have waiting : Jaune.TopLevel.prepare msg = .ok (.frame (Jaune.Frame.ofTop msg true) 0) := by
        simp only [Jaune.TopLevel.prepare, target, Option.isNone, Bool.false_eq_true, ↓reduceIte,
          Jaune.TopLevel.prepare.create, hgas, collision]
      simp only [collision, Bool.false_eq_true, ↓reduceIte]
      unfold prepare
      split <;> rename_i h <;> rw [waiting] at h <;> cases h
      simp only [Except.map, ofPreparation, Prepared.ofWaiting_frameOfTop]
  | some address =>
    rw [show Input.ofLegacy msg = legacyInput msg false by simp only [Input.ofLegacy, target, Option.isNone]]
    change (do
      let (authorized, refund) ← applyAuthorizations (legacyInput msg false)
      let resolved := resolveCodeDelegation authorized
      pure (Prepared.frame resolved.message resolved.checkpoint refund)) = _
    have agreement := applyAuthorizations_observe msg false
    cases hn : applyAuthorizations (legacyInput msg false) <;>
      cases ho : Jaune.TopLevel.applyAuthorizations msg <;>
      simp only [hn, ho, Except.mapError, Except.map] at agreement <;>
      cases agreement
    · rename_i fault
      have waiting : Jaune.TopLevel.prepare msg = .error fault := by
        simp only [Jaune.TopLevel.prepare, target, Option.isNone, Bool.false_eq_true, ↓reduceIte,
          Jaune.TopLevel.prepare.call, hgas]
        split <;> rename_i h <;> rw [ho] at h <;> cases h
        cases fault <;> rfl
      unfold prepare
      split <;> rename_i h <;> rw [waiting] at h <;> cases h
      rfl
    · rename_i pair
      obtain ⟨next, refund⟩ := pair
      have waiting : Jaune.TopLevel.prepare msg =
          .ok (.frame (Jaune.Frame.ofTop (Jaune.TopLevel.resolveCodeDelegation next) false) refund) := by
        simp only [Jaune.TopLevel.prepare, target, Option.isNone, Bool.false_eq_true, ↓reduceIte,
          Jaune.TopLevel.prepare.call, hgas]
        split <;> rename_i h <;> rw [ho] at h <;> cases h
        rfl
      unfold prepare
      split <;> rename_i h <;> rw [waiting] at h <;> cases h
      simp only [bind, Except.bind, pure, Except.pure, resolveCodeDelegation_observe,
        Except.map, ofPreparation, Prepared.ofWaiting_frameOfTop]

private theorem prepare_waiting_amsterdam (msg : Msg) (rules : StateGasRules)
    (hgas : msg.benv.stat.rules.stateGas = some rules) :
    Jaune.TopLevel.prepare msg = Jaune.TopLevel.prepare.amsterdam rules msg msg.target.isNone := by
  cases h : msg.target.isNone <;>
    simp only [Jaune.TopLevel.prepare, Jaune.TopLevel.prepare.create, Jaune.TopLevel.prepare.call,
      hgas, h, Bool.false_eq_true, ↓reduceIte]

private theorem prepareNative_amsterdam_observe (msg : Msg) (rules : StateGasRules)
    (hgas : msg.benv.stat.rules.stateGas = some rules) :
    prepareNative (Input.ofLegacy msg) = (prepare msg).map Prepared.ofWaiting := by
  have gas : (Input.ofLegacy msg).message.context.block.rules.stateGas = some rules := hgas
  have hw := prepare_waiting_amsterdam msg rules hgas
  have agreement := prepareAmsterdamFrame_agrees rules msg
  unfold prepareNative prepare
  rw [gas]
  dsimp only
  cases hn : prepareAmsterdamFrame rules (Input.ofLegacy msg) <;>
    cases ho : prepareTopLevelAmsterdam rules msg <;>
    simp only [MessageAgrees, PreparationAgrees, hn, ho, Except.mapError, Except.map] at agreement
  · rename_i native waiting
    rcases native with ⟨failure, s⟩
    rcases waiting with ⟨error, d⟩
    obtain ⟨herror, hstate⟩ := Prod.mk.inj (Except.error.inj agreement)
    cases failure with
    | halt reason =>
      simp only [PreparationFailure.toEvmError] at herror
      subst error
      have waiting : Jaune.TopLevel.prepare msg = .ok (.refused reason d) := by
        rw [hw]
        unfold Jaune.TopLevel.prepare.amsterdam
        split <;> rename_i h <;> rw [ho] at h <;> cases h
        rfl
      have reads := congrArg Jaune.Frame.State.trail hstate
      change s.trail = (Jaune.Frame.State.ofDevm d).trail at reads
      change (Except.ok (.refused (.stateGas reason (Input.ofLegacy msg).message.stateGasGrant
        s.trail.accountReads s.trail.storageReads)) : Except Fault Prepared) = _
      split <;> rename_i h <;> rw [waiting] at h <;> cases h
      simp only [Except.map, ofPreparation, Prepared.ofWaiting, hgas, reads]
      rfl
    | fault fault =>
      simp only [PreparationFailure.toEvmError] at herror
      subst error
      have waiting : Jaune.TopLevel.prepare msg = .error fault := by
        rw [hw]
        unfold Jaune.TopLevel.prepare.amsterdam
        cases fault <;> simp only [Fault.toEvmError] at ho <;>
          split <;> rename_i h <;> rw [ho] at h <;> cases h <;> rfl
      change (Except.error fault : Except Fault Prepared) = _
      split <;> rename_i h <;> rw [waiting] at h <;> cases h
      rfl
  · contradiction
  · contradiction
  · rename_i native waiting
    rcases native with ⟨message, s⟩
    rcases waiting with ⟨prepared, d⟩
    change (Except.ok (.frame message s 0) : Except Fault Prepared) = _
    obtain ⟨hmessage, hstate⟩ := Prod.mk.inj (Except.ok.inj agreement)
    change message = Message.ofLegacy (Jaune.Message.ofTop prepared msg.target.isNone) at hmessage
    change s.toLegacy = Jaune.Frame.State.ofDevm d at hstate
    have waiting : Jaune.TopLevel.prepare msg =
        .ok (.frame ⟨Jaune.Message.ofTop prepared msg.target.isNone, Jaune.Frame.State.ofDevm d⟩ 0) := by
      rw [hw]
      unfold Jaune.TopLevel.prepare.amsterdam
      split <;> rename_i h <;> rw [ho] at h <;> cases h
      rfl
    split <;> rename_i h <;> rw [waiting] at h <;> cases h
    simp only [Except.map, ofPreparation, Prepared.ofWaiting, Frame.ofLegacy]
    have hcheckpoint (raw : Jaune.Frame.State) (hraw : s.toLegacy = raw) (wf : raw.machine.memory.Wf) :
        Frame.State.ofLegacy raw wf = s := by
      subst raw
      exact Frame.State.ofLegacy_toLegacy s
    rw [hmessage, hcheckpoint _ hstate]

/-- Native preparation preserves the full observable outcome on every fork. -/
theorem prepareNative_observe (msg : Msg) :
    prepareNative (Input.ofLegacy msg) = (prepare msg).map Prepared.ofWaiting := by
  cases hgas : msg.benv.stat.rules.stateGas with
  | none =>
    have hg : (Input.ofLegacy msg).message.context.block.rules.stateGas = none := hgas
    unfold prepareNative
    rw [hg]
    exact prepareWithoutStateGas_observe msg hgas
  | some rules => exact prepareNative_amsterdam_observe msg rules hgas

/-- Native preparation and execution agree with the Checked observation of the waiting run. -/
theorem runNative_observe (msg : Msg) : runNative (Input.ofLegacy msg) = run msg := by
  unfold runNative run
  rw [prepareNative_observe]
  cases prepare msg with
  | error => rfl
  | ok prepared => cases prepared <;> rfl

/-- The shared system-call entry preserves its own start world, gas grant, and access sets. -/
theorem systemInput_observe (benv : Benv) (target : Address) (code : ByteArray) (data : Bytes) :
    systemInput benv.stat.toBlockContext benv.state benv.createdAccounts target code data =
      Input.ofLegacy (systemCallMessage benv target code data) := by
  have rules : benv.stat.toBlockContext.rules = benv.stat.rules := rfl
  cases h : benv.stat.fork.ruleSet.stateGas <;>
    simp only [systemInput, systemCallMessage, systemTransactionEnvironment, systemTransactionMessage,
      Benv.beginTransaction, Input.ofLegacy, legacyInput, Message.ofLegacy, Jaune.Message.ofTop,
      Option.isNone, Bool.false_eq_true, ↓reduceIte, rules, BenvStat.rules, h] <;> rfl

/-- Every protocol system call prepares through the same Checked entry and Amsterdam rules. -/
theorem prepareSystem_observe (benv : Benv) (target : Address) (code : ByteArray) (data : Bytes) :
    prepareNative (systemInput benv.stat.toBlockContext benv.state benv.createdAccounts target code data) =
      (prepare (systemCallMessage benv target code data)).map Prepared.ofWaiting := by
  rw [systemInput_observe]
  exact prepareNative_observe _

end TopLevel

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
        Prepared.ofLegacy, TopLevel.Input.ofLegacy, legacyInput] <;> rfl

/-- Signed transaction preparation followed by native top-level preparation preserves the
observed refusal, fault, or frame of the waiting signed path. -/
theorem Transaction.prepareFrame_observe (admitted : Jaune.Transaction.Admitted) (tx : Jaune.Transaction)
    (index : Nat) :
    (prepare admitted.benv.stat.toBlockContext admitted.benv.stat.origState admitted tx >>= fun prepared =>
      (TopLevel.prepareNative prepared.input).mapError (fun fault => TransitionError.vm fault.toEvmError)) =
    (Jaune.Transaction.prepare admitted tx index >>= fun prepared =>
      ((TopLevel.prepare prepared.msg).map TopLevel.Prepared.ofWaiting).mapError
        (fun fault => TransitionError.vm fault.toEvmError)) := by
  rw [Transaction.prepare_observe admitted tx index]
  cases Jaune.Transaction.prepare admitted tx index with
  | error => rfl
  | ok prepared =>
    exact congrArg (Except.mapError (fun fault => TransitionError.vm fault.toEvmError))
      (TopLevel.prepareNative_observe prepared.msg)

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
