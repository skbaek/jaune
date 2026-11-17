import Jaune.Exec

/-!
Raw outcome commitment, complete frame settlement and retained child frames.
CREATE code-deposit failure remains distinct from raw child success.
-/

namespace Jaune

-- `ByteArray.getInst` and other extensions of root types live in `Jaune`;
-- opening it lets generalized field notation (`code.getInst`) find them.
open Jaune

/-- Whether an execution outcome commits its frame state. -/
def Execution.commits : Execution → Bool
  | .error _ => false
  | .ok post => post.error.isNone

/-- Whether the child world survives the complete message-frame settlement.
For CREATE this is strictly stronger than raw execution success: code-deposit
failure rolls the constructor world back before the parent resumes. -/
def Legacy.Frame.settlementCommits (frame : Legacy.Frame) (raw : Execution) : Bool :=
  match frame.settle raw with
  | .error _ => false
  | .ok post => post.error.isNone

private theorem execution_commits_of_handleErrorWith_clean
    {raw : Execution} {post : Devm} {sg : Option StateGasRules}
    (hresult : executeCode.handleErrorWith sg raw = .ok post)
    (hclean : post.error.isNone = true) :
    Execution.commits raw = true := by
  cases sg with
  | none =>
      rw [executeCode.handleErrorWith_none] at hresult
      cases raw with
      | ok rawPost =>
          simp only [executeCode.handleError, Except.ok.injEq] at hresult
          subst post
          exact hclean
      | error error =>
          rcases error with ⟨error, rawPost⟩
          cases error <;>
            simp [executeCode.handleError, Devm.withError,
              Devm.setMeta] at hresult
          all_goals subst post
          all_goals change (some _).isNone = true at hclean
          all_goals simp at hclean
  | some _ =>
      rw [executeCode.handleErrorWith_some] at hresult
      cases raw with
      | ok rawPost =>
          simp only [executeCode.handleErrorAmsterdam, Except.ok.injEq] at hresult
          subst post
          exact hclean
      | error error =>
          rcases error with ⟨error, rawPost⟩
          cases error <;>
            simp [executeCode.handleErrorAmsterdam, Devm.withError,
              Devm.setMeta] at hresult
          all_goals subst post
          all_goals change (some _).isNone = true at hclean
          all_goals simp at hclean

private theorem processMessage_clean_input
    {msg : Msg}
    {input : Except (EvmError × State × AdrSet × TransientStorage) Devm}
    {post : Devm}
    (hresult : processMessage.settle msg input = .ok post)
    (hclean : post.error.isNone = true) :
    ∃ pre : Devm, input = .ok pre ∧ pre.error.isNone = true := by
  cases input with
  | error error =>
      simp [processMessage.settle, Bind.bind, Except.bind] at hresult
  | ok pre =>
      cases herror : pre.error with
      | none => exact ⟨pre, rfl, by simp [herror]⟩
      | some error =>
          simp [processMessage.settle, Bind.bind, Except.bind, herror] at hresult
          rw [← hresult] at hclean
          change pre.error.isNone = true at hclean
          rw [herror] at hclean
          simp at hclean

/-- A clean successful message settlement retains a clean successful raw
input and changes no world state after that input.  This is the common
settlement seam for consumers that need the exact retained endpoint rather
than merely the fact that the frame commits. -/
theorem ProcessMessage.clean_input_state_of_settle
    {msg : Msg}
    {input : Except (EvmError × State × AdrSet × TransientStorage) Devm}
    {post : Devm}
    (hresult : processMessage.settle msg input = .ok post)
    (hclean : post.error.isSome = false) :
    ∃ raw : Devm, input = .ok raw ∧ raw.error.isSome = false ∧
      post.state = raw.state := by
  have postNone : post.error.isNone = true := by
    cases herror : post.error <;> simp_all
  rcases processMessage_clean_input hresult postNone with
    ⟨raw, rfl, rawNone⟩
  have rawSome : raw.error.isSome = false := by
    cases herror : raw.error <;> simp_all
  refine ⟨raw, rfl, rawSome, ?_⟩
  unfold processMessage.settle at hresult
  dsimp only [bind, Except.bind] at hresult
  rw [ite_eq_right (by simp [rawSome])] at hresult
  rw [← Except.ok.inj hresult]
  rfl

private theorem processCreateMessage_clean_input
    {msg : Msg}
    {input : Except (EvmError × State × AdrSet × TransientStorage) Devm}
    {post : Devm}
    (hresult : processCreateMessage.settle msg input = .ok post)
    (hclean : post.error.isNone = true) :
    ∃ pre : Devm, input = .ok pre ∧ pre.error.isNone = true := by
  cases input with
  | error error =>
      simp [processCreateMessage.settle, Bind.bind, Except.bind] at hresult
  | ok pre =>
      cases herror : pre.error with
      | none => exact ⟨pre, rfl, by simp [herror]⟩
      | some error =>
          simp [processCreateMessage.settle, Bind.bind, Except.bind, herror] at hresult
          rw [← hresult] at hclean
          change pre.error.isNone = true at hclean
          rw [herror] at hclean
          simp at hclean

/-- Complete frame settlement can be clean only when the underlying code
execution itself was clean. -/
theorem Legacy.Frame.raw_commits_of_settlementCommits
    {frame : Legacy.Frame} {raw : Execution}
    (h : Legacy.Frame.settlementCommits frame raw = true) :
    Execution.commits raw = true := by
  unfold Legacy.Frame.settlementCommits at h
  cases hsettled : frame.settle raw with
  | error error => simp [hsettled] at h
  | ok settled =>
      have hclean : settled.error.isNone = true := by
        simpa only [hsettled] using h
      unfold Legacy.Frame.settle Legacy.Frame.settleMsg at hsettled
      cases hcreate : frame.isCreate with
      | false =>
          simp only [hcreate, Bool.false_eq_true, ↓reduceIte] at hsettled
          rcases processMessage_clean_input hsettled hclean with
            ⟨handled, hhandled, hhandledClean⟩
          exact execution_commits_of_handleErrorWith_clean hhandled hhandledClean
      | true =>
          simp only [hcreate, ↓reduceIte] at hsettled
          rcases processCreateMessage_clean_input hsettled hclean with
            ⟨inner, hinner, hinnerClean⟩
          rcases processMessage_clean_input hinner hinnerClean with
            ⟨handled, hhandled, hhandledClean⟩
          exact execution_commits_of_handleErrorWith_clean hhandled hhandledClean

/-- The concrete outcome indexed by an `Exec` derivation. -/
def Legacy.Exec.outcome {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (_ : Legacy.Exec pc sevm pre out) : Execution := out

/-- A retained successful execution frame.  Keeping the full derivation makes
the history suitable for later provenance refinements, rather than merely
retaining a precomputed numeric tally. -/
structure Legacy.Exec.Frame where
  pc : Nat
  sevm : Sevm
  pre : Devm
  out : Execution
  run : Legacy.Exec pc sevm pre out
  committed : Execution.commits out = true

/-- The committed post-machine indexed by a retained frame. -/
def Execution.committedPost (out : Execution)
    (h : Execution.commits out = true) : Devm :=
  match out with
  | .ok post => post
  | .error _ => by simp [Execution.commits] at h

def Legacy.Exec.Frame.post (frame : Legacy.Exec.Frame) : Devm :=
  Execution.committedPost frame.out frame.committed

def Legacy.Exec.Frame.ofRun {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Legacy.Exec pc sevm pre out)
    (committed : Execution.commits out = true) : Legacy.Exec.Frame :=
  ⟨pc, sevm, pre, out, run, committed⟩

/-- Successful descendant frames whose effects survive in the enclosing
successful frame.  Failed children are discarded, while successful children
are traversed to arbitrary depth. -/
def Legacy.Exec.descendantFrames {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Legacy.Exec pc sevm pre out) : List Legacy.Exec.Frame :=
  match run with
  | .halt _ => []
  | .cont _ next => Legacy.Exec.descendantFrames next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next => Legacy.Exec.descendantFrames next
  | .runErr _ _ _ _ => []
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      let childFrames :=
        if h : Legacy.Frame.settlementCommits frame raw = true then
          let hraw : Execution.commits raw = true :=
            Legacy.Frame.raw_commits_of_settlementCommits h
          Legacy.Exec.Frame.ofRun child hraw :: Legacy.Exec.descendantFrames child
        else []
      childFrames ++ Legacy.Exec.descendantFrames next
termination_by sizeOf run

/-- A successful spawn retains its settlement-committing child before the
child's descendants and before the parent continuation's descendants. -/
@[simp] theorem Legacy.Exec.descendantFrames_runOk_of_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {f : Jaune.Legacy.Frame} {rsm : Resume}
    {cevm : Evm} {raw out : Execution}
    (hstep : Jaune.Legacy.Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Legacy.Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (next : Legacy.Exec pc' sevm devm' out)
    (hcommit : Legacy.Frame.settlementCommits f raw = true) :
    Legacy.Exec.descendantFrames (Legacy.Exec.runOk hstep henter child hr next) =
      Legacy.Exec.Frame.ofRun child
          (Legacy.Frame.raw_commits_of_settlementCommits hcommit) ::
        Legacy.Exec.descendantFrames child ++ Legacy.Exec.descendantFrames next := by
  simp [Legacy.Exec.descendantFrames, hcommit]

/-- A spawned child whose complete frame settlement does not commit contributes
no retained frame, even if its raw execution itself committed. -/
@[simp] theorem Legacy.Exec.descendantFrames_runOk_of_not_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {f : Jaune.Legacy.Frame} {rsm : Resume}
    {cevm : Evm} {raw out : Execution}
    (hstep : Jaune.Legacy.Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Legacy.Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (next : Legacy.Exec pc' sevm devm' out)
    (hnot : Legacy.Frame.settlementCommits f raw ≠ true) :
    Legacy.Exec.descendantFrames (Legacy.Exec.runOk hstep henter child hr next) =
      Legacy.Exec.descendantFrames next := by
  simp only [Legacy.Exec.descendantFrames, dite_eq_right hnot, List.nil_append]

/-- In particular, a CREATE child whose raw execution commits but whose
code-deposit settlement rolls back contributes no descendant frame.  The raw
commit premise records the semantic counterexample to pruning by raw outcome
alone. -/
theorem Legacy.Exec.descendantFrames_runOk_create_codeDepositRollback
    {pc pc' : Nat} {sevm : Sevm} {pre devm' settled : Devm}
    {f : Jaune.Legacy.Frame} {rsm : Resume}
    {cevm : Evm} {raw out : Execution}
    (hstep : Jaune.Legacy.Evm.step ⟨pc, sevm, pre⟩ = .spawn f rsm pc')
    (henter : f.enter = .run cevm)
    (child : Legacy.Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : rsm.run (f.settle raw) = .ok devm')
    (next : Legacy.Exec pc' sevm devm' out)
    (_rawCommits : Execution.commits raw = true)
    (hcreate : f.isCreate = true)
    (hsettled : processCreateMessage.settle f.outer
      (processMessage.settle f.inner
        (executeCode.handleErrorWith f.inner.benv.stat.rules.stateGas raw)) =
        .ok settled)
    (herror : settled.error.isSome = true) :
    Legacy.Exec.descendantFrames (Legacy.Exec.runOk hstep henter child hr next) =
      Legacy.Exec.descendantFrames next := by
  apply Legacy.Exec.descendantFrames_runOk_of_not_settlementCommits
    hstep henter child hr next
  intro hcommit
  have hframeSettle : f.settle raw = .ok settled := by
    unfold Legacy.Frame.settle Legacy.Frame.settleMsg
    simpa only [hcreate, ↓reduceIte] using hsettled
  unfold Legacy.Frame.settlementCommits at hcommit
  rw [hframeSettle] at hcommit
  cases hoption : settled.error with
  | none => simp [hoption] at herror
  | some error => simp [hoption] at hcommit

/-- All and only committed frames in a successful root execution.  An errored
root contributes no frames, so a later enclosing rollback cannot leak actions
into the accounting fold. -/
def Legacy.Exec.committedFrames {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Legacy.Exec pc sevm pre out) : List Legacy.Exec.Frame :=
  if h : Execution.commits out = true then
    Legacy.Exec.Frame.ofRun run h :: Legacy.Exec.descendantFrames run
  else []

/-- A noncommitting root contributes no retained frame, regardless of any
locally successful descendants in its derivation. -/
@[simp] theorem Legacy.Exec.committedFrames_eq_nil_of_not_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Legacy.Exec pc sevm pre out)
    (h : Execution.commits out ≠ true) :
    Legacy.Exec.committedFrames run = [] := by
  simp [Legacy.Exec.committedFrames, h]

theorem ProcessMessage.settlementCommits_of_some_ok_clean
    {msg : Msg} {pc : Nat} {sevm : Sevm} {pre child : Devm}
    {raw : Execution}
    (hprocess : ProcessMessage msg
      (.some ⟨⟨pc, sevm, pre⟩, raw⟩) (.ok child))
    (hclean : child.error.isSome = false) :
    Legacy.Frame.settlementCommits (Legacy.Frame.ofCall msg) raw = true := by
  have hsettle := (RunFrame.some_inv hprocess).2
  have hclean' : child.error.isNone = true := by
    cases herror : child.error <;> simp_all
  unfold Legacy.Frame.settlementCommits
  rw [← hsettle]
  exact hclean'

theorem Legacy.Frame.settlementCommits_ofCall_of_raw_commits
    {msg : Msg} {raw : Execution}
    (hraw : Execution.commits raw = true) :
    Legacy.Frame.settlementCommits (Legacy.Frame.ofCall msg) raw = true := by
  cases raw with
  | error err =>
      simp [Execution.commits] at hraw
  | ok post =>
      cases herror : post.error with
      | none =>
          simp [Legacy.Frame.settlementCommits, Legacy.Frame.settle, Legacy.Frame.settleMsg,
            Legacy.Frame.ofCall, executeCode.handleErrorWith_ok,
            processMessage.settle, Bind.bind, Except.bind, herror]
      | some error =>
          simp [Execution.commits, herror] at hraw

/-- Updating one account without changing its balance preserves the complete
world-balance map. -/
lemma State.set_bal {st : Jaune.State} {a : Address} {ac : Account}
    (h : ac.balance = (st.get a).balance) : (st.set a ac).bal = st.bal := by
  funext b
  by_cases hb : b = a
  · subst hb
    show ((st.set b ac).get b).balance = (st.get b).balance
    rw [State.get_set_self]
    exact h
  · show ((st.set a ac).get b).balance = (st.get b).balance
    rw [State.get_set_ne _ (fun hc => hb hc.symm)]

/-- Presence-preserving updates also preserve every balance when the written
account's balance agrees with the prior account. -/
lemma State.setPresent_bal {st : Jaune.State} {a : Address} {ac : Account}
    (h : ac.balance = (st.get a).balance) : (st.setPresent a ac).bal = st.bal := by
  funext b
  by_cases hb : b = a
  · subst hb
    show ((st.setPresent b ac).get b).balance = (st.get b).balance
    rw [State.get_setPresent_self]
    exact h
  · show ((st.setPresent a ac).get b).balance = (st.get b).balance
    rw [State.get_setPresent_ne _ (fun hc => hb hc.symm)]

lemma State.setStor_bal {st : Jaune.State} {a : Address} {s : Storage} :
    (st.setStor a s).bal = st.bal := by
  unfold State.setStor
  split
  · exact State.setPresent_bal rfl
  · exact State.set_bal rfl

lemma State.incrNonce_bal {st : Jaune.State} {a : Address} :
    (st.incrNonce a).bal = st.bal := State.set_bal (Account.clearIfEmpty_balance _)

lemma State.setCode_bal {st : Jaune.State} {a : Address} {cd : ByteArray} :
    (st.setCode a cd).bal = st.bal := State.set_bal (Account.clearIfEmpty_balance _)

/-- CREATE's nonce and access-list preparation leaves the complete world
balance map unchanged. -/
theorem genericCreate_prepared_bal
    (sevm : Sevm) (pre : Devm) (newAddress : Address) :
    (addAccessedAddress
      (((pre.withGasLeft
          (pre.gasLeft - except64th pre.gasLeft)).withReturnData
        []).incrNonce sevm.currentTarget) newAddress).state.bal =
      pre.state.bal := by
  change (pre.state.incrNonce sevm.currentTarget).bal = pre.state.bal
  exact State.incrNonce_bal

/-- CREATE's nonce/access-list preparation preserves persistent storage when
the creator's incremented nonce is nonzero (as enforced by CREATE's overflow check). -/
theorem genericCreate_prepared_getStor
    (sevm : Sevm) (pre : Devm) (newAddress : Address)
    (hnonce : (pre.state.get sevm.currentTarget).nonce + 1 ≠ 0) :
    (addAccessedAddress
        (((pre.withGasLeft
            (pre.gasLeft - except64th pre.gasLeft)).withReturnData
          []).incrNonce sevm.currentTarget) newAddress).state.getStor =
      pre.state.getStor := by
  funext address
  change (pre.state.incrNonce sevm.currentTarget).getStor address =
    pre.state.getStor address
  simp only [State.getStor, State.incrNonce_get_stor]
  simp [Account.isEmpty, hnonce]

/-- CREATE message preparation clears the prospective account storage and
increments its nonce, but leaves the complete world-balance map unchanged. -/
theorem processCreateMessage_msg_bal_eq (msg : Msg) :
    (processCreateMessage.msg msg).benv.state.bal =
      msg.benv.state.bal := by
  change ((msg.benv.state.setStor msg.currentTarget .empty).incrNonce
    msg.currentTarget).bal = msg.benv.state.bal
  rw [State.incrNonce_bal, State.setStor_bal]

/-- State-gas charging changes only machine state. -/
private theorem chargeStateGas_state_eq {amount : Nat} {mid post : Devm}
    (h : chargeStateGas amount mid = .ok post) : post.state = mid.state := by
  unfold chargeStateGas liftMachExecution liftMach Footprint.liftOutcome
    Footprint.toExecution at h
  cases hcore : Mach.chargeStateGas amount mid.mach with
  | error err =>
      rw [hcore] at h
      dsimp only at h
      cases h
  | ok res =>
      rcases res with ⟨_, view⟩
      rw [hcore] at h
      dsimp only at h
      cases h
      exact Devm.setMach_state _ _

/-- CREATE code-deposit gas charging changes only machine state. -/
theorem processCreateMessage.chargeCodeGas_bal_eq
    {rules : ForkRules} {pre post : Devm}
    (h : processCreateMessage.chargeCodeGas rules pre = .ok post) :
    post.state.bal = pre.state.bal := by
  unfold processCreateMessage.chargeCodeGas at h
  dsimp only at h
  split at h
  · split at h
    · split at h
      · cases h
      · rcases Except.bind_eq_ok h with ⟨charged, hcharge, hrest⟩
        split at hrest
        · cases hrest
        · cases hrest
          rw [chargeGas_def] at hcharge
          split at hcharge
          · contradiction
          · cases hcharge
            rfl
    · rcases Except.bind_eq_ok h with ⟨charged, hcharge, hrest⟩
      split at hrest
      · cases hrest
      · cases hrest
        rw [chargeGas_def] at hcharge
        split at hcharge
        · contradiction
        · cases hcharge
          rfl
  · split at h
    · cases h
    · split at h
      · cases h
      · rcases Except.bind_eq_ok h with ⟨mid, hchargeGas, hchargeState⟩
        have hmid : mid.state.bal = pre.state.bal := by
          rw [chargeGas_def] at hchargeGas
          split at hchargeGas
          · contradiction
          · cases hchargeGas
            rfl
        have hpost : post.state.bal = mid.state.bal := by
          rw [chargeStateGas_state_eq hchargeState]
        exact hpost.trans hmid

/-- A clean successful CREATE settlement exposes its successful inner message
and preserves that inner result's complete balance map. -/
theorem ProcessCreateMessage.ok_state_eq_inner_of_no_error
    {msg : Msg} {slot : Xlot} {post : Devm}
    (hprocess : ProcessCreateMessage msg slot (.ok post))
    (herror : post.error.isSome = false) :
    ∃ inner : Devm,
      ProcessMessage (processCreateMessage.msg msg) slot (.ok inner) ∧
      post.state.bal = inner.state.bal := by
  rcases ProcessCreateMessage.iff_processMessage.mp hprocess with
    ⟨result, hinner, hsettle⟩
  cases result with
  | error error =>
      simp [processCreateMessage.settle, Bind.bind, Except.bind] at hsettle
  | ok inner =>
      unfold processCreateMessage.settle at hsettle
      simp only [bind, Except.bind] at hsettle
      by_cases hinnerNone : inner.error.isNone = true
      · rw [ite_eq_left hinnerNone] at hsettle
        cases hcharge :
          processCreateMessage.chargeCodeGas
            msg.benv.stat.rules inner with
        | error error =>
            rw [hcharge] at hsettle
            rcases error with ⟨error, charged⟩
            cases error with
            | halt reason =>
                cases hsg : msg.benv.stat.rules.stateGas with
                | none =>
                    rw [hsg] at hsettle
                    have heq := Except.ok.inj hsettle
                    rw [heq] at herror
                    simp [processCreateMessage.exceptionalHalt,
                      Devm.error, Devm.withStorageWrites, Devm.setWorld, Devm.setMeta] at herror
                | some _ =>
                    rw [hsg] at hsettle
                    have heq := Except.ok.inj hsettle
                    rw [heq] at herror
                    simp [processCreateMessage.exceptionalHaltAmsterdam,
                      Devm.error, Devm.withStorageWrites, Devm.setWorld, Devm.setMeta] at herror
            | revert => cases hsettle
            | crypto reason => cases hsettle
            | internal reason => cases hsettle
        | ok charged =>
            rw [hcharge] at hsettle
            have heq := Except.ok.inj hsettle
            refine ⟨inner, hinner, ?_⟩
            calc
              post.state.bal =
                  (charged.setCode msg.currentTarget
                    ⟨⟨charged.output⟩⟩).state.bal :=
                congrArg (fun d : Devm => d.state.bal) heq
              _ = charged.state.bal := by
                rw [show (charged.setCode msg.currentTarget
                  ⟨⟨charged.output⟩⟩).state =
                    charged.state.setCode msg.currentTarget
                      ⟨⟨charged.output⟩⟩ from rfl,
                  State.setCode_bal]
              _ = inner.state.bal :=
                processCreateMessage.chargeCodeGas_bal_eq hcharge
      · rw [ite_eq_right hinnerNone] at hsettle
        have heq := Except.ok.inj hsettle
        rw [heq] at herror
        simp [Devm.rollback, Devm.setWorld, Devm.error] at herror
        apply False.elim
        apply hinnerNone
        rw [show inner.error = none from herror]
        rfl


/-! ## Over the four-part message call

Settlement commits when `settle` returns a success; a retained frame is a derivation whose raw
result finished (`Except.isOk`). Neither reads `Meta.error`. -/

/-- Whether the child world survives settlement: `settle` returns a success. For a creation this
is strictly stronger than a finished raw result: a failed code deposit is a halt. -/
def Frame.settlementCommits (f : Frame) (raw : Execution) : Bool :=
  match settle f raw with
  | .ok (.success ..) => true
  | _ => false

theorem Frame.settlementCommits_iff {f : Frame} {raw : Execution} :
    Frame.settlementCommits f raw = true ↔
      ∃ output gasLeft stateGas world substate trail,
        settle f raw = .ok (.success output gasLeft stateGas world substate trail) := by
  unfold Frame.settlementCommits
  constructor
  · intro h
    split at h
    · rename_i output gasLeft stateGas world substate trail heq
      exact ⟨output, gasLeft, stateGas, world, substate, trail, heq⟩
    · cases h
  · rintro ⟨output, gasLeft, stateGas, world, substate, trail, h⟩
    rw [h]

/-- Settlement can commit only a raw result that finished. -/
theorem Frame.raw_commits_of_settlementCommits {f : Frame} {raw : Execution}
    (h : Frame.settlementCommits f raw = true) : raw.isOk = true := by
  obtain ⟨_, _, _, _, _, _, hs⟩ := Frame.settlementCommits_iff.mp h
  cases raw with
  | ok _ => rfl
  | error e =>
    rcases e with ⟨e, d⟩
    cases e <;> simp [settle] at hs

/-- A call frame's settlement commits every finished raw result. -/
theorem Frame.settlementCommits_ofCall_of_raw_commits {f : Frame} {raw : Execution}
    (hcall : f.message.kind = .call) (hraw : raw.isOk = true) :
    Frame.settlementCommits f raw = true := by
  cases raw with
  | error _ => cases hraw
  | ok d => simp [Frame.settlementCommits, settle, hcall, Frame.Result.ofSuccess]

/-- The raw result indexed by a derivation. -/
def Exec.outcome {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (_ : Exec pc sevm pre out) : Execution := out

/-- A retained finished frame, with its full derivation. -/
structure Exec.Frame where
  pc : Nat
  sevm : Sevm
  pre : Devm
  out : Execution
  run : Exec pc sevm pre out
  committed : out.isOk = true

/-- The final machine of a retained frame. -/
def Exec.Frame.post (frame : Exec.Frame) : Devm :=
  match frame.out, frame.committed with
  | .ok post, _ => post
  | .error _, h => Bool.noConfusion h

def Exec.Frame.ofRun {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out)
    (committed : out.isOk = true) : Exec.Frame :=
  ⟨pc, sevm, pre, out, run, committed⟩

/-- Descendant frames whose effects survive in the enclosing frame: a child is retained when its
settlement commits, and its own descendants are traversed to arbitrary depth. -/
def Exec.descendantFrames {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Frame :=
  match run with
  | .halt _ => []
  | .cont _ next => Exec.descendantFrames next
  | .doneErr _ _ _ => []
  | .doneOk _ _ _ next => Exec.descendantFrames next
  | .runErr _ _ _ _ => []
  | .runOk (child := frame) (raw := raw) _ _ childRun _ next =>
      let childFrames :=
        if h : Frame.settlementCommits frame raw = true then
          Exec.Frame.ofRun childRun (Frame.raw_commits_of_settlementCommits h) ::
            Exec.descendantFrames childRun
        else []
      childFrames ++ Exec.descendantFrames next
termination_by structural run

/-- A spawn retains its settlement-committing child before the child's descendants and before
the caller's continuation's descendants. -/
@[simp] theorem Exec.descendantFrames_runOk_of_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {child : Jaune.Frame} {pending : Pending}
    {cevm : Evm} {raw out : Execution}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn child pending pc')
    (henter : enter child = .run cevm)
    (childRun : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : resumeCaller sevm.benvStat.rules child pending (settle child raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (hcommit : Frame.settlementCommits child raw = true) :
    Exec.descendantFrames (Exec.runOk hstep henter childRun hr next) =
      Exec.Frame.ofRun childRun (Frame.raw_commits_of_settlementCommits hcommit) ::
        Exec.descendantFrames childRun ++ Exec.descendantFrames next := by
  simp [Exec.descendantFrames, hcommit]

/-- A spawned child whose settlement does not commit contributes no retained frame, even if its
raw result finished. -/
@[simp] theorem Exec.descendantFrames_runOk_of_not_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {child : Jaune.Frame} {pending : Pending}
    {cevm : Evm} {raw out : Execution}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn child pending pc')
    (henter : enter child = .run cevm)
    (childRun : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : resumeCaller sevm.benvStat.rules child pending (settle child raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (hnot : Frame.settlementCommits child raw ≠ true) :
    Exec.descendantFrames (Exec.runOk hstep henter childRun hr next) =
      Exec.descendantFrames next := by
  simp only [Exec.descendantFrames, dite_eq_right hnot, List.nil_append]

/-- In particular, a creation whose raw result finished but whose settlement is a failure (a
failed code deposit) contributes no descendant frame. The raw premise records the
counterexample to pruning by raw outcome alone. -/
theorem Exec.descendantFrames_runOk_create_codeDepositRollback
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {child : Jaune.Frame} {pending : Pending}
    {cevm : Evm} {raw out : Execution} {result : Frame.Result}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn child pending pc')
    (henter : enter child = .run cevm)
    (childRun : Exec cevm.pc cevm.sta cevm.dyna raw)
    (hr : resumeCaller sevm.benvStat.rules child pending (settle child raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (_rawCommits : raw.isOk = true)
    (_hcreate : child.message.kind = .create)
    (hsettled : settle child raw = .ok result)
    (hfailed : result.failed = true) :
    Exec.descendantFrames (Exec.runOk hstep henter childRun hr next) =
      Exec.descendantFrames next := by
  apply Exec.descendantFrames_runOk_of_not_settlementCommits
    hstep henter childRun hr next
  intro hcommit
  obtain ⟨_, _, _, _, _, _, hs⟩ := Frame.settlementCommits_iff.mp hcommit
  rw [hsettled] at hs
  cases hs
  simp [Frame.Result.failed] at hfailed

/-- All and only retained frames of a finished root run. A root that did not finish contributes
none, so an enclosing failure cannot leak a descendant into the accounting fold. -/
def Exec.committedFrames {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Frame :=
  if h : out.isOk = true then
    Exec.Frame.ofRun run h :: Exec.descendantFrames run
  else []

@[simp] theorem Exec.committedFrames_eq_nil_of_not_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (h : out.isOk ≠ true) :
    Exec.committedFrames run = [] := by
  simp [Exec.committedFrames, h]

end Jaune
