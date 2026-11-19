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

/-- The committed post-machine indexed by a retained frame. -/
def Execution.committedPost (out : Execution)
    (h : Execution.commits out = true) : Devm :=
  match out with
  | .ok post => post
  | .error _ => by simp [Execution.commits] at h

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
  rw [State.setStor, State.writeAccount_keepIfPresent_eq]
  split
  · exact State.setPresent_bal rfl
  · exact State.set_bal rfl

lemma State.incrNonce_bal {st : Jaune.State} {a : Address} :
    (st.incrNonce a).bal = st.bal := by
  rw [State.incrNonce, State.writeAccount_erase_eq_clear]
  exact State.set_bal (Account.clearIfEmpty_balance _)

lemma State.setCode_bal {st : Jaune.State} {a : Address} {cd : ByteArray} :
    (st.setCode a cd).bal = st.bal := by
  rw [State.setCode, State.writeAccount_erase_eq_clear]
  exact State.set_bal (Account.clearIfEmpty_balance _)

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
