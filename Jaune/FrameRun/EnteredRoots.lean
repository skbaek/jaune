import Jaune.FrameRun.Entered
import Jaune.FrameRun.CallsHistory

/-!
# Every top-level frame a block enters is entered (goal `jaune-shape-and-names-v1`, G2b, U102)

The size bounds come from header validation: `validateHeader` runs `checkGasLimit`, so a block's
gas limit is below `gasLimitMaximum = 2 ^ 63`. A transaction's gas limit fits in the block's
(`checkTransactionGasLimits`), its intrinsic gas fits in its gas limit (`validateTransaction`),
and every calldata byte costs intrinsic gas, so its calldata is shorter than the block gas limit.
A system call has `systemTransactionGas` and a word or no calldata. Preparation never touches
the stack, memory or return buffer and never raises the gas measure, so the root it enters is
`Frame.Running.Entered`. With `Frame.Run.calls_ran_entered`, so is every frame a kept history runs.
-/

namespace Jaune

open Jaune

/-! ### Preparation keeps a fresh machine -/

/-- A machine as preparation receives and hands it on: empty stack, memory and return buffer,
and a gas measure below the block gas limit cap. -/
def Frame.State.Fresh (s : Frame.State) : Prop :=
  s.machine.stack = [] ∧ s.machine.memory = .empty ∧ s.machine.returnData = [] ∧
    s.machine.gasMeasure < 2 ^ 63

namespace Frame.State.Fresh

variable {s t : Frame.State}

theorem of_machine_eq (h : s.Fresh) (e : t.machine = s.machine) : t.Fresh := by
  unfold Frame.State.Fresh; rw [e]; exact h

private theorem liftMachine_ok {core : Machine → Except (ExceptionalHalt × Machine) Machine}
    (hc : s.liftMachine core = .ok t) : ∃ m, core s.machine = .ok m ∧ t = s.withMachine m := by
  unfold Frame.State.liftMachine at hc
  cases hm : core s.machine with
  | error e => rw [hm] at hc; cases hc
  | ok m => rw [hm] at hc; cases hc; exact ⟨m, rfl, rfl⟩

private theorem of_le {m : Machine} (h : s.Fresh) (hs : m.stack = s.machine.stack)
    (hm : m.memory = s.machine.memory) (hr : m.returnData = s.machine.returnData)
    (hg : m.gasMeasure ≤ s.machine.gasMeasure) : (s.withMachine m).Fresh :=
  ⟨hs.trans h.1, hm.trans h.2.1, hr.trans h.2.2.1, Nat.lt_of_le_of_lt hg h.2.2.2⟩

theorem chargeGas {c : Nat} (h : s.Fresh) (hc : s.chargeGas c = .ok t) : t.Fresh := by
  obtain ⟨m, hm, rfl⟩ := liftMachine_ok hc
  unfold Machine.chargeGas safeSub at hm
  split at hm
  · cases hm
  · rename_i g hg
    split at hg
    · cases hg; cases hm
      exact of_le h rfl rfl rfl (by simp only [Machine.gasMeasure]; omega)
    · cases hg

theorem chargeStateGas {c : Nat} (h : s.Fresh) (hc : s.chargeStateGas c = .ok t) : t.Fresh := by
  obtain ⟨m, hm, rfl⟩ := liftMachine_ok hc
  unfold Machine.chargeStateGas at hm
  split at hm
  · cases hm; exact of_le h rfl rfl rfl (by simp only [Machine.gasMeasure]; omega)
  · split at hm
    · cases hm; exact of_le h rfl rfl rfl (by simp only [Machine.gasMeasure]; omega)
    · cases hm

theorem commitStateGas (h : s.Fresh) : s.commitStateGas.Fresh :=
  ⟨h.1, h.2.1, h.2.2.1, by
    have := h.2.2.2
    change s.machine.gasLeft + 0 + (s.machine.stateGas.committedSpill + s.machine.stateGas.spilled) < _
    simp only [Machine.gasMeasure] at this; omega⟩

theorem preparationCharge {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (hx : ∀ t, x = .ok t → t.Fresh) (h : TopLevel.preparationCharge x = .ok t) : t.Fresh := by
  unfold TopLevel.preparationCharge at h
  cases x with
  | error e => cases h
  | ok u => cases h; exact hx _ rfl

end Frame.State.Fresh

namespace TopLevel


/-- Every successful value of `x` satisfies `P`. -/
private def OkSatisfies {ε α : Type} (P : α → Prop) (x : Except ε α) : Prop := ∀ a, x = .ok a → P a

private theorem OkSatisfies.ok {ε α : Type} {P : α → Prop} {a : α} (h : P a) : OkSatisfies (ε := ε) P (.ok a) := by
  intro b hb; cases hb; exact h

private theorem OkSatisfies.error {ε α : Type} {P : α → Prop} {e : ε} : OkSatisfies P (.error e : Except ε α) := by
  intro b hb; cases hb

private theorem OkSatisfies.bind {ε α β : Type} {Q : α → Prop} {P : β → Prop} {x : Except ε α}
    {f : α → Except ε β} (hx : OkSatisfies Q x) (hf : ∀ a, Q a → OkSatisfies P (f a)) : OkSatisfies P (x >>= f) := by
  intro b hb
  obtain ⟨a, ha, hb⟩ := Except.bind_eq_ok hb
  exact hf a (hx a ha) b hb

private theorem OkSatisfies.holds {ε α : Type} {P : α → Prop} {x : Except ε α} {a : α} (h : OkSatisfies P x)
    (hx : x = .ok a) : P a := h a hx

attribute [irreducible] OkSatisfies

private theorem OkSatisfies.charge {x : Except (ExceptionalHalt × Frame.State) Frame.State}
    (hx : ∀ u, x = .ok u → u.Fresh) : OkSatisfies (ε := PreparationFailure × Frame.State) Frame.State.Fresh (preparationCharge x) :=
  by unfold OkSatisfies; exact fun _ h => Frame.State.Fresh.preparationCharge hx h

/-! Preparation without state gas. -/

private def InputFresh (input : Input) (a : Input × α) : Prop :=
  a.1.message.context.calldata = input.message.context.calldata ∧
    (input.checkpoint.Fresh → a.1.checkpoint.Fresh)

private theorem authorizationStep_fresh (auth : Authorization) (input : Input) (refund) :
    OkSatisfies (fun a => a.1.message = input.message ∧ (input.checkpoint.Fresh → a.1.checkpoint.Fresh))
      (authorizationStep auth input refund) := by
  unfold authorizationStep
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact OkSatisfies.error
    | (apply OkSatisfies.ok; exact ⟨rfl, id⟩)

private theorem authorizationLoop_fresh :
    ∀ (auths : List Authorization) (input : Input) (refund),
      OkSatisfies (fun a => a.1.message = input.message ∧ (input.checkpoint.Fresh → a.1.checkpoint.Fresh))
        (authorizationLoop auths input refund)
  | [], _, _ => OkSatisfies.ok ⟨rfl, id⟩
  | auth :: rest, input, refund => by
    unfold authorizationLoop
    refine OkSatisfies.bind (authorizationStep_fresh auth input refund) fun ⟨mid, r⟩ ⟨m1, f1⟩ => ?_
    unfold OkSatisfies
    intro b hb
    obtain ⟨m2, f2⟩ := (authorizationLoop_fresh rest mid r).holds hb
    exact ⟨m2.trans m1, f2 ∘ f1⟩

private theorem applyAuthorizations_fresh (input : Input) :
    OkSatisfies (InputFresh input) (applyAuthorizations input) := by
  unfold applyAuthorizations
  split
  · exact OkSatisfies.ok ⟨rfl, id⟩
  · refine OkSatisfies.bind (authorizationLoop_fresh _ input 0) fun x hx => ?_
    obtain ⟨mid, r⟩ := x
    obtain ⟨hm, hf⟩ := hx
    dsimp only at hm hf ⊢
    split
    · exact OkSatisfies.error
    · apply OkSatisfies.ok
      exact ⟨by dsimp only; rw [hm], hf⟩

private theorem resolveCodeDelegation_fresh (input : Input) :
    (resolveCodeDelegation input).message.context.calldata = input.message.context.calldata ∧
      (input.checkpoint.Fresh → (resolveCodeDelegation input).checkpoint.Fresh) := by
  unfold resolveCodeDelegation
  dsimp only
  split
  · exact ⟨rfl, id⟩
  · exact ⟨rfl, fun hf => hf.of_machine_eq rfl⟩

private def PreparedFresh (input : Input) : Prepared → Prop
  | .refused _ => True
  | .frame message checkpoint _ =>
    message.context.calldata = input.message.context.calldata ∧ (input.checkpoint.Fresh → checkpoint.Fresh)

private theorem prepareWithoutStateGas_fresh (input : Input) :
    OkSatisfies (PreparedFresh input) (prepareWithoutStateGas input) := by
  unfold prepareWithoutStateGas
  split
  · split
    · exact OkSatisfies.ok trivial
    · exact OkSatisfies.ok ⟨rfl, id⟩
  · refine OkSatisfies.bind (applyAuthorizations_fresh input) fun ⟨mid, r⟩ ⟨c1, f1⟩ => ?_
    obtain ⟨c2, f2⟩ := resolveCodeDelegation_fresh mid
    exact OkSatisfies.ok ⟨c2.trans c1, f2 ∘ f1⟩

/-! Preparation under state gas. -/

private theorem chargeNewAuthority_fresh {rules a} {s : Frame.State} (hs : s.Fresh) :
    OkSatisfies Frame.State.Fresh (chargeNewAuthority rules a s) := by
  unfold chargeNewAuthority
  split
  · exact OkSatisfies.charge fun _ hu => hs.chargeStateGas hu
  · exact OkSatisfies.ok hs

private theorem chargeAuthorityWrite_fresh {rules a} {s : Frame.State} {paid} (hs : s.Fresh) :
    OkSatisfies (fun x => x.1.Fresh) (chargeAuthorityWrite rules a s paid) := by
  unfold chargeAuthorityWrite
  split
  · exact OkSatisfies.ok hs
  · exact OkSatisfies.bind (OkSatisfies.charge fun _ hu => hs.chargeGas hu) fun _ h => OkSatisfies.ok h

private theorem chargeAuthorizationBase_fresh {rules original a target} {s : Frame.State} {set}
    (hs : s.Fresh) : OkSatisfies (fun x => x.1.Fresh) (chargeAuthorizationBase rules original a target s set) := by
  unfold chargeAuthorizationBase
  split
  · exact OkSatisfies.ok hs
  · dsimp only
    split
    · exact OkSatisfies.bind (OkSatisfies.charge fun _ hu => hs.chargeStateGas hu) fun _ h => OkSatisfies.ok h
    · exact OkSatisfies.bind (OkSatisfies.ok hs) fun _ h => OkSatisfies.ok h

private theorem applyValidatedAuthorization_fresh {rules context a target} {s : Frame.State}
    {paid set} (hs : s.Fresh) :
    OkSatisfies (fun x => x.1.Fresh) (applyValidatedAuthorization rules context a target s paid set) := by
  unfold applyValidatedAuthorization
  refine OkSatisfies.bind (chargeNewAuthority_fresh hs) fun s1 h1 => ?_
  refine OkSatisfies.bind (chargeAuthorityWrite_fresh h1) fun ⟨s2, p2⟩ h2 => ?_
  refine OkSatisfies.bind (chargeAuthorizationBase_fresh h2) fun ⟨s3, d3⟩ h3 => ?_
  exact OkSatisfies.ok (Frame.State.Fresh.of_machine_eq h3 rfl)

private theorem amsterdamAuthorizationStep_fresh {rules context auth} {s : Frame.State}
    {paid set} (hs : s.Fresh) :
    OkSatisfies (fun x => x.1.Fresh) (amsterdamAuthorizationStep rules context auth s paid set) := by
  unfold amsterdamAuthorizationStep
  repeat' (first | (dsimp only) | split)
  all_goals first
    | exact OkSatisfies.error
    | exact OkSatisfies.ok hs
    | exact applyValidatedAuthorization_fresh (hs.of_machine_eq rfl)

private theorem amsterdamAuthorizationLoop_fresh {rules context} :
    ∀ (auths : List Authorization) {s : Frame.State} {paid set}, s.Fresh →
      OkSatisfies (fun x => x.1.Fresh) (amsterdamAuthorizationLoop rules context auths s paid set)
  | [], _, _, _, hs => OkSatisfies.ok hs
  | auth :: rest, s, paid, set, hs => by
    unfold amsterdamAuthorizationLoop
    exact OkSatisfies.bind (amsterdamAuthorizationStep_fresh hs) fun ⟨s1, p1, d1⟩ h1 =>
      amsterdamAuthorizationLoop_fresh rest h1

private theorem applyAmsterdamAuthorizations_fresh {rules} {input : Input} (hs : input.checkpoint.Fresh) :
    OkSatisfies Frame.State.Fresh (applyAmsterdamAuthorizations rules input) := by
  unfold applyAmsterdamAuthorizations
  exact OkSatisfies.bind (amsterdamAuthorizationLoop_fresh _ hs) fun ⟨s1, p1, d1⟩ h1 => OkSatisfies.ok h1

private def MessageFresh (message : Message) (x : Message × Frame.State) : Prop :=
  x.1.context.calldata = message.context.calldata ∧ x.2.Fresh

private theorem resolveAmsterdamCall_fresh {message : Message} {s : Frame.State} (hs : s.Fresh) :
    OkSatisfies (MessageFresh message) (resolveAmsterdamCall message s) := by
  unfold resolveAmsterdamCall
  exact OkSatisfies.bind (OkSatisfies.charge fun _ hu => hs.chargeGas hu) fun s1 h1 => OkSatisfies.ok ⟨rfl, h1.of_machine_eq (by dsimp only; split <;> rfl)⟩

private theorem dispatchAmsterdam_fresh {rules} {message : Message} {s : Frame.State} (hs : s.Fresh) :
    OkSatisfies (MessageFresh message) (dispatchAmsterdam rules message s) := by
  unfold dispatchAmsterdam
  have hs' : (s.recordAccountRead message.context.block.rules message.context.recipient).Fresh :=
    hs.of_machine_eq rfl
  dsimp only
  split
  · split
    · exact OkSatisfies.error
    · split
      · exact OkSatisfies.bind (OkSatisfies.charge fun _ hu => hs'.chargeStateGas hu) fun _ h => OkSatisfies.ok ⟨rfl, h⟩
      · exact OkSatisfies.bind (OkSatisfies.ok hs') fun _ h => OkSatisfies.ok ⟨rfl, h⟩
  · split
    · exact OkSatisfies.bind (OkSatisfies.charge fun _ hu => hs'.chargeStateGas hu) fun _ h => resolveAmsterdamCall_fresh h
    · exact OkSatisfies.bind (OkSatisfies.ok hs') fun _ h => resolveAmsterdamCall_fresh h

private theorem prepareAmsterdamFrame_fresh {rules} {input : Input} (hs : input.checkpoint.Fresh) :
    OkSatisfies (MessageFresh input.message) (prepareAmsterdamFrame rules input) := by
  unfold prepareAmsterdamFrame
  dsimp only
  split
  · refine OkSatisfies.bind (OkSatisfies.ok hs) fun s1 h1 => ?_
    exact dispatchAmsterdam_fresh h1
  · refine OkSatisfies.bind (applyAmsterdamAuthorizations_fresh hs) fun s1 h1 => ?_
    exact dispatchAmsterdam_fresh h1.commitStateGas

/-- Preparation keeps the calldata and a fresh checkpoint. -/
theorem prepare_fresh {input : Input} {message : Message} {checkpoint : Frame.State} {refund : Nat}
    (hs : input.checkpoint.Fresh) (h : prepare input = .ok (.frame message checkpoint refund)) :
    message.context.calldata = input.message.context.calldata ∧ checkpoint.Fresh := by
  unfold prepare at h
  split at h
  · obtain ⟨c, f⟩ := (prepareWithoutStateGas_fresh input).holds h
    exact ⟨c, f hs⟩
  · rename_i rules _
    have hp := prepareAmsterdamFrame_fresh (rules := rules) hs
    split at h
    · cases h
      exact hp.holds (by assumption)
    · cases h
    · cases h

/-- A top-level input as transactions and system calls build it: a fresh checkpoint and calldata
whose length is a word. -/
def Input.Fresh (input : Input) : Prop :=
  input.checkpoint.Fresh ∧ input.message.context.calldata.length < 2 ^ 256

/-- The root a fresh top-level input enters is entered. -/
theorem run_root_entered {input : Input} {result : Run} {root : Root} (hi : input.Fresh)
    (accepted : run input = .ok result) (entry : result.enteredRoot = some root) :
    root.running.Entered := by
  unfold run at accepted
  obtain ⟨prepared, hp, accepted⟩ := Except.bind_eq_ok accepted
  cases prepared with
  | refused reason => cases accepted; cases entry
  | frame message checkpoint refund =>
    obtain ⟨hdata, hfresh⟩ := prepare_fresh hi.1 hp
    simp only [Prepared.toPreparation, Preparation.run] at accepted
    cases htop : Frame.runTopWithRoot ⟨message, checkpoint⟩ with
    | error e => rw [htop] at accepted; cases accepted
    | ok top =>
      rw [htop] at accepted
      cases accepted
      have hroot := Frame.runTopWithRoot_root htop
      cases hr : top.root with
      | none => simp [Run.enteredRoot, hr] at entry
      | some running =>
        simp only [Run.enteredRoot, hr, Option.map_some, Option.some.injEq] at entry
        subst entry
        rw [hr] at hroot
        cases he : enterWith ⟨message, checkpoint⟩ (Frame.mk message checkpoint).checkpoint with
        | done => rw [he] at hroot; cases hroot
        | run r =>
          rw [he] at hroot
          cases hroot
          obtain ⟨hpc, hctx, hm⟩ := Frame.enterWith_run he
          show running.Entered
          exact ⟨hpc, hm ▸ hfresh.1, hm ▸ hfresh.2.1, hm ▸ hfresh.2.2.1,
            by rw [hctx]; exact hdata ▸ hi.2, hm ▸ hfresh.2.2.2⟩

theorem initialCheckpoint_fresh {message : Message} {world accessed keys created destructs}
    (gas : message.gas < 2 ^ 63) :
    (message.initialCheckpoint world accessed keys created destructs).Fresh :=
  ⟨rfl, rfl, rfl, by simpa [Message.initialCheckpoint, Machine.gasMeasure] using gas⟩

theorem systemInput_fresh {block : BlockContext} {state : State} {recipient : Address} {code : ByteArray}
    {calldata : Bytes} (hdata : calldata.length < 2 ^ 256) :
    (systemInput block state recipient code calldata).Fresh := by
  refine ⟨?_, hdata⟩
  unfold systemInput
  dsimp only
  exact initialCheckpoint_fresh (by simp [systemTransactionGas])

end TopLevel

/-! ### Transactions -/

private theorem foldl_add_ge {α : Type} (f : α → Nat) (hf : ∀ x, 1 ≤ f x) :
    ∀ (l : List α) (init : Nat), init + l.length ≤ l.foldl (fun acc x => acc + f x) init
  | [], init => by simp
  | x :: xs, init => by
    have := foldl_add_ge f hf xs (init + f x)
    have := hf x
    simp only [List.foldl_cons, List.length_cons]
    omega

private theorem dataNonZero_pos (f : Fork) : 1 ≤ f.ruleSet.transactionRules.dataNonZero := by
  cases f <;> decide

private theorem data_le_intrinsicGas (block : BlockContext) (tx : Jaune.Transaction) (sender : Address) :
    tx.data.length ≤ (Transaction.intrinsicGas block.rules tx sender).1 := by
  have hd := foldl_add_ge
    (fun x : UInt8 => if x = 0 then Gas.standardTokenCost else block.rules.transactionRules.dataNonZero)
    (fun x => by
      split
      · simp [Gas.standardTokenCost]
      · exact dataNonZero_pos block.fork) tx.data 0
  unfold Transaction.intrinsicGas
  dsimp only
  omega

/-- Validation leaves calldata no longer than the transaction's gas limit. -/
theorem validateTransaction_data_le {block : BlockContext} {tx : Jaune.Transaction} {sender : Address}
    {result : Nat × Nat} (h : validateTransaction block.rules tx sender = .ok result) :
    tx.data.length ≤ tx.gasLimit := by
  have hd := data_le_intrinsicGas block tx sender
  unfold validateTransaction at h
  generalize hi : Transaction.intrinsicGas block.rules tx sender = intrinsic at h hd
  obtain ⟨i, f⟩ := intrinsic
  dsimp only at h hd
  split at h
  · split at h
    · cases h
    · omega
  · simp only [bind, Except.bind] at h
    repeat' split at h
    all_goals first | omega | cases h

/-- Admission keeps the transaction's gas limit within the block's. -/
theorem checkTransactionGasLimits_le {block : BlockContext} {bout : BlockOutput} {tx : Jaune.Transaction}
    {used : Nat} (h : checkTransactionGasLimits block bout tx = .ok used) : tx.gasLimit ≤ block.gasLimit := by
  have key : TopLevel.OkSatisfies (fun _ => tx.gasLimit ≤ block.gasLimit) (checkTransactionGasLimits block bout tx) := by
    unfold checkTransactionGasLimits
    dsimp only
    cases hs : block.rules.stateGas with
    | none =>
      simp only
      split
      · exact TopLevel.OkSatisfies.error
      · split
        · exact TopLevel.OkSatisfies.error
        · apply TopLevel.OkSatisfies.ok; omega
    | some st =>
      simp only
      split
      · exact TopLevel.OkSatisfies.error
      · split
        · exact TopLevel.OkSatisfies.error
        · split
          · exact TopLevel.OkSatisfies.error
          · apply TopLevel.OkSatisfies.ok; omega
  exact key.holds h

theorem Transaction.admit_bounds {block : BlockContext} {state : State} {bout : BlockOutput}
    {tx : Jaune.Transaction} {index : Nat} {admitted : Transaction.Admitted}
    (h : Transaction.admit block state bout tx index = .ok admitted) :
    tx.data.length ≤ tx.gasLimit ∧ tx.gasLimit ≤ block.gasLimit := by
  unfold Transaction.admit at h
  obtain ⟨bout', _, h⟩ := Except.bind_eq_ok h
  obtain ⟨sender, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨i, f⟩, hv, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨a, b, c, d⟩, hc, _⟩ := Except.bind_eq_ok h
  refine ⟨validateTransaction_data_le (Except.mapError_eq_ok_iff.mp hv), ?_⟩
  unfold checkTransaction at hc
  obtain ⟨used, hg, _⟩ := Except.bind_eq_ok hc
  exact checkTransactionGasLimits_le (Except.mapError_eq_ok_iff.mp hg)

private theorem allocateEvmGas_le (rules : ForkRules) (txGas intrinsic : Nat) :
    (allocateEvmGas rules txGas intrinsic).executionGas ≤ txGas := by
  unfold allocateEvmGas
  split <;> dsimp only <;> omega

theorem Transaction.prepare_fresh {block : BlockContext} {state : State} {admitted : Transaction.Admitted}
    {tx : Jaune.Transaction} {prepared : Transaction.Prepared}
    (h : Transaction.prepare block state admitted tx = .ok prepared)
    (hdata : tx.data.length < 2 ^ 256) (hgas : tx.gasLimit < 2 ^ 63) : prepared.input.Fresh := by
  unfold Transaction.prepare at h
  obtain ⟨st, _, h⟩ := Except.bind_eq_ok h
  cases h
  refine ⟨TopLevel.initialCheckpoint_fresh (Nat.lt_of_le_of_lt (allocateEvmGas_le _ _ _) hgas), ?_⟩
  dsimp only
  split <;> simp_all

/-- The root of every transaction a block with a valid gas limit runs is entered. -/
theorem Transaction.run_root_entered {block : BlockContext} {state : State} {bout : BlockOutput}
    {tx : Jaune.Transaction} {index : Nat} {run : TransactionRun} {output : BlockOutput} {root : Root}
    (gasLimit : block.gasLimit < 2 ^ 63) (accepted : Transaction.run block state bout tx index = .ok (run, output))
    (entry : run.message.enteredRoot = some root) : root.running.Entered := by
  have roots := Transaction.run_messageRoots accepted
  unfold Transaction.run at accepted
  obtain ⟨admitted, ha, accepted⟩ := Except.bind_eq_ok accepted
  obtain ⟨prepared, hp, accepted⟩ := Except.bind_eq_ok accepted
  obtain ⟨message, _, settled⟩ := Except.bind_eq_ok accepted
  have hentry : run.entry = prepared.input := by
    unfold Transaction.settleRun at settled
    obtain ⟨_, _, settled⟩ := Except.bind_eq_ok settled
    cases settled
    rfl
  obtain ⟨hd, hg⟩ := Transaction.admit_bounds ha
  have hfresh := Transaction.prepare_fresh hp (by omega) (by omega)
  rw [← hentry] at hfresh
  exact TopLevel.run_root_entered hfresh roots.1 entry

/-- The root of a system call with a word-length calldata is entered. -/
theorem processSystemRun_root_entered {block : BlockContext} {state : State} {target : Address}
    {code : ByteArray} {data : Bytes} {run : SystemRun} {root : Root} (hdata : data.length < 2 ^ 256)
    (accepted : processSystemRun block state target code data = .ok run)
    (entry : run.message.enteredRoot = some root) : root.running.Entered := by
  unfold processSystemRun at accepted
  obtain ⟨message, hm, accepted⟩ := Except.bind_eq_ok accepted
  obtain ⟨_, _, accepted⟩ := Except.bind_eq_ok accepted
  cases accepted
  exact TopLevel.run_root_entered (TopLevel.systemInput_fresh hdata) hm entry

/-! ### Bodies and blocks -/

/-- A system call operation's calldata, when it has one, is a word long. -/
private def ShortData : BodyOperation → Prop
  | .systemCall _ data _ => ∀ d, data = .ok d → d.length < 2 ^ 256
  | _ => True

private theorem stepRun_root_entered {block : BlockContext} {p : Jaune.Body.Prefix} {op : BodyOperation}
    {record : BodyOperationRun} {next : Jaune.Body.Prefix} {root : Root} (gasLimit : block.gasLimit < 2 ^ 63)
    (hop : ShortData op) (h : Body.stepRun block p op = .ok (record, next))
    (entry : record.enteredRoot = some root) : root.running.Entered := by
  cases op with
  | systemCall address data index =>
    simp only [Body.stepRun, Body.stepWith] at h
    obtain ⟨d, hd, h⟩ := Except.bind_eq_ok h
    obtain ⟨message, hm, h⟩ := Except.bind_eq_ok h
    cases h
    exact processSystemRun_root_entered (hop d hd) (Except.mapError_eq_ok_iff.mp hm) entry
  | transaction tx index =>
    simp only [Body.stepRun, Body.stepWith] at h
    obtain ⟨⟨run, bout⟩, hr, h⟩ := Except.bind_eq_ok h
    cases h
    exact Transaction.run_root_entered gasLimit hr entry
  | requestCall type address index =>
    simp only [Body.stepRun, Body.stepWith] at h
    obtain ⟨message, hm, h⟩ := Except.bind_eq_ok h
    cases h
    unfold processCheckedSystemRun at hm
    dsimp only at hm
    split at hm
    · simp [bind, Except.bind] at hm
    · obtain ⟨run, hr, hm⟩ := Except.bind_eq_ok hm
      have hrun : run = message := by split at hm <;> cases hm; rfl
      subst hrun
      exact processSystemRun_root_entered (by simp) (Except.mapError_eq_ok_iff.mp hr) entry
  | withdrawals ws index =>
    simp only [Body.stepRun, Body.stepWith] at h; cases h; cases entry
  | depositRequests =>
    simp only [Body.stepRun, Body.stepWith] at h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    cases h; cases entry
  | rewards coinbase reward credits =>
    simp only [Body.stepRun, Body.stepWith] at h; cases h; cases entry
  | buildAccessList =>
    simp only [Body.stepRun, Body.stepWith] at h; cases h; cases entry
  | checkAccessListLimit =>
    simp only [Body.stepRun, Body.stepWith] at h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    cases h; cases entry

private theorem body_run_root_entered {block : BlockContext} (gasLimit : block.gasLimit < 2 ^ 63) :
    ∀ (ops : List BodyOperation) {p : Jaune.Body.Prefix} {records : List BodyOperationRun} {final : Jaune.Body.Prefix},
      (∀ op ∈ ops, ShortData op) → Body.run block p ops = .ok (records, final) →
      ∀ record ∈ records, ∀ root, record.enteredRoot = some root → root.running.Entered
  | [], _, _, _, _, h => by cases h; simp
  | op :: ops, p, records, final, hops, h => by
    simp only [Body.run] at h
    obtain ⟨⟨record, next⟩, hstep, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨rest, final'⟩, hrest, h⟩ := Except.bind_eq_ok h
    cases h
    intro r hr root entry
    rcases List.mem_cons.mp hr with rfl | hr
    · exact stepRun_root_entered gasLimit (hops op (List.mem_cons_self ..)) hstep entry
    · exact body_run_root_entered gasLimit ops (fun o ho => hops o (List.mem_cons_of_mem _ ho)) hrest r hr root entry

private theorem shortData_of_not_systemCall {op : BodyOperation}
    (h : ∀ a d i, op ≠ .systemCall a d i) : ShortData op := by
  cases op with
  | systemCall a d i => exact absurd rfl (h a d i)
  | _ => trivial

private theorem operations_shortData (block : BlockContext) (txs : List Jaune.Transaction) (ommers : List Header)
    (wds : List Withdrawal) : ∀ op ∈ Body.operations block txs ommers wds, ShortData op := by
  intro op hop
  simp only [Body.operations, Body.postExecutionOperations, List.mem_append] at hop
  rcases hop with (hop | hop) | hop
  · simp only [Body.preExecutionOperations, List.mem_append] at hop
    rcases hop with hop | hop
    · split at hop
      · simp only [List.mem_singleton] at hop
        subst hop
        intro d hd
        cases hd
        simp [U256.length_toBytes]
      · simp at hop
    · split at hop
      · simp only [List.mem_singleton] at hop
        subst hop
        intro d hd
        cases hl : block.blockHashes.getLast? with
        | none => simp [hl, Option.toExcept, Except.map] at hd
        | some x =>
          simp only [hl, Option.toExcept, Except.map, Except.ok.injEq] at hd
          subst hd
          simp [U256.length_toBytes]
      · simp at hop
  · apply shortData_of_not_systemCall
    simp only [Jaune.Body.transactionOperations, List.mem_map] at hop
    obtain ⟨⟨i, tx⟩, _, rfl⟩ := hop
    intro a d j h
    cases h
  · apply shortData_of_not_systemCall
    intro a d j h
    subst h
    simp only [Body.withdrawalOperations, Body.requestOperations, Body.finalOperations, List.mem_append] at hop
    rcases hop with hop | hop | hop
    · split at hop <;> simp at hop
    · split at hop <;> simp at hop
    · split at hop <;> simp at hop

/-- Every top-level frame the run of a block with a valid gas limit enters is entered. -/
theorem BlockRun.roots_entered {fork : Fork} {parent : BlockChain} {block : Block} {run : BlockRun}
    (executed : BlockRun.run fork parent block = .ok run) (gasLimit : block.header.gasLimit < 2 ^ 63) :
    ∀ root ∈ run.roots, root.running.Entered := by
  unfold BlockRun.run at executed
  obtain ⟨decoded, _, executed⟩ := Except.bind_eq_ok executed
  obtain ⟨⟨ops, final⟩, hr, executed⟩ := Except.bind_eq_ok executed
  cases executed
  intro root hroot
  obtain ⟨record, hrec, entry⟩ := List.mem_filterMap.mp hroot
  exact body_run_root_entered (block := initBlockContext fork parent block.header) gasLimit _
    (operations_shortData _ _ _ _) hr record hrec root entry

/-! ### Header validation and kept histories -/

/-- `checkGasLimit` keeps a block's gas limit below `gasLimitMaximum`. -/
theorem checkGasLimit_lt {gasLimit parentGasLimit : Nat}
    (h : checkGasLimit gasLimit parentGasLimit = .ok ()) : gasLimit < gasLimitMaximum := by
  unfold checkGasLimit at h
  by_contra hc
  have hge : gasLimit ≥ gasLimitMaximum := by omega
  simp [hge, bind, Except.bind] at h

/-- Header validation keeps the header's gas limit below `gasLimitMaximum = 2 ^ 63`. Every arm of
`expectedBaseFee`, and the first fee-bearing header's own check, runs `checkGasLimit`. -/
theorem validateHeader_gasLimit_lt {rules : ForkRules} {chain : BlockChain} {header : Header}
    (h : validateHeader rules chain header = .ok ()) : header.gasLimit < gasLimitMaximum := by
  cases htip : chain.blocks.getLast? with
  | none =>
    unfold validateHeader at h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    obtain ⟨parent, hpar, h⟩ := Except.bind_eq_ok h
    rw [htip] at hpar
    simp [Option.toExcept] at hpar
  | some tip =>
    have hph := (validateHeader_links htip h).1
    unfold validateHeader at h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    obtain ⟨parent, hpar, h⟩ := Except.bind_eq_ok h
    rw [htip] at hpar
    simp only [Option.toExcept, Except.ok.injEq] at hpar
    subst hpar
    dsimp only at h
    rw [ite_eq_right (by simpa only [Header.hash, not_not] using hph)] at h
    obtain ⟨u, hfirst, h⟩ := Except.bind_eq_ok h
    obtain ⟨bf, hbf, _⟩ := Except.bind_eq_ok h
    have hf := Except.mapError_eq_ok_iff.mp hfirst
    have hb := Except.mapError_eq_ok_iff.mp hbf
    unfold expectedBaseFee at hb
    split at hb
    · obtain ⟨_, hc, _⟩ := Except.bind_eq_ok hb
      exact checkGasLimit_lt hc
    · rename_i hh hp
      simp only [checkFirstFeeGasLimit, hh, hp, Option.isSome_some, Option.isNone_none, Bool.and_self,
        ↓reduceIte] at hf
      exact checkGasLimit_lt hf
    · rename_i fee _ _
      generalize hcb : calculateBaseFeePerGas header.gasLimit tip.header.gasLimit tip.header.gasUsed fee = x at hb
      cases x with
      | error e => cases hb
      | ok v =>
        unfold calculateBaseFeePerGas at hcb
        obtain ⟨_, hc, _⟩ := Except.bind_eq_ok hcb
        exact checkGasLimit_lt hc

theorem BlockRun.run_eq {fork : Fork} {parent : BlockChain} {block : Block} {run : BlockRun}
    (executed : BlockRun.run fork parent block = .ok run) :
    run.fork = fork ∧ run.parent = parent ∧ run.block = block := by
  unfold BlockRun.run at executed
  obtain ⟨_, _, executed⟩ := Except.bind_eq_ok executed
  obtain ⟨_, _, executed⟩ := Except.bind_eq_ok executed
  cases executed
  exact ⟨rfl, rfl, rfl⟩

/-- A configured step validated its header, so its gas limit is below `2 ^ 63`. -/
theorem KeptStep.gasLimit_lt {cfg : ChainConfig} {fork : Fork} {parent : BlockChain} {block : Block}
    {post : BlockChain} (checked : KeptStep cfg fork parent block post) :
    block.header.gasLimit < 2 ^ 63 := by
  have h := checked.accepted
  unfold stateTransitionCoreTyped at h
  obtain ⟨_, hv, _⟩ := Except.bind_eq_ok h
  exact validateHeader_gasLimit_lt (Except.mapError_eq_ok_iff.mp hv)

/-- The configured transition witnesses a kept step: chain identity, fork lookup and the typed
transition with its scheduled ommer checks. -/
theorem KeptStep.of_transition {cfg : ChainConfig} {parent post : BlockChain} {block : Block}
    (accepted : stateTransitionUsing cfg parent block = .ok post) :
    ∃ fork, KeptStep cfg fork parent block post := by
  obtain ⟨fork, hf, hs⟩ := stateTransitionUsing_run accepted
  refine ⟨fork, ?_, hf, stateTransitionScheduledTyped_eq_ok_iff.mp hs⟩
  unfold stateTransitionUsing at accepted
  obtain ⟨u, chain, _⟩ := Except.bind_eq_ok accepted
  cases u
  exact Except.mapError_eq_ok_iff.mp chain

/-- Every top-level frame a kept history enters is entered. -/
theorem KeptHistory.roots_entered {cfg : ChainConfig} {start post : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory cfg start blocks post) :
    ∀ block ∈ blocks, ∀ root ∈ block.run.roots, root.running.Entered := by
  induction history with
  | refl => simp
  | @step blocks last prior checked ih =>
    intro block hb
    rcases List.mem_append.mp hb with hb | hb
    · exact ih block hb
    · rw [List.mem_singleton.mp hb]
      exact BlockRun.roots_entered last.executed checked.gasLimit_lt

/-- Every frame of every run a kept history makes starts entered. -/
theorem KeptHistory.frames_entered {cfg : ChainConfig} {start post : BlockChain} {blocks : List KeptBlock}
    (history : KeptHistory cfg start blocks post) {block : KeptBlock} (hb : block ∈ blocks)
    {root : Root} (hr : root ∈ block.run.roots) {n : Frame.Run.Node} (hn : n ∈ root.run.frames) :
    n.start.Entered :=
  Frame.Run.frames_entered root.run (history.roots_entered block hb root hr) hn

/-- Combined, at history level: every call a kept history makes that ran started its child
entered. -/
theorem KeptHistory.calls_ran_entered {cfg : ChainConfig} {start post : BlockChain}
    {blocks : List KeptBlock} (history : KeptHistory cfg start blocks post) {c : Frame.Run.Call}
    (hc : c ∈ KeptHistory.calls blocks) {n : Frame.Run.Node} (hran : c.ran = some n) : n.start.Entered := by
  obtain ⟨block, hb, root, hr, hc⟩ := KeptHistory.mem_calls.mp hc
  exact Frame.Run.calls_ran_entered root.run (history.roots_entered block hb root hr) hc hran

end Jaune
