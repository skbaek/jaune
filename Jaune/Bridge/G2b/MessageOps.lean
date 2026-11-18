import Jaune.MessageCall.MessageOps
import Jaune.MessageCall.Step
import Jaune.Bridge.G2b.State

/-!
# Bridge: message operations over `Frame.State` against the `Devm` ones (G2b, unit W3-2c)

One square per definition of `Jaune.MessageCall.MessageOps` against its `Devm` counterpart in
`Jaune.MessageCall.Step` and `Jaune.Execution`, under `Frame.State.ofDevm` and
`CallContext.ofSevm`.

The two outcome types differ in two ways, so both are compared through one observation,
`MessageOp.Observation`:

* an old outcome finishes with an `Execution`, a new one with a halt-only outcome; the
  observation embeds the new one through `Except.ofHalt` and maps the old one's states through
  `Frame.State.ofDevm`;
* an old spawn's `Pending` carries the caller's output and stored error, which the new one does
  not; the observation forgets them (`Staging.Pending.ofLegacy`).

The checkpoint of a spawned child is the same `Frame.State` on both sides: `step` already takes it
through `Frame.State.ofDevm`.

Everything here is a bridge artifact: it goes with `Devm` after G2b's tag.
-/

namespace Jaune

open Jaune

/-! ### The observation -/

/-- The legacy continuation without its two residue fields. -/
def Staging.Pending.ofLegacy (p : Jaune.Pending) : Staging.Pending :=
  ⟨p.target, p.newAccountCharged⟩

/-- What both kinds of message-operation outcome are compared through. -/
inductive MessageOp.Observation : Type
  /-- Finished in place, with the state mapped and a halt as an `EvmError`. -/
  | done (r : Except (EvmError × Frame.State) Frame.State)
  /-- A spawn, with the final continuation. -/
  | spawn (child : Frame) (pending : Staging.Pending)

/-- An old outcome, observed. -/
def MessageOp.Outcome.observe : MessageOp.Outcome → MessageOp.Observation
  | .done ex => .done (Frame.State.ofExecution ex)
  | .spawn child pending => .spawn child (.ofLegacy pending)

/-- A new outcome, observed. -/
def Staging.MessageOp.Outcome.observe : Staging.MessageOp.Outcome → MessageOp.Observation
  | .done r => .done (Except.ofHalt r)
  | .spawn child pending => .spawn child pending

/-- The observation forgets nothing of a new outcome. -/
theorem Staging.MessageOp.Outcome.observe_injective {o o' : Staging.MessageOp.Outcome}
    (h : o.observe = o'.observe) : o = o' := by
  cases o with
  | done r =>
    cases o' with
    | done r' =>
      simp only [observe, MessageOp.Observation.done.injEq] at h
      congr 1
      rcases r with ⟨e, s⟩ | s <;> rcases r' with ⟨e', s'⟩ | s' <;>
        simp_all [Except.ofHalt]
    | spawn => simp [observe] at h
  | spawn c p =>
    cases o' with
    | done => simp [observe] at h
    | spawn c' p' => simpa [observe] using h


/-! ### Delegation -/

/-- The state of a delegation result, mapped. -/
abbrev delegationOfDevm : Bool × Address × ByteArray × Nat × Devm →
    Bool × Address × ByteArray × Nat × Frame.State :=
  fun ⟨b, a, c, n, d⟩ => ⟨b, a, c, n, Frame.State.ofDevm d⟩

theorem Staging.accessDelegation_ofDevm (d : Devm) (a : Address) :
    Staging.accessDelegation (Frame.State.ofDevm d) a =
      delegationOfDevm (Jaune.accessDelegation d a) := by
  unfold Staging.accessDelegation Jaune.accessDelegation
  try dsimp only
  rw [show (Frame.State.ofDevm d).code a = d.state.getCode a from rfl]
  split <;> (rename_i h; rw [h]; try rfl)

theorem Staging.GasSchedule.accessDelegation_ofDevm (gas : GasSchedule) (d : Devm) (a : Address) :
    Staging.GasSchedule.accessDelegation gas (Frame.State.ofDevm d) a =
      delegationOfDevm (gas.accessDelegation d a) := by
  unfold Staging.GasSchedule.accessDelegation Jaune.GasSchedule.accessDelegation
  try dsimp only
  rw [show (Frame.State.ofDevm d).code a = d.state.getCode a from rfl]
  split <;> (rename_i h; rw [h]; try rfl)

theorem Staging.GasSchedule.delegationCost_ofDevm (gas : GasSchedule) (d : Devm) (a : Address) :
    Staging.GasSchedule.delegationCost gas (Frame.State.ofDevm d) a = gas.delegationCost d a := rfl

theorem Staging.ForkRules.accessDelegation_ofDevm (rules : ForkRules) (d : Devm) (a : Address) :
    Staging.ForkRules.accessDelegation rules (Frame.State.ofDevm d) a =
      delegationOfDevm (rules.accessDelegation d a) := by
  unfold Staging.ForkRules.accessDelegation Jaune.ForkRules.accessDelegation
  split
  · exact Staging.GasSchedule.accessDelegation_ofDevm _ _ _
  · rfl

theorem Staging.ForkRules.delegationCost_ofDevm (rules : ForkRules) (d : Devm) (a : Address) :
    Staging.ForkRules.delegationCost rules (Frame.State.ofDevm d) a = rules.delegationCost d a :=
  rfl

theorem Staging.completeDelegationAccess_ofDevm (d : Devm) (b : Bool) (a : Address) :
    Staging.completeDelegationAccess (Frame.State.ofDevm d) b a =
      Prod.map id Frame.State.ofDevm (Jaune.completeDelegationAccess d b a) := by
  cases b <;> rfl

/-! ### Simulation lemmas for the bodies

An old body is an `Except (EvmError × Devm) MessageOp.Outcome` and a new one an
`Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome`; they are compared after
`ofExcept`. Each lemma takes the new side's state through an equation `Frame.State.ofDevm d = s`,
so that a body's pure state updates are discharged by the commuting lemmas of
`Jaune.Bridge.G2b.State` (tactic `ofdevm_eq`). -/

namespace MessageOpSim

/-- The observation of an old body. -/
abbrev obsOld (x : Except (EvmError × Devm) MessageOp.Outcome) : MessageOp.Observation :=
  (MessageOp.Outcome.ofExcept x).observe

/-- The observation of a new body. -/
abbrev obsNew (y : Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome) :
    MessageOp.Observation :=
  (Staging.MessageOp.Outcome.ofExcept y).observe

/-- `Frame.State.ofDevm` pushed through the pure updates a message operation makes. -/
macro "ofdevm_eq" : tactic => `(tactic| first
  | rfl
  | (simp only [Frame.State.ofDevm_balReadAccount, Frame.State.ofDevm_withReturnData,
      Frame.State.ofDevm_addAccessedAddress, Frame.State.ofDevm_memExtends,
      Frame.State.ofDevm_incrNonce, Frame.State.ofDevm_withGasLeft,
      Frame.State.ofDevm_restoreChildGas, Frame.State.ofDevm_creditStateGasRefund]
     <;> rfl))

theorem bind_value {α : Type} {x : Except (EvmError × Devm) (α × Devm)}
    {y : Except (ExceptionalHalt × Frame.State) (α × Frame.State)}
    (hxy : Frame.State.ofOutcome x = Except.ofHalt y)
    {f : α × Devm → Except (EvmError × Devm) MessageOp.Outcome}
    {g : α × Frame.State → Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome}
    (k : ∀ a d, obsOld (f (a, d)) = obsNew (g (a, Frame.State.ofDevm d))) :
    obsOld (x >>= f) = obsNew (y >>= g) := by
  rcases x with ⟨e, d⟩ | ⟨a, d⟩ <;> rcases y with ⟨e', s⟩ | ⟨a', s⟩ <;>
    simp only [Frame.State.ofOutcome, Except.mapState, Except.ofHalt, Except.error.injEq,
      Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at hxy
  · obtain ⟨rfl, rfl⟩ := hxy; rfl
  · obtain ⟨rfl, rfl⟩ := hxy; exact k a d

theorem bind_exec {x : Execution} {y : Except (ExceptionalHalt × Frame.State) Frame.State}
    (hxy : Frame.State.ofExecution x = Except.ofHalt y)
    {f : Devm → Except (EvmError × Devm) MessageOp.Outcome}
    {g : Frame.State → Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome}
    (k : ∀ d, obsOld (f d) = obsNew (g (Frame.State.ofDevm d))) :
    obsOld (x >>= f) = obsNew (y >>= g) := by
  rcases x with ⟨e, d⟩ | d <;> rcases y with ⟨e', s⟩ | s <;>
    simp only [Frame.State.ofExecution, Except.mapResultState, Except.ofHalt, Except.error.injEq,
      Except.ok.injEq, Prod.mk.injEq, reduceCtorEq] at hxy
  · obtain ⟨rfl, rfl⟩ := hxy; rfl
  · subst hxy; exact k d

section
variable {d : Devm} {s : Frame.State}

theorem bind_pop (hs : Frame.State.ofDevm d = s)
    {f : U256 × Devm → Except (EvmError × Devm) MessageOp.Outcome}
    {g : U256 × Frame.State → Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome}
    (k : ∀ a d, obsOld (f (a, d)) = obsNew (g (a, Frame.State.ofDevm d))) :
    obsOld (d.pop >>= f) = obsNew (s.pop >>= g) := by
  subst hs; exact bind_value (Frame.State.ofOutcome_pop d) k

theorem bind_popToNat (hs : Frame.State.ofDevm d = s)
    {f : Nat × Devm → Except (EvmError × Devm) MessageOp.Outcome}
    {g : Nat × Frame.State → Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome}
    (k : ∀ a d, obsOld (f (a, d)) = obsNew (g (a, Frame.State.ofDevm d))) :
    obsOld (d.popToNat >>= f) = obsNew (s.popToNat >>= g) := by
  subst hs; exact bind_value (Frame.State.ofOutcome_popToNat d) k

theorem bind_popToAddress (hs : Frame.State.ofDevm d = s)
    {f : Address × Devm → Except (EvmError × Devm) MessageOp.Outcome}
    {g : Address × Frame.State → Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome}
    (k : ∀ a d, obsOld (f (a, d)) = obsNew (g (a, Frame.State.ofDevm d))) :
    obsOld (d.popToAdr >>= f) = obsNew (s.popToAddress >>= g) := by
  subst hs; exact bind_value (Frame.State.ofOutcome_popToAdr d) k

theorem bind_chargeGas (hs : Frame.State.ofDevm d = s) {c : Nat}
    {f : Devm → Except (EvmError × Devm) MessageOp.Outcome}
    {g : Frame.State → Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome}
    (k : ∀ d, obsOld (f d) = obsNew (g (Frame.State.ofDevm d))) :
    obsOld (chargeGas c d >>= f) = obsNew (s.chargeGas c >>= g) := by
  subst hs; exact bind_exec (Frame.State.ofExecution_chargeGas c d) k

theorem bind_push (hs : Frame.State.ofDevm d = s) {x : U256}
    {f : Devm → Except (EvmError × Devm) MessageOp.Outcome}
    {g : Frame.State → Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome}
    (k : ∀ d, obsOld (f d) = obsNew (g (Frame.State.ofDevm d))) :
    obsOld (d.push x >>= f) = obsNew (s.push x >>= g) := by
  subst hs; exact bind_exec (Frame.State.ofExecution_push x d) k

theorem bind_chargeStateGas (hs : Frame.State.ofDevm d = s) {n : Nat}
    {f : Devm → Except (EvmError × Devm) MessageOp.Outcome}
    {g : Frame.State → Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome}
    (k : ∀ d, obsOld (f d) = obsNew (g (Frame.State.ofDevm d))) :
    obsOld (chargeStateGas n d >>= f) = obsNew (s.chargeStateGas n >>= g) := by
  subst hs; exact bind_exec (Frame.State.ofExecution_chargeStateGas n d) k

theorem bind_ok (hs : Frame.State.ofDevm d = s)
    {f : Devm → Except (EvmError × Devm) MessageOp.Outcome}
    {g : Frame.State → Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome}
    (k : ∀ d, obsOld (f d) = obsNew (g (Frame.State.ofDevm d))) :
    obsOld (Except.ok d >>= f) = obsNew (Except.ok s >>= g) := by
  subst hs; exact k d

theorem bind_assert (hs : Frame.State.ofDevm d = s) {p : Prop} {_ : Decidable p}
    {h : ExceptionalHalt}
    {f : Unit → Except (EvmError × Devm) MessageOp.Outcome}
    {g : Unit → Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome}
    (k : p → obsOld (f ()) = obsNew (g ())) :
    obsOld (Except.assert p (.halt h, d) >>= f) = obsNew (Except.assert p (h, s) >>= g) := by
  subst hs
  by_cases hp : p
  · simp only [Except.assert, hp, ↓reduceIte]; exact k hp
  · simp only [Except.assert, hp, ↓reduceIte]; rfl

theorem bind_assertDynamic (hs : Frame.State.ofDevm d = s) {sevm : Sevm}
    {f : Unit → Except (EvmError × Devm) MessageOp.Outcome}
    {g : Unit → Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome}
    (k : sevm.isStatic = false → obsOld (f ()) = obsNew (g ())) :
    obsOld (assertDynamic sevm d >>= f) =
      obsNew (s.assertDynamic (CallContext.ofSevm sevm) >>= g) :=
  bind_assert (p := (!sevm.isStatic) = true) hs (fun hp => k (by simpa using hp))

theorem pure_done (hs : Frame.State.ofDevm d = s) :
    obsOld (pure (.done (.ok d))) = obsNew (pure (.done (.ok s))) := by
  subst hs; rfl

/-- The common finish: push zero and stop. -/
theorem push_done (hs : Frame.State.ofDevm d = s) :
    obsOld (d.push 0 >>= fun d => pure (.done (.ok d))) =
      obsNew (s.push 0 >>= fun s => pure (.done (.ok s))) :=
  bind_push hs fun _ => pure_done rfl

/-- Delegated code access inside a body. -/
theorem accessDelegation_eq (hs : Frame.State.ofDevm d = s) {rules : ForkRules} {a : Address}
    {b : Bool} {x : Address} {c : ByteArray} {n : Nat} {d' : Devm}
    (hr : rules.accessDelegation d a = (b, x, c, n, d')) :
    Staging.ForkRules.accessDelegation rules s a = (b, x, c, n, Frame.State.ofDevm d') := by
  subst hs; rw [Staging.ForkRules.accessDelegation_ofDevm, hr]

/-- The delegation price inside a body. -/
theorem delegationCost_eq (hs : Frame.State.ofDevm d = s) {rules : ForkRules} {a : Address}
    {b : Bool} {x : Address} {n : Nat} (hr : rules.delegationCost d a = (b, x, n)) :
    Staging.ForkRules.delegationCost rules s a = (b, x, n) := by
  subst hs; rw [Staging.ForkRules.delegationCost_ofDevm, hr]

/-- The access half of delegation inside a body. -/
theorem completeDelegationAccess_eq (hs : Frame.State.ofDevm d = s) {b : Bool} {a : Address}
    {c : ByteArray} {d' : Devm} (hr : completeDelegationAccess d b a = (c, d')) :
    Staging.completeDelegationAccess s b a = (c, Frame.State.ofDevm d') := by
  subst hs; rw [Staging.completeDelegationAccess_ofDevm, hr]; rfl

end

theorem sim_ite {c : Prop} {_ : Decidable c} {a b : Except (EvmError × Devm) MessageOp.Outcome}
    {a' b' : Except (ExceptionalHalt × Frame.State) Staging.MessageOp.Outcome}
    (ha : c → obsOld a = obsNew a') (hb : ¬c → obsOld b = obsNew b') :
    obsOld (if c then a else b) = obsNew (if c then a' else b') := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact ha h
  · simp only [h, ↓reduceIte]; exact hb h

theorem observe_ite {c : Prop} {_ : Decidable c} {o1 o2 : MessageOp.Outcome}
    {p1 p2 : Staging.MessageOp.Outcome}
    (h1 : c → o1.observe = p1.observe) (h2 : ¬c → o2.observe = p2.observe) :
    (if c then o1 else o2).observe = (if c then p1 else p2).observe := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact h1 h
  · simp only [h, ↓reduceIte]; exact h2 h

theorem pure_spawn {c c' : Frame} {p : Pending} {p' : Staging.Pending} (hc : c = c')
    (hp : Staging.Pending.ofLegacy p = p') :
    obsOld (pure (.spawn c p)) = obsNew (pure (.spawn c' p')) := by
  subst hc hp; rfl

theorem pure_tail {o : MessageOp.Outcome} {o' : Staging.MessageOp.Outcome}
    (h : o.observe = o'.observe) : obsOld (pure o) = obsNew (pure o') := h

/-- Generalize a delegated code access and replace it on both sides by its components. -/
macro "sim_accessDelegation" : tactic => `(tactic| (
  try dsimp only
  generalize hr : Jaune.ForkRules.accessDelegation _ _ _ = r
  obtain ⟨_, _, _, _, _⟩ := r
  rw [accessDelegation_eq ?_ hr]
  swap; ofdevm_eq
  try dsimp only))

/-- Generalize a delegation price and replace it on both sides by its components. -/
macro "sim_delegationCost" : tactic => `(tactic| (
  try dsimp only
  generalize hr : Jaune.ForkRules.delegationCost _ _ _ = r
  obtain ⟨_, _, _⟩ := r
  rw [delegationCost_eq ?_ hr]
  swap; ofdevm_eq
  try dsimp only))

/-- Generalize the access half of delegation and replace it on both sides. -/
macro "sim_completeDelegationAccess" : tactic => `(tactic| (
  try dsimp only
  generalize hr : Jaune.completeDelegationAccess _ _ _ = r
  obtain ⟨_, _⟩ := r
  rw [completeDelegationAccess_eq ?_ hr]
  swap; ofdevm_eq
  try dsimp only))

end MessageOpSim

open MessageOpSim
/-! ### Child messages -/

theorem Staging.callMessage_ofSevm (sevm : Sevm) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (t s : Bool) (calldata : Bytes) (code : ByteArray)
    (dp : Bool) :
    Staging.callMessage (.ofSevm sevm) gas value caller target codeAddress t s calldata code dp =
      Jaune.callMessage sevm gas value caller target codeAddress t s calldata code dp := rfl

theorem Staging.createMessage_ofSevm (sevm : Sevm) (g : Nat) (v : U256) (a : Address)
    (initcode : Bytes) :
    Staging.createMessage (.ofSevm sevm) g v a initcode =
      Jaune.createMessage sevm g v a initcode := rfl

/-! ### The four tails -/

theorem Staging.genericCall.step_ofDevm (sevm : Sevm) (d : Devm) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (t s : Bool) (ii is oi os : Nat) (code : ByteArray)
    (dp : Bool) :
    (Staging.genericCall.step (.ofSevm sevm) (.ofDevm d) gas value caller target codeAddress t s
        ii is oi os code dp).observe =
      (Jaune.genericCall.step sevm d gas value caller target codeAddress t s ii is oi os code
        dp).observe := by
  unfold Staging.genericCall.step Jaune.genericCall.step
  symm; dsimp only [CallContext.ofSevm]
  by_cases h : sevm.depth = 0 <;> simp only [h, ↓reduceIte]
  · exact push_done (by ofdevm_eq)
  · rfl

theorem Staging.genericCallAmsterdam.step_ofDevm (sevm : Sevm) (state : StateGasRules) (d : Devm)
    (gas reservoir : Nat) (value : U256) (caller target codeAddress : Address) (t s : Bool)
    (ii is oi os : Nat) (code : ByteArray) (dp charged poor : Bool) :
    (Staging.genericCallAmsterdam.step (.ofSevm sevm) state (.ofDevm d) gas reservoir value caller
        target codeAddress t s ii is oi os code dp charged poor).observe =
      (Jaune.genericCallAmsterdam.step sevm state d gas reservoir value caller target codeAddress
        t s ii is oi os code dp charged poor).observe := by
  unfold Staging.genericCallAmsterdam.step Jaune.genericCallAmsterdam.step
  symm; dsimp only
  refine observe_ite (fun _ => ?_) (fun _ => rfl)
  cases charged
  · exact push_done (by ofdevm_eq)
  · exact push_done (by ofdevm_eq)

theorem Staging.genericCreate.step_ofDevm (sevm : Sevm) (d : Devm) (endowment : U256)
    (newAddress : Address) (mi ms : Nat) :
    (Staging.genericCreate.step (.ofSevm sevm) (.ofDevm d) endowment newAddress mi ms).observe =
      (Jaune.genericCreate.step sevm d endowment newAddress mi ms).observe := by
  unfold Staging.genericCreate.step Jaune.genericCreate.step
  symm
  refine bind_assert (by ofdevm_eq) fun _ => ?_
  refine bind_assertDynamic (by ofdevm_eq) fun _ => ?_
  refine sim_ite (fun _ => ?_) (fun _ => ?_)
  · exact push_done (by ofdevm_eq)
  · refine sim_ite (fun _ => ?_) (fun _ => rfl)
    exact push_done (by ofdevm_eq)

theorem Staging.genericCreateAmsterdam.step_ofDevm (sevm : Sevm) (state : StateGasRules)
    (d : Devm) (endowment : U256) (newAddress : Address) (mi ms : Nat) :
    (Staging.genericCreateAmsterdam.step (.ofSevm sevm) state (.ofDevm d) endowment newAddress
        mi ms).observe =
      (Jaune.genericCreateAmsterdam.step sevm state d endowment newAddress mi ms).observe := by
  unfold Staging.genericCreateAmsterdam.step Jaune.genericCreateAmsterdam.step
  symm
  refine sim_ite (fun _ => ?_) (fun _ => ?_)
  · exact push_done (by ofdevm_eq)
  · refine sim_ite (fun _ => ?_) (fun _ => ?_)
    · refine bind_chargeStateGas (by ofdevm_eq) fun d => ?_
      refine sim_ite (fun _ => ?_) (fun _ => ?_)
      · exact push_done (by ofdevm_eq)
      · exact pure_spawn rfl rfl
    · refine bind_ok (by ofdevm_eq) fun d => ?_
      refine sim_ite (fun _ => ?_) (fun _ => ?_)
      · exact push_done (by ofdevm_eq)
      · exact pure_spawn rfl rfl

/-! The tails at any state equal to a mapped one, for use inside the operation bodies. -/

theorem Staging.genericCall.step_ofDevm' {sevm : Sevm} {d : Devm} {s : Frame.State}
    (hs : Frame.State.ofDevm d = s) {gas : Nat} {value : U256}
    {caller target codeAddress : Address} {t st : Bool} {ii is oi os : Nat} {code : ByteArray}
    {dp : Bool} :
    (Jaune.genericCall.step sevm d gas value caller target codeAddress t st ii is oi os code
        dp).observe =
      (Staging.genericCall.step (.ofSevm sevm) s gas value caller target codeAddress t st ii is oi
        os code dp).observe := by
  subst hs; exact (Staging.genericCall.step_ofDevm ..).symm

theorem Staging.genericCallAmsterdam.step_ofDevm' {sevm : Sevm} {state : StateGasRules}
    {d : Devm} {s : Frame.State} (hs : Frame.State.ofDevm d = s) {gas reservoir : Nat}
    {value : U256} {caller target codeAddress : Address} {t st : Bool} {ii is oi os : Nat}
    {code : ByteArray} {dp charged poor : Bool} :
    (Jaune.genericCallAmsterdam.step sevm state d gas reservoir value caller target codeAddress
        t st ii is oi os code dp charged poor).observe =
      (Staging.genericCallAmsterdam.step (.ofSevm sevm) state s gas reservoir value caller target
        codeAddress t st ii is oi os code dp charged poor).observe := by
  subst hs; exact (Staging.genericCallAmsterdam.step_ofDevm ..).symm

theorem Staging.genericCreate.step_ofDevm' {sevm : Sevm} {d : Devm} {s : Frame.State}
    (hs : Frame.State.ofDevm d = s) {endowment : U256} {newAddress : Address} {mi ms : Nat} :
    (Jaune.genericCreate.step sevm d endowment newAddress mi ms).observe =
      (Staging.genericCreate.step (.ofSevm sevm) s endowment newAddress mi ms).observe := by
  subst hs; exact (Staging.genericCreate.step_ofDevm ..).symm

theorem Staging.genericCreateAmsterdam.step_ofDevm' {sevm : Sevm} {state : StateGasRules}
    {d : Devm} {s : Frame.State} (hs : Frame.State.ofDevm d = s) {endowment : U256}
    {newAddress : Address} {mi ms : Nat} :
    (Jaune.genericCreateAmsterdam.step sevm state d endowment newAddress mi ms).observe =
      (Staging.genericCreateAmsterdam.step (.ofSevm sevm) state s endowment newAddress mi
        ms).observe := by
  subst hs; exact (Staging.genericCreateAmsterdam.step_ofDevm ..).symm

/-! ### One square per operation -/

theorem Staging.MessageOp.step_create_ofDevm (sevm : Sevm) (d : Devm) :
    (Staging.MessageOp.step (.ofSevm sevm) (.ofDevm d) .create).observe =
      (Jaune.MessageOp.step sevm d .create).observe := by
  symm
  have hst : (CallContext.ofSevm sevm).block.rules.stateGas = sevm.benvStat.rules.stateGas := rfl
  simp only [Jaune.MessageOp.step, Staging.MessageOp.step, hst]
  rcases sevm.benvStat.rules.stateGas with _ | state
  · refine bind_pop rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_chargeGas rfl fun d => ?_
    exact pure_tail (Staging.genericCreate.step_ofDevm' (by ofdevm_eq))
  · refine bind_assertDynamic rfl fun _ => ?_
    refine bind_pop rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_chargeGas rfl fun d => ?_
    refine bind_assert rfl fun _ => ?_
    exact pure_tail (Staging.genericCreateAmsterdam.step_ofDevm' (by ofdevm_eq))

theorem Staging.MessageOp.step_call_ofDevm (sevm : Sevm) (d : Devm) :
    (Staging.MessageOp.step (.ofSevm sevm) (.ofDevm d) .call).observe =
      (Jaune.MessageOp.step sevm d .call).observe := by
  symm
  have hb : (CallContext.ofSevm sevm).block = sevm.benvStat := rfl
  simp only [Jaune.MessageOp.step, Staging.MessageOp.step, hb]
  rcases sevm.benvStat.rules.stateGas with _ | state
  · rcases sevm.benvStat.rules.access with _ | g
    all_goals
      refine bind_pop rfl fun _ d => ?_
      refine bind_popToAddress rfl fun _ d => ?_
      refine bind_pop rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      sim_accessDelegation
      refine bind_chargeGas rfl fun d => ?_
      refine bind_assert rfl fun _ => ?_
      refine sim_ite (fun _ => ?_) (fun _ => ?_)
      · refine bind_push rfl fun d => ?_
        exact pure_done (by ofdevm_eq)
      · exact pure_tail (Staging.genericCall.step_ofDevm' (by ofdevm_eq))
  · refine bind_pop rfl fun _ d => ?_
    refine bind_popToAddress rfl fun _ d => ?_
    refine bind_pop rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_assert rfl fun _ => ?_
    refine bind_assert rfl fun _ => ?_
    sim_delegationCost
    refine bind_assert (by ofdevm_eq) fun _ => ?_
    sim_completeDelegationAccess
    refine bind_chargeGas rfl fun d => ?_
    refine sim_ite (fun _ => ?_) (fun _ => ?_)
    · refine bind_chargeStateGas rfl fun d => ?_
      refine bind_chargeGas rfl fun d => ?_
      exact pure_tail (Staging.genericCallAmsterdam.step_ofDevm' (by ofdevm_eq))
    · refine bind_ok rfl fun d => ?_
      refine bind_chargeGas rfl fun d => ?_
      exact pure_tail (Staging.genericCallAmsterdam.step_ofDevm' (by ofdevm_eq))

theorem Staging.MessageOp.step_create2_ofDevm (sevm : Sevm) (d : Devm) :
    (Staging.MessageOp.step (.ofSevm sevm) (.ofDevm d) .create2).observe =
      (Jaune.MessageOp.step sevm d .create2).observe := by
  symm
  have hb : (CallContext.ofSevm sevm).block = sevm.benvStat := rfl
  simp only [Jaune.MessageOp.step, Staging.MessageOp.step, hb]
  refine observe_ite (fun _ => ?_) (fun _ => rfl)
  rcases sevm.benvStat.rules.stateGas with _ | state
  · refine bind_pop rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_pop rfl fun _ d => ?_
    refine bind_chargeGas rfl fun d => ?_
    exact pure_tail (Staging.genericCreate.step_ofDevm' (by ofdevm_eq))
  · refine bind_assertDynamic rfl fun _ => ?_
    refine bind_pop rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_pop rfl fun _ d => ?_
    refine bind_chargeGas rfl fun d => ?_
    refine bind_assert rfl fun _ => ?_
    exact pure_tail (Staging.genericCreateAmsterdam.step_ofDevm' (by ofdevm_eq))

theorem Staging.MessageOp.step_callcode_ofDevm (sevm : Sevm) (d : Devm) :
    (Staging.MessageOp.step (.ofSevm sevm) (.ofDevm d) .callcode).observe =
      (Jaune.MessageOp.step sevm d .callcode).observe := by
  symm
  have hb : (CallContext.ofSevm sevm).block = sevm.benvStat := rfl
  simp only [Jaune.MessageOp.step, Staging.MessageOp.step, hb]
  rcases sevm.benvStat.rules.stateGas with _ | state
  · rcases sevm.benvStat.rules.access with _ | g
    all_goals
      refine bind_pop rfl fun _ d => ?_
      refine bind_popToAddress rfl fun _ d => ?_
      refine bind_pop rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      sim_accessDelegation
      refine bind_chargeGas rfl fun d => ?_
      refine sim_ite (fun _ => ?_) (fun _ => ?_)
      · refine bind_push rfl fun d => ?_
        exact pure_done (by ofdevm_eq)
      · exact pure_tail (Staging.genericCall.step_ofDevm' (by ofdevm_eq))
  · refine bind_pop rfl fun _ d => ?_
    refine bind_popToAddress rfl fun _ d => ?_
    refine bind_pop rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_assert rfl fun _ => ?_
    sim_delegationCost
    refine bind_assert (by ofdevm_eq) fun _ => ?_
    sim_completeDelegationAccess
    refine bind_chargeGas rfl fun d => ?_
    exact pure_tail (Staging.genericCallAmsterdam.step_ofDevm' (by ofdevm_eq))

theorem Staging.MessageOp.step_delegatecall_ofDevm (sevm : Sevm) (d : Devm) :
    (Staging.MessageOp.step (.ofSevm sevm) (.ofDevm d) .delegatecall).observe =
      (Jaune.MessageOp.step sevm d .delegatecall).observe := by
  symm
  have hb : (CallContext.ofSevm sevm).block = sevm.benvStat := rfl
  simp only [Jaune.MessageOp.step, Staging.MessageOp.step, hb]
  rcases sevm.benvStat.rules.stateGas with _ | state
  · rcases sevm.benvStat.rules.access with _ | g
    all_goals
      refine bind_pop rfl fun _ d => ?_
      refine bind_popToAddress rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      sim_accessDelegation
      refine bind_chargeGas rfl fun d => ?_
      exact pure_tail (Staging.genericCall.step_ofDevm' (by ofdevm_eq))
  · refine bind_pop rfl fun _ d => ?_
    refine bind_popToAddress rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_assert rfl fun _ => ?_
    sim_delegationCost
    refine bind_assert (by ofdevm_eq) fun _ => ?_
    sim_completeDelegationAccess
    refine bind_chargeGas rfl fun d => ?_
    exact pure_tail (Staging.genericCallAmsterdam.step_ofDevm' (by ofdevm_eq))

theorem Staging.MessageOp.step_staticcall_ofDevm (sevm : Sevm) (d : Devm) :
    (Staging.MessageOp.step (.ofSevm sevm) (.ofDevm d) .staticcall).observe =
      (Jaune.MessageOp.step sevm d .staticcall).observe := by
  symm
  have hb : (CallContext.ofSevm sevm).block = sevm.benvStat := rfl
  simp only [Jaune.MessageOp.step, Staging.MessageOp.step, hb]
  rcases sevm.benvStat.rules.stateGas with _ | state
  · rcases sevm.benvStat.rules.access with _ | g
    all_goals
      refine bind_pop rfl fun _ d => ?_
      refine bind_popToAddress rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      refine bind_popToNat rfl fun _ d => ?_
      sim_accessDelegation
      refine bind_chargeGas rfl fun d => ?_
      exact pure_tail (Staging.genericCall.step_ofDevm' (by ofdevm_eq))
  · refine bind_pop rfl fun _ d => ?_
    refine bind_popToAddress rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_popToNat rfl fun _ d => ?_
    refine bind_assert rfl fun _ => ?_
    sim_delegationCost
    refine bind_assert (by ofdevm_eq) fun _ => ?_
    sim_completeDelegationAccess
    refine bind_chargeGas rfl fun d => ?_
    exact pure_tail (Staging.genericCallAmsterdam.step_ofDevm' (by ofdevm_eq))

/-! ### The step as a whole -/

/-- `MessageOp.step` over the grouped state against the old one, for every operation, every
`Sevm` (so every fork) and every `Devm`. -/
theorem Staging.MessageOp.step_ofDevm (sevm : Sevm) (d : Devm) (x : MessageOp) :
    (Staging.MessageOp.step (.ofSevm sevm) (.ofDevm d) x).observe =
      (Jaune.MessageOp.step sevm d x).observe := by
  cases x
  case create => exact Staging.MessageOp.step_create_ofDevm sevm d
  case create2 => exact Staging.MessageOp.step_create2_ofDevm sevm d
  case call => exact Staging.MessageOp.step_call_ofDevm sevm d
  case callcode => exact Staging.MessageOp.step_callcode_ofDevm sevm d
  case delegatecall => exact Staging.MessageOp.step_delegatecall_ofDevm sevm d
  case staticcall => exact Staging.MessageOp.step_staticcall_ofDevm sevm d

/-- The same square for a running machine, under `Frame.Running.ofEvm`: what `NextOp.step` runs
for a message operation. -/
theorem Staging.MessageOp.step_ofEvm (evm : Evm) (x : MessageOp) :
    (Staging.MessageOp.step (Frame.Running.ofEvm evm).context (Frame.Running.ofEvm evm).state
        x).observe =
      (Jaune.MessageOp.step evm.sta evm.dyna x).observe :=
  Staging.MessageOp.step_ofDevm evm.sta evm.dyna x

end Jaune
