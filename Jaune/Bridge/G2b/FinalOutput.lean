import Jaune.MessageCall.Step
import Jaune.Bridge.G2b.Control

/-!
# Bridge: the `Devm` interpreter keeps a running frame's output (G2b, unit W3-3)

The cleanliness premise of the halt and precompile squares (W3-2b+d) is that the running
machine's `Devm` carries no output. This module proves, by one walk over every instruction of
the old interpreter (every fork), that the old step keeps it so (`OutputWalk.Evm.step_post`):

* a step that goes on leaves the output as it was;
* a spawn passes the output through in its `Pending` (`legacyOutput`) and saves the caller as
  `Frame.State.ofDevm`, whose RIPEMD-160 flag is down.

Only a halt writes an output, and a frame stops at its halt. `Jaune.Bridge.G2b.FinalDriver`
carries this through the driver: every frame the old driver runs from a clean start is clean.

The walk is mechanical (`out_walk`): a success-channel postcondition `Post` pushed through the
binds, with one lemma per lifted primitive (`liftMach_post`, `liftMachExecution_post`) and the
read-set updates (`balReadAccount`, `balReadStorage`), whose output is the input's in both
branches. Everything here goes with `Devm` after G2b's tag.
-/

namespace Jaune

namespace OutputWalk

/-- A postcondition on the success channel; the error channel is unconstrained. -/
def Post {α : Type} (P : α → Prop) : Except (EvmError × Devm) α → Prop
  | .ok a => P a
  | .error _ => True

theorem Post.bind {α β : Type} {P : α → Prop} {Q : β → Prop} {x : Except (EvmError × Devm) α}
    {f : α → Except (EvmError × Devm) β} (hx : Post P x) (hf : ∀ a, P a → Post Q (f a)) :
    Post Q (x >>= f) := by
  cases x with
  | error e => trivial
  | ok a => exact hf a hx

theorem Post.error {α : Type} {P : α → Prop} (e : EvmError × Devm) :
    Post P (Except.error e : Except (EvmError × Devm) α) := trivial

theorem Post.true {α : Type} (x : Except (EvmError × Devm) α) : Post (fun _ => True) x := by
  cases x <;> trivial

theorem liftMach_post {α : Type} {o : Bytes} (core : Mach → Footprint.Outcome Mach α) {d : Devm}
    (h : d.output = o) : Post (fun a : α × Devm => a.2.output = o) (liftMach core d) := by
  unfold liftMach Footprint.liftOutcome
  rcases core d.mach with ⟨e, m⟩ | ⟨a, m⟩
  · trivial
  · exact h

theorem liftMachExecution_post {o : Bytes} (core : Mach → Footprint.Outcome Mach Unit) {d : Devm}
    (h : d.output = o) : Post (fun d' : Devm => d'.output = o) (liftMachExecution core d) := by
  unfold liftMachExecution liftMach Footprint.liftOutcome Footprint.toExecution
  rcases core d.mach with ⟨e, m⟩ | ⟨a, m⟩
  · trivial
  · exact h

theorem Devm.balReadStorage_output (rules : ForkRules) (a : Address) (k : U256) (d : Devm) :
    (d.balReadStorage rules a k).output = d.output := by
  unfold Devm.balReadStorage; split <;> rfl

theorem Post.ite {α : Type} {P : α → Prop} {c : Prop} [Decidable c]
    {a b : Except (EvmError × Devm) α} (ha : c → Post P a) (hb : ¬c → Post P b) :
    Post P (if c then a else b) := by
  by_cases h : c
  · simp only [h, ↓reduceIte]; exact ha h
  · simp only [h, ↓reduceIte]; exact hb h

theorem Post.mapRev {α β : Type} {P : α → Prop} {Q : β → Prop} {x : Except (EvmError × Devm) α}
    {f : α → β} (hx : Post P x) (hf : ∀ a, P a → Q (f a)) : Post Q (x <&> f) := by
  cases x with
  | error e => trivial
  | ok a => exact hf a hx

theorem balance_post (rules : ForkRules) {d : Devm} {o : Bytes} (h : d.output = o) :
    Post (fun d' : Devm => d'.output = o)
      (liftMachMetaWorldExecution (PlainOp.balanceCore rules) d) := by
  unfold liftMachMetaWorldExecution liftMachMetaExecution liftMachMeta Footprint.liftOutcome
    Footprint.toExecution PlainOp.balanceCore
  dsimp only
  rcases d.mach.pop with ⟨e, m⟩ | ⟨x, m⟩
  · trivial
  · dsimp only
    rcases Mach.chargeGas _ m with ⟨e, m'⟩ | ⟨u, m'⟩
    · trivial
    · dsimp only
      rcases Mach.push _ m' with ⟨e, m''⟩ | ⟨u, m''⟩
      · trivial
      · dsimp only
        repeat' split
        all_goals exact h

/-- What a message operation owes the output invariant: a finished operation keeps the output;
a spawn passes it through in its `Pending` and saves the caller grouped, flag down. -/
def OutcomePost (o : Bytes) : MessageOp.Outcome → Prop
  | .done ex => Post (fun d' : Devm => d'.output = o) ex
  | .spawn child p => p.legacyOutput = o ∧ child.checkpoint.trail.touchedRIPEMD160 = false

open Lean Elab Tactic Meta in
/-- Close `X.output = o` (or a success-channel `Post` on `Except.ok X`, which reduces to it) from
a hypothesis `Y.output = o` where `X.output` unfolds to `Y.output`. Fails fast on any other goal. -/
elab "out_close" : tactic => withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  if tgt.isAppOf ``Post then
    unless tgt.appArg!.isAppOf ``Except.ok do throwError "out_close: not a leaf"
  else unless tgt.isAppOf ``Eq || tgt.isAppOf ``And do throwError "out_close: not a leaf"
  for decl in (← getLCtx) do
    if decl.isImplementationDetail then continue
    let ty ← instantiateMVars decl.type
    unless ty.isAppOf ``Eq && ty.appArg!.isFVar do continue
    let h ← Term.exprToSyntax (mkFVar decl.fvarId)
    let s ← saveState
    let ok ← (do
        evalTactic (← `(tactic| exact Eq.trans rfl $h))
        pure true) <|> (do
        s.restore
        evalTactic (← `(tactic| exact ⟨Eq.trans rfl $h, rfl⟩))
        pure true) <|> (do s.restore; pure false)
    if ok then return
  throwError "out_close: no hypothesis closes the goal"

open Lean Elab Tactic Meta in
/-- Close a success-channel `Post` on an error. -/
elab "out_error" : tactic => withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  unless tgt.isAppOf ``Post && tgt.appArg!.isAppOf ``Except.error do throwError "out_error"
  evalTactic (← `(tactic| exact Post.error _))

/-- `out_close`, after forgetting the read-set updates that cannot change the output. -/
macro "out_close'" : tactic => `(tactic| first
  | out_close
  | (((try simp only [Post, OutcomePost, Jaune.Devm.balReadAccount, Jaune.Devm.balReadStorage]); repeat' split) <;>
      out_close))

theorem ok_bind' {α β : Type} (a : α) (f : α → Except (EvmError × Devm) β) :
    (Except.ok a >>= f) = f a := rfl

/-- A primitive's postcondition. -/
macro "out_prim" : tactic => `(tactic| first
  | exact liftMach_post _ (by out_close')
  | exact liftMachExecution_post _ (by out_close')
  | exact Post.true _)

/-- Walk a computation, carrying the output. -/
macro "out_walk" : tactic => `(tactic| repeat' (first
  | out_close'
  | out_error
  | rw [ok_bind']
  | (simp only [pure, Except.pure])
  | (simp only [Devm.withholdCreateGas, Devm.drainStateGasReservoir, Devm.memRead,
      completeDelegationAccess])
  | exact liftMachExecution_post _ (by out_close')
  | (refine Post.bind (by out_prim) ?_; intro ⟨_, _⟩ _)
  | (refine Post.bind (by out_prim) ?_; intro _ _)
  | (apply Post.ite <;> intro _)
  | split
  | (dsimp only)))

end OutputWalk

set_option maxHeartbeats 4000000 in
open OutputWalk in
theorem PlainOp.runCore_post (pc : Nat) (d : Devm) (sevm : Sevm) (op : PlainOp) {o : Bytes}
    (h : d.output = o) : Post (fun d' : Devm => d'.output = o) (PlainOp.runCore pc d sevm op) := by
  cases op
  case balance => exact balance_post _ h
  case pop =>
    simp only [PlainOp.runCore]
    exact Post.bind (Post.mapRev (liftMach_post _ h) (fun a ha => ha))
      (fun a ha => liftMachExecution_post _ ha)
  all_goals simp only [PlainOp.runCore]
  all_goals out_walk

namespace OutputWalk

theorem OutcomePost.ofExcept {o : Bytes} {x : Except (EvmError × Devm) MessageOp.Outcome}
    (h : Post (OutcomePost o) x) : OutcomePost o (MessageOp.Outcome.ofExcept x) := by
  cases x with
  | error e => trivial
  | ok a => exact h

theorem genericCall.step_post (sevm : Sevm) {d : Devm} {o : Bytes} (h : d.output = o)
    (gas : Nat) (value : U256) (caller target codeAddress : Address)
    (shouldTransferValue isStaticcall : Bool) (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles : Bool) :
    OutcomePost o (genericCall.step sevm d gas value caller target codeAddress shouldTransferValue
      isStaticcall inputIndex inputSize outputIndex outputSize code disablePrecompiles) := by
  unfold genericCall.step
  dsimp only
  split
  · refine OutcomePost.ofExcept ?_
    out_walk
  · exact ⟨h, rfl⟩

theorem genericCallAmsterdam.step_post (sevm : Sevm) (state : StateGasRules) {d : Devm} {o : Bytes}
    (h : d.output = o) (gas reservoir : Nat) (value : U256) (caller target codeAddress : Address)
    (shouldTransferValue isStaticcall : Bool) (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles newAccountCharged insufficientBalance : Bool) :
    OutcomePost o (genericCallAmsterdam.step sevm state d gas reservoir value caller target
      codeAddress shouldTransferValue isStaticcall inputIndex inputSize outputIndex outputSize code
      disablePrecompiles newAccountCharged insufficientBalance) := by
  unfold genericCallAmsterdam.step
  dsimp only
  split
  · refine OutcomePost.ofExcept ?_
    out_walk
  · exact ⟨h, rfl⟩

theorem genericCreate.step_post (sevm : Sevm) {d : Devm} {o : Bytes} (h : d.output = o)
    (endowment : U256) (newAddress : Address) (memoryIndex memorySize : Nat) :
    OutcomePost o (genericCreate.step sevm d endowment newAddress memoryIndex memorySize) := by
  unfold genericCreate.step
  refine OutcomePost.ofExcept ?_
  out_walk

theorem genericCreateAmsterdam.step_post (sevm : Sevm) (state : StateGasRules) {d : Devm}
    {o : Bytes} (h : d.output = o) (endowment : U256) (newAddress : Address)
    (memoryIndex memorySize : Nat) :
    OutcomePost o (genericCreateAmsterdam.step sevm state d endowment newAddress memoryIndex
      memorySize) := by
  unfold genericCreateAmsterdam.step
  refine OutcomePost.ofExcept ?_
  out_walk

theorem accessDelegation_cases (rules : ForkRules) (d : Devm) (a : Address) :
    ∃ b ad c n d', rules.accessDelegation d a = (b, ad, c, n, d') ∧ d'.output = d.output := by
  unfold ForkRules.accessDelegation GasSchedule.accessDelegation
  split
  · dsimp only
    split
    · exact ⟨_, _, _, _, _, rfl, rfl⟩
    · exact ⟨_, _, _, _, _, rfl, rfl⟩
  · exact ⟨_, _, _, _, _, rfl, rfl⟩

open Lean Elab Tactic Meta in
/-- Replace a delegation access in the goal by its explicit tuple, recording the output. -/
elab "out_deleg" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let some e := tgt.find? (fun e => e.isAppOfArity ``ForkRules.accessDelegation 3)
    | throwError "out_deleg: no delegation access"
  let t ← Term.exprToSyntax e
  let #[re, de, ae] := e.getAppArgs | throwError "out_deleg: unexpected arity"
  let r ← Term.exprToSyntax re
  let dv ← Term.exprToSyntax de
  let a ← Term.exprToSyntax ae
  evalTactic (← `(tactic|
    (obtain ⟨_, _, _, _, _, hx, hout⟩ := accessDelegation_cases $r $dv $a
     have := Eq.trans hout (by out_close' : ($dv).output = _)
     rw [show $t = _ from hx])))

open Lean Elab Tactic Meta in
/-- Close a leaf that is one of the four tails. -/
elab "out_tail" : tactic => withMainContext do
  let tgt ← whnfR (← instantiateMVars (← getMainTarget))
  unless tgt.isAppOf ``Post && tgt.appArg!.isAppOf ``Except.ok do throwError "out_tail"
  let inner := tgt.appArg!.appArg!
  let some n := inner.getAppFn.constName? | throwError "out_tail"
  if n == ``genericCall.step then
    evalTactic (← `(tactic| exact genericCall.step_post _ (by out_close') _ _ _ _ _ _ _ _ _ _ _ _ _))
  else if n == ``genericCallAmsterdam.step then
    evalTactic (← `(tactic|
      exact genericCallAmsterdam.step_post _ _ (by out_close') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
  else if n == ``genericCreate.step then
    evalTactic (← `(tactic| exact genericCreate.step_post _ (by out_close') _ _ _ _))
  else if n == ``genericCreateAmsterdam.step then
    evalTactic (← `(tactic| exact genericCreateAmsterdam.step_post _ _ (by out_close') _ _ _ _))
  else throwError "out_tail"

set_option maxHeartbeats 4000000 in
theorem MessageOp.step_post (sevm : Sevm) {d : Devm} {o : Bytes} (h : d.output = o)
    (x : MessageOp) : OutcomePost o (MessageOp.step sevm d x) := by
  cases x <;> simp only [MessageOp.step]
  all_goals repeat' (first
    | (refine OutcomePost.ofExcept ?_)
    | out_tail
    | out_close'
    | out_error
    | rw [ok_bind']
    | (simp only [pure, Except.pure])
    | (simp only [Devm.withholdCreateGas, Devm.drainStateGasReservoir, Devm.memRead,
        completeDelegationAccess])
    | out_deleg
    | (refine Post.bind (by out_prim) ?_; intro ⟨_, _⟩ _)
    | (refine Post.bind (by out_prim) ?_; intro _ _)
    | (apply Post.ite <;> intro _)
    | split
    | (dsimp only))

set_option maxHeartbeats 1000000 in
theorem JumpOp.runCore_post (pc : Nat) (d : Devm) (sevm : Sevm) (j : JumpOp) {o : Bytes}
    (h : d.output = o) :
    Post (fun a : Nat × Devm => a.2.output = o) (JumpOp.runCore pc d sevm j) := by
  cases j <;> simp only [JumpOp.runCore] <;> out_walk

/-- What a step owes the output invariant. -/
def StepPost (o : Bytes) : Step → Prop
  | .halt _ => True
  | .next _ d => d.output = o
  | .spawn child p _ => p.legacyOutput = o ∧ child.checkpoint.trail.touchedRIPEMD160 = false

theorem StepPost.ofExecution {o : Bytes} (pc : Nat) {ex : Execution}
    (h : Post (fun d' : Devm => d'.output = o) ex) : StepPost o (Step.ofExecution pc ex) := by
  cases ex with
  | error e => trivial
  | ok d => exact h

set_option maxHeartbeats 1000000 in
theorem NextOp.step_post (evm : Evm) {o : Bytes} (h : evm.dyna.output = o) (n : NextOp) :
    StepPost o (NextOp.step evm n) := by
  cases n with
  | plain op => exact StepPost.ofExecution _ (PlainOp.runCore_post _ _ _ op h)
  | message x =>
    have := MessageOp.step_post evm.sta h x
    simp only [NextOp.step]
    revert this
    cases MessageOp.step evm.sta evm.dyna x with
    | done ex => exact StepPost.ofExecution _
    | spawn c p => exact id
  | _ =>
    simp only [NextOp.step]
    (try split) <;> refine StepPost.ofExecution _ ?_ <;> out_walk

/-- One step keeps the output: a continuing state has the frame's output, a spawn passes it
through and saves the caller grouped. -/
theorem Evm.step_post (evm : Evm) {o : Bytes} (h : evm.dyna.output = o) :
    StepPost o (Evm.step evm) := by
  unfold Evm.step
  split
  · trivial
  · exact NextOp.step_post evm h _
  · have := JumpOp.runCore_post evm.pc evm.dyna evm.sta ‹JumpOp› h
    simp only [JumpOp.run]
    revert this
    cases JumpOp.runCore evm.pc evm.dyna evm.sta ‹JumpOp› with
    | error e => intro; trivial
    | ok a => exact id
  · trivial

end OutputWalk

end Jaune
