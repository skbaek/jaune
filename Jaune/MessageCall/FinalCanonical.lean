import Jaune.MessageCall.Canonical
import Jaune.MessageCall.FinalTotality

/-! Canonicality of the world and original state through the native grouped frame driver. -/
namespace Jaune.Staging

open Jaune

/-- The current state and transient storage are canonical. -/
abbrev Frame.State.Canonical (s : Frame.State) : Prop := s.world.Canonical

/-- The original and current states within a running frame are canonical. -/
def Frame.Running.Canonical (r : Frame.Running) : Prop := r.context.block.Canonical ∧ Frame.State.Canonical r.state

abbrev Frame.Exit.Canonical (e : Frame.Exit) : Prop := Frame.State.Canonical e.state

private theorem liftCanonical {ε : Type} {s : Frame.State} (h : Frame.State.Canonical s)
    (f : Machine → Except (ε × Machine) Machine) :
    Walk Frame.State.Canonical Frame.State.Canonical (s.liftMachine f) := by
  unfold Jaune.Frame.State.liftMachine
  split <;> exact h

private theorem liftValueCanonical {ε α : Type} {s : Frame.State} (h : Frame.State.Canonical s)
    (f : Machine → Except (ε × Machine) (α × Machine)) :
    Walk Frame.State.Canonical (fun p => Frame.State.Canonical p.2) (s.liftMachineValue f) := by
  unfold Jaune.Frame.State.liftMachineValue
  split <;> exact h

private theorem storageValue_canonical {s : Frame.State} (h : Frame.State.Canonical s) (a : Address) (k v : U256) :
    Frame.State.Canonical (s.setStorageValue a k v) :=
  ⟨h.1.setStorVal _ _ _, h.2⟩

private theorem transientValue_canonical {s : Frame.State} (h : Frame.State.Canonical s) (a : Address) (k v : U256) :
    Frame.State.Canonical (s.setTransientValue a k v) :=
  ⟨h.1, h.2.setStorageValue _ _ _⟩

private theorem incrNonce_canonical {s : Frame.State} (h : Frame.State.Canonical s) (a : Address) :
    Frame.State.Canonical (s.incrNonce a) :=
  ⟨h.1.incrNonce _, h.2⟩

private theorem accessDelegation_world (rules : ForkRules) (s : Frame.State) (a : Address) :
    (ForkRules.accessDelegation rules s a).2.2.2.2.world = s.world := by
  unfold ForkRules.accessDelegation GasSchedule.accessDelegation
  split
  · dsimp only
    split <;> rfl
  · rfl

private theorem completeDelegation_world (s : Frame.State) (b : Bool) (a : Address) :
    (completeDelegationAccess s b a).2.world = s.world := by
  cases b <;> rfl

local macro "canonical_leaf" : tactic => `(tactic| first
  | assumption
  | (with_reducible apply storageValue_canonical; assumption)
  | (with_reducible apply transientValue_canonical; assumption)
  | (with_reducible apply incrNonce_canonical; assumption)
  | (solve | simp only [Frame.State.Canonical, accessDelegation_world, completeDelegation_world,
      Frame.State.addAccessedAddress, Frame.State.recordAccountRead, Frame.State.withTrail,
      Frame.State.withSubstate] at * <;> assumption)
  | exact True.intro)

private theorem canonical_push (x : U256) {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical Frame.State.Canonical (s.push x) :=
  liftCanonical h _

private theorem canonical_pop {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical (fun p => Frame.State.Canonical p.2) (s.pop) :=
  liftValueCanonical h _

private theorem canonical_chargeGas (cost : Nat) {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical Frame.State.Canonical (s.chargeGas cost) :=
  liftCanonical h _

private theorem canonical_chargeStateGas (amount : Nat) {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical Frame.State.Canonical (s.chargeStateGas amount) :=
  liftCanonical h _

private theorem canonical_popToNat {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical (fun p => Frame.State.Canonical p.2) (s.popToNat) :=
  liftValueCanonical h _

private theorem canonical_popToAddress {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical (fun p => Frame.State.Canonical p.2) (s.popToAddress) :=
  liftValueCanonical h _

private theorem canonical_popN (k : Nat) {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical (fun p => Frame.State.Canonical p.2) (s.popN k) :=
  liftValueCanonical h _

private theorem canonical_pushItem (x : U256) (cost : Nat) {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical Frame.State.Canonical (s.pushItem x cost) :=
  liftCanonical h _

private theorem canonical_applyUnary (f : U256 → U256) (cost : Nat) {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical Frame.State.Canonical (s.applyUnary f cost) :=
  liftCanonical h _

private theorem canonical_applyBinary (f : U256 → U256 → U256) (cost : Nat) {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical Frame.State.Canonical (s.applyBinary f cost) :=
  liftCanonical h _

private theorem canonical_applyTernary (f : U256 → U256 → U256 → U256) (cost : Nat) {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical Frame.State.Canonical (s.applyTernary f cost) :=
  liftCanonical h _

private theorem canonical_assertDynamic (ctx : CallContext) {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical (fun _ => True) (s.assertDynamic ctx) := Walk.assert h

open Lean Elab Tactic Meta in
elab "canonical_primitive" : tactic => withMainContext do
  let target ← instantiateMVars (← getMainTarget)
  unless target.isAppOf ``Walk do throwError "expected a state walk"
  let x := target.appArg!.headBeta
  let bound := x.isAppOf ``Bind.bind
  let op := if bound then (x.getArg! 4).headBeta else x
  let some head := op.getAppFn.constName? | throwError "expected a primitive"
  if head == ``Jaune.Frame.State.liftMachine && !bound then
    evalTactic (← `(tactic| exact liftCanonical (by canonical_leaf) _))
    return
  let (rule, arity, pair) ← match head with
    | ``Jaune.Frame.State.push => pure (mkIdent ``canonical_push, 1, false)
    | ``Jaune.Frame.State.pop => pure (mkIdent ``canonical_pop, 0, true)
    | ``Jaune.Frame.State.chargeGas => pure (mkIdent ``canonical_chargeGas, 1, false)
    | ``Jaune.Frame.State.chargeStateGas => pure (mkIdent ``canonical_chargeStateGas, 1, false)
    | ``Jaune.Frame.State.popToNat => pure (mkIdent ``canonical_popToNat, 0, true)
    | ``Jaune.Frame.State.popToAddress => pure (mkIdent ``canonical_popToAddress, 0, true)
    | ``Jaune.Frame.State.popN => pure (mkIdent ``canonical_popN, 1, true)
    | ``Jaune.Frame.State.pushItem => pure (mkIdent ``canonical_pushItem, 2, false)
    | ``Jaune.Frame.State.applyUnary => pure (mkIdent ``canonical_applyUnary, 2, false)
    | ``Jaune.Frame.State.applyBinary => pure (mkIdent ``canonical_applyBinary, 2, false)
    | ``Jaune.Frame.State.applyTernary => pure (mkIdent ``canonical_applyTernary, 2, false)
    | ``Jaune.Frame.State.assertDynamic => pure (mkIdent ``canonical_assertDynamic, 1, false)
    | ``Except.assert => pure (mkIdent ``Walk.assert, 0, false)
    | _ => throwError "expected a machine or state operation"
  let fact ← match arity with
    | 0 => `($rule (by canonical_leaf))
    | 1 => `($rule _ (by canonical_leaf))
    | _ => `($rule _ _ (by canonical_leaf))
  let combinator := mkIdent (if bound then ``Walk.bind else ``Walk.mono)
  if pair then
    evalTactic (← `(tactic| (refine $combinator $fact ?_; intro ⟨_, _⟩ _; try dsimp only at *)))
  else
    evalTactic (← `(tactic| (refine $combinator $fact ?_; intro _ _; try dsimp only at *)))

local macro "canonical_walk" : tactic => `(tactic| repeat' first
  | canonical_primitive
  | simp only [Walk.ok_iff, Walk.error_iff]
  | canonical_leaf
  | dsimp only
  | split)

private theorem sstoreBerlin_canonical (ctx : CallContext) {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical Frame.State.Canonical (PlainOp.sstoreBerlin ctx s) := by
  unfold PlainOp.sstoreBerlin
  refine Walk.bind (canonical_pop h) ?_
  intro ⟨key, t⟩ ht
  refine Walk.bind (canonical_pop ht) ?_
  intro ⟨value, u⟩ hu
  refine Walk.bind (Walk.assert (H := Frame.State.Canonical) hu) ?_
  intro _ _
  dsimp only
  split <;> refine Walk.bind (canonical_chargeGas _ (by split <;> exact hu)) ?_ <;> intro v hv <;>
    refine Walk.bind (canonical_assertDynamic ctx hv) ?_ <;> intro _ _ <;>
    exact storageValue_canonical hv _ _ _

private theorem sstoreLegacy_canonical (ctx : CallContext) {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical Frame.State.Canonical (PlainOp.sstoreLegacy ctx s) := by
  unfold PlainOp.sstoreLegacy
  canonical_walk
  all_goals apply storageValue_canonical; assumption

private theorem sstoreAmsterdam_canonical (state : StateGasRules) (ctx : CallContext) {s : Frame.State}
    (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical Frame.State.Canonical (PlainOp.sstoreAmsterdam state ctx s) := by
  unfold PlainOp.sstoreAmsterdam
  refine Walk.bind (canonical_assertDynamic ctx h) ?_
  intro _ _
  refine Walk.bind (canonical_pop h) ?_
  intro ⟨key, t⟩ ht
  refine Walk.bind (canonical_pop ht) ?_
  intro ⟨value, u⟩ hu
  refine Walk.bind (Walk.assert (H := Frame.State.Canonical) hu) ?_
  intro _ _
  refine Walk.bind (canonical_chargeGas _ ?_) ?_
  · split <;> exact hu
  · intro v hv
    refine Walk.bind (canonical_chargeStateGas _ hv) ?_
    intro w hw
    exact storageValue_canonical hw _ _ _

theorem PlainOp.runCore_canonical (pc : Nat) (ctx : CallContext) {s : Frame.State} (h : Frame.State.Canonical s)
    (op : Jaune.PlainOp) : Walk Frame.State.Canonical Frame.State.Canonical (PlainOp.runCore pc ctx s op) := by
  cases op
  case log k =>
    simp only [PlainOp.runCore, PlainOp.liftLog]
    split <;> exact h
  case sstore =>
    simp only [PlainOp.runCore]
    split
    · split <;> first | exact sstoreBerlin_canonical _ h | exact sstoreLegacy_canonical _ h
    · exact sstoreAmsterdam_canonical _ _ h
  all_goals simp only [PlainOp.runCore]
  all_goals canonical_walk

theorem JumpOp.runCore_canonical (pc : Nat) (ctx : CallContext) {s : Frame.State} (h : Frame.State.Canonical s)
    (op : Jaune.JumpOp) :
    Walk Frame.State.Canonical (fun p => Frame.State.Canonical p.2) (JumpOp.runCore pc ctx s op) := by
  cases op <;> simp only [JumpOp.runCore] <;> canonical_walk

private def ExitCanonical : Except Fault Frame.Exit → Prop
  | .error _ => True
  | .ok e => Frame.Exit.Canonical e

private theorem catchHalt_canonical {body : Except (ExceptionalHalt × Frame.State) (Except Fault Frame.Exit)}
    (h : Walk Frame.State.Canonical ExitCanonical body) : ExitCanonical (Frame.Exit.catchHalt body) := by
  cases body with
  | error e => cases e; exact h
  | ok result => exact h

private theorem creditBeneficiary_canonical {s : Frame.State} (h : Frame.State.Canonical s) (rules : ForkRules)
    (a : Address) (v : U256) : Frame.State.Canonical (s.creditBeneficiary rules a v) := by
  unfold Frame.State.creditBeneficiary
  split
  · exact World.Canonical.addBalance h _ _
  · exact ⟨h.1.setPresent a (ac := (s.world.state.get a).withBalance (s.world.state.bal a + v))
        (h.1.storage a), h.2⟩

private theorem setBalance_canonical {s : Frame.State} (h : Frame.State.Canonical s)
    (a : Address) (v : U256) : Frame.State.Canonical (s.setBalance a v) :=
  ⟨h.1.setBal a v, h.2⟩

private theorem selfdestructRefund_canonical {s : Frame.State} (h : Frame.State.Canonical s)
    (rules : ForkRules) (p : Prop) [Decidable p] (a : Address) :
    Frame.State.Canonical ((s.addSelfDestruct a).creditSelfdestructRefund rules p) := by
  unfold Frame.State.creditSelfdestructRefund
  split <;> exact h

private theorem selfdestruct_canonical (ctx : CallContext) {s : Frame.State} (h : Frame.State.Canonical s) :
    ExitCanonical (HaltOp.run ctx s .selfdestruct) := by
  cases hs : ctx.block.rules.stateGas with
  | none =>
    simp only [HaltOp.run, hs]
    apply catchHalt_canonical
    refine Walk.bind (liftValueCanonical h _) ?_
    rintro ⟨donee, t⟩ ht
    cases ctx.block.rules.access <;> simp only
    all_goals repeat' split
    all_goals
      refine Walk.bind (liftCanonical (by exact ht) _) ?_
      intro u hu
      refine Walk.bind (Walk.assert (H := Frame.State.Canonical) hu) ?_
      intro _ _
      unfold Frame.State.subtractBalance
      cases hb : u.world.subtractBalance ctx.recipient _ with
      | none => trivial
      | some w =>
        simp only [Option.map]
        have hw : Frame.State.Canonical (u.withWorld w) := World.Canonical.subtractBalance hu hb
        -- Dispatch each branch by its shape and leave the credited value to unification: a
        -- failed or value-checking `exact` would `whnf` through `State.writeAccount` inside
        -- `creditBeneficiary`.
        split
        · exact selfdestructRefund_canonical
            (setBalance_canonical (creditBeneficiary_canonical hw _ _ _) _ _) _ _ _
        · exact creditBeneficiary_canonical hw _ _ _
  | some state =>
    simp only [HaltOp.run, hs]
    apply catchHalt_canonical
    refine Walk.bind (Walk.assert (H := Frame.State.Canonical) h) ?_
    intro _ _
    refine Walk.bind (liftValueCanonical h _) ?_
    rintro ⟨donee, t⟩ ht
    refine Walk.bind (Walk.assert (H := Frame.State.Canonical) ht) ?_
    intro _ _
    split <;> refine Walk.bind (liftCanonical (by exact ht) _) ?_ <;>
      intro u hu <;> refine Walk.bind (liftCanonical hu _) ?_ <;> intro v hv
    all_goals
      unfold Frame.State.subtractBalance
      cases hb : v.world.subtractBalance ctx.recipient _ with
      | none => trivial
      | some w =>
        simp only [Option.map]
        have hw := World.Canonical.subtractBalance hv hb
        unfold Frame.State.emitTransferLog
        repeat' split
        all_goals exact World.Canonical.addBalance hw _ _

theorem HaltOp.run_canonical (ctx : CallContext) {s : Frame.State} (hs : Frame.State.Canonical s)
    (op : Jaune.HaltOp) {e : Frame.Exit} (h : HaltOp.run ctx s op = .ok e) : Frame.Exit.Canonical e := by
  suffices hp : ExitCanonical (HaltOp.run ctx s op) by rw [h] at hp; exact hp
  cases op with
  | stop => exact hs
  | selfdestruct => exact selfdestruct_canonical _ hs
  | revert | return_ => apply catchHalt_canonical; canonical_walk

/-- Canonicality of a completed instruction or the saved checkpoint of a child. -/
def MessageOp.Outcome.Canonical : MessageOp.Outcome → Prop
  | .done x => Walk Frame.State.Canonical Frame.State.Canonical x
  | .spawn child _ => Jaune.Frame.Canonical child

theorem MessageOp.Outcome.ofExcept_canonical {x : Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (h : Walk Frame.State.Canonical MessageOp.Outcome.Canonical x) : (MessageOp.Outcome.ofExcept x).Canonical := by
  cases x <;> exact h

private theorem pushZero_canonical {s : Frame.State} (h : Frame.State.Canonical s) :
    Walk Frame.State.Canonical MessageOp.Outcome.Canonical (do
      let t ← s.push 0
      return .done (.ok t)) := by
  refine Walk.bind (liftCanonical h _) ?_
  intro t ht
  exact ht

theorem genericCall.step_canonical (ctx : CallContext) (s : Frame.State) (gas : Nat) (value : U256)
    (caller target codeAddress : Address) (transfersValue isStaticcall : Bool)
    (inputIndex inputSize outputIndex outputSize : Nat) (code : ByteArray) (disablePrecompiles : Bool)
    (hc : ctx.block.Canonical) (h : Frame.State.Canonical s) :
    MessageOp.Outcome.Canonical (genericCall.step ctx s gas value caller target codeAddress transfersValue
      isStaticcall inputIndex inputSize outputIndex outputSize code disablePrecompiles) := by
  unfold genericCall.step
  split
  · apply MessageOp.Outcome.ofExcept_canonical
    exact pushZero_canonical h
  · exact ⟨h, hc⟩

theorem genericCallAmsterdam.step_canonical (ctx : CallContext) (state : StateGasRules)
    (s : Frame.State) (gas reservoir : Nat) (value : U256) (caller target codeAddress : Address)
    (transfersValue isStaticcall : Bool) (inputIndex inputSize outputIndex outputSize : Nat)
    (code : ByteArray) (disablePrecompiles newAccountCharged insufficientBalance : Bool) (hc : ctx.block.Canonical) (h : Frame.State.Canonical s) :
    MessageOp.Outcome.Canonical (genericCallAmsterdam.step ctx state
      s gas reservoir value caller target codeAddress transfersValue isStaticcall inputIndex
      inputSize outputIndex outputSize code disablePrecompiles newAccountCharged insufficientBalance) := by
  unfold genericCallAmsterdam.step
  split
  · apply MessageOp.Outcome.ofExcept_canonical
    cases newAccountCharged <;> exact pushZero_canonical h
  · exact ⟨h, hc⟩

theorem genericCreate.step_canonical (ctx : CallContext) (s : Frame.State) (endowment : U256)
    (address : Address) (offset size : Nat) (hc : ctx.block.Canonical) (h : Frame.State.Canonical s) :
    MessageOp.Outcome.Canonical (genericCreate.step ctx s endowment address offset size) := by
  unfold genericCreate.step
  apply MessageOp.Outcome.ofExcept_canonical
  refine Walk.bind (Walk.assert (H := Frame.State.Canonical) h) ?_
  intro _ _
  refine Walk.bind (Walk.assert (H := Frame.State.Canonical) h) ?_
  intro _ _
  dsimp only
  split
  · exact pushZero_canonical h
  · split
    · exact pushZero_canonical (incrNonce_canonical h _)
    · exact ⟨incrNonce_canonical h _, hc⟩

theorem genericCreateAmsterdam.step_canonical (ctx : CallContext) (rules : StateGasRules)
    (s : Frame.State) (endowment : U256) (address : Address) (offset size : Nat) (hc : ctx.block.Canonical) (h : Frame.State.Canonical s) :
    MessageOp.Outcome.Canonical (genericCreateAmsterdam.step ctx rules s endowment address offset size) := by
  unfold genericCreateAmsterdam.step
  apply MessageOp.Outcome.ofExcept_canonical
  dsimp only
  split
  · exact pushZero_canonical h
  · split
    · refine Walk.bind (canonical_chargeStateGas _ (by exact h)) ?_
      intro t ht
      split
      · exact pushZero_canonical (incrNonce_canonical ht _)
      · exact ⟨incrNonce_canonical ht _, hc⟩
    · simp only [bind, Except.bind]
      split
      · exact pushZero_canonical (incrNonce_canonical h _)
      · exact ⟨incrNonce_canonical h _, hc⟩

private theorem bind_ok {ε α β : Type} (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl

/-- Unfold one dispatch arm and carry the canonical world across its stack pops and charges.
Keep each opcode a separate kernel declaration. -/
local macro "canonical_message " name:ident " for " op:term : command =>
  `(private theorem $name (ctx : CallContext) (s : Frame.State) (hc : ctx.block.Canonical)
      (h : Frame.State.Canonical s) : (MessageOp.step ctx s $op).Canonical := by
    simp only [MessageOp.step]
    repeat' first
      | canonical_primitive
      | simp only [pure, Except.pure, Walk.ok_iff, Walk.error_iff]
      | (with_reducible apply MessageOp.Outcome.ofExcept_canonical)
      | (solve | canonical_leaf)
      | simp only [bind_ok]
      | dsimp only
      | split
    all_goals first
      | (apply genericCall.step_canonical <;> assumption)
      | (apply genericCallAmsterdam.step_canonical <;> assumption)
      | (apply genericCreate.step_canonical <;> assumption)
      | (apply genericCreateAmsterdam.step_canonical <;> assumption))

canonical_message canonical_call for .call
canonical_message canonical_callcode for .callcode
canonical_message canonical_delegatecall for .delegatecall
canonical_message canonical_staticcall for .staticcall
canonical_message canonical_create for .create
canonical_message canonical_create2 for .create2

theorem MessageOp.step_canonical (ctx : CallContext) (s : Frame.State) (hc : ctx.block.Canonical)
    (h : Frame.State.Canonical s) (op : Jaune.MessageOp) : (MessageOp.step ctx s op).Canonical := by
  cases op with
  | call => exact canonical_call _ _ hc h
  | callcode => exact canonical_callcode _ _ hc h
  | delegatecall => exact canonical_delegatecall _ _ hc h
  | staticcall => exact canonical_staticcall _ _ hc h
  | create => exact canonical_create _ _ hc h
  | create2 => exact canonical_create2 _ _ hc h

def Step.Canonical : Step → Prop
  | .next _ s => Frame.State.Canonical s
  | .exit e => Frame.Exit.Canonical e
  | .spawn child _ _ => Jaune.Frame.Canonical child

theorem Step.ofHalt_canonical {pc : Nat} {x}
    (h : Walk Frame.State.Canonical Frame.State.Canonical x) : (Step.ofHalt pc x).Canonical := by
  cases x with
  | error e => cases e; exact h
  | ok _ => exact h

theorem MessageOp.Outcome.toStep_canonical {pc : Nat} {o : MessageOp.Outcome}
    (h : o.Canonical) : (o.toStep pc).Canonical := by
  cases o with
  | done _ => exact Step.ofHalt_canonical h
  | spawn _ _ => exact h

theorem NextOp.step_canonical {r : Frame.Running} (h : Frame.Running.Canonical r) (op : Jaune.NextOp) :
    (NextOp.step r op).Canonical := by
  have hstate := h.2
  cases op with
  | plain p => exact Step.ofHalt_canonical (PlainOp.runCore_canonical _ _ h.2 p)
  | message m => exact MessageOp.Outcome.toStep_canonical (MessageOp.step_canonical _ _ h.1 h.2 m)
  | push xs _ =>
    simp only [NextOp.step]
    split
    · exact h.2
    · apply Step.ofHalt_canonical; canonical_walk
  | dupn imm | swapn imm | exchange imm => apply Step.ofHalt_canonical; canonical_walk

theorem step_canonical {r : Frame.Running} (h : Frame.Running.Canonical r) {out : Step}
    (hs : step r = .ok out) : out.Canonical := by
  unfold step at hs
  split at hs
  · cases hs; exact h.2
  · cases hs; exact NextOp.step_canonical h _
  · rename_i j _
    have hj := JumpOp.runCore_canonical r.pc r.context h.2 j
    unfold JumpOp.run at hs
    split at hs
    · rename_i p he; rw [he] at hj; cases hs; cases p; exact hj
    · rename_i pc s he; rw [he] at hj; cases hs; exact hj
  · rename_i op _
    cases he : HaltOp.run r.context r.state op with
    | error f => rw [he] at hs; cases hs
    | ok exit => rw [he] at hs; cases hs; exact HaltOp.run_canonical _ h.2 op he

/-- Charging the deposit affects only the machine. -/
theorem chargeDeposit_world {rules : ForkRules} {code : Bytes} {s t : Frame.State}
    (h : chargeDeposit rules code s = .ok t) : t.world = s.world := by
  have onlyWorld {a : Frame.State} {f : Machine → Except (ExceptionalHalt × Machine) Machine} :
      Walk (fun _ => True) (fun b => b.world = a.world) (a.liftMachine f) := by
    unfold Frame.State.liftMachine
    split <;> trivial
  have chargeSize (bytes : Bytes) : Walk (fun _ => True) (fun b => b.world = s.world) (do
      let v ← s.chargeGas (bytes.length * Gas.codeDeposit)
      if rules.code.maxCodeSize < bytes.length then .error (.outOfGas .none, v) else .ok v) := by
    refine Walk.bind onlyWorld ?_
    intro v hv
    split <;> first | exact hv | trivial
  have world : Walk (fun _ => True) (fun b => b.world = s.world) (chargeDeposit rules code s) := by
    unfold chargeDeposit
    dsimp only
    repeat' first | trivial | apply chargeSize | split
    all_goals
      refine Walk.bind onlyWorld ?_
      intro v hv
      exact Walk.mono onlyWorld (fun _ hw => hw.trans hv)
  rw [h] at world
  exact world

theorem settle_canonical {f : Frame} {e : Frame.Exit} (hi : Frame.Exit.Canonical e) {r : Frame.Result}
    (h : settle f e = .ok r) : r.Canonical := by
  cases e with
  | halted reason s => cases h; trivial
  | reverted bytes s => cases h; trivial
  | finished bytes s =>
    simp only [settle] at h
    split at h
    · cases h; exact hi
    · split at h
      · rename_i t ht
        unfold depositCode at ht
        cases hd : chargeDeposit _ _ _ with
        | error p => rw [hd] at ht; cases ht
        | ok w =>
          rw [hd] at ht
          cases ht; cases h
          have hw : Frame.State.Canonical w := by
            unfold Frame.State.Canonical; rw [chargeDeposit_world hd]; exact hi
          exact ⟨hw.1.setCode _ _, hw.2⟩
      · cases h; trivial

def Frame.Entry.Canonical : Frame.Entry → Prop
  | .run r => Frame.Running.Canonical r
  | .done (.ok result) => result.Canonical
  | .done (.error _) => True

private theorem runPrecompile_canonical {run : Frame.Running} (a : Address) {e : Frame.Exit}
    (hi : Frame.State.Canonical run.state) (h : runPrecompile run a = .ok e) : Frame.Exit.Canonical e := by
  unfold runPrecompile Frame.Exit.ofPrecompileResult at h
  split at h
  · cases h; exact hi
  · split at h <;> cases h <;> exact hi

theorem enterWith_canonical {f : Frame} (hf : f.Canonical) (start : Frame.State) :
    (enterWith f start).Canonical := by
  unfold enterWith
  dsimp only
  split
  · trivial
  · rename_i world hw
    have hi : Frame.Running.Canonical (Frame.entered f start world) :=
      ⟨hf.2, Jaune.Message.transfer_canonical (Jaune.Frame.enteredWorld_canonical hf) hw⟩
    split
    · split
      · rename_i hp
        cases he : runPrecompile (Frame.entered f start world) _ with
        | error fault => trivial
        | ok e =>
          change Frame.Entry.Canonical (.done (settle f e))
          cases hs : settle f e with
          | error fault => trivial
          | ok r => exact settle_canonical (runPrecompile_canonical _ hi.2 he) hs
      · exact hi
    · exact hi

theorem enter_canonical {f : Frame} (hf : f.Canonical) : (enter f).Canonical := enterWith_canonical hf _

theorem resume_canonical {rules : ForkRules} {p : Pending} {saved : Frame.State} {r : Frame.Result}
    (hs : Frame.State.Canonical saved) (hr : r.Canonical) {x}
    (h : resume rules p saved r = .ok x) : Walk Frame.State.Canonical Frame.State.Canonical x := by
  unfold resume at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals cases h
  all_goals first | exact hs | exact hr

theorem execFueled_run_canonical (fuel : Nat) (run : Frame.Running) (hi : Frame.Running.Canonical run)
    {e : Frame.Exit} (h : (execFueled run fuel).run = some (.ok e)) : Frame.Exit.Canonical e := by
  induction fuel generalizing run e with
  | zero => nomatch h
  | succ fuel ih =>
    rw [execFueled] at h
    rcases hs : step run with fault | exit | ⟨pc, s⟩ | ⟨child, p, pc⟩ <;> rw [hs] at h
    · cases h
    · cases h; exact step_canonical hi hs
    · exact ih ⟨pc, run.context, s⟩ ⟨hi.1, step_canonical hi hs⟩ h
    · have hf : Jaune.Frame.Canonical child := step_canonical hi hs
      have hent := enter_canonical hf
      have resultCanonical : ∀ res, (match enter child with
          | .done result => some result
          | .run cr => (execFueled cr fuel).run.map (· >>= settle child)) = some (.ok res) → res.Canonical := by
        intro res hres
        rcases he : enter child with cr | result <;> simp only [he] at hres hent
        · rcases hx : (execFueled cr fuel).run with _ | err | exit <;> rw [hx] at hres
          · cases hres
          · cases hres
          · exact settle_canonical (ih cr hent hx) (Option.some.inj hres)
        · cases hres; exact hent
      dsimp only at h
      split at h
      · cases h
      · cases h
      · rename_i res he
        have hr := resultCanonical res he
        split at h
        · cases h
        · rename_i reason s hres
          cases h
          exact resume_canonical hf.1 hr hres
        · rename_i s hres
          exact ih ⟨pc, run.context, s⟩ ⟨hi.1, resume_canonical hf.1 hr hres⟩ h

theorem exec_canonical {run : Frame.Running} (h : Frame.Running.Canonical run)
    {e : Frame.Exit} (he : exec run = .ok e) : Frame.Exit.Canonical e :=
  execFueled_run_canonical _ run h ((execFueled_run_sufficientFuel run).trans (congrArg some he))

/-- Running an entire frame and selecting its committed world preserves canonicality. -/
theorem Frame.runTop_canonical {f : Frame} (hf : f.Canonical) {r : Frame.Result}
    (h : Frame.runTop f = .ok r) : (f.worldAfter r).Canonical := by
  have hr : r.Canonical := by
    unfold Frame.runTop at h
    have hi := enterWith_canonical hf f.checkpoint
    cases he : enterWith f f.checkpoint with
    | done result => rw [he] at h hi; cases h; exact hi
    | run run =>
      rw [he] at h hi
      dsimp only at h
      cases hx : exec run with
      | error fault => rw [hx] at h; cases h
      | ok exit => rw [hx] at h; exact settle_canonical (exec_canonical hi hx) h
  unfold Jaune.Frame.worldAfter
  split
  · exact hr
  · exact hf.1

end Jaune.Staging
