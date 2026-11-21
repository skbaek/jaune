import Jaune.FrameRun.Entered
import Jaune.FrameRun.CallsHistory
import Jaune.MessageCall.ResumeFacts
import Jaune.Instructions.StoreFacts

/-!
# Warm addresses over a frame run (goal `jaune-shape-and-names-v1`, G2b, U103)

EIP-2929's accessed-address set only grows while a frame runs. Every instruction that goes on
in the same frame keeps every accessed address (`step_next_accessedAddresses`); a spawned child
starts with every address its caller had (`step_spawn_child_warm`); and the caller resumes with
every address it had at the call, whether the child succeeded (its set is united into the
caller's) or failed (the caller keeps the set it saved at the call) (`resume_accessedAddresses`).

So every address accessed when a run starts is accessed at every visit of the run
(`Frame.Run.visits_warm`), at the start of every frame it enters (`Frame.Run.frames_warm`),
including frames inside subtrees that later revert, and at the start of every call that ran
(`Frame.Run.calls_ran_warm`). There is no premise on the fork: the facts hold with and without
state gas.
-/

namespace Jaune

open Jaune

/-! ### Primitive laws -/

private theorem warm_addAccessedAddress {a : Address} {s : Frame.State} (x : Address)
    (h : a ∈ s.accessedAddresses) : a ∈ (s.addAccessedAddress x).accessedAddresses :=
  Std.HashSet.mem_insert.2 (Or.inr h)

private theorem warm_accessDelegation {a : Address} {s : Frame.State} (rules : ForkRules) (x : Address)
    (h : a ∈ s.accessedAddresses) : a ∈ (ForkRules.accessDelegation rules s x).2.2.2.2.accessedAddresses := by
  unfold ForkRules.accessDelegation
  cases rules.delegationEnabled with
  | false => exact h
  | true =>
    unfold GasSchedule.accessDelegation
    dsimp only
    cases getDelegatedCodeAddress (s.code x) with
    | none => exact h
    | some adr => exact warm_addAccessedAddress adr h

private theorem warm_completeDelegation {a : Address} {s : Frame.State} (d : Bool) (x : Address)
    (h : a ∈ s.accessedAddresses) : a ∈ (completeDelegationAccess s d x).2.accessedAddresses := by
  cases d with
  | false => exact h
  | true => exact warm_addAccessedAddress x h

private theorem warm_accessRule {a : Address} {s : Frame.State} (acc : AccessSchedule) (x : Address)
    (h : a ∈ s.accessedAddresses) :
    a ∈ (match acc with | .eip2929 => s.addAccessedAddress x | .flat _ => s).accessedAddresses := by
  cases acc with
  | flat _ => exact h
  | eip2929 => exact warm_addAccessedAddress x h

private theorem warm_withMachine {a : Address} {s : Frame.State} (m : Machine)
    (h : a ∈ s.accessedAddresses) : a ∈ (s.withMachine m).accessedAddresses := h

private theorem warm_withWorld {a : Address} {s : Frame.State} (w : World)
    (h : a ∈ s.accessedAddresses) : a ∈ (s.withWorld w).accessedAddresses := h

private theorem warm_withTrail {a : Address} {s : Frame.State} (t : Trail)
    (h : a ∈ s.accessedAddresses) : a ∈ (s.withTrail t).accessedAddresses := h

/-- Close a membership goal on a state built from a warm one by the primitives. Every step
matches at reducible transparency, so no state function is unfolded. -/
syntax "warm_leaf" : tactic
macro_rules | `(tactic| warm_leaf) => `(tactic| with_reducible assumption)
macro_rules | `(tactic| warm_leaf) => `(tactic| ((with_reducible apply warm_withMachine); warm_leaf))
macro_rules | `(tactic| warm_leaf) => `(tactic| ((with_reducible apply warm_withWorld); warm_leaf))
macro_rules | `(tactic| warm_leaf) => `(tactic| ((with_reducible apply warm_withTrail); warm_leaf))
macro_rules | `(tactic| warm_leaf) => `(tactic| ((with_reducible apply warm_addAccessedAddress); warm_leaf))
macro_rules | `(tactic| warm_leaf) => `(tactic| ((with_reducible apply warm_accessDelegation); warm_leaf))
macro_rules | `(tactic| warm_leaf) => `(tactic| ((with_reducible apply warm_completeDelegation); warm_leaf))
macro_rules | `(tactic| warm_leaf) => `(tactic| ((apply warm_accessRule); warm_leaf))

/-! ### Plain instructions and jumps -/

/-- A family step that goes on keeps every accessed address. -/
theorem Family.run_accessedAddresses {f : Family} {x : Frame.Running} {s : Frame.State}
    (h : f.run x = .ok s) {a : Address} (ha : a ∈ x.state.accessedAddresses) :
    a ∈ s.accessedAddresses := by
  cases f with
  | word row | shuffle row | memory row =>
    simp only [Family.run, Frame.State.liftMachine] at h
    split at h
    · cases h
    · cases h; exact ha
  | log row =>
    simp only [Family.run, Frame.State.liftLog] at h
    split at h
    · cases h
    · cases h; exact ha
  | read row =>
    simp only [Family.run, Frame.State.liftRead] at h
    split at h
    · cases h
    · cases h
      rename_i t _
      unfold Frame.State.applyReadTouch
      rcases t with ⟨warmed, read⟩
      rcases warmed with _ | ⟨b⟩ | ⟨b, k⟩ <;> rcases read with _ | ⟨c⟩ | ⟨c, l⟩
      all_goals first | exact ha | exact warm_addAccessedAddress b ha
  | store kind =>
    cases kind <;> simp only [Family.run, Frame.State.liftStore] at h <;> split at h
    all_goals first
      | cases h; done
      | (cases h; rw [Frame.State.applyStoreTouch_accessedAddresses]; exact ha)

/-! ### Message instructions that finish without a frame -/

/-- What a finished message instruction leaves warm. A spawn is covered by
`step_spawn_accessedAddresses`. -/
private def DonePost (a : Address) : MessageOp.Outcome → Prop
  | .done (.ok t) => a ∈ t.accessedAddresses
  | _ => True

private abbrev W (a : Address) (x : Except (ExceptionalHalt × Frame.State) MessageOp.Outcome) : Prop :=
  Walk (fun _ => True) (DonePost a) x

private theorem ofExcept_donePost {a : Address} {x : Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hx : W a x) : DonePost a (MessageOp.Outcome.ofExcept x) := by
  cases x with
  | error _ => trivial
  | ok _ => exact hx

private theorem walk_liftMachineValue {α β : Type} {P : Address → β → Prop} {a : Address} {s : Frame.State}
    {core : Machine → Except (ExceptionalHalt × Machine) (α × Machine)}
    {k : α × Frame.State → Except (ExceptionalHalt × Frame.State) β}
    (hs : a ∈ s.accessedAddresses)
    (hk : ∀ v s', a ∈ s'.accessedAddresses → Walk (fun _ => True) (P a) (k (v, s'))) :
    Walk (fun _ => True) (P a) (s.liftMachineValue core >>= k) := by
  unfold Frame.State.liftMachineValue
  cases core s.machine with
  | error _ => trivial
  | ok p => exact hk p.1 (s.withMachine p.2) hs

private theorem walk_liftMachine {β : Type} {P : Address → β → Prop} {a : Address} {s : Frame.State}
    {core : Machine → Except (ExceptionalHalt × Machine) Machine}
    {k : Frame.State → Except (ExceptionalHalt × Frame.State) β}
    (hs : a ∈ s.accessedAddresses) (hk : ∀ s', a ∈ s'.accessedAddresses → Walk (fun _ => True) (P a) (k s')) :
    Walk (fun _ => True) (P a) (s.liftMachine core >>= k) := by
  unfold Frame.State.liftMachine
  cases core s.machine with
  | error _ => trivial
  | ok m => exact hk (s.withMachine m) hs

private theorem walk_pop {β : Type} {P : Address → β → Prop} {a : Address} {s : Frame.State}
    {k : U256 × Frame.State → Except (ExceptionalHalt × Frame.State) β}
    (hs : a ∈ s.accessedAddresses) (hk : ∀ v s', a ∈ s'.accessedAddresses → Walk (fun _ => True) (P a) (k (v, s'))) :
    Walk (fun _ => True) (P a) (s.pop >>= k) :=
  walk_liftMachineValue hs hk

private theorem walk_popToNat {β : Type} {P : Address → β → Prop} {a : Address} {s : Frame.State}
    {k : Nat × Frame.State → Except (ExceptionalHalt × Frame.State) β}
    (hs : a ∈ s.accessedAddresses) (hk : ∀ v s', a ∈ s'.accessedAddresses → Walk (fun _ => True) (P a) (k (v, s'))) :
    Walk (fun _ => True) (P a) (s.popToNat >>= k) :=
  walk_liftMachineValue hs hk

private theorem walk_popToAddress {β : Type} {P : Address → β → Prop} {a : Address} {s : Frame.State}
    {k : Address × Frame.State → Except (ExceptionalHalt × Frame.State) β}
    (hs : a ∈ s.accessedAddresses) (hk : ∀ v s', a ∈ s'.accessedAddresses → Walk (fun _ => True) (P a) (k (v, s'))) :
    Walk (fun _ => True) (P a) (s.popToAddress >>= k) :=
  walk_liftMachineValue hs hk

private theorem walk_chargeGas {β : Type} {P : Address → β → Prop} {a : Address} {s : Frame.State} {cost : Nat}
    {k : Frame.State → Except (ExceptionalHalt × Frame.State) β}
    (hs : a ∈ s.accessedAddresses) (hk : ∀ s', a ∈ s'.accessedAddresses → Walk (fun _ => True) (P a) (k s')) :
    Walk (fun _ => True) (P a) (s.chargeGas cost >>= k) :=
  walk_liftMachine hs hk

private theorem walk_chargeStateGas {β : Type} {P : Address → β → Prop} {a : Address} {s : Frame.State} {amount : Nat}
    {k : Frame.State → Except (ExceptionalHalt × Frame.State) β}
    (hs : a ∈ s.accessedAddresses) (hk : ∀ s', a ∈ s'.accessedAddresses → Walk (fun _ => True) (P a) (k s')) :
    Walk (fun _ => True) (P a) (s.chargeStateGas amount >>= k) :=
  walk_liftMachine hs hk

private theorem walk_push {β : Type} {P : Address → β → Prop} {a : Address} {s : Frame.State} {x : U256}
    {k : Frame.State → Except (ExceptionalHalt × Frame.State) β}
    (hs : a ∈ s.accessedAddresses) (hk : ∀ s', a ∈ s'.accessedAddresses → Walk (fun _ => True) (P a) (k s')) :
    Walk (fun _ => True) (P a) (s.push x >>= k) :=
  walk_liftMachine hs hk

private theorem walk_ok {β : Type} {P : Address → β → Prop} {a : Address} {s : Frame.State}
    {k : Frame.State → Except (ExceptionalHalt × Frame.State) β}
    (hs : a ∈ s.accessedAddresses) (hk : ∀ s', a ∈ s'.accessedAddresses → Walk (fun _ => True) (P a) (k s')) :
    Walk (fun _ => True) (P a) (Except.ok s >>= k) :=
  hk s hs

private theorem walk_assert {β : Type} {P : Address → β → Prop} {a : Address} {p : Prop} [Decidable p] {e : ExceptionalHalt × Frame.State}
    {k : Unit → Except (ExceptionalHalt × Frame.State) β} (hk : Walk (fun _ => True) (P a) (k ())) :
    Walk (fun _ => True) (P a) (Except.assert p e >>= k) := by
  unfold Except.assert
  split
  · exact hk
  · trivial

private theorem walk_assertDynamic {β : Type} {P : Address → β → Prop} {a : Address} {s : Frame.State} {ctx : CallContext}
    {k : Unit → Except (ExceptionalHalt × Frame.State) β} (hk : Walk (fun _ => True) (P a) (k ())) :
    Walk (fun _ => True) (P a) (s.assertDynamic ctx >>= k) :=
  walk_assert hk

private theorem walk_ite {β : Type} {P : Address → β → Prop} {a : Address} {c : Prop} [Decidable c]
    {t e : Except (ExceptionalHalt × Frame.State) β} (ht : Walk (fun _ => True) (P a) t) (he : Walk (fun _ => True) (P a) e) :
    Walk (fun _ => True) (P a) (if c then t else e) := by
  split
  · exact ht
  · exact he

/-- What a jump leaves warm. -/
private def JumpPost (a : Address) (p : Nat × Frame.State) : Prop := a ∈ p.2.accessedAddresses

private theorem jump_walk (pc : Nat) (ctx : CallContext) (s : Frame.State) (j : JumpOp) {a : Address}
    (h : a ∈ s.accessedAddresses) :
    Walk (fun _ => True) (JumpPost a) (JumpOp.runCore pc ctx s j) := by
  cases j <;> simp only [JumpOp.runCore]
  all_goals repeat' (first
    | (apply walk_pop; assumption; intro _ _ _)
    | (apply walk_chargeGas; assumption; intro _ _)
    | apply walk_assert
    | split
    | assumption)

/-- A jump that goes on keeps every accessed address. -/
theorem JumpOp.run_accessedAddresses {x r : Frame.Running} {j : JumpOp} (h : JumpOp.run x j = .ok r)
    {a : Address} (ha : a ∈ x.state.accessedAddresses) : a ∈ r.state.accessedAddresses := by
  unfold JumpOp.run at h
  cases hj : JumpOp.runCore x.pc x.context x.state j with
  | error e => rw [hj] at h; cases h
  | ok p =>
    rcases p with ⟨pc, s⟩
    rw [hj] at h
    cases h
    have hw := jump_walk x.pc x.context x.state j ha
    rw [hj] at hw
    exact hw

private theorem walk_done {a : Address} {t : Frame.State} (h : a ∈ t.accessedAddresses) :
    W a (pure (.done (.ok t))) := h

private theorem walk_tail {a : Address} {o : MessageOp.Outcome} (h : DonePost a o) : W a (pure o) := h

private theorem prepareCall_donePost {a : Address} {ctx s gas value caller target addr transfer static
    ii il oi ol code disabled} (h : a ∈ s.accessedAddresses) :
    DonePost a (prepareCall.step ctx s gas value caller target addr transfer static ii il oi ol code
      disabled) := by
  unfold prepareCall.step
  dsimp only
  split
  · apply ofExcept_donePost
    exact walk_push h fun t ht => walk_done ht
  · trivial

private theorem prepareCallAmsterdam_donePost {a : Address} {ctx rules s gas reservoir value caller
    target addr transfer static ii il oi ol code disabled charged insufficient}
    (h : a ∈ s.accessedAddresses) :
    DonePost a (prepareCallAmsterdam.step ctx rules s gas reservoir value caller target addr transfer
      static ii il oi ol code disabled charged insufficient) := by
  unfold prepareCallAmsterdam.step
  dsimp only
  split
  · apply ofExcept_donePost
    cases charged <;> exact walk_push h fun t ht => walk_done ht
  · trivial

private theorem prepareCreate_donePost {a : Address} {ctx s value addr i len}
    (h : a ∈ s.accessedAddresses) : DonePost a (prepareCreate.step ctx s value addr i len) := by
  unfold prepareCreate.step
  apply ofExcept_donePost
  try dsimp only
  apply walk_assert
  apply walk_assertDynamic
  split
  · exact walk_push h fun t ht => walk_done ht
  · split
    · exact walk_push (warm_addAccessedAddress _ h) fun t ht => walk_done ht
    · exact True.intro

private theorem prepareCreateAmsterdam_donePost {a : Address} {ctx rules s value addr i len}
    (h : a ∈ s.accessedAddresses) : DonePost a (prepareCreateAmsterdam.step ctx rules s value addr i len) := by
  unfold prepareCreateAmsterdam.step
  apply ofExcept_donePost
  try dsimp only
  split
  · exact walk_push h fun t ht => walk_done ht
  · split
    all_goals first
      | (apply walk_chargeStateGas; exact warm_addAccessedAddress addr h)
      | (apply walk_ok; exact warm_addAccessedAddress addr h)
    all_goals
      intro t ht
      split
      · exact walk_push ht fun u hu => walk_done hu
      · exact True.intro

local macro "done_walk" : tactic => `(tactic| repeat' (first
  | (with_reducible apply walk_ite)
  | ((with_reducible apply walk_pop); (solve | warm_leaf); intro _ _ _; try dsimp only)
  | ((with_reducible apply walk_popToNat); (solve | warm_leaf); intro _ _ _; try dsimp only)
  | ((with_reducible apply walk_popToAddress); (solve | warm_leaf); intro _ _ _; try dsimp only)
  | ((with_reducible apply walk_chargeGas); (solve | warm_leaf); intro _ _; try dsimp only)
  | ((with_reducible apply walk_chargeStateGas); (solve | warm_leaf); intro _ _; try dsimp only)
  | ((with_reducible apply walk_ok); (solve | warm_leaf); intro _ _; try dsimp only)
  | ((with_reducible apply walk_push); (solve | warm_leaf); intro _ _; try dsimp only)
  | ((with_reducible apply walk_assert); try dsimp only)
  | ((with_reducible apply walk_assertDynamic); try dsimp only)
  | ((with_reducible apply walk_done); warm_leaf)
  | ((with_reducible apply walk_tail); first
      | (apply prepareCall_donePost; warm_leaf)
      | (apply prepareCallAmsterdam_donePost; warm_leaf)
      | (apply prepareCreate_donePost; warm_leaf)
      | (apply prepareCreateAmsterdam_donePost; warm_leaf))
  | (apply (Walk.error_iff _).mpr; trivial)))

/-- One message operation's walk, under each state-gas regime, as its own declaration. -/
local macro "done_message " name:ident " for " op:term : command =>
  `(private theorem $name (ctx : CallContext) (s : Frame.State) {a : Address}
      (h : a ∈ s.accessedAddresses) : DonePost a (MessageOp.step ctx s $op) := by
    simp only [MessageOp.step]
    split <;> apply ofExcept_donePost <;> done_walk)

done_message call_donePost for .call
done_message callcode_donePost for .callcode
done_message delegatecall_donePost for .delegatecall
done_message staticcall_donePost for .staticcall
done_message create_donePost for .create

private theorem create2_donePost (ctx : CallContext) (s : Frame.State) {a : Address}
    (h : a ∈ s.accessedAddresses) : DonePost a (MessageOp.step ctx s .create2) := by
  simp only [MessageOp.step]
  cases ctx.block.rules.opcodes.create2 with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; trivial
  | true =>
    simp only [↓reduceIte]
    split <;> apply ofExcept_donePost <;> done_walk

private theorem op_donePost (ctx : CallContext) (s : Frame.State) (op : Jaune.MessageOp) {a : Address}
    (h : a ∈ s.accessedAddresses) : DonePost a (MessageOp.step ctx s op) := by
  cases op with
  | call => exact call_donePost ctx s h
  | callcode => exact callcode_donePost ctx s h
  | delegatecall => exact delegatecall_donePost ctx s h
  | staticcall => exact staticcall_donePost ctx s h
  | create => exact create_donePost ctx s h
  | create2 => exact create2_donePost ctx s h

/-- A message instruction that finishes without opening a frame keeps every accessed address. -/
theorem MessageOp.step_done_accessedAddresses {ctx : CallContext} {s t : Frame.State}
    {x : Jaune.MessageOp} (h : MessageOp.step ctx s x = .done (.ok t)) {a : Address}
    (ha : a ∈ s.accessedAddresses) : a ∈ t.accessedAddresses := by
  have hp := op_donePost ctx s x ha
  rw [h] at hp
  exact hp

/-! ### One step and one resumption -/

/-- An instruction that goes on in the same frame keeps every accessed address. -/
theorem step_next_accessedAddresses {r : Frame.Running} {pc : Nat} {s : Frame.State}
    (h : step r = .ok (.next pc s)) {a : Address} (ha : a ∈ r.state.accessedAddresses) :
    a ∈ s.accessedAddresses := by
  have ofHalt : ∀ {pc' : Nat} {x : Except (ExceptionalHalt × Frame.State) Frame.State},
      Step.ofHalt pc' x = .next pc s → x = .ok s := by
    intro pc' x hx
    cases x with
    | error e => cases hx
    | ok t => cases hx; rfl
  unfold step at h
  split at h
  · cases h
  · rename_i n _
    have hn := Except.ok.inj h
    cases n with
    | plain op => exact Family.run_accessedAddresses (ofHalt hn) ha
    | push xs _ => exact Family.run_accessedAddresses (ofHalt hn) ha
    | dupn imm => exact Family.run_accessedAddresses (ofHalt hn) ha
    | swapn imm => exact Family.run_accessedAddresses (ofHalt hn) ha
    | exchange imm => exact Family.run_accessedAddresses (ofHalt hn) ha
    | message x =>
      simp only [NextOp.step] at hn
      cases hs : MessageOp.step r.context r.state x with
      | spawn f p => rw [hs] at hn; cases hn
      | done res =>
        rw [hs] at hn
        exact MessageOp.step_done_accessedAddresses (by rw [hs, ofHalt hn]) ha
  · rename_i j _
    have hj := Except.ok.inj h
    unfold Step.ofJump at hj
    split at hj
    · cases hj
    · rename_i r' hr
      cases hj
      exact JumpOp.run_accessedAddresses hr ha
  · rename_i l _
    cases he : HaltOp.run r.context r.state l <;> rw [he] at h <;> cases h

/-- A caller resumed after its child keeps every address accessed in its saved state: a
successful child's set is united into it, and a failed child leaves the saved set. -/
theorem resume_accessedAddresses {rules : ForkRules} {p : Pending} {saved t : Frame.State}
    {r : Frame.Result} (h : resume rules p saved r = .ok (.ok t)) {a : Address}
    (ha : a ∈ saved.accessedAddresses) : a ∈ t.accessedAddresses := by
  unfold resume at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals simp only [Except.ok.injEq, reduceCtorEq] at h
  all_goals subst h
  all_goals first
    | exact ha
    | (simp only [Substate.absorb, Std.HashSet.union_eq]; exact Std.HashSet.mem_union_of_left ha)

/-- A caller that goes on after a call keeps every address it had before the call. -/
theorem resumeCaller_accessedAddresses {r : Frame.Running} {child : Frame} {pending : Pending}
    {pc : Nat} {result : Except Fault Frame.Result} {s : Frame.State}
    (hs : step r = .ok (.spawn child pending pc))
    (hr : resumeCaller r.context.block.rules child pending result = .ok s) {a : Address}
    (ha : a ∈ r.state.accessedAddresses) : a ∈ s.accessedAddresses := by
  cases result with
  | error f => cases hr
  | ok v =>
    simp only [resumeCaller] at hr
    rcases he : resume r.context.block.rules pending child.checkpoint v with
      f | ⟨reason, t⟩ | t <;> rw [he] at hr
    · cases hr
    · cases hr
    · cases hr
      exact resume_accessedAddresses he (step_spawn_accessedAddresses hs ha)

/-! ### Over a run -/

namespace Frame.Run

private theorem eventsFrom_warm {r out} (t : Frame.Run r (.exit out)) (path kept frameStart enclosing counter)
    {a : Address} (ha : a ∈ r.state.accessedAddresses) :
    ∀ v, Event.visit v ∈ eventsFrom t path kept frameStart enclosing counter →
      a ∈ v.node.start.state.accessedAddresses := by
  intro v hv
  cases t with
  | halt =>
    simp only [eventsFrom, List.mem_singleton, Event.visit.injEq] at hv
    subst hv; exact ha
  | callDoneEnd =>
    simp only [eventsFrom, List.mem_singleton, Event.visit.injEq] at hv
    subst hv; exact ha
  | next hs rest =>
    rw [eventsFrom] at hv
    rcases List.mem_cons.mp hv with hv | hv
    · cases hv; exact ha
    · exact eventsFrom_warm rest _ _ _ _ _ (step_next_accessedAddresses hs ha) v hv
  | callDone hs he hr rest =>
    rw [eventsFrom] at hv
    rcases List.mem_cons.mp hv with hv | hv
    · cases hv; exact ha
    · exact eventsFrom_warm rest _ _ _ _ _ (resumeCaller_accessedAddresses hs hr ha) v hv
  | callRan hs he child hr rest =>
    rw [eventsFrom] at hv
    rcases List.mem_cons.mp hv with hv | hv
    · cases hv; exact ha
    · rcases List.mem_append.mp hv with hv | hv
      · exact eventsFrom_warm child _ _ _ _ _ (step_spawn_child_warm hs he ha) v hv
      · rcases List.mem_cons.mp hv with hv | hv
        · cases hv
        · exact eventsFrom_warm rest _ _ _ _ _ (resumeCaller_accessedAddresses hs hr ha) v hv
  | callRanEnd hs he child hr =>
    rw [eventsFrom] at hv
    rcases List.mem_cons.mp hv with hv | hv
    · cases hv; exact ha
    · rcases List.mem_append.mp hv with hv | hv
      · exact eventsFrom_warm child _ _ _ _ _ (step_spawn_child_warm hs he ha) v hv
      · simp at hv
termination_by sizeOf t

/-- Every address accessed when a run starts is accessed at every visit of the run, in every
frame, including frames inside subtrees that later revert. -/
theorem visits_warm {r out} (t : Frame.Run r (.exit out)) {a : Address}
    (ha : a ∈ r.state.accessedAddresses) {v : Visit} (hv : v ∈ visits t) :
    a ∈ v.node.start.state.accessedAddresses := by
  obtain ⟨e, he, hx⟩ := List.mem_filterMap.mp hv
  cases e with
  | exit _ => cases hx
  | visit w =>
    cases hx
    exact eventsFrom_warm t _ _ _ _ _ ha _ he

/-- Every frame a run enters starts with every address accessed when the run starts. -/
theorem frames_warm {r out} (t : Frame.Run r (.exit out)) {a : Address}
    (ha : a ∈ r.state.accessedAddresses) {n : Node} (hn : n ∈ frames t) :
    a ∈ n.start.state.accessedAddresses := by
  simp only [frames, List.mem_map, List.mem_filter] at hn
  obtain ⟨v, ⟨hv, _⟩, rfl⟩ := hn
  exact visits_warm t ha hv

/-- Every call of a run that ran started its child with every address accessed when the run
starts. -/
theorem calls_ran_warm {r out} (t : Frame.Run r (.exit out)) {a : Address}
    (ha : a ∈ r.state.accessedAddresses) {c : Call} {n : Node} (hc : c ∈ calls t)
    (hran : c.ran = some n) : a ∈ n.start.state.accessedAddresses := by
  apply frames_warm t ha
  rw [frames_eq_calls]
  exact List.mem_cons_of_mem _ (List.mem_filterMap.mpr ⟨c, hc, hran⟩)

end Frame.Run

/-! ### Over top-level roots and kept histories

The run facts need no premise, so the lifts need none: every frame of every top-level root a
kept history enters starts with every address accessed when its root started. -/

/-- Every frame a top-level root enters starts with every address accessed when the root
starts. -/
theorem Root.frames_warm (root : Root) {a : Address} (ha : a ∈ root.running.state.accessedAddresses)
    {n : Frame.Run.Node} (hn : n ∈ root.run.frames) : a ∈ n.start.state.accessedAddresses :=
  Frame.Run.frames_warm root.run ha hn

/-- In every block of a kept history, every frame a top-level root enters starts with every
address accessed when the root starts. -/
theorem KeptHistory.frames_warm (blocks : List KeptBlock) :
    ∀ block ∈ blocks, ∀ root ∈ block.run.roots, ∀ n ∈ root.run.frames,
      ∀ a ∈ root.running.state.accessedAddresses, a ∈ n.start.state.accessedAddresses :=
  fun _ _ root _ _ hn _ ha => root.frames_warm ha hn

/-- Every call of a kept history that ran started its child with every address accessed when
the top-level root it belongs to started. -/
theorem KeptHistory.calls_ran_warm {blocks : List KeptBlock} {c : Frame.Run.Call}
    (hc : c ∈ KeptHistory.calls blocks) :
    ∃ block ∈ blocks, ∃ root ∈ block.run.roots, c ∈ root.run.calls ∧
      ∀ n, c.ran = some n →
        ∀ a ∈ root.running.state.accessedAddresses, a ∈ n.start.state.accessedAddresses := by
  obtain ⟨block, hb, root, hr, hc⟩ := KeptHistory.mem_calls.mp hc
  exact ⟨block, hb, root, hr, hc, fun _ hran _ ha => Frame.Run.calls_ran_warm root.run ha hc hran⟩

end Jaune
