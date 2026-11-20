import Jaune.MessageCall.CheckedParts
import Jaune.MessageCall.CheckedMemoryAccounting
import Jaune.CheckedSufficiencyWalk

/-! Native spawn checkpoints and the child's call or creation kind. -/
namespace Jaune.Checked

open Jaune

private theorem push_done_noSpawn {s : Frame.State} {c : Frame} {p : Staging.Pending} :
    MessageOp.Outcome.ofExcept (do
      let t ← s.push 0
      return MessageOp.Outcome.done (.ok t)) ≠ .spawn c p := by
  cases s.push 0 <;> simp [MessageOp.Outcome.ofExcept, bind, Except.bind, pure, Except.pure]

/-- A successful CALL-family spawn carries a call message directed to its code address. -/
theorem genericCall.step_spawn_kind {ctx : CallContext} {s : Frame.State} {gas : Nat} {value : U256}
    {caller target codeAddress : Address} {transfer static : Bool} {ii il oi ol : Nat}
    {code : ByteArray} {disabled : Bool} {child : Frame} {p : Staging.Pending}
    (h : genericCall.step ctx s gas value caller target codeAddress transfer static ii il oi ol code
      disabled = .spawn child p) : child.message.kind = .call ∧ child.message.codeAddress = some codeAddress := by
  unfold genericCall.step at h
  split at h
  · exact absurd h push_done_noSpawn
  · cases h; exact ⟨rfl, rfl⟩

/-- The caller checkpoint and return window at a CALL-family spawn. -/
theorem genericCall.step_spawn_checkpoint {ctx : CallContext} {s : Frame.State} {gas : Nat} {value : U256}
    {caller target codeAddress : Address} {transfer static : Bool} {ii il oi ol : Nat}
    {code : ByteArray} {disabled : Bool} {child : Frame} {p : Staging.Pending}
    (h : genericCall.step ctx s gas value caller target codeAddress transfer static ii il oi ol code
      disabled = .spawn child p) :
    child.checkpoint = s.withReturnData [] ∧ p = ⟨.call oi ol, false⟩ ∧
      child.message.kind = .call ∧ child.message.codeAddress = some codeAddress :=
  ⟨(genericCall.step_spawn_call h).2.1, (genericCall.step_spawn_call h).2.2,
    genericCall.step_spawn_kind h⟩

/-- Under state gas the child starts from the cleared caller checkpoint and carries its output
window, gas reservoir, and new-account charge. -/
theorem genericCallAmsterdam.step_spawn_checkpoint {ctx : CallContext} {state : StateGasRules}
    {s : Frame.State} {gas reservoir : Nat} {value : U256} {caller target codeAddress : Address}
    {transfer static : Bool} {ii il oi ol : Nat} {code : ByteArray} {disabled charged insufficient : Bool}
    {child : Frame} {p : Staging.Pending} (h : genericCallAmsterdam.step ctx state s gas reservoir value
      caller target codeAddress transfer static ii il oi ol code disabled charged insufficient = .spawn child p) :
    child.checkpoint = s.withReturnData [] ∧ p = ⟨.call oi ol, charged⟩ ∧
      child.message.kind = .call ∧ child.message.codeAddress = some codeAddress ∧
      child.message.context.block = ctx.block ∧ child.message.context.tx = ctx.tx ∧
      child.message.stateGasGrant = reservoir := by
  unfold genericCallAmsterdam.step at h
  split at h
  · exact absurd h push_done_noSpawn
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The legacy creation checkpoint carries the withheld child grant, cleared return data,
incremented creator nonce and warm destination. -/
theorem genericCreate.step_spawn_checkpoint {ctx : CallContext} {s : Frame.State} {value : U256}
    {a : Address} {i len : Nat} {child : Frame} {p : Staging.Pending}
    (h : genericCreate.step ctx s value a i len = .spawn child p) :
    child.checkpoint = (((s.withGasLeft (s.gasLeft - except64th s.gasLeft)).withReturnData
        []).incrNonce ctx.recipient).addAccessedAddress a ∧ p = ⟨.create a, false⟩ ∧
      child.message.kind = .create ∧ child.message.codeAddress = none ∧ child.message.context.recipient = a ∧
      child.message.context.block = ctx.block ∧ child.message.context.tx = ctx.tx := by
  simp only [genericCreate.step, bind, Except.bind, pure, Except.pure, Except.assert,
    Frame.State.assertDynamic] at h
  repeat' split at h
  all_goals simp only [MessageOp.Outcome.ofExcept, MessageOp.Outcome.spawn.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem chargeStateGas_substate {s t : Frame.State} {n : Nat} (h : s.chargeStateGas n = .ok t) :
    t.substate = s.substate := by
  unfold Frame.State.chargeStateGas Frame.State.liftMachine at h
  cases hc : s.machine.chargeStateGas n with
  | error pair => rw [hc] at h; contradiction
  | ok m => rw [hc] at h; cases h; rfl

/-- Amsterdam withholds child gas and drains the reservoir from the charged caller. Its
checkpoint increments the nonce, and the creation destination remains warm. -/
theorem genericCreateAmsterdam.step_spawn_checkpoint {ctx : CallContext} {rules : StateGasRules}
    {s : Frame.State} {value : U256} {a : Address} {i len : Nat} {child : Frame} {p : Staging.Pending}
    (h : genericCreateAmsterdam.step ctx rules s value a i len = .spawn child p) :
    let caller := (s.withReturnData []).recordAccountRead ctx.block.rules ctx.recipient
    let accessed := (caller.addAccessedAddress a).recordAccountRead ctx.block.rules a
    (∃ t : Frame.State, (if (accessed.account a).isEmpty then accessed.chargeStateGas rules.newAccount else .ok accessed) = .ok t ∧
      child.checkpoint = t.withholdCreateGas.2.drainStateGasReservoir.2.incrNonce ctx.recipient) ∧
    a ∈ child.checkpoint.accessedAddresses ∧ p.target = .create a ∧
    child.message.kind = .create ∧ child.message.codeAddress = none ∧ child.message.context.recipient = a ∧
    child.message.context.block = ctx.block ∧ child.message.context.tx = ctx.tx := by
  simp only [genericCreateAmsterdam.step, bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals simp only [MessageOp.Outcome.ofExcept, MessageOp.Outcome.spawn.injEq, reduceCtorEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals refine ⟨?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  all_goals first
    | (refine ⟨_, ?_, rfl⟩; split <;> first | assumption | rfl | contradiction)
    | (rename_i t hc _
       change a ∈ t.substate.accessedAddresses
       rw [chargeStateGas_substate hc]
       exact (Std.HashSet.mem_insert_self : a ∈ (_ : AdrSet).insert a))
    | exact (Std.HashSet.mem_insert_self : a ∈ (_ : AdrSet).insert a)

private def SpawnShape (ctx : CallContext) (f : Frame) : Prop :=
  f.message.context.block = ctx.block ∧ f.message.context.tx = ctx.tx ∧
    ((f.message.kind = .call ∧ (∃ a, f.message.codeAddress = some a) ∧
      ∃ s : Frame.State, f.checkpoint = s.withReturnData []) ∨
      (f.message.kind = .create ∧ f.message.codeAddress = none ∧
        f.message.context.recipient ∈ f.checkpoint.accessedAddresses))

private theorem callShape {ctx s gas value caller target addr transfer static ii il oi ol code disabled f p}
    (h : genericCall.step ctx s gas value caller target addr transfer static ii il oi ol code disabled =
      .spawn f p) : SpawnShape ctx f := by
  obtain ⟨hcp, _, hk, ha⟩ := genericCall.step_spawn_checkpoint h
  obtain ⟨hb, ht⟩ := genericCall.step_spawn_context h
  exact ⟨hb, ht, .inl ⟨hk, ⟨_, ha⟩, ⟨s, hcp⟩⟩⟩

private theorem callStateShape {ctx rules s gas reservoir value caller target addr transfer static
    ii il oi ol code disabled charged insufficient f p}
    (h : genericCallAmsterdam.step ctx rules s gas reservoir value caller target addr transfer static ii il oi ol
      code disabled charged insufficient = .spawn f p) : SpawnShape ctx f := by
  obtain ⟨hcp, _, hk, ha, hb, ht, _⟩ := genericCallAmsterdam.step_spawn_checkpoint h
  exact ⟨hb, ht, .inl ⟨hk, ⟨_, ha⟩, ⟨s, hcp⟩⟩⟩

private theorem createShape {ctx s value a i len f p}
    (h : genericCreate.step ctx s value a i len = .spawn f p) : SpawnShape ctx f := by
  obtain ⟨hcp, _, hk, ha, hr, hb, ht⟩ := genericCreate.step_spawn_checkpoint h
  refine ⟨hb, ht, .inr ⟨hk, ha, ?_⟩⟩
  rw [hr, hcp]
  exact Std.HashSet.mem_insert_self

private theorem createStateShape {ctx rules s value a i len f p}
    (h : genericCreateAmsterdam.step ctx rules s value a i len = .spawn f p) : SpawnShape ctx f := by
  obtain ⟨_, hw, _, hk, ha, hr, hb, ht⟩ := genericCreateAmsterdam.step_spawn_checkpoint h
  exact ⟨hb, ht, .inr ⟨hk, ha, hr.symm ▸ hw⟩⟩

/-- Bound operations that fail cannot spawn. Their successful branches can be checked at the
tail, independently of the intermediate stack words and charges. -/
private theorem walkAny {α β : Type} {P : β → Prop} {x : Except (ExceptionalHalt × Frame.State) α}
    {k : α → Except (ExceptionalHalt × Frame.State) β}
    (h : ∀ a, Walk (fun _ => True) P (k a)) : Walk (fun _ => True) P (x >>= k) := by
  cases x with
  | error e => trivial
  | ok a => exact h a

private def spawnPost (ctx : CallContext) : MessageOp.Outcome → Prop
  | .done _ => True
  | .spawn f _ => SpawnShape ctx f

private theorem ofExcept_spawnPost {ctx : CallContext} {x : Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hx : Walk (fun _ => True) (spawnPost ctx) x) : spawnPost ctx (MessageOp.Outcome.ofExcept x) := by
  cases x with
  | error p => trivial
  | ok o => exact hx

private theorem tail_spawnPost {ctx : CallContext} {o : MessageOp.Outcome}
    (h : ∀ f p, o = .spawn f p → SpawnShape ctx f) : spawnPost ctx o := by
  cases o with
  | done r => trivial
  | spawn f p => exact h f p rfl

private theorem purePost {ctx : CallContext} (o : MessageOp.Outcome) (h : spawnPost ctx o) :
    Walk (ε := ExceptionalHalt) (fun _ => True) (spawnPost ctx) (pure o) := h

local macro "spawn_tail" : tactic => `(tactic|
  first | (apply tail_spawnPost; exact fun _ _ h => callShape h)
        | (apply tail_spawnPost; exact fun _ _ h => callStateShape h)
        | (apply tail_spawnPost; exact fun _ _ h => createShape h)
        | (apply tail_spawnPost; exact fun _ _ h => createStateShape h))

local macro "spawn_walk" : tactic => `(tactic| repeat' (first
  | (with_reducible apply walkAny; intro a; try (guard_hyp a : _ × _; rcases a with ⟨_, _⟩); try dsimp only)
  | (apply purePost; first | exact True.intro | spawn_tail)
  | (apply (Walk.error_iff _).mpr; trivial)
  | spawn_tail
  | split
  | trivial))

private theorem op_spawn_post (ctx : CallContext) (s : Frame.State) (op : Jaune.MessageOp) :
    spawnPost ctx (MessageOp.step ctx s op) := by
  cases op <;> simp only [MessageOp.step]
  all_goals repeat' split
  all_goals apply ofExcept_spawnPost; spawn_walk

theorem MessageOp.step_spawn_cases {ctx : CallContext} {s : Frame.State} {x : Jaune.MessageOp}
    {child : Frame} {p : Staging.Pending} (h : MessageOp.step ctx s x = .spawn child p) :
    (child.message.kind = .call ∧ ∃ a, child.message.codeAddress = some a) ∨
      (child.message.kind = .create ∧ child.message.codeAddress = none ∧
        child.message.context.recipient ∈ child.checkpoint.accessedAddresses) := by
  have shape := op_spawn_post ctx s x
  rw [h] at shape
  rcases shape.2.2 with ⟨hk, ha, _⟩ | hc
  · exact .inl ⟨hk, ha⟩
  · exact .inr hc

theorem MessageOp.step_spawn_call_checkpoint {ctx : CallContext} {s : Frame.State} {x : Jaune.MessageOp}
    {child : Frame} {p : Staging.Pending} (h : MessageOp.step ctx s x = .spawn child p)
    (hk : child.message.kind = .call) :
    ∃ post : Frame.State, child.checkpoint = post.withReturnData [] := by
  have shape := op_spawn_post ctx s x
  rw [h] at shape
  rcases shape.2.2 with ⟨_, _, hc⟩ | ⟨hc, _⟩
  · exact hc
  · rw [hk] at hc; cases hc

theorem MessageOp.step_spawn_context {ctx : CallContext} {s : Frame.State} {x : Jaune.MessageOp}
    {child : Frame} {p : Staging.Pending} (h : MessageOp.step ctx s x = .spawn child p) :
    child.message.context.block = ctx.block ∧ child.message.context.tx = ctx.tx := by
  have shape := op_spawn_post ctx s x
  rw [h] at shape
  exact ⟨shape.1, shape.2.1⟩

/-- Proposed replacement of row 41. A CREATE-family spawn hands the parent's block and transaction
records to the child frame. -/
theorem genericCreate.step_spawn_context {ctx : CallContext} {s : Frame.State} {value : U256}
    {a : Address} {i len : Nat} {child : Frame} {p : Staging.Pending}
    (h : genericCreate.step ctx s value a i len = .spawn child p) :
    child.message.context.block = ctx.block ∧ child.message.context.tx = ctx.tx :=
  let ⟨_, _, _, _, _, hb, ht⟩ := genericCreate.step_spawn_checkpoint h
  ⟨hb, ht⟩

/-- Proposed replacement of rows 38 and 39. Entering a frame runs it under its message's whole
call context. -/
theorem Frame.enter_run_context {f : Frame} {r : Frame.Running} (h : enter f = .run r) :
    r.context = f.message.context := by
  unfold enter enterWith at h
  rcases ht : f.message.transfer f.enteredWorld with fault | world <;> simp only [ht] at h
  · cases h
  · rcases hc : f.message.codeAddress with _ | address <;> simp only [hc] at h
    · cases h; rfl
    · split at h
      · cases h
      · cases h; rfl

private theorem ofHalt_ne_spawn (pc : Nat) (x : Except (ExceptionalHalt × Frame.State) Frame.State)
    (child : Frame) (p : Staging.Pending) (dest : Nat) : Step.ofHalt pc x ≠ .spawn child p dest := by
  cases x <;> intro h <;> cases h

theorem step_spawn_message {r : Frame.Running} {child : Frame} {p : Staging.Pending} {pc : Nat}
    (h : step r = .ok (.spawn child p pc)) : ∃ x, MessageOp.step r.context r.state x = .spawn child p := by
  unfold step at h
  split at h
  · cases h
  · rename_i n _
    have ho := Except.ok.inj h
    cases n with
    | message x =>
      refine ⟨x, ?_⟩
      simp only [NextOp.step] at ho
      cases hs : MessageOp.step r.context r.state x with
      | done result => rw [hs] at ho; exact absurd ho (ofHalt_ne_spawn _ _ _ _ _)
      | spawn f pend => rw [hs] at ho; cases ho; rfl
    | _ => exact absurd ho (ofHalt_ne_spawn _ _ _ _ _)
  · simp only [Step.ofJump] at h; split at h <;> cases h
  · rename_i op _
    cases he : HaltOp.run r.context r.state op <;> rw [he] at h <;> cases h

/-- Creation messages have no code address and call messages have one. -/
def Message.KindCoherent (m : Message) : Prop :=
  m.kind = .create ↔ m.codeAddress = none

theorem Message.kindCoherent_call {m : Message} (hk : m.kind = .call) (a : Address)
    (ha : m.codeAddress = some a) : m.KindCoherent := by
  unfold Message.KindCoherent; rw [hk, ha]; simp

theorem Message.kindCoherent_create {m : Message} (hk : m.kind = .create)
    (ha : m.codeAddress = none) : m.KindCoherent := by
  unfold Message.KindCoherent; rw [hk, ha]; simp

theorem step_spawn_kindCoherent {r : Frame.Running} {child : Frame} {p : Staging.Pending} {pc : Nat}
    (h : step r = .ok (.spawn child p pc)) : child.message.KindCoherent := by
  obtain ⟨_, hx⟩ := step_spawn_message h
  rcases MessageOp.step_spawn_cases hx with ⟨hk, a, ha⟩ | ⟨hk, ha, _⟩
  · exact Message.kindCoherent_call hk a ha
  · exact Message.kindCoherent_create hk ha

theorem step_spawn_create_warm {r : Frame.Running} {child : Frame} {p : Staging.Pending} {pc : Nat}
    (h : step r = .ok (.spawn child p pc)) (hk : child.message.kind = .create) :
    child.message.context.recipient ∈ child.checkpoint.accessedAddresses := by
  obtain ⟨_, hx⟩ := step_spawn_message h
  rcases MessageOp.step_spawn_cases hx with ⟨hcall, _⟩ | ⟨_, _, hw⟩
  · rw [hk] at hcall; cases hcall
  · exact hw

/-! ### Accessed-address growth through spawns and frame entry -/

private def AccGrow (pre post : Frame.State) : Prop :=
  ∀ a, a ∈ pre.accessedAddresses → a ∈ post.accessedAddresses

private theorem AccGrow.rfl {s : Frame.State} : AccGrow s s := fun _ h => h

private theorem AccGrow.trans {s₁ s₂ s₃ : Frame.State}
    (h₁ : AccGrow s₁ s₂) (h₂ : AccGrow s₂ s₃) : AccGrow s₁ s₃ :=
  fun a ha => h₂ a (h₁ a ha)

private theorem AccGrow.of_substate_eq {s₁ s₂ : Frame.State}
    (h : s₂.substate = s₁.substate) : AccGrow s₁ s₂ := by
  intro a ha
  change a ∈ s₂.substate.accessedAddresses
  rw [h]
  exact ha

private theorem AccGrow.addAccessedAddress (s : Frame.State) (x : Address) :
    AccGrow s (s.addAccessedAddress x) := by
  intro a ha
  exact Std.HashSet.mem_insert.2 (Or.inr ha)

private theorem AccGrow.accessDelegation (rules : ForkRules) (s : Frame.State) (x : Address) :
    AccGrow s (ForkRules.accessDelegation rules s x).2.2.2.2 := by
  unfold ForkRules.accessDelegation
  cases rules.delegationEnabled with
  | false => simp only [Bool.false_eq_true, ↓reduceIte]; exact AccGrow.rfl
  | true =>
    unfold GasSchedule.accessDelegation
    dsimp only
    cases getDelegatedCodeAddress (s.code x) with
    | none => exact AccGrow.rfl
    | some adr => exact AccGrow.addAccessedAddress s adr

private theorem AccGrow.completeDelegation (s : Frame.State) (d : Bool) (x : Address) :
    AccGrow s (completeDelegationAccess s d x).2 := by
  cases d with
  | false => exact AccGrow.rfl
  | true => exact AccGrow.addAccessedAddress s x

private theorem AccGrow.accessRule (acc : AccessSchedule) (s : Frame.State) (x : Address) :
    AccGrow s (match acc with | .eip2929 => s.addAccessedAddress x | .flat _ => s) := by
  cases acc with
  | flat _ => exact AccGrow.rfl
  | eip2929 => exact AccGrow.addAccessedAddress s x

private theorem AccGrow.trans_substate {s0 s1 s2 : Frame.State}
    (h1 : AccGrow s0 s1) (h2 : s2.substate = s1.substate) : AccGrow s0 s2 :=
  h1.trans (AccGrow.of_substate_eq h2)

private theorem AccGrow.trans_substate_add {s0 s1 s2 : Frame.State} {x : Address}
    (h1 : AccGrow s0 s1) (h2 : s2.substate = (s1.addAccessedAddress x).substate) :
    AccGrow s0 s2 :=
  (h1.trans (AccGrow.addAccessedAddress _ _)).trans (AccGrow.of_substate_eq h2)

private theorem AccGrow.trans_accessDelegation {s0 s : Frame.State} {rules : ForkRules}
    {x : Address} (h : AccGrow s0 s) :
    AccGrow s0 (ForkRules.accessDelegation rules s x).2.2.2.2 :=
  h.trans (AccGrow.accessDelegation _ _ _)

private theorem AccGrow.trans_completeDelegation {s0 s : Frame.State} {d : Bool} {x : Address}
    (h : AccGrow s0 s) : AccGrow s0 (completeDelegationAccess s d x).2 :=
  h.trans (AccGrow.completeDelegation _ _ _)

private theorem AccGrow.trans_accessRule {s0 s : Frame.State} {acc : AccessSchedule}
    {x : Address} (h : AccGrow s0 s) :
    AccGrow s0 (match acc with | .eip2929 => s.addAccessedAddress x | .flat _ => s) :=
  h.trans (AccGrow.accessRule _ _ _)

private theorem callAccGrow {ctx s gas value caller target addr transfer static ii il oi ol code
    disabled f p}
    (h : genericCall.step ctx s gas value caller target addr transfer static ii il oi ol code
      disabled = .spawn f p) : AccGrow s f.checkpoint := by
  obtain ⟨hcp, _, _⟩ := genericCall.step_spawn_checkpoint h
  exact AccGrow.of_substate_eq (by rw [hcp]; rfl)

private theorem callStateAccGrow {ctx rules s gas reservoir value caller target addr transfer static
    ii il oi ol code disabled charged insufficient f p}
    (h : genericCallAmsterdam.step ctx rules s gas reservoir value caller target addr transfer static
      ii il oi ol code disabled charged insufficient = .spawn f p) : AccGrow s f.checkpoint := by
  obtain ⟨hcp, _, _⟩ := genericCallAmsterdam.step_spawn_checkpoint h
  exact AccGrow.of_substate_eq (by rw [hcp]; rfl)

private theorem createAccGrow {ctx s value a i len f p}
    (h : genericCreate.step ctx s value a i len = .spawn f p) : AccGrow s f.checkpoint := by
  obtain ⟨hcp, _, _⟩ := genericCreate.step_spawn_checkpoint h
  have h1 : AccGrow s (((s.withGasLeft (s.gasLeft - except64th s.gasLeft)).withReturnData
      []).incrNonce ctx.recipient) := AccGrow.of_substate_eq rfl
  have h2 := h1.trans (AccGrow.addAccessedAddress _ a)
  rw [← hcp] at h2
  exact h2

private theorem createStateAccGrow {ctx rules s value a i len f p}
    (h : genericCreateAmsterdam.step ctx rules s value a i len = .spawn f p) :
    AccGrow s f.checkpoint := by
  obtain ⟨⟨t, hif, hcp⟩, _⟩ := genericCreateAmsterdam.step_spawn_checkpoint h
  let caller := (s.withReturnData []).recordAccountRead ctx.block.rules ctx.recipient
  let accessed := (caller.addAccessedAddress a).recordAccountRead ctx.block.rules a
  have h1 : AccGrow s caller := AccGrow.of_substate_eq rfl
  have h2 : AccGrow caller accessed :=
    (AccGrow.addAccessedAddress caller a).trans (AccGrow.of_substate_eq rfl)
  have hsub : t.substate = accessed.substate := by
    split at hif
    · exact chargeStateGas_substate hif
    · cases hif; rfl
  exact (h1.trans h2).trans (AccGrow.of_substate_eq (by rw [hcp]; exact hsub))

private def spawnAccPost (s0 : Frame.State) : MessageOp.Outcome → Prop
  | .done _ => True
  | .spawn f _ => AccGrow s0 f.checkpoint

private theorem ofExcept_spawnAccPost {s0 : Frame.State}
    {x : Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hx : Walk (fun _ => True) (spawnAccPost s0) x) :
    spawnAccPost s0 (MessageOp.Outcome.ofExcept x) := by
  cases x with
  | error _ => trivial
  | ok _ => exact hx

private theorem tail_spawnAccPost {s0 : Frame.State} {o : MessageOp.Outcome}
    (h : ∀ f p, o = .spawn f p → AccGrow s0 f.checkpoint) : spawnAccPost s0 o := by
  cases o with
  | done _ => trivial
  | spawn f p => exact h f p rfl

private theorem pureAccPost {s0 : Frame.State} {o : MessageOp.Outcome} (h : spawnAccPost s0 o) :
    Walk (ε := ExceptionalHalt) (fun _ => True) (spawnAccPost s0) (pure o) := h

private theorem walk_liftMachineValue {α : Type} {s0 s : Frame.State}
    {core : Machine → Except (ExceptionalHalt × Machine) (α × Machine)}
    {k : α × Frame.State → Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hs : AccGrow s0 s)
    (hk : ∀ a s', AccGrow s0 s' → Walk (fun _ => True) (spawnAccPost s0) (k (a, s'))) :
    Walk (fun _ => True) (spawnAccPost s0) (s.liftMachineValue core >>= k) := by
  unfold Frame.State.liftMachineValue
  cases hc : core s.machine with
  | error _ => trivial
  | ok p => exact hk p.1 (s.withMachine p.2) hs

private theorem walk_liftMachine {s0 s : Frame.State}
    {core : Machine → Except (ExceptionalHalt × Machine) Machine}
    {k : Frame.State → Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hs : AccGrow s0 s)
    (hk : ∀ s', AccGrow s0 s' → Walk (fun _ => True) (spawnAccPost s0) (k s')) :
    Walk (fun _ => True) (spawnAccPost s0) (s.liftMachine core >>= k) := by
  unfold Frame.State.liftMachine
  cases hc : core s.machine with
  | error _ => trivial
  | ok m => exact hk (s.withMachine m) hs

private theorem walk_pop {s0 s : Frame.State}
    {k : U256 × Frame.State → Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hs : AccGrow s0 s)
    (hk : ∀ a s', AccGrow s0 s' → Walk (fun _ => True) (spawnAccPost s0) (k (a, s'))) :
    Walk (fun _ => True) (spawnAccPost s0) (s.pop >>= k) :=
  walk_liftMachineValue hs hk

private theorem walk_popToNat {s0 s : Frame.State}
    {k : Nat × Frame.State → Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hs : AccGrow s0 s)
    (hk : ∀ a s', AccGrow s0 s' → Walk (fun _ => True) (spawnAccPost s0) (k (a, s'))) :
    Walk (fun _ => True) (spawnAccPost s0) (s.popToNat >>= k) :=
  walk_liftMachineValue hs hk

private theorem walk_popToAddress {s0 s : Frame.State}
    {k : Address × Frame.State → Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hs : AccGrow s0 s)
    (hk : ∀ a s', AccGrow s0 s' → Walk (fun _ => True) (spawnAccPost s0) (k (a, s'))) :
    Walk (fun _ => True) (spawnAccPost s0) (s.popToAddress >>= k) :=
  walk_liftMachineValue hs hk

private theorem walk_chargeGas {s0 s : Frame.State} {cost : Nat}
    {k : Frame.State → Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hs : AccGrow s0 s)
    (hk : ∀ s', AccGrow s0 s' → Walk (fun _ => True) (spawnAccPost s0) (k s')) :
    Walk (fun _ => True) (spawnAccPost s0) (s.chargeGas cost >>= k) :=
  walk_liftMachine hs hk

private theorem walk_chargeStateGas {s0 s : Frame.State} {amount : Nat}
    {k : Frame.State → Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hs : AccGrow s0 s)
    (hk : ∀ s', AccGrow s0 s' → Walk (fun _ => True) (spawnAccPost s0) (k s')) :
    Walk (fun _ => True) (spawnAccPost s0) (s.chargeStateGas amount >>= k) :=
  walk_liftMachine hs hk

private theorem walk_push {s0 s : Frame.State} {x : U256}
    {k : Frame.State → Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hs : AccGrow s0 s)
    (hk : ∀ s', AccGrow s0 s' → Walk (fun _ => True) (spawnAccPost s0) (k s')) :
    Walk (fun _ => True) (spawnAccPost s0) (s.push x >>= k) :=
  walk_liftMachine hs hk

private theorem walk_assert {s0 : Frame.State} {p : Prop} [Decidable p]
    {e : ExceptionalHalt × Frame.State}
    {k : Unit → Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hk : Walk (fun _ => True) (spawnAccPost s0) (k ())) :
    Walk (fun _ => True) (spawnAccPost s0) (Except.assert p e >>= k) := by
  unfold Except.assert
  split
  · exact hk
  · trivial

private theorem walk_assertDynamic {s0 s : Frame.State} {ctx : CallContext}
    {k : Unit → Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hk : Walk (fun _ => True) (spawnAccPost s0) (k ())) :
    Walk (fun _ => True) (spawnAccPost s0) (s.assertDynamic ctx >>= k) :=
  walk_assert hk

private theorem walk_ok {s0 s : Frame.State}
    {k : Frame.State → Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (hs : AccGrow s0 s)
    (hk : ∀ s', AccGrow s0 s' → Walk (fun _ => True) (spawnAccPost s0) (k s')) :
    Walk (fun _ => True) (spawnAccPost s0) (Except.ok s >>= k) :=
  hk s hs

private theorem walk_ite {s0 : Frame.State} {c : Prop} [Decidable c]
    {t e : Except (ExceptionalHalt × Frame.State) MessageOp.Outcome}
    (ht : Walk (fun _ => True) (spawnAccPost s0) t)
    (he : Walk (fun _ => True) (spawnAccPost s0) e) :
    Walk (fun _ => True) (spawnAccPost s0) (if c then t else e) := by
  split
  · exact ht
  · exact he

local macro "spawn_acc_tail" : tactic => `(tactic| first
  | (apply tail_spawnAccPost;
     exact fun _ _ h => AccGrow.trans (AccGrow.trans_substate (by assumption) _root_.rfl) (callAccGrow h))
  | (apply tail_spawnAccPost;
     exact fun _ _ h => AccGrow.trans (AccGrow.trans_substate (by assumption) _root_.rfl) (callStateAccGrow h))
  | (apply tail_spawnAccPost;
     exact fun _ _ h => AccGrow.trans (AccGrow.trans_substate (by assumption) _root_.rfl) (createAccGrow h))
  | (apply tail_spawnAccPost;
     exact fun _ _ h => AccGrow.trans (AccGrow.trans_substate (by assumption) _root_.rfl) (createStateAccGrow h)))

local macro "spawn_acc_walk" : tactic => `(tactic| repeat' (first
  | apply walk_ite
  | (apply walk_pop; (solve | exact AccGrow.rfl | assumption); intro _ _ _; try dsimp only)
  | (apply walk_popToNat; (solve | exact AccGrow.rfl | assumption); intro _ _ _; try dsimp only)
  | (apply walk_popToAddress; (solve | exact AccGrow.rfl | assumption); intro _ _ _; try dsimp only)
  | (apply walk_chargeGas; (solve
      | exact AccGrow.rfl
      | assumption
      | (with_reducible apply AccGrow.trans_completeDelegation;
         exact AccGrow.trans_substate_add (by assumption) _root_.rfl)
      | (apply AccGrow.trans_accessDelegation;
         apply AccGrow.trans_accessRule;
         assumption)); intro _ _; try dsimp only)
  | (apply walk_chargeStateGas; (solve | exact AccGrow.rfl | assumption); intro _ _; try dsimp only)
  | (apply walk_ok; (solve | exact AccGrow.rfl | assumption); intro _ _; try dsimp only)
  | (apply walk_push; (solve
      | exact AccGrow.rfl
      | assumption
      | exact AccGrow.trans_substate (by assumption) _root_.rfl); intro _ _; try dsimp only)
  | (apply walk_assert; try dsimp only)
  | (apply walk_assertDynamic; try dsimp only)
  | (apply pureAccPost; first | exact True.intro | spawn_acc_tail)
  | (apply (Walk.error_iff _).mpr; trivial)
  | trivial))

private theorem op_spawn_accGrow (ctx : CallContext) (s0 : Frame.State) (op : Jaune.MessageOp) :
    spawnAccPost s0 (MessageOp.step ctx s0 op) := by
  cases op with
  | create2 =>
    simp only [MessageOp.step]
    cases ctx.block.rules.opcodes.create2 with
    | false => simp only [Bool.false_eq_true, ↓reduceIte]; trivial
    | true =>
      simp only [↓reduceIte]
      split <;> apply ofExcept_spawnAccPost <;> spawn_acc_walk
  | _ =>
    simp only [MessageOp.step]
    split <;> apply ofExcept_spawnAccPost <;> spawn_acc_walk

/-- A child frame's start state inherits the checkpoint's accessed addresses. -/
theorem Frame.startState_accessedAddresses (f : Frame) :
    f.startState.accessedAddresses = f.checkpoint.accessedAddresses := rfl

/-- Entering a frame preserves the checkpoint's accessed addresses on the running child. -/
theorem Frame.enter_run_accessedAddresses {f : Frame} {r : Frame.Running} (h : enter f = .run r) :
    r.state.accessedAddresses = f.checkpoint.accessedAddresses := by
  unfold enter enterWith at h
  rcases ht : f.message.transfer f.enteredWorld with fault | world <;> simp only [ht] at h
  · cases h
  · rcases hc : f.message.codeAddress with _ | address <;> simp only [hc] at h
    · cases h; rfl
    · split at h
      · cases h
      · cases h; rfl

/-- Any spawned message operation (call or creation, on every fork) preserves the caller's
accessed addresses into the child checkpoint. -/
theorem MessageOp.step_spawn_accessedAddresses {ctx : CallContext} {s : Frame.State}
    {x : Jaune.MessageOp} {child : Frame} {p : Staging.Pending} {a : Address}
    (h : MessageOp.step ctx s x = .spawn child p) (ha : a ∈ s.accessedAddresses) :
    a ∈ child.checkpoint.accessedAddresses := by
  have hg := op_spawn_accGrow ctx s x
  rw [h] at hg
  exact hg a ha

/-- A spawning step preserves the parent's accessed addresses into the child checkpoint. -/
theorem step_spawn_accessedAddresses {r : Frame.Running} {child : Frame} {p : Staging.Pending}
    {pc : Nat} {a : Address} (h : step r = .ok (.spawn child p pc))
    (ha : a ∈ r.state.accessedAddresses) : a ∈ child.checkpoint.accessedAddresses := by
  obtain ⟨_, hx⟩ := step_spawn_message h
  exact MessageOp.step_spawn_accessedAddresses hx ha

/-- A spawning step preserves the parent's accessed addresses into the child's start state. -/
theorem step_spawn_start_warm {r : Frame.Running} {child : Frame} {p : Staging.Pending}
    {pc : Nat} {a : Address} (h : step r = .ok (.spawn child p pc))
    (ha : a ∈ r.state.accessedAddresses) : a ∈ child.startState.accessedAddresses := by
  rw [Frame.startState_accessedAddresses]
  exact step_spawn_accessedAddresses h ha

/-- A child entered from a spawning step starts with every address warm in its parent
(call and create, all forks). -/
theorem step_spawn_child_warm {r childRunning : Frame.Running} {child : Frame}
    {p : Staging.Pending} {pc : Nat} {a : Address}
    (hstep : step r = .ok (.spawn child p pc)) (henter : enter child = .run childRunning)
    (ha : a ∈ r.state.accessedAddresses) : a ∈ childRunning.state.accessedAddresses := by
  rw [Frame.enter_run_accessedAddresses henter]
  exact step_spawn_accessedAddresses hstep ha

/-- A creation child entered from a spawning step starts with its recipient address warm. -/
theorem step_spawn_create_enter_warm {r childRunning : Frame.Running} {child : Frame}
    {p : Staging.Pending} {pc : Nat}
    (hstep : step r = .ok (.spawn child p pc)) (hk : child.message.kind = .create)
    (henter : enter child = .run childRunning) :
    childRunning.context.recipient ∈ childRunning.state.accessedAddresses := by
  rw [Frame.enter_run_context henter, Frame.enter_run_accessedAddresses henter]
  exact step_spawn_create_warm hstep hk

/-- A child entered from a spawning step inherits the parent's block and transaction context. -/
theorem step_spawn_enter_context {r childRunning : Frame.Running} {child : Frame}
    {p : Staging.Pending} {pc : Nat}
    (hstep : step r = .ok (.spawn child p pc)) (henter : enter child = .run childRunning) :
    childRunning.context.block = r.context.block ∧ childRunning.context.tx = r.context.tx := by
  obtain ⟨_, hx⟩ := step_spawn_message hstep
  rw [Frame.enter_run_context henter]
  exact MessageOp.step_spawn_context hx

/-! ### The prepared transaction frame -/




end Jaune.Checked
