import Jaune.MessageCall.CheckedParts
import Jaune.MessageCall.CheckedMemoryAccounting
import Jaune.CheckedSufficiencyWalk
import Jaune.MessageCall.SpawnFacts
import Jaune.Run.Message

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

/-! ### The prepared transaction frame -/

/-- A prepared creation keeps its code address and a prepared call has one. -/
theorem prepareTopLevelAmsterdam_message {state : StateGasRules} {msg : Msg} {p : Msg × Devm}
    (h : Staging.prepareTopLevelAmsterdam state msg = .ok p) :
    p.1.target = msg.target ∧ (msg.target = none → p.1.codeAddress = msg.codeAddress) ∧
      (msg.target ≠ none → p.1.codeAddress ≠ none) := by
  have hcall : ∀ {d : Devm} {p : Msg × Devm}, Staging.resolveTopLevelCallAmsterdam msg d = .ok p →
      p.1.target = msg.target ∧ p.1.codeAddress ≠ none := by
    intro d p hc
    unfold Staging.resolveTopLevelCallAmsterdam at hc
    obtain ⟨d1, h1, hc⟩ := Except.bind_eq_ok hc
    cases hc
    exact ⟨rfl, by simp⟩
  have key : ∀ d1, Staging.finishTopLevelAmsterdam state msg d1 = .ok p →
      p.1.target = msg.target ∧ (msg.target = none → p.1.codeAddress = msg.codeAddress) ∧
        (msg.target ≠ none → p.1.codeAddress ≠ none) := by
    intro d1 h
    unfold Staging.finishTopLevelAmsterdam Staging.dispatchTopLevelAmsterdam at h
    generalize (if msg.tenv.stat.auths.isEmpty then d1 else d1.commitStateGas) = d2 at h
    dsimp only at h
    split at h
    · rename_i hnone
      have ht : msg.target = none := Option.isNone_iff_eq_none.mp hnone
      split at h
      · simp only [reduceCtorEq] at h
      · split at h <;> obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h <;> cases h <;>
          exact ⟨rfl, fun _ => rfl, fun hne => absurd ht hne⟩
    · rename_i hsome
      have ht : msg.target ≠ none := fun e => hsome (by simp [e])
      split at h <;> obtain ⟨d4, h4, h⟩ := Except.bind_eq_ok h <;>
        exact ⟨(hcall h).1, fun e => absurd e ht, fun _ => (hcall h).2⟩
  unfold Staging.prepareTopLevelAmsterdam at h
  dsimp only at h
  split at h <;> obtain ⟨d1, h1, h⟩ := Except.bind_eq_ok h <;> exact key _ h

private theorem prepare_amsterdam_coherent {state : StateGasRules} {msg : Msg} {f : Jaune.Frame}
    {refund : Nat} (hcode : msg.codeAddress = none ↔ msg.target = none)
    (h : Staging.TopLevel.prepare.amsterdam state msg msg.target.isNone = .ok (.frame f refund)) :
    f.message.KindCoherent := by
  unfold Staging.TopLevel.prepare.amsterdam at h
  split at h
  · cases h
  · exact absurd (by assumption) (Staging.prepareTopLevelAmsterdam_error_ne_revert _ _ _)
  · cases h
  · cases h
  rename_i prepared d hp
  cases h
  obtain ⟨_, hc, hcall⟩ := prepareTopLevelAmsterdam_message hp
  apply (Message.ofTop_kindCoherent_iff _ _).mpr
  cases ht : msg.target with
  | none => simpa [ht] using (hc ht).trans (hcode.mpr ht)
  | some a => simp [hcall (by simp [ht])]

/-- A prepared top-level frame has a creation kind exactly when its code address is absent. -/
theorem TopLevel.prepare_kindCoherent {benv : Benv} {tenv : Tenv} {tx : Transaction} {msg : Msg}
    {f : Jaune.Frame} {refund : Nat} (hm : prepareMessage benv tenv tx = .ok msg)
    (h : Staging.TopLevel.prepare msg = .ok (.frame f refund)) : f.message.KindCoherent := by
  have hcode := prepareMessage_codeAddress_eq_none_iff hm
  cases ht : msg.target with
  | none =>
    simp only [Staging.TopLevel.prepare, ht, Option.isNone_none, ↓reduceIte, Staging.TopLevel.prepare.create] at h
    cases hs : msg.benv.stat.rules.stateGas with
    | none =>
      simp only [hs] at h
      split at h
      · cases h
      · cases h
        exact prepareMessage_create_kindCoherent hm ht
    | some st =>
      simp only [hs] at h
      apply prepare_amsterdam_coherent hcode
      simpa only [ht, Option.isNone_none] using h
  | some a =>
    simp only [Staging.TopLevel.prepare, ht, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
      Staging.TopLevel.prepare.call] at h
    cases hs : msg.benv.stat.rules.stateGas with
    | none =>
      simp only [hs] at h
      split at h
      · cases h
      · rename_i d refund' ha
        cases h
        exact resolveCodeDelegation_call_kindCoherent
          (Jaune.processMessageCall.authorize_codeAddress ha (fun eq => by have := hcode.mp eq; simp [ht] at this))
    | some st =>
      simp only [hs] at h
      apply prepare_amsterdam_coherent hcode
      simpa only [ht, Option.isNone_some] using h

end Jaune.Checked
