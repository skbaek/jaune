import Jaune.Bridge.Driver
import Jaune.MessageCall.TraceJson

/-!
# The four-part message call: the trace bridge (goal `jaune-shape-and-names-v1`, W1 unit K1)

Today's streaming driver (`Jaune.Trace`) and the staged one (`Jaune.MessageCall.Trace`) deliver
corresponding events in the same order, for every machine, fuel, run identity and monad
(`execFueled_trace_legacy`, `exec_trace_legacy`, `runFrame_trace_legacy`): any two sinks that
agree on corresponding events (`Event.Corr`) have the same effects, and return the same next
frame number. Today's serialiser and the staged one agree on corresponding events
(`consume_legacy`, `sink_legacy`), so the tracer's `IO` run writes the same bytes to the same
handles (`runFrame_json_legacy`, `exec_json_legacy`).

This module reads adapter modules, so it is classified `adapter`, not `bridge`. About today's
definitions, and deleted with them after the gate's tag (the W1 design note, second revision,
§6.5 and §3.2, unit K1).
-/

namespace Jaune

namespace Staging

open Legacy
open Jaune.Trace (Context CertifiedResult)

namespace Trace

/-- Corresponding events: what today's driver and the staged one emit at the same point of a
run. The step is each side's own step of the same machine; a frame is the staged reading of
today's, and its entry and settled result are read by `Frame.Entry.ofLegacy` and
`Frame.Result.ofSettled`, with today's settlement guarantees; a raw result agrees up to a fault's
erased state. -/
def Event.Corr : Jaune.Trace.Event → Event → Prop
  | .instruction c b s, .instruction c' b' s' =>
    c = c' ∧ b = b' ∧ s = Jaune.Evm.step b ∧ s' = Staging.Evm.step b
  | .entered c f e, .entered c' f' e' =>
    c = c' ∧ f'.message = Message.ofLegacy f.outer f.isCreate ∧ e' = Frame.Entry.ofLegacy e
  | .exited c r, .exited c' r' =>
    c = c' ∧ r.map Execution.observe = r'.map Execution.observe
  | .settled c f r, .settled c' f' r' =>
    c = c' ∧ f'.message = Message.ofLegacy f.outer f.isCreate ∧ f.inner.gas = f.outer.gas ∧
      r' = Frame.Result.ofSettled r ∧
      ∃ parent rules, f'.checkpoint.world = parent.world ∧ SettledFacts parent rules r
  | .resumed c k x, .resumed c' k' x' => c = c' ∧ k = k' ∧ x.observe = x'.observe
  | _, _ => False

/-- Transport along an erasure proof does not change the next frame number. -/
theorem map_cast_nextFrame {m : Type → Type} [Monad m] {e₁ e₂ : Fueled (EvmError × Devm) Devm}
    (h : e₁ = e₂) (x : m (CertifiedResult e₁)) :
    CertifiedResult.nextFrame <$> cast (congrArg (fun e => m (CertifiedResult e)) h) x
      = CertifiedResult.nextFrame <$> x := by
  subst h; rfl

/-- A certified result is determined by its next frame number. -/
theorem bind_certified {m : Type → Type} [Monad m] [LawfulMonad m]
    {e : Fueled (EvmError × Devm) Devm} {β : Type} (x : m (CertifiedResult e))
    (g : CertifiedResult e → m β) :
    x >>= g = (CertifiedResult.nextFrame <$> x) >>= fun k => g ⟨e, k, rfl⟩ := by
  rw [bind_map_left]; congr 1; funext cr; rcases cr with ⟨v, k, h⟩; subst h; rfl

/-- The staged driver's tail, observed, is the staged resumption of the settled result. -/
theorem resumedRaw_observe (rules : ForkRules) (child : Frame) (pending : Pending)
    (X : Except Fault Frame.Result) :
    (resumedRaw rules child pending X).observe
      = (X >>= resume rules pending child.checkpoint).map ofHalting := by
  rcases X with fault | result
  · cases fault <;> rfl
  · show _ = (resume rules pending child.checkpoint result).map ofHalting
    simp only [resumedRaw]
    rcases resume rules pending child.checkpoint result with fault | ⟨reason, devm⟩ | devm
    · cases fault <;> rfl
    · rfl
    · rfl

/-! ### Both drivers, with only the next frame number kept

Each driver's spawn branch with its certificates erased: the events in order, and the next
frame number. Stated for each side so the comparison below is between two plain terms. -/

section Shapes

variable {m : Type → Type} [Monad m]

/-- Today's caller after its child settled, keeping only the next frame number. -/
def legacyResumed (sinkOld : Jaune.Trace.Sink m) (evm : Evm) (fuel : Nat) (context : Context)
    (nextFrame pc : Nat) (x : Execution) (k : Nat) : m Nat :=
  match x with
  | .error error => do
    sinkOld (.resumed context nextFrame (.error error))
    sinkOld (.exited context (some (.error error)))
    pure k
  | .ok devm => do
    sinkOld (.resumed context nextFrame (.ok devm))
    CertifiedResult.nextFrame <$>
      Jaune.Trace.execFueled sinkOld ⟨pc, evm.sta, devm⟩ fuel context k

/-- The staged caller after its child settled, keeping only the next frame number. -/
def stagedResumed (sink : Sink m) (evm : Evm) (fuel : Nat) (context : Context)
    (nextFrame pc : Nat) (x : Execution) (k : Nat) : m Nat :=
  match x with
  | .error error => do
    sink (.resumed context nextFrame (.error error))
    sink (.exited context (some (.error error)))
    pure k
  | .ok devm => do
    sink (.resumed context nextFrame (.ok devm))
    CertifiedResult.nextFrame <$> execFueled sink ⟨pc, evm.sta, devm⟩ fuel context k

/-- Today's spawn branch after the instruction event, keeping only the next frame number. -/
def legacySpawn (sinkOld : Jaune.Trace.Sink m) (evm : Evm) (fuel : Nat) (context : Context)
    (nextFrame : Nat) (f : Jaune.Frame) (rsm : Resume) (pc : Nat) : m Nat :=
  let childContext : Context :=
    { context with frame := nextFrame, depth := context.depth + 1 }
  match f.enter with
  | .done settled => do
    sinkOld (.entered childContext f (.done settled))
    sinkOld (.settled childContext f settled)
    legacyResumed sinkOld evm fuel context nextFrame pc (rsm.run settled) (nextFrame + 1)
  | .run child => do
    sinkOld (.entered childContext f (.run child))
    let k ← CertifiedResult.nextFrame <$>
      Jaune.Trace.execFueled sinkOld child fuel childContext (nextFrame + 1)
    match (Jaune.execFueled child fuel).run with
    | none => do
      sinkOld (.exited context none)
      pure k
    | some raw => do
      sinkOld (.settled childContext f (f.settle raw))
      legacyResumed sinkOld evm fuel context nextFrame pc (rsm.run (f.settle raw)) k

/-- The staged spawn branch after the instruction event, keeping only the next frame number. -/
def stagedSpawn (sink : Sink m) (evm : Evm) (fuel : Nat) (context : Context)
    (nextFrame : Nat) (child : Frame) (pending : Pending) (pc : Nat) : m Nat :=
  let childContext : Context :=
    { context with frame := nextFrame, depth := context.depth + 1 }
  let rules := evm.sta.benvStat.rules
  match enter child with
  | .done settled => do
    sink (.entered childContext child (.done settled))
    sink (.settled childContext child settled)
    stagedResumed sink evm fuel context nextFrame pc (resumedRaw rules child pending settled)
      (nextFrame + 1)
  | .run childEvm => do
    sink (.entered childContext child (.run childEvm))
    let k ← CertifiedResult.nextFrame <$>
      execFueled sink childEvm fuel childContext (nextFrame + 1)
    match (Staging.execFueled childEvm fuel).run with
    | none => do
      sink (.exited context none)
      pure k
    | some raw => do
      sink (.settled childContext child (settle child raw))
      stagedResumed sink evm fuel context nextFrame pc
        (resumedRaw rules child pending (settle child raw)) k

variable [LawfulMonad m]

theorem legacy_halt (sinkOld : Jaune.Trace.Sink m) {evm : Evm} {fuel : Nat} {raw : Execution}
    (hs : Jaune.Evm.step evm = .halt raw) (context : Context) (nextFrame : Nat) :
    CertifiedResult.nextFrame <$> Jaune.Trace.execFueled sinkOld evm (fuel + 1) context nextFrame
      = (do sinkOld (.instruction context evm (.halt raw)); sinkOld (.exited context (some raw))
            pure nextFrame) := by
  rw [Jaune.Trace.execFueled]
  split <;> rename_i hs' <;> rw [hs] at hs' <;> cases hs'
  simp only [map_bind, map_pure]

theorem legacy_cont (sinkOld : Jaune.Trace.Sink m) {evm : Evm} {fuel pc : Nat} {devm : Devm}
    (hs : Jaune.Evm.step evm = .cont pc devm) (context : Context) (nextFrame : Nat) :
    CertifiedResult.nextFrame <$> Jaune.Trace.execFueled sinkOld evm (fuel + 1) context nextFrame
      = (do sinkOld (.instruction context evm (.cont pc devm))
            CertifiedResult.nextFrame <$>
              Jaune.Trace.execFueled sinkOld ⟨pc, evm.sta, devm⟩ fuel context nextFrame) := by
  rw [Jaune.Trace.execFueled]
  split <;> rename_i hs' <;> rw [hs] at hs' <;> cases hs'
  simp only [map_bind]
  rw [map_cast_nextFrame]
  simp only [Jaune.execFueled, hs]

theorem legacy_spawn (sinkOld : Jaune.Trace.Sink m) {evm : Evm} {fuel pc : Nat} {f : Jaune.Frame}
    {rsm : Resume} (hs : Jaune.Evm.step evm = .spawn f rsm pc) (context : Context)
    (nextFrame : Nat) :
    CertifiedResult.nextFrame <$> Jaune.Trace.execFueled sinkOld evm (fuel + 1) context nextFrame
      = (do sinkOld (.instruction context evm (.spawn f rsm pc))
            legacySpawn sinkOld evm fuel context nextFrame f rsm pc) := by
  rw [Jaune.Trace.execFueled]
  split <;> rename_i hs' <;> rw [hs] at hs' <;> cases hs'
  simp only [map_bind, legacySpawn]
  congr 1; funext _
  split <;> rename_i he <;> simp only [he]
  · simp only [map_bind]
    congr 1; funext _; congr 1; funext _
    split <;> rename_i hr <;> simp only [hr, legacyResumed, map_bind, map_pure]
    rw [map_cast_nextFrame]
    simp only [Jaune.execFueled, hs, he, hr]
  · simp only [map_bind]
    congr 1; funext _
    rw [bind_certified, bind_map_left, bind_map_left]
    congr 1; funext a
    dsimp only
    split <;> rename_i hc <;> simp only [hc, map_bind, map_pure]
    congr 1; funext _
    split <;> rename_i hr <;> simp only [hr, legacyResumed, map_bind, map_pure]
    rw [map_cast_nextFrame]
    simp only [Jaune.execFueled, hs, he, hc, hr]

theorem staged_halt (sink : Sink m) {evm : Evm} {fuel : Nat} {raw : Execution}
    (hs : Staging.Evm.step evm = .halt raw) (context : Context) (nextFrame : Nat) :
    CertifiedResult.nextFrame <$> execFueled sink evm (fuel + 1) context nextFrame
      = (do sink (.instruction context evm (.halt raw)); sink (.exited context (some raw))
            pure nextFrame) := by
  rw [execFueled]
  split <;> rename_i hs' <;> rw [hs] at hs' <;> cases hs'
  simp only [map_bind, map_pure]

theorem staged_next (sink : Sink m) {evm : Evm} {fuel pc : Nat} {devm : Devm}
    (hs : Staging.Evm.step evm = .next pc devm) (context : Context) (nextFrame : Nat) :
    CertifiedResult.nextFrame <$> execFueled sink evm (fuel + 1) context nextFrame
      = (do sink (.instruction context evm (.next pc devm))
            CertifiedResult.nextFrame <$>
              execFueled sink ⟨pc, evm.sta, devm⟩ fuel context nextFrame) := by
  rw [execFueled]
  split <;> rename_i hs' <;> rw [hs] at hs' <;> cases hs'
  simp only [map_bind]
  rw [map_cast_nextFrame]
  simp only [Staging.execFueled, hs]

theorem staged_spawn (sink : Sink m) {evm : Evm} {fuel pc : Nat} {child : Frame}
    {pending : Pending} (hs : Staging.Evm.step evm = .spawn child pending pc) (context : Context)
    (nextFrame : Nat) :
    CertifiedResult.nextFrame <$> execFueled sink evm (fuel + 1) context nextFrame
      = (do sink (.instruction context evm (.spawn child pending pc))
            stagedSpawn sink evm fuel context nextFrame child pending pc) := by
  rw [execFueled]
  split <;> rename_i hs' <;> rw [hs] at hs' <;> cases hs'
  simp only [map_bind, stagedSpawn]
  congr 1; funext _
  split <;> rename_i he <;> simp only [he]
  · simp only [map_bind]
    congr 1; funext _; congr 1; funext _
    split <;> rename_i hr <;> simp only [hr, stagedResumed, map_bind, map_pure]
    rw [map_cast_nextFrame]
    rw [execFueled_spawn hs, he]; dsimp only; rw [hr]
  · simp only [map_bind]
    congr 1; funext _
    rw [bind_certified, bind_map_left, bind_map_left]
    congr 1; funext a
    dsimp only
    split <;> rename_i hc <;> simp only [hc, map_bind, map_pure]
    congr 1; funext _
    split <;> rename_i hr <;> simp only [hr, stagedResumed, map_bind, map_pure]
    rw [map_cast_nextFrame]
    rw [execFueled_spawn hs, he]; dsimp only; rw [hc, Option.map_some]; dsimp only; rw [hr]

end Shapes

section Simulation

variable {m : Type → Type} [Monad m] [LawfulMonad m]
  (sinkOld : Jaune.Trace.Sink m) (sink : Sink m)
  (hsink : ∀ eo en, Event.Corr eo en → sinkOld eo = sink en)
include hsink

omit [LawfulMonad m] in
/-- One corresponding event, then corresponding continuations. -/
theorem corr_bind {β : Type} {eo : Jaune.Trace.Event} {en : Event} {k k' : PUnit → m β}
    (h : Event.Corr eo en) (hk : ∀ u, k u = k' u) : (sinkOld eo >>= k) = (sink en >>= k') := by
  rw [hsink _ _ h]; congr 1; funext u; exact hk u

omit [LawfulMonad m] in
/-- The resumption tails agree on raw results that agree up to a fault's erased state. -/
theorem resumed_legacy {evm : Evm} {fuel : Nat}
    (ih : ∀ (evm : Evm) (context : Context) (nextFrame : Nat),
      CertifiedResult.nextFrame <$> Jaune.Trace.execFueled sinkOld evm fuel context nextFrame
        = CertifiedResult.nextFrame <$> execFueled sink evm fuel context nextFrame)
    (context : Context) (nextFrame pc : Nat) {x y : Execution} (h : x.observe = y.observe)
    (k : Nat) :
    legacyResumed sinkOld evm fuel context nextFrame pc x k
      = stagedResumed sink evm fuel context nextFrame pc y k := by
  rcases x with ⟨e, d⟩ | d <;> rcases y with ⟨e', d'⟩ | d'
  · simp only [legacyResumed, stagedResumed]
    refine corr_bind sinkOld sink hsink (by unfold Event.Corr; exact ⟨rfl, rfl, h⟩) fun _ => ?_
    refine corr_bind sinkOld sink hsink ?_ fun _ => rfl
    unfold Event.Corr; exact ⟨rfl, by simp only [Option.map_some, h]⟩
  · cases e <;> simp [Execution.observe] at h
  · cases e' <;> simp [Execution.observe] at h
  · have hd : d = d' := by simpa [Execution.observe] using h
    subst hd
    simp only [legacyResumed, stagedResumed]
    refine corr_bind sinkOld sink hsink ?_ fun _ => ih _ _ _
    unfold Event.Corr; exact ⟨rfl, rfl, rfl⟩

omit [LawfulMonad m] in
/-- The spawn branches agree, given that the drivers agree at the remaining fuel. -/
theorem spawn_legacy {evm : Evm} {fuel : Nat}
    (ih : ∀ (evm : Evm) (context : Context) (nextFrame : Nat),
      CertifiedResult.nextFrame <$> Jaune.Trace.execFueled sinkOld evm fuel context nextFrame
        = CertifiedResult.nextFrame <$> execFueled sink evm fuel context nextFrame)
    {f : Jaune.Frame} {rsm : Resume} {pc : Nat} (hs : Jaune.Evm.step evm = .spawn f rsm pc)
    (context : Context) (nextFrame : Nat) :
    legacySpawn sinkOld evm fuel context nextFrame f rsm pc
      = stagedSpawn sink evm fuel context nextFrame (Frame.ofLegacy f rsm) (Pending.ofLegacy rsm)
          pc := by
  obtain ⟨hc, hb, -, hm⟩ := step_spawn_coherent hs
  have hr : f.outer.benv.stat.rules = evm.sta.benvStat.rules := congrArg BenvStat.rules hb
  have hgas : f.inner.gas = f.outer.gas := congrArg Message.gas (inner_fields hc.paired).1
  unfold legacySpawn stagedSpawn
  dsimp only
  rw [← enter_legacy f rsm hc]
  rcases he : f.enter with settled | child <;> simp only [Frame.Entry.ofLegacy]
  · refine corr_bind sinkOld sink hsink (by unfold Event.Corr; exact ⟨rfl, rfl, rfl⟩) fun _ => ?_
    have hf := Frame.enter_done_facts hc hr he
    refine corr_bind sinkOld sink hsink ?_ fun _ => ?_
    · unfold Event.Corr; exact ⟨rfl, rfl, hgas, rfl, rsm.parent, _, rfl, hf⟩
    apply resumed_legacy sinkOld sink hsink ih
    rw [resumedRaw_observe]
    exact resume_of_facts hm hf
  · refine corr_bind sinkOld sink hsink ?_ fun _ => ?_
    · unfold Event.Corr; exact ⟨rfl, rfl, rfl⟩
    rw [ih]
    congr 1; funext k
    have hih := execFueled_legacy fuel child
    cases hL : (Jaune.execFueled child fuel).run with
    | none =>
      rw [hL, Option.map_none, eq_comm, Option.map_eq_none_iff] at hih
      rw [hih]
      dsimp only
      refine corr_bind sinkOld sink hsink ?_ fun _ => rfl
      unfold Event.Corr; exact ⟨rfl, rfl⟩
    | some raw =>
      rw [hL, Option.map_some, eq_comm, Option.map_eq_some_iff] at hih
      obtain ⟨raw', hN, hobs⟩ := hih
      have hclean : Execution.Clean raw := by
        rcases raw with _ | d
        · trivial
        · exact (execFueled_ok_error fuel child hL).trans (Frame.enter_run_error he)
      have hset : settle (Frame.ofLegacy f rsm) raw' = Frame.Result.ofSettled (f.settle raw) :=
        (settle_observe hobs).trans
          (settle_legacy f rsm.parent hc.toTopCoherent raw hclean).symm
      rw [hN]
      dsimp only
      rw [hset]
      refine corr_bind sinkOld sink hsink ?_ fun _ => ?_
      · unfold Event.Corr
        exact ⟨rfl, rfl, hgas, rfl, rsm.parent, _, rfl, settledFacts hc hr hclean⟩
      apply resumed_legacy sinkOld sink hsink ih
      rw [resumedRaw_observe]
      exact resume_legacy hc hm hr raw hclean

/-- **The trace driver.** Today's streaming driver and the staged one, run with sinks that agree
on corresponding events, have the same effects and return the same next frame number, for every
machine, fuel, run identity and frame number, in every lawful monad. -/
theorem execFueled_trace_legacy (fuel : Nat) (evm : Evm) (context : Context) (nextFrame : Nat) :
    CertifiedResult.nextFrame <$> Jaune.Trace.execFueled sinkOld evm fuel context nextFrame
      = CertifiedResult.nextFrame <$> execFueled sink evm fuel context nextFrame := by
  induction fuel generalizing evm context nextFrame with
  | zero =>
    rw [Jaune.Trace.execFueled, execFueled]
    simp only [map_bind, map_pure]
    refine corr_bind sinkOld sink hsink ?_ fun _ => rfl
    unfold Event.Corr; exact ⟨rfl, rfl⟩
  | succ fuel ih =>
    have hst := step_legacy evm
    rcases hs : Jaune.Evm.step evm with raw | ⟨pc, devm⟩ | ⟨f, rsm, pc⟩ <;> rw [hs] at hst
    · rw [legacy_halt sinkOld hs, staged_halt sink hst.symm]
      refine corr_bind sinkOld sink hsink ?_ fun _ => ?_
      · unfold Event.Corr; exact ⟨rfl, rfl, hs.symm, hst⟩
      refine corr_bind sinkOld sink hsink ?_ fun _ => rfl
      unfold Event.Corr; exact ⟨rfl, rfl⟩
    · rw [legacy_cont sinkOld hs, staged_next sink hst.symm]
      refine corr_bind sinkOld sink hsink ?_ fun _ => ih _ _ _
      unfold Event.Corr; exact ⟨rfl, rfl, hs.symm, hst⟩
    · rw [legacy_spawn sinkOld hs, staged_spawn sink hst.symm]
      refine corr_bind sinkOld sink hsink ?_ fun _ =>
        spawn_legacy sinkOld sink hsink ih hs context nextFrame
      unfold Event.Corr; exact ⟨rfl, rfl, hs.symm, hst⟩

/-- **The total trace driver.** Today's `Trace.exec` and the staged one, run with sinks that agree
on corresponding events, have the same effects and return the same next frame number. -/
theorem exec_trace_legacy (evm : Evm) (context : Context) (nextFrame : Nat) :
    Jaune.Trace.ExecutionResult.nextFrame <$> Jaune.Trace.exec sinkOld evm context nextFrame
      = ExecutionResult.nextFrame <$> exec sink evm context nextFrame := by
  unfold Jaune.Trace.exec exec
  simp only [map_bind]
  rw [bind_certified (Jaune.Trace.execFueled sinkOld evm _ context nextFrame),
    bind_certified (execFueled sink evm _ context nextFrame),
    execFueled_trace_legacy sinkOld sink hsink]
  congr 1; funext k
  dsimp only
  split
  · split <;> simp only [map_pure]
  · rename_i hrun
    simp [execFueled_run_sufficientFuel] at hrun

end Simulation

end Trace

end Staging

namespace Legacy

/-- What today's settlement guarantees, for a frame coherent with its top-level start. -/
theorem settledFacts_top {f : Jaune.Frame} {parent : Devm} {rules : ForkRules}
    (h : Frame.TopCoherent f parent) (hr : f.outer.benv.stat.rules = rules) {raw : Execution}
    (clean : raw.Clean) : SettledFacts parent rules (f.settle raw) where
  fault := Frame.settle_error_isFault f raw
  world := fun hs hf => by
    rw [Frame.settle_failed_world f h.paired hs hf, h.state, h.transient, h.storageWrites]
    rfl
  refund := fun hs hf hsg => Frame.settle_failed_refund f h.paired (hr ▸ hsg) clean hs hf
  halted := Frame.settle_halted f clean

/-- `Frame.enter_done_facts` for a frame coherent with its top-level start. -/
theorem Frame.enter_done_facts_top {f : Jaune.Frame} {parent : Devm} {rules : ForkRules}
    (h : Frame.TopCoherent f parent) (hr : f.outer.benv.stat.rules = rules)
    {r : Except (EvmError × Jaune.State × AdrSet × TransientStorage) Devm}
    (he : f.enter = .done r) : SettledFacts parent rules r := by
  rw [Frame.enter_eq_enterFrom] at he
  unfold Frame.enterFrom at he
  split at he
  · rename_i e hb
    cases he
    have hfault := Msg.benvAfterTransfer_error hb
    have hs : f.settleMsg (.error e) = .error e := by
      unfold Jaune.Frame.settleMsg processMessage.settle processCreateMessage.settle
      split <;> rfl
    rw [hs]
    refine ⟨?_, fun hs _ => (nomatch hs), fun hs _ _ => (nomatch hs), fun hs _ => (nomatch hs)⟩
    intro e' st c t he'
    cases he'
    exact .inr ⟨_, hfault⟩
  · dsimp only at he
    split at he
    · cases he
    · split at he
      · cases he
        apply settledFacts_top h hr
        show Execution.Clean _
        cases hp : executePrecompile _ _ with
        | error _ => trivial
        | ok d => exact (executePrecompile_ok_error hp).trans rfl
      · cases he

/-- The top-level frames of today are coherent with their message's start. -/
theorem Frame.top_topCoherent (msg : Msg) (isCreate : Bool) :
    Frame.TopCoherent (if isCreate then Jaune.Frame.ofCreate msg else Jaune.Frame.ofCall msg)
      (initDevm msg) := by
  cases isCreate <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Legacy

namespace Staging

open Legacy
open Jaune.Trace (Context CertifiedResult)

namespace Trace

/-- A top-level frame's checkpoint, as a start state, is its message's `initDevm`. -/
theorem ofTop_start (msg : Msg) (isCreate : Bool) :
    (Frame.ofTop msg isCreate).checkpoint.toDevm = initDevm msg :=
  Frame.State.toDevm_ofDevm _ rfl rfl

/-- A total execution result of today is determined by its next frame number. -/
theorem bind_execution_legacy {m : Type → Type} [Monad m] [LawfulMonad m] {evm : Evm} {β : Type}
    (x : m (Jaune.Trace.ExecutionResult evm)) (g : Jaune.Trace.ExecutionResult evm → m β) :
    x >>= g = (Jaune.Trace.ExecutionResult.nextFrame <$> x) >>= fun k =>
      g ⟨Jaune.exec evm, k, rfl⟩ := by
  rw [bind_map_left]; congr 1; funext r; rcases r with ⟨v, k, h⟩; subst h; rfl

/-- A staged total execution result is determined by its next frame number. -/
theorem bind_execution {m : Type → Type} [Monad m] [LawfulMonad m] {evm : Evm} {β : Type}
    (x : m (ExecutionResult evm)) (g : ExecutionResult evm → m β) :
    x >>= g = (ExecutionResult.nextFrame <$> x) >>= fun k => g ⟨Staging.exec evm, k, rfl⟩ := by
  rw [bind_map_left]; congr 1; funext r; rcases r with ⟨v, k, h⟩; subst h; rfl

section Top

variable {m : Type → Type} [Monad m] [LawfulMonad m]
  (sinkOld : Jaune.Trace.Sink m) (sink : Sink m)
  (hsink : ∀ eo en, Event.Corr eo en → sinkOld eo = sink en)
include hsink

/-- **The top-level frame.** Today's `Trace.runFrame` on a message's call or create frame and the
staged one on the message's top frame, run with sinks that agree on corresponding events, have
the same effects and return the same next frame number. -/
theorem runFrame_trace_legacy (msg : Msg) (isCreate : Bool) (runId : String) :
    Jaune.Trace.FrameResult.nextFrame <$> Jaune.Trace.runFrame sinkOld
        (if isCreate then Jaune.Frame.ofCreate msg else Jaune.Frame.ofCall msg) runId
      = FrameResult.nextFrame <$> runFrame sink (Frame.ofTop msg isCreate) runId := by
  have htop := Legacy.Frame.top_topCoherent msg isCreate
  have hmsg : (Frame.ofTop msg isCreate).message
      = Message.ofLegacy
          (if isCreate then Jaune.Frame.ofCreate msg else Jaune.Frame.ofCall msg).outer
          (if isCreate then Jaune.Frame.ofCreate msg else Jaune.Frame.ofCall msg).isCreate := by
    cases isCreate <;> rfl
  have hgas := congrArg Message.gas (inner_fields htop.paired).1
  have hE := enterWith_top msg isCreate
  rw [← ofTop_start msg isCreate] at hE
  generalize (if isCreate then Jaune.Frame.ofCreate msg else Jaune.Frame.ofCall msg) = F
    at htop hmsg hgas hE ⊢
  unfold Jaune.Trace.runFrame runFrame
  dsimp only
  split <;> rename_i he <;> split <;> rename_i he' <;> rw [he', he] at hE <;>
    simp only [Frame.Entry.ofLegacy, Frame.Entry.done.injEq, Frame.Entry.run.injEq,
      reduceCtorEq] at hE
  · subst hE
    simp only [map_bind, map_pure]
    refine corr_bind sinkOld sink hsink ?_ fun _ => ?_
    · unfold Event.Corr; exact ⟨rfl, hmsg, rfl⟩
    refine corr_bind sinkOld sink hsink ?_ fun _ => rfl
    unfold Event.Corr
    exact ⟨rfl, hmsg, hgas, rfl, initDevm msg, _, rfl,
      Legacy.Frame.enter_done_facts_top htop rfl he⟩
  · subst hE
    simp only [map_bind, map_pure]
    refine corr_bind sinkOld sink hsink ?_ fun _ => ?_
    · unfold Event.Corr; exact ⟨rfl, hmsg, rfl⟩
    rw [bind_execution_legacy, bind_execution, exec_trace_legacy sinkOld sink hsink]
    congr 1; funext k
    dsimp only
    rename_i child _
    have hclean : Execution.Clean (Jaune.exec child) := by
      cases hx : Jaune.exec child with
      | error _ => trivial
      | ok d =>
        exact (execFueled_ok_error _ child
          ((execFueled_run_sufficientFuel child).trans (congrArg some hx))).trans
          (Legacy.Frame.enter_run_error he)
    have hf : Frame.ofTop msg isCreate
        = ⟨Message.ofLegacy F.outer F.isCreate, Frame.State.ofDevm (initDevm msg)⟩ := by
      rw [← hmsg]; rfl
    have hset : settle (Frame.ofTop msg isCreate) (Staging.exec child)
        = Frame.Result.ofSettled (F.settle (Jaune.exec child)) := by
      rw [settle_observe (exec_legacy child).symm, hf,
        settle_legacy F (initDevm msg) htop _ hclean]
    rw [hset]
    refine corr_bind sinkOld sink hsink ?_ fun _ => rfl
    unfold Event.Corr
    exact ⟨rfl, hmsg, hgas, rfl, initDevm msg, _, rfl, Legacy.settledFacts_top htop rfl hclean⟩

end Top

end Trace

namespace TraceJson

open Lean
open Jaune.TraceJson (Config)

/-- The gas cost read from the staged step is today's, for the step of any machine. -/
theorem gasCost?_legacy {before : Evm} {s : Jaune.Step} (hs : Jaune.Evm.step before = s) :
    gasCost? before (Step.ofLegacy s) = Jaune.TraceJson.gasCost? before s := by
  rcases s with raw | ⟨pc, devm⟩ | ⟨f, rsm, pc⟩
  · rcases raw with ⟨e, d⟩ | d
    · cases e <;> rfl
    · rfl
  · rfl
  · obtain ⟨hc, -, -, hm⟩ := step_spawn_coherent hs
    have hgas : f.inner.gas = f.outer.gas := congrArg Message.gas (inner_fields hc.paired).1
    unfold gasCost? Jaune.TraceJson.gasCost?
    split
    · rfl
    · rename_i hsg
      cases rsm <;>
        simp_all [Resume.Matches, Step.ofLegacy, Frame.ofLegacy, Pending.ofLegacy,
          Frame.State.ofDevm, Message.ofLegacy, Resume.parent]

/-- The instruction row read from the staged step is today's, for the step of any machine. -/
theorem instruction_legacy (cfg : Config) (context : Context) (refundBase : Int) {before : Evm}
    {s : Jaune.Step} (hs : Jaune.Evm.step before = s) :
    instruction cfg context refundBase before (Step.ofLegacy s)
      = Jaune.TraceJson.instruction cfg context refundBase before s := by
  have hg := gasCost?_legacy hs
  unfold instruction
  rw [hg]
  rcases s with ⟨⟨e, d⟩ | d⟩ | ⟨pc, devm⟩ | ⟨f, rsm, pc⟩ <;> rfl

/-- Today's root summary body, over its read values. -/
def rootBody (cfg : Config) (grant : Nat) (root : U256) (output : Bytes) (gasLeft : Nat)
    (pass : Bool) : Except String Json := do
  if output.length > cfg.maxDataBytes then throw "output exceeds maxDataBytes"
  let some used := safeSub grant gasLeft
    | throw "settled gas exceeds root grant"
  return Json.mkObj [
    ("stateRoot", .str (T8n.hexU256 root)),
    ("output", bytes output), ("gasUsed", quantity used),
    ("pass", .bool pass)]

/-- The staged root summary is today's body over what it reads. -/
theorem rootSummary_eq (cfg : Config) (f : Frame) (r : Frame.Result) {grant : Nat} {root : U256}
    {output : Bytes} {gasLeft : Nat} {pass : Bool} (h1 : f.message.gas = grant)
    (h2 : (f.worldAfter r).state.root = root) (h3 : r.output = output) (h4 : r.gasLeft = gasLeft)
    (h5 : (!r.failed) = pass) :
    rootSummary cfg f r = rootBody cfg grant root output gasLeft pass := by
  subst h1 h2 h3 h4 h5
  rfl

/-- **The serialiser.** The staged `consume` gives today's rows and state on corresponding
events. -/
theorem consume_legacy (cfg : Config) (state : Jaune.TraceJson.State) {eo : Jaune.Trace.Event}
    {en : Trace.Event} (h : Trace.Event.Corr eo en) :
    consume cfg state en = Jaune.TraceJson.consume cfg state eo := by
  rcases eo with ⟨c, b, s⟩ | ⟨c, f, e⟩ | ⟨c, r⟩ | ⟨c, f, r⟩ | ⟨c, k, x⟩ <;>
    rcases en with ⟨c', b', s'⟩ | ⟨c', f', e'⟩ | ⟨c', r'⟩ | ⟨c', f', r'⟩ | ⟨c', k', x'⟩ <;>
    simp only [Trace.Event.Corr] at h
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := h
    rw [← step_legacy]
    generalize hs : Jaune.Evm.step b = st
    rcases st with raw | ⟨pc, devm⟩ | ⟨f, rsm, pc⟩
    · rcases raw with ⟨e, d⟩ | d
      · cases e <;> rfl
      · rfl
    · rfl
    · unfold consume
      simp only [instruction_legacy cfg _ _ hs]
      cases rsm <;> rfl
  · obtain ⟨rfl, -, -⟩ := h; rfl
  · obtain ⟨rfl, hr⟩ := h
    cases r <;> cases r' <;> simp at hr <;> rfl
  · obtain ⟨rfl, hmsg, hgas, rfl, parent, rules, hw, hf⟩ := h
    have hgrant : f'.message.gas = f.inner.gas := by rw [hmsg, hgas]; rfl
    rcases r with ⟨e, st, cc, t⟩ | d
    · rcases hf.fault rfl with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;> rfl
    · have key : ∃ res, Frame.Result.ofSettled (.ok d) = .ok res ∧
          (f'.worldAfter res).state.root = d.state.root ∧ res.output = d.output ∧
          res.gasLeft = d.gasLeft ∧ (!res.failed) = d.error.isNone := by
        cases hd : d.error with
        | none =>
          refine ⟨Frame.Result.ofSuccess d.output d, by simp only [Frame.Result.ofSettled, hd],
            rfl, rfl, rfl, ?_⟩
          simp [Frame.Result.ofSuccess, Frame.Result.failed]
        | some e =>
          have hwd : d.world = f'.checkpoint.world := by
            rw [hw]; exact hf.world rfl (by simp [hd])
          let trail : Trail :=
            { (Frame.State.ofDevm d).trail with
              touchedRIPEMD160 := d.meta.touchedAccounts.contains ripemd160Address }
          cases e with
          | revert =>
            refine ⟨.revert d.output d.gasLeft d.stateGas trail,
              by simp only [Frame.Result.ofSettled, hd, trail], ?_, rfl, rfl,
              by simp [Frame.Result.failed]⟩
            simp only [Frame.worldAfter, Devm.state, hwd]
          | halt reason =>
            obtain ⟨hg0, ho0⟩ := hf.halted rfl hd
            refine ⟨.halt reason d.stateGas trail,
              by simp only [Frame.Result.ofSettled, hd, trail], ?_, ho0.symm, hg0.symm,
              by simp [Frame.Result.failed]⟩
            simp only [Frame.worldAfter, Devm.state, hwd]
      obtain ⟨res, hres, h2, h3, h4, h5⟩ := key
      rw [hres]
      unfold consume
      simp only [rootSummary_eq cfg f' res hgrant h2 h3 h4 h5]
      rfl
  · obtain ⟨rfl, rfl, -⟩ := h; rfl

/-- `EST` is a lawful monad. -/
instance instLawfulMonadEST (ε σ : Type) : LawfulMonad (EST ε σ) := LawfulMonad.mk'
  (id_map := fun x => by
    funext s
    simp only [Functor.map, EST.bind, EST.pure, Function.comp, id]
    cases x s <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x f g => by
    funext s
    simp only [bind, EST.bind]
    cases x s <;> rfl)

/-- `IO` is a lawful monad: it is `EST` over the real world. -/
instance instLawfulMonadIO : LawfulMonad IO :=
  inferInstanceAs (LawfulMonad (EST IO.Error IO.RealWorld))

/-- **The `IO` sink.** The staged sink performs today's reads, writes, flushes and state update
on corresponding events. -/
theorem sink_legacy (cfg : Config) (state : IO.Ref Jaune.TraceJson.State)
    (trace frames : IO.FS.Handle) {eo : Jaune.Trace.Event} {en : Trace.Event}
    (h : Trace.Event.Corr eo en) :
    sink cfg state trace frames en = Jaune.TraceJson.sink cfg state trace frames eo := by
  unfold sink Jaune.TraceJson.sink
  simp only [consume_legacy cfg _ h]
  rfl

/-- **The tracer's message run.** With the serialiser's `IO` sink, today's top-level frame run
(as `TraceMain` builds it) and the staged one perform the same `IO` actions, so they write the
same bytes to the same handles, and return the same next frame number. -/
theorem runFrame_json_legacy (cfg : Config) (state : IO.Ref Jaune.TraceJson.State)
    (trace frames : IO.FS.Handle) (msg : Msg) (runId : String) :
    Jaune.Trace.FrameResult.nextFrame <$> Jaune.Trace.runFrame
        (Jaune.TraceJson.sink cfg state trace frames)
        (if msg.target.isSome then Jaune.Frame.ofCall msg else Jaune.Frame.ofCreate msg) runId
      = Trace.FrameResult.nextFrame <$> Trace.runFrame (sink cfg state trace frames)
          (Frame.ofTop msg msg.target.isNone) runId := by
  have e : (if msg.target.isSome then Jaune.Frame.ofCall msg else Jaune.Frame.ofCreate msg)
      = (if msg.target.isNone then Jaune.Frame.ofCreate msg else Jaune.Frame.ofCall msg) := by
    cases h : msg.target <;> simp
  rw [e]
  exact Trace.runFrame_trace_legacy (m := IO) _ _
    (fun _ _ h => (sink_legacy cfg state trace frames h).symm) msg msg.target.isNone runId

/-- **The tracer's total run.** With the serialiser's `IO` sink, today's `Trace.exec` (which the
transaction tracer runs) and the staged one perform the same `IO` actions and return the same
next frame number. -/
theorem exec_json_legacy (cfg : Config) (state : IO.Ref Jaune.TraceJson.State)
    (trace frames : IO.FS.Handle) (evm : Evm) (context : Context) (nextFrame : Nat) :
    Jaune.Trace.ExecutionResult.nextFrame <$>
        Jaune.Trace.exec (Jaune.TraceJson.sink cfg state trace frames) evm context nextFrame
      = Trace.ExecutionResult.nextFrame <$>
          Trace.exec (sink cfg state trace frames) evm context nextFrame :=
  Trace.exec_trace_legacy _ _ (fun _ _ h => (sink_legacy cfg state trace frames h).symm)
    evm context nextFrame

end TraceJson

end Staging

end Jaune
