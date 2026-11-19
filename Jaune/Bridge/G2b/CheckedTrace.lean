import Jaune.MessageCall.CheckedTrace
import Jaune.MessageCall.TraceJson
import Jaune.Bridge.G2b.CheckedTop
import Jaune.Run.Trace

/-!
# Bridge: the staged checked tracer against the `Devm` tracer (G2b, F1e)

Old side: `Jaune.Trace.execFueled`, `Jaune.Trace.exec` and `Jaune.Trace.runFrame`
(`Jaune/MessageCall/Trace.lean`) and the serialiser `Jaune.TraceJson.consume`/`TraceJson.sink`
(`Jaune/MessageCall/TraceJson.lean`) at `9ce48608`, unedited. New side: `Checked.Trace.execFueled`,
`Checked.Trace.exec` and `Checked.Trace.runFrame` (`Jaune.MessageCall.CheckedTrace`).

The new tracer emits the old event type, projected from the checked state. The projection forgets
exactly what no reader of an event reads: a `Devm`'s output and stored error where a running
machine or a continuing step carries them, a halted frame's output, a fault's (never read) state,
and a pending return's two passed-through fields. `normalize` forgets the same on an old event.

* `execFueled_events`, `exec_events`, `runFrame_events`: from related starts, the new tracer with
  any sink, in any lawful monad, is the old tracer with the same sink after `normalize`: the same
  sink calls on the same (normalised) events in the same order, the same frame numbering, and the
  same returned value. `runFrame_events` holds for every checked frame against its projection.
* `consume_normalize`, `sink_normalize`: the serialiser reads nothing `normalize` forgets.
* `runFrame_json`: so the two tracers write byte-identical `trace.jsonl` and `frames.jsonl` rows,
  and return the same result, for every checked frame (goal 3.1: the serialised event stream as a
  further observation, proved equal).

It is classified `adapter` in `scripts/layering.json`, not `bridge`: a bridge module may not import
an adapter, and both tracers and the serialiser are adapters. It is reached by the default build
through `JauneChecks`, outside the `Jaune` library. Everything here goes with `Devm` after G2b's
tag.
-/

namespace Jaune.Bridge.G2b.CheckedTrace

open Jaune

/-! ### What the projection forgets -/

/-- A `Devm` without its output and stored error. -/
def normDevm (d : Devm) : Devm := (Frame.State.ofDevm d).toDevm

/-- A running machine without its `Devm`'s output and stored error. -/
def normEvm (evm : Evm) : Evm := ⟨evm.pc, evm.sta, normDevm evm.dyna⟩

/-- A raw result as an exit and back: a halted frame's output and every stored error are
forgotten, and a fault's state is the default. -/
def normRaw (raw : Execution) : Execution :=
  match Frame.Exit.ofExecution raw with
  | .ok e => e.toExecution
  | .error fault => .error (fault.toEvmError, default)

/-- A pending return without its two passed-through fields. -/
def normPending (p : Pending) : Pending := ⟨p.target, p.newAccountCharged, [], none⟩

def normStep : Step → Step
  | .halt raw => .halt (normRaw raw)
  | .next pc d => .next pc (normDevm d)
  | .spawn child p pc => .spawn child (normPending p) pc

def normEntry : Frame.Entry → Frame.Entry
  | .done result => .done result
  | .run evm => .run (normEvm evm)

/-- An old event, normalised. -/
def normalize : Trace.Event → Trace.Event
  | .instruction context before step => .instruction context (normEvm before) (normStep step)
  | .entered context frame entry => .entered context frame (normEntry entry)
  | .exited context raw => .exited context (raw.map normRaw)
  | .settled context frame result => .settled context frame result
  | .resumed parent child raw => .resumed parent child (normRaw raw)

/-! ### The serialiser reads nothing `normalize` forgets -/

theorem consume_normalize (cfg : TraceJson.Config) (st : TraceJson.State) (e : Trace.Event) :
    TraceJson.consume cfg st (normalize e) = TraceJson.consume cfg st e := by
  cases e with
  | instruction context before step =>
    cases step with
    | halt raw =>
      rcases raw with ⟨error, d⟩ | d
      · cases error <;> rfl
      · rfl
    | next pc d => rfl
    | spawn child p pc => rfl
  | entered context frame entry => cases entry <;> rfl
  | exited context raw => cases raw <;> rfl
  | settled => rfl
  | resumed => rfl

theorem sink_normalize (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (e : Trace.Event) :
    TraceJson.sink cfg state trace frames (normalize e) = TraceJson.sink cfg state trace frames e := by
  simp only [TraceJson.sink, consume_normalize]

/-! ### The projections, against the bridge maps -/

theorem state_eq (s : Checked.Frame.State) : Checked.Trace.state s = s.toLegacy := rfl

theorem frame_eq (f : Checked.Frame) : Checked.Trace.frame f = f.toLegacy := rfl

/-- What relates a running checked frame of the message `msg` to a running machine: the same
frame, grouped; the message's static record; no output. -/
structure Related (msg : Message) (r : Checked.Frame.Running) (evm : Evm) : Prop where
  running : r.toLegacy = Frame.Running.ofEvm evm
  static : evm.sta = msg.sevm
  output : evm.dyna.output = []

theorem Related.evm_eq {msg : Message} {r : Checked.Frame.Running} {evm : Evm}
    (h : Related msg r evm) : Checked.Trace.evm msg r = normEvm evm := by
  have hpc : r.pc = evm.pc := congrArg Frame.Running.pc h.running
  have hs : Checked.Trace.state r.state = Frame.State.ofDevm evm.dyna :=
    congrArg Frame.Running.state h.running
  simp only [Checked.Trace.evm, normEvm, normDevm, Checked.Trace.devm, hpc, hs, h.static]

theorem normRaw_of_fault {raw : Execution} {fault : Fault}
    (h : Frame.Exit.ofExecution raw = .error fault) : normRaw raw = Checked.Trace.faultRaw fault := by
  simp only [normRaw, h, Checked.Trace.faultRaw]

theorem normRaw_of_exit {raw : Execution} {e : Checked.Frame.Exit}
    (h : Frame.Exit.ofExecution raw = .ok e.toLegacy) : normRaw raw = Checked.Trace.exitRaw e := by
  simp only [normRaw, h]
  cases e <;> rfl

/-- The old raw result's exit, against the new driver's outcome. -/
theorem normRaw_of_square {raw : Execution} {x : Except Fault Checked.Frame.Exit}
    (h : x.map Checked.Frame.Exit.toLegacy = Frame.Exit.ofExecution raw) :
    normRaw raw = Checked.Trace.raw x := by
  rcases x with fault | e
  · exact normRaw_of_fault h.symm
  · exact normRaw_of_exit h.symm

/-! ### One step, entry, settlement and resumption, related -/

/-- The new step against the old one, from a related start. -/
theorem step_rel {msg : Message} {r : Checked.Frame.Running} {evm : Evm} (h : Related msg r evm) :
    (Checked.step r).map Checked.Step.toLegacy = (Jaune.Evm.step evm).observe := by
  rw [← MemorySimulation.step, h.running]
  exact Staging.step_ofEvm evm h.output

/-- A machine an entry hands back runs its frame's message. -/
theorem enterWith_run_sta {f : Frame} {start : Devm} {evm : Evm}
    (h : enterWith f start = .run evm) : evm.sta = f.message.sevm := by
  unfold enterWith at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · cases h; rfl
    · cases h; rfl

/-- The new entry of a spawned child against the old one. -/
theorem enter_rel (child : Checked.Frame) :
    (enter (Checked.Trace.frame child)).observe = (Checked.enter child).toLegacy := by
  rw [Frame.Entry.observe_enter, frame_eq, Checked.enter_toLegacy]

/-- The new entry of a top-level frame against the old one. -/
theorem enterWith_rel (f : Checked.Frame) :
    (enterWith (Checked.Trace.frame f) (Checked.Trace.frame f).checkpoint.toDevm).observe =
      (Checked.enterWith f f.checkpoint).toLegacy := by
  rw [Frame.Entry.observe_enterWith _ rfl, Staging.enterWith_ofDevm_toDevm, frame_eq,
    show f.toLegacy.checkpoint = f.checkpoint.toLegacy from rfl, Checked.enterWith_toLegacy]

/-- The new settlement against the old one. -/
theorem settle_rel (child : Checked.Frame) {raw : Execution} {x : Except Fault Checked.Frame.Exit}
    (h : x.map Checked.Frame.Exit.toLegacy = Frame.Exit.ofExecution raw) :
    settle (Checked.Trace.frame child) raw = x >>= Checked.settle child := by
  rw [settle_eq, ← h, frame_eq]
  rcases x with fault | e
  · rfl
  · exact Checked.settle_toLegacy child e

/-- The new child run against the old one. -/
theorem execFueled_rel (fuel : Nat) {msg : Message} {r : Checked.Frame.Running} {evm : Evm}
    (h : Related msg r evm) :
    (Checked.execFueled r fuel).run.map (Except.map Checked.Frame.Exit.toLegacy) =
      (Jaune.execFueled evm fuel).run.map Frame.Exit.ofExecution := by
  rw [← Checked.execFueled_toLegacy, h.running]
  exact execFueled_square fuel evm h.output

/-- The new resumption against the old one, for a caller saved with its RIPEMD-160 flag down. -/
theorem resume_rel (rules : ForkRules) (p : Pending) (saved : Checked.Frame.State)
    (result : Frame.Result) (hflag : (Checked.Trace.state saved).trail.touchedRIPEMD160 = false) :
    (resume rules p (Checked.Trace.state saved) result).map (Except.mapResultState Frame.State.ofDevm) =
      (Checked.resume rules (Staging.Pending.ofLegacy p) saved result).map
        Checked.ResumeResult.toLegacy := by
  rw [resume_ofDevm _ _ _ _ hflag, state_eq, Checked.resume_toLegacy]

/-- A resumed caller has the output its spawn passed through. -/
theorem resume_output {rules : ForkRules} {p : Pending} {saved : Frame.State}
    {result : Frame.Result} {d : Devm} (h : resume rules p saved result = .ok (.ok d)) :
    d.output = p.legacyOutput := by
  rw [resume_eq] at h
  revert h
  cases Staging.resume rules (.ofLegacy p) saved result with
  | error e => intro h; cases h
  | ok x =>
    rcases x with ⟨reason, s⟩ | s
    · intro h; cases h
    · intro h; cases h; rfl

/-- How the old caller goes on after its child, against the new one. -/
inductive ResumedRel (msg : Message) (pc : Nat) (sta : Sevm) (context : CallContext) :
    Execution → Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State) →
    Prop
  /-- Both go on, from related states. -/
  | resumed {d : Devm} {s : Checked.Frame.State} :
      Related msg ⟨pc, context, s⟩ ⟨pc, sta, d⟩ →
      Checked.Trace.resumedRaw (.ok (.ok s)) = normRaw (.ok d) →
      ResumedRel msg pc sta context (.ok d) (.ok (.ok s))
  /-- Both stop, with the same normalised raw result. -/
  | stopped {e : EvmError × Devm} {x} :
      (∀ s, x ≠ .ok (.ok s)) → normRaw (.error e) = Checked.Trace.resumedRaw x →
      ResumedRel msg pc sta context (.error e) x

theorem resumedRel {msg : Message} {r : Checked.Frame.Running} {evm : Evm} (h : Related msg r evm)
    {child : Checked.Frame} {p : Pending} {pc : Nat}
    (hflag : (Checked.Trace.frame child).checkpoint.trail.touchedRIPEMD160 = false)
    (hpo : p.legacyOutput = []) (settled : Except Fault Frame.Result) :
    ResumedRel msg pc evm.sta r.context
      (Trace.resumedRaw evm.sta.benvStat.rules (Checked.Trace.frame child) p settled)
      (Checked.Trace.resumed r.context.block.rules child (Staging.Pending.ofLegacy p) settled) := by
  have hctx : r.context = CallContext.ofSevm evm.sta := congrArg Frame.Running.context h.running
  have hrules : r.context.block.rules = evm.sta.benvStat.rules := by rw [hctx]; rfl
  rcases settled with fault | result
  · apply ResumedRel.stopped
    · intro s hs; cases hs
    · simp only [Checked.Trace.resumedRaw]
      exact normRaw_of_fault (ofExecution_fault fault _)
  · have hr : (resume evm.sta.benvStat.rules p (Checked.Trace.frame child).checkpoint result).map
        (Except.mapResultState Frame.State.ofDevm) =
        (Checked.resume evm.sta.benvStat.rules (Staging.Pending.ofLegacy p) child.checkpoint
          result).map Checked.ResumeResult.toLegacy :=
      resume_rel evm.sta.benvStat.rules p child.checkpoint result hflag
    have ho := fun d (hd : resume evm.sta.benvStat.rules p (Checked.Trace.frame child).checkpoint
        result = .ok (.ok d)) => resume_output hd
    simp only [Trace.resumedRaw, Checked.Trace.resumed, hrules]
    revert hr ho
    rcases resume evm.sta.benvStat.rules p (Checked.Trace.frame child).checkpoint result with
      fault | (⟨reason, d⟩ | d) <;>
    rcases Checked.resume evm.sta.benvStat.rules (Staging.Pending.ofLegacy p) child.checkpoint
      result with fault' | (⟨reason', s⟩ | s) <;>
    intro hr ho <;> simp only [Except.map, Except.mapResultState, Checked.ResumeResult.toLegacy,
      reduceCtorEq, Except.error.injEq, Except.ok.injEq, Prod.mk.injEq] at hr
    · subst hr
      apply ResumedRel.stopped
      · intro s hs; cases hs
      · exact normRaw_of_fault (ofExecution_fault _ _)
    · obtain ⟨rfl, hs⟩ := hr
      apply ResumedRel.stopped
      · intro s' hs'; cases hs'
      simp only [normRaw, Frame.Exit.ofExecution, Frame.Exit.toExecution, Checked.Trace.resumedRaw,
        Checked.Trace.devm, hs, state_eq]
    · have hdo : d.output = [] := (ho d rfl).trans hpo
      refine .resumed ⟨?_, h.static, hdo⟩ ?_
      · show (⟨pc, r.context, s.toLegacy⟩ : Frame.Running) = ⟨pc, CallContext.ofSevm evm.sta, _⟩
        rw [hctx, ← hr]
      · simp only [normRaw, Frame.Exit.ofExecution, Frame.Exit.toExecution, Checked.Trace.resumedRaw,
          Checked.Trace.devm, hr, hdo, state_eq]
        rfl

/-! ### Results erase to their values -/

theorem trace_cast {m : Type → Type} [Functor m] {a b : Fueled (EvmError × Devm) Devm} (h : a = b)
    (x : m (Trace.CertifiedResult a)) :
    Trace.CertifiedResult.nextFrame <$> cast (congrArg (fun e => m (Trace.CertifiedResult e)) h) x =
      Trace.CertifiedResult.nextFrame <$> x := by
  subst h; rfl

theorem checked_cast {m : Type → Type} [Functor m] {a b : Fueled Fault Checked.Frame.Exit}
    (h : a = b) (x : m (Checked.Trace.CertifiedResult a)) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        cast (congrArg (fun e => m (Checked.Trace.CertifiedResult e)) h) x =
      Checked.Trace.CertifiedResult.nextFrame <$> x := by
  subst h; rfl

theorem trace_cast' {m : Type → Type} [Functor m] {a b : Fueled (EvmError × Devm) Devm}
    (h : m (Trace.CertifiedResult a) = m (Trace.CertifiedResult b)) (hab : a = b)
    (x : m (Trace.CertifiedResult a)) :
    Trace.CertifiedResult.nextFrame <$> cast h x = Trace.CertifiedResult.nextFrame <$> x := by
  subst hab; rfl

theorem checked_cast' {m : Type → Type} [Functor m] {a b : Fueled Fault Checked.Frame.Exit}
    (h : m (Checked.Trace.CertifiedResult a) = m (Checked.Trace.CertifiedResult b)) (hab : a = b)
    (x : m (Checked.Trace.CertifiedResult a)) :
    Checked.Trace.CertifiedResult.nextFrame <$> cast h x =
      Checked.Trace.CertifiedResult.nextFrame <$> x := by
  subst hab; rfl

/-! ### `normalize`, one constructor at a time -/

theorem normalize_instruction (c : Trace.Context) (b : Evm) (st : Step) :
    normalize (.instruction c b st) = .instruction c (normEvm b) (normStep st) := rfl
theorem normalize_entered_done (c : Trace.Context) (f : Frame) (r : Except Fault Frame.Result) :
    normalize (.entered c f (.done r)) = .entered c f (.done r) := rfl
theorem normalize_entered_run (c : Trace.Context) (f : Frame) (evm : Evm) :
    normalize (.entered c f (.run evm)) = .entered c f (.run (normEvm evm)) := rfl
theorem normalize_exited_none (c : Trace.Context) :
    normalize (.exited c none) = .exited c none := rfl
theorem normalize_exited_some (c : Trace.Context) (raw : Execution) :
    normalize (.exited c (some raw)) = .exited c (some (normRaw raw)) := rfl
theorem normalize_settled (c : Trace.Context) (f : Frame) (r : Except Fault Frame.Result) :
    normalize (.settled c f r) = .settled c f r := rfl
theorem normalize_resumed (c : Trace.Context) (n : Nat) (raw : Execution) :
    normalize (.resumed c n raw) = .resumed c n (normRaw raw) := rfl

section Unfold

variable {m : Type → Type} [Monad m] [LawfulMonad m] (sink : Trace.Sink m)

theorem trace_bind {α : Type} {e : Fueled (EvmError × Devm) Devm} (x : m (Trace.CertifiedResult e))
    (k : Trace.CertifiedResult e → m α) :
    x >>= k = (Trace.CertifiedResult.nextFrame <$> x) >>= fun n => k ⟨e, n, rfl⟩ := by
  rw [bind_map_left]
  congr 1
  funext c
  obtain ⟨v, n, hv⟩ := c
  subst hv
  rfl

theorem checked_bind {α : Type} {e : Fueled Fault Checked.Frame.Exit}
    (x : m (Checked.Trace.CertifiedResult e)) (k : Checked.Trace.CertifiedResult e → m α) :
    x >>= k = (Checked.Trace.CertifiedResult.nextFrame <$> x) >>= fun n => k ⟨e, n, rfl⟩ := by
  rw [bind_map_left]
  congr 1
  funext c
  obtain ⟨v, n, hv⟩ := c
  subst hv
  rfl

/-! #### The old tracer, one outcome at a time -/

theorem trace_zero (evm : Evm) (context : Trace.Context) (nextFrame : Nat) :
    Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink evm 0 context nextFrame =
      (do sink (.exited context none); pure nextFrame) := by
  rw [Trace.execFueled]
  simp only [map_bind, map_pure]

theorem trace_halt {evm : Evm} {fuel : Nat} {raw : Execution} (hstep : Evm.step evm = .halt raw)
    (context : Trace.Context) (nextFrame : Nat) :
    Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink evm (fuel + 1) context nextFrame =
      (do
        sink (.instruction context evm (.halt raw))
        sink (.exited context (some raw))
        pure nextFrame) := by
  rw [Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind, map_pure]

theorem trace_next {evm : Evm} {fuel : Nat} {pc : Nat} {d : Devm} (hstep : Evm.step evm = .next pc d)
    (context : Trace.Context) (nextFrame : Nat) :
    Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink evm (fuel + 1) context nextFrame =
      (do
        sink (.instruction context evm (.next pc d))
        Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink ⟨pc, evm.sta, d⟩ fuel context nextFrame) := by
  rw [Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  rw [trace_cast' _ (by simp only [Jaune.execFueled, hstep])]

theorem trace_done_error {evm : Evm} {fuel : Nat} {child : Frame} {p : Pending} {pc : Nat}
    {settled : Except Fault Frame.Result} {error : EvmError × Devm}
    (hstep : Evm.step evm = .spawn child p pc) (hentry : enter child = .done settled)
    (hresume : Trace.resumedRaw evm.sta.benvStat.rules child p settled = .error error)
    (context : Trace.Context) (nextFrame : Nat) :
    Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink evm (fuel + 1) context nextFrame =
      (do
        sink (.instruction context evm (.spawn child p pc))
        sink (.entered { context with frame := nextFrame, depth := context.depth + 1 } child
          (.done settled))
        sink (.settled { context with frame := nextFrame, depth := context.depth + 1 } child settled)
        sink (.resumed context nextFrame (.error error))
        sink (.exited context (some (.error error)))
        pure (nextFrame + 1)) := by
  rw [Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hentry] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hresume] at h <;> cases h
  simp only [map_bind, map_pure]

theorem trace_done_ok {evm : Evm} {fuel : Nat} {child : Frame} {p : Pending} {pc : Nat}
    {settled : Except Fault Frame.Result} {d : Devm}
    (hstep : Evm.step evm = .spawn child p pc) (hentry : enter child = .done settled)
    (hresume : Trace.resumedRaw evm.sta.benvStat.rules child p settled = .ok d)
    (context : Trace.Context) (nextFrame : Nat) :
    Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink evm (fuel + 1) context nextFrame =
      (do
        sink (.instruction context evm (.spawn child p pc))
        sink (.entered { context with frame := nextFrame, depth := context.depth + 1 } child
          (.done settled))
        sink (.settled { context with frame := nextFrame, depth := context.depth + 1 } child settled)
        sink (.resumed context nextFrame (.ok d))
        Trace.CertifiedResult.nextFrame <$>
          Trace.execFueled sink ⟨pc, evm.sta, d⟩ fuel context (nextFrame + 1)) := by
  rw [Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hentry] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hresume] at h <;> cases h
  simp only [map_bind]
  rw [trace_cast' _ (by rw [Trace.execFueled_spawn hstep, hentry]; dsimp only; rw [hresume])]

theorem trace_run_none {evm : Evm} {fuel : Nat} {child : Frame} {p : Pending} {pc : Nat}
    {cevm : Evm} (hstep : Evm.step evm = .spawn child p pc) (hentry : enter child = .run cevm)
    (hrun : (Jaune.execFueled cevm fuel).run = none) (context : Trace.Context) (nextFrame : Nat) :
    Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink evm (fuel + 1) context nextFrame =
      (do
        sink (.instruction context evm (.spawn child p pc))
        sink (.entered { context with frame := nextFrame, depth := context.depth + 1 } child
          (.run cevm))
        let n ← Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink cevm fuel
          { context with frame := nextFrame, depth := context.depth + 1 } (nextFrame + 1)
        sink (.exited context none)
        pure n) := by
  rw [Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hentry] at h <;> cases h
  simp only [map_bind]
  refine bind_congr fun _ => bind_congr fun _ => ?_
  rw [trace_bind]
  refine bind_congr fun n => ?_
  dsimp only
  split <;> rename_i h <;> rw [hrun] at h <;> cases h
  simp only [map_bind, map_pure]

theorem trace_run_error {evm : Evm} {fuel : Nat} {child : Frame} {p : Pending} {pc : Nat}
    {cevm : Evm} {raw : Execution} {error : EvmError × Devm}
    (hstep : Evm.step evm = .spawn child p pc) (hentry : enter child = .run cevm)
    (hrun : (Jaune.execFueled cevm fuel).run = some raw)
    (hresume : Trace.resumedRaw evm.sta.benvStat.rules child p (settle child raw) = .error error)
    (context : Trace.Context) (nextFrame : Nat) :
    Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink evm (fuel + 1) context nextFrame =
      (do
        sink (.instruction context evm (.spawn child p pc))
        sink (.entered { context with frame := nextFrame, depth := context.depth + 1 } child
          (.run cevm))
        let n ← Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink cevm fuel
          { context with frame := nextFrame, depth := context.depth + 1 } (nextFrame + 1)
        sink (.settled { context with frame := nextFrame, depth := context.depth + 1 } child
          (settle child raw))
        sink (.resumed context nextFrame (.error error))
        sink (.exited context (some (.error error)))
        pure n) := by
  rw [Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hentry] at h <;> cases h
  simp only [map_bind]
  refine bind_congr fun _ => bind_congr fun _ => ?_
  rw [trace_bind]
  refine bind_congr fun n => ?_
  dsimp only
  split <;> rename_i h <;> rw [hrun] at h <;> cases h
  simp only [map_bind]
  refine bind_congr fun _ => ?_
  split <;> rename_i h <;> rw [hresume] at h <;> cases h
  simp only [map_bind, map_pure]

theorem trace_run_ok {evm : Evm} {fuel : Nat} {child : Frame} {p : Pending} {pc : Nat}
    {cevm : Evm} {raw : Execution} {d : Devm}
    (hstep : Evm.step evm = .spawn child p pc) (hentry : enter child = .run cevm)
    (hrun : (Jaune.execFueled cevm fuel).run = some raw)
    (hresume : Trace.resumedRaw evm.sta.benvStat.rules child p (settle child raw) = .ok d)
    (context : Trace.Context) (nextFrame : Nat) :
    Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink evm (fuel + 1) context nextFrame =
      (do
        sink (.instruction context evm (.spawn child p pc))
        sink (.entered { context with frame := nextFrame, depth := context.depth + 1 } child
          (.run cevm))
        let n ← Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink cevm fuel
          { context with frame := nextFrame, depth := context.depth + 1 } (nextFrame + 1)
        sink (.settled { context with frame := nextFrame, depth := context.depth + 1 } child
          (settle child raw))
        sink (.resumed context nextFrame (.ok d))
        Trace.CertifiedResult.nextFrame <$> Trace.execFueled sink ⟨pc, evm.sta, d⟩ fuel context n) := by
  rw [Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hentry] at h <;> cases h
  simp only [map_bind]
  refine bind_congr fun _ => bind_congr fun _ => ?_
  rw [trace_bind]
  refine bind_congr fun n => ?_
  dsimp only
  split <;> rename_i h <;> rw [hrun] at h <;> cases h
  simp only [map_bind]
  refine bind_congr fun _ => ?_
  split <;> rename_i h <;> rw [hresume] at h <;> cases h
  simp only [map_bind]
  rw [trace_cast' _ (by
      rw [Trace.execFueled_spawn hstep, hentry]
      dsimp only
      rw [hrun]
      dsimp only [Option.map]
      rw [hresume])]

/-! #### The new tracer, one outcome at a time -/

theorem checked_zero (msg : Message) (r : Checked.Frame.Running) (context : Trace.Context)
    (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$> Checked.Trace.execFueled sink msg r 0 context nextFrame =
      (do sink (.exited context none); pure nextFrame) := by
  rw [Checked.Trace.execFueled]
  simp only [map_bind, map_pure]

theorem checked_fault {msg : Message} {r : Checked.Frame.Running} {fuel : Nat} {fault : Fault}
    (hstep : Checked.step r = .error fault) (context : Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled sink msg r (fuel + 1) context nextFrame =
      (do
        sink (.instruction context (Checked.Trace.evm msg r) (Checked.Trace.step (.error fault)))
        sink (.exited context (some (Checked.Trace.faultRaw fault)))
        pure nextFrame) := by
  rw [Checked.Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind, map_pure]

theorem checked_exit {msg : Message} {r : Checked.Frame.Running} {fuel : Nat}
    {e : Checked.Frame.Exit} (hstep : Checked.step r = .ok (.exit e)) (context : Trace.Context)
    (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled sink msg r (fuel + 1) context nextFrame =
      (do
        sink (.instruction context (Checked.Trace.evm msg r) (Checked.Trace.step (.ok (.exit e))))
        sink (.exited context (some (Checked.Trace.exitRaw e)))
        pure nextFrame) := by
  rw [Checked.Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind, map_pure]

theorem checked_next {msg : Message} {r : Checked.Frame.Running} {fuel : Nat} {pc : Nat}
    {s : Checked.Frame.State} (hstep : Checked.step r = .ok (.next pc s)) (context : Trace.Context)
    (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled sink msg r (fuel + 1) context nextFrame =
      (do
        sink (.instruction context (Checked.Trace.evm msg r) (Checked.Trace.step (.ok (.next pc s))))
        Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled sink msg ⟨pc, r.context, s⟩ fuel context nextFrame) := by
  rw [Checked.Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  rw [checked_cast' _ (by simp only [Checked.execFueled, hstep])]

/-- The rows a stopped caller emits after its child. -/
abbrev stopRows (context : Trace.Context) (nextFrame : Nat)
    (x : Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State))
    (n : Nat) : m Nat := do
  sink (.resumed context nextFrame (Checked.Trace.resumedRaw x))
  sink (.exited context (some (Checked.Trace.resumedRaw x)))
  pure n

theorem checked_done_ok {msg : Message} {r : Checked.Frame.Running} {fuel : Nat}
    {child : Checked.Frame} {p : Staging.Pending} {pc : Nat} {settled : Except Fault Frame.Result}
    {s : Checked.Frame.State} (hstep : Checked.step r = .ok (.spawn child p pc))
    (hentry : Checked.enter child = .done settled)
    (hresume : Checked.Trace.resumed r.context.block.rules child p settled = .ok (.ok s))
    (context : Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled sink msg r (fuel + 1) context nextFrame =
      (do
        sink (.instruction context (Checked.Trace.evm msg r)
          (Checked.Trace.step (.ok (.spawn child p pc))))
        sink (.entered { context with frame := nextFrame, depth := context.depth + 1 }
          (Checked.Trace.frame child) (.done settled))
        sink (.settled { context with frame := nextFrame, depth := context.depth + 1 }
          (Checked.Trace.frame child) settled)
        sink (.resumed context nextFrame (Checked.Trace.resumedRaw (.ok (.ok s))))
        Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled sink msg ⟨pc, r.context, s⟩ fuel context (nextFrame + 1)) := by
  rw [Checked.Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hentry] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hresume] at h <;> cases h
  simp only [map_bind]
  rw [checked_cast' _ (by
      rw [Checked.Trace.execFueled_spawn hstep, hentry]
      dsimp only
      rw [hresume]
      try rfl)]

theorem checked_done_stop {msg : Message} {r : Checked.Frame.Running} {fuel : Nat}
    {child : Checked.Frame} {p : Staging.Pending} {pc : Nat} {settled : Except Fault Frame.Result}
    {x : Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State)}
    (hstep : Checked.step r = .ok (.spawn child p pc))
    (hentry : Checked.enter child = .done settled)
    (hresume : Checked.Trace.resumed r.context.block.rules child p settled = x)
    (hx : ∀ s, x ≠ .ok (.ok s)) (context : Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled sink msg r (fuel + 1) context nextFrame =
      (do
        sink (.instruction context (Checked.Trace.evm msg r)
          (Checked.Trace.step (.ok (.spawn child p pc))))
        sink (.entered { context with frame := nextFrame, depth := context.depth + 1 }
          (Checked.Trace.frame child) (.done settled))
        sink (.settled { context with frame := nextFrame, depth := context.depth + 1 }
          (Checked.Trace.frame child) settled)
        stopRows sink context nextFrame x (nextFrame + 1)) := by
  rw [Checked.Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hentry] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hresume] at h <;> subst h
  · exact absurd rfl (hx _)
  all_goals simp only [map_bind, map_pure, stopRows]

theorem checked_run_none {msg : Message} {r : Checked.Frame.Running} {fuel : Nat}
    {child : Checked.Frame} {p : Staging.Pending} {pc : Nat} {cr : Checked.Frame.Running}
    (hstep : Checked.step r = .ok (.spawn child p pc)) (hentry : Checked.enter child = .run cr)
    (hrun : (Checked.execFueled cr fuel).run = none) (context : Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled sink msg r (fuel + 1) context nextFrame =
      (do
        sink (.instruction context (Checked.Trace.evm msg r)
          (Checked.Trace.step (.ok (.spawn child p pc))))
        sink (.entered { context with frame := nextFrame, depth := context.depth + 1 }
          (Checked.Trace.frame child) (.run (Checked.Trace.evm child.message cr)))
        let n ← Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled sink child.message cr fuel
            { context with frame := nextFrame, depth := context.depth + 1 } (nextFrame + 1)
        sink (.exited context none)
        pure n) := by
  rw [Checked.Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hentry] at h <;> cases h
  simp only [map_bind]
  refine bind_congr fun _ => bind_congr fun _ => ?_
  rw [checked_bind]
  refine bind_congr fun n => ?_
  dsimp only
  split <;> rename_i h <;> rw [hrun] at h <;> cases h
  simp only [map_bind, map_pure]

theorem checked_run_ok {msg : Message} {r : Checked.Frame.Running} {fuel : Nat}
    {child : Checked.Frame} {p : Staging.Pending} {pc : Nat} {cr : Checked.Frame.Running}
    {x : Except Fault Checked.Frame.Exit} {s : Checked.Frame.State}
    (hstep : Checked.step r = .ok (.spawn child p pc)) (hentry : Checked.enter child = .run cr)
    (hrun : (Checked.execFueled cr fuel).run = some x)
    (hresume : Checked.Trace.resumed r.context.block.rules child p (x >>= Checked.settle child) =
      .ok (.ok s))
    (context : Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled sink msg r (fuel + 1) context nextFrame =
      (do
        sink (.instruction context (Checked.Trace.evm msg r)
          (Checked.Trace.step (.ok (.spawn child p pc))))
        sink (.entered { context with frame := nextFrame, depth := context.depth + 1 }
          (Checked.Trace.frame child) (.run (Checked.Trace.evm child.message cr)))
        let n ← Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled sink child.message cr fuel
            { context with frame := nextFrame, depth := context.depth + 1 } (nextFrame + 1)
        sink (.settled { context with frame := nextFrame, depth := context.depth + 1 }
          (Checked.Trace.frame child) (x >>= Checked.settle child))
        sink (.resumed context nextFrame (Checked.Trace.resumedRaw (.ok (.ok s))))
        Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled sink msg ⟨pc, r.context, s⟩ fuel context n) := by
  rw [Checked.Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hentry] at h <;> cases h
  simp only [map_bind]
  refine bind_congr fun _ => bind_congr fun _ => ?_
  rw [checked_bind]
  refine bind_congr fun n => ?_
  dsimp only
  split <;> rename_i h <;> rw [hrun] at h <;> cases h
  simp only [map_bind]
  refine bind_congr fun _ => ?_
  split <;> rename_i h <;> rw [hresume] at h <;> cases h
  simp only [map_bind]
  rw [checked_cast' _ (by
      rw [Checked.Trace.execFueled_spawn hstep, hentry]
      dsimp only
      rw [hrun]
      dsimp only [Option.map]
      rw [hresume]
      try rfl)]

theorem checked_run_stop {msg : Message} {r : Checked.Frame.Running} {fuel : Nat}
    {child : Checked.Frame} {p : Staging.Pending} {pc : Nat} {cr : Checked.Frame.Running}
    {x : Except Fault Checked.Frame.Exit}
    {y : Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State)}
    (hstep : Checked.step r = .ok (.spawn child p pc)) (hentry : Checked.enter child = .run cr)
    (hrun : (Checked.execFueled cr fuel).run = some x)
    (hresume : Checked.Trace.resumed r.context.block.rules child p (x >>= Checked.settle child) = y)
    (hy : ∀ s, y ≠ .ok (.ok s)) (context : Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled sink msg r (fuel + 1) context nextFrame =
      (do
        sink (.instruction context (Checked.Trace.evm msg r)
          (Checked.Trace.step (.ok (.spawn child p pc))))
        sink (.entered { context with frame := nextFrame, depth := context.depth + 1 }
          (Checked.Trace.frame child) (.run (Checked.Trace.evm child.message cr)))
        let n ← Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled sink child.message cr fuel
            { context with frame := nextFrame, depth := context.depth + 1 } (nextFrame + 1)
        sink (.settled { context with frame := nextFrame, depth := context.depth + 1 }
          (Checked.Trace.frame child) (x >>= Checked.settle child))
        stopRows sink context nextFrame y n) := by
  rw [Checked.Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hentry] at h <;> cases h
  simp only [map_bind]
  refine bind_congr fun _ => bind_congr fun _ => ?_
  rw [checked_bind]
  refine bind_congr fun n => ?_
  dsimp only
  split <;> rename_i h <;> rw [hrun] at h <;> cases h
  simp only [map_bind]
  refine bind_congr fun _ => ?_
  split <;> rename_i h <;> rw [hresume] at h <;> subst h
  · exact absurd rfl (hy _)
  all_goals simp only [map_bind, map_pure, stopRows]

end Unfold

/-! ### The event streams -/

section Events

variable {m : Type → Type} [Monad m] [LawfulMonad m] (sink : Trace.Sink m)

/-- **The driver.** From related starts, the checked tracer with `sink` makes the same sink calls,
in the same order, as the `Devm` tracer with `sink` after `normalize`, and numbers the frames the
same way. -/
theorem execFueled_events (fuel : Nat) :
    ∀ (msg : Message) (r : Checked.Frame.Running) (evm : Evm) (context : Trace.Context)
      (nextFrame : Nat), Related msg r evm →
      Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled sink msg r fuel context nextFrame =
        Trace.CertifiedResult.nextFrame <$>
          Trace.execFueled (fun e => sink (normalize e)) evm fuel context nextFrame := by
  induction fuel with
  | zero =>
    intro msg r evm context nextFrame _
    rw [checked_zero, trace_zero]
    rfl
  | succ fuel ih =>
    intro msg r evm context nextFrame h
    have hrel := step_rel h
    have hpost := OutputWalk.Evm.step_post evm h.output
    have hevm := h.evm_eq
    have hctx : r.context = CallContext.ofSevm evm.sta := congrArg Frame.Running.context h.running
    cases hc : Checked.step r with
    | error fault =>
      rw [hc] at hrel
      cases hw : Evm.step evm with
      | halt raw =>
        rw [hw] at hrel
        have hraw : normRaw raw = Checked.Trace.faultRaw fault :=
          normRaw_of_square (x := .error fault) (by
            simp only [Jaune.Step.observe, Except.map] at hrel ⊢
            revert hrel; cases Frame.Exit.ofExecution raw <;> simp)
        rw [checked_fault sink hc, trace_halt _ hw]
        simp only [normalize_instruction, normalize_exited_some, normStep, hevm, hraw, Checked.Trace.step]
      | next pc d => rw [hw] at hrel; simp [Jaune.Step.observe, Except.map] at hrel
      | spawn child p pc => rw [hw] at hrel; simp [Jaune.Step.observe, Except.map] at hrel
    | ok step =>
      rw [hc] at hrel
      cases step with
      | exit e =>
        cases hw : Evm.step evm with
        | halt raw =>
          rw [hw] at hrel
          have hraw : normRaw raw = Checked.Trace.exitRaw e :=
            normRaw_of_square (x := .ok e) (by
              simp only [Jaune.Step.observe, Except.map, Checked.Step.toLegacy] at hrel ⊢
              revert hrel; cases Frame.Exit.ofExecution raw <;> simp)
          rw [checked_exit sink hc, trace_halt _ hw]
          simp only [normalize_instruction, normalize_exited_some, normStep, hevm, hraw, Checked.Trace.step]
        | next pc d => rw [hw] at hrel; simp [Jaune.Step.observe, Except.map, Checked.Step.toLegacy] at hrel
        | spawn child p pc =>
          rw [hw] at hrel; simp [Jaune.Step.observe, Except.map, Checked.Step.toLegacy] at hrel
      | next pc s =>
        cases hw : Evm.step evm with
        | halt raw =>
          rw [hw] at hrel
          simp only [Jaune.Step.observe, Except.map, Checked.Step.toLegacy] at hrel
          revert hrel; cases Frame.Exit.ofExecution raw <;> simp
        | next pc' d =>
          rw [hw] at hrel
          simp only [Jaune.Step.observe, Except.map, Checked.Step.toLegacy, Except.ok.injEq,
            Staging.Step.next.injEq] at hrel
          obtain ⟨rfl, hs⟩ := hrel
          have hd : d.output = [] := by have := hpost; rw [hw] at this; exact this
          rw [checked_next sink hc, trace_next _ hw]
          simp only [normalize_instruction, normStep, hevm, Checked.Trace.step]
          have hdevm : Checked.Trace.devm s = normDevm d := by
            simp only [Checked.Trace.devm, normDevm, state_eq, hs]
          rw [hdevm]
          refine bind_congr fun _ => ?_
          refine ih msg _ _ context nextFrame ⟨?_, h.static, hd⟩
          show (⟨pc, r.context, s.toLegacy⟩ : Frame.Running) = ⟨pc, CallContext.ofSevm evm.sta, _⟩
          rw [hctx, hs]
        | spawn child p pc' =>
          rw [hw] at hrel; simp [Jaune.Step.observe, Except.map, Checked.Step.toLegacy] at hrel
      | spawn child p pc =>
        cases hw : Evm.step evm with
        | halt raw =>
          rw [hw] at hrel
          simp only [Jaune.Step.observe, Except.map, Checked.Step.toLegacy] at hrel
          revert hrel; cases Frame.Exit.ofExecution raw <;> simp
        | next pc' d =>
          rw [hw] at hrel; simp [Jaune.Step.observe, Except.map, Checked.Step.toLegacy] at hrel
        | spawn child' p' pc' =>
          rw [hw] at hrel
          simp only [Jaune.Step.observe, Except.map, Checked.Step.toLegacy, Except.ok.injEq,
            Staging.Step.spawn.injEq] at hrel
          obtain ⟨hchild, hp, rfl⟩ := hrel
          have hchild' : child' = Checked.Trace.frame child := hchild.symm
          subst hchild' hp
          have hpost' := hpost
          rw [hw] at hpost'
          obtain ⟨hpo, hflag⟩ := hpost'
          have hinstr : normalize (.instruction context evm (.spawn (Checked.Trace.frame child) p' pc)) =
              .instruction context (Checked.Trace.evm msg r)
                (Checked.Trace.step (.ok (.spawn child (Staging.Pending.ofLegacy p') pc))) := by
            simp only [normalize, normStep, hevm, Checked.Trace.step, normPending,
              Checked.Trace.pending]
            rfl
          have hrules : r.context.block.rules = evm.sta.benvStat.rules := by rw [hctx]; rfl
          have hentry := enter_rel child
          cases hce : Checked.enter child with
          | done settled =>
            rw [hce] at hentry
            have hwe : enter (Checked.Trace.frame child) = .done settled := by
              revert hentry
              cases enter (Checked.Trace.frame child) <;>
                simp [Frame.Entry.observe, Checked.Frame.Entry.toLegacy]
            have hres := resumedRel h (pc := pc) hflag hpo settled
            revert hres
            generalize hx : Checked.Trace.resumed r.context.block.rules child
              (Staging.Pending.ofLegacy p') settled = x
            generalize hy : Trace.resumedRaw evm.sta.benvStat.rules (Checked.Trace.frame child) p'
              settled = y
            intro hres
            cases hres with
            | resumed hR hraw =>
              rw [checked_done_ok sink hc hce hx, trace_done_ok _ hw hwe hy]
              simp only [hinstr]
              refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => ?_
              rw [hraw]
              refine bind_congr fun _ => ?_
              exact ih msg _ _ context (nextFrame + 1) hR
            | stopped hne hraw =>
              rw [checked_done_stop sink hc hce hx hne, trace_done_error _ hw hwe hy]
              simp only [hinstr]
              simp only [stopRows, normalize_entered_done, normalize_exited_some,
                normalize_settled, normalize_resumed, hraw]
          | run cr =>
            rw [hce] at hentry
            obtain ⟨cevm, hwe, hcr⟩ : ∃ cevm, enter (Checked.Trace.frame child) = .run cevm ∧
                cr.toLegacy = Frame.Running.ofEvm cevm := by
              revert hentry
              cases enter (Checked.Trace.frame child) with
              | done _ => simp [Frame.Entry.observe, Checked.Frame.Entry.toLegacy]
              | run cevm =>
                intro hentry
                simp only [Frame.Entry.observe, Checked.Frame.Entry.toLegacy,
                  Staging.Frame.Entry.run.injEq] at hentry
                exact ⟨cevm, rfl, hentry.symm⟩
            have hR : Related child.message cr cevm :=
              ⟨hcr, enterWith_run_sta hwe, enter_run_output hwe⟩
            have hcevm : Checked.Trace.evm child.message cr = normEvm cevm := hR.evm_eq
            have hrun := execFueled_rel fuel hR
            cases hcx : (Checked.execFueled cr fuel).run with
            | none =>
              rw [hcx] at hrun
              have hwx : (Jaune.execFueled cevm fuel).run = none := by
                revert hrun; cases (Jaune.execFueled cevm fuel).run <;> simp
              rw [checked_run_none sink hc hce hcx, trace_run_none _ hw hwe hwx]
              simp only [hinstr]; simp only [normalize_entered_run, normalize_exited_none, hcevm]
              refine bind_congr fun _ => bind_congr fun _ => ?_
              rw [ih child.message cr cevm _ (nextFrame + 1) hR]
            | some x =>
              rw [hcx] at hrun
              obtain ⟨raw, hwx, hraw⟩ : ∃ raw, (Jaune.execFueled cevm fuel).run = some raw ∧
                  x.map Checked.Frame.Exit.toLegacy = Frame.Exit.ofExecution raw := by
                revert hrun
                cases (Jaune.execFueled cevm fuel).run with
                | none => simp
                | some raw =>
                  intro hrun
                  simp only [Option.map, Option.some.injEq] at hrun
                  exact ⟨raw, rfl, hrun⟩
              have hsettle := settle_rel child hraw
              have hres := resumedRel h (pc := pc) hflag hpo (settle (Checked.Trace.frame child) raw)
              rw [hsettle] at hres
              revert hres
              generalize hxr : Checked.Trace.resumed r.context.block.rules child
                (Staging.Pending.ofLegacy p') (x >>= Checked.settle child) = xr
              generalize hy : Trace.resumedRaw evm.sta.benvStat.rules (Checked.Trace.frame child) p'
                (x >>= Checked.settle child) = y
              intro hres
              have hy' : Trace.resumedRaw evm.sta.benvStat.rules (Checked.Trace.frame child) p'
                  (settle (Checked.Trace.frame child) raw) = y := by rw [hsettle]; exact hy
              cases hres with
              | resumed hR' hraw' =>
                rw [checked_run_ok sink hc hce hcx hxr, trace_run_ok _ hw hwe hwx hy']
                simp only [hinstr]
                simp only [normalize_entered_run, normalize_settled, normalize_resumed, hcevm,
                  hsettle, hraw']
                refine bind_congr fun _ => bind_congr fun _ => ?_
                rw [ih child.message cr cevm _ (nextFrame + 1) hR]
                refine bind_congr fun n => bind_congr fun _ => bind_congr fun _ => ?_
                exact ih msg _ _ context n hR'
              | stopped hne hraw' =>
                rw [checked_run_stop sink hc hce hcx hxr hne, trace_run_error _ hw hwe hwx hy']
                simp only [hinstr]
                simp only [normalize_entered_run, normalize_exited_some, normalize_settled,
                  normalize_resumed, hcevm, hsettle, stopRows, hraw']
                refine bind_congr fun _ => bind_congr fun _ => ?_
                rw [ih child.message cr cevm _ (nextFrame + 1) hR]

theorem trace_exec (evm : Evm) (context : Trace.Context) (nextFrame : Nat) :
    Trace.ExecutionResult.nextFrame <$> Trace.exec sink evm context nextFrame =
      Trace.CertifiedResult.nextFrame <$>
        Trace.execFueled sink evm (sufficientFuel evm.dyna.gasMeasure) context nextFrame := by
  unfold Trace.exec
  rw [map_bind, trace_bind]
  refine (bind_congr fun n => ?_).trans (bind_pure _)
  dsimp only
  split <;> simp only [map_pure]

theorem checked_exec (msg : Message) (r : Checked.Frame.Running) (context : Trace.Context)
    (nextFrame : Nat) :
    Checked.Trace.ExecutionResult.nextFrame <$> Checked.Trace.exec sink msg r context nextFrame =
      Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled sink msg r (sufficientFuel r.state.machine.gasMeasure) context
          nextFrame := by
  unfold Checked.Trace.exec
  rw [map_bind, checked_bind]
  refine (bind_congr fun n => ?_).trans (bind_pure _)
  dsimp only
  split <;> simp only [map_pure]

/-- **The total driver.** -/
theorem exec_events {msg : Message} {r : Checked.Frame.Running} {evm : Evm} (h : Related msg r evm)
    (context : Trace.Context) (nextFrame : Nat) :
    Checked.Trace.ExecutionResult.nextFrame <$> Checked.Trace.exec sink msg r context nextFrame =
      Trace.ExecutionResult.nextFrame <$>
        Trace.exec (fun e => sink (normalize e)) evm context nextFrame := by
  rw [checked_exec, trace_exec,
    show r.state.machine.gasMeasure = evm.dyna.gasMeasure from
      congrArg (fun x : Frame.Running => x.state.machine.gasMeasure) h.running]
  exact execFueled_events sink _ msg r evm context nextFrame h

theorem trace_execution_bind {α : Type} {evm : Evm} (x : m (Trace.ExecutionResult evm))
    (k : Trace.ExecutionResult evm → m α) :
    x >>= k = (Trace.ExecutionResult.nextFrame <$> x) >>= fun n => k ⟨Jaune.exec evm, n, rfl⟩ := by
  rw [bind_map_left]
  congr 1
  funext c
  obtain ⟨v, n, hv⟩ := c
  subst hv
  rfl

theorem checked_execution_bind {α : Type} {r : Checked.Frame.Running}
    (x : m (Checked.Trace.ExecutionResult r)) (k : Checked.Trace.ExecutionResult r → m α) :
    x >>= k = (Checked.Trace.ExecutionResult.nextFrame <$> x) >>= fun n =>
      k ⟨Checked.exec r, n, rfl⟩ := by
  rw [bind_map_left]
  congr 1
  funext c
  obtain ⟨v, n, hv⟩ := c
  subst hv
  rfl

/-- **The top-level frame**, by frame number: for every checked frame, the checked tracer with
`sink` makes the same sink calls, in the same order, as the `Devm` tracer on the frame's
projection with `sink` after `normalize`. -/
theorem runFrame_nextFrame (f : Checked.Frame) (runId : String) :
    Checked.Trace.FrameResult.nextFrame <$> Checked.Trace.runFrame sink f runId =
      Trace.FrameResult.nextFrame <$>
        Trace.runFrame (fun e => sink (normalize e)) (Checked.Trace.frame f) runId := by
  have hentry := enterWith_rel f
  unfold Checked.Trace.runFrame Trace.runFrame
  dsimp only
  split
  next settled hce =>
    rw [hce] at hentry
    have hwe : enterWith (Checked.Trace.frame f) (Checked.Trace.frame f).checkpoint.toDevm =
        .done settled := by
      revert hentry
      cases enterWith (Checked.Trace.frame f) (Checked.Trace.frame f).checkpoint.toDevm <;>
        simp [Frame.Entry.observe, Checked.Frame.Entry.toLegacy]
    split <;> rename_i h <;> rw [hwe] at h <;> cases h
    simp only [map_bind, map_pure, normalize_entered_done, normalize_settled]
  next r hce =>
    rw [hce] at hentry
    obtain ⟨evm, hwe, hr⟩ : ∃ evm, enterWith (Checked.Trace.frame f)
        (Checked.Trace.frame f).checkpoint.toDevm = .run evm ∧
        r.toLegacy = Frame.Running.ofEvm evm := by
      revert hentry
      cases enterWith (Checked.Trace.frame f) (Checked.Trace.frame f).checkpoint.toDevm with
      | done _ => simp [Frame.Entry.observe, Checked.Frame.Entry.toLegacy]
      | run evm =>
        intro hentry
        simp only [Frame.Entry.observe, Checked.Frame.Entry.toLegacy,
          Staging.Frame.Entry.run.injEq] at hentry
        exact ⟨evm, rfl, hentry.symm⟩
    have hR : Related f.message r evm := ⟨hr, enterWith_run_sta hwe, enterWith_run_output rfl hwe⟩
    have hsettle : settle (Checked.Trace.frame f) (Jaune.exec evm) = Checked.exec r >>= Checked.settle f := by
      apply settle_rel
      rw [← Checked.exec_toLegacy, hr]
      exact exec_square evm hR.output
    split <;> rename_i h <;> rw [hwe] at h <;> cases h
    simp only [map_bind, map_pure, normalize_entered_run, normalize_settled, hR.evm_eq]
    refine bind_congr fun _ => ?_
    rw [checked_execution_bind, trace_execution_bind, exec_events sink hR]
    refine bind_congr fun n => ?_
    simp only [hsettle]

/-- **The top-level frame.** The same, with the returned value: the settled result, which is
`Checked.Frame.runTop f` on both sides. -/
theorem runFrame_events (f : Checked.Frame) (runId : String) :
    (fun x => (x.value, x.nextFrame)) <$> Checked.Trace.runFrame sink f runId =
      (fun x => (x.value, x.nextFrame)) <$>
        Trace.runFrame (fun e => sink (normalize e)) (Checked.Trace.frame f) runId := by
  have hl : (fun x : Checked.Trace.FrameResult f => (x.value, x.nextFrame)) =
      (fun n => (Checked.Frame.runTop f, n)) ∘ Checked.Trace.FrameResult.nextFrame := by
    funext x; rw [← x.erases]; rfl
  have hr : (fun x : Trace.FrameResult (Checked.Trace.frame f) => (x.value, x.nextFrame)) =
      (fun n => (Checked.Frame.runTop f, n)) ∘ Trace.FrameResult.nextFrame := by
    funext x; show (x.value, x.nextFrame) = (Checked.Frame.runTop f, x.nextFrame)
    rw [x.erases, Checked.Frame.runTop_square]; rfl
  rw [hl, hr, comp_map, comp_map, runFrame_nextFrame]

end Events

/-! ### The serialised stream -/

/-- The monad laws of `EST`, by unfolding; core states them for `EStateM` only. `IO` is
`EIO IO.Error`, whose monad is `EST`'s. Local to this module. -/
local instance instLawfulMonadEST (ε σ : Type) : LawfulMonad (EST ε σ) := .mk'
  (id_map := fun x => by
    funext s
    show (match x s with | .ok a s => EST.Out.ok (id a) s | .error e s => .error e s) = x s
    cases x s <;> rfl)
  (pure_bind := fun _ _ => rfl)
  (bind_assoc := fun x f g => by
    funext s
    show EST.bind (EST.bind x f) g s = EST.bind x (fun a => EST.bind (f a) g) s
    simp only [EST.bind]
    cases x s <;> rfl)

local instance instLawfulMonadEIO (ε : Type) : LawfulMonad (EIO ε) :=
  inferInstanceAs (LawfulMonad (EST ε IO.RealWorld))

/-- **Byte-identical serialisation.** For every checked frame, the checked tracer through the
JSON sink makes the same row writes as the `Devm` tracer through it on the frame's projection,
and returns the same result. -/
theorem runFrame_json (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (f : Checked.Frame) (runId : String) :
    (fun x => (x.value, x.nextFrame)) <$>
        Checked.Trace.runFrame (TraceJson.sink cfg state trace frames) f runId =
      (fun x => (x.value, x.nextFrame)) <$>
        Trace.runFrame (TraceJson.sink cfg state trace frames) (Checked.Trace.frame f) runId := by
  rw [runFrame_events]
  congr 2
  funext e
  exact sink_normalize cfg state trace frames e

/-- The checked top-level frame of a message projects onto the `Devm` one. -/
theorem frame_topFrame (msg : Msg) (isCreate : Bool) :
    Checked.Trace.frame (Checked.Trace.topFrame msg isCreate) = Frame.ofTop msg isCreate := rfl

/-- **The message runner's call.** `TraceMain` traces a message as
`Trace.runFrame sink (Frame.ofTop msg isCreate) runId`; the checked tracer on
`Checked.Trace.topFrame msg isCreate` writes the same rows and returns the same result. -/
theorem runFrame_json_top (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (msg : Msg) (isCreate : Bool) (runId : String) :
    (fun x => (x.value, x.nextFrame)) <$>
        Checked.Trace.runFrame (TraceJson.sink cfg state trace frames)
          (Checked.Trace.topFrame msg isCreate) runId =
      (fun x => (x.value, x.nextFrame)) <$>
        Trace.runFrame (TraceJson.sink cfg state trace frames) (Frame.ofTop msg isCreate) runId := by
  rw [runFrame_json, frame_topFrame]

/-- The traced top-level message result and its connection to the pure Checked run. -/
structure MessageResult (msg : Msg) where
  run : Except Fault Checked.TopLevel.Run
  erases : run = Checked.TopLevel.run msg

/-- Trace a prepared transaction message. Legacy calls notify the tracer of the
authorization refund before entering the frame. Preparation faults and refusals
produce no frame events. -/
def runMessage {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (msg : Msg) (runId : String) : m (MessageResult msg) := do
  match hp : Checked.TopLevel.prepare msg with
  | .error fault => pure ⟨.error fault, by rw [Checked.TopLevel.run, hp]; rfl⟩
  | .ok preparation =>
    let reportRefund := if msg.benv.stat.rules.stateGas.isNone && msg.target.isSome
      then authorizationRefund else fun _ => pure ()
    let result ← Checked.Trace.runPrepared sink reportRefund preparation runId
    pure ⟨result.run, by rw [result.erases, Checked.TopLevel.run, hp]; rfl⟩

/-- The tracer's transaction-visible observation agrees with the original
message call, including pre-frame failure. -/
theorem MessageResult.output_eq {msg : Msg} (result : MessageResult msg) :
    (result.run.mapError Fault.toEvmError >>= Checked.TopLevel.Run.output msg) =
      processMessageCall msg := by
  rw [result.erases]
  exact Checked.preparedMessageOutput_square msg

/-- The checked message run makes the same JSON sink calls and reports the
same authorization refund at the same point as the staged transaction tracer. -/
theorem runMessage_json (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (authorizationRefund : Nat → IO Unit) (msg : Msg) (runId : String) :
    (fun _ => ()) <$> runMessage (TraceJson.sink cfg state trace frames) authorizationRefund msg runId =
      (fun _ => ()) <$> Staging.TraceTransaction.runMessage
        (TraceJson.sink cfg state trace frames) authorizationRefund msg runId := by
  let sink := TraceJson.sink cfg state trace frames
  have frameEffects (f : Checked.Frame) :
      (fun _ => ()) <$> Checked.Trace.runFrame sink f runId =
        (fun _ => ()) <$> Trace.runFrame sink (Checked.Trace.frame f) runId := by
    have h := congrArg (Functor.map (fun _ => ())) (runFrame_json cfg state trace frames f runId)
    simpa only [← comp_map, Function.comp_def] using h
  unfold Staging.TraceTransaction.runMessage
  split
  · rename_i fault hp
    have hc : Checked.TopLevel.prepare msg = .error fault := by
      unfold Checked.TopLevel.prepare
      split <;> rename_i h <;> rw [hp] at h <;> cases h
      rfl
    unfold runMessage
    split <;> rename_i h <;> rw [hc] at h <;> cases h
    rfl
  · rename_i reason halted hp
    let refused : Checked.TopLevel.Refusal := match msg.benv.stat.rules.stateGas with
      | none => .collision reason
      | some _ => .stateGas reason msg.stateGasGrant halted.meta.accountReads halted.meta.storageReads
    have hc : Checked.TopLevel.prepare msg = .ok (.refused refused) := by
      unfold Checked.TopLevel.prepare
      split <;> rename_i h <;> rw [hp] at h <;> cases h
      cases hg : msg.benv.stat.rules.stateGas <;> simp only [refused, hg]
    unfold runMessage
    split <;> rename_i h <;> rw [hc] at h <;> cases h
    simp only [Checked.Trace.runPrepared, pure_bind, map_pure]
  · rename_i frame refund hp
    let f := Checked.Frame.ofLegacy frame (Staging.TopLevel.prepare_frame_memory_wf hp)
    have hc : Checked.TopLevel.prepare msg = .ok (.frame f refund) := by
      unfold Checked.TopLevel.prepare
      split <;> rename_i h <;> rw [hp] at h <;> cases h
      rfl
    have hFrame := frameEffects f
    rw [frame_eq, Checked.Frame.toLegacy_ofLegacy] at hFrame
    unfold runMessage
    split <;> rename_i h <;> rw [hc] at h <;> cases h
    simp only [← bind_pure_comp, sink] at hFrame
    by_cases report : (msg.benv.stat.rules.stateGas.isNone && msg.target.isSome) = true
    all_goals
      simp only [report, Bool.false_eq_true, ite_true, ite_false, Checked.Trace.runPrepared,
        ← bind_pure_comp, bind_assoc, pure_bind]
      rw [hFrame]
      unfold Trace.runFrame
      try refine bind_congr fun _ => ?_
      dsimp only
      split <;> rename_i he
      all_goals first
        | solve | simp only [bind_assoc, pure_bind]
        | split <;> rename_i he' <;> rw [he] at he' <;> cases he'
          simp only [bind_assoc, pure_bind]

/-! ### The transaction boundary -/

private theorem processTransaction_prepared (benv : Benv) (bout : BlockOutput)
    (tx : Transaction) (index : Nat) :
    Staging.B2.processTransaction benv bout tx index = (do
      let prepared ← Staging.TraceTransaction.prepareTransaction benv bout tx index
      let ⟨state, output⟩ ← Except.mapError TransitionError.vm (processMessageCall prepared.msg)
      Staging.Transaction.settle prepared tx index state output) := by
  rw [Jaune.Bridge.G2a.processTransaction_eq_staged]
  unfold Staging.processTransaction Staging.TraceTransaction.prepareTransaction
  simp only [bind_assoc, Jaune.Bridge.G2a.processMessageCall_eq]

/-- The Checked transaction trace retains the message needed to interpret its
typed run. The certificate refers to the current staged transaction value. -/
structure TransactionResult (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat)
    extends TraceTransaction.Certified (Staging.B2.processTransaction benv bout tx index) where
  messageRun : Option (Msg × Checked.TopLevel.Run)
  observes : messageRun =
    (Staging.TraceTransaction.prepareTransaction benv bout tx index).toOption.bind fun prepared =>
      (Checked.TopLevel.run prepared.msg).toOption.map fun run => (prepared.msg, run)

/-- Trace one Checked message and settle its result through the transaction's
shared preparation and the checked bridge to staging settlement. -/
def runTransaction {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (benv : Benv) (bout : BlockOutput) (tx : Transaction)
    (index : Nat) (runId : String) : m (TransactionResult benv bout tx index) := do
  match hp : Staging.TraceTransaction.prepareTransaction benv bout tx index with
  | .error error =>
    pure {
      value := .error error
      messageRun := none
      erases := by rw [processTransaction_prepared, hp]; rfl
      observes := by rw [hp]; rfl }
  | .ok prepared =>
    let message ← runMessage sink authorizationRefund prepared.msg runId
    let rendered := message.run.mapError Fault.toEvmError >>= Checked.TopLevel.Run.output prepared.msg
    pure {
      value := do
        let ⟨state, output⟩ ← rendered.mapError TransitionError.vm
        Staging.Transaction.settle prepared tx index state output
      messageRun := message.run.toOption.map fun run => (prepared.msg, run)
      erases := by rw [processTransaction_prepared, hp]; simp only [rendered, message.output_eq]; rfl
      observes := by rw [hp, message.erases]; rfl }

private def messageSummary (rendered : Except EvmError (State × MsgCallOutput)) : Option (Bytes × Bool) :=
  rendered.toOption.map fun (_, output) => (output.returnData, output.error.isNone)

/-- The returned bytes and success flag read by the deferred transaction row. -/
def TransactionResult.summary {benv bout tx index} (result : TransactionResult benv bout tx index) :
    Option (Bytes × Bool) :=
  result.messageRun.bind fun (msg, run) => messageSummary (run.output msg)

private def transactionSummary (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat) :
    Option (Bytes × Bool) :=
  (Staging.TraceTransaction.prepareTransaction benv bout tx index).toOption.bind fun prepared =>
    messageSummary (processMessageCall prepared.msg)

private theorem TransactionResult.summary_eq {benv bout tx index} (result : TransactionResult benv bout tx index) :
    result.summary = transactionSummary benv bout tx index := by
  unfold TransactionResult.summary transactionSummary
  rw [result.observes]
  cases Staging.TraceTransaction.prepareTransaction benv bout tx index with
  | error => rfl
  | ok prepared =>
    have h := congrArg messageSummary (Checked.preparedMessageOutput_square prepared.msg)
    unfold Checked.preparedMessageOutput at h
    cases hr : Checked.TopLevel.run prepared.msg <;>
      simpa only [bind, Except.bind, Except.mapError, messageSummary, Except.toOption,
        Option.bind, Option.map, hr] using h

private theorem stagedSummary_eq {benv bout tx index}
    (result : Staging.TraceTransaction.TransactionResult benv bout tx index) :
    result.messageRun.bind (messageSummary ∘ Staging.MessageRun.output) =
      transactionSummary benv bout tx index := by
  unfold transactionSummary
  rw [result.observes]
  cases Staging.TraceTransaction.prepareTransaction benv bout tx index with
  | error => rfl
  | ok prepared =>
    have h := congrArg messageSummary (Jaune.Bridge.G2a.processMessageCall_eq prepared.msg)
    unfold Staging.processMessageCall at h
    cases hr : Staging.Message.run prepared.msg <;>
      simpa only [bind, Except.bind, Except.mapError, messageSummary, Except.toOption,
        Option.bind, Option.map, Function.comp_def, hr] using h

/-- The Checked transaction makes the same JSON writes and refund calls as
the staged transaction tracer. The transaction value and the message fields
used by the deferred summary also agree. -/
theorem runTransaction_json (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (authorizationRefund : Nat → IO Unit) (benv : Benv)
    (bout : BlockOutput) (tx : Transaction) (index : Nat) (runId : String) :
    (fun result => (result.value, result.summary)) <$> runTransaction (TraceJson.sink cfg state trace frames)
        authorizationRefund benv bout tx index runId =
      (fun result => (result.value, result.messageRun.bind fun run =>
        run.output.toOption.map fun (_, output) => (output.returnData, output.error.isNone))) <$>
        Staging.TraceTransaction.runTransaction (TraceJson.sink cfg state trace frames)
          authorizationRefund benv bout tx index runId := by
  let sink := TraceJson.sink cfg state trace frames
  have effects : (fun _ => ()) <$> runTransaction sink authorizationRefund benv bout tx index runId =
      (fun _ => ()) <$> Staging.TraceTransaction.runTransaction sink
        authorizationRefund benv bout tx index runId := by
    unfold runTransaction Staging.TraceTransaction.runTransaction
    split
    · rename_i error hp
      split <;> rename_i h <;> rw [hp] at h <;> cases h
      simp only [map_pure]
    · rename_i prepared hp
      split <;> rename_i h <;> rw [hp] at h <;> cases h
      simp only [← bind_pure_comp, bind_assoc, pure_bind]
      simpa only [← bind_pure_comp] using
        runMessage_json cfg state trace frames authorizationRefund prepared.msg runId
  let observation := (Staging.B2.processTransaction benv bout tx index, transactionSummary benv bout tx index)
  have checkedObs : (fun result : TransactionResult benv bout tx index => (result.value, result.summary)) =
      (fun _ : Unit => observation) ∘ (fun _ => ()) :=
    funext fun result => congrArg₂ Prod.mk result.erases result.summary_eq
  have stagedObs : (fun result : Staging.TraceTransaction.TransactionResult benv bout tx index =>
      (result.value, result.messageRun.bind (messageSummary ∘ Staging.MessageRun.output))) =
        (fun _ : Unit => observation) ∘ (fun _ => ()) :=
    funext fun result => congrArg₂ Prod.mk result.erases (stagedSummary_eq result)
  change (fun result => (result.value, result.summary)) <$> runTransaction sink
      authorizationRefund benv bout tx index runId =
    (fun result => (result.value, result.messageRun.bind (messageSummary ∘ Staging.MessageRun.output))) <$>
      Staging.TraceTransaction.runTransaction sink authorizationRefund benv bout tx index runId
  rw [checkedObs, stagedObs]
  simpa only [← comp_map] using congrArg (fun action => (fun _ : Unit => observation) <$> action) effects

end Jaune.Bridge.G2b.CheckedTrace
