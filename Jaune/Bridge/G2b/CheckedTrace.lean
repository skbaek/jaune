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

The new tracer emits its own events (`Jaune.MessageCall.CheckedTraceEvent`). `Legacy.event`
projects each onto the old event type, from the checked state; `Legacy.sink` reads an old sink
through it. The projection forgets exactly what no reader of an event reads: a `Devm`'s output
and stored error where a running machine or a continuing step carries them, a halted frame's
output, a fault's (never read) state, and a pending return's two passed-through fields.
`normalize` forgets the same on an old event.

* `execFueled_events`, `exec_events`, `runFrame_events`: from related starts, the new tracer with
  any old sink through `Legacy.sink`, in any lawful monad, is the old tracer with the same sink
  after `normalize`: the same
  sink calls on the same (normalised) events in the same order, the same frame numbering, and the
  same returned value. `runFrame_events` holds for every checked frame against its projection.
* `consume_normalize`, `sink_normalize`: the serialiser reads nothing `normalize` forgets.
* `runFrame_json`: so the two tracers write byte-identical `trace.jsonl` and `frames.jsonl` rows,
  and return the same result, for every checked frame (goal 3.1: the serialised event stream as a
  further observation, proved equal). `Jaune.Bridge.G2b.CheckedTraceJson` carries this to the new
  serialiser.

It is classified `adapter` in `scripts/layering.json`, not `bridge`: a bridge module may not import
an adapter, and both tracers and the serialiser are adapters. It is reached by the default build
through `JauneChecks`, outside the `Jaune` library. Everything here goes with `Devm` after G2b's
tag.
-/

namespace Jaune.Bridge.G2b.CheckedTrace

variable [Checked.LegacyTransaction]

open Jaune

/-! ### The checked tracer's events, projected onto the `Devm` tracer's event vocabulary -/

namespace Legacy

/-- A checked memory as the event's memory. -/
def mem (m : Memory) : Mem := ⟨m.data, m.size⟩

/-- A checked state as the event's lifetime-grouped state. -/
def state (s : Checked.Frame.State) : Frame.State :=
  ⟨⟨s.machine.stack, mem s.machine.memory, s.machine.gasLeft, s.machine.stateGas,
    s.machine.returnData⟩, s.world, s.substate, s.trail⟩

/-- A checked state as a `Devm`, with no output and no stored error. -/
def devm (s : Checked.Frame.State) : Devm := (state s).toDevm

/-- A checked frame as the event's frame. -/
def frame (f : Checked.Frame) : Frame := f.toLegacy

/-- A running frame of the message `msg` as the event's running machine. -/
def evm (msg : Message) (r : Checked.Frame.Running) : Evm := ⟨r.pc, msg.sevm, devm r.state⟩

/-- How a frame stopped, as the event's raw result. -/
def exitRaw : Checked.Frame.Exit → Execution
  | .finished output s => .ok ((devm s).withOutput output)
  | .reverted output s => .error (.revert, (devm s).withOutput output)
  | .halted reason s => .error (.halt reason, devm s)

/-- A fault as the event's raw result. Its state is never read. -/
def faultRaw (fault : Fault) : Execution := .error (fault.toEvmError, default)

/-- A frame's raw result or fault, as the event's raw result. -/
def raw : Except Fault Checked.Frame.Exit → Execution
  | .error fault => faultRaw fault
  | .ok exit => exitRaw exit

/-- A pending return as the event's, with no passed-through output and no stored error. -/
def pending (p : Staging.Pending) : Pending := ⟨p.target, p.newAccountCharged, [], none⟩

/-- One checked step as the event's step. A fault is shown as the raw result it ends the run
with. -/
def step (result : Except Fault Checked.Step) : Step :=
  match result with
  | .error fault => .halt (faultRaw fault)
  | .ok (.exit e) => .halt (exitRaw e)
  | .ok (.next pc s) => .next pc (devm s)
  | .ok (.spawn child p pc) => .spawn (frame child) (pending p) pc

/-- The top-level frame of a message, with the checked memory: `Frame.ofTop`'s, whose checkpoint
memory is empty. -/
def topFrame (msg : Msg) (isCreate : Bool) : Checked.Frame :=
  let top := Frame.ofTop msg isCreate
  let s := top.checkpoint
  ⟨Checked.Message.ofLegacy top.message,
    ⟨⟨s.machine.stack, Memory.empty, s.machine.gasLeft, s.machine.stateGas, s.machine.returnData⟩,
      s.world, s.substate, s.trail⟩⟩

/-- An entry of a frame of the message `msg` as the event's entry. -/
def entry (msg : Message) : Checked.Frame.Entry → Frame.Entry
  | .done result => .done result
  | .run r => .run (evm msg r)

/-- The caller after its child, as the event's raw result. -/
def resumedRaw :
    Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State) → Execution
  | .error fault => faultRaw fault
  | .ok (.error (reason, s)) => .error (.halt reason, devm s)
  | .ok (.ok s) => .ok (devm s)

/-- The run identity as the event's. -/
abbrev context (c : Checked.Trace.Context) : Trace.Context := ⟨c.runId, c.frame, c.depth⟩

/-- A checked tracer event as the `Devm` tracer's: the checked state projected, the frame's
message observed through the transaction template. -/
def event : Checked.Trace.Event → Trace.Event
  | .instruction c msg r result =>
    .instruction (context c) (evm (msg.toLegacy Checked.LegacyTransaction.template) r) (step result)
  | .entered c f e =>
    .entered (context c) (frame f) (entry (f.message.toLegacy Checked.LegacyTransaction.template) e)
  | .exited c outcome => .exited (context c) (outcome.map raw)
  | .settled c f result => .settled (context c) (frame f) result
  | .resumed c child x => .resumed (context c) child (resumedRaw x)

/-- A `Devm` tracer sink as a checked tracer sink, through `event`. -/
abbrev sink {m : Type → Type} (s : Trace.Sink m) : Checked.Trace.Sink m := fun e => s (event e)

/-- The projection of each event, one constructor at a time. -/
theorem event_instruction (c : Checked.Trace.Context) (msg : Checked.Message)
    (r : Checked.Frame.Running) (result : Except Fault Checked.Step) :
    event (.instruction c msg r result) =
      .instruction (context c) (evm (msg.toLegacy Checked.LegacyTransaction.template) r)
        (step result) := rfl
theorem event_entered_done (c : Checked.Trace.Context) (f : Checked.Frame)
    (x : Except Fault Frame.Result) :
    event (.entered c f (.done x)) = .entered (context c) (frame f) (.done x) := rfl
theorem event_entered_run (c : Checked.Trace.Context) (f : Checked.Frame)
    (r : Checked.Frame.Running) :
    event (.entered c f (.run r)) =
      .entered (context c) (frame f)
        (.run (evm (f.message.toLegacy Checked.LegacyTransaction.template) r)) := rfl
theorem event_exited_none (c : Checked.Trace.Context) :
    event (.exited c none) = .exited (context c) none := rfl
theorem event_exited_some (c : Checked.Trace.Context) (o : Except Fault Checked.Frame.Exit) :
    event (.exited c (some o)) = .exited (context c) (some (raw o)) := rfl
theorem event_settled (c : Checked.Trace.Context) (f : Checked.Frame)
    (x : Except Fault Frame.Result) :
    event (.settled c f x) = .settled (context c) (frame f) x := rfl
theorem event_resumed (c : Checked.Trace.Context) (n : Nat)
    (x : Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State)) :
    event (.resumed c n x) = .resumed (context c) n (resumedRaw x) := rfl

end Legacy

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

theorem state_eq (s : Checked.Frame.State) : Legacy.state s = s.toLegacy := rfl

theorem frame_eq (f : Checked.Frame) : Legacy.frame f = f.toLegacy := rfl

/-- What relates a running checked frame of the message `msg` to a running machine: the same
frame, grouped; the message's static record; no output. -/
structure Related (msg : Message) (r : Checked.Frame.Running) (evm : Evm) : Prop where
  running : r.toLegacy = Frame.Running.ofEvm evm
  static : evm.sta = msg.sevm
  output : evm.dyna.output = []

theorem Related.evm_eq {msg : Message} {r : Checked.Frame.Running} {evm : Evm}
    (h : Related msg r evm) : Legacy.evm msg r = normEvm evm := by
  have hpc : r.pc = evm.pc := congrArg Frame.Running.pc h.running
  have hs : Legacy.state r.state = Frame.State.ofDevm evm.dyna :=
    congrArg Frame.Running.state h.running
  simp only [Legacy.evm, normEvm, normDevm, Legacy.devm, hpc, hs, h.static]

theorem normRaw_of_fault {raw : Execution} {fault : Fault}
    (h : Frame.Exit.ofExecution raw = .error fault) : normRaw raw = Legacy.faultRaw fault := by
  simp only [normRaw, h, Legacy.faultRaw]

theorem normRaw_of_exit {raw : Execution} {e : Checked.Frame.Exit}
    (h : Frame.Exit.ofExecution raw = .ok e.toLegacy) : normRaw raw = Legacy.exitRaw e := by
  simp only [normRaw, h]
  cases e <;> rfl

/-- The old raw result's exit, against the new driver's outcome. -/
theorem normRaw_of_square {raw : Execution} {x : Except Fault Checked.Frame.Exit}
    (h : x.map Checked.Frame.Exit.toLegacy = Frame.Exit.ofExecution raw) :
    normRaw raw = Legacy.raw x := by
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
    (h : enterWith f start = .run evm) : evm.sta = f.message.sevm :=
  (Checked.Frame.entry_static_error h).1

/-- The new entry of a spawned child against the old one. -/
theorem enter_rel (child : Checked.Frame) :
    (enter (Legacy.frame child)).observe = (Checked.enter child).toLegacy := by
  rw [Frame.Entry.observe_enter, frame_eq, Checked.enter_toLegacy]

/-- The new entry of a top-level frame against the old one. -/
theorem enterWith_rel (f : Checked.Frame) :
    (enterWith (Legacy.frame f) (Legacy.frame f).checkpoint.toDevm).observe =
      (Checked.enterWith f f.checkpoint).toLegacy := by
  simpa only [frame_eq] using f.enterWith_square

/-- The new settlement against the old one. -/
theorem settle_rel (child : Checked.Frame) {raw : Execution} {x : Except Fault Checked.Frame.Exit}
    (h : x.map Checked.Frame.Exit.toLegacy = Frame.Exit.ofExecution raw) :
    settle (Legacy.frame child) raw = x >>= Checked.settle child := by
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
    (result : Frame.Result) (hflag : (Legacy.state saved).trail.touchedRIPEMD160 = false) :
    (resume rules p (Legacy.state saved) result).map (Except.mapResultState Frame.State.ofDevm) =
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
inductive ResumedRel (msg : Message) (pc : Nat) (sta : Sevm) (context : Checked.CallContext) :
    Execution → Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State) →
    Prop
  /-- Both go on, from related states. -/
  | resumed {d : Devm} {s : Checked.Frame.State} :
      Related msg ⟨pc, context, s⟩ ⟨pc, sta, d⟩ →
      Legacy.resumedRaw (.ok (.ok s)) = normRaw (.ok d) →
      ResumedRel msg pc sta context (.ok d) (.ok (.ok s))
  /-- Both stop, with the same normalised raw result. -/
  | stopped {e : EvmError × Devm} {x} :
      (∀ s, x ≠ .ok (.ok s)) → normRaw (.error e) = Legacy.resumedRaw x →
      ResumedRel msg pc sta context (.error e) x

theorem resumedRel {msg : Message} {r : Checked.Frame.Running} {evm : Evm} (h : Related msg r evm)
    {child : Checked.Frame} {p : Pending} {pc : Nat}
    (hflag : (Legacy.frame child).checkpoint.trail.touchedRIPEMD160 = false)
    (hpo : p.legacyOutput = []) (settled : Except Fault Frame.Result) :
    ResumedRel msg pc evm.sta r.context
      (Trace.resumedRaw evm.sta.benvStat.rules (Legacy.frame child) p settled)
      (Checked.Trace.resumed r.context.block.rules child (Staging.Pending.ofLegacy p) settled) := by
  have hctx : r.context.inLegacy = CallContext.ofSevm evm.sta := congrArg Frame.Running.context h.running
  have hrules : r.context.block.rules = evm.sta.benvStat.rules :=
      congrArg (fun ctx : CallContext => ctx.block.rules) hctx
  rcases settled with fault | result
  · apply ResumedRel.stopped
    · intro s hs; cases hs
    · simp only [Legacy.resumedRaw]
      exact normRaw_of_fault (ofExecution_fault fault _)
  · have hr : (resume evm.sta.benvStat.rules p (Legacy.frame child).checkpoint result).map
        (Except.mapResultState Frame.State.ofDevm) =
        (Checked.resume evm.sta.benvStat.rules (Staging.Pending.ofLegacy p) child.checkpoint
          result).map Checked.ResumeResult.toLegacy :=
      resume_rel evm.sta.benvStat.rules p child.checkpoint result hflag
    have ho := fun d (hd : resume evm.sta.benvStat.rules p (Legacy.frame child).checkpoint
        result = .ok (.ok d)) => resume_output hd
    simp only [Trace.resumedRaw, Checked.Trace.resumed, hrules]
    revert hr ho
    rcases resume evm.sta.benvStat.rules p (Legacy.frame child).checkpoint result with
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
      simp only [normRaw, Frame.Exit.ofExecution, Frame.Exit.toExecution, Legacy.resumedRaw,
        Legacy.devm, hs, state_eq]
    · have hdo : d.output = [] := (ho d rfl).trans hpo
      refine .resumed ⟨?_, h.static, hdo⟩ ?_
      · show (⟨pc, r.context.inLegacy, s.toLegacy⟩ : Frame.Running) = ⟨pc, CallContext.ofSevm evm.sta, _⟩
        rw [hctx, ← hr]
      · simp only [normRaw, Frame.Exit.ofExecution, Frame.Exit.toExecution, Legacy.resumedRaw,
        Legacy.devm, hr, hdo, state_eq]
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

/-! #### The new tracer, one outcome at a time, for any sink of its own events -/

variable (nsink : Checked.Trace.Sink m)

theorem checked_zero (msg : Checked.Message) (r : Checked.Frame.Running)
    (context : Checked.Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$> Checked.Trace.execFueled nsink msg r 0 context nextFrame =
      (do nsink (.exited context none); pure nextFrame) := by
  rw [Checked.Trace.execFueled]
  simp only [map_bind, map_pure]

theorem checked_fault {msg : Checked.Message} {r : Checked.Frame.Running} {fuel : Nat} {fault : Fault}
    (hstep : Checked.step r = .error fault) (context : Checked.Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled nsink msg r (fuel + 1) context nextFrame =
      (do
        nsink (.instruction context msg r (.error fault))
        nsink (.exited context (some (.error fault)))
        pure nextFrame) := by
  rw [Checked.Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind, map_pure]

theorem checked_exit {msg : Checked.Message} {r : Checked.Frame.Running} {fuel : Nat}
    {e : Checked.Frame.Exit} (hstep : Checked.step r = .ok (.exit e))
    (context : Checked.Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled nsink msg r (fuel + 1) context nextFrame =
      (do
        nsink (.instruction context msg r (.ok (.exit e)))
        nsink (.exited context (some (.ok e)))
        pure nextFrame) := by
  rw [Checked.Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind, map_pure]

theorem checked_next {msg : Checked.Message} {r : Checked.Frame.Running} {fuel : Nat} {pc : Nat}
    {s : Checked.Frame.State} (hstep : Checked.step r = .ok (.next pc s))
    (context : Checked.Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled nsink msg r (fuel + 1) context nextFrame =
      (do
        nsink (.instruction context msg r (.ok (.next pc s)))
        Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled nsink msg ⟨pc, r.context, s⟩ fuel context nextFrame) := by
  rw [Checked.Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  rw [checked_cast' _ (by simp only [Checked.execFueled, hstep])]

/-- How a caller stopped after its child: a fault or an exceptional halt. The resumed case is
never shown. -/
def stopOutcome :
    Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State) →
      Except Fault Checked.Frame.Exit
  | .error fault => .error fault
  | .ok (.error (reason, s)) => .ok (.halted reason s)
  | .ok (.ok s) => .ok (.finished [] s)

/-- A stopped caller's outcome, projected, is its resumption's raw result. -/
theorem raw_stopOutcome
    (x : Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State)) :
    Legacy.raw (stopOutcome x) = Legacy.resumedRaw x := by
  rcases x with fault | ⟨reason, s⟩ | s <;> rfl

/-- The rows a stopped caller emits after its child. -/
abbrev stopRows (context : Checked.Trace.Context) (nextFrame : Nat)
    (x : Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State))
    (n : Nat) : m Nat := do
  nsink (.resumed context nextFrame x)
  nsink (.exited context (some (stopOutcome x)))
  pure n

theorem checked_done_ok {msg : Checked.Message} {r : Checked.Frame.Running} {fuel : Nat}
    {child : Checked.Frame} {p : Staging.Pending} {pc : Nat} {settled : Except Fault Frame.Result}
    {s : Checked.Frame.State} (hstep : Checked.step r = .ok (.spawn child p pc))
    (hentry : Checked.enter child = .done settled)
    (hresume : Checked.Trace.resumed r.context.block.rules child p settled = .ok (.ok s))
    (context : Checked.Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled nsink msg r (fuel + 1) context nextFrame =
      (do
        nsink (.instruction context msg r (.ok (.spawn child p pc)))
        nsink (.entered { context with frame := nextFrame, depth := context.depth + 1 }
          child (.done settled))
        nsink (.settled { context with frame := nextFrame, depth := context.depth + 1 }
          child settled)
        nsink (.resumed context nextFrame (.ok (.ok s)))
        Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled nsink msg ⟨pc, r.context, s⟩ fuel context (nextFrame + 1)) := by
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

theorem checked_done_stop {msg : Checked.Message} {r : Checked.Frame.Running} {fuel : Nat}
    {child : Checked.Frame} {p : Staging.Pending} {pc : Nat} {settled : Except Fault Frame.Result}
    {x : Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State)}
    (hstep : Checked.step r = .ok (.spawn child p pc))
    (hentry : Checked.enter child = .done settled)
    (hresume : Checked.Trace.resumed r.context.block.rules child p settled = x)
    (hx : ∀ s, x ≠ .ok (.ok s)) (context : Checked.Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled nsink msg r (fuel + 1) context nextFrame =
      (do
        nsink (.instruction context msg r (.ok (.spawn child p pc)))
        nsink (.entered { context with frame := nextFrame, depth := context.depth + 1 }
          child (.done settled))
        nsink (.settled { context with frame := nextFrame, depth := context.depth + 1 }
          child settled)
        stopRows nsink context nextFrame x (nextFrame + 1)) := by
  rw [Checked.Trace.execFueled]
  split <;> rename_i h <;> rw [hstep] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hentry] at h <;> cases h
  simp only [map_bind]
  split <;> rename_i h <;> rw [hresume] at h <;> subst h
  · exact absurd rfl (hx _)
  all_goals simp only [map_bind, map_pure, stopRows, stopOutcome]

theorem checked_run_none {msg : Checked.Message} {r : Checked.Frame.Running} {fuel : Nat}
    {child : Checked.Frame} {p : Staging.Pending} {pc : Nat} {cr : Checked.Frame.Running}
    (hstep : Checked.step r = .ok (.spawn child p pc)) (hentry : Checked.enter child = .run cr)
    (hrun : (Checked.execFueled cr fuel).run = none) (context : Checked.Trace.Context)
    (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled nsink msg r (fuel + 1) context nextFrame =
      (do
        nsink (.instruction context msg r (.ok (.spawn child p pc)))
        nsink (.entered { context with frame := nextFrame, depth := context.depth + 1 }
          child (.run cr))
        let n ← Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled nsink child.message cr fuel
            { context with frame := nextFrame, depth := context.depth + 1 } (nextFrame + 1)
        nsink (.exited context none)
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

theorem checked_run_ok {msg : Checked.Message} {r : Checked.Frame.Running} {fuel : Nat}
    {child : Checked.Frame} {p : Staging.Pending} {pc : Nat} {cr : Checked.Frame.Running}
    {x : Except Fault Checked.Frame.Exit} {s : Checked.Frame.State}
    (hstep : Checked.step r = .ok (.spawn child p pc)) (hentry : Checked.enter child = .run cr)
    (hrun : (Checked.execFueled cr fuel).run = some x)
    (hresume : Checked.Trace.resumed r.context.block.rules child p (x >>= Checked.settle child) =
      .ok (.ok s))
    (context : Checked.Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled nsink msg r (fuel + 1) context nextFrame =
      (do
        nsink (.instruction context msg r (.ok (.spawn child p pc)))
        nsink (.entered { context with frame := nextFrame, depth := context.depth + 1 }
          child (.run cr))
        let n ← Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled nsink child.message cr fuel
            { context with frame := nextFrame, depth := context.depth + 1 } (nextFrame + 1)
        nsink (.settled { context with frame := nextFrame, depth := context.depth + 1 }
          child (x >>= Checked.settle child))
        nsink (.resumed context nextFrame (.ok (.ok s)))
        Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled nsink msg ⟨pc, r.context, s⟩ fuel context n) := by
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

theorem checked_run_stop {msg : Checked.Message} {r : Checked.Frame.Running} {fuel : Nat}
    {child : Checked.Frame} {p : Staging.Pending} {pc : Nat} {cr : Checked.Frame.Running}
    {x : Except Fault Checked.Frame.Exit}
    {y : Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State)}
    (hstep : Checked.step r = .ok (.spawn child p pc)) (hentry : Checked.enter child = .run cr)
    (hrun : (Checked.execFueled cr fuel).run = some x)
    (hresume : Checked.Trace.resumed r.context.block.rules child p (x >>= Checked.settle child) = y)
    (hy : ∀ s, y ≠ .ok (.ok s)) (context : Checked.Trace.Context) (nextFrame : Nat) :
    Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled nsink msg r (fuel + 1) context nextFrame =
      (do
        nsink (.instruction context msg r (.ok (.spawn child p pc)))
        nsink (.entered { context with frame := nextFrame, depth := context.depth + 1 }
          child (.run cr))
        let n ← Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled nsink child.message cr fuel
            { context with frame := nextFrame, depth := context.depth + 1 } (nextFrame + 1)
        nsink (.settled { context with frame := nextFrame, depth := context.depth + 1 }
          child (x >>= Checked.settle child))
        stopRows nsink context nextFrame y n) := by
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
  all_goals simp only [map_bind, map_pure, stopRows, stopOutcome]

end Unfold

/-! ### The event streams -/

section Events

variable {m : Type → Type} [Monad m] [LawfulMonad m] (sink : Trace.Sink m)

/-- **The driver.** From related starts, the checked tracer with `sink` makes the same sink calls,
in the same order, as the `Devm` tracer with `sink` after `normalize`, and numbers the frames the
same way. -/
theorem execFueled_events (fuel : Nat) :
    ∀ (msg : Checked.Message) (r : Checked.Frame.Running) (evm : Evm)
      (context : Checked.Trace.Context) (nextFrame : Nat),
      Related (msg.toLegacy Checked.LegacyTransaction.template) r evm →
      Checked.Trace.CertifiedResult.nextFrame <$>
          Checked.Trace.execFueled (Legacy.sink sink) msg r fuel context nextFrame =
        Trace.CertifiedResult.nextFrame <$>
          Trace.execFueled (fun e => sink (normalize e)) evm fuel (Legacy.context context)
            nextFrame := by
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
    have hctx : r.context.inLegacy = CallContext.ofSevm evm.sta := congrArg Frame.Running.context h.running
    cases hc : Checked.step r with
    | error fault =>
      rw [hc] at hrel
      cases hw : Evm.step evm with
      | halt raw =>
        rw [hw] at hrel
        have hraw : normRaw raw = Legacy.faultRaw fault :=
          normRaw_of_square (x := .error fault) (by
            simp only [Jaune.Step.observe, Except.map] at hrel ⊢
            revert hrel; cases Frame.Exit.ofExecution raw <;> simp)
        rw [checked_fault (Legacy.sink sink) hc, trace_halt _ hw]
        simp only [Legacy.sink, Legacy.event_instruction, Legacy.event_exited_some, Legacy.raw,
          normalize_instruction, normalize_exited_some, normStep, hevm, hraw, Legacy.step]
      | next pc d => rw [hw] at hrel; simp [Jaune.Step.observe, Except.map] at hrel
      | spawn child p pc => rw [hw] at hrel; simp [Jaune.Step.observe, Except.map] at hrel
    | ok step =>
      rw [hc] at hrel
      cases step with
      | exit e =>
        cases hw : Evm.step evm with
        | halt raw =>
          rw [hw] at hrel
          have hraw : normRaw raw = Legacy.exitRaw e :=
            normRaw_of_square (x := .ok e) (by
              simp only [Jaune.Step.observe, Except.map, Checked.Step.toLegacy] at hrel ⊢
              revert hrel; cases Frame.Exit.ofExecution raw <;> simp)
          rw [checked_exit (Legacy.sink sink) hc, trace_halt _ hw]
          simp only [Legacy.sink, Legacy.event_instruction, Legacy.event_exited_some, Legacy.raw,
            normalize_instruction, normalize_exited_some, normStep, hevm, hraw, Legacy.step]
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
          rw [checked_next (Legacy.sink sink) hc, trace_next _ hw]
          simp only [Legacy.sink, Legacy.event_instruction, normalize_instruction, normStep, hevm,
            Legacy.step]
          have hdevm : Legacy.devm s = normDevm d := by
            simp only [Legacy.devm, normDevm, state_eq, hs]
          rw [hdevm]
          refine bind_congr fun _ => ?_
          refine ih msg _ _ context nextFrame ⟨?_, h.static, hd⟩
          show (⟨pc, r.context.inLegacy, s.toLegacy⟩ : Frame.Running) = ⟨pc, CallContext.ofSevm evm.sta, _⟩
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
          have hchild' : child' = Legacy.frame child := hchild.symm
          subst hchild' hp
          have hpost' := hpost
          rw [hw] at hpost'
          obtain ⟨hpo, hflag⟩ := hpost'
          have hinstr : normalize (.instruction (Legacy.context context) evm
                (.spawn (Legacy.frame child) p' pc)) =
              .instruction (Legacy.context context)
                (Legacy.evm (msg.toLegacy Checked.LegacyTransaction.template) r)
                (Legacy.step (.ok (.spawn child (Staging.Pending.ofLegacy p') pc))) := by
            simp only [normalize, normStep, hevm, Legacy.step, normPending, Legacy.pending]
            rfl
          have hrules : r.context.block.rules = evm.sta.benvStat.rules :=
            congrArg (fun ctx : CallContext => ctx.block.rules) hctx
          have hentry := enter_rel child
          cases hce : Checked.enter child with
          | done settled =>
            rw [hce] at hentry
            have hwe : enter (Legacy.frame child) = .done settled := by
              revert hentry
              cases enter (Legacy.frame child) <;>
                simp [Frame.Entry.observe, Checked.Frame.Entry.toLegacy]
            have hres := resumedRel h (pc := pc) hflag hpo settled
            revert hres
            generalize hx : Checked.Trace.resumed r.context.block.rules child
              (Staging.Pending.ofLegacy p') settled = x
            generalize hy : Trace.resumedRaw evm.sta.benvStat.rules (Legacy.frame child) p'
              settled = y
            intro hres
            cases hres with
            | resumed hR hraw =>
              rw [checked_done_ok (Legacy.sink sink) hc hce hx, trace_done_ok _ hw hwe hy]
              simp only [Legacy.sink, Legacy.event_instruction, Legacy.event_entered_done,
                Legacy.event_settled, Legacy.event_resumed, hinstr]
              refine bind_congr fun _ => bind_congr fun _ => bind_congr fun _ => ?_
              rw [hraw]
              refine bind_congr fun _ => ?_
              exact ih msg _ _ context (nextFrame + 1) hR
            | stopped hne hraw =>
              rw [checked_done_stop (Legacy.sink sink) hc hce hx hne, trace_done_error _ hw hwe hy]
              simp only [stopRows, Legacy.sink, Legacy.event_instruction, Legacy.event_entered_done,
                Legacy.event_exited_some, Legacy.event_settled, Legacy.event_resumed,
                raw_stopOutcome, hinstr]
              simp only [normalize_entered_done, normalize_exited_some, normalize_settled,
                normalize_resumed, hraw]
          | run cr =>
            rw [hce] at hentry
            obtain ⟨cevm, hwe, hcr⟩ : ∃ cevm, enter (Legacy.frame child) = .run cevm ∧
                cr.toLegacy = Frame.Running.ofEvm cevm := by
              revert hentry
              cases enter (Legacy.frame child) with
              | done _ => simp [Frame.Entry.observe, Checked.Frame.Entry.toLegacy]
              | run cevm =>
                intro hentry
                simp only [Frame.Entry.observe, Checked.Frame.Entry.toLegacy,
                  Staging.Frame.Entry.run.injEq] at hentry
                exact ⟨cevm, rfl, hentry.symm⟩
            have hR : Related child.toLegacy.message cr cevm :=
              ⟨hcr, enterWith_run_sta hwe, enter_run_output hwe⟩
            have hcevm : Legacy.evm (child.message.toLegacy Checked.LegacyTransaction.template) cr =
                normEvm cevm := hR.evm_eq
            have hrun := execFueled_rel fuel hR
            cases hcx : (Checked.execFueled cr fuel).run with
            | none =>
              rw [hcx] at hrun
              have hwx : (Jaune.execFueled cevm fuel).run = none := by
                revert hrun; cases (Jaune.execFueled cevm fuel).run <;> simp
              rw [checked_run_none (Legacy.sink sink) hc hce hcx, trace_run_none _ hw hwe hwx]
              simp only [Legacy.sink, Legacy.event_instruction, Legacy.event_entered_run,
                Legacy.event_exited_none,
                hinstr]; simp only [normalize_entered_run, normalize_exited_none, hcevm]
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
              have hres := resumedRel h (pc := pc) hflag hpo (settle (Legacy.frame child) raw)
              rw [hsettle] at hres
              revert hres
              generalize hxr : Checked.Trace.resumed r.context.block.rules child
                (Staging.Pending.ofLegacy p') (x >>= Checked.settle child) = xr
              generalize hy : Trace.resumedRaw evm.sta.benvStat.rules (Legacy.frame child) p'
                (x >>= Checked.settle child) = y
              intro hres
              have hy' : Trace.resumedRaw evm.sta.benvStat.rules (Legacy.frame child) p'
                  (settle (Legacy.frame child) raw) = y := by rw [hsettle]; exact hy
              cases hres with
              | resumed hR' hraw' =>
                rw [checked_run_ok (Legacy.sink sink) hc hce hcx hxr, trace_run_ok _ hw hwe hwx hy']
                simp only [Legacy.sink, Legacy.event_instruction, Legacy.event_entered_run,
                  Legacy.event_settled, Legacy.event_resumed, hinstr]
                simp only [normalize_entered_run, normalize_settled, normalize_resumed, hcevm,
                  hsettle, hraw']
                refine bind_congr fun _ => bind_congr fun _ => ?_
                rw [ih child.message cr cevm _ (nextFrame + 1) hR]
                refine bind_congr fun n => bind_congr fun _ => bind_congr fun _ => ?_
                exact ih msg _ _ context n hR'
              | stopped hne hraw' =>
                rw [checked_run_stop (Legacy.sink sink) hc hce hcx hxr hne, trace_run_error _ hw hwe hwx hy']
                simp only [stopRows, Legacy.sink, Legacy.event_instruction,
                  Legacy.event_entered_run, Legacy.event_exited_some, Legacy.event_settled,
                  Legacy.event_resumed, raw_stopOutcome, hinstr]
                simp only [normalize_entered_run, normalize_exited_some, normalize_settled,
                  normalize_resumed, hcevm, hsettle, hraw']
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

theorem checked_exec (nsink : Checked.Trace.Sink m) (msg : Checked.Message)
    (r : Checked.Frame.Running) (context : Checked.Trace.Context) (nextFrame : Nat) :
    Checked.Trace.ExecutionResult.nextFrame <$> Checked.Trace.exec nsink msg r context nextFrame =
      Checked.Trace.CertifiedResult.nextFrame <$>
        Checked.Trace.execFueled nsink msg r (sufficientFuel r.state.machine.gasMeasure) context
          nextFrame := by
  unfold Checked.Trace.exec
  rw [map_bind, checked_bind]
  refine (bind_congr fun n => ?_).trans (bind_pure _)
  dsimp only
  split <;> simp only [map_pure]

/-- **The total driver.** -/
theorem exec_events {msg : Checked.Message} {r : Checked.Frame.Running} {evm : Evm}
    (h : Related (msg.toLegacy Checked.LegacyTransaction.template) r evm)
    (context : Checked.Trace.Context) (nextFrame : Nat) :
    Checked.Trace.ExecutionResult.nextFrame <$>
        Checked.Trace.exec (Legacy.sink sink) msg r context nextFrame =
      Trace.ExecutionResult.nextFrame <$>
        Trace.exec (fun e => sink (normalize e)) evm (Legacy.context context) nextFrame := by
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
    Checked.Trace.FrameResult.nextFrame <$> Checked.Trace.runFrame (Legacy.sink sink) f runId =
      Trace.FrameResult.nextFrame <$>
        Trace.runFrame (fun e => sink (normalize e)) (Legacy.frame f) runId := by
  have hentry := enterWith_rel f
  unfold Checked.Trace.runFrame Trace.runFrame
  dsimp only
  split
  next settled hce =>
    rw [hce] at hentry
    have hwe : enterWith (Legacy.frame f) (Legacy.frame f).checkpoint.toDevm =
        .done settled := by
      revert hentry
      cases enterWith (Legacy.frame f) (Legacy.frame f).checkpoint.toDevm <;>
        simp [Frame.Entry.observe, Checked.Frame.Entry.toLegacy]
    split <;> rename_i h <;> rw [hwe] at h <;> cases h
    simp only [map_bind, map_pure, Legacy.sink, Legacy.event_entered_done, Legacy.event_settled,
      normalize_entered_done, normalize_settled]
  next r hce =>
    rw [hce] at hentry
    obtain ⟨evm, hwe, hr⟩ : ∃ evm, enterWith (Legacy.frame f)
        (Legacy.frame f).checkpoint.toDevm = .run evm ∧
        r.toLegacy = Frame.Running.ofEvm evm := by
      revert hentry
      cases enterWith (Legacy.frame f) (Legacy.frame f).checkpoint.toDevm with
      | done _ => simp [Frame.Entry.observe, Checked.Frame.Entry.toLegacy]
      | run evm =>
        intro hentry
        simp only [Frame.Entry.observe, Checked.Frame.Entry.toLegacy,
          Staging.Frame.Entry.run.injEq] at hentry
        exact ⟨evm, rfl, hentry.symm⟩
    have hR : Related (f.message.toLegacy Checked.LegacyTransaction.template) r evm :=
      ⟨hr, enterWith_run_sta hwe, enterWith_run_output rfl hwe⟩
    have hsettle : settle (Legacy.frame f) (Jaune.exec evm) = Checked.exec r >>= Checked.settle f := by
      apply settle_rel
      rw [← Checked.exec_toLegacy, hr]
      exact exec_square evm hR.output
    split <;> rename_i h <;> rw [hwe] at h <;> cases h
    simp only [map_bind, map_pure, Legacy.sink, Legacy.event_entered_run, Legacy.event_settled,
      normalize_entered_run, normalize_settled, hR.evm_eq]
    refine bind_congr fun _ => ?_
    rw [checked_execution_bind, trace_execution_bind, exec_events sink hR]
    refine bind_congr fun n => ?_
    simp only [hsettle]

/-- **The top-level frame.** The same, with the returned value: the settled result, which is
`Checked.Frame.runTop f` on both sides. -/
theorem runFrame_events (f : Checked.Frame) (runId : String) :
    (fun x => (x.value, x.nextFrame)) <$> Checked.Trace.runFrame (Legacy.sink sink) f runId =
      (fun x => (x.value, x.nextFrame)) <$>
        Trace.runFrame (fun e => sink (normalize e)) (Legacy.frame f) runId := by
  have hl : (fun x : Checked.Trace.FrameResult f => (x.value, x.nextFrame)) =
      (fun n => (Checked.Frame.runTop f, n)) ∘ Checked.Trace.FrameResult.nextFrame := by
    funext x; rw [← x.erases]; rfl
  have hr : (fun x : Trace.FrameResult (Legacy.frame f) => (x.value, x.nextFrame)) =
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

section Template

omit [Checked.LegacyTransaction]

variable (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State) (trace frames : IO.FS.Handle)
  (left right : Checked.LegacyTransaction)

local notation "jsonSink" => TraceJson.sink cfg state trace frames

/-- The JSON sink reads nothing of the transaction template an event is projected through. -/
private theorem event_template (e : Checked.Trace.Event) :
    jsonSink (@Legacy.event left e) = jsonSink (@Legacy.event right e) := by
  cases e with
  | instruction context msg r step =>
    cases step with
    | error => rfl
    | ok step => cases step <;> rfl
  | entered => rfl
  | exited => rfl
  | settled context f result =>
    cases result with
    | error => rfl
    | ok result => cases result <;> rfl
  | resumed => rfl

/-- So the JSON sink through either template is the same checked tracer sink. -/
private theorem sink_template :
    @Legacy.sink left IO jsonSink = @Legacy.sink right IO jsonSink :=
  funext (event_template cfg state trace frames left right)

/-- Changing projection-only transaction metadata preserves the entire traced frame action. -/
theorem runFrame_json_template (f : Checked.Frame) (runId : String) :
    Checked.Trace.runFrame (@Legacy.sink left IO jsonSink) f runId =
      Checked.Trace.runFrame (@Legacy.sink right IO jsonSink) f runId := by
  rw [sink_template cfg state trace frames left right]

/-- Authorization reporting and frame tracing do not depend on the transaction template. -/
private theorem runPrepared_json_template (reportRefund : Nat → IO Unit)
    (prepared : Checked.TopLevel.Preparation) (runId : String) :
    Checked.Trace.runPrepared (@Legacy.sink left IO jsonSink) reportRefund prepared runId =
      Checked.Trace.runPrepared (@Legacy.sink right IO jsonSink) reportRefund prepared runId := by
  rw [sink_template cfg state trace frames left right]

end Template

/-- **Byte-identical serialisation.** For every checked frame, the checked tracer through the
JSON sink makes the same row writes as the `Devm` tracer through it on the frame's projection,
and returns the same result. -/
theorem runFrame_json (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (f : Checked.Frame) (runId : String) :
    (fun x => (x.value, x.nextFrame)) <$>
        Checked.Trace.runFrame (Legacy.sink (TraceJson.sink cfg state trace frames)) f runId =
      (fun x => (x.value, x.nextFrame)) <$>
        Trace.runFrame (TraceJson.sink cfg state trace frames) (Legacy.frame f) runId := by
  rw [runFrame_events]
  congr 2
  funext e
  exact sink_normalize cfg state trace frames e

/-- The checked top-level frame of a message projects onto the `Devm` one. -/
theorem frame_topFrame (msg : Msg) (isCreate : Bool) :
    letI : Checked.LegacyTransaction := ⟨msg.tenv.stat⟩
    Legacy.frame (Legacy.topFrame msg isCreate) = Frame.ofTop msg isCreate := rfl

/-- **The message runner's call.** `TraceMain` traces a message as
`Trace.runFrame sink (Frame.ofTop msg isCreate) runId`; the checked tracer on
`Legacy.topFrame msg isCreate` writes the same rows and returns the same result. -/
theorem runFrame_json_top (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (msg : Msg) (isCreate : Bool) (runId : String) :
    letI : Checked.LegacyTransaction := ⟨msg.tenv.stat⟩
    (fun x => (x.value, x.nextFrame)) <$>
        Checked.Trace.runFrame (Legacy.sink (TraceJson.sink cfg state trace frames))
          (Legacy.topFrame msg isCreate) runId =
      (fun x => (x.value, x.nextFrame)) <$>
        Trace.runFrame (TraceJson.sink cfg state trace frames) (Frame.ofTop msg isCreate) runId := by
  letI : Checked.LegacyTransaction := ⟨msg.tenv.stat⟩
  change (fun x => (x.value, x.nextFrame)) <$> Checked.Trace.runFrame _ _ _ = _
  rw [runFrame_json, frame_topFrame]

omit [Checked.LegacyTransaction] in
private theorem directFrame_eq (msg : Msg) :
    Legacy.topFrame msg msg.target.isNone =
      ⟨(Checked.TopLevel.Input.ofLegacy msg).message, (Checked.TopLevel.Input.ofLegacy msg).checkpoint⟩ := by
  rw [Checked.TopLevel.Input.ofLegacy_checkpoint]
  rfl

omit [Checked.LegacyTransaction] in
/-- Tracing the directly initialized Checked frame has the old message scope's JSON effects
and settled result. The message scope enters the frame without transaction preparation. -/
theorem runDirectFrame_json (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (template : Checked.LegacyTransaction) (msg : Msg) (runId : String) :
    let input := Checked.TopLevel.Input.ofLegacy msg
    (fun x => (x.value, x.nextFrame)) <$> Checked.Trace.runFrame
        (@Legacy.sink template IO (TraceJson.sink cfg state trace frames))
        ⟨input.message, input.checkpoint⟩ runId =
      (fun x => (x.value, x.nextFrame)) <$> Trace.runFrame
        (TraceJson.sink cfg state trace frames) (Frame.ofTop msg msg.target.isNone) runId := by
  dsimp only
  rw [← directFrame_eq msg, runFrame_json_template cfg state trace frames template ⟨msg.tenv.stat⟩]
  exact runFrame_json_top cfg state trace frames msg msg.target.isNone runId

/-- The Checked result and the observation consumed by the current transaction settlement. -/
structure MessageResult (msg : Msg) extends TraceTransaction.Certified (TopLevel.run msg) where
  run : Except Fault Checked.TopLevel.Run
  run_erases : run = Checked.TopLevel.run msg
  refund_erases : (run >>= Checked.TopLevel.Run.refundCounter) = (value >>= TopLevelRun.refundCounter)

/-- Prepare once, then trace the Checked frame. The ordinary call's authorization
refund is reported before entry. Preparation faults and refusals emit no frame events. -/
def runMessage {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (msg : Msg) (runId : String) : m (MessageResult msg) := do
  match hp : TopLevel.prepare msg with
  | .error fault =>
    pure {
      value := .error fault
      run := .error fault
      erases := by rw [TopLevel.run, hp]; rfl
      run_erases := by
        unfold Checked.TopLevel.run Checked.TopLevel.prepare
        split <;> rename_i h <;> rw [hp] at h <;> cases h
        rfl
      refund_erases := rfl }
  | .ok prepared =>
    let template : Checked.LegacyTransaction := ⟨match prepared with
      | .frame waiting _ => waiting.message.context.tx
      | .refused .. => msg.tenv.stat⟩
    let reportRefund := if msg.benv.stat.rules.stateGas.isNone && msg.target.isSome
      then authorizationRefund else fun _ => pure ()
    let result ← Checked.Trace.runPrepared (@Legacy.sink template m sink) reportRefund
      (Checked.TopLevel.ofPreparation msg prepared hp) runId
    pure {
      value := result.run.map (Checked.TopLevel.observe msg prepared)
      run := result.run
      erases := by
        rw [result.erases]
        exact Checked.TopLevel.run_observe msg prepared hp
      run_erases := by
        rw [result.erases]
        unfold Checked.TopLevel.run Checked.TopLevel.prepare
        split <;> rename_i h <;> rw [hp] at h <;> cases h
        rfl
      refund_erases := by
        rw [result.erases]
        cases hr : (Checked.TopLevel.ofPreparation msg prepared hp).run with
        | error => rfl
        | ok checked => exact Checked.TopLevel.refundCounter_observe hp hr }

/-- The Checked message run makes the same JSON sink and refund calls in the same order. -/
theorem runMessage_json (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (authorizationRefund : Nat → IO Unit) (msg : Msg) (runId : String) :
    (fun _ => ()) <$> runMessage (TraceJson.sink cfg state trace frames) authorizationRefund msg runId =
      (fun _ => ()) <$> TraceTransaction.runMessage
        (TraceJson.sink cfg state trace frames) authorizationRefund msg runId := by
  let sink := TraceJson.sink cfg state trace frames
  have frameEffects [Checked.LegacyTransaction] (f : Checked.Frame) :
      (fun _ => ()) <$> Checked.Trace.runFrame (Legacy.sink sink) f runId =
        (fun _ => ()) <$> Trace.runFrame sink (Legacy.frame f) runId := by
    have h := congrArg (Functor.map (fun _ => ())) (runFrame_json cfg state trace frames f runId)
    simpa only [← comp_map, Function.comp_def] using h
  unfold TraceTransaction.runMessage
  split
  · rename_i fault hp
    unfold runMessage
    split <;> rename_i h <;> rw [hp] at h <;> cases h
    rfl
  · rename_i reason halted hp
    unfold runMessage
    split <;> rename_i h <;> rw [hp] at h <;> cases h
    simp only [Checked.TopLevel.ofPreparation, Checked.Trace.runPrepared, pure_bind, map_pure]
  · rename_i frame refund hp
    letI : Checked.LegacyTransaction := ⟨frame.message.context.tx⟩
    let f := Checked.Frame.ofLegacy frame (Staging.TopLevel.prepare_frame_memory_wf hp)
    have hFrame := frameEffects f
    have projection : f.toLegacy = frame := Checked.Frame.toLegacy_ofLegacy _ _
    rw [frame_eq, projection] at hFrame
    unfold runMessage
    split <;> rename_i h <;> rw [hp] at h <;> cases h
    simp only [← bind_pure_comp, sink] at hFrame
    by_cases report : (msg.benv.stat.rules.stateGas.isNone && msg.target.isSome) = true
    all_goals
      simp only [report, Bool.false_eq_true, ite_true, ite_false, Checked.TopLevel.ofPreparation,
        Checked.Trace.runPrepared, ← bind_pure_comp, bind_assoc, pure_bind]
      rw [hFrame]
      unfold Trace.runFrame
      try refine bind_congr fun _ => ?_
      dsimp only
      split <;> rename_i he
      all_goals first
        | solve | simp only [bind_assoc, pure_bind]
        | split <;> rename_i he' <;> rw [he] at he' <;> cases he'
          simp only [bind_assoc, pure_bind]

omit [Checked.LegacyTransaction] in
/-- Native top-level preparation and tracing have the exact JSON and refund effects of
the waiting message, for any choice of projection-only transaction metadata. -/
theorem runInput_json_observe (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (template : Checked.LegacyTransaction)
    (authorizationRefund : Nat → IO Unit) (msg : Msg) (runId : String) :
    (fun _ => ()) <$> Checked.Trace.runInput
        (@Legacy.sink template IO (TraceJson.sink cfg state trace frames))
        (if msg.benv.stat.rules.stateGas.isNone && msg.target.isSome
          then authorizationRefund else fun _ => pure ())
        (Checked.TopLevel.Input.ofLegacy msg) runId =
      (fun _ => ()) <$> TraceTransaction.runMessage
        (TraceJson.sink cfg state trace frames) authorizationRefund msg runId := by
  rw [← runMessage_json]
  cases hp : TopLevel.prepare msg with
  | error fault =>
    have native : Checked.TopLevel.prepareNative (.ofLegacy msg) = .error fault := by
      rw [Checked.TopLevel.prepareNative_observe]
      unfold Checked.TopLevel.prepare
      split <;> rename_i h <;> rw [hp] at h <;> cases h
      rfl
    unfold Checked.Trace.runInput runMessage
    split <;> rename_i h <;> rw [native] at h <;> cases h
    split <;> rename_i h <;> rw [hp] at h <;> cases h
    simp only [map_pure]
  | ok prepared =>
    let checked := Checked.TopLevel.ofPreparation msg prepared hp
    have native : Checked.TopLevel.prepareNative (.ofLegacy msg) = .ok (.ofWaiting checked) := by
      rw [Checked.TopLevel.prepareNative_observe]
      unfold Checked.TopLevel.prepare
      split <;> rename_i h <;> rw [hp] at h <;> cases h
      rfl
    have prep : (Checked.TopLevel.Prepared.ofWaiting checked).toPreparation = checked := by
      cases checked <;> rfl
    let waitingTemplate : Checked.LegacyTransaction := ⟨match prepared with
      | .frame frame _ => frame.message.context.tx
      | .refused .. => msg.tenv.stat⟩
    unfold Checked.Trace.runInput runMessage
    split <;> rename_i h <;> rw [native] at h <;> cases h
    generalize (if msg.benv.stat.rules.stateGas.isNone && msg.target.isSome
      then authorizationRefund else fun _ => pure () : Nat → IO Unit) = report
    split <;> rename_i h <;> rw [hp] at h <;> cases h
    simp only [map_bind, map_pure]
    rw [prep, runPrepared_json_template cfg state trace frames template waitingTemplate]

omit [Checked.LegacyTransaction] in
/-- The production signed-transaction tracer has the same JSON and refund effects as the
waiting tracer, including admission failures, preparation refusals and immediate exits. -/
theorem runNativeTransaction_json_effects (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (template : Checked.LegacyTransaction)
    (authorizationRefund : Nat → IO Unit) {benv : Benv} (fresh : benv.Fresh) (bout : BlockOutput)
    (tx : Transaction) (index : Nat) (runId : String) :
    (fun _ => ()) <$> Checked.Trace.runTransaction
        (@Legacy.sink template IO (TraceJson.sink cfg state trace frames)) authorizationRefund benv.stat.toBlockContext benv.state
        bout tx index runId =
      (fun _ => ()) <$> TraceTransaction.runTransaction
        (TraceJson.sink cfg state trace frames) authorizationRefund benv bout tx index runId := by
  unfold Checked.Trace.runTransaction TraceTransaction.runTransaction
  have hadmit := Checked.Transaction.admit_observe benv bout tx index
  split
  next error hna =>
    rw [hadmit] at hna
    split <;> rename_i h <;> rw [h] at hna <;> cases hna
    simp only [map_pure]
  next nativeAdmitted hna =>
    rw [hadmit] at hna
    obtain ⟨admitted, ha, rfl⟩ : ∃ a, Transaction.admit benv bout tx index = .ok a ∧
        Checked.Transaction.Admitted.ofLegacy a = nativeAdmitted := by
      cases h : Transaction.admit benv bout tx index with
      | error => rw [h] at hna; cases hna
      | ok a => rw [h] at hna; cases hna; exact ⟨a, rfl, rfl⟩
    have begun := Transaction.admit_begun fresh ha
    have hctx : benv.stat.toBlockContext = admitted.benv.stat.toBlockContext := by
      rw [Transaction.admit_benv ha]; rfl
    have hst : benv.state = admitted.benv.state := by
      rw [Transaction.admit_benv ha]; rfl
    cases hp : Transaction.prepare admitted tx index with
    | error error =>
      have hn : Checked.Transaction.prepare benv.stat.toBlockContext benv.state
          (.ofLegacy admitted) tx = .error error := by
        rw [hctx, hst, Checked.Transaction.prepare_observe begun tx index, hp]
        rfl
      split <;> rename_i h <;> rw [hn] at h <;> cases h
      split <;> rename_i h <;> rw [ha] at h <;> cases h
      split <;> rename_i h <;> rw [hp] at h <;> cases h
      simp only [map_pure]
    | ok prepared =>
      have hn : Checked.Transaction.prepare benv.stat.toBlockContext benv.state
          (.ofLegacy admitted) tx = .ok (.ofLegacy prepared) := by
        rw [hctx, hst, Checked.Transaction.prepare_observe begun tx index, hp]
        rfl
      split <;> rename_i h <;> rw [hn] at h <;> cases h
      split <;> rename_i h <;> rw [ha] at h <;> cases h
      split <;> rename_i h <;> rw [hp] at h <;> cases h
      simp only [← bind_pure_comp, bind_assoc, pure_bind]
      have input : (Checked.Transaction.Prepared.ofLegacy prepared).input =
          Checked.TopLevel.Input.ofLegacy prepared.msg := rfl
      have refund : ((Checked.TopLevel.Input.ofLegacy prepared.msg).message.context.block.rules.stateGas.isNone &&
          (Checked.TopLevel.Input.ofLegacy prepared.msg).message.target.isSome) =
          (prepared.msg.benv.stat.rules.stateGas.isNone && prepared.msg.target.isSome) := rfl
      rw [input, refund]
      simpa only [← bind_pure_comp] using
        runInput_json_observe cfg state trace frames template authorizationRefund prepared.msg runId

omit [Checked.LegacyTransaction] in
private theorem waitingMessage_of_success {benv bout tx index run output}
    (traced : TraceTransaction.TransactionResult benv bout tx index)
    (h : Transaction.run benv bout tx index = .ok (run, output)) :
    traced.messageRun = some run.message := by
  unfold Transaction.run at h
  obtain ⟨admitted, ha, h⟩ := Except.bind_eq_ok h
  obtain ⟨prepared, hp, h⟩ := Except.bind_eq_ok h
  obtain ⟨message, hm, hs⟩ := Except.bind_eq_ok h
  have hmessage : TopLevel.run prepared.msg = .ok message := by
    cases hw : TopLevel.run prepared.msg <;> rw [hw] at hm <;> cases hm
    rfl
  unfold Transaction.settleRun at hs
  obtain ⟨_, _, hs⟩ := Except.bind_eq_ok hs
  cases hs
  rw [traced.observes]
  simp only [TraceTransaction.prepareTransaction, ha, bind, Except.bind, hp, Except.toOption,
    Option.bind, hmessage]

omit [Checked.LegacyTransaction] in
/-- Both signed tracers produce the same JSON effects and the same observations consumed by
the transaction summary, including the final state, block output, return bytes and halt. -/
theorem runNativeTransaction_json (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (template : Checked.LegacyTransaction)
    (authorizationRefund : Nat → IO Unit) {benv : Benv} (fresh : benv.Fresh) (bout : BlockOutput)
    (tx : Transaction) (index : Nat) (runId : String) :
    let native (r : Checked.Trace.TransactionResult benv.stat.toBlockContext benv.state bout tx index) :=
      (r.value.map (fun (run, out) => ((run.state, out), run.message.settlement run.entry))).map
        (fun (out, effects) => (out, some effects))
    let waiting (r : TraceTransaction.TransactionResult benv bout tx index) :=
      r.value.map (fun out => (out, r.messageRun.map Checked.TopLevel.Settlement.ofLegacy))
    native <$> Checked.Trace.runTransaction
        (@Legacy.sink template IO (TraceJson.sink cfg state trace frames)) authorizationRefund benv.stat.toBlockContext benv.state
        bout tx index runId =
      waiting <$> TraceTransaction.runTransaction
        (TraceJson.sink cfg state trace frames) authorizationRefund benv bout tx index runId := by
  intro native waiting
  let observed := ((Transaction.run benv bout tx index).map
    (fun (run, out) => ((run.state, out), Checked.TopLevel.Settlement.ofLegacy run.message))).map
      (fun (out, effects) => (out, some effects))
  have hl : native = (fun _ : Unit => observed) ∘ (fun _ => ()) := by
    funext result
    dsimp only [native, observed, Function.comp_apply]
    rw [result.erases, Checked.Transaction.run_settlement_observe fresh]
  have hr : waiting = (fun _ : Unit => observed) ∘ (fun _ => ()) := by
    funext result
    dsimp only [waiting, observed, Function.comp_apply]
    rw [result.erases]
    cases h : Transaction.run benv bout tx index with
    | error => rfl
    | ok value =>
      rcases value with ⟨run, out⟩
      rw [waitingMessage_of_success result h]
      rfl
  rw [hl, hr]
  simp only [comp_map, runNativeTransaction_json_effects _ _ _ _ _ _ fresh]

/-! ### The transaction boundary -/

private theorem prepared_originalState {benv : Benv} {bout : BlockOutput} {tx : Transaction}
    {index : Nat} {prepared : Transaction.Prepared}
    (h : TraceTransaction.prepareTransaction benv bout tx index = .ok prepared) :
    prepared.msg.benv.stat.origState = benv.state := by
  obtain ⟨checked, hc, hp⟩ := Except.bind_eq_ok h
  have hchecked : checked.benv.stat.origState = benv.state := Transaction.admit_originalState hc
  unfold Transaction.prepare at hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨msg, hm, hp⟩ := Except.bind_eq_ok hp
  cases hp
  unfold prepareMessage at hm
  cases tx.type.to? <;> cases hm <;> exact hchecked

/-- The existing transaction observations and the Checked run that produced them. -/
structure TransactionResult (benv : Benv) (bout : BlockOutput) (tx : Transaction) (index : Nat)
    extends TraceTransaction.TransactionResult benv bout tx index where
  checkedRun : Option (Msg × Checked.TopLevel.Run)
  observesChecked : checkedRun =
    (TraceTransaction.prepareTransaction benv bout tx index).toOption.bind fun prepared =>
      (Checked.TopLevel.run prepared.msg).toOption.map fun run => (prepared.msg, run)

/-- The retained frame uses the transaction entry state as its SSTORE baseline.
The body supplies its current prefix state, including earlier operations. -/
theorem TransactionResult.frame_originalState {benv bout tx index}
    (result : TransactionResult benv bout tx index) {msg : Msg} {f : Checked.Frame}
    {refund : Nat} {run : Checked.Frame.TopRun}
    (h : result.checkedRun = some (msg, .frame f refund run)) :
    f.message.context.tx.originalState = benv.state := by
  rw [result.observesChecked] at h
  cases hp : TraceTransaction.prepareTransaction benv bout tx index with
  | error => rw [hp] at h; cases h
  | ok prepared =>
    rw [hp] at h
    cases hr : Checked.TopLevel.run prepared.msg <;> simp only [Except.toOption, Option.bind, hr, Option.map] at h
    · cases h
    · cases h
      exact (Checked.TopLevel.run_frame_originalState hr).trans (prepared_originalState hp)

/-- Settlement with a refund supplied by the Checked run. The other observations
still come from the waiting run representation. -/
private def settleRunWithRefund (checked : Transaction.Admitted) (prepared : Transaction.Prepared)
    (tx : Transaction) (index : Nat) (run : TopLevelRun) (refund : Except Fault Nat) :
    Except TransitionError (TransactionRun × BlockOutput) := do
  let benv := prepared.benv
  let bout := prepared.bout
  let sender := prepared.sender
  let effectiveGasPrice := prepared.effectiveGasPrice
  let txBlobGasUsed := prepared.txBlobGasUsed
  let calldataFloorGasCost := prepared.calldataFloorGasCost
  let refundCounter : Nat ← refund.mapError (fun e => TransitionError.vm e.toEvmError)
  let settlement :=
    settleTransactionGas benv.stat.rules tx.gasLimit calldataFloorGasCost
      run.gasLeft run.stateGasLeft refundCounter run.stateGasUsed
  let gasRefundAmount : Nat := settlement.gasLeft * effectiveGasPrice
  let priorityFeePerGas := effectiveGasPrice - benv.stat.baseFeePerGas
  let transactionFee := settlement.gasUsed * priorityFeePerGas
  let state := run.state.addBal sender gasRefundAmount.toU256
  let storageWrites := run.storageWrites.clearIfEmpty state sender
  let state := state.addBal benv.stat.coinbase transactionFee.toU256
  let storageWrites := storageWrites.clearIfEmpty state benv.stat.coinbase
  let storageWrites := run.accountsToDelete.toList.foldl
    (fun writes a => writes.eraseAddress a) storageWrites
  let state := settleSelfdestructs benv.stat.rules run.accountsToDelete.toList state
  let state := sweepTouchedAccounts benv.stat.rules run.touchedAccounts.toList state
  let bout ← .ok (bout.withGasSettlement settlement txBlobGasUsed)
  let receipt := makeReceipt tx run.error bout.cumulativeGasUsed run.logs
  let receiptKey : Bytes := Rlp.Item.toBytes <| .bytes index.toBytes
  let bout ← .ok {bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie := bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ run.logs}
  let bal := match benv.stat.rules.blockAccessListRules with
    | none => bout.blockAccessListBuilder
    | some _ => bout.blockAccessListBuilder.incorporate (index + 1) benv.state state
        (sender :: benv.stat.coinbase :: run.accountReads.toList)
        run.storageReads.toList storageWrites.toList
  .ok (⟨index, tx, checked.sender, checked.intrinsicGas, prepared.txBlobGasUsed, checked.effectiveGasPrice,
    run, settlement, state, receipt, storageWrites⟩, {bout with blockAccessListBuilder := bal})

private def settleMessage (admitted : Transaction.Admitted) (prepared : Transaction.Prepared)
    (tx : Transaction) (index : Nat) (message : MessageResult prepared.msg) :
    Except TransitionError (TransactionRun × BlockOutput) := do
  let observed ← message.value.mapError (fun e => TransitionError.vm e.toEvmError)
  settleRunWithRefund admitted prepared tx index observed (message.run >>= Checked.TopLevel.Run.refundCounter)

/-- The typed refund supplies the same whole settlement, including errors, gas,
surviving storage writes, receipt and block summary. -/
theorem settleMessage_eq (admitted : Transaction.Admitted) (prepared : Transaction.Prepared)
    (tx : Transaction) (index : Nat) (message : MessageResult prepared.msg) :
    settleMessage admitted prepared tx index message = (do
      let observed ← message.value.mapError (fun e => TransitionError.vm e.toEvmError)
      Transaction.settleRun admitted prepared tx index observed) := by
  unfold settleMessage
  rw [message.refund_erases]
  cases message.value <;> rfl

/-- Trace one Checked message, then settle with its typed refund. -/
def runTransaction {m : Type → Type} [Monad m] (sink : Trace.Sink m)
    (authorizationRefund : Nat → m Unit) (benv : Benv) (bout : BlockOutput) (tx : Transaction)
    (index : Nat) (runId : String) : m (TransactionResult benv bout tx index) := do
  match ha : Transaction.admit benv bout tx index with
  | .error error =>
    pure {
      value := .error error
      messageRun := none
      checkedRun := none
      erases := by simp only [Transaction.run, ha, bind, Except.bind]; rfl
      observes := by simp only [TraceTransaction.prepareTransaction, ha, bind, Except.bind]; rfl
      observesChecked := by simp only [TraceTransaction.prepareTransaction, ha, bind, Except.bind]; rfl }
  | .ok admitted =>
    match hp : Transaction.prepare admitted tx index with
    | .error error =>
      pure {
        value := .error error
        messageRun := none
        checkedRun := none
        erases := by simp only [Transaction.run, ha, hp, bind, Except.bind]; rfl
        observes := by simp only [TraceTransaction.prepareTransaction, ha, hp, bind, Except.bind]; rfl
        observesChecked := by simp only [TraceTransaction.prepareTransaction, ha, hp, bind, Except.bind]; rfl }
    | .ok prepared =>
      let message ← runMessage sink authorizationRefund prepared.msg runId
      pure {
        value := (fun pair => (pair.1.state, pair.2)) <$> settleMessage admitted prepared tx index message
        messageRun := message.value.toOption
        checkedRun := message.run.toOption.map (fun run => (prepared.msg, run))
        erases := by
          rw [settleMessage_eq, message.erases]
          simp only [Transaction.run, ha, hp, bind, Except.bind]
        observes := by
          simp only [TraceTransaction.prepareTransaction, ha, hp, bind, Except.bind, message.erases]
          rfl
        observesChecked := by
          simp only [TraceTransaction.prepareTransaction, ha, hp, bind, Except.bind, message.run_erases]
          rfl }

/-- The Checked transaction has the same JSON effects, transaction value and
complete message observation as the current tracer. In particular, the
message observation determines the return data and success in the summary. -/
theorem runTransaction_json (cfg : TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (authorizationRefund : Nat → IO Unit) (benv : Benv)
    (bout : BlockOutput) (tx : Transaction) (index : Nat) (runId : String) :
    (fun result => (result.value, result.messageRun)) <$> runTransaction
      (TraceJson.sink cfg state trace frames) authorizationRefund benv bout tx index runId =
    (fun result => (result.value, result.messageRun)) <$> TraceTransaction.runTransaction
      (TraceJson.sink cfg state trace frames) authorizationRefund benv bout tx index runId := by
  let sink := TraceJson.sink cfg state trace frames
  have effects : (fun _ => ()) <$> runTransaction sink authorizationRefund benv bout tx index runId =
      (fun _ => ()) <$> TraceTransaction.runTransaction sink authorizationRefund benv bout tx index runId := by
    unfold runTransaction TraceTransaction.runTransaction
    split
    · rename_i error ha
      split <;> rename_i h <;> rw [ha] at h <;> cases h
      rfl
    · rename_i admitted ha
      split
      · rename_i error hp
        split <;> rename_i h <;> rw [ha] at h <;> cases h
        split <;> rename_i h <;> rw [hp] at h <;> cases h
        rfl
      · rename_i prepared hp
        split <;> rename_i h <;> rw [ha] at h <;> cases h
        split <;> rename_i h <;> rw [hp] at h <;> cases h
        simpa only [← bind_pure_comp, bind_assoc, pure_bind] using
          runMessage_json cfg state trace frames authorizationRefund prepared.msg runId
  let observation := ((fun pair => (pair.1.state, pair.2)) <$> Transaction.run benv bout tx index,
    (TraceTransaction.prepareTransaction benv bout tx index).toOption.bind
      fun prepared => (TopLevel.run prepared.msg).toOption)
  have checkedObs : (fun result : TransactionResult benv bout tx index => (result.value, result.messageRun)) =
      (fun _ : Unit => observation) ∘ (fun _ => ()) :=
    funext fun result => congrArg₂ Prod.mk result.erases result.observes
  have currentObs : (fun result : TraceTransaction.TransactionResult benv bout tx index =>
      (result.value, result.messageRun)) = (fun _ : Unit => observation) ∘ (fun _ => ()) :=
    funext fun result => congrArg₂ Prod.mk result.erases result.observes
  rw [checkedObs, currentObs]
  simpa only [← comp_map] using congrArg (fun action => (fun _ : Unit => observation) <$> action) effects

end Jaune.Bridge.G2b.CheckedTrace
