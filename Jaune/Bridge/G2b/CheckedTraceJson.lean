import Jaune.Bridge.G2b.CheckedTrace
import Jaune.MessageCall.CheckedTraceJson

/-!
# Bridge: the checked tracer's serialiser against the `Devm` tracer's (G2b, Neon review finding 2)

Old side: the serialiser `Jaune.TraceJson.consume`/`TraceJson.sink`
(`Jaune/MessageCall/TraceJson.lean`), unedited, over the `Devm` tracer's events. New side:
`Checked.TraceJson.consume`/`Checked.TraceJson.sinkWith` (`Jaune.MessageCall.CheckedTraceJson`),
over the checked tracer's own events (`Jaune.MessageCall.CheckedTraceEvent`).

* `consume_event`: for every event and serialiser state, the new serialiser returns the old one's
  rows, and its next state is the old one's, through the state's representation map.
* `sinkWith_event`: so the new `IO` sink, keeping its state in the old sink's reference through
  that map, is the old sink on the projected event (`Legacy.sink`), for every transaction template.
* `runFrame_nativeJson`, `runDirectFrame_nativeJson`, `runNativeTransaction_nativeJson`: composed
  with `Jaune.Bridge.G2b.CheckedTrace`, the checked tracer through the new serialiser writes the
  same `trace.jsonl` and `frames.jsonl` rows, in the same order, and returns the same result as the
  `Devm` tracer and the waiting transaction tracer through the old one (goal 3.1: the serialised
  event stream, proved equal).

The serialiser state lives in an `IO.Ref`; the theorems keep it in the old reference through the
representation map. `TraceMain` keeps the new state in its own reference of the new type; that the
two placements write the same bytes is the statement that a state read and written only through
`get`/`set` is independent of how it is stored, which the theorems here do not state.

It is classified `adapter` in `scripts/layering.json`, as `Jaune.Bridge.G2b.CheckedTrace` is.
Everything here goes with `Devm` after G2b's tag.
-/

namespace Jaune.Bridge.G2b.CheckedTrace

open Jaune

namespace Legacy

/-- A serialiser configuration as the old serialiser's. -/
def config (c : Checked.TraceJson.Config) : TraceJson.Config :=
  ⟨c.runId, c.memory, c.deferSummary, c.maxDataBytes, c.maxSteps, c.maxRowBytes⟩

/-- An open frame as the old serialiser's. -/
def openFrame (f : Checked.TraceJson.OpenFrame) : TraceJson.OpenFrame := ⟨f.id, f.refundBase⟩

/-- An old open frame as the new serialiser's. -/
def ofOpenFrame (f : TraceJson.OpenFrame) : Checked.TraceJson.OpenFrame := ⟨f.id, f.refundBase⟩

/-- A serialiser state as the old serialiser's. -/
def jsonState (s : Checked.TraceJson.State) : TraceJson.State :=
  ⟨s.frames.map openFrame, s.childRefundBase, s.rootRefund, s.steps, s.started, s.closed⟩

/-- An old serialiser state as the new serialiser's. -/
def ofJsonState (s : TraceJson.State) : Checked.TraceJson.State :=
  ⟨s.frames.map ofOpenFrame, s.childRefundBase, s.rootRefund, s.steps, s.started, s.closed⟩

theorem jsonState_ofJsonState (s : TraceJson.State) : jsonState (ofJsonState s) = s := by
  rcases s with ⟨frames, childRefundBase, rootRefund, steps, started, closed⟩
  have h : (frames.map ofOpenFrame).map openFrame = frames := by
    induction frames with
    | nil => rfl
    | cons f frames ih => simp only [List.map_cons, ih]; rfl
  simp only [jsonState, ofJsonState, h]

end Legacy

/-! ### One event -/

section Consume

variable [Checked.LegacyTransaction]

omit [Checked.LegacyTransaction] in
private theorem except_map_fmap {ε α β γ : Type} (g : β → γ) (f : α → β) (x : Except ε α) :
    Except.map g (f <$> x) = (fun a => g (f a)) <$> x := by
  cases x <;> rfl

/-- An instruction row is the old row of the projected running machine and step. -/
theorem instruction_event (cfg : Checked.TraceJson.Config) (context : Checked.Trace.Context)
    (refundBase : Int) (msg : Checked.Message) (r : Checked.Frame.Running)
    (step : Except Fault Checked.Step) :
    Checked.TraceJson.instruction cfg context refundBase msg r step =
      TraceJson.instruction (Legacy.config cfg) (Legacy.context context) refundBase
        (Legacy.evm (msg.toLegacy Checked.LegacyTransaction.template) r) (Legacy.step step) := by
  rcases step with fault | (e | ⟨pc, s⟩ | ⟨child, p, pc⟩)
  · cases fault <;> rfl
  · cases e <;> rfl
  · rfl
  · rfl

/-- A root summary is the old summary of the projected frame. -/
theorem rootSummary_event (cfg : Checked.TraceJson.Config) (f : Checked.Frame)
    (result : Frame.Result) :
    Checked.TraceJson.rootSummary cfg f result =
      TraceJson.rootSummary (Legacy.config cfg) (Legacy.frame f) result := by
  cases result <;> rfl

private theorem consume_fault (cfg : Checked.TraceJson.Config) (st : Checked.TraceJson.State)
    (context : Checked.Trace.Context)
    (msg : Checked.Message) (r : Checked.Frame.Running) (fault : Fault) :
    (Checked.TraceJson.consume cfg st (.instruction context msg r (.error fault))).map
        (fun r => (Legacy.jsonState r.1, r.2)) =
      TraceJson.consume (Legacy.config cfg) (Legacy.jsonState st)
        (Legacy.event (.instruction context msg r (.error fault))) := by
  rcases st with ⟨frames, childRefundBase, rootRefund, steps, started, closed⟩
  rcases cfg with ⟨runId, memory, deferSummary, maxDataBytes, maxSteps, maxRowBytes⟩
  simp only [TraceJson.consume, Legacy.event, Legacy.jsonState, ← instruction_event]
  cases frames <;> cases maxSteps <;>
    simp [Legacy.faultRaw, Checked.TraceJson.consume, Checked.TraceJson.current, TraceJson.current,
      Legacy.config, Legacy.openFrame, Checked.TraceJson.lifecycle, TraceJson.lifecycle,
      Checked.TraceJson.number, TraceJson.number, Legacy.evm, Legacy.step, Message.sevm,
      Checked.Message.toLegacy, Checked.CallContext.toLegacy]
  all_goals (split_ifs <;> first | rfl | (simp only [pure_bind, except_map_fmap]; try rfl))

private theorem consume_finished (cfg : Checked.TraceJson.Config) (st : Checked.TraceJson.State)
    (context : Checked.Trace.Context)
    (msg : Checked.Message) (r : Checked.Frame.Running) (o : Bytes) (s : Checked.Frame.State) :
    (Checked.TraceJson.consume cfg st
        (.instruction context msg r (.ok (.exit (.finished o s))))).map
        (fun r => (Legacy.jsonState r.1, r.2)) =
      TraceJson.consume (Legacy.config cfg) (Legacy.jsonState st)
        (Legacy.event (.instruction context msg r (.ok (.exit (.finished o s))))) := by
  rcases st with ⟨frames, childRefundBase, rootRefund, steps, started, closed⟩
  rcases cfg with ⟨runId, memory, deferSummary, maxDataBytes, maxSteps, maxRowBytes⟩
  simp only [TraceJson.consume, Legacy.event, Legacy.jsonState, ← instruction_event]
  cases frames <;> cases maxSteps <;>
    simp [Legacy.exitRaw, Checked.TraceJson.consume, Checked.TraceJson.current, TraceJson.current,
      Legacy.config, Legacy.openFrame, Checked.TraceJson.lifecycle, TraceJson.lifecycle,
      Checked.TraceJson.number, TraceJson.number, Legacy.evm, Legacy.step, Message.sevm,
      Checked.Message.toLegacy, Checked.CallContext.toLegacy]
  all_goals (split_ifs <;> first | rfl | (simp only [pure_bind, except_map_fmap]; try rfl))

private theorem consume_reverted (cfg : Checked.TraceJson.Config) (st : Checked.TraceJson.State)
    (context : Checked.Trace.Context)
    (msg : Checked.Message) (r : Checked.Frame.Running) (o : Bytes) (s : Checked.Frame.State) :
    (Checked.TraceJson.consume cfg st
        (.instruction context msg r (.ok (.exit (.reverted o s))))).map
        (fun r => (Legacy.jsonState r.1, r.2)) =
      TraceJson.consume (Legacy.config cfg) (Legacy.jsonState st)
        (Legacy.event (.instruction context msg r (.ok (.exit (.reverted o s))))) := by
  rcases st with ⟨frames, childRefundBase, rootRefund, steps, started, closed⟩
  rcases cfg with ⟨runId, memory, deferSummary, maxDataBytes, maxSteps, maxRowBytes⟩
  simp only [TraceJson.consume, Legacy.event, Legacy.jsonState, ← instruction_event]
  cases frames <;> cases maxSteps <;>
    simp [Legacy.exitRaw, Checked.TraceJson.consume, Checked.TraceJson.current, TraceJson.current,
      Legacy.config, Legacy.openFrame, Checked.TraceJson.lifecycle, TraceJson.lifecycle,
      Checked.TraceJson.number, TraceJson.number, Legacy.evm, Legacy.step, Message.sevm,
      Checked.Message.toLegacy, Checked.CallContext.toLegacy]
  all_goals (split_ifs <;> first | rfl | (simp only [pure_bind, except_map_fmap]; try rfl))

private theorem consume_halted (cfg : Checked.TraceJson.Config) (st : Checked.TraceJson.State)
    (context : Checked.Trace.Context)
    (msg : Checked.Message) (r : Checked.Frame.Running) (h : ExceptionalHalt)
    (s : Checked.Frame.State) :
    (Checked.TraceJson.consume cfg st (.instruction context msg r (.ok (.exit (.halted h s))))).map
        (fun r => (Legacy.jsonState r.1, r.2)) =
      TraceJson.consume (Legacy.config cfg) (Legacy.jsonState st)
        (Legacy.event (.instruction context msg r (.ok (.exit (.halted h s))))) := by
  rcases st with ⟨frames, childRefundBase, rootRefund, steps, started, closed⟩
  rcases cfg with ⟨runId, memory, deferSummary, maxDataBytes, maxSteps, maxRowBytes⟩
  simp only [TraceJson.consume, Legacy.event, Legacy.jsonState, ← instruction_event]
  cases frames <;> cases maxSteps <;>
    simp [Legacy.exitRaw, Checked.TraceJson.consume, Checked.TraceJson.current, TraceJson.current,
      Legacy.config, Legacy.openFrame, Checked.TraceJson.lifecycle, TraceJson.lifecycle,
      Checked.TraceJson.number, TraceJson.number, Legacy.evm, Legacy.step, Message.sevm,
      Checked.Message.toLegacy, Checked.CallContext.toLegacy]
  all_goals (split_ifs <;> first | rfl | (simp only [pure_bind, except_map_fmap]; try rfl))

private theorem consume_next (cfg : Checked.TraceJson.Config) (st : Checked.TraceJson.State)
    (context : Checked.Trace.Context)
    (msg : Checked.Message) (r : Checked.Frame.Running) (pc : Nat) (s : Checked.Frame.State) :
    (Checked.TraceJson.consume cfg st (.instruction context msg r (.ok (.next pc s)))).map
        (fun r => (Legacy.jsonState r.1, r.2)) =
      TraceJson.consume (Legacy.config cfg) (Legacy.jsonState st)
        (Legacy.event (.instruction context msg r (.ok (.next pc s)))) := by
  rcases st with ⟨frames, childRefundBase, rootRefund, steps, started, closed⟩
  rcases cfg with ⟨runId, memory, deferSummary, maxDataBytes, maxSteps, maxRowBytes⟩
  simp only [TraceJson.consume, Legacy.event, Legacy.jsonState, ← instruction_event]
  cases frames <;> cases maxSteps <;>
    simp [Checked.TraceJson.consume, Checked.TraceJson.current, TraceJson.current, Legacy.config,
      Legacy.openFrame, Checked.TraceJson.lifecycle, TraceJson.lifecycle, Checked.TraceJson.number,
      TraceJson.number, Legacy.evm, Legacy.step, Message.sevm, Checked.Message.toLegacy,
      Checked.CallContext.toLegacy]
  all_goals (split_ifs <;> first | rfl | (simp only [pure_bind, except_map_fmap]; try rfl))

private theorem consume_spawn (cfg : Checked.TraceJson.Config) (st : Checked.TraceJson.State)
    (context : Checked.Trace.Context)
    (msg : Checked.Message) (r : Checked.Frame.Running) (child : Checked.Frame)
    (p : Staging.Pending) (pc : Nat) :
    (Checked.TraceJson.consume cfg st (.instruction context msg r (.ok (.spawn child p pc)))).map
        (fun r => (Legacy.jsonState r.1, r.2)) =
      TraceJson.consume (Legacy.config cfg) (Legacy.jsonState st)
        (Legacy.event (.instruction context msg r (.ok (.spawn child p pc)))) := by
  rcases st with ⟨frames, childRefundBase, rootRefund, steps, started, closed⟩
  rcases cfg with ⟨runId, memory, deferSummary, maxDataBytes, maxSteps, maxRowBytes⟩
  simp only [TraceJson.consume, Legacy.event, Legacy.jsonState, ← instruction_event]
  cases frames <;> cases maxSteps <;>
    simp [Checked.TraceJson.consume, Checked.TraceJson.current, TraceJson.current, Legacy.config,
      Legacy.openFrame, Checked.TraceJson.lifecycle, TraceJson.lifecycle, Checked.TraceJson.number,
      TraceJson.number, Legacy.evm, Legacy.step, Legacy.frame, Message.sevm,
      Checked.Message.toLegacy, Checked.CallContext.toLegacy, Checked.Frame.toLegacy]
  all_goals (split_ifs <;> first | rfl | (simp only [pure_bind, except_map_fmap]; try rfl))

private theorem consume_entered (cfg : Checked.TraceJson.Config) (st : Checked.TraceJson.State)
    (context : Checked.Trace.Context) (f : Checked.Frame) (entry : Checked.Frame.Entry) :
    (Checked.TraceJson.consume cfg st (.entered context f entry)).map
        (fun r => (Legacy.jsonState r.1, r.2)) =
      TraceJson.consume (Legacy.config cfg) (Legacy.jsonState st)
        (Legacy.event (.entered context f entry)) := by
  rcases st with ⟨frames, childRefundBase, rootRefund, steps, started, closed⟩
  rcases cfg with ⟨runId, memory, deferSummary, maxDataBytes, maxSteps, maxRowBytes⟩
  cases frames <;> cases childRefundBase <;>
    simp [Checked.TraceJson.consume, TraceJson.consume, Legacy.event, Legacy.config,
      Legacy.jsonState, Legacy.openFrame, Checked.TraceJson.lifecycle, TraceJson.lifecycle,
      Checked.TraceJson.number, TraceJson.number, Legacy.frame, Checked.Message.toLegacy,
      Checked.CallContext.toLegacy, Checked.Frame.toLegacy]
  all_goals (split_ifs <;> rfl)

private theorem consume_exited (cfg : Checked.TraceJson.Config) (st : Checked.TraceJson.State)
    (context : Checked.Trace.Context) (outcome : Option (Except Fault Checked.Frame.Exit)) :
    (Checked.TraceJson.consume cfg st (.exited context outcome)).map
        (fun r => (Legacy.jsonState r.1, r.2)) =
      TraceJson.consume (Legacy.config cfg) (Legacy.jsonState st)
        (Legacy.event (.exited context outcome)) := by
  rcases st with ⟨frames, childRefundBase, rootRefund, steps, started, closed⟩
  rcases cfg with ⟨runId, memory, deferSummary, maxDataBytes, maxSteps, maxRowBytes⟩
  cases frames <;>
    simp [Checked.TraceJson.consume, TraceJson.consume, Checked.TraceJson.current,
      TraceJson.current, Legacy.event, Legacy.config, Legacy.jsonState, Legacy.openFrame,
      Checked.TraceJson.lifecycle, TraceJson.lifecycle, Checked.TraceJson.number, TraceJson.number]
  all_goals (split_ifs <;> rfl)

private theorem consume_settled (cfg : Checked.TraceJson.Config) (st : Checked.TraceJson.State)
    (context : Checked.Trace.Context) (f : Checked.Frame) (result : Except Fault Frame.Result) :
    (Checked.TraceJson.consume cfg st (.settled context f result)).map
        (fun r => (Legacy.jsonState r.1, r.2)) =
      TraceJson.consume (Legacy.config cfg) (Legacy.jsonState st)
        (Legacy.event (.settled context f result)) := by
  rcases st with ⟨frames, childRefundBase, rootRefund, steps, started, closed⟩
  rcases cfg with ⟨runId, memory, deferSummary, maxDataBytes, maxSteps, maxRowBytes⟩
  cases frames <;> cases result <;>
    simp [Checked.TraceJson.consume, TraceJson.consume, Checked.TraceJson.current,
      TraceJson.current, Legacy.event, Legacy.config, Legacy.jsonState, Legacy.openFrame,
      Checked.TraceJson.lifecycle, TraceJson.lifecycle, Checked.TraceJson.number, TraceJson.number,
      Legacy.frame, Checked.Message.toLegacy, Checked.CallContext.toLegacy, Checked.Frame.toLegacy,
      rootSummary_event]
  all_goals (split_ifs <;> first | rfl | simp only [pure_bind, except_map_fmap])

private theorem consume_resumed (cfg : Checked.TraceJson.Config) (st : Checked.TraceJson.State)
    (context : Checked.Trace.Context)
    (child : Nat)
    (x : Except Fault (Except (ExceptionalHalt × Checked.Frame.State) Checked.Frame.State)) :
    (Checked.TraceJson.consume cfg st (.resumed context child x)).map
        (fun r => (Legacy.jsonState r.1, r.2)) =
      TraceJson.consume (Legacy.config cfg) (Legacy.jsonState st)
        (Legacy.event (.resumed context child x)) := by
  rcases st with ⟨frames, childRefundBase, rootRefund, steps, started, closed⟩
  rcases cfg with ⟨runId, memory, deferSummary, maxDataBytes, maxSteps, maxRowBytes⟩
  cases frames <;>
    simp [Checked.TraceJson.consume, TraceJson.consume, Checked.TraceJson.current,
      TraceJson.current, Legacy.event, Legacy.config, Legacy.jsonState, Legacy.openFrame,
      Checked.TraceJson.lifecycle, TraceJson.lifecycle, Checked.TraceJson.number, TraceJson.number]
  all_goals (split_ifs <;> rfl)

/-- **One event.** The new serialiser on a checked event is the old one on its projection: the
same rows, or the same refusal, and the next state through the representation map. -/
theorem consume_event (cfg : Checked.TraceJson.Config) (st : Checked.TraceJson.State)
    (e : Checked.Trace.Event) :
    (Checked.TraceJson.consume cfg st e).map (fun r => (Legacy.jsonState r.1, r.2)) =
      TraceJson.consume (Legacy.config cfg) (Legacy.jsonState st) (Legacy.event e) := by
  cases e with
  | instruction context msg r step =>
    rcases step with fault | (e | ⟨pc, s⟩ | ⟨child, p, pc⟩)
    · exact consume_fault cfg st context msg r fault
    · cases e with
      | finished o s => exact consume_finished cfg st context msg r o s
      | reverted o s => exact consume_reverted cfg st context msg r o s
      | halted h s => exact consume_halted cfg st context msg r h s
    · exact consume_next cfg st context msg r pc s
    · exact consume_spawn cfg st context msg r child p pc
  | entered context f entry => exact consume_entered cfg st context f entry
  | exited context outcome => exact consume_exited cfg st context outcome
  | settled context f result => exact consume_settled cfg st context f result
  | resumed context child x => exact consume_resumed cfg st context child x

end Consume

/-! ### The `IO` sink -/

-- `IO`'s monad laws, stated in `Jaune.Bridge.G2b.CheckedTrace`.
attribute [local instance] instLawfulMonadEST instLawfulMonadEIO

/-- The new sink, keeping its state in the old sink's reference through the representation
map. -/
def Legacy.nativeSink (cfg : Checked.TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) : Checked.Trace.Sink IO :=
  Checked.TraceJson.sinkWith cfg (Legacy.ofJsonState <$> state.get)
    (fun s => state.set (Legacy.jsonState s)) trace frames

section Sink

variable [Checked.LegacyTransaction]

/-- **The sink.** The new sink on a checked event makes the old sink's writes, reads and updates
on the projected event. -/
theorem nativeSink_event (cfg : Checked.TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (e : Checked.Trace.Event) :
    Legacy.nativeSink cfg state trace frames e =
      TraceJson.sink (Legacy.config cfg) state trace frames (Legacy.event e) := by
  unfold Legacy.nativeSink Checked.TraceJson.sinkWith TraceJson.sink
  simp only [bind_map_left]
  refine bind_congr fun s => ?_
  have h := consume_event cfg (Legacy.ofJsonState s) e
  rw [Legacy.jsonState_ofJsonState] at h
  rw [← h]
  cases Checked.TraceJson.consume cfg (Legacy.ofJsonState s) e <;> rfl

/-- So the new sink is the old sink, through the projection, for every transaction template. -/
theorem nativeSink_eq (cfg : Checked.TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) :
    Legacy.nativeSink cfg state trace frames =
      Legacy.sink (TraceJson.sink (Legacy.config cfg) state trace frames) :=
  funext (nativeSink_event cfg state trace frames)

/-- **Byte-identical serialisation, frame scope.** For every checked frame, the checked tracer
through the new serialiser makes the same row writes as the `Devm` tracer through the old one on
the frame's projection, and returns the same result. -/
theorem runFrame_nativeJson (cfg : Checked.TraceJson.Config) (state : IO.Ref TraceJson.State)
    (trace frames : IO.FS.Handle) (f : Checked.Frame) (runId : String) :
    (fun x => (x.value, x.nextFrame)) <$>
        Checked.Trace.runFrame (Legacy.nativeSink cfg state trace frames) f runId =
      (fun x => (x.value, x.nextFrame)) <$>
        Trace.runFrame (TraceJson.sink (Legacy.config cfg) state trace frames) (Legacy.frame f)
          runId := by
  rw [nativeSink_eq]
  exact runFrame_json _ state trace frames f runId

end Sink

/-- **Byte-identical serialisation, message scope.** `TraceMain`'s message scope traces the directly
initialized checked frame; through the new serialiser it has the old message scope's row writes
and settled result. -/
theorem runDirectFrame_nativeJson (cfg : Checked.TraceJson.Config)
    (state : IO.Ref TraceJson.State) (trace frames : IO.FS.Handle) (msg : Msg) (runId : String) :
    let input := Checked.TopLevel.Input.ofLegacy msg
    (fun x => (x.value, x.nextFrame)) <$> Checked.Trace.runFrame
        (Legacy.nativeSink cfg state trace frames) ⟨input.message, input.checkpoint⟩ runId =
      (fun x => (x.value, x.nextFrame)) <$> Trace.runFrame
        (TraceJson.sink (Legacy.config cfg) state trace frames) (Frame.ofTop msg msg.target.isNone)
        runId := by
  dsimp only
  rw [@nativeSink_eq ⟨default⟩]
  exact runDirectFrame_json _ state trace frames ⟨default⟩ msg runId

/-- **Byte-identical serialisation, transaction scope.** `TraceMain`'s signed-transaction tracer
through the new serialiser has the waiting tracer's row writes through the old one, and the same
observations consumed by the transaction summary: the final state, block output, return bytes and
halt. -/
theorem runNativeTransaction_nativeJson (cfg : Checked.TraceJson.Config)
    (state : IO.Ref TraceJson.State) (trace frames : IO.FS.Handle)
    (authorizationRefund : Nat → IO Unit) {benv : Benv} (fresh : benv.Fresh) (bout : BlockOutput)
    (tx : Transaction) (index : Nat) (runId : String) :
    let native (r : Checked.Trace.TransactionResult benv.stat.toBlockContext benv.state bout tx
        index) :=
      (r.value.map (fun (run, out) => ((run.state, out), run.message.settlement run.entry))).map
        (fun (out, effects) => (out, some effects))
    let waiting (r : TraceTransaction.TransactionResult benv bout tx index) :=
      r.value.map (fun out => (out, r.messageRun.map Checked.TopLevel.Settlement.ofLegacy))
    native <$> Checked.Trace.runTransaction (Legacy.nativeSink cfg state trace frames)
        authorizationRefund benv.stat.toBlockContext benv.state bout tx index runId =
      waiting <$> TraceTransaction.runTransaction
        (TraceJson.sink (Legacy.config cfg) state trace frames) authorizationRefund benv bout tx
        index runId := by
  rw [@nativeSink_eq ⟨default⟩]
  exact runNativeTransaction_json _ state trace frames ⟨default⟩ authorizationRefund fresh bout tx
    index runId

end Jaune.Bridge.G2b.CheckedTrace
