import Jaune.MessageCall.Exec

/-!
# The checked tracer's events (goal `jaune-shape-and-names-v1`, G2b, Neon review finding 2)

The run identity and the events the checked tracer (`Jaune.MessageCall.CheckedTrace`) emits, over
the checked interpreter's own types: a running frame and its message, a checked step, a frame and
its entry, a frame's exit or fault, a settled frame result, and the caller's resumption after its
child. The serialiser `Jaune.MessageCall.CheckedTraceJson` reads them.

At the `gate/g2b` tag the bridge `Jaune.Bridge.G2b.CheckedTrace` projected each event onto the
`Devm` tracer's event vocabulary and proved the serialised stream unchanged; the bridge was deleted
with the `Devm` tracer after the tag (bridge ledger, gate G2b). This module sits outside `Jaune.lean`'s import
closure.
-/

namespace Jaune.Trace

open Jaune

/-- Explicit run identity plus a unique frame number and observed call depth. The depth counts
entered frames, unlike a message's remaining depth allowance. -/
structure Context where
  runId : String
  frame : Nat
  depth : Nat
  deriving Repr

/-- The trace events. `instruction` carries the frame's message, the running frame before the step
and the step's outcome; `entered` the frame and its entry; `exited` how the frame's run stopped,
none when fuel ran out; `settled` the settled result; `resumed` the caller's resumption after its
child. -/
inductive Event where
  | instruction (context : Context) (message : Message) (before : Frame.Running)
      (step : Except Fault Step)
  | entered (context : Context) (frame : Frame) (entry : Frame.Entry)
  | exited (context : Context) (outcome : Option (Except Fault Frame.Exit))
  | settled (context : Context) (frame : Frame) (result : Except Fault Frame.Result)
  | resumed (parent : Context) (childFrame : Nat)
      (caller : Except Fault (Except (ExceptionalHalt × Frame.State) Frame.State))

abbrev Sink (m : Type → Type) := Event → m Unit

end Jaune.Trace
