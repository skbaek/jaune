import Jaune.MessageCall.Trace
import Jaune.Transaction

/-!
Transaction-side tracing, kept outside the core executor's import closure.
Each traced message operation runs the top frame with `Trace.runFrame` and
renders its settled result exactly as `processMessageCall` does, so its
certificate is the public operation itself.
-/
namespace Jaune
open Jaune

/-- Successful monadic observations carry the value of the existing pure
boundary. The expected value appears only in a type and an erased proof. -/
structure TraceTransaction.Certified {α : Type} (expected : α) where
  value : α
  erases : value = expected














end Jaune
