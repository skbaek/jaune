import Jaune.MessageCall.Trace
import Jaune.Transaction

/-!
Transaction-side tracing certificates, kept outside the core executor's import
closure. `Jaune.Run.Trace` uses them to tie the observed results to the pure
message and transaction runners.
-/
namespace Jaune
open Jaune

/-- Successful monadic observations carry the value of the existing pure
boundary. The expected value appears only in a type and an erased proof. -/
structure TraceTransaction.Certified {α : Type} (expected : α) where
  value : α
  erases : value = expected














end Jaune
