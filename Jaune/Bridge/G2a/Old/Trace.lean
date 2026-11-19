import Jaune.TraceTransaction
import Jaune.Bridge.G2a.Old.Transaction
import Jaune.Run.Trace
import Jaune.Bridge.G2a.Consumers

/-!
# The old trace drivers (goal `jaune-shape-and-names-v1`, gate G2a, adapter-class old side)

The bridge at the traced transaction's value: the staged traced transaction returns today's
`processTransaction` result. The old drivers of `Jaune.TraceTransaction` move here at the switch.
-/

namespace Jaune

open Jaune Jaune.Staging

/-- **Bridge at the traced transaction's value.** For every monad, sink and input, the value the
staged traced transaction returns is today's `processTransaction` result, and so the value
`Jaune.TraceTransaction.runTransaction` returns. -/
theorem Staging.TraceTransaction.runTransaction_value_eq {benv : Benv} {bout : BlockOutput} {tx : Transaction}
    {index : Nat} (result : Staging.TraceTransaction.TransactionResult benv bout tx index)
    (old : Jaune.TraceTransaction.TransactionResult benv bout tx index) :
    result.value = old.value := by
  rw [result.erases, Staging.B2.Transaction.run_output, old.erases, Bridge.G2a.processTransaction_eq_b2]

end Jaune
