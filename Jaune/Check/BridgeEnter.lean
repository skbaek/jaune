-- Check/BridgeEnter.lean : ties the W1 unit D bridge to the adapter it cannot import.
--
-- Check module (see `scripts/layering.json`). `Jaune.Bridge.Enter` restates the prepared
-- top frame's entry, `TraceTransaction.preparedEntry`, as `Legacy.preparedEntry`, because a
-- bridge module may not import an adapter. This check states that the two are the same
-- function, so `Staging.enterWith_prepared` is about today's prepared entry. It goes with the
-- bridge module after the gate's tag.
import Jaune.Bridge.Enter
import Jaune.TraceTransaction

example : Jaune.TraceTransaction.preparedEntry = Jaune.Legacy.preparedEntry := rfl
