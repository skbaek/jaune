import Jaune.Execution
import Jaune.MessageCall

/-!
# Shared records of the frame vocabulary (goal `jaune-shape-and-names-v1`, G2b N4-0)

The defaults of the static records a frame reads, the substate and trail operations, the
`Pending` a spawn hands the driver, the status word a calling opcode pushes, and `SELFDESTRUCT`'s
fault. They were extracted unchanged from the `Devm`-era message-call modules so that the checked
interpreter no longer imports those modules.
-/
