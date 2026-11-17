import Jaune.Execution
import Jaune.MessageCall.Top

/-!
# The four-part message call: maps from today's definitions (W1 unit B, bridge)

The maps between today's message-call types and the staged ones of `Jaune.MessageCall`, used
only in bridges. (`Frame.State.ofDevm` and `toDevm` sit in `Jaune.MessageCall` itself, and `Message.ofLegacy`
and `Frame.ofTop` in `Jaune.MessageCall.Top`: the W1 bodies use them.) They live in this bridge module with the old side and
are deleted with it after the gate's tag (goal 3.1).

Also here, about today's definitions: `Resume.parent`, the saved caller every `Resume` carries,
and `Execution.Clean`, the premise that a raw result stores no settled error (the W1 design note,
section 3.1).
-/

namespace Jaune

/-- The saved caller a `Resume` carries. -/
def Resume.parent : Resume → Devm
  | .create parent _ => parent
  | .call parent _ _ => parent
  | .createAmsterdam _ parent _ _ => parent
  | .callAmsterdam _ parent _ _ _ => parent

/-- A raw result that stores no settled error. The error channel is unconstrained. -/
def Execution.Clean : Execution → Prop
  | .ok d => d.error = none
  | .error _ => True

end Jaune

namespace Jaune

/-- Grouping by lifetime and back loses nothing of a state with no output and no stored error. -/
theorem Frame.State.toDevm_ofDevm (d : Devm) (hout : d.output = []) (herr : d.error = none) :
    (Frame.State.ofDevm d).toDevm = d := by
  rcases d with ⟨⟨stack, memory, gasLeft, stateGas⟩, ⟨logs, refund, output, deletions,
    returnData, error, accessed, keys, created, accountReads, storageReads, touched⟩, world⟩
  simp only [Devm.output, Devm.error] at hout herr
  subst hout herr
  rfl

/-- What a `Resume` waits with besides its saved caller. -/
def Pending.ofLegacy : Resume → Pending
  | .create parent newAddress =>
    ⟨.create newAddress, false, parent.output, parent.error⟩
  | .call parent outputIndex outputSize =>
    ⟨.call outputIndex outputSize, false, parent.output, parent.error⟩
  | .createAmsterdam _ parent newAddress charged =>
    ⟨.create newAddress, charged, parent.output, parent.error⟩
  | .callAmsterdam _ parent outputIndex outputSize charged =>
    ⟨.call outputIndex outputSize, charged, parent.output, parent.error⟩

/-- A spawned child frame of today, with the `Resume` it was spawned with: the message is the
outer one (before a creation's set-up), the checkpoint is the saved caller. -/
def Frame.ofLegacy (f : Jaune.Legacy.Frame) (rsm : Resume) : Frame :=
  ⟨Message.ofLegacy f.outer f.isCreate, Frame.State.ofDevm rsm.parent⟩

end Jaune

