import Jaune.Execution
import Jaune.MessageCall

/-!
# Measures and position predicates (goal `jaune-shape-and-names-v1`, G2b N4-0)

Which operation a code position holds, whether a state-gas meter has settled, the gas measure of
a frame result, and the list-length facts the run invariants use. Extracted unchanged from the
`Devm`-era frame and message-call proof modules.
-/

section
open Jaune
namespace Jaune
def HaltOp.At (code : ByteArray) (pc : Nat) (l : HaltOp) : Prop := code.getOp pc = some (.halt l)
end Jaune
end

section
open Jaune
namespace Jaune
def NextOp.At (code : ByteArray) (pc : Nat) (n : NextOp) : Prop := code.getOp pc = some (.next n)
end Jaune
end

section
open Jaune
namespace Jaune
def JumpOp.At (code : ByteArray) (pc : Nat) (j : JumpOp) : Prop := code.getOp pc = some (.jump j)
end Jaune
end

section
open Jaune
namespace Jaune
def PlainOp.At (code : ByteArray) (pc : Nat) (r : PlainOp) : Prop := code.getOp pc = some (.next (.plain r))
end Jaune
end

section
open Jaune
namespace Jaune
def MessageOp.At (code : ByteArray) (pc : Nat) (x : MessageOp) : Prop := code.getOp pc = some (.next (.message x))
end Jaune
end

section
namespace Jaune
/-- A failed child's meter as settlement leaves it: no committed or outstanding spill, and the
reservoir at its baseline. -/
def StateGasMeter.Settled (m : StateGasMeter) : Prop :=
  m.committedSpill = 0 ∧ m.spilled = 0 ∧ m.left = m.baseline
end Jaune
end

section
namespace Jaune
instance (m : StateGasMeter) : Decidable m.Settled := by
  unfold StateGasMeter.Settled; infer_instance
end Jaune
end

section
namespace Jaune.RunInvariants
theorem List.swap_length {ξ : Type} {l l' : List ξ} {k : Nat} (h : List.swap l k = some l') :
    l'.length = l.length := by
  cases l with
  | nil => simp [List.swap] at h
  | cons x xs =>
    simp only [List.swap, bind, Option.bind] at h
    split at h
    · cases h
    · cases h; simp
end Jaune.RunInvariants
end

section
namespace Jaune.RunInvariants
theorem List.exchange_length {ξ : Type} {l l' : List ξ} {n m : Nat}
    (h : List.exchange l n m = some l') : l'.length = l.length := by
  unfold List.exchange at h
  cases hn : l[n]? <;> cases hm : l[m]? <;> simp_all [bind, Option.bind] <;> cases h <;> simp
end Jaune.RunInvariants
end

section
open Jaune
namespace Jaune
/-- A frame result's gas measure: what its caller can absorb, its execution gas and its
state-gas spill. -/
def Frame.Result.gasMeasure (r : Frame.Result) : Nat :=
  r.gasLeft + r.stateGas.spilled + r.stateGas.committedSpill
end Jaune
end
