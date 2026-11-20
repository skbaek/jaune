import Jaune.MessageCall

/-!
# Canonical worlds under the world operations (goal `jaune-shape-and-names-v1`, G2b N4-0)

Canonicality of a world after a balance change or a creation's set-up, of a value transfer's
result, and of a frame result. Extracted unchanged from `Jaune.MessageCall.Canonical`.
-/

section
open Jaune
namespace Jaune
theorem World.Canonical.createSetUp {w : World} (h : w.Canonical) (a : Address) :
    (w.createSetUp a).Canonical :=
  ⟨State.Canonical.incrNonce (State.Canonical.setStor h.1 a Storage.canonical_empty) a, h.2⟩
end Jaune
end

section
open Jaune
namespace Jaune
theorem World.Canonical.subtractBalance {w w' : World} (h : w.Canonical) {a : Address} {v : U256}
    (hw : w.subtractBalance a v = some w') : w'.Canonical := by
  unfold World.subtractBalance at hw
  cases hs : w.state.subBal a v with
  | none => rw [hs] at hw; nomatch hw
  | some st =>
    rw [hs] at hw
    cases hw
    exact ⟨State.Canonical.subBal h.1 hs, h.2⟩
end Jaune
end

section
open Jaune
namespace Jaune
theorem World.Canonical.addBalance {w : World} (h : w.Canonical) (a : Address) (v : U256) :
    (w.addBalance a v).Canonical :=
  ⟨State.Canonical.addBal h.1 a v, h.2⟩
end Jaune
end

section
open Jaune
namespace Jaune
end Jaune
end

section
open Jaune
namespace Jaune
/-- What a frame result must preserve: a successful frame's world is canonical. -/
def Frame.Result.Canonical : Frame.Result → Prop
  | .success _ _ _ world _ _ => world.Canonical
  | _ => True
end Jaune
end
