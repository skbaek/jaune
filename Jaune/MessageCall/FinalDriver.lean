import Jaune.MessageCall.FinalStep
import Jaune.MessageCall.FinalParts
import Jaune.Fuel

/-!
# The driver over `Frame.Running` (goal `jaune-shape-and-names-v1`, W3 unit W3-3)

The final form of the fuelled driver (W1/W3 design, revision 2 §2.5): `Staging.execFueled` runs a
frame step by step (`Staging.step`). A step that spawns a child enters it (`Staging.enter`),
runs it if it has code to run, settles how it stopped (`Staging.settle`), and resumes the caller
with the settled result (`Staging.resume`).

The driver returns how the frame stopped (`Frame.Exit`) or a fault, on the fault channel; a fault
carries no state. It consumes fuel exactly as the `Devm` driver does: one unit per step, and a
child's run and its caller's continuation each get the fuel that remains.

The total `Staging.exec` over this driver is in `Jaune.MessageCall.FinalExec`, a separate module,
so that the cached twin of this driver (`Jaune.Implementation.FinalCachedDriver`) can be imported
before `exec` is compiled once the compiled-code substitution moves to it.
-/

namespace Jaune.Staging

open Jaune

/-- The fuel-bounded driver over `Staging.Step`. -/
def execFueled : Frame.Running → Nat → Fueled Fault Frame.Exit
  | _, 0 => Fueled.exhausted
  | r, fuel + 1 =>
    match step r with
    | .error fault => Fueled.ofExcept (.error fault)
    | .ok (.exit e) => Fueled.ofExcept (.ok e)
    | .ok (.next pc s) => execFueled ⟨pc, r.context, s⟩ fuel
    | .ok (.spawn child pending pc) =>
      let settled : Option (Except Fault Frame.Result) :=
        match enter child with
        | .done result => some result
        | .run childRunning => ((execFueled childRunning fuel).run).map (· >>= settle child)
      match settled with
      | none => Fueled.exhausted
      | some (.error fault) => Fueled.ofExcept (.error fault)
      | some (.ok result) =>
        match resume r.context.block.rules pending child.checkpoint result with
        | .error fault => Fueled.ofExcept (.error fault)
        | .ok (.error (reason, s)) => Fueled.ofExcept (.ok (.halted reason s))
        | .ok (.ok s) => execFueled ⟨pc, r.context, s⟩ fuel

end Jaune.Staging
