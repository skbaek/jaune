import Jaune.MessageCall.CheckedParts
import Jaune.MessageCall.CheckedStep
import Jaune.Fuel

/-! The checked-memory frame interpreter. -/
namespace Jaune.Checked

open Jaune

/-- The fuel-bounded driver over `Checked.Step`. -/
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

end Jaune.Checked
