import Jaune.MessageCall.Step
import Jaune.MessageCall.Enter
import Jaune.MessageCall.Resume

/-!
# The four-part message call: the driver (goal `jaune-shape-and-names-v1`, W1 unit F)

`execFueled` runs a frame's machine step by step. A step that spawns a child enters it
(`enter`), runs it if it has code to run, settles its raw result (`settle`), and resumes the
caller with the settled result (`resume`). Staged under `Jaune.Staging` beside today's
`execFueled`; nothing in today's interpreter reads it until the switch commit.

This is the W1 form: the driver keeps today's type and returns the frame's raw result, so it
consumes fuel exactly as today does. A fault still carries a `Devm` in W1; the driver puts the
child's checkpoint there, and nothing reads it.

The total `exec` over this driver is in `Jaune.MessageCall.Exec`, a separate module, so that the
cached twin of this driver can be imported before `exec` is compiled.
-/

namespace Jaune

/-- The fuel-bounded driver over the staged `Step`. Each step consumes one unit of fuel; a
child's run and its caller's continuation each get the fuel that remains. -/
def execFueled : Evm → Nat → Fueled (EvmError × Devm) Devm
  | _, 0 => Fueled.exhausted
  | evm, fuel + 1 =>
    match Evm.step evm with
    | .halt ex => Fueled.ofExcept ex
    | .next pc devm => execFueled ⟨pc, evm.sta, devm⟩ fuel
    | .spawn child pending pc =>
      let settled : Option (Except Fault Frame.Result) :=
        match enter child with
        | .done result => some result
        | .run childEvm => ((execFueled childEvm fuel).run).map (settle child)
      match settled with
      | none => Fueled.exhausted
      | some (.error fault) => Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
      | some (.ok result) =>
        match resume evm.sta.benvStat.rules pending child.checkpoint result with
        | .error fault =>
          Fueled.ofExcept (.error (fault.toEvmError, child.checkpoint.toDevm))
        | .ok (.error (reason, devm)) => Fueled.ofExcept (.error (.halt reason, devm))
        | .ok (.ok devm) => execFueled ⟨pc, evm.sta, devm⟩ fuel

end Jaune

