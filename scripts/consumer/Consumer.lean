import Jaune.SymbolicPush

/- A disposable external consumer: build a complete raw failure derivation and
connect it to the interpreter. No Blanc package or example imports are used. -/
namespace Consumer
open Jaune

def outOfGas {pc : Nat} {env : Sevm} {pre : Devm}
    (bytes : Bytes) (width : bytes.length ≤ 32)
    (decoded : Jaune.Ninst.At env.code pc (.push bytes width))
    (gas : pre.gasLeft < SymbolicPush.cost bytes) :
    Jaune.Exec pc env pre (.error ⟨.halt (.outOfGas .none), pre⟩) :=
  .halt ((Jaune.Evm.step_next decoded).trans
    (SymbolicPush.step_outOfGas ⟨pc, env, pre⟩ bytes width gas))

theorem interpreter_outOfGas {pc : Nat} {env : Sevm} {pre : Devm}
    (bytes : Bytes) (width : bytes.length ≤ 32)
    (decoded : Jaune.Ninst.At env.code pc (.push bytes width))
    (gas : pre.gasLeft < SymbolicPush.cost bytes) :
    exec ⟨pc, env, pre⟩ = .error ⟨.halt (.outOfGas .none), pre⟩ :=
  (Jaune.exec_iff_exec_eq _ _ _ _).mp ⟨outOfGas bytes width decoded gas⟩

end Consumer
