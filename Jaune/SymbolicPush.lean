import Jaune.Exec

/-!
Symbolic PUSH rules with explicit gas and stack-capacity premises.
The state, operand bytes, fork and program counter remain variable.
-/

namespace Jaune.SymbolicPush

def cost (bytes : Bytes) : Nat := if bytes = [] then gBase else gVerylow

def afterCharge (bytes : Bytes) (pre : Devm) : Devm :=
  pre.setMach { pre.mach with gasLeft := pre.gasLeft - cost bytes }

def post (bytes : Bytes) (pre : Devm) : Devm :=
  pre.setMach { pre.mach with
    stack := bytes.toB256 :: pre.stack
    gasLeft := pre.gasLeft - cost bytes }

/-- Success charges the selected PUSH cost and prepends the operand word. -/
theorem step_success (evm : Evm) (bytes : Bytes) (width : bytes.length ≤ 32)
    (gas : cost bytes ≤ evm.dyna.gasLeft)
    (room : evm.dyna.stack.length < 1024) :
    Ninst.step evm (.push bytes width) =
      .cont (evm.pc + bytes.length + 1) (post bytes evm.dyna) := by
  dsimp [cost] at gas
  dsimp [Devm.stack] at room
  rw [Ninst.step_push]
  simp [chargeGas_def, safeSub, gas, Devm.push_def, Except.assert,
    Devm.stack, Devm.setMach, room, post, cost, bind, Except.bind, Step.ofExecution]

/-- Gas exhaustion is checked before stack capacity and leaves the input state. -/
theorem step_outOfGas (evm : Evm) (bytes : Bytes) (width : bytes.length ≤ 32)
    (gas : evm.dyna.gasLeft < cost bytes) :
    Ninst.step evm (.push bytes width) =
      .halt (.error ⟨.halt (.outOfGas .none), evm.dyna⟩) := by
  dsimp [cost] at gas
  rw [Ninst.step_push]
  simp [chargeGas_def, safeSub, Nat.not_le_of_lt gas,
    bind, Except.bind, Step.ofExecution]

/-- With gas available, stack overflow retains the gas charge in the raw error. -/
theorem step_stackOverflow (evm : Evm) (bytes : Bytes) (width : bytes.length ≤ 32)
    (gas : cost bytes ≤ evm.dyna.gasLeft)
    (full : 1024 ≤ evm.dyna.stack.length) :
    Ninst.step evm (.push bytes width) =
      .halt (.error ⟨.halt (.stackOverflow .none), afterCharge bytes evm.dyna⟩) := by
  dsimp [cost] at gas
  dsimp [Devm.stack] at full
  rw [Ninst.step_push]
  simp [chargeGas_def, safeSub, gas, Devm.push_def, Except.assert,
    Devm.stack, Devm.setMach, afterCharge, cost, bind, Except.bind,
    Step.ofExecution, Nat.not_lt_of_ge full]

/-- Prepend a decoded PUSH to a complete continuation, preserving its outcome. -/
def prepend {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (bytes : Bytes) (width : bytes.length ≤ 32)
    (decoded : Ninst.At sevm.code pc (.push bytes width))
    (gas : cost bytes ≤ pre.gasLeft) (room : pre.stack.length < 1024)
    (next : Exec (pc + bytes.length + 1) sevm (post bytes pre) out) :
    Exec pc sevm pre out :=
  .cont ((Evm.step_next decoded).trans
    (step_success ⟨pc, sevm, pre⟩ bytes width gas room)) next

end Jaune.SymbolicPush
