import Jaune.Exec
import Jaune.MessageCall.Step

/-!
Symbolic PUSH rules with explicit gas and stack-capacity premises.
The state, operand bytes, fork and program counter remain variable.
-/

namespace Jaune.SymbolicPush

def cost (bytes : Bytes) : Nat := if bytes = [] then Gas.base else Gas.veryLow

def afterCharge (bytes : Bytes) (pre : Devm) : Devm :=
  pre.setMach { pre.mach with gasLeft := pre.gasLeft - cost bytes }

def post (bytes : Bytes) (pre : Devm) : Devm :=
  pre.setMach { pre.mach with
    stack := bytes.toU256 :: pre.stack
    gasLeft := pre.gasLeft - cost bytes }

/-- S8 (EIP-3855) availability: `PUSH0` needs its fork. Every PUSH rule below
carries it, so a gated-off byte never reaches these equations. -/
private theorem pushGate_false (evm : Evm) (bytes : Bytes)
    (hgate : bytes ≠ [] ∨ evm.sta.benvStat.rules.opcodes.push0) :
    (decide (bytes = []) && !evm.sta.benvStat.rules.opcodes.push0) = false := by
  rcases hgate with hne | hon
  · simp [hne]
  · simp [hon]

/-! ## On the four-part message call's `NextOp.step` -/

private theorem nextOp_step_push {evm : Evm} {xs : Bytes} {le : xs.length ≤ 32} :
    NextOp.step evm (.push xs le) =
      if xs = [] && !evm.sta.benvStat.rules.opcodes.push0 then
        Step.ofExecution (evm.pc + xs.length + 1)
          (.error ⟨.halt (.invalidOpcode .none), evm.dyna⟩)
      else
        Step.ofExecution (evm.pc + xs.length + 1) (do
          let devm ← chargeGas (if xs = [] then Gas.base else Gas.veryLow) evm.dyna
          devm.push xs.toU256) := rfl

/-- Success charges the selected PUSH cost and prepends the operand word. -/
theorem nextOp_step_success (evm : Evm) (bytes : Bytes) (width : bytes.length ≤ 32)
    (gas : cost bytes ≤ evm.dyna.gasLeft)
    (room : evm.dyna.stack.length < 1024)
    (hgate : bytes ≠ [] ∨ evm.sta.benvStat.rules.opcodes.push0) :
    NextOp.step evm (.push bytes width) =
      .next (evm.pc + bytes.length + 1) (post bytes evm.dyna) := by
  dsimp [cost] at gas
  dsimp [Devm.stack] at room
  rw [nextOp_step_push, pushGate_false evm bytes hgate]
  simp [chargeGas_def, safeSub, gas, Devm.push_def, Except.assert,
    Devm.stack, Devm.setMach, room, post, cost, bind, Except.bind, Step.ofExecution]

/-- Gas exhaustion is checked before stack capacity and leaves the input state. -/
theorem nextOp_step_outOfGas (evm : Evm) (bytes : Bytes) (width : bytes.length ≤ 32)
    (gas : evm.dyna.gasLeft < cost bytes)
    (hgate : bytes ≠ [] ∨ evm.sta.benvStat.rules.opcodes.push0) :
    NextOp.step evm (.push bytes width) =
      .halt (.error ⟨.halt (.outOfGas .none), evm.dyna⟩) := by
  dsimp [cost] at gas
  rw [nextOp_step_push, pushGate_false evm bytes hgate]
  simp [chargeGas_def, safeSub, Nat.not_le_of_lt gas,
    bind, Except.bind, Step.ofExecution]

/-- With gas available, stack overflow retains the gas charge in the raw error. -/
theorem nextOp_step_stackOverflow (evm : Evm) (bytes : Bytes) (width : bytes.length ≤ 32)
    (gas : cost bytes ≤ evm.dyna.gasLeft)
    (full : 1024 ≤ evm.dyna.stack.length)
    (hgate : bytes ≠ [] ∨ evm.sta.benvStat.rules.opcodes.push0) :
    NextOp.step evm (.push bytes width) =
      .halt (.error ⟨.halt (.stackOverflow .none), afterCharge bytes evm.dyna⟩) := by
  dsimp [cost] at gas
  dsimp [Devm.stack] at full
  rw [nextOp_step_push, pushGate_false evm bytes hgate]
  simp [chargeGas_def, safeSub, gas, Devm.push_def, Except.assert,
    Devm.stack, Devm.setMach, afterCharge, cost, bind, Except.bind,
    Step.ofExecution, Nat.not_lt_of_ge full]

/-- `prepend` on the four-part message call: prepend a decoded PUSH to a complete continuation,
preserving its outcome. -/
def prependExec {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (bytes : Bytes) (width : bytes.length ≤ 32)
    (decoded : NextOp.At sevm.code pc (.push bytes width))
    (gas : cost bytes ≤ pre.gasLeft) (room : pre.stack.length < 1024)
    (hgate : bytes ≠ [] ∨ sevm.benvStat.rules.opcodes.push0)
    (next : Exec (pc + bytes.length + 1) sevm (post bytes pre) out) :
    Exec pc sevm pre out :=
  .cont ((Evm.step_of_next decoded).trans
    (nextOp_step_success ⟨pc, sevm, pre⟩ bytes width gas room hgate)) next

end Jaune.SymbolicPush
