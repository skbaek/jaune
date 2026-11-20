import Jaune.MessageCall.State
import Jaune.Precompiles
import Jaune.MessageCall.Records

/-!
# Jumps, halts and precompile results over `Frame.State` (goal `jaune-shape-and-names-v1`, W3-2b+d)

The instructions that move the program counter or end a frame, and the result of a precompile,
written over the running frame (`Frame.Running`) and its lifetime-grouped state:

* `Staging.JumpOp.runCore` is `JUMPDEST`, `JUMP` and `JUMPI`, returning the next program counter
  with the state; `Staging.JumpOp.run` puts them back into a running frame.
* `Staging.HaltOp.run` is `STOP`, `RETURN`, `REVERT` and `SELFDESTRUCT`. It returns how the
  frame stopped (`Frame.Exit`) instead of writing an output and an error into the state; a
  fault (`SELFDESTRUCT`'s broken balance invariant) leaves on the fault channel.
* `runPrecompile` runs a precompile on a running frame and returns its `Frame.Exit`; a fault
  (a pairing check that cannot convert, an unmapped address) leaves on the fault channel.
* `Frame.Running.getOp` decodes the operation at the program counter, the part of `step` the
  jump and halt arms need.

The machine operations raise only exceptional halts (`ExceptionalHalt`). A computation that ends
the frame runs in that halt-only monad and returns its exit or fault; `Frame.Exit.catchHalt`
turns a halt on the way into a `.halted` exit.

This module is staged beside the `Devm` interpreter: nothing in the interpreter uses it yet. The
squares against `JumpOp.runCore`, `HaltOp.run`, `applyPrecompileResult`, `executePrecompile`
and `Evm.step`'s jump and halt arms are in `Jaune.Bridge.G2b.Control`.
-/

namespace Jaune

/-! ### Vocabulary -/

/-- Finish a computation that ends the frame: an exceptional halt on the way is a `.halted`
exit with the state it halted in; otherwise the computation's own exit, or its fault. -/
def Frame.Exit.catchHalt :
    Except (ExceptionalHalt × Frame.State) (Except Fault Frame.Exit) → Except Fault Frame.Exit
  | .error (reason, s) => .ok (.halted reason s)
  | .ok result => result

/-- The operation at the program counter, if the code has one there. -/
def Frame.Running.getOp (r : Frame.Running) : Option Op :=
  Jaune.ByteArray.getOp r.context.code r.pc

namespace Frame.State

/-- Schedule an account for deletion at the end of the transaction. -/
abbrev addSelfDestruct (s : Frame.State) (a : Address) : Frame.State :=
  s.withSelfDestructs (s.selfDestructs.insert a)

/-- The `SELFDESTRUCT` refund hook (`REFUND_SELF_DESTRUCT`): 24000 before EIP-3529 (London),
0 after, credited when this `SELFDESTRUCT` newly schedules the donor. -/
abbrev creditSelfdestructRefund (rules : ForkRules) (alreadyScheduled : Prop)
    [Decidable alreadyScheduled] (s : Frame.State) : Frame.State :=
  if alreadyScheduled then s else s.withRefund (s.refund + rules.settlement.selfdestructRefund)

end Frame.State

/-- `SELFDESTRUCT`'s fault: the donor's balance could not be debited by itself. -/
def insufficientBalanceFault : Fault :=
  .internal (.invariant (.text "InsufficientBalanceError"))

namespace Staging

/-! ### Jumps -/

/-- `JUMPDEST`, `JUMP` and `JUMPI` at `pc`: the next program counter and the state. -/
def JumpOp.runCore (pc : Nat) (ctx : CallContext) (s : Frame.State) :
    JumpOp → Except (ExceptionalHalt × Frame.State) (Nat × Frame.State)
  | .jumpdest => do
    let s ← s.chargeGas Gas.jumpdest
    .ok (pc + 1, s)
  | .jump => do
    let (dest, s) ← s.pop
    let s ← s.chargeGas Gas.mid
    Except.assert (jumpable ctx.code dest.toNat) (.invalidJumpDest .none, s)
    .ok (dest.toNat, s)
  | .jumpi => do
    let (dest, s) ← s.pop
    let (cond, s) ← s.pop
    let s ← s.chargeGas Gas.high
    let pc' : Nat ←
      if cond = 0 then .ok (pc + 1)
      else do
        Except.assert (jumpable ctx.code dest.toNat) (.invalidJumpDest .none, s)
        .ok dest.toNat
    .ok (pc', s)

/-- A jump on a running frame: the frame goes on at the new program counter. -/
def JumpOp.run (r : Frame.Running) (j : JumpOp) :
    Except (ExceptionalHalt × Frame.State) Frame.Running :=
  match JumpOp.runCore r.pc r.context r.state j with
  | .error e => .error e
  | .ok (pc, s) => .ok ⟨pc, r.context, s⟩

/-! ### Halts -/

/-- `STOP`, `RETURN`, `REVERT` and `SELFDESTRUCT`: how the frame stops.

`SELFDESTRUCT` follows `vm/instructions/system.py`. The two shapes differ in more than numbers,
so it is a `match` on the state-gas switch: Amsterdam moves the static check ahead of the pop,
checks the access cost before warming the beneficiary, replaces the 25,000 new-account charge by
`ACCOUNT_WRITE` (execution) plus `NEW_ACCOUNT` (state) when the sweep creates the beneficiary,
logs the sweep, and schedules the originator without zeroing it. -/
def HaltOp.run (ctx : CallContext) (s : Frame.State) : HaltOp → Except Fault Frame.Exit
  | .stop => .ok (.finished [] s)
  | .revert => Frame.Exit.catchHalt do
    let (start, s) ← s.popToNat
    let (size, s) ← s.popToNat
    let s ← s.chargeGas (s.extCost [(start, size)])
    let (output, s) := s.memRead start size
    return .ok (.reverted output s)
  | .return_ => Frame.Exit.catchHalt do
    let (start, s) ← s.popToNat
    let (size, s) ← s.popToNat
    let s ← s.chargeGas (s.extCost [(start, size)])
    let (output, s) := s.memRead start size
    return .ok (.finished output s)
  | .selfdestruct =>
    let rules := ctx.block.rules
    match rules.stateGas with
    | none => Frame.Exit.catchHalt do
      let donor := ctx.recipient
      let (donee, s) ← s.popToAddress
      -- `is_account_alive(beneficiary)` and `get_account(originator)` (EIP-7928).
      let s := (s.recordAccountRead rules donee).recordAccountRead rules donor
      let donorBalance := s.balance donor
      let (s, cost) : Frame.State × Nat :=
        match rules.access with
        | .eip2929 =>
          if donee ∉ s.accessedAddresses then
            (s.addAccessedAddress donee, Gas.selfdestruct + rules.gas.coldAccountAccess)
          else (s, Gas.selfdestruct)
        | .flat _ => (s, Gas.selfdestruct)
      let cost :=
        if (s.account donee).isEmpty ∧ donorBalance ≠ 0 then cost + Gas.selfdestructNewAccount
        else cost
      let s ← s.chargeGas cost
      s.assertDynamic ctx
      match s.subtractBalance donor donorBalance with
      | none => return .error insufficientBalanceFault
      | some s =>
        let s := s.creditBeneficiary rules donee donorBalance
        -- EIP-6780 (Cancun): only an account created in this transaction is scheduled;
        -- before that every `SELFDESTRUCT` schedules, and the refund hook applies.
        if donor ∈ s.createdAccounts ∨ rules.settlement.selfdestructOnlyCreated = false then
          return .ok (.finished []
            (((s.setBalance donor 0).addSelfDestruct donor).creditSelfdestructRefund rules
              (donor ∈ s.selfDestructs)))
        else return .ok (.finished [] s)
    | some state => Frame.Exit.catchHalt do
      s.assertDynamic ctx
      let donor := ctx.recipient
      let (donee, s) ← s.popToAddress
      -- GAS (state-independent), checked before the beneficiary is warmed.
      let cold := donee ∉ s.accessedAddresses
      let cost := Gas.selfdestruct + (if cold then rules.gas.coldAccountAccess else 0)
      Except.assert (cost ≤ s.gasLeft) (.outOfGas .none, s)
      -- STATE ACCESS: warm the beneficiary, then the two reads (EIP-7928).
      let s := if cold then s.addAccessedAddress donee else s
      let s := (s.recordAccountRead rules donee).recordAccountRead rules donor
      let donorBalance := s.balance donor
      -- STATE GAS: a sweep that creates the beneficiary pays the write and the creation.
      let creating := (s.account donee).isEmpty ∧ donorBalance ≠ 0
      let s ← s.chargeGas (cost + if creating then state.accountWrite else 0)
      let s ← s.chargeStateGas (if creating then state.newAccount else 0)
      -- OPERATION: move the whole balance, log it, schedule the deletion.
      match s.subtractBalance donor donorBalance with
      | none => return .error insufficientBalanceFault
      | some s =>
        let s := (s.addBalance donee donorBalance).emitTransferLog donor donee donorBalance
        if donor ∈ s.createdAccounts then return .ok (.finished [] (s.addSelfDestruct donor))
        else return .ok (.finished [] s)

end Staging

/-! ### Precompiles -/

/-- The machine today's precompile bodies (`precompileRun`) take, built from a running frame.
They read only its input (`sta.data`), its rules (`sta.benvStat`) and its gas left
(`dyna.gasLeft`); the fields that stay on the message are placeholders. -/
def Frame.Running.precompileEvm (r : Frame.Running) : Evm :=
  ⟨r.pc,
    { caller := r.context.caller, target := none, currentTarget := r.context.recipient, gas := 0
      value := r.context.value, data := r.context.calldata, codeAddress := none
      code := r.context.code, depth := r.context.depthLeft, shouldTransferValue := false
      isStatic := r.context.isStatic, disablePrecompiles := false, benvStat := r.context.block
      tenvStat := r.context.tx },
    r.state.toDevm⟩

/-- A precompile's result as an exit: the cost is charged on every channel, the output is the
frame's output, and a fault leaves on the fault channel. -/
def Frame.Exit.ofPrecompileResult (s : Frame.State) : PrecompileResult → Except Fault Frame.Exit
  | .ok cost output => .ok (.finished output (s.withGasLeft (s.gasLeft - cost)))
  | .error reason cost =>
    let s := s.withGasLeft (s.gasLeft - cost)
    match reason with
    | .halt h => .ok (.halted h s)
    | .revert => .ok (.reverted [] s)
    | .crypto r => .error (.crypto r)
    | .internal r => .error (.internal r)

/-- Run the precompile at `address` on a running frame. -/
def runPrecompile (r : Frame.Running) (address : Address) : Except Fault Frame.Exit :=
  Frame.Exit.ofPrecompileResult r.state (precompileRun r.precompileEvm address)

end Jaune
