import Jaune.MessageCall.CheckedState
import Jaune.PrecompileInput
import Jaune.MessageCall.Records

/-! Control and native precompile instructions on checked frame memory. -/
namespace Jaune.Checked

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

/-! ### Jumps -/

/-- `JUMPDEST`, `JUMP` and `JUMPI` at `pc`: the next program counter and the state.

Outside the instruction table (goal S4): a jump returns the next program counter, which a family
step, over the frame state alone, cannot (W4 design note §2.3), so the class keeps these explicit
equations. -/
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
logs the sweep, and schedules the originator without zeroing it.

Outside the instruction table (goal S4): a halt produces a `Frame.Exit`, and `SELFDESTRUCT` can end
in an internal fault, which a family's error type (`ExceptionalHalt × _`) cannot carry (W4 design
note §2.3), so the class keeps these explicit equations. -/
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


/-- What a precompile reads of a running frame: its input, its gas left and its block's fork. -/
def Frame.Running.precompileInput (r : Frame.Running) : PrecompileInput :=
  { calldata := r.context.calldata, gasLeft := r.state.gasLeft, fork := r.context.block.fork }

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
  Frame.Exit.ofPrecompileResult r.state (Precompile.run r.precompileInput address)


end Jaune.Checked
