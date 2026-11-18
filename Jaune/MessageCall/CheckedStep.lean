import Jaune.MessageCall.CheckedPlain
import Jaune.MessageCall.CheckedControl
import Jaune.MessageCall.CheckedMessageOps

/-! One instruction of a checked running frame. -/
namespace Jaune.Checked

open Jaune

/-- One step of a running frame. -/
inductive Step : Type
  /-- The frame stopped. -/
  | exit (e : Frame.Exit)
  /-- The frame goes on at `pc` with `state`; its context is unchanged. -/
  | next (pc : Nat) (state : Frame.State)
  /-- The frame opens a child, and goes on at `pc` when the child is resumed. The saved caller is
  the child's checkpoint. -/
  | spawn (child : Frame) (pending : Staging.Pending) (pc : Nat)

/-- A frame-local result as a step that goes on at `pc`: an exceptional halt stops the frame. -/
def Step.ofHalt (pc : Nat) : Except (ExceptionalHalt × Frame.State) Frame.State → Step
  | .error (reason, s) => .exit (.halted reason s)
  | .ok s => .next pc s

/-- A jump's result as a step. -/
def Step.ofJump : Except (ExceptionalHalt × Frame.State) Frame.Running → Step
  | .error (reason, s) => .exit (.halted reason s)
  | .ok r => .next r.pc r.state

/-- A message operation's result as a step that goes on at `pc`. -/
def MessageOp.Outcome.toStep (pc : Nat) : MessageOp.Outcome → Step
  | .done r => Step.ofHalt pc r
  | .spawn child pending => .spawn child pending pc

/-- The operations that go on to the next instruction. -/
def NextOp.step (r : Frame.Running) (n : NextOp) : Step :=
  let pc := r.pc + n.size
  let rules := r.context.block.rules
  match n with
  -- S8 (EIP-3855): `PUSH0` is the empty push; without the fork the byte is an undefined
  -- instruction whatever the stack and gas hold.
  | .push xs _ =>
    if xs = [] && !rules.opcodes.push0 then
      Step.ofHalt pc (.error (.invalidOpcode .none, r.state))
    else
      let cost := if xs = [] then Gas.base else Gas.veryLow
      Step.ofHalt pc do
        let s ← r.state.chargeGas cost
        s.push xs.toU256
  | .plain op => Step.ofHalt pc (PlainOp.run r op)
  | .message x => (MessageOp.step r.context r.state x).toStep pc
  -- EIP-8024: the availability check first, then the charge before the immediate is decoded,
  -- then the decode (a forbidden immediate is an invalid instruction), then the stack.
  | .dupn imm =>
    Step.ofHalt pc <| do
      if rules.opcodes.stackAccess then
        let s ← r.state.chargeGas Gas.veryLow
        match decodeSingle imm with
        | none => .error (.invalidOpcode .none, s)
        | some n =>
          match s.stack[n - 1]? with
          | none => .error (.stackUnderflow .none, s)
          | some word => s.push word
      else
        .error (.invalidOpcode .none, r.state)
  | .swapn imm =>
    Step.ofHalt pc <| do
      if rules.opcodes.stackAccess then
        let s ← r.state.chargeGas Gas.veryLow
        match decodeSingle imm with
        | none => .error (.invalidOpcode .none, s)
        | some n =>
          match List.swap s.stack (n - 1) with
          | none => .error (.stackUnderflow .none, s)
          | some stack => .ok (s.withStack stack)
      else
        .error (.invalidOpcode .none, r.state)
  | .exchange imm =>
    Step.ofHalt pc <| do
      if rules.opcodes.stackAccess then
        let s ← r.state.chargeGas Gas.veryLow
        match decodePair imm with
        | none => .error (.invalidOpcode .none, s)
        | some (n, m) =>
          match List.exchange s.stack n m with
          | none => .error (.stackUnderflow .none, s)
          | some stack => .ok (s.withStack stack)
      else
        .error (.invalidOpcode .none, r.state)

/-- One step of a running frame: decode the operation at the program counter and run it. An
undecodable byte is an invalid instruction; only a halt can fault. -/
def step (r : Frame.Running) : Except Fault Step :=
  match r.getOp with
  | none => .ok (.exit (.halted (.invalidOpcode .none) r.state))
  | some (.next n) => .ok (NextOp.step r n)
  | some (.jump j) => .ok (Step.ofJump (JumpOp.run r j))
  | some (.halt l) => (HaltOp.run r.context r.state l).map .exit
end Jaune.Checked
