import Jaune.MessageCall.Plain
import Jaune.MessageCall.Control
import Jaune.MessageCall.MessageOps

/-!
# One step of a running frame over `Frame.Running` (goal `jaune-shape-and-names-v1`, W3 unit W3-3)

The final form of `step` (W1/W3 design, revision 2 §2.5): one step of a running frame
(`Frame.Running`), decoded at its program counter and dispatched to the staged instruction bodies
of W3-2:

* plain instructions to `Staging.PlainOp.run`;
* jumps to `Staging.JumpOp.run`;
* halts to `Staging.HaltOp.run`, which returns how the frame stopped (`Frame.Exit`) or a fault;
* message operations to `Staging.MessageOp.step`, whose spawn hands the driver a child `Frame`
  and the final `Staging.Pending`;
* the pushes and the EIP-8024 stack operations (`DUPN`, `SWAPN`, `EXCHANGE`), written here.

A step either stops the frame (`Staging.Step.exit`), goes on at a program counter with a new
state (`Staging.Step.next`; the context does not change within a frame), or opens a child frame
and goes on at a program counter once the child is resumed (`Staging.Step.spawn`). Only a halt
can fault, so `Staging.step` returns `Except Fault Staging.Step`.

Every definition is staged under `Jaune.Staging` beside the `Devm` interpreter (`Evm.step`), which
nothing here replaces yet. The square against `Evm.step` is in `Jaune.Bridge.G2b.FinalStep`.
-/

namespace Jaune.Staging

open Jaune

/-- One step of a running frame. -/
inductive Step : Type
  /-- The frame stopped. -/
  | exit (e : Frame.Exit)
  /-- The frame goes on at `pc` with `state`; its context is unchanged. -/
  | next (pc : Nat) (state : Frame.State)
  /-- The frame opens a child, and goes on at `pc` when the child is resumed. The saved caller is
  the child's checkpoint. -/
  | spawn (child : Frame) (pending : Pending) (pc : Nat)

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

end Jaune.Staging
