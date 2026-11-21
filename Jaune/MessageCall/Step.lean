import Jaune.MessageCall.Plain
import Jaune.MessageCall.Control
import Jaune.MessageCall.MessageOps

/-! One instruction of a checked running frame. -/
namespace Jaune

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

/-- The operations that go on to the next instruction. A push and EIP-8024's `DUPN`, `SWAPN` and
`EXCHANGE` run their family's step on their row (`NextOp.family?`), a plain instruction its
table row (`PlainOp.run`). A message operation opens a frame, which S4 leaves out: it keeps its
explicit equations (`MessageOp.step`). -/
def NextOp.step (r : Frame.Running) (n : NextOp) : Step :=
  let pc := r.pc + n.size
  match n with
  | .push xs _ => Step.ofHalt pc ((Family.word (NextOp.pushRow xs)).run r)
  | .plain op => Step.ofHalt pc (PlainOp.run r op)
  | .message x => (MessageOp.step r.context r.state x).toStep pc
  | .dupn imm => Step.ofHalt pc ((Family.shuffle (NextOp.dupnRow imm)).run r)
  | .swapn imm => Step.ofHalt pc ((Family.shuffle (NextOp.swapnRow imm)).run r)
  | .exchange imm => Step.ofHalt pc ((Family.shuffle (NextOp.exchangeRow imm)).run r)

/-- One step of a running frame: decode the operation at the program counter and run it. An
undecodable byte is an invalid instruction; only a halt can fault. -/
def step (r : Frame.Running) : Except Fault Step :=
  match r.getOp with
  | none => .ok (.exit (.halted (.invalidOpcode .none) r.state))
  | some (.next n) => .ok (NextOp.step r n)
  | some (.jump j) => .ok (Step.ofJump (JumpOp.run r j))
  | some (.halt l) => (HaltOp.run r.context r.state l).map .exit
end Jaune
