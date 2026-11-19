import Jaune.Instructions.Table

/-! Plain EVM instructions over checked frame memory, read from the instruction table (goal
`jaune-shape-and-names-v1`, S4).

Each family has one step, and every plain instruction runs its family's step on its row
(`PlainOp.family`). There is no plain instruction outside the families: the classes S4 excludes
(jumps, halts and the frame-opening message operations) are not `PlainOp`s, and keep explicit
equations in `Jaune.MessageCall.CheckedControl` and `Jaune.MessageCall.CheckedMessageOps`. -/

namespace Jaune.Checked

open Jaune

/-- One step of a family on a running frame (W4 design note §3.7). The lifts fix what each family
can change outside the machine: `liftMachine` nothing, `liftLog` one appended log, `liftRead` one
warmed key and one recorded read, `liftStore` at most one slot of the recipient plus its warming,
its refund and its reads. -/
def Family.run (f : Family) (x : Frame.Running) :
    Except (ExceptionalHalt × Frame.State) Frame.State :=
  match f with
  | .word row => x.state.liftMachine (row.step x.context.block.rules.opcodes ⟨x.pc, x.context⟩)
  | .shuffle row => x.state.liftMachine (row.step x.context.block.rules.opcodes)
  | .memory row => x.state.liftMachine (row.step x.context.block.rules.opcodes x.context)
  | .log row => x.state.liftLog (row.step x.context x.state.machine)
  | .read row =>
    x.state.liftRead x.context.block.rules (row.step x.context.block.rules x.context x.state.readView)
  | .store .persistent =>
    x.state.liftStore x.context.block.rules x.context.recipient
      ((SstoreRow.ofRules x.context.block.rules).step x.context.isStatic
        (fun k => x.state.slotView x.context k))
  | .store .transient =>
    x.state.liftStore x.context.block.rules x.context.recipient
      ((TstoreRow.ofRules x.context.block.rules).step x.context.block.rules.opcodes
        x.context.isStatic)

namespace PlainOp

/-- The plain instructions over the lifetime-grouped state: each runs its family's step on its
row. `pc` is the program counter (`PC` reads it), `ctx` what the frame reads of its message, `s`
its state. -/
def runCore (pc : Nat) (ctx : CallContext) (s : Frame.State) (op : Jaune.PlainOp) :
    Except (ExceptionalHalt × Frame.State) Frame.State :=
  (PlainOp.family op).run ⟨pc, ctx, s⟩

/-- A running frame's plain instruction (the form W4 states its table over). -/
def run (x : Frame.Running) (op : Jaune.PlainOp) :
    Except (ExceptionalHalt × Frame.State) Frame.State :=
  runCore x.pc x.context x.state op

end PlainOp
end Jaune.Checked
