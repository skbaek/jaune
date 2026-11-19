import Jaune.Bridge.G2b.CheckedRowAgreement
import Jaune.Bridge.G2b.CheckedStoreAgreement

/-!
# Bridge: the family dispatch against the per-opcode arms (G2b, W4 step H; goal S4, X1)

Anchors: `Jaune.Checked.PlainOp.runCore` (and `PlainOp.run`) and `Jaune.Checked.NextOp.step`.
Old side: the per-opcode arms at `9ce48608`, moved unchanged to `Jaune.Checked.Arms`
(`Jaune.Bridge.G2b.CheckedPlainArms`). New side: `PlainOp.runCore pc ctx s op =
(PlainOp.family op).run ⟨pc, ctx, s⟩`, and `NextOp.step`'s push, `DUPN`, `SWAPN` and `EXCHANGE`
arms through their rows.

Inputs: every program counter, call context (so every block context, hence every `Fork` and every
rule set) and frame state, every plain instruction and every non-message operation, with every
immediate. Observation: the whole result, as a plain `Eq` on `Except (ExceptionalHalt ×
Frame.State) Frame.State` (`Step` for `NextOp.step`): the halt reason and the partial state on
the error channel, the state on the success channel. The block transition reaches these anchors
by name through unchanged code, so it follows by congruence.

The proof reads each instruction's family off the table and applies that family's agreement lemma
(`Jaune.Bridge.G2b.CheckedRowAgreement`, `Jaune.Bridge.G2b.CheckedStoreAgreement`); no opcode is
walked here.
-/

namespace Jaune.Checked

open Jaune

private theorem family_store_persistent {op : Jaune.PlainOp}
    (h : PlainOp.family op = .store .persistent) : op = .sstore := by
  cases op <;> first | rfl | simp [PlainOp.family] at h

private theorem family_store_transient {op : Jaune.PlainOp}
    (h : PlainOp.family op = .store .transient) : op = .tstore := by
  cases op <;> first | rfl | simp [PlainOp.family] at h

/-- **Bridge (the plain instructions):** the family dispatch equals the per-opcode arms, for
every program counter, call context and frame state (hence every `Fork`), on both channels. -/
theorem PlainOp.runCore_arms (pc : Nat) (ctx : Jaune.CallContext) (s : Frame.State)
    (op : Jaune.PlainOp) : PlainOp.runCore pc ctx s op = Arms.PlainOp.runCore pc ctx s op := by
  cases h : PlainOp.family op with
  | word row =>
    rw [← Arms.PlainOp.wordRow?_runCore_eq (PlainOp.wordRow?_eq_some.2 h) pc ctx s]
    simp only [PlainOp.runCore, h, Family.run]
  | shuffle row =>
    rw [← Arms.PlainOp.shuffleRow?_runCore_eq (PlainOp.shuffleRow?_eq_some.2 h) pc ctx s]
    simp only [PlainOp.runCore, h, Family.run]
  | memory row =>
    rw [← Arms.PlainOp.memoryRow?_runCore_eq (PlainOp.memoryRow?_eq_some.2 h) pc ctx s]
    simp only [PlainOp.runCore, h, Family.run]
  | log row =>
    rw [← Arms.PlainOp.logRow?_runCore_eq (PlainOp.logRow?_eq_some.2 h) pc ctx s]
    simp only [PlainOp.runCore, h, Family.run]
  | read row =>
    rw [← Arms.PlainOp.readRow?_runCore_eq (PlainOp.readRow?_eq_some.2 h) pc ctx s]
    simp only [PlainOp.runCore, h, Family.run]
  | store kind =>
    cases kind with
    | persistent =>
      obtain rfl := family_store_persistent h
      rw [← Arms.SstoreRow.ofRules_lift_eq pc ctx s]
      rfl
    | transient =>
      obtain rfl := family_store_transient h
      rw [← Arms.TstoreRow.ofRules_lift_eq pc ctx s]
      rfl

/-- **Bridge (the plain instructions, on a running frame).** -/
theorem PlainOp.run_arms (x : Frame.Running) (op : Jaune.PlainOp) :
    PlainOp.run x op = Arms.PlainOp.run x op :=
  PlainOp.runCore_arms x.pc x.context x.state op

/-- **Bridge (the non-message operations, and the step as a whole):** `NextOp.step`, whose push,
`DUPN`, `SWAPN` and `EXCHANGE` arms run their rows and whose plain arm runs the family dispatch,
equals the per-opcode `NextOp.step`, for every running frame (hence every `Fork`) and every
operation. The message arm is the same definition on both sides. -/
theorem NextOp.step_arms (r : Frame.Running) (n : Jaune.NextOp) :
    NextOp.step r n = Arms.NextOp.step r n := by
  cases n with
  | plain op =>
    show Step.ofHalt _ (PlainOp.run r op) = Step.ofHalt _ (Arms.PlainOp.run r op)
    rw [PlainOp.run_arms]
  | message x => rfl
  | push xs h => exact Arms.NextOp.pushRow_step_eq xs h r
  | dupn imm => exact Arms.NextOp.shuffleRow?_step_eq (n := .dupn imm) rfl r
  | swapn imm => exact Arms.NextOp.shuffleRow?_step_eq (n := .swapn imm) rfl r
  | exchange imm => exact Arms.NextOp.shuffleRow?_step_eq (n := .exchange imm) rfl r

end Jaune.Checked
