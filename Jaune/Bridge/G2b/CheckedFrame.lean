import Jaune.MessageCall.CheckedFrame
import Jaune.MessageCall.State
import Jaune.Bridge.Memory

/-! Exact grouping of legacy memory in a running machine and in its saved checkpoint. -/

namespace Jaune.Checked

/-- The discarded transaction fields used when reconstructing the waiting side of a comparison.
The same template applies to every frame of one transaction. -/
class LegacyTransaction where
  template : TenvStat

instance (priority := low) : LegacyTransaction := ⟨default⟩

abbrev CallContext.inLegacy (ctx : CallContext) [LegacyTransaction] : Jaune.CallContext :=
  ctx.toLegacy LegacyTransaction.template

section
variable [LegacyTransaction] (ctx : CallContext)

@[simp] theorem CallContext.inLegacy_caller : ctx.inLegacy.caller = ctx.caller := rfl
@[simp] theorem CallContext.inLegacy_recipient : ctx.inLegacy.recipient = ctx.recipient := rfl
@[simp] theorem CallContext.inLegacy_value : ctx.inLegacy.value = ctx.value := rfl
@[simp] theorem CallContext.inLegacy_calldata : ctx.inLegacy.calldata = ctx.calldata := rfl
@[simp] theorem CallContext.inLegacy_code : ctx.inLegacy.code = ctx.code := rfl
@[simp] theorem CallContext.inLegacy_depthLeft : ctx.inLegacy.depthLeft = ctx.depthLeft := rfl
@[simp] theorem CallContext.inLegacy_isStatic : ctx.inLegacy.isStatic = ctx.isStatic := rfl
@[simp] theorem CallContext.inLegacy_rules : ctx.inLegacy.block.rules = ctx.block.rules := rfl

end


def Machine.toLegacy (m : Machine) : Jaune.Machine :=
  ⟨m.stack, m.memory.toMem, m.gasLeft, m.stateGas, m.returnData⟩

def Machine.ofLegacy (m : Jaune.Machine) (h : m.memory.Wf) : Machine :=
  ⟨m.stack, Memory.ofMem m.memory h, m.gasLeft, m.stateGas, m.returnData⟩

def Frame.State.toLegacy (s : Frame.State) : Jaune.Frame.State :=
  ⟨s.machine.toLegacy, s.world, s.substate, s.trail⟩

def Frame.State.ofLegacy (s : Jaune.Frame.State) (h : s.machine.memory.Wf) : Frame.State :=
  ⟨Machine.ofLegacy s.machine h, s.world, s.substate, s.trail⟩

def Frame.toLegacy (f : Frame) [LegacyTransaction] : Jaune.Frame :=
  ⟨f.message.toLegacy LegacyTransaction.template, f.checkpoint.toLegacy⟩

def Frame.ofLegacy (f : Jaune.Frame) (h : f.checkpoint.machine.memory.Wf) : Frame :=
  ⟨Message.ofLegacy f.message, Frame.State.ofLegacy f.checkpoint h⟩

def Frame.Running.toLegacy (r : Frame.Running) [LegacyTransaction] : Jaune.Frame.Running :=
  ⟨r.pc, r.context.inLegacy, r.state.toLegacy⟩

def Frame.Running.ofLegacy (r : Jaune.Frame.Running) (h : r.state.machine.memory.Wf) :
    Frame.Running := ⟨r.pc, r.context.toChecked, Frame.State.ofLegacy r.state h⟩

def Frame.Exit.toLegacy : Frame.Exit → Jaune.Frame.Exit
  | .finished output s => .finished output s.toLegacy
  | .reverted output s => .reverted output s.toLegacy
  | .halted reason s => .halted reason s.toLegacy

def Frame.Exit.ofLegacy (e : Jaune.Frame.Exit) (h : e.state.machine.memory.Wf) : Frame.Exit :=
  match e with
  | .finished output s => .finished output (Frame.State.ofLegacy s h)
  | .reverted output s => .reverted output (Frame.State.ofLegacy s h)
  | .halted reason s => .halted reason (Frame.State.ofLegacy s h)

@[simp] theorem Machine.toLegacy_ofLegacy (m : Jaune.Machine) (h : m.memory.Wf) :
    (Machine.ofLegacy m h).toLegacy = m := rfl

@[simp] theorem Machine.ofLegacy_toLegacy (m : Machine) :
    Machine.ofLegacy m.toLegacy m.memory.wf_toMem = m := rfl

@[simp] theorem Frame.State.toLegacy_ofLegacy (s : Jaune.Frame.State) (h : s.machine.memory.Wf) :
    (Frame.State.ofLegacy s h).toLegacy = s := rfl

@[simp] theorem Frame.State.ofLegacy_toLegacy (s : Frame.State) :
    Frame.State.ofLegacy s.toLegacy s.machine.memory.wf_toMem = s := rfl

@[simp] theorem CallContext.toLegacy_toChecked (c : Jaune.CallContext) :
    c.toChecked.toLegacy c.tx = c := by
  cases c
  rfl

@[simp] theorem CallContext.toChecked_toLegacy (c : CallContext) (template : TenvStat) :
    (c.toLegacy template).toChecked = c := by
  cases c
  rfl

@[simp] theorem Message.toLegacy_ofLegacy (m : Jaune.Message) :
    (Message.ofLegacy m).toLegacy m.context.tx = m := by
  cases m
  simp only [Message.ofLegacy, Message.toLegacy, CallContext.toLegacy_toChecked]

@[simp] theorem Message.ofLegacy_toLegacy (m : Message) (template : TenvStat) :
    Message.ofLegacy (m.toLegacy template) = m := by
  cases m
  simp only [Message.ofLegacy, Message.toLegacy, CallContext.toChecked_toLegacy]

@[simp] theorem Frame.toLegacy_ofLegacy (f : Jaune.Frame) (h : f.checkpoint.machine.memory.Wf) :
    @Frame.toLegacy (Frame.ofLegacy f h) ⟨f.message.context.tx⟩ = f := by
  cases f
  simp only [Frame.ofLegacy, Frame.toLegacy, LegacyTransaction.template, Message.toLegacy_ofLegacy, Frame.State.toLegacy_ofLegacy]

@[simp] theorem Frame.ofLegacy_toLegacy (f : Frame) [LegacyTransaction] :
    Frame.ofLegacy f.toLegacy f.checkpoint.machine.memory.wf_toMem = f := by
  cases f
  simp only [Frame.ofLegacy, Frame.toLegacy, Message.ofLegacy_toLegacy, Frame.State.ofLegacy_toLegacy]

@[simp] theorem Frame.Running.toLegacy_ofLegacy (r : Jaune.Frame.Running) (h : r.state.machine.memory.Wf) :
    @Frame.Running.toLegacy (Frame.Running.ofLegacy r h) ⟨r.context.tx⟩ = r := by
  cases r
  simp only [Frame.Running.ofLegacy, Frame.Running.toLegacy, CallContext.inLegacy, CallContext.toLegacy_toChecked,
    Frame.State.toLegacy_ofLegacy, LegacyTransaction.template]

@[simp] theorem Frame.Running.ofLegacy_toLegacy (r : Frame.Running) [LegacyTransaction] :
    Frame.Running.ofLegacy r.toLegacy r.state.machine.memory.wf_toMem = r := by
  cases r
  simp only [Frame.Running.ofLegacy, Frame.Running.toLegacy, CallContext.toChecked_toLegacy,
    Frame.State.ofLegacy_toLegacy]

@[simp] theorem Frame.Exit.toLegacy_ofLegacy (e : Jaune.Frame.Exit) (h : e.state.machine.memory.Wf) :
    (Frame.Exit.ofLegacy e h).toLegacy = e := by cases e <;> rfl

theorem Frame.Exit.wf_toLegacy (e : Frame.Exit) : e.toLegacy.state.machine.memory.Wf := by
  cases e with
  | finished _ s | reverted _ s | halted _ s => exact s.machine.memory.wf_toMem

@[simp] theorem Frame.Exit.ofLegacy_toLegacy (e : Frame.Exit) :
    Frame.Exit.ofLegacy e.toLegacy e.wf_toLegacy = e := by cases e <;> rfl

end Jaune.Checked
