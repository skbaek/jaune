import Jaune.MessageCall.CheckedFrame
import Jaune.MessageCall.State
import Jaune.Bridge.Memory

/-! Exact grouping of legacy memory in a running machine and in its saved checkpoint. -/

namespace Jaune.Checked

def Machine.toLegacy (m : Machine) : Jaune.Machine :=
  ⟨m.stack, m.memory.toMem, m.gasLeft, m.stateGas, m.returnData⟩

def Machine.ofLegacy (m : Jaune.Machine) (h : m.memory.Wf) : Machine :=
  ⟨m.stack, Memory.ofMem m.memory h, m.gasLeft, m.stateGas, m.returnData⟩

def Frame.State.toLegacy (s : Frame.State) : Jaune.Frame.State :=
  ⟨s.machine.toLegacy, s.world, s.substate, s.trail⟩

def Frame.State.ofLegacy (s : Jaune.Frame.State) (h : s.machine.memory.Wf) : Frame.State :=
  ⟨Machine.ofLegacy s.machine h, s.world, s.substate, s.trail⟩

def Frame.toLegacy (f : Frame) : Jaune.Frame := ⟨f.message, f.checkpoint.toLegacy⟩

def Frame.ofLegacy (f : Jaune.Frame) (h : f.checkpoint.machine.memory.Wf) : Frame :=
  ⟨f.message, Frame.State.ofLegacy f.checkpoint h⟩

def Frame.Running.toLegacy (r : Frame.Running) : Jaune.Frame.Running :=
  ⟨r.pc, r.context, r.state.toLegacy⟩

def Frame.Running.ofLegacy (r : Jaune.Frame.Running) (h : r.state.machine.memory.Wf) :
    Frame.Running := ⟨r.pc, r.context, Frame.State.ofLegacy r.state h⟩

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

@[simp] theorem Frame.toLegacy_ofLegacy (f : Jaune.Frame) (h : f.checkpoint.machine.memory.Wf) :
    (Frame.ofLegacy f h).toLegacy = f := rfl

@[simp] theorem Frame.ofLegacy_toLegacy (f : Frame) :
    Frame.ofLegacy f.toLegacy f.checkpoint.machine.memory.wf_toMem = f := rfl

@[simp] theorem Frame.Running.toLegacy_ofLegacy (r : Jaune.Frame.Running) (h : r.state.machine.memory.Wf) :
    (Frame.Running.ofLegacy r h).toLegacy = r := rfl

@[simp] theorem Frame.Running.ofLegacy_toLegacy (r : Frame.Running) :
    Frame.Running.ofLegacy r.toLegacy r.state.machine.memory.wf_toMem = r := rfl

@[simp] theorem Frame.Exit.toLegacy_ofLegacy (e : Jaune.Frame.Exit) (h : e.state.machine.memory.Wf) :
    (Frame.Exit.ofLegacy e h).toLegacy = e := by cases e <;> rfl

theorem Frame.Exit.wf_toLegacy (e : Frame.Exit) : e.toLegacy.state.machine.memory.Wf := by
  cases e with
  | finished _ s | reverted _ s | halted _ s => exact s.machine.memory.wf_toMem

@[simp] theorem Frame.Exit.ofLegacy_toLegacy (e : Frame.Exit) :
    Frame.Exit.ofLegacy e.toLegacy e.wf_toLegacy = e := by cases e <;> rfl

end Jaune.Checked
