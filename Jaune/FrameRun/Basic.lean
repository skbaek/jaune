import Jaune.MessageCall.FinalChronology

namespace Jaune.Staging

/-- A same-frame prefix stops at a running state. A whole run ends at its raw outcome. -/
inductive Frame.Run.End where
  | at (state : Frame.Running)
  | exit (outcome : Except Fault Frame.Exit)

/-- An ordered frame run. Entered children finish before the caller's continuation begins. -/
inductive Frame.Run : Frame.Running → Frame.Run.End → Type
  | stop (r : Frame.Running) : Frame.Run r (.at r)
  | halt {r out} : step r = out.map Step.exit → Frame.Run r (.exit out)
  | next {r pc state e} : step r = .ok (.next pc state) →
      Frame.Run ⟨pc, r.context, state⟩ e → Frame.Run r e
  | callDone {r child pending pc result state e} :
      step r = .ok (.spawn child pending pc) → enter child = .done result →
      resumeCaller r.context.block.rules child pending result = .ok state →
      Frame.Run ⟨pc, r.context, state⟩ e → Frame.Run r e
  | callRan {r child pending pc cr raw state e} :
      step r = .ok (.spawn child pending pc) → enter child = .run cr → Frame.Run cr (.exit raw) →
      resumeCaller r.context.block.rules child pending (raw >>= settle child) = .ok state →
      Frame.Run ⟨pc, r.context, state⟩ e → Frame.Run r e
  | callDoneEnd {r child pending pc result out} :
      step r = .ok (.spawn child pending pc) → enter child = .done result →
      resumeCaller r.context.block.rules child pending result = .error out → Frame.Run r (.exit out)
  | callRanEnd {r child pending pc cr raw out} :
      step r = .ok (.spawn child pending pc) → enter child = .run cr → Frame.Run cr (.exit raw) →
      resumeCaller r.context.block.rules child pending (raw >>= settle child) = .error out → Frame.Run r (.exit out)

namespace Frame.Run

abbrev Prefix (r s : Frame.Running) := Frame.Run r (.at s)

/-- Follow a prefix with a run beginning at its endpoint. -/
def append {r s e} (p : Prefix r s) (t : Frame.Run s e) : Frame.Run r e :=
  match p with
  | .stop _ => t
  | .next hs rest => .next hs (append rest t)
  | .callDone hs he hr rest => .callDone hs he hr (append rest t)
  | .callRan hs he child hr rest => .callRan hs he child hr (append rest t)
termination_by sizeOf p

@[simp] theorem stop_append {r e} (t : Frame.Run r e) : append (.stop r) t = t := by simp [append]

@[simp] theorem append_stop {r s} (p : Prefix r s) : append p (.stop s) = p := by
  cases p with
  | stop => simp
  | next hs rest => simp [append, append_stop rest]
  | callDone hs he hr rest => simp [append, append_stop rest]
  | callRan hs he child hr rest => simp [append, append_stop rest]
termination_by sizeOf p

theorem append_assoc {r s u e} (p : Prefix r s) (q : Prefix s u) (t : Frame.Run u e) :
    append (append p q) t = append p (append q t) := by
  cases p with
  | stop => simp
  | next hs rest => simp [append, append_assoc rest q t]
  | callDone hs he hr rest => simp [append, append_assoc rest q t]
  | callRan hs he child hr rest => simp [append, append_assoc rest q t]
termination_by sizeOf p

structure Node where
  start : Frame.Running
  exit : Except Fault Frame.Exit
  run : Frame.Run start (.exit exit)

structure Kept where
  node : Node
  committed : Exec.finished node.exit = true

structure Located where
  path : List Nat
  frame : Kept

/-- The data at the first step of a complete run, including the boundary on both sides of a child. -/
inductive Head where
  | halt (out : Except Fault Frame.Exit)
  | next (pc : Nat) (state : Frame.State)
  | callDone (child : Frame) (res : Except Fault Frame.Result) (pc : Nat) (state : Frame.State)
  | callRan (child : Frame) (cr : Frame.Running) (raw : Except Fault Frame.Exit) (pc : Nat) (state : Frame.State)
  | callDoneEnd (child : Frame) (res : Except Fault Frame.Result) (out : Except Fault Frame.Exit)
  | callRanEnd (child : Frame) (cr : Frame.Running) (raw out : Except Fault Frame.Exit)

def Node.head (n : Node) : Head :=
  match n.run with
  | .halt _ => .halt n.exit
  | .next (pc := pc) (state := s) .. => .next pc s
  | .callDone (child := f) (result := v) (pc := pc) (state := s) .. => .callDone f v pc s
  | .callRan (child := f) (cr := cr) (raw := raw) (pc := pc) (state := s) .. => .callRan f cr raw pc s
  | .callDoneEnd (child := f) (result := v) .. => .callDoneEnd f v n.exit
  | .callRanEnd (child := f) (cr := cr) (raw := raw) .. => .callRanEnd f cr raw n.exit

def Head.spawned? : Head → Option Frame
  | .halt .. | .next .. => none
  | .callDone f .. | .callRan f .. | .callDoneEnd f .. | .callRanEnd f .. => some f

end Frame.Run
end Jaune.Staging
