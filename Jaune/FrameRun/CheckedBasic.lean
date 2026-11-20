import Jaune.MessageCall.CheckedDriver
import Jaune.MessageCall.Measures

/-!
The frame boundary (`resumeCaller`, the driver's spawn equations, settlement commitment) and the
ordered frame run `Frame.Run`. Nothing here depends on the derivation `Checked.Exec`.
-/

namespace Jaune.Checked

/-- Finishing a call either gives the driver's final outcome or a caller state to resume. -/
def resumeCaller (rules : ForkRules) (child : Frame) (pending : Staging.Pending) :
    Except Fault Frame.Result → Except (Except Fault Frame.Exit) Frame.State
  | .error fault => .error (.error fault)
  | .ok result =>
    match resume rules pending child.checkpoint result with
    | .error fault => .error (.error fault)
    | .ok (.error (reason, state)) => .error (.ok (.halted reason state))
    | .ok (.ok state) => .ok state

theorem execFueled_spawn_done {r : Frame.Running} {fuel : Nat} {child pending pc result}
    (hs : step r = .ok (.spawn child pending pc)) (he : enter child = .done result) :
    execFueled r (fuel + 1) =
      match resumeCaller r.context.block.rules child pending result with
      | .error out => Fueled.ofExcept out
      | .ok state => execFueled ⟨pc, r.context, state⟩ fuel := by
  rw [execFueled, hs]
  dsimp only
  rw [he]
  cases result with
  | error f => rfl
  | ok v =>
    dsimp only [resumeCaller]
    rcases resume r.context.block.rules pending child.checkpoint v with
      f | ⟨reason, state⟩ | state <;> rfl

theorem execFueled_spawn_run {r : Frame.Running} {fuel : Nat} {child pending pc cr}
    (hs : step r = .ok (.spawn child pending pc)) (he : enter child = .run cr) :
    execFueled r (fuel + 1) =
      match (execFueled cr fuel).run with
      | none => Fueled.exhausted
      | some raw =>
        match resumeCaller r.context.block.rules child pending (raw >>= settle child) with
        | .error out => Fueled.ofExcept out
        | .ok state => execFueled ⟨pc, r.context, state⟩ fuel := by
  rw [execFueled, hs]
  dsimp only
  rw [he]
  dsimp only
  cases hc : (execFueled cr fuel).run with
  | none => rfl
  | some raw =>
    dsimp only [Option.map]
    cases raw >>= settle child with
    | error f => rfl
    | ok v =>
      dsimp only [resumeCaller]
      rcases resume r.context.block.rules pending child.checkpoint v with
        f | ⟨reason, state⟩ | state <;> rfl

/-- The raw root finished successfully. A creation still has to deposit its code. -/
def Exec.finished : Except Fault Frame.Exit → Bool
  | .ok (.finished ..) => true
  | _ => false

def Frame.settlementCommits (frame : Frame) (raw : Except Fault Frame.Exit) : Bool :=
  match raw >>= settle frame with
  | .ok (.success ..) => true
  | _ => false

theorem Frame.settlementCommits_iff {frame : Frame} {raw : Except Fault Frame.Exit} :
    Frame.settlementCommits frame raw = true ↔
      ∃ output gas meters world substate trail,
        (raw >>= settle frame) = .ok (.success output gas meters world substate trail) := by
  unfold Frame.settlementCommits
  constructor
  · intro h
    split at h
    · exact ⟨_, _, _, _, _, _, by assumption⟩
    · cases h
  · rintro ⟨_, _, _, _, _, _, h⟩
    rw [h]

theorem Frame.finished_of_settlementCommits {frame : Frame} {raw : Except Fault Frame.Exit}
    (h : Frame.settlementCommits frame raw = true) : Exec.finished raw = true := by
  rcases raw with fault | ⟨output, s⟩ | ⟨output, s⟩ | ⟨reason, s⟩
  · cases h
  · rfl
  · cases h
  · cases h

/-- Row 29. Settlement can commit only a raw result that finished. -/
theorem Frame.raw_commits_of_settlementCommits {f : Frame} {raw : Except Fault Frame.Exit}
    (h : Frame.settlementCommits f raw = true) : Exec.finished raw = true :=
  Frame.finished_of_settlementCommits h

/-- Row 35. A call frame's settlement commits every finished raw result. -/
theorem Frame.settlementCommits_ofCall_of_raw_commits {f : Frame} {raw : Except Fault Frame.Exit}
    (hcall : f.message.kind = .call) (hraw : Exec.finished raw = true) :
    Frame.settlementCommits f raw = true := by
  rcases raw with fault | ⟨output, s⟩ | ⟨output, s⟩ | ⟨reason, s⟩
  · cases hraw
  · simp [Frame.settlementCommits, settle, hcall, bind, Except.bind, Frame.Result.ofSuccess]
  · cases hraw
  · cases hraw

/-- A decoded next-op instruction steps through `NextOp.step`. -/
theorem step_of_next {r : Frame.Running} {n : NextOp} (h : NextOp.At r.context.code r.pc n) :
    step r = .ok (NextOp.step r n) := by
  unfold step
  rw [show r.getOp = some (.next n) from h]

/-- A decoded halting instruction exits with its own result. -/
theorem step_of_halt {r : Frame.Running} {l : HaltOp} (h : HaltOp.At r.context.code r.pc l) :
    step r = (HaltOp.run r.context r.state l).map Step.exit := by
  unfold step
  rw [show r.getOp = some (.halt l) from h]

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
end Jaune.Checked
