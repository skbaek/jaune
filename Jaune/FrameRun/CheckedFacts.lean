import Jaune.FrameRun.CheckedOrder
import Jaune.FrameRun.CheckedAdequacy
import Jaune.Run.CheckedTransaction

/-!
# `Exec`-free restatements over the checked frame sequence (goal `jaune-shape-and-names-v1`, G2b)

The checked derivation facts that `Checked.Frame.Run` did not already state, with the same
conclusions: the canonical derivation is inhabited, a failed root retains no node, and the
same-frame continuation is reflexive, transitive and well-founded.
-/

namespace Jaune.Checked.Frame.Run

/-- Restates `Checked.Exec.nonempty`. -/
theorem nonempty (r : Frame.Running) : Nonempty (Frame.Run r (.exit (exec r))) := ⟨canonical r⟩

/-- Restates `Checked.Exec.retainedNodes_eq_nil_of_failed`. -/
theorem retainedNodes_eq_nil_of_failed {r out} (t : Frame.Run r (.exit out))
    (h : Exec.finished out = false) : retainedNodes t = [] := by
  simp [retainedNodes, h]

/-- Restates `Checked.Exec.committedFrames_eq_nil_of_failed`. -/
theorem committedFrames_eq_nil_of_failed {r out} (t : Frame.Run r (.exit out))
    (h : Exec.finished out = false) : committedFrames t = [] := by
  simp [committedFrames, h]

theorem Node.Prefix.refl (a : Node) : a.Prefix a := ⟨.stop _, rfl, by simp⟩

/-- Restates `Checked.Exec.Deriv.ParentPrefix.trans` (and `snoc`, its one-step case). -/
theorem Node.Prefix.trans {a b c : Node} (first : a.Prefix b) (last : b.Prefix c) : a.Prefix c := by
  rcases a with ⟨r, out, t⟩
  rcases b with ⟨s, u, q⟩
  rcases c with ⟨w, v, x⟩
  obtain ⟨p, hu, e⟩ := first
  obtain ⟨p', hv, e'⟩ := last
  dsimp only at hu hv p p' e e'
  subst hu hv
  exact ⟨append p p', rfl, by rw [e, e', append_assoc]⟩

private theorem mem_spine {r out} (t : Frame.Run r (.exit out)) (b : Node) (h : b ∈ spine t) :
    b = ⟨r, out, t⟩ ∨ Node.lt b ⟨r, out, t⟩ := by
  cases t with
  | halt | callDoneEnd | callRanEnd => simp only [spine, List.mem_singleton] at h; exact .inl h
  | next hs rest | callDone _ _ hs rest | callRan _ _ _ hs rest =>
    rw [spine] at h
    rcases List.mem_cons.mp h with h | h
    · exact .inl h
    · refine .inr ?_
      rcases mem_spine rest b h with rfl | lt
      · exact .single (by simp [Node.Sub, Node.children])
      · exact .tail lt (by simp [Node.Sub, Node.children])
termination_by sizeOf t

/-- Restates `Checked.Exec.Deriv.ParentStep.prec` and `ParentStep.lt`: a proper same-frame
continuation is strictly below its start in the structural order. -/
theorem Node.Prefix.lt {a b : Node} (h : a.Prefix b) (ne : b ≠ a) : Node.lt b a := by
  rcases a with ⟨r, out, t⟩
  rcases (mem_spine t b ((Node.prefix_iff_mem_spine _ b).mp h)) with eq | lt
  · exact absurd eq ne
  · exact lt

end Jaune.Checked.Frame.Run

namespace Jaune.Checked

/-- The code entry recorded by a top-level message, with its complete checked frame run. -/
structure Root where
  frame : Frame
  running : Frame.Running
  outcome : Except Fault Frame.Exit
  run : Frame.Run running (.exit outcome)

def Root.ofEntry (frame : Frame) (running : Frame.Running) : Root :=
  ⟨frame, running, exec running, Frame.Run.canonical running⟩

def Root.settled (root : Root) : Except Fault Frame.Result :=
  root.outcome >>= settle root.frame

/-- The root's own settlement can roll back a successful raw execution, including code deposit. -/
def Root.frames (root : Root) : List Frame.Run.Kept :=
  if Frame.settlementCommits root.frame root.outcome then root.run.committedFrames else []

theorem Root.frames_of_failed {root : Root}
    (failed : Frame.settlementCommits root.frame root.outcome = false) : root.frames = [] := by
  simp [Root.frames, failed]

theorem Root.frames_of_success {root : Root}
    (success : Frame.settlementCommits root.frame root.outcome = true) :
    root.frames = root.run.committedFrames := by
  simp [Root.frames, success]

/-- A refusal or a completion at entry, such as a precompile, contributes no code root. -/
def TopLevel.Run.enteredRoot : TopLevel.Run → Option Root
  | .refused _ => none
  | .frame f _ top => top.root.map (Root.ofEntry f)

def TopLevel.Run.frames (run : TopLevel.Run) : List Frame.Run.Kept :=
  run.enteredRoot.toList.flatMap Root.frames

theorem Frame.runTopWithRoot_settled {frame : Frame} {top : Frame.TopRun} {running : Frame.Running}
    (accepted : frame.runTopWithRoot = .ok top) (entry : top.root = some running) :
    (Root.ofEntry frame running).settled = .ok top.result := by
  have result := congrArg (Except.map Frame.TopRun.result) accepted
  change frame.runTop = .ok top.result at result
  rw [Frame.runTop_eq] at result
  have recorded := (Frame.runTopWithRoot_root accepted).symm.trans entry
  cases started : enterWith frame frame.checkpoint with
  | done => rw [started] at recorded; cases recorded
  | run root =>
    rw [started] at recorded result
    cases recorded
    exact result

/-- An entered root settles to the result held by the successful message that supplied it. -/
theorem TopLevel.runNative_root_settled {input : TopLevel.Input} {run : TopLevel.Run} {root : Root}
    (accepted : TopLevel.runNative input = .ok run) (entry : run.enteredRoot = some root) :
    ∃ top refund, run = .frame root.frame refund top ∧ root.settled = .ok top.result := by
  unfold TopLevel.runNative at accepted
  obtain ⟨prepared, _, accepted⟩ := Except.bind_eq_ok accepted
  cases preparation : prepared.toPreparation with
  | refused => rw [preparation] at accepted; cases accepted; cases entry
  | frame frame refund =>
    rw [preparation] at accepted
    cases acceptedFrame : frame.runTopWithRoot with
    | error err => simp [TopLevel.Preparation.run, acceptedFrame, Except.map] at accepted
    | ok top =>
      simp only [TopLevel.Preparation.run, acceptedFrame, Except.map, Except.ok.injEq] at accepted
      subst run
      cases recorded : top.root with
      | none => simp [TopLevel.Run.enteredRoot, recorded] at entry
      | some running =>
        simp only [TopLevel.Run.enteredRoot, recorded, Option.map_some, Option.some.injEq] at entry
        subst root
        exact ⟨top, refund, rfl, Frame.runTopWithRoot_settled acceptedFrame recorded⟩

/-- The roots of a successful message come from that run's sole possible code entry. -/
def MessageRoots (input : TopLevel.Input) (run : TopLevel.Run) (roots : List Root) : Prop :=
  TopLevel.runNative input = .ok run ∧ roots = run.enteredRoot.toList

theorem exists_messageRoots {input run} (accepted : TopLevel.runNative input = .ok run) :
    ∃ roots, MessageRoots input run roots := ⟨_, accepted, rfl⟩

theorem MessageRoots.atMostOne {input run roots} (h : MessageRoots input run roots) :
    roots.length ≤ 1 := by
  obtain ⟨_, rfl⟩ := h
  cases run.enteredRoot <;> simp

def TransactionRun.frames (transaction : TransactionRun) : List Frame.Run.Kept :=
  transaction.message.frames

/-- The transaction's sender, final observations and roots come from the same run. -/
def TransactionRoots (benv : Benv) (input : BlockOutput) (tx : Jaune.Transaction) (index : Nat)
    (state : State) (output : BlockOutput) (sender : Address) (roots : List Root) : Prop :=
  ∃ run, Transaction.run benv input tx index = .ok (run, output) ∧ run.state = state ∧
    run.sender = sender ∧ MessageRoots run.entry run.message roots

theorem Transaction.run_messageRoots {benv input tx index run output}
    (accepted : Transaction.run benv input tx index = .ok (run, output)) :
    MessageRoots run.entry run.message run.message.enteredRoot.toList := by
  unfold Transaction.run at accepted
  obtain ⟨_, _, accepted⟩ := Except.bind_eq_ok accepted
  obtain ⟨prepared, _, accepted⟩ := Except.bind_eq_ok accepted
  obtain ⟨message, executed, settled⟩ := Except.bind_eq_ok accepted
  unfold Transaction.settleRun at settled
  obtain ⟨_, _, settled⟩ := Except.bind_eq_ok settled
  cases settled
  exact ⟨Except.mapError_eq_ok_iff.mp executed, rfl⟩

theorem exists_transactionRoots {benv input tx index state output}
    (accepted : (Transaction.run benv input tx index).map (fun (run, next) => (run.state, next)) =
      .ok (state, output)) : ∃ sender roots, TransactionRoots benv input tx index state output sender roots := by
  cases executed : Transaction.run benv input tx index with
  | error => simp [executed, Except.map] at accepted
  | ok pair =>
    rcases pair with ⟨run, next⟩
    simp only [executed, Except.map, Except.ok.injEq, Prod.mk.injEq] at accepted
    obtain ⟨rfl, rfl⟩ := accepted
    exact ⟨run.sender, _, run, executed, rfl, rfl, Transaction.run_messageRoots executed⟩

end Jaune.Checked
