import Jaune.ExecDeriv
import Jaune.ExecSettlement

/-!
Raw and settlement-retained node order for the canonical derivation.
Children precede resumed parents; rollback filters the retained chronology.
Same-frame prefixes retain the existing descendant-to-root edge orientation.
-/

namespace Blanc

open Jaune

/-- Every reached driver node, in execution order.  This is deliberately not
`Exec.Deriv.le`: the child and resumed continuation of `runOk` are sibling
recursive premises, while the chronology orders the child first. -/
def Exec.rawNodes {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) : List Exec.Deriv :=
  let root : Exec.Deriv := ⟨pc, sevm, pre, out, run⟩
  match run with
  | .halt _ => [root]
  | .cont _ next => root :: Exec.rawNodes next
  | .doneErr _ _ _ => [root]
  | .doneOk _ _ _ next => root :: Exec.rawNodes next
  | .runErr _ _ child _ => root :: Exec.rawNodes child
  | .runOk _ _ child _ next =>
      root :: (Exec.rawNodes child ++ Exec.rawNodes next)
termination_by sizeOf run

/-- The execution proof itself heads its raw chronology. -/
theorem Exec.mem_rawNodes_self
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) ∈ Exec.rawNodes run := by
  cases run <;> simp [Exec.rawNodes]

/-! ## Settlement-retained chronology -/

/-- The retained node stream of a known-committing execution.  A spawned
child is included only when complete frame settlement commits; in particular,
raw CREATE success is insufficient when code deposit rolls back. -/
def Exec.retainedNodesOfCommits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : Execution.commits out = true) :
    List Exec.Deriv :=
  let root : Exec.Deriv := ⟨pc, sevm, pre, out, run⟩
  match run with
  | .halt _ => [root]
  | .cont _ next => root :: Exec.retainedNodesOfCommits next committed
  | .doneErr _ _ _ => by simp [Execution.commits] at committed
  | .doneOk _ _ _ next => root :: Exec.retainedNodesOfCommits next committed
  | .runErr _ _ _ _ => by simp [Execution.commits] at committed
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      root ::
        ((if h : Frame.settlementCommits frame raw = true then
            Exec.retainedNodesOfCommits child
              (Frame.raw_commits_of_settlementCommits h)
          else []) ++
          Exec.retainedNodesOfCommits next committed)
termination_by sizeOf run

/-- Public retained chronology.  The whole stream is erased when the root
does not commit, so locally successful work cannot leak through rollback. -/
def Exec.retainedNodes
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List Exec.Deriv :=
  if h : Execution.commits out = true then
    Exec.retainedNodesOfCommits run h
  else []

@[simp] theorem Exec.retainedNodes_eq_nil_of_not_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (h : Execution.commits out ≠ true) :
    Exec.retainedNodes run = [] := by
  simp [Exec.retainedNodes, h]

@[simp] theorem Exec.retainedNodes_eq_of_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (h : Execution.commits out = true) :
    Exec.retainedNodes run = Exec.retainedNodesOfCommits run h := by
  simp [Exec.retainedNodes, h]

@[simp] theorem Exec.retainedNodes_runOk_of_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {frame : Jaune.Frame} {resume : Resume}
    {childEvm : Evm} {raw out : Execution}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (rootCommits : Execution.commits out = true)
    (childSettles : Frame.settlementCommits frame raw = true) :
    Exec.retainedNodes (.runOk hstep henter child hresume next) =
      ⟨pc, sevm, pre, out,
        Exec.runOk hstep henter child hresume next⟩ ::
        (Exec.retainedNodes child ++ Exec.retainedNodes next) := by
  have childCommits := Frame.raw_commits_of_settlementCommits childSettles
  simp [Exec.retainedNodes, Exec.retainedNodesOfCommits, rootCommits,
    childSettles, childCommits]

@[simp] theorem Exec.retainedNodes_runOk_of_not_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {frame : Jaune.Frame} {resume : Resume}
    {childEvm : Evm} {raw out : Execution}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (rootCommits : Execution.commits out = true)
    (childDoesNotSettle : Frame.settlementCommits frame raw ≠ true) :
    Exec.retainedNodes (.runOk hstep henter child hresume next) =
      ⟨pc, sevm, pre, out,
        Exec.runOk hstep henter child hresume next⟩ ::
        Exec.retainedNodes next := by
  simp [Exec.retainedNodes, Exec.retainedNodesOfCommits, rootCommits,
    childDoesNotSettle]

/-- The unique same-frame continuation edge.  Entered child proofs are not
edges here: they are the chronological segment crossed by `runOk` before its
parent continuation. -/
inductive Exec.Deriv.ParentStep : Exec.Deriv → Exec.Deriv → Prop
  | cont {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
      (next : Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .cont hstep next⟩
  | doneOk {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {frame : Jaune.Frame} {resume : Resume}
      {settled : Except (EvmError × State × AdrSet × Tra) Devm}
      {out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (henter : frame.enter = .done settled)
      (hresume : resume.run settled = .ok post)
      (next : Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .doneOk hstep henter hresume next⟩
  | runOk {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {frame : Jaune.Frame} {resume : Resume} {childEvm : Evm}
      {raw out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (henter : frame.enter = .run childEvm)
      (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (hresume : resume.run (frame.settle raw) = .ok post)
      (next : Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .runOk hstep henter child hresume next⟩

/-- A same-frame node has only one continuation in one concrete proof. -/
theorem Exec.Deriv.ParentStep.unique
    {root nextLeft nextRight : Exec.Deriv}
    (left : Exec.Deriv.ParentStep nextLeft root)
    (right : Exec.Deriv.ParentStep nextRight root) :
    nextLeft = nextRight := by
  cases left <;> cases right <;> simp_all

/-- A same-frame parent edge is an immediate recursive derivation edge. -/
theorem Exec.Deriv.ParentStep.prec
    {root next : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next root) : next ≺ root := by
  cases edge with
  | cont hstep next => exact .cont hstep next
  | doneOk hstep henter hresume next =>
      exact .doneOk hstep henter hresume next
  | runOk hstep henter child hresume next =>
      exact .runOkCont hstep henter child hresume next

/-- A same-frame parent edge strictly descends in the execution proof. -/
theorem Exec.Deriv.ParentStep.lt
    {root next : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next root) : Exec.Deriv.lt next root :=
  Exec.Deriv.lt_of_prec edge.prec

/-- A finite same-frame prefix. -/
inductive Exec.Deriv.ParentPrefix : Exec.Deriv → Exec.Deriv → Prop
  | refl (root : Exec.Deriv) : ParentPrefix root root
  | step {root next tail : Exec.Deriv}
      (head : Exec.Deriv.ParentStep next root)
      (rest : Exec.Deriv.ParentPrefix next tail) :
      Exec.Deriv.ParentPrefix root tail

/-- Append one same-frame continuation edge. -/
theorem Exec.Deriv.ParentPrefix.snoc
    {root current next : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentPrefix root current)
    (edge : Exec.Deriv.ParentStep next current) :
    Exec.Deriv.ParentPrefix root next := by
  induction hprefix with
  | refl => exact .step edge (.refl _)
  | step head rest ih => exact .step head (ih edge)

/-- Compose two finite same-frame prefixes. -/
theorem Exec.Deriv.ParentPrefix.trans
    {root middle tail : Exec.Deriv}
    (left : Exec.Deriv.ParentPrefix root middle)
    (right : Exec.Deriv.ParentPrefix middle tail) :
    Exec.Deriv.ParentPrefix root tail := by
  induction left with
  | refl => exact right
  | step head rest ih => exact .step head (ih right)

end Blanc
