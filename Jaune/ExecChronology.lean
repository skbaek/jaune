import Jaune.ExecDeriv
import Jaune.ExecSettlement

/-!
Raw and settlement-retained node order for the canonical derivation.
Children precede resumed parents; rollback filters the retained chronology.
Same-frame prefixes retain the existing descendant-to-root edge orientation.
-/

namespace Jaune

-- `ByteArray.getInst` and other extensions of root types live in `Jaune`;
-- opening it lets generalized field notation (`code.getInst`) find them.
open Jaune

/-- Every reached driver node, in execution order.  This is deliberately not
`Exec.Deriv.le`: the child and resumed continuation of `runOk` are sibling
recursive premises, while the chronology orders the child first. -/
def Legacy.Exec.rawNodes {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Legacy.Exec pc sevm pre out) : List Legacy.Exec.Deriv :=
  let root : Legacy.Exec.Deriv := ⟨pc, sevm, pre, out, run⟩
  match run with
  | .halt _ => [root]
  | .cont _ next => root :: Legacy.Exec.rawNodes next
  | .doneErr _ _ _ => [root]
  | .doneOk _ _ _ next => root :: Legacy.Exec.rawNodes next
  | .runErr _ _ child _ => root :: Legacy.Exec.rawNodes child
  | .runOk _ _ child _ next =>
      root :: (Legacy.Exec.rawNodes child ++ Legacy.Exec.rawNodes next)
termination_by sizeOf run

/-- The execution proof itself heads its raw chronology. -/
theorem Legacy.Exec.mem_rawNodes_self
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Legacy.Exec pc sevm pre out) :
    (⟨pc, sevm, pre, out, run⟩ : Legacy.Exec.Deriv) ∈ Legacy.Exec.rawNodes run := by
  cases run <;> simp [Legacy.Exec.rawNodes]

/-! ## Settlement-retained chronology -/

/-- The retained node stream of a known-committing execution.  A spawned
child is included only when complete frame settlement commits; in particular,
raw CREATE success is insufficient when code deposit rolls back. -/
def Legacy.Exec.retainedNodesOfCommits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Legacy.Exec pc sevm pre out) (committed : Execution.commits out = true) :
    List Legacy.Exec.Deriv :=
  let root : Legacy.Exec.Deriv := ⟨pc, sevm, pre, out, run⟩
  match run with
  | .halt _ => [root]
  | .cont _ next => root :: Legacy.Exec.retainedNodesOfCommits next committed
  | .doneErr _ _ _ => by simp [Execution.commits] at committed
  | .doneOk _ _ _ next => root :: Legacy.Exec.retainedNodesOfCommits next committed
  | .runErr _ _ _ _ => by simp [Execution.commits] at committed
  | .runOk (f := frame) (raw := raw) _ _ child _ next =>
      root ::
        ((if h : Legacy.Frame.settlementCommits frame raw = true then
            Legacy.Exec.retainedNodesOfCommits child
              (Legacy.Frame.raw_commits_of_settlementCommits h)
          else []) ++
          Legacy.Exec.retainedNodesOfCommits next committed)
termination_by sizeOf run

/-- Public retained chronology.  The whole stream is erased when the root
does not commit, so locally successful work cannot leak through rollback. -/
def Legacy.Exec.retainedNodes
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Legacy.Exec pc sevm pre out) : List Legacy.Exec.Deriv :=
  if h : Execution.commits out = true then
    Legacy.Exec.retainedNodesOfCommits run h
  else []

@[simp] theorem Legacy.Exec.retainedNodes_eq_nil_of_not_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Legacy.Exec pc sevm pre out)
    (h : Execution.commits out ≠ true) :
    Legacy.Exec.retainedNodes run = [] := by
  simp [Legacy.Exec.retainedNodes, h]

@[simp] theorem Legacy.Exec.retainedNodes_eq_of_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Legacy.Exec pc sevm pre out)
    (h : Execution.commits out = true) :
    Legacy.Exec.retainedNodes run = Legacy.Exec.retainedNodesOfCommits run h := by
  simp [Legacy.Exec.retainedNodes, h]

@[simp] theorem Legacy.Exec.retainedNodes_runOk_of_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {frame : Jaune.Legacy.Frame} {resume : Resume}
    {childEvm : Evm} {raw out : Execution}
    (hstep : Legacy.Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run childEvm)
    (child : Legacy.Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok devm')
    (next : Legacy.Exec pc' sevm devm' out)
    (rootCommits : Execution.commits out = true)
    (childSettles : Legacy.Frame.settlementCommits frame raw = true) :
    Legacy.Exec.retainedNodes (.runOk hstep henter child hresume next) =
      ⟨pc, sevm, pre, out,
        Legacy.Exec.runOk hstep henter child hresume next⟩ ::
        (Legacy.Exec.retainedNodes child ++ Legacy.Exec.retainedNodes next) := by
  have childCommits := Legacy.Frame.raw_commits_of_settlementCommits childSettles
  simp [Legacy.Exec.retainedNodes, Legacy.Exec.retainedNodesOfCommits, rootCommits,
    childSettles, childCommits]

@[simp] theorem Legacy.Exec.retainedNodes_runOk_of_not_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {frame : Jaune.Legacy.Frame} {resume : Resume}
    {childEvm : Evm} {raw out : Execution}
    (hstep : Legacy.Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run childEvm)
    (child : Legacy.Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resume.run (frame.settle raw) = .ok devm')
    (next : Legacy.Exec pc' sevm devm' out)
    (rootCommits : Execution.commits out = true)
    (childDoesNotSettle : Legacy.Frame.settlementCommits frame raw ≠ true) :
    Legacy.Exec.retainedNodes (.runOk hstep henter child hresume next) =
      ⟨pc, sevm, pre, out,
        Legacy.Exec.runOk hstep henter child hresume next⟩ ::
        Legacy.Exec.retainedNodes next := by
  simp [Legacy.Exec.retainedNodes, Legacy.Exec.retainedNodesOfCommits, rootCommits,
    childDoesNotSettle]

/-- The unique same-frame continuation edge.  Entered child proofs are not
edges here: they are the chronological segment crossed by `runOk` before its
parent continuation. -/
inductive Legacy.Exec.Deriv.ParentStep : Legacy.Exec.Deriv → Legacy.Exec.Deriv → Prop
  | cont {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {out : Execution}
      (hstep : Legacy.Evm.step ⟨pc, sevm, pre⟩ = .cont pc' post)
      (next : Legacy.Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .cont hstep next⟩
  | doneOk {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {frame : Jaune.Legacy.Frame} {resume : Resume}
      {settled : Except (EvmError × State × AdrSet × TransientStorage) Devm}
      {out : Execution}
      (hstep : Legacy.Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (henter : frame.enter = .done settled)
      (hresume : resume.run settled = .ok post)
      (next : Legacy.Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .doneOk hstep henter hresume next⟩
  | runOk {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {frame : Jaune.Legacy.Frame} {resume : Resume} {childEvm : Evm}
      {raw out : Execution}
      (hstep : Legacy.Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
      (henter : frame.enter = .run childEvm)
      (child : Legacy.Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (hresume : resume.run (frame.settle raw) = .ok post)
      (next : Legacy.Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .runOk hstep henter child hresume next⟩

/-- A same-frame node has only one continuation in one concrete proof. -/
theorem Legacy.Exec.Deriv.ParentStep.unique
    {root nextLeft nextRight : Legacy.Exec.Deriv}
    (left : Legacy.Exec.Deriv.ParentStep nextLeft root)
    (right : Legacy.Exec.Deriv.ParentStep nextRight root) :
    nextLeft = nextRight := by
  cases left <;> cases right <;> simp_all

/-- A same-frame parent edge is an immediate recursive derivation edge. -/
theorem Legacy.Exec.Deriv.ParentStep.prec
    {root next : Legacy.Exec.Deriv}
    (edge : Legacy.Exec.Deriv.ParentStep next root) : next ≺ root := by
  cases edge with
  | cont hstep next => exact .cont hstep next
  | doneOk hstep henter hresume next =>
      exact .doneOk hstep henter hresume next
  | runOk hstep henter child hresume next =>
      exact .runOkCont hstep henter child hresume next

/-- A same-frame parent edge strictly descends in the execution proof. -/
theorem Legacy.Exec.Deriv.ParentStep.lt
    {root next : Legacy.Exec.Deriv}
    (edge : Legacy.Exec.Deriv.ParentStep next root) : Legacy.Exec.Deriv.lt next root :=
  Legacy.Exec.Deriv.lt_of_prec edge.prec

/-- A finite same-frame prefix. -/
inductive Legacy.Exec.Deriv.ParentPrefix : Legacy.Exec.Deriv → Legacy.Exec.Deriv → Prop
  | refl (root : Legacy.Exec.Deriv) : ParentPrefix root root
  | step {root next tail : Legacy.Exec.Deriv}
      (head : Legacy.Exec.Deriv.ParentStep next root)
      (rest : Legacy.Exec.Deriv.ParentPrefix next tail) :
      Legacy.Exec.Deriv.ParentPrefix root tail

/-- Append one same-frame continuation edge. -/
theorem Legacy.Exec.Deriv.ParentPrefix.snoc
    {root current next : Legacy.Exec.Deriv}
    (hprefix : Legacy.Exec.Deriv.ParentPrefix root current)
    (edge : Legacy.Exec.Deriv.ParentStep next current) :
    Legacy.Exec.Deriv.ParentPrefix root next := by
  induction hprefix with
  | refl => exact .step edge (.refl _)
  | step head rest ih => exact .step head (ih edge)

/-- Compose two finite same-frame prefixes. -/
theorem Legacy.Exec.Deriv.ParentPrefix.trans
    {root middle tail : Legacy.Exec.Deriv}
    (left : Legacy.Exec.Deriv.ParentPrefix root middle)
    (right : Legacy.Exec.Deriv.ParentPrefix middle tail) :
    Legacy.Exec.Deriv.ParentPrefix root tail := by
  induction left with
  | refl => exact right
  | step head rest ih => exact .step head (ih right)

end Jaune
