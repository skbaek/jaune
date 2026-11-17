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

/-! ## Over the four-part message call -/

/-- Every reached driver node, in execution order: a spawned child before its caller's
continuation. -/
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
termination_by structural run

/-- The derivation itself heads its raw chronology. -/
theorem Exec.mem_rawNodes_self
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) :
    (⟨pc, sevm, pre, out, run⟩ : Exec.Deriv) ∈ Exec.rawNodes run := by
  cases run <;> simp [Exec.rawNodes]

/-- The retained node stream of a finished run. A spawned child is included only when its
settlement commits; a finished creation whose code deposit fails is not. -/
def Exec.retainedNodesOfCommits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) (committed : out.isOk = true) :
    List Exec.Deriv :=
  let root : Exec.Deriv := ⟨pc, sevm, pre, out, run⟩
  match run with
  | .halt _ => [root]
  | .cont _ next => root :: Exec.retainedNodesOfCommits next committed
  | .doneErr _ _ _ => Bool.noConfusion committed
  | .doneOk _ _ _ next => root :: Exec.retainedNodesOfCommits next committed
  | .runErr _ _ _ _ => Bool.noConfusion committed
  | .runOk (child := frame) (raw := raw) _ _ child _ next =>
      root ::
        ((if h : Frame.settlementCommits frame raw = true then
            Exec.retainedNodesOfCommits child (Frame.raw_commits_of_settlementCommits h)
          else []) ++
          Exec.retainedNodesOfCommits next committed)
termination_by structural run

/-- The retained chronology. The whole stream is erased when the root does not finish, so work
inside a failed run cannot leak. -/
def Exec.retainedNodes
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out) : List Exec.Deriv :=
  if h : out.isOk = true then
    Exec.retainedNodesOfCommits run h
  else []

@[simp] theorem Exec.retainedNodes_eq_nil_of_not_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (h : out.isOk ≠ true) :
    Exec.retainedNodes run = [] := by
  simp [Exec.retainedNodes, h]

@[simp] theorem Exec.retainedNodes_eq_of_commits
    {pc : Nat} {sevm : Sevm} {pre : Devm} {out : Execution}
    (run : Exec pc sevm pre out)
    (h : out.isOk = true) :
    Exec.retainedNodes run = Exec.retainedNodesOfCommits run h := by
  simp [Exec.retainedNodes, h]

@[simp] theorem Exec.retainedNodes_runOk_of_settlementCommits
    {pc pc' : Nat} {sevm : Sevm} {pre devm' : Devm}
    {frame : Jaune.Frame} {pending : Pending}
    {childEvm : Evm} {raw out : Execution}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame pending pc')
    (henter : enter frame = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resumeCaller sevm.benvStat.rules frame pending (settle frame raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (rootCommits : out.isOk = true)
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
    {frame : Jaune.Frame} {pending : Pending}
    {childEvm : Evm} {raw out : Execution}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame pending pc')
    (henter : enter frame = .run childEvm)
    (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
    (hresume : resumeCaller sevm.benvStat.rules frame pending (settle frame raw) = .ok devm')
    (next : Exec pc' sevm devm' out)
    (rootCommits : out.isOk = true)
    (childDoesNotSettle : Frame.settlementCommits frame raw ≠ true) :
    Exec.retainedNodes (.runOk hstep henter child hresume next) =
      ⟨pc, sevm, pre, out,
        Exec.runOk hstep henter child hresume next⟩ ::
        Exec.retainedNodes next := by
  simp [Exec.retainedNodes, Exec.retainedNodesOfCommits, rootCommits,
    childDoesNotSettle]

/-- The unique same-frame continuation edge. -/
inductive Exec.Deriv.ParentStep : Exec.Deriv → Exec.Deriv → Prop
  | cont {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .next pc' post)
      (next : Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .cont hstep next⟩
  | doneOk {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {frame : Jaune.Frame} {pending : Pending}
      {settled : Except Fault Frame.Result}
      {out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame pending pc')
      (henter : enter frame = .done settled)
      (hresume : resumeCaller sevm.benvStat.rules frame pending settled = .ok post)
      (next : Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .doneOk hstep henter hresume next⟩
  | runOk {pc pc' : Nat} {sevm : Sevm} {pre post : Devm}
      {frame : Jaune.Frame} {pending : Pending} {childEvm : Evm}
      {raw out : Execution}
      (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame pending pc')
      (henter : enter frame = .run childEvm)
      (child : Exec childEvm.pc childEvm.sta childEvm.dyna raw)
      (hresume : resumeCaller sevm.benvStat.rules frame pending (settle frame raw) = .ok post)
      (next : Exec pc' sevm post out) :
      ParentStep
        ⟨pc', sevm, post, out, next⟩
        ⟨pc, sevm, pre, out, .runOk hstep henter child hresume next⟩

/-- A same-frame node has only one continuation in one derivation. -/
theorem Exec.Deriv.ParentStep.unique
    {root nextLeft nextRight : Exec.Deriv}
    (left : Exec.Deriv.ParentStep nextLeft root)
    (right : Exec.Deriv.ParentStep nextRight root) :
    nextLeft = nextRight := by
  cases left <;> cases right <;> simp_all

/-- A same-frame edge is an immediate sub-derivation edge. -/
theorem Exec.Deriv.ParentStep.prec
    {root next : Exec.Deriv}
    (edge : Exec.Deriv.ParentStep next root) : Exec.Deriv.Prec next root := by
  cases edge with
  | cont hstep next => exact .cont hstep next
  | doneOk hstep henter hresume next =>
      exact .doneOk hstep henter hresume next
  | runOk hstep henter child hresume next =>
      exact .runOkCont hstep henter child hresume next

/-- A same-frame edge strictly descends in the derivation. -/
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

theorem Exec.Deriv.ParentPrefix.snoc
    {root current next : Exec.Deriv}
    (hprefix : Exec.Deriv.ParentPrefix root current)
    (edge : Exec.Deriv.ParentStep next current) :
    Exec.Deriv.ParentPrefix root next := by
  induction hprefix with
  | refl => exact .step edge (.refl _)
  | step head rest ih => exact .step head (ih edge)

theorem Exec.Deriv.ParentPrefix.trans
    {root middle tail : Exec.Deriv}
    (left : Exec.Deriv.ParentPrefix root middle)
    (right : Exec.Deriv.ParentPrefix middle tail) :
    Exec.Deriv.ParentPrefix root tail := by
  induction left with
  | refl => exact right
  | step head rest ih => exact .step head (ih right)

end Jaune
