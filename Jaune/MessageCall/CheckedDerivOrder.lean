import Jaune.MessageCall.CheckedChronology

namespace Jaune.Checked

/-- Count driver nodes in a derivation, including rolled-back children. -/
def Exec.nodeCount {r out} (tree : Exec r out) : Nat :=
  match tree with
  | .halt _ | .doneErr .. => 1
  | .cont _ next | .doneOk _ _ _ next => next.nodeCount + 1
  | .runErr _ _ child _ => child.nodeCount + 1
  | .runOk _ _ child _ next => child.nodeCount + next.nodeCount + 1
termination_by structural tree

/-- Immediate subderivations in execution order. -/
def Exec.Deriv.children (root : Exec.Deriv) : List Exec.Deriv :=
  match root.run with
  | .halt _ | .doneErr .. => []
  | .cont _ next | .doneOk _ _ _ next => [⟨_, _, next⟩]
  | .runErr _ _ child _ => [⟨_, _, child⟩]
  | .runOk _ _ child _ next => [⟨_, _, child⟩, ⟨_, _, next⟩]

def Exec.Deriv.Prec (node root : Exec.Deriv) : Prop := node ∈ root.children

abbrev Exec.Deriv.lt := Relation.TransGen Exec.Deriv.Prec

theorem Exec.Deriv.Prec.nodeCount_lt {node root : Exec.Deriv}
    (edge : node.Prec root) : node.run.nodeCount < root.run.nodeCount := by
  rcases root with ⟨r, out, run⟩
  cases run <;> simp only [Exec.Deriv.Prec, Exec.Deriv.children, List.mem_cons,
    List.not_mem_nil, or_false] at edge
  all_goals first
    | subst node; simp [Exec.nodeCount]
    | rcases edge with rfl | rfl <;> simp [Exec.nodeCount] <;> omega

theorem Exec.Deriv.lt.well_founded : WellFounded Exec.Deriv.lt :=
  (Subrelation.wf (fun h => Exec.Deriv.Prec.nodeCount_lt h)
    (measure (fun d : Exec.Deriv => d.run.nodeCount)).wf).transGen

theorem Exec.Deriv.strongRec (P : Exec.Deriv → Prop)
    (step : ∀ root, (∀ node, node.lt root → P node) → P root) (root : Exec.Deriv) : P root :=
  Exec.Deriv.lt.well_founded.induction root step

theorem Exec.Deriv.ParentStep.prec {node root : Exec.Deriv} (h : node.ParentStep root) :
    node.Prec root := by
  rcases root with ⟨r, out, run⟩
  cases run <;> simp [ParentStep, parentNext] at h <;> subst node <;> simp [Prec, children]

theorem Exec.Deriv.ParentStep.lt {node root : Exec.Deriv} (h : node.ParentStep root) :
    node.lt root := .single h.prec

theorem Exec.Deriv.ParentPrefix.snoc {root current next : Exec.Deriv}
    (path : root.ParentPrefix current) (edge : next.ParentStep current) :
    root.ParentPrefix next := path.tail edge

theorem Exec.Deriv.ParentPrefix.trans {root middle tail : Exec.Deriv}
    (first : root.ParentPrefix middle) (last : middle.ParentPrefix tail) :
    root.ParentPrefix tail := Relation.ReflTransGen.trans first last

/-- Induction on the remaining call depth, independent of the same-frame step count. -/
theorem Exec.strong_rec (P : ∀ {r out}, Exec r out → Prop)
    (step : ∀ {r out} (run : Exec r out),
      (∀ {r' out'} (child : Exec r' out'), r'.context.depthLeft < r.context.depthLeft → P child) →
      P run) {r out} (run : Exec r out) : P run := by
  induction depth : r.context.depthLeft using Nat.strong_induction_on generalizing r out with
  | h depth ih =>
    apply step
    intro r' out' child lower
    exact ih _ (depth ▸ lower) child rfl

end Jaune.Checked
