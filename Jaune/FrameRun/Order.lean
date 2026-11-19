import Jaune.FrameRun.Decompose

namespace Jaune.Staging.Frame.Run

/-- Immediate structural subruns. The child precedes the caller's continuation in execution order. -/
def Node.children (root : Node) : List Node :=
  match root.run with
  | .halt _ | .callDoneEnd .. => []
  | .next _ rest | .callDone _ _ _ rest => [⟨_, _, rest⟩]
  | .callRanEnd _ _ child _ => [⟨_, _, child⟩]
  | .callRan _ _ child _ rest => [⟨_, _, child⟩, ⟨_, _, rest⟩]

def Node.Sub (child parent : Node) : Prop := child ∈ parent.children

abbrev Node.lt := Relation.TransGen Node.Sub

private theorem Node.Sub.size_lt {child parent : Node} (h : Node.Sub child parent) :
    sizeOf child.run < sizeOf parent.run := by
  rcases parent with ⟨r, out, run⟩
  cases run <;> simp only [Node.Sub, Node.children, List.mem_cons, List.not_mem_nil, or_false] at h
  all_goals first
    | subst child; simp_wf
    | rcases h with rfl | rfl <;> (simp_wf; try omega)

theorem Node.Sub.wellFounded : WellFounded Node.Sub :=
  Subrelation.wf (fun h => Node.Sub.size_lt h) (measure (fun d : Node => sizeOf d.run)).wf

theorem Node.lt.wellFounded : WellFounded Node.lt := Node.Sub.wellFounded.transGen

theorem Node.strongRec (P : Node → Prop) (step : ∀ a, (∀ b, Node.lt b a → P b) → P a) (a : Node) : P a :=
  Node.lt.wellFounded.induction a step

/-- Induct by the remaining depth, independently of the number of same-frame steps. -/
theorem strong_rec (P : ∀ {r out}, Frame.Run r (.exit out) → Prop)
    (step : ∀ {r out} (t : Frame.Run r (.exit out)),
      (∀ {s raw} (child : Frame.Run s (.exit raw)), s.context.depthLeft < r.context.depthLeft → P child) →
      P t) {r out} (t : Frame.Run r (.exit out)) : P t := by
  induction depth : r.context.depthLeft using Nat.strong_induction_on generalizing r out with
  | h depth ih =>
    apply step
    intro s raw child lower
    exact ih _ (depth ▸ lower) child rfl

end Jaune.Staging.Frame.Run
