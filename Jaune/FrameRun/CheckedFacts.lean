import Jaune.FrameRun.CheckedOrder
import Jaune.FrameRun.CheckedAdequacy

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
