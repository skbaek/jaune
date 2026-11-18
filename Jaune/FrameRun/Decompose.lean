import Jaune.FrameRun.Views

namespace Jaune.Staging.Frame.Run

/-- A cut on a complete same-frame run with its exact reassembly equation. -/
structure Cut {r out} (t : Frame.Run r (.exit out)) where
  middle : Frame.Running
  initial : Prefix r middle
  remaining : Frame.Run middle (.exit out)
  reassemble : append initial remaining = t

private def Cut.prepend {r s out} {t : Frame.Run s (.exit out)}
    (wrap : ∀ {e}, Frame.Run s e → Frame.Run r e)
    (law : ∀ {u e} (p : Prefix s u) (q : Frame.Run u e), append (wrap p) q = wrap (append p q))
    (c : Cut t) : Cut (wrap t) :=
  ⟨c.middle, wrap c.initial, c.remaining, (law c.initial c.remaining).trans (congrArg wrap c.reassemble)⟩

/-- All same-frame cuts, including the empty prefix at the first state. -/
def cuts {r out} (t : Frame.Run r (.exit out)) : List (Cut t) :=
  match t with
  | .halt _ | .callDoneEnd .. | .callRanEnd .. => [⟨r, .stop r, _, stop_append _⟩]
  | .next hs rest =>
    ⟨r, .stop r, _, stop_append _⟩ ::
      (cuts rest).map (Cut.prepend (.next hs ·) (fun _ _ => by rw [append]))
  | .callDone hs he hr rest =>
    ⟨r, .stop r, _, stop_append _⟩ ::
      (cuts rest).map (Cut.prepend (.callDone hs he hr ·) (fun _ _ => by rw [append]))
  | .callRan hs he child hr rest =>
    ⟨r, .stop r, _, stop_append _⟩ ::
      (cuts rest).map (Cut.prepend (.callRan hs he child hr ·) (fun _ _ => by rw [append]))
termination_by sizeOf t

def decompose {r out} (t : Frame.Run r (.exit out)) :
    List (Σ s, Prefix r s × Frame.Run s (.exit out)) :=
  (cuts t).map fun c => ⟨c.middle, c.initial, c.remaining⟩

theorem decompose_append {r out} {t : Frame.Run r (.exit out)} {x} (h : x ∈ decompose t) :
    append x.2.1 x.2.2 = t := by
  obtain ⟨c, _, rfl⟩ := List.mem_map.mp h
  exact c.reassemble

def Node.Prefix (a b : Node) : Prop :=
  ∃ (p : Frame.Run.Prefix a.start b.start) (h : b.exit = a.exit), a.run = h ▸ append p b.run

private theorem suffix_mem_spine {r s out} (p : Prefix r s) (t : Frame.Run s (.exit out)) :
    (⟨s, out, t⟩ : Node) ∈ spine (append p t) := by
  cases p with
  | stop => cases t <;> simp [spine]
  | next hs rest | callDone _ _ hs rest | callRan _ _ _ hs rest =>
    rw [append, spine]
    exact List.mem_cons_of_mem _ (suffix_mem_spine rest t)
termination_by sizeOf p

private theorem cuts_nodes {r out} (t : Frame.Run r (.exit out)) :
    (cuts t).map (fun c => (⟨c.middle, out, c.remaining⟩ : Node)) = spine t := by
  cases t with
  | halt | callRanEnd | callDoneEnd => simp [cuts, spine]
  | next hs rest | callDone _ _ hs rest | callRan _ _ _ hs rest =>
    simpa [cuts, spine, Cut.prepend, List.map_map, Function.comp_def] using cuts_nodes rest
termination_by sizeOf t

theorem Node.prefix_iff_mem_spine (a b : Node) : Node.Prefix a b ↔ b ∈ spine a.run := by
  rcases a with ⟨r, out, t⟩
  rcases b with ⟨s, u, q⟩
  constructor
  · rintro ⟨p, h, assembled⟩
    cases h
    rw [assembled]
    exact suffix_mem_spine p q
  · intro h
    rw [← cuts_nodes] at h
    obtain ⟨c, _, hc⟩ := List.mem_map.mp h
    cases hc
    exact ⟨c.initial, rfl, c.reassemble.symm⟩

end Jaune.Staging.Frame.Run
