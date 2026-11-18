import Jaune.FrameRun.Basic

namespace Jaune.Staging.Frame.Run

/-- Relabel a complete six-constructor derivation at its original start and result indices. -/
def ofExec {r out} (d : Exec r out) : Frame.Run r (.exit out) :=
  match d with
  | .halt hs => .halt hs
  | .cont hs rest => .next hs (ofExec rest)
  | .doneErr hs he hr => .callDoneEnd hs he hr
  | .doneOk hs he hr rest => .callDone hs he hr (ofExec rest)
  | .runErr hs he child hr => .callRanEnd hs he (ofExec child) hr
  | .runOk hs he child hr rest => .callRan hs he (ofExec child) hr (ofExec rest)
termination_by structural d

/-- Forget the endpoint tag of a complete frame sequence. -/
def toExec {r out} (t : Frame.Run r (.exit out)) : Exec r out :=
  match t with
  | .halt hs => .halt hs
  | .next hs rest => .cont hs (toExec rest)
  | .callDoneEnd hs he hr => .doneErr hs he hr
  | .callDone hs he hr rest => .doneOk hs he hr (toExec rest)
  | .callRanEnd hs he child hr => .runErr hs he (toExec child) hr
  | .callRan hs he child hr rest => .runOk hs he (toExec child) hr (toExec rest)
termination_by sizeOf t

@[simp] theorem toExec_ofExec {r out} (d : Exec r out) : toExec (ofExec d) = d := by
  induction d <;> simp_all [ofExec, toExec]

@[simp] theorem ofExec_toExec {r out} (t : Frame.Run r (.exit out)) : ofExec (toExec t) = t := by
  cases t with
  | halt | callDoneEnd => simp [ofExec, toExec]
  | next hs rest | callDone _ _ hs rest => simp [ofExec, toExec, ofExec_toExec rest]
  | callRanEnd hs he child hr => simp [ofExec, toExec, ofExec_toExec child]
  | callRan hs he child hr rest => simp [ofExec, toExec, ofExec_toExec child, ofExec_toExec rest]
termination_by sizeOf t

def equivExec (r : Frame.Running) (out : Except Fault Frame.Exit) :
    Frame.Run r (.exit out) ≃ Exec r out :=
  ⟨toExec, ofExec, ofExec_toExec, toExec_ofExec⟩

def Node.ofDeriv (d : Exec.Deriv) : Node := ⟨d.running, d.outcome, ofExec d.run⟩

def Kept.ofFrame (f : Exec.Frame) : Kept := ⟨⟨f.running, _, ofExec f.run⟩, rfl⟩

end Jaune.Staging.Frame.Run
