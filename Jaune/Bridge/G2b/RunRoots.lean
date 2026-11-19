import Jaune.Run.Root
import Jaune.Run.Block
import Jaune.Bridge.G2b.FinalDriver
import Jaune.Run.BodyFacts

namespace Jaune.Staging

/-- Read the entered code frame from the recorded message. Refusal and immediate completion
produce no root. This conversion disappears when the message record stores a native machine. -/
def MessageRun.enteredRoot (message : MessageRun) : Option Root :=
  match message.preparation, message.root with
  | .frame frame _, some evm => some (Root.ofEntry frame (.ofEvm evm))
  | _, _ => none

def MessageRun.frames (message : MessageRun) : List Exec.Frame :=
  message.enteredRoot.toList.flatMap Root.frames

def B2.TransactionRun.frames (transaction : B2.TransactionRun) : List Exec.Frame :=
  transaction.message.frames

def OpRun.messageRoot : OpRun → Option Root
  | .systemCall _ _ message | .requestCall _ _ _ message => message.enteredRoot
  | .transaction tx => tx.message.enteredRoot
  | .withdrawals .. | .depositRequests .. | .rewards .. | .buildAccessList .. | .checkAccessListLimit => none

def BlockRun.roots (block : BlockRun) : List Root := block.ops.filterMap OpRun.messageRoot

def BlockRun.frames (block : BlockRun) : List Exec.Frame := block.roots.flatMap Root.frames

/-- The recorded root, when present, settles to precisely the result the message recorded. -/
theorem Message.run_root_settled {msg : Msg} {message : MessageRun} {root : Root}
    (run : Message.run msg = .ok message) (entry : message.enteredRoot = some root) :
    ∃ result, message.result = some result ∧ root.settled = .ok result := by
  unfold Message.run at run
  obtain ⟨preparation, _, run⟩ := Except.bind_eq_ok run
  cases preparation with
  | refused reason halted =>
    cases run
    cases entry
  | frame f refund =>
    dsimp only at run
    cases he : Jaune.enterWith f f.checkpoint.toDevm with
    | done terminal =>
      rw [he] at run
      obtain ⟨result, _, run⟩ := Except.bind_eq_ok run
      cases run
      cases entry
    | run evm =>
      rw [he] at run
      obtain ⟨result, settled, run⟩ := Except.bind_eq_ok run
      cases run
      cases entry
      refine ⟨result, rfl, ?_⟩
      change (exec (.ofEvm evm) >>= settle f) = .ok result
      rw [exec_square evm (enterWith_run_output rfl he), ← settle_eq]
      exact settled

/-- Every successful body transition has a run with exactly its final world. -/
theorem E.exists_blockRun {ε : Type} {embed : TransitionError → ε} {fork : Fork}
    {parent post : BlockChain} {block : Block} {ommers : Unit → Except ε Unit}
    (h : E.stateTransitionCoreE embed fork parent block ommers = .ok post) :
    ∃ run, BlockRun.run fork parent block = .ok run ∧ run.final.state = post.state := by
  rw [E.stateTransitionCoreE_eq_run] at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨run, hr, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases h
  exact ⟨run, Except.mapError_eq_ok_iff.mp hr, rfl⟩

end Jaune.Staging
