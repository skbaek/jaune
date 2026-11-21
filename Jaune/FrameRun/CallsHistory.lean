import Jaune.FrameRun.Calls
import Jaune.FrameRun.Facts

/-!
# Calls lifted to messages, transactions, bodies, blocks and kept histories (G2b, U102)

Wherever `Facts` lifts kept frames (`Root.frames` up to `KeptHistory.frames`), the calls
are lifted the same way: `calls` collects every call of every entered root, and `keptCalls`
applies the root's own settlement exactly as `Root.frames` does. A top-level frame that finished
at entry has no root, so it contributes no call: it was sent by no running frame.
-/

namespace Jaune

/-- Every call of the root's run. -/
def Root.calls (root : Root) : List Frame.Run.Call := root.run.calls

/-- The root's kept calls, empty when the root's own settlement does not commit, as `Root.frames`. -/
def Root.keptCalls (root : Root) : List Frame.Run.Call :=
  if Frame.settlementCommits root.frame root.outcome then root.run.keptCalls else []

theorem Root.keptCalls_of_failed {root : Root}
    (failed : Frame.settlementCommits root.frame root.outcome = false) : root.keptCalls = [] := by
  simp [Root.keptCalls, failed]

theorem Root.keptCalls_of_success {root : Root}
    (success : Frame.settlementCommits root.frame root.outcome = true) :
    root.keptCalls = root.run.keptCalls := by
  simp [Root.keptCalls, success]

theorem Root.keptCalls_sublist (root : Root) : root.keptCalls.Sublist root.calls := by
  unfold Root.keptCalls Root.calls
  split
  · exact Frame.Run.keptCalls_sublist _
  · exact List.nil_sublist _

def TopLevel.Run.calls (run : TopLevel.Run) : List Frame.Run.Call :=
  run.enteredRoot.toList.flatMap Root.calls

def TopLevel.Run.keptCalls (run : TopLevel.Run) : List Frame.Run.Call :=
  run.enteredRoot.toList.flatMap Root.keptCalls

def TransactionRun.calls (transaction : TransactionRun) : List Frame.Run.Call :=
  transaction.message.calls

def TransactionRun.keptCalls (transaction : TransactionRun) : List Frame.Run.Call :=
  transaction.message.keptCalls

def BlockRun.calls (run : BlockRun) : List Frame.Run.Call := run.roots.flatMap Root.calls

def BlockRun.keptCalls (run : BlockRun) : List Frame.Run.Call := run.roots.flatMap Root.keptCalls

def BodyPhase.calls (phase : BodyPhase) : List Frame.Run.Call := phase.roots.flatMap Root.calls

def BodyPhase.keptCalls (phase : BodyPhase) : List Frame.Run.Call :=
  phase.roots.flatMap Root.keptCalls

def BodyRun.calls (run : BodyRun) : List Frame.Run.Call := run.roots.flatMap Root.calls

def BodyRun.keptCalls (run : BodyRun) : List Frame.Run.Call := run.roots.flatMap Root.keptCalls

/-- A block's recorded phases make exactly its calls and kept calls. -/
theorem BlockRun.exists_bodyRoots_calls {fork parent block run}
    (executed : BlockRun.run fork parent block = .ok run) :
    ∃ body, BodyRoots run.context run.parent.state block.transactions block.ommers block.withdrawals
      run.final body ∧
      body.roots = run.roots ∧ body.calls = run.calls ∧ body.keptCalls = run.keptCalls := by
  obtain ⟨body, roots, rootsEq, _⟩ := BlockRun.exists_bodyRoots executed
  exact ⟨body, roots, rootsEq, by simp [BodyRun.calls, BlockRun.calls, rootsEq],
    by simp [BodyRun.keptCalls, BlockRun.keptCalls, rootsEq]⟩

def KeptBlock.calls (block : KeptBlock) : List Frame.Run.Call := block.run.calls

def KeptBlock.keptCalls (block : KeptBlock) : List Frame.Run.Call := block.run.keptCalls

def KeptHistory.calls (blocks : List KeptBlock) : List Frame.Run.Call := blocks.flatMap KeptBlock.calls

def KeptHistory.keptCalls (blocks : List KeptBlock) : List Frame.Run.Call :=
  blocks.flatMap KeptBlock.keptCalls

theorem KeptHistory.calls_append (blocks : List KeptBlock) (last : KeptBlock) :
    KeptHistory.calls (blocks ++ [last]) = KeptHistory.calls blocks ++ last.calls := by
  simp [KeptHistory.calls]

theorem KeptHistory.keptCalls_append (blocks : List KeptBlock) (last : KeptBlock) :
    KeptHistory.keptCalls (blocks ++ [last]) = KeptHistory.keptCalls blocks ++ last.keptCalls := by
  simp [KeptHistory.keptCalls]

/-- Every call of a kept history is a call of one of the history's entered roots. -/
theorem KeptHistory.mem_calls {blocks : List KeptBlock} {c : Frame.Run.Call} :
    c ∈ KeptHistory.calls blocks ↔ ∃ block ∈ blocks, ∃ root ∈ block.run.roots, c ∈ root.run.calls := by
  simp [KeptHistory.calls, KeptBlock.calls, BlockRun.calls, Root.calls]

end Jaune
