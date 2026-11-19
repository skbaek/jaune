import Jaune.Bridge.G2b.RunRoots
import Jaune.Transaction

namespace Jaune.Staging

/-- One configured successful block, with the recorded body that produced its final state. -/
structure KeptBlock where
  fork : Fork
  parent : BlockChain
  block : Block
  post : BlockChain
  run : BlockRun
  executed : BlockRun.run fork parent block = .ok run
  finalState : run.final.state = post.state

def KeptBlock.frames (block : KeptBlock) : List Exec.Frame := block.run.frames

/-- The configured importer selected this fork and accepted the block using its scheduled
ommer lookup. The rule data permits every supported fork. -/
structure KeptStep (cfg : ChainConfig) (fork : Fork) (parent : BlockChain) (block : Block)
    (post : BlockChain) : Prop where
  chainId : cfg.checkChainId parent = .ok ()
  forkAt : cfg.forkAt block.header.number block.header.timestamp = .ok fork
  accepted : stateTransitionCoreE (Sum.inr (α := RulesLookupError)) fork parent block
    (fun _ => checkBlockOmmersScheduledE cfg fork.ruleSet parent block.header block.ommers) = .ok post

theorem KeptStep.of_transition {cfg : ChainConfig} {parent post : BlockChain} {block : Block}
    (h : stateTransitionUsing cfg parent block = .ok post) :
    ∃ fork, KeptStep cfg fork parent block post := by
  unfold stateTransitionUsing at h
  obtain ⟨u, chain, h⟩ := Except.bind_eq_ok h
  cases u
  obtain ⟨fork, hf, h⟩ := Except.bind_eq_ok h
  refine ⟨fork, Except.mapError_eq_ok_iff.mp chain, Except.mapError_eq_ok_iff.mp hf, ?_⟩
  rw [← Jaune.stateTransitionScheduledE_eq_ok_iff]
  cases hs : Jaune.stateTransitionScheduledE cfg fork parent block with
  | error err => rw [hs] at h; cases h
  | ok result =>
    rw [hs] at h
    exact congrArg Except.ok (Except.mapError_eq_ok_iff.mp h)

inductive KeptHistory (cfg : ChainConfig) (start : BlockChain) : List KeptBlock → BlockChain → Prop
  | refl : KeptHistory cfg start [] start
  | step {blocks : List KeptBlock} {last : KeptBlock} :
    KeptHistory cfg start blocks last.parent →
    KeptStep cfg last.fork last.parent last.block last.post →
    KeptHistory cfg start (blocks ++ [last]) last.post

def KeptHistory.frames (blocks : List KeptBlock) : List Exec.Frame := blocks.flatMap KeptBlock.frames

theorem KeptHistory.frames_step (blocks : List KeptBlock) (last : KeptBlock) :
    KeptHistory.frames (blocks ++ [last]) = KeptHistory.frames blocks ++ last.frames := by
  simp [KeptHistory.frames]

theorem KeptStep.exists_block {cfg : ChainConfig} {fork parent block post}
    (step : KeptStep cfg fork parent block post) :
    ∃ b : KeptBlock, b.fork = fork ∧ b.parent = parent ∧ b.block = block ∧ b.post = post := by
  obtain ⟨run, hr, hf⟩ := E.exists_blockRun step.accepted
  exact ⟨⟨fork, parent, block, post, run, hr, hf⟩, rfl, rfl, rfl, rfl⟩

/-- Extend an existing history at a real successful configured step. -/
theorem KeptHistory.exists_snoc {cfg : ChainConfig} {start parent post fork block blocks}
    (history : KeptHistory cfg start blocks parent) (step : KeptStep cfg fork parent block post) :
    ∃ b, b.block = block ∧ KeptHistory cfg start (blocks ++ [b]) post := by
  obtain ⟨run, hr, hf⟩ := E.exists_blockRun step.accepted
  let b : KeptBlock := ⟨fork, parent, block, post, run, hr, hf⟩
  exact ⟨b, rfl, .step history step⟩

/-- Successful configured transitions are represented at all forks in their original order. -/
theorem KeptHistory.of_fold {cfg : ChainConfig} {start current post : BlockChain}
    {blocks : List KeptBlock} (prior : KeptHistory cfg start blocks current)
    (inputs : List Block) (accepted : inputs.foldlM (stateTransitionUsing cfg) current = .ok post) :
    ∃ suffix, suffix.map KeptBlock.block = inputs ∧ KeptHistory cfg start (blocks ++ suffix) post := by
  induction inputs generalizing current blocks with
  | nil =>
    cases accepted
    exact ⟨[], rfl, by simpa using prior⟩
  | cons first rest ih =>
    obtain ⟨next, step, tail⟩ := Except.bind_eq_ok accepted
    obtain ⟨fork, checkedStep⟩ := KeptStep.of_transition step
    obtain ⟨b, hb, history⟩ := prior.exists_snoc checkedStep
    obtain ⟨suffix, entries, full⟩ := ih history tail
    refine ⟨b :: suffix, by simp [hb, entries], ?_⟩
    simpa only [List.append_assoc, List.singleton_append] using full

end Jaune.Staging
