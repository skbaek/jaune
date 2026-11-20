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

end Jaune.Staging
