import Jaune.Run.Import

namespace Jaune.Staging

theorem importExplicit_eq (fork : Fork) (chain : BlockChain) (candidate : CanonicalBlock) :
    importExplicit fork chain candidate = addBlockToChainCanonicalE fork chain candidate := by
  unfold importExplicit importCore addBlockToChainCanonicalE
  cases checkBlockRlpSize fork.ruleSet.block candidate.rawSize with
  | error e => rfl
  | ok unit =>
    cases unit
    dsimp only [bind, Except.bind]
    cases stateTransitionE fork chain candidate.block with
    | ok next => rfl
    | error e => cases e.split <;> rfl

theorem importScheduled_eq (cfg : ChainConfig) (fork : Fork) (chain : BlockChain)
    (candidate : CanonicalBlock) :
    importScheduled cfg fork chain candidate = addBlockToChainScheduledCanonicalE cfg fork chain candidate := by
  unfold importScheduled importCore addBlockToChainScheduledCanonicalE
  cases checkBlockRlpSize fork.ruleSet.block candidate.rawSize with
  | error e => rfl
  | ok unit =>
    cases unit
    dsimp only
    cases stateTransitionScheduledE cfg fork chain candidate.block with
    | error e => rfl
    | ok result =>
      cases result with
      | ok next => rfl
      | error e => cases e.split <;> rfl

end Jaune.Staging
