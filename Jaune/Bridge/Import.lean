import Jaune.Run.Import

namespace Jaune.Bridge.Import

def addBlockToChainCanonicalE (f : Fork) (chain : BlockChain)
    (cb : CanonicalBlock) : Except ImportFailure (ImportOutcome BlockChain) :=
  match checkBlockRlpSize f.ruleSet.block cb.rawSize with
  | .error err => .ok (.inr (.block err))
  | .ok () =>
    match stateTransitionE f chain cb.block with
    | .error e =>
      match e.split with
      | .inl failure => .error failure
      | .inr rejection => .ok (.inr rejection)
    | .ok chain' => .ok (.inl chain')

def addBlockToChainScheduledCanonicalE (cfg : ChainConfig) (f : Fork)
    (chain : BlockChain) (cb : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) :=
  match checkBlockRlpSize f.ruleSet.block cb.rawSize with
  | .error err => .ok (.inr (.block err))
  | .ok () =>
    match stateTransitionScheduledE cfg f chain cb.block with
    | .error e => .error (ImportFailure.ofLookup e)
    | .ok (.error e) =>
      match e.split with
      | .inl failure => .error failure
      | .inr rejection => .ok (.inr rejection)
    | .ok (.ok chain') => .ok (.inl chain')

end Jaune.Bridge.Import

namespace Jaune.Staging

theorem importExplicit_eq (fork : Fork) (chain : BlockChain) (candidate : CanonicalBlock) :
    importExplicit fork chain candidate = Bridge.Import.addBlockToChainCanonicalE fork chain candidate := by
  unfold importExplicit importCore Bridge.Import.addBlockToChainCanonicalE
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
    importScheduled cfg fork chain candidate = Bridge.Import.addBlockToChainScheduledCanonicalE cfg fork chain candidate := by
  unfold importScheduled importCore Bridge.Import.addBlockToChainScheduledCanonicalE
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

theorem canonicalImport_eq (fork : Fork) (chain : BlockChain) (candidate : CanonicalBlock) :
    Jaune.addBlockToChainCanonicalE fork chain candidate =
      Bridge.Import.addBlockToChainCanonicalE fork chain candidate :=
  importExplicit_eq fork chain candidate

theorem scheduledCanonicalImport_eq (cfg : ChainConfig) (fork : Fork) (chain : BlockChain)
    (candidate : CanonicalBlock) :
    Jaune.addBlockToChainScheduledCanonicalE cfg fork chain candidate =
      Bridge.Import.addBlockToChainScheduledCanonicalE cfg fork chain candidate :=
  importScheduled_eq cfg fork chain candidate

end Jaune.Staging
