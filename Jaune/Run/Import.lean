import Jaune.Transaction

namespace Jaune.Staging

/-- Import an envelope using its original wire length. The transition function supplies
the fork semantics and keeps lookup failures outside consensus rejections. -/
def importCore
    (transition : BlockChain → Block → Except ImportFailure (Except TransitionError BlockChain))
    (limits : BlockLimits) (chain : BlockChain) (candidate : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) := do
  match checkBlockRlpSize limits candidate.rawSize with
  | .error error => return .inr (.block error)
  | .ok () =>
    match ← transition chain candidate.block with
    | .ok next => return .inl next
    | .error error =>
      match error.split with
      | .inl failure => throw failure
      | .inr rejection => return .inr rejection

def importExplicit (fork : Fork) (chain : BlockChain) (candidate : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) :=
  importCore (fun ch block => .ok (stateTransitionE fork ch block)) fork.ruleSet.block chain candidate

def importScheduled (cfg : ChainConfig) (fork : Fork) (chain : BlockChain) (candidate : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) :=
  importCore (fun ch block => (stateTransitionScheduledE cfg fork ch block).mapError ImportFailure.ofLookup)
    fork.ruleSet.block chain candidate

end Jaune.Staging
