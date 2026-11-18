import Jaune.Transaction

namespace Jaune.Staging

def importExplicit (fork : Fork) (chain : BlockChain) (candidate : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) :=
  importCore (fun ch block => .ok (stateTransitionE fork ch block)) fork.ruleSet.block chain candidate

def importScheduled (cfg : ChainConfig) (fork : Fork) (chain : BlockChain) (candidate : CanonicalBlock) :
    Except ImportFailure (ImportOutcome BlockChain) :=
  importCore (fun ch block => (stateTransitionScheduledE cfg fork ch block).mapError ImportFailure.ofLookup)
    fork.ruleSet.block chain candidate

end Jaune.Staging
