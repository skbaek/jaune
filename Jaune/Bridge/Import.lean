import Batteries.Tactic.OpenPrivate
import Jaune.Bridge.G2a.Block
import Jaune.Run.Import

/-!
The waiting canonical import wrappers call the historical block transition. The
proofs carry the existing block result equality through size checking and both
import error channels, under the block bridge's decode-order hypothesis.
-/

open private Jaune.splitScheduled from Jaune.Transaction

namespace Jaune.Bridge.Import

def stateTransitionE (f : Fork) (chain : BlockChain) (block : Block) :
    Except TransitionError BlockChain :=
  Bridge.G2a.Old.stateTransitionCoreE id f chain block
    (fun _ => checkBlockOmmers f.ruleSet chain block.header block.ommers)

def stateTransitionScheduledE (cfg : ChainConfig) (f : Fork)
    (chain : BlockChain) (block : Block) :
    Except RulesLookupError (Except TransitionError BlockChain) :=
  Jaune.splitScheduled <| Bridge.G2a.Old.stateTransitionCoreE Sum.inr f chain block
    (fun _ => checkBlockOmmersScheduledE cfg f.ruleSet chain block.header block.ommers)

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

theorem importExplicit_eq (fork : Fork) (chain : BlockChain) (candidate : CanonicalBlock)
    (h : ¬ Bridge.G2a.BlockDecodeOrderSplit fork chain candidate.block
      (fun _ => checkBlockOmmers fork.ruleSet chain candidate.block.header candidate.block.ommers)) :
    importExplicit fork chain candidate = Bridge.Import.addBlockToChainCanonicalE fork chain candidate := by
  unfold importExplicit importCore Bridge.Import.addBlockToChainCanonicalE
  have htransition : stateTransitionE fork chain candidate.block =
      Bridge.Import.stateTransitionE fork chain candidate.block :=
    Bridge.G2a.E.stateTransitionCoreE_eq_of_not_split id fork chain candidate.block _ h
  cases checkBlockRlpSize fork.ruleSet.block candidate.rawSize with
  | error e => rfl
  | ok unit =>
    cases unit
    dsimp only [bind, Except.bind]
    rw [htransition]
    cases Bridge.Import.stateTransitionE fork chain candidate.block with
    | ok next => rfl
    | error e => cases e.split <;> rfl

theorem importScheduled_eq (cfg : ChainConfig) (fork : Fork) (chain : BlockChain)
    (candidate : CanonicalBlock)
    (h : ¬ Bridge.G2a.BlockDecodeOrderSplit fork chain candidate.block
      (fun _ => checkBlockOmmersScheduledE cfg fork.ruleSet chain
        candidate.block.header candidate.block.ommers)) :
    importScheduled cfg fork chain candidate = Bridge.Import.addBlockToChainScheduledCanonicalE cfg fork chain candidate := by
  unfold importScheduled importCore Bridge.Import.addBlockToChainScheduledCanonicalE
  have htransition : stateTransitionScheduledE cfg fork chain candidate.block =
      Bridge.Import.stateTransitionScheduledE cfg fork chain candidate.block :=
    congrArg Jaune.splitScheduled
      (Bridge.G2a.E.stateTransitionCoreE_eq_of_not_split Sum.inr fork chain candidate.block _ h)
  cases checkBlockRlpSize fork.ruleSet.block candidate.rawSize with
  | error e => rfl
  | ok unit =>
    cases unit
    dsimp only
    rw [htransition]
    cases Bridge.Import.stateTransitionScheduledE cfg fork chain candidate.block with
    | error e => rfl
    | ok result =>
      cases result with
      | ok next => rfl
      | error e => cases e.split <;> rfl

theorem canonicalImport_eq (fork : Fork) (chain : BlockChain) (candidate : CanonicalBlock)
    (h : ¬ Bridge.G2a.BlockDecodeOrderSplit fork chain candidate.block
      (fun _ => checkBlockOmmers fork.ruleSet chain candidate.block.header candidate.block.ommers)) :
    Jaune.addBlockToChainCanonicalE fork chain candidate =
      Bridge.Import.addBlockToChainCanonicalE fork chain candidate :=
  importExplicit_eq fork chain candidate h

theorem scheduledCanonicalImport_eq (cfg : ChainConfig) (fork : Fork) (chain : BlockChain)
    (candidate : CanonicalBlock)
    (h : ¬ Bridge.G2a.BlockDecodeOrderSplit fork chain candidate.block
      (fun _ => checkBlockOmmersScheduledE cfg fork.ruleSet chain
        candidate.block.header candidate.block.ommers)) :
    Jaune.addBlockToChainScheduledCanonicalE cfg fork chain candidate =
      Bridge.Import.addBlockToChainScheduledCanonicalE cfg fork chain candidate :=
  importScheduled_eq cfg fork chain candidate h

end Jaune.Staging
