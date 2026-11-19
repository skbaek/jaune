import Jaune.Run.Canonical
import Jaune.Run.BlockFacts
import Jaune.Bridge.G2a.Consumers
import Jaune.Bridge.G2a.Block

/-!
# W2-C: the restated facts agree with the old ones (goal `jaune-shape-and-names-v1`, gate G2a, bridge)

A sanity check, not a dependency: `Jaune.Run.Canonical` and `Jaune.Run.BlockFacts` are proved
without the bridges. Here the old statements are recovered from the new ones through the bridges,
so the restatements say what the old ones said.

* `processTransaction`: through `processTransaction_eq_b2` and `B2.Transaction.run_output`.
* `processCheckedSystemTransaction`: through `processCheckedSystemTransaction_eq` and the output
  map `render`, whose state is the run's.
* The block transition: off the decode-order split, through `E.stateTransitionCoreE_eq_of_not_split`
  (on the split the two transitions differ by decisions 14 and 16, so no agreement is owed there).
-/

namespace Jaune.Bridge.G2a

open Jaune

/-- The old `processTransaction_canonical`, from the staged one. -/
theorem processTransaction_canonical_of_staged {benv : Benv} (h : benv.Canonical)
    {bout : BlockOutput} {tx : Transaction} {index : Nat} {p}
    (hp : Jaune.Bridge.G2a.Old.processTransaction benv bout tx index = .ok p) : State.Canonical p.1 := by
  rw [← processTransaction_eq_b2, ← Bridge.G2a.Phased.B2.Transaction.run_output] at hp
  cases hr : Transaction.run benv bout tx index with
  | error e => rw [hr] at hp; cases hp
  | ok r =>
    rw [hr] at hp
    cases hp
    exact Transaction.run_canonical h hr

/-- The old `processCheckedSystemTransaction_canonical`, from the staged one. -/
theorem processCheckedSystemTransaction_canonical_of_staged {benv : Benv} (h : benv.Canonical)
    {target : Address} {data : Bytes} {p}
    (hp : Jaune.Bridge.G2a.Old.processCheckedSystemTransaction benv target data = .ok p) :
    State.Canonical p.1 := by
  rw [processCheckedSystemTransaction_eq] at hp
  cases hq : processCheckedSystemTransaction benv target data with
  | error e => rw [hq] at hp; cases hp
  | ok run =>
    rw [hq] at hp
    cases hp
    exact processCheckedSystemTransaction_canonical h hq

/-- Off the split, an old successful transition is a staged one. -/
private theorem staged_of_old {ε : Type} {embed : TransitionError → ε} {f : Fork}
    {ch : BlockChain} {block : Block} {checkOmmers : Unit → Except ε Unit} {ch'}
    (hs : ¬ BlockDecodeOrderSplit f ch block checkOmmers)
    (hp : Jaune.Bridge.G2a.Old.stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    stateTransitionCoreE embed f ch block checkOmmers = .ok ch' :=
  (E.stateTransitionCoreE_eq_of_not_split embed f ch block checkOmmers hs).trans hp

/-- The old `stateTransitionCoreE_canonical`, from the staged one, off the split. -/
theorem stateTransitionCoreE_canonical_of_staged {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch : BlockChain} (h : ch.Canonical) {block : Block} {ch'}
    {checkOmmers : Unit → Except ε Unit}
    (hs : ¬ BlockDecodeOrderSplit f ch block checkOmmers)
    (hp : Jaune.Bridge.G2a.Old.stateTransitionCoreE embed f ch block checkOmmers = .ok ch') : ch'.Canonical :=
  stateTransitionCoreE_canonical h (staged_of_old hs hp)

/-- The old `stateTransitionCoreE_eq_ok`, from the staged one, off the split. -/
theorem stateTransitionCoreE_eq_ok_of_staged {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (hs : ¬ BlockDecodeOrderSplit f ch block checkOmmers)
    (hp : Jaune.Bridge.G2a.Old.stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    validateHeader f.ruleSet ch block.header = .ok () ∧
      ch'.blocks = appendBlock ch.blocks block ∧
      ch'.state.root = block.header.stateRoot :=
  stateTransitionCoreE_eq_ok (staged_of_old hs hp)

/-- The old `stateTransitionCoreE_preserves_chainId`, from the staged one, off the split. -/
theorem stateTransitionCoreE_preserves_chainId_of_staged {ε : Type}
    {embed : TransitionError → ε} {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (hs : ¬ BlockDecodeOrderSplit f ch block checkOmmers)
    (hp : Jaune.Bridge.G2a.Old.stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    ch'.chainId = ch.chainId :=
  stateTransitionCoreE_preserves_chainId (staged_of_old hs hp)

end Jaune.Bridge.G2a
