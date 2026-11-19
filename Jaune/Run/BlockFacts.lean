import Jaune.Run.Block

/-!
# What a block transition establishes (goal `jaune-shape-and-names-v1`, W2 unit W2-C)

Four facts about the staged block transition `E.stateTransitionCoreE`, restated from the ones
`Jaune.Transaction` states over the old `stateTransitionCoreE` and proved without the bridges:

* `E.stateTransitionCoreE_mapError`: embedding the static transition's error type commutes with
  the whole algorithm, failures included;
* `E.stateTransitionCoreE_header`: a success validated the header;
* `E.stateTransitionCoreE_preserves_chainId`: a success keeps the chain identity;
* `E.stateTransitionCoreE_eq_ok`: a success validated the header, appended the block, and its
  state's root is the header's.

The statements are the old ones with the staged transition in place of the old. The state-root
half of `_eq_ok` reads `Block.check`'s third comparison (`Block.check_stateRoot`) where the old
read `stateTransitionChecks`'s.

Staged under `Jaune.Staging.E`, beside the transition.
-/

namespace Jaune

open Jaune

private theorem except_mapError_id {ε α : Type} (r : Except ε α) : r.mapError id = r := by
  cases r <;> rfl

private theorem except_mapError_bind {ε ε' α β : Type}
    (g : ε → ε') (r : Except ε α) (k : α → Except ε β) :
    (r.bind k).mapError g = (r.mapError g).bind (fun a => (k a).mapError g) := by
  cases r <;> rfl

private theorem except_mapError_comp {ε ε' ε'' α : Type}
    (g : ε → ε') (g' : ε' → ε'') (r : Except ε α) :
    (r.mapError g).mapError g' = r.mapError (g' ∘ g) := by
  cases r <;> rfl

/-- A block check that passes compared the header's state root against the computed one. -/
theorem Block.check_stateRoot {header : Header} {c : Block.Commitments}
    (h : Block.check header c = .ok ()) : c.stateRoot = header.stateRoot := by
  by_contra hne
  revert h
  unfold Block.check Block.checkCommitments
  by_cases h1 : c.gasUsed ≠ header.gasUsed <;>
    by_cases h2 : c.transactionsRoot ≠ header.transactionsRoot <;>
    simp [h1, h2, hne, bind, Except.bind]


/-- Embedding the static transition's error type commutes with the whole algorithm, including
failures. This is the constant-action specialization used by a single-fork schedule. -/
theorem stateTransitionCoreE_mapError {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except TransitionError Unit) :
    stateTransitionCoreE embed f ch block
      (fun u => (checkOmmers u).mapError embed) =
      (stateTransitionCoreE id f ch block checkOmmers).mapError embed := by
  simp only [stateTransitionCoreE, except_mapError_id, Function.id_comp, bind,
    except_mapError_bind, except_mapError_comp]
  rfl

/-- A successful transition validated the header. -/
theorem stateTransitionCoreE_header {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (h : stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    validateHeader f.ruleSet ch block.header = .ok () := by
  unfold stateTransitionCoreE at h
  obtain ⟨u, hu, _⟩ := Except.bind_eq_ok h
  cases u
  exact Except.mapError_eq_ok_iff.mp hu

/-- Error embeddings and ommer resolution cannot change the chain identity copied by any
successful execution of the common algorithm. -/
theorem stateTransitionCoreE_preserves_chainId {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (h : stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    ch'.chainId = ch.chainId := by
  unfold stateTransitionCoreE at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases h
  rfl

/-- Success inversion shared by static and scheduled transitions. -/
theorem stateTransitionCoreE_eq_ok {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (h : stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    validateHeader f.ruleSet ch block.header = .ok () ∧
      ch'.blocks = appendBlock ch.blocks block ∧
      ch'.state.root = block.header.stateRoot := by
  unfold stateTransitionCoreE at h
  obtain ⟨u1, hvh, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨q, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨u3, hchk, h⟩ := Except.bind_eq_ok h
  cases u1
  cases u3
  cases h
  exact ⟨Except.mapError_eq_ok_iff.mp hvh, rfl,
    Block.check_stateRoot (Except.mapError_eq_ok_iff.mp hchk)⟩


end Jaune
