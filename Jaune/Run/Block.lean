import Jaune.Run.Body
import Jaune.Run.Prefix

/-!
# The block is a run with commitments (goal `jaune-shape-and-names-v1`, W2 cut E)

A block's transition validates the header, checks the ommers, runs the body, and then compares
what the header commits to against what the body produced.

* `Block.Commitments` is every value the header commits to that the body determines, in the order
  the transition compares them (`execute_block`): the gas used, the transactions root, the state
  root, the receipts root, the logs bloom, the withdrawals root, the blob gas used, the requests
  hash, and (under rules with a block-level access list, EIP-7928) the access list's hash.
  `Block.Commitments.ofPrefix` reads them off the body's final prefix.
* `Block.check` compares the header against the commitments, one field at a time in that order, and
  rejects at the first mismatch with today's reason and text.
* `BlockRun` is a block's run: the fork, the parent chain, the block, its decoded transactions, the
  record of each body operation and the body's final prefix. `BlockRun.run` builds it with
  `Body.run`; `BlockRun.commitments` are the final prefix's.
* `stateTransitionCoreE` is the typed block transition over these: header validation, the ommer
  check, the importer's body (`Body.importer`, a streaming fold), `Block.check`, append.

-/

namespace Jaune

open Jaune

/-! ### Commitments -/



/-! ### The check -/




/-! ### The block run -/

/-- A block's run: the fork, the parent chain, the block, its decoded transactions, each body
operation's record, and the body's final prefix. -/
structure BlockRun : Type where
  fork : Fork
  parent : BlockChain
  block : Block
  transactions : List Transaction
  ops : List OpRun
  final : Body.Prefix

/-- The block environment of a block over its parent (`initBlockEnvironment`). -/
def BlockRun.benv (r : BlockRun) : Benv := initBlockEnvironment r.fork r.parent r.block.header

/-- A run's commitments: its final prefix's, under its fork's rules. -/
def BlockRun.commitments (r : BlockRun) : Block.Commitments :=
  Block.Commitments.ofPrefix r.fork.ruleSet r.final

/-- The block's run: decode the transactions, then run the importer's operations from the empty
prefix over the parent's state, keeping each operation's record. -/
def BlockRun.run (f : Fork) (ch : BlockChain) (block : Block) :
    Except TransitionError BlockRun := do
  let benv := initBlockEnvironment f ch block.header
  let txs ← block.transactions.mapM (decodeTransaction benv.stat.rules)
  let ⟨ops, final⟩ ← Body.run benv (Body.Prefix.init benv.state)
    (Body.ops benv txs block.ommers block.withdrawals)
  pure { fork := f, parent := ch, block := block, transactions := txs, ops := ops, final := final }

/-! ### The block transition -/

/-- **The typed block transition** (`stateTransitionCoreE`): validate the header, check the
ommers, run the body, check the header's commitments, and append the block. -/
def stateTransitionCoreE {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except ε Unit) : Except ε BlockChain := do
  Except.mapError embed (validateHeader f.ruleSet ch block.header)
  checkOmmers ()
  let q ← Except.mapError embed
    (Body.importer (initBlockEnvironment f ch block.header) block.transactions block.ommers block.withdrawals)
  Except.mapError (embed ∘ TransitionError.block) <|
    Block.check block.header (Block.Commitments.ofPrefix f.ruleSet q)
  .ok ⟨appendBlock ch.blocks block, q.state, ch.chainId⟩

end Jaune
