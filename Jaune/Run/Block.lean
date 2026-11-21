import Jaune.Run.Message
import Jaune.Run.Prefix
import Jaune.Run.Body

namespace Jaune

open Jaune

/-! ### The block record and transaction admission

Decision 13 at the runner: a block is run against its `BlockContext` and the state of the body's
prefix; the state a transaction starts on is passed explicitly and becomes the transaction
record's `originalState`. Nothing here carries a block environment. -/

/-- The block record a block's frames read, from its fork, its parent chain and its header. -/
def initBlockContext (fork : Fork) (chain : BlockChain) (header : Header) : BlockContext :=
  { fork
    chainId := chain.chainId
    gasLimit := header.gasLimit
    blockHashes := BlockChain.recentBlockHashes chain
    coinbase := header.coinbase
    number := header.number
    -- Absent before London and Cancun respectively, where nothing that reads them is reachable.
    baseFeePerGas := header.baseFeePerGas.getD 0
    timestamp := header.timestamp.toU256
    -- Before the merge `DIFFICULTY` reads the header's difficulty instead of `prevRandao`.
    prevRandao :=
      match fork.ruleSet.proofOfWork with
      | some _ => Nat.toU256 header.difficulty
      | none => header.prevRandao
    excessBlobGas := header.excessBlobGas.getD 0
    parentBeaconBlockRoot := header.parentBeaconBlockRoot.getD 0
    slotNumber := header.slotNumber.getD 0 }

















namespace Body













end Body


/-- A block's decoded transactions and ordered Checked operations over its parent. -/
structure BlockRun where
  fork : Fork
  parent : BlockChain
  block : Block
  transactions : List Jaune.Transaction
  operationRuns : List BodyOperationRun
  final : Jaune.Body.Prefix

/-- The block record the run's frames read. -/
def BlockRun.context (run : BlockRun) : BlockContext :=
  initBlockContext run.fork run.parent run.block.header

def BlockRun.run (fork : Fork) (parent : BlockChain) (block : Block) : Except TransitionError BlockRun := do
  let context := initBlockContext fork parent block.header
  let decoded ← block.transactions.mapM (decodeTransaction context.rules)
  let (ops, final) ← Body.run context (Jaune.Body.Prefix.init parent.state)
    (Body.operations context decoded block.ommers block.withdrawals)
  pure ⟨fork, parent, block, decoded, ops, final⟩

/-- Validate the header and ommers, execute the Checked body, then check its commitments. -/
def stateTransitionCoreTyped {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block) (checkOmmers : Unit → Except ε Unit) :
    Except ε BlockChain := do
  Except.mapError embed (validateHeader f.ruleSet ch block.header)
  checkOmmers ()
  let q ← Except.mapError embed
    (Body.importer (initBlockContext f ch block.header) ch.state block.transactions block.ommers
      block.withdrawals)
  Except.mapError (embed ∘ TransitionError.block) <|
    Block.check block.header (Block.Commitments.ofPrefix f.ruleSet q)
  .ok ⟨appendBlock ch.blocks block, q.state, ch.chainId⟩

end Jaune
