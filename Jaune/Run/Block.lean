import Jaune.Run.Body

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
* `E.stateTransitionCoreE` is the typed block transition over these: header validation, the ommer
  check, the importer's body (`Body.importer`, a streaming fold), `Block.check`, append.

Staged under `Jaune.Staging` (the transition under `Jaune.Staging.E`, since cut D staged
`Jaune.Staging.stateTransitionCoreE`); the bridges are in gate G2a's bridge modules.
-/

namespace Jaune

open Jaune

/-! ### Commitments -/

/-- Every header value the body determines, in the order the transition compares them. -/
structure Block.Commitments : Type where
  /-- The block's gas used: the larger of execution gas and (Amsterdam) state gas. -/
  gasUsed : Nat
  transactionsRoot : U256
  stateRoot : U256
  receiptsRoot : U256
  logsBloom : Bytes
  withdrawalsRoot : U256
  blobGasUsed : Nat
  /-- `none` exactly under rules without the field (before Prague). -/
  requestsHash : Option U256
  /-- EIP-7928: `none` exactly under rules without a block-level access list. -/
  blockAccessListHash : Option U256

/-- The commitments of a body's final prefix, under `rules`. -/
def Block.Commitments.ofPrefix (rules : ForkRules) (q : Body.Prefix) : Block.Commitments :=
  { gasUsed := max q.executionGasUsed q.stateGasUsed
    transactionsRoot := getTransactionsRoot q.toBlockOutput
    stateRoot := q.state.root
    receiptsRoot := getReceiptRoot q.toBlockOutput
    logsBloom := Jaune.logsBloom q.logs
    withdrawalsRoot := getWithdrawalsRoot q.toBlockOutput
    blobGasUsed := q.blobGasUsed
    requestsHash :=
      if rules.header.requestsHash then some (computeRequestsHash q.requests) else none
    blockAccessListHash := rules.blockAccessListRules.map fun _ => q.blockAccessList.hash }

/-! ### The check -/

/-- The header against the commitments of `execute_block`'s comparisons, in order; the first
mismatch rejects the block. The withdrawals root and the blob gas used are compared only where the
header carries the field (`validateHeader` has tied its presence to the rules). -/
def Block.checkCommitments (header : Header) (c : Block.Commitments) :
    Except BlockValidationError Unit := do
  if c.gasUsed ≠ header.gasUsed then
    .error <| .gasUsedMismatch <| .text
      s!"computed block gas used = {c.gasUsed} ≠ \
         header block gas used = {header.gasUsed}"
  if c.transactionsRoot ≠ header.transactionsRoot then
    .error <| .transactionsRoot <| .text
      s!"computed transactions root = {c.transactionsRoot} \
         ≠ header transactions root = {header.transactionsRoot}"
  if c.stateRoot ≠ header.stateRoot then
    .error <| .stateRoot <| .text
      s!"computed state root = {c.stateRoot} ≠ \
         header state root = {header.stateRoot}"
  if c.receiptsRoot ≠ header.receiptsRoot then
    .error <| .receiptsRoot <| .text
      s!"computed receipts root = {c.receiptsRoot} ≠ \
         header receipts root = {header.receiptsRoot}"
  if c.logsBloom ≠ header.logsBloom then
    .error <| .logBloom <| .text
      s!"computed logs bloom ≠ header logs bloom"
  if header.withdrawalsRoot.any (· != c.withdrawalsRoot) then
    .error <| .withdrawalsRoot <| .text
      s!"computed withdrawals root = {c.withdrawalsRoot} ≠ \
         header withdrawals root = {header.withdrawalsRoot.getD 0}"
  if header.blobGasUsed.any (· != c.blobGasUsed) then
    .error <| .blobGasUsed <| .text
      s!"computed blob gas used = {c.blobGasUsed} ≠ \
         header blob gas used = {header.blobGasUsed.getD 0}"
  if c.requestsHash ≠ header.requestsHash then
    .error <| .requestsHash <| .text
      s!"computed requests hash = {c.requestsHash.getD 0} ≠ \
         header requests hash = {header.requestsHash}"

/-- EIP-7928: the header's access-list hash against the computed one, under rules that have one. -/
def Block.checkAccessListHash (header : Header) (c : Block.Commitments) :
    Except BlockValidationError Unit :=
  match c.blockAccessListHash with
  | none => .ok ()
  | some hash =>
    if some hash ≠ header.blockAccessListHash then
      .error <| .blockAccessListHash hash <| .text
        s!"computed block access list hash = {hash} ≠ \
           header block access list hash = {header.blockAccessListHash}"
    else .ok ()

/-- **The block check**: the header against the commitments, in order (`execute_block`'s
comparisons, then the access-list hash); the first mismatch rejects the block with its reason. -/
def Block.check (header : Header) (c : Block.Commitments) : Except BlockValidationError Unit := do
  Block.checkCommitments header c
  Block.checkAccessListHash header c

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
