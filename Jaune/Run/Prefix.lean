import Jaune.Transaction.Parts

/-!
# A block body's prefix, its operations and the block checks (goal `jaune-shape-and-names-v1`, G2b N4-0)

`Body.Prefix` (what a block body has produced so far), `BodyOp` and the transaction operations of
a body, `creditAll`, and the block's commitments and header checks. Extracted unchanged from the
`Devm`-era `Jaune.Run` modules.
-/

section
open Jaune
namespace Jaune
/-- What a block body has produced so far: the state and `BlockOutput`'s carrier. -/
structure Body.Prefix : Type where
  state : State
  /-- Execution gas used by the block (`BlockOutput.blockGasUsed`). -/
  executionGasUsed : Nat
  /-- Amsterdam's state gas used by the block (`BlockOutput.blockStateGasUsed`). -/
  stateGasUsed : Nat
  /-- Sender-facing gas after refunds, for the receipts. -/
  cumulativeGasUsed : Nat
  blobGasUsed : Nat
  transactionsTrie : Std.TreeMap Bytes Transaction compare
  receiptsTrie : Std.TreeMap Bytes (Fin 5 × Receipt) compare
  receiptKeys : List Bytes
  /-- The block's logs (`BlockOutput.blockLogs`). -/
  logs : List Log
  withdrawalsTrie : Std.TreeMap Bytes Withdrawal compare
  requests : List Bytes
  /-- EIP-7928: the block-level access-list builder (`BlockOutput.blockAccessListBuilder`). -/
  blockAccessListBuilder : BlockAccessListBuilder
  /-- EIP-7928: the built list (`BlockOutput.blockAccessList`). -/
  blockAccessList : BlockAccessList
end Jaune
end

section
open Jaune
namespace Jaune
/-- The block output a prefix carries. -/
def Body.Prefix.toBlockOutput (p : Body.Prefix) : BlockOutput :=
  { blockGasUsed := p.executionGasUsed
    blockStateGasUsed := p.stateGasUsed
    cumulativeGasUsed := p.cumulativeGasUsed
    transactionsTrie := p.transactionsTrie
    receiptsTrie := p.receiptsTrie
    receiptKeys := p.receiptKeys
    blockLogs := p.logs
    withdrawalsTrie := p.withdrawalsTrie
    blobGasUsed := p.blobGasUsed
    requests := p.requests
    blockAccessListBuilder := p.blockAccessListBuilder
    blockAccessList := p.blockAccessList }
end Jaune
end

section
open Jaune
namespace Jaune
/-- The prefix of a state and a block output. -/
def Body.Prefix.ofBlockOutput (state : State) (bout : BlockOutput) : Body.Prefix :=
  { state := state
    executionGasUsed := bout.blockGasUsed
    stateGasUsed := bout.blockStateGasUsed
    cumulativeGasUsed := bout.cumulativeGasUsed
    blobGasUsed := bout.blobGasUsed
    transactionsTrie := bout.transactionsTrie
    receiptsTrie := bout.receiptsTrie
    receiptKeys := bout.receiptKeys
    logs := bout.blockLogs
    withdrawalsTrie := bout.withdrawalsTrie
    requests := bout.requests
    blockAccessListBuilder := bout.blockAccessListBuilder
    blockAccessList := bout.blockAccessList }
end Jaune
end

section
open Jaune
namespace Jaune
/-- The empty prefix over a state. -/
def Body.Prefix.init (state : State) : Body.Prefix := Body.Prefix.ofBlockOutput state BlockOutput.init
end Jaune
end

section
open Jaune
namespace Jaune
/-- The body's result as the importer returned it: the state and the block output. -/
def Body.Prefix.output (p : Body.Prefix) : State × BlockOutput := (p.state, p.toBlockOutput)
end Jaune
end

section
open Jaune
namespace Jaune
@[simp] theorem Body.Prefix.toBlockOutput_ofBlockOutput (state : State) (bout : BlockOutput) :
    (Body.Prefix.ofBlockOutput state bout).toBlockOutput = bout := rfl
end Jaune
end

section
open Jaune
namespace Jaune
@[simp] theorem Body.Prefix.state_ofBlockOutput (state : State) (bout : BlockOutput) :
    (Body.Prefix.ofBlockOutput state bout).state = state := rfl
end Jaune
end

section
open Jaune
namespace Jaune
@[simp] theorem Body.Prefix.ofBlockOutput_toBlockOutput (p : Body.Prefix) :
    Body.Prefix.ofBlockOutput p.state p.toBlockOutput = p := rfl
end Jaune
end

section
open Jaune
namespace Jaune
/-- One operation of a block body. -/
inductive BodyOp : Type where
  /-- An unchecked system call to `address` with `data` (whose failure fails the body before the
  call), incorporated into the block access list at `index`. -/
  | systemCall (address : Address) (data : Except TransitionError Bytes) (index : Nat)
  /-- A transaction at `index`. -/
  | transaction (tx : Transaction) (index : Nat)
  /-- The withdrawals, incorporated into the block access list at `index`. -/
  | withdrawals (ws : List Withdrawal) (index : Nat)
  /-- The deposit requests parsed from the receipts so far (EIP-6110). -/
  | depositRequests
  /-- A checked request call of request type `type` to `address`, incorporated at `index`. -/
  | requestCall (type : UInt8) (address : Address) (index : Nat)
  /-- Proof-of-work rewards: `minerReward` to `coinbase`, then each credit in turn. -/
  | rewards (coinbase : Address) (minerReward : Nat) (credits : List (Address × Nat))
  /-- Build the block access list from the builder. -/
  | buildAccessList
  /-- The block access list's item limit (`validate_block_access_list_gas_limit`). -/
  | checkAccessListLimit
end Jaune
end

section
open Jaune
namespace Jaune
/-- Credit each `(address, amount)` in turn (`create_ether`). -/
def creditAll (credits : List (Address × Nat)) (state : State) : State :=
  credits.foldl (fun acc c => acc.addBal c.1 c.2.toU256) state
end Jaune
end

section
open Jaune
namespace Jaune
/-- The transactions, each at its position. -/
def Body.transactionOps (txs : List Transaction) : List BodyOp :=
  txs.putIndex.map fun ⟨i, tx⟩ => .transaction tx i
end Jaune
end

section
open Jaune
namespace Jaune
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
end Jaune
end

section
open Jaune
namespace Jaune
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
end Jaune
end

section
open Jaune
namespace Jaune
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
end Jaune
end

section
open Jaune
namespace Jaune
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
end Jaune
end

section
open Jaune
namespace Jaune
/-- **The block check**: the header against the commitments, in order (`execute_block`'s
comparisons, then the access-list hash); the first mismatch rejects the block with its reason. -/
def Block.check (header : Header) (c : Block.Commitments) : Except BlockValidationError Unit := do
  Block.checkCommitments header c
  Block.checkAccessListHash header c
end Jaune
end

section
open Jaune
namespace Jaune
/-- A block check that passes compared the header's state root against the computed one. -/
theorem Block.check_stateRoot {header : Header} {c : Block.Commitments}
    (h : Block.check header c = .ok ()) : c.stateRoot = header.stateRoot := by
  by_contra hne
  revert h
  unfold Block.check Block.checkCommitments
  by_cases h1 : c.gasUsed ≠ header.gasUsed <;>
    by_cases h2 : c.transactionsRoot ≠ header.transactionsRoot <;>
    simp [h1, h2, hne, bind, Except.bind]
end Jaune
end

section
open Jaune
namespace Jaune
/-- Crediting balances in turn keeps a state canonical. -/
theorem State.Canonical.creditAll {state : State} (h : state.Canonical)
    (credits : List (Address × Nat)) : (Jaune.creditAll credits state).Canonical := by
  unfold Jaune.creditAll
  induction credits generalizing state with
  | nil => exact h
  | cons c cs ih => exact ih (State.Canonical.addBal h _ _)
end Jaune
end
