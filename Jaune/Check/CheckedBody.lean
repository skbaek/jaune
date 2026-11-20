-- Check/CheckedBody.lean : the block-environment guards of `Jaune/Check/Transaction.lean` and
-- `Jaune/Check/Machine.lean`, restated over the Checked run layer.
--
-- Check module (see `scripts/layering.json`). Goal `jaune-shape-and-names-v1`, G2b (unit jsn-u87,
-- S0): the guards that build a W1 block environment (`Benv`) -- the `applyBody` bodies, the
-- rewards fold, the block-allowance and blob admission checks, the system-call reservoir, and the
-- transaction-boundary original-state regression -- are restated over `Checked.applyBody`,
-- `Checked.Body.step`/`postOps`, `Checked.checkTransactionGasLimits`/`checkTransactionBlobData`,
-- `Checked.TopLevel.systemInput` and `Checked.Transaction.prepare`, with the same observations and
-- expected values. A guard `benv` maps to the block record `benv.stat.toBlockContext` and the
-- prestate `benv.state` (u82's named map; every guard `Benv` here has empty `createdAccounts`). The
-- old guards stay until the delete commit (precedent: G2a `8840b59b`). The default build compiles
-- this module through `JauneChecks.lean`.
import Jaune.Run.CheckedTransaction

namespace Jaune.Checked

open Jaune

/-! ### The transaction boundary (`Jaune/Check/Machine.lean`, `origStateRegressionOrigVals`)

Regression for the transaction-scoped original state (finding 3.8). Slot `(a, k)` holds 11 in the
block prestate. The first transaction starts on the prestate and so reads 11 as the slot's original
value, then overwrites it with 22; the second starts on the first's output and must read 22. The
W1 guard opened each boundary with `Benv.beginTransaction`; the Checked body opens it by passing
the prefix state to `Transaction.run`, which hands it to `Transaction.prepare` as the original
state. -/

/-- The block record of `(default : Benv).stat`. -/
private def bodyGuardDefaultBlock (fork : Fork := .prague) : BlockContext :=
  { fork, chainId := 0, gasLimit := 0, blockHashes := [], coinbase := 0, number := 0
    baseFeePerGas := 0, timestamp := 0, prevRandao := 0, excessBlobGas := 0
    parentBeaconBlockRoot := 0 }

/-- A free call from a sender distinct from the probed account. -/
private def origStateGuardTx : Jaune.Transaction :=
  { nonce := 0, gasLimit := Gas.transaction, value := 0, data := [], v := 27, r := [], s := []
    type := .legacy 0 (some 0x9999) }

private def origStateGuardAdmitted : Transaction.Admitted :=
  { bout := .init, sender := 0x1234, effectiveGasPrice := 0, blobVersionedHashes := []
    txBlobGasUsed := 0, intrinsicGas := Gas.transaction, calldataFloorGasCost := 0 }

/-- The original value of `(a, k)` a transaction starting on `state` reads. -/
private def origStateGuardRead (state : State) (a : Address) (k : U256) : Option U256 :=
  match Transaction.prepare (bodyGuardDefaultBlock) state origStateGuardAdmitted
      origStateGuardTx with
  | .ok prepared => some ((prepared.input.message.context.tx.originalState.get a).storage.get k)
  | .error _ => none

private def origStateRegressionOrigVals : Option U256 × Option U256 :=
  let a : Address := (0x5678 : Address)
  let k : U256 := Nat.toU256 7
  let prestate : State := State.setStorVal .empty a k (Nat.toU256 11)
  -- transaction 1: starts on the prestate, reads the original value, writes the slot
  let orig1 := origStateGuardRead prestate a k
  let state1 : State := prestate.setStorVal a k (Nat.toU256 22)
  -- transaction 2: starts on the first transaction's output
  let orig2 := origStateGuardRead state1 a k
  ⟨orig1, orig2⟩

#guard origStateRegressionOrigVals = ⟨some (Nat.toU256 11), some (Nat.toU256 22)⟩
-- The same slot, with the boundary opened only once per block, is the defect: the second
-- transaction would have kept reading the block prestate value 11.
#guard origStateRegressionOrigVals.2 ≠ origStateRegressionOrigVals.1

/-! ### Block allowances and blob admission (`Jaune/Check/Transaction.lean:409-452`) -/

private def bodyTxvFails {α : Type} (p : TransactionValidationError → Bool) :
    Except TransactionValidationError α → Bool
  | .error e => p e
  | .ok _ => false

private def bodyFixtureTx : Jaune.Transaction :=
  { nonce := 0, gasLimit := Gas.transaction, value := 0, data := [], v := 27, r := [], s := []
    type := .legacy 10 (some 0) }

/-- The block record of `fixtureTestBenv blockGasLimit`. -/
private def bodyFixtureBlock (blockGasLimit : Nat := 10000000) : BlockContext :=
  { fork := .prague, chainId := 1, gasLimit := blockGasLimit, blockHashes := [], coinbase := 0
    number := 1, baseFeePerGas := 1, timestamp := 0, prevRandao := 0, excessBlobGas := 0
    parentBeaconBlockRoot := 0 }

/-- The block record of `fixtureAmsterdamBenv blockGasLimit`. -/
private def bodyFixtureAmsterdamBlock (blockGasLimit : Nat := 30000000) : BlockContext :=
  { bodyFixtureBlock blockGasLimit with fork := .amsterdam }

private def bodyAmsterdamTxMaxGas : Nat :=
  amsterdamRules.tx.maxGas.getD 0

private def bodyAmsterdamCapacityTx : Jaune.Transaction :=
  { bodyFixtureTx with gasLimit := bodyAmsterdamTxMaxGas + 50, value := 1
                       type := .legacy 10 (some 2) }

private def bodyAmsterdamCapacityBlock : BlockContext :=
  bodyFixtureAmsterdamBlock (bodyAmsterdamTxMaxGas + 100)

private def bodyAmsterdamCapacityOutput : BlockOutput :=
  { BlockOutput.init with blockGasUsed := 100, blockStateGasUsed := 50 }

#guard bodyTxvFails (fun | .gasAllowanceExceeded _ => true | _ => false) <|
  checkTransactionGasLimits (bodyFixtureBlock Gas.transaction) .init
    { bodyFixtureTx with gasLimit := Gas.transaction + 1 }

#guard (checkTransactionGasLimits bodyAmsterdamCapacityBlock
    bodyAmsterdamCapacityOutput bodyAmsterdamCapacityTx).toOption.isSome
#guard bodyTxvFails (fun | .gasAllowanceExceeded _ => true | _ => false) <|
  checkTransactionGasLimits bodyAmsterdamCapacityBlock
    { bodyAmsterdamCapacityOutput with blockGasUsed := 101 } bodyAmsterdamCapacityTx
#guard bodyTxvFails (fun | .gasAllowanceExceeded _ => true | _ => false) <|
  checkTransactionGasLimits bodyAmsterdamCapacityBlock
    { bodyAmsterdamCapacityOutput with blockStateGasUsed := 51 } bodyAmsterdamCapacityTx

#guard bodyTxvFails (fun | .type3BlobCountExceeded _ => true | _ => false) <|
  checkTransactionGasLimits bodyFixtureBlock .init
    { bodyFixtureTx with type := .eip4844 1 1 10 0 [] 1 (List.replicate 10 0) }
#guard bodyTxvFails (fun | .type3ZeroBlobs _ => true | _ => false) <|
  checkTransactionBlobData bodyFixtureBlock
    { bodyFixtureTx with type := .eip4844 1 1 10 0 [] 1 [] } 10
#guard bodyTxvFails (fun | .type3InvalidBlobVersionedHash _ => true | _ => false) <|
  checkTransactionBlobData bodyFixtureBlock
    { bodyFixtureTx with type := .eip4844 1 1 10 0 [] 1 [0] } 10
-- The blob-fee rejection renders its exact observed golden message.
#guard bodyTxvFails
    (fun e => e.render ==
      "InsufficientMaxFeePerBlobGasError : insufficient max fee per blob gas") <|
  checkTransactionBlobData bodyFixtureBlock
    { bodyFixtureTx with type := .eip4844 1 1 10 0 [] 0 [(1 : U256) <<< 248] } 10

/-! ### The system-call reservoir (`Jaune/Check/Transaction.lean:466-471`)

W1 kept the system call's state-gas reservoir on its transaction environment and granted it to the
message; a Checked system call has no transaction environment, and the reservoir is the message's
grant. Both W1 observations are this one. -/

#guard (TopLevel.systemInput bodyFixtureAmsterdamBlock .empty 1 .empty []).message.stateGasGrant
  = amsterdamStateGasRules.systemReservoir

/-! ### The Byzantium body (`Jaune/Check/Transaction.lean:1578-1650`)

A Byzantium-shaped chain: genesis `g`, its child `p`, and a block `b` on `p` that names `o` -- a
second child of `g`, mined by another coinbase -- as its one ommer. The headers are those of
`Jaune/Check/Transaction.lean` (`guardTestHeader`, `guardHeader15`, `guardPowAt`, ...). -/

private def bodyTestHeader : Header := {
  parentHash := 0
  ommersHash := emptyOmmerHash
  coinbase := 0
  stateRoot := 0
  transactionsRoot := 0
  receiptsRoot := 0
  logsBloom := List.replicate 256 (0 : UInt8)
  difficulty := 0
  number := 1
  gasLimit := 30000000
  gasUsed := 0
  timestamp := 0
  extraData := []
  prevRandao := 0
  nonce := 0
  baseFeePerGas := some 7
  withdrawalsRoot := some 0
  blobGasUsed := some 0
  excessBlobGas := some 0
  parentBeaconBlockRoot := some 0
  requestsHash := none
  blockAccessListHash := none
  slotNumber := none
}

private def bodyHeader15 : Header :=
  { bodyTestHeader with
      baseFeePerGas := none, withdrawalsRoot := none, blobGasUsed := none
      excessBlobGas := none, parentBeaconBlockRoot := none }

/-- `ommersListHash`: the keccak of the RLP list of the ommer headers. -/
private def bodyOmmersListHash (ommers : List Header) : U256 :=
  (Rlp.Item.list (ommers.map Header.toRlpItem)).toBytes.keccak

private def bodyPowCoinbase : Address := 0xc0
private def bodyOmmerCoinbase : Address := 0x0e

private def bodyPowAt (parent : Header) (timestamp : Nat) (coinbase : Address) : Header :=
  let child : Header :=
    { bodyHeader15 with
        number := parent.number + 1, timestamp := timestamp,
        parentHash := parent.hash, coinbase := coinbase }
  { child with difficulty := match byzantiumRules.proofOfWork with
      | some pow => expectedDifficulty pow child parent
      | none => 0 }

private def bodyPowGenesis : Header :=
  { bodyHeader15 with number := 0, difficulty := 131072 }
private def bodyPowParent : Header := bodyPowAt bodyPowGenesis 5 bodyPowCoinbase
private def bodyPowOmmer : Header := bodyPowAt bodyPowGenesis 6 bodyOmmerCoinbase
private def bodyPowBlockWith (ommers : List Header) : Header :=
  { bodyPowAt bodyPowParent 20 bodyPowCoinbase with
      ommersHash := bodyOmmersListHash ommers }
private def bodyPowChain : BlockChain :=
  { blocks := [bodyPowGenesis, bodyPowParent].map
      (fun h => { header := h, transactions := [], ommers := [], withdrawals := [] })
    state := .empty
    chainId := 1 }

-- The rewards (EELS `pay_rewards`, Byzantium's 3 ETH), as the body's rewards step pays them: the
-- miner gets `3 + 3/32` ETH for one ommer, and the age-1 ommer's miner `7/8` of 3 ETH. The W1
-- helper folded W1 `Body.step` over `Body.postOps` on the default block environment with the
-- given fork, number and coinbase; this one folds the Checked step over the Checked operations on
-- that environment's block record.
private def bodyRewards (pow : ProofOfWorkRules) (number : Nat) (coinbase : Address)
    (ommers : List Header) (st : State) : State :=
  let fork : Fork := if pow.blockReward = 3 * 10 ^ 18 then .byzantium else .constantinople
  let block : BlockContext := { bodyGuardDefaultBlock fork with number, coinbase }
  match block.rules.proofOfWork with
  | some p =>
    if p.blockReward = pow.blockReward ∧ p.bombDelay = pow.bombDelay then
      match (Body.postOps block 0 ommers []).foldlM (Body.step block)
          (Jaune.Body.Prefix.init st) with
      | .ok q => q.state
      | .error _ => .empty
    else .empty
  | none => .empty

#guard (bodyRewards { blockReward := 3 * 10 ^ 18, bombDelay := 3000000 } 2
    bodyPowCoinbase [bodyPowOmmer] .empty).bal bodyPowCoinbase
  = (3093750000000000000 : Nat).toU256
#guard (bodyRewards { blockReward := 3 * 10 ^ 18, bombDelay := 3000000 } 2
    bodyPowCoinbase [bodyPowOmmer] .empty).bal bodyOmmerCoinbase
  = (2625000000000000000 : Nat).toU256
-- Age 2 pays 6/8; no ommer pays the miner the bare block reward.
#guard (bodyRewards { blockReward := 2 * 10 ^ 18, bombDelay := 5000000 } 3
    bodyPowCoinbase [bodyPowOmmer] .empty).bal bodyOmmerCoinbase
  = (1500000000000000000 : Nat).toU256
#guard (bodyRewards { blockReward := 2 * 10 ^ 18, bombDelay := 5000000 } 3
    bodyPowCoinbase [] .empty).bal bodyPowCoinbase
  = (2 * 10 ^ 18 : Nat).toU256

-- The whole Byzantium body on that block: the two system calls, the withdrawals and the request
-- pass are gated off, so the state the body leaves is exactly the input state plus the rewards --
-- two accounts. `initBlockEnvironment`'s block record is `initBlockContext` and its state the
-- chain's.
private def bodyPowContext : BlockContext :=
  initBlockContext .byzantium bodyPowChain (bodyPowBlockWith [bodyPowOmmer])

#guard (match applyBody bodyPowContext bodyPowChain.state [] [bodyPowOmmer] [] with
  | .ok ⟨st, bout⟩ =>
      st.bal bodyPowCoinbase == (3093750000000000000 : Nat).toU256 &&
      st.bal bodyOmmerCoinbase == (2625000000000000000 : Nat).toU256 &&
      st.toList.length == 2 && bout.requests.isEmpty
  | .error _ => false)

-- The two system-call gates, observed: with a storage-writing contract at both system addresses
-- and no block hashes, Byzantium's body leaves both contracts' storage empty and never asks for a
-- parent hash, while Cancun's runs the beacon-roots call and still never asks for one (its history
-- call is gated off too). `guardSysBenv benv` is the block record of `benv` without block hashes
-- over the system-code state.
private def bodySysCode : ByteArray := ⟨#[0x60, 0x01, 0x60, 0x00, 0x55, 0x00]⟩

private def bodySysState : State :=
  (State.setCode .empty beaconRootsAddress bodySysCode).setCode historyStorageAddress bodySysCode

private def bodySysContext (block : BlockContext) : BlockContext :=
  { block with blockHashes := [] }

#guard (match applyBody (bodySysContext bodyPowContext) bodySysState [] [bodyPowOmmer] [] with
  | .ok ⟨st, _⟩ => (st.get beaconRootsAddress).storage.isEmpty &&
      (st.get historyStorageAddress).storage.isEmpty
  | .error _ => false)
#guard (match applyBody (bodySysContext (initBlockContext .cancun bodyPowChain bodyTestHeader))
    bodySysState [] [] [] with
  | .ok ⟨st, _⟩ => !(st.get beaconRootsAddress).storage.isEmpty &&
      (st.get historyStorageAddress).storage.isEmpty
  | .error _ => false)

-- Under Prague's rules the same body runs every step: the request pass calls the request
-- contracts, which this chain has not deployed.
#guard (match applyBody (initBlockContext .prague bodyPowChain (bodyPowBlockWith []))
    bodyPowChain.state [] [bodyPowOmmer] [] with
  | .error (.block (.systemContractEmpty _)) => true
  | _ => false)

end Jaune.Checked
