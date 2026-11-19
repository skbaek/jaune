import Jaune.Bridge.G2a.Old.Message

section
open Jaune
namespace Jaune
/-- Run one top-level Amsterdam message call: prepare the machine, settle a
preparation failure, or run the top frame whose checkpoint is the prepared state
and render its result. Amsterdam-only. -/
def Bridge.G2a.Old.processTopLevelAmsterdam (state : StateGasRules) (msg : Msg) (isCreate : Bool) :
    Except EvmError (State × Bridge.G2a.Old.MessageCallOutput) :=
  match prepareTopLevelAmsterdam state msg with
  | .error ⟨error, devm⟩ => Bridge.G2a.Old.settleTopLevelPreparationFailure msg error devm
  | .ok ⟨msg, devm⟩ => do
    let f : Frame := ⟨Message.ofTop msg isCreate, Frame.State.ofDevm devm⟩
    let r ← (Frame.runTop f).mapError Fault.toEvmError
    Bridge.G2a.Old.Frame.outputAmsterdam f r
end Jaune
end

section
open Jaune
namespace Jaune
def Bridge.G2a.Old.processMessageCall.create (msg : Msg) :
    Except EvmError (State × Bridge.G2a.Old.MessageCallOutput) := do
  match msg.benv.stat.rules.stateGas with
  | none =>
    if accountHasCodeOrNonce msg.benv.state msg.currentTarget then
      return ⟨msg.benv.state,
        { gasLeft := 0, refundCounter := 0, logs := [],
          accountsToDelete := .emptyWithCapacity,
          error := .some (.halt (.addressCollision .none)), returnData := [] }⟩
    else
      let f := Frame.ofTop msg true
      let r ← (Frame.runTop f).mapError Fault.toEvmError
      Bridge.G2a.Old.Frame.output f 0 r
  | some state => Bridge.G2a.Old.processTopLevelAmsterdam state msg true
end Jaune
end

section
open Jaune
namespace Jaune
def Bridge.G2a.Old.processMessageCall.call (msg : Msg) :
    Except EvmError (State × Bridge.G2a.Old.MessageCallOutput) := do
  match msg.benv.stat.rules.stateGas with
  | none =>
    let ⟨delegated, authorizationRefund⟩ ← TopLevel.applyAuthorizations msg
    let f := Frame.ofTop (TopLevel.resolveCodeDelegation delegated) false
    let r ← (Frame.runTop f).mapError Fault.toEvmError
    Bridge.G2a.Old.Frame.output f authorizationRefund r
  | some state => Bridge.G2a.Old.processTopLevelAmsterdam state msg false
end Jaune
end

section
open Jaune
namespace Jaune
def Bridge.G2a.Old.processMessageCall (msg : Msg) :
    Except EvmError (State × Bridge.G2a.Old.MessageCallOutput) := do
  if msg.target.isNone then
    Bridge.G2a.Old.processMessageCall.create msg
  else
    Bridge.G2a.Old.processMessageCall.call msg
end Jaune
end

section
open Jaune
namespace Jaune
def Bridge.G2a.Old.processTransaction
  (benv: Benv) (bout : BlockOutput)
  (tx: Transaction) (index : Nat) : Except TransitionError (State × BlockOutput) := do
  -- NOTE: linearized into a straight `let ← .ok (…)` / `let := …` chain
  -- (no `mut`/`for`) so the block inverts cleanly with `of_bind_eq_ok` and the
  -- `bout` bookkeeping stays opaque.  Definitionally equal to the previous
  -- `mut`/`for` form except that the final account-deletion `for` is expressed
  -- as `foldl`, which agrees because `destroyAccount` commutes over the
  -- distinct addresses of the `accountsToDelete` set.
  let benv := benv.beginTransaction
  let bout ← .ok {bout with
    transactionsTrie := bout.transactionsTrie.insert (Rlp.Item.bytes index.toBytes).toBytes tx}
  let validationSender : Address ← recoverValidationSender benv tx
  let ⟨intrinsicGas, calldataFloorGasCost⟩ ←
    Except.mapError TransitionError.transaction
      (validateTransaction benv.stat.rules tx validationSender)
  let ⟨
    sender,
    effectiveGasPrice,
    blobVersionedHashes,
    txBlobGasUsed
  ⟩ ← checkTransaction benv bout tx
  let blobGasFee :=
    if tx.isEip4844
    then calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
    else 0
  let effectiveGasFee := tx.gasLimit * effectiveGasPrice
  let allocation := allocateEvmGas benv.stat.rules tx.gasLimit intrinsicGas
  let state : State := benv.state.incrNonce sender
  let state ← (state.subBal sender (effectiveGasFee + blobGasFee).toU256).toExcept
    (TransitionError.internal (.invariant (.text "balance underflow")))
  -- EIP-3651 (Shanghai) warms the coinbase; before it only the access list is
  -- pre-warmed.
  let preaccessedAddresses : AdrSet :=
    if benv.stat.rules.transactionRules.warmCoinbase then
    .ofList (benv.stat.coinbase :: tx.accessList.map Prod.fst)
    else .ofList (tx.accessList.map Prod.fst)
  let preaccessedStorageKeys : KeySet :=
    .ofList (tx.accessList.map <| λ ⟨adr, keys⟩ => keys.map (⟨adr, ·⟩)).flatten
  let tenv : Tenv := {
    transientStorage := .empty
    stat := {
      origin := sender
      gasPrice := effectiveGasPrice
      gas := allocation.executionGas
      stateGasReservoir := allocation.stateGasReservoir
      accessListAddresses := preaccessedAddresses
      accessListStorageKeys := preaccessedStorageKeys
      blobVersionedHashes := blobVersionedHashes
      auths := tx.authorizationList
      indexInBlock := index
      txHash := transactionHash tx
    }
  }
  let msg ← prepareMessage {benv with state := state} tenv tx
  let ⟨state, txOutput⟩ ← Except.mapError TransitionError.vm (Bridge.G2a.Old.processMessageCall msg)
  let refundCounter : Nat ←
    (Int.toNat? txOutput.refundCounter).toExcept
      (TransitionError.internal (.invariant (.text "refund counter is negative")))
  let settlement :=
    settleTransactionGas benv.stat.rules tx.gasLimit calldataFloorGasCost
      txOutput.gasLeft txOutput.stateGasLeft refundCounter txOutput.stateGasUsed
  let gasRefundAmount : Nat :=
    settlement.gasLeft * effectiveGasPrice
  let priorityFeePerGas := effectiveGasPrice - benv.stat.baseFeePerGas
  let transactionFee := settlement.gasUsed * priorityFeePerGas
  let state := state.addBal sender gasRefundAmount.toU256
  let storageWrites :=
    if (state.get sender).isEmpty then txOutput.storageWrites.eraseAddress sender
    else txOutput.storageWrites
  let state := state.addBal benv.stat.coinbase transactionFee.toU256
  let storageWrites :=
    if (state.get benv.stat.coinbase).isEmpty then storageWrites.eraseAddress benv.stat.coinbase
    else storageWrites
  let storageWrites := txOutput.accountsToDelete.toList.foldl
    (fun writes a => writes.eraseAddress a) storageWrites
  let state := settleSelfdestructs benv.stat.rules
    txOutput.accountsToDelete.toList state
  -- EIP-161: `destroy_touched_empty_accounts` (Spurious Dragon to Gray Glacier).
  let state := sweepTouchedAccounts benv.stat.rules
    txOutput.touchedAccounts.toList state
  let bout ← .ok (bout.withGasSettlement settlement txBlobGasUsed)
  let receipt :=
    makeReceipt tx txOutput.error bout.cumulativeGasUsed txOutput.logs
  let receiptKey : Bytes := Rlp.Item.toBytes <| .bytes index.toBytes
  let bout ← .ok {bout with
    receiptKeys := bout.receiptKeys ++ [receiptKey]
    receiptsTrie := bout.receiptsTrie.insert receiptKey receipt
    blockLogs := bout.blockLogs ++ txOutput.logs}
  -- EIP-7928: `incorporate_tx_into_block` at `index + 1`, after the
  -- self-destruct settlement: surviving explicit storage writes and account
  -- changes, plus reads and the transaction-level ones --
  -- the sender (`check_transaction`, `update_sender_state`, the refund) and
  -- the coinbase (`disburse_gas_fees` credits it even a zero fee).
  let bal := match benv.stat.rules.blockAccessListRules with
    | none => bout.blockAccessListBuilder
    | some _ => bout.blockAccessListBuilder.incorporate (index + 1) benv.state state
        (sender :: benv.stat.coinbase :: txOutput.accountReads.toList)
        txOutput.storageReads.toList storageWrites.toList
  .ok ⟨state, {bout with blockAccessListBuilder := bal}⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- Under a legacy schedule, the real transaction producer preserves the
legacy block-counter relation through its settlement and receipt updates. -/
theorem Bridge.G2a.Old.processTransaction_legacyGasAccounting {benv : Benv}
    (hnone : benv.stat.rules.stateGas = none) {bout : BlockOutput}
    (hb : bout.LegacyGasAccounting) {tx : Transaction} {index : Nat} {p}
    (hp : Bridge.G2a.Old.processTransaction benv bout tx index = .ok p) :
    p.2.LegacyGasAccounting := by
  unfold Bridge.G2a.Old.processTransaction at hp
  obtain ⟨b1, hb1, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨validationSender, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨ig, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨ck, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨st1, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨msg, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨rc, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨b2, hb2, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨b3, hb3, hp⟩ := Except.bind_eq_ok hp
  simp only [Except.ok.injEq] at hb1 hb2 hb3
  have hb1' : b1.LegacyGasAccounting := by
    rw [← hb1]
    exact hb
  have hb2' : b2.LegacyGasAccounting := by
    rw [← hb2]
    exact BlockOutput.LegacyGasAccounting.withGasSettlement hb1'
      (settleTransactionGas_none_invariants hnone _ _ _ _ _ _) _
  have hb3' : b3.LegacyGasAccounting := by
    rw [← hb3]
    exact hb2'
  cases hp
  exact hb3'
end Jaune
end

section
open Jaune
namespace Jaune
private theorem Bridge.G2a.Old.frameOutput_canonical {f : Frame} {a : Nat} {r : Frame.Result}
    (hw : (f.worldAfter r).Canonical) {p} (hp : Bridge.G2a.Old.Frame.output f a r = .ok p) : State.Canonical p.1 := by
  unfold Bridge.G2a.Old.Frame.output at hp
  obtain ⟨refund, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact hw.1
end Jaune
end

section
open Jaune
namespace Jaune
private theorem Bridge.G2a.Old.frameOutputAmsterdam_canonical {f : Frame} {r : Frame.Result}
    (hw : (f.worldAfter r).Canonical) {p} (hp : Bridge.G2a.Old.Frame.outputAmsterdam f r = .ok p) :
    State.Canonical p.1 := by
  unfold Bridge.G2a.Old.Frame.outputAmsterdam at hp
  obtain ⟨refund, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact hw.1
end Jaune
end

section
open Jaune
namespace Jaune
private theorem Bridge.G2a.Old.runTopOutput_canonical {f : Frame} (hf : f.Canonical)
    {k : Frame.Result → Except EvmError (State × Bridge.G2a.Old.MessageCallOutput)}
    (hk : ∀ r, (f.worldAfter r).Canonical → ∀ p, k r = .ok p → State.Canonical p.1) {p}
    (hp : ((Frame.runTop f).mapError Fault.toEvmError >>= k) = .ok p) :
    State.Canonical p.1 := by
  obtain ⟨r, hr, hp⟩ := Except.bind_eq_ok hp
  cases hrun : Frame.runTop f with
  | error e => rw [hrun] at hr; cases hr
  | ok r' =>
    rw [hrun] at hr
    cases hr
    exact hk r (Frame.runTop_canonical hf hrun) p hp
end Jaune
end

section
open Jaune
namespace Jaune
private theorem Bridge.G2a.Old.processTopLevelAmsterdam_canonical {state : StateGasRules}
    {msg : Msg} (hm : msg.Canonical) (isCreate : Bool) {p}
    (hp : Bridge.G2a.Old.processTopLevelAmsterdam state msg isCreate = .ok p) :
    State.Canonical p.1 := by
  unfold Bridge.G2a.Old.processTopLevelAmsterdam at hp
  have hprepare := prepareTopLevelAmsterdam_canonical (state := state) hm
  cases hprep : prepareTopLevelAmsterdam state msg with
  | error failure =>
    rw [hprep] at hp
    obtain ⟨error, devm⟩ := failure
    cases error <;> simp only [Bridge.G2a.Old.settleTopLevelPreparationFailure] at hp <;> cases hp
    exact hm.1.1
  | ok prepared =>
    rw [hprep] at hp hprepare
    obtain ⟨preparedMsg, preparedDevm⟩ := prepared
    exact Bridge.G2a.Old.runTopOutput_canonical
      (Frame.prepared_canonical hprepare.2 hprepare.1 isCreate)
      (fun _ hw _ hk => Bridge.G2a.Old.frameOutputAmsterdam_canonical hw hk) hp
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.processMessageCall.create_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : Bridge.G2a.Old.processMessageCall.create msg = .ok p) :
    State.Canonical p.1 := by
  unfold Bridge.G2a.Old.processMessageCall.create at hp
  dsimp only at hp
  split at hp
  · split at hp
    · cases hp; exact h.1.1
    · exact Bridge.G2a.Old.runTopOutput_canonical (Frame.ofTop_canonical h true)
        (fun _ hw _ hk => Bridge.G2a.Old.frameOutput_canonical hw hk) hp
  · exact Bridge.G2a.Old.processTopLevelAmsterdam_canonical h true hp
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.processMessageCall.call_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : Bridge.G2a.Old.processMessageCall.call msg = .ok p) :
    State.Canonical p.1 := by
  unfold Bridge.G2a.Old.processMessageCall.call at hp
  dsimp only at hp
  split at hp
  · obtain ⟨pair, hpair, hp⟩ := Except.bind_eq_ok hp
    obtain ⟨delegated, refund⟩ := pair
    have hm := TopLevel.applyAuthorizations_canonical h hpair
    exact Bridge.G2a.Old.runTopOutput_canonical
      (Frame.ofTop_canonical (TopLevel.resolveCodeDelegation_canonical hm) false)
      (fun _ hw _ hk => Bridge.G2a.Old.frameOutput_canonical hw hk) hp
  · exact Bridge.G2a.Old.processTopLevelAmsterdam_canonical h false hp
end Jaune
end

section
open Jaune
namespace Jaune
/-- A successful message call leaves a canonical state, for both the create
and the call route. -/
theorem Bridge.G2a.Old.processMessageCall_canonical {msg : Msg} (h : msg.Canonical)
    {p} (hp : Bridge.G2a.Old.processMessageCall msg = .ok p) : State.Canonical p.1 := by
  unfold Bridge.G2a.Old.processMessageCall at hp
  split at hp
  · exact Bridge.G2a.Old.processMessageCall.create_canonical h hp
  · exact Bridge.G2a.Old.processMessageCall.call_canonical h hp
end Jaune
end

section
open Jaune
namespace Jaune
/-- A successful transaction leaves a canonical state: the fee movements go
through `incrNonce`/`subBal`/`addBal`, the call itself through
`processMessageCall`, and settlement follows the fork's SELFDESTRUCT rule. -/
theorem Bridge.G2a.Old.processTransaction_canonical {benv : Benv} (h : benv.Canonical)
    {bout : BlockOutput} {tx : Transaction} {index : Nat} {p}
    (hp : Bridge.G2a.Old.processTransaction benv bout tx index = .ok p) :
    State.Canonical p.1 := by
  unfold Bridge.G2a.Old.processTransaction at hp
  obtain ⟨b1, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨validationSender, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨ig, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨ck, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨st1, hst1, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨msg, hmsg, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨rc, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨b2, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨b3, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  have hst1c : st1.Canonical :=
    State.Canonical.subBal
      (by exact State.Canonical.incrNonce (by exact h.1) _)
      (Option.toExcept_eq_ok hst1)
  have hmsgc : msg.Canonical :=
    prepareMessage_canonical (by exact ⟨hst1c, h.1⟩)
      (by exact TransientStorage.canonical_empty) hmsg
  have hqc := Bridge.G2a.Old.processMessageCall_canonical hmsgc (Except.mapError_eq_ok_iff.mp hq)
  exact State.Canonical.sweepTouchedAccounts (State.Canonical.settleSelfdestructs
    (State.Canonical.addBal (State.Canonical.addBal hqc _ _) _ _) _ _) _ _
end Jaune
end
