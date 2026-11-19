import Jaune.MessageCall.CheckedContext

/-!
# Bridge: the shared call context and the checked one (goal `jaune-shape-and-names-v1`, G2b, decision 13)

`CallContext.toChecked` is the total forgetful map from the shared `CallContext` (with its
`TenvStat` and `BenvStat`, unedited while the `Devm` interpreter waits as the old side, 3.1) to
`Checked.CallContext`. The transaction's grant fields (`gas`, `stateGasReservoir`,
`accessListAddresses`, `accessListStorageKeys`, `auths`) and `indexInBlock`/`txHash` are dropped:
the decision-13 environment walk found no frame-side reader of any of them. The original state
moves from the block record to the transaction record.

The squares state that every read a step makes through the checked context is the read it made
through the shared one, so a body retyped onto `Checked.CallContext` agrees with its old self on
`toChecked ctx`.
-/

namespace Jaune

namespace CallContext

variable (c : CallContext)

@[simp] theorem toChecked_caller : c.toChecked.caller = c.caller := rfl
@[simp] theorem toChecked_recipient : c.toChecked.recipient = c.recipient := rfl
@[simp] theorem toChecked_value : c.toChecked.value = c.value := rfl
@[simp] theorem toChecked_calldata : c.toChecked.calldata = c.calldata := rfl
@[simp] theorem toChecked_code : c.toChecked.code = c.code := rfl
@[simp] theorem toChecked_depthLeft : c.toChecked.depthLeft = c.depthLeft := rfl
@[simp] theorem toChecked_isStatic : c.toChecked.isStatic = c.isStatic := rfl
@[simp] theorem toChecked_origin : c.toChecked.tx.origin = c.tx.origin := rfl
@[simp] theorem toChecked_gasPrice : c.toChecked.tx.gasPrice = c.tx.gasPrice := rfl
@[simp] theorem toChecked_blobVersionedHashes :
    c.toChecked.tx.blobVersionedHashes = c.tx.blobVersionedHashes := rfl
/-- The original state `SSTORE` compares against moves from the block to the transaction. -/
@[simp] theorem toChecked_originalState : c.toChecked.tx.originalState = c.block.origState := rfl
@[simp] theorem toChecked_rules : c.toChecked.block.rules = c.block.rules := rfl
@[simp] theorem toChecked_fork : c.toChecked.block.fork = c.block.fork := rfl
@[simp] theorem toChecked_chainId : c.toChecked.block.chainId = c.block.chainId := rfl
/-- `GASLIMIT` reads the header's `gasLimit`, which the shared record calls `blockGasLimit`. -/
@[simp] theorem toChecked_gasLimit : c.toChecked.block.gasLimit = c.block.blockGasLimit := rfl
@[simp] theorem toChecked_blockHashes : c.toChecked.block.blockHashes = c.block.blockHashes := rfl
@[simp] theorem toChecked_coinbase : c.toChecked.block.coinbase = c.block.coinbase := rfl
@[simp] theorem toChecked_number : c.toChecked.block.number = c.block.number := rfl
@[simp] theorem toChecked_baseFeePerGas : c.toChecked.block.baseFeePerGas = c.block.baseFeePerGas := rfl
/-- `TIMESTAMP` reads the header's `timestamp`, which the shared record calls `time`. -/
@[simp] theorem toChecked_timestamp : c.toChecked.block.timestamp = c.block.time := rfl
@[simp] theorem toChecked_prevRandao : c.toChecked.block.prevRandao = c.block.prevRandao := rfl
@[simp] theorem toChecked_excessBlobGas : c.toChecked.block.excessBlobGas = c.block.excessBlobGas := rfl
@[simp] theorem toChecked_parentBeaconBlockRoot :
    c.toChecked.block.parentBeaconBlockRoot = c.block.parentBeaconBlockRoot := rfl
@[simp] theorem toChecked_slotNumber : c.toChecked.block.slotNumber = c.block.slotNumber := rfl

/-- The map forgets exactly the transaction's grant fields and `indexInBlock`/`txHash`: two shared
contexts that agree on every other field have the same image. -/
theorem toChecked_eq_of_reads {c d : CallContext} (hcaller : c.caller = d.caller)
    (hrecipient : c.recipient = d.recipient) (hvalue : c.value = d.value)
    (hcalldata : c.calldata = d.calldata) (hcode : c.code = d.code)
    (hdepth : c.depthLeft = d.depthLeft) (hstatic : c.isStatic = d.isStatic)
    (horigin : c.tx.origin = d.tx.origin) (hprice : c.tx.gasPrice = d.tx.gasPrice)
    (hblobs : c.tx.blobVersionedHashes = d.tx.blobVersionedHashes) (hblock : c.block = d.block) :
    c.toChecked = d.toChecked := by
  unfold toChecked TenvStat.toTransactionContext
  rw [hcaller, hrecipient, hvalue, hcalldata, hcode, hdepth, hstatic, horigin, hprice, hblobs, hblock]

end CallContext

end Jaune
