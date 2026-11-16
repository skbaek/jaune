import JauneConsensus.Signing
import JauneConsensus.Ctx

/-!
# Deposit helpers shared by block and epoch processing

`get_validator_from_deposit`, `set_or_append_list`, `add_validator_to_registry` and
`is_valid_deposit_signature` (`specs/{phase0,altair,electra}/beacon-chain.md`), used by
`apply_deposit` (block processing) and `process_pending_deposits` (epoch processing).
-/

namespace JauneConsensus
open Jaune (Bytes B256)

variable {P : Preset} {f : CFork}

/-- `get_validator_from_deposit`: Electra caps the effective balance at
`get_max_effective_balance(validator)` (`specs/electra/beacon-chain.md`); before Electra at
`MAX_EFFECTIVE_BALANCE` (`specs/phase0/beacon-chain.md`). -/
def getValidatorFromDeposit (P : Preset) (f : CFork) (pubkey : BLSPubkey) (wc : Bytes32)
    (amount : U64) : M Validator := do
  let v : Validator :=
    { pubkey, withdrawal_credentials := wc, effective_balance := U64.zero, slashed := false,
      activation_eligibility_epoch := FAR_FUTURE_EPOCH, activation_epoch := FAR_FUTURE_EPOCH,
      exit_epoch := FAR_FUTURE_EPOCH, withdrawable_epoch := FAR_FUTURE_EPOCH }
  let maxEb ← c64 (if f.atLeast .electra then getMaxEffectiveBalance P v else P.MAX_EFFECTIVE_BALANCE)
  let rounded ← U64.sub? amount (← U64.mod? amount (← c64 P.EFFECTIVE_BALANCE_INCREMENT)
    "get_validator_from_deposit") "get_validator_from_deposit"
  pure { v with effective_balance := if rounded < maxEb then rounded else maxEb }

/-- `set_or_append_list` (Altair). -/
def setOrAppendList {α : Type} {n : Nat} (xs : SszList α n) (index : ValidatorIndex) (v : α)
    (site : String) : M (SszList α n) :=
  if index.toNat == xs.length then xs.push v site else xs.set index.toNat v site

/-- `add_validator_to_registry` (Electra; Altair to Deneb differ only in `get_validator_from_deposit`). -/
def addValidatorToRegistry (state : BeaconState P f) (pubkey : BLSPubkey) (wc : Bytes32)
    (amount : U64) : M (BeaconState P f) := do
  let site := "add_validator_to_registry"
  let index ← U64.ofNat? state.validators.length "get_index_for_new_validator"
  let validator ← getValidatorFromDeposit P f pubkey wc amount
  let zeroFlags : ParticipationFlags := UIntN.zero
  pure { state with
    validators := ← setOrAppendList state.validators index validator site
    balances := ← setOrAppendList state.balances index amount site
    previous_epoch_participation := ← setOrAppendList state.previous_epoch_participation index zeroFlags site
    current_epoch_participation := ← setOrAppendList state.current_epoch_participation index zeroFlags site
    inactivity_scores := ← setOrAppendList state.inactivity_scores index U64.zero site }

/-- `is_valid_deposit_signature` (Electra). -/
def isValidDepositSignature (ctx : Ctx) (pubkey : BLSPubkey) (wc : Bytes32) (amount : U64)
    (signature : BLSSignature) : M Bool := do
  let msg : DepositMessage := { pubkey, withdrawal_credentials := wc, amount }
  let domain ← computeDomainDefault ctx.cfg DOMAIN_DEPOSIT
  let root := computeSigningRoot msg domain
  pure (blsVerify ctx.blsActive pubkey root signature)

end JauneConsensus
