import Jaune.MessageCall.CheckedContext
import Jaune.MessageCall.CheckedExec
import Jaune.Execution

namespace Jaune.Checked

open Jaune

/-- Store or clear a designation, then increment its authority's nonce. Each write
applies the account-clearing rule to the surviving storage-write keys. -/
def Frame.State.writeDelegation (s : Frame.State) (authority target : Address) : Frame.State :=
  let code := if target = 0 then .empty else (eoaDelegationMarker ++ target.toBytes).toByteArray
  let world := ({ s.world with state := s.world.state.setCode authority code })
    |>.clearStorageWritesIfEmpty authority
  let world := ({ world with state := world.state.incrNonce authority })
    |>.clearStorageWritesIfEmpty authority
  s.withWorld world

namespace TopLevel

/-- A prepared native message with its rollback checkpoint, or a refusal at preparation. -/
inductive Prepared where
  | refused (reason : Refusal)
  | frame (message : Message) (checkpoint : Frame.State) (authorizationRefund : Nat)

/-- Apply one authorization before state gas. Successful recovery warms the authority
before its code and nonce are checked. -/
def authorizationStep (auth : Authorization) (input : Input) (refund : U256) :
    Except Fault (Input × U256) :=
  let block := input.message.context.block
  if auth.chainId != block.chainId.toU256 && auth.chainId != 0 then
    .ok (input, refund)
  else if auth.nonce = UInt64.max then
    .ok (input, refund)
  else
    match recoverAuthority auth with
    | .error (.invalidSignature _) => .ok (input, refund)
    | .error fault => .error (.crypto fault)
    | .ok authority =>
      let checkpoint := input.checkpoint.addAccessedAddress authority
      let input := { input with checkpoint }
      let world := checkpoint.world.state
      let account := world.get authority
      if ¬(account.code.isEmpty ∨ isValidDelegation account.code) then
        .ok (input, refund)
      else if account.nonce != auth.nonce then
        .ok (input, refund)
      else
        let refund := if AccountExists world authority then
          refund + (block.rules.gas.perAuthorizationIntrinsic - Gas.perAuthBaseCost).toU256
          else refund
        .ok ({ input with checkpoint := checkpoint.writeDelegation authority auth.address }, refund)

def authorizationLoop : List Authorization → Input → U256 → Except Fault (Input × U256)
  | [], input, refund => .ok (input, refund)
  | auth :: rest, input, refund => do
    let (input, refund) ← authorizationStep auth input refund
    authorizationLoop rest input refund

/-- Apply the transaction's authorization tuples, then reload the recipient's code. -/
def applyAuthorizations (input : Input) : Except Fault (Input × Nat) := do
  if !input.message.context.block.rules.delegationEnabled || input.authorizationList.isEmpty then
    .ok (input, 0)
  else
    let (authorized, refund) ← authorizationLoop input.authorizationList input 0
    match authorized.message.codeAddress with
    | none => .error (.internal (.invariant (.text "Invalid type 4 transaction: no target")))
    | some address =>
      let code := authorized.checkpoint.world.state.getCode address
      .ok ({ authorized with message.context.code := code }, refund.toNat)

/-- Resolve top-level delegation and warm the delegate without a nested-call surcharge. -/
def resolveCodeDelegation (input : Input) : Input :=
  let context := input.message.context
  match context.block.rules.delegatedCodeAddress context.code with
  | none => input
  | some address =>
    let code := input.checkpoint.world.state.getCode address
    { input with
      message := { input.message with
        context := { context with code }
        codeAddress := some address
        disablePrecompiles := true }
      checkpoint := input.checkpoint.addAccessedAddress address }

/-- Prepare a call or creation under rules without state gas. -/
def prepareWithoutStateGas (input : Input) : Except Fault Prepared := do
  match input.message.kind with
  | .create =>
    if accountHasCodeOrNonce input.checkpoint.world.state input.message.context.recipient then
      .ok (.refused (.collision (.addressCollision .none)))
    else .ok (.frame input.message input.checkpoint 0)
  | .call =>
    let (input, refund) ← applyAuthorizations input
    let input := resolveCodeDelegation input
    .ok (.frame input.message input.checkpoint refund)

end TopLevel

end Jaune.Checked
