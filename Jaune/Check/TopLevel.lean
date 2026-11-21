-- Check/CheckedTransaction.lean : the top-level message guards of `Jaune/Check/Transaction.lean`,
-- restated over the Checked top-level run.
--
-- Check module (see `scripts/layering.json`). Goal `jaune-shape-and-names-v1`, G2b (unit jsn-u85,
-- S0): the guards of `Jaune/Check/Transaction.lean` that run the W1 top-level message
-- (`TopLevel.run` over a `Msg`) are restated over `Checked.TopLevel.runNative` and its settlement
-- (`Checked.TopLevel.Run.settlement`), with the same observations and expected values; the W1
-- top-level Amsterdam preparation (`prepareTopLevelAmsterdam`) is restated over
-- `Checked.TopLevel.prepareAmsterdamFrame` where the same guard reads it. A `Msg` of a W1 guard
-- is written here as the `Checked.TopLevel.Input` that `Checked.TopLevel.Input.ofLegacy` maps it
-- to: the message's call context, kind (a creation when it has no target), grants and flags, on
-- `Checked.Message.initialCheckpoint` over the message's state. The old guards stay until the
-- delete commit (precedent: G2a `8840b59b`). The default build compiles this module through
-- `JauneChecks.lean`.
import Jaune.Run.Message

namespace Jaune

open Jaune

/-- A top-level input: the message on the checkpoint it starts from over `state`, with the
given warm addresses and no authorizations. -/
private def guardInput (message : Message) (state : State)
    (accessed : AddressSet := .emptyWithCapacity) : TopLevel.Input :=
  ⟨message, message.initialCheckpoint ⟨state, .empty, .emptyWithCapacity⟩ accessed
    .emptyWithCapacity .emptyWithCapacity .emptyWithCapacity, []⟩

/-- The settlement of a top-level run, when it does not fault. -/
private def guardSettle (input : TopLevel.Input) : Option TopLevel.Settlement :=
  match TopLevel.run input with
  | .ok run => some (run.settlement input)
  | .error _ => none

private def fixtureTestAccount
    (nonce : UInt64) (bal : U256) (code : ByteArray := .empty) : Account :=
  { nonce := nonce, balance := bal, storage := .empty, code := code }

/-- The block record of `fixtureAmsterdamBenv`. -/
private def fixtureAmsterdamBlock : BlockContext :=
  { fork := .amsterdam, chainId := 1, gasLimit := 30000000, blockHashes := [], coinbase := 0
    number := 1, baseFeePerGas := 1, timestamp := 0, prevRandao := 0, excessBlobGas := 0
    parentBeaconBlockRoot := 0 }

/-- `fixtureAmsterdamMsg`: sender 1, value-transferring, depth left 1024, the code of
`currentTarget` in `state`. -/
private def fixtureAmsterdamInput (state origState : State)
    (target : Option Address) (currentTarget : Address) (value gas grant : Nat)
    (accessed : AddressSet := .emptyWithCapacity) : TopLevel.Input :=
  guardInput
    { context := {
        caller := 1, recipient := currentTarget, value := value.toU256, calldata := []
        code := state.getCode currentTarget, depthLeft := 1024, isStatic := false
        tx := { origin := 1, gasPrice := 0, blobVersionedHashes := []
                originalState := origState }
        block := fixtureAmsterdamBlock }
      kind := if target.isNone then .create else .call
      codeAddress := target, target := target, gas := gas, stateGasGrant := grant
      transfersValue := true, disablePrecompiles := false }
    state accessed

/-- A creation by `Msg`'s defaults (sender 0, no value, no code, Prague's block record) at
`address` over `state` with 20,000 gas. -/
private def legacyCreateInput (state : State) (address : Address) : TopLevel.Input :=
  guardInput
    { context := {
        caller := 0, recipient := address, value := 0, calldata := [], code := .empty
        depthLeft := 1024, isStatic := false
        tx := { origin := 0, gasPrice := 0, blobVersionedHashes := [], originalState := .empty }
        block := default }
      kind := .create, codeAddress := none, target := none, gas := 20000, stateGasGrant := 0
      transfersValue := false, disablePrecompiles := false }
    state

private def prepareCreateGuard (collision : Bool) :
    Option (Nat × Nat × Option SettledHalt) :=
  let address : Address := 9
  let account := fixtureTestAccount 1 0
  let state := if collision then State.set .empty address account else .empty
  let input := fixtureAmsterdamInput state state none address 0 20000 200000
  match TopLevel.prepareAmsterdamFrame amsterdamStateGasRules input with
  | .ok ⟨_, s⟩ => some ⟨s.gasLeft, s.stateGas.left, none⟩
  | .error _ =>
    match guardSettle input with
    | some run => some ⟨run.gasLeft, run.stateGasLeft, run.error⟩
    | none => none

#guard prepareCreateGuard false = some ⟨20000, 16400, none⟩
#guard prepareCreateGuard true =
  some ⟨0, 200000, some (.halt (.addressCollision .none))⟩

-- Storage-only top-level creation deploys and wipes storage in both lanes;
-- code and nonce remain independent collision controls.
private def legacyStorageOnlyCreateGuard : Bool :=
  let address : Address := 12
  let state := State.setStorageValue .empty address 1 1
  match guardSettle (legacyCreateInput state address) with
  | some run =>
    run.error.isNone && (run.state.get address).storage.isEmpty && (run.state.get address).nonce == 1
  | none => false

private def amsterdamStorageOnlyCreateGuard : Bool :=
  let address : Address := 13
  let state := State.setStorageValue .empty address 1 1
  match guardSettle (fixtureAmsterdamInput state state none address 0 20000 200000) with
  | some run =>
    run.error.isNone && (run.state.get address).storage.isEmpty && (run.state.get address).nonce == 1
  | none => false

private def legacyCreateCollisionGuard (code : Bool) : Bool :=
  let address : Address := 14
  let state :=
    if code then State.setCode .empty address (.mk (.mk [0x00]))
    else State.set .empty address (fixtureTestAccount 1 0)
  match guardSettle (legacyCreateInput state address) with
  | some run =>
    run.gasLeft == 0 && run.error == some (.halt (.addressCollision .none))
  | none => false

private def amsterdamCreateCollisionGuard (code : Bool) : Bool :=
  let address : Address := 15
  let state :=
    if code then State.setCode .empty address (.mk (.mk [0x00]))
    else State.set .empty address (fixtureTestAccount 1 0)
  let input := fixtureAmsterdamInput state state none address 0 20000 200000
  match TopLevel.prepareAmsterdamFrame amsterdamStateGasRules input with
  | .error ⟨.halt (.addressCollision .none), _⟩ => true
  | _ => false

#guard legacyStorageOnlyCreateGuard
#guard amsterdamStorageOnlyCreateGuard
#guard legacyCreateCollisionGuard true
#guard legacyCreateCollisionGuard false
#guard amsterdamCreateCollisionGuard true
#guard amsterdamCreateCollisionGuard false

private def delegatedDispatchGuard (warm : Bool) :
    Option (Nat × Nat × Option Address) :=
  let target : Address := 10
  let delegate : Address := 11
  let delegation :=
    (eoaDelegationMarker ++ delegate.toBytes).toByteArray
  let state :=
    (State.set .empty target (fixtureTestAccount 0 0 delegation)).set
      delegate (fixtureTestAccount 0 0 (.mk (.mk [0x00])))
  let accessed : AddressSet :=
    if warm then ({target, delegate} : AddressSet) else {target}
  let input := fixtureAmsterdamInput state state (some target) target 0
    10000 0 accessed
  match TopLevel.prepareAmsterdamFrame amsterdamStateGasRules input with
  | .error _ => none
  | .ok ⟨prepared, s⟩ =>
    some ⟨s.gasLeft, s.stateGas.left, prepared.codeAddress⟩

#guard delegatedDispatchGuard false = some ⟨7000, 0, some 11⟩
#guard delegatedDispatchGuard true = some ⟨9900, 0, some 11⟩

/-! ### EIP-161: touched accounts and the end-of-transaction sweep

The touch guards of `Jaune/Check/Transaction.lean` over the Checked top-level run, under Gray
Glacier (the last rule set that sweeps) against Prague (which does not). -/

private def touchParent : Address := 0x1000
private def checkedTouchEmptyAccount : Address := 0x2000
private def checkedTouchCodeAccount : Address := 0x4000

/-- `CALL(gas, to, 0, 0, 0, 0, 0)`, then `POP` the success word. -/
private def touchCall (dest gas : Nat) : List UInt8 :=
  [0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0,
   0x61, (dest / 256).toUInt8, (dest % 256).toUInt8,
   0x61, (gas / 256).toUInt8, (gas % 256).toUInt8, 0xF1, 0x50]

private def touchRevert : List UInt8 := [0x60, 0, 0x60, 0, 0xFD]

private def touchState (parentCode cCode : List UInt8) : State :=
  let st := (State.setStorageValue .empty checkedTouchEmptyAccount 1 1).setStorageValue ripemd160Address 1 1
  let st := State.setCode st touchParent ⟨parentCode.toArray⟩
  State.setCode st checkedTouchCodeAccount ⟨cCode.toArray⟩

/-- `touchMsg`: a call from 0x5000 to the parent at depth left 8 with 200,000 gas, over `state`,
which is also the original state. -/
private def touchInputOn (fork : Fork) (parentCode : List UInt8) (state : State) :
    TopLevel.Input :=
  guardInput
    { context := {
        caller := 0x5000, recipient := touchParent, value := 0, calldata := []
        code := ⟨parentCode.toArray⟩, depthLeft := 8, isStatic := false
        tx := { origin := 0, gasPrice := 0, blobVersionedHashes := [], originalState := state }
        block := { (default : BlockContext) with fork } }
      kind := .call, codeAddress := some touchParent, target := some touchParent
      gas := 200000, stateGasGrant := 0, transfersValue := false, disablePrecompiles := false }
    state

private def touchInput (fork : Fork) (parentCode cCode : List UInt8) : TopLevel.Input :=
  touchInputOn fork parentCode (touchState parentCode cCode)

/-- The transaction-level touched set the top-level run reports. -/
private def touchedOf (fork : Fork) (parentCode : List UInt8)
    (cCode : List UInt8 := []) : Option (List Address) :=
  match guardSettle (touchInput fork parentCode cCode) with
  | some run => some run.touchedAccounts.toList
  | none => none

-- A successful child's empty target is touched; Prague records nothing.
#guard touchedOf .grayGlacier (touchCall 0x2000 1000 ++ [0x00]) = some [checkedTouchEmptyAccount]
#guard touchedOf .prague (touchCall 0x2000 1000 ++ [0x00]) = some []
-- A zero `SELFDESTRUCT` credit to the storage-only `touchE`: before Paris it is kept and
-- touched; from Paris the credit erases it at once and nothing is touched.
private def touchSelfdestruct (fork : Fork) : Option (Bool × U256 × List Address) :=
  match guardSettle (touchInput fork [0x61, 0x20, 0x00, 0xFF] []) with
  | some run =>
    some (run.state[checkedTouchEmptyAccount]?.isSome, (run.state.get checkedTouchEmptyAccount).storage.get 1,
      run.touchedAccounts.toList)
  | none => none
#guard touchSelfdestruct .berlin = some (true, 1, [checkedTouchEmptyAccount])
#guard touchSelfdestruct .grayGlacier = some (true, 1, [checkedTouchEmptyAccount])
#guard touchSelfdestruct .paris = some (false, 0, [])
#guard touchSelfdestruct .prague = some (false, 0, [])
-- A failed child's touches die with it ...
#guard touchedOf .grayGlacier (touchCall 0x4000 50000 ++ [0x00])
    (touchCall 0x2000 1000 ++ touchRevert) = some []
-- ... except 0x03: the quirk keeps a touch of RIPEMD-160 made inside the
-- failed child,
#guard touchedOf .grayGlacier (touchCall 0x4000 50000 ++ [0x00])
    (touchCall 0x03 1000 ++ touchRevert) = some [ripemd160Address]
-- and a failed call to 0x03 itself (out of gas) still touches it.
#guard touchedOf .grayGlacier (touchCall 0x03 1 ++ [0x00]) = some [ripemd160Address]
#guard touchedOf .prague (touchCall 0x03 1 ++ [0x00]) = some []
-- A failed transaction keeps no touch at all.
#guard touchedOf .grayGlacier (touchCall 0x2000 1000 ++ touchRevert) = some []

/-- `CALL(gas, to, value, 0, 0, 0, 0)`, then `POP` the success word. -/
private def touchCallValue (dest gas value : Nat) : List UInt8 :=
  [0x60, 0, 0x60, 0, 0x60, 0, 0x60, 0, 0x60, value.toUInt8,
   0x61, (dest / 256).toUInt8, (dest % 256).toUInt8,
   0x61, (gas / 256).toUInt8, (gas % 256).toUInt8, 0xF1, 0x50]

/-- The parent (funded with 1 wei) calls `touchC`, which self-destructs to the storage-only
`touchE` with a zero balance, and then sends `touchE` 1 wei; the transaction's sweep follows.
Reported as (`touchE`'s balance, its slot 1). -/
private def touchSelfdestructThenFund (fork : Fork) : Option (U256 × U256) :=
  let parentCode := touchCall 0x4000 50000 ++ touchCallValue 0x2000 1000 1 ++ [0x00]
  let original := touchState parentCode [0x61, 0x20, 0x00, 0xFF]
  let input := touchInputOn fork parentCode (original.setBalance touchParent 1)
  let input := { input with message := { input.message with context :=
    { input.message.context with tx := { input.message.context.tx with originalState := original } } } }
  match guardSettle input with
  | some run =>
    let state := sweepTouchedAccounts (Fork.ruleSet fork) run.touchedAccounts.toList run.state
    some ((state.get checkedTouchEmptyAccount).balance, (state.get checkedTouchEmptyAccount).storage.get 1)
  | none => none
#guard touchSelfdestructThenFund .berlin = some (1, 1)
#guard touchSelfdestructThenFund .grayGlacier = some (1, 1)
#guard touchSelfdestructThenFund .paris = some (1, 0)
#guard touchSelfdestructThenFund .prague = some (1, 0)

/-! ### Amsterdam authority charges (`Jaune/Check/Transaction.lean:194-209`, jsn-u87)

`delegationChargeGuard`: the validated-authorization charge of W1
`applyValidatedDelegationAmsterdam` over `initDevm` of `fixtureAmsterdamMsg`, restated over
`Checked.TopLevel.applyValidatedAuthorization` on the checkpoint of the corresponding input. -/

private def delegationChargeGuard (doRepeat : Bool) :
    Option (Nat × Nat × Nat × Nat) :=
  let input := fixtureAmsterdamInput .empty .empty (some 2) 2 0 20000 300000
  let context := input.message.context
  match TopLevel.applyValidatedAuthorization amsterdamStateGasRules context 5 6
      input.checkpoint .emptyWithCapacity .emptyWithCapacity with
  | .error _ => none
  | .ok ⟨once, paid, setFor⟩ =>
    if doRepeat then
      match TopLevel.applyValidatedAuthorization amsterdamStateGasRules context 5 7
          once paid setFor with
      | .error _ => none
      | .ok ⟨twice, _, _⟩ =>
        some ⟨once.gasLeft, once.stateGas.left, twice.gasLeft, twice.stateGas.left⟩
    else some ⟨once.gasLeft, once.stateGas.left, 0, 0⟩

#guard delegationChargeGuard false =
  some ⟨11000, 81210, 0, 0⟩
-- The second write to one authority pays neither ACCOUNT_WRITE nor AUTH_BASE.
#guard delegationChargeGuard true =
  some ⟨11000, 81210, 11000, 81210⟩

/-! ### Amsterdam failure-order regressions (`Jaune/Check/Transaction.lean:2011-2097`, jsn-u87)

These pin failure precedence and warming at the metering switch over the Checked `PlainOp.runCore`,
all four Checked `MessageOp.step` CALL variants, and the Checked top-level dispatch boundary
(`TopLevel.resolveAmsterdamCall`, W1 `resolveTopLevelCallAmsterdam`). `orderingGuardMessage` is
`Msg`'s defaults with sender and recipient 0x1000 (holding 100 wei, also the original state), the
given gas and fork, at depth left 8; its `initDevm`/`initSevm` are the input's checkpoint and
call context. -/

private def orderingGuardState : State := State.setBalance .empty (0x1000 : Address) 100

private def orderingGuardInputOn (fork : Fork) (gas : Nat) (state : State)
    (recipient : Address := 0x1000) (isStatic : Bool := false) : TopLevel.Input :=
  guardInput
    { context := {
        caller := 0x1000, recipient := recipient, value := 0, calldata := [], code := .empty
        depthLeft := 8, isStatic := isStatic
        tx := { origin := 0, gasPrice := 0, blobVersionedHashes := []
                originalState := orderingGuardState }
        block := { fork, chainId := 0, gasLimit := 0, blockHashes := [], coinbase := 0
                   number := 0, baseFeePerGas := 0, timestamp := 0, prevRandao := 0
                   excessBlobGas := 0, parentBeaconBlockRoot := 0 } }
      kind := .call, codeAddress := none, target := some recipient, gas := gas, stateGasGrant := 0
      transfersValue := false, disablePrecompiles := false }
    state

private def orderingGuardSummary (r : Except (ExceptionalHalt × Frame.State) Frame.State) :
    String × Nat × List Nat × Bool × Bool :=
  let (status, s) := match r with
    | .ok s => ("ok", s)
    | .error (e, s) => (e.render, s)
  (status, s.gasLeft, s.stack.map U256.toNat,
    s.substate.accessedAddresses.contains (0x2000 : Address),
    s.substate.accessedAddresses.contains (0x3000 : Address))

private def orderingGuardTstore (fork : Fork) (gas : Nat) (stack : List U256) :=
  let input := orderingGuardInputOn fork gas orderingGuardState (isStatic := true)
  orderingGuardSummary
    (PlainOp.runCore 0 input.message.context (input.checkpoint.withStack stack) .tstore)

-- Amsterdam follows `storage.py.tstore`: the static error precedes stack
-- access and charging. The `none` lane retains the pre-Amsterdam order.
#guard orderingGuardTstore .amsterdam 0 [] =
  ("WriteInStaticContext", 0, [], false, false)
#guard orderingGuardTstore .amsterdam 99 [1, 2] =
  ("WriteInStaticContext", 99, [1, 2], false, false)
#guard orderingGuardTstore .amsterdam 100 [1, 2] =
  ("WriteInStaticContext", 100, [1, 2], false, false)
#guard orderingGuardTstore .prague 0 [] =
  ("StackUnderflowError", 0, [], false, false)
#guard orderingGuardTstore .prague 99 [1, 2] =
  ("OutOfGasError", 99, [], false, false)

/-- `orderingGuardDelegatedMessage`: 0x2000 delegates to 0x3000 in the current state only. -/
private def orderingGuardDelegatedState : State :=
  orderingGuardState.setCode 0x2000 (eoaDelegationMarker ++ (0x3000 : Address).toBytes).toByteArray

private def orderingGuardCall (gas : Nat) (x : MessageOp) (stack : List U256) :=
  let input := orderingGuardInputOn .amsterdam gas orderingGuardDelegatedState
  match MessageOp.step input.message.context (input.checkpoint.withStack stack) x with
  | .done r => orderingGuardSummary r
  | .spawn _ _ => ("spawn", 0, [], false, false)

-- The first check may warm the direct code address. The second includes the
-- delegated access price and must fail before the delegated address is warmed.
#guard orderingGuardCall 2999 .staticcall [0, 0x2000, 0, 0, 0, 0] =
  ("OutOfGasError", 2999, [], false, false)
#guard orderingGuardCall 3000 .call [0, 0x2000, 0, 0, 0, 0, 0] =
  ("OutOfGasError", 3000, [], true, false)
#guard orderingGuardCall 3000 .callcode [0, 0x2000, 0, 0, 0, 0, 0] =
  ("OutOfGasError", 3000, [], true, false)
#guard orderingGuardCall 3000 .delegatecall [0, 0x2000, 0, 0, 0, 0] =
  ("OutOfGasError", 3000, [], true, false)
#guard orderingGuardCall 3000 .staticcall [0, 0x2000, 0, 0, 0, 0] =
  ("OutOfGasError", 3000, [], true, false)
#guard (orderingGuardCall 6000 .staticcall [0, 0x2000, 0, 0, 0, 0]).1 =
  "spawn"

private def orderingGuardTopLevel (gas : Nat) : String × Nat × Bool × Bool :=
  let input := orderingGuardInputOn .amsterdam gas orderingGuardDelegatedState 0x2000
  let s := input.checkpoint.addAccessedAddress 0x2000
  match TopLevel.resolveAmsterdamCall input.message s with
  | .error (e, s) =>
    (match e with
      | .halt reason => reason.render
      | .fault _ => "fault", s.gasLeft,
      s.substate.accessedAddresses.contains (0x2000 : Address),
      s.substate.accessedAddresses.contains (0x3000 : Address))
  | .ok (_, s) =>
    ("ok", s.gasLeft,
      s.substate.accessedAddresses.contains (0x2000 : Address),
      s.substate.accessedAddresses.contains (0x3000 : Address))

-- Top-level dispatch has the same boundary: a cold delegated access priced at
-- 3,000 with only 2,999 gas leaves the already-warm recipient as the sole one.
#guard orderingGuardTopLevel 2999 = ("OutOfGasError", 2999, true, false)

/-! ### A failed child's block-access-list reads (`Jaune/Check/Transaction.lean:2218-2229`, jsn-u87)

A failed child's reads survive the merge into its parent: the Checked `resume` takes the reverted
child's trail. The parent is the checkpoint of `orderingGuardMessage .amsterdam 100000`. -/

private def blockAccessListGuardAddress : Address := 0x2000

#guard
  let parent := (orderingGuardInputOn .amsterdam 100000 orderingGuardState).checkpoint
  let child := (parent.recordAccountRead amsterdamRules blockAccessListGuardAddress).recordStorageRead
    amsterdamRules blockAccessListGuardAddress 5
  let failed : Frame.Result := .revert [] 0 StateGasMeter.zero child.trail
  match resume amsterdamRules ⟨.call 0 0, false⟩ parent failed with
  | .ok (.ok merged) =>
    merged.trail.accountReads.contains blockAccessListGuardAddress ∧
      merged.trail.storageReads.contains (blockAccessListGuardAddress, 5) ∧
      ¬ parent.trail.accountReads.contains blockAccessListGuardAddress
  | _ => False

end Jaune
