import Jaune.Run.Fields

/-!
# System calls read their message run (goal `jaune-shape-and-names-v1`, W2 cut B2)

A system call is a top-level message run from the system address with the fixed system gas
(`systemTransactionMessage`), on a freshly begun transaction. Its consumers read the
`MessageRun` through its functions (`Jaune.Run.Fields`) instead of a rendered output record:

* `processSystemTransaction` runs the message and returns the run. As before, a run whose refund
  counter faults fails the call; the counter itself is not read further.
* `processUncheckedSystemTransaction` runs the contract's code as it stands.
* `processCheckedSystemTransaction` first rejects the block when the contract holds no code, then
  rejects it when the run settled with a halt or a revert.
* `runRequestContracts`, `processGeneralPurposeRequestsAt` and `processGeneralPurposeRequests`
  collect the request contracts' return data and incorporate each call's reads and writes.
* `beaconRootsCall` and `historyStorageCall` are the two pre-execution calls.

Staged under `Jaune.Staging`; the bridges are in `Jaune.Bridge.G2a.Consumers`.
-/

namespace Jaune.Staging

open Jaune

/-- The single boundary shared by all four system transactions (beacon roots, history storage,
withdrawal requests, consolidation requests): begin the transaction, so that each takes its own
input state as the original state, and run the system message. A run whose refund counter faults
fails the call. -/
def processSystemTransaction (benv : Benv) (target : Address) (code : ByteArray) (data : Bytes) :
    Except Fault MessageRun := do
  let benv := benv.beginTransaction
  let txEnv : Tenv := systemTransactionEnvironment benv
  let systemTxMsg : Msg := systemTransactionMessage benv txEnv target data code
  let run ← Message.run systemTxMsg
  let _ ← run.refundCounter
  pure run

/-- A system call that runs the contract's code as it stands, even none. -/
def processUncheckedSystemTransaction (benv : Benv) (target : Address) (data : Bytes) :
    Except Fault MessageRun :=
  let systemContractCode : ByteArray := benv.state.getCode target
  processSystemTransaction benv target systemContractCode data

/-- A mandatory system call: a contract without code rejects the block before the call
(`BlockException.SYSTEM_CONTRACT_EMPTY`), and so does a call that settles with a halt or a
revert; the rejection carries the settled halt. -/
def processCheckedSystemTransaction (benv : Benv) (target : Address) (data : Bytes) :
    Except TransitionError MessageRun := do
  let systemContractCode : ByteArray := benv.state.getCode target
  if systemContractCode.isEmpty then
    .error <| .block <| .systemContractEmpty <| .text
      s!"system contract address {target.toHex} holds no code"
  let run ← (processSystemTransaction benv target systemContractCode data).mapError
    (fun e => TransitionError.vm e.toEvmError)
  match run.error with
  | some halt => .error <| .block <| .systemContractCallFailed target halt
  | none => .ok run

/-- Call each request-producing system contract in turn, threading the state. Each contract's
non-empty return data is appended prefixed with its type byte; under rules with a block-level
access list each call incorporates its reads and writes, and the contract account `create_evm`
read, at `idx`. -/
def runRequestContracts (idx : Nat) :
    List (UInt8 × Address) → Benv → List Bytes → BlockAccessListBuilder →
      Except TransitionError (State × List Bytes × BlockAccessListBuilder)
  | [], benv, acc, bal => .ok ⟨benv.state, acc, bal⟩
  | ⟨requestType, address⟩ :: rest, benv, acc, bal => do
    let run ← processCheckedSystemTransaction benv address []
    let acc :=
      if run.returnData.length > 0 then
        acc ++ [[requestType] ++ run.returnData]
      else
        acc
    let bal := match benv.stat.rules.blockAccessListRules with
      | none => bal
      | some _ => bal.incorporate idx benv.state run.state
          (address :: run.accountReads.toList) run.storageReads.toList run.storageWrites.toList
    runRequestContracts idx rest (benv.withState run.state) acc bal

/-- Run the block's request-producing system contracts, after the deposit requests parsed from the
receipts, and collect their output (EIP-7685). -/
def processGeneralPurposeRequestsAt (balIndex : Nat) (benv : Benv) (bout : BlockOutput) :
    Except TransitionError (State × BlockOutput) := do
  let depositRequests ← parseDepositRequests bout
  let seeded : List Bytes :=
    if depositRequests.length > 0 then
      bout.requests ++ [depositRequestType ++ depositRequests]
    else
      bout.requests
  let ⟨state, allRequests, bal⟩ ←
    runRequestContracts balIndex benv.stat.rules.requests benv seeded bout.blockAccessListBuilder
  .ok ⟨state, {bout with requests := allRequests, blockAccessListBuilder := bal}⟩

/-- The block pipeline's request pass, at the post-execution index `n + 1` (EIP-7928), `n` the
number of receipts. -/
def processGeneralPurposeRequests (benv : Benv) (bout : BlockOutput) :
    Except TransitionError (State × BlockOutput) :=
  processGeneralPurposeRequestsAt (bout.receiptKeys.length + 1) benv bout

/-- EIP-4788's pre-execution beacon-roots call (Cancun on), with its block-level access-list
incorporation at index 0; under rules without `sys.beaconRoots` the identity: the state as given and
an empty builder. -/
def beaconRootsCall (rules : ForkRules) (benv : Benv) :
    Except TransitionError (State × BlockAccessListBuilder) :=
  if rules.systemCalls.beaconRoots then do
    let run ←
      (processUncheckedSystemTransaction benv beaconRootsAddress
          benv.stat.parentBeaconBlockRoot.toBytes).mapError
        (fun e => TransitionError.vm e.toEvmError)
    .ok ⟨run.state, BlockAccessListBuilder.incorporateSystem {} rules 0 benv.state run.state
      (beaconRootsAddress :: run.accountReads.toList) run.storageReads.toList
      run.storageWrites.toList⟩
  else .ok ⟨benv.state, {}⟩

/-- EIP-2935's pre-execution history-storage call (Prague on), incorporated at index 0; under rules
without `sys.historyStorage` the identity. -/
def historyStorageCall (rules : ForkRules) (benv : Benv) (bal : BlockAccessListBuilder) :
    Except TransitionError (State × BlockAccessListBuilder) :=
  if rules.systemCalls.historyStorage then do
    let lastHash ←
       benv.stat.blockHashes.getLast?.toExcept
         (TransitionError.internal (.invariant (.text "block hashes is empty")))
    let run ←
      (processUncheckedSystemTransaction benv historyStorageAddress lastHash.toBytes).mapError
        (fun e => TransitionError.vm e.toEvmError)
    .ok ⟨run.state, bal.incorporateSystem rules 0 benv.state run.state
      (historyStorageAddress :: run.accountReads.toList) run.storageReads.toList
      run.storageWrites.toList⟩
  else .ok ⟨benv.state, bal⟩

end Jaune.Staging
