import JauneConsensus.Block
import JauneConsensus.GloasBlock
import JauneConsensus.Harness.Discovery
import JauneConsensus.Harness.Snappy
import JauneConsensus.Harness.Yaml

/-!
# `operations` case checks (harness only)

`tests/formats/operations/README.md` (`consensus-specs` `v1.6.1`): decode `pre` (a
`BeaconState` of the case's preset and fork) and the operation, apply the processing call; when
`post` is present the result must equal it byte for byte (its SSZ serialization), otherwise the
call must reject. `bls_setting` (`meta.yaml`): `2` turns BLS verification off; `0`, `1` or an
absent setting runs it on. `execution_payload` cases carry the mocked engine's verdict in
`execution.yaml`.
-/

namespace JauneConsensus.Harness
open Jaune (Bytes)
open Yaml

/-- Read and Snappy-decode a case file. -/
private def readSsz (c : Case) (file : String) : IO (Except String Bytes) := do
  match Snappy.decompress (← IO.FS.readBinFile (c.dir / file)) with
  | .ok b => pure (.ok b.toList)
  | .error e => pure (.error s!"{file}: snappy: {e}")

private def readYamlFile (c : Case) (file : String) : IO (Except String YVal) := do
  pure ((parse (← IO.FS.readBinFile (c.dir / file))).mapError (s!"{file}: " ++ toString ·))

private def decodeAs {α : Type} [Ssz α] (bytes : Bytes) (what : String) : Except String α :=
  match (deserialize bytes : M α) with
  | .ok v => .ok v
  | .error r => .error s!"{what}: decode rejected: {repr r}"

/-- Apply one operation case: `input` is the operation file, `apply` the processing call. -/
@[nospecialize] def runOperation {P : Preset} {f : CFork} {α : Type} [Ssz α] (c : Case) (ctx : Ctx)
    (input : String) (apply : Ctx → BeaconState P f → α → M (BeaconState P f)) :
    IO (Except String Unit) := do
  let pre ← readSsz c "pre.ssz_snappy"
  let op ← readSsz c (input ++ ".ssz_snappy")
  let post ← if c.has "post.ssz_snappy" then (some <$> readSsz c "post.ssz_snappy") else pure none
  pure do
    let state : BeaconState P f ← decodeAs (← pre) "pre"
    let operation : α ← decodeAs (← op) input
    let result := apply ctx state operation
    match post with
    | none =>
      match result with
      | .ok _ => throw "expected the operation to be rejected (no post state), but it applied"
      | .error _ => pure ()
    | some postBytes =>
      let postBytes ← postBytes
      match result with
      | .error r => throw s!"rejected: {repr r}"
      | .ok s =>
        if serialize s == postBytes then pure ()
        else throw "post state differs"

/-- The `bls_setting` of the case: BLS is off only for `2`. -/
private def blsActiveOf (c : Case) : IO (Except String Bool) := do
  if !c.has "meta.yaml" then return .ok true
  let doc ← readYamlFile c "meta.yaml"
  pure do
    let v ← doc
    match v.get? "bls_setting" with
    | none => pure true
    | some x =>
      match x.asNat with
      | .ok n => pure (n != 2)
      | .error e => throw (toString e)

/-- `execution.yaml: execution_valid`. -/
private def executionValidOf (c : Case) : IO (Except String Bool) := do
  if !c.has "execution.yaml" then return .ok true
  let doc ← readYamlFile c "execution.yaml"
  pure do
    let v ← doc
    (v.field "execution_valid" >>= YVal.asBool).mapError toString

/-! ## Gloas (`JauneConsensus/Gloas{Withdrawals,Operations,Block}.lean`)

Gloas states are `Gloas.BeaconState P` (`ContainersGloas.lean`), a separate structure, so the
Gloas arms decode, apply and compare that type. `withdrawals` has no input file (Gloas
`process_withdrawals(state)`); `attestation` reads its extra `parent_slot` input from
`meta.yaml` (`tests/formats/operations/README.md` at `v1.7.0-beta.4`); `voluntary_exit_churn` is
`process_voluntary_exit` on the `voluntary_exit` input. -/

/-- Apply a Gloas step to the case's `pre` and compare with `post` (or expect a rejection). -/
@[nospecialize] def runGloasStep {P : Preset} (c : Case)
    (step : Gloas.BeaconState P → Except String (M (Gloas.BeaconState P))) :
    IO (Except String Unit) := do
  let pre ← readSsz c "pre.ssz_snappy"
  let post ← if c.has "post.ssz_snappy" then (some <$> readSsz c "post.ssz_snappy") else pure none
  pure do
    let state : Gloas.BeaconState P ← decodeAs (← pre) "pre"
    let result ← step state
    match post with
    | none =>
      match result with
      | .ok _ => throw "expected the operation to be rejected (no post state), but it applied"
      | .error _ => pure ()
    | some postBytes =>
      let postBytes ← postBytes
      match result with
      | .error r => throw s!"rejected: {repr r}"
      | .ok s =>
        if serialize s == postBytes then pure ()
        else throw "post state differs"

/-- Apply one Gloas operation case: `input` is the operation file. -/
@[nospecialize] def runGloasOperation {P : Preset} {α : Type} [Ssz α] (c : Case) (ctx : Ctx)
    (input : String) (apply : Ctx → Gloas.BeaconState P → α → M (Gloas.BeaconState P)) :
    IO (Except String Unit) := do
  let op ← readSsz c (input ++ ".ssz_snappy")
  runGloasStep (P := P) c fun state => do
    let operation : α ← decodeAs (← op) input
    pure (apply ctx state operation)

/-- `meta.yaml: parent_slot` (the Gloas `attestation` handler's extra input). -/
private def parentSlotOf (c : Case) : IO (Except String Slot) := do
  if !c.has "meta.yaml" then return .error "meta.yaml: no parent_slot"
  let doc ← readYamlFile c "meta.yaml"
  pure do
    let v ← doc
    match v.get? "parent_slot" with
    | none => throw "meta.yaml: no parent_slot"
    | some x =>
      let n ← x.asNat.mapError toString
      match (U64.ofNat? n "parent_slot" : M U64) with
      | .ok s => pure s
      | .error r => throw s!"meta.yaml: parent_slot: {repr r}"

/-- Run a Gloas `operations/<handler>` case at preset `P` under `ctx`. -/
def gloasOperationsCase (P : Preset) (ctx : Ctx) (c : Case) : IO (Except String Unit) := do
  match c.key.handler with
  | "attestation" =>
    let parentSlot ← match ← parentSlotOf c with
      | .ok s => pure s
      | .error e => return .error e
    runGloasOperation (P := P) c ctx "attestation" fun x s a =>
      Gloas.processAttestation x s a parentSlot
  | "attester_slashing" =>
    runGloasOperation (P := P) c ctx "attester_slashing" Gloas.processAttesterSlashing
  | "block_header" =>
    runGloasOperation (P := P) c ctx "block" fun _ s (b : Gloas.BeaconBlock P) =>
      Gloas.processBlockHeader s b
  | "bls_to_execution_change" =>
    runGloasOperation (P := P) c ctx "address_change" Gloas.processBlsToExecutionChange
  | "builder_deposit_request" =>
    runGloasOperation (P := P) c ctx "builder_deposit_request" Gloas.processBuilderDepositRequest
  | "builder_exit_request" =>
    runGloasOperation (P := P) c ctx "builder_exit_request" fun x s r =>
      Gloas.processBuilderExitRequest x.cfg s r
  | "consolidation_request" =>
    runGloasOperation (P := P) c ctx "consolidation_request" fun x s r =>
      Gloas.processConsolidationRequest x.cfg s r
  | "deposit_request" =>
    runGloasOperation (P := P) c ctx "deposit_request" fun _ s r =>
      pure (Gloas.processDepositRequest s r)
  | "execution_payload_bid" =>
    runGloasOperation (P := P) c ctx "execution_payload_bid" Gloas.processExecutionPayloadBid
  | "parent_execution_payload" =>
    runGloasOperation (P := P) c ctx "block" Gloas.processParentExecutionPayload
  | "payload_attestation" =>
    runGloasOperation (P := P) c ctx "payload_attestation" Gloas.processPayloadAttestation
  | "proposer_slashing" =>
    runGloasOperation (P := P) c ctx "proposer_slashing" Gloas.processProposerSlashing
  | "sync_aggregate" =>
    runGloasOperation (P := P) c ctx "sync_aggregate" Gloas.processSyncAggregate
  | "voluntary_exit" | "voluntary_exit_churn" =>
    runGloasOperation (P := P) c ctx "voluntary_exit" Gloas.processVoluntaryExit
  | "withdrawal_request" =>
    runGloasOperation (P := P) c ctx "withdrawal_request" fun x s r =>
      Gloas.processWithdrawalRequest x.cfg s r
  | "withdrawals" => runGloasStep (P := P) c fun s => pure (Gloas.processWithdrawals s)
  | h => pure (.error s!"UNIMPLEMENTED: no Gloas operations handler {h}")

/-- Run an `operations/<handler>` case at its preset and fork under `cfg`. -/
def operationsCase (cfg : Config) (c : Case) : IO (Except String Unit) := do
  let some P := Preset.ofName? c.preset | return .error s!"no preset {c.preset}"
  let some f := CFork.ofName? c.key.fork | return .error s!"no fork {c.key.fork}"
  let blsActive ← match ← blsActiveOf c with
    | .ok b => pure b
    | .error e => return .error e
  let executionValid ← match ← executionValidOf c with
    | .ok b => pure b
    | .error e => return .error e
  let ctx : Ctx := { cfg, blsActive, executionValid }
  if f == .gloas then return ← gloasOperationsCase P ctx c
  match c.key.handler with
  | "attestation" => runOperation (P := P) (f := f) c ctx "attestation" processAttestation
  | "attester_slashing" => runOperation (P := P) (f := f) c ctx "attester_slashing" processAttesterSlashing
  | "block_header" =>
    runOperation (P := P) (f := f) c ctx "block" fun _ s (b : BeaconBlock P f) => processBlockHeader s b
  | "bls_to_execution_change" =>
    runOperation (P := P) (f := f) c ctx "address_change" processBlsToExecutionChange
  | "consolidation_request" =>
    runOperation (P := P) (f := f) c ctx "consolidation_request" fun x s r =>
      processConsolidationRequest x.cfg s r
  | "deposit" => runOperation (P := P) (f := f) c ctx "deposit" processDeposit
  | "deposit_request" =>
    runOperation (P := P) (f := f) c ctx "deposit_request" fun _ s r => processDepositRequest s r
  | "execution_payload" =>
    runOperation (P := P) (f := f) c ctx "body" processExecutionPayload
  | "proposer_slashing" => runOperation (P := P) (f := f) c ctx "proposer_slashing" processProposerSlashing
  | "sync_aggregate" => runOperation (P := P) (f := f) c ctx "sync_aggregate" processSyncAggregate
  | "voluntary_exit" => runOperation (P := P) (f := f) c ctx "voluntary_exit" processVoluntaryExit
  | "withdrawal_request" =>
    runOperation (P := P) (f := f) c ctx "withdrawal_request" fun x s r =>
      processWithdrawalRequest x.cfg s r
  | "withdrawals" =>
    runOperation (P := P) (f := f) c ctx "execution_payload" fun _ s (p : ExecutionPayload P) =>
      processWithdrawals s p
  | h => pure (.error s!"UNIMPLEMENTED: no operations handler {h}")

end JauneConsensus.Harness
