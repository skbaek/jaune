import Jaune.Bridge.G2a.Old.Transaction

section
open Jaune
namespace Jaune
def Bridge.G2a.Old.processSystemTransaction (benv : Benv)
  (target : Address) (code : ByteArray) (data : Bytes) :
  Except EvmError (State × Bridge.G2a.Old.MessageCallOutput) := do
  let benv := benv.beginTransaction
  let txEnv : Tenv := systemTransactionEnvironment benv
  let systemTxMsg : Msg :=
    systemTransactionMessage benv txEnv target data code
  Bridge.G2a.Old.processMessageCall systemTxMsg
end Jaune
end

section
open Jaune
namespace Jaune
def Bridge.G2a.Old.processUncheckedSystemTransaction
  (benv : Benv) (target : Address) (data : Bytes) :
  Except EvmError (State × Bridge.G2a.Old.MessageCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  Bridge.G2a.Old.processSystemTransaction benv target systemContractCode data
end Jaune
end

section
open Jaune
namespace Jaune
def Bridge.G2a.Old.processCheckedSystemTransaction
  (benv : Benv) (target : Address) (data : Bytes) :
  Except TransitionError (State × Bridge.G2a.Old.MessageCallOutput) := do
  let systemContractCode : ByteArray := benv.state.getCode target
  -- A mis-provisioned chain: the mandatory system contract holds no code. The
  -- pinned `process_checked_system_transaction` raises `InvalidBlock` here,
  -- before attempting the call, and the corpus names the reason
  -- `BlockException.SYSTEM_CONTRACT_EMPTY`; it is a block rejection with its
  -- own typed reason and its own fixture identity. (Until goal D this arm was
  -- a fail-closed *internal* invariant, with the note that the identity was
  -- "outside this build's reviewed vocabulary" and "unobserved in every
  -- corpus"; the Glamsterdam devnet transition corpus observes it in the four
  -- `deploy_after_fork` cases of `eip8282_…/test_contract_deployment.py`, so
  -- the reason is rewritten to the block channel -- goal D, packet DP-2,
  -- owner-approved.)
  if systemContractCode.isEmpty then
    .error <| .block <| .systemContractEmpty <| .text
      s!"system contract address {target.toHex} holds no code"
  let ⟨state, systemTxOutput⟩ ←
    Except.mapError TransitionError.vm
      (Bridge.G2a.Old.processSystemTransaction benv target systemContractCode data)
  -- P0.6 item 3: the halt is extracted by the total match, never by a partial
  -- projection out of the optional error field. The rejection carries the
  -- halt itself; `BlockValidationError.detail` writes its text (3.2).
  match systemTxOutput.error with
  | some halt => .error <| .block <| .systemContractCallFailed target halt
  | none => .ok ⟨state, systemTxOutput⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- Call each request-producing system contract in turn, threading the state.

Structural recursion on the contract list rather than a loop, so that the
invariant proofs are an induction on that list instead of a fixed number of
nested case splits -- which is what makes adding Amsterdam's two contracts a
change to data and to nothing else. Each contract's non-empty return data is
appended prefixed with its own type byte, and the state each call produces is
what the next call runs against. -/
def Bridge.G2a.Old.runRequestContracts (idx : Nat) :
    List (UInt8 × Address) → Benv → List Bytes → BlockAccessListBuilder →
      Except TransitionError (State × List Bytes × BlockAccessListBuilder)
  | [], benv, acc, bal => .ok ⟨benv.state, acc, bal⟩
  | ⟨requestType, address⟩ :: rest, benv, acc, bal => do
    let ⟨state, output⟩ ← Bridge.G2a.Old.processCheckedSystemTransaction benv address []
    let acc :=
      if output.returnData.length > 0 then
        acc ++ [[requestType] ++ output.returnData]
      else
        acc
    -- EIP-7928: each checked call incorporates its own writes and reads at
    -- the post-execution index; `create_evm` read the contract's account.
    let bal := match benv.stat.rules.blockAccessListRules with
      | none => bal
      | some _ => bal.incorporate idx benv.state state
          (address :: output.accountReads.toList) output.storageReads.toList output.storageWrites.toList
    Bridge.G2a.Old.runRequestContracts idx rest (benv.withState state) acc bal
end Jaune
end

section
open Jaune
namespace Jaune
/-- Run the block's request-producing system contracts and collect their output.

The contracts come from `rules.requests` -- an ordered list of
`(type byte, address)` pairs -- and this is a fold over it rather than a
sequence of named calls. The order is the rule: the request bytes are
concatenated in call order and hashed into `requestsHash`, so calling the same
contracts in a different order is a different block. Amsterdam appends two more
entries (EIP-8282's builder deposit and exit), and appending to a list is the
whole change; nothing here learns their names.

The receipt-derived deposit request stays where it is, ahead of the fold and
outside the list. It is parsed out of the block's logs rather than produced by
a system call, so it is not one of these contracts -- which is also why the
rule data does not carry a type-0 entry.

`pragueRules.requests` reproduces exactly the two calls, in the order, this
function made before the list existed: `pragueRules_requests` in
`Jaune/Machine.lean` states that by `rfl`; a `Jaune/Check/Fork.lean` `#guard` runs it. -/
def Bridge.G2a.Old.processGeneralPurposeRequestsAt (balIndex : Nat)
  (benv : Benv) (bout : BlockOutput) :
  Except TransitionError (State × BlockOutput) := do
  let depositRequests ← parseDepositRequests bout
  let seeded : List Bytes :=
    if depositRequests.length > 0 then
      bout.requests ++ [depositRequestType ++ depositRequests]
    else
      bout.requests
  let ⟨state, allRequests, bal⟩ ←
    Bridge.G2a.Old.runRequestContracts balIndex benv.stat.rules.requests benv seeded bout.blockAccessListBuilder
  .ok ⟨state, {bout with requests := allRequests, blockAccessListBuilder := bal}⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- The block pipeline's request pass. EIP-7928: post-execution operations use
index `n + 1`, `n` the number of transactions -- one receipt key each, since a
block whose transaction is rejected is itself rejected. The transition tool,
whose driver counts the transactions it was handed, calls
`processGeneralPurposeRequestsAt` with its own count. -/
def Bridge.G2a.Old.processGeneralPurposeRequests (benv : Benv) (bout : BlockOutput) :
    Except TransitionError (State × BlockOutput) :=
  Bridge.G2a.Old.processGeneralPurposeRequestsAt (bout.receiptKeys.length + 1) benv bout
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.processGeneralPurposeRequests_legacyGasAccounting {benv : Benv}
    {bout : BlockOutput} (hb : bout.LegacyGasAccounting) {p}
    (hp : Bridge.G2a.Old.processGeneralPurposeRequests benv bout = .ok p) :
    p.2.LegacyGasAccounting := by
  unfold Bridge.G2a.Old.processGeneralPurposeRequests Bridge.G2a.Old.processGeneralPurposeRequestsAt at hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact hb
end Jaune
end

section
open Jaune
namespace Jaune
def Bridge.G2a.Old.applyTransactions :
    List (Nat × Transaction) → Benv → BlockOutput → Except TransitionError (Benv × BlockOutput)
  | [], benv, bout => .ok (benv, bout)
  | ⟨i, tx⟩ :: txis, benv , bout => do
    let ⟨st, bout'⟩ ← Bridge.G2a.Old.processTransaction benv bout tx i
    Bridge.G2a.Old.applyTransactions txis (benv.withState st) bout'
end Jaune
end

section
open Jaune
namespace Jaune
/-- The actual transaction-list fold preserves the legacy block counters at
every successful iteration. -/
theorem Bridge.G2a.Old.applyTransactions_legacyGasAccounting :
    ∀ (txis : List (Nat × Transaction)) {benv : Benv},
      benv.stat.rules.stateGas = none →
      ∀ {bout : BlockOutput} {p}, bout.LegacyGasAccounting →
        Bridge.G2a.Old.applyTransactions txis benv bout = .ok p → p.2.LegacyGasAccounting
  | [], _, _, _, _, hb, hp => by cases hp; exact hb
  | txi :: txis, benv, hnone, bout, p, hb, hp => by
    unfold Bridge.G2a.Old.applyTransactions at hp
    obtain ⟨⟨st, bout'⟩, hq, hp⟩ := Except.bind_eq_ok hp
    exact Bridge.G2a.Old.applyTransactions_legacyGasAccounting txis
      (benv := benv.withState st) hnone
      (Bridge.G2a.Old.processTransaction_legacyGasAccounting hnone hb hq) hp
end Jaune
end

section
open Jaune
namespace Jaune
/-- Starting from the producer's real initializer discharges the initial
legacy relation required by the iteration theorem. -/
theorem Bridge.G2a.Old.applyTransactions_init_legacyGasAccounting
    (txis : List (Nat × Transaction)) {benv : Benv}
    (hnone : benv.stat.rules.stateGas = none) {p}
    (hp : Bridge.G2a.Old.applyTransactions txis benv .init = .ok p) :
    p.2.LegacyGasAccounting :=
  Bridge.G2a.Old.applyTransactions_legacyGasAccounting txis hnone
    BlockOutput.init_legacyGasAccounting hp
end Jaune
end

section
open Jaune
namespace Jaune
/-- EIP-4788's pre-execution beacon-roots call (Cancun on), with its
block-level access-list incorporation at index 0; under rules without
`sys.beaconRoots` the identity: the state as given and an empty builder. -/
def Bridge.G2a.Old.beaconRootsCall (rules : ForkRules) (benv : Benv) :
    Except TransitionError (State × BlockAccessListBuilder) :=
  if rules.systemCalls.beaconRoots then do
    let ⟨st, out⟩ ←
      Except.mapError TransitionError.vm <|
        Bridge.G2a.Old.processUncheckedSystemTransaction benv
          beaconRootsAddress
          benv.stat.parentBeaconBlockRoot.toBytes
    .ok ⟨st, BlockAccessListBuilder.incorporateSystem {} rules 0 benv.state st
      (beaconRootsAddress :: out.accountReads.toList) out.storageReads.toList
      out.storageWrites.toList⟩
  else .ok ⟨benv.state, {}⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- EIP-2935's pre-execution history-storage call (Prague on), incorporated at
index 0; under rules without `sys.historyStorage` the identity. -/
def Bridge.G2a.Old.historyStorageCall (rules : ForkRules) (benv : Benv) (bal : BlockAccessListBuilder) :
    Except TransitionError (State × BlockAccessListBuilder) :=
  if rules.systemCalls.historyStorage then do
    let lastHash ←
       benv.stat.blockHashes.getLast?.toExcept
         (TransitionError.internal (.invariant (.text "block hashes is empty")))
    let ⟨st, out⟩ ←
      Except.mapError TransitionError.vm <|
        Bridge.G2a.Old.processUncheckedSystemTransaction benv
          historyStorageAddress
          lastHash.toBytes
    .ok ⟨st, bal.incorporateSystem rules 0 benv.state st
      (historyStorageAddress :: out.accountReads.toList) out.storageReads.toList
      out.storageWrites.toList⟩
  else .ok ⟨benv.state, bal⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- EIP-4895's withdrawals (Shanghai on), gated by `header.withdrawalsRoot`:
the credits, the withdrawals trie, and -- EIP-7928 -- one incorporation at
`n + 1`, every recipient read by `create_ether` whatever the amount. Under
rules without the field the identity. -/
def Bridge.G2a.Old.withdrawalsPass (rules : ForkRules) (benv : Benv) (bout : BlockOutput)
    (wds : List Withdrawal) : State × BlockOutput :=
  if rules.header.withdrawalsRoot then
    let ⟨stWds, boutWds⟩ := processWithdrawals benv bout wds
    let balWds := boutWds.blockAccessListBuilder.incorporateSystem rules
      (bout.receiptKeys.length + 1) benv.state stWds (wds.map Withdrawal.address) [] []
    ⟨stWds, {boutWds with blockAccessListBuilder := balWds}⟩
  else ⟨benv.state, bout⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- EIP-7685's request pass (Prague on), deposit-log parsing included, gated by
`header.requestsHash`; under rules without the field the identity. -/
def Bridge.G2a.Old.requestsPass (rules : ForkRules) (benv : Benv) (bout : BlockOutput) :
    Except TransitionError (State × BlockOutput) :=
  if rules.header.requestsHash then Bridge.G2a.Old.processGeneralPurposeRequests benv bout
  else .ok ⟨benv.state, bout⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- `pay_rewards`, Byzantium through Gray Glacier: the block reward plus
`reward / 32` per ommer to the block's coinbase, then to each ommer's coinbase
`(8 - age) * reward / 8`, where `age = number - ommer.number`. Written
`(8 + ommer.number - number)`, which is the same number for every age
`validateOmmers` admits (1 to 6). Each credit is `create_ether`, which is
`State.addBal`. The reward is minted: no account is debited. -/
def Bridge.G2a.Old.payRewards (pow : ProofOfWorkRules) (number : Nat) (coinbase : Address)
    (ommers : List Header) (st : State) : State :=
  let minerReward := pow.blockReward + ommers.length * (pow.blockReward / 32)
  ommers.foldl
    (fun acc ommer =>
      acc.addBal ommer.coinbase ((8 + ommer.number - number) * pow.blockReward / 8).toU256)
    (st.addBal coinbase minerReward.toU256)
end Jaune
end

section
open Jaune
namespace Jaune
/-- `apply_body`, every fork from Byzantium on, with each fork-dependent step
gated by rule data and the identity where its rule is off: the beacon-roots
call (`sys.beaconRoots`), the history-storage call (`sys.historyStorage`), the
withdrawals (`header.withdrawalsRoot`), the request pass with its deposit-log
parsing (`header.requestsHash`), and the proof-of-work rewards
(`pow = some _`), paid last. `ommers` is the block's ommer list, the EELS
pre-merge signature; after Paris `checkBlockOmmers` has already required it
empty and nothing reads it.

The rewards are not incorporated into a block-level access list: no fork
carries both `pow = some _` and `bal = some _`. -/
def Bridge.G2a.Old.applyBody
  (benv : Benv) (txs : List (Bytes ⊕ Transaction)) (ommers : List Header)
  (wds : List Withdrawal) :
  Except TransitionError (State × BlockOutput) := do
  let rules := benv.stat.rules
  -- EIP-7928: the two pre-execution system calls incorporate at index 0.
  let ⟨stBeacon, bal⟩ ← Bridge.G2a.Old.beaconRootsCall rules benv
  let benvBeacon : Benv := benv.withState stBeacon
  let ⟨stHistory, bal⟩ ← Bridge.G2a.Old.historyStorageCall rules benvBeacon bal
  let benvHistory := benvBeacon.withState stHistory
  let ⟨benvTxs, boutTxs⟩ ←
    Bridge.G2a.Old.applyTransactions (← txs.mapM (decodeTransaction benvHistory.stat.rules)).putIndex benvHistory {BlockOutput.init with blockAccessListBuilder := bal}
  let ⟨stWds, boutWds⟩ := Bridge.G2a.Old.withdrawalsPass rules benvTxs boutTxs wds
  let ⟨stReq, boutReq⟩ ← Bridge.G2a.Old.requestsPass rules (benvTxs.withState stWds) boutWds
  let stRewards := match rules.proofOfWork with
    | none => stReq
    | some pow => Bridge.G2a.Old.payRewards pow benv.stat.number benv.stat.coinbase ommers stReq
  -- `build_block_access_list`, then the item rule -- before any header check.
  let list := match rules.blockAccessListRules with
    | none => []
    | some _ => boutReq.blockAccessListBuilder.build
  checkBlockAccessListGasLimit rules benv.stat.blockGasLimit list
  .ok ⟨stRewards, {boutReq with blockAccessList := list}⟩
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.withdrawalsPass_legacyGasAccounting {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} (hb : bout.LegacyGasAccounting) (wds : List Withdrawal) :
    (Bridge.G2a.Old.withdrawalsPass rules benv bout wds).2.LegacyGasAccounting := by
  unfold Bridge.G2a.Old.withdrawalsPass
  split
  · exact processWithdrawals_legacyGasAccounting (benv := benv) hb wds
  · exact hb
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.requestsPass_legacyGasAccounting {rules : ForkRules} {benv : Benv}
    {bout : BlockOutput} (hb : bout.LegacyGasAccounting) {p}
    (hp : Bridge.G2a.Old.requestsPass rules benv bout = .ok p) : p.2.LegacyGasAccounting := by
  unfold Bridge.G2a.Old.requestsPass at hp
  split at hp
  · exact Bridge.G2a.Old.processGeneralPurposeRequests_legacyGasAccounting hb hp
  · cases hp; exact hb
end Jaune
end

section
open Jaune
namespace Jaune
/-- A successful legacy block body starts from `BlockOutput.init`, preserves
the relation through every transaction, and keeps it through withdrawals,
the request pass and the rewards, each of which is the identity on the gas
counters whether its rule is on or off. -/
theorem Bridge.G2a.Old.applyBody_legacyGasAccounting {benv : Benv}
    (hnone : benv.stat.rules.stateGas = none)
    {txs : List (Bytes ⊕ Transaction)} {ommers : List Header} {wds : List Withdrawal} {p}
    (hp : Bridge.G2a.Old.applyBody benv txs ommers wds = .ok p) : p.2.LegacyGasAccounting := by
  unfold Bridge.G2a.Old.applyBody at hp
  obtain ⟨q1, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q2, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨txsD, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  -- The initial output is `.init` with the two system calls' access-list
  -- incorporation; the relation reads none of that.
  have hqLegacy : q.2.LegacyGasAccounting :=
    Bridge.G2a.Old.applyTransactions_legacyGasAccounting txsD.putIndex
      (benv := (benv.withState q1.1).withState q2.1) hnone
      (by simp [BlockOutput.LegacyGasAccounting, BlockOutput.init]) hq
  obtain ⟨benvTxs, boutTxs⟩ := q
  dsimp only at hp hqLegacy
  have hwLegacy := Bridge.G2a.Old.withdrawalsPass_legacyGasAccounting
    (rules := benv.stat.rules) (benv := benvTxs) hqLegacy wds
  rcases hw : Bridge.G2a.Old.withdrawalsPass benv.stat.rules benvTxs boutTxs wds with ⟨stWds, boutWds⟩
  simp only [hw] at hp hwLegacy
  -- The request pass, the rewards, the item rule and the built list touch no
  -- gas counter.
  obtain ⟨q', hq', hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact Bridge.G2a.Old.requestsPass_legacyGasAccounting (p := q') hwLegacy hq'
end Jaune
end

section
open Jaune
namespace Jaune
/-- Shared typed transition algorithm. The caller supplies only the ommer
check and a typed embedding for transition failures; header validation and
execution remain common to static and scheduled callers. The ommer action is
suspended until after the containing header has passed. -/
def Bridge.G2a.Old.stateTransitionCoreE {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except ε Unit) : Except ε BlockChain := do
  let rules := f.ruleSet
  Except.mapError embed (validateHeader rules ch block.header)
  checkOmmers ()
  let benv : Benv := initBlockEnvironment f ch block.header
  let ⟨st, bout⟩ ← Except.mapError embed
    (Bridge.G2a.Old.applyBody benv block.transactions block.ommers block.withdrawals)
  let blockStateRoot : U256 := st.root
  let transactionsRoot : U256 := getTransactionsRoot bout
  let receiptRoot : U256 := getReceiptRoot bout
  let blockLogsBloom : Bytes := logsBloom bout.blockLogs
  let withdrawalsRoot : U256 := getWithdrawalsRoot bout
  let requestsHash :=
    if rules.header.requestsHash then some (computeRequestsHash bout.requests) else none
  Except.mapError (embed ∘ TransitionError.block) <|
    stateTransitionChecks bout block.header
      transactionsRoot blockStateRoot receiptRoot
      blockLogsBloom withdrawalsRoot requestsHash
  Except.mapError (embed ∘ TransitionError.block) <|
    blockAccessListCheck rules bout block.header
  .ok ⟨appendBlock ch.blocks block, st, ch.chainId⟩
end Jaune
end

section
open Jaune
namespace Jaune
/-- Embedding the static transition's error type commutes with the whole
algorithm, including failures. This is the constant-action specialization used
by a single-fork schedule. -/
theorem Bridge.G2a.Old.stateTransitionCoreE_mapError {ε : Type} (embed : TransitionError → ε)
    (f : Fork) (ch : BlockChain) (block : Block)
    (checkOmmers : Unit → Except TransitionError Unit) :
    Bridge.G2a.Old.stateTransitionCoreE embed f ch block
      (fun u => (checkOmmers u).mapError embed) =
      (Bridge.G2a.Old.stateTransitionCoreE id f ch block checkOmmers).mapError embed := by
  simp only [Bridge.G2a.Old.stateTransitionCoreE, transition_mapError_id, Function.id_comp, bind,
    transition_mapError_bind, transition_mapError_comp]
  rfl
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.stateTransitionCoreE_header {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (h : Bridge.G2a.Old.stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    validateHeader f.ruleSet ch block.header = .ok () := by
  unfold Bridge.G2a.Old.stateTransitionCoreE at h
  obtain ⟨u, hu, _⟩ := Except.bind_eq_ok h
  cases u
  exact Except.mapError_eq_ok_iff.mp hu
end Jaune
end

section
open Jaune
namespace Jaune
/-- Error embeddings and ommer resolution cannot change the chain identity
copied by any successful execution of the common algorithm. -/
theorem Bridge.G2a.Old.stateTransitionCoreE_preserves_chainId {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (h : Bridge.G2a.Old.stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    ch'.chainId = ch.chainId := by
  unfold Bridge.G2a.Old.stateTransitionCoreE at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨⟨st, bout⟩, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases h
  rfl
end Jaune
end

section
open Jaune
namespace Jaune
/-- The single boundary all four system transactions share. -/
theorem Bridge.G2a.Old.processSystemTransaction_canonical {benv : Benv} (h : benv.Canonical)
    {target : Address} {code : ByteArray} {data : Bytes} {p}
    (hp : Bridge.G2a.Old.processSystemTransaction benv target code data = .ok p) :
    State.Canonical p.1 := by
  unfold Bridge.G2a.Old.processSystemTransaction at hp
  exact Bridge.G2a.Old.processMessageCall_canonical
    (by exact ⟨⟨h.1, h.1⟩, TransientStorage.canonical_empty⟩) hp
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.processUncheckedSystemTransaction_canonical {benv : Benv}
    (h : benv.Canonical) {target : Address} {data : Bytes} {p}
    (hp : Bridge.G2a.Old.processUncheckedSystemTransaction benv target data = .ok p) :
    State.Canonical p.1 :=
  Bridge.G2a.Old.processSystemTransaction_canonical h hp
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.processCheckedSystemTransaction_canonical {benv : Benv}
    (h : benv.Canonical) {target : Address} {data : Bytes} {p}
    (hp : Bridge.G2a.Old.processCheckedSystemTransaction benv target data = .ok p) :
    State.Canonical p.1 := by
  unfold Bridge.G2a.Old.processCheckedSystemTransaction at hp
  dsimp only at hp
  split at hp
  · obtain ⟨u, hu, hp⟩ := Except.bind_eq_ok hp
    nomatch hu
  · obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    obtain ⟨qs, qo⟩ := q
    dsimp only at hp
    split at hp
    · nomatch hp
    · cases hp
      exact Bridge.G2a.Old.processSystemTransaction_canonical h (Except.mapError_eq_ok_iff.mp hq)
end Jaune
end

section
open Jaune
namespace Jaune
/-- Every prefix of the request fold leaves a canonical state.

An induction on the contract list, so the proof does not grow when the list
does: Amsterdam's two extra contracts are covered by the same argument. -/
theorem Bridge.G2a.Old.runRequestContracts_canonical (idx : Nat) :
    ∀ (rs : List (UInt8 × Address)) {benv : Benv}, benv.Canonical →
      ∀ {acc : List Bytes} {bal : BlockAccessListBuilder} {p},
        Bridge.G2a.Old.runRequestContracts idx rs benv acc bal = .ok p → State.Canonical p.1
  | [], _, h, _, _, _, hp => by cases hp; exact h.1
  | _ :: rs, benv, h, acc, bal, p, hp => by
    unfold Bridge.G2a.Old.runRequestContracts at hp
    obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    exact Bridge.G2a.Old.runRequestContracts_canonical idx rs
      (by exact ⟨Bridge.G2a.Old.processCheckedSystemTransaction_canonical h hq, h.2⟩) hp
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.processGeneralPurposeRequests_canonical {benv : Benv}
    (h : benv.Canonical) {bout : BlockOutput} {p}
    (hp : Bridge.G2a.Old.processGeneralPurposeRequests benv bout = .ok p) :
    State.Canonical p.1 := by
  unfold Bridge.G2a.Old.processGeneralPurposeRequests Bridge.G2a.Old.processGeneralPurposeRequestsAt at hp
  obtain ⟨dr, _, hp⟩ := Except.bind_eq_ok hp
  dsimp only at hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact Bridge.G2a.Old.runRequestContracts_canonical _ _ h hq
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.applyTransactions_canonical :
    ∀ (txis : List (Nat × Transaction)) {benv : Benv}, benv.Canonical →
      ∀ {bout : BlockOutput} {p},
        Bridge.G2a.Old.applyTransactions txis benv bout = .ok p → p.1.Canonical
  | [], _, h, _, _, hp => by cases hp; exact h
  | txi :: txis, benv, h, bout, p, hp => by
    unfold Bridge.G2a.Old.applyTransactions at hp
    obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    exact Bridge.G2a.Old.applyTransactions_canonical txis
      (by exact ⟨Bridge.G2a.Old.processTransaction_canonical h hq, h.2⟩) hp
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.beaconRootsCall_canonical {rules : ForkRules} {benv : Benv}
    (h : benv.Canonical) {p} (hp : Bridge.G2a.Old.beaconRootsCall rules benv = .ok p) :
    State.Canonical p.1 := by
  unfold Bridge.G2a.Old.beaconRootsCall at hp
  split at hp
  · obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    cases hp
    exact Bridge.G2a.Old.processUncheckedSystemTransaction_canonical h (Except.mapError_eq_ok_iff.mp hq)
  · cases hp; exact h.1
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.historyStorageCall_canonical {rules : ForkRules} {benv : Benv}
    (h : benv.Canonical) {bal : BlockAccessListBuilder} {p}
    (hp : Bridge.G2a.Old.historyStorageCall rules benv bal = .ok p) : State.Canonical p.1 := by
  unfold Bridge.G2a.Old.historyStorageCall at hp
  split at hp
  · obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
    obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
    cases hp
    exact Bridge.G2a.Old.processUncheckedSystemTransaction_canonical h (Except.mapError_eq_ok_iff.mp hq)
  · cases hp; exact h.1
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.withdrawalsPass_canonical {rules : ForkRules} {benv : Benv}
    (h : benv.state.Canonical) {bout : BlockOutput} (wds : List Withdrawal) :
    (Bridge.G2a.Old.withdrawalsPass rules benv bout wds).1.Canonical := by
  unfold Bridge.G2a.Old.withdrawalsPass
  split
  · exact processWithdrawalsState_canonical h wds
  · exact h
end Jaune
end

section
open Jaune
namespace Jaune
theorem Bridge.G2a.Old.requestsPass_canonical {rules : ForkRules} {benv : Benv}
    (h : benv.Canonical) {bout : BlockOutput} {p}
    (hp : Bridge.G2a.Old.requestsPass rules benv bout = .ok p) : State.Canonical p.1 := by
  unfold Bridge.G2a.Old.requestsPass at hp
  split at hp
  · exact Bridge.G2a.Old.processGeneralPurposeRequests_canonical h hp
  · cases hp; exact h.1
end Jaune
end

section
open Jaune
namespace Jaune
/-- The rewards are balance credits, so they preserve canonicality. -/
theorem Bridge.G2a.Old.payRewards_canonical {st : State} (h : st.Canonical) (pow : ProofOfWorkRules)
    (number : Nat) (coinbase : Address) (ommers : List Header) :
    (Bridge.G2a.Old.payRewards pow number coinbase ommers st).Canonical := by
  unfold Bridge.G2a.Old.payRewards
  dsimp only
  generalize hs : st.addBal coinbase _ = st'
  have h' : st'.Canonical := hs ▸ State.Canonical.addBal h _ _
  clear hs h
  induction ommers generalizing st' with
  | nil => exact h'
  | cons o os ih => exact ih _ (State.Canonical.addBal h' _ _)
end Jaune
end

section
open Jaune
namespace Jaune
/-- A successful block body leaves a canonical state: system transactions,
ordinary transactions, withdrawals, general-purpose requests and the
proof-of-work rewards all preserve the invariant, whether each is run or
gated off. -/
theorem Bridge.G2a.Old.applyBody_canonical {benv : Benv} (h : benv.Canonical)
    {txs : List (Bytes ⊕ Transaction)} {ommers : List Header} {wds : List Withdrawal} {p}
    (hp : Bridge.G2a.Old.applyBody benv txs ommers wds = .ok p) : State.Canonical p.1 := by
  unfold Bridge.G2a.Old.applyBody at hp
  obtain ⟨q1, hq1, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q2, hq2, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨txsD, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q3, hq3, hp⟩ := Except.bind_eq_ok hp
  have hb1 : q1.1.Canonical := Bridge.G2a.Old.beaconRootsCall_canonical h hq1
  have hb2 : q2.1.Canonical :=
    Bridge.G2a.Old.historyStorageCall_canonical (benv := benv.withState q1.1) (by exact ⟨hb1, h.2⟩) hq2
  have hb3 : q3.1.Canonical :=
    Bridge.G2a.Old.applyTransactions_canonical _ (by exact ⟨hb2, h.2⟩) hq3
  obtain ⟨benvTxs, boutTxs⟩ := q3
  dsimp only at hp hb3
  have hw := Bridge.G2a.Old.withdrawalsPass_canonical (rules := benv.stat.rules) (bout := boutTxs) hb3.1 wds
  rcases hwp : Bridge.G2a.Old.withdrawalsPass benv.stat.rules benvTxs boutTxs wds with ⟨stWds, boutWds⟩
  simp only [hwp] at hp hw
  -- The access-list incorporation, the item rule and the built list carry no
  -- state.
  obtain ⟨q4, hq4, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  have hc := Bridge.G2a.Old.requestsPass_canonical
    (benv := benvTxs.withState stWds) ⟨hw, hb3.2⟩ hq4
  dsimp only
  split
  · exact hc
  · exact Bridge.G2a.Old.payRewards_canonical hc _ _ _ _
end Jaune
end

section
open Jaune
namespace Jaune
/-- Canonicality depends on the common execution body, not the resolver or
its error carrier. -/
theorem Bridge.G2a.Old.stateTransitionCoreE_canonical {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch : BlockChain} (h : ch.Canonical) {block : Block} {ch'}
    {checkOmmers : Unit → Except ε Unit}
    (hp : Bridge.G2a.Old.stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    ch'.Canonical := by
  unfold Bridge.G2a.Old.stateTransitionCoreE at hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨q, hq, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  obtain ⟨_, _, hp⟩ := Except.bind_eq_ok hp
  cases hp
  exact Bridge.G2a.Old.applyBody_canonical (by exact ⟨h, h⟩) (Except.mapError_eq_ok_iff.mp hq)
end Jaune
end

section
open Jaune
namespace Jaune
/-- Success inversion shared by static and scheduled transitions. -/
theorem Bridge.G2a.Old.stateTransitionCoreE_eq_ok {ε : Type} {embed : TransitionError → ε}
    {f : Fork} {ch ch' : BlockChain} {block : Block}
    {checkOmmers : Unit → Except ε Unit}
    (h : Bridge.G2a.Old.stateTransitionCoreE embed f ch block checkOmmers = .ok ch') :
    validateHeader f.ruleSet ch block.header = .ok () ∧
      ch'.blocks = appendBlock ch.blocks block ∧
      ch'.state.root = block.header.stateRoot := by
  unfold Bridge.G2a.Old.stateTransitionCoreE at h
  obtain ⟨u1, hvh, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨q, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨u3, hchk, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases u1
  cases u3
  cases h
  exact ⟨Except.mapError_eq_ok_iff.mp hvh, rfl,
    stateTransitionChecks_stateRoot (Except.mapError_eq_ok_iff.mp hchk)⟩
end Jaune
end
