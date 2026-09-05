# Architecture note — the multi-fork API

Date: 2026-07-26 (Asia/Seoul), amended 2026-07-27 for Steps 4, 5, and 6.
Plan: `~/plans/migration.md`, Step 2.

This note fixes the public fork API. Per the plan, a material redesign of
anything named here is a human-attention stop condition from this point on.
Later steps amend it only by filling in rule data the Step-2 shape already
anticipated; the entry points and the way rules reach the interpreter are
unchanged.

## The three separated ideas

`Elevm/Fork.lean` deliberately keeps apart what a fork *is*, what its rules
*say*, and *when* a chain adopts them.

| concept | type | role |
|---|---|---|
| identity | `Fork` (`prague`, `osaka`, `bpo1`, `bpo2`) | a name; carries no semantics |
| rules | `ForkRules` | the data execution actually reads |
| schedule | `ChainConfig` | which rules a given chain uses at a given block |

`Fork` also has `toString`, a strict `ofString?`, `all`, and `index`. `index` is
the *only* ordering notion on forks and exists solely so a schedule can be
checked for monotonicity — it is not a licence to compare forks in execution.

## The single place fork ordering becomes rule data

```
Fork.rules? : Fork → Option ForkRules
```

This is the one function that turns an identity into semantics. Adding a fork
means adding a case here plus the rule data it names — never a second
interpreter, never a comparison at a use site. `Fork.rules` wraps it as a
failing lookup; `none` reports `UnsupportedForkError` rather than answering with
another fork's rules, because running Osaka blocks under Prague semantics would
turn a missing implementation into a silent consensus fault.

**Four of the five declared forks resolve.** `prague` and `osaka` carry
complete static execution rules; `bpo1` and `bpo2` are `osakaRules` with one
field replaced:

```
bpo1Rules = { osakaRules with fork := .bpo1, blob := bpo1BlobSchedule }
bpo2Rules = { osakaRules with fork := .bpo2, blob := bpo2BlobSchedule }
```

Writing them as record updates is what makes "blob parameter only" a property
of the code rather than a claim about it: a guard undoes the update and
requires the whole record to equal `osakaRules`, so no BPO fork can acquire a
rule of its own, and a later Osaka correction reaches both automatically.

`amsterdam` is the fifth, and it resolves to `none` on purpose. Declaring an
identity without its rules is what the `Option` in `Fork.rules?` was for, and
this is the first time it is used: the label parses, has an index, and appears
in transition labels, while every attempt to run it is `UnsupportedForkError`.
So the `UnsupportedForkError` branch is reachable again rather than merely
retained.

That makes two different lists, and conflating them is the mistake the code is
arranged to prevent:

```
Fork.all           = [prague, osaka, bpo1, bpo2, amsterdam]   -- declared
Fork.supported     = Fork.all.filter (·.rules?.isSome)        -- runnable
Fork.unimplemented = Fork.all.filter (·.rules?.isNone)
```

Both derived lists come from `Fork.rules?` rather than being written out, so
they cannot drift from what actually resolves. The distinction is carried
through every user-facing surface: a diagnostic about an *unrecognised* label
names the declared list, one about a label this build cannot *run* names the
runnable list, and `t8n --forks` — the handshake a framework reads to decide
what to send this binary — advertises only the runnable one.

A fixture case at an unimplemented fork is refused at the top of the per-case
run, before a header, a prestate or a block is read, and for both endpoints of
a transition label. Routed through the import path instead it would surface as
"block 0 was expected valid but failed", which reads as a verdict about a block
this build never examined.

## What `ForkRules` carries

```
ForkRules := { fork : Fork, blob : BlobSchedule, code : CodeLimits,
               tx : TransactionLimits, block : BlockLimits,
               modexp : ModexpRules, op : OpcodeRules,
               gas : GasSchedule, header : HeaderRules,
               requests : List (UInt8 × Adr),
               precompiles : List Adr }
```

- `blob : BlobSchedule` — `target`, `max`, `baseFeeUpdateFraction`, and
  `reserveBaseCost`. The first three replace the former blob-gas globals;
  `reserveBaseCost : Option Nat` activates EIP-7918 without a fork branch.
  BPO1/BPO2 remain data-only reparameterisations of this schedule.
- `code : CodeLimits` — `maxCodeSize`, `maxInitCodeSize` (EIP-170, EIP-3860).
  Formerly globals of the same names.
- `tx : TransactionLimits` (added in Step 5) — optional `maxGas` and
  `maxBlobCount`. Prague states both limits as inactive; Osaka carries EIP-7825
  and EIP-7594's `2^24` and `6` boundaries.
- `block : BlockLimits` (added in Step 5) — optional `maxRlpSize`. Osaka carries
  EIP-7934's 8,388,608-byte maximum on the original input encoding.
- `modexp : ModexpRules` (added in Step 4) — `maxLength`, `flatComplexity`,
  `complexityCoeff`, `iterationCoeff`, `gasDivisor`, `minGas`. Every number the
  `MODEXP` pricing reads, so EIP-7823's input bound and EIP-7883's repricing are
  a second record rather than a branch inside the precompile.
- `op : OpcodeRules` (added in Step 4) — currently just `clz`. An opcode this
  record switches off has an undefined byte at that fork, so reaching it is an
  invalid instruction. Decoding stays fork-independent; the check is in
  `Rinst.runCore`, before the operand pop, so instruction positions and every
  downstream statement about them do not depend on which rules are running.
- `precompiles : List Adr` — the activation set, written out against the
  specification's address table. Formerly the hard-wired range in
  `Adr.isPrecomp`, which stated a Prague fact at a use site. Precompile sets are
  not contiguous in general (Osaka's P256VERIFY sits at 0x100), so the rule is
  carried as the set itself. `ForkRules.isPrecomp` is the membership predicate.
  Step 4 also made EIP-2929's pre-warmed access list in `prepareMessage` read
  this field, which was the last surviving literal copy of the Prague set.
- `gas : GasSchedule` (added for Amsterdam) — the ten numbers a supported fork
  moves *inside a formula both forks share*: `coldAccountAccess`, `callValue`,
  `createAccess`, `storageClearRefund`, `txBase`, `txAccessListAddress`,
  `txAccessListStorageKey`, `floorTokenCost`, `perAuthIntrinsic`, and
  `codeReadSurcharge`. The scope is deliberately narrow, and the narrowness is
  the design: a number belongs here when a later fork reprices it *and* both
  forks compute with it the same way, so one field serves both without a
  branch. Numbers no supported fork moves stay global, and so do numbers only
  one fork's formula mentions — `gasStorageSet`, `gasStorageUpdate`,
  `gNewAccount`, `gasCodeDeposit`, the 12,500 authorisation refund — because
  moving them would state a fork difference that does not exist.
  `codeReadSurcharge` is additive with identity `0`, which is what makes the
  Prague formula literally unchanged rather than merely equal to what it was.
  Every field's Prague value is `rfl`-equal to the global that has always held
  it (`pragueRules_gas_*` in `Jaune/Machine.lean`, exported `@[simp]`), so no
  Prague-stated proof and no Prague fixture can observe that the number now
  arrives through a record.
- `header : HeaderRules` (added for Amsterdam) — `blockAccessListHash` and
  `slotNumber`, one `Bool` per EIP (7928 and 7843). Two flags rather than one
  because nothing in the protocol makes the two fields arrive together.
  `validateHeader` requires each field to be present exactly when its flag is
  set, in both directions: a header carrying a field the rules do not define is
  as invalid as one missing a field they do.
- `requests : List (UInt8 × Adr)` (added for Amsterdam) — the
  request-producing system contracts, as `(type byte, address)` pairs, in call
  order. The order is the rule, not an implementation detail: the request bytes
  are concatenated in that order and hashed into `requestsHash`.
  `processGeneralPurposeRequests` folds over this list, so EIP-8282's two extra
  contracts are an appended pair and nothing else. The receipt-derived deposit
  request (type 0) is deliberately absent — it is parsed out of the block's
  logs rather than produced by a system call.
- `fork` — provenance for reports and error messages, not a dispatch key.

Every static Prague/Osaka execution category identified by the pinned EELS diff
is rule data. So is everything Amsterdam adds, and `amsterdamRules` is now the
fifth complete record: `bpo2Rules` with `amsterdamGasSchedule` and
`amsterdamStateGasRules` (the metering goal's), `amsterdamCodeLimits`
(EIP-7954: `0x10000` / `0x20000`), `amsterdamOpcodeRules` (`clz`, `slotnum`,
`stackAccess`), `amsterdamHeaderRules` (both EIP-7928/7843 header fields
required), `amsterdamRequests` (Prague's two system calls followed by
EIP-8282's builder deposit and exit contracts, in call order) and `bal := some
{ itemCost := 2000 }` — the one record for the block-level access list
(`BalRules`), whose presence is what switches on read recording, the builder,
the item rule and the header's hash check. `Fork.rules? .amsterdam = some
amsterdamRules`; `Fork.supported` is five forks and `Fork.unimplemented` is
empty; the transition tool's fork-local metering resolver is retired and it
reads `Fork.rules` like everything else. `ForkRules.Valid` gained two
conjuncts for the new record — `bal`, when present, has a non-zero
`itemCost`, and `bal.isSome` equals the header rule's `blockAccessListHash`
flag — each refused under its own `RuleDefect`, so a record that carries a
list without the header field, or the field without the list, is not a rule
set the semantics accept.

The block-level access list itself is the one Amsterdam category that is not
a number. Its read set is recorded in `Devm.meta` (`accountReads`,
`storageReads`) by two recorders that are the identity when `rules.bal` is
`none`, defined so that every `mach`/`world` projection is `rfl` — which is
why the gas and state proofs written before the list existed still hold
unchanged. The recording sites are the pinned `state_tracker`'s
`get_account*` calls, one by one; reads survive reverts because every child
merge unions them and a halted top-level preparation keeps them. The builder
beside `BlockOutput` incorporates each transaction as a diff against the
block's cumulative state at index `i + 1`, the two pre-execution system calls
at 0 and the post-execution operations at `n + 1`, then sorts, encodes in the
dataclass field order and hashes; the item rule fires inside the body and the
header comparison is the last of the pinned `execute_block` checks. Consensus
observes only that hash. The corpus's three identities for a bad list are
answered by the fixture runner from the fixture's published copy of the list
— header-inconsistent → `INVALID_BAL_HASH`, canonicalised-equal-to-computed →
`INCORRECT_BLOCK_FORMAT`, otherwise `INVALID_BLOCK_ACCESS_LIST` — from the
typed rejection and the decoded header, never from a rendered message.

**Every number in this record is machine-checked**, not transcribed:
`scripts/gen-fork-constants.py` extracts each declared fork's constants from
the pinned `execution-specs` revision — by importing the fork module, since
several are computed rather than literal — and
`scripts/check-fork-constants.sh` compares them against
`lake exe jaune --rules <fork>`. Its coverage table classifies *every* field,
so a field added later cannot become silently unchecked; the six `MODEXP`
parameters are classified as checked elsewhere, because upstream gives them no
names to read and they are covered as behaviour by the vector suite and the
repricing subtrees.

The three interpreter-step numbers that were left on the globals —
`coldAccountAccess`, `callValue` and `createAccess` — are read through
`rules.gas` at the account-access sites, and the premise that made the
deferral necessary exists: **`GasSchedule.Valid`**. The three Amsterdam
instructions are gated the same way — `SLOTNUM` by `rules.op.slotnum`,
`DUPN`/`SWAPN`/`EXCHANGE` by `rules.op.stackAccess` — decoded at every fork
(EIP-8024's two-byte forms are sized by `getInst` fork-independently) and
refused as `InvalidOpcode` where the rule is off. The jumpdest claim has two
halves and they have different standing: `pinnedJumpDestsFrom_eq_legacy`
**proves** that the pinned Amsterdam destination walk and the pre-Amsterdam
walk agree on every byte array (so the three immediates change no
destination); the bridge from those walks to Jaune's own `jumpable`/
`noPushBefore` scan is **sampled** by `scripts/check-jumpdest.sh`, not proved
(goal C's independent review, P2; re-implementing `jumpable` on the walk is
reserved to the owner).

It is deliberately small, and it was discovered rather than designed. The
gas-decreasing theorems are stated over an arbitrary `Sevm`, so a zero-valued
schedule would break termination; instantiating the family at exactly that
schedule and reading the failures gives three inequalities and no more —
`100 ≤ coldAccountAccess`, `0 < createAccess`, `2300 ≤ callValue`, which are
`gasWarmAccess`, positivity, and `gCallStipend`. Each is refused under its own
`RuleDefect`, so a rule set the semantics cannot use says which number is the
problem. `ForkRules.Valid` carries it, every named fork's record carries the
witness, and `ValidRules.check` is still the one way a caller-supplied record
obtains one.

Two consequences are worth stating because they are what kept the change from
spreading:

* `accessCost` keeps its name and its arity. The schedule-carrying form is a
  sibling, `GasSchedule.accessCost`, and `pragueRules_gas_accessCost` is the
  `rfl` proof that the two are the same function at Prague. A downstream proof
  that names `accessCost` is untouched.
* `exec` keeps its signature and stays total. Sufficiency now needs a
  hypothesis and a `def` cannot demand one, so the exhaustion branch became a
  typed internal invariant error — the pattern this executable already uses for
  the unreachable — with `exec_of_valid` proving a usable rule set never
  reaches it. Because that branch returns the frame's own `Devm`, the
  *canonicality* family needs no premise at all and every one of its signatures
  is unchanged.

`accessCost`'s cold half is the one number a metering vehicle can move without
any other part of the record moving with it, which is why the account-access
sites were the right place to land this first.

## Osaka's state

`Fork.osaka.rules?` resolves to the complete static Osaka execution rule set:
Step 4's `MODEXP`, `CLZ`, and `P256VERIFY` delta plus Step 5's transaction gas
cap, six-blob transaction limit, blob reserve-price formula, and original block
RLP limit. `check-mainnet.sh --suite osaka` is active only because all 2,514
manifest files (17,323 cases) pass.

## Labels, schedules, and the named mainnet configuration

Step 6 completed activation. Three additions, all in `Elevm/Fork.lean`:

| name | role |
|---|---|
| `ForkTransition` | one activation boundary: `before`, `after`, `timestamp` |
| `NetworkSpec` | what a fixture `network` label names: `.static f` or `.transition t` |
| `mainnetChainConfig` | mainnet's own schedule, with its four activation timestamps |

`ForkTransition.ofString?` parses the `<before>To<after>AtTime<n>` labels the
fixtures use, strictly: exactly one `AtTime`, exactly one `To`, a decimal
timestamp with the fixtures' optional `k` thousands suffix, and both endpoints
parseable by `Fork.ofString?`. A historical label such as
`CancunToPragueAtTime15k` therefore fails at the parser rather than being run
through one of its endpoints. `ForkTransition.chainConfig` turns the parsed
label into the schedule it describes; whether that schedule is *usable* stays
`ChainConfig.validate`'s answer, so a label naming an activation at genesis or
a backwards step is refused where every other unusable schedule is.

`mainnetChainConfig` is the one place mainnet timestamps appear. The supported
chain begins at Prague, so Prague is the schedule's floor rather than an
activation — this build has no pre-Prague rules to run before it, and a
schedule may not name rules that do not exist. `mainnetPragueTimestamp` records
the real activation for provenance and is checked against the schedule.

## Prague's and Osaka's shared blob schedule

`pragueBlobSchedule` and `osakaBlobSchedule` carry the same target and ceiling,
which is why the first *observable* blob-schedule boundary on the supported
chain is Osaka to BPO1. This is a fact about the protocol (EIP-7892 restates
Osaka's schedule without moving it), not a shortcut: the two records stay
separate, and Osaka's is stated through the EIP's blob-count product.

## How rules reach the interpreter

`rules : ForkRules` is a **field of `BenvStat`**. Every environment that
execution already threads reaches a `BenvStat`:

| environment | path to the rules |
|---|---|
| `BenvStat` | `.rules` |
| `Benv` | `.stat.rules` |
| `Msg` | `.benv.stat.rules` |
| `Sevm` | `.benvStat.rules` |
| `Evm` | `.sta.benvStat.rules` |

This is what keeps one interpreter. No opcode evaluator, precompile dispatcher,
transaction pipeline, or block transition was duplicated or given a fork
parameter; the functions that consume a rule read it from the environment they
already had. `Devm` deliberately does **not** carry rules — it is the mutable
machine state, and the two functions that need a rule while holding only a
`Devm` (`processCreateMessage.chargeCodeGas`) take `ForkRules` explicitly from
their caller.

Rule consumers, and where each reads its rule:

| consumer | rule |
|---|---|
| `BLOBBASEFEE` in `Rinst.runCore` | `sevm.benvStat.rules.blob` |
| `calculateExcessBlobGas` (via `validateHeader`) | `rules.blob`, including `reserveBaseCost` |
| `checkTransactionGasLimits` | `benv.stat.rules.blob.max` |
| `checkTransactionGasCap` (via `validateTransaction`) | `rules.tx.maxGas` |
| `checkTransactionBlobData` | `benv.stat.rules.blob` and `rules.tx.maxBlobCount` |
| `checkBlockRlpSize` (via `addBlockToChainCore`) | `rules.block.maxRlpSize` plus original byte length |
| `calculate_data_fee` (via `processTransaction`) | `benv.stat.rules.blob` |
| `processCreateMessage.chargeCodeGas` | `rules.code.maxCodeSize` |
| `genericCreate` | `sevm.benvStat.rules.code.maxInitCodeSize` |
| `checkInitcodeSize` (via `validateTransaction`) | `rules.code` |
| `executeCode` precompile dispatch | `msg.benv.stat.rules.isPrecomp` |

## Public entry points

Four layers, each named by how it obtains rules. This naming is now fixed.

| suffix | selects rules by | intended caller |
|---|---|---|
| `…With rules` | given explicitly | the core implementation |
| `…At fork` | a named `Fork` | static fixture suites |
| `…Using cfg` | a `ChainConfig` and the block timestamp | a configured chain |
| *(none)* | Prague | existing callers and downstream proofs |

```
stateTransitionWith  : ForkRules   → BlockChain → Block → Except String BlockChain
stateTransitionAt    : Fork        → BlockChain → Block → Except String BlockChain
stateTransitionUsing : ChainConfig → BlockChain → Block → Except String BlockChain
stateTransition      :               BlockChain → Block → Except String BlockChain

addBlockToChainWith  : ForkRules   → BlockChain → B8L → Except String (BlockChain ⊕ String)
addBlockToChainAt    : Fork        → BlockChain → B8L → Except String (BlockChain ⊕ String)
addBlockToChainUsing : ChainConfig → BlockChain → B8L → Except String (BlockChain ⊕ String)
addBlockToChain      :               BlockChain → B8L → Except String (BlockChain ⊕ String)
```

`addBlockToChainCore` sits under the `addBlockToChain*` family and takes an
already-decoded block plus the authoritative original RLP length. Thus `…Using`
can read the block timestamp without decoding twice, while EIP-7934 never
measures a shorter re-encoding. The public entry-point signatures are unchanged.

### The Prague wrappers are the core, not a copy

`stateTransition` and `addBlockToChain` keep their original names, types, and
behaviour. Four `example`s in `Execution.lean` prove this by `rfl`:

```
stateTransition ch block          = stateTransitionWith pragueRules ch block
stateTransitionAt .prague ch block = stateTransition ch block
addBlockToChain chain rlp          = addBlockToChainWith pragueRules chain rlp
addBlockToChainAt .prague chain rlp = addBlockToChain chain rlp
```

`rfl` rather than sample-data equality is the point: it holds for every input,
so no wrapper can diverge from the core somewhere untested. Prague is permanent
supported protocol, not scaffolding, and Blanc's four protected theorems state
their results about these unwrapped names.

### Which entry point a fixture uses

`Main.lean` resolves `--network` to a `NetworkSpec` and dispatches on it:
`.static f` imports at `addBlockToChainAt f`, `.transition t` imports through
`addBlockToChainUsing (t.chainConfig chainId)`. Static suites therefore keep
naming their fork explicitly, and only a transition lets the block's timestamp
choose — which is the whole content of a transition fixture, and the reason a
transition label may not be forced through one static endpoint.

`--vectors` keeps the static-only resolution (`getFork`): one vector file runs
at one fork, so a transition label there is an error rather than an ambiguity.

## Strictness

- Unknown fork label → `Fork.ofString?` gives `none`; `Main.lean`'s `getFork`
  aborts. There is no case folding and no fallback to Prague.
- Unknown *network* label → `NetworkSpec.ofString?` gives `none` after trying
  both the static and the transition grammar; the fixture runner aborts.
- Declared but unimplemented fork → `UnsupportedForkError`, raised while
  resolving rules, before anything is decoded or executed. On the block-import
  API this is the harness `.error` channel, never a `.inr` block-rejection
  verdict: a fork this build has not implemented says nothing about whether the
  block is valid. No fork this build declares is in that state today.
- A fixture that declares its own blob schedule is checked against the rules
  the run will apply, for every fork the label can select. The archive, not
  this repository, is the authority for the numbers a BPO fork consists of.
- Unusable schedule → `InvalidChainConfigError`. A schedule must be non-empty,
  active from timestamp 0, and strictly increasing in both timestamp and fork
  order. Equal timestamps would make the active fork depend on list order, and a
  non-increasing fork sequence would describe a chain running backwards.
- Selection is by the last activation at or before the block timestamp, so the
  activation block itself already runs the new rules.

## Downstream (Blanc) consequences

`BenvStat`-carried rules meant Blanc needed no new fork parameter on any
`Sevm`-indexed lemma. The repairs were the three upstream shape changes and
their proof sites, and reusable lemmas were **generalised over rules** —
`{rules : ForkRules}` binders on `chargeCodeGas_*`, `validateTransaction_*` —
rather than being copied per fork, as the plan's design decision 6 requires.

Adding BPO1 and BPO2 required no Blanc repair at all, which is the clearest
evidence that they are data: nothing downstream reads a blob schedule.

Blanc's solvency results are now stated over an arbitrary `ForkRules`
(`stateTransitionWith_inv_solvent`, `addBlockToChainWith_inv_solvent`), with
the named-fork and configured-chain entry points as instances and the two
protected Prague theorems as the `pragueRules` instance of the same proof.
`BlockChain.ReachUsing` is reachability along a configured chain, so a sequence
crossing Prague, Osaka, BPO1, and BPO2 is one induction rather than one
relation per fork. The four protected statements are textually unchanged and
each still has exactly `[propext, Classical.choice, Quot.sound]`.
