# Architecture note — the multi-fork API

Date: 2026-07-26 (Asia/Seoul), amended 2026-07-27 for Step 4.
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

`prague` and `osaka` resolve; `bpo1` and `bpo2` are declared identities without
rules. Osaka resolving does not mean Osaka is complete — see "Osaka's state"
below.

## What `ForkRules` carries

```
ForkRules := { fork : Fork, blob : BlobSchedule, code : CodeLimits,
               modexp : ModexpRules, op : OpcodeRules,
               precompiles : List Adr }
```

- `blob : BlobSchedule` — `target`, `max`, `baseFeeUpdateFraction`. Formerly the
  globals `targetBlobGasPerBlock`, `maxBlobGasPerBlock`, and
  `blobBaseFeeUpdateFraction`. BPO1/BPO2 are, on the execution layer, exactly a
  change to these three numbers, which is why they are data and not code.
- `code : CodeLimits` — `maxCodeSize`, `maxInitCodeSize` (EIP-170, EIP-3860).
  Formerly globals of the same names.
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
- `fork` — provenance for reports and error messages, not a dispatch key.

Categories still **not** added, because no implemented rule varies along them:
transaction gas cap (Step 5), blob base-fee reserve price (Step 5), block RLP
size limit (Step 5), and per-transaction blob count limit (Step 5; see the
step-4 report — it is in the EELS Prague-to-Osaka diff but not in the plan's
anticipated Step-5 checklist).

## Osaka's state

`Fork.osaka.rules?` resolves from Step 4 onward, and its rule data is Prague's
except for the three VM-level changes that step implemented: the `MODEXP`
schedule and bound, `CLZ`, and `P256VERIFY`. The rest of Osaka's
execution-layer delta is still Prague-valued until Step 5 lands it.

That intermediate state is deliberate and is why `check-mainnet.sh` still
refuses `--suite osaka` as a whole: the only Osaka fixtures run as gates are the
per-EIP subtrees reached through `--suite osaka --dir`, and each of those is
all-PASS. Nothing reports Osaka as conformant before it is.

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
| `calculateExcessBlobGas` (via `validateHeader`) | `rules.blob` |
| `checkTransactionGasLimits` | `benv.stat.rules.blob.max` |
| `checkTransactionBlobData` | `benv.stat.rules.blob` |
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
already-decoded block, so `…Using` can read the block's timestamp to select
rules without decoding the RLP twice.

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

## Strictness

- Unknown fork label → `Fork.ofString?` gives `none`; `Main.lean`'s `getFork`
  aborts. There is no case folding and no fallback to Prague.
- Declared but unimplemented fork → `UnsupportedForkError`, raised while
  resolving rules, before anything is decoded or executed. On the block-import
  API this is the harness `.error` channel, never a `.inr` block-rejection
  verdict: a fork this build has not implemented says nothing about whether the
  block is valid.
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

Mainnet activation timestamps appear nowhere in this step. When Step 6 adds
them, they belong in a named mainnet `ChainConfig`, never in `ForkRules`.
