# Jaune for proof authors

This guide is for people who want to prove properties of EVM execution
against Jaune. It is organized by the task you are trying to do. Each section
starts with the proof task this revision demonstrates, names the example that
checks it, and lists the narrow imports that task needs.

Everything here describes **this revision only**. Read
[Compatibility](#compatibility) before depending on a name.

- [How declarations are classified](#how-declarations-are-classified)
- [1. Symbolic decoding and stepping](#1-symbolic-decoding-and-stepping)
- [2. Complete raw-frame execution](#2-complete-raw-frame-execution)
- [3. Frame, message and transaction execution](#3-frame-message-and-transaction-execution)
- [4. Checked block and chain transitions](#4-checked-block-and-chain-transitions)
- [5. State, accounts, rules, bytes, hashes and codecs](#5-state-accounts-rules-bytes-hashes-and-codecs)
- [6. Lemma families for downstream proof libraries](#6-lemma-families-for-downstream-proof-libraries)
- [Compatibility](#compatibility)

## How declarations are classified

Lean has no module-level export control. Every public declaration reachable
from an import can be named, whether or not it is meant for you. This guide
therefore classifies whole modules and named families. It does not list
individual declarations one by one.

| class | meaning | what it covers |
|---|---|---|
| **supported** | Intended entry point for a task in this guide. Exercised at this revision by a checked example, a gate or the fixture runner. | The canonical execution modules: `Jaune.FrameRun.Basic`, `Jaune.FrameRun.Adequacy`, `Jaune.FrameRun.Prefix`, `Jaune.FrameRun.Views`, `Jaune.FrameRun.SettlementViews`, `Jaune.FrameRun.Order`, `Jaune.FrameRun.Decompose`, `Jaune.SymbolicPush`, `Jaune.SymbolicArithmetic`. Also the entry-point families named in sections 3–5, such as `exec`, `Frame.runTop`, `TopLevel.run`, `Transaction.run`, the checked chain types, and `State`/`Storage` access, and the lemma families and modules named in section 6. |
| **incidental** | Public only because Lean cannot hide it. It may be renamed, restated or removed in any commit, without notice. | Every other public declaration (section 6 lifts named families out of this class) in the `Jaune` library closure, such as interpreter internals in `Jaune.Machine`, `Jaune.Execution` and `Jaune.MessageCall.Totality`, and helper lemmas in `Jaune.Basic` and `Jaune.Types`. Also the `Fueled` residue lemmas in `Jaune.Fuel`, and the cached driver `Jaune.Implementation.CachedDriver` (an implementation module with the public `execFueledCached` and private equation `execFueled_eq_cached`, reached through `Jaune.MessageCall.Exec`). Runner-side modules outside `import Jaune` (`Jaune.T8n`, `Jaune.ChainStore`, `Jaune.FixtureException`, `Jaune.FixtureTransition`, `Jaune.MessageCall.Trace`, `Jaune.MessageCall.TraceJson`, `Jaune.MessageCall.TraceEvent`, `Jaune.Run.BodyFactsT8n`, `Jaune.Adapter.IO`, `Main`, `MemoryProbe`, `TraceMain`) are adapters, and the executable checks (`Jaune.BLSGuards` and the `Jaune.Check.*` modules, library `JauneChecks`) are checks; neither is proof surface. `scripts/layering.json` classifies every module. |
| **experimental** | Implemented and gated, but expected to change as its upstream target moves. | The Amsterdam lane: `amsterdamRules`, the `StateGasRules` / `stateGas` dimension, `prepareCallAmsterdam` / `prepareCreateAmsterdam` and their lemmas, the state-gas arms of `settle` and `resume`, and the `BlockAccessList` / `BlockAccessList*` family. Also the reusable axiom-audit command `#expect_axioms` (`scripts/AxiomAudit.lean`, library `Assurance`). |

A module's class applies to all of its declarations unless this guide says
otherwise. `private` declarations are never API.

**The umbrella `import Jaune` is convenient, but it enforces no public
subset.** It pulls in the whole library closure, supported and incidental
alike. It does not include the runner-side modules above, the `Examples`
library or the `Assurance` library. Prefer the narrow imports each section
lists: they state what your file depends on, and they keep the import closure
smaller.

The stable core of the supported surface is the canonical execution type, its
constructors and adequacy, the derivation operations and the symbolic rules.
These are also the declarations the destination axiom audit pins. Their 52 rows
are listed in [`scripts/ExecutionAxioms.lean`](scripts/ExecutionAxioms.lean),
and each row's provenance is in
[`scripts/assurance-manifest.json`](scripts/assurance-manifest.json).

## 1. Symbolic decoding and stepping

**Demonstrated task.** Decode `PUSH1 a; PUSH1 b; ADD; STOP` with symbolic
operand bytes, then prove its result from symbolic gas `g` and incoming stack
`s`, under the premises `9 ≤ g` and `s.length < 1023`. See
[`Examples/Arithmetic.lean`](Examples/Arithmetic.lean). The decode facts are
`first`, `second`, `third` and `last`; the step equations are `step0`, `step2`, `step4` and `step5`, named by program counter.
The PUSH-only version is [`Examples/Execution.lean`](Examples/Execution.lean).
[`Examples/README.md`](Examples/README.md) walks through both.

**Imports.** `import Jaune.SymbolicPush` and/or `import Jaune.SymbolicArithmetic`.
Each imports `Jaune.FrameRun.Basic`.

**Decoding.** The decode predicates are `NextOp.At`, `HaltOp.At`, `JumpOp.At`,
`PlainOp.At` and `MessageOp.At` (in `Jaune.MessageCall.Measures`). Each says that
`code.getOp pc` returns the named instruction. To turn a decode fact into the
step equation that the `Frame.Run` constructors take, use `step_of_next` (a
decoded `NextOp` steps by `NextOp.step`) or `step_of_halt` (a decoded
`HaltOp` exits with its own result), both in `Jaune.FrameRun.Basic`. There is no such
lemma for a decoded jump. The examples decode concrete bytecode
with one `simp` lemma list followed by `rfl`
([`Examples/Execution.lean#L18`](Examples/Execution.lean#L18)); reuse that list.

**PUSH** (`Jaune.SymbolicPush`). The operand bytes, the state, the fork and
the program counter are all variables.

- `step_success` needs `cost bytes ≤ gasLeft` and `stack.length < 1024`.
- `step_outOfGas` returns the input state unchanged.
- `step_stackOverflow` keeps the gas charge in the halted state.

The gas check comes before the stack-capacity check. These three, and the
arithmetic rules below, are equations about `NextOp.step`; `step_of_next`
turns each into a `step` equation. `prepend` puts a decoded PUSH in front of
any run from its successor, a prefix or a whole run. `cost`, `post` and `afterCharge`
name the charged quantities.

**`ADD`, `SUB`, `MUL`** (`Jaune.SymbolicArithmetic`). The family is the inductive
`Op`. `step_eq` reduces every member to `applyBinary`.

- `step_success` needs a two-operand stack, `op.cost ≤ gasLeft` and room.
- `step_outOfGas` carries the popped stack in its halted state.
- `step_stackUnderflow` fires before any gas is charged.

`prepend` composes as for PUSH. Other binary opcodes (`DIV`, `MOD`, shifts,
comparisons) are **not** members of `Op`. The first negative check in
`Examples/Arithmetic.lean` (line 200) keeps it that way: the `ADD` rule
applied to `DIV` must fail to elaborate.

These are direct-frame step equations. They make no claim about transaction
validity or message settlement, and they are not an all-opcodes rule set.

## 2. Complete raw-frame execution

**Demonstrated task.** Compose a multi-step run by inversion.
[`Examples.Arithmetic.result`](Examples/Arithmetic.lean#L163) takes an *arbitrary* whole
`Frame.Run` from the start state. It peels off the three continuing steps with the
example-local inversion `next` (line 140), then settles `STOP` with the example-local
`halt_inv`. So every run has the stated outcome, not just the one that was built.
[`interpreter`](Examples/Arithmetic.lean#L173) reads the answer of the total interpreter
`exec` through adequacy. [`concrete`](Examples/Arithmetic.lean#L179) shows that the
premises can be met, at `g = 9` and `s = []`. The second negative check (line 214) keeps
the build red if eight gas were ever accepted.
[`Examples/Prefix.lean`](Examples/Prefix.lean) is one induction over prefixes: no
same-frame prefix raises the gas measure.

**Imports.** `import Jaune.FrameRun.Basic` gives the type, its constructors and prefix
composition. Add `Jaune.FrameRun.Adequacy` for adequacy, `Jaune.FrameRun.Prefix` for
induction over prefixes, `Jaune.FrameRun.Views` and `Jaune.FrameRun.SettlementViews` for
node lists and retained frames, `Jaune.FrameRun.Order` for the sub-run order, and
`Jaune.FrameRun.Decompose` for cutting a whole run into a prefix and a rest.

**The type.** `Jaune.Frame.Run r e : Type` is the canonical run of one frame.
`r : Frame.Running` is where it starts: a program counter, the call context and the
frame's state. `e : Frame.Run.End` is where it ends: `.at s`, a later running state of the
same frame (a prefix, `Frame.Run.Prefix r s`), or `.exit out`, the frame's raw outcome (a
whole run). It has seven constructors:

| constructor | case |
|---|---|
| `stop` | the empty prefix: the run ends where it starts |
| `halt` | the step exits the frame, or faults |
| `next` | the step continues in the same frame |
| `callDone` / `callDoneEnd` | the spawned frame finished at entry, e.g. a precompile or an entry failure; the caller goes on, or resuming it ends the run |
| `callRan` / `callRanEnd` | the spawned frame ran, and its whole run is kept as a premise; the caller goes on, or resuming it ends the run |

Every premise other than a sub-run is an equation about a non-recursive function of the
four-part message call (section 3): `step`, `enter`, `settle`, and `resumeCaller`, which
runs `resume` and ends the run on a fault or a halted caller. Child results, settlement,
gas and the resumed parent state all stay visible in the run. For frame-level statements,
`Frame.Returns child r` says that `r` is a result the driver hands back from `child`, and
`NextOp.Run` packages one nonterminal instruction with any child it spawns (both in
`Jaune.MessageCall.DriverInvariants`).

**Inversion.** The library has no inversion lemma. Use `cases` on the run and close the
other alternatives with the step equation: a run that ends in an exit has six (Lean rules
out `stop`). `Examples.Arithmetic.next` shows the pattern for a continuing step and the
example's `halt_inv` for a step that exits. Whole runs and prefixes are unique
(`Frame.Run.Prefix.unique` and the `Subsingleton` instances in `Jaune.FrameRun.Unique`),
and `Frame.Run.exit_unique` says two whole runs from one start have one outcome.

**Adequacy.** `Frame.Run.exec_iff r out` states
`Nonempty (Frame.Run r (.exit out)) ↔ exec r = out`. It is fuel-free: `exec` is total, and
the sufficiency proof discharges the fuel bound once (`execFueled_run_sufficientFuel`).
`Frame.Run.canonical r` is the whole run of `exec r`. At frame level,
`Frame.Returns.of_exec` names the result of a child entered and run through `exec`, and
`Frame.runTop_eq` gives `Frame.runTop f` as the entry's own result, or as
`exec r >>= settle f` for a frame entered into the interpreter.

**Traversal and observations.**
- `Frame.Run.strongRec` is induction on the call depth left.
- `Frame.Run.Node` packs a whole run with its start and outcome. `Node.Sub` is the
  immediate sub-run relation and `Node.lt` its transitive closure; `Node.lt.wellFounded`
  and `Node.strongRec` give well-founded induction over it.
- `Frame.Run.rawNodes` lists every reached node in execution order, with each child before
  its resumed parent.
- `Frame.Run.retainedNodes`, `Frame.Run.descendantFrames` and `Frame.Run.committedFrames`
  keep only what settlement commits. A CREATE whose code deposit rolls back is dropped
  even if the raw child finished
  (`Frame.Run.descendantFrames_callRan_create_codeDepositRollback`).
- `Node.parentNext` and `Node.Prefix` relate same-frame nodes inside one whole run: the
  immediate continuation, and the nodes on its `spine` (`Node.prefix_iff_mem_spine`).

The run type and its views are not a contract or Hoare-logic API.

**Prefixes.** `Frame.Run.Prefix r s` is a run of one frame from `r` to a later running
state `s` of the same frame; every child entered on the way has run to completion and been
resumed. `Frame.Run.append` follows a prefix with a run from its endpoint, with the laws
`stop_append`, `append_stop` and `append_assoc`. `Frame.Run.prefix_induction` proves a
property of every endpoint from a same-frame step case and a call case, and
`Frame.Run.exec_of_prefix` says the interpreter gives one outcome from both ends of a
prefix. A prefix carries no step count, and it does not stop inside a child.

## 3. Frame, message and transaction execution

**Demonstrated task.** [`Examples/ShapePilot.lean`](Examples/ShapePilot.lean)
runs two message calls with `TopLevel.run`. Two `#guard` checks cover a Prague
CALL whose child writes storage and a log and then reverts with one byte, and an
Amsterdam CREATE whose code deposit runs out of gas. Its theorems
`call_return_survival` and `create_return_survival` apply the `resume` lemmas
below at any spawn that a top-level frame's run reaches, without unfolding a
concrete state.

The transaction-entry example is finite and checked. It is not a theorem. The
checked-in `transfer-blockchain` case selects Prague, sends one wei to a
contract, runs that contract's `SSTORE`, and compares the full result and
post-state allocation against registered goldens:

```sh
scripts/check-t8n.sh --case transfer-blockchain
```

See [Examples/README.md, Transaction entry](Examples/README.md#transaction-entry).

**Imports.** Use `import Jaune.MessageCall.Exec` for `exec` and `Frame.runTop`,
`import Jaune.MessageCall.ResumeFacts` for what `resume` does with a child's result, and
`import Jaune.MessageCall.DriverInvariants` for the same facts at a spawn a run reaches.
`Jaune.FrameRun.Basic` already imports the four parts and the driver. Use
`import Jaune.Run.Message` for the top-level message call and `import Jaune.Transaction`
for transaction and block processing.

**The message call in four parts.** The shared records are in `Jaune.MessageCall`
(`Substate`, `Trail`, `BlockContext`, `TransactionContext`, `Frame.Result`, `Fault`); the
frame types are in `Jaune.MessageCall.Context` and `Jaune.MessageCall.Frame`.

- A `Frame` is one `Message` and one checkpoint: the `Frame.State` a failed frame falls
  back to. The checkpoint is the saved caller after call preparation, or for a top-level
  frame the state its message was prepared on. `Frame.State` groups a frame's dynamic
  state by what happens to it when the frame fails: the `Machine` is local to the frame,
  the `World` and the `Substate` are dropped, and the `Trail` is kept. Call versus create
  is the message's `kind`. A message's `CallContext` is what `step` reads: caller,
  recipient, value, calldata, code, `depthLeft`, the static flag, and the
  `TransactionContext` and `BlockContext`. A `Frame.Running` is a program counter, that
  context and a `Frame.State`.
- `step` (`Jaune.MessageCall.Step`) runs one instruction of a `Frame.Running`. It exits
  with a `Frame.Exit` (`finished`, `reverted` or `halted`, each with the state it stopped
  in), goes on at a new program counter, or spawns a child `Frame` with a `Pending`
  continuation.
- `enter` (`Jaune.MessageCall.Parts`) transfers the value. It then hands back a
  `Frame.Running` to run, or a result at once: a precompile's, or a fault from a failed
  transfer. A precompile reads a `PrecompileInput` (calldata, gas left, fork) and nothing
  else of the frame (`Precompile.run`, `Jaune.PrecompileInput`).
- `settle` (`Jaune.MessageCall.Parts`) turns a frame's `Frame.Exit` into a `Frame.Result`
  (`success`, `revert` or `halt`), or into a `Fault`. A creation deposits its code here.
- `resume` (`Jaune.MessageCall.Parts`) hands the result back to the saved caller. It
  merges the child's state into the caller's by lifetime, then runs the calling opcode's
  push and output write.
- `execFueled` (`Jaune.MessageCall.Driver`) is the fuel-bounded driver over these four,
  and `exec` (`Jaune.MessageCall.Exec`) is the total interpreter over it. The compiled
  code runs a cached twin of the driver, `Jaune.Implementation.CachedDriver`, through a
  proved `@[csimp]` equation; see [TRUSTED.md](TRUSTED.md).
- `Frame.runTop` (`Jaune.MessageCall.Exec`) runs a top-level frame: it enters the frame
  from its checkpoint, runs `exec`, and settles. `Frame.runTopWithRoot` also returns the
  running frame it entered with, when it ran code. A top-level frame is a
  `TopLevel.Input`'s message on its checkpoint; `Message.initialCheckpoint` builds that
  checkpoint.

**What is proved about it.**

- `Jaune.MessageCall.MessageExecution` connects `exec` to `Frame.runTop`, in namespace
  `MessageExecution`:
  - `runTop_eq_settle_exec_of_enter` gives the equation.
  - `enterWith_eq_run_of_notPrecompile`, `enterWith_eq_run_of_noCodeAddress`
    and `enterWith_eq_run_of_disablePrecompiles` discharge the entry.
  - `settle_ok_call`, `settle_revert` and `settle_halt` give the outcome
    cases, and `worldAfter_of_failed` says that a failed result leaves the
    checkpoint's world.
- `Jaune.MessageCall.ResumeFacts` says what `resume` does, relative to the
  saved caller and with no induction over the interpreter. `resume_failed`: a
  failed child leaves the caller's world and substate as saved, except the
  one touch of RIPEMD-160's address that a rule keeps, and the caller takes
  the child's trail. `returnedMachine_failed_call` and
  `returnedMachine_failed_create` give the calling opcode's effect on the
  caller's machine. `resume_success` covers a successful child.
  `Frame.Running.Reaches.resume_failed` and `Frame.Running.Reaches.resume_success` restate them at
  a spawn a run reaches, with their stack-room and state-gas premises
  discharged by run invariants.
- `Jaune.FrameRun.Basic` gives commitment: `Frame.rawFinished` (the raw outcome finished),
  `Frame.settlementCommits` and `Frame.raw_commits_of_settlementCommits`.

**Transactions.** `TopLevel.run` runs a top-level message call from a `TopLevel.Input`:
the message, its checkpoint and the authorization list. `TopLevel.prepare` either refuses
before any frame or supplies a frame. Without state gas, preparation handles the creation
collision check or resolves authorization and delegation for a call. Under Amsterdam's
state-gas rules it uses `TopLevel.prepareAmsterdamFrame`. The frame enters from its
checkpoint, runs, and settles as in `Frame.runTop`. The resulting `TopLevel.Run` is a
refusal, or the frame with its authorization refund and its `Frame.TopRun`: the running
frame it entered with, when there was one, and the settled result.

`Transaction.run block state bout tx index` applies one transaction on a `BlockContext`
and the state before it, through `Transaction.admit`, `Transaction.prepare`,
`TopLevel.run`, and `Transaction.settleRun`. Settlement reads the message run through
`TopLevel.Run.settlement`, a `TopLevel.Settlement` (state, gas left, logs, accounts to
delete, reads and writes), and `TopLevel.Run.refundCounter`. A successful transaction
returns its `TransactionRun`, which includes the message run, gas settlement and receipt,
together with the updated `BlockOutput`.

The command-line entry for transactions is `lake exe jaune t8n`; see
[README.md](README.md#the-t8n-transition-tool). `jaune t8n --forks` prints the
forks it accepts. `Jaune.T8n` is runner code, not proof surface.

## 4. Checked block and chain transitions

**Demonstrated task.** Jaune has no Lean example for this layer. The fixture
runner imports fixture blocks through the checked core.
`Main.lean`'s `evaluateFixtureBlock` decodes once, builds a `CanonicalBlock`,
and calls `addBlockToChainChecked` on a `CheckedBlockChain` parent. The
substantial proof consumer is Blanc: its
[`Blanc/Solvent.lean`](https://github.com/skbaek/blanc/blob/main/Blanc/Solvent.lean)
proves that a WETH contract stays solvent across `stateTransitionAt`,
`stateTransitionUsing`, `stateTransition` and `addBlockToChainAt`. That is a
safety invariant over every reachable state, not a liveness claim. Blanc pins
its own Jaune revision; its README records which one.

**Imports.** `import Jaune.Transaction`. It brings in `Jaune.Fork` for `Fork`,
`ForkRules` and `ChainConfig`.

**Checked entry points (recommended).**

- `CanonicalBlock.ofRlp?` is the checked wire ingress. `CanonicalBlock` has a
  private constructor; the only way to build one is `CanonicalBlock.ofDecode`,
  which demands the strict decoder's equation.
- `CheckedBlockChain` pairs a chain with evidence of retained-history validity
  and tip/state-root agreement. Build it with `CheckedBlockChain.ofGenesis` /
  `ofGenesis?`, or check an existing chain with `BlockChain.check`.
- `stateTransitionChecked` and `addBlockToChainChecked` advance a checked
  chain. `CheckedBlockChain.ofTransition` and `CheckedBlockChain.ofImport`
  carry the evidence forward without recomputing it.
- `ConfiguredChain` (private constructor; build with `ConfiguredChain.of?`)
  adds a validated `ChainConfig` activation schedule. It is driven by
  `stateTransitionConfigured` and `CheckedBlockChain.ofConfiguredTransition`.

**Raw entry points.** `stateTransitionAt`, `stateTransitionUsing`,
`stateTransition`, `addBlockToChainAt`, `addBlockToChainUsing`,
`addBlockToChain` and `rlpToBlock` remain for existing callers and statements
that name them. `stateTransitionChecked_eq`, `stateTransitionConfigured_eq`
and `addBlockToChainAt_eq_canonical` relate them to the checked forms.

**Proved facts.**

- Canonicity is preserved: `stateTransitionAt_canonical`,
  `stateTransitionUsing_canonical`, `applyBody_canonical`,
  `Transaction.run_canonical` and `TopLevel.run_canonical`.
- The chain ID is preserved: `stateTransitionUsing_preserves_chainId`,
  `addBlockToChainUsing_preserves_chainId`.

## 5. State, accounts, rules, bytes, hashes and codecs

**Demonstrated task.** The `final_world` / `final_substate_trail` observations in both
examples. The symbolic rules state their premises on the fields themselves
(`r.state.machine.stack`, `r.state.machine.gasLeft`), so the example proofs unfold no
accessor.

**Imports.** Import the narrowest module that defines what you need:

| need | module | supported families |
|---|---|---|
| frame and message state | `Jaune.MessageCall`, `Jaune.MessageCall.Context`, `Jaune.MessageCall.Frame`, `Jaune.MessageCall.State` | `Frame`, `Frame.Running`, `Frame.State` (`machine` / `world` / `substate` / `trail`, and accessors such as `Frame.State.stack`, `Frame.State.gasLeft`, `Frame.State.state`, `Frame.State.balance`), `Machine`, `Substate`, `Trail`, `Frame.Exit`, `Frame.Result`, `Message`, `CallContext`, `BlockContext`, `TransactionContext` |
| chain and world state | `Jaune.Machine` | `World`, `Header`, `Block`, `Transaction`, `BlockChain`, `State` (`State.get`, `State.set`, `State.get_set_self`, `State.get_set_ne`, `State.balance`, `State.setBalance`), `Storage.set`, `Storage.get_set_self`, `Storage.get_set_ne` |
| account and instruction types | `Jaune.Types` | `Account` (`nonce`, `balance`, `storage`, `code`), `Storage`, `Storage.get`, `Address`, `PlainOp`, `HaltOp`, `JumpOp` |
| fork rules and schedules | `Jaune.Fork` | `Fork`, `Fork.rules?`, `Fork.supported`, `ForkRules`, `ForkCriterion`, `ChainConfig` (`forkAt`/`rulesAt` at a block number and timestamp), `mainnetChainConfig` |
| words, bytes and RLP | `Jaune.Basic` | `Bytes`, `U256`, `Bytes.toU256`, `U256.toBytes`, `Rlp.Item`, `Rlp.Item.toBytes`, `Bytes.toRlpItem?` |
| hashes | `Jaune.Hash`, `Jaune.SHA256Spec`, `Jaune.KeccakSpec` | `Bytes.keccak`, `Bytes.sha256`, `Bytes.sha256_eq_fips`, `Bytes.keccak_eq_fips`, `ByteArray.keccak_eq_fips` |
| state root | `Jaune.Transaction` | `State.root` |

`Storage.get_set_ne` and `State.get_set_ne` take the same hypothesis orientation:
*written key ≠ read key*. For `Storage.get_set_ne s h v : (s.set k v).get a = s.get a`,
`h : k ≠ a`; for `State.get_set_ne w h ac`, `h : a ≠ b`, where `a` is written
and `b` is read. `State.set` erases an account set to `Account.nil`
(`State.getElem?_set`).

[TRUSTED.md](TRUSTED.md) says exactly what `Bytes.sha256_eq_fips`,
`Bytes.keccak_eq_fips` and `KECCAK.permutation_eq_referencePermutation` do and do not establish, and its
primitive provenance table gives every primitive's reference and evidence.

## 6. Lemma families for downstream proof libraries

**Who this is for.** A library that proves facts about concrete contracts on
top of Jaune (Blanc is the first) does not stay inside the canonical execution
modules: it rewrites machine states, word arithmetic and RLP bytes thousands of
times. The families below are the ones such a consumer names by `rw`/`simp
only`, so they are **supported**: a rename or restatement updates this guide
in the same commit. Their `@[simp]` attributes, where present, are not part of
the promise; a consumer that works by `simp only` names the lemma.

**Naming rule.** An update-projection law is named update-first,
`<updater>_<accessor>`: `Frame.State.withMachine_world`, `Frame.State.withTrail_substate`.

**Rule for additions.** A consumer that needs an update-projection pair, a
comparison-flag fact or a word-literal law that is missing here adds it to the
Jaune module named below, under the naming rule, instead of proving a local
copy; a new `Frame.State` updater lands with its projection laws beside it in `Jaune.MessageCall.State`. A
public codec meant for concrete evidence gets a structural twin and a
`decide +kernel` control next to it, as `Jaune.RlpEval` does.

| need | module | supported families | why |
|---|---|---|---|
| a `Frame.State` update against a field | `Jaune.MessageCall.State` | `Frame.State.withMachine_*`, `withWorld_*`, `withSubstate_*`, `withTrail_*` (all `@[simp]`) | a state is four lifetime groups, so updating one leaves the other three by one law |
| what an instruction family can change | `Jaune.Instructions.WordFacts`, `ShuffleFacts`, `PushFacts`, `LogFacts`, `MemoryFacts`, `ReadFacts`, `StoreFacts` | per family, the success and failure laws of its row | an effect law is proved once for the family, not once per opcode |
| word values and the order | `Jaune.Types` | `U256.toNat_toU256`, `U256.toNat_toU256_of_lt`, `U256.toNat_inj`, `U256.toNat_lt`, `U256.toNat_add`, `U256.toNat_sub_eq_of_le`, `U256.lt_iff_toNat_lt_toNat`, `U256.le_iff_toNat_le_toNat`, `U256.toNat_lt_toNat`, `U256.lt_of_toNat_lt_toNat` | the bridge from compiled words to `Nat` arithmetic |
| comparison flags and literal arithmetic | `Jaune.WordFacts` | `U256.{eq,lt,gt}Check_{ne,eq}_zero_iff`, `U256.eq_of_eqCheck_ne_zero`, `U256.not_lt_of_ltCheck_eq_zero`, `U256.lt_of_{lt,gt}Check_ne_zero`, `U256.{lt,gt}Check_eq_zero_of_toNat_le`, `U256.{lt,gt}Check_ne_zero_of_toNat_lt`, `Nat.toU256_{add,mul}_toU256`, `Nat.toU256_sub_toU256`, `U256.toNat_add_toU256_of_lt` | a branch flag (`EQ`, `LT`, `GT`, `ISZERO` of `EQ`) is discharged by one citation |
| multiplicative arithmetic | `Jaune.MulDiv` | floor/ceiling `a * b / d` bounds, rounding direction, monotonicity, round-trip loss, and the guarded `U256` bridges (`U256.toNat_mul_mod`, `U256.toNat_mul_eq_of_mul_no_overflow`, `U256.toNat_div`, `U256.toNat_mulmod`, `U256.toNat_addmod`, …) | ratio pricing in token and vault contracts; every word statement is explicit about `% 2 ^ 256` or carries a no-overflow premise |
| iterated rounded multiplication | `Jaune.RPow` | `mulRounded`, `rpow` and their error surface, with guarded `U256` bridges (`U256.toNat_mulRounded`, …) | Maker-shaped `rpow` loops; no word theorem hides wraparound |
| memory charged before a CALL | `Jaune.MessageCall.MessageMemory`, `Jaune.MessageCall.MemoryAccounting` | the `calculateMessageCallGas_*` bounds and the per-kind memory accounting facts; across a spawn and the driver, `step_memory_accounting_output`, `exec_memory_accounting_output` and the call-spawn reply bounds in `Jaune.MessageCall.MemoryAccounting` | exact gas accounting across a call boundary; these facts do not bound arbitrary parent gas or complete the recursive memory/output invariant |
| original-run STATICCALL stack and output-memory effects | `Jaune.MessageCall.StaticcallEffects` | `NextOp.staticcall_run_effects` | from the actual six-operand instruction run, on every fork including state gas: one status word replaces the operands; the output is a write of at most the requested byte count over both prepaid memory windows. No child-success or precompile premise; no gas or whole-world preservation claim |
| excluding an interpreter child from an enabled native STATICCALL | `Jaune.MessageCall.NativePrecompile` | `MessageOp.step_staticcall_not_run_of_precompile` | from the actual six-operand stack, `rules.stateGas = none`, enabled `rules.isPrecompile` and effective direct code designation, the actual `MessageOp.step` spawn and `enter child = .run c` equations imply `False`; native failure outcomes are included, with no native-success premise |
| evaluating concrete RLP in the kernel | `Jaune.RlpEval` | `Bytes.toRlpItem?_eq_toRlpItemStructural`, `Bytes.toRlpItemDiff?_eq_toRlpItemDiffStructural`, `Bytes.toRlpItems?_eq_toRlpItemsStructural`, `Rlp.Item.toBytes_eq_toBytesStructural`, `Rlp.Items.toBytes_eq_toBytesStructural`, `Nat.toBytes_eq_toBytesStructural`, and `DecidableEq Rlp.Item` | see below |

**Native STATICCALL entry.** `MessageOp.step_staticcall_not_run_of_precompile`
uses the selected fork's effective `delegatedCodeAddress = none`; it covers
both flat access pricing and EIP2929 access warming. For Blanc's lifted
`staticcall_spawn_not_run_of_precompile` wrapper, derive that effective-direct
premise from the existing conditional raw nondelegation premise and pass the
actual spawn and entry equations. The lifted `StepRun` / `CallCodeH` code-resolution
adapter stays in Blanc. The theorem does not construct a spawn or assert that
native execution succeeds, and its `stateGas = none` premise remains explicit.

**Concrete RLP.** `Bytes.toRlpItemDiff?` / `Bytes.toRlpItems?`, `Rlp.Item.toBytes` and
`Nat.toBytes` are compiled by well-founded recursion, so `decide +kernel`
cannot evaluate them. `Jaune.RlpEval` restates each by structural recursion and
proves it equal to the public definition on every input. A concrete decode or
encode is then

```lean
example : Bytes.toRlpItem? [0xc1, 0x01] = some (.list [.bytes [0x01]]) := by
  rw [Bytes.toRlpItem?_eq_toRlpItemStructural]; decide +kernel
```

The public definitions and their equation lemmas are unchanged.

## Compatibility

### Toolchain and dependencies

The only supported pair is the one this revision declares: the Lean
toolchain named in `lean-toolchain`, and Mathlib as required in
`lakefile.lean` and resolved to an exact revision in `lake-manifest.json`.
A consumer must use the same Lean toolchain. The files are the record; read them rather
than this paragraph:

```sh
cat lean-toolchain
python3 -c "import json;print([(p['name'],p['rev'],p.get('inputRev')) for p in json.load(open('lake-manifest.json'))['packages']])"
```

### Installing from Git

Depend on an exact commit:

```lean
require jaune from git "https://github.com/skbaek/jaune.git" @ "<full commit id>"
```

[Examples/README.md, Installing as a Git dependency](Examples/README.md#installing-as-a-git-dependency)
has the complete route. It uses `scripts/external-consumer.py`, which prepares
a disposable package, and a verifier. The verifier checks the resolved URL and
revision, a clean installed checkout, matching toolchains, Git-only
dependencies, and the built consumer. The `external-consumer` CI job runs that
route on pushes to `main` and on pull requests. Its verdict for a revision is
that revision's CI run. It compiles `scripts/consumer/Consumer.lean`, which
imports `Jaune.SymbolicPush` and `Jaune.FrameRun.Adequacy`. Do not replace the Git dependency with a
sibling path or symlink.

### Constructor, reduction and simp behavior

- `Frame.Run` lives in `Type`, not `Prop`. Runs are data, so you can define them with
  `def`, traverse them (`Frame.Run.rawNodes`) and invert them with `cases`. Adequacy wraps
  the type in `Nonempty`.
- The `Frame.Run` constructors take step equations, not decode facts. Bridge with
  `step_of_next` / `step_of_halt`, as `SymbolicPush.prepend` and `SymbolicArithmetic.prepend`
  do.
- The symbolic `cost`, `post`, `afterCharge`, `popped`, `Op.evaluate` and `Op.cost`
  are plain definitions with no `@[simp]`. Unfold them by name, as the
  examples do. Final-state projections such as `final_stack` close by `rfl`.
- `@[simp]` is set on `Frame.Run.stop_append` and `Frame.Run.append_stop` in
  `Jaune.FrameRun.Basic`, and on the `Frame.State.with*` projection laws in
  `Jaune.MessageCall.State`. The settlement-view lemmas are not simp lemmas; name them.
- The run modules declare no notation.
- `CanonicalBlock` and `ConfiguredChain` have private constructors. Use their
  checked constructors.

### Fork coverage of the proof layer

- **Rule-parametric.** `Frame.Run`, adequacy, the run views and the PUSH /
  `ADD` / `SUB` / `MUL` rules are stated over a `CallContext`, whose `block.rules` is the rule data. Historical fork instances retain each declaration's explicit decoding,
  gas, stack and execution premises; this is not an unconditional theorem for
  every opcode or every specialization. Frame spawn lemmas have distinct
  ordinary and Amsterdam CALL/CREATE forms; use their stated hypotheses.
- **Conditional settlement.** The revert and exceptional-halt forms in
  `Jaune.MessageCall.MessageExecution` (`MessageExecution.settle_revert`,
  `MessageExecution.settle_halt`) require
  `f.message.context.block.rules.stateGas = none`, and they leave the settled
  trail unstated. The entry forms each require a successful value transfer,
  and either a code address that is not a precompile, no code address, or
  `f.message.disablePrecompiles = true`. The rule condition holds for every
  declared preset except Amsterdam, whose state-gas dimension prevents
  applying these forms unchanged. No Amsterdam revert/exceptional-halt
  settlement form is claimed here.
- **What the theorems are about.** They are statements about Jaune's model.
  How faithfully that model follows each fork is evidence from testing, not
  proof. Amsterdam support is a snapshot at `tests@v21.0.2` of a fork still
  unscheduled upstream, not final Amsterdam. See
  [README.md, Verification status](README.md#verification-status) and
  [TRUSTED.md](TRUSTED.md#testing-versus-proof).
- **Blanc's scope.** Blanc's contract coverage and fork scope are Blanc's
  claims; Blanc states them.

### Experimental status, updates and deprecation

This API is pre-release. There are no release tags, no version numbers and no
semantic-versioning promise, and `main` moves. Pin a full commit id.

- **Supported names** can change in any commit. When a supported name changes,
  the same commit updates the examples and this guide. No deprecation period
  and no compatibility alias is promised; none exists at this revision.
- **Incidental names** carry no such commitment.
- **Experimental names** will change as Amsterdam settles upstream.
- **Audited rows.** Adding, removing or re-pinning a row in
  `scripts/ExecutionAxioms.lean` is a reviewed decision, recorded in
  [`scripts/GATES.md`](scripts/GATES.md#destination-axiom-audit).

**Examples are checked per revision only.** The ordinary `lake build` compiles
`Examples` alongside the library, so revision X's examples are known to work
with revision X. Copying them unchanged to another revision may fail. There is
no cross-revision source compatibility. To upgrade, change your pinned commit
and rebuild your own code.
