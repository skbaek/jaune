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
- [Compatibility](#compatibility)

## How declarations are classified

Lean has no module-level export control. Every public declaration reachable
from an import can be named, whether or not it is meant for you. This guide
therefore classifies whole modules and named families. It does not list
individual declarations one by one.

| class | meaning | what it covers |
|---|---|---|
| **supported** | Intended entry point for a task in this guide. Exercised at this revision by a checked example, a gate or the fixture runner. | The eight canonical execution modules: `Jaune.ExecFrame`, `Jaune.Exec`, `Jaune.ExecDeriv`, `Jaune.ExecSettlement`, `Jaune.ExecChronology`, `Jaune.MessageExecution`, `Jaune.SymbolicPush`, `Jaune.SymbolicArith`. Also the entry-point families named in sections 3–5, such as `exec`, `processMessage`, `processTransaction`, the checked chain types, and `State`/`Stor` access. |
| **incidental** | Public only because Lean cannot hide it. It may be renamed, restated or removed in any commit, without notice. | Every other public declaration in the `Jaune` library closure, such as interpreter internals in `Jaune.Machine`, `Jaune.Execution` and `Jaune.Sufficiency`, and helper lemmas in `Jaune.Basic` and `Jaune.Types`. Also the `Fueled` residue lemmas in `Jaune.Exec`. Runner-side modules outside `import Jaune` (`Jaune.T8n`, `Jaune.ChainStore`, `Jaune.FixtureException`, `Jaune.BLSGuards`, `Main`, `MemoryProbe`) are adapters, not proof surface. |
| **experimental** | Implemented and gated, but expected to change as its upstream target moves. | The Amsterdam lane: `amsterdamRules`, the `StateGasRules` / `stateGas` dimension, `genericCallAmsterdam` / `genericCreateAmsterdam` and their lemmas, `executeCode.handleErrorAmsterdam`, and the `BlockAccessList` / `Bal*` family. Also the reusable axiom-audit command `#expect_axioms` (`scripts/AxiomAudit.lean`, library `Assurance`). |

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
These are also the declarations the destination axiom audit pins. Their 53 rows
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

**Imports.** `import Jaune.SymbolicPush` and/or `import Jaune.SymbolicArith`.
Each imports `Jaune.Exec`.

**Decoding.** The decode predicates are `Ninst.At`, `Linst.At`, `Jinst.At`,
`Rinst.At` and `Xinst.At` (in `Jaune.ExecFrame`). Each says that
`code.getInst pc` returns the named instruction. To turn a decode fact into the
step equation that the `Exec` constructors take, use `Evm.step_next`,
`Evm.step_last` or `Evm.step_jump`. The examples decode concrete bytecode
with one `simp` lemma list followed by `rfl`
([`Examples/Execution.lean#L14`](Examples/Execution.lean#L14)); reuse that list.

**PUSH** (`Jaune.SymbolicPush`). The operand bytes, the state, the fork and
the program counter are all variables.

- `step_success` needs `cost bytes ≤ gasLeft` and `stack.length < 1024`.
- `step_outOfGas` returns the input state unchanged.
- `step_stackOverflow` keeps the gas charge in the raw error.

The gas check comes before the stack-capacity check. `prepend` composes a
decoded PUSH with any complete continuation. `cost`, `post` and `afterCharge`
name the charged quantities.

**`ADD`, `SUB`, `MUL`** (`Jaune.SymbolicArith`). The family is the inductive
`Op`. `step_eq` reduces every member to `applyBinary`.

- `step_success` needs a two-operand stack, `op.cost ≤ gasLeft` and room.
- `step_outOfGas` carries the popped stack in its raw error.
- `step_stackUnderflow` fires before any gas is charged.

`prepend` composes as for PUSH. Other binary opcodes (`DIV`, `MOD`, shifts,
comparisons) are **not** members of `Op`. The second negative check in
`Examples/Arithmetic.lean` keeps it that way: the `ADD` rule applied to `DIV`
must fail to elaborate.

These are direct-frame step equations. They make no claim about transaction
validity or message settlement, and they are not an all-opcodes rule set.

## 2. Complete raw-frame execution

**Demonstrated task.** Compose a multi-step run by inversion.
[`Examples.Arithmetic.result`](Examples/Arithmetic.lean#L131) takes an
*arbitrary* `Exec` derivation from the start state. It peels off the three
continuing steps with the example-local inversion `next` (line 118), then
settles `STOP` with `Exec.halt_inv`. So every derivation has the stated
outcome, not just the one that was built.
[`interpreter`](Examples/Arithmetic.lean#L141) reads the answer of the total
interpreter `exec` through adequacy. [`concrete`](Examples/Arithmetic.lean#L175)
shows that the premises can be met, at `g = 9` and `s = []`. The first negative
check (line 185) keeps the build red if eight gas were ever accepted.

**Imports.** `import Jaune.Exec` gives the type, the constructors, inversion
and adequacy. Add `Jaune.ExecDeriv` for induction and subderivation order,
`Jaune.ExecSettlement` for commitment and retained frames, and
`Jaune.ExecChronology` for node order. `Jaune.ExecChronology` imports the other
two.

**The type.** `Jaune.Exec pc sevm devm out : Type` is the canonical complete
execution derivation. `pc` is the initial program counter, not a step count.
It has six constructors:

| constructor | case |
|---|---|
| `halt` | the step halts |
| `cont` | the step continues in the same frame |
| `doneErr` / `doneOk` | the spawned frame finished at entry, e.g. a precompile or an entry failure |
| `runErr` / `runOk` | the spawned frame ran a child derivation that is kept as a premise |

Every premise other than a sub-derivation is an equation about a
non-recursive function (`Evm.step`, `Frame.enter`, `Resume.run`,
`Frame.settle`). Child results, settlement, gas and the resumed parent state
all stay visible in the derivation. `Xlot.Filled` and `Ninst.Run` package an
optional child derivation for frame-level statements.

**Inversion.** `Exec.halt_inv` says the root step's halt value is the outcome.
`Exec.last_inv` does the same from a `Linst.At` decode. For a continuing step,
use a six-way `cases`; `Examples.Arithmetic.next` shows the pattern. It lives
in the example, not the library.

**Adequacy.** `exec_iff_exec_eq pc sevm devm out` states
`Nonempty (Exec pc sevm devm out) ↔ exec ⟨pc, sevm, devm⟩ = out`. It is
fuel-free: `exec` is total, and the sufficiency proof discharges the fuel bound
once. `Xlot.filled_exec` gives a closed derivation for any `exec` result.
`of_runFrame`, `of_processMessage` and `of_processCreateMessage` produce the
frame-level witnesses.

**Traversal and observations.**

- `Exec.strong_rec` is induction on frame depth over `Exec.Fa` / `Fortify`.
- `Exec.Deriv` packs a derivation with its indices. `Exec.Deriv.Prec` (`≺`)
  is the immediate-subderivation relation. `Exec.Deriv.lt.well_founded` and
  `Exec.Deriv.strongRec` give well-founded induction over it.
- `Exec.rawNodes` lists every reached node in execution order, with each child
  before its resumed parent.
- `Exec.retainedNodes`, `Exec.descendantFrames` and `Exec.committedFrames`
  keep only what settlement commits. A CREATE whose code deposit rolls back is
  dropped even if the raw child succeeded
  (`Exec.descendantFrames_runOk_create_codeDepositRollback`).
- `Exec.Deriv.ParentStep` and `Exec.Deriv.ParentPrefix` relate same-frame nodes
  *inside* one completed derivation.

`Exec.Pred` and `Exec.Fa` alone do not make a contract or Hoare-logic API.

**No running-prefix interface is delivered.** An `Exec` derivation always ends
in an outcome, so it is not a reflexive-transitive closure of a state-to-state
step relation. There is no relation for "after these steps, from `pc`, the
machine is in state X" without running to completion. There are no zero-step,
single-step or concatenation laws for such a relation, and no step-count
convention. It was left out because the composition task chosen for this
programme is a **completed raw frame**, which `Exec` expresses directly.
`ParentPrefix` does not fill this gap: it orders nodes of a derivation that is
already complete.

## 3. Frame, message and transaction execution

**Demonstrated task.** The transaction-entry example is finite and checked. It
is not a theorem. The checked-in `transfer-blockchain` case selects Prague,
sends one wei to a contract, runs that contract's `SSTORE`, and compares the
full result and post-state allocation against registered goldens:

```sh
scripts/check-t8n.sh --case transfer-blockchain
```

See [Examples/README.md, Transaction entry](Examples/README.md#transaction-entry).
No example in this repository composes the message-settlement theorems below;
they are proved, but no checked example exercises them yet.

**Imports.** Use `import Jaune.MessageExecution` for raw-to-settled message
bridges. `import Jaune.ExecFrame` gives the frame relations; `Jaune.Exec`
already imports it. Use `import Jaune.Transaction` for transaction and block
processing.

**Frames and messages.**

- `processMessage` and `processCreateMessage` (defined in `Jaune.Sufficiency`)
  are the total message functions. `runFrame` is the shared frame driver
  beneath them.
- `RunFrame`, `ProcessMessage` and `ProcessCreateMessage` are their relational
  forms over an optional child derivation (`Xlot`). `RunFrame.iff_settleMsg`
  and `ProcessMessage.iff_body` unfold them.
- `Jaune.MessageExecution` connects `exec (initEvm msg)` to `processMessage msg`:
  - `processMessage_eq_settle_exec` and its `afterTransfer`, `of_enter` and
    `of_notPrecompile` variants give the equation.
  - `processMessage_clean_of_exec`, `processMessage_revert_of_exec` and
    `processMessage_halt_of_exec` give the outcome cases. `settledRevert` and
    `settledHalt` name the settled machines and come with `@[simp]`
    projections.
- `Jaune.ExecSettlement` gives commitment: `Execution.commits`,
  `Frame.settlementCommits` and `Frame.raw_commits_of_settlementCommits`.

**Transactions.** `processMessageCall` is the top-level message dispatch.
`processTransaction benv bout tx index` validates and applies one transaction.
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
that name them. `stateTransitionChecked_eq_raw`, `stateTransitionConfigured_eq`
and `addBlockToChainAt_eq_canonical` relate them to the checked forms.

**Proved facts.**

- Canonicity is preserved: `stateTransitionAt_canonical`,
  `stateTransitionUsing_canonical`, `applyBody_canonical`,
  `processTransaction_canonical`.
- The chain ID is preserved: `stateTransitionUsing_preserves_chainId`,
  `addBlockToChainUsing_preserves_chainId`.

## 5. State, accounts, rules, bytes, hashes and codecs

**Demonstrated task.** The `final_world` / `final_meta` observations in both
examples. The symbolic example proofs also unfold the `Devm` accessors
(`Devm.stack`, `Devm.gasLeft`, `Devm.setMach`).

**Imports.** Import the narrowest module that defines what you need:

| need | module | supported families |
|---|---|---|
| machine and world state | `Jaune.Machine` | `Evm`, `Sevm`, `Devm` (`mach` / `meta` / `world` and accessors such as `Devm.stack`, `Devm.gasLeft`, `Devm.state`, `Devm.getBal`), `Execution`, `Msg`, `Benv`, `Tenv`, `Header`, `Block`, `Tx`, `BlockChain`, `State` (`State.get`, `State.set`, `State.get_set_self`, `State.get_set_ne`, `State.bal`, `State.setBal`), `Stor.set`, `Stor.get_set_self`, `Stor.get_set_ne` |
| account and instruction types | `Jaune.Types` | `Acct` (`nonce`, `bal`, `stor`, `code`), `Stor`, `Stor.get`, `Adr`, `Rinst`, `Linst`, `Jinst` |
| fork rules and schedules | `Jaune.Fork` | `Fork`, `Fork.rules?`, `Fork.supported`, `ForkRules`, `ChainConfig`, `mainnetChainConfig` |
| words, bytes and RLP | `Jaune.Basic` | `Bytes`, `B256`, `Bytes.toB256`, `B256.toBytes`, `BLT`, `BLT.toBytes`, `Bytes.toBLT?` |
| hashes | `Jaune.Hash`, `Jaune.SHA256Spec` | `Bytes.keccak`, `Bytes.sha256`, `Bytes.sha256_eq_fips` |
| state root | `Jaune.Transaction` | `State.root` |

`Stor.get_set_ne` and `State.get_set_ne` take the same hypothesis orientation:
*written key ≠ read key*. For `Stor.get_set_ne s h v : (s.set k v).get a = s.get a`,
`h : k ≠ a`; for `State.get_set_ne w h ac`, `h : a ≠ b`, where `a` is written
and `b` is read. `State.set` erases an account set to `Acct.nil`
(`State.getElem?_set`).

[TRUSTED.md](TRUSTED.md) says exactly what `Bytes.sha256_eq_fips` and
`KECCAK.f1600_eq` do and do not establish.

## Compatibility

### Toolchain and dependencies

The only supported pair is the one this revision declares: `lean-toolchain`
(currently `leanprover/lean4:v4.34.0`), and Mathlib as required in
`lakefile.lean` (`v4.34.0`) and resolved in `lake-manifest.json`. A consumer
must use the same Lean toolchain. The files are the record; read them rather
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
imports only `Jaune.SymbolicPush`. Do not replace the Git dependency with a
sibling path or symlink.

### Constructor, reduction and simp behavior

- `Exec` lives in `Type`, not `Prop`. Derivations are data, so you can define
  them with `def`, traverse them (`Exec.rawNodes`) and invert them with
  `cases`. Adequacy wraps the type in `Nonempty`.
- The `Exec` constructors take step equations, not decode facts. Bridge with
  `Evm.step_next` / `step_last` / `step_jump`, as `SymbolicPush.prepend` and
  `SymbolicArith.prepend` do.
- The symbolic `cost`, `post`, `afterCharge`, `popped`, `Op.eval` and `Op.cost`
  are plain definitions with no `@[simp]`. Unfold them by name, as the
  examples do. Final-state projections such as `final_stack` close by `rfl`.
- `@[simp]` is set on:
  - the `settledRevert_*` / `settledHalt_*` projections and `Msg.initDevm_*` /
    `Msg.initSevm_*` in `Jaune.MessageExecution`;
  - `Exec.descendantFrames_runOk_*` and
    `Exec.committedFrames_eq_nil_of_not_commits` in `Jaune.ExecSettlement`;
  - `Exec.retainedNodes_*` in `Jaune.ExecChronology`.
- `Jaune.ExecDeriv` declares the notations `≺` (`Exec.Deriv.Prec`), `→p` and
  `□p`. They are global, not scoped.
- `CanonicalBlock` and `ConfiguredChain` have private constructors. Use their
  checked constructors.

### Fork coverage of the proof layer

- **Fork-generic.** The `Exec` type, adequacy, the derivation operations, the
  frame spawn lemmas and the PUSH / `ADD` / `SUB` / `MUL` rules quantify over
  every `Sevm`, whatever rule record it carries. They therefore hold for every
  fork Jaune models: Prague, Osaka, BPO1, BPO2 and the Amsterdam snapshot. The
  spawn lemmas have separate Amsterdam CALL/CREATE forms.
- **Pre-Amsterdam only.** The revert and exceptional-halt settlement theorems
  in `Jaune.MessageExecution` (`processMessage_revert_of_exec*`,
  `processMessage_halt_of_exec*`) assume `msg.benv.stat.rules.stateGas = none`.
  That holds for Prague, Osaka, BPO1 and BPO2 and fails for Amsterdam. No
  Amsterdam form is proved.
- **What the theorems are about.** They are statements about Jaune's model.
  How faithfully that model follows each fork is evidence from testing, not
  proof. Amsterdam support is a devnet snapshot, not final Amsterdam. See
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
