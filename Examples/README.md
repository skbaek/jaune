# Execution examples

These examples use this checkout's Jaune revision, Lean toolchain and Mathlib
dependency. `Examples` is a default Lake library outside the production import
closure; an ordinary `lake build` compiles it alongside Jaune.

## Symbolic instructions and composition

[Execution.lean](Execution.lean) imports `Jaune.SymbolicPush`. Its operands,
environment, world and metadata are variables. It proves decoding and complete
raw-frame execution of `PUSH1 a; PUSH1 b; STOP`, starting with six gas and an empty
stack. The result has the two operand words on its stack, zero gas and unchanged
world and metadata. `interpreter` connects the constructed derivation to total
`Jaune.exec` through adequacy.

The reusable `Jaune.SymbolicPush` rules describe success, insufficient gas and
stack overflow. Success requires enough gas and fewer than 1024 stack entries.
Out-of-gas leaves the input state; overflow after charging retains the gas charge
in the raw error. `prepend` composes a decoded PUSH with an existing continuation.
These are direct-frame statements, not transaction validation or settlement
claims. The bytecode example uses PUSH1; it does not establish support for every
instruction or fork-specific opcode.

`Jaune.Exec` owns the canonical execution type and adequacy theorem. Historical
qualified names such as `Blanc.Exec` and `Blanc.exec_iff_exec_eq` remain for
compatibility; importing a Blanc package is unnecessary. `Jaune.ExecDeriv`,
`Jaune.ExecSettlement` and `Jaune.ExecChronology` expose derivation, settlement and
occurrence support respectively. Compiler and contract-specific APIs remain in
Blanc.

## Transaction entry

The separate [transfer-blockchain fixture](../scripts/t8n/cases/transfer-blockchain)
contains complete checked-in inputs: `case.json` selects **Prague**, chain ID 1,
blockchain mode and reward -1; `env.json` supplies the block environment;
`alloc.json` supplies accounts and code; `txs.json` supplies the signed transaction.
`txs.src.json` documents its reproducible test-key source. That key is fixture data.

After building, run:

```sh
scripts/check-t8n.sh --case transfer-blockchain
```

This enters through the `jaune t8n` transaction interface, including system
operations and transaction accounting. It transfers one wei to address `0x100`
and executes its `PUSH1 1; PUSH1 1; SSTORE; STOP` code. The checked expected
allocation gives that account balance 1 and storage slot 1 equal to 1. The expected
result has one successful receipt, no rejected transactions, and gas used
`0xa862` (43106). See [expected allocation](../scripts/t8n/cases/transfer-blockchain/expected/alloc.json)
and [expected result](../scripts/t8n/cases/transfer-blockchain/expected/result.json)
for the complete assertions, including sender, fee recipient and system accounts.

The existing gate checks deterministic output, compares the complete result,
allocation and body against the registered conformance target's goldens, and
verifies their provenance. It applies only the canonicalizations and registered
deviations described in [the corpus guide](../scripts/t8n/README.md). CI already
runs this case as part of `scripts/check-t8n.sh`; this example adds no duplicate
conformance harness and changes no golden. It is finite transaction evidence,
separate from the universally quantified direct-frame proof above.

## Installing as a Git dependency

The external smoke source in [scripts/consumer/Consumer.lean](../scripts/consumer/Consumer.lean)
constructs a complete out-of-gas derivation and proves its interpreter result.
It imports only `Jaune.SymbolicPush`; it uses neither this example library nor
a Blanc package. A disposable package can be prepared for a published commit:

```sh
python3 scripts/external-consumer.py prepare /tmp/jaune-consumer \
  --url https://github.com/skbaek/jaune.git --revision "$(git rev-parse HEAD)"
cd /tmp/jaune-consumer
lake update
lake exe cache get
lake build
python3 verify-consumer.py verify .
```

Use a fresh destination path. On a coordinated development host, use its admitted
build launcher. The generated package carries this checkout's toolchain and a
Git dependency on the requested commit. Verification checks the manifest URL and
revision, the installed clean checkout, matching toolchains, Git-only dependency
types and the compiled consumer artifact. It rejects a sibling path dependency.

CI prepares the package from a sparse bootstrap checkout, removes that checkout,
then builds and verifies the Git-installed consumer. It disables GitHub artifact
cache restoration and downloads Mathlib's published cache; that is an explicit
cache condition, not a claim that all dependencies compile from source. Local
file-URL mirrors are accepted only for unpublished-candidate rehearsals and do
not establish HTTPS availability or newcomer download cost.
