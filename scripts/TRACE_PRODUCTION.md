# Producing message traces

`jaune-trace REQUEST.json NEW_OUTPUT_DIRECTORY` runs one explicitly identified
message through `Jaune.Trace.runFrame`, the streaming driver whose returned
value carries an erasure certificate to `Jaune.runFrame`. The executable is a
default build target and remains outside `Jaune.lean`'s import closure.

Build through the host's owned wrapper, then run the binary directly:

```sh
~/creme/scripts/creme lake-build jaune-execution-tracing-v1 -- jaune-trace
.lake/build/bin/jaune-trace request.json output
python3 scripts/compare-traces.py output/trace.jsonl reference.jsonl \
  --run-id example --step-fields pc,op,depth,gas,gasCost,stack,memSize,refund \
  --summary-fields output,gasUsed,pass --json
```

For geth input, first use the explicit
[call-frame adapter](GETH_TRACE_ADAPTER.md). Select the same fork, code,
allocation, block context, message gas and warm accesses in both executions.
The comparator reports the selected projection; it does not certify either
executor. Error names differ between clients and are never silently aliased.

## Message boundary

This executable runs a **message**, not a signed transaction. There is no
intrinsic gas charge, sender nonce or fee processing, authorization processing,
transaction refund cap, receipt, or block finalization. Creation takes an
explicit destination address; it does not derive it or advance its creator's
nonce. Allocation and state root describe this message boundary. The root
gasUsed is its grant minus settled remaining gas, including code-deposit cost
for creation; it excludes transaction settlement. Amsterdam accepts an explicit
state-gas grant but does not apply the transaction runner's preparation.

The existing `jaune t8n` trace refusals and ordinary behavior remain unchanged.
Full transaction tracing is a separate integration obligation. The driver
shares core step/entry/settlement functions, but does not inherit the ordinary
native executor's private calldata-cache optimization. Its theorem proves
execution projection, not serialization, I/O success or memory equivalence.

## Request

This minimal request executes `PUSH1 2; PUSH1 3; ADD; STOP`:

```json
{
  "runId": "example",
  "fork": "Prague",
  "memory": true,
  "alloc": {
    "0x0000000000000000000000000000000000000200": {
      "balance": "0x00", "nonce": "0x00", "code": "0x600260030100", "storage": {}
    }
  },
  "env": {"currentBaseFee": "0x0", "currentExcessBlobGas": "0x0"},
  "message": {
    "kind": "call",
    "caller": "0x1111111111111111111111111111111111111111",
    "address": "0x0000000000000000000000000000000000000200",
    "gas": "0x100000"
  }
}
```

`runId`, `fork`, `alloc`, `env` and `message` are required. Fork selection uses
the existing supported-fork decoder with no fallback. Allocation and block
environment reuse `T8n` parsing, including its canonical state construction,
hex-byte allocation values and environment defaults/derivations. `chainId`
defaults to 1 and must fit uint64. Quantities outside allocation are prefixed
hex strings; addresses are 20-byte prefixed strings. Input is limited to 8 MiB.

Message fields:

| field | meaning/default |
|---|---|
| kind | required `call` or `create` |
| caller, address, gas | required caller, current target, execution-gas grant |
| input | bytes, default empty; call data for call, initcode for create |
| value | uint256 quantity, default zero |
| origin, gasPrice | defaults caller and zero |
| static, transferValue, disablePrecompiles | booleans, defaults false/true/false |
| stateGas | quantity, default zero; nonzero requires state-gas fork rules |
| accessedAddresses | array of warm addresses, default empty |
| accessedStorageKeys | array of `{address, key}` objects, default empty; key is a 32-byte hash |
| blobVersionedHashes | array of 32-byte hashes, default empty |

Call code comes from the allocation at address, with normal precompile
dispatch. The remaining depth allowance is 1024. Warm accesses are supplied
explicitly: a transaction-like context normally warms the sender, target,
coinbase and active precompiles, plus its access list. There is no implicit
transaction access-list preparation here.

## Observations and limits

Pre-step stack is bottom-to-top; memory, when enabled, is an array of 32-byte
words in increasing address order, with logical zero padding. Return data is
always emitted, including empty bytes. Refund is the sum of the current
frame's local counter and suspended ancestors' counters. A negative sum is
unavailable rather than clamped to zero. Child rollback is reflected when the
parent resumes. Errors are Jaune's rendered text encoded as UTF-8 hex bytes.

Single-gas forks have gasCost for ordinary successful steps, RETURN/STOP,
REVERT, and spawning calls/creations. CALL includes charged forwarded gas;
CREATE excludes the child grant. Non-spawning CALL/CREATE can return or consume
a grant before the observation boundary, so their gasCost is unavailable.
Exceptional failed charges and Amsterdam's two-dimensional gasCost are also
unavailable. Missing fields remain absent and must not be read as zero.
No instruction is rerun to infer its cost. Empty code's synthetic executor
STOP transition is recorded as lifecycle `empty-code`, not a bytecode step;
nonempty code's implicit end-of-code STOP remains an instruction.

`memory` defaults false. `maxDataBytes` defaults `0x100000` and bounds emitted
memory/return/output byte strings before encoding. `maxRowBytes` defaults
`0x100000`, including newline. Optional `maxSteps` bounds emitted instructions;
zero permits only zero-instruction executions. Without maxSteps, output length
is unbounded. State retained by serialization is proportional to active frame
depth plus one bounded row; the EVM's own memory/state is separate. The native
IO driver tail-calls continuation steps, retaining execution continuations only
for active child frames. Its certificate transport is proof-only: rebuilding
a certificate after each recursive call would retain instruction history on
the native stack. An arbitrary caller-supplied monad or sink can itself retain
observations; this memory claim concerns the shipped IO runner.

The output directory must not exist. It contains:

- `trace.jsonl`: strict instruction rows and one root message summary.
- `frames.jsonl`: lifecycle sidecar with runId, unique frame number, depth and
  event (`entered`, `instruction`, `empty-code`, `exited`, `settled`, `resumed`).
  Entry records identify parents; instruction records identify zero-based trace
  step ordinals; resumed records identify the child. A settled root is marked.
- `run.json`: written only after successful completion, recording identity,
  fork, message scope and instruction count.

Exit 0 means tracing completed, including executions whose summary pass is
false. Exit 2 means input, execution infrastructure, limit or I/O failure.
Errors go to stderr; successful execution prints nothing. Each JSONL write is
flushed. Failure may leave partial files, so callers must check exit status and
run.json. Limits or exhausted fuel do not produce a completing trace summary;
a failed final metadata write can follow a flushed summary and still exits 2.

Run `python3 scripts/check-trace.py` after building. These native controls
check observations, frame identity, nested refunds, limits and CLI failures;
they do not duplicate the kernel-proved execution projection.
