# geth call-frame trace adapter

`normalize-geth-trace.py` converts **one geth 1.15.6 call-frame JSONL stream**
to the supported schema of [the comparator](TRACE_COMPARISON.md). Python 3.11
and its standard library suffice. This is format normalization, not a proof
of EVM correctness, trace authenticity, or transaction equivalence.

Capture with geth `evm t8n --trace --trace.callframes --trace.returndata`
and explicit `--state.fork`, `--input.alloc`, `--input.env`, `--input.txs`
and `--output.basedir` arguments. Select the trace file for one transaction;
never concatenate transaction files. Add `--trace.memory` to observe memory.
The adapter deliberately rejects the default tracer's untagged stream without
frame entries. Binary version selection remains the caller's responsibility.

```sh
python3 scripts/normalize-geth-trace.py reference.jsonl \
  --dialect geth-1.15.6-callframes --run-id case-1 \
  --output reference-normalized.jsonl
python3 scripts/compare-traces.py jaune.jsonl reference-normalized.jsonl \
  --run-id case-1 --step-fields pc,op,depth,gas,gasCost,stack,memSize,refund \
  --summary-fields output,gasUsed,pass --json
```

This example is an **explicit projection**: it omits return data, memory,
storage, instruction names/errors and state roots. Add observations to the
selection when both producers supply them. A missing selected observation
reports unavailable, including when it is missing on both sides. Use the
same run identity when producing and comparing the files; the string is a
caller-assigned label, not a verified transaction hash. The strict normalized
rows contain no extra run metadata.

## Protocol and observations

- The root is CALL or CREATE. Nested entries must immediately follow an
  operation of the matching CALL, CALLCODE, DELEGATECALL, STATICCALL, CREATE,
  CREATE2 or SELFDESTRUCT type. SELFDESTRUCT's transfer callback has no
  executable child steps. Frame entries/exits must balance, instruction depth
  must match, and EOF must follow the root exit. Child exits never become
  terminal summaries. These are structural checks, not semantic replay.
- Every observed operation stays in ordinal order. A second, immediately
  adjacent error-bearing row with the same pc/op/gas/gasCost/depth/opName is
  the OnFault callback for the pending operation. Keep the first row's
  pre-operation observations and attach the error. The fault's stack, memory
  and refund may already have changed. No future-PC search occurs. An error
  row with a different operation identity is a separate failed operation,
  as with pre-execution stack/gas failures. A fault must be followed by its
  frame exit with the same error. Ambiguous identities fail closed.
- Geth emits a null stack when stack capture is disabled; the adapter leaves
  stack absent. An observed `[]` remains an empty stack in bottom-to-top order.
  Omitted returnData/memory remain absent, even when geth's omission might
  mean empty. Geth's JSON logger does not supply storage or stateRoot; neither
  is synthesized. Supplied unsupported extensions are rejected.
- Geth memory is one prefixed byte string in increasing byte-address order.
  Its length must equal memSize and be divisible by 32. It becomes an array
  of prefixed 32-byte strings in the same order. No padding or integer
  conversion changes those bytes.
- Errors are nonempty plaintext strings encoded as UTF-8 hexadecimal bytes.
  Their content is preserved; this does not equate different clients' error
  labels. Root `pass` means its exit has no error. A failed child can be caught
  by a successful parent. Unprefixed root output becomes prefixed byte hex.
- Root gasUsed is **frame-execution gas**, excluding transaction intrinsic
  gas and transaction-level refund/fee settlement. It must only be compared
  against the corresponding message-execution summary. The adapter cannot
  turn this into a complete transaction summary. Without stateRoot, default
  full-field comparison cannot report equality.

The callback rules and encoding were checked against geth v1.15.6's
[JSON logger](https://github.com/ethereum/go-ethereum/blob/v1.15.6/eth/tracers/logger/logger_json.go),
[generated encoder](https://github.com/ethereum/go-ethereum/blob/v1.15.6/eth/tracers/logger/gen_structlog.go)
and [interpreter](https://github.com/ethereum/go-ethereum/blob/v1.15.6/core/vm/interpreter.go),
plus actual call-frame traces from that binary. Other versions require their
own format validation; passing the dialect flag is an explicit assertion by
the caller, not automatic version detection.

## Limits and failures

Input and output may be `-` for stdin/stdout. An output path must be new:
existing files are refused, including aliases of the input. JSONL alone goes
to stdout; errors go to stderr with the run identity and input line when known.
Exit 0 means normalization completed; exit 2 means arguments, input, limits or
I/O failed. Always check the process exit status, including in pipelines.

The default maximum row is 1 MiB including newline; default frame depth is
1025. `--max-row-bytes` and `--max-depth` set explicit positive bounds.
`--max-output-bytes` optionally limits total encoded output; otherwise output
length is unbounded. The library `adapt_stream` borrows a binary stream and
yields records with retention O(maximum row bytes + maximum frame depth):
one pending instruction, the current decoded row and bounded frame metadata.
It never collects the trace. Duplicate keys, nonstandard numeric constants,
malformed UTF-8, unsupported fields and incorrect types fail closed.

Partial instruction output may remain after a failure. Malformed/trailing
input, incomplete frames and an output limit prevent a terminal summary from
being emitted. Output I/O failure returns nonzero; partial writes or a final
flush failure still require the caller to check the exit status. Files are
streamed, not atomically published. The comparator also validates terminal
completion and EOF, but cannot detect every storage failure from content alone.

Focused protocol controls:

```sh
python3 -m unittest discover -s scripts/tests -p test_geth_trace_adapter.py
```
