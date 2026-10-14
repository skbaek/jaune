# Comparing instruction traces

`compare-traces.py` compares one explicitly identified transaction/run pair as
streaming JSONL. It finds the first observed disagreement, without deciding
which executor is correct or asserting EVM equivalence. Run it from this checkout:

```sh
python3 scripts/compare-traces.py jaune.jsonl reference.jsonl --run-id tx-0
python3 scripts/compare-traces.py jaune.jsonl reference.jsonl --run-id tx-0 --json
```

`--run-id` is a caller-assigned identity, not authenticated transaction
provenance. Route each transaction into its own trace file and retain the mapping
from this identity to the original inputs. Concatenated runs are rejected: each
input must contain operations followed by exactly one terminal summary and EOF.
A zero-operation execution consisting of a summary is valid. A final newline is
optional; blank lines, records or other bytes after the summary are invalid.
One input may be `-` to read binary stdin.

| Exit | Meaning |
|---|---|
| 0 | Complete equality of the reported comparison scope; both summaries and EOFs validated. |
| 1 | Observed value, control-flow/order/length, or summary disagreement. |
| 2 | Invalid, empty, incomplete, unsupported input, input I/O failure, invalid CLI configuration, or report I/O failure. |
| 3 | A required or explicitly selected observation is unavailable on either side, including when absent on both. |

Operations are paired by zero-based ordinal in serialized order. Neither repeated
PCs nor nested frames cause resynchronization. PC, numeric opcode and depth are
compared first as control flow. Within a paired record, unavailable observations
take precedence over available payload differences; a control-flow disagreement
remains reportable when payload fields are missing. Reports include both input
names, identity, actual compared fields, source lines (one-based), operation
ordinal (zero-based), frame depth, PC, numeric opcode, values, and preceding row
metadata. A summary's `step` is the number of preceding operations. A length
report shows the conflicting row kinds/metadata instead of invented values.
The comparator does not infer unique frame IDs from depth.

By default it stops reading at the first disagreement. `suffix_validated: false`
means the unread remainder may contain malformed or incomplete input; this
outcome is an observed prefix disagreement, never complete equality. Add
`--validate-suffix` to validate both remaining inputs. An invalid suffix changes
the final status to `invalid_input` and retains the first disagreement. Equality
always validates both complete inputs, regardless of this flag.

## Supported format and interpretation ledger

The primary specification is [EIP-3155](https://eips.ethereum.org/EIPS/eip-3155),
inspected 2026-10-15. The normative datatype/field tables and prose govern this
parser; the illustrative examples contain incompatible representations.

| Record | Required comparison observations | Optional semantic observations |
|---|---|---|
| Operation | `pc`, `op`, `gas`, `gasCost`, `memSize`, `stack`, `depth`, `returnData`, `refund` | `opName`, `error`, `memory`, `storage` |
| Terminal summary | `stateRoot`, `output`, `gasUsed`, `pass` | `fork` |

Missing observation fields are preserved as unavailable, not rejected as zero
or treated as agreement. Each operation must carry `pc`, `op` and `depth` to
identify its structural shape. A summary must carry at least one of its
required observation names. Unknown fields and mixtures of step/summary fields
are rejected, so an unsupported extension cannot silently affect the meaning of
an equality report. Explicit future adapters must document their field and
identity conventions; there is currently no client adapter in this comparator.

The decisions are:

- JSON Number fields are nonnegative integers; booleans and floats are rejected.
  `op` must be 0..255. Summary `time` is validated as a nonnegative integer but
  excluded from comparison because it is runtime metadata. Reports list this
  exclusion.
- Hex-Number fields (`gas`, `gasCost`, `gasUsed` and stack elements) require a
  lowercase `0x` prefix and at least one hexadecimal digit. Digit case and
  leading zeros normalize numerically (`0x00A` equals `0xa`).
- Hex-String fields (`returnData`, `error`, `stateRoot`, summary `output`, memory
  elements and storage keys/values) require `0x` and an even number of digits.
  Digit case normalizes; byte length is preserved (`0x00` differs from `0x`).
  State-root length is not inferred as a client-specific validity check.
- The summary's `output` type is blank in the normative table; this supported
  dialect explicitly chooses a byte hex string, consistent with return bytes.
  An unprefixed empty string is rejected.
- `pass` is a JSON boolean. `stack` and `memory` are arrays, never null. `storage`
  is a JSON object of byte hex strings. Duplicate keys at every object level and
  storage keys colliding after digit-case normalization are rejected.
- Optional `error`, when present, is a byte hex string, per the normative table.
  An example's `error: null`, plaintext client errors, `memory` as one string,
  quoted summary booleans, missing required fields in examples, NaN/Infinity and
  unrelated client shapes do not change the supported dialect.
- Default comparison includes every required observation plus the union of
  supplied optional semantic fields. An optional field absent on both sides is
  outside the observed scope. Present on one side only means unavailable.

## Explicit projections

Use projections when the diagnostic deliberately compares fewer observations:

```sh
python3 scripts/compare-traces.py a.jsonl b.jsonl --run-id tx-0 \
  --step-fields gas,gasCost,stack --summary-fields output,gasUsed,pass --json
```

Operation projections always include `pc`, `op` and `depth`. Only explicit
selected observations are required in a projected scope; missing nonselected
required observations do not prevent projection equality. Missing selected
fields still return 3. All supplied fields, including nonselected fields, are
validated. A complete equality report says **complete projection agreement**,
identifies the exact step/summary scope, and makes no claim of full trace
agreement. Projecting one record type leaves the other at its default scope.

A default geth JSON logger stream may omit `returnData`, emit extra fault rows
and contain intermediate frame summaries or nonconforming fields. Do not feed
such a stream through silent coercion: it requires a separately documented,
explicit adapter that preserves operation/frame/run identity.

## Resource limits and library API

Defaults: `--max-row-bytes 1048576` (including newline), `--context 3` preceding
row pairs, and `--max-value-chars 256` per reported value. Increase limits
explicitly for large observations. Oversized rows fail before JSON parsing;
values larger than the report limit have bounded previews and a `truncated`
marker. Context carries metadata, not copies of stack/memory/storage. Both JSON
and human reports are deterministic for the same inputs/options.

The implementation retains only two current rows, a bounded context deque and
fixed-field report state. It uses binary `readline(max_row_bytes + 1)` and does
not read whole files, retain a trace list, or align/search subsequent operations.
Memory is bounded in trace length at fixed row/context limits; a supplied stream
must honor `readline(size)`. Trace length/output volume is otherwise unlimited.
`--validate-suffix` can therefore take time proportional to the entire trace.

Import `scripts/trace_compare.py` and call:

```python
report = trace_compare.compare_streams(
    left_binary_stream, right_binary_stream,
    left_name="jaune.jsonl", right_name="reference.jsonl", run_id="tx-0",
    max_row_bytes=1048576, context=3, max_value_chars=256,
    step_fields=None, summary_fields=None, validate_suffix=False,
)
```

The return value is a JSON-serializable report with `status` and `exit_code`.
Streams are borrowed and remain caller-owned. Invalid API options raise
`ValueError`; invalid input returns a report. The library expects binary streams
implementing `readline(size)` and propagates unrelated programming errors.

Run the focused observational controls with:

```sh
python3 -m unittest discover -s scripts/tests -p test_trace_compare.py -v
```

These controls verify serialization, normalization, streaming behavior and
reports. They do not duplicate or establish execution-fidelity theorems.
