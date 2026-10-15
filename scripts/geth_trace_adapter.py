"""Stream geth 1.15.6 call-frame JSONL into the trace comparator's schema."""
from __future__ import annotations

import argparse
from contextlib import ExitStack
import json
import sys

from trace_compare import (_constant, _hex_bytes, _hex_number, _object, _positive,
                           TraceInputError, normalize)

DIALECT = "geth-1.15.6-callframes"
ENTER_REQUIRED = {"from", "to", "gas", "value", "type"}
OP_REQUIRED = {"pc", "op", "gas", "gasCost", "memSize", "stack", "depth", "refund", "opName"}
CALL_TYPES = {0xF0: "CREATE", 0xF1: "CALL", 0xF2: "CALLCODE", 0xF4: "DELEGATECALL",
              0xF5: "CREATE2", 0xFA: "STATICCALL", 0xFF: "SELFDESTRUCT"}
CALLBACK_KEY = ("pc", "op", "gas", "gasCost", "depth", "opName")


def _shape(row, required, optional=()):
    missing = required - row.keys()
    unknown = row.keys() - required - set(optional)
    if missing or unknown:
        raise ValueError(f"record fields: missing={sorted(missing)}, unsupported={sorted(unknown)}")


def _error(value):
    if not isinstance(value, str) or not value:
        raise ValueError("error must be a nonempty string")
    return "0x" + value.encode("utf-8").hex()


def _uint64_hex(value, field):
    result = _hex_number(value, field)
    if int(result, 16) >= 2 ** 64:
        raise ValueError(f"{field} exceeds uint64")
    return result


def _entry(row):
    _shape(row, ENTER_REQUIRED, {"input"})
    for field in ("from", "to"):
        if len(_hex_bytes(row[field], field)) != 42:
            raise ValueError(f"{field} must be a 20-byte address")
    _uint64_hex(row["gas"], "gas")
    if row["type"] not in CALL_TYPES.values():
        raise ValueError("unsupported frame type")
    if row["value"] is None:
        if row["type"] not in ("STATICCALL", "DELEGATECALL"):
            raise ValueError("null value is only supported for STATICCALL/DELEGATECALL")
    elif int(_hex_number(row["value"], "value"), 16) >= 2 ** 256:
        raise ValueError("value exceeds uint256")
    if "input" in row:
        _hex_bytes(row["input"], "input")
    return row["type"]


def _operation(row):
    _shape(row, OP_REQUIRED, {"returnData", "memory", "error"})
    result = dict(row)
    # geth emits null for a disabled stack, distinct from an observed empty stack.
    if result["stack"] is None:
        del result["stack"]
    if "error" in result:
        result["error"] = _error(result["error"])
    if "memory" in result:
        memory = _hex_bytes(result["memory"], "memory")[2:]
        if len(memory) % 64 or len(memory) // 2 != result["memSize"]:
            raise ValueError("memory must contain memSize bytes in complete 32-byte words")
        result["memory"] = ["0x" + memory[i:i + 64] for i in range(0, len(memory), 64)]
    _, result = normalize(result)
    for field in ("gas", "gasCost"):
        _uint64_hex(result[field], field)
    for field in ("pc", "refund"):
        if result[field] >= 2 ** 64:
            raise ValueError(f"{field} exceeds uint64")
    if result["memSize"] % 32:
        raise ValueError("memSize must be a multiple of 32")
    if not result["opName"]:
        raise ValueError("opName must be nonempty")
    if len(result.get("stack", [])) > 1024 or any(
            int(word, 16) >= 2 ** 256 for word in result.get("stack", [])):
        raise ValueError("stack exceeds EVM bounds")
    return result


def _exit(row):
    _shape(row, {"output", "gasUsed"}, {"error"})
    if not isinstance(row["output"], str):
        raise ValueError("output must be unprefixed hexadecimal bytes")
    output = _hex_bytes("0x" + row["output"], "output")
    gas_used = _uint64_hex(row["gasUsed"], "gasUsed")
    error = _error(row["error"]) if "error" in row else None
    return {"output": output, "gasUsed": gas_used, "pass": error is None}, error


def adapt_stream(stream, *, dialect, run_id, source="input", max_row_bytes=1024 * 1024,
                 max_depth=1025):
    """Yield normalized records; validate EOF before yielding the root summary.

    The caller's run_id identifies the single input, not authenticated provenance.
    No run metadata is injected into the strict comparison schema. Retention is
    O(max_row_bytes + max_depth); streams are borrowed and never closed here.
    """
    if dialect != DIALECT:
        raise ValueError(f"dialect must be {DIALECT}")
    if not isinstance(run_id, str) or not run_id.strip():
        raise ValueError("a nonempty run_id is required")
    for key, value in (("max_row_bytes", max_row_bytes), ("max_depth", max_depth)):
        if type(value) is not int or value < 1:
            raise ValueError(f"{key} must be a positive integer")
    frames = []
    pending = summary = None
    line = steps = 0
    started = False
    while True:
        try:
            raw = stream.readline(max_row_bytes + 1)
            if not isinstance(raw, bytes):
                raise ValueError("input must be a binary stream")
            if not raw:
                if summary is None:
                    raise ValueError("empty input" if not started else "missing root frame exit")
                yield summary
                return
            line += 1
            if len(raw) > max_row_bytes:
                raise ValueError(f"row exceeds max_row_bytes={max_row_bytes}")
            if summary is not None:
                raise ValueError("bytes after root frame exit")
            row = json.loads(raw.decode("utf-8"), object_pairs_hook=_object, parse_constant=_constant)
            if not isinstance(row, dict):
                raise ValueError("record must be an object")
            if "type" in row or "from" in row:
                frame_type = _entry(row)
                if len(frames) >= max_depth:
                    raise ValueError(f"frame depth exceeds max_depth={max_depth}")
                if frames:
                    if (pending is None or "error" in pending or
                            CALL_TYPES.get(pending["op"]) != frame_type):
                        raise ValueError("child entry requires the immediately preceding matching call operation")
                    yield pending
                    steps += 1
                    pending = None
                elif started or frame_type not in ("CALL", "CREATE"):
                    raise ValueError("root must be one CALL or CREATE frame")
                frames.append(frame_type)
                started = True
            elif "pc" in row or "op" in row:
                if not frames or frames[-1] == "SELFDESTRUCT":
                    raise ValueError("operation outside an executable frame")
                current = _operation(row)
                if current["depth"] != len(frames):
                    raise ValueError("operation depth disagrees with frame entries")
                if pending is not None:
                    if "error" in pending:
                        raise ValueError("operation after a fault before frame exit")
                    if "error" in current and all(current[k] == pending[k] for k in CALLBACK_KEY):
                        # Only adjacent same-frame callbacks can pair. The fault's
                        # stack/memory/refund may be post-operation: keep pre-state.
                        pending["error"] = current["error"]
                        continue
                    if ("error" in current and current["pc"] == pending["pc"] and
                            current["op"] == pending["op"] and current["gas"] == pending["gas"]):
                        raise ValueError("ambiguous fault callback identity")
                    yield pending
                    steps += 1
                pending = current
            elif "output" in row or "gasUsed" in row:
                current_summary, error = _exit(row)
                if not frames:
                    raise ValueError("exit without a frame entry")
                if pending is not None:
                    if "error" in pending and pending["error"] != error:
                        raise ValueError("fault and frame exit errors disagree")
                    yield pending
                    steps += 1
                    pending = None
                frames.pop()
                if not frames:
                    summary = current_summary
            else:
                raise ValueError("unsupported geth event shape")
        except (ValueError, OSError, UnicodeError, RecursionError) as exc:
            raise TraceInputError(source, line or 1, steps, str(exc)) from exc


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", help="one call-frame JSONL trace, or - for stdin")
    parser.add_argument("--output", default="-", help="new output file, or - for stdout")
    parser.add_argument("--dialect", required=True, choices=[DIALECT])
    parser.add_argument("--run-id", required=True)
    parser.add_argument("--max-row-bytes", type=_positive, default=1024 * 1024)
    parser.add_argument("--max-depth", type=_positive, default=1025)
    parser.add_argument("--max-output-bytes", type=_positive, help="optional total output byte ceiling")
    args = parser.parse_args(argv)
    try:
        with ExitStack() as stack:
            src = sys.stdin.buffer if args.input == "-" else stack.enter_context(open(args.input, "rb"))
            dst = sys.stdout.buffer if args.output == "-" else stack.enter_context(open(args.output, "xb"))
            written = 0
            for record in adapt_stream(src, dialect=args.dialect, run_id=args.run_id, source=args.input,
                                       max_row_bytes=args.max_row_bytes, max_depth=args.max_depth):
                data = (json.dumps(record, separators=(",", ":"), sort_keys=True) + "\n").encode("utf-8")
                if args.max_output_bytes is not None and written + len(data) > args.max_output_bytes:
                    raise ValueError("max_output_bytes exceeded")
                if dst.write(data) != len(data):
                    raise OSError("short output write")
                dst.flush()
                written += len(data)
    except (OSError, ValueError) as exc:
        location = f" line {exc.line}" if isinstance(exc, TraceInputError) else ""
        print(f"run={args.run_id!r}{location}: {exc}", file=sys.stderr)
        return 2
    return 0
