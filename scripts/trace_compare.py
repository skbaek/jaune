"""Strict, bounded-memory comparison of a single EIP-3155 JSONL run pair."""
from __future__ import annotations

import argparse
from collections import deque
from contextlib import ExitStack
import json
import re
import sys
from typing import BinaryIO

STEP_REQUIRED = ("pc", "op", "gas", "gasCost", "memSize", "stack", "depth", "returnData", "refund")
STEP_OPTIONAL = ("opName", "error", "memory", "storage")
SUMMARY_REQUIRED = ("stateRoot", "output", "gasUsed", "pass")
SUMMARY_OPTIONAL = ("fork",)
CONTROL = ("pc", "op", "depth")
HEX_NUMBER = re.compile(r"0x[0-9a-fA-F]+\Z")
HEX_BYTES = re.compile(r"0x(?:[0-9a-fA-F]{2})*\Z")
EXIT_CODES = {"equal": 0, "difference": 1, "invalid_input": 2, "unavailable": 3}


class TraceInputError(ValueError):
    def __init__(self, source, line, step, message):
        super().__init__(message)
        self.source, self.line, self.step = source, line, step

    def detail(self):
        return {"source": self.source, "line": self.line, "step": self.step, "message": str(self)}


def _object(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate key {key!r}")
        result[key] = value
    return result


def _constant(value):
    raise ValueError(f"non-JSON numeric constant {value}")


def _number(value, field):
    if type(value) is not int or value < 0:
        raise ValueError(f"{field} must be a nonnegative JSON integer")
    return value


def _hex_number(value, field):
    if not isinstance(value, str) or not HEX_NUMBER.fullmatch(value):
        raise ValueError(f"{field} must be a 0x-prefixed hexadecimal number")
    return hex(int(value[2:], 16))


def _hex_bytes(value, field):
    if not isinstance(value, str) or not HEX_BYTES.fullmatch(value):
        raise ValueError(f"{field} must be a 0x-prefixed whole-byte hexadecimal string")
    return value.lower()


def normalize(row):
    """Validate every supplied field; missing observations remain absent."""
    if not isinstance(row, dict):
        raise ValueError("record must be a JSON object")
    if any(field in row for field in CONTROL):
        kind = "step"
        if not all(field in row for field in CONTROL):
            raise ValueError("operation requires pc, op and depth")
        allowed = STEP_REQUIRED + STEP_OPTIONAL
    elif any(field in row for field in SUMMARY_REQUIRED):
        kind = "summary"
        allowed = SUMMARY_REQUIRED + SUMMARY_OPTIONAL + ("time",)
    else:
        raise ValueError("record is neither an operation nor a terminal summary")
    unknown = sorted(set(row) - set(allowed))
    if unknown:
        raise ValueError(f"unsupported {kind} fields: {', '.join(unknown)}")
    result = {}
    for field, value in row.items():
        if field in ("pc", "op", "memSize", "depth", "refund", "time"):
            result[field] = _number(value, field)
            if field == "op" and value > 255:
                raise ValueError("op must be an opcode byte (0..255)")
        elif field in ("gas", "gasCost", "gasUsed"):
            result[field] = _hex_number(value, field)
        elif field in ("returnData", "error", "stateRoot", "output"):
            result[field] = _hex_bytes(value, field)
        elif field == "pass":
            if type(value) is not bool:
                raise ValueError("pass must be a JSON boolean")
            result[field] = value
        elif field in ("opName", "fork"):
            if not isinstance(value, str):
                raise ValueError(f"{field} must be a JSON string")
            result[field] = value
        elif field in ("stack", "memory"):
            if not isinstance(value, list):
                raise ValueError(f"{field} must be an array")
            encoder = _hex_number if field == "stack" else _hex_bytes
            result[field] = [encoder(item, field) for item in value]
        elif field == "storage":
            if not isinstance(value, dict):
                raise ValueError("storage must be an object of hexadecimal byte strings")
            storage = {}
            for key, item in value.items():
                key = _hex_bytes(key, "storage key")
                if key in storage:
                    raise ValueError("storage keys collide after hexadecimal normalization")
                storage[key] = _hex_bytes(item, "storage value")
            result[field] = storage
    return kind, result


class TraceReader:
    """Requires binary readline(size), so row limits bound reads before JSON parsing."""
    def __init__(self, stream: BinaryIO, name: str, max_row_bytes: int):
        self.stream, self.name, self.max_row_bytes = stream, name, max_row_bytes
        self.line = self.steps = 0
        self.summary_seen = self.done = False

    def next(self):
        if self.done:
            return None
        try:
            raw = self.stream.readline(self.max_row_bytes + 1)
        except (OSError, ValueError) as exc:
            raise TraceInputError(self.name, self.line + 1, self.steps, f"read failed: {exc}") from exc
        if not raw:
            self.done = True
            if not self.summary_seen:
                reason = "empty input" if self.line == 0 else "missing terminal summary"
                raise TraceInputError(self.name, self.line + 1, self.steps, reason)
            return None
        self.line += 1
        try:
            if not isinstance(raw, bytes):
                raise ValueError("stream must supply bytes")
            if len(raw) > self.max_row_bytes:
                raise ValueError(f"row exceeds max_row_bytes={self.max_row_bytes} (including newline)")
            if self.summary_seen:
                raise ValueError("record or bytes after terminal summary")
            row = json.loads(raw.decode("utf-8"), object_pairs_hook=_object, parse_constant=_constant)
            kind, values = normalize(row)
        except (ValueError, UnicodeError, RecursionError) as exc:
            raise TraceInputError(self.name, self.line, self.steps, str(exc)) from exc
        record = {"kind": kind, "line": self.line, "step": self.steps, "values": values}
        if kind == "summary":
            self.summary_seen = True
        else:
            self.steps += 1
        return record


def _metadata(record):
    if record is None:
        return None
    result = {key: record[key] for key in ("kind", "line", "step")}
    result.update({key: record["values"][key] for key in CONTROL if key in record["values"]})
    if "opName" in record["values"]:
        result["opName"] = record["values"]["opName"]
    return result


def _value(values, field, limit):
    if field not in values:
        return {"available": False}
    value = values[field]
    encoded = json.dumps(value, sort_keys=True, ensure_ascii=True, separators=(",", ":"))
    if len(encoded) > limit:
        return {"available": True, "preview": encoded[:limit], "truncated": True, "encoded_chars": len(encoded)}
    return {"available": True, "value": value, "truncated": False}


def _fields(record, other, selected):
    if selected is not None:
        return list(selected)
    required = STEP_REQUIRED if record["kind"] == "step" else SUMMARY_REQUIRED
    optional = STEP_OPTIONAL if record["kind"] == "step" else SUMMARY_OPTIONAL
    return list(required) + [field for field in optional if field in record["values"] or field in other["values"]]


def _selection(fields, allowed, required=()):
    if fields is None:
        return None
    fields = tuple(fields)
    if not fields or len(set(fields)) != len(fields) or any(field not in allowed for field in fields):
        raise ValueError("projection fields must be a nonempty, unique supported field list")
    return tuple(dict.fromkeys((*required, *fields)))


def compare_streams(left: BinaryIO, right: BinaryIO, *, left_name="left", right_name="right",
                    run_id: str, max_row_bytes=1024 * 1024, context=3,
                    max_value_chars=256, step_fields=None, summary_fields=None,
                    validate_suffix=False):
    """Compare ordinal operations and summaries; 0/equal always validates both EOFs.

    A caller-supplied run_id identifies this single run pair, not authenticated
    transaction provenance. Streams are borrowed; callers own their lifetimes.
    """
    if not isinstance(run_id, str) or not run_id.strip():
        raise ValueError("a nonempty run_id is required")
    for key, value, minimum in (("max_row_bytes", max_row_bytes, 1), ("context", context, 0),
                                ("max_value_chars", max_value_chars, 1)):
        if type(value) is not int or value < minimum:
            raise ValueError(f"{key} must be an integer >= {minimum}")
    step_fields = _selection(step_fields, STEP_REQUIRED + STEP_OPTIONAL, CONTROL)
    summary_fields = _selection(summary_fields, SUMMARY_REQUIRED + SUMMARY_OPTIONAL)
    readers = [TraceReader(left, left_name, max_row_bytes), TraceReader(right, right_name, max_row_bytes)]
    report = {"run_id": run_id, "inputs": {"left": left_name, "right": right_name},
              "scope": {"mode": "projection" if step_fields is not None or summary_fields is not None else "supported_fields",
                        "step_fields": list(step_fields) if step_fields is not None else list(STEP_REQUIRED),
                        "summary_fields": list(summary_fields) if summary_fields is not None else list(SUMMARY_REQUIRED),
                        "optional_policy": "compare union of observed supported optional fields for unprojected rows",
                        "excluded_fields": ["time"]},
              "suffix_validated": False, "compared_steps": 0, "context": []}
    history = deque(maxlen=context)
    compared = {"step": set(), "summary": set()}
    first = None
    try:
        while True:
            a, b = readers[0].next(), readers[1].next()
            if a is None and b is None:
                report["suffix_validated"] = True
                break
            pair = {"left": _metadata(a), "right": _metadata(b)}
            if a is None or b is None or a["kind"] != b["kind"]:
                first = {"category": "control_flow_length", **pair, "fields": [],
                         "message": "operation/summary order or trace length differs"}
            else:
                fields = _fields(a, b, step_fields if a["kind"] == "step" else summary_fields)
                compared[a["kind"]].update(fields)
                missing = [field for field in fields if field not in a["values"] or field not in b["values"]]
                unequal = [field for field in fields if field not in missing and a["values"][field] != b["values"][field]]
                # Control flow is observable even if payload observations are unavailable.
                controls = [field for field in unequal if field in CONTROL]
                affected = controls or missing or unequal
                if affected:
                    category = "control_flow" if controls else "unavailable_observation" if missing else "value"
                    first = {"category": category, **pair, "fields": affected,
                             "values": {field: {"left": _value(a["values"], field, max_value_chars),
                                                "right": _value(b["values"], field, max_value_chars)} for field in affected}}
                elif a["kind"] == "step":
                    report["compared_steps"] += 1
            if first:
                report["context"] = list(history) + [pair]
                if validate_suffix:
                    for reader in readers:
                        while reader.next() is not None:
                            pass
                    report["suffix_validated"] = True
                break
            history.append(pair)
    except TraceInputError as exc:
        report.update(status="invalid_input", exit_code=2, error=exc.detail())
        if first is not None:
            report["first_disagreement"] = first
        report["context"] = report["context"] or list(history)
    else:
        status = "equal" if first is None else "unavailable" if first["category"] == "unavailable_observation" else "difference"
        report.update(status=status, exit_code=EXIT_CODES[status])
        if first is not None:
            report["first_disagreement"] = first
    report["compared_fields"] = {kind: sorted(fields) for kind, fields in compared.items()}
    report["validated_records"] = {"left": readers[0].line, "right": readers[1].line}
    if report["status"] == "equal":
        report["message"] = "complete projection agreement" if report["scope"]["mode"] == "projection" else "complete agreement of supported comparison fields"
    return report


def human_report(report):
    lines = [f"{report['status'].upper()}: {report['inputs']['left']} vs {report['inputs']['right']}",
             f"run={report['run_id']} scope={report['scope']['mode']} compared_steps={report['compared_steps']}",
             f"compared fields: {json.dumps(report.get('compared_fields', {}), sort_keys=True)}",
             f"suffix validated: {str(report['suffix_validated']).lower()}"]
    if "message" in report:
        lines.append(report["message"])
    if "error" in report:
        error = report["error"]
        lines.append(f"invalid input {error['source']} line {error['line']} step {error['step']}: {error['message']}")
    if "first_disagreement" in report:
        first = report["first_disagreement"]
        lines.append(f"first disagreement: {first['category']} fields={','.join(first['fields']) or '(row kind/length)'}")
        for side in ("left", "right"):
            lines.append(f"{side}: {json.dumps(first[side], sort_keys=True)}")
        for field, values in first.get("values", {}).items():
            lines.append(f"{field}: {json.dumps(values, sort_keys=True)}")
    if report["context"]:
        lines.append("context (preceding rows and disagreement):")
        lines.extend(json.dumps(pair, sort_keys=True) for pair in report["context"])
    return "\n".join(lines)


def _positive(value):
    number = int(value)
    if number < 1:
        raise argparse.ArgumentTypeError("must be positive")
    return number


def _nonnegative(value):
    number = int(value)
    if number < 0:
        raise argparse.ArgumentTypeError("must be nonnegative")
    return number


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("left")
    parser.add_argument("right")
    parser.add_argument("--run-id", required=True, help="caller-assigned identity of this one transaction/run pair")
    parser.add_argument("--json", action="store_true", help="emit one deterministic JSON report")
    parser.add_argument("--max-row-bytes", type=_positive, default=1024 * 1024)
    parser.add_argument("--context", type=_nonnegative, default=3, help="number of preceding row pairs in diagnostic context")
    parser.add_argument("--max-value-chars", type=_positive, default=256)
    parser.add_argument("--step-fields", help="comma-separated explicit projection; pc/op/depth always included")
    parser.add_argument("--summary-fields", help="comma-separated explicit summary projection")
    parser.add_argument("--validate-suffix", action="store_true", help="validate both suffixes after first disagreement")
    args = parser.parse_args(argv)
    if args.left == "-" and args.right == "-":
        parser.error("at most one input can be stdin (-)")
    report = None
    try:
        with ExitStack() as stack:
            streams = [sys.stdin.buffer if path == "-" else stack.enter_context(open(path, "rb")) for path in (args.left, args.right)]
            report = compare_streams(*streams, left_name=args.left, right_name=args.right, run_id=args.run_id,
                                     max_row_bytes=args.max_row_bytes, context=args.context,
                                     max_value_chars=args.max_value_chars,
                                     step_fields=args.step_fields.split(",") if args.step_fields is not None else None,
                                     summary_fields=args.summary_fields.split(",") if args.summary_fields is not None else None,
                                     validate_suffix=args.validate_suffix)
    except (OSError, ValueError) as exc:
        report = {"status": "invalid_input", "exit_code": 2, "run_id": args.run_id,
                  "inputs": {"left": args.left, "right": args.right}, "scope": {"mode": "requested"},
                  "compared_steps": 0, "suffix_validated": False, "context": [],
                  "error": {"source": "CLI", "line": None, "step": None, "message": str(exc)}}
    try:
        print(json.dumps(report, sort_keys=True, ensure_ascii=True) if args.json else human_report(report), flush=True)
    except (OSError, UnicodeError):
        return 2
    return report["exit_code"]
