"""Observable comparison/validation controls; no execution semantics fixtures."""
import copy
import importlib.util
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import tracemalloc
import unittest
from unittest import mock

SCRIPT = Path(__file__).parents[1] / "trace_compare.py"
SPEC = importlib.util.spec_from_file_location("trace_compare", SCRIPT)
TRACE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TRACE)


def step(**changes):
    row = {"pc": 0, "op": 96, "gas": "0x100", "gasCost": "0x3", "memSize": 0,
           "stack": [], "depth": 1, "returnData": "0x", "refund": 0}
    row.update(changes)
    return row


def summary(**changes):
    row = {"stateRoot": "0x1234", "output": "0x", "gasUsed": "0x3", "pass": True}
    row.update(changes)
    return row


def stream(rows):
    return io.BytesIO("".join(json.dumps(row) + "\n" for row in rows).encode())


def compare(left, right, **kwargs):
    return TRACE.compare_streams(stream(left), stream(right), run_id="tx-7", **kwargs)


class GeneratedTrace:
    """Generates bounded rows on demand; never holds the trace in a container."""
    def __init__(self, count, mismatch=None):
        self.count, self.mismatch, self.index = count, mismatch, 0
        self.operation = json.dumps(step()).encode() + b"\n"
        self.changed = json.dumps(step(gas="0xfe")).encode() + b"\n"
        self.summary = json.dumps(summary()).encode() + b"\n"
        self.max_requested = 0

    def readline(self, size):
        self.max_requested = max(self.max_requested, size)
        index = self.index
        self.index += 1
        row = self.summary if index == self.count else b"" if index > self.count else self.changed if index == self.mismatch else self.operation
        return row[:size]


class TraceCompareTests(unittest.TestCase):
    def test_equal_validates_complete_stream_and_reports_scope(self):
        result = compare([step(), summary()], [step(), summary()])
        self.assertEqual(result["exit_code"], 0)
        self.assertTrue(result["suffix_validated"])
        self.assertEqual(result["validated_records"], {"left": 2, "right": 2})
        self.assertEqual(result["compared_steps"], 1)
        self.assertIn("returnData", result["compared_fields"]["step"])
        self.assertEqual(result["inputs"], {"left": "left", "right": "right"})

    def test_numeric_hex_equivalence_and_byte_case(self):
        a = step(gas="0x000a", stack=["0x00", "0x0A"], returnData="0xAB00")
        b = step(gas="0xA", stack=["0x0", "0xa"], returnData="0xab00")
        self.assertEqual(compare([a, summary()], [b, summary(gasUsed="0x03")])["exit_code"], 0)
        b["returnData"] = "0xab"
        self.assertEqual(compare([a, summary()], [b, summary()])["first_disagreement"]["fields"], ["returnData"])

    def test_summary_only_zero_step_runs(self):
        result = compare([summary()], [summary()])
        self.assertEqual(result["exit_code"], 0)
        self.assertEqual(result["compared_steps"], 0)

    def test_summary_outcomes_are_compared(self):
        for field, value in (("stateRoot", "0xabcd"), ("gasUsed", "0x4"), ("output", "0x00"), ("pass", False)):
            with self.subTest(field=field):
                result = compare([step(), summary()], [step(), summary(**{field: value})])
                self.assertEqual(result["exit_code"], 1)
                self.assertEqual(result["first_disagreement"]["fields"], [field])
                self.assertEqual(result["first_disagreement"]["left"]["line"], 2)

    def test_nested_frames_repeated_pc_do_not_resynchronize(self):
        a = [step(pc=0, depth=1), step(pc=0, depth=2), step(pc=2, depth=2), step(pc=0, depth=1), summary()]
        b = [step(pc=0, depth=1), step(pc=0, depth=1), step(pc=0, depth=2), step(pc=2, depth=2), summary()]
        result = compare(a, b, left_name="jaune", right_name="reference")
        first = result["first_disagreement"]
        self.assertEqual(first["category"], "control_flow")
        self.assertEqual(first["fields"], ["depth"])
        self.assertEqual(first["left"]["step"], 1)
        self.assertEqual(first["left"]["line"], 2)
        self.assertEqual(first["left"]["pc"], 0)
        self.assertEqual(first["left"]["op"], 96)
        self.assertEqual(first["values"]["depth"]["left"]["value"], 2)
        self.assertFalse(result["suffix_validated"])

    def test_extra_or_missing_operation(self):
        for a, b in (([step(), summary()], [step(), step(), summary()]),
                     ([step(), step(), summary()], [step(), summary()])):
            result = compare(a, b, validate_suffix=True)
            self.assertEqual(result["exit_code"], 1)
            self.assertEqual(result["first_disagreement"]["category"], "control_flow_length")
            self.assertTrue(result["suffix_validated"])

    def test_missing_observations_never_become_agreement_or_zero(self):
        for field in ("gas", "returnData", "stack", "refund"):
            a = step()
            del a[field]
            for b in (a, step()):
                with self.subTest(field=field, both=a == b):
                    result = compare([a, summary()], [b, summary()])
                    self.assertEqual(result["exit_code"], 3)
                    self.assertEqual(result["first_disagreement"]["category"], "unavailable_observation")
                    self.assertFalse(result["first_disagreement"]["values"][field]["left"]["available"])
        a = summary()
        del a["pass"]
        self.assertEqual(compare([a], [a])["exit_code"], 3)

    def test_missing_optional_field_on_one_side_is_unavailable(self):
        result = compare([step(opName="PUSH1"), summary()], [step(), summary()])
        self.assertEqual(result["exit_code"], 3)
        self.assertEqual(result["first_disagreement"]["fields"], ["opName"])
        self.assertEqual(compare([step(), summary()], [step(), summary()])["exit_code"], 0)

    def test_projection_is_explicit_and_still_compares_control_flow(self):
        result = compare([step(gas="0x1"), summary()], [step(gas="0x2"), summary()], step_fields=["stack"])
        self.assertEqual(result["exit_code"], 0)
        self.assertEqual(result["message"], "complete projection agreement")
        self.assertEqual(result["scope"]["step_fields"], ["pc", "op", "depth", "stack"])
        self.assertEqual(compare([step(depth=1), summary()], [step(depth=2), summary()], step_fields=["gas"])["exit_code"], 1)
        self.assertEqual(compare([step(gas=1), summary()], [step(gas=1), summary()], step_fields=["stack"])["exit_code"], 2)

    def test_control_flow_difference_survives_missing_payload(self):
        a = step()
        del a["returnData"]
        result = compare([a, summary()], [step(op=0), summary()])
        self.assertEqual(result["first_disagreement"]["fields"], ["op"])
        self.assertEqual(result["exit_code"], 1)

    def test_empty_missing_summary_truncated_or_trailing_inputs(self):
        good = json.dumps(summary()).encode() + b"\n"
        malformed = (b"", json.dumps(step()).encode() + b"\n", b'{"pc":', good + b"\n", good + good,
                     good + json.dumps(step()).encode(), b"\xff", b"[]\n", b"{}\n", b"null\n")
        for data in malformed:
            with self.subTest(data=data):
                result = TRACE.compare_streams(io.BytesIO(data), io.BytesIO(data), run_id="invalid")
                self.assertEqual(result["exit_code"], 2)
                self.assertFalse(result["suffix_validated"])

    def test_missing_final_newline_is_valid_when_summary_is_complete(self):
        data = json.dumps(summary()).encode()
        self.assertEqual(TRACE.compare_streams(io.BytesIO(data), io.BytesIO(data), run_id="zero")["exit_code"], 0)

    def test_duplicate_keys_nested_or_outer_rejected(self):
        rows = [json.dumps(step()).replace('"pc": 0', '"pc": 1, "pc": 0'),
                json.dumps(step(storage={})).replace('"storage": {}', '"storage": {"0x00":"0x01","0x00":"0x01"}')]
        for row in rows:
            data = (row + "\n" + json.dumps(summary())).encode()
            result = TRACE.compare_streams(io.BytesIO(data), io.BytesIO(data), run_id="duplicates")
            self.assertEqual(result["exit_code"], 2)
            self.assertIn("duplicate key", result["error"]["message"])

    def test_invalid_typed_values(self):
        cases = (("pc", True), ("op", 256), ("depth", 1.0), ("refund", -1), ("memSize", "0x0"),
                 ("gas", 1), ("gas", "0x"), ("gas", "0X1"), ("gas", "0xgg"),
                 ("returnData", "0x1"), ("stack", None), ("stack", [False]), ("memory", "0x"),
                 ("memory", ["0x1"]), ("storage", []), ("storage", {"x": "0x00"}),
                 ("storage", {"0xAB": "0x01", "0xab": "0x01"}), ("error", None), ("error", "reverted"),
                 ("opName", 96), ("gas", float("nan")), ("refund", float("inf")))
        for field, value in cases:
            with self.subTest(field=field, value=value):
                a = step(**{field: value})
                self.assertEqual(compare([a, summary()], [a, summary()])["exit_code"], 2)
        for field, value in (("pass", "true"), ("pass", 1), ("output", ""), ("time", True), ("fork", 1)):
            with self.subTest(field=field, value=value):
                a = summary(**{field: value})
                self.assertEqual(compare([a], [a])["exit_code"], 2)

    def test_unknown_mixed_and_control_missing_rows_rejected(self):
        a = step()
        del a["depth"]
        for row in (a, step(extra=0), step(gasUsed="0x1"), summary(pc=0)):
            self.assertEqual(compare([row, summary()], [row, summary()])["exit_code"], 2)

    def test_optional_semantic_fields_and_time_policy(self):
        a = step(opName="PUSH1", error="0x", memory=["0x00"], storage={"0xab": "0xcd"})
        b = copy.deepcopy(a)
        b["storage"] = {"0xAB": "0xCD"}
        self.assertEqual(compare([a, summary(time=1, fork="Prague")], [b, summary(time=2, fork="Prague")])["exit_code"], 0)
        b["memory"] = ["0x01"]
        self.assertEqual(compare([a, summary()], [b, summary()])["first_disagreement"]["fields"], ["memory"])
        self.assertEqual(compare([summary(fork="Prague")], [summary(fork="Osaka")])["exit_code"], 1)

    def test_malformed_suffix_cannot_disguise_complete_equality(self):
        a = json.dumps(step()).encode() + b"\n" + b"bad\n"
        b = json.dumps(step(gas="0x2")).encode() + b"\n" + b"bad\n"
        early = TRACE.compare_streams(io.BytesIO(a), io.BytesIO(b), run_id="early")
        self.assertEqual(early["exit_code"], 1)
        self.assertFalse(early["suffix_validated"])
        full = TRACE.compare_streams(io.BytesIO(a), io.BytesIO(b), run_id="full", validate_suffix=True)
        self.assertEqual(full["exit_code"], 2)
        self.assertIn("first_disagreement", full)
        self.assertFalse(full["suffix_validated"])

    def test_row_limit_enforced_during_bounded_read(self):
        a = GeneratedTrace(2)
        result = TRACE.compare_streams(a, GeneratedTrace(2), run_id="limit", max_row_bytes=16)
        self.assertEqual(result["exit_code"], 2)
        self.assertEqual(a.max_requested, 17)
        self.assertIn("max_row_bytes", result["error"]["message"])

    def test_context_and_value_previews_bounded(self):
        rows = [step(pc=index) for index in range(10)]
        a, b = rows + [step(stack=["0x1234567890"] * 100), summary()], rows + [step(stack=["0x1"] * 100), summary()]
        result = compare(a, b, context=2, max_value_chars=20)
        self.assertEqual(len(result["context"]), 3)
        self.assertEqual(result["context"][0]["left"]["step"], 8)
        value = result["first_disagreement"]["values"]["stack"]["left"]
        self.assertTrue(value["truncated"])
        self.assertEqual(len(value["preview"]), 20)

    def test_late_mismatch_generator_stream(self):
        left, right = GeneratedTrace(20000), GeneratedTrace(20000, mismatch=19999)
        result = TRACE.compare_streams(left, right, run_id="large", context=2)
        self.assertEqual(result["exit_code"], 1)
        self.assertEqual(result["first_disagreement"]["left"]["step"], 19999)
        self.assertEqual(result["first_disagreement"]["left"]["line"], 20000)
        self.assertEqual(result["first_disagreement"]["fields"], ["gas"])
        self.assertLessEqual(left.index, 20000)

    def test_generator_memory_does_not_scale_with_trace_length(self):
        def peak(count):
            tracemalloc.start()
            try:
                result = TRACE.compare_streams(GeneratedTrace(count), GeneratedTrace(count), run_id="memory", context=2)
                _, measured = tracemalloc.get_traced_memory()
                self.assertEqual(result["exit_code"], 0)
                self.assertEqual(result["compared_steps"], count)
                return measured
            finally:
                tracemalloc.stop()
        small, large = peak(50), peak(5000)
        self.assertLess(large, small + 256 * 1024)
        self.assertLess(large, 1024 * 1024)

    def test_read_error_is_invalid_input(self):
        class Failed:
            def readline(self, size):
                raise OSError("planted read failure")
        result = TRACE.compare_streams(Failed(), stream([summary()]), run_id="io")
        self.assertEqual(result["exit_code"], 2)
        self.assertIn("planted read failure", result["error"]["message"])

    def test_invalid_api_configuration(self):
        for options in ({"run_id": ""}, {"context": -1}, {"context": True}, {"max_row_bytes": 0},
                        {"max_value_chars": 0}, {"step_fields": []}, {"step_fields": ["gas", "gas"]},
                        {"summary_fields": ["time"]}):
            kwargs = {"run_id": "api", **options}
            with self.subTest(options=options), self.assertRaises(ValueError):
                TRACE.compare_streams(stream([summary()]), stream([summary()]), **kwargs)

    def test_cli_json_human_and_exit_codes(self):
        entry = SCRIPT.with_name("compare-traces.py")
        with tempfile.TemporaryDirectory() as directory:
            left, right = Path(directory) / "a.jsonl", Path(directory) / "b.jsonl"
            left.write_bytes(stream([step(), summary()]).getvalue())
            for rows, expected in (([step(), summary()], 0), ([step(gas="0x2"), summary()], 1), ([], 2)):
                right.write_bytes(stream(rows).getvalue())
                result = subprocess.run([sys.executable, str(entry), str(left), str(right), "--run-id", "tx", "--json"], capture_output=True, text=True)
                self.assertEqual(result.returncode, expected, result.stderr)
                self.assertEqual(json.loads(result.stdout)["exit_code"], expected)
                self.assertEqual(result.stderr, "")
            a = step()
            del a["returnData"]
            right.write_bytes(stream([a, summary()]).getvalue())
            result = subprocess.run([sys.executable, str(entry), str(left), str(right), "--run-id", "tx"], capture_output=True, text=True)
            self.assertEqual(result.returncode, 3)
            self.assertIn("unavailable_observation", result.stdout)
            self.assertIn("depth", result.stdout)
            self.assertIn("suffix validated: false", result.stdout)
            result = subprocess.run([sys.executable, str(entry), str(left), str(right), "--run-id", "tx", "--step-fields", "gas"], capture_output=True, text=True)
            self.assertEqual(result.returncode, 0)
            self.assertIn("projection agreement", result.stdout)

    def test_report_io_failure_does_not_return_success(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "trace"
            path.write_bytes(stream([summary()]).getvalue())
            with mock.patch("builtins.print", side_effect=OSError("report sink failed")):
                self.assertEqual(TRACE.main([str(path), str(path), "--run-id", "io"]), 2)

    def test_cli_stdin_and_missing_file(self):
        entry = SCRIPT.with_name("compare-traces.py")
        with tempfile.TemporaryDirectory() as directory:
            right = Path(directory) / "trace"
            right.write_bytes(stream([summary()]).getvalue())
            result = subprocess.run([sys.executable, str(entry), "-", str(right), "--run-id", "stdin", "--json"], input=right.read_bytes(), capture_output=True)
            self.assertEqual(result.returncode, 0)
            missing = subprocess.run([sys.executable, str(entry), str(right.with_name("missing")), str(right), "--run-id", "io", "--json"], capture_output=True, text=True)
            self.assertEqual(missing.returncode, 2)
            self.assertEqual(json.loads(missing.stdout)["status"], "invalid_input")


if __name__ == "__main__":
    unittest.main()
