"""Protocol controls for geth callbacks; these do not assert EVM equivalence."""
import io
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from geth_trace_adapter import DIALECT, adapt_stream, main
from trace_compare import TraceInputError, compare_streams


def enter(kind="CALL", **changes):
    return dict({"from": "0x" + "11" * 20, "to": "0x" + "22" * 20,
                 "gas": "0x10000", "value": "0x0", "type": kind}, **changes)


def op(**changes):
    return dict({"pc": 0, "op": 0, "opName": "STOP", "gas": "0x10000",
                 "gasCost": "0x0", "memSize": 0, "stack": [], "depth": 1, "refund": 0}, **changes)


def end(**changes):
    return dict({"output": "", "gasUsed": "0x0"}, **changes)


def encode(rows):
    return b"".join((json.dumps(row) + "\n").encode() for row in rows)


def adapted(rows, **kwargs):
    return list(adapt_stream(io.BytesIO(encode(rows)), dialect=DIALECT, run_id="case", **kwargs))


class GethAdapterTests(unittest.TestCase):
    def invalid(self, rows, message=None, **kwargs):
        with self.assertRaisesRegex(TraceInputError, message or "."):
            adapted(rows, **kwargs)

    def test_zero_step_root_and_case_normalization(self):
        self.assertEqual(adapted([enter(), end(output="AABB", gasUsed="0x000F")]),
                         [{"output": "0xaabb", "gasUsed": "0xf", "pass": True}])
        self.assertEqual(adapted([enter("CREATE"), end()])[-1]["pass"], True)

    def test_missing_observations_stay_unavailable(self):
        rows = adapted([enter(), op(stack=None), end()])
        for field in ("returnData", "storage", "memory", "stack"):
            self.assertNotIn(field, rows[0])
        self.assertNotIn("stateRoot", rows[-1])
        result = compare_streams(io.BytesIO(encode(rows)), io.BytesIO(encode(rows)), run_id="case")
        self.assertEqual(result["status"], "unavailable")
        result = compare_streams(io.BytesIO(encode(rows)), io.BytesIO(encode(rows)), run_id="case",
                                 step_fields=["gas", "gasCost"], summary_fields=["output", "gasUsed", "pass"])
        self.assertEqual(result["status"], "equal")
        self.assertEqual(result["scope"]["mode"], "projection")

    def test_nested_create_and_precompile_keep_order_and_only_root_summary(self):
        rows = [enter(), op(op=0xf0, opName="CREATE"), enter("CREATE"),
                op(depth=2, pc=0, op=0xfa, opName="STATICCALL"), enter("STATICCALL", value=None),
                end(output="aa", gasUsed="0x12"), op(depth=2, pc=1), end(output="00", gasUsed="0x20"),
                op(pc=1), end(gasUsed="0x100")]
        result = adapted(rows)
        self.assertEqual([(r["pc"], r["depth"]) for r in result[:-1]], [(0, 1), (0, 2), (1, 2), (1, 1)])
        self.assertEqual(result[-1], {"output": "0x", "gasUsed": "0x100", "pass": True})

    def test_all_supported_child_frame_types(self):
        for opcode, kind in [(0xf0, "CREATE"), (0xf1, "CALL"), (0xf2, "CALLCODE"),
                             (0xf4, "DELEGATECALL"), (0xf5, "CREATE2"),
                             (0xfa, "STATICCALL"), (0xff, "SELFDESTRUCT")]:
            with self.subTest(kind=kind):
                value = None if kind in ("DELEGATECALL", "STATICCALL") else "0x0"
                result = adapted([enter(), op(op=opcode, opName=kind), enter(kind, value=value), end(), end()])
                self.assertEqual(len(result), 2)

    def test_fault_callback_preserves_pre_operation_state(self):
        pre = op(pc=4, op=253, opName="REVERT", stack=["0x0", "0x0"],
                 returnData="0xaa", memory="0x" + "00" * 32, memSize=32, refund=4)
        fault = dict(pre, stack=[], memory="0x" + "ff" * 64, memSize=64,
                     refund=9, error="execution reverted")
        del fault["returnData"]
        result = adapted([enter(), pre, fault, end(error="execution reverted")])
        self.assertEqual(len(result), 2)
        self.assertEqual(result[0]["stack"], ["0x0", "0x0"])
        self.assertEqual(result[0]["memory"], ["0x" + "00" * 32])
        self.assertEqual(result[0]["returnData"], "0xaa")
        self.assertEqual(result[0]["refund"], 4)
        self.assertEqual(bytes.fromhex(result[0]["error"][2:]).decode(), "execution reverted")
        self.assertFalse(result[-1]["pass"])

    def test_standalone_error_is_an_instruction(self):
        result = adapted([enter(), op(error="stack underflow (0 <=> 2)"), end(error="stack underflow (0 <=> 2)")])
        self.assertEqual(len(result), 2)
        self.assertIn("error", result[0])
        self.assertFalse(result[-1]["pass"])

    def test_repeated_pc_is_never_search_aligned(self):
        a = op(pc=3, op=0x56, opName="JUMP", gas="0x20", gasCost="0x8")
        b = dict(a, gas="0x18")
        c = dict(a, gas="0x10", error="bad jump")
        result = adapted([enter(), a, b, c, end(error="bad jump")])
        self.assertEqual([r["gas"] for r in result[:-1]], ["0x20", "0x18", "0x10"])
        self.assertNotIn("error", result[0])

    def test_fault_is_terminal_and_cannot_change_identity(self):
        fault = op(error="failure")
        self.invalid([enter(), fault, op(), end()], "after a fault")
        self.invalid([enter(), fault, fault, end(error="failure")], "after a fault")
        self.invalid([enter(), fault, end()], "errors disagree")
        self.invalid([enter(), op(), op(gasCost="0x1", error="failure"), end(error="failure")], "ambiguous")
        self.invalid([enter(), op(op=0xf1, opName="CALL", error="failure"), enter(), end(), end()])

    def test_child_fault_does_not_fail_root(self):
        result = adapted([enter(), op(op=0xf1, opName="CALL"), enter(),
                          op(depth=2, error="failure"), end(error="failure"), op(pc=1), end()])
        self.assertTrue(result[-1]["pass"])
        self.assertIn("error", result[1])

    def test_memory_layout_and_empty_values(self):
        memory = "00" * 31 + "ab" + "cd" + "00" * 31
        result = adapted([enter(input="0x1234"), op(memory="0x" + memory, memSize=64, returnData="0x"), end()])
        self.assertEqual(result[0]["memory"], ["0x" + memory[:64], "0x" + memory[64:]])
        self.assertEqual(result[0]["returnData"], "0x")
        self.assertEqual(adapted([enter(), op(memory="0x"), end()])[0]["memory"], [])
        for memory, size in [("0x00", 1), ("0x" + "00" * 32, 64), ([], 0), ("zz", 0)]:
            self.invalid([enter(), op(memory=memory, memSize=size), end()])

    def test_depth_entry_and_exit_validation(self):
        for rows in [[], [op(), end()], [end()], [enter()], [enter(), op()],
                     [enter(), op(depth=2), end()], [enter(), enter(), end(), end()],
                     [enter(), op(op=0xf1), enter("CREATE"), end(), end()],
                     [enter(), op(op=0xf1), enter(), op(depth=1), end(), end()],
                     [enter(), op(op=0xf1), enter(), end()],
                     [enter(), op(op=0xff), enter("SELFDESTRUCT"), op(depth=2), end(), end()]]:
            with self.subTest(rows=rows):
                self.invalid(rows)

    def test_no_terminal_output_until_eof_is_verified(self):
        for suffix in [b"\n", b"{}\n", encode([end()]), b"x" * 100]:
            emitted = []
            with self.assertRaises(TraceInputError):
                for row in adapt_stream(io.BytesIO(encode([enter(), op(), end()]) + suffix),
                                        dialect=DIALECT, run_id="case"):
                    emitted.append(row)
            self.assertEqual(len(emitted), 1)
            self.assertNotIn("pass", emitted[0])

    def test_malformed_records_fail_closed(self):
        bad_ops = [op(pc=True), op(op=256), op(depth=1.0), op(gas="123"),
                   op(gas=hex(2**64)), op(refund=-1), op(stack=[hex(2**256)]),
                   op(stack=["0x0"] * 1025), op(returnData="0x0"), op(error=""),
                   op(error=3), op(opName=None), op(storage={}), op(extra=1)]
        bad_ops.append({k: v for k, v in op().items() if k != "gas"})
        for row in bad_ops:
            with self.subTest(row=row):
                self.invalid([enter(), row, end()])
        for row in [enter(value=None), enter(to="0x00"), enter("BOGUS"), enter(extra=1),
                    enter(gas=hex(2**64)), enter(input="0x1")]:
            self.invalid([row, end()])
        for row in [end(output="0x00"), end(gasUsed=0), end(extra=1), end(error="")]:
            self.invalid([enter(), row])

    def test_decoder_rejects_duplicates_unicode_and_non_json(self):
        for raw in [b'{"pc":0,"pc":1}\n', b'{"pc":NaN}\n', b'[]\n', b'\xff\n',
                    b'{"error":"\\ud800"}\n', b'{"unknown":0}\n']:
            with self.subTest(raw=raw), self.assertRaises(TraceInputError):
                list(adapt_stream(io.BytesIO(encode([enter()]) + raw), dialect=DIALECT, run_id="case"))

    def test_duplicate_keys_in_otherwise_valid_stream_fail(self):
        duplicate_op = json.dumps(op())[:-1].encode() + b', "pc": 1}\n'
        raw = encode([enter()]) + duplicate_op + encode([end()])
        with self.assertRaisesRegex(TraceInputError, "duplicate key"):
            list(adapt_stream(io.BytesIO(raw), dialect=DIALECT, run_id="duplicate"))

    def test_row_and_frame_limits(self):
        self.invalid([enter(), end()], "max_row_bytes", max_row_bytes=5)
        self.invalid([enter(), op(op=0xf1), enter(), end(), end()], "max_depth", max_depth=1)
        for key, value in [("max_depth", 0), ("max_row_bytes", False)]:
            with self.assertRaises(ValueError):
                adapted([enter(), end()], **{key: value})
        for dialect, run_id in [("geth", "run"), (DIALECT, " ")]:
            with self.assertRaises(ValueError):
                list(adapt_stream(io.BytesIO(), dialect=dialect, run_id=run_id))

    def test_bounded_reads_and_lazy_output(self):
        class Generated:
            def __init__(self):
                self.reads = 0

            def readline(self, size):
                self_outer.assertEqual(size, 1025)
                self.reads += 1
                if self.reads == 1:
                    return encode([enter()])
                if self.reads <= 5001:
                    return encode([op(pc=self.reads - 2)])
                return encode([end()]) if self.reads == 5002 else b""

        self_outer = self
        src = Generated()
        iterator = adapt_stream(src, dialect=DIALECT, run_id="long", max_row_bytes=1024)
        self.assertEqual(next(iterator)["pc"], 0)
        self.assertEqual(src.reads, 3)
        self.assertEqual(sum(1 for _ in iterator), 5000)
        self.assertEqual(src.reads, 5003)

    def test_read_failure_after_root_exit_cannot_emit_summary(self):
        class FailingEOF(io.BytesIO):
            def readline(self, size):
                raw = super().readline(size)
                if not raw:
                    raise OSError("lost input")
                return raw

        emitted = []
        with self.assertRaisesRegex(TraceInputError, "lost input"):
            for row in adapt_stream(FailingEOF(encode([enter(), op(), end()])), dialect=DIALECT, run_id="io"):
                emitted.append(row)
        self.assertEqual(len(emitted), 1)
        self.assertNotIn("pass", emitted[0])

    def test_output_failure_is_nonzero(self):
        class Output:
            def write(self, data):
                raise OSError("lost output")

        with patch("sys.stdin") as stdin, patch("sys.stdout") as stdout, patch("sys.stderr", new_callable=io.StringIO) as stderr:
            stdin.buffer = io.BytesIO(encode([enter(), end()]))
            stdout.buffer = Output()
            result = main(["-", "--dialect", DIALECT, "--run-id", "io"])
        self.assertEqual(result, 2)
        self.assertIn("lost output", stderr.getvalue())

    def cli(self, raw, *args):
        script = Path(__file__).resolve().parents[1] / "normalize-geth-trace.py"
        return subprocess.run([sys.executable, str(script), "-", "--dialect", DIALECT,
                               "--run-id", "cli", *args], input=raw, capture_output=True)

    def test_cli_success_and_output_limit(self):
        raw = encode([enter(), op(), end()])
        result = self.cli(raw)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stderr, b"")
        self.assertTrue(json.loads(result.stdout.splitlines()[-1])["pass"])
        result = self.cli(raw, "--max-output-bytes", "150")
        self.assertEqual(result.returncode, 2)
        self.assertIn(b"max_output_bytes", result.stderr)
        self.assertNotIn(b'"pass"', result.stdout)

    def test_cli_never_overwrites_existing_output(self):
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory) / "same.jsonl"
            out.write_bytes(b"preserve me")
            result = self.cli(encode([enter(), end()]), "--output", str(out))
            self.assertEqual(result.returncode, 2)
            self.assertEqual(out.read_bytes(), b"preserve me")


if __name__ == "__main__":
    unittest.main()
