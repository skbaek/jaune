#!/usr/bin/env python3
"""Native trace serialization/CLI controls, not a second execution-fidelity suite."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest

from trace_compare import normalize

ROOT = Path(__file__).resolve().parents[1]
CALLER = "0x" + "11" * 20
ADDRESS = "0x" + "00" * 18 + "0200"
CHILD = "0x" + "00" * 18 + "0300"
BINARY = ROOT / ".lake/build/bin/jaune-trace"


def request(code):
    return {"runId": "control", "fork": "Prague", "memory": True,
            "alloc": {ADDRESS: {"balance": "0x00", "nonce": "0x00", "code": "0x" + code,
                                "storage": {}}},
            "env": {"currentBaseFee": "0x0", "currentExcessBlobGas": "0x0"},
            "message": {"kind": "call", "caller": CALLER, "address": ADDRESS,
                        "gas": "0x100000", "accessedAddresses": [CALLER, ADDRESS, CHILD]}}


def transaction_request(case="call-logs", fork="Prague"):
    directory = ROOT / "scripts/t8n/cases" / case
    return {"runId": "transaction-control", "fork": fork, "memory": True,
            "alloc": json.loads((directory / "alloc.json").read_text()),
            "env": json.loads((directory / "env.json").read_text()),
            "transaction": json.loads((directory / "txs.json").read_text())[0]}


class TraceControls(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)

    def run_request(self, value, expect=0, outcome="executed"):
        src, out = self.root / "request.json", self.root / "output"
        src.write_text(json.dumps(value))
        result = subprocess.run([str(BINARY), str(src), str(out)], capture_output=True, timeout=30)
        self.assertEqual(result.returncode, expect, result.stderr.decode(errors="replace"))
        self.assertEqual(result.stdout, b"")
        rows = [json.loads(line) for line in (out / "trace.jsonl").read_text().splitlines()] if (out / "trace.jsonl").exists() else []
        for row in rows:
            normalize(row)
        if expect == 0:
            self.assertEqual(result.stderr, b"")
            metadata = json.loads((out / "run.json").read_text())
            self.assertTrue(metadata["complete"])
            self.assertEqual(metadata["outcome"], outcome)
            self.assertEqual(metadata["traceComplete"], outcome == "executed")
            self.assertEqual(sum("pass" in row for row in rows), int(outcome == "executed"))
            if outcome == "executed":
                self.assertIn("pass", rows[-1])
        else:
            self.assertFalse((out / "run.json").exists())
            self.assertFalse(any("pass" in row for row in rows))
        return rows, result

    def test_arithmetic_fields_stack_order_and_identity(self):
        rows, _ = self.run_request(request("600260030100"))
        self.assertEqual([r["pc"] for r in rows[:-1]], [0, 2, 4, 5])
        self.assertEqual([r["gasCost"] for r in rows[:-1]], ["0x3", "0x3", "0x3", "0x0"])
        self.assertEqual(rows[2]["stack"], ["0x2", "0x3"])
        self.assertEqual(rows[3]["stack"], ["0x5"])
        self.assertEqual(rows[-1]["gasUsed"], "0x9")
        frames = [json.loads(line) for line in (self.root / "output/frames.jsonl").read_text().splitlines()]
        self.assertTrue(all(r["runId"] == "control" and r["frame"] == 0 for r in frames))
        self.assertEqual([r["step"] for r in frames if r["event"] == "instruction"], [0, 1, 2, 3])
        self.assertEqual(frames[0]["event"], "entered")
        self.assertEqual(frames[-1], {"runId": "control", "frame": 0, "depth": 1, "event": "settled", "root": True})

    def test_memory_words_and_return_data(self):
        rows, _ = self.run_request(request("602a60005360016000f3"))
        self.assertEqual(rows[2]["memory"], [])
        self.assertEqual(rows[3]["memory"], ["0x2a" + "00" * 31])
        self.assertEqual(rows[3]["memSize"], 32)
        self.assertEqual(rows[-1]["output"], "0x2a")
        self.assertTrue(all(row["returnData"] == "0x" for row in rows[:-1]))

    def test_precompile_has_zero_instruction_rows(self):
        value = request("")
        value["message"].update(address="0x" + "00" * 19 + "04", input="0x2a")
        rows, _ = self.run_request(value)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["output"], "0x2a")
        self.assertEqual(rows[0]["gasUsed"], "0x12")

    def test_empty_code_has_no_synthetic_instruction(self):
        value = request("")
        value["maxSteps"] = "0x0"
        rows, _ = self.run_request(value)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["gasUsed"], "0x0")

    def test_create_child_has_unique_frame_and_own_depth(self):
        rows, _ = self.run_request(request("69600060005360016000f3600052600a60166000f000"))
        self.assertEqual(len(rows) - 1, 14)
        create = next(row for row in rows[:-1] if row["op"] == 240)
        self.assertEqual(create["gasCost"], "0x7d02")
        self.assertEqual([row["depth"] for row in rows[:-1]], [1] * 7 + [2] * 6 + [1])
        frames = [json.loads(line) for line in (self.root / "output/frames.jsonl").read_text().splitlines()]
        entries = [r for r in frames if r["event"] == "entered"]
        self.assertEqual([(r["frame"], r.get("parent")) for r in entries], [(0, None), (1, 0)])

    def test_root_creation_uses_explicit_address_and_initcode(self):
        value = request("")
        value["message"].update(kind="create", input="0x600160005360016000f3")
        rows, _ = self.run_request(value)
        self.assertEqual(rows[-1]["output"], "0x01")
        self.assertEqual(rows[-1]["gasUsed"], "0xda")
        self.assertTrue(rows[-1]["pass"])

    def test_invalid_cost_stays_unavailable_and_error_is_bytes(self):
        rows, _ = self.run_request(request("fe"))
        self.assertEqual(len(rows), 2)
        self.assertNotIn("gasCost", rows[0])
        self.assertTrue(bytes.fromhex(rows[0]["error"][2:]).decode())
        self.assertFalse(rows[-1]["pass"])

    def test_out_of_gas_does_not_invent_zero_cost(self):
        value = request("6001")
        value["message"]["gas"] = "0x1"
        rows, _ = self.run_request(value)
        self.assertNotIn("gasCost", rows[0])
        self.assertEqual(rows[-1]["gasUsed"], "0x1")
        self.assertFalse(rows[-1]["pass"])

    def test_revert_keeps_pre_step_stack(self):
        rows, _ = self.run_request(request("60006000fd"))
        self.assertEqual(rows[-2]["stack"], ["0x0", "0x0"])
        self.assertEqual(rows[-2]["gasCost"], "0x0")
        self.assertFalse(rows[-1]["pass"])

    def refund_request(self, child_code):
        value = request("60006000556000600060006000600061030061fffff100")
        value["alloc"][ADDRESS]["storage"] = {"0x00": "0x01"}
        value["alloc"][CHILD] = {"balance": "0x00", "nonce": "0x00", "code": "0x" + child_code,
                                  "storage": {"0x00": "0x01"}}
        return value

    def test_child_refund_includes_ancestors(self):
        rows, _ = self.run_request(self.refund_request("600060005500"))
        child = [r for r in rows[:-1] if r["depth"] == 2]
        self.assertEqual(child[0]["refund"], 4800)
        self.assertEqual(child[-1]["refund"], 9600)
        self.assertEqual(rows[-2]["refund"], 9600)

    def test_reverted_child_refund_does_not_leak_to_parent(self):
        rows, _ = self.run_request(self.refund_request("600060005560006000fd"))
        child = [r for r in rows[:-1] if r["depth"] == 2]
        self.assertEqual(child[-1]["refund"], 9600)
        self.assertEqual(rows[-2]["refund"], 4800)
        self.assertTrue(rows[-1]["pass"])

    def test_instruction_limit_cannot_complete(self):
        value = request("600160020100")
        value["maxSteps"] = "0x2"
        rows, result = self.run_request(value, 2)
        self.assertEqual(len(rows), 2)
        self.assertIn(b"instruction limit", result.stderr)

    def test_row_limit_cannot_complete(self):
        value = request("00")
        value["maxRowBytes"] = "0x1"
        rows, result = self.run_request(value, 2)
        self.assertEqual(rows, [])
        self.assertIn(b"row byte limit", result.stderr)

    def test_memory_limit_cannot_complete(self):
        value = request("602a60005300")
        value["maxDataBytes"] = "0x1"
        _, result = self.run_request(value, 2)
        self.assertIn(b"memory observation", result.stderr)

    def test_existing_directory_is_preserved(self):
        out = self.root / "output"
        out.mkdir()
        marker = out / "keep"
        marker.write_text("untouched")
        _, result = self.run_request(request("00"), 2)
        self.assertIn(b"exists", result.stderr)
        self.assertEqual(marker.read_text(), "untouched")

    def test_unknown_input_field_refused(self):
        value = request("00")
        value["message"]["garbage"] = 3
        _, result = self.run_request(value, 2)
        self.assertIn(b"unrecognised field", result.stderr)
        self.assertFalse((self.root / "output").exists())

    def test_identity_and_chain_boundaries_refused_before_output(self):
        for field, value in [("runId", "  "), ("chainId", hex(2**64)), ("fork", "unknown")]:
            with self.subTest(field=field):
                data = request("00")
                data[field] = value
                self.run_request(data, 2)
                self.assertFalse((self.root / "output").exists())

    def test_transaction_summary_has_settled_gas_and_wire_identity(self):
        value = transaction_request()
        rows, _ = self.run_request(value)
        self.assertEqual(int(rows[-1]["gasUsed"], 16), 21000 + sum(int(r["gasCost"], 16) for r in rows[:-1]))
        metadata = json.loads((self.root / "output/run.json").read_text())
        self.assertEqual(metadata["scope"], "transaction")
        self.assertEqual(metadata["transactionIndex"], 0)
        self.assertEqual(metadata["transactionHash"], "0xa6b4da4327822d815dc46cc0f40259191130a8d8c0eed57591c3a22710e41971")
        frames = [json.loads(line) for line in (self.root / "output/frames.jsonl").read_text().splitlines()]
        self.assertTrue(all(r["runId"] == value["runId"] for r in frames))

    def test_zero_instruction_transaction_still_has_settled_summary(self):
        value = transaction_request()
        value["alloc"][ADDRESS]["code"] = "0x"
        value["maxSteps"] = "0x0"
        rows, _ = self.run_request(value)
        self.assertEqual(len(rows), 1)
        self.assertEqual(rows[0]["gasUsed"], "0x5208")

    def test_transaction_rejection_is_not_a_complete_execution_trace(self):
        value = transaction_request()
        value["alloc"].pop("0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b")
        rows, _ = self.run_request(value, outcome="rejected")
        self.assertEqual(rows, [])
        metadata = json.loads((self.root / "output/run.json").read_text())
        self.assertTrue(metadata["error"])

    def test_transaction_exception_is_executed_but_pass_false(self):
        value = transaction_request()
        value["alloc"][ADDRESS]["code"] = "0xfe"
        rows, _ = self.run_request(value)
        self.assertFalse(rows[-1]["pass"])
        self.assertNotIn("gasCost", rows[0])

    def test_authorization_refund_is_visible_in_root_and_child(self):
        value = transaction_request("am-delegation-state-test")
        target = value["transaction"]["to"]
        value["alloc"][target]["code"] = "0x60006000600060006000600061030061fffff100"
        value["alloc"][CHILD] = {"nonce": "0x00", "balance": "0x00", "code": "0x00", "storage": {}}
        rows, _ = self.run_request(value)
        self.assertTrue(any(r["depth"] == 2 for r in rows[:-1]))
        self.assertTrue(all(r["refund"] == 25000 for r in rows[:-1]))
        metadata = json.loads((self.root / "output/run.json").read_text())
        self.assertEqual(metadata["authorizationRefund"], 25000)

    def test_amsterdam_prepared_frame_has_no_guessed_gas_cost(self):
        rows, _ = self.run_request(transaction_request("am-delegation-state-test", "Amsterdam"))
        self.assertGreater(len(rows), 1)
        self.assertTrue(all("gasCost" not in r for r in rows[:-1]))

    def test_transaction_creation_serializes_initcode_output(self):
        rows, _ = self.run_request(transaction_request("am-create-state-test"))
        self.assertEqual(rows[-1]["output"], "0x00")
        self.assertTrue(rows[-1]["pass"])

    def test_transaction_step_limit_never_emits_frame_summary(self):
        value = transaction_request()
        value["maxSteps"] = "0x1"
        rows, result = self.run_request(value, 2)
        self.assertEqual(len(rows), 1)
        self.assertIn(b"instruction limit", result.stderr)

    def test_transaction_output_limit_applies_after_settlement(self):
        value = transaction_request()
        value["alloc"][ADDRESS]["code"] = "0x602a60005360016000f3"
        value.update(memory=False, maxDataBytes="0x0")
        _, result = self.run_request(value, 2)
        self.assertIn(b"output exceeds", result.stderr)

    def test_ambiguous_or_absent_execution_scope_refused(self):
        for ambiguous in [False, True]:
            value = transaction_request()
            if ambiguous:
                value["message"] = request("00")["message"]
            else:
                value.pop("transaction")
            _, result = self.run_request(value, 2)
            self.assertIn(b"exactly one", result.stderr)
            self.assertFalse((self.root / "output").exists())

    @unittest.skipUnless(os.name == "posix", "requires POSIX file-size limits")
    def test_write_failure_cannot_complete(self):
        import resource
        import signal
        def limit_output():
            signal.signal(signal.SIGXFSZ, signal.SIG_IGN)
            resource.setrlimit(resource.RLIMIT_FSIZE, (256, 256))
        src, out = self.root / "request.json", self.root / "output"
        src.write_text(json.dumps(transaction_request()))
        result = subprocess.run([str(BINARY), str(src), str(out)], capture_output=True,
                                timeout=30, preexec_fn=limit_output)
        self.assertEqual(result.returncode, 2, result.stderr)
        self.assertTrue(result.stderr)
        self.assertFalse((out / "run.json").exists())
        # Real I/O failure may tear a JSON row. Comparing the partial file to
        # itself must still reject it, never turn it into agreement.
        comparison = subprocess.run(["python3", str(ROOT / "scripts/compare-traces.py"),
                                     str(out / "trace.jsonl"), str(out / "trace.jsonl")],
                                    capture_output=True, timeout=30)
        self.assertEqual(comparison.returncode, 2, comparison.stdout + comparison.stderr)

    def test_creation_collision_has_summary_without_entered_frame(self):
        value = transaction_request("am-create-state-test")
        value["alloc"]["0x6295ee1b4f6dd65047762f924ecd367c17eabf8f"] = {
            "nonce": "0x01", "balance": "0x00", "code": "0x00", "storage": {}}
        rows, _ = self.run_request(value)
        self.assertEqual(len(rows), 1)
        self.assertFalse(rows[0]["pass"])
        self.assertEqual((self.root / "output/frames.jsonl").read_text(), "")

    def test_amsterdam_intrinsic_rejection_has_no_synthetic_frame(self):
        rows, _ = self.run_request(transaction_request("am-reject-intrinsic-state-test", "Amsterdam"),
                                   outcome="rejected")
        self.assertEqual(rows, [])
        self.assertEqual((self.root / "output/frames.jsonl").read_text(), "")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--binary", type=Path, default=BINARY)
    args, rest = parser.parse_known_args()
    BINARY = args.binary.resolve()
    if not BINARY.is_file():
        parser.error("build jaune-trace through the owned wrapper first")
    unittest.main(argv=[__file__, *rest])
