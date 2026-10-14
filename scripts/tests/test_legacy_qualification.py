#!/usr/bin/env python3
"""Unit tests for scripts/legacy_qualification.py.

Self-contained and synthetic: no EELS checkout, no network, no private
evidence, and no fixture full checkout. The strict-classifier acceptance
paths use the real tracked baselines (their bytes are pinned by hash) with
synthetic reports derived from them; extraction spot-checks read the five
public fixture files, while every deviation case is synthetic.
"""

from __future__ import annotations

import importlib.util
import json
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

SCRIPTS_DIR = Path(__file__).resolve().parents[1]
if str(SCRIPTS_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPTS_DIR))


def _load_qualification():
    spec = importlib.util.spec_from_file_location(
        "legacy_qualification", SCRIPTS_DIR / "legacy_qualification.py"
    )
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


LQ = _load_qualification()

SMOKE_FLIP = {
    "GeneralStateTests/stCreate2/RevertInCreateInInitCreate2Paris.json",
    "GeneralStateTests/stRevertTest/RevertInCreateInInit_Paris.json",
}


def _report_from_baseline(baseline: bytes, flips: set[str]) -> bytes:
    rows = []
    for line in baseline.decode().splitlines():
        status, path = line.split("\t")
        rows.append(f"{'FAIL' if path in flips else status}\t0.01s\t{path}")
    return ("\n".join(rows) + "\n").encode()


def _synthetic_population(paths, statuses):
    return ("\n".join(f"{s}\t{p}" for s, p in zip(statuses, paths)) + "\n").encode()


def _synthetic_report(paths, statuses):
    return ("\n".join(f"{s}\t0.01s\t{p}" for s, p in zip(statuses, paths)) + "\n").encode()


def _minimal_prague_case(**overrides):
    tx = {
        "data": "0x1234",
        "gasLimit": "0x0a00000000",
        "gasPrice": "0x0a",
        "nonce": "0x00",
        "r": "0x11",
        "s": "0x22",
        "sender": "0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b",
        "to": "",
        "v": "0x1c",
        "value": "0x00",
    }
    tx.update(overrides.pop("tx", {}))
    case = {
        "network": "Prague",
        "sealEngine": "NoProof",
        "config": {"chainid": "0x01"},
        "genesisBlockHeader": {"number": "0x00", "hash": "0x" + "aa" * 32},
        "blocks": [
            {
                "blockHeader": {
                    "number": "0x01",
                    "gasUsed": "0x9999",
                    "coinbase": "0x" + "bb" * 20,
                    "gasLimit": "0x0b00000000",
                    "timestamp": "0x03e8",
                    "mixHash": "0x" + "cc" * 32,
                    "baseFeePerGas": "0x0a",
                    "excessBlobGas": "0x00",
                    "parentBeaconBlockRoot": "0x" + "00" * 32,
                },
                "transactions": [tx],
                "uncleHeaders": [],
                "withdrawals": [],
            }
        ],
        "pre": {"0x01": {"balance": "0x01"}},
    }
    case.update(overrides)
    return case


class StrictClassifierTests(unittest.TestCase):
    def test_smoke_exact_delta_qualifies(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes()
        report = _report_from_baseline(baseline, SMOKE_FLIP)
        verdict = LQ.qualify("smoke", baseline, report, 1)
        self.assertEqual(verdict["verdict"], "QUALIFIED")
        self.assertEqual(verdict["raw_verdict"], "RED")
        self.assertEqual(verdict["raw_exit"], 1)
        self.assertEqual(
            set(verdict["changes"]), SMOKE_FLIP
        )

    def test_full_exact_delta_qualifies(self):
        baseline = (SCRIPTS_DIR / "baseline-full.txt").read_bytes()
        report = _report_from_baseline(baseline, set(LQ.QUALIFIED_PATHS))
        verdict = LQ.qualify("full", baseline, report, 1)
        self.assertEqual(verdict["verdict"], "QUALIFIED")
        self.assertEqual(verdict["files"], 2983)
        self.assertEqual(len(verdict["changes"]), 5)

    def test_extra_change_is_rejected(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes()
        flips = set(SMOKE_FLIP) | {"GeneralStateTests/stZeroKnowledge2/ecmul_0-3_5616_28000_96_Paris.json"}
        with self.assertRaisesRegex(LQ.QualificationError, "exact owner qualification"):
            LQ.qualify("smoke", baseline, _report_from_baseline(baseline, flips), 1)

    def test_missing_change_is_rejected(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes()
        flips = set(list(SMOKE_FLIP)[:1])
        with self.assertRaisesRegex(LQ.QualificationError, "exact owner qualification"):
            LQ.qualify("smoke", baseline, _report_from_baseline(baseline, flips), 1)

    def test_reversed_direction_is_rejected(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes()
        report = _report_from_baseline(baseline, set())
        with self.assertRaisesRegex(LQ.QualificationError, "exact owner qualification"):
            LQ.qualify("smoke", baseline, report, 1)

    def test_raw_exit_zero_is_rejected(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes()
        report = _report_from_baseline(baseline, SMOKE_FLIP)
        with self.assertRaisesRegex(LQ.QualificationError, "RED exit1"):
            LQ.qualify("smoke", baseline, report, 0)

    def test_raw_exit_two_is_rejected(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes()
        report = _report_from_baseline(baseline, SMOKE_FLIP)
        with self.assertRaisesRegex(LQ.QualificationError, "RED exit1"):
            LQ.qualify("smoke", baseline, report, 2)

    def test_tampered_baseline_is_rejected(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes() + b"PASS\textra.json\n"
        report = _report_from_baseline(
            (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes(), SMOKE_FLIP
        )
        with self.assertRaisesRegex(LQ.QualificationError, "unchanged owner-reviewed"):
            LQ.qualify("smoke", baseline, report, 1)

    def test_missing_report_row_is_rejected(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes()
        lines = baseline.decode().splitlines()[1:]
        partial = ("\n".join(f"{s}\t0.01s\t{p}" for s, p in
                             (ln.split("\t") for ln in lines)) + "\n").encode()
        with self.assertRaisesRegex(LQ.QualificationError, "population differs"):
            LQ.qualify("smoke", baseline, partial, 1)

    def test_extra_report_row_is_rejected(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes()
        report = _report_from_baseline(baseline, SMOKE_FLIP) + b"PASS\t0.01s\textra.json\n"
        with self.assertRaisesRegex(LQ.QualificationError, "population differs"):
            LQ.qualify("smoke", baseline, report, 1)

    def test_duplicate_report_row_is_rejected(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes()
        report = _report_from_baseline(baseline, SMOKE_FLIP)
        doubled = report + report.splitlines()[0] + b"\n"
        with self.assertRaisesRegex(LQ.QualificationError, "duplicate"):
            LQ.qualify("smoke", baseline, doubled, 1)

    def test_malformed_report_row_is_rejected(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes()
        report = _report_from_baseline(baseline, SMOKE_FLIP)
        broken = report.replace(b"\t0.01s\t", b"\t", 1)
        with self.assertRaisesRegex(LQ.QualificationError, "malformed"):
            LQ.qualify("smoke", baseline, broken, 1)

    def test_empty_report_is_rejected(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes()
        with self.assertRaisesRegex(LQ.QualificationError, "empty"):
            LQ.qualify("smoke", baseline, b"", 1)

    def test_bad_status_word_is_rejected(self):
        baseline = (SCRIPTS_DIR / "baseline-smoke.txt").read_bytes()
        report = _report_from_baseline(baseline, SMOKE_FLIP).replace(b"FAIL", b"SKIP", 1)
        with self.assertRaisesRegex(LQ.QualificationError, "malformed"):
            LQ.qualify("smoke", baseline, report, 1)


class ExtractionTests(unittest.TestCase):
    def test_public_fixture_counts_are_one_three_one_one_four(self):
        root = Path(__file__).resolve().parents[2] / "public-legacy-fixtures"
        if not root.is_dir():
            self.skipTest("public fixture export is absent")
        expected = dict(LQ.FIXTURE_CASE_COUNTS)
        total = 0
        for rel, count in LQ.FIXTURE_CASE_COUNTS:
            doc = json.loads((root / rel).read_bytes())
            cases = LQ.extract_prague_cases(rel, doc)
            self.assertEqual(len(cases), count, rel)
            total += len(cases)
        self.assertEqual(total, 10)

    def test_public_extraction_preserves_signed_values(self):
        root = Path(__file__).resolve().parents[2] / "public-legacy-fixtures"
        if not root.is_dir():
            self.skipTest("public fixture export is absent")
        rel = "GeneralStateTests/stCreate2/RevertInCreateInInitCreate2Paris.json"
        doc = json.loads((root / rel).read_bytes())
        (case,) = LQ.extract_prague_cases(rel, doc)
        raw_tx = next(
            c["blocks"][0]["transactions"][0]
            for k, c in doc.items() if "-fork_Prague-" in k
        )
        (tx,) = case.txs
        for key in ("nonce", "gasPrice", "value", "v", "r", "s"):
            legacy_key = {"gas": "gasLimit", "input": "data"}.get(key, key)
            self.assertEqual(tx[key], raw_tx[legacy_key])
        self.assertEqual(tx["input"], raw_tx["data"])
        self.assertEqual(tx["gas"], raw_tx["gasLimit"])
        self.assertEqual(tx["type"], "0x0")
        self.assertEqual(tx["chainId"], "0x1")
        self.assertNotIn("sender", tx)
        self.assertEqual(
            case.env["blockHashes"], {"0x0": case.genesis_hash}
        )

    def test_normalization_spelling_only(self):
        tx = _minimal_prague_case()["blocks"][0]["transactions"][0]
        normalized = LQ.normalize_legacy_tx(dict(tx))
        self.assertEqual(normalized["v"], tx["v"])
        self.assertEqual(normalized["r"], tx["r"])
        self.assertEqual(normalized["s"], tx["s"])
        self.assertIsNone(normalized["to"])
        addressed = dict(tx, to="0x" + "dd" * 20)
        self.assertEqual(
            LQ.normalize_legacy_tx(addressed)["to"], "0x" + "dd" * 20
        )

    def test_extra_tx_field_fails_closed(self):
        tx = dict(_minimal_prague_case()["blocks"][0]["transactions"][0])
        tx["yParity"] = "0x0"
        with self.assertRaisesRegex(LQ.QualificationError, "schema mismatch"):
            LQ.normalize_legacy_tx(tx)

    def test_missing_tx_field_fails_closed(self):
        tx = dict(_minimal_prague_case()["blocks"][0]["transactions"][0])
        del tx["sender"]
        with self.assertRaisesRegex(LQ.QualificationError, "schema mismatch"):
            LQ.normalize_legacy_tx(tx)

    def test_two_blocks_rejected(self):
        doc = {"k-fork_Prague-d0g0v0": _minimal_prague_case()}
        doc["k-fork_Prague-d0g0v0"]["blocks"].append(
            doc["k-fork_Prague-d0g0v0"]["blocks"][0]
        )
        with self.assertRaisesRegex(LQ.QualificationError, "exactly one block"):
            LQ.extract_prague_cases("f.json", doc)

    def test_nonempty_uncles_rejected(self):
        case = _minimal_prague_case()
        case["blocks"][0]["uncleHeaders"] = [{"hash": "0x01"}]
        with self.assertRaisesRegex(LQ.QualificationError, "uncles"):
            LQ.extract_prague_cases("f.json", {"k-fork_Prague-d0g0v0": case})

    def test_nonempty_withdrawals_rejected(self):
        case = _minimal_prague_case()
        case["blocks"][0]["withdrawals"] = [{"index": "0x0"}]
        with self.assertRaisesRegex(LQ.QualificationError, "withdrawals"):
            LQ.extract_prague_cases("f.json", {"k-fork_Prague-d0g0v0": case})

    def test_wrong_chainid_rejected(self):
        case = _minimal_prague_case(config={"chainid": "0x02"})
        with self.assertRaisesRegex(LQ.QualificationError, "chainid"):
            LQ.extract_prague_cases("f.json", {"k-fork_Prague-d0g0v0": case})

    def test_wrong_block_number_rejected(self):
        case = _minimal_prague_case()
        case["blocks"][0]["blockHeader"]["number"] = "0x02"
        with self.assertRaisesRegex(LQ.QualificationError, "block number"):
            LQ.extract_prague_cases("f.json", {"k-fork_Prague-d0g0v0": case})

    def test_two_transactions_rejected(self):
        case = _minimal_prague_case()
        case["blocks"][0]["transactions"].append(
            case["blocks"][0]["transactions"][0]
        )
        with self.assertRaisesRegex(LQ.QualificationError, "one legacy"):
            LQ.extract_prague_cases("f.json", {"k-fork_Prague-d0g0v0": case})

    def test_case_count_enforced(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "BlockchainTests"
            (root / "GeneralStateTests" / "stCreate2").mkdir(parents=True)
            for rel, _ in LQ.FIXTURE_CASE_COUNTS:
                (root / rel).parent.mkdir(parents=True, exist_ok=True)
                (root / rel).write_text(
                    json.dumps({"k-fork_Prague-d0g0v0": _minimal_prague_case()})
                )
            with self.assertRaisesRegex(LQ.QualificationError, "expected 3"):
                LQ.collect_prague_cases(root)


def _stub_outputs(out_dir: Path, gas_used: str, marker: str = "x") -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "result.json").write_text(
        json.dumps({"stateRoot": "0x" + marker * 64, "gasUsed": gas_used})
    )
    (out_dir / "alloc.json").write_text(json.dumps({"0x01": {"balance": marker}}))
    (out_dir / "body.json").write_text(json.dumps({"hash": marker}))


class TargetResolutionTests(unittest.TestCase):
    def test_resolution_reuses_gen_module_without_generation(self):
        """Target resolution is fully stubbed: no checkout, git, or network."""

        class StubGen:
            def target_paths(self):
                return (Path("t8n"), Path("python"), "abc123")

        with mock.patch.object(
            LQ, "load_gen_goldens_module", return_value=StubGen()
        ) as loader:
            self.assertEqual(
                LQ.resolve_conformance_target(),
                (Path("t8n"), Path("python"), "abc123"),
            )
        loader.assert_called_once_with()

    def test_manifest_loads_from_canonical_sources(self):
        manifest = LQ.load_manifest()
        self.assertEqual(
            manifest["conformance_target"]["default_env_var"], "JAUNE_T8N_TARGET"
        )


class ComparisonTests(unittest.TestCase):
    def test_identical_outputs_compare_equal(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _stub_outputs(root / "a", "0x01")
            _stub_outputs(root / "b", "0x01")
            digests = LQ.compare_case_outputs("k", root / "a", root / "b")
            self.assertEqual(len(digests), 6)

    def test_mismatched_alloc_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _stub_outputs(root / "a", "0x01")
            _stub_outputs(root / "b", "0x01", marker="y")
            with self.assertRaisesRegex(LQ.QualificationError, "differs"):
                LQ.compare_case_outputs("k", root / "a", root / "b")

    def test_partial_output_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _stub_outputs(root / "a", "0x01")
            _stub_outputs(root / "b", "0x01")
            (root / "b" / "body.json").unlink()
            with self.assertRaisesRegex(LQ.QualificationError, "cannot read"):
                LQ.compare_case_outputs("k", root / "a", root / "b")

    def test_nonzero_tool_exit_fails_replay(self):
        def failing(argv):
            return LQ.ToolRun(argv=argv, exit=1, stdout="", stderr="boom")

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            inputs = LQ.CaseInputs(
                fixture_rel="f",
                case_key="k",
                alloc={},
                env={},
                txs=[],
                frozen_gas_used="0x00",
                genesis_hash="0x00",
            )
            work = root / "w"
            LQ.write_shared_inputs(inputs, work)
            with self.assertRaisesRegex(LQ.QualificationError, "exited 1"):
                LQ.run_t8n(Path("jaune"), "k", work, root / "o", runner=failing)

    def test_successful_tool_with_missing_outputs_fails_with_retained_logs(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            work = root / "w"
            work.mkdir()
            for name in LQ.INPUT_FILES:
                (work / name).write_text("{}")
            def incomplete(argv):
                return LQ.ToolRun(argv=argv, exit=0, stdout="partial", stderr="notice")
            with self.assertRaisesRegex(LQ.QualificationError, "k: jaune wrote no"):
                LQ.run_t8n(Path("jaune"), "k", work, root / "o", runner=incomplete)
            self.assertEqual((root / "o" / "stdout.log").read_text(), "partial")
            self.assertEqual((root / "o" / "stderr.log").read_text(), "notice")
            self.assertEqual(json.loads((root / "o" / "command.json").read_text())["exit"], 0)

    def test_missing_shared_inputs_are_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            work = root / "w"
            work.mkdir()
            with self.assertRaisesRegex(LQ.QualificationError, "shared inputs missing"):
                LQ.run_t8n(Path("jaune"), "k", work, root / "o")

    def test_stale_output_dir_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "o").mkdir()
            with self.assertRaisesRegex(LQ.QualificationError, "already exists"):
                LQ.require_fresh_dir(root / "o")

    def test_replay_uses_one_shared_triple_and_compares_whole(self):
        seen_inputs: list[tuple[str, str, str]] = []

        def canned(argv):
            mapping = dict(a.split("=", 1) for a in argv if "=" in a)
            seen_inputs.append(
                (mapping["--input.alloc"], mapping["--input.env"], mapping["--input.txs"])
            )
            out = Path(mapping["--output.basedir"])
            _stub_outputs(out, "0x02")
            return LQ.ToolRun(argv=argv, exit=0, stdout="ok", stderr="")

        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            inputs = LQ.CaseInputs(
                fixture_rel="f",
                case_key="k",
                alloc={"0x01": {}},
                env={"a": "b"},
                txs=[{"type": "0x0"}],
                frozen_gas_used="0x01",
                genesis_hash="0x00",
            )
            evidence = LQ.replay_case(
                inputs, "deadbeef", Path("jaune"), Path("ref"), root / "case",
                runner=canned,
            )
            self.assertEqual(evidence.live_gas_used, "0x02")
            self.assertEqual(evidence.jaune_exit, 0)
            # Both tools read the same triple written once.
            self.assertEqual(len(seen_inputs), 2)
            self.assertEqual(seen_inputs[0], seen_inputs[1])
            # Evidence hashes are the actual shared files, with full streams.
            work = root / "case" / "work"
            for name in ("alloc.json", "env.json", "txs.json"):
                self.assertEqual(
                    evidence.input_files[name],
                    LQ.sha256_file(work / name),
                )
            self.assertEqual(evidence.jaune_stdout, "ok")
            self.assertEqual(evidence.ref_stderr, "")
            with self.assertRaisesRegex(LQ.QualificationError, "not fresh"):
                LQ.replay_case(
                    inputs, "deadbeef", Path("jaune"), Path("ref"), root / "case",
                    runner=canned,
                )

    def test_vacuous_gas_replay_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _stub_outputs(root, "0x01")
            with self.assertRaisesRegex(LQ.QualificationError, "vacuous"):
                LQ.assert_gas_divergence("k", root, "0x01")

    def test_equivalent_hex_gas_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            ref = Path(tmp)
            (ref / "result.json").write_text('{"gasUsed": "0x01"}')
            with self.assertRaises(LQ.QualificationError):
                LQ.assert_gas_divergence("case", ref, "0x1")

    def test_live_gas_divergence_returns_live_value(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            _stub_outputs(root, "0x02")
            self.assertEqual(LQ.assert_gas_divergence("k", root, "0x01"), "0x02")

    def test_missing_gas_used_fails_closed(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            root.mkdir(exist_ok=True)
            (root / "result.json").write_text(json.dumps({"stateRoot": "0x00"}))
            with self.assertRaisesRegex(LQ.QualificationError, "no top-level gasUsed"):
                LQ.assert_gas_divergence("k", root, "0x01")

    def test_nested_gas_used_is_not_inferred(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            root.mkdir(exist_ok=True)
            (root / "result.json").write_text(
                json.dumps({"stateRoot": "0x00", "receipts": [{"gasUsed": "0x02"}]})
            )
            with self.assertRaisesRegex(LQ.QualificationError, "no top-level gasUsed"):
                LQ.assert_gas_divergence("k", root, "0x01")


if __name__ == "__main__":
    unittest.main()
