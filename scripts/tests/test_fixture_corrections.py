"""Bounded package, provenance and real harness routing controls; no native EVM."""
from __future__ import annotations
import copy
import gzip
import hashlib
import io
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tarfile
import tempfile
import unittest

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))
import fixture_corrections as F
import env_doctor
import gen_mainnet_manifest as G

PATCH = (f"diff --git a/{F.SOURCE} b/{F.SOURCE}\nindex 4444444..5555555 100644\n").encode()


def record(label, **facts):
    destination = os.environ.get("JAUNE_CORRECTION_TEST_RECEIPTS")
    if destination:
        with open(destination, "a") as stream:
            stream.write(json.dumps({"control": label, **facts}, sort_keys=True) + "\n")


def fixture(case_key, old, *, ordinary=False, network=F.NETWORK):
    case = {"network": network, "pre": {}, "postState": {}, "genesisRLP": "0xc0",
        "lastblockhash": "0x00", "blocks": [{"rlp": "0xc0", "expectException": old}],
        "config": {"blobSchedule": {fork: {"target": "0x0e", "max": "0x15", "baseFeeUpdateFraction": "0xb24b3f"}
                   for fork in ("Prague", "BPO2", "Amsterdam")}}, "ordinary": ordinary}
    case["_info"] = {"fixture-format": "blockchain_test", "description": "original", "url": "base"}
    rehash(case)
    return {case_key: case}


def rehash(case):
    case["_info"]["hash"] = "0x" + F.digest(json.dumps(F.semantic(case), sort_keys=True, separators=(",", ":")).encode())


class PackageCase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="jaune correction ")
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.repo = self.root / "checkout with spaces"
        scripts = self.repo / "scripts"
        scripts.mkdir(parents=True)
        for path in SCRIPTS.iterdir():
            if path.is_file():
                shutil.copy2(path, scripts / path.name)
        self.sources = json.loads((SCRIPTS / "sources.json").read_text())
        self.fixtures = self.root / "base install/fixtures"
        for directory in self.sources["amsterdam"]["expected_top_level_dirs"]:
            (self.fixtures / directory).mkdir(parents=True)
        (self.fixtures / ".meta").mkdir()
        (self.fixtures / ".meta/index.json").write_text(json.dumps(self.sources["amsterdam"]["metadata_json_expected"]))
        self.members, self.entries = {}, []
        for path, old in sorted(F.DELTAS.items()):
            key = F.CASE_PREFIX + Path(path).stem + "[fork_" + F.NETWORK + "-blockchain_test]"
            original = fixture(key, old)
            corrected = copy.deepcopy(original)
            corrected[key]["blocks"][0]["expectException"] = F.NEW
            corrected[key]["_info"].update(description="corrected", url="local-correction")
            rehash(corrected[key])
            before, after = F.canonical(original), F.canonical(corrected)
            output = self.fixtures / "blockchain_tests" / path
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(before)
            self.members["fixtures/blockchain_tests/" + path] = after
            self.entries.append({"path": path, "network": F.NETWORK, "case": key,
                "original_sha256": F.digest(before), "generated_sha256": F.digest(after),
                "wire_sha256": F.digest(bytes.fromhex("c0")), "old": old, "new": F.NEW,
                "metadata_changed_keys": ["description", "hash", "url"]})
        for path, network in (("for_bpo2toamsterdamattime15k/ordinary space/a.json", F.NETWORK),
                              ("for_amsterdam/amsterdam/a.json", "Amsterdam"),
                              ("for_prague/prague/a.json", "Prague"), ("for_cancun/cancun/a.json", "Cancun")):
            file = self.fixtures / "blockchain_tests" / path
            file.parent.mkdir(parents=True, exist_ok=True)
            file.write_bytes(F.canonical(fixture(network + " ordinary", F.NEW, ordinary=True, network=network)))
        # A tiny pristine base archive, using the same unchanged deep verifier.
        base_members = {p.relative_to(self.fixtures.parent).as_posix(): p.read_bytes()
                        for p in self.fixtures.rglob("*") if p.is_file()}
        base_archive = F.archive_bytes(base_members)
        (self.fixtures.parent / "fixtures.tar.gz").write_bytes(base_archive)
        for lane in ("amsterdam", "current_mainnet"):
            self.sources[lane]["archive_sha256"] = F.digest(base_archive)
            self.sources[lane]["archive_size_bytes"] = len(base_archive)
        self.base = F.base_identity(self.sources["amsterdam"])
        self.receipt = {"kind": "jaune-correction-generation-receipt-v1", "id": F.ID,
            "source": {"base_commit": self.base["release_commit"], "base_tree": "1" * 40,
                "commit": "2" * 40, "tree": "3" * 40, "path": F.SOURCE,
                "before_blob": "4" * 40, "after_blob": "5" * 40, "before_sha256": "6" * 64,
                "after_sha256": "7" * 64, "mode": "100644", "patch_sha256": F.digest(PATCH)},
            "environment": {"uv_lock_sha256": "8" * 64, "python": "3.11.9", "packages": [["test", "1"]], "files": [{"role": "lock", "sha256": "8" * 64, "bytes": 1}]},
            "evidence": {"experiment_manifest_sha256": "9" * 64, "experiment_acceptance_sha256": "a" * 64,
                "accepted_report_sha256": "b" * 64, "packager_sha256": "c" * 64, "verifier_sha256": "d" * 64,
                "artifacts": [{"path": "synthetic.command.json", "sha256": "e" * 64, "bytes": 1}]},
            "commands": [{"record": "synthetic.command.json", "argv": ["synthetic"], "cwd": "<SYNTHETIC>",
                "exit": 0, "started_utc": "synthetic", "timing_scope": "synthetic only",
                "stdout_sha256": "f" * 64, "stderr_sha256": "0" * 64}],
            "formats": {"two_phase": {"blockchain_test": 2, "blockchain_test_engine": 2, "blockchain_test_engine_x": 2},
                "ordinary": {"blockchain_test": 2, "blockchain_test_engine": 2}, "stateful": "not run", "sync": "not run"},
            "limits": ["synthetic harness only"]}
        self.package_dir = scripts / "amsterdam/corrections" / F.ID
        self.package_dir.mkdir(parents=True)
        self.reg = self.write_package()
        self.cache_root = self.root / "cache with spaces"
        self.package = F.verify_package(self.reg, self.package_dir)
        F.verify_base_bindings(self.package, self.sources["amsterdam"], self.fixtures)
        F.install(self.package, self.fixtures, self.cache_root)
        self.activate()

    def write_package(self):
        receipt = F.canonical(self.receipt)
        index = {"kind": F.KIND, "id": F.ID, "base": self.base,
                 "generation_receipt_sha256": F.digest(receipt), "entries": self.entries}
        index_raw = F.canonical(index)
        self.members["correction-index.json"] = index_raw
        archive = F.archive_bytes(self.members)
        reg = {**index, "source_patch_sha256": F.digest(PATCH),
            "archive_sha256": F.digest(archive), "archive_size_bytes": len(archive), "index_sha256": F.digest(index_raw)}
        for name, raw in {"registration.json": F.canonical(reg), "generation-receipt.json": receipt,
                          "source.patch": PATCH, "artifact.tar.gz": archive}.items():
            (self.package_dir / name).write_bytes(raw)
        return reg

    def activate(self):
        self.sources["amsterdam"]["fixture_correction"] = {"id": F.ID,
            "registration": f"scripts/amsterdam/corrections/{F.ID}/registration.json",
            "registration_sha256": F.sha(self.package_dir / "registration.json")}
        (self.repo / "scripts/sources.json").write_text(json.dumps(self.sources))

    def fails(self, label, message, function, *args):
        with self.assertRaisesRegex(F.CorrectionError, message) as caught:
            function(*args)
        record(label, outcome="expected rejection", boundary=str(caught.exception))

    def test_schema_receipt_and_source_boundaries(self):
        pointer = copy.deepcopy(self.sources["amsterdam"]["fixture_correction"])
        for key, value, message in (("id", "unknown", "unknown fixture"),
                                    ("registration_sha256", "0" * 64, "registration hash"),
                                    ("extra", 1, "exact fields")):
            changed = {**pointer, key: value}
            self.fails("pointer-" + key, message, F.load_registration, changed, self.repo)
        self.fails("duplicate-json-key", "duplicate JSON", F.parse, b'{"id":1,"id":2}')
        changed = copy.deepcopy(self.receipt)
        changed["source"]["path"] = "another.py"
        reg = {**self.reg, "generation_receipt_sha256": F.digest(F.canonical(changed))}
        self.fails("extra-source-path", "source contract", F.verify_receipt, F.canonical(changed), reg)
        self.fails("receipt-byte-drift", "receipt hash", F.verify_receipt, F.canonical(changed), self.reg)
        changed = copy.deepcopy(self.receipt)
        changed["source"]["before_blob"] = "9" * 40
        self.receipt = changed
        reg = self.write_package()
        self.fails("source-blob-drift", "patch/blob", F.verify_package, reg, self.package_dir)
        self.receipt["source"]["before_blob"] = "4" * 40
        self.write_package()
        changed = copy.deepcopy(self.receipt)
        changed["environment"]["uv_lock_sha256"] = "pending"
        reg = {**self.reg, "generation_receipt_sha256": F.digest(F.canonical(changed))}
        self.fails("environment-digest", "digest", F.verify_receipt, F.canonical(changed), reg)
        changed_sources = copy.deepcopy(self.sources)
        changed_sources["current_mainnet"]["fixture_correction"] = pointer
        self.fails("wrong-registration-lane", "Amsterdam-only", F.validate_sources, changed_sources, self.repo)

    def test_exact_membership_and_semantic_delta_controls(self):
        for label, entries in (("missing", self.entries[:1]), ("third", self.entries + self.entries[:1]),
                               ("duplicate", [self.entries[0], self.entries[0]])):
            self.fails("entries-" + label, "two|duplicate", F.validate_entries, entries)
        entry = self.entries[0]
        original = (self.fixtures / "blockchain_tests" / entry["path"]).read_bytes()
        good = self.members["fixtures/blockchain_tests/" + entry["path"]]
        for label, mutate, boundary in (
            ("RLP", lambda c: c["blocks"][0].update(rlp="0xc1"), "semantic drift"),
            ("prestate", lambda c: c["pre"].update(changed={}), "semantic drift"),
            ("poststate", lambda c: c["postState"].update(changed={}), "semantic drift"),
            ("expected-name", lambda c: c["blocks"][0].update(expectException=entry["old"]), "expected-name delta"),
            ("metadata-hash", lambda c: c["_info"].update(hash="0x" + "0" * 64), "metadata hash")):
            changed = F.parse(good)
            case = changed[entry["case"]]
            mutate(case)
            if label != "metadata-hash":
                rehash(case)
            raw = F.canonical(changed)
            refreshed = {**entry, "generated_sha256": F.digest(raw)}
            self.fails("fixture-" + label, boundary, F.verify_fixture_delta, original, raw, refreshed)
        self.fails("fixture-stale-filehash", "file hash", F.verify_fixture_delta, original, good + b" ", entry)
        for field, value in (("network", "Amsterdam"), ("case", "different")):
            self.fails("entry-" + field, field, F.validate_entry, {**entry, field: value})
        F.verify_fixture_delta(original, good, entry)
        record("semantic-restoration", original_sha256=F.digest(original), corrected_sha256=F.digest(good), restored_exact=True)

    def altered_archive(self, transform):
        buffer = io.BytesIO()
        with gzip.GzipFile(fileobj=buffer, mode="wb", filename="", mtime=0) as zipped:
            with tarfile.open(fileobj=zipped, mode="w", format=tarfile.USTAR_FORMAT) as archive:
                for name, raw in sorted(self.members.items()):
                    info = tarfile.TarInfo(name)
                    info.size, info.mode = len(raw), 0o644
                    transform(archive, info, raw)
        raw = buffer.getvalue()
        (self.package_dir / "artifact.tar.gz").write_bytes(raw)
        return {**self.reg, "archive_sha256": F.digest(raw), "archive_size_bytes": len(raw)}

    def test_archive_integrity_controls_reach_named_boundary(self):
        green = (self.package_dir / "artifact.tar.gz").read_bytes()
        def add(archive, info, raw):
            archive.addfile(info, io.BytesIO(raw))
        transforms = {
            "missing": lambda a, i, b: add(a, i, b) if i.name != "correction-index.json" else None,
            "duplicate": lambda a, i, b: (add(a, i, b), add(a, i, b)),
            "traversal": lambda a, i, b: (setattr(i, "name", "../escape"), add(a, i, b)),
            "symlink": lambda a, i, b: (setattr(i, "type", tarfile.SYMTYPE), setattr(i, "size", 0), setattr(i, "linkname", "target"), a.addfile(i)),
            "metadata": lambda a, i, b: (setattr(i, "mtime", 1), add(a, i, b)),
            "extra": lambda a, i, b: (add(a, i, b), setattr(i, "name", "extra"), add(a, i, b)),
        }
        for label, transform in transforms.items():
            reg = self.altered_archive(transform)
            self.fails("archive-" + label, "member|unsafe|metadata", F.verify_package, reg, self.package_dir)
            (self.package_dir / "artifact.tar.gz").write_bytes(green)
            self.assertEqual(F.sha(self.package_dir / "artifact.tar.gz"), self.reg["archive_sha256"])
        self.fails("archive-digest", "archive hash", F.verify_package, {**self.reg, "archive_sha256": "0" * 64}, self.package_dir)
        self.fails("index-digest", "index hash", F.verify_package, {**self.reg, "index_sha256": "0" * 64}, self.package_dir)
        # Use GzipFile to retain the canonical outer header, reaching tar checks.
        buffer = io.BytesIO()
        with gzip.GzipFile(fileobj=buffer, mode="wb", filename="", mtime=0) as zipped:
            zipped.write(F.tar_bytes(self.members) + b"hidden trailing content")
        hidden = buffer.getvalue()
        (self.package_dir / "artifact.tar.gz").write_bytes(hidden)
        refreshed = {**self.reg, "archive_sha256": F.digest(hidden), "archive_size_bytes": len(hidden)}
        self.fails("archive-hidden-trailing-content", "trailing correction tar", F.verify_package, refreshed, self.package_dir)
        (self.package_dir / "artifact.tar.gz").write_bytes(green)
        member = "fixtures/blockchain_tests/" + self.entries[0]["path"]
        old = self.members[member]
        self.members[member] = old + b" "
        archive = F.archive_bytes(self.members)
        (self.package_dir / "artifact.tar.gz").write_bytes(archive)
        reg = {**self.reg, "archive_sha256": F.digest(archive), "archive_size_bytes": len(archive)}
        self.fails("archive-fixture-byte-drift", "fixture file hash", F.verify_package, reg, self.package_dir)
        self.members[member] = old
        (self.package_dir / "artifact.tar.gz").write_bytes(green)
        patch = (self.package_dir / "source.patch").read_bytes()
        (self.package_dir / "source.patch").write_bytes(patch + b"x")
        self.fails("source-patch-drift", "source patch hash", F.verify_package, self.reg, self.package_dir)
        (self.package_dir / "source.patch").write_bytes(patch)
        self.assertEqual(F.archive_bytes(self.members), green)
        record("archive-restoration", restored_exact=True, archive_sha256=F.digest(green))

    def test_registered_check_uses_exact_output_and_base_without_source_edit(self):
        from unittest.mock import patch
        spec = importlib.util.spec_from_file_location('test_correction_packager', SCRIPTS / 'gen-amsterdam-fixture-correction.py')
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        output = {p.name: p.read_bytes() for p in self.package_dir.iterdir()}
        args = ['--sources', str(self.repo / 'scripts/sources.json'), '--base-root', str(self.fixtures.parent),
                '--experiment-receipt', str(self.root / 'synthetic-accepted-receipt'), '--output', str(self.package_dir), '--check']
        with patch.object(module, 'package_bytes', return_value=output):
            self.assertEqual(module.main(args), 0)
            wrong = list(args)
            wrong[wrong.index('--output') + 1] = str(self.root / 'unregistered output')
            self.assertEqual(module.main(wrong), 2)
            self.assertEqual(module.main(args[:-1]), 2)
        record('registered-check-interface', registered_exact_output_exit=0,
               wrong_output_exit=2, new_generation_with_active_pointer_exit=2,
               synthetic_producer_mock=True, note='interface-only; actual accepted package registered --check separately recorded')

    def test_cache_and_official_base_remain_separate(self):
        installed = F.verify_installed(self.package, self.fixtures, self.cache_root)
        self.fails("missing-cache", "missing correction setup", F.verify_installed, self.package, self.fixtures, self.root / "absent")
        target = installed / ("fixtures/blockchain_tests/" + self.entries[0]["path"])
        raw = target.read_bytes()
        target.write_bytes(raw + b" ")
        self.fails("occupied-invalid-cache", "installed correction bytes", F.install, self.package, self.fixtures, self.cache_root)
        target.write_bytes(raw)
        target.unlink()
        target.symlink_to(self.fixtures / "blockchain_tests" / self.entries[0]["path"])
        self.fails("cache-link", "linked correction", F.verify_installed, self.package, self.fixtures, self.cache_root)
        target.unlink()
        target.write_bytes(raw)
        linked = self.root / "hardlink"
        os.link(target, linked)
        self.fails("cache-hardlink", "regular unlinked", F.verify_installed, self.package, self.fixtures, self.cache_root)
        linked.unlink()
        base = self.fixtures / "blockchain_tests" / self.entries[0]["path"]
        original = base.read_bytes()
        base.write_bytes(original + b" ")
        with self.env():
            checks = env_doctor.deep_compare_amsterdam(self.sources, self.fixtures.parent, self.repo / "scripts/sources.json")
        failures = [c for c in checks if c.status != env_doctor.STATUS_OK]
        self.assertTrue(any("tree vs archive" in c.name and "changed" in c.detail for c in failures))
        self.assertTrue(any("base original file hash" in c.detail for c in failures))
        record("base-deep-still-checks-original", failures=[c.__dict__ for c in failures])
        base.write_bytes(original)
        with self.env():
            self.assertTrue(all(c.status == env_doctor.STATUS_OK for c in
                env_doctor.deep_compare_amsterdam(self.sources, self.fixtures.parent, self.repo / "scripts/sources.json")))

    def env(self):
        from unittest.mock import patch
        return patch.dict(os.environ, {"JAUNE_FIXTURE_CORRECTION_CACHE": str(self.cache_root)})

    def prepare_harness(self):
        for lane in ("amsterdam", "mainnet", "historical"):
            manifest = G.inventory(self.fixtures, self.sources, G.LANES[lane], self.repo, self.cache_root)
            output = self.repo / "scripts" / lane / "manifests.json"
            G.write_json(output, manifest)
        binary = self.repo / ".lake/build/bin/jaune"
        binary.parent.mkdir(parents=True)
        binary.write_text('''#!/usr/bin/env python3
import json,os,sys
case=next(iter(json.load(open(sys.argv[1])).values()))
ok=case['ordinary'] or case['blocks'][0]['expectException']=='BlockException.INCORRECT_BLOCK_FORMAT'
with open(os.environ['ROUTING_LOG'],'a') as f: f.write(json.dumps({'file':sys.argv[1],'ok':ok})+'\\n')
if not ok: print('CONTENT ASSERTION: old raw expectation dispatched',file=sys.stderr)
sys.exit(0 if ok else 9)
''')
        binary.chmod(0o755)

    def run_harness(self, lane="amsterdam", suite="amsterdam-transitions", jobs=1, extra=()):
        env = dict(os.environ, HOME=str(self.root / "private home"),
                   JAUNE_FIXTURE_CORRECTION_CACHE=str(self.cache_root), ROUTING_LOG=str(self.root / "routing.jsonl"))
        return subprocess.run([str(self.repo / "scripts/check-mainnet.sh"), "--lane", lane, "--suite", suite,
            "--no-build", "--fixtures-root", str(self.fixtures), "--jobs", str(jobs), *extra],
            cwd=self.repo, env=env, text=True, capture_output=True)

    def test_real_harness_routes_both_modes_and_preserves_selection(self):
        self.prepare_harness()
        for jobs in (1, 2):
            result = self.run_harness(jobs=jobs)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            self.assertIn(F.ID, result.stdout)
            receipts = sorted((self.repo / ".lake/fixture-input-receipts").iterdir(), key=lambda p: p.stat().st_mtime_ns)
            receipt = F.read(receipts[-1])
            self.assertEqual(receipt["applied_replacements"], 2)
            self.assertEqual([r["path"] for r in receipt["rows"]], sorted(r["path"] for r in receipt["rows"]))
            for row in receipt["rows"]:
                self.assertEqual(row["source_kind"] == "fixture-correction", row["path"] in F.DELTAS)
                self.assertIn("cache with spaces" if row["path"] in F.DELTAS else "base install", row["physical_path"])
            record("actual-routing-" + str(jobs), exit=result.returncode, stdout=result.stdout, stderr=result.stderr,
                   receipt=receipt)
        for lane, suite in (("mainnet", "smoke"), ("historical", "hist-smoke"), ("amsterdam", "amsterdam-smoke")):
            result = self.run_harness(lane, suite)
            self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
            record("ordinary-route-" + lane, exit=0, stdout=result.stdout, stderr=result.stderr)
        result = self.run_harness(extra=("--start-at", "2"))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("1 skipped by --start-at and NOT verified", result.stdout)
        result = self.run_harness(extra=("--dir", F.PREFIX.rstrip("/")))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        self.assertIn("2/2", result.stdout)

    def test_production_routing_mutant_fails_actual_content_assertion(self):
        self.prepare_harness()
        source = self.repo / "scripts/check-mainnet.sh"
        green = source.read_bytes()
        marker = b'\' "$GUARD" "$BIN" "$FILE" --network "$NETWORK"'
        self.assertEqual(green.count(marker), 1)
        source.write_bytes(green.replace(marker, b'\' "$GUARD" "$BIN" "$FIXTURES_ROOT/blockchain_tests/$REL" --network "$NETWORK"'))
        result = self.run_harness()
        self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
        observed = [json.loads(line) for line in (self.root / "routing.jsonl").read_text().splitlines()]
        self.assertTrue(any(not row["ok"] for row in observed))
        self.assertIn("non-PASS fixture", result.stderr)
        record("production-routing-mutant", exit=1, stdout=result.stdout, stderr=result.stderr,
               stub_content_assertion_failed=True, observed=observed)
        source.write_bytes(green)
        self.assertEqual(source.read_bytes(), green)
        record("production-routing-restored", source_sha256=F.digest(green), restored_exact=True, rerun=False)

    def test_dispatch_receipt_missing_mapping_and_post_run_drift(self):
        self.prepare_harness()
        manifest = F.read(self.repo / "scripts/amsterdam/manifests.json")
        entries = F.suite_entries(manifest, "amsterdam-transitions")
        changed = copy.deepcopy(entries)
        del next(e for e in changed if e["path"] in F.DELTAS)["fixture_correction"]
        self.fails("missing-mapping", "missing/wrong correction mapping", F.resolve_inputs,
            self.sources, "amsterdam", self.repo, self.fixtures, manifest, changed, 1, self.cache_root)
        wrong_lane_manifest = copy.deepcopy(manifest)
        self.fails("wrong-manifest-lane", "manifest correction identity", F.resolve_inputs,
            self.sources, "mainnet", self.repo, self.fixtures, wrong_lane_manifest, entries, 1, self.cache_root)
        result = self.run_harness()
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)
        path = max((self.repo / ".lake/fixture-input-receipts").iterdir(), key=lambda p: p.stat().st_mtime_ns)
        receipt_sha = F.sha(path)
        self.fails("receipt-missing", "missing or linked", F.verify_dispatch, self.root / "missing.json", receipt_sha)
        raw = path.read_bytes()
        path.write_bytes(raw + b" ")
        self.fails("receipt-replaced", "receipt hash", F.verify_dispatch, path, receipt_sha)
        path.write_bytes(raw)
        changed = F.parse(raw)
        changed["rows"][0]["effective_sha256"] = "0" * 64
        changed_raw = F.canonical(changed)
        path.write_bytes(changed_raw)
        with self.env():
            self.fails("receipt-identity-omitted", "post-run dispatch identity", F.verify_dispatch, path, F.digest(changed_raw))
        path.write_bytes(raw)
        row = F.read(path)["rows"][0]
        physical = Path(row["physical_path"])
        content = physical.read_bytes()
        physical.write_bytes(content + b" ")
        with self.env():
            self.fails("post-run-input-drift", "installed correction bytes|content hash", F.verify_dispatch, path, receipt_sha)
        physical.write_bytes(content)
        index = self.fixtures / ".meta/index.json"
        index_raw = index.read_bytes()
        index.write_bytes(index_raw + b" ")
        self.fails("post-run-index-drift", "release index changed", F.verify_dispatch, path, receipt_sha)
        index.write_bytes(index_raw)
        with self.env():
            F.verify_dispatch(path, receipt_sha)
        record("post-input-restored", restored_exact=True)


if __name__ == "__main__":
    unittest.main()
