"""Synthetic reference-admission controls; never download or import EELS."""
from __future__ import annotations

import hashlib
import io
import json
import subprocess
import sys
import tempfile
import unittest
from contextlib import contextmanager, redirect_stderr
from types import SimpleNamespace
from unittest import mock
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import bootstrap_conformance
from conformance_reference import CLI_PATH, WRAPPER_PATHS, ReferenceError, check_reference_records, verify_reference


def blob(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()


class ReferenceAdmissionTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name) / "target"
        self.root.mkdir()
        self.scripts = Path(self.temp.name) / "scripts"
        self.scripts.mkdir()
        self.git("init", "-q")
        self.git("config", "user.name", "Synthetic test")
        self.git("config", "user.email", "synthetic@example.invalid")
        self.git("config", "commit.gpgsign", "false")
        self.write(CLI_PATH, b"base CLI\n")
        self.write("src/ethereum/fork.py", b"unchanged specification\n")
        self.commit()
        base = self.git("rev-parse", "HEAD").strip()
        self.adapted = b"exact reviewed CLI adapter\n"
        patch = self.scripts / "adapter.patch"
        patch.write_bytes(b"synthetic patch identity\n")
        self.entry = {"commit": base, "cli_adapter": {
            "id": "ommer-reward-summary-cli-v1", "path": CLI_PATH,
            "base_git_blob": blob(b"base CLI\n"), "adapted_git_blob": blob(self.adapted),
            "adapted_sha256": hashlib.sha256(self.adapted).hexdigest(), "mode": "100644",
            "patch_subpath": "adapter.patch", "patch_sha256": hashlib.sha256(patch.read_bytes()).hexdigest(),
        }}

    def git(self, *args):
        return subprocess.run(["git", "-C", str(self.root), *args], check=True, capture_output=True, text=True).stdout

    def write(self, relative, content):
        p = self.root / relative
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_bytes(content)

    def commit(self):
        self.git("add", ".")
        self.git("commit", "-q", "-m", "synthetic")

    def verify(self):
        return verify_reference(self.root, self.entry, self.scripts)

    @contextmanager
    def refusal(self, pattern, label):
        with self.assertRaisesRegex(ReferenceError, pattern) as rejected:
            yield
        print("SYNTHETIC_CONTROL " + json.dumps({"label": label,
              "exception": type(rejected.exception).__name__,
              "message": str(rejected.exception)}, sort_keys=True))

    def tree_identity(self):
        """Exact tracked source tree, independent of restoration commit metadata."""
        return self.git("rev-parse", "HEAD^{tree}").strip()

    def cli_verdict(self, expected, label):
        manifest = self.scripts / "sources.json"
        manifest.write_text(json.dumps({"conformance_target": self.entry}))
        command = [sys.executable, str(Path(__file__).resolve().parents[1] / "conformance_reference.py"),
                   "--manifest", str(manifest), "--root", str(self.root)]
        run = subprocess.run(command, capture_output=True, text=True)
        print("SYNTHETIC_CONTROL " + json.dumps({"label": label, "command": command,
              "exit": run.returncode, "stdout": run.stdout, "stderr": run.stderr}, sort_keys=True))
        self.assertEqual(run.returncode, expected)
        return run

    def install_adapter(self):
        self.write(CLI_PATH, self.adapted)
        self.commit()
        return self.verify()

    def test_base_and_existing_four_wrapper_paths_still_pass(self):
        self.assertEqual(self.verify()["kind"], "base")
        self.assertEqual(len(WRAPPER_PATHS), 4)
        for relative in WRAPPER_PATHS:
            self.write(relative, b"existing wrapper allowance\n")
        self.commit()
        self.assertEqual(self.verify()["kind"], "jaune-wrapper")

    def test_exact_adapter_passes_but_one_changed_byte_does_not(self):
        self.assertEqual(self.install_adapter()["kind"], "cli-adapter")
        self.cli_verdict(0, "exact-adapter-admitted")
        self.write(CLI_PATH, self.adapted + b"changed\n")
        self.commit()
        run = self.cli_verdict(1, "changed-cli-byte-refused")
        self.assertIn("mode/blob", run.stderr)

    def test_other_specification_path_and_adapter_plus_wrapper_are_refused(self):
        self.install_adapter()
        green_tree = self.tree_identity()
        self.write("src/ethereum/fork.py", b"changed semantics\n")
        self.commit()
        with self.refusal("unregistered reference changes", "extra-specification-path-refused"):
            self.verify()
        self.git("revert", "--no-edit", "HEAD")
        self.assertEqual(self.tree_identity(), green_tree)
        self.write(next(iter(WRAPPER_PATHS)), b"combined wrapper\n")
        self.commit()
        with self.refusal("unregistered reference changes", "adapter-plus-wrapper-refused"):
            self.verify()

    def test_dirty_checkout_patch_digest_and_wrong_mode_are_refused(self):
        self.install_adapter()
        self.write(CLI_PATH, b"uncommitted\n")
        with self.refusal("uncommitted", "dirty-checkout-refused"):
            self.verify()
        self.write(CLI_PATH, self.adapted)
        self.assertEqual((self.root / CLI_PATH).read_bytes(), self.adapted)
        patch = self.scripts / "adapter.patch"
        original = patch.read_bytes()
        patch.write_bytes(original + b"changed\n")
        with self.refusal("patch digest", "changed-patch-digest-refused"):
            self.verify()
        patch.write_bytes(original)
        self.assertEqual(patch.read_bytes(), original)
        self.git("update-index", "--chmod=+x", CLI_PATH)
        (self.root / CLI_PATH).chmod(0o755)
        self.git("commit", "-q", "-m", "wrong file mode")
        with self.refusal("mode/blob", "wrong-cli-mode-refused"):
            self.verify()

    def test_adapter_provenance_cannot_be_dropped_or_replaced_by_base(self):
        identity = self.install_adapter()
        cases = Path(self.temp.name) / "cases"
        for name, ommers in [("old", []), ("new", [{"delta": "0x1", "address": "0x01"}])]:
            (cases / name).mkdir(parents=True)
            (cases / name / "env.json").write_text(json.dumps({"ommers": ommers}))
        old_entry = {"expected/result.json": "a" * 64}
        provenance = {"cases": {"old": old_entry, "new": {}}, "reference_identities": {"new": identity}}
        check_reference_records(provenance, self.entry, self.scripts, cases)
        green_provenance = json.dumps(provenance, sort_keys=True)
        self.assertEqual(provenance["cases"]["old"], old_entry)
        del provenance["reference_identities"]["new"]
        with self.refusal("require recorded adapter", "dropped-adapter-provenance-refused"):
            check_reference_records(provenance, self.entry, self.scripts, cases)
        provenance["reference_identities"]["new"] = {
            "semantic_base": self.entry["commit"], "checkout_head": self.entry["commit"], "kind": "base"}
        with self.refusal("require CLI adapter", "base-relabelled-adapter-provenance-refused"):
            check_reference_records(provenance, self.entry, self.scripts, cases)
        provenance["reference_identities"]["new"] = identity
        self.assertEqual(json.dumps(provenance, sort_keys=True), green_provenance)


    def test_bootstrap_refuses_existing_mismatch_without_writing_or_network(self):
        self.install_adapter()
        self.write(CLI_PATH, b"existing mismatching contents\n")
        self.entry.update({"repo_url": "https://example.invalid/never-clone.git",
                           "default_env_var": "SYNTHETIC_REFERENCE_ONLY",
                           "default_subpath_from_home": "unused-synthetic-reference"})
        manifest = self.scripts / "sources.json"
        manifest.write_text(json.dumps({"conformance_target": self.entry}))
        # Include Git metadata as well as source bytes/modes in the snapshot.
        def snapshot():
            return {str(p.relative_to(self.root)): (p.stat().st_mode, p.read_bytes())
                    for p in self.root.rglob("*") if p.is_file()}
        baseline = snapshot()
        stderr = io.StringIO()
        forbidden_provision = mock.Mock(side_effect=AssertionError("bootstrap provisioning/network was attempted"))
        proxy = SimpleNamespace(run=forbidden_provision, CalledProcessError=subprocess.CalledProcessError)
        argv = ["bootstrap_conformance.py", "--manifest", str(manifest),
                "--root", str(self.root), "--with-cli-adapter"]
        # Only the bootstrap's direct provisioning subprocess is blocked.
        # The separate read-only verifier still uses local Git normally.
        with mock.patch.object(bootstrap_conformance, "subprocess", proxy), \
             mock.patch.object(sys, "argv", argv), redirect_stderr(stderr):
            with self.assertRaises(SystemExit) as stopped:
                bootstrap_conformance.main()
        self.assertEqual(stopped.exception.code, 1)
        self.assertIn("uncommitted changes", stderr.getvalue())
        forbidden_provision.assert_not_called()
        self.assertEqual(snapshot(), baseline)
        print("SYNTHETIC_CONTROL " + json.dumps({"label": "bootstrap-existing-mismatch-refused",
              "argv": argv, "exit": stopped.exception.code, "stderr": stderr.getvalue(),
              "destination_bytes_and_modes": "identical", "provision_calls": 0}, sort_keys=True))

if __name__ == "__main__":
    unittest.main()
