import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest


ROOT = Path(__file__).parents[2]
SCRIPT = ROOT / "scripts" / "check-assurance-manifest.py"
SPEC = importlib.util.spec_from_file_location("check_assurance_manifest", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)
FILES = ("scripts/assurance-manifest.json", "scripts/ExecutionAxioms.lean",
         "Jaune/SymbolicPush.lean", "Jaune/SymbolicArith.lean")


class AssuranceManifestTests(unittest.TestCase):
    """Each omission the check exists for fails it; the tracked tree passes."""

    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.root)
        for name in FILES:
            (self.root / name).parent.mkdir(parents=True, exist_ok=True)
            shutil.copy(ROOT / name, self.root / name)

    def edit(self, name, old, new):
        path = self.root / name
        text = path.read_text(encoding="utf-8")
        self.assertIn(old, text)
        path.write_text(text.replace(old, new, 1), encoding="utf-8")

    def test_tracked_tree_passes(self):
        rows, rules, modules = MODULE.check(self.root)
        self.assertGreater(rows, 0)
        self.assertEqual(modules, 2)

    def test_deleted_row_fails(self):
        self.edit("scripts/ExecutionAxioms.lean",
                  "#expect_axioms Jaune.SymbolicArith.prepend ", "-- ")
        with self.assertRaisesRegex(ValueError, "without row"):
            MODULE.check(self.root)

    def test_deleted_entry_fails(self):
        path = self.root / "scripts/assurance-manifest.json"
        manifest = json.loads(path.read_text(encoding="utf-8"))
        manifest["entries"] = [e for e in manifest["entries"]
                               if e["declaration"] != "Jaune.Exec.strong_rec"]
        path.write_text(json.dumps(manifest), encoding="utf-8")
        with self.assertRaisesRegex(ValueError, "without manifest entry"):
            MODULE.check(self.root)

    def test_unaudited_rule_fails(self):
        self.edit("Jaune/SymbolicArith.lean", "end Jaune.SymbolicArith",
                  "@[simp] theorem extra : True := trivial\n\nend Jaune.SymbolicArith")
        with self.assertRaisesRegex(ValueError, "Jaune.SymbolicArith.extra"):
            MODULE.check(self.root)


if __name__ == "__main__":
    unittest.main()
