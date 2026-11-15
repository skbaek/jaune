import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest

ROOT = Path(__file__).parents[2]
SCRIPT = ROOT / "scripts" / "check-layering.py"
SPEC = importlib.util.spec_from_file_location("check_layering", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)

LAKEFILE = """import Lake
open Lake DSL
package «t»
@[default_target]
lean_lib «Jaune» where
@[default_target]
lean_lib «JauneChecks» where
@[default_target]
lean_exe «t» where
  root := `Main
"""

FILES = {
    "Jaune.lean": "import Jaune.Spec\nimport Jaune.Proof\n\nnamespace Jaune\n\nend Jaune\n",
    "JauneChecks.lean": "import Jaune.Check.Spec\n",
    "Main.lean": "import Jaune.Adapter\ndef main : IO Unit := pure ()\n",
    "Jaune/Spec.lean": "import Jaune.Impl.Cached\nnamespace Jaune\ndef exec : Nat := 1\nend Jaune\n",
    "Jaune/Proof.lean": "import Jaune.Spec\ntheorem t : True := trivial\n",
    "Jaune/Impl/Cached.lean": "import Jaune.Base\ndef cached : Nat := 1\n",
    "Jaune/Base.lean": "def base : Nat := 0\n",
    "Jaune/Adapter.lean": "import Jaune.Spec\ndef run : Nat := 2\n",
    "Jaune/Check/Spec.lean": "import Jaune.Spec\n#guard Jaune.exec = 1\n",
}
CLASSES = {
    "Jaune.Spec": "specification",
    "Jaune.Base": "specification",
    "Jaune.Proof": "proof",
    "Jaune.Impl.Cached": "implementation",
    "Jaune.Adapter": "adapter",
    "Jaune.Check.Spec": "check",
    "Main": "adapter",
}
DATA = {
    "umbrellas": ["Jaune", "JauneChecks"],
    "modules": CLASSES,
    "implementation_imports": [{"importer": "Jaune.Spec", "imported": "Jaune.Impl.Cached"}],
    "fixture_vocabulary_residue": {"evm_halt_kinds": [], "called_by_specification": []},
}


class LayeringTests(unittest.TestCase):
    """The layering check on synthetic trees, each defect planted alone."""

    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.root)
        (self.root / "scripts").mkdir()
        (self.root / "lakefile.lean").write_text(LAKEFILE, encoding="utf-8")
        for name, text in FILES.items():
            self.write(name, text)
        self.data = json.loads(json.dumps(DATA))
        self.save()

    def write(self, name, text):
        path = self.root / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text, encoding="utf-8")

    def save(self):
        (self.root / "scripts" / "layering.json").write_text(
            json.dumps(self.data), encoding="utf-8")

    def problems(self):
        return MODULE.check(self.root)[0]

    def assertProblem(self, fragment):
        found = self.problems()
        self.assertTrue(any(fragment in p for p in found), found)

    def test_green_tree_passes(self):
        self.assertEqual(self.problems(), [])

    def test_guard_in_specification_module_fails(self):
        self.write("Jaune/Base.lean", "def base : Nat := 0\n#guard base = 0\n")
        self.assertProblem("Jaune.Base:2: #guard in a specification module")

    def test_example_and_eval_in_specification_module_fail(self):
        self.write("Jaune/Base.lean", "def base : Nat := 0\nexample : base = 0 := rfl\n#eval base\n")
        self.assertProblem("example in a specification module")
        self.assertProblem("#eval in a specification module")

    def test_guard_in_a_comment_is_ignored(self):
        self.write("Jaune/Base.lean", "def base : Nat := 0\n-- #guard base = 0\n/- #guard base = 0 -/\n")
        self.assertEqual(self.problems(), [])

    def test_guard_in_a_check_module_passes(self):
        self.assertEqual(self.problems(), [])

    def test_test_helper_in_specification_module_fails(self):
        self.write("Jaune/Base.lean", "namespace Jaune\nprivate def guardAdr : Nat := 1\nend Jaune\n")
        self.assertProblem("test helper in a specification module: guardAdr")

    def test_fixture_helper_names_fail(self):
        self.write("Jaune/Base.lean", "def fixtureTestTx : Nat := 1\ndef totalGuardCode : Nat := 1\n")
        self.assertProblem("fixtureTestTx")
        self.assertProblem("totalGuardCode")

    def test_ordinary_names_with_guard_inside_a_word_pass(self):
        self.write("Jaune/Base.lean", "theorem of_guard_eq_some : True := trivial\ndef IO.guard : Nat := 1\n")
        self.assertEqual(self.problems(), [])

    def test_vocabulary_outside_the_residue_fails_and_listed_passes(self):
        self.write("Jaune/Base.lean", "def nonceTag : String := \"X\"\ndef Foo.render : String := \"\"\n")
        self.assertProblem("fixture vocabulary not in fixture_vocabulary_residue: nonceTag")
        self.assertProblem("Foo.render")
        self.data["fixture_vocabulary_residue"]["called_by_specification"] = ["nonceTag", "Foo.render"]
        self.save()
        self.assertEqual(self.problems(), [])

    def test_second_import_of_implementation_module_fails(self):
        self.write("Jaune/Base.lean", "import Jaune.Impl.Cached\ndef base : Nat := 0\n")
        self.assertProblem("Jaune.Base: specification module imports implementation module")

    def test_registered_import_must_be_present(self):
        self.write("Jaune/Spec.lean", "namespace Jaune\ndef exec : Nat := 1\nend Jaune\n")
        self.assertProblem("registered implementation import absent: Jaune.Spec -> Jaune.Impl.Cached")

    def test_wrong_way_imports_fail(self):
        self.write("Jaune/Proof.lean", "import Jaune.Adapter\ntheorem t : True := trivial\n")
        self.assertProblem("Jaune.Proof (proof) imports Jaune.Adapter (adapter)")
        self.write("Jaune/Proof.lean", "import Jaune.Spec\ntheorem t : True := trivial\n")
        self.write("Jaune/Base.lean", "import Jaune.Proof\ndef base : Nat := 0\n")
        self.assertProblem("Jaune.Base (specification) imports Jaune.Proof (proof)")

    def test_unreached_check_module_fails(self):
        self.write("JauneChecks.lean", "-- nothing\n")
        self.assertProblem("Jaune.Check.Spec (check) is not reached by a default build target")

    def test_unclassified_and_stale_modules_fail(self):
        self.write("Jaune/Extra.lean", "def extra : Nat := 1\n")
        self.assertProblem("unclassified module: Jaune.Extra")
        (self.root / "Jaune" / "Extra.lean").unlink()
        self.data["modules"]["Jaune.Gone"] = "check"
        self.save()
        self.assertProblem("classified module has no source file: Jaune.Gone")

    def test_unknown_class_fails(self):
        self.data["modules"]["Jaune.Base"] = "spec"
        self.save()
        self.assertProblem("unknown class")

    def test_umbrella_root_must_only_import(self):
        self.write("Jaune.lean", "import Jaune.Spec\nimport Jaune.Proof\ndef x : Nat := 1\n")
        self.assertProblem("umbrella root declares something")

    def test_bridge_class_is_accepted_and_ordered(self):
        self.write("Jaune/Bridge.lean", "import Jaune.Spec\ntheorem b : True := trivial\n")
        self.data["modules"]["Jaune.Bridge"] = "bridge"
        self.save()
        self.assertEqual(self.problems(), [])
        self.write("Jaune/Base.lean", "import Jaune.Bridge\ndef base : Nat := 0\n")
        self.assertProblem("Jaune.Base (specification) imports Jaune.Bridge (bridge)")

    def test_tracked_data_and_tree_pass_the_classification_rules(self):
        data = json.loads((ROOT / "scripts" / "layering.json").read_text(encoding="utf-8"))
        self.assertEqual(set(data["modules"].values()) - set(MODULE.CLASSES), set())


if __name__ == "__main__":
    unittest.main()
