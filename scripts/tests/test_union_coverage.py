import importlib.util
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).parents[2]
SPEC = importlib.util.spec_from_file_location(
    'assurance_union_coverage', ROOT / 'scripts/check-assurance-manifest.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class UnionCoverageTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        (self.root / 'Jaune').mkdir()
        (self.root / 'scripts').mkdir()
        self.write('Jaune.lean', 'import Jaune.Core\n')
        self.write('Jaune/Core.lean', 'import Init\n')
        self.write('Jaune/Trace.lean', 'import Jaune.Core\n')
        self.write('scripts/JauneUnionAxioms.lean',
                   'import AxiomAudit\nimport Jaune\nimport Jaune.Trace\n')

    def write(self, name, text):
        (self.root / name).write_text(text)

    def test_current_tree_is_covered(self):
        self.assertEqual(MODULE.check_union_coverage(ROOT),
                         1 + len(list((ROOT / 'Jaune').rglob('*.lean'))))

    def test_transitive_coverage(self):
        self.assertEqual(MODULE.check_union_coverage(self.root), 3)

    def test_dropped_trace_import_fails(self):
        self.write('scripts/JauneUnionAxioms.lean', 'import Jaune\n')
        with self.assertRaisesRegex(ValueError, 'outside whole-library.*Jaune.Trace'):
            MODULE.check_union_coverage(self.root)

    def test_commented_import_does_not_cover(self):
        self.write('scripts/JauneUnionAxioms.lean',
                   'import Jaune\n/- nested /- comment -/\nimport Jaune.Trace\n-/\n')
        with self.assertRaisesRegex(ValueError, 'outside whole-library.*Jaune.Trace'):
            MODULE.check_union_coverage(self.root)

    def test_new_module_is_detected(self):
        self.write('Jaune/New.lean', 'import Init\n')
        with self.assertRaisesRegex(ValueError, 'outside whole-library.*Jaune.New'):
            MODULE.check_union_coverage(self.root)

    def test_missing_dependency_fails(self):
        self.write('Jaune/Trace.lean', 'import Jaune.Missing\n')
        with self.assertRaisesRegex(ValueError, 'missing local.*Jaune.Missing'):
            MODULE.check_union_coverage(self.root)

    def test_missing_source_tree_fails(self):
        (self.root / 'Jaune.lean').unlink()
        with self.assertRaisesRegex(ValueError, 'missing Jaune source'):
            MODULE.check_union_coverage(self.root)


if __name__ == '__main__':
    unittest.main()
