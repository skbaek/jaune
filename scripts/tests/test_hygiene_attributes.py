"""Exercise the real text gate on isolated source trees; never invoke Lean."""
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest


GATE = Path(__file__).resolve().parents[1] / 'check-hygiene.sh'


class HygieneAttributes(unittest.TestCase):
    def setUp(self):
        self.scratch = tempfile.TemporaryDirectory(prefix='jaune-hygiene-')
        self.addCleanup(self.scratch.cleanup)
        self.root = Path(self.scratch.name)
        for name in ('Jaune', 'Examples', 'scripts/consumer'):
            (self.root / name).mkdir(parents=True)
        for name in ('Jaune.lean', 'Examples.lean', 'MemoryProbe.lean',
                     'scripts/consumer/Consumer.lean'):
            (self.root / name).write_text('')
        shutil.copyfile(GATE, self.root / 'scripts/check-hygiene.sh')

    def run_gate(self, text, allow=''):
        (self.root / 'Jaune/Subject.lean').write_text(text + '\n')
        (self.root / 'scripts/hygiene-allow.txt').write_text(allow)
        return subprocess.run(['bash', 'scripts/check-hygiene.sh'],
                              cwd=self.root, capture_output=True, text=True)

    def test_direct_attribute_commands_are_visible(self):
        for text in ('attribute [csimp] replacement',
                     '  attribute [local csimp] replacement',
                     'attribute [scoped csimp] replacement',
                     'attribute [simp, csimp] replacement',
                     'attribute [extern "foreign_body"] target',
                     'attribute [implemented_by replacement] target'):
            with self.subTest(text=text):
                result = self.run_gate(text)
                self.assertEqual(result.returncode, 1, result.stdout + result.stderr)
                self.assertIn('Jaune/Subject.lean', result.stdout)
                self.assertIn('REGRESSION', result.stdout)

    def test_declaration_attributes_remain_visible(self):
        for text in ('@[csimp] theorem replacement := value',
                     '@[extern "foreign_body"] def target := value',
                     '@[implemented_by replacement] def target := value'):
            with self.subTest(text=text):
                self.assertEqual(self.run_gate(text).returncode, 1)

    def test_prose_and_unrelated_attributes_are_not_commands(self):
        result = self.run_gate('\n'.join((
            '-- attribute [csimp] is discussed here',
            'def message := "attribute [implemented_by replacement] target"',
            'attribute [simp] ordinary',
            'def csimp_helper := 0',
            '@[inline] def ordinary := 0')))
        self.assertEqual(result.returncode, 0, result.stdout + result.stderr)

    def test_allowlist_still_binds_exact_source_and_path(self):
        text = 'attribute [csimp] replacement'
        allowed = 'Jaune/Subject.lean ' + text + '\n'
        self.assertEqual(self.run_gate(text, allowed).returncode, 0)
        self.assertEqual(self.run_gate(text + ' another', allowed).returncode, 1)
        self.assertEqual(self.run_gate(text, 'Examples/Subject.lean ' + text + '\n').returncode, 1)


if __name__ == '__main__':
    unittest.main()
