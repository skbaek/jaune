import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).parents[2]
SPEC = importlib.util.spec_from_file_location('naming_apply', ROOT / 'scripts/apply-naming-map.py')
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)


def entry(old='Pilot.Tx.gas', new='Pilot.Tx.gasLimit'):
    return dict(old=old, new=new, kind='field', layer='execution', rule='2',
                source='User decision 8: transaction gasLimit')


def index_for(text, locations):
    refs = {}
    for spelling, name, occurrence, definition in locations:
        start = -1
        for _ in range(occurrence + 1):
            start = text.index(spelling, start + 1)
        line = text.count('\n', 0, start)
        bol = text.rfind('\n', 0, start) + 1
        col = len(text[bol:start].encode('utf-16-le')) // 2
        width = len(spelling.encode('utf-16-le')) // 2
        loc = [line, col, line, col + width]
        key = json.dumps({'c': {'m': 'Pilot', 'n': name}})
        ref = refs.setdefault(key, {'definition': None, 'usages': []})
        if definition:
            ref['definition'] = loc
        else:
            ref['usages'].append(loc)
    return dict(version=5, module='Pilot', references=refs, decls={}, directImports=[])


class NamingApplyTests(unittest.TestCase):
    def test_shared_field_with_projection_literals_updates_and_simp(self):
        text = ('structure Tx where\n  gas : Nat\nstructure Msg where\n  gas : Nat\n'
                'def a (t : Tx) := t.gas\ndef b (m : Msg) := m.gas\n'
                'def c : Tx := { gas := 7 }\ndef d (t : Tx) := { t with gas := 8 }\n'
                'example : (c).gas = 7 := by simp [c, Tx.gas]\n')
        names = ['Pilot.Tx.gas', 'Pilot.Msg.gas', 'Pilot.Tx.gas', 'Pilot.Msg.gas',
                 'Pilot.Tx.gas', 'Pilot.Tx.gas', 'Pilot.Tx.gas', 'Pilot.Tx.gas']
        index = index_for(text, [('gas', n, i, i < 2) for i, n in enumerate(names)])
        edits, problems = M.plan_file(text, index, [entry()])
        self.assertEqual(problems, [])
        self.assertEqual(len(edits), 6)
        for edit in reversed(edits):
            text = text[:edit['start']] + edit['new'] + text[edit['end']:]
        self.assertIn('structure Msg where\n  gas : Nat', text)
        self.assertIn('m.gas', text)
        self.assertIn('with gasLimit := 8', text)
        self.assertIn('simp [c, Tx.gasLimit]', text)

    def test_dot_constructor_reference(self):
        text = 'def f := .gas\n'
        index = index_for(text, [('.gas', 'Pilot.Op.gas', 0, False)])
        edits, problems = M.plan_file(text, index, [entry('Pilot.Op.gas', 'Pilot.Op.gasOp')])
        self.assertEqual(problems, [])
        self.assertEqual(edits[0]['new'], '.gasOp')

    def test_unresolved_use_is_reported(self):
        text = 'def a (x : Tx) := x.gas\n'
        _, problems = M.plan_file(text, index_for(text, []), [entry()])
        self.assertEqual(len(problems), 1)
        self.assertIn('unresolved token', problems[0]['reason'])

    def test_comments_plain_strings_and_interpolations(self):
        text = '-- gas\n/- gas /- gas -/ gas -/\ndef s := "gas"\ndef t := s!"{x.gas}"\n'
        _, problems = M.plan_file(text, index_for(text, []), [entry()])
        self.assertEqual(len(problems), 1)
        self.assertEqual(text[problems[0]['start']:problems[0]['end']], 'gas')

    def test_utf16_and_crlf(self):
        text = 'def s := "😀"; def f (x : Tx) := x.gas\r\n'
        index = index_for(text, [('gas', 'Pilot.Tx.gas', 0, False)])
        edits, problems = M.plan_file(text, index, [entry()])
        self.assertEqual(problems, [])
        self.assertEqual(text[edits[0]['start']:edits[0]['end']], 'gas')
        with self.assertRaisesRegex(ValueError, 'surrogate'):
            M.position('😀', 0, 1)

    def test_stale_reference_does_not_replace_another_word(self):
        index = index_for('def a := gas', [('gas', 'Pilot.Tx.gas', 0, False)])
        _, problems = M.plan_file('def a := fee', index, [entry()])
        self.assertIn('not a suffix', problems[0]['reason'])

    def test_descendant_not_silently_skipped(self):
        text = '#check Tx.gas\n'
        index = index_for(text, [('Tx.gas', 'Pilot.Tx.gas', 0, False)])
        _, problems = M.plan_file(text, index, [entry('Pilot.Tx', 'Pilot.Transaction')])
        self.assertIn('descendant', problems[0]['reason'])

    def test_conflicting_references_refuse(self):
        text = 'gas'
        index = index_for(text, [('gas', 'Pilot.Tx.gas', 0, False),
                                 ('gas', 'Pilot.Msg.gas', 0, False)])
        _, problems = M.plan_file(text, index,
                                 [entry(), entry('Pilot.Msg.gas', 'Pilot.Msg.gasLeft')])
        self.assertIn('conflicting', problems[0]['reason'])

    def test_unknown_format_and_namespace_depth_refuse(self):
        with self.assertRaisesRegex(ValueError, 'format 5'):
            M.plan_file('', {'version': 6}, [])
        with self.assertRaisesRegex(ValueError, 'relocation'):
            M.replacement('gas', 'Pilot.Tx.gas', 'Gas.limit')

    def test_mapped_and_unchanged_overlap_refused(self):
        text = 'gas'
        index = index_for(text, [('gas', 'Pilot.Tx.gas', 0, False),
                                 ('gas', 'Pilot.Msg.gas', 0, False)])
        _, problems = M.plan_file(text, index, [entry()])
        self.assertIn('unchanged compiler reference', problems[0]['reason'])

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.map = self.root / 'map.json'
        self.map.write_text(json.dumps(dict(schema_version=1, retired_tokens=[],
                                           allowed_abbreviations=[], entries=[entry()])))
        self.text = 'def f (x : Tx) := x.gas\n'
        (self.root / 'Pilot.lean').write_text(self.text)
        (self.root / 'Pilot.ilean').write_text(json.dumps(dict(source=self.text, index=index_for(
            self.text, [('gas', 'Pilot.Tx.gas', 0, False)]))))

    def plan(self):
        return M.build_plan(self.root, self.map, [('Pilot.lean', 'Pilot.ilean')])

    def test_apply_and_reapply_refusal(self):
        plan = self.plan()
        self.assertEqual(M.apply_plan(self.root, plan, self.map), 1)
        self.assertIn('x.gasLimit', (self.root / 'Pilot.lean').read_text())
        with self.assertRaises(ValueError):
            M.apply_plan(self.root, plan, self.map)

    def test_plan_tampering_refused(self):
        plan = self.plan()
        plan['files'][0]['edits'][0]['new'] = 'fee'
        with self.assertRaisesRegex(ValueError, 'changed since planning'):
            M.apply_plan(self.root, plan, self.map)
        self.assertEqual((self.root / 'Pilot.lean').read_text(), self.text)

    def test_stale_second_file_leaves_first_untouched(self):
        (self.root / 'Other.lean').write_text(self.text)
        (self.root / 'Other.ilean').write_bytes((self.root / 'Pilot.ilean').read_bytes())
        plan = M.build_plan(self.root, self.map, [('Pilot.lean', 'Pilot.ilean'),
                                                ('Other.lean', 'Other.ilean')])
        (self.root / 'Other.lean').write_text(self.text + '-- changed\n')
        with self.assertRaisesRegex(ValueError, 'source mismatch'):
            M.apply_plan(self.root, plan, self.map)
        self.assertEqual((self.root / 'Pilot.lean').read_text(), self.text)

    def test_changed_map_and_index_refused(self):
        plan = self.plan()
        original = self.map.read_bytes()
        self.map.write_bytes(original + b'\n')
        with self.assertRaisesRegex(ValueError, 'map changed'):
            M.apply_plan(self.root, plan, self.map)
        self.map.write_bytes(original)
        index = self.root / 'Pilot.ilean'
        index.write_bytes(index.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'changed since planning'):
            M.apply_plan(self.root, plan, self.map)

    def test_escape_and_symlink_refused(self):
        with self.assertRaisesRegex(ValueError, 'tree-relative'):
            M.safe_path(self.root, '../outside')
        (self.root / 'Alias.lean').symlink_to(self.root / 'Pilot.lean')
        with self.assertRaisesRegex(ValueError, 'symlink'):
            M.safe_path(self.root, 'Alias.lean')


if __name__ == '__main__':
    unittest.main()
