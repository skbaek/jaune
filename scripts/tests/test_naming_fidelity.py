import importlib.util
from pathlib import Path
import unittest

ROOT = Path(__file__).parents[2]
SPEC = importlib.util.spec_from_file_location('naming_fidelity', ROOT / 'scripts/check-naming-fidelity.py')
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


def ref(name):
    return ['name', name]


def constant(value=1, attrs=None):
    return dict(kernel=dict(type=['const', ref('Nat'), []], universes=0,
                            payload=['definition', value]), attributes=attrs or {})


def snapshot(constants, roots, guards=None, attributes=None):
    return dict(constants=constants, roots=set(roots), guards=guards or [],
                attributes=attributes or [], version='fixture', modules={}, receipts=[])


class NamingFidelityTests(unittest.TestCase):
    def setUp(self):
        self.before = snapshot({'N.old': constant()}, ['N.old'])
        self.after = snapshot({'N.new': constant()}, ['N.new'])
        self.renames = {'N.old': 'N.new'}

    def run_check(self):
        return CHECK.Comparison(self.before, self.after, self.renames).run()

    def test_exact_rename_and_reference_mapping(self):
        self.before['guards'] = [ref('N.old')]
        self.after['guards'] = [ref('N.new')]
        self.assertEqual(self.run_check()['status'], 'OK')

    def test_type_body_and_attribute_changes_fail(self):
        for key in ('type', 'payload'):
            self.after['constants']['N.new']['kernel'][key] = ['changed']
            with self.assertRaisesRegex(CHECK.Mismatch, 'kernel'):
                self.run_check()
            self.after['constants']['N.new'] = constant()
        self.after['constants']['N.new']['attributes'] = {'csimp': True}
        with self.assertRaisesRegex(CHECK.Mismatch, 'attributes'):
            self.run_check()

    def test_authored_set_and_collision_fail(self):
        self.after['roots'].add('N.extra')
        with self.assertRaisesRegex(CHECK.Mismatch, 'authored constant set'):
            self.run_check()
        self.after['roots'].remove('N.extra')
        self.before['roots'].add('N.new')
        with self.assertRaisesRegex(CHECK.Mismatch, 'authored constant set'):
            self.run_check()

    def test_generated_names_do_not_need_map_rows(self):
        self.before['constants']['N.helper_1'] = constant(ref('N.old'))
        self.after['constants']['N.helper_42'] = constant(ref('N.new'))
        self.before['constants']['N.old'] = constant(ref('N.helper_1'))
        self.after['constants']['N.new'] = constant(ref('N.helper_42'))
        self.assertEqual(self.run_check()['generated_constants'], 1)
        self.after['constants']['N.helper_42'] = constant(3)
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()

    def test_generated_correspondence_is_bijective(self):
        self.before['constants'].update(a=constant(), b=constant())
        self.after['constants']['c'] = constant()
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()

    def test_unreferenced_generated_nodes_are_checked(self):
        self.before['constants']['a'] = constant(1)
        self.after['constants']['b'] = constant(2)
        with self.assertRaisesRegex(CHECK.Mismatch, 'generated-constant'):
            self.run_check()

    def test_external_reference_change_fails(self):
        self.before['constants']['N.old'] = constant(ref('External.a'))
        self.after['constants']['N.new'] = constant(ref('External.b'))
        with self.assertRaisesRegex(CHECK.Mismatch, 'reference'):
            self.run_check()

    def test_guards_can_move_but_not_change_or_disappear(self):
        self.before['guards'] = [['nat', 1], ['nat', 2], ['nat', 1]]
        self.after['guards'] = [['nat', 1], ['nat', 1], ['nat', 2]]
        self.assertEqual(self.run_check()['status'], 'OK')
        self.after['guards'].pop()
        with self.assertRaisesRegex(CHECK.Mismatch, 'guards'):
            self.run_check()

    def test_explicit_attribute_command_cannot_move_to_another_constant(self):
        self.before['attributes'] = [['syntax', [ref('N.old'), 'custom']]]
        self.after['attributes'] = [['syntax', [ref('N.other'), 'custom']]]
        with self.assertRaisesRegex(CHECK.Mismatch, 'attributes'):
            self.run_check()

    def test_generated_cannot_replace_authored_or_external_reference(self):
        self.before['constants']['gen'] = constant()
        self.before['constants']['N.old'] = constant(ref('gen'))
        self.after['constants']['N.new'] = constant(ref('Nat'))
        with self.assertRaisesRegex(CHECK.Mismatch, 'generated reference'):
            self.run_check()

    def test_unmapped_authored_rename_fails(self):
        self.renames = {}
        with self.assertRaisesRegex(CHECK.Mismatch, 'authored constant set'):
            self.run_check()

    def test_lean_version_mismatch_and_empty_exports_refused(self):
        mapping = dict(schema_version=1, entries=[], retired_tokens=[], allowed_abbreviations=[])
        self.after['version'] = 'other'
        with self.assertRaisesRegex(ValueError, 'versions differ'):
            CHECK.check(self.before, self.after, mapping)
        with self.assertRaisesRegex(ValueError, 'no exported modules'):
            CHECK.read_exports([])


if __name__ == '__main__':
    unittest.main()
