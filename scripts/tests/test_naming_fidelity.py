import importlib.util
import copy
import json
from pathlib import Path
import tempfile
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

    def test_identical_registered_equations_coalesce(self):
        equation = constant()
        equation['equation_origin'] = ref('N.parent')
        existing = {'N.parent.eq_1': equation}
        self.assertEqual(CHECK.merge_constants(existing, set(), copy.deepcopy(existing), set()),
                         {'N.parent.eq_1'})
        self.assertEqual(len(existing), 1)

    def test_equal_bytes_without_provenance_do_not_coalesce(self):
        existing = {'N.parent.eq_1': constant()}
        with self.assertRaisesRegex(ValueError, 'duplicate constants'):
            CHECK.merge_constants(existing, set(), copy.deepcopy(existing), set())

    def test_authored_or_changed_equation_copies_refuse(self):
        equation = constant()
        equation['equation_origin'] = ref('N.parent')
        for authored_before, authored_after in [(True, False), (False, True)]:
            with self.assertRaisesRegex(ValueError, 'duplicate constants'):
                CHECK.merge_constants({'eq': copy.deepcopy(equation)}, {'eq'} if authored_before else set(),
                                      {'eq': copy.deepcopy(equation)}, {'eq'} if authored_after else set())
        for field, value in [('equation_origin', ref('Other.parent')), ('attributes', {'simp': True}),
                             ('kernel', {'type': 'different'})]:
            changed = copy.deepcopy(equation)
            changed[field] = value
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, 'duplicate constants'):
                CHECK.merge_constants({'eq': equation}, set(), {'eq': changed}, set())

    def test_equation_parent_is_compared_under_map(self):
        left, right = constant(), constant()
        left['equation_origin'], right['equation_origin'] = ref('N.old'), ref('N.new')
        self.before['constants']['N.old.eq_1'] = left
        self.after['constants']['N.new.eq_7'] = right
        self.assertEqual(self.run_check()['generated_constants'], 1)
        right['equation_origin'] = ref('Other.parent')
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()

    def test_provenance_requires_new_schema_and_valid_name(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'export.json'
            c = constant()
            c['equation_origin'] = ref('N.parent')
            data = dict(schema_version=6, lean_version='fixture', source='',
                        index=dict(version=5, module='Fixture', directImports=[], decls={}, references={}),
                        constants={'eq': c}, checked_commands=[], guards=[], attribute_syntax=[])
            path.write_text(json.dumps(data))
            self.assertEqual(CHECK.read_exports([path])['constants']['eq']['equation_origin'], ref('N.parent'))
            data['schema_version'] = 5
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'requires schema 6'):
                CHECK.read_exports([path])
            data['schema_version'] = 6
            c['equation_origin'] = ['guessed', 'N.parent']
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'invalid equation provenance'):
                CHECK.read_exports([path])

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
