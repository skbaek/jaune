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

    def entries(self, *rows):
        return CHECK.MAP.Renamer([dict(old=a, new=b, kind=k, **extra) for a, b, k, extra in rows])

    def test_namespace_row_maps_descendants_and_private_names(self):
        self.before = snapshot({'N.B256': constant(), 'N.B256.toNat': constant(2),
                                '_private.M.0.N.B256.go': constant(3)},
                               ['N.B256', 'N.B256.toNat', '_private.M.0.N.B256.go'])
        self.after = snapshot({'N.U256': constant(), 'N.U256.toNat': constant(2),
                               '_private.M.0.N.U256.go': constant(3)},
                              ['N.U256', 'N.U256.toNat', '_private.M.0.N.U256.go'])
        self.renames = self.entries(('N.B256', 'N.U256', 'namespace', {}))
        self.assertEqual(self.run_check()['authored_constants'], 3)
        self.after['constants']['N.U256.toNat'] = constant(9)
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()

    def test_swap_maps_each_side_once(self):
        # `a -> Old.a` and `Staging.a -> a` in one map: each before constant is compared
        # with its own image, so exchanging the two bodies fails.
        self.before = snapshot({'N.a': constant(2), 'N.Staging.a': constant(3)}, ['N.a', 'N.Staging.a'])
        self.after = snapshot({'N.Old.a': constant(2), 'N.a': constant(3)}, ['N.Old.a', 'N.a'])
        self.renames = self.entries(('N.a', 'N.Old.a', 'declaration', {}),
                                    ('N.Staging.a', 'N.a', 'declaration', {}))
        self.assertEqual(self.run_check()['authored_constants'], 2)
        self.after = snapshot({'N.Old.a': constant(3), 'N.a': constant(2)}, ['N.Old.a', 'N.a'])
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()

    def test_module_identity_requires_relocation_rows(self):
        self.before = snapshot({'N.f': constant()}, ['N.f'])
        self.after = snapshot({'N.f': constant()}, ['N.f'])
        self.before['owners'], self.after['owners'] = {'N.f': 'A'}, {'N.f': 'B'}
        self.renames = {}
        with self.assertRaisesRegex(CHECK.Mismatch, 'module A became B'):
            self.run_check()
        self.renames = self.entries(('N.f', 'N.f', 'relocation', dict(from_module='A', to_module='B')))
        self.assertEqual(self.run_check()['status'], 'OK')
        self.renames = self.entries(('N.f', 'N.f', 'relocation', dict(from_module='C', to_module='B')))
        with self.assertRaisesRegex(CHECK.Mismatch, 'relocation row names module C'):
            self.run_check()
        # A module row moves all of its declarations, private prefixes included.
        self.before = snapshot({'_private.A.0.N.g': constant()}, ['_private.A.0.N.g'])
        self.after = snapshot({'_private.B.0.N.g': constant()}, ['_private.B.0.N.g'])
        self.before['owners'], self.after['owners'] = {'_private.A.0.N.g': 'A'}, {'_private.B.0.N.g': 'B'}
        self.renames = self.entries(('A', 'B', 'module', {}))
        self.assertEqual(self.run_check()['status'], 'OK')

    def test_promoting_a_private_declaration_requires_its_exact_row(self):
        old = '_private.A.0.N.f'
        self.before = snapshot({old: constant()}, [old])
        self.after = snapshot({'N.f': constant()}, ['N.f'])
        self.before['owners'], self.after['owners'] = {old: 'A'}, {'N.f': 'B'}
        row = dict(from_module='A', to_module='B')
        self.renames = self.entries(('N.f', 'N.f', 'relocation', row))
        with self.assertRaisesRegex(CHECK.Mismatch, 'authored constant set changed'):
            self.run_check()
        row['public_from'] = old
        self.renames = self.entries(('N.f', 'N.f', 'relocation', row))
        self.assertEqual(self.run_check()['status'], 'OK')
        self.after['constants']['N.f'] = constant(2)
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()
        self.before = snapshot({'N.f': constant()}, ['N.f'])
        self.before['owners'] = {'N.f': 'A'}
        self.after['constants']['N.f'] = constant()
        with self.assertRaisesRegex(CHECK.Mismatch, 'public_from names no authored private'):
            self.run_check()

    def test_compiler_named_declarations_are_graph_matched(self):
        source = 'instance : Inhabited B256 := ⟨⟨0⟩⟩\ndef B256.f := 1\n'
        def export(name):
            index = dict(version=5, module='M', directImports=[], references={},
                         decls={name: [0, 0, 0, 30, 0, 0, 0, 8], 'N.B256.f': [1, 0, 1, 15, 1, 4, 1, 10]})
            return dict(schema_version=6, lean_version='x', source=source, index=index,
                        constants={name: dict(constant(), equation_origin=None),
                                   'N.B256.f': dict(constant(2), equation_origin=None)},
                        guards=[], attribute_syntax=[], checked_commands=[], imports={})
        with tempfile.TemporaryDirectory() as tmp:
            paths = []
            for label, name in [('before', 'N.instInhabitedB256'), ('after', 'N.instInhabitedU256')]:
                path = Path(tmp) / f'{label}.json'
                path.write_text(json.dumps(export(name)))
                paths.append(path)
            before, after = CHECK.read_exports([paths[0]]), CHECK.read_exports([paths[1]])
            self.assertEqual(before['roots'], {'N.B256.f'})
            self.renames = {'N.B256.f': 'N.B256.f'} and self.entries()
            self.before, self.after = before, after
            result = self.run_check()
            self.assertEqual(result['generated_constants'], 1)

    def test_quoted_identifier_compares_spelling_and_preresolution_under_map(self):
        def c(n):
            return ['const', ['name', n], []]
        def app(f, *xs):
            for x in xs:
                f = ['app', f, x]
            return f
        def name(*parts):
            return app(c(f'Lean.Name.mkStr{len(parts)}'), *[['str', x] for x in parts])
        def ident(raw, parts, decl, scoped=False):
            pre = app(c('List.cons'), c('T'), app(c('Lean.Syntax.Preresolved.decl'), name(*decl.split('.')),
                                                  app(c('List.nil'), c('String'))), app(c('List.nil'), c('T')))
            val = name(*parts)
            if scoped:
                val = app(c('Lean.addMacroScope'), ['bvar', 0], val, ['bvar', 1])
            return app(c('Lean.Syntax.ident'), c('Lean.SourceInfo.none'),
                       app(c("String.toRawSubstring'"), ['str', raw]), val, pre)
        def verdict(before, after):
            self.before = snapshot({'N.m': CHECK.quoted_identifiers(dict(kernel=before, attributes={}))}, ['N.m'])
            self.after = snapshot({'N.m': CHECK.quoted_identifiers(dict(kernel=after, attributes={}))}, ['N.m'])
            return self.run_check()['status']
        self.renames = CHECK.MAP.Renamer([dict(old='Jaune.B256', new='Jaune.U256', kind='declaration'),
                                          dict(old='Jaune.Tx.receiver', new='Jaune.Tx.to', kind='field')])
        for scoped in (False, True):
            # The names-only respelling passes, at the spelled depth.
            self.assertEqual(verdict(ident('B256', ['B256'], 'Jaune.B256', scoped),
                                     ident('U256', ['U256'], 'Jaune.U256', scoped)), 'OK')
            self.assertEqual(verdict(ident('Jaune.B256', ['Jaune', 'B256'], 'Jaune.B256', scoped),
                                     ident('Jaune.U256', ['Jaune', 'U256'], 'Jaune.U256', scoped)), 'OK')
            # A qualification changes what `Syntax.getId` returns.
            with self.assertRaisesRegex(CHECK.Mismatch, 'quoted spelling'):
                verdict(ident('B256', ['B256'], 'Jaune.B256', scoped),
                        ident('Jaune.U256', ['Jaune', 'U256'], 'Jaune.U256', scoped))
            # A reviewed capture-qualified quotation is accepted only as recorded.
            record = dict(module='M', constant='N.m', before='B256', after='Jaune.U256', map_old='Jaune.B256',
                          map_new='Jaune.U256', decision='d', reason='r', precedent='p')
            def reviewed(rec, holder='N.m', twice=False, module='M'):
                one = lambda *a: ident(*a, scoped)
                pair = lambda *a: ['app', one(*a), one(*a)] if twice else one(*a)
                self.before = snapshot({holder: CHECK.quoted_identifiers(dict(kernel=pair('B256', ['B256'], 'Jaune.B256'), attributes={}))}, [holder])
                self.after = snapshot({holder: CHECK.quoted_identifiers(dict(kernel=pair('Jaune.U256', ['Jaune', 'U256'], 'Jaune.U256'), attributes={}))}, [holder])
                self.before['owners'] = {holder: module}
                used = set()
                verdict = CHECK.Comparison(self.before, self.after, self.renames, [rec], used).run()
                return verdict['status'], used
            self.assertEqual(reviewed(record), ('OK', {0}))
            # Control: a record naming another constant, or another map row, does not apply.
            for bad in (dict(record, constant='N.other'), dict(record, map_old='Jaune.Tx.receiver', map_new='Jaune.Tx.to'),
                        dict(record, after='Jaune.Other', map_new='Jaune.Other')):
                with self.assertRaisesRegex(CHECK.Mismatch, 'quoted spelling'):
                    reviewed(bad)
            # Control (finding 6): a record binds its own constant, not one its
            # name prefixes; its module; and one occurrence.
            with self.assertRaisesRegex(CHECK.Mismatch, 'quoted spelling'):
                reviewed(dict(record, constant='N'), holder='N.m')
            with self.assertRaisesRegex(CHECK.Mismatch, 'quoted spelling'):
                reviewed(record, module='Elsewhere')
            with self.assertRaisesRegex(CHECK.Mismatch, 'occurs more than once'):
                reviewed(record, twice=True)
            # The same spelling resolving to another declaration fails too.
            with self.assertRaisesRegex(CHECK.Mismatch, 'reference'):
                verdict(ident('B256', ['B256'], 'Jaune.B256', scoped),
                        ident('U256', ['U256'], 'JauneConsensus.U256', scoped))
        # Quotations inside guards follow the same rule.
        self.before = snapshot({'N.m': constant()}, ['N.m'],
                               guards=[CHECK.quoted_identifiers(ident('B256', ['B256'], 'Jaune.B256'))])
        self.after = snapshot({'N.m': constant()}, ['N.m'],
                              guards=[CHECK.quoted_identifiers(ident('U256', ['U256'], 'Jaune.U256'))])
        self.assertEqual(self.run_check()['status'], 'OK')
        self.after['guards'] = [CHECK.quoted_identifiers(ident('Jaune.U256', ['Jaune', 'U256'], 'Jaune.U256'))]
        with self.assertRaisesRegex(CHECK.Mismatch, 'guards'):
            self.run_check()
        # Keyword escapes in the raw text are spelling only.
        self.assertEqual(verdict(ident('Tx.receiver', ['Tx', 'receiver'], 'Jaune.Tx.receiver'),
                                 ident('Tx.«to»', ['Tx', 'to'], 'Jaune.Tx.to')), 'OK')
        with self.assertRaisesRegex(CHECK.Mismatch, 'raw text'):
            verdict(ident('Tx.receiver', ['Tx', 'receiver'], 'Jaune.Tx.receiver'),
                    ident('Tx.other', ['Tx', 'to'], 'Jaune.Tx.to'))
        # Control (finding 11): an unchanged spelling keeps its raw escapes.
        self.renames = CHECK.MAP.Renamer([dict(old='Jaune.B256', new='Jaune.U256', kind='declaration')])
        self.assertEqual(verdict(ident('Tx.«to»', ['Tx', 'to'], 'Jaune.Tx.to'),
                                 ident('Tx.«to»', ['Tx', 'to'], 'Jaune.Tx.to')), 'OK')
        with self.assertRaisesRegex(CHECK.Mismatch, 'unchanged spelling'):
            verdict(ident('«Tx».foo', ['Tx', 'foo'], 'Jaune.Tx.foo'),
                    ident('Tx.foo', ['Tx', 'foo'], 'Jaune.Tx.foo'))

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

    def test_realized_copies_coalesce_only_when_identical_and_not_authored(self):
        # Lean realizes auxiliaries (`congr_simp`, `_sparseCasesOn` equations)
        # in every module that needs them; agreeing copies are one constant.
        existing = {'Std.Range.mk.congr_simp': constant()}
        self.assertEqual(CHECK.merge_constants(existing, set(), copy.deepcopy(existing), set()),
                         {'Std.Range.mk.congr_simp'})
        with self.assertRaisesRegex(ValueError, 'duplicate constants'):
            CHECK.merge_constants(existing, set(), {'Std.Range.mk.congr_simp': constant(2)}, set())
        with self.assertRaisesRegex(ValueError, 'duplicate constants'):
            CHECK.merge_constants(existing, {'Std.Range.mk.congr_simp'}, copy.deepcopy(existing), set())

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

    def test_checks_stay_in_their_module_unless_a_relocation_row_links_it(self):
        for key in ('guards', 'checks', 'attributes'):
            self.setUp()
            self.before[key], self.after[key] = [['nat', 1]], [['nat', 1]]
            self.before['item_modules'] = {key: ['A']}
            self.after['item_modules'] = {key: ['B']}
            with self.assertRaisesRegex(CHECK.Mismatch, rf"{key}: .*modules \['A', 'B'\]"):
                self.run_check()
            self.renames = self.entries(('N.old', 'N.new', 'relocation', dict(from_module='A', to_module='B')))
            self.assertEqual(self.run_check()['status'], 'OK')
            # A module row renames the module the check stays in.
            self.renames = self.entries(('N.old', 'N.new', 'declaration', {}), ('A', 'B', 'module', {}))
            self.assertEqual(self.run_check()['status'], 'OK')

    def guard(self, text):
        return [['syntax', 'Lean.guardMsgsCmd', [
            ['syntax', 'null', [['syntax', 'Lean.Parser.Command.docComment', [['atom', '/--'], ['atom', text]]]]],
            ['atom', '#guard_msgs'], ['syntax', 'null', []], ['atom', 'in']]]]

    def test_guard_msgs_text_compares_as_the_map_respelling(self):
        self.before = snapshot({'N.Ninst.step': constant(), 'N.x': constant(2)}, ['N.Ninst.step', 'N.x'])
        self.after = snapshot({'N.NextOp.step': constant(), 'N.x': constant(2)}, ['N.NextOp.step', 'N.x'])
        self.renames = self.entries(('N.Ninst.step', 'N.NextOp.step', 'declaration', {}))
        self.before['checks'] = self.guard('error: Ninst.step x =\n  x-/')
        self.after['checks'] = self.guard('error: NextOp.step x =\n  x-/')
        self.assertEqual(self.run_check()['status'], 'OK')
        # Control: a change beyond the respelling fails.
        self.after['checks'] = self.guard('error: NextOp.step x ≠\n  x-/')
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()
        # Control: an old name left unrenamed in the after text fails.
        self.after['checks'] = self.guard('error: Ninst.step x =\n  x-/')
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()

    def derived_repr(self, ctor, label, width, extra=' := '):
        text = lambda t: ['app', ['const', ['name', 'Std.Format.text'], []], ['str', t]]
        nest = ['app', ['app', ['const', ['name', 'Std.Format.nest'], []], ['nat', width]],
                ['app', ['const', ['name', 'N.S.' + label], []], ['bvar', 0]]]
        return dict(kernel=['definition', 'safe', ['app', text(ctor), ['app', text(label), ['app', text(extra), nest]]]],
                    attributes={})

    def test_derived_repr_text_follows_the_map_and_nothing_else(self):
        rows = self.entries(('N.T.old', 'N.T.new', 'constructor', {}), ('N.S.lbl', 'N.S.label', 'field', {}))
        def check(before_args, after_args, derived=True):
            self.before = snapshot({'N.T.old': constant(), 'N.S.lbl': constant(2), 'inst.repr': self.derived_repr(*before_args)},
                                   ['N.T.old', 'N.S.lbl'])
            self.after = snapshot({'N.T.new': constant(), 'N.S.label': constant(2), 'inst.repr': self.derived_repr(*after_args)},
                                  ['N.T.new', 'N.S.label'])
            if derived:
                self.before['derived'] = {'inst.repr': ('N.S', 'Repr')}
            self.renames = rows
            return self.run_check()
        verdict = check(('N.T.old', 'lbl', 7), ('N.T.new', 'label', 9))
        self.assertEqual(verdict['status'], 'OK')
        self.assertEqual(sorted(r[3] for r in verdict['derived_literals_respelled']),
                         ['field label', 'field label width', 'qualified name'])
        # Control: any other change of derived text fails.
        with self.assertRaises(CHECK.Mismatch):
            check(('N.T.old', 'lbl', 7), ('N.T.new', 'label', 9, ' = '))
        # Control: a label change that is not the field row's leaf change fails.
        with self.assertRaises(CHECK.Mismatch):
            check(('N.T.old', 'lbl', 7), ('N.T.new', 'labels', 10))
        # Control: a width change without the label's respelling fails.
        with self.assertRaises(CHECK.Mismatch):
            check(('N.T.old', 'lbl', 7), ('N.T.new', 'label', 8))
        # Control: the same literals outside a derived constant are compared as written.
        with self.assertRaises(CHECK.Mismatch):
            check(('N.T.old', 'lbl', 7), ('N.T.new', 'label', 9), derived=False)
        # Control: an unqualified key of another handler (ToJson) stays literal.
        self.before = snapshot({'N.T.old': constant(), 'N.S.lbl': constant(2), 'inst.repr': self.derived_repr('N.T.old', 'lbl', 7)},
                               ['N.T.old', 'N.S.lbl'])
        self.after = snapshot({'N.T.new': constant(), 'N.S.label': constant(2), 'inst.repr': self.derived_repr('N.T.new', 'label', 9)},
                              ['N.T.new', 'N.S.label'])
        self.before['derived'] = {'inst.repr': ('N.S', 'ToJson')}
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()

    def test_derived_provenance_needs_a_deriving_clause_and_no_declaration_range(self):
        source = 'structure S where\n  lbl : Nat\nderiving Repr\n'
        value = ['app', ['app', ['const', ['name', 'Repr.mk'], []], ['const', ['name', 'N.S'], []]],
                 ['const', ['name', 'N.instReprS.repr'], []]]
        def data(src, inst_range=False):
            decls = {'N.S': [0, 10, 0, 11, 0, 10, 0, 11]}
            if inst_range:
                decls['N.instReprS'] = [2, 0, 2, 8, 2, 0, 2, 8]
            return dict(source=src, constants={'N.instReprS': dict(kernel=['definition', 'safe', value]),
                                               'N.instReprS.repr': dict(kernel=['definition', 'safe', ['nat', 0]])},
                        index=dict(decls=decls, naming_syntax=dict(commands=[[0, len(src.encode()), 'Lean.Parser.Command.declaration']])))
        def derived(d):
            positions = CHECK.APPLY.Positions(d['source'])
            offsets = [0]
            for ch in d['source']:
                offsets.append(offsets[-1] + len(ch.encode()))
            return CHECK.derived_constants(d, None, offsets, positions)
        self.assertEqual(derived(data(source)), {'N.instReprS': ('N.S', 'Repr'), 'N.instReprS.repr': ('N.S', 'Repr')})
        # Control: without a deriving clause for the class, nothing is derived.
        self.assertEqual(derived(data(source.replace('deriving Repr', 'deriving BEq'))), {})
        # Control: an instance with a source declaration range (hand-written) is not derived.
        self.assertEqual(derived(data(source, inst_range=True)), {})

    def test_resolved_name_literals_follow_the_map(self):
        def lit(*parts):
            e = ['const', ['name', f'Lean.Name.mkStr{len(parts)}'], []]
            for p in parts:
                e = ['app', e, ['str', p]]
            return dict(kernel=['definition', 'safe', e], attributes={})
        self.renames = self.entries(('N.old', 'N.new', 'declaration', {}))
        def check(before, after):
            self.before = snapshot({'N.old': constant(), 'N.m': lit(*before)}, ['N.old', 'N.m'])
            self.after = snapshot({'N.new': constant(), 'N.m': lit(*after)}, ['N.new', 'N.m'])
            return self.run_check()
        verdict = check(('N', 'old'), ('N', 'new'))
        self.assertEqual([r[3] for r in verdict['derived_literals_respelled']], ['name literal'])
        # Control: a literal that names no renamed constant is compared as written.
        with self.assertRaises(CHECK.Mismatch):
            check(('N', 'other'), ('N', 'another'))
        # Control: a renamed constant's literal changed some other way fails.
        with self.assertRaises(CHECK.Mismatch):
            check(('N', 'old'), ('N', 'newer'))

    def test_collect_all_reports_every_mismatch_and_still_fails(self):
        self.before = snapshot({'N.old': constant(), 'N.a': constant(1), 'N.b': constant(2)}, ['N.old', 'N.a', 'N.b'])
        self.after = snapshot({'N.new': constant(), 'N.a': constant(5), 'N.b': constant(6)}, ['N.new', 'N.a', 'N.b'])
        with self.assertRaises(CHECK.Mismatch) as first:
            CHECK.Comparison(self.before, self.after, self.renames).run()
        self.assertNotIn('mismatch(es)', str(first.exception))
        with self.assertRaises(CHECK.Mismatch) as every:
            CHECK.Comparison(self.before, self.after, self.renames, collect=True).run()
        self.assertIn('2 mismatch(es)', str(every.exception))
        self.assertIn('constant N.a', str(every.exception))
        self.assertIn('constant N.b', str(every.exception))

    def test_generated_constants_follow_a_derived_namespace(self):
        # Two member rows rename namespace N.Inv -> N.Invariant (derived); the
        # compiler-named syntax kind N.Inv.tacticFoo has no row and moves with it.
        rows = self.entries(('N.Inv.a', 'N.Invariant.a', 'declaration', {}), ('N.Inv.b', 'N.Invariant.b', 'declaration', {}))
        lit = lambda *ps: ['definition', 'safe', ['app', ['app', ['app', ['const', ['name', 'Lean.Name.mkStr3'], []],
                                                                        ['str', ps[0]]], ['str', ps[1]]], ['str', ps[2]]]]
        def run(before_ns, after_ns, kind_parent):
            self.before = snapshot({'N.Inv.a': constant(), 'N.Inv.b': constant(2), f'{kind_parent}.tacticFoo': constant(7),
                                    'gen': dict(kernel=lit('N', before_ns, 'tacticFoo'), attributes={})},
                                   ['N.Inv.a', 'N.Inv.b'])
            after_kind = f'N.Invariant.tacticFoo' if kind_parent == 'N.Inv' else f'{kind_parent}.tacticFoo'
            self.after = snapshot({'N.Invariant.a': constant(), 'N.Invariant.b': constant(2), after_kind: constant(7),
                                   'gen': dict(kernel=lit('N', after_ns, 'tacticFoo'), attributes={})},
                                  ['N.Invariant.a', 'N.Invariant.b'])
            self.renames = rows
            return self.run_check()
        verdict = run('Inv', 'Invariant', 'N.Inv')
        self.assertIn(['gen', 'N.Inv.tacticFoo', 'N.Invariant.tacticFoo', 'name literal'], verdict['derived_literals_respelled'])
        # Control: a generated constant whose parent namespace is not renamed does not move.
        with self.assertRaises(CHECK.Mismatch):
            run('Other', 'Otherwise', 'N.Other')

    def dot_export(self, source, ctor, ref_ctor=None):
        """A one-module export whose checked command contains `.ctor` with the
        compiler's reference recorded over the dot-inclusive range."""
        start = source.index('.' + ctor)
        ref = ref_ctor or ctor
        refs = {json.dumps({'c': {'m': 'M', 'n': f'N.T.{ref}'}}): dict(definition=None, usages=[[0, start, 0, start + 1 + len(ctor)]])}
        b = len(source[:start].encode())
        syntax = ['syntax', 'Lean.Parser.Term.dotIdent', [['atom', '.'], ['ident', ctor, b + 1, b + 1 + len(ctor.encode())]]]
        return dict(schema_version=7, lean_version='x', source=source,
                    index=dict(version=5, module='M', directImports=[], references=refs, decls={}),
                    constants={f'N.T.{ref}': dict(constant(), equation_origin=None)}, guards=[], attribute_syntax=[],
                    checked_commands=[dict(syntax=syntax, literal_names=False, start=0, end=len(source.encode()),
                                           expected_failure_scope=False)], imports={})

    def test_dot_identifiers_resolve_over_the_dot(self):
        with tempfile.TemporaryDirectory() as tmp:
            def read(data, label):
                path = Path(tmp) / f'{label}.json'
                path.write_text(json.dumps(data))
                return CHECK.read_exports([path])
            self.renames = self.entries(('N.T.reg', 'N.T.plain', 'constructor', {}))
            self.before = read(self.dot_export('#guard x = .reg', 'reg'), 'b')
            self.after = read(self.dot_export('#guard x = .plain', 'plain'), 'a')
            self.assertEqual(self.before['checks'][0][2][1], ['name', 'N.T.reg'])
            self.assertEqual(self.before['dot_identifiers_resolved'], 1)
            self.assertEqual(self.run_check()['status'], 'OK')
            # Control: a dot identifier naming a different constructor fails
            # (both constructors exist on each side; only the check differs).
            def both(source, ctor, label):
                data = self.dot_export(source, ctor)
                data['constants'] = {'N.T.reg' if 'b' in label else 'N.T.plain': dict(constant(1), equation_origin=None),
                                     'N.T.div': dict(constant(2), equation_origin=None)}
                return read(data, label)
            self.before = both('#guard x = .reg', 'reg', 'b2')
            self.after = read(dict(self.dot_export('#guard x = .div', 'div'),
                                   constants={'N.T.plain': dict(constant(1), equation_origin=None),
                                              'N.T.div': dict(constant(2), equation_origin=None)}), 'a2')
            with self.assertRaises(CHECK.Mismatch):
                self.run_check()
            # Control: a shifted lookup that finds a different constant than the token refuses.
            with self.assertRaisesRegex(ValueError, 'dot identifier'):
                read(self.dot_export('#guard x = .reg', 'reg', ref_ctor='div'), 'bad')

    def test_quoted_spelling_with_projection_fields(self):
        def c(n):
            return ['const', ['name', n], []]
        def app(f, *xs):
            for x in xs:
                f = ['app', f, x]
            return f
        def name(*parts):
            return app(c(f'Lean.Name.mkStr{len(parts)}'), *[['str', x] for x in parts])
        def ident(raw, decl, fields):
            pre = app(c('List.cons'), c('T'), app(c('Lean.Syntax.Preresolved.decl'), name(*decl.split('.')),
                      app(c('List.cons'), c('String'), ['str', fields[0]], app(c('List.nil'), c('String')))),
                      app(c('List.nil'), c('T')))
            return app(c('Lean.Syntax.ident'), c('Lean.SourceInfo.none'),
                       app(c("String.toRawSubstring'"), ['str', raw]), name(*raw.split('.')), pre)
        self.renames = CHECK.MAP.Renamer([dict(old='N.Inv.core', new='N.Invariant.core', kind='declaration'),
                                          dict(old='N.Inv.x', new='N.Invariant.x', kind='declaration')])
        def verdict(before, after):
            self.before = snapshot({'N.m': CHECK.quoted_identifiers(dict(kernel=before, attributes={}))}, ['N.m'])
            self.after = snapshot({'N.m': CHECK.quoted_identifiers(dict(kernel=after, attributes={}))}, ['N.m'])
            return self.run_check()['status']
        self.assertEqual(verdict(ident('core.trans', 'N.Inv.core', ['trans']),
                                 ident('core.trans', 'N.Invariant.core', ['trans'])), 'OK')
        # Control: a changed field component fails.
        with self.assertRaisesRegex(CHECK.Mismatch, 'quoted spelling'):
            verdict(ident('core.trans', 'N.Inv.core', ['trans']), ident('core.symm', 'N.Invariant.core', ['symm']))

    def test_generated_auxiliaries_prefer_their_renamed_parent(self):
        same = dict(kernel=['definition', 'safe', ['nat', 1]], attributes={})
        self.renames = self.entries(('N.a', 'N.z', 'declaration', {}), ('N.b', 'N.y', 'declaration', {}))
        self.before = snapshot({'N.a': constant(), 'N.b': constant(2), 'N.a.match_1': same, 'N.b.match_1': same},
                               ['N.a', 'N.b'])
        self.after = snapshot({'N.z': constant(), 'N.y': constant(2), 'N.z.match_1': same, 'N.y.match_1': same},
                              ['N.z', 'N.y'])
        self.before['holders'] = {'N.a.match_1': {'A'}, 'N.b.match_1': {'B'}}
        self.after['holders'] = {'N.z.match_1': {'A'}, 'N.y.match_1': {'B'}}
        self.assertEqual(self.run_check()['status'], 'OK')
        # Control: without the preference the identical matchers cross modules.
        original = CHECK.Comparison.preferred_generated
        try:
            CHECK.Comparison.preferred_generated = lambda self, name: self.name(name)
            with self.assertRaisesRegex(CHECK.Mismatch, 'generated constant'):
                self.run_check()
        finally:
            CHECK.Comparison.preferred_generated = original

    def test_namespace_and_private_kind_literals_follow_a_derived_namespace(self):
        rows = self.entries(('N.Inv.a', 'N.Invariant.a', 'declaration', {}), ('N.Inv.b', 'N.Invariant.b', 'declaration', {}))
        def lit(*ps):
            e = ['const', ['name', f'Lean.Name.mkStr{len(ps)}'], []]
            for p in ps:
                e = ['app', e, ['str', p]]
            return e
        def run(before_lits, after_lits, holder_module='M'):
            kernel = lambda lits: dict(kernel=['definition', 'safe', ['app', lit(*lits[0]), lit(*lits[1])]], attributes={})
            self.before = snapshot({'N.Inv.a': constant(), 'N.Inv.b': constant(2), '_private.M.0.N.Inv.tacticFoo': constant(7),
                                    'gen': kernel(before_lits)}, ['N.Inv.a', 'N.Inv.b'])
            self.before['owners'] = {'gen': holder_module}
            self.after = snapshot({'N.Invariant.a': constant(), 'N.Invariant.b': constant(2),
                                   '_private.M.0.N.Invariant.tacticFoo': constant(7), 'gen': kernel(after_lits)},
                                  ['N.Invariant.a', 'N.Invariant.b'])
            self.renames = rows
            return self.run_check()
        verdict = run([('N', 'Inv'), ('N', 'Inv', 'tacticFoo')], [('N', 'Invariant'), ('N', 'Invariant', 'tacticFoo')])
        self.assertEqual(sorted(r[3] for r in verdict['derived_literals_respelled']), ['namespace literal', 'namespace literal'])
        # Control: a literal under an unrenamed namespace stays literal.
        with self.assertRaises(CHECK.Mismatch):
            run([('N', 'Other'), ('N', 'Inv', 'tacticFoo')], [('N', 'Otherwise'), ('N', 'Invariant', 'tacticFoo')])
        # Control: a literal under the renamed namespace that names no constant stays literal.
        with self.assertRaises(CHECK.Mismatch):
            run([('N', 'Inv'), ('N', 'Inv', 'zzz')], [('N', 'Invariant'), ('N', 'Invariant', 'zzz')])
        # Control (finding 14): a private kind of module M says nothing about a
        # literal held in module B.
        with self.assertRaises(CHECK.Mismatch):
            run([('N', 'Inv'), ('N', 'Inv', 'tacticFoo')], [('N', 'Invariant'), ('N', 'Invariant', 'tacticFoo')],
                holder_module='B')
        # Control: an authored constant under the namespace is not moved by this path.
        self.before = snapshot({'N.Inv.a': constant(), 'N.Inv.b': constant(2), 'N.Inv.c': constant(3),
                                'gen': dict(kernel=['definition', 'safe', lit('N', 'Inv', 'c')], attributes={})},
                               ['N.Inv.a', 'N.Inv.b', 'N.Inv.c'])
        comparison = CHECK.Comparison(self.before, self.before, rows)
        self.assertEqual(comparison.namespace_literal('N.Inv.c'), 'N.Inv.c')

    def test_unhygienic_quoted_identifiers_follow_the_map_at_plan_edits(self):
        def c(n):
            return ['const', ['name', n], []]
        def app(f, *xs):
            for x in xs:
                f = ['app', f, x]
            return f
        def ident(raw):
            parts = raw.split('.')
            val = app(c(f'Lean.Name.mkStr{len(parts)}'), *[['str', x] for x in parts])
            return app(c('Lean.Syntax.ident'), c('Lean.SourceInfo.none'), app(c("String.toRawSubstring'"), ['str', raw]),
                       val, app(c('List.nil'), c('Lean.Syntax.Preresolved')))
        rows = self.entries(('N.HdrEq', 'N.HeaderEq', 'declaration', {}))
        def run(before, after, plan=True, hygienic=False, sites=None, edits=None):
            self.before = snapshot({'N.HdrEq': constant(), 'N.m': CHECK.quoted_identifiers(dict(kernel=ident(before), attributes={}))},
                                   ['N.HdrEq', 'N.m'])
            self.after = snapshot({'N.HeaderEq': constant(), 'N.m': CHECK.quoted_identifiers(dict(kernel=ident(after), attributes={}))},
                                  ['N.HeaderEq', 'N.m'])
            self.before['quotation_sites'] = {'M': sites or [(10, 15, 'HdrEq'), (20, 23, 'x13')]}
            self.before['module_commands'] = {'M': [(0, 18), (18, 30), (30, 40)]}
            self.before['module_sources'] = {'M': ''}
            self.before['owners'] = {'N.m': 'M', 'N.HdrEq': 'M'}
            if edits is None:
                edits = {('M', 10, 15, 'HdrEq', 'HeaderEq')} if plan else set()
            return CHECK.check(self.before | dict(version='v'), self.after | dict(version='v'),
                               dict(schema_version=1, retired_tokens=[], allowed_abbreviations=[], entries=[
                                   dict(old='N.HdrEq', new='N.HeaderEq', kind='declaration', layer='execution', rule='4', source='x')]),
                               plan_edits=edits)
        self.assertEqual(CHECK.quoted_identifiers(ident('HdrEq'))[0], 'unhygienicIdentifier')
        verdict = run('HdrEq', 'HeaderEq')
        self.assertEqual([(r['old'], r['new'], r['module']) for r in verdict['unhygienic_respellings']], [('HdrEq', 'HeaderEq', 'M')])
        # Control: changed beyond the respelling fails.
        with self.assertRaises(CHECK.Mismatch):
            run('HdrEq', 'HeaderEqs')
        # Control: an unhygienic local naming no constant, changed, fails.
        with self.assertRaises(CHECK.Mismatch):
            run('x13', 'x14')
        # Control: a respelling with no matching plan edit fails.
        with self.assertRaisesRegex(CHECK.Mismatch, 'unhygienic quoted spelling'):
            run('HdrEq', 'HeaderEq', plan=False)
        # A spelling the plan never edited (a local that happens to equal a
        # renamed leaf) stays as written.
        self.assertEqual(run('HdrEq', 'HdrEq', plan=False)['status'], 'OK')
        # Control (finding 15, per-site binding): the module quotes HdrEq in
        # two commands and the plan edits only the first; the constant's
        # identifier is the second command's, so its respelling fails (the
        # module-pooled rule accepted it) and keeping it passes.
        two = [(10, 15, 'HdrEq'), (32, 37, 'HdrEq')]
        edit_first = {('M', 10, 15, 'HdrEq', 'HeaderEq')}
        with self.assertRaisesRegex(CHECK.Mismatch, 'cannot be bound|unhygienic quoted spelling'):
            run('HdrEq', 'HeaderEq', sites=two, edits=edit_first)
        # Both commands match the one-identifier constant, with different
        # plan outcomes: ambiguous, refused even when kept.
        with self.assertRaisesRegex(CHECK.Mismatch, 'cannot be bound'):
            run('HdrEq', 'HdrEq', sites=two, edits=edit_first)
        # With a second identifier in the first command only the second
        # command matches: kept passes, respelled fails.
        three = [(10, 15, 'HdrEq'), (16, 17, 'y'), (32, 37, 'HdrEq')]
        self.assertEqual(run('HdrEq', 'HdrEq', sites=three, edits=edit_first)['status'], 'OK')
        with self.assertRaisesRegex(CHECK.Mismatch, 'unhygienic quoted spelling'):
            run('HdrEq', 'HeaderEq', sites=three, edits=edit_first)
        # ... and with the edit at the second command's range, respelled passes.
        self.assertEqual(run('HdrEq', 'HeaderEq', sites=three,
                             edits={('M', 32, 37, 'HdrEq', 'HeaderEq')})['status'], 'OK')

    # --- G0a landing-review hardening (jsn-u16): each test fails on the
    # checker before its fix and passes after it.

    def lit_kernel(self, *parts):
        e = ['const', ['name', f'Lean.Name.mkStr{len(parts)}'], []]
        for part in parts:
            e = ['app', e, ['str', part]]
        return dict(kernel=['definition', 'safe', e], attributes={})

    def test_derived_provenance_ignores_comments_and_strings(self):
        # Finding 5: a commented-out or quoted deriving clause is not one.
        value = ['app', ['app', ['const', ['name', 'Repr.mk'], []], ['const', ['name', 'N.S'], []]],
                 ['const', ['name', 'N.instReprS.repr'], []]]
        def derived(src):
            d = dict(source=src, constants={'N.instReprS': dict(kernel=['definition', 'safe', value]),
                                            'N.instReprS.repr': dict(kernel=['definition', 'safe', ['nat', 0]])},
                     index=dict(decls={'N.S': [0, 10, 0, 11, 0, 10, 0, 11]},
                                naming_syntax=dict(commands=[[0, len(src.encode()), 'Lean.Parser.Command.declaration']])))
            positions = CHECK.APPLY.Positions(src)
            offsets = [0]
            for ch in src:
                offsets.append(offsets[-1] + len(ch.encode()))
            return CHECK.derived_constants(d, None, offsets, positions)
        self.assertEqual(len(derived('structure S where\n  lbl : Nat\nderiving Repr\n')), 2)
        for fake in ('-- deriving Repr', '/-- deriving Repr -/', '/- deriving Repr -/ deriving BEq',
                     'deriving BEq -- , Repr', 'deriving BEq\n#eval "deriving Repr"'):
            self.assertEqual(derived('structure S where\n  lbl : Nat\n' + fake + '\n'), {}, fake)

    def test_reviewed_record_is_not_consumed_by_a_failed_speculation(self):
        # Findings 6/13: a record accepted inside a failed speculative pairing
        # is rolled back, so a record no successful comparison used is stale.
        def c(n):
            return ['const', ['name', n], []]
        def app(f, *xs):
            for x in xs:
                f = ['app', f, x]
            return f
        def name(*parts):
            return app(c(f'Lean.Name.mkStr{len(parts)}'), *[['str', x] for x in parts])
        def ident(raw, decl):
            pre = app(c('List.cons'), c('T'), app(c('Lean.Syntax.Preresolved.decl'), name(*decl.split('.')),
                                                  app(c('List.nil'), c('String'))), app(c('List.nil'), c('T')))
            return app(c('Lean.Syntax.ident'), c('Lean.SourceInfo.none'),
                       app(c("String.toRawSubstring'"), ['str', raw]), name(*raw.split('.')), pre)
        def gen(raw, decl, k):
            return CHECK.quoted_identifiers(dict(kernel=['app', ident(raw, decl), ['nat', k]], attributes={}))
        self.renames = CHECK.MAP.Renamer([dict(old='Jaune.B256', new='Jaune.U256', kind='declaration')])
        self.before = snapshot({'N.r': constant(), 'g1': gen('B256', 'Jaune.B256', 1)}, ['N.r'])
        self.after = snapshot({'N.r': constant(), 'g1': gen('Jaune.U256', 'Jaune.U256', 2),
                               'g2': gen('U256', 'Jaune.U256', 1)}, ['N.r'])
        self.before['owners'] = {'g1': 'M', 'N.r': 'M'}
        record = dict(module='M', constant='g1', before='B256', after='Jaune.U256', map_old='Jaune.B256',
                      map_new='Jaune.U256', decision='d', reason='r', precedent='p')
        used = set()
        # g1 tries its same-named image first: the record is accepted there,
        # then the payload differs and the pairing is rolled back; g1 then
        # matches g2 by the names-only respelling. (g1's image is left
        # unmatched, so the run fails; the record must not count as used.)
        comparison = CHECK.Comparison(self.before, self.after, self.renames, [record], used, collect=True)
        with self.assertRaises(CHECK.Mismatch):
            comparison.run()
        self.assertEqual(comparison.pairs.get('g1'), 'g2')
        self.assertEqual(used, set())
        self.assertEqual(comparison.reviewed_here, set())

    def test_aux_module_component_is_single_pass_and_injective(self):
        # Finding 8: chained module rows do not compose, and mangling must be injective.
        rows = self.entries(('A.M1', 'A.M2', 'module', {}), ('A.M2', 'A.M3', 'module', {}))
        self.renames = rows
        self.before = snapshot({'N._aux_A_M1___x': constant()}, ['N._aux_A_M1___x'])
        self.after = snapshot({'N._aux_A_M2___x': constant()}, ['N._aux_A_M2___x'])
        self.assertEqual(self.run_check()['status'], 'OK')
        self.after = snapshot({'N._aux_A_M3___x': constant()}, ['N._aux_A_M3___x'])
        with self.assertRaisesRegex(CHECK.Mismatch, 'authored constant set changed'):
            self.run_check()
        self.renames = self.entries(('A.B_C', 'A.X', 'module', {}), ('A_B.C', 'A.Y', 'module', {}))
        with self.assertRaisesRegex(ValueError, 'mangle alike'):
            self.run_check()

    def test_name_literal_components_and_data_literals(self):
        # Finding 9: a literal is respelled only as a name of plain
        # components, and a single-backtick data literal only where the
        # applied plan respelled it.
        self.renames = self.entries(('N.old', 'N.new', 'declaration', {}))
        def check(before, after, source=None, edits=None):
            self.before = snapshot({'N.old': constant(), 'N.m': self.lit_kernel(*before)}, ['N.old', 'N.m'])
            self.after = snapshot({'N.new': constant(), 'N.m': self.lit_kernel(*after)}, ['N.new', 'N.m'])
            if source is not None:
                self.before['module_sources'] = {'M': source}
                self.before['owners'] = {'N.m': 'M', 'N.old': 'M'}
            return CHECK.Comparison(self.before, self.after, self.renames, plan_edits=edits).run()
        self.assertEqual(check(('N', 'old'), ('N', 'new'))['status'], 'OK')
        # One component holding a dot is not the dotted name.
        with self.assertRaises(CHECK.Mismatch):
            check(('N.old',), ('N', 'new'))
        with self.assertRaises(CHECK.Mismatch):
            check(('N.old',), ('N.new',))
        # A double-backtick literal (resolved by Lean) follows the rename.
        self.assertEqual(check(('N', 'old'), ('N', 'new'), source='def m := ``old\n')['status'], 'OK')
        # A single-backtick literal is data: unchanged unless the plan respelled it there.
        src = 'def m := `N.old\n'
        with self.assertRaises(CHECK.Mismatch):
            check(('N', 'old'), ('N', 'new'), source=src)
        self.assertEqual(check(('N', 'old'), ('N', 'old'), source=src)['status'], 'OK')
        start = src.index('N.old')
        self.assertEqual(check(('N', 'old'), ('N', 'new'), source=src,
                               edits={('M', start + 2, start + 5, 'old', 'new')})['status'], 'OK')
        # Backticks in comments and strings are not literals.
        self.assertEqual(check(('N', 'old'), ('N', 'new'),
                               source='/-- see `N.old` -/\ndef m := ``old -- `N.old\n#eval "`N.old"\n')['status'], 'OK')

    def test_derived_namespace_moves_only_when_every_member_moves(self):
        # Finding 10: an authored member left behind blocks the derived
        # namespace from carrying compiler-named constants and literals.
        rows = self.entries(('N.Inv.a', 'N.Invariant.a', 'declaration', {}),
                            ('N.Inv.b', 'N.Invariant.b', 'declaration', {}))
        def run(stay):
            extra_b = {'N.Inv.c': constant(3)} if stay else {}
            self.before = snapshot({'N.Inv.a': constant(), 'N.Inv.b': constant(2), 'N.Inv.tacticFoo': constant(7),
                                    'gen': self.lit_kernel('N', 'Inv', 'tacticFoo'), **extra_b},
                                   ['N.Inv.a', 'N.Inv.b', *extra_b])
            self.after = snapshot({'N.Invariant.a': constant(), 'N.Invariant.b': constant(2),
                                   'N.Invariant.tacticFoo': constant(7),
                                   'gen': self.lit_kernel('N', 'Invariant', 'tacticFoo'), **extra_b},
                                  ['N.Invariant.a', 'N.Invariant.b', *extra_b])
            self.renames = rows
            return self.run_check()
        self.assertEqual(run(False)['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run(True)
        # A member whose own row renames its leaf inside the new namespace
        # still moves with it (the real Gloas.Inv -> Gloas.Invariant shape).
        rows = self.entries(('N.Inv.a', 'N.Invariant.a', 'declaration', {}),
                            ('N.Inv.b', 'N.Invariant.b', 'declaration', {}),
                            ('N.Inv.c', 'N.Invariant.charlie', 'declaration', {}))
        self.before = snapshot({'N.Inv.a': constant(), 'N.Inv.b': constant(2), 'N.Inv.c': constant(3),
                                'N.Inv.tacticFoo': constant(7), 'gen': self.lit_kernel('N', 'Inv', 'tacticFoo')},
                               ['N.Inv.a', 'N.Inv.b', 'N.Inv.c'])
        self.after = snapshot({'N.Invariant.a': constant(), 'N.Invariant.b': constant(2), 'N.Invariant.charlie': constant(3),
                               'N.Invariant.tacticFoo': constant(7), 'gen': self.lit_kernel('N', 'Invariant', 'tacticFoo')},
                              ['N.Invariant.a', 'N.Invariant.b', 'N.Invariant.charlie'])
        self.renames = rows
        self.assertEqual(self.run_check()['status'], 'OK')
        # The same holds for a literal naming the namespace itself (rule D).
        rows_only = lambda stay: (snapshot({'N.Inv.a': constant(), 'N.Inv.b': constant(2), 'gen': self.lit_kernel('N', 'Inv'),
                                            **({'N.Inv.c': constant(3)} if stay else {})},
                                           ['N.Inv.a', 'N.Inv.b'] + (['N.Inv.c'] if stay else [])),
                                  snapshot({'N.Invariant.a': constant(), 'N.Invariant.b': constant(2),
                                            'gen': self.lit_kernel('N', 'Invariant'), **({'N.Inv.c': constant(3)} if stay else {})},
                                           ['N.Invariant.a', 'N.Invariant.b'] + (['N.Inv.c'] if stay else [])))
        self.before, self.after = rows_only(False)
        self.assertEqual(self.run_check()['status'], 'OK')
        self.before, self.after = rows_only(True)
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()

    def test_dot_identifier_leaf_is_checked_on_every_resolution(self):
        # Finding 12: a reference recorded over the identifier's own range
        # that names another leaf is refused, as for the shifted range.
        with tempfile.TemporaryDirectory() as tmp:
            data = self.dot_export('#guard x = .reg', 'reg')
            start = '#guard x = .reg'.index('.reg')
            data['index']['references'][json.dumps({'c': {'m': 'M', 'n': 'N.T.div'}})] = dict(
                definition=None, usages=[[0, start + 1, 0, start + 4]])
            data['constants']['N.T.div'] = dict(constant(2), equation_origin=None)
            path = Path(tmp) / 'x.json'
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'dot identifier'):
                CHECK.read_exports([path])

    def test_module_named_auxiliaries_follow_module_rows(self):
        self.renames = self.entries(('N.old', 'N.new', 'declaration', {}), ('A.Mod', 'A.Module', 'module', {}))
        aux = 'N._aux_A_Mod___elabRules_N_tac_1.go'
        self.before = snapshot({'N.old': constant(), aux: constant(3)}, ['N.old', aux])
        self.after = snapshot({'N.new': constant(), aux.replace('A_Mod___', 'A_Module___'): constant(3)},
                              ['N.new', aux.replace('A_Mod___', 'A_Module___')])
        self.assertEqual(self.run_check()['status'], 'OK')
        # Control: without the module row the auxiliary's new name is a difference.
        self.renames = self.entries(('N.old', 'N.new', 'declaration', {}))
        with self.assertRaisesRegex(CHECK.Mismatch, 'authored constant set changed'):
            self.run_check()

    def test_unexported_generated_names_follow_their_parent(self):
        ref = lambda n: dict(kernel=['definition', 'safe', ['const', ['name', n], []]], attributes={})
        self.renames = self.entries(('N.old', 'N.new', 'declaration', {}))
        self.before = snapshot({'N.old': constant(), 'N.t': ref('N.old.match_8')}, ['N.old', 'N.t'])
        self.after = snapshot({'N.new': constant(), 'N.t': ref('N.new.match_8')}, ['N.new', 'N.t'])
        self.assertEqual(self.run_check()['status'], 'OK')
        # Control: a suffix that is not compiler-generated does not follow.
        self.before['constants']['N.t'] = ref('N.old.helper')
        self.after['constants']['N.t'] = ref('N.new.helper')
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()

    def test_generated_constants_keep_their_modules(self):
        self.before['constants']['gen'] = constant(5)
        self.after['constants']['gen2'] = constant(5)
        self.before['holders'], self.after['holders'] = {'gen': {'A'}}, {'gen2': {'A'}}
        self.assertEqual(self.run_check()['status'], 'OK')
        self.after['holders'] = {'gen2': {'B'}}
        with self.assertRaisesRegex(CHECK.Mismatch, "generated constant gen .*'A'.* became .*'B'"):
            self.run_check()

    def test_direct_imports_compare_under_module_rows(self):
        self.before['modules'] = {'A': [['Dep', False, False, False]], 'Dep': []}
        self.after['modules'] = {'A': [['NewDep', False, False, False]], 'NewDep': []}
        self.renames = self.entries(('N.old', 'N.new', 'declaration', {}), ('Dep', 'NewDep', 'module', {}))
        self.assertEqual(self.run_check()['status'], 'OK')
        self.after['modules']['A'].append(['Other', False, False, False])
        with self.assertRaisesRegex(CHECK.Mismatch, 'module A: direct imports changed'):
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

    def _reloc_split_case(self, leaf='match_1', third_module=False, bad_body=False,
                          instance_attr=None, extra_right=False, with_reloc=True):
        shared_b = 'N.moved.' + leaf
        copy_a = 'N.stay.' + leaf
        copy_b = 'N.moved.' + leaf
        b_consts = {
            'N.moved': constant(ref(shared_b)),
            'N.stay': constant(ref(shared_b)),
            shared_b: constant(7, dict(instance=instance_attr)) if instance_attr else constant(7),
        }
        a_consts = {
            'N.moved': constant(ref(copy_b)),
            'N.stay': constant(ref(copy_a)),
            copy_a: constant(7, dict(instance=instance_attr)) if instance_attr else constant(7),
            copy_b: constant(9 if bad_body else 7, dict(instance=instance_attr)) if instance_attr else constant(9 if bad_body else 7),
        }
        if extra_right:
            a_consts['N.stay.match_2'] = constant(8)
        self.before = snapshot(b_consts, ['N.moved', 'N.stay'])
        self.after = snapshot(a_consts, ['N.moved', 'N.stay'])
        self.before['owners'] = {'N.moved': 'A', 'N.stay': 'A'}
        self.after['owners'] = {'N.moved': 'B' if with_reloc else 'A', 'N.stay': 'A'}
        self.before['holders'] = {shared_b: {'A'}}
        self.after['holders'] = {copy_a: {'C' if third_module else 'A'}, copy_b: {'B'}}
        if extra_right:
            self.after['holders']['N.stay.match_2'] = {'A'}
        self.renames = self.entries(('N.moved', 'N.moved', 'relocation', dict(from_module='A', to_module='B'))) if with_reloc else self.entries()

    def test_relocation_auxiliary_split_across_linked_modules(self):
        for leaf in ('match_1', '_sparseCasesOn_1'):
            self._reloc_split_case(leaf=leaf)
            result = self.run_check()
            self.assertEqual(result['status'], 'OK')
            self.assertEqual(result['relocated_auxiliary_pairs'], 2)

    def test_relocation_auxiliary_split_controls_bite(self):
        # Controls: without relocation row, third module C, changed body, or instance attr all fail.
        for bad_kwargs in (dict(with_reloc=False), dict(third_module=True), dict(bad_body=True), dict(instance_attr='inst')):
            self._reloc_split_case(**bad_kwargs)
            with self.assertRaises(CHECK.Mismatch):
                self.run_check()

    def test_relocation_extra_unmatched_after_auxiliary_fails(self):
        self._reloc_split_case(extra_right=True)
        with self.assertRaisesRegex(CHECK.Mismatch, 'additional generated constants'):
            self.run_check()

    def test_promoted_private_matcher_reducibility_status(self):
        priv_f = '_private.A.0.N.f'
        priv_m = priv_f + '.match_1'
        self.before = snapshot({priv_f: constant(ref(priv_m)), priv_m: constant(7, dict(reducibility='Lean.ReducibilityStatus.semireducible'))}, [priv_f])
        self.after = snapshot({'N.f': constant(ref('N.f.match_1')), 'N.f.match_1': constant(7, dict(reducibility='Lean.ReducibilityStatus.instanceReducible'))}, ['N.f'])
        self.before['owners'], self.after['owners'] = {priv_f: 'A'}, {'N.f': 'B'}
        self.before['holders'], self.after['holders'] = {priv_m: {'A'}}, {'N.f.match_1': {'B'}}
        self.renames = self.entries(('N.f', 'N.f', 'relocation', dict(from_module='A', to_module='B', public_from=priv_f)))
        self.assertEqual(self.run_check()['status'], 'OK')
        # Without public_from or on a non-matcher suffix, semireducible -> instanceReducible fails.
        priv_p = priv_f + '.proof_1'
        self.before = snapshot({priv_f: constant(ref(priv_p)), priv_p: constant(7, dict(reducibility='Lean.ReducibilityStatus.semireducible'))}, [priv_f])
        self.after = snapshot({'N.f': constant(ref('N.f.proof_1')), 'N.f.proof_1': constant(7, dict(reducibility='Lean.ReducibilityStatus.instanceReducible'))}, ['N.f'])
        self.before['holders'], self.after['holders'] = {priv_p: {'A'}}, {'N.f.proof_1': {'B'}}
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()
        self.before = snapshot({priv_f: constant(ref(priv_m)), priv_m: constant(7, dict(reducibility='Lean.ReducibilityStatus.semireducible'))}, [priv_f])
        self.after = snapshot({'N.f': constant(ref('N.f.match_1')), 'N.f.match_1': constant(7, dict(reducibility='Lean.ReducibilityStatus.instanceReducible'))}, ['N.f'])
        self.before['holders'], self.after['holders'] = {priv_m: {'A'}}, {'N.f.match_1': {'B'}}
        self.renames = self.entries(('N.f', 'N.f', 'relocation', dict(from_module='A', to_module='B')))
        with self.assertRaisesRegex(CHECK.Mismatch, 'authored constant set'):
            self.run_check()

    def test_realized_relocated_matcher_behind_eq_def(self):
        priv_f = '_private.A.0.N.f'
        priv_m2 = priv_f + '.match_2'
        priv_eq = priv_f + '.eq_def'
        self.before = snapshot({priv_f: constant(ref(priv_m2)), priv_m2: constant(7), priv_eq: constant(ref(priv_m2))}, [priv_f])
        self.after = snapshot({'N.f': constant(ref('N.f.match_2')), 'N.f.match_2': constant(7), 'N.f.eq_def': constant(ref('N.f.match_3'))}, ['N.f'])
        self.before['owners'], self.after['owners'] = {priv_f: 'A'}, {'N.f': 'B'}
        self.before['holders'] = {priv_m2: {'A'}, priv_eq: {'A'}}
        self.after['holders'] = {'N.f.match_2': {'B'}, 'N.f.eq_def': {'A'}}
        self.renames = self.entries(('N.f', 'N.f', 'relocation', dict(from_module='A', to_module='B', public_from=priv_f)))
        self.assertEqual(self.run_check()['status'], 'OK')
        # Control: fails when exported N.f.match_2 has a different body or when N.f did not relocate.
        self.after['constants']['N.f.match_2'] = constant(99)
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()
        self.after['constants']['N.f.match_2'] = constant(7)
        self.before['roots'] = {priv_f}
        self.after['roots'] = {'N.f'}
        self.before['owners'], self.after['owners'] = {priv_f: 'A'}, {'N.f': 'A'}
        self.after['holders']['N.f.match_2'] = {'A'}
        self.renames = self.entries(('N.f', 'N.f', 'declaration', dict(public_from=priv_f)))
        with self.assertRaisesRegex(CHECK.Mismatch, 'no verified generated-constant match|generated reference'):
            self.run_check()

    def test_open_private_import_drop_under_public_from_and_controls(self):
        priv_f = '_private.A.0.N.f'
        self.before = snapshot({priv_f: constant()}, [priv_f])
        self.after = snapshot({'N.f': constant()}, ['N.f'])
        self.before['owners'], self.after['owners'] = {priv_f: 'A'}, {'N.f': 'B'}
        self.before['modules'] = {'A': [], 'C': [['A', False], ['Batteries.Tactic.OpenPrivate', False]]}
        self.after['modules'] = {'A': [], 'B': [], 'C': [['B', False]]}
        self.renames = self.entries(('N.f', 'N.f', 'relocation', dict(from_module='A', to_module='B', public_from=priv_f)))
        self.assertEqual(self.run_check()['status'], 'OK')
        # Control 1: dropping Batteries.Tactic.OpenPrivate without public_from fails.
        self.before = snapshot({'N.f': constant()}, ['N.f'])
        self.after = snapshot({'N.f': constant()}, ['N.f'])
        self.before['owners'], self.after['owners'] = {'N.f': 'A'}, {'N.f': 'B'}
        self.before['modules'] = {'A': [], 'C': [['A', False], ['Batteries.Tactic.OpenPrivate', False]]}
        self.after['modules'] = {'A': [], 'B': [], 'C': [['B', False]]}
        self.renames = self.entries(('N.f', 'N.f', 'relocation', dict(from_module='A', to_module='B')))
        with self.assertRaisesRegex(CHECK.Mismatch, 'direct imports changed'):
            self.run_check()
        # Control 2: adding Batteries.Tactic.OpenPrivate under public_from fails.
        self.before = snapshot({priv_f: constant()}, [priv_f])
        self.after = snapshot({'N.f': constant()}, ['N.f'])
        self.before['owners'], self.after['owners'] = {priv_f: 'A'}, {'N.f': 'B'}
        self.before['modules'] = {'A': [], 'C': [['A', False]]}
        self.after['modules'] = {'A': [], 'B': [], 'C': [['B', False], ['Batteries.Tactic.OpenPrivate', False]]}
        self.renames = self.entries(('N.f', 'N.f', 'relocation', dict(from_module='A', to_module='B', public_from=priv_f)))
        with self.assertRaisesRegex(CHECK.Mismatch, 'direct imports changed'):
            self.run_check()
        # Control 3: dropping another import under public_from fails.
        self.before['modules'] = {'A': [], 'C': [['A', False], ['Jaune.Other', False]]}
        self.after['modules'] = {'A': [], 'B': [], 'C': [['B', False]]}
        with self.assertRaisesRegex(CHECK.Mismatch, 'direct imports changed'):
            self.run_check()

    def test_downstream_realized_reloc_eq_matcher_and_controls(self):
        # Downstream module C realizes N.stay.eq_1 / _private.C.0.N.stay.match_5.eq_1
        # referencing shifted match_k of declarations in relocation component {A, B}.
        self.before = snapshot({
            'N.moved': constant(1),
            'N.stay': constant(ref('N.stay.match_1')),
            'N.stay.match_1': constant(10),
            'N.stay.match_3': constant(11),
            'N.stay.eq_1': constant(ref('N.stay.match_1')),
            '_private.C.0.N.stay.match_5.eq_1': constant(ref('N.stay.match_1')),
        }, ['N.moved', 'N.stay'])
        self.after = snapshot({
            'N.moved': constant(1),
            'N.stay': constant(ref('N.stay.match_1')),
            'N.stay.match_1': constant(10),
            'N.stay.match_3': constant(11),
            'N.stay.eq_1': constant(ref('N.stay.match_3')),
            '_private.C.0.N.stay.match_9.eq_1': constant(ref('N.stay.match_3')),
        }, ['N.moved', 'N.stay'])
        self.before['owners'] = {'N.moved': 'A', 'N.stay': 'A'}
        self.after['owners'] = {'N.moved': 'B', 'N.stay': 'A'}
        self.before['holders'] = {
            'N.stay.match_1': {'A'}, 'N.stay.match_3': {'A'},
            'N.stay.eq_1': {'C'}, '_private.C.0.N.stay.match_5.eq_1': {'C'},
        }
        self.after['holders'] = {
            'N.stay.match_1': {'A'}, 'N.stay.match_3': {'A'},
            'N.stay.eq_1': {'C'}, '_private.C.0.N.stay.match_9.eq_1': {'C'},
        }
        self.renames = self.entries(('N.moved', 'N.moved', 'relocation', dict(from_module='A', to_module='B')))
        self.assertEqual(self.run_check()['status'], 'OK')
        # Control (a): mutating another constant/payload inside eq_1 fails.
        self.after['constants']['N.stay.eq_1'] = constant([ref('N.stay.match_3'), ref('Nat')])
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()
        self.after['constants']['N.stay.eq_1'] = constant(ref('N.stay.match_3'))
        # Control (b): changing downstream holder C -> D fails.
        self.after['holders']['N.stay.eq_1'] = {'D'}
        with self.assertRaisesRegex(CHECK.Mismatch, "became \\['D'\\]"):
            self.run_check()
        self.after['holders']['N.stay.eq_1'] = {'C'}
        # Control (c): referencing a matcher in a non-relocated module Z fails.
        self.before['constants']['N.z'] = constant(1)
        self.after['constants']['N.z'] = constant(1)
        self.before['constants']['N.stay.eq_1'] = constant(ref('N.z.match_1'))
        self.before['roots'].add('N.z')
        self.after['roots'].add('N.z')
        self.before['owners']['N.z'], self.after['owners']['N.z'] = 'Z', 'Z'
        with self.assertRaisesRegex(CHECK.Mismatch, 'reference N.z.match_1 became N.stay.match_3'):
            self.run_check()
        # Control (d): changing matcher reference inside an authored consumer fails.
        self.before['constants']['N.stay.eq_1'] = constant(ref('N.stay.match_1'))
        self.before['constants']['N.consumer'] = constant(ref('N.stay.match_1'))
        self.after['constants']['N.consumer'] = constant(ref('N.stay.match_3'))
        self.before['roots'].add('N.consumer')
        self.after['roots'].add('N.consumer')
        self.before['owners']['N.consumer'], self.after['owners']['N.consumer'] = 'C', 'C'
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()

    def test_downstream_eq_prefers_same_holder_component_under_public_from(self):
        priv_f = '_private.A.0.N.f'
        self.before = snapshot({
            priv_f: constant(ref(priv_f + '.match_2')),
            priv_f + '.match_2': constant(10),
            '_private.A.0.N.f.match_2.eq_1': constant(ref(priv_f + '.match_2')),
            '_private.Bridge.0.N.f.match_3.eq_1': constant(ref(priv_f + '.match_3')),
        }, [priv_f])
        self.after = snapshot({
            'N.f': constant(ref('N.f.match_2')),
            'N.f.match_2': constant(10),
            '_private.A.0.N.f.match_3.eq_1': constant(ref('N.f.match_3')),
            '_private.Bridge.0.N.f.match_3.eq_1': constant(ref('N.f.match_3')),
        }, ['N.f'])
        self.before['owners'], self.after['owners'] = {priv_f: 'A'}, {'N.f': 'B'}
        self.before['holders'] = {
            priv_f + '.match_2': {'A'},
            '_private.A.0.N.f.match_2.eq_1': {'A'},
            '_private.Bridge.0.N.f.match_3.eq_1': {'Bridge'},
        }
        self.after['holders'] = {
            'N.f.match_2': {'B'},
            '_private.A.0.N.f.match_3.eq_1': {'A'},
            '_private.Bridge.0.N.f.match_3.eq_1': {'Bridge'},
        }
        self.renames = self.entries(('N.f', 'N.f', 'relocation', dict(from_module='A', to_module='B', public_from=priv_f)))
        self.assertEqual(self.run_check()['status'], 'OK')
        # Control: missing holder on Bridge still fails.
        self.after['holders']['_private.Bridge.0.N.f.match_3.eq_1'] = {'Other'}
        with self.assertRaisesRegex(CHECK.Mismatch, "became \\['Other'\\]"):
            self.run_check()

    def _schema8_file(self, path, source, decl_names, constants, expr_pool, level_pool=None, module='M'):
        decls = {}
        for dname in decl_names:
            leaf = dname.rsplit('.', 1)[-1]
            pos = source.index(leaf)
            prefix = source[:pos]
            line = prefix.count('\n')
            col = pos - (prefix.rfind('\n') + 1)
            decls[dname] = [line, col, line, col + len(leaf)]
        data = dict(
            schema_version=8,
            lean_version='fixture',
            import_modules=[],
            source=source,
            level_pool=level_pool if level_pool is not None else [],
            expr_pool=expr_pool,
            index=dict(version=5, module=module, directImports=[], decls=decls, references={},
                       naming_syntax=dict(version=2, commands=[], from_olean=True)),
            constants=constants,
            guards=[],
            attribute_syntax=[],
            checked_commands=[],
        )
        path.write_text(json.dumps(data))
        return path

    def test_schema8_pool_roundtrip_binder_info_and_let_nondep_controls(self):
        levels = [['zero'], ['succ', 0]]
        pool = [
            ['sort', 1],                                       # 0: Type
            ['const', ['name', 'Nat'], []],                    # 1: Nat
            ['bvar', 0],                                       # 2: #0
            ['nat', 0],                                        # 3: 0
            ['forall', 'Lean.BinderInfo.default', 1, 1],       # 4: Nat -> Nat
            ['forall', 'Lean.BinderInfo.implicit', 0, 4],      # 5: {α : Type} -> Nat -> Nat
            ['lam', 'Lean.BinderInfo.default', 1, 2],          # 6: fun (x : Nat) => x
            ['let', False, 1, 3, 2],                           # 7: let x : Nat := 0; x
            ['lam', 'Lean.BinderInfo.implicit', 1, 2],         # 8: fun {x : Nat} => x (mutation)
            ['forall', 'Lean.BinderInfo.default', 0, 4],       # 9: (α : Type) -> Nat -> Nat (mutation)
            ['let', True, 1, 3, 2],                            # 10: have x : Nat := 0; x (mutation)
        ]
        def defn(type_id, val_id):
            return dict(kernel=dict(universes=0, type=type_id, payload=['definition', 'Lean.DefinitionSafety.safe', val_id]),
                        attributes={}, equation_origin=None)
        mapping = dict(
            schema_version=1, retired_tokens=[], allowed_abbreviations=[],
            entries=[
                dict(old='N.old', new='N.new', kind='declaration', layer='execution', rule='4', source='t'),
                dict(old='N.old_let', new='N.new_let', kind='declaration', layer='execution', rule='4', source='t'),
            ])
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            b_path = self._schema8_file(
                root / 'b.json', 'def old := 0\ndef old_let := 0\n', ['N.old', 'N.old_let'],
                {'N.old': defn(5, 6), 'N.old_let': defn(4, 7)}, pool, levels)
            a_ok = self._schema8_file(
                root / 'a_ok.json', 'def new := 0\ndef new_let := 0\n', ['N.new', 'N.new_let'],
                {'N.new': defn(5, 6), 'N.new_let': defn(4, 7)}, pool, levels)
            self.assertEqual(CHECK.check(CHECK.read_exports([b_path]), CHECK.read_exports([a_ok]), mapping)['status'], 'OK')

            for label, after_consts in (
                ('lam-binder-info', {'N.new': defn(5, 8), 'N.new_let': defn(4, 7)}),
                ('forall-binder-info', {'N.new': defn(9, 6), 'N.new_let': defn(4, 7)}),
                ('let-nondep', {'N.new': defn(5, 6), 'N.new_let': defn(4, 10)}),
            ):
                with self.subTest(label=label):
                    a_bad = self._schema8_file(
                        root / f'{label}.json', 'def new := 0\ndef new_let := 0\n', ['N.new', 'N.new_let'],
                        after_consts, pool, levels)
                    with self.assertRaisesRegex(CHECK.Mismatch, 'kernel'):
                        CHECK.check(CHECK.read_exports([b_path]), CHECK.read_exports([a_bad]), mapping)

    def test_unreferenced_realized_theorem_holder_shift_and_biting_controls(self):
        def thm(type_expr, attrs=None):
            return dict(kernel=dict(type=type_expr, universes=0, payload=['theorem']),
                        attributes=attrs or {}, equation_origin=None)
        self.renames = self.entries()
        self.before = snapshot(
            {'N.f': constant(1), 'N.f.eq_1': thm(['nat', 1]), 'N.f._proof_1_1': thm(['nat', 1]),
             'N.f._simp_1_3': thm(['nat', 1])},
            ['N.f'])
        self.after = snapshot({'N.f': constant(1), 'N.f.eq_1': thm(['nat', 1])}, ['N.f'])
        self.before['owners'] = {'N.f': 'A', 'N.f.eq_1': 'A', 'N.f._proof_1_1': 'A', 'N.f._simp_1_3': 'A'}
        self.after['owners'] = {'N.f': 'A', 'N.f.eq_1': 'A'}
        self.before['holders'] = {'N.f': {'A'}, 'N.f.eq_1': {'A', 'B'}, 'N.f._proof_1_1': {'A'}, 'N.f._simp_1_3': {'A'}}
        self.after['holders'] = {'N.f': {'A'}, 'N.f.eq_1': {'A'}}
        verdict = self.run_check()
        self.assertEqual(verdict['status'], 'OK')
        self.assertIn('N.f.eq_1', verdict['ignored_unreferenced_realized_theorems']['before'])
        self.assertIn('N.f._proof_1_1', verdict['ignored_unreferenced_realized_theorems']['before'])
        self.assertIn('N.f._simp_1_3', verdict['ignored_unreferenced_realized_theorems']['before'])

        # Unreferenced realized theorem disappearing on one side also passes and is audited.
        self.after = snapshot({'N.f': constant(1)}, ['N.f'])
        self.after['owners'], self.after['holders'] = {'N.f': 'A'}, {'N.f': {'A'}}
        verdict2 = self.run_check()
        self.assertEqual(verdict2['status'], 'OK')
        self.assertEqual(verdict2['ignored_unreferenced_realized_theorems']['before'],
                         ['N.f._proof_1_1', 'N.f._simp_1_3', 'N.f.eq_1'])
        self.assertEqual(verdict2['ignored_unreferenced_realized_theorems']['after'], [])

        # Biting control A: referenced eq_1 / _proof_1 / _simp_1 with mutated statement MUST fail.
        for sym in ('N.f.eq_1', 'N.f._proof_1', 'N.f._simp_1'):
            with self.subTest(sym=sym):
                self.before = snapshot({'N.f': constant(1), 'N.user': constant(ref(sym)), sym: thm(['nat', 1])},
                                       ['N.f', 'N.user'])
                self.after = snapshot({'N.f': constant(1), 'N.user': constant(ref(sym)), sym: thm(['nat', 2])},
                                      ['N.f', 'N.user'])
                with self.assertRaises(CHECK.Mismatch):
                    self.run_check()

        # Biting control B: unreferenced @[simp] eq_1 with mutated type or holder shift MUST fail.
        self.before = snapshot({'N.f': constant(1), 'N.f.eq_1': thm(['nat', 1], {'simp': True})}, ['N.f'])
        self.after = snapshot({'N.f': constant(1), 'N.f.eq_1': thm(['nat', 2], {'simp': True})}, ['N.f'])
        self.before['holders'] = {'N.f': {'A'}, 'N.f.eq_1': {'A', 'B'}}
        self.after['holders'] = {'N.f': {'A'}, 'N.f.eq_1': {'A'}}
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()

    def test_shared_dag_reviewed_quotation_occurs_more_than_once_under_expr_eq_cache(self):
        def add_ident_pool(raw, parts, decl):
            pool = []
            def add(node):
                pool.append(node)
                return len(pool) - 1
            def mk_const(n):
                return add(['const', ['name', n], []])
            def mk_app(f, *xs):
                cur = f
                for x in xs:
                    cur = add(['app', cur, x])
                return cur
            def mk_name(ps):
                return mk_app(mk_const(f'Lean.Name.mkStr{len(ps)}'), *[add(['str', p]) for p in ps])
            t_id = mk_const('T')
            nil_t = mk_app(mk_const('List.nil'), t_id)
            nil_s = mk_app(mk_const('List.nil'), mk_const('String'))
            preres = mk_app(mk_const('Lean.Syntax.Preresolved.decl'), mk_name(decl.split('.')), nil_s)
            pre_list = mk_app(mk_const('List.cons'), t_id, preres, nil_t)
            raw_ss = mk_app(mk_const("String.toRawSubstring'"), add(['str', raw]))
            q_id = mk_app(mk_const('Lean.Syntax.ident'), mk_const('Lean.SourceInfo.none'),
                          raw_ss, mk_name(parts), pre_list)
            pair_id = mk_app(q_id, q_id)
            nat_id = mk_const('Nat')
            return pool, nat_id, q_id, pair_id

        mapping = CHECK.MAP.Renamer([dict(old='Jaune.B256', new='Jaune.U256', kind='declaration')])
        rec = dict(module='M', constant='N.m', before='B256', after='Jaune.U256', map_old='Jaune.B256',
                   map_new='Jaune.U256', decision='d', reason='r', precedent='p')
        b_pool, b_nat, b_q, b_pair = add_ident_pool('B256', ['B256'], 'Jaune.B256')
        a_pool, a_nat, a_q, a_pair = add_ident_pool('Jaune.U256', ['Jaune', 'U256'], 'Jaune.U256')
        def defn(t, v):
            return dict(kernel=dict(universes=0, type=t, payload=['definition', 'Lean.DefinitionSafety.safe', v]),
                        attributes={}, equation_origin=None)
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            b1 = self._schema8_file(root / 'b1.json', 'def m := 1\n', ['N.m'], {'N.m': defn(b_nat, b_q)}, b_pool)
            a1 = self._schema8_file(root / 'a1.json', 'def m := 1\n', ['N.m'], {'N.m': defn(a_nat, a_q)}, a_pool)
            used = set()
            verdict = CHECK.Comparison(CHECK.read_exports([b1]), CHECK.read_exports([a1]), mapping, [rec], used).run()
            self.assertEqual((verdict['status'], used), ('OK', {0}))

            # Duplicated shared DAG quotation q_id referenced twice via pair_id=['app', q_id, q_id]
            # must NOT bypass single-occurrence check under _expr_eq_cache.
            b2 = self._schema8_file(root / 'b2.json', 'def m := 1\n', ['N.m'], {'N.m': defn(b_nat, b_pair)}, b_pool)
            a2 = self._schema8_file(root / 'a2.json', 'def m := 1\n', ['N.m'], {'N.m': defn(a_nat, a_pair)}, a_pool)
            with self.assertRaisesRegex(CHECK.Mismatch, 'occurs more than once'):
                CHECK.Comparison(CHECK.read_exports([b2]), CHECK.read_exports([a2]), mapping, [rec], set()).run()

    def test_multi_index_match_suffix_and_holder_preference_under_swap(self):
        # Alphabetical order places Old.f < N.f; GENERATED_SUFFIX must handle
        # multi-index match_1_1 and holder preference must prevent cross-pairing
        # when Staging.f (in A, renamed to N.f) and N.f (in B, relocated to C
        # as Old.f) share identical match_1_1 helper bodies.
        self.renames = self.entries(
            ('Staging.f', 'N.f', 'declaration', {}),
            ('N.f', 'Old.f', 'relocation', dict(from_module='B', to_module='C')),
        )
        self.before = snapshot(
            {
                'Staging.f': constant(ref('Staging.f.match_1_1')),
                'Staging.f.match_1_1': constant(['nat', 5]),
                'N.f': constant(ref('N.f.match_1_1')),
                'N.f.match_1_1': constant(['nat', 5]),
            },
            ['Staging.f', 'N.f'],
        )
        self.after = snapshot(
            {
                'N.f': constant(ref('N.f.match_1_1')),
                'N.f.match_1_1': constant(['nat', 5]),
                'Old.f': constant(ref('Old.f.match_1_1')),
                'Old.f.match_1_1': constant(['nat', 5]),
            },
            ['N.f', 'Old.f'],
        )
        self.before['owners'] = {
            'Staging.f': 'A', 'Staging.f.match_1_1': 'A',
            'N.f': 'B', 'N.f.match_1_1': 'B',
        }
        self.after['owners'] = {
            'N.f': 'A', 'N.f.match_1_1': 'A',
            'Old.f': 'C', 'Old.f.match_1_1': 'C',
        }
        self.before['holders'] = {
            'Staging.f': {'A'}, 'Staging.f.match_1_1': {'A'},
            'N.f': {'B'}, 'N.f.match_1_1': {'B'},
        }
        self.after['holders'] = {
            'N.f': {'A'}, 'N.f.match_1_1': {'A'},
            'Old.f': {'C'}, 'Old.f.match_1_1': {'C'},
        }
        verdict = self.run_check()
        self.assertEqual(verdict['status'], 'OK')

        # Negative control: mutating Old.f.match_1_1 MUST fail even with Staging.f.match_1_1 identical.
        self.after['constants']['Old.f.match_1_1'] = constant(['nat', 6])
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()


    # --- U9 N4 extensions (master ruling R5): each admits only exact map images.

    @staticmethod
    def name_chain(name, heads=('Lean.Name.mkStr', 'Lean.Name.mkNum'), ofnat=False):
        e = ['const', ['name', 'Lean.Name.anonymous'], []]
        for part in name.split('.'):
            if part.isdigit():
                num = ['nat', int(part)]
                if ofnat:
                    num = ['app', ['app', ['app', ['const', ['name', 'OfNat.ofNat'], [0]], ['const', ['name', 'Nat'], []]],
                                   num], ['app', ['const', ['name', 'instOfNatNat'], []], num]]
                e = ['app', ['app', ['const', ['name', heads[1]], []], e], num]
            else:
                e = ['app', ['app', ['const', ['name', heads[0]], []], e], ['str', part]]
        return e

    def test_chained_private_name_literals_follow_the_map(self):
        # A private syntax kind's literal is a mkStr/mkNum chain (its `.0.`);
        # the module row and the namespace row rename it as they rename the kind.
        rows = self.entries(('N.Old', 'N.New', 'namespace', {}), ('M', 'M2', 'module', {}))
        kind_b, kind_a = '_private.M.0.N.Old.tac', '_private.M2.0.N.New.tac'
        def run(before_lit, after_lit, body=7, ofnat=False, head='Lean.ParserDescr.node', index=0):
            def parser(lit):
                fn = ['const', ['name', head], []]
                for _ in range(index):
                    fn = ['app', fn, ['bvar', 0]]
                return dict(kernel=['definition', 'safe', ['app', fn, self.name_chain(lit, ofnat=ofnat)]],
                            attributes={})
            self.before = snapshot({'N.Old.a': constant(), kind_b: constant(body), 'gen': parser(before_lit)}, ['N.Old.a'])
            self.after = snapshot({'N.New.a': constant(), kind_a: constant(7), 'gen': parser(after_lit)}, ['N.New.a'])
            self.renames = rows
            return self.run_check()
        verdict = run(kind_b, kind_a)
        self.assertEqual([r[1:] for r in verdict['derived_literals_respelled']],
                         [[kind_b, kind_a, 'chained name literal']])
        self.assertEqual(run(kind_b, kind_a, ofnat=True)['status'], 'OK')
        # Control: a respelling that is not the map image fails.
        with self.assertRaises(CHECK.Mismatch):
            run(kind_b, '_private.M2.0.N.Other.tac')
        # Control: the numeric component must stay (it is the chain's own numeral).
        with self.assertRaises(CHECK.Mismatch):
            run(kind_b, '_private.M2.1.N.New.tac')
        # Control: a literal left unrespelled fails.
        with self.assertRaises(CHECK.Mismatch):
            run(kind_b, kind_b)
        # Control: a body change beside the literal still fails.
        with self.assertRaises(CHECK.Mismatch):
            run(kind_b, kind_a, body=8)
        # R17: only where a quotation writes a chain (a pre-resolution or a
        # syntax kind). The same chain as an ordinary argument is data.
        for head in ('Lean.Syntax.node2', 'Lean.Syntax.isOfKind'):
            self.assertEqual(run(kind_b, kind_a, head=head, index=1)['status'], 'OK')
        for head, index in (('P.node', 0), ('Lean.Syntax.node2', 0), ('Lean.ParserDescr.node', 1)):
            self.assertEqual(run(kind_b, kind_b, head=head, index=index)['status'], 'OK')
            with self.assertRaises(CHECK.Mismatch):
                run(kind_b, kind_a, head=head, index=index)
        # Control: a rebuilt name may use only the chain's own numerals.
        _, numerals, heads = CHECK._name_chain(self.name_chain(kind_b))
        self.assertIsNotNone(CHECK._name_chain_expr(kind_a, numerals, heads))
        self.assertIsNone(CHECK._name_chain_expr('_private.M2.1.N.New.tac', numerals, heads))

    def test_hand_built_name_chains_are_data(self):
        # A mkStr chain that mkStrK could write is never a quotation: runtime data.
        lit = self.name_chain('N.old')
        self.assertIsNotNone(CHECK._name_chain(lit))
        self.assertFalse(CHECK._literal_chain(CHECK._name_chain(lit)))
        def gen(e):
            return dict(kernel=['definition', 'safe', e], attributes={})
        def run(after_name):
            self.before = snapshot({'N.old': constant(), 'N.m': gen(self.name_chain('N.old'))}, ['N.old', 'N.m'])
            self.after = snapshot({'N.new': constant(), 'N.m': gen(self.name_chain(after_name))}, ['N.new', 'N.m'])
            return self.run_check()
        # Data is compared as written: kept, it passes; respelled, it fails.
        self.assertEqual(run('N.old')['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run('N.new')
        # R17/R19: a constructor-form chain `mkStrK` could write is never a
        # literal; one `toExpr` writes in that form is only a candidate
        # (`'ctor'`, admitted with double-backtick evidence); a mixed chain
        # is refused.
        pattern = self.name_chain('N.old', heads=('Lean.Name.str', 'Lean.Name.num'))
        self.assertFalse(CHECK._literal_chain(CHECK._name_chain(pattern)))
        self.assertEqual(CHECK._literal_chain(CHECK._name_chain(
            self.name_chain('_private.M.0.N.old', heads=('Lean.Name.str', 'Lean.Name.num')))), 'ctor')
        mixed = self.name_chain('N.0.old', heads=('Lean.Name.str', 'Lean.Name.mkNum'))
        self.assertIsNone(CHECK._name_chain(mixed))

    def test_private_preresolution_decodes_numeric_components(self):
        chain = self.name_chain('_private.M.0.N.f')
        self.assertEqual(CHECK._name(chain), ['_private', 'M', '0', 'N', 'f'])
        self.assertEqual(CHECK._name(self.name_chain('_private.M.0.N.f', ofnat=True)), ['_private', 'M', '0', 'N', 'f'])
        decl = ['app', ['app', ['const', ['name', 'Lean.Syntax.Preresolved.decl'], []], chain],
                ['app', ['const', ['name', 'List.nil'], []], ['const', ['name', 'String'], []]]]
        self.assertEqual(CHECK._preresolved(decl), ['decl', ['name', '_private.M.0.N.f'], []])
        # Control: a numeric component that is not a literal does not decode.
        bad = ['app', ['app', ['const', ['name', 'Lean.Name.mkNum'], []], self.name_chain('M')], ['bvar', 0]]
        self.assertIsNone(CHECK._name(bad))

    # --- R17 hardening after the cross-family review (Neon finding 3).

    def gen_body(self, e):
        return dict(kernel=['definition', 'safe', e], attributes={})

    def test_constructor_form_name_chains_are_data(self):
        # Neon counterexample 1: `def tag : Name := .str (.str .anonymous "N") "old"`
        # under `N.old -> N.new` must not respell.
        ctor = ('Lean.Name.str', 'Lean.Name.num')
        def run(before_name, after_name, rows):
            self.before = snapshot({'N.old': constant(), 'N.Old.a': constant(2),
                                    'N.tag': self.gen_body(self.name_chain(before_name, heads=ctor))},
                                   ['N.old', 'N.Old.a', 'N.tag'])
            self.after = snapshot({'N.new': constant(), 'N.New.a': constant(2),
                                   'N.tag': self.gen_body(self.name_chain(after_name, heads=ctor))},
                                  ['N.new', 'N.New.a', 'N.tag'])
            self.renames = self.entries(*rows)
            return self.run_check()
        rows = [('N.old', 'N.new', 'declaration', {}), ('N.Old', 'N.New', 'namespace', {})]
        self.assertEqual(run('N.old', 'N.old', rows)['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run('N.old', 'N.new', rows)
        # Neon counterexample 2: a descendant of a namespace row naming nothing.
        self.assertEqual(run('N.Old.anything', 'N.Old.anything', rows)['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run('N.Old.anything', 'N.New.anything', rows)
        # A private name in constructor form is data too.
        with self.assertRaises(CHECK.Mismatch):
            run('_private.M.0.N.old', '_private.M.0.N.new', rows)
        # Even where a quotation would write a chain (a syntax kind), the
        # constructor form is not one: it stays as written.
        def at_site(before_name, after_name):
            kind = lambda n: self.gen_body(['app', ['const', ['name', 'Lean.ParserDescr.node'], []],
                                            self.name_chain(n, heads=ctor)])
            self.before = snapshot({'_private.M.0.N.old': constant(), 'N.k': kind(before_name)},
                                   ['_private.M.0.N.old', 'N.k'])
            self.after = snapshot({'_private.M.0.N.new': constant(), 'N.k': kind(after_name)},
                                  ['_private.M.0.N.new', 'N.k'])
            self.renames = self.entries(('N.old', 'N.new', 'declaration', {}))
            return self.run_check()
        self.assertEqual(at_site('_private.M.0.N.old', '_private.M.0.N.old')['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            at_site('_private.M.0.N.old', '_private.M.0.N.new')

    def test_double_backtick_private_literals_follow_the_map(self):
        # Master rulings R19/R20: ``helper`` of a private helper elaborates to a
        # constructor-form chain in the definition body; it respells to the
        # helper's image only by the compiler's resolved references to it in
        # the holder's own declaration span, at most once per reference.
        ctor = ('Lean.Name.str', 'Lean.Name.num')
        old, new = '_private.M.0.N.C.helper', '_private.M2.0.N.helper'
        rows = [('N.C', 'N', 'namespace', {}), ('M', 'M2', 'module', {})]
        chain = lambda n: self.name_chain(n, heads=ctor)
        pair = lambda a, b: ['app', ['app', ['const', ['name', 'Prod.mk'], []], a], b]
        def run(before_e, after_e, refs=((old, 'N.C.k', 20),), span=(10, 40), before_consts=None,
                after_consts=None, holder='N.C.k'):
            self.before = snapshot(dict({holder: self.gen_body(before_e)}, **(before_consts if before_consts is not None
                                                                             else {old: constant(3)})), [holder])
            image = holder.replace('N.C.', 'N.')
            self.after = snapshot(dict({image: self.gen_body(after_e)}, **(after_consts if after_consts is not None
                                                                         else {new: constant(3)})), [image])
            self.before['owners'] = {holder: 'M', old: 'M'}
            self.after['owners'] = {image: 'M2', new: 'M2'}
            self.before['module_sources'] = {'M': ' ' * 60}
            self.before['module_decls'] = {'M': {} if span is None else {holder: span}}
            self.before['module_references'] = {'M': [(c, by, at, at + 6) for c, by, at in refs]}
            self.renames = self.entries(*rows)
            return self.run_check()
        verdict = run(chain(old), chain(new))
        self.assertIn(['N.C.k', old, new, 'double-backtick name literal (compiler reference)'],
                      verdict['derived_literals_respelled'])
        # Neon-3 counterexample 1 (raw string `r#" ``helper "#`) and any other
        # hand-built chain: no compiler reference, no respelling.
        self.assertEqual(run(chain(old), chain(old), refs=())['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run(chain(old), chain(new), refs=())
        # Counterexample 2: ``zero resolved to `Nat.zero`, not to the local helper.
        with self.assertRaises(CHECK.Mismatch):
            run(chain(old), chain(new), refs=(('Nat.zero', 'N.C.k', 20),))
        # Counterexample 3: a holder without a recorded span (a generated
        # matcher `g.match_1`) is never admitted, even if another declaration
        # references the helper; no module-level fallback.
        with self.assertRaises(CHECK.Mismatch):
            run(chain(old), chain(new), refs=((old, 'N.C.unrelated', 20),), span=None)
        with self.assertRaises(CHECK.Mismatch):
            run(chain(old), chain(new), refs=((old, 'N.C.unrelated', 20),))
        with self.assertRaises(CHECK.Mismatch):
            run(chain(old), chain(new), span=None)
        # A reference outside the holder's span does not count.
        with self.assertRaises(CHECK.Mismatch):
            run(chain(old), chain(new), refs=((old, 'N.C.k', 50),))
        # Counterexample 4: a real literal and a hand-built chain in the same
        # declaration: two occurrences, one reference: neither respells.
        self.assertEqual(run(pair(chain(old), chain(old)), pair(chain(old), chain(old)))['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run(pair(chain(old), chain(old)), pair(chain(new), chain(new)))
        with self.assertRaises(CHECK.Mismatch):
            run(pair(chain(old), chain(old)), pair(chain(new), chain(old)))
        shared = chain(old)  # one DAG node on two paths is two occurrences
        with self.assertRaises(CHECK.Mismatch):
            run(pair(shared, shared), pair(chain(new), chain(new)))
        # Two references admit two occurrences.
        self.assertEqual(run(pair(chain(old), chain(old)), pair(chain(new), chain(new)),
                             refs=((old, 'N.C.k', 20), (old, 'N.C.k', 30)))['status'], 'OK')
        # (2) a chain naming no existing old constant, or whose image is no
        # after constant (checked on the whole-environment tables).
        missing = '_private.M.0.N.C.absent'
        self.assertEqual(run(chain(missing), chain(missing), refs=((missing, 'N.C.k', 20),))['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run(chain(missing), chain('_private.M2.0.N.absent'), refs=((missing, 'N.C.k', 20),))
        run(chain(old), chain(new))
        self.after['constants']['_private.M2.0.N.absent'] = constant(5)
        self.before['module_references'] = {'M': [(missing, 'N.C.k', 20, 26), (old, 'N.C.k', 30, 36)]}
        probe = CHECK.Comparison(self.before, self.after, self.renames)
        both = pair(chain(old), chain(missing))
        self.assertEqual(probe.compiler_reference_admissions('N.C.k', both), {old})
        del self.after['constants'][new]
        CHECK.Comparison._NAMESPACES.clear()
        probe = CHECK.Comparison(self.before, self.after, self.renames)
        self.assertEqual(probe.compiler_reference_admissions('N.C.k', both), frozenset())
        # (1) a constructor chain `toExpr` would write as `mkStrK` (simple, at
        # most eight string components) is data even with a reference.
        self.assertEqual(run(chain('N.C.pub'), chain('N.C.pub'), refs=(('N.C.pub', 'N.C.k', 20),),
                             before_consts={'N.C.pub': constant(3)}, after_consts={'N.pub': constant(3)})['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run(chain('N.C.pub'), chain('N.pub'), refs=(('N.C.pub', 'N.C.k', 20),),
                before_consts={'N.C.pub': constant(3)}, after_consts={'N.pub': constant(3)})

    def test_respell_cache_is_per_holder_for_contextual_chains(self):
        # Neon-3 finding 6: one shared chain node, data in one constant and a
        # quotation-site literal in another of the same module, must respell
        # in the second whatever the order the constants are visited.
        kind_b, kind_a = '_private.M.0.N.Old.tac', '_private.M2.0.N.New.tac'
        rows = self.entries(('N.Old', 'N.New', 'namespace', {}), ('M', 'M2', 'module', {}))
        for order in (('N.a', 'N.b'), ('N.b', 'N.a')):
            node_b, node_a = self.name_chain(kind_b), self.name_chain(kind_a)
            site = lambda n: self.gen_body(['app', ['const', ['name', 'Lean.ParserDescr.node'], []], n])
            data = lambda n: self.gen_body(['app', ['const', ['name', 'P.data'], []], n])
            before = {'N.Old.x': constant(), kind_b: constant(7)}
            before.update({k: (data(node_b) if k == 'N.a' else site(node_b)) for k in order})
            after = {'N.New.x': constant(), kind_a: constant(7), 'N.a': data(node_b), 'N.b': site(node_a)}
            self.before = snapshot(before, ['N.Old.x', 'N.a', 'N.b'])
            self.after = snapshot(after, ['N.New.x', 'N.a', 'N.b'])
            self.before['owners'] = {k: 'M' for k in before}
            self.after['owners'] = {k: 'M2' for k in after}
            self.assertEqual(CHECK.Comparison(self.before, self.after, rows).run()['status'], 'OK')

    def test_chained_literals_only_at_quotation_sites(self):
        # Neon counterexample 3: a toExpr-encoded chain (private, or over eight
        # components) in an ordinary definition body is runtime data; and the
        # inner prefix of a runtime chain is never decoded on its own.
        kind = '_private.M.0.N.Old.tac'
        rows = [('N.Old', 'N.New', 'namespace', {}), ('M', 'M2', 'module', {})]
        def run(before_e, after_e):
            self.before = snapshot({'N.Old.a': constant(), kind: constant(7), 'N.k': self.gen_body(before_e)},
                                   ['N.Old.a', 'N.k'])
            self.after = snapshot({'N.New.a': constant(), '_private.M2.0.N.New.tac': constant(7),
                                   'N.k': self.gen_body(after_e)}, ['N.New.a', 'N.k'])
            self.renames = self.entries(*rows)
            return self.run_check()
        new = '_private.M2.0.N.New.tac'
        self.assertEqual(run(self.name_chain(kind), self.name_chain(kind))['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run(self.name_chain(kind), self.name_chain(new))
        dyn = lambda e: ['app', ['app', ['const', ['name', 'Lean.Name.mkStr'], []], e], ['bvar', 0]]
        self.assertEqual(run(dyn(self.name_chain(kind)), dyn(self.name_chain(kind)))['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run(dyn(self.name_chain(kind)), dyn(self.name_chain(new)))

    def test_chained_literals_name_an_existing_constant_or_namespace(self):
        # Rule D for a chain (R17): the before chain names a constant or a
        # namespace before, and its image one after. Nine components force a chain.
        long_old, long_new = 'N.Old.a.b.c.d.e.f.g', 'N.New.a.b.c.d.e.f.g'
        def run(after_lit, exists):
            parser = lambda lit: self.gen_body(['app', ['const', ['name', 'Lean.ParserDescr.node'], []],
                                                self.name_chain(lit)])
            before = {'N.Old.x': constant(), 'gen': parser(long_old)}
            after = {'N.New.x': constant(), 'gen': parser(after_lit)}
            if exists:
                before[long_old + '.h'], after[long_new + '.h'] = constant(3), constant(3)
            self.before = snapshot(before, ['N.Old.x'] + ([long_old + '.h'] if exists else []))
            self.after = snapshot(after, ['N.New.x'] + ([long_new + '.h'] if exists else []))
            self.renames = self.entries(('N.Old', 'N.New', 'namespace', {}))
            return self.run_check()
        self.assertEqual(run(long_new, exists=True)['status'], 'OK')
        self.assertEqual(run(long_old, exists=False)['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run(long_new, exists=False)

    def test_name_and_numeral_decoding_are_exact(self):
        nat = ['const', ['name', 'Nat'], []]
        def ofnat(n, ty=nat, inst='instOfNatNat', m=None):
            return ['app', ['app', ['app', ['const', ['name', 'OfNat.ofNat'], [0]], ty], ['nat', n]],
                    ['app', ['const', ['name', inst], []], ['nat', n if m is None else m]]]
        self.assertEqual(CHECK._numeral(['nat', 0]), 0)
        self.assertEqual(CHECK._numeral(ofnat(3)), 3)
        self.assertIsNone(CHECK._numeral(ofnat(3, inst='evilInst')))
        self.assertIsNone(CHECK._numeral(ofnat(3, ty=['const', ['name', 'Int'], []])))
        self.assertIsNone(CHECK._numeral(ofnat(3, m=4)))
        self.assertIsNone(CHECK._numeral(['nat', -1]))
        # `Name.str p "0"` never reads as `Name.num p 0`.
        self.assertIsNone(CHECK._name(self.mkstr('foo', '0')))
        self.assertEqual(CHECK._name(self.name_chain('foo.0')), ['foo', '0'])
        str0 = ['app', ['app', ['const', ['name', 'Lean.Name.str'], []], self.mkstr('foo')], ['str', '0']]
        self.assertIsNone(CHECK._name(str0))
        # Neon finding 3.2 end to end: an identifier whose value changes from
        # `foo.«0»` to `foo.0`, or whose numeral instance changes, fails.
        def ident(val):
            info = ['const', ['name', 'Lean.SourceInfo.none'], []]
            raw = ['app', ['const', ['name', 'String.toRawSubstring'], []], ['str', 'foo.0']]
            pre = ['app', ['const', ['name', 'List.nil'], [['zero']]], ['const', ['name', 'Lean.Syntax.Preresolved'], []]]
            return ['app', ['app', ['app', ['app', ['const', ['name', 'Lean.Syntax.ident'], []], info], raw], val], pre]
        num = lambda n: ['app', ['app', ['const', ['name', 'Lean.Name.mkNum'], []], self.mkstr('foo')], n]
        def run(before_val, after_val):
            self.before = snapshot({'N.old': constant(), 'N.k': self.gen_body(ident(before_val))}, ['N.old', 'N.k'])
            self.after = snapshot({'N.new': constant(), 'N.k': self.gen_body(ident(after_val))}, ['N.new', 'N.k'])
            self.before['constants'] = {k: CHECK.quoted_identifiers(v) for k, v in self.before['constants'].items()}
            self.after['constants'] = {k: CHECK.quoted_identifiers(v) for k, v in self.after['constants'].items()}
            return self.run_check()
        self.assertEqual(run(num(ofnat(0)), num(ofnat(0)))['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run(self.mkstr('foo', '0'), num(ofnat(0)))
        with self.assertRaises(CHECK.Mismatch):
            run(num(ofnat(0, inst='instA')), num(ofnat(0, inst='instB')))

    @staticmethod
    def mkstr(*parts):
        e = ['const', ['name', f'Lean.Name.mkStr{len(parts)}'], []]
        for part in parts:
            e = ['app', e, ['str', part]]
        return e

    def union_audit(self, prefix):
        return ['syntax', 'Jaune.AxiomAudit.unionAxiomsOfModules',
                [['atom', '#union_axioms_of_modules'], ['name', prefix], ['syntax', 'null', []]]]

    def test_union_audit_prefix_follows_module_rows_with_its_population(self):
        rows = self.entries(('N.old', 'N.new', 'declaration', {}), ('P', 'P2', 'module', {}),
                            ('P.X', 'P2.X', 'module', {}), ('A', 'B', 'module', {}))
        def run(after_prefix, after_imports, before_imports=('P', 'P.X', 'Q')):
            self.setUp()
            self.before['checks'], self.after['checks'] = [self.union_audit('P')], [self.union_audit(after_prefix)]
            self.before['item_modules'], self.after['item_modules'] = {'checks': ['A']}, {'checks': ['B']}
            self.before['import_modules'] = {'A': list(before_imports)}
            self.after['import_modules'] = {'B': list(after_imports)}
            self.renames = rows
            return self.run_check()
        verdict = run('P2', ['P2', 'P2.X', 'Q'])
        self.assertIn(['A', 'P', 'P2', 'union audit module prefix'], verdict['derived_literals_respelled'])
        # Control: a literal that is not the module row's image fails.
        with self.assertRaises(CHECK.Mismatch):
            run('P3', ['P2', 'P2.X', 'Q'])
        # Control: the after population gained a module the rows do not account for.
        with self.assertRaises(CHECK.Mismatch):
            run('P2', ['P2', 'P2.X', 'P2.Z', 'Q'])
        # Control: a module under the prefix that the rows leave behind.
        with self.assertRaises(CHECK.Mismatch):
            run('P2', ['P2', 'P2.X', 'Q'], before_imports=('P', 'P.X', 'P.Y', 'Q'))
        # Control: without import records the literal is compared as written.
        self.setUp()
        self.before['checks'], self.after['checks'] = [self.union_audit('P')], [self.union_audit('P2')]
        self.before['item_modules'], self.after['item_modules'] = {'checks': ['A']}, {'checks': ['B']}
        self.renames = rows
        with self.assertRaises(CHECK.Mismatch):
            self.run_check()

    def test_union_audit_prefix_is_never_mapped_twice_or_moved(self):
        # Neon finding 2, R17: each counterexample now fails.
        def run(rows, before_check, after_check, before_imports, after_imports,
                before_owner='Audit', after_owner='Audit', extra_after=None):
            self.setUp()
            self.before['checks'], self.after['checks'] = [self.union_audit(before_check)], [self.union_audit(after_check)]
            self.before['item_modules'] = {'checks': [before_owner]}
            self.after['item_modules'] = {'checks': [after_owner]}
            self.before['import_modules'] = {'Audit': list(before_imports), 'Other': ['Q']}
            self.after['import_modules'] = dict({'Audit': list(after_imports), 'Other': ['Q']}, **(extra_after or {}))
            self.renames = self.entries(('N.old', 'N.new', 'declaration', {}), *rows)
            return self.run_check()
        # 2.1: a namespace row `Jaune.Checked -> Jaune` must not stand in for a
        # population check that failed (B dropped from the audit).
        ns = [('Jaune.Checked', 'Jaune', 'namespace', {}),
              ('Jaune.Checked.A', 'Jaune.A', 'module', {}), ('Jaune.Checked.B', 'Jaune.B', 'module', {})]
        with self.assertRaises(CHECK.Mismatch):
            run(ns, 'Jaune.Checked', 'Jaune', ['Jaune.Checked.A', 'Jaune.Checked.B'], ['Jaune.A'])
        # 2.2: a module row `ModA -> Foo` and a declaration row `Foo -> Bar`:
        # the prefix is `Foo` after, never `Bar` (which audits nothing).
        twice = [('ModA', 'Foo', 'module', {}), ('Foo', 'Bar', 'declaration', {})]
        with self.assertRaises(CHECK.Mismatch):
            run(twice, 'ModA', 'Bar', ['ModA'], ['Foo'])
        self.assertEqual(run(twice, 'ModA', 'Foo', ['ModA'], ['Foo'])['status'], 'OK')
        # 2.3: a relocation component must not move the check to a module with
        # fewer imports (`B` audits `P2` without `P2.X`).
        reloc = [('P', 'P2', 'module', {}), ('P.X', 'P2.X', 'module', {}),
                 ('N.f', 'N.f', 'relocation', dict(from_module='Audit', to_module='Other'))]
        def relocated(after_owner, other_imports):
            self.setUp()
            self.before['constants']['N.f'] = self.after['constants']['N.f'] = constant(3)
            self.before['roots'].add('N.f')
            self.after['roots'].add('N.f')
            self.before['owners'] = {'N.old': 'Audit', 'N.f': 'Audit'}
            self.after['owners'] = {'N.new': 'Audit', 'N.f': 'Other'}
            self.before['checks'], self.after['checks'] = [self.union_audit('P')], [self.union_audit('P2')]
            self.before['item_modules'] = {'checks': ['Audit']}
            self.after['item_modules'] = {'checks': [after_owner]}
            self.before['import_modules'] = {'Audit': ['P', 'P.X'], 'Other': ['P2']}
            self.after['import_modules'] = {'Audit': ['P2', 'P2.X'], 'Other': other_imports}
            self.renames = self.entries(('N.old', 'N.new', 'declaration', {}), *reloc)
            return self.run_check()
        self.assertEqual(relocated('Audit', ['P2'])['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            relocated('Other', ['P2'])
        # An unrenamed prefix whose population the module rows change fails too.
        moved = [('Q.X', 'R.X', 'module', {})]
        with self.assertRaises(CHECK.Mismatch):
            run(moved, 'Q', 'Q', ['Q', 'Q.X'], ['Q', 'R.X'])
        self.assertEqual(run(moved, 'Q', 'Q', ['Q', 'Q.Y'], ['Q', 'Q.Y'])['status'], 'OK')
        # The population is read on a dot boundary: `PX` is not under `P`.
        dot = [('P', 'P2', 'module', {}), ('PX', 'PX2', 'module', {})]
        self.assertEqual(run(dot, 'P', 'P2', ['P', 'PX'], ['P2', 'PX2'])['status'], 'OK')
        # A renamed prefix with an empty population is refused.
        with self.assertRaises(CHECK.Mismatch):
            run([('P', 'P2', 'module', {})], 'P', 'P2', ['Q'], ['Q'])

    def test_guard_msgs_field_notation_follows_constructor_and_method_rows(self):
        ctor = lambda: dict(kernel=dict(type=['const', ref('N.Op'), []], universes=0,
                                        payload=['constructor', ref('N.Op'), 0, 0, 0, False]), attributes={})
        def method(value, domain='N.Op', binder='Lean.BinderInfo.default'):
            # `def Op.rinst {α : Type} (o : Op) : Nat`: Op is the first explicit argument.
            ty = ['forall', 'Lean.BinderInfo.implicit', ['sort', 1],
                  ['forall', binder, ['const', ref(domain), []], ['const', ref('Nat'), []]]]
            return dict(kernel=dict(type=ty, universes=0, payload=['definition', value]), attributes={})
        def run(after_text, rows=None, add=ctor, rinst=lambda: method(2)):
            self.before = snapshot({'N.Op': constant(5), 'N.Op.add': add(), 'N.Op.rinst': rinst()},
                                   ['N.Op', 'N.Op.add', 'N.Op.rinst'])
            self.after = snapshot({'N.Op': constant(5), 'N.Op.plus': add(), 'N.Op.toPlain': rinst()},
                                  ['N.Op', 'N.Op.plus', 'N.Op.toPlain'])
            self.renames = self.entries(*(rows or [('N.Op.add', 'N.Op.plus', 'declaration', {}),
                                                   ('N.Op.rinst', 'N.Op.toPlain', 'declaration', {})]))
            self.before['checks'] = self.guard('error: Op.add.rinst x-/')
            self.after['checks'] = self.guard(after_text)
            return self.run_check()
        self.assertEqual(run('error: Op.plus.toPlain x-/')['status'], 'OK')
        # Control: the field part must follow the method's row.
        with self.assertRaises(CHECK.Mismatch):
            run('error: Op.plus.rinst x-/')
        with self.assertRaises(CHECK.Mismatch):
            run('error: Op.add.toPlain x-/')
        # Control: a change beyond the respelling still fails.
        with self.assertRaises(CHECK.Mismatch):
            run('error: Op.plus.toPlain y-/')
        # Control: `P` that is not a constructor gives no field respelling.
        with self.assertRaises(CHECK.Mismatch):
            run('error: Op.plus.toPlain x-/', add=lambda: constant(3))
        # R17 (Neon finding 8.2): `T.f` must take a `T` as its first explicit
        # argument; a constant of T's namespace that does not is no method.
        self.assertEqual(run('error: Op.add.rinst x-/', rinst=lambda: constant(2))['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run('error: Op.plus.toPlain x-/', rinst=lambda: constant(2))
        with self.assertRaises(CHECK.Mismatch):
            run('error: Op.plus.toPlain x-/', rinst=lambda: method(2, domain='Nat'))
        with self.assertRaises(CHECK.Mismatch):
            run('error: Op.plus.toPlain x-/', rinst=lambda: method(2, binder='Lean.BinderInfo.instImplicit'))
        # Finding 8.1: when `P` may also denote a constant that is no
        # constructor, the token stays as written, whatever the set order.
        self.before = snapshot({'N.Op': constant(5), 'N.Op.add': ctor(), 'N.Op.rinst': method(2),
                                'M.Op.add': constant(4)}, ['N.Op', 'N.Op.add', 'N.Op.rinst', 'M.Op.add'])
        rows = [('N.Op.add', 'N.Op.plus', 'declaration', {}), ('N.Op.rinst', 'N.Op.toPlain', 'declaration', {})]
        comparison = CHECK.Comparison(self.before, self.before, self.entries(*rows))
        self.assertEqual(comparison.respell_message('Op.add.rinst', 'guard_msgs'), 'Op.add.rinst')
        # Control: a method moved out of the type's namespace gives none either
        # (`rinst` is a genuine method, so the namespace check is what decides; R20).
        self.before = snapshot({'N.Op': constant(5), 'N.Op.add': ctor(), 'N.Op.rinst': method(2)},
                               ['N.Op', 'N.Op.add', 'N.Op.rinst'])
        comparison = CHECK.Comparison(self.before, self.before, self.entries(
            ('N.Op.add', 'N.Op.plus', 'declaration', {}), ('N.Op.rinst', 'N.Other.toPlain', 'declaration', {})))
        self.assertEqual(comparison.respell_message('Op.add.rinst', 'guard_msgs'), 'Op.add.rinst')

    def test_root_declaration_ids_spell_the_whole_name(self):
        def spelled(text, name):
            source = f'theorem {text} : True'
            return CHECK.spelled_name(source, 8, 8 + len(text), name)
        self.assertTrue(spelled('_root_.N.B.f', '_private.M.0.N.B.f'))
        self.assertTrue(spelled('_root_.N.B.f', 'N.B.f'))
        self.assertTrue(spelled('B.f', 'N.B.f'))
        # Control: under `_root_` a suffix is not enough, and other names fail.
        self.assertFalse(spelled('_root_.B.f', 'N.B.f'))
        self.assertFalse(spelled('_root_.N.B.g', 'N.B.f'))
        self.assertFalse(spelled('_root_', 'N.B.f'))


    @staticmethod
    def preresolved_list(*names, element='Lean.Syntax.Preresolved'):
        T = ['const', ['name', element], []]
        out = ['app', ['const', ['name', 'List.nil'], [['zero']]], T]
        for n in reversed(names):
            parts = n.split('.')
            lit = ['const', ['name', f'Lean.Name.mkStr{len(parts)}'], []]
            for part in parts:
                lit = ['app', lit, ['str', part]]
            entry = ['app', ['const', ['name', 'Lean.Syntax.Preresolved.namespace'], []], lit]
            out = ['app', ['app', ['app', ['const', ['name', 'List.cons'], [['zero']]], T], entry], out]
        return out

    @staticmethod
    def hygiene_ident(pre, val=None, scoped=True):
        """`Lean.Syntax.ident info raw v pre` as a quotation writes its
        hygiene ident: `v` = `Lean.addMacroScope m Name.anonymous s`."""
        anonymous = ['const', ['name', 'Lean.Name.anonymous'], []]
        if val is None:
            val = (['app', ['app', ['app', ['const', ['name', 'Lean.addMacroScope'], []], ['bvar', 0]], anonymous],
                    ['bvar', 1]] if scoped else anonymous)
        info = ['const', ['name', 'Lean.SourceInfo.none'], []]
        raw = ['app', ['const', ['name', 'String.toRawSubstring'], []], ['str', '']]
        return ['app', ['app', ['app', ['app', ['const', ['name', 'Lean.Syntax.ident'], []], info], raw], val], pre]

    def test_preresolved_lists_drop_only_duplicates_the_map_made(self):
        # Master ruling R12: `namespace A.C` + `open A` pre-resolve to
        # [A.C, ..., A]; merged into `A` (and `open A` dropped) the after
        # list is [A, ...]. A later duplicate never changes resolution.
        rows = self.entries(('A.C', 'A', 'namespace', {}), ('A.C.R.x', 'A.R.x', 'declaration', {}))
        def run(before, after, element='Lean.Syntax.Preresolved'):
            gen = lambda names: dict(kernel=['definition', 'safe', self.hygiene_ident(
                self.preresolved_list(*names, element=element))], attributes={})
            self.before = snapshot({'A.C.R.x': constant(), 'gen': gen(before)}, ['A.C.R.x'])
            self.after = snapshot({'A.R.x': constant(), 'gen': gen(after)}, ['A.R.x'])
            self.renames = rows
            return self.run_check()
        # Two levels, three levels, and a duplicate that is not adjacent.
        verdict = run(['A.C', 'A'], ['A'])
        self.assertIn('preresolved duplicate removed (R12)', [r[3] for r in verdict['derived_literals_respelled']])
        self.assertEqual(run(['A.C.R', 'A.C', 'A'], ['A.R', 'A'])['status'], 'OK')
        self.assertEqual(run(['A.C', 'B.M', 'B', 'A'], ['A', 'B.M', 'B'])['status'], 'OK')
        # Lists of equal length are compared as they are: no removal.
        self.assertEqual(run(['A.C', 'A'], ['A', 'A'])['status'], 'OK')
        # A duplicate already present before the rename stays.
        self.assertEqual(run(['A', 'A', 'A.C'], ['A', 'A'])['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run(['A', 'A', 'A.C'], ['A'])
        with self.assertRaises(CHECK.Mismatch):
            run(['A', 'A', 'B'], ['A', 'B'])
        # Control: removing an entry that is no duplicate fails.
        with self.assertRaises(CHECK.Mismatch):
            run(['A.C', 'B'], ['A'])
        # Control: reordering fails.
        with self.assertRaises(CHECK.Mismatch):
            run(['A.C', 'B', 'A'], ['B', 'A'])
        # Control: the after side never loses or gains by this rule.
        with self.assertRaises(CHECK.Mismatch):
            run(['A'], ['A', 'A'])
        with self.assertRaises(CHECK.Mismatch):
            run(['A.C', 'A'], ['A', 'A', 'A'])
        with self.assertRaises(CHECK.Mismatch):
            run(['A.C', 'A'], [])
        # Control: only a list of `Lean.Syntax.Preresolved` is a candidate set.
        with self.assertRaises(CHECK.Mismatch):
            run(['A.C', 'A'], ['A'], element='Lean.Name')
        # Control: a namespace the rows do not merge is no duplicate.
        with self.assertRaises(CHECK.Mismatch):
            run(['A.D', 'A'], ['A'])

    def test_preresolved_lists_drop_prefixes_of_the_current_namespace(self):
        # Master ruling R12b: inside `namespace N.C` + `open N` (+ `namespace R`)
        # the list is [N.C.R, ..., N]; merged into `N` with the `open` dropped,
        # `N` is a proper prefix of the current namespace `N.R` and implicitly open.
        rows = self.entries(('N.C', 'N', 'namespace', {}), ('N.C.R.x', 'N.R.x', 'declaration', {}),
                            ('Jaune.C', 'Jaune', 'namespace', {}), ('Jaune.C.R.y', 'Jaune.R.y', 'declaration', {}))
        def run(before, after):
            gen = lambda names: dict(kernel=['definition', 'safe', self.hygiene_ident(self.preresolved_list(*names))],
                                     attributes={})
            self.before = snapshot({'N.C.R.x': constant(), 'Jaune.C.R.y': constant(2), 'gen': gen(before)},
                                   ['N.C.R.x', 'Jaune.C.R.y'])
            self.after = snapshot({'N.R.x': constant(), 'Jaune.R.y': constant(2), 'gen': gen(after)},
                                  ['N.R.x', 'Jaune.R.y'])
            self.renames = rows
            return self.run_check()
        self.assertEqual(run(['N.C.R', 'L.M', 'L', 'N'], ['N.R', 'L.M', 'L'])['status'], 'OK')
        self.assertEqual(run(['N.C.R', 'N'], ['N.R'])['status'], 'OK')
        # Equal length: nothing drops.
        self.assertEqual(run(['N.C.R', 'N'], ['N.R', 'N'])['status'], 'OK')
        # Control: an entry that is not a prefix of the current namespace stays.
        with self.assertRaises(CHECK.Mismatch):
            run(['N.C.R', 'M'], ['N.R'])
        # Control: a prefix must end on a dot boundary.
        with self.assertRaises(CHECK.Mismatch):
            run(['Jaune.C.R', 'Jau'], ['Jaune.R'])
        # Control: only the current namespace (the first entry, kept in place on
        # both sides) implies its prefixes.
        with self.assertRaises(CHECK.Mismatch):
            run(['L', 'N.C.R', 'N'], ['L', 'N.R'])
        with self.assertRaises(CHECK.Mismatch):
            run(['N.C.R', 'N'], ['N'])
        # Control: the first entry itself never drops.
        with self.assertRaises(CHECK.Mismatch):
            run(['N.C.R', 'L'], ['L'])
        # Control: an entry already equal to the current namespace before stays.
        with self.assertRaises(CHECK.Mismatch):
            run(['N.C.R', 'N.C.R', 'N'], ['N.R'])
        # The checks that the first entry keeps its place, that the dropped entry
        # differed from it before the rename, and that the first entry never
        # drops are implied by the proper-prefix condition with the entrywise
        # comparison (entry 0 never drops, so the after list must start with it;
        # an entry equal before has an equal image, never a proper prefix). They
        # are kept as defence in depth; no mutation of them alone can bite.

    def test_preresolved_rules_apply_only_to_hygiene_idents_the_map_touched(self):
        # Neon finding 1, R17. Each counterexample now fails.
        def run(before, after, rows, wrap=None):
            wrap = wrap or self.hygiene_ident
            gen = lambda names: dict(kernel=['definition', 'safe', wrap(self.preresolved_list(*names))], attributes={})
            self.before = snapshot({'A.C.R.x': constant(), 'f': gen(before)}, ['A.C.R.x', 'f'])
            self.after = snapshot({'A.R.x': constant(), 'f': gen(after)}, ['A.R.x', 'f'])
            self.renames = self.entries(('A.C.R.x', 'A.R.x', 'declaration', {}), *rows)
            return self.run_check()
        merge = [('A.C', 'A', 'namespace', {})]
        # The rules still admit the hygiene case they were made for, with or
        # without a macro scope on the anonymous value.
        self.assertEqual(run(['A.C', 'A'], ['A'], merge)['status'], 'OK')
        self.assertEqual(run(['A.C', 'A'], ['A'], merge, wrap=lambda l: self.hygiene_ident(l, scoped=False))['status'], 'OK')
        # Counterexample 1.1: a bare list in a definition body (`([..]).length`),
        # under an empty map: R12b no longer drops `A`.
        bare = lambda l: ['app', ['const', ['name', 'List.length'], []], l]
        with self.assertRaises(CHECK.Mismatch):
            run(['A.B', 'A'], ['A.B'], [], wrap=bare)
        with self.assertRaises(CHECK.Mismatch):
            run(['A.C', 'A'], ['A'], merge, wrap=bare)
        # ... nor inside a hygiene ident the map did not touch.
        with self.assertRaises(CHECK.Mismatch):
            run(['A.B', 'A'], ['A.B'], [])
        # Counterexample 1.2a: a quoted identifier naming a namespace (`open B`
        # inside `namespace A.B` with `open A`): its value is not anonymous.
        named = lambda l: self.hygiene_ident(l, val=self.mkstr('B'))
        with self.assertRaises(CHECK.Mismatch):
            run(['A.B.B', 'A.B'], ['A.B.B'], [])
        with self.assertRaises(CHECK.Mismatch):
            run(['A.C.B', 'A'], ['A.B'], merge, wrap=named)

    def test_preresolved_prefix_rule_checks_the_before_side_and_duplicates(self):
        # Neon finding 1.2b: under `Old -> N.R`, `[Old, L, N]` -> `[N.R, L]`:
        # `N` was no prefix of `Old` before, so it was an ordinary open.
        rows = self.entries(('Old', 'N.R', 'namespace', {}), ('Old.x', 'N.R.x', 'declaration', {}),
                            ('N.C', 'N', 'namespace', {}), ('N.C.R.y', 'N.R.y', 'declaration', {}))
        def run(before, after):
            gen = lambda names: dict(kernel=['definition', 'safe', self.hygiene_ident(self.preresolved_list(*names))],
                                     attributes={})
            self.before = snapshot({'Old.x': constant(), 'N.C.R.y': constant(2), 'g': gen(before)}, ['Old.x', 'N.C.R.y'])
            self.after = snapshot({'N.R.x': constant(), 'N.R.y': constant(2), 'g': gen(after)}, ['N.R.x', 'N.R.y'])
            self.renames = rows
            return self.run_check()
        self.assertEqual(run(['N.C.R', 'L', 'N'], ['N.R', 'L'])['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run(['Old', 'L', 'N'], ['N.R', 'L'])
        # Finding 1.3: a duplicate already present before is never dropped by R12b.
        with self.assertRaises(CHECK.Mismatch):
            run(['N.C.R', 'N', 'N'], ['N.R', 'N'])
        with self.assertRaises(CHECK.Mismatch):
            run(['N.C.R', 'N', 'N'], ['N.R'])
        self.assertEqual(run(['N.C.R', 'N', 'N'], ['N.R', 'N', 'N'])['status'], 'OK')
        # Every drop is in the audit trail with its rule.
        verdict = run(['N.C.R', 'L', 'N'], ['N.R', 'L'])
        self.assertIn(['g', 'N', 'N', 'preresolved implied prefix removed (R12b)'], verdict['derived_literals_respelled'])

    def test_preresolved_hardening_after_review_3(self):
        # R20 (Neon-3 findings 3, 5.2, 8).
        T = ['const', ['name', 'Lean.Syntax.Preresolved'], []]
        def lit(n):
            parts = n.split('.')
            e = ['const', ['name', f'Lean.Name.mkStr{len(parts)}'], []]
            for part in parts:
                e = ['app', e, ['str', part]]
            return e
        def entry(kind, n):
            if kind == 'ns':
                return ['app', ['const', ['name', 'Lean.Syntax.Preresolved.namespace'], []], lit(n)]
            nil = ['app', ['const', ['name', 'List.nil'], [['zero']]], ['const', ['name', 'String'], []]]
            return ['app', ['app', ['const', ['name', 'Lean.Syntax.Preresolved.decl'], []], lit(n)], nil]
        def lst(*entries):
            out = ['app', ['const', ['name', 'List.nil'], [['zero']]], T]
            for e in reversed(entries):
                out = ['app', ['app', ['app', ['const', ['name', 'List.cons'], [['zero']]], T], e], out]
            return out
        def run(before, after, rows):
            gen = lambda l: dict(kernel=['definition', 'safe', self.hygiene_ident(l)], attributes={})
            self.before = snapshot({'A.C.R.x': constant(), 'L.Old.y': constant(2), 'g': gen(lst(*before))},
                                   ['A.C.R.x', 'L.Old.y'])
            self.after = snapshot({'A.R.x': constant(), 'L.New.y': constant(2), 'g': gen(lst(*after))},
                                  ['A.R.x', 'L.New.y'])
            self.renames = self.entries(('L.Old', 'L.New', 'namespace', {}), *rows)
            return self.run_check()
        merge = [('A.C', 'A', 'namespace', {}), ('A.C.R.x', 'A.R.x', 'declaration', {})]
        # Finding 3: an R12 drop of a `Preresolved.decl` entry is recorded (no crash).
        verdict = run([entry('ns', 'A.C'), entry('decl', 'A.C.R.x'), entry('decl', 'A.R.x')],
                      [entry('ns', 'A'), entry('decl', 'A.R.x')], merge)
        self.assertIn('preresolved duplicate removed (R12)', [r[3] for r in verdict['derived_literals_respelled']])
        # Finding 5.2: R12b drops a prefix only when the map respelled the
        # current namespace or the dropped entry, not another entry.
        with self.assertRaises(CHECK.Mismatch):
            run([entry('ns', 'A.B'), entry('ns', 'L.Old'), entry('ns', 'A')],
                [entry('ns', 'A.B'), entry('ns', 'L.New')], merge)
        # Finding 8: `[N.C.R, N.C, N, N]` keeps its pre-existing `N, N`.
        rows = [('A.C', 'A', 'namespace', {}), ('A.C.R.x', 'A.R.x', 'declaration', {})]
        with self.assertRaises(CHECK.Mismatch):
            run([entry('ns', 'A.C.R'), entry('ns', 'A.C'), entry('ns', 'A'), entry('ns', 'A')],
                [entry('ns', 'A.R'), entry('ns', 'A')], rows)
        # A map-made duplicate of a pre-existing pair: none of them drops.
        with self.assertRaises(CHECK.Mismatch):
            run([entry('ns', 'A.C'), entry('ns', 'A'), entry('ns', 'A')], [entry('ns', 'A'), entry('ns', 'A')], rows)
        # Without drops the list compares entry by entry.
        self.assertEqual(run([entry('ns', 'A.C.R'), entry('ns', 'A.C'), entry('ns', 'A'), entry('ns', 'A')],
                             [entry('ns', 'A.R'), entry('ns', 'A'), entry('ns', 'A'), entry('ns', 'A')],
                             rows)['status'], 'OK')

    def test_preresolved_pairing_uses_the_coarse_bucket(self):
        # Finding 6.4: generated constants whose names differ are paired only
        # through the coarse bucket, which must see the dropped entry.
        rows = self.entries(('A.C', 'A', 'namespace', {}), ('A.C.R.x', 'A.R.x', 'declaration', {}))
        def run(before, after, user=None):
            gen = lambda names: dict(kernel=['definition', 'safe', self.hygiene_ident(self.preresolved_list(*names))],
                                     attributes={})
            # No authored constant refers to them: only the bucket pairs them.
            self.before = snapshot({'A.C.R.x': constant(), 'genOld': gen(before)}, ['A.C.R.x'])
            self.after = snapshot({'A.R.x': constant(), 'genNew': gen(after)}, ['A.R.x'])
            self.renames = rows
            comparison = CHECK.Comparison(self.before, self.after, self.renames)
            self.assertNotEqual(comparison.preferred_generated('genOld'), 'genNew')
            return comparison.run()
        self.assertEqual(run(['A.C', 'L', 'A'], ['A', 'L'])['status'], 'OK')
        with self.assertRaises(CHECK.Mismatch):
            run(['A.C', 'L', 'A'], ['A', 'M'])
        # Finding 6.3: the coarse set applies to the whole list only. In
        # `[L, A.B, A]` the tail `[A.B, A]` is not collapsed (A is no prefix of L).
        self.before = snapshot({'k': constant()}, ['k'])
        comparison = CHECK.Comparison(self.before, self.before, {})
        # (Both inputs stay alive: the coarse cache is keyed by object identity.)
        lists = [self.hygiene_ident(self.preresolved_list('L', 'A.B', 'A')),
                 self.hygiene_ident(self.preresolved_list('A.B', 'L', 'A'))]
        coarse = [comparison.normalize(x, 'after', coarse=True) for x in lists]
        self.assertEqual([len(CHECK.Comparison._list_cells(c[2])[1]) for c in coarse], [3, 2])


if __name__ == '__main__':
    unittest.main()
