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
            def reviewed(rec):
                self.before = snapshot({'N.m': CHECK.quoted_identifiers(dict(kernel=ident('B256', ['B256'], 'Jaune.B256', scoped), attributes={}))}, ['N.m'])
                self.after = snapshot({'N.m': CHECK.quoted_identifiers(dict(kernel=ident('Jaune.U256', ['Jaune', 'U256'], 'Jaune.U256', scoped), attributes={}))}, ['N.m'])
                used = set()
                verdict = CHECK.Comparison(self.before, self.after, self.renames, [rec], used).run()
                return verdict['status'], used
            self.assertEqual(reviewed(record), ('OK', {0}))
            # Control: a record naming another constant, or another map row, does not apply.
            for bad in (dict(record, constant='N.other'), dict(record, map_old='Jaune.Tx.receiver', map_new='Jaune.Tx.to'),
                        dict(record, after='Jaune.Other', map_new='Jaune.Other')):
                with self.assertRaisesRegex(CHECK.Mismatch, 'quoted spelling'):
                    reviewed(bad)
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
        def run(before_lits, after_lits):
            kernel = lambda lits: dict(kernel=['definition', 'safe', ['app', lit(*lits[0]), lit(*lits[1])]], attributes={})
            self.before = snapshot({'N.Inv.a': constant(), 'N.Inv.b': constant(2), '_private.M.0.N.Inv.tacticFoo': constant(7),
                                    'gen': kernel(before_lits)}, ['N.Inv.a', 'N.Inv.b'])
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
        def run(before, after, plan=True, hygienic=False):
            self.before = snapshot({'N.HdrEq': constant(), 'N.m': CHECK.quoted_identifiers(dict(kernel=ident(before), attributes={}))},
                                   ['N.HdrEq', 'N.m'])
            self.after = snapshot({'N.HeaderEq': constant(), 'N.m': CHECK.quoted_identifiers(dict(kernel=ident(after), attributes={}))},
                                  ['N.HeaderEq', 'N.m'])
            self.before['quotation_sites'] = {'M': [(10, 15, 'HdrEq'), (20, 23, 'x13')]}
            self.before['module_sources'] = {'M': ''}
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


if __name__ == '__main__':
    unittest.main()
