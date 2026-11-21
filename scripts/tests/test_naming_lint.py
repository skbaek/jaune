import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).parents[2]
SPEC = importlib.util.spec_from_file_location('naming_lint', ROOT / 'scripts/check-naming.py')
LINT = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(LINT)


class NamingLintTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        self.mapping = LINT.read_json(ROOT / 'scripts/naming-map.json')
        self.policy = dict(schema_version=1, words=['account', 'balance', 'gas', 'limit', 'field', 'read', 'value'],
                           sources={}, bindings={})

    def lint(self, *names):
        words = LINT.validate_policy(self.policy, self.root)
        return LINT.lint_names(dict.fromkeys(names, [0, 0, 0, 1]), self.mapping, self.policy, words)[0]

    def bind(self, name, spelling, style='verbatim', text=None):
        raw = (text or spelling).encode()
        (self.root / 'upstream.txt').write_bytes(raw)
        self.policy['sources']['upstream'] = dict(path='upstream.txt', sha256=LINT.sha(raw), citation='Synthetic source fixture')
        self.policy['bindings'][name] = dict(rule='1', source='upstream', spelling=spelling, style=style)

    def bundle(self, source='Jaune/Test.lean', text='def value := 1\n', name='Jaune.value'):
        path = self.root / source
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(text)
        module = source[:-5].replace('/', '.')
        last = name.split('.')[-1]
        index = dict(version=5, module=module, references={},
                     decls={name: [0, 0, 0, len(text) - 1, 0, 4, 0, 4 + len(last)]})
        bundle = self.root / (module + '.json')
        bundle.write_text(json.dumps(dict(source=text, index=index)))
        return source, str(bundle)

    def test_whole_words_abbreviations_and_numerals(self):
        self.assertEqual(self.lint('Jaune.Account.gasLimit', 'Jaune.read_UInt32', 'Jaune.value2'), [])

    def test_acronym_run_splits_only_at_an_allowed_acronym(self):
        # Lean naming (doc/std/naming.md, Acronyms): IO stays upper case, so IO + U256 is one capital run.
        self.assertEqual(self.lint('Jaune.readIOU256', 'Jaune.readIOUInt64', 'Jaune.readIOValue'), [])
        # The remainder of the run is still a token of its own and must be registered.
        self.assertEqual([p['tokens'] for p in self.lint('Jaune.readIORBValue')], [['RB']])
        # A run with no allowed acronym at its head is not split.
        self.assertEqual([p['tokens'] for p in self.lint('Jaune.readXIOValue')], [['XIO']])
        # A whole run that is itself an allowed multi-token acronym is never split.
        self.assertEqual(self.lint('Jaune.readU256', 'Jaune.readEVM'), [])

    def test_retired_execution_and_consensus(self):
        for name in ('Jaune.Devm', 'Jaune.Account.bal', 'JauneConsensus.Ctx', 'JauneConsensus.bal'):
            self.assertTrue(any(p['reason'] == 'retired token' for p in self.lint(name)))
        self.bind('Jaune.bal', 'bal')
        self.assertTrue(any(p['reason'] == 'retired token' for p in self.lint('Jaune.bal')))

    def retire(self, enforced=(), pending=()):
        self.mapping['retired_names'], self.mapping['pending_retired_names'] = list(enforced), list(pending)
        self.policy['words'] = sorted(set(self.policy['words']) | {
            'generic', 'call', 'create', 'frame', 'outer', 'spawn', 'step', 'ssz', 'case'})

    def reasons(self, *names, final=False):
        words = LINT.validate_policy(self.policy, self.root)
        problems, _, pending = LINT.lint_names(dict.fromkeys(names, [0, 0, 0, 1]), self.mapping, self.policy,
                                               words, final)
        return [(p['reason'], p['names']) for p in problems if 'names' in p], [p['names'] for p in pending]

    def test_retired_names_in_declarations_fields_and_private_names(self):
        self.retire(enforced=['genericCall', 'Frame.outer'])
        for name in ('Jaune.genericCall', 'Jaune.Checked.genericCallAmsterdam.step',
                     'JauneConsensus.step_genericCall'):
            self.assertEqual(self.reasons(name), ([('retired name', ['genericCall'])], []), name)
        self.assertEqual(self.reasons('Jaune.Frame.outer'), ([('retired name', ['Frame.outer'])], []))
        for name in ('Jaune.genericCreate', 'Jaune.Frame.step', 'Jaune.outer', 'Jaune.spawnCall'):
            self.assertEqual(self.lint(name), [], name)
        # A field definition and a private name, as the compiler indexes them.
        text = 'outer genericCall'
        ref = lambda n: json.dumps({'c': {'m': 'Jaune.Test', 'n': n}})
        index = dict(version=5, module='Jaune.Test', decls={}, references={
            ref('Jaune.Frame.outer'): {'definition': [0, 0, 0, 5], 'usages': []},
            ref('_private.Jaune.Test.0.Jaune.genericCall'): {'definition': [0, 6, 0, 17], 'usages': []}})
        names = LINT.declarations(text, index)
        words = LINT.validate_policy(self.policy, self.root)
        found = LINT.lint_names(names, self.mapping, self.policy, words)[0]
        self.assertEqual({(p['name'], p['reason']) for p in found},
                         {('Jaune.Frame.outer', 'retired name'), ('Jaune.genericCall', 'retired name')})

    def test_retired_names_spare_source_names_and_no_source_exempts_one(self):
        self.retire(enforced=['genericCall', 'genericCreate'])
        self.bind('JauneConsensus.ssz_generic', 'ssz_generic')
        self.assertEqual(self.lint('JauneConsensus.ssz_generic', 'JauneConsensus.sszGenericCase'), [])
        self.policy['bindings'] = {}
        self.bind('Jaune.genericCall', 'generic_call', 'lowerCamel')
        self.assertEqual(self.reasons('Jaune.genericCall'), ([('retired name', ['genericCall'])], []))

    def test_pending_retired_names_report_until_the_final_run(self):
        self.retire(enforced=['Frame.outer'], pending=['genericCall'])
        self.assertEqual(self.reasons('Jaune.genericCall.step'), ([], [['genericCall']]))
        self.assertEqual(self.reasons('Jaune.genericCall.step', final=True),
                         ([('retired name', ['genericCall'])], []))
        pair = self.bundle(text='def genericCall := 1\n', name='Jaune.genericCall')
        result = LINT.check(self.root, self.mapping, self.policy, self.root, [pair], [])
        self.assertEqual((result['status'], result['final'], result['pending_retired_names']),
                         ('OK', False, ['genericCall']))
        self.assertEqual([(p['source'], p['name'], p['reason'], p['names']) for p in result['pending']],
                         [('Jaune/Test.lean', 'Jaune.genericCall', 'pending retired name', ['genericCall'])])
        result = LINT.check(self.root, self.mapping, self.policy, self.root, [pair], [], final=True)
        self.assertEqual(result['status'], 'REGRESSION')
        self.assertEqual([(p['name'], p['reason']) for p in result['problems']],
                         [('Jaune.genericCall', 'retired name'),
                          ('genericCall', 'retired name still registered as pending')])
        # A final run with a clean tree still fails while the map registers a pending name.
        clean = self.bundle()
        result = LINT.check(self.root, self.mapping, self.policy, self.root, [clean], [], final=True)
        self.assertEqual([p['reason'] for p in result['problems']], ['retired name still registered as pending'])
        self.retire(enforced=['Frame.outer', 'genericCall'])
        result = LINT.check(self.root, self.mapping, self.policy, self.root, [clean], [], final=True)
        self.assertEqual((result['status'], result['final'], result['pending']), ('OK', True, []))

    def test_reintroducing_a_retired_name_or_token_fails_on_a_synthetic_tree(self):
        # The S1 and N3 controls: the tracked map with its pending names enforced, as at landing.
        enforced, pending = LINT.MAP.retired_name_lists(self.mapping)
        self.retire(enforced=enforced + pending)
        green = 'def spawnCall := 1\n'
        pair = self.bundle(text=green, name='Jaune.spawnCall')
        other = self.bundle('JauneConsensus/Test.lean', name='JauneConsensus.value')
        roots = ['Jaune', 'JauneConsensus']
        baseline = LINT.check(self.root, self.mapping, self.policy, self.root, [pair, other], roots, final=True)
        self.assertEqual((baseline['status'], baseline['scope']), ('OK', 'whole-tree'))
        source = self.root / 'Jaune/Test.lean'
        for planted, reason in (('genericCall', 'retired name'), ('genericCreateAmsterdam', 'retired name'),
                                ('incorporateChild', 'retired name'), ('executeCode', 'retired name'),
                                ('Devm', 'retired token')):
            mutated = self.bundle(text=green.replace('spawnCall', planted), name='Jaune.' + planted)
            result = LINT.check(self.root, self.mapping, self.policy, self.root, [mutated, other], roots, final=True)
            self.assertEqual(result['status'], 'REGRESSION', planted)
            self.assertEqual([(p['source'], p['name'], p['reason']) for p in result['problems']
                              if p['reason'].startswith('retired')],
                             [('Jaune/Test.lean', 'Jaune.' + planted, reason)], planted)
            source.write_text(green)
            self.assertEqual(LINT.sha(source.read_bytes()), baseline['files'][0]['source_sha256'])
        # Without the registration the planted name passes: the control is the map's entry.
        self.retire(enforced=[name for name in enforced + pending if name != 'genericCall'])
        mutated = self.bundle(text=green.replace('spawnCall', 'genericCall'), name='Jaune.genericCall')
        result = LINT.check(self.root, self.mapping, self.policy, self.root, [mutated, other], roots, final=True)
        self.assertEqual(result['status'], 'OK')

    def test_unknown_words_cannot_hide_in_unicode_or_punctuation(self):
        for name in ('Jaune.acct', 'Jaune.readΞ', 'Jaune.read__value', 'Jaune.read$'):
            self.assertTrue(self.lint(name), name)
        self.assertEqual(self.lint("Jaune.read_value'"), [])

    def test_leading_lowercase_abbreviation_plural_and_keyword_escape(self):
        abbreviations = {'BPO', 'G1', 'UInt32', 'Int', 'U64'}
        words = {'rules', 'valid', 'to', 'halt', 'op', 'length', 'return'}
        unknown = lambda s: LINT.unknown_words(s, words, abbreviations)
        # A leading all-capitals abbreviation is lowered by lowerCamel; inside a name it is not.
        self.assertEqual(unknown('bpo1Rules_valid'), [])
        self.assertEqual(unknown('g1Length'), [])
        self.assertEqual(unknown('rulesBPO1'), [])
        self.assertEqual(unknown('rulesBpo1'), ['Bpo'])
        self.assertEqual(unknown('validBpo'), ['Bpo'])
        # Only all-capitals abbreviations are lowered: `Int` is a word-like abbreviation.
        self.assertEqual(unknown('intRules'), ['int'])
        # The lowered form must match the whole abbreviation, digits included.
        self.assertEqual(unknown('g2Length'), ['g'])
        # The plural of a registered abbreviation that ends in digits.
        self.assertEqual(unknown('UInt32s'), [])
        self.assertEqual(unknown('Rules32s'), ['s'])
        # A Lean keyword escape is accepted only as the single trailing underscore.
        self.assertEqual(unknown('return_'), [])
        self.assertEqual(unknown('rules_'), ['<empty>'])
        self.assertEqual(unknown('return__'), ['<empty>', '<empty>'])
        self.assertEqual(unknown('halt_return_'), ['<empty>'])

    def test_default_suffix_only_with_its_lean_source(self):
        # Ruling 6: Lean core's `D` (`Array.getD`) is accepted only when its pinned source is registered.
        self.policy['words'] += ['slice', 'take', 'right', 'byte', 'eq', 'go', 'list']
        self.assertEqual([p['tokens'] for p in self.lint('Jaune.sliceD')], [['D']])
        raw = b'@[inline] abbrev Array.getD (a : Array \xce\xb1) (i : Nat) (v\xe2\x82\x80 : \xce\xb1) : \xce\xb1 :=\n'
        (self.root / 'prelude.txt').write_bytes(raw)
        self.policy['sources']['lean4-prelude'] = dict(path='prelude.txt', sha256=LINT.sha(raw), citation='Lean core fixture')
        self.assertEqual(self.lint('Jaune.sliceD', 'Jaune.List.takeRightD', 'Jaune.byteD_eq', 'Jaune.sliceD.go'), [])
        # Only a final `D` after a word: not inside a component, not alone, not after a one-letter token.
        self.assertEqual([p['tokens'] for p in self.lint('Jaune.sliceDRight')], [['D']])
        self.assertEqual([p['tokens'] for p in self.lint('Jaune.DSlice')], [['D']])
        self.assertEqual([p['tokens'] for p in self.lint('Jaune.value_D')], [['D']])
        # The source must spell the definition; another Prelude text does not activate the suffix.
        raw = b'def Option.get! (opt : Option \xce\xb1) : \xce\xb1\n'
        (self.root / 'prelude.txt').write_bytes(raw)
        self.policy['sources']['lean4-prelude']['sha256'] = LINT.sha(raw)
        self.assertEqual([p['tokens'] for p in self.lint('Jaune.sliceD')], [['D']])

    def test_source_names_pass_only_with_exact_registration(self):
        self.bind('JauneConsensus.eth1_data', 'eth1_data')
        self.assertEqual(self.lint('JauneConsensus.eth1_data'), [])
        self.assertTrue(self.lint('Jaune.eth1_data'))
        self.policy['bindings'] = {}
        self.bind('Jaune.sload', 'SLOAD', 'lowerCamel')
        self.assertEqual(self.lint('Jaune.sload'), [])
        self.assertTrue(self.lint('Jaune.Account.sload'))

    def test_consensus_function_transliteration_and_changed_source(self):
        self.bind('JauneConsensus.readValue', 'read_value', 'lowerCamel')
        self.assertEqual(self.lint('JauneConsensus.readValue'), [])
        (self.root / 'upstream.txt').write_text('changed')
        with self.assertRaisesRegex(ValueError, 'digest mismatch'):
            self.lint('JauneConsensus.readValue')

    def test_source_substring_wrong_case_missing_and_path_escape(self):
        self.bind('Jaune.sload', 'sload', text='mysload')
        with self.assertRaisesRegex(ValueError, 'spelling absent'):
            self.lint('Jaune.sload')
        self.bind('Jaune.Sload', 'sload')
        del self.policy['bindings']['Jaune.sload']
        with self.assertRaisesRegex(ValueError, 'case mismatch'):
            self.lint('Jaune.Sload')
        self.policy['bindings'] = {}
        self.policy['sources']['upstream']['path'] = '../escape'
        with self.assertRaisesRegex(ValueError, 'tree-relative'):
            self.lint('Jaune.value')

    def test_fields_constructors_and_private_names_are_included(self):
        text = 'value field read'
        ref = lambda n: json.dumps({'c': {'m': 'Jaune.Test', 'n': n}})
        index = dict(version=5, module='Jaune.Test', decls={}, references={
            ref('Jaune.Account.field'): {'definition': [0, 6, 0, 11], 'usages': []},
            ref('_private.Jaune.Test.0.Jaune.read'): {'definition': [0, 12, 0, 16], 'usages': []},
            ref('Jaune.Account.value'): {'definition': [0, 0, 0, 5], 'usages': []},
        })
        self.assertEqual(set(LINT.declarations(text, index)), {'Jaune.Account.field', 'Jaune.read', 'Jaune.Account.value'})
        index['references'][ref('Jaune.Account.field')]['definition'] = [0, 30, 0, 31]
        with self.assertRaisesRegex(ValueError, 'outside source'):
            LINT.declarations(text, index)

    def test_anonymous_example_navigation_entry_is_not_a_declaration(self):
        index = dict(version=5, module='Test', decls={}, references={
            json.dumps({'c': {'m': 'Test', 'n': 'Test._example'}}):
                {'definition': [0, 0, 0, 7], 'usages': []}})
        self.assertEqual(LINT.declarations('example : True := trivial', index), {})

    def test_stale_bundle_and_wrong_version(self):
        pair = self.bundle()
        bundle = LINT.read_json(pair[1])
        bundle['source'] += ' '
        Path(pair[1]).write_text(json.dumps(bundle))
        with self.assertRaisesRegex(ValueError, 'source mismatch'):
            LINT.check(self.root, self.mapping, self.policy, self.root, [pair], [])
        bundle['index']['version'] = 4
        with self.assertRaisesRegex(ValueError, 'format 5'):
            LINT.declarations(bundle['source'], bundle['index'])

    def test_whole_tree_requires_every_file_and_rejects_stale_binding(self):
        pair = self.bundle()
        other = self.bundle('JauneConsensus/Test.lean', name='JauneConsensus.value')
        with self.assertRaisesRegex(ValueError, 'incomplete tree coverage'):
            LINT.check(self.root, self.mapping, self.policy, self.root, [pair], ['Jaune', 'JauneConsensus'])
        result = LINT.check(self.root, self.mapping, self.policy, self.root, [pair, other], ['Jaune', 'JauneConsensus'])
        self.assertEqual((result['status'], result['scope']), ('OK', 'whole-tree'))
        self.bind('Jaune.sload', 'sload')
        result = LINT.check(self.root, self.mapping, self.policy, self.root, [pair, other], ['Jaune', 'JauneConsensus'])
        self.assertEqual(result['problems'][0]['reason'], 'unused source binding')

    def test_partial_scope_and_duplicate_files(self):
        pair = self.bundle()
        result = LINT.check(self.root, self.mapping, self.policy, self.root, [pair], [])
        self.assertEqual((result['status'], result['scope']), ('OK', 'selected-files'))
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            LINT.check(self.root, self.mapping, self.policy, self.root, [pair, pair], [])

    def test_protocol_map_row_cannot_fall_back_to_english_words(self):
        self.mapping['entries'] = [dict(old='Jaune.oldValue', new='Jaune.value',
            kind='declaration', layer='execution', rule='1', source='Synthetic fixture')]
        self.assertEqual(self.lint('Jaune.value')[0]['reason'], 'map requires matching source binding')
        self.bind('Jaune.value', 'value')
        self.assertEqual(self.lint('Jaune.value'), [])

    def register_derived(self, old, new, base='Jaune.Yzz', **changes):
        root = dict(old='Jaune.Zzz', new='Jaune.Yzz', kind='declaration',
                    layer='execution', rule='1, 7', source='synthetic protocol name')
        target = dict(root, old=old, new=new)
        target.update(changes)
        self.mapping['entries'] = [root, target]
        self.bind('Jaune.Yzz', 'YZZ', style='upperCamel', text='YZZ ZZZ KQQ')
        self.policy['derived'] = {new: dict(old=old, base=base)}

    def test_source_derived_namespace_and_residual_words(self):
        self.register_derived('Jaune.Zzz.balance', 'Jaune.Yzz.balance')
        self.assertEqual(self.lint('Jaune.Yzz.balance'), [])
        self.register_derived('Jaune.Zzz.qxz', 'Jaune.Yzz.qxz')
        findings = self.lint('Jaune.Yzz.qxz')
        self.assertEqual([(f['reason'], f['tokens']) for f in findings],
                         [('unregistered word or source', ['qxz'])])

    def test_component_source_only_covers_the_replaced_occurrences(self):
        self.register_derived('Jaune.readZzz_Zzz', 'Jaune.readYzz_Yzz')
        self.assertEqual(self.lint('Jaune.readYzz_Yzz'), [])
        self.register_derived('Jaune.readYzz_Zzz', 'Jaune.readYzz_Yzz')
        findings = self.lint('Jaune.readYzz_Yzz')
        self.assertEqual([f['tokens'] for f in findings], [['Yzz']])
        self.register_derived('Jaune.qxzZzz', 'Jaune.qxzYzz')
        self.assertEqual([f['tokens'] for f in self.lint('Jaune.qxzYzz')], [['qxz']])

    def test_derived_binding_requires_same_root_change_and_explicit_actual_old(self):
        for old, new in [('Jaune.Zzz.read', 'Jaune.Yzz.balance'),
                         ('Jaune.Foreign.Zzz.read', 'Jaune.Other.Yzz.read'),
                         ('Jaune.readZzzy', 'Jaune.readYzzy')]:
            self.register_derived(old, new)
            with self.assertRaisesRegex(ValueError, 'extends beyond'):
                self.lint(new)
        self.register_derived('Jaune.Zzz.read', 'Jaune.Yzz.read')
        self.policy['derived']['Jaune.Yzz.read']['old'] = 'Jaune.Foreign.Zzz.read'
        with self.assertRaisesRegex(ValueError, 'lacks matching'):
            self.lint('Jaune.Yzz.read')

    def test_derived_binding_rechecks_root_source_and_actual_map_citation(self):
        self.register_derived('Jaune.Zzz.read', 'Jaune.Yzz.read',
                              source='an unrelated citation')
        with self.assertRaisesRegex(ValueError, 'lacks matching'):
            self.lint('Jaune.Yzz.read')
        self.register_derived('Jaune.Zzz.read', 'Jaune.Yzz.read')
        self.policy['bindings']['Jaune.Yzz']['spelling'] = 'KQQ'
        with self.assertRaisesRegex(ValueError, 'case mismatch'):
            self.lint('Jaune.Yzz.read')
        self.policy['bindings']['Jaune.Yzz']['spelling'] = 'YZZ'
        self.policy['sources']['upstream']['sha256'] = '0' * 64
        with self.assertRaisesRegex(ValueError, 'digest mismatch'):
            self.lint('Jaune.Yzz.read')

    def test_derived_rows_are_opt_in_and_unused_rows_fail(self):
        self.register_derived('Jaune.Zzz.read', 'Jaune.Yzz.read')
        no_rows = self.policy.pop('derived')
        self.assertIn('map requires matching source binding', [p['reason'] for p in self.lint('Jaune.Yzz.read')])
        self.policy['derived'] = no_rows
        pair = self.bundle()
        result = LINT.check(self.root, self.mapping, self.policy, self.root, [pair], ['Jaune'])
        self.assertIn('Jaune.Yzz.read', [p['name'] for p in result['problems']
                                       if p['reason'] == 'unused source binding'])

    def test_internal_lean_suffix_requires_its_theorems_actual_compiler_reference(self):
        name = 'Jaune.read?_balance'
        ref = {'c': {'m': 'Jaune.Test', 'n': 'Jaune.read?'}}
        bundle = {'index': {'module': 'Jaune.Test', 'references': {}},
                  'constants': {name: {'kernel': {'payload': ['theorem']}}}}
        words = set(self.policy['words'])

        def check(owner, target, kind):
            ref['c']['n'] = target
            bundle['index']['references'] = {json.dumps(ref): {'usages': [[0, 0, 0, 4, owner]]}}
            bundle['constants'][name]['kernel']['payload'] = [kind]
            return LINT.lint_names({name: []}, self.mapping, self.policy, words,
                                   reference_endings=LINT.theorem_reference_endings(bundle))[0]

        self.assertEqual(check(name, 'Jaune.read?', 'theorem'), [])
        for owner, target, kind in [(name, 'Jaune.Other.read?', 'theorem'),
                                  ('Jaune.other', 'Jaune.read?', 'theorem'),
                                  (name, 'Jaune.read?', 'definition')]:
            self.assertTrue(check(owner, target, kind))
        words.remove('read')
        self.assertEqual(check(name, 'Jaune.read?', 'theorem')[0]['tokens'], ['read'])
        words.add('read')
        words.remove('balance')
        self.assertEqual(check(name, 'Jaune.read?', 'theorem')[0]['tokens'], ['balance'])

    # Rule 7: names built from the definitions a kernel statement uses.
    LEAN_SOURCES = {
        'lean4-std-naming': '| `refl` | reflexive |\n| `trans` | transitive |\n',
        'lean4-list-lex': 'protected theorem not_lt_iff_ge\nprotected theorem not_le_iff_gt\n',
        'lean4-list-lemmas': 'theorem reverse_concat\n',
        'lean4-elab-structure': 'private def defaultCtorName := `mk\n',
        'lean4-prelude': 'structure Subtype where\n  val : α\n',
    }

    def register_lean(self, *keys):
        for key in keys:
            raw = self.LEAN_SOURCES[key].encode()
            (self.root / (key + '.txt')).write_bytes(raw)
            self.policy['sources'][key] = dict(path=key + '.txt', sha256=LINT.sha(raw), citation='Synthetic Lean source')

    def statement(self, name, kind, pool, root, value=None, extra=None, references=None):
        payload = {'theorem': ['theorem'], 'definition': ['definition', 'safe', value],
                   'constructor': ['constructor', ['name', 'Jaune.Value'], 0, 0, 0, False]}[kind]
        constants = {name: {'kernel': {'payload': payload, 'type': root}}}
        constants.update(extra or {})
        bundle = {'index': {'module': 'Jaune.Test', 'references': references or {}},
                  'constants': constants, 'expr_pool': pool, 'level_pool': [['zero'], ['succ', 0]]}
        return LINT.theorem_reference_endings(bundle)

    def lean_lint(self, name, evidence):
        words = LINT.validate_policy(self.policy, self.root)
        return LINT.lint_names({name: []}, self.mapping, self.policy, words, reference_endings=evidence)[0]

    LE_POOL = [['const', ['name', 'LE.le'], []], ['const', ['name', 'Nat'], []], ['app', 0, 1]]

    def test_statement_relation_names_only_what_the_statement_uses(self):
        name = 'Jaune.value_le_limit'
        self.assertEqual(self.lean_lint(name, self.statement(name, 'theorem', self.LE_POOL, 2)), [])
        other = [['const', ['name', 'LT.lt'], []], ['const', ['name', 'Nat'], []], ['app', 0, 1]]
        self.assertEqual(self.lean_lint(name, self.statement(name, 'theorem', other, 2))[0]['tokens'], ['le'])
        own = [['const', ['name', 'Jaune.le'], []]]
        self.assertEqual(self.lean_lint(name, self.statement(name, 'theorem', own, 0))[0]['tokens'], ['le'])
        # Data is not named by the theorem algorithm.
        self.assertTrue(self.lean_lint(name, self.statement(name, 'definition', self.LE_POOL, 2, value=1)))
        # A type spelled in lower camel case (`Nat` as `nat`) and a punctuated Lean name.
        pool = [['const', ['name', 'GetElem?.getElem?'], []], ['const', ['name', 'Nat'], []], ['app', 0, 1]]
        self.assertEqual(self.lean_lint('Jaune.getElem?_nat_value', self.statement(
            'Jaune.getElem?_nat_value', 'theorem', pool, 2)), [])

    def test_lean_keywords_need_a_registered_source_a_theorem_and_a_whole_component(self):
        name = 'Jaune.value_refl'
        evidence = self.statement(name, 'theorem', self.LE_POOL, 2)
        self.assertEqual(self.lean_lint(name, evidence)[0]['tokens'], ['refl'])
        self.register_lean('lean4-std-naming')
        self.assertEqual(self.lean_lint(name, evidence), [])
        self.assertTrue(self.lean_lint(name, self.statement(name, 'definition', self.LE_POOL, 2, value=1)))
        self.assertTrue(self.lean_lint('Jaune.valueRefl', self.statement('Jaune.valueRefl', 'theorem', self.LE_POOL, 2)))
        self.policy['sources']['lean4-std-naming']['sha256'] = '0' * 64
        with self.assertRaises(ValueError):
            LINT.validate_policy(self.policy, self.root)

    def test_swapped_relation_and_singleton_append(self):
        name = 'Jaune.value_ge'
        self.register_lean('lean4-list-lex', 'lean4-list-lemmas')
        self.assertEqual(self.lean_lint(name, self.statement(name, 'theorem', self.LE_POOL, 2)), [])
        lt = [['const', ['name', 'LT.lt'], []]]
        self.assertTrue(self.lean_lint(name, self.statement(name, 'theorem', lt, 0)))
        # `l ++ [a]` is `concat`; a plain append is not.
        pool = [['const', ['name', 'HAppend.hAppend'], []], ['bvar', 0], ['const', ['name', 'List.cons'], []],
                ['const', ['name', 'List.nil'], []], ['app', 3, 1], ['app', 2, 1], ['app', 5, 1], ['app', 6, 4]]
        for depth in range(5):
            pool.append(['app', len(pool) - 1 if depth else 0, 1])
        pool.append(['app', len(pool) - 1, 7])
        name = 'Jaune.value_concat'
        self.assertEqual(self.lean_lint(name, self.statement(name, 'theorem', pool, len(pool) - 1)), [])
        pool[-1] = ['app', len(pool) - 2, 1]
        self.assertEqual(self.lean_lint(name, self.statement(name, 'theorem', pool, len(pool) - 1))[0]['tokens'],
                         ['concat'])

    def test_constructor_projection_and_instance_method_names(self):
        self.register_lean('lean4-elab-structure', 'lean4-prelude')
        value = [['const', ['name', 'Jaune.Value'], []], ['const', ['name', 'Nat'], []],
                 ['forall', 'default', 1, 0], ['bvar', 0], ['proj', ['name', 'Jaune.Value'], 0, 3],
                 ['lam', 'default', 0, 4]]
        self.assertEqual(self.lean_lint('Jaune.Value.mk', self.statement('Jaune.Value.mk', 'constructor', value, 2)), [])
        self.assertEqual(self.lean_lint('Jaune.Value.mk', self.statement('Jaune.Value.mk', 'definition', value, 2, 3)), [])
        self.assertTrue(self.lean_lint('Jaune.Value.mk', self.statement('Jaune.Value.mk', 'definition', value, 1, 3)))
        self.assertEqual(self.lean_lint('Jaune.Value.val', self.statement('Jaune.Value.val', 'definition', value, 1, 5)), [])
        self.assertTrue(self.lean_lint('Jaune.Value.val', self.statement('Jaune.Value.val', 'definition', value, 1, 3)))
        # A theorem may spell the referenced constructor or projection.
        ref = [['const', ['name', 'Jaune.Value.val'], []]]
        self.assertEqual(self.lean_lint('Jaune.read_val', self.statement('Jaune.read_val', 'theorem', ref, 0)), [])
        # `instance : Neg Value := ⟨Value.neg⟩` names the method after the class.
        pool = [['const', ['name', 'Jaune.Value'], []], ['const', ['name', 'Neg.mk'], []],
                ['const', ['name', 'Jaune.Value.neg'], []], ['app', 1, 0], ['app', 3, 2],
                ['const', ['name', 'Neg'], []], ['app', 5, 0]]
        instance = {'Jaune.instNegValue': {'attributes': {'instance': 'default'},
                                           'kernel': {'payload': ['definition', 'safe', 4], 'type': 6}}}
        evidence = self.statement('Jaune.Value.neg', 'definition', pool, 0, value=0, extra=instance)
        self.assertEqual(self.lean_lint('Jaune.Value.neg', evidence), [])
        del instance['Jaune.instNegValue']['attributes']['instance']
        evidence = self.statement('Jaune.Value.neg', 'definition', pool, 0, value=0, extra=instance)
        self.assertTrue(self.lean_lint('Jaune.Value.neg', evidence))

    def test_mirrored_namespace_predicate_body_and_punctuated_jaune_name(self):
        pool = [['const', ['name', 'Std.TreeMap'], []]]
        name = 'Jaune.Std.TreeMap.value'
        self.assertEqual(self.lean_lint(name, self.statement(name, 'definition', pool, 0, value=0)), [])
        self.assertTrue(self.lean_lint(name, self.statement(name, 'definition', [['const', ['name', 'Nat'], []]], 0, 0)))
        # A proposition defined by `≤` may be named with it; its body supplies the name.
        pool = [['sort', 0], ['const', ['name', 'LE.le'], []], ['const', ['name', 'Nat'], []]]
        self.assertEqual(self.lean_lint('Jaune.ValueLe', self.statement('Jaune.ValueLe', 'definition', pool, 0, 1)), [])
        self.assertTrue(self.lean_lint('Jaune.ValueLe', self.statement('Jaune.ValueLe', 'definition', pool, 0, 2)))
        # The punctuation of a referenced Jaune name is kept; its words are still linted.
        pool = [['const', ['name', 'Jaune.read?'], []]]
        self.assertEqual(self.lean_lint('Jaune.value_read?_limit', self.statement('Jaune.value_read?_limit', 'theorem', pool, 0)), [])
        pool = [['const', ['name', 'Jaune.bal?'], []]]
        self.assertEqual(self.lean_lint('Jaune.value_bal?_limit', self.statement('Jaune.value_bal?_limit', 'theorem', pool, 0))[0]['tokens'],
                         ['bal'])

    FIXTURE = 'YZZ WWW VVV G_{callstipend} GAS_PER_BLOB the hex-prefix encoding'

    def option(self, name, spelling, style='lowerCamel', rule='1', **options):
        self.bind(name, spelling, style, text=self.FIXTURE)
        self.policy['bindings'][name].update(rule=rule, **options)

    def test_hyphenated_and_segmented_source_spellings(self):
        self.option('Jaune.hexPrefix', 'hex-prefix')
        self.assertEqual(self.lint('Jaune.hexPrefix'), [])
        self.option('Jaune.callStipend', 'callstipend')
        with self.assertRaisesRegex(ValueError, 'case mismatch'):
            self.lint('Jaune.callStipend')
        self.option('Jaune.callStipend', 'callstipend', segments=['call', 'stipend'])
        self.policy['words'].append('call')
        self.assertEqual([f['tokens'] for f in self.lint('Jaune.callStipend')], [['stipend']])
        self.policy['words'].append('stipend')
        self.assertEqual(self.lint('Jaune.callStipend'), [])
        for segments in (['call', 'stipen'], ['callstipend'], ['call', '', 'stipend'], 'call stipend'):
            self.policy['bindings']['Jaune.callStipend']['segments'] = segments
            with self.assertRaisesRegex(ValueError, 'segments must split'):
                self.lint('Jaune.callStipend')

    def test_namespace_replaces_only_the_named_source_prefix(self):
        self.option('Jaune.Gas.perBlob', 'GAS_PER_BLOB', namespace_prefix='GAS')
        self.assertEqual(self.lint('Jaune.Gas.perBlob'), [])
        for name, prefix in (('Jaune.Fee.perBlob', 'GAS'), ('Jaune.Gas.perBlob', 'PER'), ('Jaune.perBlob', 'GAS')):
            self.policy['bindings'] = {}
            self.option(name, 'GAS_PER_BLOB', namespace_prefix=prefix)
            with self.assertRaisesRegex(ValueError, 'namespace does not replace'):
                self.lint(name)

    def test_component_binding_credits_its_component_alone(self):
        self.mapping['entries'] = [dict(old='Jaune.Zzz', new='Jaune.readYzz?', kind='declaration',
                                        layer='execution', rule='1, 7', source='synthetic protocol name')]
        self.assertEqual(self.lint('Jaune.readYzz?')[0]['reason'], 'map requires matching source binding')
        self.option('Jaune.readYzz?', 'YZZ', 'upperCamel', component='Yzz')
        self.assertEqual(self.lint('Jaune.readYzz?'), [])
        self.policy['words'].remove('read')
        self.assertEqual([(f['reason'], f['tokens']) for f in self.lint('Jaune.readYzz?')],
                         [('unregistered word or source', ['read'])])
        self.policy['words'].append('read')
        self.policy['bindings']['Jaune.readYzz?']['rule'] = '3'
        self.assertEqual(self.lint('Jaune.readYzz?')[0]['reason'], 'map requires matching source binding')
        for name, component in (('Jaune.readYzzy', 'Yzz'), ('Jaune.readYzz', 'Www'), ('Jaune.readWww', 'Yzz')):
            self.policy['bindings'] = {}
            self.option(name, 'YZZ', 'upperCamel', component=component)
            with self.assertRaisesRegex(ValueError, 'case mismatch'):
                self.lint(name)

    def register_compound(self, old, new, bases, rule='1, 3, 7', layer='execution',
                          source='Derived by token: `Zzz` -> `Yzz` (synthetic) [B]; `Qqq` -> `Www` (other) [M]'):
        roots = [dict(old='Jaune.Zzz', new='Jaune.Yzz', kind='declaration', layer='execution', rule='1, 7',
                      source='Derived by token: `Zzz` -> `Yzz` (synthetic) [B]'),
                 dict(old='Jaune.Qqq', new='Jaune.Www', kind='declaration', layer='execution', rule='3, 7',
                      source='Derived by token: `Qqq` -> `Www` (other) [M]')]
        self.mapping['entries'] = roots + [dict(old=old, new=new, kind='declaration', layer=layer, rule=rule,
                                                 source=source)]
        self.policy['bindings'] = {}
        self.option('Jaune.Yzz', 'YZZ', 'upperCamel')
        self.option('Jaune.Www', 'WWW', 'upperCamel', rule='3')
        self.option('Jaune.Vvv', 'VVV', 'upperCamel')
        self.policy['derived'] = {new: dict(old=old, bases=bases)}
        return self.lint(new)

    def test_compound_derived_row_needs_a_bound_cited_base_for_each_sourced_rule(self):
        both = ['Jaune.Yzz', 'Jaune.Www']
        self.assertEqual(self.register_compound('Jaune.Zzz.readQqq', 'Jaune.Yzz.readWww', both), [])
        self.assertEqual(self.register_compound('Jaune.readQqq_Zzz', 'Jaune.readWww_Yzz', both), [])
        # A changed suffix is admitted, but only the bound spellings are credited.
        found = self.register_compound('Jaune.Zzz.qxzQqq', 'Jaune.Yzz.qxzqWww', both)
        self.assertEqual([(f['reason'], f['tokens']) for f in found], [('unregistered word or source', ['qxzq'])])
        self.assertEqual(self.register_compound('Jaune.Zzz.read', 'Jaune.Yzz.read', ['Jaune.Yzz'], rule='1, 5, 7',
                                                layer='adapter'), [])
        for bases, rule, message in (
                (['Jaune.Yzz'], '1, 3, 7', 'lacks a base for each sourced rule'),
                (both, '1, 7', 'does not list the rule'),
                (['Jaune.Yzz', 'Jaune.Vvv'], '1, 3, 7', 'one known old name'),
                (['Jaune.Yzz', 'Jaune.Missing'], '1, 3, 7', 'one known old name'),
                ([], '1, 3, 7', 'lacks matching map row'),
                ([['Jaune.Yzz']], '1, 3, 7', 'invalid derived base')):
            with self.assertRaisesRegex(ValueError, message):
                self.register_compound('Jaune.Zzz.readQqq', 'Jaune.Yzz.readWww', bases, rule=rule)
        with self.assertRaisesRegex(ValueError, 'does not name the rename of Jaune.Www'):
            self.register_compound('Jaune.Zzz.readQqq', 'Jaune.Yzz.readWww', both,
                                   source='Derived by token: `Zzz` -> `Yzz` (synthetic) [B]; `Kqq` -> `Www` (other) [M]')
        with self.assertRaisesRegex(ValueError, 'another layer'):
            self.register_compound('Jaune.Zzz.readQqq', 'Jaune.Yzz.readWww', both, layer='consensus')
        # The sourced spelling must stand where the old token stood: no mid-token or missing change.
        for old, new in (('Jaune.readZzzy_Qqq', 'Jaune.readYzzy_Www'), ('Jaune.readZzz_Qqq', 'Jaune.readKqq_Www'),
                         ('Jaune.read_Qqq', 'Jaune.readYzz_Www')):
            with self.assertRaisesRegex(ValueError, 'extends beyond sourced component Jaune.Yzz'):
                self.register_compound(old, new, both)
        self.register_compound('Jaune.Zzz.readQqq', 'Jaune.Yzz.readWww', both)
        self.policy['derived']['Jaune.Yzz.readWww']['old'] = 'Jaune.Zzz.readKqq'
        with self.assertRaisesRegex(ValueError, 'lacks matching map row'):
            self.lint('Jaune.Yzz.readWww')

    def test_compound_base_may_be_a_bound_namespace_with_its_stated_old_name(self):
        source = 'Derived by token: `Jaune.Uuu` -> `Vvv` (synthetic plural) [M]'
        stated = [dict(name='Jaune.Vvv', old='Jaune.Uuu')]
        self.assertEqual(self.register_compound('Jaune.Uuu.read', 'Jaune.Vvv.read', stated, rule='1, 7',
                                                source=source), [])
        self.assertEqual(self.register_compound('Jaune.readUuu', 'Jaune.readVvv', stated, rule='1, 7',
                                                source='`Uuu` -> `Vvv`'), [])
        with self.assertRaisesRegex(ValueError, 'does not name the rename'):
            self.register_compound('Jaune.Uuu.read', 'Jaune.Vvv.read', [dict(name='Jaune.Vvv', old='Jaune.Kqq')],
                                   rule='1, 7', source=source)
        with self.assertRaisesRegex(ValueError, 'one known old name'):
            self.register_compound('Jaune.Uuu.read', 'Jaune.Vvv.read', [dict(name='Jaune.Yzz', old='Jaune.Uuu')],
                                   rule='1, 7', source=source)
        self.register_compound('Jaune.Uuu.read', 'Jaune.Vvv.read', stated, rule='1, 7', source=source)
        pair = self.bundle()
        result = LINT.check(self.root, self.mapping, self.policy, self.root, [pair], ['Jaune'])
        self.assertIn('Jaune.Vvv.read', [p['name'] for p in result['problems']
                                       if p['reason'] == 'unused source binding'])

    def test_rule_seven_binding_needs_a_lean_ecosystem_source(self):
        # Rule 7: the name Lean core gives the same definition (`Nat.decEq`, `BitVec.neg`).
        raw = ('def decEq {a : Sort u} [inst : DecidableEq a] (a b : a) : Decidable (Eq a b) :=\n'
               'protected def neg (x : BitVec n) : BitVec n := .ofNat n (2^n - x.toNat)\n').encode()
        (self.root / 'lean.txt').write_bytes(raw)
        self.policy['sources']['lean'] = dict(path='lean.txt', sha256=LINT.sha(raw),
                                              citation='leanprover/lean4 v4.35.0 at ' + 'e' * 40 + ', src/Init/Prelude.lean')
        self.policy['words'] += ['list', 'one']
        names = ('Jaune.Value.decEq', 'Jaune.Value.decEq.decEqList', 'Jaune.Value.negOne')
        self.assertEqual([p['segment'] for p in self.lint(*names)],
                         ['Jaune.Value.decEq', 'Jaune.Value.decEq', 'Jaune.Value.decEq.decEqList', 'Jaune.Value.negOne'])
        lean = dict(rule='7', source='lean', style='lowerCamel')
        self.policy['bindings'] = {'Jaune.Value.decEq': dict(lean, spelling='decEq'),
                                   'Jaune.Value.decEq.decEqList': dict(lean, spelling='decEq', component='decEq'),
                                   'Jaune.Value.negOne': dict(lean, spelling='neg', component='neg')}
        self.assertEqual(self.lint(*names), [])
        # The spelling stays exact, and only a Lean core, Std, Batteries or Mathlib file carries rule 7.
        self.policy['bindings']['Jaune.Value.negOne']['spelling'] = 'negOne'
        with self.assertRaisesRegex(ValueError, 'spelling absent'):
            self.lint(*names)
        self.policy['bindings']['Jaune.Value.negOne']['spelling'] = 'neg'
        for citation in ('ethereum/execution-specs at ' + 'e' * 40, 'Synthetic leanprover/lean4 fixture'):
            self.policy['sources']['lean']['citation'] = citation
            with self.assertRaisesRegex(ValueError, 'rule 7 binding needs a Lean'):
                self.lint(*names)
        self.policy['sources']['lean']['citation'] = 'leanprover-community/mathlib4 at ' + 'e' * 40
        self.assertEqual(self.lint(*names), [])
        self.policy['bindings']['Jaune.Value.decEq']['rule'] = '6'
        with self.assertRaisesRegex(ValueError, 'invalid source binding'):
            self.lint(*names)

    def product_bundle(self, source, name, kind, pool, root, value=None):
        path = self.root / source
        path.parent.mkdir(parents=True, exist_ok=True)
        last = name.split('.')[-1]
        text = f'def {last} := 1\n'
        path.write_text(text)
        module = source[:-5].replace('/', '.')
        payload = {'theorem': ['theorem'], 'definition': ['definition', 'safe', value]}[kind]
        index = dict(version=5, module=module, references={},
                     decls={name: [0, 0, 0, len(text) - 1, 0, 4, 0, 4 + len(last)]})
        bundle = self.root / (module + '.json')
        bundle.write_text(json.dumps(dict(source=text, index=index, expr_pool=pool, level_pool=[['zero']],
                                          constants={name: {'kernel': {'payload': payload, 'type': root}}})))
        return source, str(bundle)

    def test_theorem_spells_a_product_name_that_passes_where_it_is_declared(self):
        self.policy['words'] += ['settled', 'mono', 'run', 'to']
        # `def SettledGasLe (n : Nat) : Exit -> Prop` in one file: the `≤` of its body names it.
        predicate = [['sort', 0], ['const', ['name', 'LE.le'], []]]
        defining = self.product_bundle('Jaune/A.lean', 'Jaune.SettledGasLe', 'definition', predicate, 0, 1)
        # A theorem in another file about it, one whose statement uses it, and a definition that uses it.
        uses = [['const', ['name', 'Jaune.SettledGasLe'], []], ['const', ['name', 'Nat'], []], ['app', 0, 1]]
        mono = self.product_bundle('Jaune/B.lean', 'Jaune.SettledGasLe.mono', 'theorem', uses, 2)
        run = self.product_bundle('Jaune/C.lean', 'Jaune.run_settledGasLe', 'theorem', uses, 2)
        data = self.product_bundle('Jaune/D.lean', 'Jaune.toSettledGasLe', 'definition', uses, 2, 0)

        def segments(*files):
            result = LINT.check(self.root, self.mapping, self.policy, self.root, list(files), [])
            return sorted((p['segment'], tuple(p['tokens'])) for p in result['problems'])

        self.assertEqual(segments(defining, mono, run, data), [('Jaune.toSettledGasLe', ('Le',))])
        # Without the declaring file the name has no evidence.
        self.assertEqual(segments(mono, run), [('Jaune.SettledGasLe', ('Le',)), ('Jaune.run_settledGasLe', ('Le',))])
        # A referenced name that fails where it is declared credits nothing.
        self.policy['words'].remove('settled')
        self.assertEqual([s for s, _ in segments(defining, mono, run)],
                         ['Jaune.SettledGasLe', 'Jaune.SettledGasLe', 'Jaune.run_settledGasLe'])

    # Freeze additions (jsn-u9 F): Lean conventions for the vocabulary residue.
    def register_text(self, key, text):
        raw = text.encode()
        (self.root / (key + '.txt')).write_bytes(raw)
        self.policy['sources'][key] = dict(path=key + '.txt', sha256=LINT.sha(raw), citation='Synthetic Lean source')

    def test_leading_core_type_in_lower_camel_case_needs_its_lean_source(self):
        names = ('Jaune.natValue', 'Jaune.Value.bool', 'Jaune.boolField')
        self.assertEqual(sorted(t for p in self.lint(*names) for t in p['tokens']), ['bool', 'bool', 'nat'])
        self.register_text('lean4-prelude', 'inductive Bool : Type where\ninductive Nat where\n')
        # The type alone is not enough: the naming convention must be registered too.
        self.assertTrue(self.lint('Jaune.natValue'))
        self.register_text('lean4-std-naming', '* When encountering a name, put it in lower camel case.\n')
        self.assertEqual(self.lint(*names), [])
        # Only the leading token of the declaration's own component, and only a registered type.
        self.assertEqual(self.lint('Jaune.read_nat')[0]['tokens'], ['nat'])
        self.assertEqual(self.lint('Jaune.valueNatural')[0]['tokens'], ['Natural'])
        self.assertEqual(self.lint('Jaune.intValue')[0]['tokens'], ['int'])
        self.register_text('lean4-int-basic', 'inductive Int : Type where\n')
        self.assertEqual(self.lint('Jaune.intValue'), [])

    def instance_evidence(self, name, pool, root, instance=True):
        attributes = {'instance': ['instance', 1000, [1], 'global', 0]} if instance else {}
        extra = {name: {'attributes': attributes, 'kernel': {'payload': ['definition', 'safe', 0], 'type': root}}}
        return self.statement(name, 'definition', pool, root, value=0, extra=extra)

    def test_instance_spelled_as_lean_would_name_it(self):
        # `instance {c : Bool} : BEq (Value c)` is `instBEqValue` (Lean.Elab.mkInstanceName).
        pool = [['const', ['name', 'BEq'], []], ['const', ['name', 'Jaune.Value'], []], ['bvar', 0],
                ['app', 1, 2], ['app', 0, 3], ['const', ['name', 'Bool'], []], ['forall', 'implicit', 5, 4]]
        name = 'Jaune.instBEqValue'
        evidence = self.instance_evidence(name, pool, 6)
        self.assertEqual(evidence[name].instance_name, 'instBEqValue')
        self.assertTrue(self.lean_lint(name, evidence))
        self.register_text('lean4-decl-name-gen',
                           'runTermElabM fun _ => NameGen.mkBaseNameWithSuffix\' "inst" binders type\n')
        self.assertEqual(self.lean_lint(name, evidence), [])
        # Another spelling, a non-instance and a name Lean would suffix with the project are refused.
        self.assertTrue(self.lean_lint('Jaune.instValueBEq', self.instance_evidence('Jaune.instValueBEq', pool, 6)))
        self.assertTrue(self.lean_lint(name, self.instance_evidence(name, pool, 6, instance=False)))
        foreign = [['const', ['name', 'BEq'], []], ['const', ['name', 'Nat'], []], ['app', 0, 1]]
        evidence = self.instance_evidence('Jaune.instBEqNat', foreign, 2)
        self.assertEqual(evidence['Jaune.instBEqNat'].instance_name, 'instBEqNat_jaune')
        self.assertTrue(self.lean_lint('Jaune.instBEqNat', evidence))
        # A non-dependent instance-implicit binder that renders to something new adds `Of`.
        hyp = [['const', ['name', 'Jaune.Value'], []], ['const', ['name', 'Repr'], []], ['app', 1, 0],
               ['const', ['name', 'Hashable'], []], ['app', 3, 0], ['forall', 'instImplicit', 4, 2]]
        evidence = self.instance_evidence('Jaune.instReprValueOfHashable', hyp, 5)
        self.assertEqual(evidence['Jaune.instReprValueOfHashable'].instance_name, 'instReprValueOfHashable')

    def test_beq_and_elim_are_lean_keywords_with_their_prelude_source(self):
        names = ('Jaune.value_beq', 'Jaune.read_elim')
        evidence = {n: self.statement(n, 'theorem', self.LE_POOL, 2)[n] for n in names}
        words = LINT.validate_policy(self.policy, self.root)
        found = LINT.lint_names(dict.fromkeys(names, []), self.mapping, self.policy, words, reference_endings=evidence)[0]
        self.assertEqual(sorted(t for p in found for t in p['tokens']), ['beq', 'elim'])
        self.register_text('lean4-prelude', '@[macro_inline] def False.elim {C : Sort u} (h : False) : C :=\n'
                                            'def Nat.beq : (@& Nat) → (@& Nat) → Bool\n')
        words = LINT.validate_policy(self.policy, self.root)
        self.assertEqual(LINT.lint_names(dict.fromkeys(names, []), self.mapping, self.policy, words,
                                         reference_endings=evidence)[0], [])
        # Keywords name theorems; a definition `beq` is still a word to register or bind.
        self.assertTrue(self.lean_lint('Jaune.Value.beq', self.statement('Jaune.Value.beq', 'definition',
                                                                         self.LE_POOL, 2, value=1)))

    def test_compiler_generated_aux_namespace_of_the_declaring_module(self):
        name = 'Jaune._aux_Jaune_Test___elabRules_Jaune_tacticRead_1.read'
        words = LINT.validate_policy(self.policy, self.root)
        self.assertTrue(LINT.lint_names({name: []}, self.mapping, self.policy, words, module='Jaune.Test')[0])
        self.register_text('lean4-elab-auxdef', '    let id := `_aux ++ (← getMainModule) ++ `_ ++ id\n')
        words = LINT.validate_policy(self.policy, self.root)
        self.assertEqual(LINT.lint_names({name: []}, self.mapping, self.policy, words, module='Jaune.Test')[0], [])
        # Only the declaring module's own generated prefix, and only when the module is known.
        self.assertTrue(LINT.lint_names({name: []}, self.mapping, self.policy, words, module='Jaune.Other')[0])
        self.assertTrue(LINT.lint_names({name: []}, self.mapping, self.policy, words)[0])
        self.assertTrue(LINT.lint_names({'Jaune._aux_Jaune_Test_read.read': []}, self.mapping, self.policy, words,
                                        module='Jaune.Test')[0])

    def test_final_component_keeps_the_referenced_lean_constants_punctuation(self):
        pool = [['const', ['name', 'GetElem?.getElem?'], []], ['const', ['name', 'Nat'], []], ['app', 0, 1]]
        name = 'Jaune.read_getElem?'
        self.assertEqual(self.lean_lint(name, self.statement(name, 'theorem', pool, 2)), [])
        # Not when the statement does not use it, nor for a definition.
        self.assertTrue(self.lean_lint(name, self.statement(name, 'theorem', self.LE_POOL, 2)))
        self.assertTrue(self.lean_lint(name, self.statement(name, 'definition', pool, 2, value=1)))
        # `getElem!` is a different constant.
        self.assertTrue(self.lean_lint('Jaune.read_getElem!', self.statement('Jaune.read_getElem!', 'theorem', pool, 2)))

    def test_binding_may_back_another_rule_the_row_lists(self):
        # Master ruling R15: `B256.neg` -> `U256.neg`, rule `3, 7`: rule 3 renames
        # the namespace token (bound at `Jaune.U256`), rule 7 is the kept leaf
        # (Lean's `BitVec.neg`), evidenced by the name's own direct binding.
        raw = ('def decEq {a : Sort u} [inst : DecidableEq a] (a b : a) : Decidable (Eq a b) :=\n'
               'protected def neg (x : BitVec n) : BitVec n := .ofNat n (2^n - x.toNat)\n'
               'Qww Yzz GT\n').encode()
        (self.root / 'lean.txt').write_bytes(raw)
        (self.root / 'spec.txt').write_bytes(raw)
        self.policy['sources']['lean'] = dict(path='lean.txt', sha256=LINT.sha(raw),
                                              citation='leanprover/lean4 v4.35.0 at ' + 'e' * 40 + ', src/Init/Prelude.lean')
        self.policy['sources']['spec'] = dict(path='spec.txt', sha256=LINT.sha(raw), citation='Synthetic spec fixture')
        self.policy['words'] += ['list', 'one', 'check']
        def row(old, new, rule):
            return dict(old=old, new=new, kind='declaration', layer='execution', rule=rule, source='synthetic')
        self.mapping = dict(self.mapping, entries=list(self.mapping['entries']) + [
            row('Jaune.Zzz', 'Jaune.Yzz', '3'), row('Jaune.Zzz.neg', 'Jaune.Yzz.neg', '3, 7'),
            row('Jaune.Zzz.negOne', 'Jaune.Yzz.negOne', '3, 7'), row('Jaune.Zzz.decEq', 'Jaune.Yzz.decEq', '3, 7'),
            row('Jaune.Zzz.decEq.decEqList', 'Jaune.Yzz.decEq.decEqList', '3, 7'),
            row('Jaune.Ppp', 'Jaune.Qww', '1'), row('Jaune.Ppp.decEq', 'Jaune.Qww.decEq', '1, 7'),
            row('Jaune.Zzz.gtCheck', 'Jaune.Yzz.gtCheck', '3, 7')])
        lean = dict(rule='7', source='lean', style='lowerCamel')
        base = {'Jaune.Yzz': dict(rule='3', source='spec', spelling='Yzz', style='verbatim'),
                'Jaune.Qww': dict(rule='1', source='spec', spelling='Qww', style='verbatim'),
                'Jaune.Yzz.neg': dict(lean, spelling='neg'),
                'Jaune.Yzz.negOne': dict(lean, spelling='neg', component='neg'),
                'Jaune.Yzz.decEq': dict(lean, spelling='decEq'),
                'Jaune.Yzz.decEq.decEqList': dict(lean, spelling='decEq', component='decEq'),
                'Jaune.Qww.decEq': dict(lean, spelling='decEq')}
        names = ('Jaune.Yzz', 'Jaune.Qww', 'Jaune.Yzz.neg', 'Jaune.Yzz.negOne', 'Jaune.Yzz.decEq',
                 'Jaune.Yzz.decEq.decEqList', 'Jaune.Qww.decEq')
        self.policy['bindings'] = dict(base)
        self.assertEqual(self.lint(*names), [])
        reasons = lambda *ns: [(p['name'], p['reason']) for p in self.lint(*ns)]
        # Control: a binding under a rule the row does not list.
        self.policy['bindings'] = dict(base, **{'Jaune.Yzz.gtCheck': dict(rule='1', source='spec', spelling='GT',
                                                                         style='lowerCamel', component='gt')})
        self.assertIn(('Jaune.Yzz.gtCheck', 'map requires matching source binding'), reasons('Jaune.Yzz', 'Jaune.Yzz.gtCheck'))
        # Control: the renamed namespace token's rule has no backing.
        self.policy['bindings'] = {k: v for k, v in base.items() if k != 'Jaune.Yzz'}
        self.assertIn(('Jaune.Yzz.neg', 'map requires matching source binding'), reasons('Jaune.Yzz.neg'))
        self.policy['bindings'] = dict(base, **{'Jaune.Yzz': dict(base['Jaune.Yzz'], rule='1')})
        self.assertIn(('Jaune.Yzz.neg', 'map requires matching source binding'), reasons('Jaune.Yzz.neg'))
        # Control: the backing base must be the rename of the row's own old namespace.
        self.policy['bindings'] = dict(base)
        self.mapping['entries'].append(row('Jaune.Www.neg', 'Jaune.Yzz.negWww', '3, 7'))
        self.policy['bindings']['Jaune.Yzz.negWww'] = dict(lean, spelling='neg', component='neg')
        self.policy['words'] += ['www']
        self.assertIn(('Jaune.Yzz.negWww', 'map requires matching source binding'), reasons('Jaune.Yzz', 'Jaune.Yzz.negWww'))
        # Control: a binding that covers no token of the name is refused by policy
        # validation before this rule runs (`source_form`).
        self.policy['bindings'] = dict(base, **{'Jaune.Yzz.neg': dict(lean, spelling='decEq')})
        with self.assertRaisesRegex(ValueError, 'spelling/case mismatch'):
            self.lint(*names)

    def r15_fixture(self):
        raw = ('protected def neg (x : BitVec n) : BitVec n := .ofNat n (2^n - x.toNat)\n'
               'Qww Yzz Ooo GT EXP\n').encode()
        (self.root / 'lean.txt').write_bytes(raw)
        (self.root / 'spec.txt').write_bytes(raw)
        self.policy['sources']['lean'] = dict(path='lean.txt', sha256=LINT.sha(raw),
                                              citation='leanprover/lean4 v4.35.0 at ' + 'e' * 40 + ', src/Init/Prelude.lean')
        self.policy['sources']['spec'] = dict(path='spec.txt', sha256=LINT.sha(raw), citation='Synthetic spec fixture')
        self.policy['words'] += ['check', 'extra', 'word', 'sub', 'x', 'bad', 'old']
        lean = dict(rule='7', source='lean', style='lowerCamel')
        base = {'Jaune.Yzz': dict(rule='3', source='spec', spelling='Yzz', style='verbatim'),
                'Jaune.Qww': dict(rule='1', source='spec', spelling='Qww', style='verbatim'),
                'Jaune.Ooo': dict(rule='1', source='spec', spelling='Ooo', style='verbatim')}
        self.policy['bindings'] = dict(base)
        def row(old, new, rule, kind='declaration', layer='execution'):
            return dict(old=old, new=new, kind=kind, layer=layer, rule=rule, source='synthetic')
        def reasons(name, rows, binding):
            self.mapping = dict(self.mapping, entries=[r for r in self.mapping['entries']
                                                       if not r['new'].startswith(('Jaune.Yzz', 'Jaune.Qww', 'Jaune.Ooo'))] + rows)
            self.policy['bindings'] = dict(base, **{name: binding})
            return [p['reason'] for p in self.lint(name) if p['name'] == name]
        return lean, row, reasons

    def test_listed_rules_are_all_backed_hardened(self):
        # Neon finding 4, R17: each counterexample now fails.
        lean, row, reasons = self.r15_fixture()
        bad = 'map requires matching source binding'
        neg = dict(lean, spelling='neg')
        yzz = row('Jaune.Zzz', 'Jaune.Yzz', '3')
        # The cases R15 was made for still pass.
        self.assertEqual(reasons('Jaune.Yzz.neg', [yzz, row('Jaune.Zzz.neg', 'Jaune.Yzz.neg', '3, 7')], neg), [])
        gt = dict(rule='1', source='spec', spelling='GT', style='lowerCamel', component='gt')
        self.assertEqual(reasons('Jaune.Yzz.gtCheck', [yzz, row('Jaune.Zzz.gtCheck', 'Jaune.Yzz.gtCheck', '3, 1, 7')],
                                 gt), [])
        # 4.1: a relocation prefix row (`old == new`) backs nothing.
        reloc = row('Jaune.Ooo', 'Jaune.Ooo', '1', kind='relocation')
        self.assertIn(bad, reasons('Jaune.Ooo.neg', [reloc, row('Jaune.Ooo.badOld', 'Jaune.Ooo.neg', '1, 7')], neg))
        # 4.2: the prefix row's layer must be the row's.
        self.assertIn(bad, reasons('Jaune.Yzz.neg', [row('Jaune.Zzz', 'Jaune.Yzz', '3', layer='consensus'),
                                                     row('Jaune.Zzz.neg', 'Jaune.Yzz.neg', '3, 7')], neg))
        # 4.2: the rest of the name is kept: no other leaf, no depth change.
        negc = dict(lean, spelling='neg', component='neg')
        self.assertIn(bad, reasons('Jaune.Yzz.negExtraWord',
                                   [yzz, row('Jaune.Zzz.unrelatedOld', 'Jaune.Yzz.negExtraWord', '3, 7')], negc))
        self.assertIn(bad, reasons('Jaune.Yzz.neg', [yzz, row('Jaune.Zzz.Sub.x', 'Jaune.Yzz.neg', '3, 7')], neg))
        # A leaf the direct binding spells whole may change (`bexp` -> `exp`, rule 1).
        exp = dict(rule='1', source='spec', spelling='EXP', style='lowerCamel')
        self.assertEqual(reasons('Jaune.Yzz.exp', [yzz, row('Jaune.Zzz.bexp', 'Jaune.Yzz.exp', '1, 3, 7')], exp), [])
        self.assertIn(bad, reasons('Jaune.Yzz.exp', [yzz, row('Jaune.Zzz.Sub.bexp', 'Jaune.Yzz.exp', '1, 3, 7')], exp))
        # 4.3: a binding under the primary rule no longer short-circuits the
        # other listed rules 1-3 (rule 3 has no prefix row here).
        self.assertIn(bad, reasons('Jaune.Yzz.exp', [row('Jaune.Zzz.bexp', 'Jaune.Yzz.exp', '1, 3, 7')], exp))
        # A single listed rule 1-3 bound under it stays as before.
        self.assertEqual(reasons('Jaune.Yzz.exp', [row('Jaune.Zzz.bexp', 'Jaune.Yzz.exp', '1, 7')], exp), [])
        # R20 (Neon-3 finding 2): a rule 1-3 listed after another rule is
        # checked too: `7, 3` and `4, 1` with no binding at all are findings.
        for rule in ('7, 3', '4, 1'):
            self.mapping = dict(self.mapping, entries=[r for r in self.mapping['entries']
                                                       if not r['new'].startswith('Jaune.Yzz')] +
                                [row('Jaune.Zzz.word', 'Jaune.Yzz.word', rule)])
            self.policy['bindings'] = {'Jaune.Yzz': dict(rule='3', source='spec', spelling='Yzz', style='verbatim')}
            self.assertIn(bad, [p['reason'] for p in self.lint('Jaune.Yzz.word') if p['name'] == 'Jaune.Yzz.word'])
        # ... and passes when every listed rule 1-3 is backed (`7, 3`: rule 7
        # direct binding for the kept leaf, rule 3 by the renamed prefix).
        self.assertEqual(reasons('Jaune.Yzz.neg', [yzz, row('Jaune.Zzz.neg', 'Jaune.Yzz.neg', '7, 3')], neg), [])

    def test_root_spelled_declaration_is_linted(self):
        # Neon finding 5, R17: `_root_.N.x` spells the whole name, as N4 reads it.
        text = 'theorem _root_.Jaune.value : True := trivial\n'
        self.assertTrue(LINT.spelled(text, 8, 8 + len('_root_.Jaune.value'), 'Jaune.value'))
        self.assertFalse(LINT.spelled(text, 8, 8 + len('_root_.Jaune.value'), 'Jaune.Other.value'))
        self.assertFalse(LINT.spelled('theorem _root_.value : True', 8, 8 + len('_root_.value'), 'Jaune.value'))
        self.assertFalse(LINT.spelled('theorem _root_ : True', 8, 14, 'Jaune.value'))
        index = dict(version=5, module='Jaune.Test', references={},
                     decls={'Jaune.value': [0, 0, 0, len(text) - 1, 0, 8, 0, 8 + len('_root_.Jaune.value')]})
        self.assertEqual(LINT.declarations(text, index), {'Jaune.value': [0, 8, 0, 8 + len('_root_.Jaune.value')]})

    def test_malformed_policy_refused(self):
        for policy in ([], {}, dict(self.policy, words=['bal', 'bal']),
                       dict(self.policy, sources={'bad': {'citation': 1}})):
            with self.assertRaises(ValueError):
                LINT.validate_policy(policy, self.root)


if __name__ == '__main__':
    unittest.main()
