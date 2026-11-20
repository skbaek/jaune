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

    def test_malformed_policy_refused(self):
        for policy in ([], {}, dict(self.policy, words=['bal', 'bal']),
                       dict(self.policy, sources={'bad': {'citation': 1}})):
            with self.assertRaises(ValueError):
                LINT.validate_policy(policy, self.root)


if __name__ == '__main__':
    unittest.main()
