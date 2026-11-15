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
        index = dict(version=5, module=module, decls={name: [0, 0, 0, 14, 0, 4, 0, 9]}, references={})
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

    def test_malformed_policy_refused(self):
        for policy in ([], {}, dict(self.policy, words=['bal', 'bal']),
                       dict(self.policy, sources={'bad': {'citation': 1}})):
            with self.assertRaises(ValueError):
                LINT.validate_policy(policy, self.root)


if __name__ == '__main__':
    unittest.main()
