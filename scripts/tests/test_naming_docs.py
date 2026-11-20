import importlib.util
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('naming_docs', ROOT / 'scripts/naming-docs.py')
DOCS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(DOCS)


class DeletedDocumentationNames(unittest.TestCase):
    def setUp(self):
        tmp = tempfile.TemporaryDirectory()
        self.addCleanup(tmp.cleanup)
        root = Path(tmp.name)
        self.head = 'a' * 40
        self.snapshot = root / 'snapshot.json'
        self.snapshot.write_text(json.dumps({
            'candidate': {'head': self.head, 'modules': {'Jaune.Current': {'path': 'Jaune/Current.lean'}}},
            'exports': {'Jaune.Current': {'path': 'current.json'}},
        }))
        (root / 'current.json').write_text(json.dumps({'constants': dict.fromkeys([
            'Jaune.Checked.keep', 'Jaune.NewFrame.step', 'Jaune.OldType.live_member', 'Jaune.Current',
        ])}))
        self.mapping = {'entries': [{'kind': 'namespace', 'old': 'Jaune.Checked', 'new': 'Jaune.Frame'}]}
        deleted = ['Jaune.Frame.keep', 'Jaune.OldType', 'Jaune.Frame.lost', 'Jaune.OldType.run_call',
                   'Jaune.OldType.run_create', '_private.Jaune.Old.0.Jaune.OldType.helper']
        self.receipt = {
            'schema_version': 1, 'verdict': 'OK', 'unbound_rehearsal': False,
            'before': {'bound': True}, 'after': {'bound': True, 'revision': self.head},
            'deleted_declarations': len(deleted), 'deleted': {'Jaune.Old': [{'name': n} for n in deleted]},
            'modules': {'deleted': ['Jaune.Old', 'Historical.Current']},
        }

    def scan(self, document):
        index = DOCS.Index(self.snapshot, self.mapping, deletion=self.receipt)
        return DOCS.findings(document, index)

    def test_point_at_deletions_and_keep_ordinary_substitutions(self):
        findings = self.scan('`Checked.keep` `OldType.helper` `Jaune/Old.lean` `Old.lean`')
        self.assertEqual([(row['old'], row['candidates'], row['unique']) for row in findings], [
            ('Checked.keep', ['Frame.keep'], True),
            ('OldType.helper', [], False), ('Jaune/Old.lean', [], False), ('Old.lean', [], False),
        ])
        self.assertEqual(findings[1]['rows'], ['deleted Jaune.OldType.helper'])

    def test_reoccupied_names_and_basenames_stay_live(self):
        self.assertEqual(self.scan('`Frame.keep` and `Jaune.OldType.live_member` in `Current.lean`'), [])

    def test_contextual_forms_never_substitute_for_a_deleted_name(self):
        findings = self.scan('`Frame` (`keep`, `lost`), `OldType.run_*` and `OldType.run_{call,create}`.')
        self.assertEqual([row['old'] for row in findings], ['lost', 'OldType.run_', 'OldType.run_{call,create}'])
        self.assertTrue(all(not row['unique'] for row in findings))

    def test_requires_passing_bound_complete_receipt(self):
        for overrides in ({'unbound_rehearsal': True}, {'verdict': 'FAILED'}, {'before': {'bound': False}},
                          {'deleted_declarations': 0}):
            with self.subTest(overrides=overrides), self.assertRaises(ValueError):
                DOCS.Index(self.snapshot, self.mapping, deletion={**self.receipt, **overrides})

    def test_intervening_commits_must_descend_from_delete(self):
        earlier = 'b' * 40
        self.receipt['after']['revision'] = earlier
        with patch.object(DOCS.subprocess, 'run') as check:
            check.return_value.returncode = 0
            self.scan('`Frame.keep`')
            check.assert_called_once_with(['git', 'merge-base', '--is-ancestor', earlier, self.head], cwd=ROOT)
            check.return_value.returncode = 1
            with self.assertRaisesRegex(ValueError, 'ancestor'):
                self.scan('`Frame.keep`')
