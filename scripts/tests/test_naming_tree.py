import copy
import importlib.util
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).parents[2]
SPEC = importlib.util.spec_from_file_location('naming_tree', ROOT / 'scripts/naming-tree.py')
TREE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(TREE)


class NamingTreeTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.directory = Path(self.temp.name)
        self.root = self.directory / 'repo'
        self.root.mkdir()
        self.source = 'def client := Old.value\n'
        (self.root / 'Indexed.lean').write_text(self.source)
        (self.root / 'Other.lean').write_text('def other := 0\n')
        (self.root / 'lakefile.lean').write_text('-- configuration\n')
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        subprocess.run(['git', '-C', str(self.root), 'add', '.'], check=True)
        subprocess.run(['git', '-C', str(self.root), '-c', 'user.name=Fixture',
                        '-c', 'user.email=fixture@example.invalid', '-c', 'commit.gpgsign=false',
                        'commit', '-qm', 'fixture'], check=True)
        self.map = self.directory / 'map.json'
        self.mapping = dict(schema_version=1, retired_tokens=[], allowed_abbreviations=[], entries=[
            dict(old='Old.value', new='Old.renamed', kind='declaration', layer='execution',
                 rule='4', source='Synthetic tree coverage control')])
        self.map.write_text(json.dumps(self.mapping))
        self.capture = self.directory / 'capture'
        self.capture.mkdir()
        self.snapshot = self.capture / 'snapshot.json'
        self.make_snapshot()

    def make_snapshot(self):
        candidate = TREE.CANDIDATE.inventory(self.root, ['.'])
        source = copy.deepcopy(candidate)
        headers = dict(schema_version=1, lean_version='fixture', modules={})
        for name, row in candidate['modules'].items():
            row.update(imports=[], is_module=False)
            headers['modules'][name] = dict(path=row['path'], is_module=False, direct_imports=[])
        index = dict(version=5, module='Indexed', directImports=[], decls={}, references={
            json.dumps({'c': {'m': 'Old', 'n': 'Old.value'}}):
                dict(definition=None, usages=[[0, 14, 0, 23]])})
        export = dict(schema_version=5, lean_version='fixture', source=self.source,
                      index=index, constants={}, guards=[], attribute_syntax=[],
                      checked_commands=[], imports={})
        self.export = self.capture / 'Indexed.json'
        self.export.write_text(json.dumps(export))
        (self.capture / 'headers.json').write_text(json.dumps(headers))
        (self.capture / 'source-before.json').write_text(json.dumps(source))
        snapshot = dict(schema_version=2, status='OK', build=dict(exit=0),
                        candidate=candidate, roots=['Indexed'], selected=['Indexed'],
                        exports={'Indexed': dict(path='Indexed.json', sha256=TREE.CANDIDATE.file_sha(self.export))},
                        headers_sha256=TREE.CANDIDATE.file_sha(self.capture / 'headers.json'),
                        tool_sources={}, artifacts={}, local_built={})
        self.snapshot.write_text(json.dumps(snapshot))

    def plan(self):
        return TREE.build_plan(self.root, self.snapshot, self.map)

    def test_all_lean_sources_are_accounted_for(self):
        plan = self.plan()
        self.assertEqual(plan['status'], 'planned')
        self.assertEqual([r['path'] for r in plan['files']],
                         ['Indexed.lean', 'Other.lean', 'lakefile.lean'])
        self.assertEqual([r['indexed'] for r in plan['files']], [True, False, False])
        self.assertEqual(TREE.apply_plan(self.root, plan, self.map), 1)
        self.assertEqual((self.root / 'Indexed.lean').read_text(), 'def client := Old.renamed\n')

    def test_standalone_capture_requires_exact_producer_partition(self):
        data = json.loads(self.snapshot.read_text())
        data.update(schema_version=3, source_only=['Indexed'], producers=[])
        self.snapshot.write_text(json.dumps(data))
        self.assertEqual(self.plan()['status'], 'planned')
        data['source_only'] = []
        self.snapshot.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'producer artifact inventory'):
            self.plan()
        data['source_only'] = ['Indexed']
        data['local_built'] = {'Indexed': {}}
        self.snapshot.write_text(json.dumps(data))
        with self.assertRaisesRegex(ValueError, 'producer artifact inventory'):
            self.plan()
        self.assertEqual((self.root / 'Indexed.lean').read_text(), self.source)

    def test_missing_affected_export_is_reported_and_cannot_apply(self):
        (self.root / 'Other.lean').write_text('def other := Old.value\n')
        self.make_snapshot()
        plan = self.plan()
        self.assertEqual(plan['status'], 'unresolved')
        self.assertIn('no compiler export', plan['files'][1]['unresolved'][0]['reason'])
        with self.assertRaisesRegex(ValueError, 'fully resolved'):
            TREE.apply_plan(self.root, plan, self.map)
        self.assertEqual((self.root / 'Indexed.lean').read_text(), self.source)

    def test_configuration_source_is_not_silently_excluded(self):
        (self.root / 'lakefile.lean').write_text('def target := Old.value\n')
        self.make_snapshot()
        self.assertEqual(self.plan()['status'], 'unresolved')

    def test_added_file_after_plan_refuses_before_any_write(self):
        plan = self.plan()
        (self.root / 'Late.lean').write_text('def late := Old.value\n')
        with self.assertRaisesRegex(ValueError, 'inventory changed'):
            TREE.apply_plan(self.root, plan, self.map)
        self.assertEqual((self.root / 'Indexed.lean').read_text(), self.source)

    def test_changed_unindexed_file_refuses_before_any_write(self):
        plan = self.plan()
        (self.root / 'Other.lean').write_text('def other := 1\n')
        with self.assertRaisesRegex(ValueError, 'inventory changed'):
            TREE.apply_plan(self.root, plan, self.map)
        self.assertEqual((self.root / 'Indexed.lean').read_text(), self.source)

    def test_removed_file_refuses(self):
        plan = self.plan()
        (self.root / 'Other.lean').unlink()
        with self.assertRaises(ValueError):
            TREE.apply_plan(self.root, plan, self.map)

    def test_plan_edit_and_omission_refuse(self):
        plan = self.plan()
        plan['files'].pop()
        with self.assertRaisesRegex(ValueError, 'plan changed'):
            TREE.apply_plan(self.root, plan, self.map)
        plan = self.plan()
        plan['files'][0]['edits'][0]['new'] = 'unsafeReplacement'
        with self.assertRaisesRegex(ValueError, 'plan changed'):
            TREE.apply_plan(self.root, plan, self.map)
        self.assertEqual((self.root / 'Indexed.lean').read_text(), self.source)

    def test_map_and_export_drift_refuse(self):
        plan = self.plan()
        raw = self.map.read_bytes()
        self.map.write_bytes(raw + b'\n')
        with self.assertRaisesRegex(ValueError, 'map changed'):
            TREE.apply_plan(self.root, plan, self.map)
        self.map.write_bytes(raw)
        self.export.write_bytes(self.export.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'digest changed'):
            TREE.apply_plan(self.root, plan, self.map)

    def test_artifact_drift_is_rechecked_at_apply(self):
        artifact = self.directory / 'External.olean'
        artifact.write_bytes(b'before')
        data = json.loads(self.snapshot.read_text())
        data['artifacts'] = TREE.CANDIDATE.bind_artifacts({
            'External': TREE.CANDIDATE.artifact_parts(artifact)})
        self.snapshot.write_text(json.dumps(data))
        plan = self.plan()
        artifact.write_bytes(b'after')
        with self.assertRaisesRegex(ValueError, 'artifacts changed'):
            TREE.apply_plan(self.root, plan, self.map)
        self.assertEqual((self.root / 'Indexed.lean').read_text(), self.source)

    def test_needs_lists_missing_clients_and_configuration(self):
        (self.root / 'Other.lean').write_text('def other := Old.value\n')
        (self.root / 'lakefile.lean').write_text('def config := Old.value\n')
        result = TREE.needs(self.root, ['.'], self.mapping)
        self.assertEqual(result['modules'], ['Indexed', 'Other'])
        self.assertEqual(len(result['files']), 3)
        self.assertIsNone(result['files'][-1]['module'])

    def test_module_rows_remain_explicitly_unsupported(self):
        self.mapping['entries'][0]['kind'] = 'module'
        self.map.write_text(json.dumps(self.mapping))
        plan = self.plan()
        self.assertEqual(plan['status'], 'unresolved')
        self.assertTrue(plan['unsupported'])


if __name__ == '__main__':
    unittest.main()
