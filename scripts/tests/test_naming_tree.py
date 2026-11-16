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

    def test_module_rows_move_file_and_rewrite_imports(self):
        files = {'A.lean': 'def a := 1\n', 'B.lean': '/- import A -/\nimport A\ndef b := a\n',
                 'lakefile.lean': '-- configuration\n'}
        fixture = TreeFixture(self.directory / 'modules', files, imports={'B': ['A']})
        fixture.export('B', decls={}, commands=[], eof=[0, '[anonymous]', []])
        row = dict(old='A', new='Core.A', kind='module', layer='execution', rule='4',
                   source='Synthetic module relocation control')
        plan = fixture.plan([row])
        self.assertEqual(plan['status'], 'planned', plan)
        self.assertEqual(plan['moves'], [['A.lean', 'Core/A.lean']])
        self.assertEqual(TREE.apply_plan(fixture.root, plan, fixture.map), 2)
        self.assertFalse((fixture.root / 'A.lean').exists())
        self.assertEqual((fixture.root / 'Core/A.lean').read_text(), 'def a := 1\n')
        self.assertEqual((fixture.root / 'B.lean').read_text(), '/- import A -/\nimport Core.A\ndef b := a\n')
        # A module name in configuration or a name literal is reported, not guessed.
        files['lakefile.lean'] = 'lean_lib x where roots := #[`A]\n'
        fixture = TreeFixture(self.directory / 'modules2', files, imports={'B': ['A']})
        fixture.export('B', decls={}, commands=[], eof=[0, '[anonymous]', []])
        plan = fixture.plan([row])
        self.assertEqual(plan['status'], 'unresolved')
        self.assertIn('outside an import', plan['files'][-1]['unresolved'][0]['reason'])

    def test_lexed_imports_must_equal_compiler_headers(self):
        files = {'A.lean': 'def a := 1\n', 'B.lean': 'import A\ndef b := a\n', 'lakefile.lean': ''}
        fixture = TreeFixture(self.directory / 'headers', files, imports={'B': []})
        fixture.export('B', decls={}, commands=[], eof=[0, '[anonymous]', []])
        row = dict(old='A', new='Core.A', kind='module', layer='execution', rule='4', source='x')
        with self.assertRaisesRegex(ValueError, 'compiler header'):
            fixture.plan([row])

    def relocation(self, src_text=None, tgt_text='def t := 0\n', client='import Src\nimport Tgt\ndef c := P.moved\n',
                   flags=(False, False, False), eof=0):
        src_text = src_text or 'namespace P\n/-- doc -/\ndef moved := 2\ndef keep := 1\nend P\n'
        files = {'Src.lean': src_text, 'Tgt.lean': tgt_text, 'Client.lean': client, 'lakefile.lean': ''}
        imports = {'Client': [line.split()[1] for line in client.splitlines() if line.startswith('import')]}
        fixture = TreeFixture(self.directory / f'relocation{len(list(self.directory.iterdir()))}', files, imports)
        moved = src_text.index('/-- doc -/')
        moved_end = src_text.index('def keep') - 1
        fixture.export('Src', decls={'P.moved': (moved, moved_end, src_text.index('moved')),
                                     'P.keep': (src_text.index('def keep'), src_text.index('end P') - 1,
                                                src_text.index('keep'))},
                       commands=[(0, 11, 'namespace', '[anonymous]', [], [False] * 3),
                                 (moved, moved_end, 'declaration', 'P', [['simple', 'Q', []]], list(flags))],
                       eof=[0, '[anonymous]', []])
        fixture.export('Tgt', decls={}, commands=[], eof=[eof, '[anonymous]', []])
        fixture.export('Client', decls={}, commands=[], eof=[0, '[anonymous]', []],
                       refs=[('P.moved', 'Src', client.index('P.moved'), client.index('P.moved') + 7)])
        row = dict(old='P.moved', new='P.moved', kind='relocation', layer='execution', rule='4',
                   source='Synthetic relocation control', from_module='Src', to_module='Tgt')
        return fixture, fixture.plan([row])

    def test_relocation_moves_command_with_scope(self):
        fixture, plan = self.relocation()
        self.assertEqual(plan['status'], 'planned', plan)
        TREE.apply_plan(fixture.root, plan, fixture.map)
        self.assertEqual((fixture.root / 'Src.lean').read_text(), 'namespace P\ndef keep := 1\nend P\n')
        self.assertEqual((fixture.root / 'Tgt.lean').read_text(),
                         'def t := 0\n\nsection\nopen Q\nnamespace P\n/-- doc -/\ndef moved := 2\nend P\nend\n')

    def test_relocation_obligations_are_reported(self):
        for kwargs, reason in [(dict(flags=(True, False, False)), 'section variables'),
                               (dict(eof=1), 'ends inside an open'),
                               (dict(client='import Src\ndef c := P.moved\n'), 'does not import Tgt')]:
            with self.subTest(reason=reason):
                fixture, plan = self.relocation(**kwargs)
                self.assertEqual(plan['status'], 'unresolved')
                reasons = [p['reason'] for r in plan['files'] for p in r['unresolved']]
                self.assertTrue(any(reason in text for text in reasons), reasons)
                self.assertEqual((fixture.root / 'Src.lean').read_bytes(),
                                 fixture.files['Src.lean'].encode())

    def test_registered_exclusion_is_accounted_not_omitted(self):
        import hashlib
        text = 'def legacy := A.a\n'
        inventory = dict(schema_version=1, lint_roots=[], policy='', excluded_sources=[dict(
            path='Old.lean', sha256=hashlib.sha256(text.encode()).hexdigest(), status='historical-non-elaborating',
            reason='fixture', decision='fixture')])
        files = {'A.lean': 'def a := 1\n', 'Old.lean': text, 'lakefile.lean': '',
                 'scripts/naming-inventory.json': json.dumps(inventory)}
        (self.directory / 'excl').mkdir()
        fixture = TreeFixture(self.directory / 'excl' / 'x', {k: v for k, v in files.items() if '/' not in k}, {})
        (fixture.root / 'scripts').mkdir()
        (fixture.root / 'scripts/naming-inventory.json').write_text(files['scripts/naming-inventory.json'])
        fixture.candidate = TREE.CANDIDATE.inventory(fixture.root, ['.'])
        fixture.source = copy.deepcopy(fixture.candidate)
        for name, row in fixture.candidate['modules'].items():
            row.update(imports=[], is_module=False)
        fixture.export('A', decls={}, commands=[], eof=[0, '[anonymous]', []])
        row = dict(old='A.a', new='A.b', kind='declaration', layer='execution', rule='4', source='x')
        plan = fixture.plan([row])
        old = next(r for r in plan['files'] if r['path'] == 'Old.lean')
        self.assertEqual((old['excluded'], old['excluded_tokens'], old['unresolved']),
                         ('historical-non-elaborating', 1, []))
        (fixture.root / 'Old.lean').write_text(text + '-- edited\n')
        fixture.candidate = TREE.CANDIDATE.inventory(fixture.root, ['.'])
        fixture.source = copy.deepcopy(fixture.candidate)
        for name, r in fixture.candidate['modules'].items():
            r.update(imports=[], is_module=False)
        plan = fixture.plan([row])
        self.assertEqual(plan['status'], 'unresolved')



    def consumer(self, client, refs, dep_decls, entries, consumer=True, dependency=True):
        """A dependency package fixture (Dep.lean with its own whole-tree capture)
        and a consumer tree importing it, as Blanc imports Jaune."""
        base = self.directory / f'consumer{len(list(self.directory.iterdir()))}'
        dep_text = 'namespace Dep\ndef Val := 1\nend Dep\nnamespace Q\ndef Thing := 2\nend Q\n'
        dep = TreeFixture(base / 'dep', {'Dep.lean': dep_text, 'lakefile.lean': ''}, {})
        dep.export('Dep', decls={name: (dep_text.index(name.split('.')[-1]), dep_text.index(name.split('.')[-1]) + 1,
                                        dep_text.index(name.split('.')[-1])) for name in dep_decls},
                   commands=[], eof=[0, '[anonymous]', []])
        dep.plan([])  # writes the dependency's snapshot
        files = {'B.lean': client, 'lakefile.lean': '', '.gitignore': '/.lake\n'}
        fixture = TreeFixture(base / 'consumer', files, imports={'B': ['Dep']})
        fixture.export('B', decls={}, commands=[(0, len(client.encode()), 'declaration', '[anonymous]',
                                                [['simple', 'Dep', []], ['simple', 'Q', []]], [False] * 3)],
                       eof=[0, '[anonymous]', []], refs=refs)
        package = base / 'consumer/repo/.lake/packages/dep'
        (package / '.lake/build/lib/lean').mkdir(parents=True)
        (package / 'Dep.lean').write_text(dep_text)
        olean = package / '.lake/build/lib/lean/Dep.olean'
        olean.write_bytes(b'dep')
        original = TREE.build_plan
        def build(root, path, map_path, *rest):
            data = json.loads(Path(path).read_text())
            data['artifacts'] = TREE.CANDIDATE.bind_artifacts({'Dep': TREE.CANDIDATE.artifact_parts(olean)})
            Path(path).write_text(json.dumps(data))
            return original(root, path, map_path, consumer,
                            [dep.capture / 'snapshot.json'] if dependency else [])
        TREE.build_plan = build
        try:
            plan = fixture.plan(entries)
        finally:
            TREE.build_plan = original
        return fixture, plan

    def test_consumer_rewrites_imports_of_a_dependency_module_row(self):
        client = 'import Dep\ndef b := 1\n'
        refs = []
        row = dict(old='Dep', new='Core.Dep', kind='module', layer='execution', rule='4', source='x')
        fixture, plan = self.consumer(client, refs, ['Dep.Val', 'Q.Thing'], [row])
        self.assertEqual((plan['status'], plan['moves'], plan['consumer']), ('planned', [], True), plan)
        self.assertEqual(plan['dependencies'][0]['bound_modules'], 1)
        self.assertEqual(TREE.apply_plan(fixture.root, plan, fixture.map), 1)
        self.assertEqual((fixture.root / 'B.lean').read_text(), 'import Core.Dep\ndef b := 1\n')
        # Without consumer mode a dependency module row is an unknown module.
        with self.assertRaisesRegex(ValueError, 'unknown module'):
            self.consumer(client, refs, ['Dep.Val', 'Q.Thing'], [row], consumer=False, dependency=False)
        with self.assertRaisesRegex(ValueError, 'needs --dependency-snapshot'):
            self.consumer(client, refs, ['Dep.Val', 'Q.Thing'], [row], dependency=False)

    def test_consumer_capture_sees_dependency_constants_it_never_references(self):
        # `Dep.Val` -> `Dep.Thing`; the consumer never mentions `Q.Thing`, but with
        # `open Dep Q` a bare `Thing` would be ambiguous. Only the dependency's own
        # capture knows `Q.Thing` exists.
        client = 'import Dep\ndef b := Val\n'
        refs = [('Dep.Val', 'Dep', client.index('Val'), client.index('Val') + 3)]
        row = dict(old='Dep.Val', new='Dep.Thing', kind='declaration', layer='execution', rule='4', source='x')
        fixture, plan = self.consumer(client, refs, ['Dep.Val', 'Q.Thing'], [row])
        self.assertEqual(plan['status'], 'planned', plan)
        edits = [e['new'] for r in plan['files'] for e in r['edits']]
        self.assertEqual(edits, ['Dep.Thing'], plan)
        self.assertEqual(plan['name_capture']['capture_requalified'], 1)
        # A dependency capture whose source differs from the imported package refuses.
        fixture2, _ = self.consumer(client, refs, ['Dep.Val', 'Q.Thing'], [row])
        (fixture2.root / '.lake/packages/dep/Dep.lean').write_text('-- other revision\n')
        snapshot = fixture2.capture / 'snapshot.json'
        dep = fixture2.directory.parent / 'dep/capture/snapshot.json'
        with self.assertRaisesRegex(ValueError, 'does not match the imported package source'):
            TREE.build_plan(fixture2.root, snapshot, fixture2.map, True, [dep])


class TreeFixture:
    """A git checkout plus a schema-3 capture whose exports carry syntax rows."""

    def __init__(self, directory, files, imports):
        self.files = files
        self.directory = directory
        self.root = directory / 'repo'
        self.root.mkdir(parents=True)
        for name, text in files.items():
            (self.root / name).write_text(text)
        subprocess.run(['git', 'init', '-q', str(self.root)], check=True)
        subprocess.run(['git', '-C', str(self.root), 'add', '.'], check=True)
        subprocess.run(['git', '-C', str(self.root), '-c', 'user.name=Fixture',
                        '-c', 'user.email=fixture@example.invalid', '-c', 'commit.gpgsign=false',
                        'commit', '-qm', 'fixture'], check=True)
        self.capture = directory / 'capture'
        self.capture.mkdir()
        self.candidate = TREE.CANDIDATE.inventory(self.root, ['.'])
        self.source = copy.deepcopy(self.candidate)
        self.headers = dict(schema_version=1, lean_version='fixture', modules={})
        for name, row in self.candidate['modules'].items():
            row.update(imports=imports.get(name, []), is_module=False)
            self.headers['modules'][name] = dict(path=row['path'], is_module=False,
                                                 direct_imports=[[i, False, False] for i in row['imports']])
        self.exports = {}
        self.map = directory / 'map.json'

    def lsp(self, text, i):
        line = text.count('\n', 0, i)
        return [line, len(text[text.rfind('\n', 0, i) + 1:i].encode('utf-16-le')) // 2]

    def export(self, module, decls, commands, eof, refs=()):
        text = self.files[module + '.lean']
        def b(i):
            return len(text[:i].encode())
        references = {}
        for name, (start, end, selection) in decls.items():
            references[json.dumps({'c': {'m': module, 'n': name}})] = dict(
                definition=self.lsp(text, selection) + self.lsp(text, selection + len(name.split('.')[-1])),
                usages=[])
        for name, owner, start, end in refs:
            references.setdefault(json.dumps({'c': {'m': owner, 'n': name}}),
                                  dict(definition=None, usages=[]))['usages'].append(
                self.lsp(text, start) + self.lsp(text, end))
        index = dict(version=5, module=module, directImports=self.headers['modules'][module]['direct_imports'],
                     references=references,
                     decls={name: self.lsp(text, start) + self.lsp(text, end) +
                            self.lsp(text, sel) + self.lsp(text, sel + len(name.split('.')[-1]))
                            for name, (start, end, sel) in decls.items()},
                     naming_syntax=dict(version=2, literal_ranges=[], named_arguments=[], namespaces=[],
                                        commands=[[b(x), b(y), *rest] for x, y, *rest in commands],
                                        imports=[], unresolved_syntax=[], eof_scope=eof))
        path = self.capture / f'{module}.json'
        constants = {name: dict(kernel=['theorem'], attributes={}, equation_origin=None) for name in decls}
        path.write_text(json.dumps(dict(schema_version=6, lean_version='fixture', source=text, index=index,
                                        constants=constants, guards=[], attribute_syntax=[], checked_commands=[],
                                        imports={})))
        self.exports[module] = dict(path=path.name, sha256=TREE.CANDIDATE.file_sha(path))

    def plan(self, entries):
        self.map.write_text(json.dumps(dict(schema_version=1, retired_tokens=[], allowed_abbreviations=[],
                                            entries=entries)))
        (self.capture / 'headers.json').write_text(json.dumps(self.headers))
        (self.capture / 'source-before.json').write_text(json.dumps(self.source))
        modules = self.candidate['modules']
        roots = sorted(self.exports) or []
        selected = TREE.CANDIDATE.closure(modules, roots)
        for module in selected:
            if module not in self.exports:
                self.export(module, decls={}, commands=[], eof=[0, '[anonymous]', []])
        producers = TREE.CANDIDATE.build_modules(modules, roots, [])
        artifacts = self.directory / 'artifacts'
        artifacts.mkdir(exist_ok=True)
        paths = {}
        for module in producers:
            olean = artifacts / f'{module}.olean'
            olean.write_bytes(module.encode())
            paths[module] = TREE.CANDIDATE.artifact_parts(olean)
        snapshot = dict(schema_version=3, status='OK', build=dict(exit=0), candidate=self.candidate,
                        roots=roots, selected=selected, source_only=[], producers=producers,
                        exports=self.exports,
                        headers_sha256=TREE.CANDIDATE.file_sha(self.capture / 'headers.json'),
                        tool_sources={}, artifacts={}, local_built=TREE.CANDIDATE.bind_artifacts(paths))
        path = self.capture / 'snapshot.json'
        path.write_text(json.dumps(snapshot))
        return TREE.build_plan(self.root, path, self.map)

if __name__ == '__main__':
    unittest.main()
