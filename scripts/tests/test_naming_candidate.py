import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).parents[2]
SPEC = importlib.util.spec_from_file_location('naming_candidate', ROOT / 'scripts/naming-candidate.py')
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)


def module(path, digest, imports=()):
    return dict(path=path, sha256=digest, imports=list(imports), is_module=False)


def snapshot(graph, roots):
    selected = CHECK.closure(graph, roots)
    return dict(candidate=dict(head='fixture', source_dirs=['.'], modules=graph,
                               files={r['path']: r['sha256'] for r in graph.values()}),
                roots=roots, selected=selected, tool_sources={}, artifacts={},
                fidelity={root: dict(constants={}, roots=set(), guards=[], attributes=[],
                                     modules={}, receipts=[], version='fixture')
                          for root in CHECK.environments(graph, selected)})


EMPTY = dict(schema_version=1, entries=[], retired_tokens=[], allowed_abbreviations=[])


def union_bundle(constants, owner, guards=(), imports=()):
    """One module's comparator bundle, as `read_exports` returns it."""
    return dict(constants=dict(constants), roots=set(constants), guards=list(guards), attributes=[],
                modules={owner: [[i, False, False, False] for i in imports]}, receipts=[], checks=[],
                version='fixture', coalesced_equations=[], owners={n: owner for n in constants},
                holders={n: {owner} for n in constants},
                item_modules=dict(guards=[owner] * len(guards), attributes=[], checks=[]))


class CandidateTests(unittest.TestCase):
    def setUp(self):
        self.graph = {'Dep': module('Dep.lean', 'a'),
                      'Client': module('Client.lean', 'b', ['Dep']),
                      'Untouched': module('Untouched.lean', 'c')}
        self.before = snapshot(copy.deepcopy(self.graph), ['Client'])
        self.after = copy.deepcopy(self.before)

    def check(self):
        return CHECK.compare(self.before, self.after, EMPTY)

    def test_compiler_headers_cover_every_inventoried_module(self):
        source = dict(modules={'Dep': dict(path='Dep.lean', sha256='a')})
        headers = dict(schema_version=1, modules={'Dep': dict(path='Dep.lean', is_module=False, direct_imports=[['Init', False, False, False]])})
        self.assertEqual(CHECK.bind_headers(source, headers)['modules']['Dep']['imports'], ['Init'])
        headers['modules'].clear()
        with self.assertRaisesRegex(ValueError, 'does not cover all'):
            CHECK.bind_headers(source, headers)

    def test_compiler_header_cannot_bind_another_source_path(self):
        source = dict(modules={'Dep': dict(path='Dep.lean', sha256='a')})
        headers = dict(schema_version=1, modules={'Dep': dict(path='Other.lean', is_module=False, direct_imports=[])})
        with self.assertRaisesRegex(ValueError, 'source path differs'):
            CHECK.bind_headers(source, headers)

    def test_closed_identity_passes(self):
        self.assertEqual(self.check()['scope'], 'candidate-affected-local-closure')

    def test_source_only_requires_explicit_unimported_roots(self):
        self.assertEqual(CHECK.build_modules(self.graph, ['Client'], ['Client']), ['Dep'])
        with self.assertRaisesRegex(ValueError, 'explicit capture roots'):
            CHECK.build_modules(self.graph, ['Client'], ['Untouched'])
        with self.assertRaisesRegex(ValueError, 'imported by a local source'):
            CHECK.build_modules(self.graph, ['Dep'], ['Dep'])
        self.assertEqual(CHECK.build_modules(self.graph, ['Untouched'], ['Untouched']), [])

    def test_independent_environments_keep_shared_dependencies(self):
        graph = {**self.graph, 'OtherClient': module('OtherClient.lean', 'd', ['Dep'])}
        self.assertEqual(CHECK.environments(graph, CHECK.closure(graph, ['Client', 'OtherClient'])),
                         {'Client': ['Dep', 'Client'], 'OtherClient': ['Dep', 'OtherClient']})

    def test_source_only_classification_cannot_change_in_comparison(self):
        self.after['source_only'] = ['Client']
        with self.assertRaisesRegex(ValueError, 'classification changed'):
            self.check()

    def test_environment_omission_cannot_hide_checks(self):
        self.after['fidelity'] = {}
        with self.assertRaisesRegex(ValueError, 'environment roots changed'):
            self.check()

    def test_duplicate_main_is_separate_but_imported_collisions_refuse(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            graph = {'One': module('One.lean', 'one'), 'Two': module('Two.lean', 'two')}
            paths = {}
            for name, value in [('One', 1), ('Two', 2)]:
                path = directory / (name + '.json')
                data = dict(schema_version=5, lean_version='fixture', source='def main := 0\n',
                            index=dict(version=5, module=name, directImports=[], decls={'main': [0, 0, 0, 13, 0, 4, 0, 8]}, references={}),
                            constants={'main': {'value': value}}, guards=[['lit', value]],
                            attribute_syntax=[], checked_commands=[])
                path.write_text(json.dumps(data))
                paths[name] = path
            envs = CHECK.read_environments(paths, graph, ['One', 'Two'])
            self.assertEqual(set(envs), {'One', 'Two'})
            self.assertEqual(envs['One']['constants']['main']['value'], 1)
            self.assertEqual(envs['Two']['constants']['main']['value'], 2)
            before = snapshot(graph, ['One', 'Two'])
            before['fidelity'] = envs
            after = copy.deepcopy(before)
            self.assertEqual(CHECK.compare(before, after, EMPTY)['status'], 'OK')
            after['fidelity']['Two']['constants']['main']['value'] = 3
            with self.assertRaises(CHECK.FIDELITY.Mismatch):
                CHECK.compare(before, after, EMPTY)
            # A global multiset would miss swapping checks between executable
            # environments; each environment must retain its own commands.
            after = copy.deepcopy(before)
            after['fidelity']['One']['guards'], after['fidelity']['Two']['guards'] = (
                after['fidelity']['Two']['guards'], after['fidelity']['One']['guards'])
            with self.assertRaises(CHECK.FIDELITY.Mismatch):
                CHECK.compare(before, after, EMPTY)
            graph['Two']['imports'] = ['One']
            with self.assertRaisesRegex(ValueError, 'duplicate constants in one import environment'):
                CHECK.read_environments(paths, graph, ['One', 'Two'])

    def test_relocation_is_checked_in_each_environment_that_imports_its_module(self):
        graph = {m: module(m + '.lean', m) for m in ('A', 'B', 'Tool')}
        graph['Client'] = module('Client.lean', 'client', ['A', 'B'])
        before = snapshot(graph, ['Client', 'Tool'])
        after = copy.deepcopy(before)
        val = dict(kernel=['definition', 1])
        for snap, owner in [(before, 'A'), (after, 'B')]:
            env = union_bundle({'N.f': val}, owner)
            env['modules'].update({'Client': [], 'A': [], 'B': []})
            snap['fidelity']['Client'] = env
            snap['fidelity']['Tool'] = union_bundle({'main': val}, 'Tool')
        row = dict(old='N.f', new='N.f', kind='relocation', layer='execution', rule='4',
                   source='fixture', from_module='A', to_module='B')
        mapping = dict(EMPTY, entries=[row])
        self.assertEqual(CHECK.compare(before, after, mapping)['status'], 'OK')
        after['fidelity']['Tool']['constants']['main'] = dict(kernel=['definition', 2])
        with self.assertRaises(CHECK.FIDELITY.Mismatch):
            CHECK.compare(before, after, mapping)
        after['fidelity']['Tool']['constants']['main'] = val
        with self.assertRaisesRegex(CHECK.FIDELITY.Mismatch, 'outside every compared'):
            CHECK.compare(before, after, dict(EMPTY, entries=[row, dict(row, old='Absent.f',
                          new='Absent.f', from_module='Absent', to_module='AlsoAbsent')]))

    def test_batched_compare_covers_every_environment_and_row(self):
        graph = {m: module(m + '.lean', m) for m in ('A', 'B', 'Tool')}
        graph['Client'] = module('Client.lean', 'client', ['A', 'B'])
        val = dict(kernel=['definition', 1])
        full = {}
        for side, owner in [('before', 'A'), ('after', 'B')]:
            snap = snapshot(graph, ['Client', 'Tool'])
            env = union_bundle({'N.f': val}, owner)
            env['modules'].update({'Client': [], 'A': [], 'B': []})
            snap['fidelity'] = {'Client': env, 'Tool': union_bundle({'main': val}, 'Tool')}
            snap['all_environments'] = ['Client', 'Tool']
            full[side] = snap
        row = dict(old='N.f', new='N.f', kind='relocation', layer='execution', rule='4',
                   source='fixture', from_module='A', to_module='B')
        mapping = dict(EMPTY, entries=[row])
        def batch(*roots):
            sides = [dict(full[s], fidelity={r: full[s]['fidelity'][r] for r in roots}) for s in ('before', 'after')]
            return CHECK.compare(*sides, mapping, batch=True)
        tool, client = batch('Tool'), batch('Client')
        self.assertEqual((tool['batch']['scoped_rows_checked'], client['batch']['scoped_rows_checked']), ([], [0]))
        self.assertEqual(CHECK.combine([tool, client])['environments'], ['Client', 'Tool'])
        # The batches must partition the environments and check every relocation row.
        with self.assertRaisesRegex(CHECK.FIDELITY.Mismatch, 'missing'):
            CHECK.combine([client])
        with self.assertRaisesRegex(CHECK.FIDELITY.Mismatch, 'repeated'):
            CHECK.combine([tool, client, tool])
        with self.assertRaisesRegex(CHECK.FIDELITY.Mismatch, 'rows outside'):
            CHECK.combine([tool, dict(client, batch=dict(client['batch'], scoped_rows_checked=[]))])
        # A batch still fails on a changed body in its own environment.
        full['after']['fidelity']['Tool']['constants']['main'] = dict(kernel=['definition', 2])
        with self.assertRaises(CHECK.FIDELITY.Mismatch):
            batch('Tool')

    def test_relocation_to_a_new_root_compares_the_union(self):
        bundle = union_bundle
        value = dict(kernel=['definition', 1])
        before_graph = {'Spec': module('Spec.lean', 'a'), 'Main': module('Main.lean', 'b', ['Spec'])}
        after_graph = dict(before_graph, Spec=module('Spec.lean', 'c'), Tests=module('Tests.lean', 'd', ['Spec']))
        self.before = snapshot(before_graph, ['Main'])
        self.after = snapshot(after_graph, ['Main', 'Tests'])
        self.before['module_bundles'] = {'Spec': bundle({'J.f': value, 'J.check': value}, 'Spec', [['g', 1]]),
                                         'Main': bundle({'main': value}, 'Main')}
        self.after['module_bundles'] = {'Spec': bundle({'J.f': value}, 'Spec'),
                                        'Main': bundle({'main': value}, 'Main'),
                                        'Tests': bundle({'J.check': value}, 'Tests', [['g', 1]])}
        rows = [dict(old='J.check', new='J.check', kind='relocation', layer='execution', rule='4',
                     source='fixture', from_module='Spec', to_module='Tests')]
        mapping = dict(EMPTY, entries=rows)
        with self.assertRaisesRegex(ValueError, 'without module/relocation rows'):
            CHECK.compare(self.before, self.after, EMPTY)
        self.assertEqual(CHECK.compare(self.before, self.after, mapping)['environments']['<union>']['status'], 'OK')
        # A moved guard is still compared as an expression; changing it fails.
        self.after['module_bundles']['Tests']['guards'] = [['g', 2]]
        with self.assertRaises(CHECK.FIDELITY.Mismatch):
            CHECK.compare(self.before, self.after, mapping)
        # A declaration that moved without its row fails the module identity check.
        self.after['module_bundles']['Tests']['guards'] = [['g', 1]]
        with self.assertRaisesRegex(CHECK.FIDELITY.Mismatch, 'module Spec became Tests'):
            CHECK.compare(self.before, self.after, dict(EMPTY, entries=[dict(rows[0], old='J.f', new='J.f')]))

    def union_case(self):
        """Two independent executables over a shared module; a third root appears."""
        value = dict(kernel=['definition', 1])
        graph = {'Spec': module('Spec.lean', 'a'), 'Main': module('Main.lean', 'b', ['Spec']),
                 'Tool': module('Tool.lean', 'c', ['Spec'])}
        after_graph = dict(graph, Spec=module('Spec.lean', 'd'), Tests=module('Tests.lean', 'e', ['Spec']))
        self.before = snapshot(graph, ['Main', 'Tool'])
        self.after = snapshot(after_graph, ['Main', 'Tool', 'Tests'])
        self.before['module_bundles'] = {
            'Spec': union_bundle({'J.f': value, 'J.check': value}, 'Spec'),
            'Main': union_bundle({'main': value}, 'Main', [['safety', 1]], imports=['Spec']),
            'Tool': union_bundle({'main': dict(kernel=['definition', 2])}, 'Tool', imports=['Spec'])}
        self.after['module_bundles'] = copy.deepcopy(self.before['module_bundles'])
        self.after['module_bundles']['Spec'] = union_bundle({'J.f': value}, 'Spec')
        self.after['module_bundles']['Tests'] = union_bundle({'J.check': value}, 'Tests', imports=['Spec'])
        rows = [dict(old='J.check', new='J.check', kind='relocation', layer='execution', rule='4',
                     source='fixture', from_module='Spec', to_module='Tests')]
        return dict(EMPTY, entries=rows)

    def test_union_keeps_checks_in_their_modules(self):
        mapping = self.union_case()
        self.assertEqual(CHECK.compare(self.before, self.after, mapping)['environments']['<union>']['status'], 'OK')
        # A guard moved from one executable to an unrelated one, with no
        # relocation row linking the modules, fails.
        bundles = self.after['module_bundles']
        bundles['Main'] = union_bundle({'main': dict(kernel=['definition', 1])}, 'Main', imports=['Spec'])
        bundles['Tool'] = union_bundle({'main': dict(kernel=['definition', 2])}, 'Tool', [['safety', 1]],
                                       imports=['Spec'])
        with self.assertRaisesRegex(CHECK.FIDELITY.Mismatch, r"guards: .*modules \['Main', 'Tool'\]"):
            CHECK.compare(self.before, self.after, mapping)
        # Along a relocation row the same move is accepted.
        bundles['Tool'] = union_bundle({'main': dict(kernel=['definition', 2])}, 'Tool', imports=['Spec'])
        bundles['Tests'] = union_bundle({'J.check': dict(kernel=['definition', 1])}, 'Tests', [['safety', 1]],
                                        imports=['Spec'])
        bundles['Spec'] = union_bundle({'J.f': dict(kernel=['definition', 1])}, 'Spec', [['safety', 1]])
        bundles['Tests']['guards'] = []
        bundles['Tests']['item_modules']['guards'] = []
        self.before['module_bundles']['Main'] = union_bundle(
            {'main': dict(kernel=['definition', 1])}, 'Main', imports=['Spec'])
        self.before['module_bundles']['Spec'] = union_bundle(
            {'J.f': dict(kernel=['definition', 1]), 'J.check': dict(kernel=['definition', 1])}, 'Spec', [['safety', 1]])
        bundles['Spec'] = union_bundle({'J.f': dict(kernel=['definition', 1])}, 'Spec')
        bundles['Tests'] = union_bundle({'J.check': dict(kernel=['definition', 1])}, 'Tests', [['safety', 1]],
                                        imports=['Spec'])
        self.assertEqual(CHECK.compare(self.before, self.after, mapping)['environments']['<union>']['status'], 'OK')

    def test_union_generated_constants_keep_their_module(self):
        mapping = self.union_case()
        instance = dict(kernel=['definition', 7])
        self.before['module_bundles']['Main']['constants']['instTagNat'] = instance
        self.before['module_bundles']['Main']['holders']['instTagNat'] = {'Main'}
        self.after['module_bundles']['Main'] = copy.deepcopy(self.before['module_bundles']['Main'])
        self.assertEqual(CHECK.compare(self.before, self.after, mapping)['environments']['<union>']['status'], 'OK')
        del self.after['module_bundles']['Main']['constants']['instTagNat']
        self.after['module_bundles']['Tool']['constants']['instTagNat'] = instance
        with self.assertRaisesRegex(CHECK.FIDELITY.Mismatch, r"generated constant instTagNat.*\['Main'\] became \['Tool'\]"):
            CHECK.compare(self.before, self.after, mapping)

    def test_union_compares_direct_imports_of_unmoved_modules(self):
        mapping = self.union_case()
        self.after['module_bundles']['Tool']['modules']['Tool'] = [['Spec', False, False, False],
                                                                   ['Extra', False, False, False]]
        with self.assertRaisesRegex(CHECK.FIDELITY.Mismatch, 'module Tool: direct imports changed'):
            CHECK.compare(self.before, self.after, mapping)
        # A relocation module's imports may change with what moved into it.
        self.after['module_bundles']['Tool']['modules']['Tool'] = [['Spec', False, False, False]]
        self.after['module_bundles']['Tests']['modules']['Tests'].append(['Extra', False, False, False])
        self.assertEqual(CHECK.compare(self.before, self.after, mapping)['environments']['<union>']['status'], 'OK')

    def test_union_coalesces_identical_realized_copies(self):
        realized = dict(kernel=['theorem', 1], equation_origin=None)
        bundles = {'A': union_bundle({'J.f': dict(kernel=['definition', 1])}, 'A'),
                   'B': union_bundle({'J.g': dict(kernel=['definition', 2])}, 'B')}
        for name in ('A', 'B'):
            bundles[name]['constants']['J.f.eq_1'] = realized
            bundles[name]['holders']['J.f.eq_1'] = {name}
        merged = CHECK.union_environment(bundles)
        self.assertEqual(merged['coalesced_equations'], ['J.f.eq_1'])
        self.assertEqual(merged['holders']['J.f.eq_1'], {'A', 'B'})
        self.assertNotIn('J.f.eq_1@A', merged['constants'])
        bundles['B']['constants']['J.f.eq_1'] = dict(realized, kernel=['theorem', 2])
        merged = CHECK.union_environment(bundles)
        self.assertIn('J.f.eq_1@A', merged['constants'])
        self.assertIn('J.f.eq_1@B', merged['constants'])

    def test_module_row_renaming_a_root_compares_environments_pairwise(self):
        graph = {'Dep': module('Dep.lean', 'a'), 'OldMain': module('OldMain.lean', 'b', ['Dep'])}
        after_graph = {'Dep': module('Dep.lean', 'a'), 'NewMain': module('NewMain.lean', 'b', ['Dep'])}
        self.before = snapshot(graph, ['OldMain'])
        self.after = snapshot(after_graph, ['NewMain'])
        mapping = dict(EMPTY, entries=[dict(old='OldMain', new='NewMain', kind='module', layer='execution',
                                            rule='4', source='fixture')])
        self.before['candidate']['source_dirs'] = self.after['candidate']['source_dirs']
        result = CHECK.compare(self.before, self.after, mapping)
        self.assertEqual(set(result['environments']), {'OldMain'})

    def test_dependency_cannot_be_missing_from_closure(self):
        self.assertEqual(CHECK.closure(self.graph, ['Client']), ['Dep', 'Client'])
        with self.assertRaisesRegex(ValueError, 'unknown local root'):
            CHECK.closure(self.graph, ['Missing'])
        self.graph['Dep']['imports'] = ['Client']
        with self.assertRaisesRegex(ValueError, 'cycle'):
            CHECK.closure(self.graph, ['Client'])

    def test_changed_file_outside_exports_is_refused(self):
        self.after['candidate']['files']['Untouched.lean'] = 'different'
        with self.assertRaisesRegex(ValueError, 'changed Lean sources outside'):
            self.check()

    def test_unchanged_importer_of_changed_dependency_must_be_exported(self):
        self.before = snapshot(copy.deepcopy(self.graph), ['Dep'])
        self.after = copy.deepcopy(self.before)
        self.after['candidate']['modules']['Dep']['sha256'] = 'changed'
        self.after['candidate']['files']['Dep.lean'] = 'changed'
        with self.assertRaisesRegex(ValueError, 'affected importers.*Client'):
            self.check()

    def test_removed_import_edge_still_requires_old_importer(self):
        self.after['candidate']['modules']['Client']['imports'] = []
        self.after['selected'] = ['Dep']
        with self.assertRaisesRegex(ValueError, 'affected importers.*Client'):
            self.check()

    def test_transitive_reverse_closure(self):
        graph = {**self.graph, 'Top': module('Top.lean', 'd', ['Client'])}
        after = copy.deepcopy(graph)
        after['Dep']['sha256'] = 'changed'
        self.assertEqual(CHECK.affected_modules(graph, after), {'Dep', 'Client', 'Top'})

    def test_configuration_or_tool_change_is_refused(self):
        for key in CHECK.CONFIG:
            self.after['candidate']['files'][key] = 'changed'
            with self.assertRaisesRegex(ValueError, 'configuration changed'):
                self.check()
            del self.after['candidate']['files'][key]
        self.after['tool_sources'] = {'exporter': 'changed'}
        with self.assertRaisesRegex(ValueError, 'implementation changed'):
            self.check()

    def test_external_boundary_uses_hashes_not_host_paths(self):
        parts = {k: None for k in CHECK.PARTS}
        parts['olean'] = dict(path='/before/Init.olean', sha256='same')
        self.before['artifacts'] = {'Init': parts}
        self.after['artifacts'] = copy.deepcopy(self.before['artifacts'])
        self.after['artifacts']['Init']['olean']['path'] = '/after/Init.olean'
        self.assertEqual(self.check()['status'], 'OK')
        self.after['artifacts']['Init']['olean']['sha256'] = 'different'
        with self.assertRaisesRegex(ValueError, 'external import artifact'):
            self.check()

    def test_optional_artifact_appearance_and_disappearance_fail(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'Dep.olean'
            path.write_bytes(b'compiled')
            parts = CHECK.artifact_parts(path)
            CHECK.bind_artifacts({'Dep': parts})
            extra = path.with_suffix('.ir.sig')
            extra.write_bytes(b'extra')
            with self.assertRaisesRegex(ValueError, 'appeared, disappeared'):
                CHECK.bind_artifacts({'Dep': parts})
            parts = CHECK.artifact_parts(path)
            extra.unlink()
            with self.assertRaisesRegex(ValueError, 'appeared, disappeared'):
                CHECK.bind_artifacts({'Dep': parts})

    def test_artifact_parts_follow_lean_logical_path_before_symlinks(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / 'cache-one').write_bytes(b'olean')
            (root / 'cache-two').write_bytes(b'private')
            (root / 'Dep.olean').symlink_to(root / 'cache-one')
            (root / 'Dep.olean.private').symlink_to(root / 'cache-two')
            bound = CHECK.bind_artifacts({'Dep': CHECK.artifact_parts(root / 'Dep.olean')})
            self.assertEqual(bound['Dep']['olean.private']['sha256'], CHECK.sha(b'private'))

    def test_artifact_byte_change_changes_binding(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'Dep.olean'
            path.write_bytes(b'first')
            parts = CHECK.artifact_parts(path)
            first = CHECK.bind_artifacts({'Dep': parts})
            path.write_bytes(b'other')
            self.assertNotEqual(first, CHECK.bind_artifacts({'Dep': parts}))

    def test_argv_is_never_shell_text(self):
        self.assertEqual(CHECK.argv('["command", "literal;$(text)"]'), ['command', 'literal;$(text)'])
        for bad in ['"shell text"', '[]', '[""]', '[1]']:
            with self.assertRaises(ValueError):
                CHECK.argv(bad)

    def test_snapshot_rejects_missing_dependency_export_before_reading_files(self):
        data = dict(schema_version=2, status='OK', build=dict(exit=0),
                    candidate=self.before['candidate'], roots=['Client'],
                    selected=['Dep', 'Client'], exports={'Client': {}})
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'snapshot.json'
            source = copy.deepcopy(data['candidate'])
            headers = dict(schema_version=1, modules={})
            for module, row in source['modules'].items():
                imports = row.pop('imports')
                is_module = row.pop('is_module')
                headers['modules'][module] = dict(path=row['path'], is_module=is_module, direct_imports=[[name, False, False, False] for name in imports])
            (path.parent / 'source-before.json').write_text(json.dumps(source))
            (path.parent / 'headers.json').write_text(json.dumps(headers))
            data['headers_sha256'] = CHECK.file_sha(path.parent / 'headers.json')
            path.write_text(json.dumps(data))
            with self.assertRaisesRegex(ValueError, 'incomplete candidate export closure'):
                CHECK.read_snapshot(path)

    def test_plan_only_capture_is_refused_for_fidelity(self):
        data = dict(schema_version=3, status='OK', build=dict(exit=0), purpose='plan',
                    candidate=self.before['candidate'], roots=['Client'], selected=['Dep', 'Client'],
                    exports={}, source_only=[], producers=['Dep', 'Client'], local_built={})
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / 'snapshot.json'
            source = copy.deepcopy(data['candidate'])
            headers = dict(schema_version=1, modules={})
            for module, row in source['modules'].items():
                imports = row.pop('imports')
                headers['modules'][module] = dict(path=row['path'], is_module=row.pop('is_module'),
                                                  direct_imports=[[name, False, False, False] for name in imports])
            (path.parent / 'source-before.json').write_text(json.dumps(source))
            (path.parent / 'headers.json').write_text(json.dumps(headers))
            data['headers_sha256'] = CHECK.file_sha(path.parent / 'headers.json')
            data['selected'] = CHECK.closure(data['candidate']['modules'], ['Client'])
            data['exports'] = {}
            path.write_text(json.dumps(data))
            # Fidelity refuses it before reading anything else.
            with self.assertRaisesRegex(ValueError, 'plan-only capture'):
                CHECK.read_snapshot(path)


    def _tool_root_capture(self, tmp, toolchain, prefix=True):
        import argparse
        import subprocess
        tmp = Path(tmp)
        candidate, tool = tmp / 'candidate', tmp / 'tool'
        for root, chain in ((candidate, 'leanprover/lean4:v4.35.0\n'), (tool, toolchain)):
            root.mkdir()
            (root / 'lean-toolchain').write_text(chain)
            (root / 'Client.lean').write_text('def x := 1\n')
            subprocess.run(['git', 'init', '-q', str(root)], check=True)
            subprocess.run(['git', '-C', str(root), 'add', '-A'], check=True)
            subprocess.run(['git', '-C', str(root), '-c', 'user.name=t', '-c', 'user.email=t@t',
                            'commit', '-qm', 'fixture'], check=True)
        # The fake owned build records where it ran and fails, ending capture.
        build = json.dumps(['sh', '-c', 'pwd > built-here; exit 7', 'fake-build'])
        args = argparse.Namespace(root=candidate, output=tmp / 'out', source_dir=['.'], module=['Client'],
                                  source_only=[], build_prefix=json.dumps(['false']),
                                  tool_root=tool, tool_build_prefix=build if prefix else None,
                                  admit_command='["true"]', release_command='["true"]', reuse=None, jobs=1)
        return candidate, tool, args

    def test_external_tool_root_builds_the_exporter_there(self):
        with tempfile.TemporaryDirectory() as tmp:
            candidate, tool, args = self._tool_root_capture(tmp, 'leanprover/lean4:v4.35.0\n')
            with self.assertRaisesRegex(ValueError, 'tool-build exited 7'):
                CHECK.capture(args)
            self.assertEqual((tool / 'built-here').read_text().strip(), str(tool.resolve()))
            self.assertFalse((candidate / 'built-here').exists())
            receipt = json.loads((args.output / 'tool-build.command.json').read_text())
            self.assertEqual(receipt['cwd'], str(tool.resolve()))
            self.assertEqual(receipt['argv'][-1], 'jaune-naming-fidelity')

    def test_external_tool_root_needs_same_toolchain_and_its_own_build(self):
        with tempfile.TemporaryDirectory() as tmp:
            _, tool, args = self._tool_root_capture(tmp, 'leanprover/lean4:v4.34.0\n')
            with self.assertRaisesRegex(ValueError, 'different Lean toolchains'):
                CHECK.capture(args)
            self.assertFalse((tool / 'built-here').exists())
        with tempfile.TemporaryDirectory() as tmp:
            _, tool, args = self._tool_root_capture(tmp, 'leanprover/lean4:v4.35.0\n', prefix=False)
            with self.assertRaisesRegex(ValueError, 'needs --tool-build-prefix'):
                CHECK.capture(args)



class ReviewedQuotationTests(unittest.TestCase):
    def test_stale_record_fails(self):
        CHECK.stale_quotations([{'constant': 'a'}], {0})
        with self.assertRaisesRegex(CHECK.FIDELITY.Mismatch, 'stale'):
            CHECK.stale_quotations([{'constant': 'a'}, {'constant': 'b'}], {0})


class PlanBindingTests(unittest.TestCase):
    def test_plan_is_bound_to_map_snapshot_and_status(self):
        # Finding 15: --plan is accepted only for this map and this before
        # snapshot, and only as a planned plan.
        before = json.dumps(dict(candidate=dict(modules={'M': dict(path='M.lean')}))).encode()
        mapping = b'{"entries": []}'
        def plan(**over):
            row = dict(status='planned', map_sha256=CHECK.sha(mapping), snapshot_sha256=CHECK.sha(before),
                       files=[dict(path='M.lean', edits=[dict(start=1, end=4, old='abc', new='abd')])])
            row.update(over)
            return json.dumps(row).encode()
        self.assertEqual(CHECK.plan_edits(plan(), mapping, before), {('M', 1, 4, 'abc', 'abd')})
        for bad, message in ((dict(status='applied'), 'not planned'), (dict(map_sha256='0' * 64), 'another map'),
                             (dict(snapshot_sha256='0' * 64), 'another before snapshot')):
            with self.assertRaisesRegex(ValueError, message):
                CHECK.plan_edits(plan(**bad), mapping, before)


class UnionEnvironmentTests(unittest.TestCase):
    def test_union_keeps_per_module_source_fields(self):
        # Rule E binds unhygienic identifiers to command ranges: the union
        # scope must carry each module's commands with its sources.
        merged = CHECK.empty_environment()
        CHECK.extend_items(merged, dict(guards=[], attributes=[], checks=[], receipts=[],
                                        item_modules={k: [] for k in CHECK.FIDELITY.ITEMS},
                                        quotation_sites={'M': [(1, 2, 'x')]}, module_sources={'M': 'src'},
                                        module_decls={'M': {}}, module_commands={'M': [(0, 3)]}))
        self.assertEqual(merged['module_commands'], {'M': [(0, 3)]})


FAKES = ROOT / 'scripts/tests/naming/incremental'


class IncrementalCaptureTests(unittest.TestCase):
    """Per-module content-keyed reuse through the real `capture`, with a fake
    Lake, owned build and exporter (no Lean). Graph: C imports B imports A;
    D imports nothing local; every module imports the external `Init`."""

    SOURCES = {'A.lean': 'def a := 1\n', 'B.lean': 'import A\ndef b := 2\n',
               'C.lean': 'import B\ndef c := 3\n', 'D.lean': 'def d := 4\n'}

    def setUp(self):
        import os
        import subprocess
        self.tmp = Path(tempfile.mkdtemp())
        self.addCleanup(__import__('shutil').rmtree, self.tmp)
        bin_dir, toolchain = self.tmp / 'bin', self.tmp / 'toolchain/lib/lean'
        bin_dir.mkdir()
        (bin_dir / 'lake').symlink_to(FAKES / 'fake_lake.py')
        toolchain.mkdir(parents=True)
        (toolchain / 'Init.olean').write_text('init')
        self.calls = self.tmp / 'calls.log'
        self.env = {'PATH': f'{bin_dir}:{os.environ["PATH"]}', 'FAKE_TOOLCHAIN_LIB': str(toolchain),
                    'FAKE_CALLS': str(self.calls)}
        self.saved = {k: os.environ.get(k) for k in [*self.env, 'FAKE_EXPORTER_VARIANT', 'FAKE_SCHEMA']}
        self.addCleanup(self._restore_env)
        os.environ.update(self.env)
        self.root = self._candidate(self.tmp / 'candidate')
        self.runs = 0

    def _restore_env(self):
        import os
        for key, value in self.saved.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value

    def _candidate(self, root):
        import subprocess
        root.mkdir()
        files = dict(self.SOURCES, **{'lean-toolchain': 'leanprover/lean4:v4.35.0\n', '.gitignore': '.lake/\n'})
        for name, text in files.items():
            (root / name).write_text(text)
        subprocess.run(['git', 'init', '-q', str(root)], check=True)
        subprocess.run(['git', '-C', str(root), 'add', '-A'], check=True)
        subprocess.run(['git', '-C', str(root), '-c', 'user.name=t', '-c', 'user.email=t@t',
                        'commit', '-qm', 'fixture'], check=True)
        return root

    def capture(self, reuse=(), root=None):
        import argparse
        self.runs += 1
        self.calls.write_text('')
        args = argparse.Namespace(
            root=root or self.root, output=self.tmp / f'out{self.runs}', source_dir=['.'],
            module=['C', 'D'], source_only=[], build_prefix=json.dumps(['python3', str(FAKES / 'fake_build.py')]),
            tool_root=None, tool_build_prefix=None, admit_command='["true"]', release_command='["true"]',
            reuse=list(reuse) or None, jobs=2, plan_only=True)
        CHECK.capture(args)
        ran = sorted(line for line in self.calls.read_text().splitlines())
        snapshot = json.loads((args.output / 'snapshot.json').read_bytes())
        return args.output, ran, snapshot

    def edit(self, name, text):
        (self.root / name).write_text(text)

    @staticmethod
    def exports(modules):
        return sorted(f'{mode} {m}' for m in modules for mode in ('export', 'imports'))

    def test_cold_capture_elaborates_every_module(self):
        _, ran, snapshot = self.capture()
        self.assertEqual(ran, self.exports('ABCD'))
        self.assertNotIn('provenance', snapshot)

    def test_unchanged_candidate_reuses_everything(self):
        cold, _, _ = self.capture()
        warm, ran, snapshot = self.capture([cold])
        self.assertEqual(ran, [])
        self.assertEqual({m: row['export'] for m, row in snapshot['provenance'].items()},
                         {m: dict(reused_from=str(cold)) for m in 'ABCD'})
        for m in 'ABCD':
            for kind in ('imports', 'export'):
                self.assertEqual((warm / f'{m}.{kind}.json').read_bytes(), (cold / f'{m}.{kind}.json').read_bytes())

    def test_leaf_edit_reruns_only_that_module(self):
        """Control (a)."""
        cold, _, _ = self.capture()
        self.edit('C.lean', 'import B\ndef c := 30\n')
        _, ran, snapshot = self.capture([cold])
        self.assertEqual(ran, self.exports('C'))
        self.assertEqual(snapshot['provenance']['C'], dict(imports='elaborated', export='elaborated'))

    def test_imported_module_edit_reruns_its_importers_only(self):
        """Control (b): A's artifacts change, so A, B and C rerun; D is reused."""
        cold, _, _ = self.capture()
        self.edit('A.lean', 'def a := 10\n')
        _, ran, snapshot = self.capture([cold])
        self.assertEqual(ran, self.exports('ABC'))
        self.assertEqual(snapshot['provenance']['D']['export'], dict(reused_from=str(cold)))

    def test_changed_exporter_reruns_all(self):
        """Control (c), binary."""
        import os
        cold, _, _ = self.capture()
        os.environ['FAKE_EXPORTER_VARIANT'] = '1'
        _, ran, _ = self.capture([cold])
        self.assertEqual(ran, self.exports('ABCD'))

    def test_changed_export_schema_reruns_all(self):
        """Control (c), schema."""
        import os
        from unittest import mock
        cold, _, _ = self.capture()
        os.environ['FAKE_SCHEMA'] = '9'
        with mock.patch.object(CHECK.FIDELITY, 'CURRENT_SCHEMA', 9):
            _, ran, _ = self.capture([cold])
        # Every export reruns; `--imports` outputs (their own schema, same
        # exporter binary) do not depend on the export schema and are reused.
        self.assertEqual(ran, self.exports('ABCD')[:4])

    def test_changed_configuration_reruns_all(self):
        cold, _, _ = self.capture()
        self.edit('lean-toolchain', 'leanprover/lean4:v4.35.1\n')
        _, ran, _ = self.capture([cold])
        self.assertEqual(ran, self.exports('ABCD'))

    def test_changed_external_artifact_reruns_its_importers(self):
        cold, _, _ = self.capture()
        (Path(self.env['FAKE_TOOLCHAIN_LIB']) / 'Init.olean').write_text('init 2')
        _, ran, _ = self.capture([cold])
        self.assertEqual(ran, self.exports('ABCD'))

    def test_shadowing_import_resolution_reruns(self):
        """A reused `--imports` output must still name what Lean would load."""
        cold, _, _ = self.capture()
        shadow = self.root / '.lake/build/lib/lean/Init.olean'
        shadow.write_text('init')  # same bytes, earlier search-path entry
        with self.assertRaisesRegex(ValueError, 'uninventoried local import'):
            self.capture([cold])
        self.assertEqual(sorted(set(l.split()[0] for l in self.calls.read_text().splitlines())), ['imports'])

    def test_prior_from_another_worktree_is_relocated(self):
        """Paths are not part of the key: a second checkout of the same content
        reuses every output, relocated byte-identically to a fresh capture."""
        cold, _, _ = self.capture()
        other = self._candidate(self.tmp / 'other')
        warm, ran, _ = self.capture([cold], root=other)
        self.assertEqual(ran, [])
        fresh, _, _ = self.capture(root=other)
        for m in 'ABCD':
            for kind in ('imports', 'export'):
                self.assertEqual((warm / f'{m}.{kind}.json').read_bytes(), (fresh / f'{m}.{kind}.json').read_bytes())
        self.assertNotIn(str(self.root), (warm / 'C.export.json').read_text())

    def test_prior_output_that_does_not_round_trip_is_elaborated(self):
        """Across roots a reused output is re-serialized; one whose bytes are
        not the exporter's own serialization is elaborated instead (late)."""
        cold, _, _ = self.capture()
        text = (cold / 'D.export.json').read_text()
        (cold / 'D.export.json').write_text(text.replace('{', '{ ', 1))
        other = self._candidate(self.tmp / 'other')
        _, ran, snapshot = self.capture([cold], root=other)
        self.assertEqual(ran, ['export D'])
        self.assertEqual(snapshot['provenance']['D'], dict(imports=dict(reused_from=str(cold)), export='elaborated'))

    def test_complete_capture_without_reuse_index_is_a_prior(self):
        cold, _, _ = self.capture()
        (cold / 'reuse-index.json').unlink()
        self.edit('C.lean', 'import B\ndef c := 30\n')
        _, ran, _ = self.capture([cold])
        self.assertEqual(ran, self.exports('C'))

    def test_failed_export_capture_resumes(self):
        import os
        cold, _, _ = self.capture()
        self.edit('A.lean', 'def a := 10\n')
        os.environ['FAKE_SCHEMA'] = '6'  # every fresh export is refused at binding
        with self.assertRaisesRegex(ValueError, 'export is not bound'):
            self.capture([cold])
        failed = self.tmp / f'out{self.runs}'
        del os.environ['FAKE_SCHEMA']
        # Exports of A, B, C ran (and were bound-refused); fix and resume from both.
        for m in 'ABC':
            (failed / f'{m}.export.json').unlink()
        _, ran, _ = self.capture([failed, cold])
        self.assertEqual(ran, ['export A', 'export B', 'export C'])  # imports come from the failed run

    def test_reused_receipts_record_provenance_and_time(self):
        cold, _, _ = self.capture()
        receipt = json.loads((cold / 'A-export.command.json').read_bytes())
        self.assertIsInstance(receipt['seconds'], float)
        warm, _, _ = self.capture([cold])
        reused = json.loads((warm / 'A-export.command.json').read_bytes())
        self.assertEqual((reused['reused_from'], reused['seconds'], reused['cwd']),
                         (str(cold), receipt['seconds'], str(self.root.resolve())))

    def test_compact_matches_lean_json_compress(self):
        # Lean names only quote, backslash, newline and carriage return; every
        # other control character is \u00xx (a G0a export string held a tab).
        self.assertEqual(CHECK.compact({'s': 'a\tb\\t\\\tc\b\f\n\r"\x01\x7fé'}),
                         '{"s":"a\\u0009b\\\\t\\\\\\u0009c\\u0008\\u000c\\n\\r\\"\\u0001\x7fé"}')

    def test_longest_prior_first_and_unknown_before_timed(self):
        with tempfile.TemporaryDirectory() as tmp:
            prior = Path(tmp)
            for label, seconds in (('A', 1.0), ('B', 30.0), ('C', 5.0)):
                CHECK.save(prior / f'{label}.command.json', dict(seconds=seconds))
            calls = [(None, None, label, []) for label in 'ABCDE']
            order = CHECK.longest_first(calls, [dict(directory=prior)])
            self.assertEqual([calls[i][2] for i in order], ['D', 'E', 'B', 'C', 'A'])

    def test_cache_dir_from_olean_and_exit3_fallback(self):
        import argparse
        import os
        cache_dir = self.tmp / 'shared-cache'
        os.environ['FAKE_OLEAN_EXIT3'] = 'B'
        try:
            def run_cached():
                self.runs += 1
                self.calls.write_text('')
                args = argparse.Namespace(
                    root=self.root, output=self.tmp / f'cache-out{self.runs}', source_dir=['.'],
                    module=['C', 'D'], source_only=[], build_prefix=json.dumps(['python3', str(FAKES / 'fake_build.py')]),
                    tool_root=None, tool_build_prefix=None, admit_command='["true"]', release_command='["true"]',
                    reuse=None, cache_dir=cache_dir, jobs=2, plan_only=False)
                CHECK.capture(args)
                return args.output, sorted(l for l in self.calls.read_text().splitlines()), json.loads(
                    (args.output / 'snapshot.json').read_bytes())

            out1, ran1, snap1 = run_cached()
            self.assertEqual(snap1['schema_version'], 4)
            self.assertEqual(ran1, ['export B', 'imports A', 'imports B', 'imports C', 'imports D',
                                    'olean A', 'olean C', 'olean D', 'olean-exit3 B'])
            self.assertEqual(snap1['exports']['A']['from_olean'], True)
            self.assertEqual(snap1['exports']['B']['from_olean'], False)
            self.assertTrue((out1 / 'A.meta.json').is_file())

            # Second capture into fresh output dir reuses both olean (A,C,D) and fallback elab (B) from --cache-dir.
            _, ran2, snap2 = run_cached()
            self.assertEqual(ran2, ['imports A', 'imports B', 'imports C', 'imports D', 'olean-exit3 B'])
            self.assertTrue(snap2['provenance']['A']['export'].get('cache_hit'))
            self.assertTrue(snap2['provenance']['B']['export'].get('cache_hit'))

            # Leaf edit to A invalidates A in --cache-dir AND B's fallback elab_key (since B imports A's changed .olean);
            # downstream C (unchanged own .olean in fake_build) stays cached under olean_key!
            self.edit('A.lean', 'def a := 99\n')
            _, ran3, _ = run_cached()
            self.assertEqual(ran3, ['export B', 'imports A', 'imports B', 'imports C', 'imports D', 'olean A', 'olean-exit3 B'])
        finally:
            os.environ.pop('FAKE_OLEAN_EXIT3', None)


class ComponentCompareTests(unittest.TestCase):
    def _build_snapshot(self, root_dir, modules_spec):
        """Materialize a schema-4 snapshot with real Schema-8 `.export.json` + `.meta.json`."""
        root_dir = Path(root_dir)
        root_dir.mkdir(parents=True, exist_ok=True)
        files = {}
        mods = {}
        headers_mods = {}
        artifacts = {}
        local_built = {}
        local_ileans = {}
        exports = {}
        for mod, spec in modules_spec.items():
            src = spec['source']
            rel = f'{mod}.lean'
            src_sha = CHECK.sha(src.encode())
            files[rel] = src_sha
            imps = list(spec.get('imports', ()))
            mods[mod] = dict(path=rel, sha256=src_sha, imports=imps, is_module=False)
            direct_info = [[i, False, False, False] for i in imps]
            headers_mods[mod] = dict(path=rel, is_module=False, direct_imports=direct_info)

            olean = root_dir / f'{mod}.olean'
            olean.write_text(f'olean {mod}')
            ilean = root_dir / f'{mod}.ilean'
            ilean.write_text('{}')
            arts = {part: (dict(path=str(olean), sha256=CHECK.file_sha(olean)) if part == 'olean' else None)
                    for part in CHECK.PARTS}
            artifacts[mod] = arts
            local_built[mod] = arts
            local_ileans[mod] = dict(path=str(ilean), sha256=CHECK.file_sha(ilean))

            decls = {}
            for dname in spec.get('roots', ()):
                leaf = dname.rsplit('.', 1)[-1]
                idx_pos = src.find(leaf)
                if idx_pos >= 0:
                    prefix = src[:idx_pos]
                    line = prefix.count('\n')
                    col = idx_pos - (prefix.rfind('\n') + 1)
                    decls[dname] = [line, col, line, col + len(leaf), line, col, line, col + len(leaf)]
            expr_pool = spec.get('expr_pool', [])
            level_pool = spec.get('level_pool', [])
            export_obj = dict(
                schema_version=8,
                lean_version='fixture',
                import_modules=sorted(imps),
                source=src,
                level_pool=level_pool,
                expr_pool=expr_pool,
                index=dict(version=5, module=mod, directImports=direct_info, decls=decls, references={},
                           naming_syntax=dict(version=2, commands=[], from_olean=spec.get('from_olean', True))),
                constants=spec['constants'],
                guards=spec.get('guards', []),
                attribute_syntax=spec.get('attribute_syntax', []),
                checked_commands=spec.get('checked_commands', []),
            )
            exp_path = root_dir / f'{mod}.export.json'
            exp_path.write_bytes(CHECK.compact(export_obj).encode())
            exp_sha = CHECK.file_sha(exp_path)
            meta = CHECK.FIDELITY.extract_module_meta(exp_path, exp_sha)
            meta_path = root_dir / f'{mod}.meta.json'
            meta_path.write_bytes(CHECK.compact(meta).encode())
            exports[mod] = dict(path=exp_path.name, sha256=exp_sha, meta_path=meta_path.name,
                                meta_sha256=CHECK.file_sha(meta_path), from_olean=spec.get('from_olean', True))

        source_before = dict(head='fixture', source_dirs=['.'], files=files, modules=mods)
        headers = dict(schema_version=1, lean_version='fixture', modules=headers_mods)
        (root_dir / 'source-before.json').write_text(json.dumps(source_before))
        (root_dir / 'headers.json').write_text(json.dumps(headers))
        candidate = CHECK.bind_headers(source_before, headers)
        roots = sorted(modules_spec)
        selected = CHECK.closure(candidate['modules'], roots)
        snap = dict(
            schema_version=4, status='OK', build=dict(exit=0),
            candidate=candidate, roots=roots, selected=selected, source_only=[], producers=selected,
            headers_sha256=CHECK.file_sha(root_dir / 'headers.json'),
            exporter_sha256='fake-exporter', tool_sources={},
            artifacts=artifacts, local_built=local_built, local_ileans=local_ileans, exports=exports,
        )
        snap_path = root_dir / 'snapshot.json'
        snap_path.write_text(json.dumps(snap))
        return snap_path

    @staticmethod
    def _defn(type_id, val_id):
        return dict(kernel=dict(universes=0, type=type_id, payload=['definition', 'Lean.DefinitionSafety.safe', val_id]),
                    attributes={}, equation_origin=None)

    def test_cross_component_renamed_generated_constant_and_mutation_control(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            b_pool = [['nat', 7], ['const', ['name', 'Upstream.inst_1'], []], ['const', ['name', 'Nat'], []]]
            a_pool = [['nat', 7], ['const', ['name', 'Upstream.inst_2'], []], ['const', ['name', 'Nat'], []],
                      ['const', ['name', 'Upstream.other'], []]]
            u_pool = [['nat', 1], ['const', ['name', 'Nat'], []]]
            before_spec = {
                'Unaffected': dict(source='def keep := 1\n', roots=['Unaffected.keep'], expr_pool=u_pool,
                                   constants={'Unaffected.keep': self._defn(1, 0)}),
                'Upstream': dict(source='def old := 7\n', roots=['Upstream.old'], expr_pool=[['nat', 7], ['const', ['name', 'Nat'], []]],
                                 constants={'Upstream.old': self._defn(1, 0), 'Upstream.inst_1': self._defn(1, 0)}),
                'Downstream': dict(source='def use := 7\n', imports=['Upstream'], roots=['Downstream.use'], expr_pool=b_pool,
                                   constants={'Downstream.use': self._defn(2, 1)}),
            }
            after_spec = {
                'Unaffected': before_spec['Unaffected'],
                'Upstream': dict(source='def new := 7\n', roots=['Upstream.new'], expr_pool=[['nat', 7], ['const', ['name', 'Nat'], []]],
                                 constants={'Upstream.new': self._defn(1, 0), 'Upstream.inst_2': self._defn(1, 0)}),
                'Downstream': dict(source='def use2 := 7\n', imports=['Upstream'], roots=['Downstream.use2'], expr_pool=a_pool,
                                   constants={'Downstream.use2': self._defn(2, 1)}),
            }
            row_u = dict(old='Upstream.old', new='Upstream.new', kind='declaration', layer='execution', rule='4', source='t')
            row_d = dict(old='Downstream.use', new='Downstream.use2', kind='declaration', layer='execution', rule='4', source='t')
            mapping = dict(EMPTY, entries=[row_u, row_d])
            b_path = self._build_snapshot(root / 'before', before_spec)
            a_path = self._build_snapshot(root / 'after', after_spec)
            verdict = CHECK.compare_components(b_path, a_path, mapping)
            self.assertEqual(verdict['fast_path_modules'], ['Unaffected'])
            self.assertEqual([c['before_modules'] for c in verdict['active_components']], [['Upstream'], ['Downstream']])

            # Negative control: mutating Downstream.use2 to reference Upstream.other must fail!
            bad_spec = copy.deepcopy(after_spec)
            bad_spec['Downstream']['constants']['Downstream.use2'] = self._defn(2, 3)
            bad_path = self._build_snapshot(root / 'bad', bad_spec)
            with self.assertRaisesRegex(CHECK.FIDELITY.Mismatch, 'external generated constant'):
                CHECK.compare_components(b_path, bad_path, mapping)

    def test_compare_components_reports_the_respelling_audit_trail(self):
        # Neon finding 7, R17: the landing verdict lists every derived
        # respelling (with constant and module), the R12/R12b drops and the
        # unhygienic respellings, which compare_components used to discard.
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            def pool(leaf):
                return [['str', 'Upstream'], ['str', leaf], ['const', ['name', 'Lean.Name.mkStr2'], []],
                        ['app', 2, 0], ['app', 3, 1], ['const', ['name', 'Lean.Name'], []]]
            upstream = lambda leaf: dict(source=f'def {leaf} := 7\n', roots=[f'Upstream.{leaf}'],
                                         expr_pool=[['nat', 7], ['const', ['name', 'Nat'], []]],
                                         constants={f'Upstream.{leaf}': self._defn(1, 0)})
            down = lambda leaf: dict(source=f'def lit := ``Upstream.{leaf}\n', imports=['Upstream'],
                                     roots=['Downstream.lit'], expr_pool=pool(leaf),
                                     constants={'Downstream.lit': self._defn(5, 4)})
            row_u = dict(old='Upstream.old', new='Upstream.new', kind='declaration', layer='execution', rule='4', source='t')
            mapping = dict(EMPTY, entries=[row_u])
            b_path = self._build_snapshot(root / 'before', {'Upstream': upstream('old'), 'Downstream': down('old')})
            a_path = self._build_snapshot(root / 'after', {'Upstream': upstream('new'), 'Downstream': down('new')})
            verdict = CHECK.compare_components(b_path, a_path, mapping)
            self.assertEqual(verdict['derived_literals_respelled'],
                             [dict(constant='Downstream.lit', module='Downstream', old='Upstream.old',
                                   new='Upstream.new', reason='name literal')])
            self.assertEqual(verdict['preresolved_drops'], [])
            self.assertEqual(verdict['unhygienic_respellings'], [])

    def test_global_uniform_namespace_and_multi_component_reloc_aux_controls(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            # CompA moves Ns.a -> NewNs.a and holds ``Ns` (`Name.mkStr1 "Ns"); CompB leaves Ns.b unmoved.
            lit_pool = [
                ['const', ['name', 'Lean.Name.mkStr1'], []],
                ['str', 'Ns'],
                ['app', 0, 1],
                ['const', ['name', 'Lean.Name'], []],
                ['const', ['name', 'Lean.Name.mkStr1'], []],
                ['str', 'NewNs'],
                ['app', 4, 5],
            ]
            u_pool = [['nat', 1], ['const', ['name', 'Nat'], []]]
            before_ns = {
                'CompA': dict(source='def a := 1\ndef lit := 1\n', roots=['Ns.a', 'CompA.lit'], expr_pool=lit_pool + u_pool,
                              constants={'Ns.a': self._defn(8, 7), 'CompA.lit': self._defn(3, 2)}),
                'CompB': dict(source='def b := 1\n', roots=['Ns.b'], expr_pool=u_pool,
                              constants={'Ns.b': self._defn(1, 0)}),
            }
            after_ok = copy.deepcopy(before_ns)
            after_ok['CompA']['source'] = 'def a2 := 1\ndef lit := 1\n'
            after_ok['CompA']['roots'] = ['NewNs.a', 'CompA.lit']
            after_ok['CompA']['constants'] = {'NewNs.a': self._defn(8, 7), 'CompA.lit': self._defn(3, 2)}
            after_ok['CompB']['source'] = 'def b := 1 -- changed\n'
            row_a = dict(old='Ns.a', new='NewNs.a', kind='declaration', layer='execution', rule='4', source='t')
            map_ns = dict(EMPTY, entries=[row_a])
            bp = self._build_snapshot(root / 'ns_b', before_ns)
            ap = self._build_snapshot(root / 'ns_a', after_ok)
            self.assertEqual(CHECK.compare_components(bp, ap, map_ns)['status'], 'OK')

            after_bad = copy.deepcopy(after_ok)
            after_bad['CompA']['constants']['CompA.lit'] = self._defn(3, 6)  # wrongly changed `Ns` -> `NewNs`
            abp = self._build_snapshot(root / 'ns_bad', after_bad)
            with self.assertRaises(CHECK.FIDELITY.Mismatch):
                CHECK.compare_components(bp, abp, map_ns)

            # Multi-component is_reloc_aux control: M3 (unrelocated) also holds M1.f.match_1
            m_pool = [['nat', 5], ['const', ['name', 'Nat'], []], ['const', ['name', 'M1.f.match_1'], []],
                      ['const', ['name', 'M1.f.match_2'], []]]
            reloc_b = {
                'M1': dict(source='def f := 5\n', roots=['M1.f'], expr_pool=m_pool,
                           constants={'M1.f': self._defn(1, 2), 'M1.f.match_1': self._defn(1, 0)}),
                'M2': dict(source='def g := 1\n', roots=['M2.g'], expr_pool=m_pool,
                           constants={'M2.g': self._defn(1, 0)}),
                'M3': dict(source='def h := 1\n', roots=['M3.h'], expr_pool=m_pool,
                           constants={'M3.h': self._defn(1, 0), 'M1.f.match_1': self._defn(1, 0)}),
            }
            reloc_a = {
                'M1': dict(source='def moved := 1\n', roots=[], expr_pool=m_pool, constants={}),
                'M2': dict(source='def g := 1\ndef f := 5\n', roots=['M2.g', 'M1.f'], expr_pool=m_pool,
                           constants={'M2.g': self._defn(1, 0), 'M1.f': self._defn(1, 3), 'M1.f.match_2': self._defn(1, 0)}),
                'M3': dict(source='def h := 1 -- changed\n', roots=['M3.h'], expr_pool=m_pool,
                           constants={'M3.h': self._defn(1, 0), 'M1.f.match_1': self._defn(1, 0)}),
            }
            row_r = dict(old='M1.f', new='M1.f', kind='relocation', layer='execution', rule='4', source='t',
                         from_module='M1', to_module='M2')
            rb = self._build_snapshot(root / 'rel_b', reloc_b)
            ra = self._build_snapshot(root / 'rel_a', reloc_a)
            with self.assertRaises(CHECK.FIDELITY.Mismatch):
                CHECK.compare_components(rb, ra, dict(EMPTY, entries=[row_r]))

    def test_fast_path_disjointness_promotes_unapplied_rows(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pool_u = [
                ['nat', 1], ['const', ['name', 'Nat'], []],
                ['const', ['name', 'Lean.Name.mkStr2'], []], ['str', 'V'], ['str', 'lit'],
                ['app', 2, 3], ['app', 5, 4], ['const', ['name', 'Lean.Name'], []],
            ]
            pool_v = [['nat', 2], ['const', ['name', 'Nat'], []]]
            spec_b = {
                'U': dict(source='def stay := 1\ndef ns_keep := 1\ndef use_lit := 1\n',
                          roots=['U.stay', 'Ns.keep', 'U.use_lit'],
                          expr_pool=pool_u,
                          constants={
                              'U.stay': self._defn(1, 0),
                              'Ns.keep': self._defn(1, 0),
                              'U.use_lit': self._defn(7, 6),
                          }),
                'V': dict(source='def lit := 2\ndef other := 2\n',
                          roots=['V.lit', 'V.other'],
                          expr_pool=pool_v,
                          constants={
                              'V.lit': self._defn(1, 0),
                              'V.other': self._defn(1, 0),
                          }),
            }
            spec_other = copy.deepcopy(spec_b)
            spec_other['V']['source'] = 'def lit := 2\ndef other2 := 2\n'
            spec_other['V']['roots'] = ['V.lit', 'V.other2']
            spec_other['V']['constants'] = {'V.lit': self._defn(1, 0), 'V.other2': self._defn(1, 0)}
            spec_vlit = copy.deepcopy(spec_b)
            spec_vlit['V']['source'] = 'def lit_new := 2\ndef other := 2\n'
            spec_vlit['V']['roots'] = ['V.lit_new', 'V.other']
            spec_vlit['V']['constants'] = {'V.lit_new': self._defn(1, 0), 'V.other': self._defn(1, 0)}

            bp = self._build_snapshot(root / 'b', spec_b)
            ap = self._build_snapshot(root / 'a', spec_b)
            ap_other = self._build_snapshot(root / 'a_other', spec_other)
            ap_vlit = self._build_snapshot(root / 'a_vlit', spec_vlit)

            # Disjoint map (EMPTY and unrelated V.other -> V.other2) keeps U on fast_path.
            self.assertEqual(CHECK.compare_components(bp, ap, EMPTY)['fast_path_modules'], ['U', 'V'])
            verdict_other = CHECK.compare_components(
                bp, ap_other,
                dict(EMPTY, entries=[dict(old='V.other', new='V.other2', kind='declaration', layer='execution', rule='4', source='t')]))
            self.assertEqual(verdict_other['fast_path_modules'], ['U'])

            # Unapplied declaration or namespace rows touching U promote U and fail.
            for entry in (
                dict(old='U.stay', new='U.moved', kind='declaration', layer='execution', rule='4', source='t'),
                dict(old='Ns', new='NewNs', kind='namespace', layer='execution', rule='4', source='t'),
            ):
                with self.assertRaises(CHECK.FIDELITY.Mismatch):
                    CHECK.compare_components(bp, ap, dict(EMPTY, entries=[entry]))

            # Cross-module V.lit -> V.lit_new updated in V while U stays byte-identical with
            # Lean.Name.mkStr2 "V" "lit" MUST promote U off fast_path and fail!
            vlit_map = dict(EMPTY, entries=[
                dict(old='V.lit', new='V.lit_new', kind='declaration', layer='execution', rule='4', source='t')])
            with self.assertRaises(CHECK.FIDELITY.Mismatch):
                CHECK.compare_components(bp, ap_vlit, vlit_map)

    def test_compare_components_refuses_export_mode_flip(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            pool = [['nat', 1], ['const', ['name', 'Nat'], []]]
            spec_b = {'M': dict(source='def old := 1\n', roots=['M.old'], expr_pool=pool,
                                constants={'M.old': self._defn(1, 0)}, from_olean=True)}
            spec_a = {'M': dict(source='def new := 1\n', roots=['M.new'], expr_pool=pool,
                                constants={'M.new': self._defn(1, 0)}, from_olean=False)}
            bp = self._build_snapshot(root / 'b', spec_b)
            ap = self._build_snapshot(root / 'a', spec_a)
            mapping = dict(EMPTY, entries=[
                dict(old='M.old', new='M.new', kind='declaration', layer='execution', rule='4', source='t')])
            with self.assertRaisesRegex(ValueError, 'export mode mismatch'):
                CHECK.compare_components(bp, ap, mapping)

    def test_downstream_splitter_dedup_and_collect_all_no_cascade(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            # 1) Two relocated declarations M1/M2 -> M3 merge their identical match_1 helpers
            # and downstream consumer C deduplicates their identical .splitter helpers.
            b_pool = [
                ['nat', 1],                                  # 0
                ['const', ['name', 'Nat'], []],              # 1
                ['const', ['name', 'A.f.match_1'], []],      # 2
                ['const', ['name', 'B.g.match_1'], []],      # 3
                ['const', ['name', '_private.C.0.A.f.match_1.splitter'], []],  # 4
                ['const', ['name', '_private.C.0.B.g.match_1.splitter'], []],  # 5
                ['nat', 99],                                 # 6
            ]
            a_pool = [
                ['nat', 1],                                  # 0
                ['const', ['name', 'Nat'], []],              # 1
                ['const', ['name', 'M3.f.match_1'], []],     # 2
                ['const', ['name', '_private.C.0.M3.f.match_1.splitter'], []],  # 3
            ]
            spec_b = {
                'M1': dict(source='def f := 1\n', roots=['A.f'], expr_pool=b_pool,
                           constants={'A.f': self._defn(1, 2), 'A.f.match_1': self._defn(1, 0)}),
                'M2': dict(source='def g := 1\n', roots=['B.g'], expr_pool=b_pool,
                           constants={'B.g': self._defn(1, 3), 'B.g.match_1': self._defn(1, 0)}),
                'M3': dict(source='-- target\n', roots=[], expr_pool=b_pool, constants={}),
                'C': dict(source='def h := 1\ndef k := 1\n', imports=['M1', 'M2'], roots=['C.h', 'C.k'], expr_pool=b_pool,
                          constants={
                              'C.h': self._defn(1, 4),
                              'C.k': self._defn(1, 5),
                              '_private.C.0.A.f.match_1.splitter': self._defn(1, 2),
                              '_private.C.0.B.g.match_1.splitter': self._defn(1, 3),
                          }),
            }
            spec_a = {
                'M1': dict(source='-- moved\n', roots=[], expr_pool=a_pool, constants={}),
                'M2': dict(source='-- moved\n', roots=[], expr_pool=a_pool, constants={}),
                'M3': dict(source='def f := 1\ndef g := 1\n', roots=['M3.f', 'M3.g'], expr_pool=a_pool,
                           constants={'M3.f': self._defn(1, 2), 'M3.g': self._defn(1, 2), 'M3.f.match_1': self._defn(1, 0)}),
                'C': dict(source='def h := 1\ndef k := 1 -- changed\n', imports=['M3'], roots=['C.h', 'C.k'], expr_pool=a_pool,
                          constants={
                              'C.h': self._defn(1, 3),
                              'C.k': self._defn(1, 3),
                              '_private.C.0.M3.f.match_1.splitter': self._defn(1, 2),
                          }),
            }
            mapping = dict(EMPTY, entries=[
                dict(old='A.f', new='M3.f', kind='relocation', from_module='M1', to_module='M3', layer='execution', rule='4', source='t'),
                dict(old='B.g', new='M3.g', kind='relocation', from_module='M2', to_module='M3', layer='execution', rule='4', source='t'),
            ])
            bp = self._build_snapshot(root / 'spl_b', spec_b)
            ap = self._build_snapshot(root / 'spl_a', spec_a)
            self.assertEqual(CHECK.compare_components(bp, ap, mapping)['status'], 'OK')

            # Negative control: mutating one of C's before-side splitters MUST fail.
            spec_bad_spl = copy.deepcopy(spec_b)
            spec_bad_spl['C']['constants']['_private.C.0.B.g.match_1.splitter'] = self._defn(1, 6)
            bp_bad = self._build_snapshot(root / 'spl_b_bad', spec_bad_spl)
            with self.assertRaises(CHECK.FIDELITY.Mismatch):
                CHECK.compare_components(bp_bad, ap, mapping)

            # 2) --collect-all harvest control: an upstream mismatch in M1 must not
            # starve downstream C of paired valid generated helpers from M1.
            c_pool_b = [['nat', 1], ['nat', 2], ['const', ['name', 'Nat'], []], ['const', ['name', 'U.ok.aux'], []]]
            c_pool_a = [['nat', 1], ['nat', 2], ['const', ['name', 'Nat'], []], ['const', ['name', 'U.ok2.aux'], []]]
            cb = {
                'U': dict(source='def bad := 1\ndef ok := 1\n', roots=['U.bad', 'U.ok'], expr_pool=c_pool_b,
                          constants={'U.bad': self._defn(2, 0), 'U.ok': self._defn(2, 3), 'U.ok.aux': self._defn(2, 0)}),
                'D': dict(source='def use := 1\n', imports=['U'], roots=['D.use'], expr_pool=c_pool_b,
                          constants={'D.use': self._defn(2, 3)}),
            }
            ca = {
                'U': dict(source='def bad := 2\ndef ok2 := 1\n', roots=['U.bad', 'U.ok2'], expr_pool=c_pool_a,
                          constants={'U.bad': self._defn(2, 1), 'U.ok2': self._defn(2, 3), 'U.ok2.aux': self._defn(2, 0)}),
                'D': dict(source='def use2 := 1\n', imports=['U'], roots=['D.use2'], expr_pool=c_pool_a,
                          constants={'D.use2': self._defn(2, 3)}),
            }
            cmap = dict(EMPTY, entries=[
                dict(old='U.ok', new='U.ok2', kind='declaration', layer='execution', rule='4', source='t'),
                dict(old='D.use', new='D.use2', kind='declaration', layer='execution', rule='4', source='t'),
            ])
            cbp = self._build_snapshot(root / 'col_b', cb)
            cap = self._build_snapshot(root / 'col_a', ca)
            with self.assertRaises(CHECK.FIDELITY.Mismatch) as ctx:
                CHECK.compare_components(cbp, cap, cmap, collect=True)
            msg = str(ctx.exception)
            self.assertIn('[U]', msg)
            self.assertNotIn('[D]', msg)


if __name__ == '__main__':
    unittest.main()
