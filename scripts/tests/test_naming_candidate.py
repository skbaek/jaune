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
        os.environ['FAKE_SCHEMA'] = '8'
        with mock.patch.object(CHECK.FIDELITY, 'CURRENT_SCHEMA', 8):
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


if __name__ == '__main__':
    unittest.main()
