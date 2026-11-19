"""The bridge-ledger check (goal jaune-shape-and-names-v1, section 8).

Mode B's closure comparison on synthetic exports and Mode A on a synthetic
Git repository; each defect is planted alone."""
import copy
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest
import unittest.mock

ROOT = Path(__file__).parents[2]
SPEC = importlib.util.spec_from_file_location('check_bridge_ledger', ROOT / 'scripts/check-bridge-ledger.py')
LEDGER = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(LEDGER)
FIDELITY = LEDGER.FIDELITY
STANDARD = ['Classical.choice', 'Quot.sound', 'propext']


def c(name):
    return ['const', ['name', name], []]


def app(f, *xs):
    for x in xs:
        f = ['app', f, x]
    return f


def definition(value):
    return dict(kernel=dict(type=c('Nat'), universes=0, payload=['definition', value]), attributes={})


def environment(constants):
    return dict(constants=constants, roots=set(constants), guards=[], attributes=[], version='fixture',
                modules={}, receipts=[], checks=[])


def renamer(rows):
    return [dict(old=a, new=b, kind='declaration') for a, b in rows.items()]


class ClosureTests(unittest.TestCase):
    """`closure_compare`: the old root's closure under the map, against the tag."""

    def setUp(self):
        # Old revision: the root calls a helper and Nat.add (not exported: a
        # non-Jaune constant); `J.other` is outside the root's closure.
        self.before = environment({
            'J.root': definition(app(c('Nat.add'), c('J.helper'), ['lit', 1])),
            'J.helper': definition(['lit', 1]),
            'J.other': definition(['lit', 2]),
        })
        # The tag: the old side waits under `J.Old`, everything else in place.
        self.after = environment({
            'J.Old.root': definition(app(c('Nat.add'), c('J.helper'), ['lit', 1])),
            'J.helper': definition(['lit', 1]),
            'J.other': definition(['lit', 2]),
        })
        self.maps = [renamer({'J.root': 'J.Old.root'})]
        self.exempt = {}

    def compare(self):
        return LEDGER.closure_compare(self.before, self.after, self.maps, ['J.root'], ['J.Old.root'], self.exempt)

    def test_unchanged_closure_passes(self):
        result = self.compare()
        self.assertEqual(result['verdict'], 'OK')
        self.assertEqual((result['closure'], result['authored'], result['external_references']), (2, 2, 2))

    def test_changed_body_of_a_closure_member_fails(self):
        self.after['constants']['J.helper'] = definition(['lit', 7])
        result = self.compare()
        self.assertEqual(result['verdict'], 'REGRESSION')
        self.assertTrue(any(m.startswith('constant J.helper:') for m in result['mismatches']), result['mismatches'])

    def test_changed_attribute_of_a_closure_member_fails(self):
        self.after['constants']['J.helper'] = dict(definition(['lit', 1]), attributes={'inline': 'always'})
        self.assertEqual(self.compare()['verdict'], 'REGRESSION')

    def test_out_of_closure_change_passes(self):
        self.after['constants']['J.other'] = definition(['lit', 9])
        self.assertEqual(self.compare()['verdict'], 'OK')

    def test_exempt_change_passes_only_with_a_bridged_by_entry(self):
        self.after['constants']['J.helper'] = definition(['lit', 7])
        ledger = dict(entries=[dict(id='E1', old=dict(roots=['J.root']),
                                    exempt=[dict(name='J.helper', bridged_by='E2')]),
                               dict(id='E2', kind='theorem', old=dict(roots=['J.helper']),
                                    new=dict(names=['J.helper2']), exempt=[])])
        self.exempt = LEDGER.exemptions(ledger, ledger['entries'][0])
        result = self.compare()
        self.assertEqual(result['verdict'], 'OK')
        self.assertEqual(result['stopped_exempt'], ['J.helper'])
        # Without a bridging entry the exemption is refused, and without the
        # exemption the change is a regression.
        for row in (dict(name='J.helper'), dict(name='J.helper', bridged_by='E9'),
                    dict(name='J.helper', bridged_by='E1')):
            ledger['entries'][0]['exempt'] = [row]
            with self.assertRaises(LEDGER.Finding):
                LEDGER.exemptions(ledger, ledger['entries'][0])
        self.exempt = {}
        self.assertEqual(self.compare()['verdict'], 'REGRESSION')

    def test_exempt_replacement_admits_the_replaced_reference(self):
        # The old side now calls the bridged replacement (W6b's in-place edit).
        self.after['constants']['J.Old.root'] = definition(app(c('Nat.add'), c('J.helper2'), ['lit', 1]))
        self.after['constants']['J.helper2'] = definition(['lit', 1])
        self.assertEqual(self.compare()['verdict'], 'REGRESSION')
        self.exempt = {'J.helper': dict(name='J.helper', bridged_by='E2', replacement='J.helper2')}
        self.assertEqual(self.compare()['verdict'], 'OK')

    def test_old_root_must_map_to_the_recorded_old_side(self):
        result = LEDGER.closure_compare(self.before, self.after, self.maps, ['J.root'], ['J.Elsewhere.root'], {})
        self.assertEqual(result['verdict'], 'REGRESSION')
        self.assertIn('ledger names J.Elsewhere.root', result['mismatches'][0])

    def test_exemptions_cannot_remove_the_root_from_either_closure(self):
        self.exempt = {'J.root': dict(name='J.root', bridged_by='E2')}
        with self.assertRaisesRegex(LEDGER.Finding, '^old roots cannot be exempt'):
            self.compare()
        self.exempt = {'J.helper': dict(name='J.helper', bridged_by='E2', replacement='J.Old.root')}
        with self.assertRaisesRegex(LEDGER.Finding, '^tag-side old roots cannot be exempt'):
            self.compare()

    def test_missing_closure_member_at_the_tag_fails(self):
        del self.after['constants']['J.helper']
        self.assertEqual(self.compare()['verdict'], 'REGRESSION')

    def test_new_dependency_of_the_old_side_fails(self):
        self.after['constants']['J.Old.root'] = definition(app(c('Nat.add'), c('J.helper'), c('J.extra')))
        self.after['constants']['J.extra'] = definition(['lit', 1])
        self.after['roots'].add('J.extra')
        self.assertEqual(self.compare()['verdict'], 'REGRESSION')

    def test_closure_walk_visits_a_shared_expression_once(self):
        class CountedExpr(list):
            visits = 0

            def __iter__(self):
                self.visits += 1
                return super().__iter__()

        shared = CountedExpr(app(c('J.helper'), c('Nat.add')))
        nested = shared
        for _ in range(8):
            nested = app(nested, nested)
        constants = {'J.one': definition(nested), 'J.two': definition(shared),
                     'J.helper': definition(['lit', 1])}

        self.assertEqual(LEDGER.walk(constants, ['J.one', 'J.two'], {'J.helper'}),
                         ({'J.one', 'J.two'}, {'J.helper'}, {'Nat', 'Nat.add'}))
        self.assertEqual(shared.visits, 1)
        self.assertEqual(LEDGER.walk(constants, ['J.one'], set()),
                         ({'J.one', 'J.helper'}, set(), {'Nat', 'Nat.add'}))
        self.assertEqual(shared.visits, 2)
        self.assertEqual(LEDGER.references(('const', ('name', 'J.helper'), ()), set()), {'J.helper'})

    def test_maps_compose_in_order(self):
        self.after['constants']['J.Older.root'] = self.after['constants'].pop('J.Old.root')
        self.after['roots'] = set(self.after['constants'])
        self.maps = [renamer({'J.root': 'J.Old.root'}), renamer({'J.Old.root': 'J.Older.root'})]
        result = LEDGER.closure_compare(self.before, self.after, self.maps, ['J.root'], ['J.Older.root'], {})
        self.assertEqual(result['verdict'], 'OK')

    def test_generated_closure_members_are_compared(self):
        self.before['constants']['J.root'] = definition(app(c('J.root.match_1'), c('J.helper')))
        self.before['constants']['J.root.match_1'] = definition(['lit', 3])
        self.before['roots'].discard('J.root.match_1')
        self.after['constants']['J.Old.root'] = definition(app(c('J.Old.root.match_1'), c('J.helper')))
        self.after['constants']['J.Old.root.match_1'] = definition(['lit', 3])
        self.after['roots'].discard('J.Old.root.match_1')
        result = self.compare()
        self.assertEqual((result['verdict'], result['generated']), ('OK', 1))
        self.after['constants']['J.Old.root.match_1'] = definition(['lit', 4])
        self.assertEqual(self.compare()['verdict'], 'REGRESSION')


    def test_unreached_generated_members_match_by_graph_not_by_number(self):
        # The root's own comparison stops at its first difference, so its
        # matchers are matched afterwards by graph; their numbering swapped.
        self.before['constants']['J.root'] = definition(app(['lit', 0], c('J.root.match_1'), c('J.root.match_2')))
        self.before['constants']['J.root.match_1'] = definition(['lit', 3])
        self.before['constants']['J.root.match_2'] = definition(['lit', 4])
        self.after['constants']['J.Old.root'] = definition(app(['lit', 9], c('J.Old.root.match_2'),
                                                               c('J.Old.root.match_1')))
        self.after['constants']['J.Old.root.match_1'] = definition(['lit', 4])
        self.after['constants']['J.Old.root.match_2'] = definition(['lit', 3])
        for env in (self.before, self.after):
            env['roots'] -= {n for n in env['constants'] if '.match_' in n}
        result = self.compare()
        self.assertEqual([m.split(':')[0] for m in result['mismatches']], ['constant J.root'])
        self.after['constants']['J.Old.root.match_2'] = definition(['lit', 5])
        self.assertIn('no verified generated-constant match for J.root.match_1',
                      ' '.join(self.compare()['mismatches']))

class ModeBGlueTests(unittest.TestCase):
    """`mode_b` end to end from capture-shaped snapshots over synthetic
    compiler exports (the snapshot reader itself is naming-candidate's)."""

    def export(self, tmp, label, root, helper_value):
        source = f'def {root.split(".", 1)[1]} := helper\ndef helper := {helper_value}\n'
        width = len(root.split('.', 1)[1])
        index = dict(version=5, module='M', directImports=[], references={},
                     decls={root: [0, 0, 0, 4 + width, 0, 4, 0, 4 + width], 'J.helper': [1, 0, 1, 15, 1, 4, 1, 10]})
        constants = {root: dict(definition(app(c('Nat.succ'), c('J.helper'))), equation_origin=None),
                     'J.helper': dict(definition(['lit', helper_value]), equation_origin=None)}
        data = dict(schema_version=6, lean_version='x', source=source, index=index, constants=constants,
                    guards=[], attribute_syntax=[], checked_commands=[], imports={})
        path = Path(tmp) / f'{label}.export.json'
        path.write_text(json.dumps(data))
        (Path(tmp) / f'{label}.snapshot.json').write_text('{}')
        modules = {'M': dict(path='M.lean', sha256=hashlib.sha256(source.encode()).hexdigest(), imports=[],
                             is_module=False)}
        return dict(candidate=dict(head='0' * 40, files={}, modules=modules, source_dirs=['.']),
                    tool_sources={}, artifacts={}, exports={'M': dict(path=path.name, sha256='x')},
                    export_paths={'M': path})

    def run_b(self, helper_after, repeat_scope=False):
        ledger = dict(schema_version=1, standard_axioms=STANDARD,
                      gates=dict(GX=dict(tag='gate/gx', commit=None, status='pending')),
                      entries=[dict(id='GX-1', gate='GX', kind='theorem', theorem='J.bridge', module='M',
                                    audit=[dict(kind='union_walk', file='U.lean')],
                                    old=dict(revision='0' * 40, roots=['J.root'], modules=['M'],
                                             at_tag=['J.Old.root'], modules_at_tag=['M']),
                                    new=dict(names=[], modules=[]), exempt=[], maps=[], n4_receipts=[],
                                    accepted=[], gaps=[], notes=[])])
        with tempfile.TemporaryDirectory() as tmp:
            sides = {'before': self.export(tmp, 'before', 'J.root', 1),
                     'after': self.export(tmp, 'after', 'J.Old.root', helper_after)}
            map_file = Path(tmp) / 'map.json'
            map_file.write_text(json.dumps(dict(schema_version=1, retired_tokens=[], allowed_abbreviations=[],
                                                entries=[dict(old='J.root', new='J.Old.root', kind='declaration',
                                                              layer='execution', rule='4', source='fixture')])))
            ledger['entries'][0]['maps'] = [dict(path='map.json', revision=None, gap='fixture',
                                                 sha256=hashlib.sha256(map_file.read_bytes()).hexdigest())]
            if repeat_scope:
                original = ledger['entries'][0]
                ledger['entries'].append(dict(original, id='GX-2', theorem='J.anotherBridge'))
                ledger['entries'].append(dict(original, id='GX-3', theorem='J.changedBridge',
                                              old=dict(original['old'], at_tag=['J.helper'])))
            reader = LEDGER.Git(ROOT)
            try:
                with unittest.mock.patch.object(LEDGER.CANDIDATE, 'read_snapshot',
                                                lambda path, fidelity=True: sides[Path(path).name.split('.')[0]]):
                    return LEDGER.mode_b(ledger, reader, 'GX', Path(tmp) / 'before.snapshot.json',
                                         Path(tmp) / 'after.snapshot.json', maps=[map_file])
            finally:
                reader.close()

    def test_receipt_binds_maps_and_verdict(self):
        receipt = self.run_b(1)
        self.assertEqual(receipt['verdict'], 'OK')
        self.assertEqual((receipt['entries'][0]['closure'], receipt['before']['bound'], receipt['after']['bound']),
                         (2, False, False))
        self.assertEqual(len(receipt['entries'][0]['maps']), 1)
        self.assertRegex(receipt['entries'][0]['closure_scope_sha256'], r'^[0-9a-f]{64}$')
        self.assertEqual(self.run_b(2)['verdict'], 'REGRESSION')

    def test_identical_closure_scope_reuses_comparison_and_keeps_both_receipt_rows(self):
        with unittest.mock.patch.object(LEDGER, 'closure_compare', wraps=LEDGER.closure_compare) as compare:
            result = self.run_b(1, repeat_scope=True)
        self.assertEqual(compare.call_count, 2)
        first, second, changed = result['entries']
        self.assertEqual([r['id'] for r in result['entries']], ['GX-1', 'GX-2', 'GX-3'])
        self.assertEqual(dict(first, id='GX-2'), second)
        self.assertEqual(changed['verdict'], 'REGRESSION')
        self.assertNotEqual(changed['closure_scope_sha256'], first['closure_scope_sha256'])


THEOREM = '''import Jaune.Old
/-! theorem Jaune.decoy : True -- inside a comment -/
namespace Jaune
namespace G
theorem foo_bridge : old = old := rfl
end G
end Jaune
'''
OLD = 'namespace Jaune\ndef old : Nat := 1\ndef Old.side : Nat := 1\nend Jaune\n'
NEW = 'namespace Jaune\nsection\nprivate def «new» : Nat := 1\ndef new : Nat := 1\nend\nend Jaune\n'
AUDIT = '''import AxiomAudit
import Jaune.Bridge.G
#expect_axioms Jaune.G.foo_bridge [Classical.choice, Quot.sound, propext]
'''
UNION = 'import AxiomAudit\nimport Jaune\n'
UMBRELLA = 'import Jaune.Bridge.G\nimport Jaune.New\n'


def git(root, *args):
    return subprocess.run(['git', '-C', str(root), *args], check=True, capture_output=True,
                          text=True).stdout.strip()


class ModeATests(unittest.TestCase):
    """Mode A on a synthetic repository: one gate tag, one theorem bridge,
    one map bridge."""

    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.root)
        git(self.root, 'init', '-q')
        git(self.root, 'config', 'user.email', 'fixture@example.invalid')
        git(self.root, 'config', 'user.name', 'fixture')
        self.files = {'Jaune.lean': UMBRELLA, 'Jaune/Bridge/G.lean': THEOREM, 'Jaune/Old.lean': OLD,
                      'Jaune/New.lean': NEW, 'Jaune/Check/GAudit.lean': AUDIT,
                      'scripts/JauneUnionAxioms.lean': UNION, 'scripts/maps/m.json': '{"entries": []}\n'}
        self.old = self.commit()
        self.tag = self.commit({'Jaune/Old.lean': OLD + '-- edited\n'}, tag='gate/gx')
        self.receipts = self.root / 'receipts'
        map_sha = hashlib.sha256(self.files['scripts/maps/m.json'].encode()).hexdigest()
        theorem = dict(
            id='GX-1', gate='GX', kind='theorem', theorem='Jaune.G.foo_bridge', module='Jaune.Bridge.G',
            audit=[dict(kind='expect_axioms', file='Jaune/Check/GAudit.lean'),
                   dict(kind='union_walk', file='scripts/JauneUnionAxioms.lean')],
            old=dict(revision=self.old, roots=['Jaune.old'], modules=['Jaune.Old'], at_tag=['Jaune.Old.side'],
                     modules_at_tag=['Jaune.Old']),
            new=dict(names=['Jaune.new'], modules=['Jaune.New']), exempt=[], maps=[], n4_receipts=[],
            accepted=[dict(decision='fixture', covers='closure', text='no closure run in the fixture')],
            gaps=[], notes=[])
        mapped = dict(
            id='GX-map', gate='GX', kind='map', theorem=None, module=None, audit=[],
            old=dict(revision=self.old, roots=[], modules=[], at_tag=[], modules_at_tag=[]),
            new=dict(names=[], modules=[]), exempt=[],
            maps=[dict(path='scripts/maps/m.json', revision=self.tag, sha256=map_sha)],
            n4_receipts=[dict(map_sha256=map_sha, before_candidate=self.old, after_candidate=self.tag,
                              status='OK', record='fixture')],
            accepted=[], gaps=[], notes=[])
        self.ledger = dict(schema_version=1, standard_axioms=STANDARD,
                           gates=dict(GX=dict(tag='gate/gx', commit=self.tag, status='tagged'),
                                      GY=dict(tag='gate/gy', commit=None, status='pending')),
                           entries=[theorem, mapped])

    def commit(self, changes=None, tag=None):
        self.files.update(changes or {})
        for path, text in self.files.items():
            (self.root / path).parent.mkdir(parents=True, exist_ok=True)
            (self.root / path).write_text(text)
        git(self.root, 'add', '-A')
        git(self.root, 'commit', '-q', '--allow-empty', '-m', 'fixture')
        if tag:
            git(self.root, 'tag', tag)
        return git(self.root, 'rev-parse', 'HEAD')

    def run_a(self, ledger=None, **kwargs):
        reader = LEDGER.Git(self.root)
        try:
            return LEDGER.mode_a(ledger or self.ledger, reader, receipts=self.receipts, **kwargs)
        finally:
            reader.close()

    def assertFinding(self, pattern, ledger=None, **kwargs):
        with self.assertRaisesRegex(LEDGER.Finding, pattern):
            self.run_a(ledger, **kwargs)

    def test_well_formed_ledger_passes(self):
        result = self.run_a()
        self.assertEqual((result['status'], result['entries'], result['gaps']), ('OK', 2, []))

    def test_capture_binding_requires_the_complete_tracked_tree(self):
        candidate = LEDGER.CANDIDATE.inventory(self.root, ['.'])
        reader = LEDGER.Git(self.root)
        self.addCleanup(reader.close)
        self.assertTrue(LEDGER.bound(reader, {'candidate': candidate}, self.tag))
        with self.subTest('omitted tracked path'):
            partial = copy.deepcopy(candidate)
            del partial['files']['scripts/maps/m.json']
            self.assertFalse(LEDGER.bound(reader, {'candidate': partial}, self.tag))
        with self.subTest('untracked path'):
            extra = copy.deepcopy(candidate)
            extra['files']['untracked.txt'] = hashlib.sha256(b'fixture').hexdigest()
            self.assertFalse(LEDGER.bound(reader, {'candidate': extra}, self.tag))
        with self.subTest('changed bytes'):
            changed = copy.deepcopy(candidate)
            changed['files']['Jaune/Old.lean'] = hashlib.sha256(OLD.encode()).hexdigest()
            self.assertFalse(LEDGER.bound(reader, {'candidate': changed}, self.tag))

    def test_renamed_theorem_fails(self):
        self.ledger['entries'][0]['theorem'] = 'Jaune.G.foo_bridgeX'
        self.assertFinding(r'GX-1: Jaune\.G\.foo_bridgeX is not declared in Jaune\.Bridge\.G')

    def test_name_in_a_comment_is_not_a_declaration(self):
        self.ledger['entries'][0]['theorem'] = 'Jaune.decoy'
        self.assertFinding('Jaune.decoy is not declared')

    def test_missing_audit_row_fails(self):
        self.tag = self.commit({'Jaune/Check/GAudit.lean': AUDIT.replace('#expect', '-- #expect')})
        git(self.root, 'tag', '-f', 'gate/gx')
        self.ledger['gates']['GX']['commit'] = self.tag
        self.ledger['entries'][1]['maps'][0]['revision'] = self.tag
        self.assertFinding('no #expect_axioms row for Jaune.G.foo_bridge')
        # The union walk alone still reaches the module; without it no row is present.
        self.ledger['entries'][0]['audit'] = [dict(kind='expect_axioms', file='Jaune/Check/GAudit.lean')]
        self.assertFinding('GX-1: no audit row present')

    def test_union_walk_must_reach_the_module(self):
        self.ledger['entries'][0]['audit'] = [dict(kind='union_walk', file='Jaune/Old.lean')]
        self.assertFinding('does not import Jaune.Bridge.G')

    def test_audit_row_with_nonstandard_axioms_fails(self):
        self.tag = self.commit({'Jaune/Check/GAudit.lean': AUDIT.replace('Quot.sound, ', '')})
        git(self.root, 'tag', '-f', 'gate/gx')
        self.ledger['gates']['GX']['commit'] = self.tag
        self.ledger['entries'][1]['maps'][0]['revision'] = self.tag
        self.assertFinding('not the standard axioms')

    def test_old_side_and_new_side_must_be_declared(self):
        ledger = copy.deepcopy(self.ledger)
        ledger['entries'][0]['old']['roots'] = ['Jaune.Old.side']  # declared at the old revision too
        self.run_a(ledger)
        ledger['entries'][0]['old']['at_tag'] = ['Jaune.gone']
        self.assertFinding('old side at the tag.*Jaune.gone', ledger)
        ledger = copy.deepcopy(self.ledger)
        ledger['entries'][0]['new']['names'] = ['Jaune.newer']
        self.assertFinding('new side.*Jaune.newer', ledger)

    def test_tag_must_resolve_to_the_recorded_commit(self):
        self.ledger['gates']['GX']['commit'] = self.old
        self.assertFinding('gate/gx resolves to')

    def test_map_sha_must_match_and_receipt_must_cite_a_map(self):
        ledger = copy.deepcopy(self.ledger)
        ledger['entries'][1]['maps'][0]['sha256'] = '0' * 64
        self.assertFinding('has sha256', ledger)
        ledger = copy.deepcopy(self.ledger)
        ledger['entries'][1]['n4_receipts'][0]['map_sha256'] = '1' * 64
        self.assertFinding("none of the entry's maps", ledger)

    def test_uncommitted_map_is_an_open_gap(self):
        row = self.ledger['entries'][1]['maps'][0]
        row.update(revision=None, gap='kept with the captures')
        result = self.run_a()
        self.assertEqual(len(result['gaps']), 1)
        self.assertFinding('gate GX not closed', require_closed=['GX'])
        self.assertFinding('gate GY not closed: its tag is pending', require_closed=['GY'])
        del row['gap']
        self.assertFinding('uncommitted with its gap stated')

    def test_exempt_reference_must_resolve(self):
        entry = self.ledger['entries'][0]
        entry['exempt'] = [dict(name='Jaune.Old.side', bridged_by='GX-9')]
        self.assertFinding('needs another ledger entry')
        entry['exempt'] = [dict(name='Jaune.Old.side')]
        self.assertFinding('exempt rows are')
        entry['exempt'] = [dict(name='Jaune.Old.side', bridged_by='GX-map')]
        self.assertFinding('needs a theorem bridge that names it as an old root')
        helper = copy.deepcopy(entry)
        helper.update(id='GX-2', exempt=[])
        self.ledger['entries'].append(helper)
        row = entry['exempt'][0]
        row['bridged_by'] = 'GX-2'
        self.assertFinding('needs a theorem bridge that names it as an old root')
        helper['old']['roots'] = ['Jaune.Old.side']
        row['replacement'] = 'Jaune.unrelated'
        self.assertFinding('replacement Jaune.unrelated is not named by bridge GX-2')
        row['replacement'] = 'Jaune.new'
        self.assertEqual(self.run_a()['status'], 'OK')

    def test_missing_closure_receipt_is_a_gap_and_a_receipt_is_checked(self):
        theorem = self.ledger['entries'][0]
        theorem['accepted'] = []
        self.assertEqual(self.run_a()['gaps'], ['entry GX-1: no Mode B closure receipt (GX.json)'])
        self.receipts.mkdir()
        row = dict(id='GX-1', maps=[], roots=['Jaune.old'], old_revision=self.old,
                   verdict='OK', mismatches=[], closure_scope_sha256=LEDGER.closure_scope_sha256(theorem))
        receipt = dict(schema_version=1, gate='GX', verdict='OK', tag_commit=self.tag,
                       before=dict(bound=True, head=self.old), after=dict(bound=True, head=self.tag),
                       entries=[row])
        path = self.receipts / 'GX.json'
        path.write_text(json.dumps(receipt))
        self.assertEqual(self.run_a()['gaps'], [])
        theorem['notes'].append('Clarify the prose without changing the comparison.')
        self.assertEqual(self.run_a()['gaps'], [])
        for change in (dict(verdict='REGRESSION'), dict(tag_commit=self.old), dict(after=dict(bound=False)),
                       dict(before=dict(bound=True, head=self.tag)), dict(after=dict(bound=True, head=self.old)),
                       dict(entries=[row, row]), dict(entries=[dict(row, verdict='REGRESSION')]),
                       dict(entries=[dict(row, maps=['x'])])):
            path.write_text(json.dumps(dict(receipt, **change)))
            self.assertFinding('receipt GX')
        path.write_text(json.dumps(receipt))
        helper = copy.deepcopy(theorem)
        helper.update(id='GY-1', gate='GY', accepted=[dict(decision='fixture', covers='closure', text='fixture')])
        helper['old']['roots'] = ['Jaune.Old.side']
        self.ledger['entries'].append(helper)
        theorem['exempt'] = [dict(name='Jaune.Old.side', bridged_by='GY-1')]
        self.assertFinding('closure scope differs')
        theorem['exempt'] = []
        theorem['old'].update(at_tag=['Jaune.new'], modules_at_tag=['Jaune.New'])
        self.assertFinding('closure scope differs')

    def test_pending_gate_reads_head(self):
        entry = copy.deepcopy(self.ledger['entries'][0])
        entry.update(id='GY-1', gate='GY')
        self.ledger['entries'].append(entry)
        self.assertEqual(self.run_a()['status'], 'OK')
        self.ledger['entries'][-1]['theorem'] = 'Jaune.G.missing'
        self.assertFinding('GY-1: Jaune.G.missing is not declared')


class ScannerTests(unittest.TestCase):
    def test_declarations_namespaces_and_blanked_text(self):
        source = ('namespace A.B\n@[simp] protected theorem t : True := trivial\nsection S\n'
                  'def _root_.top := 1\nend S\nend A.B\n'
                  'def s := "theorem fake : True"\n/- def c := 1 /- nested -/ def d := 2 -/\ndef e := 3\n')
        self.assertEqual(LEDGER.declared_names(source), {'A.B.t', 'top', 's', 'e'})

    def test_real_ledger_is_well_formed(self):
        self.assertEqual(LEDGER.validate(json.loads((ROOT / 'scripts/bridge-ledger.json').read_bytes())), [])


if __name__ == '__main__':
    unittest.main()
