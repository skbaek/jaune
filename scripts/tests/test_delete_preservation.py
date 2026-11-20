"""The delete-preservation check (goal jaune-shape-and-names-v1, X1; the U7 delete).

Synthetic compiler exports in capture-shaped snapshots; each defect is planted
alone on a delete that otherwise passes."""
import contextlib
import copy
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
import unittest.mock

ROOT = Path(__file__).parents[2]
SPEC = importlib.util.spec_from_file_location('check_delete_preservation',
                                              ROOT / 'scripts/check-delete-preservation.py')
CHECK = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CHECK)
FIDELITY = CHECK.FIDELITY


def c(name):
    return ['const', ['name', name], []]


def app(f, *xs):
    for x in xs:
        f = ['app', f, x]
    return f


def definition(value, type_=None, **attributes):
    return dict(kernel=dict(type=type_ or c('Nat'), universes=0, payload=['definition', value]),
                attributes=attributes, equation_origin=None)


def theorem(type_, **attributes):
    return dict(kernel=dict(type=type_, universes=0, payload=['theorem']), attributes=attributes,
                equation_origin=None)


def guard(expr):
    return ['guardBool', expr]


def module(imports, *items):
    """Items in source order: ('def' | 'inst' | 'gen', name, record),
    ('guard', expression), ('check', [names]) or ('attr', name)."""
    return dict(imports=list(imports), items=[list(item) for item in items])


def drop(tree, mod, *names):
    tree[mod]['items'] = [item for item in tree[mod]['items'] if item[1] not in names]


def put(tree, mod, name, record):
    for item in tree[mod]['items']:
        if item[1] == name:
            item[2] = record
            return
    raise KeyError(name)


def export(name, spec):
    """One module's export as the capture writes it (schema 6 keeps kernel
    terms inline; the reader gives the comparator the same bundle)."""
    lines, decls, constants, guards, checks, attributes, commands = [], {}, {}, [], [], [], []
    offset = 0
    for item in spec['items']:
        kind, row = item[0], len(lines)
        if kind == 'gen':
            constants[item[1]] = item[2]
            continue
        if kind == 'def':
            user = CHECK.user_name(item[1])
            text = f'def {user} := 0'
            decls[item[1]] = [row, 0, row, len(text), row, 4, row, 4 + len(user)]
            constants[item[1]] = item[2]
        elif kind == 'inst':
            text = 'instance : C := 0'
            decls[item[1]] = [row, 0, row, len(text), row, 0, row, 8]
            constants[item[1]] = item[2]
        elif kind == 'guard':
            text = f'#guard g{row}'
            guards.append(item[1])
        elif kind == 'check':
            text = '#expect_axioms ' + ' '.join(item[1])
            checks.append(dict(syntax=['syntax', 'cmd', [['atom', '#expect_axioms']] +
                                       [['ident', n, 0, 0] for n in item[1]]],
                               literal_names=True, start=offset, end=offset + len(text),
                               expected_failure_scope=False))
        elif kind == 'attr':
            text = f'attribute [simp] {item[1]}'
            attributes.append(['attributeCommand', [], [['atom', 'attribute'], ['atom', 'simp'], ['name', item[1]]]])
        else:
            raise ValueError(kind)
        commands.append([offset, offset + len(text), 'fixture'])
        lines.append(text)
        offset += len(text) + 1
    source = ''.join(line + '\n' for line in lines)
    index = dict(version=5, module=name, directImports=[[i, False, False, False] for i in spec['imports']],
                 references={}, decls=decls,
                 naming_syntax=dict(commands=commands, from_olean=bool(spec.get('from_olean', False))))
    return dict(schema_version=6, lean_version='fixture', source=source, index=index, constants=constants,
                guards=guards, attribute_syntax=attributes, checked_commands=checks, imports={})


def snapshot(tree, directory, head='0' * 40):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=True)
    modules, exports, paths = {}, {}, {}
    for name, spec in tree.items():
        data = export(name, spec)
        path = directory / f'{name}.export.json'
        path.write_text(json.dumps(data))
        modules[name] = dict(path=f'{name}.lean', sha256=hashlib.sha256(data['source'].encode()).hexdigest(),
                             imports=list(spec['imports']), is_module=False)
        exports[name] = dict(path=path.name, sha256=hashlib.sha256(path.read_bytes()).hexdigest())
        paths[name] = path
    imported = {i for row in modules.values() for i in row['imports']}
    roots = sorted(set(modules) - imported)
    return dict(candidate=dict(head=head, files={row['path']: row['sha256'] for row in modules.values()},
                               modules=modules, source_dirs=['.']),
                tool_sources={}, artifacts={}, roots=roots, selected=CHECK.CANDIDATE.closure(modules, roots),
                source_only=[], exports=exports, export_paths=paths, metas={})


NAT = c('Nat')
DEVM = c('J.Devm')
KEEP_GUARD = guard(app(c('Nat.beq'), c('J.keep'), ['lit', 1]))
OLD_GUARD = guard(app(c('Nat.beq'), app(c('J.oldRun'), c('J.Devm.init')), ['lit', 2]))


def base():
    """`Old` is the old side; `Mixed` holds old and kept declarations;
    `Down` only uses kept ones."""
    return {
        'Old': module(
            [],
            ('def', 'J.Devm', definition(['sort', 1], ['sort', 2])),
            ('def', 'J.Devm.init', definition(['lit', 0], DEVM)),
            ('gen', 'J.instReprDevm', definition(app(c('Repr.mk'), DEVM), app(c('Repr'), DEVM), instance=1000)),
            ('gen', 'J.instReprDevm.repr', definition(['lit', 9], ['forall', DEVM, NAT]))),
        'Mixed': module(
            ['Old'],
            ('def', 'J.keep', definition(app(c('J.keep.match_1'), ['lit', 1]))),
            ('gen', 'J.keep.match_1', definition(['lam', NAT, ['bvar', 0]])),
            ('def', 'J.keepThm', theorem(app(c('Eq'), c('J.keep'), ['lit', 1]))),
            ('def', 'J.simpLemma', theorem(app(c('Eq'), c('J.keep'), c('J.keep')), simp=['default'])),
            ('def', 'J.Checked.run', definition(['lit', 5])),
            ('def', 'J.oldRun', definition(app(c('J.oldRun.match_1'), ['lit', 2]), ['forall', DEVM, NAT])),
            ('gen', 'J.oldRun.match_1', definition(['lam', DEVM, ['lit', 2]])),
            ('def', 'J.oldRun_spec', theorem(app(c('Eq'), app(c('J.oldRun'), c('J.Devm.init')), ['lit', 2]))),
            ('guard', KEEP_GUARD),
            ('guard', OLD_GUARD),
            ('check', ['J.keepThm']),
            ('check', ['J.oldRun_spec'])),
        'Down': module(
            ['Mixed'],
            ('def', 'J.user', definition(app(c('Nat.succ'), c('J.keep'))))),
    }


def deleted(tree):
    """The delete: `Old` goes, and so do the old declarations of `Mixed`."""
    tree = copy.deepcopy(tree)
    del tree['Old']
    tree['Mixed']['imports'] = []
    drop(tree, 'Mixed', 'J.oldRun', 'J.oldRun.match_1', 'J.oldRun_spec', OLD_GUARD, ['J.oldRun_spec'])
    return tree


CLASSIFICATION = dict(schema_version=1, old_side=dict(constants=['J.Devm'], namespaces=[]),
                      replaced=[], retired=[], rewritten=[], added=[], matcher_reducibility=[])
SEMI, INSTANCE = 'Lean.ReducibilityStatus.semireducible', 'Lean.ReducibilityStatus.instanceReducible'


def old_guard_digest():
    return FIDELITY.dag_digest(OLD_GUARD)


LEDGER = dict(schema_version=1, added=[],
              deleted=[dict(module='Mixed', kind='guard', digest=old_guard_digest(),
                            disposition='deleted-with-old-side', reason='observes J.oldRun')])


class DeleteTests(unittest.TestCase):
    def setUp(self):
        self.before, self.after = base(), deleted(base())
        self.classification, self.ledger, self.map = copy.deepcopy(CLASSIFICATION), copy.deepcopy(LEDGER), None
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)

    def run_check(self):
        self.runs = getattr(self, 'runs', 0) + 1
        root = Path(self.tmp.name) / str(self.runs)
        return CHECK.check(snapshot(self.before, root / 'before'), snapshot(self.after, root / 'after'),
                           self.classification, self.ledger, self.map)

    def assertOK(self):
        result = self.run_check()
        self.assertEqual((result['verdict'], result['problems']), ('OK', []))
        return result

    def assertFinding(self, pattern):
        result = self.run_check()
        self.assertEqual(result['verdict'], 'REGRESSION')
        self.assertRegex('\n'.join(result['problems']), pattern)
        return result

    # ---- the passing delete and what it reports

    def test_clean_delete_passes_and_lists_the_deleted_set_by_module(self):
        result = self.assertOK()
        self.assertEqual(result['modules']['deleted'], ['Old'])
        self.assertEqual({m: [(e['name'], e['origin'], e['class']) for e in rows]
                          for m, rows in result['deleted'].items()},
                         {'Mixed': [('J.oldRun', 'authored', 'old-side'), ('J.oldRun_spec', 'authored', 'old-side')],
                          'Old': [('J.Devm', 'authored', 'old-side'), ('J.Devm.init', 'authored', 'old-side'),
                                  ('J.instReprDevm', 'generated', 'old-side')]})
        by_name = {e['name']: e for rows in result['deleted'].values() for e in rows}
        self.assertEqual(by_name['J.Devm']['via'], ['listed: J.Devm'])
        self.assertEqual(by_name['J.oldRun_spec']['via'], ['J.Devm.init', 'J.Devm', 'listed: J.Devm'])
        self.assertEqual((by_name['J.oldRun']['generated'], by_name['J.instReprDevm']['generated']), (1, 1))
        self.assertEqual(by_name['J.oldRun']['line'], 5)
        self.assertEqual(result['totals']['kept_authored'], 5)
        self.assertEqual(result['totals']['kept_guards'], 1)
        self.assertEqual(result['modules']['identical_exports'], 1)
        self.assertEqual(result['import_changes'], {'Mixed': dict(removed=['Old'], added=[])})
        self.assertEqual(result['deleted_checks_naming_deleted_declarations'], {'check': 1})
        guards = [row for row in result['deleted_checks'] if row['kind'] == 'guard']
        self.assertEqual([(g['line'], g['source'], g['accounted']) for g in guards], [(8, '#guard g7', 'ledger')])

    def test_identity_passes_with_and_without_the_fast_path(self):
        self.after = base()
        self.classification, self.ledger = None, None
        result = self.assertOK()
        self.assertEqual((result['modules']['identical_exports'], result['deleted_declarations']), (3, 0))
        root = Path(self.tmp.name) / 'slow'
        result = CHECK.check(snapshot(self.before, root / 'b'), snapshot(self.after, root / 'a'), fast_path=False)
        self.assertEqual((result['verdict'], result['modules']['compared'], result['totals']['kept_authored']),
                         ('OK', 3, 9))

    # ---- the four controls of the brief

    def test_control_i_changed_body_of_a_kept_definition_fails(self):
        put(self.after, 'Mixed', 'J.Checked.run', definition(['lit', 6]))
        self.assertFinding(r'\[Mixed\] kept constant J\.Checked\.run changed: .*payload.*5 became 6')

    def test_control_ii_kept_theorem_dropped_without_classification_fails(self):
        drop(self.after, 'Mixed', 'J.keepThm', ['J.keepThm'])
        result = self.assertFinding(r'\[Mixed\] deleted theorem J\.keepThm is unclassified')
        self.assertEqual(result['unclassified'],
                         [dict(module='Mixed', name='J.keepThm', kind='theorem', line=2, reason='')])
        # Its audit row names it, so that row is accounted for; the theorem is not.
        self.assertEqual(len(result['problems']), 1)

    def test_control_iii_dropped_simp_on_a_kept_constant_fails(self):
        put(self.after, 'Mixed', 'J.simpLemma', theorem(app(c('Eq'), c('J.keep'), c('J.keep'))))
        self.assertFinding(r'kept constant J\.simpLemma changed: .*attributes')

    def test_control_iv_dropped_kept_guard_fails(self):
        drop(self.after, 'Mixed', KEEP_GUARD)
        result = self.assertFinding(r'\[Mixed\] deleted guard [0-9a-f]{16} is not in the guard ledger: #guard g6')
        self.assertEqual([(r['kind'], r['line']) for r in result['unledgered']['deleted']], [('guard', 7)])

    # ---- kept constants

    def test_changed_type_of_a_kept_theorem_fails(self):
        put(self.after, 'Mixed', 'J.keepThm', theorem(app(c('Eq'), c('J.keep'), ['lit', 2])))
        self.assertFinding(r'kept constant J\.keepThm changed: .*kernel\.type')

    def test_changed_guard_expression_fails_as_deleted_and_added(self):
        drop(self.after, 'Mixed', KEEP_GUARD)
        self.after['Mixed']['items'].append(['guard', guard(app(c('Nat.beq'), c('J.keep'), ['lit', 7]))])
        result = self.assertFinding(r'added \(or changed\) guard')
        self.assertEqual({k: len(v) for k, v in result['unledgered'].items()}, dict(deleted=1, added=1))

    def test_kept_constant_moved_to_another_module_fails(self):
        moved = [item for item in self.after['Mixed']['items'] if item[1] == 'J.Checked.run']
        drop(self.after, 'Mixed', 'J.Checked.run')
        self.after['Down']['items'] += moved
        result = self.assertFinding(r'\[Down\] authored constant J\.Checked\.run exists only after the delete')
        self.assertRegex('\n'.join(result['problems']), r'\[Mixed\] deleted definition J\.Checked\.run is unclassified')

    def test_added_declaration_needs_a_row(self):
        self.after['Mixed']['items'].append(['def', 'J.fresh', definition(['lit', 3])])
        self.assertFinding(r'authored constant J\.fresh exists only after the delete')
        self.classification['added'] = [dict(module='Mixed', name='J.fresh', reason='native helper')]
        self.assertOK()

    def test_rewritten_value_needs_a_row_and_keeps_its_type(self):
        put(self.after, 'Mixed', 'J.Checked.run', definition(app(c('Nat.succ'), ['lit', 4])))
        self.assertFinding(r'kept constant J\.Checked\.run changed')
        self.classification['rewritten'] = [dict(module='Mixed', name='J.Checked.run', reason='native body')]
        self.assertOK()
        put(self.after, 'Mixed', 'J.Checked.run', definition(['lit', 5], c('Int')))
        self.assertFinding(r'rewritten constant J\.Checked\.run: .*kernel\.type')
        put(self.after, 'Mixed', 'J.Checked.run', theorem(NAT))
        self.assertFinding(r"rewritten constant J\.Checked\.run: .*'definition' became 'theorem'")

    # ---- generated constants

    def test_kept_declaration_that_reused_a_deleted_matcher_gets_its_own(self):
        # Before, `J.keep` reused the matcher the earlier old declaration made.
        put(self.before, 'Mixed', 'J.oldRun', definition(app(c('J.oldRun.match_1'), ['lit', 2]),
                                                           ['forall', DEVM, NAT]))
        put(self.before, 'Mixed', 'J.oldRun.match_1', definition(['lam', NAT, ['bvar', 0]]))
        put(self.before, 'Mixed', 'J.keep', definition(app(c('J.oldRun.match_1'), ['lit', 1])))
        drop(self.before, 'Mixed', 'J.keep.match_1')
        result = self.assertOK()
        self.assertEqual(result['renamed_generated'], {'J.oldRun.match_1': 'J.keep.match_1'})
        put(self.after, 'Mixed', 'J.keep.match_1', definition(['lam', NAT, ['lit', 0]]))
        self.assertFinding(r'kept constant J\.keep changed')

    def test_renamed_generated_constant_must_reach_its_users(self):
        put(self.before, 'Mixed', 'J.oldRun.match_1', definition(['lam', NAT, ['bvar', 0]]))
        put(self.before, 'Mixed', 'J.keep', definition(app(c('J.oldRun.match_1'), ['lit', 1])))
        drop(self.before, 'Mixed', 'J.keep.match_1')
        # A downstream export that still names the old matcher is unchanged
        # bytes with a changed meaning.
        for tree in (self.before, self.after):
            put(tree, 'Down', 'J.user', definition(app(c('J.oldRun.match_1'), c('J.keep'))))
        self.assertFinding(r'\[Down\] unchanged export names generated constant J\.oldRun\.match_1, '
                           r'which is J\.keep\.match_1 after the delete')
        put(self.after, 'Down', 'J.user', definition(app(c('J.keep.match_1'), c('J.keep'))))
        self.assertOK()
        put(self.after, 'Down', 'J.user', definition(app(c('J.other.match_1'), c('J.keep'))))
        self.assertFinding(r'\[Down\] kept constant J\.user changed: .*J\.oldRun\.match_1 became J\.other\.match_1')

    def reuse_private_matcher(self):
        """Before, the public `J.keep` reused the matcher of an earlier private
        old declaration; after, it has its own, which Lean makes
        instance-reducible where the private one was semireducible."""
        old, matcher = '_private.Mixed.0.J.oldRun', '_private.Mixed.0.J.oldRun.match_1'
        body = ['lam', NAT, ['bvar', 0]]
        drop(self.before, 'Mixed', 'J.oldRun', 'J.oldRun.match_1', 'J.oldRun_spec', 'J.keep.match_1',
             OLD_GUARD, ['J.oldRun_spec'])
        items = self.before['Mixed']['items']
        items.insert(0, ['gen', matcher, definition(body, reducibility=SEMI)])
        items.insert(0, ['def', old, definition(app(c(matcher), ['lit', 2]), ['forall', DEVM, NAT])])
        put(self.before, 'Mixed', 'J.keep', definition(app(c(matcher), ['lit', 1])))
        put(self.after, 'Mixed', 'J.keep.match_1', definition(body, reducibility=INSTANCE))
        self.ledger = None
        return matcher

    def test_matcher_reducibility_follows_the_new_owners_visibility_only_with_a_row(self):
        matcher = self.reuse_private_matcher()
        result = self.assertFinding(r'\[Mixed\] matcher _private\.Mixed\.0\.J\.oldRun\.match_1 is J\.keep\.match_1 '
                                    r'after the delete.*needs a matcher_reducibility row')
        self.assertEqual(len(result['problems']), 1)
        row = dict(module='Mixed', name=matcher, after='J.keep.match_1', reason='')
        self.assertEqual(result['unacknowledged_matcher_reducibility'], [row])
        self.classification['matcher_reducibility'] = [dict(row, reason='the old declaration was private')]
        self.assertOK()
        self.classification['matcher_reducibility'] = [dict(row, after='J.other.match_1', reason='x')]
        self.assertFinding(r'needs a matcher_reducibility row')

    def test_matcher_reducibility_row_admits_no_other_difference(self):
        matcher = self.reuse_private_matcher()
        self.classification['matcher_reducibility'] = [dict(module='Mixed', name=matcher, after='J.keep.match_1',
                                                            reason='the old declaration was private')]
        body = ['lam', NAT, ['bvar', 0]]
        put(self.after, 'Mixed', 'J.keep.match_1', definition(body, reducibility=INSTANCE, inline='inline'))
        self.assertFinding(r'kept constant J\.keep changed: .*attributes')
        put(self.after, 'Mixed', 'J.keep.match_1', definition(['lam', NAT, ['lit', 0]], reducibility=INSTANCE))
        self.assertFinding(r'kept constant J\.keep changed: .*payload')
        # The same visibility on both sides: the reducibility is a change.
        put(self.after, 'Mixed', 'J.keep.match_1', definition(body, reducibility=INSTANCE))
        put(self.before, 'Mixed', matcher, definition(body, reducibility='Lean.ReducibilityStatus.reducible'))
        self.assertFinding(r'kept constant J\.keep changed: .*reducibility')

    def test_unreferenced_matcher_of_the_other_visibility_is_found_by_graph(self):
        # A kept theorem's proof made the matcher (proofs are not exported).
        matcher = self.reuse_private_matcher()
        put(self.before, 'Mixed', 'J.keep', definition(['lit', 1]))
        put(self.after, 'Mixed', 'J.keep', definition(['lit', 1]))
        self.assertFinding(r'needs a matcher_reducibility row')
        self.classification['matcher_reducibility'] = [dict(module='Mixed', name=matcher, after='J.keep.match_1',
                                                            reason='the old declaration was private')]
        self.assertOK()

    def test_generated_constant_of_a_kept_declaration_cannot_vanish(self):
        self.before['Mixed']['items'].append(['gen', 'J.keepThm.match_1', definition(['lit', 8])])
        self.assertFinding(r'generated constant J\.keepThm\.match_1 of kept declaration J\.keepThm disappeared')
        self.after['Mixed']['items'].append(['gen', 'J.keepThm.match_2', definition(['lit', 8])])
        self.assertOK()  # Renumbered, the same graph.
        put(self.after, 'Mixed', 'J.keepThm.match_2', definition(['lit', 7]))
        self.assertFinding(r'generated constant J\.keepThm\.match_2 has no counterpart before the delete')

    def test_on_demand_auxiliary_may_vanish_with_its_last_user(self):
        self.before['Mixed']['items'].append(
            ['gen', 'J.keep.match_1.splitter', definition(['lam', NAT, ['lit', 1]], inline='inline')])
        result = self.assertOK()
        self.assertEqual(result['totals']['vanished_on_demand'], 1)

    def test_on_demand_auxiliary_realized_in_another_module_is_compared_with_the_old_copy(self):
        # Before, the deleted module realized the equation and `Down` used it.
        equation = theorem(app(c('Eq'), c('J.keep'), ['lit', 1]))
        self.before['Old']['items'].append(['gen', 'J.keep.eq_1', equation])
        for tree in (self.before, self.after):
            put(tree, 'Down', 'J.user', definition(app(c('J.keep.eq_1'), c('J.keep'))))
        self.after['Down']['items'].append(['gen', 'J.keep.eq_1', copy.deepcopy(equation)])
        result = self.assertOK()
        self.assertEqual(result['rehomed_generated'], {'J.keep.eq_1': dict(module='Down', before_module='Old')})
        put(self.after, 'Down', 'J.keep.eq_1', theorem(app(c('Eq'), c('J.keep'), ['lit', 2])))
        self.assertFinding(r'\[Down\] kept constant J\.user changed: .*J\.keep\.eq_1')

    def test_auxiliaries_of_anonymous_commands_vanish_with_their_guard(self):
        self.before['Mixed']['items'].append(['gen', '_private.Mixed.0.match_1', definition(['lam', DEVM, NAT])])
        result = self.assertOK()
        self.assertEqual(result['totals']['vanished_anonymous'], 1)

    def test_anonymous_instance_is_a_deleted_declaration(self):
        instance = definition(app(c('Inhabited.mk'), c('J.keep')), app(c('Inhabited'), NAT), instance=1000)
        self.before['Mixed']['items'].append(['inst', 'J.instInhabitedNat', instance])
        result = self.assertFinding(r'deleted definition \(instance\) J\.instInhabitedNat is unclassified')
        self.assertEqual([e['origin'] for e in result['deleted']['Mixed'] if e['name'] == 'J.instInhabitedNat'],
                         ['declared'])
        self.after['Mixed']['items'].append(['inst', 'J.instInhabitedNat', copy.deepcopy(instance)])
        self.assertOK()

    def test_derived_instance_of_a_kept_type_cannot_be_dropped_silently(self):
        derived = definition(app(c('Repr.mk'), c('J.keep')), app(c('Repr'), c('J.keep')), instance=1000)
        self.before['Mixed']['items'].append(['gen', 'J.instReprKeep', derived])
        self.assertFinding(r'deleted definition \(instance\) J\.instReprKeep is unclassified')

    # ---- classification

    def test_old_side_is_decided_from_kernel_references_not_from_names(self):
        # Named like the old side, referring to none of it.
        for tree in (self.before,):
            tree['Mixed']['items'].append(['def', 'J.Devm_helper', definition(['lit', 1])])
        self.assertFinding(r'deleted definition J\.Devm_helper is unclassified')

    def test_theorem_is_old_side_by_its_statement_only(self):
        # The statement is over kept constants; only an auxiliary of its
        # proof mentions the old side.
        self.before['Mixed']['items'] += [
            ['def', 'J.newFact', theorem(app(c('Eq'), c('J.keep'), c('J.keep')))],
            ['gen', 'J.newFact._proof_1', theorem(app(c('Eq'), c('J.Devm.init'), c('J.Devm.init')))]]
        self.assertFinding(r'deleted theorem J\.newFact is unclassified')
        self.classification['retired'] = [dict(module='Mixed', name='J.newFact', reason='restated as J.keepThm')]
        result = self.assertOK()
        self.assertEqual(result['classes'], {'old-side': 5, 'retired': 1})

    def test_definition_is_old_side_through_its_own_auxiliaries(self):
        self.before['Mixed']['items'] += [
            ['def', 'J.viaMatcher', definition(app(c('J.viaMatcher.match_1'), ['lit', 1]))],
            ['gen', 'J.viaMatcher.match_1', definition(['lam', DEVM, ['lit', 1]])]]
        result = self.assertOK()
        entry = [e for e in result['deleted']['Mixed'] if e['name'] == 'J.viaMatcher'][0]
        self.assertEqual((entry['class'], entry['via']), ('old-side', ['J.Devm', 'listed: J.Devm']))

    def test_replaced_and_retired_rows(self):
        self.before['Mixed']['items'] += [['def', 'J.generic', definition(['lit', 1])],
                                         ['def', 'J.generic_spec', theorem(app(c('Eq'), c('J.generic'), ['lit', 1]))]]
        self.assertFinding(r'J\.generic is unclassified(.|\n)*J\.generic_spec is unclassified')
        self.classification['replaced'] = [dict(module='Mixed', name='J.generic', by='J.Checked.run',
                                                with_dependents=True)]
        result = self.assertOK()
        classes = {e['name']: e['class'] for e in result['deleted']['Mixed']}
        self.assertEqual((classes['J.generic'], classes['J.generic_spec']), ('replaced', 'replaced (dependent)'))
        self.classification['replaced'][0]['with_dependents'] = False
        self.assertFinding(r'J\.generic_spec is unclassified')
        self.classification['replaced'][0].update(by='J.Checked.missing', with_dependents=True)
        self.assertFinding(r'J\.generic of Mixed is replaced by J\.Checked\.missing, which does not exist')

    def test_stale_rows_fail(self):
        self.classification['retired'] = [dict(module='Mixed', name='J.keep', reason='not deleted')]
        self.assertFinding(r'classification: stale retired row J\.keep of Mixed')
        self.classification['retired'] = []
        self.classification['rewritten'] = [dict(module='Mixed', name='J.nowhere', reason='x')]
        self.assertFinding(r'classification: stale rewritten row J\.nowhere of Mixed')

    def test_old_side_lists_must_name_deleted_declarations(self):
        self.classification['old_side']['constants'].append('J.keep')
        self.assertFinding(r'old-side constant J\.keep still exists after the delete')
        self.classification['old_side']['constants'][-1] = 'J.Nowhere'
        self.assertFinding(r'old-side constant J\.Nowhere is not a deleted declaration')
        self.classification['old_side'] = dict(constants=['J.Devm'], namespaces=['J.Staging'])
        self.assertFinding(r'old-side namespace J\.Staging holds no deleted declaration')

    def test_old_side_namespace_covers_its_deleted_members(self):
        self.before['Mixed']['items'].append(['def', 'J.Staging.thing', definition(['lit', 1])])
        self.before['Mixed']['items'].append(['def', 'J.usesStaging', definition(c('J.Staging.thing'))])
        self.classification['old_side']['namespaces'] = ['J.Staging']
        result = self.assertOK()
        via = {e['name']: e['via'] for e in result['deleted']['Mixed'] if e['name'].startswith('J.S') or
               e['name'] == 'J.usesStaging'}
        self.assertEqual(via, {'J.Staging.thing': ['listed: J.Staging.*'],
                               'J.usesStaging': ['J.Staging.thing', 'listed: J.Staging.*']})

    def test_private_declaration_made_public_needs_the_map(self):
        private = '_private.Mixed.0.J.secret'
        self.before['Mixed']['items'].append(['def', private, definition(['lit', 4])])
        self.after['Mixed']['items'].append(['def', 'J.secret', definition(['lit', 4])])
        self.assertFinding(r'authored constant J\.secret exists only after the delete')
        row = dict(old='J.secret', new='J.secret', kind='declaration', layer='execution', rule='4',
                   source='fixture', public_from=private)
        self.map = dict(schema_version=1, retired_tokens=[], allowed_abbreviations=[], entries=[row])
        self.assertOK()
        self.map['entries'] = [dict(row, new='J.renamed')]
        with self.assertRaisesRegex(ValueError, 'only a `public_from` declaration row'):
            self.run_check()

    # ---- the guard ledger

    def test_guard_ledger_rows_are_exact(self):
        self.ledger['deleted'] = []
        self.assertFinding(r'deleted guard [0-9a-f]{16} is not in the guard ledger')
        self.ledger = copy.deepcopy(LEDGER)
        self.ledger['deleted'].append(dict(module='Mixed', kind='guard', digest='0' * 64,
                                           disposition='retired', reason='none'))
        self.assertFinding(r'guard ledger: stale deleted row \(1x\) guard 0000000000000000 of Mixed')
        self.ledger = copy.deepcopy(LEDGER)
        self.ledger['deleted'][0]['count'] = 2
        self.assertFinding(r'guard ledger: stale deleted row \(1x\)')

    def test_deleted_check_that_names_only_kept_declarations_needs_the_ledger(self):
        drop(self.after, 'Mixed', ['J.keepThm'])
        result = self.assertFinding(r'deleted check [0-9a-f]{16} is not in the guard ledger: #expect_axioms J\.keepThm')
        row = result['unledgered']['deleted'][0]
        self.ledger['deleted'].append(dict(module='Mixed', kind='check', digest=row['digest'],
                                           disposition='restated', replacement='the union audit'))
        self.assertOK()

    def test_added_check_needs_an_added_row(self):
        self.after['Mixed']['items'].append(['check', ['J.keep']])
        result = self.assertFinding(r'added \(or changed\) check')
        self.ledger['added'] = [dict(module='Mixed', kind='check', digest=result['unledgered']['added'][0]['digest'],
                                     reason='registration')]
        self.assertOK()

    def test_attribute_command_on_a_kept_constant_cannot_be_dropped(self):
        self.before['Mixed']['items'].append(['attr', 'J.keep'])
        self.assertFinding(r'deleted attribute [0-9a-f]{16} is not in the guard ledger: attribute simp J\.keep')
        self.before['Mixed']['items'][-1] = ['attr', 'J.oldRun']
        self.assertOK()

    # ---- inputs

    def test_export_mode_must_match(self):
        self.after['Mixed']['from_olean'] = True
        with self.assertRaisesRegex(ValueError, 'export mode mismatch for Mixed'):
            self.run_check()

    def snapshots(self):
        self.runs = getattr(self, 'runs', 0) + 1
        root = Path(self.tmp.name) / str(self.runs)
        return snapshot(self.before, root / 'before'), snapshot(self.after, root / 'after')

    def test_captures_must_share_tools_configuration_and_external_artifacts(self):
        parts = lambda digest: {part: dict(path=part, sha256=digest) for part in CHECK.CANDIDATE.PARTS}
        before, after = self.snapshots()
        before['artifacts'] = {'Init': parts('1'), 'Std': parts('2'), 'Old': parts('3')}
        after['artifacts'] = {'Init': parts('1')}
        result = CHECK.check(before, after, self.classification, self.ledger)
        # A delete may import fewer external modules; `Old` was a local module.
        self.assertEqual((result['verdict'], result['external_artifacts']), ('OK', dict(only_before=1, only_after=[])))
        after['artifacts'] = {'Init': parts('9')}
        with self.assertRaisesRegex(ValueError, r"external import artifacts changed: \['Init'\]"):
            CHECK.check(before, after, self.classification, self.ledger)
        after['artifacts'] = {'Init': parts('1'), 'Old': parts('3')}
        with self.assertRaisesRegex(ValueError, r"imports artifacts of modules without a source: \['Old'\]"):
            CHECK.check(before, after, self.classification, self.ledger)
        before, after = self.snapshots()
        after['tool_sources'] = {'scripts/NamingFidelity.lean': 'changed'}
        with self.assertRaisesRegex(ValueError, 'capture implementation changed'):
            CHECK.check(before, after, self.classification, self.ledger)
        before, after = self.snapshots()
        after['candidate']['files']['lakefile.lean'] = 'changed'
        with self.assertRaisesRegex(ValueError, 'build/dependency configuration changed: lakefile.lean'):
            CHECK.check(before, after, self.classification, self.ledger)

    def test_every_changed_source_and_its_importers_must_be_exported(self):
        before, after = self.snapshots()
        for side in (before, after):
            side['candidate']['modules']['Pilot'] = dict(path='Pilot.lean', sha256='p', imports=['Mixed'],
                                                         is_module=False)
            side['candidate']['files'].update({'Pilot.lean': 'p', 'scripts/naming-inventory.json': 'i'})
        with self.assertRaisesRegex(ValueError, r"affected importers outside exports: \['Pilot'\]"):
            CHECK.check(before, after, self.classification, self.ledger)
        # A registered exclusion whose bytes are unchanged is accounted for.
        raw = json.dumps(dict(excluded_sources=[dict(path='Pilot.lean', sha256='p')])).encode()
        for side in (before, after):
            side['candidate']['files']['scripts/naming-inventory.json'] = hashlib.sha256(raw).hexdigest()
        result = CHECK.check(before, after, self.classification, self.ledger, inventory=(raw, json.loads(raw)))
        self.assertEqual(result['verdict'], 'OK')
        after['candidate']['files']['Pilot.lean'] = 'q'
        with self.assertRaisesRegex(ValueError, r"changed Lean sources outside exports: \['Pilot.lean'\]"):
            CHECK.check(before, after, self.classification, self.ledger, inventory=(raw, json.loads(raw)))

    def test_input_files_are_validated(self):
        for field, value, pattern in (
                ('retired', [dict(module='Mixed', name='J.x')], "missing non-empty 'reason'"),
                ('replaced', [dict(module='Mixed', name='J.x', by='J.y', extra=1)], 'unknown fields'),
                ('old_side', dict(modules=['Old']), 'old_side holds'),
                ('schema_version', 2, 'unsupported schema_version')):
            with self.assertRaisesRegex(ValueError, pattern):
                CHECK.validate_classification(dict(copy.deepcopy(CLASSIFICATION), **{field: value}))
        twice = [dict(module='Mixed', name='J.x', reason='a')]
        with self.assertRaisesRegex(ValueError, 'listed twice'):
            CHECK.validate_classification(dict(copy.deepcopy(CLASSIFICATION), retired=twice,
                                               replaced=[dict(module='Mixed', name='J.x', by='J.y')]))
        row = LEDGER['deleted'][0]
        for change, pattern in ((dict(kind='eval'), 'kind must be'), (dict(digest='abc'), 'digest must be'),
                                (dict(disposition='moved'), 'disposition must be'), (dict(count=0), 'count must be'),
                                (dict(disposition='restated'), "missing non-empty 'replacement'")):
            with self.assertRaisesRegex(ValueError, pattern):
                CHECK.validate_ledger(dict(schema_version=1, deleted=[dict(row, **change)], added=[]))


class CommandLineTests(unittest.TestCase):
    """`main` end to end: receipt, verdict lines and exit codes (the snapshot
    reader itself is naming-candidate's)."""

    def run_main(self, after, files=True, extra=('--allow-unbound',)):
        with tempfile.TemporaryDirectory() as tmp:
            tmp = Path(tmp)
            sides = dict(before=snapshot(base(), tmp / 'before'), after=snapshot(after, tmp / 'after'))
            for label in sides:
                (tmp / label / 'snapshot.json').write_text('{}')
            (tmp / 'classification.json').write_text(json.dumps(CLASSIFICATION))
            (tmp / 'ledger.json').write_text(json.dumps(LEDGER))
            argv = ['--before', str(tmp / 'before/snapshot.json'), '--after', str(tmp / 'after/snapshot.json'),
                    '--receipt', str(tmp / 'out/receipt.json')]
            if files:
                argv += ['--classification', str(tmp / 'classification.json'), '--guard-ledger', str(tmp / 'ledger.json')]
            argv += list(extra)
            out, err = io.StringIO(), io.StringIO()
            with unittest.mock.patch.object(CHECK.CANDIDATE, 'read_snapshot',
                                            lambda path, light=True: sides[Path(path).parent.name]), \
                    contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
                code = CHECK.main(argv)
            receipt = tmp / 'out/receipt.json'
            return code, out.getvalue(), err.getvalue(), json.loads(receipt.read_text()) if receipt.exists() else None

    def test_ok_writes_a_bound_receipt(self):
        code, out, err, receipt = self.run_main(deleted(base()))
        self.assertEqual((code, err), (0, ''))
        self.assertRegex(out, r'REHEARSAL \(--allow-unbound\): not a gate verdict\n'
                              r'OK — delete preservation: 5 kept authored constants and 1 kept guards unchanged; '
                              r'5 deleted declarations classified; before bound False, after bound False')
        self.assertTrue(receipt['unbound_rehearsal'])
        self.assertEqual((receipt['verdict'], receipt['classes']), ('OK', {'old-side': 5}))
        for key in ('classification_sha256', 'guard_ledger_sha256', 'tool_sha256'):
            self.assertRegex(receipt[key], r'^[0-9a-f]{64}$')
        self.assertIsNone(receipt['map_sha256'])
        for side in ('before', 'after'):
            self.assertRegex(receipt[side]['exports_sha256'], r'^[0-9a-f]{64}$')

    def test_regression_exits_1_and_lists_rows_to_complete(self):
        code, out, err, receipt = self.run_main(deleted(base()), files=False)
        self.assertEqual(code, 1)
        self.assertRegex(err, r'REGRESSION — delete preservation: 6 finding\(s\)')
        self.assertEqual(len(receipt['unclassified']), 5)
        self.assertEqual(len(receipt['unledgered']['deleted']), 1)

    def test_verdict_needs_bound_captures_and_input_files_of_the_after_capture(self):
        code, _, err, receipt = self.run_main(deleted(base()), extra=())
        self.assertEqual((code, receipt), (2, None))
        self.assertRegex(err, r'SETUP — delete preservation: pass --before-rev and --after-rev')
        code, _, err, receipt = self.run_main(deleted(base()), extra=('--before-rev', 'HEAD', '--after-rev', 'HEAD'))
        self.assertEqual(code, 1)
        self.assertRegex(err, r'the before capture is not the clean tree of HEAD')
        self.assertRegex(err, r'the after capture is not the clean tree of HEAD')
        self.assertRegex(err, r'classification\.json is not a file of the after capture with these bytes')
        self.assertRegex(err, r'ledger\.json is not a file of the after capture with these bytes')
        self.assertEqual((receipt['before']['bound'], receipt['unbound_rehearsal']), (False, False))

    def test_setup_error_exits_2(self):
        after = deleted(base())
        after['Mixed']['from_olean'] = True
        code, _, err, _ = self.run_main(after)
        self.assertEqual(code, 2)
        self.assertRegex(err, r'SETUP — delete preservation: export mode mismatch')


if __name__ == '__main__':
    unittest.main()
