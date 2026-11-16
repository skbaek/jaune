import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).parents[2]
SPEC = importlib.util.spec_from_file_location('naming_apply', ROOT / 'scripts/apply-naming-map.py')
M = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(M)


def entry(old='Pilot.Tx.gas', new='Pilot.Tx.gasLimit'):
    return dict(old=old, new=new, kind='field', layer='execution', rule='2',
                source='User decision 8: transaction gasLimit')


def index_for(text, locations):
    refs = {}
    for spelling, name, occurrence, definition in locations:
        start = -1
        for _ in range(occurrence + 1):
            start = text.index(spelling, start + 1)
        line = text.count('\n', 0, start)
        bol = text.rfind('\n', 0, start) + 1
        col = len(text[bol:start].encode('utf-16-le')) // 2
        width = len(spelling.encode('utf-16-le')) // 2
        loc = [line, col, line, col + width]
        key = json.dumps({'c': {'m': 'Pilot', 'n': name}})
        ref = refs.setdefault(key, {'definition': None, 'usages': []})
        if definition:
            ref['definition'] = loc
        else:
            ref['usages'].append(loc)
    return dict(version=5, module='Pilot', references=refs, decls={}, directImports=[])


class NamingApplyTests(unittest.TestCase):
    def test_shared_field_with_projection_literals_updates_and_simp(self):
        text = ('structure Tx where\n  gas : Nat\nstructure Msg where\n  gas : Nat\n'
                'def a (t : Tx) := t.gas\ndef b (m : Msg) := m.gas\n'
                'def c : Tx := { gas := 7 }\ndef d (t : Tx) := { t with gas := 8 }\n'
                'example : (c).gas = 7 := by simp [c, Tx.gas]\n')
        names = ['Pilot.Tx.gas', 'Pilot.Msg.gas', 'Pilot.Tx.gas', 'Pilot.Msg.gas',
                 'Pilot.Tx.gas', 'Pilot.Tx.gas', 'Pilot.Tx.gas', 'Pilot.Tx.gas']
        index = index_for(text, [('gas', n, i, i < 2) for i, n in enumerate(names)])
        edits, problems = M.plan_file(text, index, [entry()])
        self.assertEqual(problems, [])
        self.assertEqual(len(edits), 6)
        for edit in reversed(edits):
            text = text[:edit['start']] + edit['new'] + text[edit['end']:]
        self.assertIn('structure Msg where\n  gas : Nat', text)
        self.assertIn('m.gas', text)
        self.assertIn('with gasLimit := 8', text)
        self.assertIn('simp [c, Tx.gasLimit]', text)

    def test_dot_constructor_reference(self):
        text = 'def f := .gas\n'
        index = index_for(text, [('.gas', 'Pilot.Op.gas', 0, False)])
        edits, problems = M.plan_file(text, index, [entry('Pilot.Op.gas', 'Pilot.Op.gasOp')])
        self.assertEqual(problems, [])
        self.assertEqual(edits[0]['new'], '.gasOp')

    def test_wildcard_alternative_spells_no_constructor(self):
        # `cases r with | log k => ... | _ => rfl`: Lean attributes the covered
        # constructors to the `_`; a constructor rename leaves the wildcard alone.
        text = 'def f (r : Op) : Nat := by\n  cases r with\n  | gas => exact 1\n  | _ => exact 0\n'
        index = index_for(text, [('gas', 'Pilot.Op.gas', 0, False), ('_', 'Pilot.Op.gas', 0, False)])
        edits, problems = M.plan_file(text, index, [entry('Pilot.Op.gas', 'Pilot.Op.gasOp')])
        self.assertEqual(problems, [])
        self.assertEqual([(e['old'], e['new']) for e in edits], [('gas', 'gasOp')])

    def test_generated_constructor_auxiliary_follows_its_constructor(self):
        text = 'example := Op.gas.injEq\nexample := Op.gas.ext\n'
        index = index_for(text, [('Op.gas.injEq', 'Pilot.Op.gas.injEq', 0, False),
                                 ('Op.gas.ext', 'Pilot.Op.gas.ext', 0, False)])
        edits, problems = M.plan_file(text, index, [entry('Pilot.Op.gas', 'Pilot.Op.gasOp')])
        self.assertEqual([(e['old'], e['new']) for e in edits], [('Op.gas.injEq', 'Op.gasOp.injEq')])
        # The capture model knows the generated auxiliary's new name.
        universe = M.Universe({'Pilot.Op.gas', 'Pilot.Op.gas.injEq'}, M.MAP.Renamer([entry('Pilot.Op.gas', 'Pilot.Op.gasOp')]))
        self.assertIn('Pilot.Op.gasOp.injEq', universe.after)
        # An authorable descendant (`ext`) still needs its own row.
        self.assertEqual([p['reason'] for p in problems],
                         ['descendant of renamed declaration needs its own map row'])

    def test_unresolved_use_is_reported(self):
        text = 'def a (x : Tx) := x.gas\n'
        _, problems = M.plan_file(text, index_for(text, []), [entry()])
        self.assertEqual(len(problems), 1)
        self.assertIn('unresolved token', problems[0]['reason'])

    def test_comments_plain_strings_and_interpolations(self):
        text = '-- gas\n/- gas /- gas -/ gas -/\ndef s := "gas"\ndef t := s!"{x.gas}"\n'
        _, problems = M.plan_file(text, index_for(text, []), [entry()])
        self.assertEqual(len(problems), 1)
        self.assertEqual(text[problems[0]['start']:problems[0]['end']], 'gas')

    def test_parser_literals_preserve_unicode_and_embedded_references(self):
        text = 'def t := s!"😀 gas {("gas", x.gas).2} gas"\r\n'
        index = index_for(text, [('gas', 'Pilot.Tx.gas', 2, False)])
        rows = []
        for chunk, kind in [('"😀 gas {', 'interpolatedStrLitKind'),
                            ('"gas"', 'str'), ('} gas"', 'interpolatedStrLitKind')]:
            a = text.index(chunk)
            rows.append([len(text[:a].encode()), len(text[:a + len(chunk)].encode()), kind, chunk])
        index['naming_syntax'] = dict(version=1, literal_ranges=rows)
        # Use the indexed projection spelling, without changing literal data.
        edits, problems = M.plan_file(text, index, [entry()])
        self.assertEqual(problems, [])
        self.assertEqual(len(edits), 1)
        changed = text[:edits[0]['start']] + edits[0]['new'] + text[edits[0]['end']:]
        self.assertEqual(changed, text.replace('x.gas', 'x.gasLimit'))
        index['references'] = {}
        _, problems = M.plan_file(text, index, [entry()])
        self.assertEqual(len(problems), 1)
        self.assertEqual(text[problems[0]['start']:problems[0]['end']], 'gas')

    def test_unindexed_nested_quotes_cannot_hide_uses(self):
        text = 'def t := s!"{("literal", x.gas).2}"\ndef u := x.gas\n'
        matches = [(a, b) for a, b, word in M.identifiers(text) if word == 'gas']
        self.assertEqual(matches, [(text.index('x.gas') + 2, text.index('x.gas') + 5),
                                   (text.rindex('x.gas') + 2, text.rindex('x.gas') + 5)])

    def test_interpolation_discovery_does_not_assume_a_prefix(self):
        for text in ['def t := s! "{x.gas}"', 'def t := dbg_trace "{x.gas}"; 0',
                     'def t := custom "{("text", x.gas).2}"']:
            with self.subTest(text=text):
                self.assertIn('gas', [word for _, _, word in M.identifiers(text)])

    def test_literal_metadata_refuses_invalid_or_conflicting_ranges(self):
        text = '"😀 gas" gas'
        row = [0, len('"😀 gas"'.encode()), 'str', '"😀 gas"']
        for bad in ([1, 2, 'str', 'x'], [0, 999, 'str', 'x'],
                    [0, row[1], 'str', 'other'], [0, row[1], 'guessed', row[3]]):
            index = index_for(text, [])
            index['naming_syntax'] = dict(version=1, literal_ranges=[bad])
            with self.subTest(bad=bad), self.assertRaises(ValueError):
                M.plan_file(text, index, [entry()])
        index = index_for(text, [])
        index['naming_syntax'] = dict(version=1, literal_ranges=[row, row])
        with self.assertRaisesRegex(ValueError, 'overlapping literal'):
            M.plan_file(text, index, [entry()])
        index['naming_syntax']['literal_ranges'] = [row]
        index['references'] = index_for(text, [('gas', 'Pilot.Tx.gas', 0, False)])['references']
        with self.assertRaisesRegex(ValueError, 'overlaps a compiler reference'):
            M.plan_file(text, index, [entry()])
        # A lifted local expression can cover an entire do-term, including a
        # literal. Its span is not an identifier occurrence inside the literal.
        index['references'] = {json.dumps({'f': {'m': 'Main', 'i': '_uniq.fixture'}}):
                               dict(definition=None, usages=[[0, 0, 0, 8]])}
        edits, problems = M.plan_file(text, index, [entry()])
        self.assertEqual(edits, [])
        self.assertEqual(len(problems), 1)  # The unindexed gas after the literal.
        index['naming_syntax']['version'] = 3
        with self.assertRaisesRegex(ValueError, 'unsupported naming syntax'):
            M.plan_file(text, index, [entry()])

    def test_utf16_and_crlf(self):
        text = 'def s := "😀"; def f (x : Tx) := x.gas\r\n'
        index = index_for(text, [('gas', 'Pilot.Tx.gas', 0, False)])
        edits, problems = M.plan_file(text, index, [entry()])
        self.assertEqual(problems, [])
        self.assertEqual(text[edits[0]['start']:edits[0]['end']], 'gas')
        with self.assertRaisesRegex(ValueError, 'surrogate'):
            M.position('😀', 0, 1)

    def test_stale_reference_does_not_replace_another_word(self):
        index = index_for('def a := gas', [('gas', 'Pilot.Tx.gas', 0, False)])
        _, problems = M.plan_file('def a := fee', index, [entry()])
        self.assertIn('not a suffix', problems[0]['reason'])

    def test_descendant_not_silently_skipped(self):
        text = '#check Tx.gas\n'
        index = index_for(text, [('Tx.gas', 'Pilot.Tx.gas', 0, False)])
        _, problems = M.plan_file(text, index, [entry('Pilot.Tx', 'Pilot.Transaction')])
        self.assertIn('descendant', problems[0]['reason'])

    def test_conflicting_references_refuse(self):
        text = 'gas'
        index = index_for(text, [('gas', 'Pilot.Tx.gas', 0, False),
                                 ('gas', 'Pilot.Msg.gas', 0, False)])
        _, problems = M.plan_file(text, index,
                                 [entry(), entry('Pilot.Msg.gas', 'Pilot.Msg.gasLeft')])
        self.assertIn('conflicting', problems[0]['reason'])

    def test_unknown_format_and_namespace_depth_refuse(self):
        with self.assertRaisesRegex(ValueError, 'format 5'):
            M.plan_file('', {'version': 6}, [])
        with self.assertRaisesRegex(ValueError, 'relocation'):
            M.replacement('gas', 'Pilot.Tx.gas', 'Gas.limit')

    def test_mapped_and_unchanged_overlap_refused(self):
        text = 'gas'
        index = index_for(text, [('gas', 'Pilot.Tx.gas', 0, False),
                                 ('gas', 'Pilot.Msg.gas', 0, False)])
        _, problems = M.plan_file(text, index, [entry()])
        self.assertIn('unchanged compiler reference', problems[0]['reason'])

    def syntax(self, text, index, **rows):
        """Version-2 exporter metadata with byte offsets for the given rows."""
        def b(i):
            return len(text[:i].encode())
        meta = dict(version=2, literal_ranges=[], named_arguments=[], namespaces=[],
                    commands=[], imports=[], unresolved_syntax=[])
        for key, values in rows.items():
            meta[key] = [[b(a), b(z), *rest] for a, z, *rest in values]
        index['naming_syntax'] = meta
        return index

    def local_span(self, text, fragment):
        start = text.index(fragment)
        def lsp(i):
            line = text.count('\n', 0, i)
            return [line, len(text[text.rfind('\n', 0, i) + 1:i].encode('utf-16-le')) // 2]
        return {json.dumps({'f': {'m': 'Pilot', 'i': '_uniq.lift'}}):
                dict(definition=None, usages=[lsp(start) + lsp(start + len(fragment))])}

    def test_compound_local_span_does_not_mask_inner_token(self):
        # Reproducer (PAUSE item 2): Lean records `(← e)` as one local whose
        # range is the whole lifted expression. An inner candidate without
        # its own reference must still be reported.
        text = 'def f := do match (← pure (g (gas := 2))) with | _ => pure ()'
        index = index_for(text, [])
        index['references'] = self.local_span(text, '(← pure (g (gas := 2)))')
        _, problems = M.plan_file(text, index, [entry()])
        self.assertEqual([text[p['start']:p['end']] for p in problems], ['gas'])
        self.assertIn('unresolved token', problems[0]['reason'])

    def test_compound_local_span_does_not_block_inner_edit(self):
        text = 'def f (t : Tx) := do match (← pure t.gas) with | _ => pure ()'
        index = index_for(text, [('gas', 'Pilot.Tx.gas', 0, False)])
        index['references'].update(self.local_span(text, '(← pure t.gas)'))
        edits, problems = M.plan_file(text, index, [entry()])
        self.assertEqual(problems, [])
        self.assertEqual([e['new'] for e in edits], ['gasLimit'])

    def test_local_reference_covers_only_its_first_component(self):
        text = 'def f := x.gas'
        index = index_for(text, [])
        index['references'] = self.local_span(text, 'x.gas')
        _, problems = M.plan_file(text, index, [entry()])
        self.assertEqual(len(problems), 1)

    def test_compound_const_reference_cannot_be_renamed(self):
        text = 'def f := (Tx.gas)'
        index = index_for(text, [('(Tx.gas)', 'Pilot.Tx.gas', 0, False)])
        _, problems = M.plan_file(text, index, [entry()])
        self.assertIn('compound reference range', problems[0]['reason'])

    def test_namespace_row_renames_descendants_and_namespace_syntax(self):
        text = ('namespace Pilot\nnamespace B256\ndef toNat := 0\nend B256\n'
                'open B256 in\ndef a := toNat + B256.toNat + x.toNat\nexport B256 (toNat)\nend Pilot\n')
        index = index_for(text, [('toNat', 'Pilot.B256.toNat', 0, True),
                                 ('toNat', 'Pilot.B256.toNat', 1, False),
                                 ('B256.toNat', 'Pilot.B256.toNat', 0, False),
                                 ('toNat', 'Pilot.B256.toNat', 3, False),
                                 ('toNat', 'Pilot.B256.toNat', 4, False)])
        rows = []
        for occurrence, kind in [(0, 'namespace'), (1, 'namespace'), (2, 'open'), (4, 'export')]:
            start = -1
            for _ in range(occurrence + 1):
                start = text.index('B256', start + 1)
            rows.append((start, start + 4, kind, 'Pilot.B256', ''))
        self.syntax(text, index, namespaces=rows)
        row = entry('Pilot.B256', 'Pilot.U256')
        row['kind'] = 'namespace'
        edits, problems = M.plan_file(text, index, [row])
        self.assertEqual(problems, [])
        for edit in reversed(edits):
            text = text[:edit['start']] + edit['new'] + text[edit['end']:]
        self.assertNotIn('B256', text)
        self.assertIn('U256.toNat + x.toNat', text)
        # Without the exporter's namespace rows the syntax stays unresolved.
        index['naming_syntax']['namespaces'] = []
        _, problems = M.plan_file(text.replace('U256', 'B256'), index_for(text, []), [row])
        self.assertTrue(problems)

    def test_unresolved_namespace_syntax_reports_reason(self):
        text = 'open B256'
        index = self.syntax(text, index_for(text, []),
                            namespaces=[(5, 9, 'open', None, 'namespace resolves to 2 candidates')])
        row = entry('Pilot.B256', 'Pilot.U256')
        row['kind'] = 'namespace'
        _, problems = M.plan_file(text, index, [row])
        self.assertIn('2 candidates', problems[0]['reason'])

    def test_depth_change_keeps_resolution_namespace(self):
        text = 'namespace Pilot\ndef a := gVerylow\nend Pilot\ndef b := Pilot.gVerylow\n'
        index = index_for(text, [('gVerylow', 'Pilot.gVerylow', 0, False),
                                 ('Pilot.gVerylow', 'Pilot.gVerylow', 0, False)])
        edits, problems = M.plan_file(text, index, [entry('Pilot.gVerylow', 'Pilot.Gas.veryLow')])
        self.assertEqual(problems, [])
        self.assertEqual([e['new'] for e in edits], ['Gas.veryLow', 'Pilot.Gas.veryLow'])
        # Leaving the spelling's namespace needs explicit qualification.
        _, problems = M.plan_file(text, index, [entry('Pilot.gVerylow', 'Gas.veryLow')])
        self.assertTrue(any('leaves the namespace' in p['reason'] for p in problems))

    def test_projection_keeps_component_count_after_type_rename(self):
        text = 'def a (t : Tx) := t.gas'
        index = index_for(text, [('gas', 'Pilot.Tx.gas', 0, False), ('Tx', 'Pilot.Tx', 0, False)])
        ns = entry('Pilot.Tx', 'Pilot.Transaction')
        ns['kind'] = 'namespace'
        edits, problems = M.plan_file(text, index, [ns, entry('Pilot.Tx.gas', 'Pilot.Transaction.gasLimit')])
        self.assertEqual(problems, [])
        self.assertEqual([e['new'] for e in edits], ['Transaction', 'gasLimit'])

    def test_named_arguments_follow_constructor_fields_only(self):
        text = 'def a := Tx.mk (gas := 1)\ndef b := lt (gas := gas)\ndef c := f (gas := 3)\n'
        def at(n):
            start = -1
            for _ in range(n + 1):
                start = text.index('(gas', start + 1)
            return start + 1, start + 4
        index = index_for(text, [])
        index['references'] = self.local_span(text, 'gas)\ndef c')
        key = next(iter(index['references']))
        index['references'][key]['usages'][0][2:] = [1, index['references'][key]['usages'][0][1] + 3]
        self.syntax(text, index, named_arguments=[
            (*at(0), 'Pilot.Tx.mk', 'gas', 'Pilot.Tx.gas', None),
            (*at(1), 'Pilot.lt', 'gas', None, None),
            (*at(2), None, 'gas', None, 'named argument of a function without a constant head (local or elaborated term)')])
        edits, problems = M.plan_file(text, index, [entry()])
        self.assertEqual([(text[e['start']:e['end']], e['new']) for e in edits], [('gas', 'gasLimit')])
        self.assertEqual(edits[0]['start'], at(0)[0])
        self.assertEqual(len(problems), 1)
        self.assertIn('without a constant head', problems[0]['reason'])

    def test_case_label_diagnostic_is_the_reported_reason(self):
        text = 'case gas => rfl'
        index = self.syntax(text, index_for(text, []), unresolved_syntax=[
            (5, 8, 'case label goal has no ordinary `cases` constructor origin')])
        _, problems = M.plan_file(text, index, [entry()])
        self.assertIn('constructor origin', problems[0]['reason'])

    def test_whole_tree_rows_refused_by_selected_file_planner(self):
        row = entry('Jaune.Types', 'Jaune.Word')
        row['kind'] = 'module'
        self.map.write_text(json.dumps(dict(schema_version=1, retired_tokens=[],
                                           allowed_abbreviations=[], entries=[row])))
        with self.assertRaisesRegex(ValueError, 'whole-tree'):
            self.plan()

    def test_name_capture_is_qualified_not_assumed(self):
        # Execution B256 -> U256 inside a namespace that has its own U256.
        row = entry('J.B256', 'J.U256')
        row['kind'] = 'namespace'
        renamer = M.MAP.Renamer([row])
        universe = M.Universe({'J.B256', 'C.U256', 'J.w', 'C.y'}, renamer)
        text = 'namespace C\nopen J\ndef x : B256 := y\nend C\n'
        index = index_for(text, [('B256', 'J.B256', 0, False), ('y', 'C.y', 0, False)])
        index['module'] = 'Pilot'
        cmd = text.index('def x'), text.index('\nend C')
        self.syntax(text, index, commands=[(*cmd, 'declaration', 'C', [['simple', 'J', []]], [False] * 3)])
        stats = {}
        edits, problems = M.plan_file(text, index, [row], renamer, universe, stats)
        self.assertEqual(problems, [])
        self.assertEqual([e['new'] for e in edits], ['J.U256'])
        self.assertEqual(stats['capture_requalified'], 1)
        # An unchanged reference captured by a newly introduced name is requalified too.
        text = 'namespace J\nopen C\ndef z : U256 := w\nend J\n'
        index = index_for(text, [('U256', 'C.U256', 0, False), ('w', 'J.w', 0, False)])
        index['module'] = 'Pilot'
        cmd = text.index('def z'), text.index('\nend J')
        self.syntax(text, index, commands=[(*cmd, 'declaration', 'J', [['simple', 'C', []]], [False] * 3)])
        edits, problems = M.plan_file(text, index, [row], renamer, universe, stats)
        self.assertEqual([e['new'] for e in edits], ['C.U256'])
        # Without the capture universe the planner would have kept the captured spelling.
        edits, _ = M.plan_file(text, index, [row], renamer)
        self.assertEqual(edits, [])

    def test_constructor_binder_path_rows(self):
        text = 'inductive T where\n  | three (receiver : Nat) (h : receiver = receiver)\ndef v := T.three (receiver := 1) rfl\n'
        index = index_for(text, [('three', 'Pilot.T.three', 0, True), ('T.three', 'Pilot.T.three', 0, False)])
        def lsp(i):
            return [text.count('\n', 0, i), i - text.rfind('\n', 0, i) - 1]
        binder = text.index('receiver')
        uses = [text.index('receiver', binder + 1), text.index('receiver = receiver') + 11]
        index['references'][json.dumps({'f': {'m': 'Pilot', 'i': '_uniq.r'}})] = dict(
            definition=lsp(binder) + lsp(binder + 8), usages=[lsp(u) + lsp(u + 8) for u in uses])
        named = text.index('(receiver := 1)') + 1
        ctor = text.index('three')
        self.syntax(text, index,
                    named_arguments=[(named, named + 8, 'Pilot.T.three', 'receiver', None, None)],
                    constructor_binders=[(ctor, ctor + 5, binder, binder + 8, 'receiver')])
        rows = [entry('Pilot.T.three.receiver', 'Pilot.T.three.to')]
        edits, problems = M.plan_file(text, index, rows)
        self.assertEqual(problems, [])
        for edit in reversed(edits):
            text = text[:edit['start']] + edit['new'] + text[edit['end']:]
        self.assertEqual(text, 'inductive T where\n  | three («to» : Nat) (h : «to» = «to»)\ndef v := T.three («to» := 1) rfl\n')

    def test_declaration_row_renames_its_namespace_syntax(self):
        text = 'namespace B256\ndef toNat := 0\ndef keep := 1\nend B256\n'
        index = index_for(text, [('toNat', 'Pilot.B256.toNat', 0, True), ('keep', 'Pilot.B256.keep', 0, True)])
        rows = [(0, 1, 'namespace'), (1, 1, 'namespace')]
        b1, b2 = text.index('B256'), text.rindex('B256')
        self.syntax(text, index, namespaces=[(b1, b1 + 4, 'namespace', 'Pilot.B256', ''),
                                             (b2, b2 + 4, 'namespace', 'Pilot.B256', '')])
        mapping = [entry('Pilot.B256', 'Pilot.U256'), entry('Pilot.B256.toNat', 'Pilot.U256.toNat')]
        edits, problems = M.plan_file(text, index, mapping)
        self.assertEqual([e['new'] for e in edits], ['U256', 'U256'])
        # `keep` would silently move to the renamed namespace without its row.
        self.assertEqual(len(problems), 1)
        self.assertIn('needs a map row under the new namespace', problems[0]['reason'])
        mapping.append(entry('Pilot.B256.keep', 'Pilot.U256.keep'))
        _, problems = M.plan_file(text, index, mapping)
        self.assertEqual(problems, [])

    def test_compiler_named_definition_and_references(self):
        text = 'instance : Inhabited Adr := x\ndef y := instInhabitedAdr\n'
        index = index_for(text, [('instance', 'Pilot.instInhabitedAdr', 0, True),
                                 ('Adr', 'Pilot.Adr', 0, False),
                                 ('instInhabitedAdr', 'Pilot.instInhabitedAdr', 0, False)])
        renamer = M.MAP.Renamer([entry('Pilot.Adr', 'Pilot.Address')])
        universe = M.Universe({'Pilot.Adr', 'Pilot.instInhabitedAdr'}, renamer, {'Pilot.instInhabitedAdr'})
        edits, problems = M.plan_file(text, index, [entry('Pilot.Adr', 'Pilot.Address')], renamer, universe)
        self.assertEqual([e['new'] for e in edits], ['Address'])
        self.assertEqual(len(problems), 1)
        self.assertIn('compiler-named', problems[0]['reason'])
        # An explicit row for the instance is a plain rename of its references.
        rows = [entry('Pilot.Adr', 'Pilot.Address'), entry('Pilot.instInhabitedAdr', 'Pilot.instInhabitedAddress')]
        edits, problems = M.plan_file(text, index, rows, None, universe)
        self.assertEqual(problems, [])
        self.assertEqual([e['new'] for e in edits], ['Address', 'instInhabitedAddress'])

    def test_compiler_named_report_is_independent_of_hash_seed(self):
        # Two renamed words occur in `gInvJ`; the reported word must not depend on
        # set iteration order, or apply's recomputed plan differs from the saved one.
        import subprocess, sys
        code = (
            "import importlib.util, json, sys\n"
            f"spec = importlib.util.spec_from_file_location('m', {str(ROOT / 'scripts/apply-naming-map.py')!r})\n"
            "M = importlib.util.module_from_spec(spec); spec.loader.exec_module(M)\n"
            "sys.path.insert(0, %r)\n" % str(Path(__file__).parent) +
            "from test_naming_apply import index_for, entry\n"
            "text = 'def y := gInvJ\\n'\n"
            "index = index_for(text, [('gInvJ', 'Pilot.gInvJ', 0, False)])\n"
            "rows = [entry('Pilot.Inv', 'Pilot.Invariant'), entry('Pilot.J', 'Pilot.Joint')]\n"
            "u = M.Universe({'Pilot.gInvJ', 'Pilot.Inv', 'Pilot.J'}, M.MAP.Renamer(rows), {'Pilot.gInvJ'})\n"
            "print(M.plan_file(text, index, rows, None, u)[1][0]['reason'])\n")
        reasons = {subprocess.run([sys.executable, '-c', code], capture_output=True, text=True, check=True,
                                  env={'PYTHONHASHSEED': str(seed)}).stdout for seed in range(12)}
        self.assertEqual(len(reasons), 1, reasons)

    def test_field_abbreviation_keeps_the_local(self):
        text = 'def f (gas : Nat) : Tx := { gas }\n'
        index = index_for(text, [('gas', 'Pilot.Tx.gas', 1, False), ('Tx', 'Pilot.Tx', 0, False)])
        def lsp(i):
            return [0, i]
        first, pun = text.index('gas'), text.index('{ gas }') + 2
        index['references'][json.dumps({'f': {'m': 'Pilot', 'i': '_uniq.g'}})] = dict(
            definition=lsp(first) + lsp(first + 3), usages=[lsp(pun) + lsp(pun + 3)])
        edits, problems = M.plan_file(text, index, [entry()])
        self.assertEqual(problems, [])
        self.assertEqual([e['new'] for e in edits], ['gasLimit := gas'])

    def test_quotation_identifier_is_renamed_without_capture(self):
        row = entry('J.B256', 'J.U256')
        renamer = M.MAP.Renamer([row])
        universe = M.Universe({'J.B256', 'C.U256'}, renamer)
        text = 'namespace C\nopen J\nmacro "m" : term => `((0 : B256))\nend C\n'
        index = index_for(text, [])
        q = text.index('B256')
        cmd = text.index('macro'), text.index('\nend C')
        self.syntax(text, index, commands=[(*cmd, 'macro', 'C', [['simple', 'J', []]], [False] * 3)],
                    quotation_identifiers=[(q, q + 4, 'B256')])
        edits, problems = M.plan_file(text, index, [row], renamer, universe)
        self.assertEqual(problems, [])
        self.assertEqual([e['new'] for e in edits], ['J.U256'])

    def test_quoted_local_binder_without_global_resolution_stays(self):
        # `hx` is a word of a renamed declaration (J.hx), but in the quoting
        # scope (namespace C, nothing open) no constant resolves from it before
        # or after the rename: a quoted local binder, kept as written.
        row = entry('J.hx', 'J.hypothesis')
        renamer = M.MAP.Renamer([row])
        universe = M.Universe({'J.hx', 'C.y'}, renamer)
        text = 'namespace C\nmacro "m" : tactic => `(tactic| intro hx)\nend C\n'
        index = index_for(text, [])
        q = text.index('hx')
        cmd = text.index('macro'), text.index('\nend C')
        def plan(opens, names=None):
            universe = M.Universe(names or {'J.hx', 'C.y'}, renamer)
            self.syntax(text, index, commands=[(*cmd, 'macro', 'C', opens, [False] * 3)],
                        quotation_identifiers=[(q, q + 2, 'hx')])
            stats = {}
            edits, problems = M.plan_file(text, index, [row], renamer, universe, stats)
            return edits, problems, stats
        edits, problems, stats = plan([])
        self.assertEqual((edits, problems), ([], []))
        self.assertEqual(stats['quotation_no_global'], 1)
        # Control: with `open J` the same spelling pre-resolves to J.hx and is renamed.
        edits, problems, _ = plan([['simple', 'J', []]])
        self.assertEqual(problems, [])
        self.assertEqual([e['new'] for e in edits], ['hypothesis'])
        # Control: a rename that would make the spelling resolve afterwards
        # (C.z -> C.hx, captured) is reported, not kept.
        row2 = entry('C.z', 'C.hx')
        renamer = M.MAP.Renamer([row, row2])
        universe = M.Universe({'J.hx', 'C.z'}, renamer)
        self.syntax(text, index, commands=[(*cmd, 'macro', 'C', [], [False] * 3)],
                    quotation_identifiers=[(q, q + 2, 'hx')])
        edits, problems = M.plan_file(text, index, [row, row2], renamer, universe)
        self.assertEqual(len(problems), 1)
        self.assertIn('name capture', problems[0]['reason'])

    def test_quoted_dotted_spelling_without_resolution_is_reported(self):
        # `c.R` with `c` a constant and `.R` a projection onto a renamed field:
        # the whole spelling resolves to no constant, but it is not a local.
        row = entry('F.Rel.R', 'F.Rel.relation')
        renamer = M.MAP.Renamer([row])
        text = 'namespace F\nmacro "m" : term => `(c.R)\nend F\n'
        index = index_for(text, [])
        q = text.index('c.R')
        cmd = text.index('macro'), text.index('\nend F')
        self.syntax(text, index, commands=[(*cmd, 'macro', 'F', [], [False] * 3)],
                    quotation_identifiers=[(q, q + 3, 'c.R')])
        edits, problems = M.plan_file(text, index, [row], renamer, M.Universe({'F.Rel.R', 'F.c'}, renamer))
        self.assertEqual(edits, [])
        self.assertEqual(len(problems), 1)
        self.assertIn('projections', problems[0]['reason'])

    def test_quoted_projection_is_renamed_only_when_the_word_decides(self):
        # `(e).pres` in a quotation resolves through e's type; with every known
        # constant ending in `pres` renamed to `preservation`, the word decides.
        row = entry('F.Frame.pres', 'F.Frame.preservation')
        renamer = M.MAP.Renamer([row])
        text = 'namespace C\nmacro "m" : term => `((f 0).pres)\nend C\n'
        index = index_for(text, [])
        q = text.index('pres')
        cmd = text.index('macro'), text.index('\nend C')
        def plan(names):
            self.syntax(text, index, commands=[(*cmd, 'macro', 'C', [], [False] * 3)],
                        quotation_identifiers=[(q, q + 4, 'pres')])
            return M.plan_file(text, index, [row], renamer, M.Universe(names, renamer))
        edits, problems = plan({'F.Frame.pres', 'C.f'})
        self.assertEqual(problems, [])
        self.assertEqual([e['new'] for e in edits], ['preservation'])
        # Control: another constant ending in `pres` that is not renamed makes
        # the projection undecidable from the word, so it is reported.
        edits, problems = plan({'F.Frame.pres', 'G.Other.pres', 'C.f'})
        self.assertEqual(edits, [])
        self.assertIn('projection inside a quotation', problems[0]['reason'])

    def test_explicit_open_alias_is_captured_by_namespace(self):
        # `open J (B256)` inside namespace C, which has its own U256: the
        # namespace wins over the alias after renaming, so qualify.
        row = entry('J.B256', 'J.U256')
        renamer = M.MAP.Renamer([row])
        universe = M.Universe({'J.B256', 'C.U256'}, renamer)
        text = 'namespace C\nopen J (B256)\ndef x : B256 := 0\nend C\n'
        index = index_for(text, [('B256', 'J.B256', 0, False), ('B256', 'J.B256', 1, False)])
        cmd = text.index('def x'), text.index('\nend C')
        self.syntax(text, index, commands=[(*cmd, 'declaration', 'C', [['explicit', 'B256', 'J.B256']], [False] * 3)])
        edits, problems = M.plan_file(text, index, [row], renamer, universe)
        self.assertEqual(problems, [])
        self.assertEqual([e['new'] for e in edits], ['U256', 'J.U256'])

    def test_new_keyword_spelling_is_escaped(self):
        text = 'def f (t : Tx) := t.receiver'
        index = index_for(text, [('receiver', 'Pilot.Tx.receiver', 0, False), ('Tx', 'Pilot.Tx', 0, False)])
        edits, problems = M.plan_file(text, index, [entry('Pilot.Tx.receiver', 'Pilot.Tx.to')])
        self.assertEqual(problems, [])
        self.assertEqual([e['new'] for e in edits], ['«to»'])

    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.map = self.root / 'map.json'
        self.map.write_text(json.dumps(dict(schema_version=1, retired_tokens=[],
                                           allowed_abbreviations=[], entries=[entry()])))
        self.text = 'def f (x : Tx) := x.gas\n'
        (self.root / 'Pilot.lean').write_text(self.text)
        (self.root / 'Pilot.ilean').write_text(json.dumps(dict(source=self.text, index=index_for(
            self.text, [('gas', 'Pilot.Tx.gas', 0, False)]))))

    def plan(self):
        return M.build_plan(self.root, self.map, [('Pilot.lean', 'Pilot.ilean')])

    def test_apply_and_reapply_refusal(self):
        plan = self.plan()
        self.assertEqual(M.apply_plan(self.root, plan, self.map), 1)
        self.assertIn('x.gasLimit', (self.root / 'Pilot.lean').read_text())
        with self.assertRaises(ValueError):
            M.apply_plan(self.root, plan, self.map)

    def test_plan_tampering_refused(self):
        plan = self.plan()
        plan['files'][0]['edits'][0]['new'] = 'fee'
        with self.assertRaisesRegex(ValueError, 'changed since planning'):
            M.apply_plan(self.root, plan, self.map)
        self.assertEqual((self.root / 'Pilot.lean').read_text(), self.text)

    def test_stale_second_file_leaves_first_untouched(self):
        (self.root / 'Other.lean').write_text(self.text)
        (self.root / 'Other.ilean').write_bytes((self.root / 'Pilot.ilean').read_bytes())
        plan = M.build_plan(self.root, self.map, [('Pilot.lean', 'Pilot.ilean'),
                                                ('Other.lean', 'Other.ilean')])
        (self.root / 'Other.lean').write_text(self.text + '-- changed\n')
        with self.assertRaisesRegex(ValueError, 'source mismatch'):
            M.apply_plan(self.root, plan, self.map)
        self.assertEqual((self.root / 'Pilot.lean').read_text(), self.text)

    def test_changed_map_and_index_refused(self):
        plan = self.plan()
        original = self.map.read_bytes()
        self.map.write_bytes(original + b'\n')
        with self.assertRaisesRegex(ValueError, 'map changed'):
            M.apply_plan(self.root, plan, self.map)
        self.map.write_bytes(original)
        index = self.root / 'Pilot.ilean'
        index.write_bytes(index.read_bytes() + b'\n')
        with self.assertRaisesRegex(ValueError, 'changed since planning'):
            M.apply_plan(self.root, plan, self.map)

    def test_escape_and_symlink_refused(self):
        with self.assertRaisesRegex(ValueError, 'tree-relative'):
            M.safe_path(self.root, '../outside')
        (self.root / 'Alias.lean').symlink_to(self.root / 'Pilot.lean')
        with self.assertRaisesRegex(ValueError, 'symlink'):
            M.safe_path(self.root, 'Alias.lean')


if __name__ == '__main__':
    unittest.main()
