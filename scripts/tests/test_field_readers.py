"""Lock-free tests of the field-reader driver's merge and verdict (no Lean is run).

The Lean walk itself is controlled by `scripts/check-field-readers-tool.py`."""
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).parents[2]
SPEC = importlib.util.spec_from_file_location('field_readers', ROOT / 'scripts' / 'field-readers.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def entry(query, how, owner, cls='reader', module='M', line=1, kind='def'):
    return {'query': query, 'how': how, 'const': owner, 'owner': owner, 'kind': kind,
            'line': line, 'class': cls, 'module': module, 'private': False}


class Aggregate(unittest.TestCase):
    def run_aggregate(self, entries, queries, deleted=()):
        with tempfile.TemporaryDirectory() as d:
            cache = Path(d)
            (cache / 'M.json').write_text(json.dumps({'key': 'k', 'module': 'M', 'entries': entries}))
            return MODULE.aggregate(cache, {'M'}, queries, set(queries) | set(deleted))

    def test_writers_copies_generated_do_not_block(self):
        r = self.run_aggregate([
            entry('S.f', 'write', 'mk'), entry('S.f', 'copy', 'upd'),
            entry('S.f', 'projFn', 'S.ext', cls='generated')], ['S.f'])['S.f']
        self.assertEqual(r['verdict'], 'deletable')
        self.assertEqual([x['owner'] for x in r['writers']], ['mk'])
        self.assertEqual([x['owner'] for x in r['copies']], ['upd'])
        self.assertEqual([x['owner'] for x in r['generated']], ['S.ext'])

    def test_reader_blocks_and_hows_merge(self):
        r = self.run_aggregate([entry('S.f', 'projFn', 'use'), entry('S.f', 'match', 'use')],
                               ['S.f'])['S.f']
        self.assertEqual(r['verdict'], 'reader exists')
        self.assertEqual(r['readers'][0]['how'], ['match', 'projFn'])

    def test_reader_in_deletion_set_does_not_block(self):
        r = self.run_aggregate([entry('S.f', 'projFn', 'S.g'), entry('S.f', 'projFn', 'gone')],
                               ['S.f', 'S.g'], deleted=['gone'])['S.f']
        self.assertEqual(r['verdict'], 'deletable')
        self.assertEqual(sorted(x['owner'] for x in r['in_set']), ['S.g', 'gone'])

    def test_other_queries_ignored(self):
        r = self.run_aggregate([entry('S.h', 'projFn', 'use')], ['S.f'])
        self.assertEqual(list(r), ['S.f'])
        self.assertEqual(r['S.f']['verdict'], 'deletable')


if __name__ == '__main__':
    unittest.main()
