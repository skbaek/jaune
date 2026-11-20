import contextlib
import importlib.util
import io
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[2]
SPEC = importlib.util.spec_from_file_location('census', ROOT / 'scripts/naming-census.py')
CENSUS = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(CENSUS)


class NamingCensusTests(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.tree = Path(temp.name)
        (self.tree / 'scripts').mkdir()
        roots = ['Jaune', 'JauneConsensus']
        self.write('scripts/naming-inventory.json', dict(lint_roots=roots))
        self.write('policy.json', dict(schema_version=1, words=['value'], sources={}, bindings={}))
        self.write('map.json', dict(schema_version=1, entries=[], retired_tokens=[],
                                    allowed_abbreviations=[], pending_retired_names=[]))
        modules, exports, headers, files = {}, {}, {}, {}
        for root in roots:
            (self.tree / root).mkdir()
            path = f'{root}/Basic.lean'
            module = f'{root}.Basic'
            source = 'def value := 0\n'
            (self.tree / path).write_text(source)
            digest = CENSUS.CANDIDATE.file_sha(self.tree / path)
            files[path] = digest
            modules[module] = dict(path=path, sha256=digest)
            headers[module] = dict(path=path, is_module=False, direct_imports=[])
            index = dict(version=5, module=module, directImports=[], references={},
                         decls={f'{root}.value': [0, 0, 0, 14, 0, 4, 0, 9]})
            bundle = f'{module}.json'
            self.write(bundle, dict(schema_version=7, source=source, imports={}, index=index))
            exports[module] = dict(path=bundle, sha256=CENSUS.CANDIDATE.file_sha(self.tree / bundle))
        (self.tree / 'lean-toolchain').write_text('fixture compiler')
        files['lean-toolchain'] = CENSUS.CANDIDATE.file_sha(self.tree / 'lean-toolchain')
        source = dict(files=files, modules=modules)
        header = dict(schema_version=1, modules=headers)
        self.write('source-before.json', source)
        self.write('headers.json', header)
        self.write('snapshot.json', dict(schema_version=2, status='OK', build={'exit': 0},
                   candidate=CENSUS.CANDIDATE.bind_headers(source, header), roots=list(modules),
                   selected=list(modules), exports=exports, headers_sha256=CENSUS.CANDIDATE.file_sha(self.tree / 'headers.json')))

    def write(self, path, obj):
        (self.tree / path).write_text(json.dumps(obj))

    def run_cli(self, output, *options):
        argv = ['naming-census.py', 'census', '--tree', str(self.tree), '--snapshot', str(self.tree / 'snapshot.json'),
                '--policy', str(self.tree / 'policy.json'), '--map', str(self.tree / 'map.json'),
                '--source-root', str(self.tree), '--output', str(self.tree / output), *options]
        with patch('sys.argv', argv), contextlib.redirect_stdout(io.StringIO()), contextlib.redirect_stderr(io.StringIO()):
            return CENSUS.main()

    def test_report_and_final_use_registered_capture_and_final_retirements(self):
        self.assertEqual(self.run_cli('clean', '--final'), 0)
        mapping = json.loads((self.tree / 'map.json').read_bytes())
        mapping['pending_retired_names'] = ['unused']
        self.write('map.json', mapping)
        self.assertEqual(self.run_cli('report'), 0)
        self.assertEqual(self.run_cli('strict', '--final'), 1)
        result = json.loads((self.tree / 'strict/census.json').read_bytes())
        self.assertEqual((result['mode'], result['scope'], result['status']), ('final', 'whole-tree', 'REGRESSION'))
        self.assertEqual(result['summary']['declarations'], 2)
        self.assertEqual(result['summary']['by_reason'], {'retired name still registered as pending': 1})

    def test_changed_export_refuses_report_and_final(self):
        path = self.tree / 'Jaune.Basic.json'
        green = path.read_bytes()
        self.assertEqual(self.run_cli('before'), 0)
        bundle = json.loads(green)
        bundle['index']['decls'] = {}
        self.write(path.name, bundle)
        self.assertEqual(self.run_cli('changed-report'), 2)
        self.assertEqual(self.run_cli('changed-final', '--final'), 2)
        self.assertFalse((self.tree / 'changed-report').exists())
        self.assertFalse((self.tree / 'changed-final').exists())
        path.write_bytes(green)
        self.assertEqual(path.read_bytes(), green)

    def test_changed_compiler_input_refuses_final(self):
        path = self.tree / 'lean-toolchain'
        original = path.read_bytes()
        self.assertEqual(self.run_cli('before', '--final'), 0)
        path.write_bytes(b'another compiler')
        self.assertEqual(self.run_cli('changed', '--final'), 2)
        self.assertFalse((self.tree / 'changed').exists())
        path.write_bytes(original)
        self.assertEqual(path.read_bytes(), original)
