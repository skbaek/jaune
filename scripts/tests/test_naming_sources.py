import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

ROOT = Path(__file__).parents[2]
SPEC = importlib.util.spec_from_file_location('naming_sources', ROOT / 'scripts/naming_sources.py')
SOURCES = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(SOURCES)


def digest(data):
    return hashlib.sha256(data).hexdigest()


class NamingSourcesTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name) / 'cache'
        (self.root / 'sha256').mkdir(parents=True)
        self.git_text = b'def value := 1\n'
        self.url_text = b'RFC text\n'
        self.lock = {
            'git-source': dict(repository='owner/repo', revision='0' * 40, path='src/A.lean',
                               sha256=digest(self.git_text)),
            'url-source': dict(url='https://example.org/rfc.txt', sha256=digest(self.url_text)),
        }
        for data in (self.git_text, self.url_text):
            (self.root / 'sha256' / digest(data)).write_bytes(data)
        self.lock_path = Path(self.tmp.name) / 'naming-sources.lock.json'
        self.lock_path.write_text(json.dumps(self.lock))

    def verify(self):
        return subprocess.run([sys.executable, '-B', str(ROOT / 'scripts/naming_sources.py'), '--lock',
                               str(self.lock_path), '--source-root', str(self.root), '--offline'],
                              capture_output=True, text=True)

    def test_registered_lock_pins_urls_and_digests_only(self):
        lock = SOURCES.load_lock(ROOT / 'scripts/naming-sources.lock.json')
        extractor = digest((ROOT / 'scripts/pdf_text.py').read_bytes())
        for key, row in lock.items():
            self.assertTrue(set(row) in ({'repository', 'revision', 'path', 'sha256'}, {'url', 'sha256'},
                                         {'url', 'sha256', 'content_sha256', 'extract'}), key)
            if 'extract' in row:
                self.assertEqual(row['extract']['tool_sha256'], extractor, key)

    def test_offline_verify_passes_on_an_intact_cache(self):
        result = self.verify()
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn('2 source IDs', result.stdout)

    def test_offline_verify_fails_on_a_corrupted_cache_entry(self):
        for data in (self.git_text, self.url_text):
            path = self.root / 'sha256' / digest(data)
            path.write_bytes(data + b'tampered')
            result = self.verify()
            self.assertEqual(result.returncode, 1)
            self.assertIn('digest mismatch', result.stderr)
            path.write_bytes(data)
            self.assertEqual(self.verify().returncode, 0)

    def test_offline_verify_fails_on_a_missing_entry(self):
        (self.root / 'sha256' / digest(self.git_text)).unlink()
        result = self.verify()
        self.assertEqual(result.returncode, 1)
        self.assertIn('missing cached source', result.stderr)

    def test_corrupted_extract_and_wrong_extractor_fail(self):
        extract = b'extracted text\n'
        content = b'%PDF-1.4 not really\n'
        row = dict(url='https://example.org/std.pdf', sha256=digest(extract), content_sha256=digest(content),
                   extract=dict(method='pdf-text-v1', tool_sha256='0' * 64))
        SOURCES.load_lock(self.write_lock({'pdf': row}))
        # Offline with only the cached extract: a corrupted extract is refused.
        (self.root / 'sha256' / digest(extract)).write_bytes(extract + b'x')
        with self.assertRaisesRegex(ValueError, 'cached bound text digest mismatch'):
            SOURCES.materialize(self.root, row, True)
        (self.root / 'sha256' / digest(extract)).write_bytes(extract)
        self.assertEqual(SOURCES.materialize(self.root, row, True), len(extract))
        # With the PDF cached, the extract is re-derived by the pinned extractor, whose digest must match.
        (self.root / 'sha256' / digest(content)).write_bytes(content)
        with self.assertRaisesRegex(ValueError, 'extractor differs'):
            SOURCES.materialize(self.root, row, True)

    def write_lock(self, rows):
        self.lock_path.write_text(json.dumps(rows))
        return self.lock_path


if __name__ == '__main__':
    unittest.main()
