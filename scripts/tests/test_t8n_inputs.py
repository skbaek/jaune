"""Unit tests for explicit t8n alloc composition."""

from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(SCRIPTS))

from t8n_inputs import T8nInputError, composed_alloc, materialize_txs_source


class T8nAllocCompositionTests(unittest.TestCase):
    def write_json(self, path: Path, value) -> None:
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps(value))

    def test_declared_base_and_local_accounts_are_merged(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            case = root / "cases" / "sample"
            self.write_json(root / "base.json", {"0x01": {"balance": "0x01"}})
            self.write_json(case / "case.json", {"allocIncludes": ["../../base.json"]})
            self.write_json(case / "alloc.json", {"0x02": {"balance": "0x02"}})
            self.assertEqual(
                composed_alloc(case, root),
                {
                    "0x01": {"balance": "0x01"},
                    "0x02": {"balance": "0x02"},
                },
            )

    def test_duplicate_account_is_refused(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            case = root / "cases" / "sample"
            account = {"0x01": {"balance": "0x01"}}
            self.write_json(root / "base.json", account)
            self.write_json(case / "case.json", {"allocIncludes": ["../../base.json"]})
            self.write_json(case / "alloc.json", account)
            with self.assertRaisesRegex(T8nInputError, "duplicate alloc account"):
                composed_alloc(case, root)

    def test_include_cannot_escape_the_corpus(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "corpus"
            case = root / "cases" / "sample"
            outside = root.parent / "outside.json"
            self.write_json(outside, {})
            self.write_json(case / "case.json", {"allocIncludes": ["../../../outside.json"]})
            self.write_json(case / "alloc.json", {})
            with self.assertRaisesRegex(T8nInputError, "alloc include escapes"):
                composed_alloc(case, root)

    def test_state_test_transaction_include_materializes_the_shared_list(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            source = root / "cases" / "blockchain"
            mirror = root / "cases" / "state-test"
            txs = [{"nonce": "0x00"}]
            self.write_json(source / "txs.src.json", txs)
            self.write_json(
                mirror / "txs.src.json", {"include": "../blockchain/txs.src.json"}
            )
            destination = root / "materialized.json"
            materialize_txs_source(mirror, root, destination)
            self.assertEqual(json.loads(destination.read_text()), txs)

    def test_transaction_include_cannot_escape_the_corpus(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "corpus"
            case = root / "cases" / "sample"
            self.write_json(root.parent / "outside.json", [])
            self.write_json(
                case / "txs.src.json", {"include": "../../../outside.json"}
            )
            with self.assertRaisesRegex(T8nInputError, "transaction include escapes"):
                materialize_txs_source(case, root, root / "out.json")


if __name__ == "__main__":
    unittest.main()
