import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest

ROOT = Path(__file__).parents[2]
SCRIPT = ROOT / "scripts" / "check-naming-map.py"
SPEC = importlib.util.spec_from_file_location("check_naming_map", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


def _sample_entry(**overrides):
    entry = {
        "old": "Jaune.Adr",
        "new": "Jaune.Address",
        "kind": "declaration",
        "layer": "execution",
        "rule": "1",
        "source": "Yellow Paper; opcode ADDRESS",
    }
    entry.update(overrides)
    return entry


class NamingMapTests(unittest.TestCase):
    """Validate rename-map schema, bijection, sources, and retired-token rules."""

    def setUp(self):
        self.root = Path(tempfile.mkdtemp())
        self.addCleanup(shutil.rmtree, self.root)
        self.map_path = self.root / "naming-map.json"
        shutil.copy(ROOT / "scripts" / "naming-map.json", self.map_path)
        self.base_data = json.loads(self.map_path.read_text(encoding="utf-8"))

    def test_tracked_map_passes(self):
        entries, retired = MODULE.check_file(ROOT / "scripts" / "naming-map.json")
        self.assertGreaterEqual(entries, 0)
        self.assertGreater(retired, 0)

    def test_valid_sample_entries_pass(self):
        data = dict(self.base_data)
        data["entries"] = [
            _sample_entry(),
            _sample_entry(
                old="Jaune.Tx.gas",
                new="Jaune.Transaction.gasLimit",
                kind="field",
                rule="2",
                source="User decision 8 (2026-11-15)",
                notes="JSON-RPC uses gas; EIP payloads use gas_limit.",
            ),
            _sample_entry(
                old="Jaune.Acct.bal",
                new="Jaune.Account.balance",
                kind="field",
                rule="1, 6",
                source="Yellow Paper account state",
            ),
            _sample_entry(
                old="JauneConsensus.Facts.Ctx",
                new="JauneConsensus.Facts.Context",
                kind="declaration",
                layer="consensus",
                rule="4, 7",
                source="Plain English (rule 4)",
            ),
        ]
        entries, _ = MODULE.validate_map(data)
        self.assertEqual(entries, 4)

    def test_missing_source_fails(self):
        data = dict(self.base_data)
        bad = _sample_entry()
        del bad["source"]
        data["entries"] = [bad]
        with self.assertRaisesRegex(ValueError, "missing non-empty 'source'"):
            MODULE.validate_map(data)

        bad_empty = _sample_entry(source="   ")
        data["entries"] = [bad_empty]
        with self.assertRaisesRegex(ValueError, "missing non-empty 'source'"):
            MODULE.validate_map(data)

    def test_duplicate_old_or_new_fails(self):
        data = dict(self.base_data)
        data["entries"] = [
            _sample_entry(old="Jaune.Adr", new="Jaune.Address"),
            _sample_entry(old="Jaune.Adr", new="Jaune.TargetAddress"),
        ]
        with self.assertRaisesRegex(ValueError, "duplicate old name"):
            MODULE.validate_map(data)

        data["entries"] = [
            _sample_entry(old="Jaune.Adr", new="Jaune.Address"),
            _sample_entry(old="Jaune.Addr", new="Jaune.Address"),
        ]
        with self.assertRaisesRegex(ValueError, "duplicate new name"):
            MODULE.validate_map(data)

    def test_retired_token_in_new_fails(self):
        data = dict(self.base_data)
        data["entries"] = [
            _sample_entry(old="Jaune.Devm.foo", new="Jaune.Devm.bar"),
        ]
        with self.assertRaisesRegex(ValueError, "retired token"):
            MODULE.validate_map(data)

        data["entries"] = [
            _sample_entry(old="Jaune.ForkRules.bal", new="Jaune.ForkRules.balRules"),
        ]
        with self.assertRaisesRegex(ValueError, "retired token"):
            MODULE.validate_map(data)

    def test_compound_retired_tokens_match_at_word_boundaries(self):
        for name in ("Jaune.txsRootValue", "Jaune.NTBsValue", "Jaune.XStepRun"):
            self.assertTrue(MODULE.find_retired_tokens(name, self.base_data["retired_tokens"]))
        self.assertEqual(MODULE.find_retired_tokens("Jaune.balance", ["bal"]), [])

    def test_invalid_kind_layer_rule_fails(self):
        data = dict(self.base_data)
        data["entries"] = [_sample_entry(kind="alias")]
        with self.assertRaisesRegex(ValueError, "invalid kind"):
            MODULE.validate_map(data)

        data["entries"] = [_sample_entry(layer="blanc")]
        with self.assertRaisesRegex(ValueError, "invalid layer"):
            MODULE.validate_map(data)

        data["entries"] = [_sample_entry(rule="9")]
        with self.assertRaisesRegex(ValueError, "invalid rule"):
            MODULE.validate_map(data)


if __name__ == "__main__":
    unittest.main()
