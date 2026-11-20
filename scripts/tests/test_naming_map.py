import contextlib
import importlib.util
import io
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

    def test_plural_acronym_tokens(self):
        self.assertEqual(MODULE.tokenize_identifier("BLTs"), ["BLT", "s"])
        self.assertEqual(MODULE.find_retired_tokens("Jaune.Rlp.BLTs", ["BLT"]), ["BLT"])
        self.assertEqual(MODULE.find_retired_tokens("Jaune.toNTBsHash", ["NTBs"]), ["NTBs"])

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

    def test_swap_of_old_and_staged_names_passes(self):
        # One map may move the old name away and give it to the staged one.
        data = dict(self.base_data)
        data["entries"] = [
            _sample_entry(old="Jaune.applyBody", new="Jaune.Bridge.G2a.Old.applyBody", kind="relocation",
                          rule="4", source="Plain English (rule 4)", from_module="Jaune.Transaction",
                          to_module="Jaune.Bridge.G2a.Old.Body"),
            _sample_entry(old="Jaune.Staging.applyBody", new="Jaune.applyBody", rule="4",
                          source="Plain English (rule 4)"),
        ]
        entries, _ = MODULE.validate_map(data)
        self.assertEqual(entries, 2)

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

    def test_retired_names_match_consecutive_segments_by_the_token_rule(self):
        find = MODULE.find_retired_names
        # One component is a retired token: a token run anywhere in a segment.
        for name in ("Jaune.genericCall", "Jaune.Checked.genericCallAmsterdam.step",
                     "Jaune.genericCallAmsterdam_bound", "Jaune.step_genericCall_reply"):
            self.assertEqual(find(name, ["genericCall"]), ["genericCall"], name)
        # Whole tokens and exact case only; the pyspec `ssz_generic` family stays clear.
        for name in ("JauneConsensus.ssz_generic", "JauneConsensus.Harness.SszGeneric",
                     "JauneConsensus.Harness.sszGenericCase", "Jaune.genericCalls",
                     "Jaune.GenericCall", "Jaune.generic.Call", "Jaune.processMessageCall"):
            self.assertEqual(find(name, ["genericCall", "genericCreate", "ProcessMessage"]), [], name)
        self.assertEqual(find("Jaune.GenericCallAmsterdam", ["genericCall", "GenericCall"]), ["GenericCall"])
        # Several components need consecutive segments, in order.
        for name in ("Jaune.Frame.outer", "Jaune.Checked.Frame.outer", "Jaune.Frame.outer.gas",
                     "Jaune.Frame.outer_eq"):
            self.assertEqual(find(name, ["Frame.outer", "Frame.inner"]), ["Frame.outer"], name)
        for name in ("Jaune.outer", "Jaune.θ.outer", "Jaune.Frame.Run.outer", "Jaune.outer.Frame",
                     "Jaune.Frame.router", "Jaune.Frame.Run", "Jaune.NextOp.Run", "Jaune.Body.stepRun"):
            self.assertEqual(find(name, ["Frame.outer", "Step.Run", "NextOp.StepRun"]), [], name)
        self.assertEqual(find("Jaune.processMessage.settle", ["processMessage.settle"]), ["processMessage.settle"])
        self.assertEqual(find("Jaune.processMessageCall.call", ["processMessage.settle"]), [])
        # Each held name once, in list order, even when several segments hold it.
        self.assertEqual(find("Jaune.Step.Run.Step.Run", ["Step.Run", "RunFrame"]), ["Step.Run"])
        self.assertEqual(find("Jaune.value", []), [])

    def test_retired_name_lists_are_optional_and_validated(self):
        data = dict(self.base_data, entries=[])
        for key in ("retired_names", "pending_retired_names"):
            data.pop(key, None)
        self.assertEqual(MODULE.retired_name_lists(data), ([], []))
        MODULE.validate_map(data, final=True)
        for key in ("retired_names", "pending_retired_names"):
            for bad in ("genericCall", [1], [""], ["generic Call"], ["Frame..outer"], [".outer"],
                        ["Frame.outer."], ["genericCall*"], ["_generic"], ["θ.outer"],
                        ["genericCall", "genericCall"]):
                with self.assertRaises(ValueError, msg=(key, bad)):
                    MODULE.validate_map(dict(data, **{key: bad}))
        with self.assertRaisesRegex(ValueError, "listed twice"):
            MODULE.validate_map(dict(data, retired_names=["Frame.outer"], pending_retired_names=["Frame.outer"]))
        MODULE.validate_map(dict(data, retired_names=["Frame.outer", "step_bound"],
                                 pending_retired_names=["genericCall"]))

    def test_final_refuses_pending_retired_names(self):
        data = dict(self.base_data, entries=[], retired_names=["Frame.outer"],
                    pending_retired_names=["genericCall"])
        MODULE.validate_map(data)
        with self.assertRaisesRegex(ValueError, "pending retired names remain: genericCall"):
            MODULE.validate_map(data, final=True)
        MODULE.validate_map(dict(data, retired_names=["Frame.outer", "genericCall"],
                                 pending_retired_names=[]), final=True)
        self.map_path.write_text(json.dumps(data), encoding="utf-8")
        with contextlib.redirect_stdout(io.StringIO()) as out, contextlib.redirect_stderr(io.StringIO()) as err:
            self.assertEqual(MODULE.main(["--map", str(self.map_path)]), 0)
            self.assertEqual(MODULE.main(["--map", str(self.map_path), "--final"]), 1)
        self.assertIn("2 retired names (1 pending)", out.getvalue())
        self.assertIn("pending retired names remain: genericCall", err.getvalue())

    def test_row_may_record_a_rename_to_a_name_retired_later(self):
        # The map is a history: `Xinst.Run` became `MessageOp.Run` before its cut removed it.
        data = dict(self.base_data, retired_names=["MessageOp.Run"], pending_retired_names=[])
        data["entries"] = [_sample_entry(old="Jaune.Xinst.Run", new="Jaune.MessageOp.Run", rule="4",
                                         source="Plain English (rule 4)")]
        self.assertEqual(MODULE.validate_map(data)[0], 1)

    def test_tracked_map_registers_the_inherited_message_call_layers(self):
        # Goal jaune-shape-and-names-v1, S1: each inherited name is retired or pending.
        enforced, pending = MODULE.retired_name_lists(self.base_data)
        for name in ("Jaune.executeCode", "Jaune.executeCodeFueled", "Jaune.processMessage.settle",
                     "Jaune.processCreateMessage.settle", "Jaune.genericCall.step",
                     "Jaune.genericCallAmsterdam.step", "Jaune.genericCreate.step",
                     "Jaune.genericCreateAmsterdam_bound", "Jaune.incorporateChildOnSuccess",
                     "Jaune.liftToExecution", "Jaune.Frame.outer", "Jaune.Frame.inner", "Jaune.RunFrame",
                     "Jaune.ExecuteCode", "Jaune.ProcessMessage", "Jaune.ProcessCreateMessage",
                     "Jaune.GenericCall", "Jaune.GenericCallAmsterdam", "Jaune.GenericCreate",
                     "Jaune.XStep.Run", "Jaune.Step.Run", "Jaune.Xinst.Run", "Jaune.Ninst.StepRun",
                     "Jaune.MessageOp.Run", "Jaune.NextOp.StepRun"):
            self.assertTrue(MODULE.find_retired_names(name, enforced + pending), name)
        # Names of the four-part shape and of the pyspec stay clear.
        for name in ("Jaune.Frame.Run", "Jaune.Frame.Run.Kept", "Jaune.NextOp.Run", "Jaune.Frame.step",
                     "Jaune.Frame.enter", "Jaune.Frame.settle", "Jaune.Frame.resume",
                     "Jaune.processMessageCall", "Jaune.Body.stepRun", "Jaune.θ.outer",
                     "JauneConsensus.ssz_generic", "JauneConsensus.Harness.SszGeneric"):
            self.assertEqual(MODULE.find_retired_names(name, enforced + pending), [], name)

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
