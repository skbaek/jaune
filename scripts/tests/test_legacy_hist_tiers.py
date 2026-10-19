"""Tier selection controls for the historical legacy tiers (goal U10).

`scripts/check-legacy.sh` selects each `--hist-<fork>` tier by the files'
exact `network` labels across both restoration trees. A quoting slip in
that selection fails the tier as "no fixture files selected", so this test
pins the contract: it parses the tier mapping out of the real script (not a
copy of it), rebuilds the selection exactly as the script does, and runs
`grep` itself over a synthetic restoration tree.

Everything here is lock-free: the only subprocesses are a file search and
the three bomb-only refusals, which exit before the harness takes any lock.
No test runs a tier.
"""
from __future__ import annotations

import json
import re
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
CHECK_LEGACY = SCRIPTS / "check-legacy.sh"

# tier -> (network flag, selected fixture labels).
EXPECTED = {
    "hist-byzantium": (
        "Byzantium",
        {"Byzantium", "ByzantiumToConstantinopleFixAt5"},
    ),
    "hist-constantinople": ("Constantinople", {"Constantinople"}),
    "hist-petersburg": (
        "ConstantinopleFix",
        {"ConstantinopleFix", "ByzantiumToConstantinopleFixAt5"},
    ),
    "hist-istanbul": ("Istanbul", {"Istanbul"}),
    "hist-berlin": ("Berlin", {"Berlin", "BerlinToLondonAt5"}),
    "hist-london": ("London", {"London", "BerlinToLondonAt5"}),
    "hist-paris": (
        "Paris",
        {"Paris", "ArrowGlacierToParisAtDiffC0000", "ParisToShanghaiAtTime15k"},
    ),
    "hist-shanghai": (
        "Shanghai",
        {"Shanghai", "ShanghaiToCancunAtTime15k"},
    ),
    "hist-cancun": ("Cancun", {"Cancun", "ShanghaiToCancunAtTime15k"}),
}
BOMB_TIERS = ("hist-muirglacier", "hist-arrowglacier", "hist-grayglacier")


def parse_mapping(script: str) -> dict[str, tuple[str, str]]:
    """The HIST_NET/HIST_LABELS assignments, parsed out of the real script."""
    found = {}
    for match in re.finditer(
        r"^\s*hist-([a-z]+)\)\s*HIST_NET=\"([^\"]+)\";"
        r"\s*HIST_LABELS=\"([^\"]*)\"",
        script,
        re.MULTILINE,
    ):
        found[f"hist-{match.group(1)}"] = (match.group(2), match.group(3))
    return found


class HistTierSelectionTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.script = CHECK_LEGACY.read_text()
        cls.mapping = parse_mapping(cls.script)

    def test_every_runnable_tier_maps_to_its_labels(self):
        self.assertEqual(
            {tier: (net, set(labels.split("|"))) for tier, (net, labels)
             in self.mapping.items()},
            {tier: (net, labels) for tier, (net, labels) in EXPECTED.items()},
        )

    def test_bomb_only_tiers_are_refused_not_selected(self):
        branch = re.search(
            r"^\s*(hist-[a-z|+ -]+)\)\s*$"
            r"\n\s*echo \"error: tier \$TIER selects no file",
            self.script,
            re.MULTILINE,
        )
        self.assertIsNotNone(branch, "no bomb-only refusal branch found")
        refused = {name.strip() for name in branch.group(1).split("|")}
        self.assertEqual(refused, set(BOMB_TIERS))
        for tier in BOMB_TIERS:
            self.assertNotIn(tier, self.mapping)

    def selection(self, root: Path, labels: str) -> list[str]:
        """The tier's selection, run for real over a synthetic tree."""
        pattern = f'"network"[ ]*:[ ]*"({labels})"'
        run = subprocess.run(
            ["grep", "-rl", "--include=*.json", "--exclude-dir=.git",
             "-E", pattern, str(root / "Cancun"), str(root / "Constantinople")],
            capture_output=True,
            text=True,
        )
        self.assertEqual(run.returncode, 0, run.stderr)
        return sorted(
            str(Path(path).relative_to(root)) for path in run.stdout.split()
        )

    def test_selection_is_exact_per_label(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            fixtures = {
                "Cancun/a.json": "Byzantium",
                "Cancun/b.json": "ConstantinopleFix",
                "Cancun/c.json": "Constantinople",
                "Cancun/d.json": "BerlinToLondonAt5",
                "Cancun/e.json": "Prague",
                "Constantinople/f.json": "Byzantium",
                "Constantinople/g.json": "Constantinople",
                "Constantinople/h.json": "ShanghaiToCancunAtTime15k",
                "Cancun/earlier.json": "EIP158ToByzantiumAt5",
                "Cancun/transition.json": "ByzantiumToConstantinopleFixAt5",
            }
            for relative, network in fixtures.items():
                path = root / relative
                path.parent.mkdir(parents=True, exist_ok=True)
                path.write_text(json.dumps({"t": {"network": network}}))
            byzantium = self.selection(root, self.mapping["hist-byzantium"][1])
            self.assertEqual(byzantium, [
                "Cancun/a.json", "Cancun/transition.json", "Constantinople/f.json",
            ])
            # The closing quote keeps Constantinople from matching its Fix.
            constantinople = self.selection(
                root, self.mapping["hist-constantinople"][1])
            self.assertEqual(
                constantinople, ["Cancun/c.json", "Constantinople/g.json"])
            petersburg = self.selection(root, self.mapping["hist-petersburg"][1])
            self.assertEqual(petersburg, ["Cancun/b.json", "Cancun/transition.json"])
            berlin = self.selection(root, self.mapping["hist-berlin"][1])
            self.assertEqual(berlin, ["Cancun/d.json"])
            shanghai = self.selection(root, self.mapping["hist-shanghai"][1])
            self.assertEqual(shanghai, ["Constantinople/h.json"])

    def test_byzantium_scope_is_visible(self):
        start = self.script.index('case "$TIER" in\n  hist-byzantium)')
        end = self.script.index('\nesac', start) + len('\nesac')
        run = subprocess.run(
            ["bash", "-c", 'TIER=hist-byzantium\n' + self.script[start:end]],
            capture_output=True,
            text=True,
        )
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn("SCOPE — hist-byzantium:", run.stdout)
        self.assertIn("EIP158ToByzantiumAt5 is outside this tier", run.stdout)
        self.assertIn("original fixture retained and reported separately", run.stdout)

    def test_bomb_tiers_refuse_before_any_lock(self):
        for tier in BOMB_TIERS:
            run = subprocess.run(
                ["bash", str(CHECK_LEGACY), f"--{tier}", "--no-build"],
                capture_output=True,
                text=True,
            )
            self.assertEqual(run.returncode, 2, tier)
            self.assertIn("selects no file", run.stderr, tier)


if __name__ == "__main__":
    unittest.main()
