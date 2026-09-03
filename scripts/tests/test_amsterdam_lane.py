"""Synthetic tests for the Glamsterdam devnet lane.

The lane exists to be *installed and refused*, which makes its refusals the
thing worth testing: nothing else exercises them, because no conformance tier
runs this corpus and none ever will until the goal that owns Amsterdam's
semantics activates it. Two properties matter and are checked here.

* **Every suite is refused, by name, with the owning goal named.** A lane whose
  suites quietly selected zero files, or ran and reported an all-PASS verdict
  over a corpus this build cannot judge, would be exactly the permissive
  oracle the harness exists to prevent.
* **The two lanes cannot be confused.** Their suite namespaces are disjoint,
  each names the other's suites when one is asked for on the wrong lane, and
  neither reads the other's manifest or install root.

The manifest half is tested against a synthetic corpus rather than the
installed 20 GB one, so these run in a temp dir with no fixtures present.
"""
from __future__ import annotations

import json
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parents[1]
ROOT = SCRIPTS.parent
sys.path.insert(0, str(SCRIPTS))
import gen_mainnet_manifest as generator
import bootstrap_mainnet
import env_doctor

CHECK_MAINNET = SCRIPTS / "check-mainnet.sh"

AMSTERDAM_SUITES = {
    "amsterdam": "jaune-amsterdam-block-v1",
    "amsterdam-smoke": "jaune-amsterdam-block-v1",
    "amsterdam-full": "jaune-amsterdam-block-v1",
    "amsterdam-transitions": "jaune-amsterdam-currency-v1",
}


def run_check_mainnet(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(CHECK_MAINNET), *args], capture_output=True, text=True, cwd=str(ROOT)
    )


class LaneRefusalTests(unittest.TestCase):
    """The four suites, `--dir`, and both directions of lane confusion."""

    def test_every_amsterdam_suite_is_refused_naming_its_goal(self):
        for suite, goal in AMSTERDAM_SUITES.items():
            with self.subTest(suite=suite):
                run = run_check_mainnet("--lane", "amsterdam", "--suite", suite, "--no-build")
                self.assertEqual(run.returncode, 2, run.stderr)
                self.assertIn("is installed but refused", run.stderr)
                self.assertIn("Fork.rules? answers none", run.stderr)
                self.assertIn(goal, run.stderr)

    def test_refusal_precedes_any_look_at_the_corpus(self):
        """The answer must not depend on whether the archive is installed.

        A refusal that only fired once the fixtures were present would read as
        "not installed" on a fresh clone and as "refused" here, which are
        different claims. Pointing the lane at a directory that does not exist
        must still produce the refusal.
        """
        with tempfile.TemporaryDirectory() as tmp:
            run = run_check_mainnet(
                "--lane", "amsterdam", "--suite", "amsterdam", "--no-build",
                "--fixtures-root", str(Path(tmp) / "absent"),
            )
        self.assertEqual(run.returncode, 2, run.stderr)
        self.assertIn("is installed but refused", run.stderr)

    def test_dir_is_refused_on_the_devnet_lane(self):
        run = run_check_mainnet(
            "--lane", "amsterdam", "--suite", "amsterdam",
            "--dir", "amsterdam/eip7843_slotnum", "--no-build",
        )
        self.assertEqual(run.returncode, 2, run.stderr)
        self.assertIn("--dir is refused on --lane amsterdam", run.stderr)
        self.assertIn("jaune-amsterdam-block-v1", run.stderr)

    def test_mainnet_suite_on_the_devnet_lane_names_the_devnet_suites(self):
        run = run_check_mainnet("--lane", "amsterdam", "--suite", "prague", "--no-build")
        self.assertEqual(run.returncode, 2, run.stderr)
        self.assertIn("is a --lane mainnet suite", run.stderr)
        for suite in AMSTERDAM_SUITES:
            self.assertIn(suite, run.stderr)

    def test_devnet_suite_on_the_mainnet_lane_names_the_right_command(self):
        for suite in AMSTERDAM_SUITES:
            with self.subTest(suite=suite):
                run = run_check_mainnet("--suite", suite, "--no-build")
                self.assertEqual(run.returncode, 2, run.stderr)
                self.assertIn("is a --lane amsterdam suite", run.stderr)
                self.assertIn(f"--lane amsterdam --suite {suite}", run.stderr)

    def test_unknown_lane_is_refused(self):
        run = run_check_mainnet("--lane", "bogus", "--suite", "full", "--no-build")
        self.assertEqual(run.returncode, 2, run.stderr)
        self.assertIn("unknown lane bogus", run.stderr)

    def test_unknown_suite_on_the_devnet_lane_is_refused(self):
        run = run_check_mainnet("--lane", "amsterdam", "--suite", "amsterdam-nope", "--no-build")
        self.assertEqual(run.returncode, 2, run.stderr)
        self.assertIn("unknown suite", run.stderr)

    def test_the_mainnet_lane_is_untouched(self):
        """The default lane still resolves and still refuses what it always did."""
        run = run_check_mainnet("--suite", "bpo1", "--no-build")
        self.assertEqual(run.returncode, 2, run.stderr)
        self.assertIn("selects no file", run.stderr)


class LaneParserTests(unittest.TestCase):
    """The manifest generator's lane coverage, suite naming, and exclusions."""

    def test_the_devnet_lane_covers_amsterdam_and_the_mainnet_lane_does_not(self):
        statics = generator.LANES["amsterdam"].statics
        self.assertEqual(generator.label_forks("Amsterdam", statics), ("Amsterdam",))
        self.assertIsNone(generator.label_forks("Amsterdam"))

    def test_the_devnet_transition_label_resolves_only_in_its_lane(self):
        statics = generator.LANES["amsterdam"].statics
        self.assertEqual(
            generator.label_forks("BPO2ToAmsterdamAtTime15k", statics),
            ("BPO2", "Amsterdam"),
        )
        self.assertIsNone(generator.label_forks("BPO2ToAmsterdamAtTime15k"))

    def test_bpo3_and_bpo4_stay_outside_both_lanes(self):
        """Programme R2: the devnet release carries these labels and Jaune
        declares neither endpoint, so they are excluded with the missing fork
        named -- not silently dropped and not quietly declared."""
        statics = generator.LANES["amsterdam"].statics
        for label, missing in (
            ("BPO2ToBPO3AtTime15k", "BPO3"),
            ("BPO3ToBPO4AtTime15k", "BPO3, BPO4"),
        ):
            with self.subTest(label=label):
                self.assertIsNone(generator.label_forks(label, statics))
                reason = generator.exclusion_reason(label, statics)
                self.assertIn("unsupported transition", reason)
                self.assertIn(missing, reason)

    def test_suite_namespaces_are_disjoint(self):
        mainnet = generator.LANES["mainnet"]
        amsterdam = generator.LANES["amsterdam"]
        mainnet_names = {mainnet.suite(k) for k in ("smoke", "transitions", "full")} | {
            s.lower() for s in mainnet.suite_statics
        }
        amsterdam_names = {amsterdam.suite(k) for k in ("smoke", "transitions", "full")} | {
            s.lower() for s in amsterdam.suite_statics
        }
        self.assertEqual(mainnet_names & amsterdam_names, set())
        self.assertEqual(amsterdam_names, set(AMSTERDAM_SUITES))

    def test_the_lanes_write_different_manifests(self):
        self.assertNotEqual(
            generator.LANES["mainnet"].output, generator.LANES["amsterdam"].output
        )
        self.assertEqual(
            generator.LANES["amsterdam"].output.name, "manifests.json"
        )
        self.assertEqual(
            generator.LANES["amsterdam"].output.parent.name, "amsterdam"
        )


class LaneManifestFieldTests(unittest.TestCase):
    """The lane's `sources.json` section, as bootstrap and doctor read it."""

    def setUp(self):
        self.sources = json.loads((SCRIPTS / "sources.json").read_text())

    def test_the_devnet_section_validates_for_its_own_lane(self):
        lane = bootstrap_mainnet.LANES["amsterdam"]
        bootstrap_mainnet.validate_current_mainnet_manifest(self.sources, lane)

    def test_each_lane_rejects_the_other_lanes_env_var(self):
        """The convention check is per lane, so a section cannot be pointed at
        the other lane's root by copying its `default_env_var`."""
        swapped = json.loads(json.dumps(self.sources))
        swapped["glamsterdam_devnet"]["default_env_var"] = "EEST_MAINNET_ROOT"
        with self.assertRaises(bootstrap_mainnet.CurrentMainnetBootstrapError):
            bootstrap_mainnet.validate_current_mainnet_manifest(
                swapped, bootstrap_mainnet.LANES["amsterdam"]
            )

    def test_a_missing_section_is_named(self):
        without = json.loads(json.dumps(self.sources))
        del without["glamsterdam_devnet"]
        with self.assertRaises(bootstrap_mainnet.CurrentMainnetBootstrapError) as caught:
            bootstrap_mainnet.validate_current_mainnet_manifest(
                without, bootstrap_mainnet.LANES["amsterdam"]
            )
        self.assertIn("glamsterdam_devnet", str(caught.exception))

    def test_the_lanes_install_to_different_roots(self):
        mainnet = bootstrap_mainnet.current_mainnet_root_from_args(
            None, self.sources, bootstrap_mainnet.LANES["mainnet"]
        )
        amsterdam = bootstrap_mainnet.current_mainnet_root_from_args(
            None, self.sources, bootstrap_mainnet.LANES["amsterdam"]
        )
        self.assertNotEqual(mainnet, amsterdam)

    def test_the_release_identity_is_pinned_to_the_devnet_commit(self):
        devnet = self.sources["glamsterdam_devnet"]
        self.assertEqual(devnet["release_tag"], "tests-glamsterdam-devnet@v8.1.3")
        # The fixture release and the transition-tool anchor must name one
        # revision: that is what makes the extracted constants and the fixtures
        # agree by construction rather than by coincidence.
        self.assertEqual(
            devnet["release_commit"], self.sources["conformance_target"]["commit"]
        )

    def test_the_doctor_reports_the_lane_under_its_own_name(self):
        """Both lanes go through one checker, so the reported names are what
        keep two lanes' rows apart in a single doctor run."""
        with tempfile.TemporaryDirectory() as tmp:
            checks = env_doctor.check_amsterdam(self.sources, Path(tmp) / "absent")
        self.assertTrue(checks)
        self.assertTrue(all(c.name.startswith("glamsterdam-devnet") for c in checks))


if __name__ == "__main__":
    unittest.main()
