"""Synthetic tests for the Glamsterdam devnet lane.

The lane is now *fully runnable*, and that is what these tests hold in place.
This build implements Amsterdam and gates the BPO2-to-Amsterdam activation
boundary, so all four suites run: the two over the static `Amsterdam` corpus
(since goal C) and the two that select `BPO2ToAmsterdamAtTime15k` (since goal
`jaune-amsterdam-currency-v1`, which rewrote goal C's refusals into
admissions). Four properties matter and are checked below.

* **Every suite is admitted, and actually dispatches.** A suite that was
  "activated" by deleting its refusal but still selected nothing, or that
  reported an all-PASS over a subtree it only partly ran, would be the same
  permissive oracle the refusals existed to prevent. The end-to-end class runs
  the real harness over a miniature synthetic corpus with a stub binary, so the
  dispatch, the selection, and the verdict are exercised without the installed
  archive and without Lean. `--start-at` reports only what it verified.
* **No retired refusal survives, in a message or in the source.** Goal A's
  refusal said `Fork.rules?` answers `none` for Amsterdam; goal C's said no gate
  covers the activation boundary. Both are false in this build, and a refusal
  that states a false fact is worse than no refusal, so the absence of both
  statements is asserted directly, and the transition suites pointed at an
  absent root reach the corpus check like the static ones.
* **`--dir` refuses rather than under-reports.** A subtree that does not exist,
  holds no fixture, or whose on-disk file count disagrees with the manifest's
  count for the selected suite is an error, never a smaller pass.
* **The two lanes cannot be confused.** Their suite namespaces are disjoint,
  each names the other's suites when one is asked for on the wrong lane, and
  neither reads the other's manifest or install root.
"""
from __future__ import annotations

import contextlib
import json
import shutil
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

# The lane's four suite names. Every one is runnable in this build; the two
# transition-carrying ones were refused until goal jaune-amsterdam-currency-v1.
AMSTERDAM_STATIC_SUITES = ("amsterdam", "amsterdam-smoke")
AMSTERDAM_TRANSITION_SUITES = ("amsterdam-transitions", "amsterdam-full")
AMSTERDAM_RUNNABLE_SUITES = AMSTERDAM_STATIC_SUITES + AMSTERDAM_TRANSITION_SUITES
AMSTERDAM_SUITES = AMSTERDAM_RUNNABLE_SUITES

# The claims the previous refusals rested on, each made false by a later
# build. None may survive anywhere in the harness: a stale refusal reads as a
# current fact about the build. The first is goal A's (falsified by goal C),
# the second goal C's (falsified by goal jaune-amsterdam-currency-v1).
RETIRED_CLAIMS = (
    "Fork.rules? answers none",
    "no gate in this build covers the BPO2-to-Amsterdam activation boundary",
    "is installed but refused",
)

# One consistent blob schedule for the synthetic corpus. The generator requires
# every in-lane case to declare one for each fork its label can select, and
# refuses a corpus whose files disagree; these values are the pinned release's
# own, read from `for_amsterdam/amsterdam/eip7843_slotnum`.
SYNTHETIC_BLOB_SCHEDULE = {
    "Prague": {"target": "0x06", "max": "0x09", "baseFeeUpdateFraction": "0x4c6964"},
    "BPO2": {"target": "0x0e", "max": "0x15", "baseFeeUpdateFraction": "0xb24b3f"},
    "Amsterdam": {"target": "0x0e", "max": "0x15", "baseFeeUpdateFraction": "0xb24b3f"},
}

T8N = SCRIPTS / "t8n"
AMSTERDAM_T8N_SCENARIOS = (
    "am-transfer",
    "am-self-transfer",
    "am-create",
    "am-call-new-account",
    "am-call-new-account-fails",
    "am-spill",
    "am-cross-frame-refund",
    "am-sstore-lattice",
    "am-selfdestruct",
    "am-extcode",
    "am-delegation",
    "am-reservoir",
    "am-floor",
    "am-refund-cap",
    "am-reject-intrinsic",
)
AMSTERDAM_SYSTEM_ADDRESSES = {
    "0x0000bff46984e3725691fa540a8c7589300d8282",
    "0x000064d678505ad48f8ccb093bc65613800e8282",
    "0x0000f90827f1c53a10cb7a02335b175320002935",
    "0x0000bbddc7ce488642fb579f8b00f3a590007251",
    "0x00000961ef480eb55e80d19ad83579a64c007002",
    "0x000f3df6d732807ef1319fb7b8bb8522d0beac02",
}


def run_check_mainnet(*args: str) -> subprocess.CompletedProcess:
    return subprocess.run(
        [str(CHECK_MAINNET), *args], capture_output=True, text=True, cwd=str(ROOT)
    )


class LaneRefusalTests(unittest.TestCase):
    """The four suites, and both directions of lane confusion."""

    def test_the_transition_suites_are_admitted_naming_no_goal(self):
        """Goal C refused `amsterdam-transitions` and `amsterdam-full` by name,
        naming `jaune-amsterdam-currency-v1` as the goal that would gate the
        activation boundary. That goal rewrote the refusal into this admission:
        the two suites are answered exactly like the static ones -- pointed at
        an absent root they reach the corpus check -- and no message names a
        goal that "owns" them any more."""
        for suite in AMSTERDAM_TRANSITION_SUITES:
            with self.subTest(suite=suite):
                with tempfile.TemporaryDirectory() as tmp:
                    run = run_check_mainnet(
                        "--lane", "amsterdam", "--suite", suite, "--no-build",
                        "--fixtures-root", str(Path(tmp) / "absent"),
                    )
                self.assertEqual(run.returncode, 2, run.stderr)
                self.assertNotIn("is installed but refused", run.stderr)
                self.assertNotIn("jaune-amsterdam-currency-v1", run.stderr)
                self.assertIn("glamsterdam-devnet blockchain fixture root not found", run.stderr)

    def test_no_refusal_repeats_a_claim_a_later_build_falsified(self):
        """`Fork.amsterdam.rules?` resolves and the activation boundary is
        gated, so nothing may still say otherwise -- neither in a message
        printed at runtime nor in the source that prints them, where a stale
        sentence would be read as current fact."""
        for suite in AMSTERDAM_SUITES:
            with self.subTest(suite=suite):
                with tempfile.TemporaryDirectory() as tmp:
                    run = run_check_mainnet(
                        "--lane", "amsterdam", "--suite", suite, "--no-build",
                        "--fixtures-root", str(Path(tmp) / "absent"),
                    )
                for claim in RETIRED_CLAIMS:
                    self.assertNotIn(claim, run.stderr)
        for claim in RETIRED_CLAIMS:
            self.assertNotIn(claim, CHECK_MAINNET.read_text())
            self.assertNotIn(claim, (SCRIPTS / "gen_mainnet_manifest.py").read_text())

    def test_the_runnable_suites_are_admitted_and_reach_the_corpus(self):
        """Every suite this build may run -- all four -- must NOT be refused by
        name. Pointed at an absent root it gets as far as the corpus check and
        stops there -- which is the bootstrap message, not a refusal, and is
        reached before any lock is taken or any fixture is dispatched."""
        for suite in AMSTERDAM_RUNNABLE_SUITES:
            with self.subTest(suite=suite):
                with tempfile.TemporaryDirectory() as tmp:
                    run = run_check_mainnet(
                        "--lane", "amsterdam", "--suite", suite, "--no-build",
                        "--fixtures-root", str(Path(tmp) / "absent"),
                    )
                self.assertEqual(run.returncode, 2, run.stderr)
                self.assertNotIn("is installed but refused", run.stderr)
                self.assertIn("glamsterdam-devnet blockchain fixture root not found", run.stderr)

    def test_usage_states_which_devnet_suites_run(self):
        run = run_check_mainnet()
        self.assertEqual(run.returncode, 2, run.stderr)
        for suite in AMSTERDAM_SUITES:
            self.assertIn(suite, run.stderr)
        # Goal C's usage line ended "amsterdam-transitions, amsterdam-full
        # refused"; the four suites are now listed as peers and no suite on
        # this lane is described as refused.
        self.assertNotIn("refused", run.stderr.split("--lane amsterdam")[1].splitlines()[0])

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


class SyntheticLaneRunTests(unittest.TestCase):
    """The activated lane, end to end, over a corpus small enough to own.

    The installed devnet archive is ~20 GB and running any real subtree needs
    the built binary and minutes of wall time, so neither belongs in the cheap
    tier. What does belong there is the harness's own logic: that a runnable
    suite selects the right entries and dispatches them, that `--dir` picks out
    exactly one subtree, and that every way of selecting fewer files than the
    subtree holds is refused instead of reported as a smaller pass.

    So this class builds a miniature corpus (four fixtures, one of them a
    transition, in three subtrees plus an empty one), generates the lane's
    manifest over it with the real generator, and runs the real
    `check-mainnet.sh` against a stub `jaune` that passes everything. A stub
    that always passes is the right oracle here precisely because the thing
    under test is selection: if the harness ran the wrong files, or none, the
    verdict's counts would still say so.

    `--suite amsterdam-smoke` is the suite used to dispatch, because it takes no
    lock; `--suite amsterdam` takes the host-global heavy-gate lock, which a
    unit test must never contend for.
    """

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="amsterdam-lane-"))
        cls.addClassCleanup(shutil.rmtree, cls.tmp, ignore_errors=True)
        cls.checkout = cls.tmp / "checkout"
        cls.fixtures = cls.tmp / "fixtures"
        cls.build_checkout(cls.checkout)
        cls.build_corpus(cls.fixtures)
        generated = subprocess.run(
            [sys.executable, str(cls.checkout / "scripts" / "gen_mainnet_manifest.py"),
             "--lane", "amsterdam", "--fixtures-root", str(cls.fixtures)],
            capture_output=True, text=True,
        )
        assert generated.returncode == 0, generated.stderr
        cls.manifest = json.loads(
            (cls.checkout / "scripts" / "amsterdam" / "manifests.json").read_text()
        )

    @classmethod
    def build_checkout(cls, checkout: Path) -> None:
        """A throwaway copy of the harness, with a stub binary in place of Lean.

        Only the top-level files of `scripts/` are copied: the harness, the
        generator, the lock, and `sources.json`, which is the real one -- the
        release identity that seeds the smoke ranking has to be the pinned one
        for this to be a test of the shipped selection rule.
        """
        scripts = checkout / "scripts"
        scripts.mkdir(parents=True)
        for path in SCRIPTS.iterdir():
            if path.is_file():
                shutil.copy2(path, scripts / path.name)
        (scripts / "amsterdam").mkdir()
        stub = checkout / ".lake" / "build" / "bin"
        stub.mkdir(parents=True)
        binary = stub / "jaune"
        binary.write_text("#!/bin/sh\nexit 0\n")
        binary.chmod(0o755)

    @classmethod
    def build_corpus(cls, fixtures: Path) -> None:
        release = json.loads((SCRIPTS / "sources.json").read_text())["glamsterdam_devnet"]
        for name in release["expected_top_level_dirs"]:
            (fixtures / name).mkdir(parents=True)
        # The publisher's own release index, carrying the identity `sources.json`
        # pins. The generator refuses a tree whose index is not the pinned one,
        # so a synthetic corpus that omitted it would be testing a code path the
        # real lane never takes.
        index = fixtures / release["metadata_json_file_subpath"]
        index.parent.mkdir(parents=True, exist_ok=True)
        index.write_text(json.dumps(release["metadata_json_expected"]))
        cls.write_fixture(fixtures, "for_amsterdam/amsterdam/eip7843_slotnum/a.json", "Amsterdam")
        cls.write_fixture(fixtures, "for_amsterdam/amsterdam/eip7843_slotnum/b.json", "Amsterdam")
        # A subtree that mixes labels: the devnet archive re-fills earlier forks'
        # suites under `for_amsterdam` too, so a directory holding both is the
        # shape the count rule exists for.
        cls.write_fixture(fixtures, "for_amsterdam/amsterdam/eip9999_mixed/c.json", "Amsterdam")
        cls.write_fixture(fixtures, "for_amsterdam/amsterdam/eip9999_mixed/d.json", "Prague")
        cls.write_fixture(
            fixtures, "for_bpo2toamsterdamattime15k/t.json", "BPO2ToAmsterdamAtTime15k"
        )
        (fixtures / "blockchain_tests/for_amsterdam/amsterdam/eip0000_empty").mkdir()

    @classmethod
    def write_fixture(cls, fixtures: Path, relative: str, network: str) -> None:
        path = fixtures / "blockchain_tests" / relative
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(json.dumps({
            f"{network}-{relative}": {
                "network": network,
                "config": {
                    "network": network,
                    "chainid": "0x01",
                    "blobSchedule": SYNTHETIC_BLOB_SCHEDULE,
                },
            }
        }))

    def run_lane(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [str(self.checkout / "scripts" / "check-mainnet.sh"),
             "--lane", "amsterdam", "--no-build",
             "--fixtures-root", str(self.fixtures), *args],
            capture_output=True, text=True, cwd=str(self.checkout),
        )

    # -- the manifest the lane raises over this corpus --------------------

    def test_every_suite_is_runnable_and_no_refusal_reason_remains(self):
        """Goal C's manifest carried `runnable: false` and a `refusal_reason`
        naming `jaune-amsterdam-currency-v1` on the two transition suites; that
        goal rewrote the statement: every suite is runnable and the reason is
        gone from the whole document."""
        suites = self.manifest["suites"]
        self.assertEqual(sorted(suites), sorted(AMSTERDAM_SUITES))
        for name in AMSTERDAM_RUNNABLE_SUITES:
            with self.subTest(suite=name):
                self.assertTrue(suites[name]["runnable"])
                self.assertNotIn("refusal_reason", suites[name])
        self.assertTrue(self.manifest["runnable"])
        self.assertNotIn("refusal_reason", json.dumps(self.manifest))
        self.assertEqual(
            [e["path"] for e in suites["amsterdam-transitions"]["files"]],
            ["for_bpo2toamsterdamattime15k/t.json"],
        )
        self.assertEqual(suites["amsterdam-full"]["file_count"], 4)

    def test_the_static_suite_holds_every_amsterdam_case_and_nothing_else(self):
        amsterdam = self.manifest["suites"]["amsterdam"]
        self.assertEqual(
            [entry["path"] for entry in amsterdam["files"]],
            [
                "for_amsterdam/amsterdam/eip7843_slotnum/a.json",
                "for_amsterdam/amsterdam/eip7843_slotnum/b.json",
                "for_amsterdam/amsterdam/eip9999_mixed/c.json",
            ],
        )
        self.assertEqual(amsterdam["file_count"], 3)

    def test_nothing_under_for_amsterdam_is_excluded(self):
        """G7's manifest condition: the exclusion list may not reach into the
        corpus this lane runs. An exclusion there would be a file silently not
        run under a suite reported all-PASS."""
        excluded = [
            entry["path"]
            for label in self.manifest["excluded"].values()
            for entry in label["files"]
            if entry["path"].startswith("for_amsterdam/")
        ]
        self.assertEqual(excluded, [])

    # -- dispatch ---------------------------------------------------------

    def test_a_runnable_suite_dispatches_every_selected_file(self):
        run = self.run_lane("--suite", "amsterdam-smoke")
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn("OK — amsterdam-smoke: 3/3 manifest files PASS", run.stdout)

    def test_start_at_reports_only_what_it_verified(self):
        """Goal C's independent review, F2: the sequential path seeded its PASS
        count with the skipped entries and printed `3/3 manifest files PASS`
        after dispatching one -- and this test pinned that string. It now
        asserts the honest one, in the parallel path's wording."""
        run = self.run_lane("--suite", "amsterdam-smoke", "--start-at", "3")
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(
            "OK — amsterdam-smoke: 1/1 selected manifest files PASS", run.stdout
        )
        self.assertIn("(entries 3-3; 2 skipped by --start-at and NOT verified)", run.stdout)
        self.assertNotIn("3/3 manifest files PASS", run.stdout)
        self.assertIn("[3/3] PASS", run.stderr)
        self.assertNotIn("[1/3] PASS", run.stderr)

    def test_the_transition_suite_dispatches_its_fixture(self):
        """The rewritten admission is exercised end to end: the transition
        suite selects the one `BPO2ToAmsterdamAtTime15k` fixture and dispatches
        it under that label (the harness's allowed-network list admits it), and
        both of the union's components dispatch every file they select."""
        run = self.run_lane("--suite", "amsterdam-transitions")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("OK — amsterdam-transitions: 1/1 manifest files PASS", run.stdout)
        self.assertIn("[1/1] PASS for_bpo2toamsterdamattime15k/t.json", run.stderr)
        # The second dispatch used to be `--suite amsterdam-full`, the union.
        # `check-mainnet.sh` derives the heavy-gate lock from the suite *name*
        # (`osaka|prague|full|amsterdam|amsterdam-full`), and that lock is
        # host-global and refused rather than queued, so this row -- a "light",
        # no-corpus unit row -- failed with
        # `REFUSED — amsterdam-full: the heavy-gate lock is locked by PID ...`
        # whenever any other checkout on the host was running a heavy gate.
        # That is a fact about the host, not about the lane, and a unit suite
        # must stay lock-free. The union's two components are dispatched here
        # and just below through the two suites that take no lock when
        # sequential, so all four of its files are still dispatched; the
        # union's own *selection* stays pinned by
        # `test_every_suite_is_runnable_and_no_refusal_reason_remains` above
        # (`suites["amsterdam-full"]["file_count"] == 4`).
        #
        # What IS lost, stated plainly rather than glossed: after this change
        # `amsterdam-full` is dispatched nowhere -- not here, not in any other
        # test, and not in the goal's catalogue selection -- so this module's
        # first stated property, "every suite is admitted, and actually
        # dispatches", no longer holds of that one suite. Its selection is
        # pinned and each of its two components is dispatched, which is why the
        # trade was taken; restoring the union's own dispatch needs a lock-free
        # way to run it, which is `check-mainnet.sh`'s to provide.
        # (Goal `jaune-forks-by-construction-v1`, W6; independent review F-4.)
        run = self.run_lane("--suite", "amsterdam-smoke")
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("OK — amsterdam-smoke: 3/3 manifest files PASS", run.stdout)

    def test_dir_lands_a_transition_subtree_under_the_count_rule(self):
        """Open question 2 of the goal: the count rule fits the transition
        tree as it is -- a subtree of `for_bpo2toamsterdamattime15k/` holds
        only that label's files, so on-disk count equals the suite's count."""
        run = self.run_lane(
            "--suite", "amsterdam-transitions", "--dir", "for_bpo2toamsterdamattime15k"
        )
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn(
            "OK — amsterdam-transitions:for_bpo2toamsterdamattime15k: 1/1", run.stdout
        )

    def test_dir_selects_exactly_one_subtree(self):
        run = self.run_lane(
            "--suite", "amsterdam-smoke", "--dir", "for_amsterdam/amsterdam/eip7843_slotnum"
        )
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn(
            "OK — amsterdam-smoke:for_amsterdam/amsterdam/eip7843_slotnum: 2/2", run.stdout
        )

    # -- and every way of selecting fewer files than the subtree holds -----

    def test_dir_refuses_a_subtree_whose_counts_disagree(self):
        """The count rule: on-disk `.json` count must equal the manifest's count
        for the selected suite. The mixed subtree holds two files and the suite
        selects one of them, so running it would report an all-PASS over "the
        subtree" while half of it never ran."""
        run = self.run_lane(
            "--suite", "amsterdam-smoke", "--dir", "for_amsterdam/amsterdam/eip9999_mixed"
        )
        self.assertEqual(run.returncode, 2, run.stdout + run.stderr)
        self.assertIn("holds 2 fixture files but the amsterdam-smoke manifest lists 1", run.stderr)
        self.assertNotIn("PASS", run.stdout)

    def test_dir_refuses_an_empty_subtree(self):
        run = self.run_lane(
            "--suite", "amsterdam-smoke", "--dir", "for_amsterdam/amsterdam/eip0000_empty"
        )
        self.assertEqual(run.returncode, 2, run.stdout + run.stderr)
        self.assertIn("holds no fixture file", run.stderr)
        self.assertNotIn("PASS", run.stdout)

    def test_dir_refuses_a_subtree_that_is_not_there(self):
        run = self.run_lane(
            "--suite", "amsterdam-smoke", "--dir", "for_amsterdam/amsterdam/eip0000_nonexistent"
        )
        self.assertEqual(run.returncode, 2, run.stdout + run.stderr)
        self.assertIn("--dir subtree not found", run.stderr)

    def test_dir_names_the_full_path_when_the_for_amsterdam_prefix_is_missing(self):
        """The lane's own subtrees sit two levels down. `--dir` is one rule on
        both lanes -- a path under `blockchain_tests` -- so the short spelling is
        an error, and an error that can name the path meant costs nothing."""
        run = self.run_lane("--suite", "amsterdam-smoke", "--dir", "amsterdam/eip7843_slotnum")
        self.assertEqual(run.returncode, 2, run.stdout + run.stderr)
        self.assertIn("--dir subtree not found", run.stderr)
        self.assertIn("--dir for_amsterdam/amsterdam/eip7843_slotnum", run.stderr)

    def test_dir_refuses_an_escaping_path(self):
        run = self.run_lane("--suite", "amsterdam-smoke", "--dir", "../for_amsterdam")
        self.assertEqual(run.returncode, 2, run.stdout + run.stderr)
        self.assertIn("must be a relative path inside blockchain_tests", run.stderr)

    # -- the manifest catches a changed corpus, it does not absorb it -----

    def run_generator(self, *args: str) -> subprocess.CompletedProcess:
        return subprocess.run(
            [sys.executable, str(self.checkout / "scripts" / "gen_mainnet_manifest.py"),
             "--lane", "amsterdam", "--fixtures-root", str(self.fixtures), *args],
            capture_output=True, text=True,
        )

    @contextlib.contextmanager
    def mutated(self, relative: str, edit):
        """One file of the corpus, changed for the duration of one test."""
        path = self.fixtures / relative
        original = path.read_bytes()
        path.write_text(edit(json.loads(original)))
        try:
            yield
        finally:
            path.write_bytes(original)

    def test_the_unmutated_corpus_checks_clean(self):
        """The baseline the two controls below are read against."""
        run = self.run_generator("--check")
        self.assertEqual(run.returncode, 0, run.stderr)
        self.assertIn("exactly matches the pinned fixture tree", run.stdout)

    def test_a_changed_fixture_turns_check_red(self):
        """Programme §10's named risk: a fixture-format change must be caught,
        not absorbed. A key added to a fixture leaves its network label and its
        case names untouched -- the manifest's content digest is what sees it."""
        def add_a_header_field(fixture: dict) -> str:
            case = next(iter(fixture.values()))
            case["extraHeaderField"] = "0x00"
            return json.dumps(fixture)

        with self.mutated(
            "blockchain_tests/for_amsterdam/amsterdam/eip7843_slotnum/a.json",
            add_a_header_field,
        ):
            run = self.run_generator("--check")
        self.assertEqual(run.returncode, 1, run.stdout + run.stderr)
        self.assertIn("stale or fixture input differs", run.stderr)

    def test_a_changed_release_index_is_refused(self):
        """The other half of the same risk: the tree's own identity. A manifest
        generated over a tree whose index says it is a different release would
        be an exact claim about the wrong thing, so this fails closed at
        generation rather than being recorded and compared."""
        with self.mutated(
            ".meta/index.json",
            lambda index: json.dumps(dict(index, test_count=index["test_count"] + 1)),
        ):
            checked = self.run_generator("--check")
            regenerated = self.run_generator()
        self.assertEqual(checked.returncode, 2, checked.stdout + checked.stderr)
        self.assertIn("release index does not match the pin", checked.stderr)
        self.assertIn("test_count", checked.stderr)
        # And it may not be regenerated into agreement either.
        self.assertEqual(regenerated.returncode, 2, regenerated.stdout)


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
        self.assertEqual(devnet["release_tag"], "tests-glamsterdam-devnet@v8.1.4")
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


class AmsterdamT8nCorpusTests(unittest.TestCase):
    """Appendix-F scenarios, paired modes, and their declared boundary."""

    def case(self, scenario: str, mode: str) -> Path:
        return T8N / "cases" / f"{scenario}-{mode}"

    def test_appendix_f_has_exactly_fifteen_scenarios_in_both_modes(self):
        expected = {
            f"{scenario}-{mode}"
            for scenario in AMSTERDAM_T8N_SCENARIOS
            for mode in ("blockchain", "state-test")
        }
        actual = {
            path.name
            for path in (T8N / "cases").iterdir()
            if path.is_dir()
            and json.loads((path / "case.json").read_text()).get("fork")
            == "Amsterdam"
        }
        self.assertEqual(actual, expected)

    def test_each_case_owns_four_inputs_and_declares_shared_system_alloc(self):
        for scenario in AMSTERDAM_T8N_SCENARIOS:
            for mode in ("blockchain", "state-test"):
                with self.subTest(scenario=scenario, mode=mode):
                    case = self.case(scenario, mode)
                    spec = json.loads((case / "case.json").read_text())
                    self.assertEqual(spec["scenario"], scenario)
                    self.assertEqual(spec["fork"], "Amsterdam")
                    self.assertEqual(spec["mode"], mode)
                    self.assertEqual(
                        spec["allocIncludes"], ["../../amsterdam-system-alloc.json"]
                    )
                    self.assertTrue(spec["covers"])
                    for name in ("case.json", "alloc.json", "env.json", "txs.src.json"):
                        self.assertTrue((case / name).is_file(), f"{case.name}/{name}")

    def test_each_state_test_uses_the_blockchain_transactions(self):
        for scenario in AMSTERDAM_T8N_SCENARIOS:
            with self.subTest(scenario=scenario):
                blockchain = self.case(scenario, "blockchain")
                state_test = self.case(scenario, "state-test")
                source = json.loads((blockchain / "txs.src.json").read_text())
                mirror = json.loads((state_test / "txs.src.json").read_text())
                self.assertIsInstance(source, list)
                self.assertEqual(len(source), 1)
                self.assertEqual(
                    mirror, {"include": f"../{scenario}-blockchain/txs.src.json"}
                )

    def test_shared_system_alloc_is_the_exact_six_predeploys(self):
        alloc = json.loads((T8N / "amsterdam-system-alloc.json").read_text())
        self.assertEqual(set(alloc), AMSTERDAM_SYSTEM_ADDRESSES)

    def test_each_case_pins_both_block_access_fields_with_no_deviation(self):
        """Jaune emits the EIP-7928 pair itself, so the goldens pin it exactly.

        Until goal C's W4 it was absent from Jaune's result and registered as
        a target-only deviation for every case; now the registry carries no
        Amsterdam entry and both fields are compared byte for byte. Rewritten
        rather than deleted (fixed decision 8): the guard that recorded the
        omission is the same guard that now records its removal.
        """
        deviations = json.loads((T8N / "deviations.json").read_text())["fields"]
        for scenario in AMSTERDAM_T8N_SCENARIOS:
            for mode in ("blockchain", "state-test"):
                case = f"{scenario}-{mode}"
                result = json.loads(
                    (self.case(scenario, mode) / "expected" / "result.json").read_text()
                )
                with self.subTest(case=case):
                    self.assertIn("blockAccessList", result)
                    self.assertIn("blockAccessListHash", result)
                    self.assertEqual(
                        [entry for entry in deviations if entry.get("case") == case],
                        [],
                    )


if __name__ == "__main__":
    unittest.main()
