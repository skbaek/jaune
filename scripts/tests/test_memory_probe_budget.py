import argparse
import importlib.util
from pathlib import Path
import sys
import unittest
from unittest import mock


SCRIPT = Path(__file__).parents[1] / "memory_probe_budget.py"
SPEC = importlib.util.spec_from_file_location("memory_probe_budget", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class MemoryProbeBudgetTests(unittest.TestCase):
    def test_parse_bytes(self):
        self.assertEqual(MODULE.parse_bytes("4096"), 4096)
        self.assertEqual(MODULE.parse_bytes("256M"), 256 * 1024**2)
        for value in ("0", "-1", "256MiB", "word"):
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                MODULE.parse_bytes(value)

    def test_maxrss_unit_differs_by_platform(self):
        usage = mock.Mock(ru_maxrss=1024)
        with mock.patch.object(MODULE.platform, "system", return_value="Linux"):
            self.assertEqual(MODULE.maxrss_bytes(usage), 1024 * 1024)
        with mock.patch.object(MODULE.platform, "system", return_value="Darwin"):
            self.assertEqual(MODULE.maxrss_bytes(usage), 1024)

    def test_only_a_clean_in_budget_run_is_ok(self):
        self.assertEqual(
            MODULE.classify(
                returncode=0, killed_over_budget=False, timed_out=False, within=True
            ),
            "OK",
        )
        self.assertEqual(
            MODULE.classify(
                returncode=0, killed_over_budget=True, timed_out=False, within=False
            ),
            "OVER_BUDGET",
        )
        # A peak above the budget is over budget even if the watchdog never
        # fired, so a run that outgrew the budget between two samples is still
        # a failure rather than a pass.
        self.assertEqual(
            MODULE.classify(
                returncode=0, killed_over_budget=False, timed_out=False, within=False
            ),
            "OVER_BUDGET",
        )
        self.assertEqual(
            MODULE.classify(
                returncode=0, killed_over_budget=False, timed_out=True, within=True
            ),
            "TIMEOUT",
        )
        self.assertEqual(
            MODULE.classify(
                returncode=1, killed_over_budget=False, timed_out=False, within=True
            ),
            "FAILED",
        )

    def test_a_small_command_stays_within_a_generous_budget(self):
        record = MODULE.run([sys.executable, "-c", "pass"], 512 * 1024**2, 60.0)
        self.assertEqual(record["status"], "OK")
        self.assertEqual(record["returncode"], 0)
        self.assertLessEqual(record["peak_bytes"], 512 * 1024**2)

    def test_a_failing_command_is_not_a_pass(self):
        record = MODULE.run(
            [sys.executable, "-c", "raise SystemExit(3)"], 512 * 1024**2, 60.0
        )
        self.assertEqual(record["status"], "FAILED")
        self.assertEqual(record["returncode"], 3)

    def test_the_watchdog_stops_and_reports_an_over_budget_child(self):
        # The control this whole runner exists for: a child that grows past the
        # budget is killed and reported, not allowed to consume the machine.
        # It allocates in small steps so the kill lands close to the budget.
        grower = (
            "import time\n"
            "held = []\n"
            "for _ in range(400):\n"
            "    held.append(bytearray(2 * 1024 * 1024))\n"
            "    for index in range(0, len(held[-1]), 4096):\n"
            "        held[-1][index] = 1\n"
            "    time.sleep(0.002)\n"
        )
        record = MODULE.run([sys.executable, "-c", grower], 64 * 1024**2, 60.0)
        self.assertEqual(record["status"], "OVER_BUDGET")
        self.assertTrue(record["killed_over_budget"])
        self.assertGreater(record["peak_bytes"], 64 * 1024**2 // 2)
        self.assertNotEqual(record["returncode"], 0)

    def test_the_record_names_its_mechanism_and_platform(self):
        record = MODULE.run([sys.executable, "-c", "pass"], 512 * 1024**2, 60.0)
        self.assertIn("ru_maxrss", record["mechanism"])
        self.assertEqual(record["platform"], MODULE.platform.system())


if __name__ == "__main__":
    unittest.main()
