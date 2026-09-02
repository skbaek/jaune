import argparse
import importlib.util
from pathlib import Path
import unittest


SCRIPT = Path(__file__).parents[1] / "measure-resource.py"
SPEC = importlib.util.spec_from_file_location("measure_resource", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class MeasureResourceTests(unittest.TestCase):
    def test_parse_bytes(self):
        self.assertEqual(MODULE.parse_bytes("4096"), 4096)
        self.assertEqual(MODULE.parse_bytes("4G"), 4 * 1024**3)
        self.assertEqual(MODULE.parse_bytes("64m"), 64 * 1024**2)

    def test_parse_bytes_rejects_zero_and_noise(self):
        for value in ("0", "-1", "4GiB", "word"):
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                MODULE.parse_bytes(value)

    def test_parse_swap_bytes_accepts_zero_only(self):
        self.assertEqual(MODULE.parse_swap_bytes("0"), 0)
        self.assertEqual(MODULE.parse_swap_bytes("1G"), 1024**3)
        for value in ("-1", "4GiB", "word"):
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                MODULE.parse_swap_bytes(value)

    def test_flat_counter_parser(self):
        self.assertEqual(
            MODULE.parse_flat_counters("low 2\nhigh 3\noom 1\noom_kill 1\n"),
            {"low": 2, "high": 3, "oom": 1, "oom_kill": 1},
        )

    def test_dedicated_slice_membership(self):
        MODULE.require_dedicated_child(
            "/user.slice/user-1001.slice/user@1001.service/creme.slice/"
            "creme-lean.slice/jaune-resource.scope"
        )
        for path in (
            "/user.slice/user-1001.slice/user@1001.service/app.slice/x.scope",
            "/user.slice/user-1001.slice/user@1001.service",
            "/",
        ):
            with self.subTest(path=path), self.assertRaises(MODULE.MeasureError):
                MODULE.require_dedicated_child(path)

    def test_oom_count_uses_local_events(self):
        snapshot = {"memory_events_local": {"oom": 2, "oom_kill": 1}}
        self.assertEqual(MODULE.oom_count(snapshot), 1)
        self.assertEqual(MODULE.oom_count(None), 0)


if __name__ == "__main__":
    unittest.main()
