import argparse
import importlib.util
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).parents[1] / "fixture_jobs.py"
SPEC = importlib.util.spec_from_file_location("fixture_jobs", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class FixtureJobsTests(unittest.TestCase):
    def test_parse_bytes(self):
        self.assertEqual(MODULE.parse_bytes("4096"), 4096)
        self.assertEqual(MODULE.parse_bytes("6G"), 6 * 1024**3)
        for value in ("0", "-1", "6GiB", "word"):
            with self.subTest(value=value), self.assertRaises(argparse.ArgumentTypeError):
                MODULE.parse_bytes(value)

    def test_cpuset_parser(self):
        self.assertEqual(MODULE.parse_cpuset("0-3,8,10-11"), 7)
        self.assertEqual(MODULE.parse_cpuset("2,2,3"), 2)
        for value in ("", "3-1", "x", "1-"):
            with self.subTest(value=value), self.assertRaises(MODULE.DetectionError):
                MODULE.parse_cpuset(value)

    def test_memory_reduces_auto_jobs(self):
        self.assertEqual(MODULE.choose_jobs(16, 8 * MODULE.GIB), 2)
        self.assertEqual(MODULE.choose_jobs(16, 6 * MODULE.GIB), 2)
        self.assertEqual(MODULE.choose_jobs(16, 4 * MODULE.GIB), 1)

    def test_cpu_caps_memory_capacity(self):
        self.assertEqual(MODULE.choose_jobs(2, 32 * MODULE.GIB), 2)
        self.assertEqual(MODULE.choose_jobs(1, 32 * MODULE.GIB), 1)

    def test_unknown_capacity_falls_back_to_one(self):
        self.assertEqual(MODULE.choose_jobs(None, None), 1)
        self.assertEqual(MODULE.choose_jobs(16, None), 1)

    def test_nested_cgroup_uses_tightest_remaining_limit(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            outer = root / "outer"
            child = outer / "child"
            child.mkdir(parents=True)
            (outer / "memory.max").write_text(str(8 * MODULE.GIB), encoding="utf-8")
            (outer / "memory.current").write_text(str(1 * MODULE.GIB), encoding="utf-8")
            (child / "memory.max").write_text(str(6 * MODULE.GIB), encoding="utf-8")
            (child / "memory.current").write_text(str(512 * 1024**2), encoding="utf-8")
            capacity = MODULE.linux_cgroup_memory_capacity(root, "/outer/child")
            self.assertEqual(capacity.value, 11 * MODULE.GIB // 2)
            self.assertEqual(MODULE.choose_jobs(16, capacity.value), 1)

    def test_cgroup_inactive_file_cache_is_reclaimable(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            child = root / "job"
            child.mkdir()
            (child / "memory.max").write_text(str(8 * MODULE.GIB), encoding="utf-8")
            (child / "memory.current").write_text(str(4 * MODULE.GIB), encoding="utf-8")
            (child / "memory.stat").write_text(
                f"anon {MODULE.GIB}\ninactive_file {3 * MODULE.GIB}\n",
                encoding="utf-8",
            )
            capacity = MODULE.linux_cgroup_memory_capacity(root, "/job")
            self.assertEqual(capacity.value, 7 * MODULE.GIB)
            self.assertEqual(MODULE.choose_jobs(16, capacity.value), 2)

    def test_cgroup_without_memory_controller_is_unverified(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            (root / "job").mkdir()
            with self.assertRaises(MODULE.DetectionError):
                MODULE.linux_cgroup_memory_capacity(root, "/job")

    def test_finite_cgroup_limit_requires_current_usage(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            child = root / "job"
            child.mkdir()
            (child / "memory.max").write_text(str(8 * MODULE.GIB), encoding="utf-8")
            with self.assertRaises(MODULE.DetectionError):
                MODULE.linux_cgroup_memory_capacity(root, "/job")

    def test_unverified_linux_cgroup_forces_one_worker(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            proc_cgroup = root / "self.cgroup"
            proc_cgroup.write_text("not-a-unified-membership\n", encoding="utf-8")
            with (
                mock.patch.object(MODULE.platform, "system", return_value="Linux"),
                mock.patch.object(
                    MODULE,
                    "linux_mem_available",
                    return_value=MODULE.Capacity(64 * MODULE.GIB, ("host",)),
                ),
            ):
                resources = MODULE.detect_resources(root, proc_cgroup)
            self.assertIsNone(resources.memory.value)
            self.assertEqual(resources.memory.sources, ("cgroup-v2:unverified",))
            self.assertEqual(
                MODULE.choose_jobs(resources.cpu.value, resources.memory.value), 1
            )

    def test_absent_boundary_file_is_not_an_unreadable_one(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            self.assertIsNone(MODULE.read_text(root / "memory.max"))
            unreadable = root / "memory.max"
            unreadable.write_text("max\n", encoding="utf-8")
            os.chmod(unreadable, 0o000)
            try:
                with self.assertRaises(MODULE.DetectionError):
                    MODULE.read_text(unreadable)
            finally:
                os.chmod(unreadable, 0o600)

    def _unreadable_leaf_tree(self, root: Path) -> Path:
        """An outer cgroup that says `max` over a leaf whose limit is refused."""
        outer = root / "outer"
        leaf = outer / "leaf"
        leaf.mkdir(parents=True)
        (outer / "memory.max").write_text("max\n", encoding="utf-8")
        (outer / "memory.current").write_text(str(MODULE.GIB), encoding="utf-8")
        leaf_max = leaf / "memory.max"
        leaf_max.write_text(str(6 * MODULE.GIB), encoding="utf-8")
        (leaf / "memory.current").write_text(str(MODULE.GIB), encoding="utf-8")
        os.chmod(leaf_max, 0o000)
        return leaf_max

    def _resolve_on_simulated_host(self, root: Path, proc_cgroup: Path) -> int:
        """64 GiB of host memory, 16 CPUs, cgroup answers taken from `root`."""
        with (
            mock.patch.object(MODULE.platform, "system", return_value="Linux"),
            mock.patch.object(
                MODULE,
                "linux_mem_available",
                return_value=MODULE.Capacity(64 * MODULE.GIB, ("host",)),
            ),
            mock.patch.object(MODULE.os, "cpu_count", return_value=16),
            mock.patch.object(
                MODULE.os, "sched_getaffinity", return_value=set(range(16))
            ),
        ):
            resources = MODULE.detect_resources(root, proc_cgroup)
        return MODULE.choose_jobs(resources.cpu.value, resources.memory.value)

    def test_unreadable_leaf_boundary_resolves_to_one_worker(self):
        # The documented promise is "an unreadable container boundary ...
        # conservatively resolves to one worker".  Before this fix the leaf's
        # refused `memory.max` was skipped, the permissive ancestor answered
        # `max`, and a 64 GiB / 16 CPU host resolved to 16 workers.  The second
        # half of this test restores only the pre-fix `read_text` and shows
        # exactly that, so the control cannot silently stop biting.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            proc_cgroup = root / "self.cgroup"
            proc_cgroup.write_text("0::/outer/leaf\n", encoding="utf-8")
            leaf_max = self._unreadable_leaf_tree(root)
            try:
                self.assertEqual(self._resolve_on_simulated_host(root, proc_cgroup), 1)

                def prefix_read_text(path):
                    try:
                        return path.read_text(encoding="utf-8").strip()
                    except (FileNotFoundError, PermissionError, OSError):
                        return None

                with mock.patch.object(MODULE, "read_text", prefix_read_text):
                    self.assertEqual(
                        self._resolve_on_simulated_host(root, proc_cgroup), 16
                    )
            finally:
                os.chmod(leaf_max, 0o600)

    def test_absent_leaf_boundary_still_reads_the_ancestor(self):
        # The conservative path must not swallow the ordinary case: a leaf that
        # publishes no memory controller at all is absent, not refused, and the
        # tightest readable ancestor still answers.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            proc_cgroup = root / "self.cgroup"
            proc_cgroup.write_text("0::/outer/leaf\n", encoding="utf-8")
            outer = root / "outer"
            (outer / "leaf").mkdir(parents=True)
            (outer / "memory.max").write_text(str(8 * MODULE.GIB), encoding="utf-8")
            (outer / "memory.current").write_text(str(MODULE.GIB), encoding="utf-8")
            self.assertEqual(self._resolve_on_simulated_host(root, proc_cgroup), 2)

    def test_macos_vm_stat_avoids_double_counting(self):
        capacity = MODULE.parse_macos_vm_stat(
            "Mach Virtual Memory Statistics: (page size of 4096 bytes)\n"
            "Pages free:                               10.\n"
            "Pages inactive:                           20.\n"
            "Pages speculative:                         7.\n"
            "Pages purgeable:                           5.\n"
        )
        self.assertEqual(capacity.value, 30 * 4096)
        self.assertEqual(capacity.sources, ("vm_stat:free+inactive",))

    def test_cpu_quota_and_cpuset_are_both_considered(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            child = root / "job"
            child.mkdir()
            (child / "cpuset.cpus.effective").write_text("0-7", encoding="utf-8")
            (child / "cpu.max").write_text("250000 100000", encoding="utf-8")
            capacity = MODULE.linux_cgroup_cpu_capacity(root, "/job")
            self.assertEqual(capacity.value, 3)


if __name__ == "__main__":
    unittest.main()
