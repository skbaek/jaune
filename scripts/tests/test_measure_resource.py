import argparse
import hashlib
import importlib.util
import os
from pathlib import Path
import tempfile
import unittest
from unittest import mock


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
        dedicated = (
            "/user.slice/user-1001.slice/user@1001.service/creme.slice/"
            "creme-lean.slice/jaune-resource.scope"
        )
        self.assertTrue(MODULE.in_dedicated_slice(dedicated))
        MODULE.require_admitted_containment(dedicated)
        for path in (
            "/user.slice/user-1001.slice/user@1001.service/app.slice/x.scope",
            "/user.slice/user-1001.slice/user@1001.service",
            "/",
        ):
            with self.subTest(path=path):
                self.assertFalse(MODULE.in_dedicated_slice(path))

    def test_admitted_containment_accepts_only_a_transient_leaf(self):
        # The user-scope shape used where no dedicated system slice exists.
        MODULE.require_admitted_containment(
            "/user.slice/user-1000.slice/user@1000.service/app.slice/"
            "run-p1-i1.scope"
        )
        MODULE.require_admitted_containment(
            "/user.slice/user-1000.slice/user@1000.service/app.slice/"
            "jaune-resource.service"
        )
        for path in (
            "/",
            "",
            "/user.slice",
            "/user.slice/user-1000.slice",
            # The login session's own manager is never a measurement scope.
            "/user.slice/user-1000.slice/user@1000.service",
            "/user.slice/user-1000.slice/session-3.scope/nested",
        ):
            with self.subTest(path=path), self.assertRaises(MODULE.MeasureError):
                MODULE.require_admitted_containment(path)

    def test_in_scope_request_must_equal_its_own_boundary(self):
        # In-scope containment measures the scope the controller is already in,
        # so a request below that scope's limit would be a budget the kernel
        # never enforces.
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            leaf = root / "app.slice" / "run-p1-i1.scope"
            leaf.mkdir(parents=True)
            (leaf / "memory.max").write_text(str(6 * 1024**3), encoding="utf-8")
            (leaf / "memory.swap.max").write_text("0", encoding="utf-8")
            with mock.patch.object(MODULE, "CGROUP_ROOT", root):
                MODULE.validate_requested_limits(
                    "/app.slice/run-p1-i1.scope", 6 * 1024**3, 0
                )
                with self.assertRaises(MODULE.MeasureError):
                    MODULE.validate_requested_limits(
                        "/app.slice/run-p1-i1.scope", 4 * 1024**3, 0
                    )

    def test_an_infinite_boundary_is_refused(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            leaf = root / "app.slice" / "run-p1-i1.scope"
            leaf.mkdir(parents=True)
            (leaf / "memory.max").write_text("max", encoding="utf-8")
            (leaf / "memory.swap.max").write_text("max", encoding="utf-8")
            with (
                mock.patch.object(MODULE, "CGROUP_ROOT", root),
                self.assertRaises(MODULE.MeasureError),
            ):
                MODULE.validate_requested_limits(
                    "/app.slice/run-p1-i1.scope", 1024**3, 0
                )

    def test_schema_is_two(self):
        self.assertEqual(MODULE.SCHEMA_VERSION, 2)

    def test_file_identity_hashes_the_artefact_under_measurement(self):
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "jaune"
            path.write_bytes(b"binary\n")
            identity = MODULE.file_identity(path, "executable")
            self.assertTrue(identity["available"])
            self.assertEqual(
                identity["sha256"], hashlib.sha256(b"binary\n").hexdigest()
            )
            self.assertEqual(identity["size_bytes"], 7)

    def test_an_undeclared_or_unreadable_artefact_says_so_explicitly(self):
        # The schema-boundary control: a field whose source is unavailable
        # carries an explicit marker and a reason. It never disappears, because
        # a missing field and an unavailable source read identically later.
        undeclared = MODULE.file_identity(None, "fixture manifest")
        self.assertEqual(undeclared["available"], False)
        self.assertIn("fixture manifest", undeclared["reason"])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "binary"
            path.write_bytes(b"x")
            os.chmod(path, 0o000)
            try:
                identity = MODULE.file_identity(path, "executable")
            finally:
                os.chmod(path, 0o600)
            self.assertEqual(identity["available"], False)
            self.assertIn("unreadable", identity["reason"])

    def test_boot_and_session_identity_are_recorded_or_explained(self):
        for identity in (MODULE.boot_identity(), MODULE.session_identity()):
            with self.subTest(identity=identity):
                self.assertIn("available", identity)
                if identity["available"]:
                    self.assertGreater(len(identity), 1)
                else:
                    self.assertTrue(identity["reason"])

    def test_session_identity_reports_an_absent_source_rather_than_omitting_it(self):
        with (
            mock.patch.object(MODULE.shutil, "which", return_value=None),
            mock.patch.dict(MODULE.os.environ, {}, clear=True),
            mock.patch.object(MODULE, "read_optional", return_value=None),
        ):
            identity = MODULE.session_identity()
        self.assertEqual(identity["available"], False)
        self.assertEqual(identity["reason"], "loginctl is not installed")

    def test_outer_oom_counters_cover_every_ancestor_outside_the_leaf(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            leaf = root / "user.slice" / "user@1001.service" / "run-p1.scope"
            leaf.mkdir(parents=True)
            (leaf / "memory.events").write_text("oom_kill 9\n", encoding="utf-8")
            for ancestor in (root, root / "user.slice",
                             root / "user.slice" / "user@1001.service"):
                (ancestor / "memory.events").write_text(
                    "low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\n", encoding="utf-8"
                )
            with mock.patch.object(MODULE, "CGROUP_ROOT", root):
                counters = MODULE.outer_oom_counters(
                    "/user.slice/user@1001.service/run-p1.scope"
                )
            self.assertEqual(
                sorted(counters),
                ["/", "/user.slice", "/user.slice/user@1001.service"],
            )
            # The measured leaf's own kill is inside the boundary, not outside.
            self.assertNotIn(
                "/user.slice/user@1001.service/run-p1.scope", counters
            )
            self.assertEqual(counters["/user.slice/user@1001.service"]["oom_kill"], 0)

    def test_an_outer_oom_kill_is_visible_rather_than_silently_absent(self):
        clean = {"oom": 0, "oom_kill": 0, "oom_group_kill": 0}
        killed = {"oom": 1, "oom_kill": 1, "oom_group_kill": 0}
        self.assertIs(
            MODULE.outer_oom_increased({"/user.slice": clean}, {"/user.slice": clean}),
            False,
        )
        self.assertIs(
            MODULE.outer_oom_increased({"/user.slice": clean}, {"/user.slice": killed}),
            True,
        )
        # Undecidable is neither True nor False: an unreadable counter must not
        # be reported as "the desktop survived".
        unavailable = {"available": False, "reason": "unreadable"}
        self.assertIsNone(
            MODULE.outer_oom_increased(
                {"/": unavailable}, {"/": unavailable}
            )
        )

    def test_a_launcherless_run_still_classifies(self):
        # In-scope mode has no systemd-run process between controller and
        # payload, so there is no third exit status to require.
        events = {event: 0 for event in MODULE.RESOURCE_EVENT_KEYS}
        self.assertEqual(
            MODULE.classify_verdict(0, None, False, events, "success"), "PASS"
        )
        self.assertEqual(
            MODULE.classify_verdict(1, None, False, events, "success"), "FAIL"
        )


    def test_oom_count_uses_local_events(self):
        snapshot = {"memory_events_local": {"oom": 2, "oom_kill": 1}}
        self.assertEqual(MODULE.oom_count(snapshot), 1)
        self.assertEqual(MODULE.oom_count(None), 0)

    def test_every_local_memory_boundary_event_is_fatal(self):
        for key in MODULE.RESOURCE_EVENT_KEYS:
            with self.subTest(key=key):
                events = {event: 0 for event in MODULE.RESOURCE_EVENT_KEYS}
                events[key] = 1
                self.assertEqual(
                    MODULE.classify_verdict(0, 0, False, events, "success"),
                    "RESOURCE_EVENT",
                )

    def test_clean_completion_is_the_only_pass(self):
        events = {event: 0 for event in MODULE.RESOURCE_EVENT_KEYS}
        self.assertEqual(
            MODULE.classify_verdict(0, 0, False, events, "success"), "PASS"
        )
        self.assertEqual(
            MODULE.classify_verdict(0, 0, True, events, "success"), "FAIL"
        )

    def test_sampling_uses_cumulative_counters_not_a_busy_poll(self):
        self.assertGreaterEqual(MODULE.SAMPLE_INTERVAL_SECONDS, 0.1)

    def test_limit_readback_requires_inner_measurement_settings(self):
        snapshot = {
            "memory_max": "67108864",
            "memory_swap_max": "0",
            "memory_high": "max",
            "memory_oom_group": "0",
        }
        MODULE.require_readback(snapshot, 67108864, 0)
        snapshot["memory_oom_group"] = "1"
        with self.assertRaises(MODULE.MeasureError):
            MODULE.require_readback(snapshot, 67108864, 0)

    def test_boundary_probe_validates_chunk_size(self):
        for arguments in ([], ["0"], ["-1"], ["1", "2"], ["word"]):
            with self.subTest(arguments=arguments), self.assertRaises(MODULE.MeasureError):
                MODULE.boundary_probe_main(arguments)


if __name__ == "__main__":
    unittest.main()
