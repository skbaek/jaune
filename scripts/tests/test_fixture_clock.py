"""The real parallel fixture helper uses a validated monotonic interval."""
import importlib.util
import json
import math
import os
from pathlib import Path
import subprocess
import tempfile
import unittest


SCRIPTS = Path(__file__).resolve().parents[1]
HELPER = Path(os.environ.get("JAUNE_TEST_FIXTURE_RUNNER", SCRIPTS / "run-fixture.sh"))

# Inject adjustable wall time and independent monotonic readings into the real
# Perl invocations. This never changes the host clock or the guard/alarm code.
CLOCK_CONTROL = r'''
package FixtureClockControl;
use Time::HiRes ();
no warnings 'redefine';
sub tick {
  my ($kind) = @_;
  my $path = "$ENV{FIXTURE_CLOCK_STATE}.$kind";
  my $n = 0;
  if (open my $in, '<', $path) { $n = <$in>; close $in; }
  open my $out, '>', $path or die "clock counter: $!";
  print $out ++$n; close $out;
  return $n;
}
CHECK {
*Time::HiRes::time = sub { return tick('wall') == 1 ? 200 : 100; };
*Time::HiRes::clock_gettime = sub {
  my $n = tick('monotonic');
  my $mode = $ENV{FIXTURE_CLOCK_MODE};
  die "injected clock read failure\n"
    if ($mode eq 'fail_start' && $n == 1) || ($mode eq 'fail_stop' && $n == 2);
  return -1 if $mode eq 'negative';
  return 'NaN' if $mode eq 'nonfinite';
  return $n == 1 ? 10 : 9 if $mode eq 'backward';
  return $n == 1 ? 10 : 10.25;
};
*main::time = \&Time::HiRes::time;
*main::clock_gettime = \&Time::HiRes::clock_gettime;
}
1;
'''


class FixtureClock(unittest.TestCase):
    def invoke(self, *, fixture_exit=0, mode=None, guard=5, sleep=False):
        with tempfile.TemporaryDirectory(prefix="jaune-fixture-clock-") as temporary:
            root = Path(temporary)
            output = root / "out"
            output.mkdir()
            marker = root / "executed"
            fixture = root / "fixture"
            fixture.write_text("#!/bin/sh\nprintf executed > '" + str(marker) + "'\n"
                               + ("exec sleep 3\n" if sleep else "")
                               + f"exit {fixture_exit}\n")
            fixture.chmod(0o755)
            env = os.environ.copy()
            # Only this synthetic child receives the clock injection.
            if mode is not None:
                (root / "FixtureClockControl.pm").write_text(CLOCK_CONTROL)
                env.update(PERL5LIB=str(root), PERL5OPT="-MFixtureClockControl",
                           FIXTURE_CLOCK_STATE=str(root / "counter"), FIXTURE_CLOCK_MODE=mode)
            command = [str(HELPER), str(fixture), str(guard), str(output), "1",
                       "synthetic.json", "Berlin", "synthetic.json"]
            result = subprocess.run(command, env=env, capture_output=True, text=True, check=False)
            line = output / "1.line"
            record = {"command": command, "exit": result.returncode,
                      "stdout": result.stdout, "stderr": result.stderr,
                      "fixture_executed": marker.exists(),
                      "line": line.read_text() if line.exists() else None,
                      "guard_tripped": (output / ".guard-tripped").exists()}
            capture = os.environ.get("JAUNE_CLOCK_TEST_CAPTURE")
            if capture:
                Path(capture).write_text(json.dumps(record, indent=2) + "\n")
            return record

    def valid_report(self, record, status):
        self.assertTrue(record["fixture_executed"], record)
        self.assertEqual(record["exit"], 0, record)
        fields = record["line"].strip().split("\t")
        self.assertEqual((fields[0], fields[2]), (status, "synthetic.json"), record)
        elapsed = float(fields[1].removesuffix("s"))
        self.assertTrue(math.isfinite(elapsed), record)
        self.assertGreaterEqual(elapsed, 0, "nonnegative elapsed: " + repr(record))
        # Use the unchanged production parser, not a weaker test-only format.
        spec = importlib.util.spec_from_file_location("fixture_baseline_parser", SCRIPTS / "check-legacy-baseline.py")
        module = importlib.util.module_from_spec(spec)
        import sys
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        with tempfile.TemporaryDirectory() as temporary:
            report = Path(temporary) / "report.tsv"
            report.write_text(record["line"])
            parsed = module.read_report(report)
            self.assertEqual([(row.status, row.path) for row in parsed], [(status, "synthetic.json")])
        return elapsed

    def test_real_clock_pass_and_fail(self):
        self.valid_report(self.invoke(), "PASS")
        self.valid_report(self.invoke(fixture_exit=7), "FAIL")

    def test_wall_clock_rollback_uses_monotonic_elapsed(self):
        self.assertEqual(self.valid_report(self.invoke(mode="rollback"), "PASS"), 0.25)

    def test_failed_or_invalid_clock_has_no_classification(self):
        for mode in ["fail_start", "fail_stop", "negative", "nonfinite", "backward"]:
            with self.subTest(mode=mode):
                record = self.invoke(mode=mode)
                self.assertNotEqual(record["exit"], 0, record)
                self.assertIsNone(record["line"], record)
                self.assertFalse(record["guard_tripped"], record)
                self.assertIn("HARNESS ERROR", record["stderr"])
                self.assertEqual(record["fixture_executed"], mode in ["fail_stop", "backward"], record)

    def test_guard_still_has_no_classification(self):
        record = self.invoke(guard=1, sleep=True)
        self.assertEqual(record["exit"], 255, record)
        self.assertTrue(record["guard_tripped"], record)
        self.assertIsNone(record["line"], record)


if __name__ == "__main__":
    unittest.main()
