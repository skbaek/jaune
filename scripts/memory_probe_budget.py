#!/usr/bin/env python3
"""Run one command under a peak-memory budget and report the peak it reached.

This is the measurement half of `scripts/check-memory-probe.sh`. It exists
because the bounded memory regression has to be assertable on an ordinary
developer machine, not only on the 16 GB Linux acceptance host: the property it
defends is "a deeply nested call path does not retain one calldata copy per
frame", and losing that property is visible in tens of megabytes long before it
is visible in gigabytes.

Two mechanisms, both POSIX and neither needing root, cgroups or a container:

  * **The assertion** is the child's peak resident set, taken from
    `getrusage(RUSAGE_CHILDREN).ru_maxrss` after the child is reaped. The unit
    differs by platform — kibibytes on Linux, bytes on macOS — and is converted
    here rather than assumed.
  * **The bound** is a sampling watchdog that kills the child as soon as its
    resident set crosses the budget. That is what makes a lost-property run
    safe: a regression that would grow to tens of gigabytes at depth 1024 is
    stopped a few megabytes above the budget and reported, instead of taking
    the machine down. The overshoot between samples is bounded by the
    allocation rate over one interval and is recorded, not hidden.

On Linux the watchdog reads `/proc/<pid>/statm`, which spawns nothing. On other
platforms it shells out to `ps`, whose own small resident set is also counted by
`RUSAGE_CHILDREN`; that can only overstate the reported peak, never understate
it, so the assertion stays sound.

Exit status: 0 iff the child exited 0 and its peak stayed within the budget;
1 on an over-budget, timed-out or failing child; 2 on a usage error.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import platform
import resource
import shutil
import subprocess
import sys
import time


SAMPLE_INTERVAL_SECONDS = 0.02
KIB = 1024


class ProbeError(RuntimeError):
    pass


def parse_bytes(value: str) -> int:
    text = value.strip().lower()
    multipliers = {"k": KIB, "m": KIB**2, "g": KIB**3}
    if text[-1:] in multipliers:
        number, multiplier = text[:-1], multipliers[text[-1]]
    else:
        number, multiplier = text, 1
    if not number.isdigit() or int(number) <= 0:
        raise argparse.ArgumentTypeError(
            f"expected a positive byte count or K/M/G value, got {value!r}"
        )
    return int(number) * multiplier


def maxrss_bytes(usage: resource.struct_rusage) -> int:
    """`ru_maxrss` is kibibytes on Linux and bytes on Darwin."""
    return usage.ru_maxrss * (1 if platform.system() == "Darwin" else KIB)


def linux_rss_bytes(pid: int) -> int | None:
    try:
        fields = Path(f"/proc/{pid}/statm").read_text(encoding="utf-8").split()
    except OSError:
        return None
    if len(fields) < 2 or not fields[1].isdigit():
        return None
    return int(fields[1]) * resource.getpagesize()


def ps_rss_bytes(pid: int) -> int | None:
    if shutil.which("ps") is None:
        return None
    completed = subprocess.run(
        ("ps", "-o", "rss=", "-p", str(pid)),
        check=False,
        text=True,
        capture_output=True,
    )
    text = completed.stdout.strip()
    if completed.returncode != 0 or not text.isdigit():
        return None
    return int(text) * KIB


def sample_rss_bytes(pid: int) -> int | None:
    if platform.system() == "Linux":
        return linux_rss_bytes(pid)
    return ps_rss_bytes(pid)


def classify(
    *, returncode: int, killed_over_budget: bool, timed_out: bool, within: bool
) -> str:
    if killed_over_budget or not within:
        return "OVER_BUDGET"
    if timed_out:
        return "TIMEOUT"
    if returncode != 0:
        return "FAILED"
    return "OK"


def run(
    command: list[str], budget_bytes: int, timeout_seconds: float
) -> dict[str, object]:
    before = maxrss_bytes(resource.getrusage(resource.RUSAGE_CHILDREN))
    started = time.monotonic()
    process = subprocess.Popen(command)
    observed = 0
    samples = 0
    killed_over_budget = False
    timed_out = False
    try:
        while process.poll() is None:
            current = sample_rss_bytes(process.pid)
            if current is not None:
                samples += 1
                observed = max(observed, current)
                if current > budget_bytes:
                    killed_over_budget = True
                    process.kill()
                    break
            if time.monotonic() - started > timeout_seconds:
                timed_out = True
                process.kill()
                break
            time.sleep(SAMPLE_INTERVAL_SECONDS)
        process.wait()
    finally:
        if process.poll() is None:
            process.kill()
            process.wait()
    after = maxrss_bytes(resource.getrusage(resource.RUSAGE_CHILDREN))
    # `ru_maxrss` for RUSAGE_CHILDREN is a high-water mark over every reaped
    # child, so a previous child in the same process would leave it standing;
    # taking the difference against the entry value is what keeps one run's
    # peak from being read as another's.
    peak = max(after - before if after > before else after, observed)
    return {
        "command": command,
        "budget_bytes": budget_bytes,
        "peak_bytes": peak,
        "peak_from_rusage_bytes": after,
        "peak_from_sampling_bytes": observed,
        "samples": samples,
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "returncode": process.returncode,
        "killed_over_budget": killed_over_budget,
        "timed_out": timed_out,
        "platform": platform.system(),
        "mechanism": (
            "getrusage(RUSAGE_CHILDREN).ru_maxrss, bounded by a "
            + ("/proc/<pid>/statm" if platform.system() == "Linux" else "ps -o rss=")
            + " sampling watchdog"
        ),
        "status": classify(
            returncode=process.returncode,
            killed_over_budget=killed_over_budget,
            timed_out=timed_out,
            within=peak <= budget_bytes,
        ),
    }


def main(arguments: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--budget-bytes", required=True, type=parse_bytes)
    parser.add_argument("--timeout-seconds", type=float, default=300.0)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(arguments)
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a command is required after --")
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")

    record = run(command, args.budget_bytes, args.timeout_seconds)
    print(f"PROBE {json.dumps(record, sort_keys=True)}")
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(
            json.dumps(record, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    return 0 if record["status"] == "OK" else 1


if __name__ == "__main__":
    raise SystemExit(main())
