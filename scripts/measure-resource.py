#!/usr/bin/env python3
"""Run one command in a measured child cgroup below Creme's Lean-only slice.

The controller stays in the outer contained job while the payload runs in a
stricter transient service. A tiny child shim keeps successful services alive
until the controller has read the live cgroup-v2 counters; an OOM ends the
whole child group, whose counters are sampled until the unit becomes inactive.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile
import time
import uuid


DEDICATED_SLICE_FRAGMENT = "/creme.slice/creme-lean.slice/"
REQUIRED_COUNTERS = (
    "memory.current",
    "memory.peak",
    "memory.swap.current",
    "memory.swap.peak",
    "memory.events",
    "memory.events.local",
    "memory.max",
    "memory.swap.max",
    "memory.high",
    "memory.oom.group",
)
ACTIVE_STATES = {"activating", "active", "deactivating"}


class MeasureError(RuntimeError):
    pass


def parse_bytes(value: str, *, allow_zero: bool = False) -> int:
    text = value.strip().lower()
    multipliers = {"k": 1024, "m": 1024**2, "g": 1024**3}
    if text and text[-1:] in multipliers:
        number, multiplier = text[:-1], multipliers[text[-1]]
    else:
        number, multiplier = text, 1
    if not number.isdigit() or (int(number) == 0 and not allow_zero):
        qualifier = "nonnegative" if allow_zero else "positive"
        raise argparse.ArgumentTypeError(
            f"expected {qualifier} bytes or K/M/G value, got {value!r}"
        )
    return int(number) * multiplier


def parse_swap_bytes(value: str) -> int:
    return parse_bytes(value, allow_zero=True)


def parse_flat_counters(text: str) -> dict[str, int]:
    result: dict[str, int] = {}
    for raw in text.splitlines():
        fields = raw.split()
        if len(fields) != 2 or not fields[1].isdigit():
            raise MeasureError(f"malformed cgroup counter row: {raw!r}")
        result[fields[0]] = int(fields[1])
    return result


def own_cgroup_path() -> str:
    for raw in Path("/proc/self/cgroup").read_text(encoding="utf-8").splitlines():
        fields = raw.split(":", 2)
        if len(fields) == 3 and fields[0] == "0":
            return fields[2]
    raise MeasureError("cgroup-v2 membership is unavailable")


def require_dedicated_child(path: str) -> None:
    if DEDICATED_SLICE_FRAGMENT not in path:
        raise MeasureError(f"scope is outside the dedicated Lean-only slice: {path}")


def cgroup_dir(path: str) -> Path:
    require_dedicated_child(path)
    directory = Path("/sys/fs/cgroup") / path.lstrip("/")
    if not directory.is_dir():
        raise MeasureError(f"cgroup directory is unavailable: {directory}")
    return directory


def read_value(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8").strip()
    except FileNotFoundError as error:
        raise MeasureError(f"required live cgroup file disappeared: {path}") from error


def read_snapshot(directory: Path) -> dict[str, object]:
    missing = [name for name in REQUIRED_COUNTERS if not (directory / name).is_file()]
    if missing:
        raise MeasureError(f"required live cgroup counters are missing: {', '.join(missing)}")
    return {
        "memory_current": int(read_value(directory / "memory.current")),
        "memory_peak": int(read_value(directory / "memory.peak")),
        "memory_swap_current": int(read_value(directory / "memory.swap.current")),
        "memory_swap_peak": int(read_value(directory / "memory.swap.peak")),
        "memory_events": parse_flat_counters(read_value(directory / "memory.events")),
        "memory_events_local": parse_flat_counters(
            read_value(directory / "memory.events.local")
        ),
        "memory_max": read_value(directory / "memory.max"),
        "memory_swap_max": read_value(directory / "memory.swap.max"),
        "memory_high": read_value(directory / "memory.high"),
        "memory_oom_group": read_value(directory / "memory.oom.group"),
    }


def show_unit(unit: str) -> dict[str, str]:
    properties = (
        "ActiveState",
        "SubState",
        "Result",
        "ExecMainCode",
        "ExecMainStatus",
        "ControlGroup",
    )
    command = ["systemctl", "--user", "show", unit]
    for prop in properties:
        command.extend(("--property", prop))
    completed = subprocess.run(command, check=False, text=True, capture_output=True)
    if completed.returncode != 0:
        raise MeasureError(
            f"cannot inspect transient unit {unit}: {completed.stderr.strip()}"
        )
    result: dict[str, str] = {}
    for raw in completed.stdout.splitlines():
        key, separator, value = raw.partition("=")
        if separator:
            result[key] = value
    return result


def normalized_returncode(returncode: int) -> int:
    if returncode < 0:
        return 128 + (-returncode)
    return min(returncode, 255)


def child_main(arguments: list[str]) -> int:
    if len(arguments) < 4 or arguments[3] != "--":
        raise MeasureError("invalid internal child invocation")
    done_path, acknowledge_path, result_path = map(Path, arguments[:3])
    command = arguments[4:]
    if not command:
        raise MeasureError("internal child invocation has no payload")
    completed = subprocess.run(command, check=False)
    returncode = normalized_returncode(completed.returncode)
    result_path.write_text(f"{returncode}\n", encoding="utf-8")
    done_path.write_text("done\n", encoding="utf-8")
    deadline = time.monotonic() + 60
    while not acknowledge_path.exists():
        if time.monotonic() >= deadline:
            raise MeasureError("controller did not acknowledge terminal counters")
        time.sleep(0.01)
    return returncode


def validate_requested_limits(memory_max: int, swap_max: int) -> None:
    outer = cgroup_dir(own_cgroup_path())
    outer_max = read_value(outer / "memory.max")
    outer_swap = read_value(outer / "memory.swap.max")
    if outer_max == "max" or not outer_max.isdigit():
        raise MeasureError(f"outer contained memory.max is not finite: {outer_max}")
    if outer_swap == "max" or not outer_swap.isdigit():
        raise MeasureError(f"outer contained memory.swap.max is not finite: {outer_swap}")
    if memory_max > int(outer_max):
        raise MeasureError(
            f"requested memory limit {memory_max} exceeds outer boundary {outer_max}"
        )
    if swap_max > int(outer_swap):
        raise MeasureError(
            f"requested swap limit {swap_max} exceeds outer boundary {outer_swap}"
        )


def require_readback(snapshot: dict[str, object], memory_max: int, swap_max: int) -> None:
    expected = {
        "memory_max": str(memory_max),
        "memory_swap_max": str(swap_max),
        "memory_high": "max",
        "memory_oom_group": "1",
    }
    mismatches = {
        key: (snapshot[key], value)
        for key, value in expected.items()
        if snapshot[key] != value
    }
    if mismatches:
        raise MeasureError(f"transient scope limit readback mismatch: {mismatches}")


def oom_count(snapshot: dict[str, object] | None) -> int:
    if snapshot is None:
        return 0
    local = snapshot["memory_events_local"]
    assert isinstance(local, dict)
    return int(local.get("oom_kill", 0))


def controller_main(arguments: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--memory-max", required=True, type=parse_bytes)
    parser.add_argument("--swap-max", required=True, type=parse_swap_bytes)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--timeout-seconds", type=float, default=7200.0)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(arguments)
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a command is required after --")
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    if shutil.which("systemd-run") is None or shutil.which("systemctl") is None:
        raise MeasureError("systemd-run and systemctl are required")

    validate_requested_limits(args.memory_max, args.swap_max)
    started = time.monotonic()
    unit = f"jaune-resource-{os.getpid()}-{uuid.uuid4().hex[:10]}.service"
    scratch = Path(tempfile.mkdtemp(prefix="jaune-resource-", dir="/tmp"))
    done_path = scratch / "done"
    acknowledge_path = scratch / "acknowledge"
    result_path = scratch / "returncode"
    script = str(Path(__file__).resolve())
    launch = [
        "systemd-run",
        "--user",
        "--wait",
        "--pipe",
        "--quiet",
        f"--unit={unit}",
        "--slice=creme-lean.slice",
        "--property=MemoryAccounting=yes",
        "--property=MemoryHigh=infinity",
        f"--property=MemoryMax={args.memory_max}",
        f"--property=MemorySwapMax={args.swap_max}",
        "--property=OOMScoreAdjust=500",
        "--property=OOMPolicy=kill",
        sys.executable,
        script,
        "__child__",
        str(done_path),
        str(acknowledge_path),
        str(result_path),
        "--",
        *command,
    ]

    process: subprocess.Popen[bytes] | None = None
    directory: Path | None = None
    last_snapshot: dict[str, object] | None = None
    samples = 0
    timed_out = False
    unit_state: dict[str, str] = {}
    try:
        process = subprocess.Popen(launch)
        control_group = ""
        for _ in range(1000):
            try:
                unit_state = show_unit(unit)
            except MeasureError:
                if process.poll() is not None:
                    break
                time.sleep(0.01)
                continue
            control_group = unit_state.get("ControlGroup", "")
            if control_group:
                directory = cgroup_dir(control_group)
                break
            if process.poll() is not None:
                break
            time.sleep(0.01)
        if directory is None:
            raise MeasureError(f"transient unit never exposed its cgroup: {unit_state}")

        while True:
            try:
                last_snapshot = read_snapshot(directory)
                samples += 1
                require_readback(last_snapshot, args.memory_max, args.swap_max)
            except MeasureError:
                if directory.exists():
                    raise
            if done_path.exists():
                if directory.exists():
                    last_snapshot = read_snapshot(directory)
                    samples += 1
                    require_readback(last_snapshot, args.memory_max, args.swap_max)
                acknowledge_path.write_text("acknowledged\n", encoding="utf-8")
                break
            unit_state = show_unit(unit)
            if unit_state.get("ActiveState") not in ACTIVE_STATES:
                if directory.exists():
                    last_snapshot = read_snapshot(directory)
                    samples += 1
                    require_readback(last_snapshot, args.memory_max, args.swap_max)
                break
            if time.monotonic() - started > args.timeout_seconds:
                timed_out = True
                subprocess.run(("systemctl", "--user", "stop", unit), check=False)
                break
            time.sleep(0.01)

        try:
            systemd_run_rc = process.wait(timeout=60)
        except subprocess.TimeoutExpired as error:
            subprocess.run(("systemctl", "--user", "stop", unit), check=False)
            raise MeasureError("transient unit did not finish after terminal sampling") from error
        unit_state = show_unit(unit)
        payload_rc = None
        if result_path.is_file():
            text = result_path.read_text(encoding="utf-8").strip()
            payload_rc = int(text) if text.isdigit() else None
        event_oom = oom_count(last_snapshot)
        result = {
            "schema": 1,
            "unit": unit,
            "command": command,
            "memory_max": args.memory_max,
            "swap_max": args.swap_max,
            "elapsed_seconds": round(time.monotonic() - started, 6),
            "samples": samples,
            "payload_returncode": payload_rc,
            "systemd_run_returncode": systemd_run_rc,
            "timed_out": timed_out,
            "oom_kill_count": event_oom,
            "unit_state": unit_state,
            "terminal_snapshot": last_snapshot,
            "verdict": (
                "PASS"
                if payload_rc == 0 and systemd_run_rc == 0 and not timed_out and event_oom == 0
                else "RESOURCE_EVENT"
                if event_oom > 0 or unit_state.get("Result") == "oom-kill"
                else "FAIL"
            ),
        }
        encoded = json.dumps(result, sort_keys=True)
        print(f"RESOURCE {encoded}")
        if args.json_out is not None:
            args.json_out.parent.mkdir(parents=True, exist_ok=True)
            args.json_out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        if result["verdict"] == "PASS":
            return 0
        return payload_rc if isinstance(payload_rc, int) and payload_rc != 0 else 1
    finally:
        if not acknowledge_path.exists() and done_path.exists():
            acknowledge_path.write_text("cleanup\n", encoding="utf-8")
        subprocess.run(("systemctl", "--user", "stop", unit), check=False, capture_output=True)
        subprocess.run(
            ("systemctl", "--user", "reset-failed", unit),
            check=False,
            capture_output=True,
        )
        shutil.rmtree(scratch, ignore_errors=True)


def main() -> int:
    try:
        if sys.argv[1:2] == ["__child__"]:
            return child_main(sys.argv[2:])
        return controller_main(sys.argv[1:])
    except (MeasureError, OSError, ValueError) as error:
        print(f"MEASUREMENT ERROR — {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
