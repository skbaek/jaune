#!/usr/bin/env python3
"""Run one command inside an admitted containment scope and record what it cost.

Two containment shapes are admitted, and the record always says which was used.

``nested-slice`` — the original shape. The controller stays in the outer
contained job below Creme's dedicated Lean-only slice while the payload runs in
a stricter transient service beside it. A tiny child shim keeps the service
alive until the controller has read the live cgroup-v2 counters, including after
the payload crosses the inner resource boundary.

``in-scope`` — the same discipline on a host that has no such system slice (a
user-session systemd with no root, for instance). The caller places the whole
measurement inside one transient cgroup of its own,

    systemd-run --user --scope -p MemoryMax=<budget> -p MemorySwapMax=<swap> -- \
        measure-resource.py --memory-max <budget> --swap-max <swap> -- <payload>

and the payload runs as a direct child inside it. What made the original shape
trustworthy was never the *name* of the slice: it was that the measured cgroup
is a finite transient boundary whose limits are read back live from the kernel
rather than assumed, and that it is never the session, user or root cgroup.
Both shapes are held to exactly that, and ``in-scope`` additionally refuses any
leaf that is not a transient ``.scope``/``.service``, refuses a user manager
service, and requires the leaf's own ``memory.max``/``memory.swap.max`` to equal
the requested budget exactly. Its measured peak *includes this controller*,
which is recorded and is conservative in the safe direction.

The kernel's peak and event counters are cumulative, so steady-state sampling
does not spawn a process or busy-poll.

Records are ``"schema": 2``. Schema 2 is additive over schema 1 and carries what
a resource-acceptance clause actually has to show:

  * ``identity`` — the sha256 of the executable under measurement and of the
    fixture manifest in force, so a record names the artefact it measured
    instead of resting on a working directory and a file name;
  * ``survival`` — boot identity, login-session identity, and the OOM counters
    of every cgroup ancestor *outside* the measured leaf, sampled before and
    after the run, with explicit ``changed``/``increased`` verdicts. A source
    that is unavailable on this host says so in its own field rather than
    disappearing from the record.

Schema 1 records are historical. Nothing here rewrites, re-hashes or
reinterprets one, and a schema-1 record is not a schema-2 record with fields
missing: it is a record from an instrument that could not carry them.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time
import uuid


SCHEMA_VERSION = 2
DEDICATED_SLICE_FRAGMENT = "/creme.slice/creme-lean.slice/"
CGROUP_ROOT = Path("/sys/fs/cgroup")
# A user manager's own service is a session boundary, not a measurement scope:
# containing a payload "in" it would contain the whole login session with it.
USER_MANAGER = re.compile(r"^user@\d+\.service$")
TRANSIENT_LEAF_SUFFIXES = (".scope", ".service")
HASH_CHUNK_BYTES = 1024 * 1024
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
RESOURCE_EVENT_KEYS = ("max", "oom", "oom_kill")
SAMPLE_INTERVAL_SECONDS = 0.25


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


def in_dedicated_slice(path: str) -> bool:
    return DEDICATED_SLICE_FRAGMENT in path


def require_admitted_containment(path: str) -> None:
    """Refuse any cgroup that is not an admitted containment scope.

    Admitted means one of two things, and nothing else: a child of Creme's
    dedicated Lean-only slice, or a transient ``.scope``/``.service`` leaf that
    is not a user manager's own service and not the root. The session, user and
    root cgroups are refused here; the finite-limit readback in
    `validate_requested_limits` and `require_readback` refuses everything else
    that has no real boundary.
    """
    if in_dedicated_slice(path):
        return
    relative = path.strip("/")
    if not relative:
        raise MeasureError("scope is the cgroup root, which contains the whole host")
    leaf = relative.rsplit("/", 1)[-1]
    if not leaf.endswith(TRANSIENT_LEAF_SUFFIXES):
        raise MeasureError(
            f"scope is not a transient .scope/.service containment leaf: {path}"
        )
    if USER_MANAGER.match(leaf):
        raise MeasureError(
            f"scope is a user manager service, which is the login session: {path}"
        )


def cgroup_dir(path: str) -> Path:
    require_admitted_containment(path)
    directory = CGROUP_ROOT / path.lstrip("/")
    if not directory.is_dir():
        raise MeasureError(f"cgroup directory is unavailable: {directory}")
    return directory


def read_optional(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8").strip()
    except OSError:
        return None


def unavailable(reason: str) -> dict[str, object]:
    return {"available": False, "reason": reason}


def file_identity(path: Path | None, role: str) -> dict[str, object]:
    """sha256 one artefact under measurement, or say plainly why there is none."""
    if path is None:
        return unavailable(f"no {role} was declared for this run")
    try:
        digest = hashlib.sha256()
        size = 0
        with path.open("rb") as handle:
            while chunk := handle.read(HASH_CHUNK_BYTES):
                digest.update(chunk)
                size += len(chunk)
    except OSError as error:
        return unavailable(f"{role} {path} is unreadable: {error}")
    return {
        "available": True,
        "path": str(path.resolve()),
        "sha256": digest.hexdigest(),
        "size_bytes": size,
    }


def boot_identity() -> dict[str, object]:
    """Boot and machine identity: a reboot between two samples is visible here."""
    boot_id = read_optional(Path("/proc/sys/kernel/random/boot_id"))
    machine_id = read_optional(Path("/etc/machine-id"))
    if boot_id is None:
        return unavailable("/proc/sys/kernel/random/boot_id is unreadable")
    return {
        "available": True,
        "boot_id": boot_id,
        "machine_id": machine_id if machine_id is not None else None,
    }


def session_identity() -> dict[str, object]:
    """Login-session identity, so "the desktop survived" is a checkable claim.

    `loginctl list-sessions` is the authority when logind is present; the audit
    session id and `XDG_SESSION_ID` are recorded alongside it because a process
    started outside any session (a system unit, a container init) has none, and
    that absence is itself worth recording rather than hiding.
    """
    audit = read_optional(Path("/proc/self/sessionid"))
    if audit == "4294967295":
        audit = None
    xdg = os.environ.get("XDG_SESSION_ID")
    sessions: list[str] | None = None
    reason = None
    if shutil.which("loginctl") is None:
        reason = "loginctl is not installed"
    else:
        completed = subprocess.run(
            ("loginctl", "list-sessions", "--no-legend", "--no-pager"),
            check=False,
            text=True,
            capture_output=True,
        )
        if completed.returncode != 0:
            reason = f"loginctl list-sessions failed: {completed.stderr.strip()}"
        else:
            sessions = sorted(
                " ".join(line.split())
                for line in completed.stdout.splitlines()
                if line.strip()
            )
    if sessions is None and audit is None and xdg is None:
        return unavailable(reason or "no login session source on this host")
    identity: dict[str, object] = {
        "available": True,
        "audit_session_id": audit,
        "xdg_session_id": xdg,
    }
    if sessions is None:
        identity["sessions"] = None
        identity["sessions_unavailable_reason"] = reason
    else:
        identity["sessions"] = sessions
        identity["sessions_sha256"] = hashlib.sha256(
            "\n".join(sessions).encode("utf-8")
        ).hexdigest()
    return identity


def outer_oom_counters(measured_relative_path: str) -> dict[str, object]:
    """`memory.events` for every cgroup ancestor OUTSIDE the measured leaf.

    Generic by construction rather than naming one host's `user@1001.service`:
    the ancestors of the measured leaf are exactly the scopes whose counters
    must not move while a contained payload is killed inside it.
    """
    relative = measured_relative_path.strip("/")
    ancestors: list[str] = []
    parts = relative.split("/") if relative else []
    for index in range(len(parts) - 1, -1, -1):
        ancestors.append("/" + "/".join(parts[:index]) if index else "/")
    counters: dict[str, object] = {}
    for ancestor in ancestors:
        directory = CGROUP_ROOT / ancestor.lstrip("/")
        text = read_optional(directory / "memory.events")
        if text is None:
            counters[ancestor] = unavailable("memory.events is unreadable")
            continue
        try:
            counters[ancestor] = parse_flat_counters(text)
        except MeasureError as error:
            counters[ancestor] = unavailable(str(error))
    return counters


def survival_snapshot(measured_relative_path: str) -> dict[str, object]:
    return {
        "boot": boot_identity(),
        "session": session_identity(),
        "outer_oom": outer_oom_counters(measured_relative_path),
    }


def outer_oom_increased(
    pre: dict[str, object], post: dict[str, object]
) -> bool | None:
    """True if any ancestor's OOM counters moved; None if it cannot be decided."""
    decided = False
    for scope, before in pre.items():
        after = post.get(scope)
        if not isinstance(before, dict) or not isinstance(after, dict):
            continue
        if before.get("available") is False or after.get("available") is False:
            continue
        decided = True
        for key in ("oom", "oom_kill", "oom_group_kill"):
            if int(after.get(key, 0)) > int(before.get(key, 0)):
                return True
    return False if decided else None


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


def boundary_probe_main(arguments: list[str]) -> int:
    if len(arguments) != 1 or not arguments[0].isdigit() or int(arguments[0]) <= 0:
        raise MeasureError("boundary probe expects one positive chunk size in bytes")
    chunk_size = int(arguments[0])
    retained: list[bytearray] = []
    while True:
        retained.append(bytearray(chunk_size))


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


def validate_requested_limits(own_path: str, memory_max: int, swap_max: int) -> None:
    """The containing scope must be a finite boundary that covers the request.

    In `nested-slice` mode the payload runs in a stricter transient service
    beside this controller, so the request must fit inside the boundary this
    controller is under. In `in-scope` mode the containing scope *is* the
    measured boundary, so the request must equal it exactly — a request smaller
    than the enclosing limit would be a budget nobody enforces.
    """
    outer = cgroup_dir(own_path)
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
    if not in_dedicated_slice(own_path):
        if memory_max != int(outer_max) or swap_max != int(outer_swap):
            raise MeasureError(
                "in-scope containment measures the enclosing scope itself, so the "
                f"request ({memory_max}/{swap_max}) must equal its boundary "
                f"({outer_max}/{outer_swap})"
            )


def require_readback(snapshot: dict[str, object], memory_max: int, swap_max: int) -> None:
    expected = {
        "memory_max": str(memory_max),
        "memory_swap_max": str(swap_max),
        "memory_high": "max",
        # The approved outer Creme boundary has memory.oom.group=1. Keeping the
        # inner measurement shim outside the payload's single-process event is
        # what makes the local counters available before systemd collection.
        "memory_oom_group": "0",
    }
    mismatches = {
        key: (snapshot[key], value)
        for key, value in expected.items()
        if snapshot[key] != value
    }
    if mismatches:
        raise MeasureError(f"transient scope limit readback mismatch: {mismatches}")


def oom_count(snapshot: dict[str, object] | None) -> int:
    return local_resource_events(snapshot)["oom_kill"]


def local_resource_events(snapshot: dict[str, object] | None) -> dict[str, int]:
    if snapshot is None:
        return {key: 0 for key in RESOURCE_EVENT_KEYS}
    local = snapshot["memory_events_local"]
    assert isinstance(local, dict)
    return {key: int(local.get(key, 0)) for key in RESOURCE_EVENT_KEYS}


def classify_verdict(
    payload_returncode: int | None,
    systemd_run_returncode: int | None,
    timed_out: bool,
    resource_events: dict[str, int],
    unit_result: str,
) -> str:
    """`systemd_run_returncode` is `None` in in-scope mode: there is no launcher
    process between the controller and the payload, so there is no third exit
    status to require. Every other condition is unchanged."""
    if any(resource_events.values()) or unit_result == "oom-kill":
        return "RESOURCE_EVENT"
    launcher_ok = systemd_run_returncode in (0, None)
    if payload_returncode == 0 and launcher_ok and not timed_out:
        return "PASS"
    return "FAIL"


def resolve_payload_binary(command: list[str]) -> Path | None:
    resolved = shutil.which(command[0])
    if resolved is None:
        return None
    path = Path(resolved)
    return path if path.is_file() else None


def run_nested_slice(
    args: argparse.Namespace, command: list[str], started: float
) -> dict[str, object]:
    """The original shape: a stricter transient service beside this controller."""
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
        f"--working-directory={Path.cwd()}",
        "--property=MemoryAccounting=yes",
        "--property=MemoryHigh=infinity",
        f"--property=MemoryMax={args.memory_max}",
        f"--property=MemorySwapMax={args.swap_max}",
        "--property=OOMScoreAdjust=500",
        "--property=OOMPolicy=continue",
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
    control_group = ""
    try:
        process = subprocess.Popen(launch)
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
            # systemd-run --wait exits when an unexpectedly terminated child
            # unit is collected.  The normal child cannot exit here because it
            # waits for acknowledge_path after writing done_path.  Polling the
            # local process is therefore sufficient and avoids launching a
            # systemctl subprocess for every sample of a long-running gate.
            if process.poll() is not None:
                if directory.exists():
                    last_snapshot = read_snapshot(directory)
                    samples += 1
                    require_readback(last_snapshot, args.memory_max, args.swap_max)
                break
            if time.monotonic() - started > args.timeout_seconds:
                timed_out = True
                subprocess.run(("systemctl", "--user", "stop", unit), check=False)
                break
            time.sleep(SAMPLE_INTERVAL_SECONDS)

        try:
            systemd_run_rc = process.wait(timeout=60)
        except subprocess.TimeoutExpired as error:
            subprocess.run(("systemctl", "--user", "stop", unit), check=False)
            raise MeasureError(
                "transient unit did not finish after terminal sampling"
            ) from error
        unit_state = show_unit(unit)
        payload_rc = None
        if result_path.is_file():
            text = result_path.read_text(encoding="utf-8").strip()
            payload_rc = int(text) if text.isdigit() else None
        return {
            "containment": {
                "mode": "nested-slice",
                "measured_cgroup": control_group,
                "controller_inside_measured_cgroup": False,
                "peak_reset_before_payload": False,
            },
            "unit": unit,
            "samples": samples,
            "timed_out": timed_out,
            "payload_returncode": payload_rc,
            "systemd_run_returncode": systemd_run_rc,
            "unit_state": unit_state,
            "terminal_snapshot": last_snapshot,
            "measured_relative_path": control_group,
        }
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


def run_in_scope(
    args: argparse.Namespace, command: list[str], own_path: str, started: float
) -> dict[str, object]:
    """Measure the transient scope this controller is already contained by.

    The payload is an ordinary child process, so the kernel's OOM killer acts
    on it inside the same boundary that would have contained a nested unit, and
    the leaf's cumulative `memory.peak`, `memory.swap.peak` and
    `memory.events.local` are read live exactly as before. The controller's own
    footprint is inside the measurement; that is recorded, and it can only make
    the reported peak larger than the payload's own.
    """
    directory = cgroup_dir(own_path)
    entry_snapshot = read_snapshot(directory)
    require_readback(entry_snapshot, args.memory_max, args.swap_max)
    entry_peak = int(entry_snapshot["memory_peak"])  # type: ignore[arg-type]
    # Linux 6.2 and later reset a cgroup's cumulative `memory.peak` on any
    # write. Where that works the reported peak is the payload's own rather
    # than the whole scope's history; where it does not, the record says so and
    # the peak is read as it stands, which can only overstate the payload.
    try:
        (directory / "memory.peak").write_text("0", encoding="utf-8")
    except OSError:
        peak_after_reset = entry_peak
    else:
        peak_after_reset = int(read_value(directory / "memory.peak"))
    peak_reset = peak_after_reset < entry_peak

    unit = own_path.strip("/").rsplit("/", 1)[-1]
    samples = 0
    timed_out = False
    last_snapshot: dict[str, object] | None = None
    process = subprocess.Popen(command)
    try:
        while True:
            last_snapshot = read_snapshot(directory)
            samples += 1
            require_readback(last_snapshot, args.memory_max, args.swap_max)
            if process.poll() is not None:
                break
            if time.monotonic() - started > args.timeout_seconds:
                timed_out = True
                process.kill()
                break
            time.sleep(SAMPLE_INTERVAL_SECONDS)
        process.wait(timeout=60)
    finally:
        if process.poll() is None:
            process.kill()
            process.wait(timeout=60)
    last_snapshot = read_snapshot(directory)
    samples += 1
    require_readback(last_snapshot, args.memory_max, args.swap_max)

    try:
        unit_state = show_unit(unit)
    except MeasureError:
        unit_state = {}
    return {
        "containment": {
            "mode": "in-scope",
            "measured_cgroup": own_path,
            "controller_inside_measured_cgroup": True,
            "peak_reset_before_payload": peak_reset,
            "peak_bytes_at_controller_entry": entry_peak,
            "peak_bytes_after_reset": peak_after_reset,
        },
        "unit": unit,
        "samples": samples,
        "timed_out": timed_out,
        "payload_returncode": normalized_returncode(process.returncode),
        "systemd_run_returncode": None,
        "unit_state": unit_state,
        "terminal_snapshot": last_snapshot,
        "measured_relative_path": own_path,
    }


def controller_main(arguments: list[str]) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--memory-max", required=True, type=parse_bytes)
    parser.add_argument("--swap-max", required=True, type=parse_swap_bytes)
    parser.add_argument("--json-out", type=Path)
    parser.add_argument("--timeout-seconds", type=float, default=7200.0)
    parser.add_argument(
        "--executable",
        type=Path,
        action="append",
        help="the built executable under measurement; hashed into the record. "
        "Repeatable. Omitting it is recorded as an explicit unavailable marker, "
        "not as a missing field.",
    )
    parser.add_argument(
        "--manifest",
        type=Path,
        action="append",
        help="the fixture manifest in force; hashed into the record. Repeatable.",
    )
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args(arguments)
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command:
        parser.error("a command is required after --")
    if args.timeout_seconds <= 0:
        parser.error("--timeout-seconds must be positive")
    if shutil.which("systemd-run") is None or shutil.which("systemctl") is None:
        raise MeasureError("systemd-run and systemctl are required")

    own_path = own_cgroup_path()
    require_admitted_containment(own_path)
    validate_requested_limits(own_path, args.memory_max, args.swap_max)
    nested = in_dedicated_slice(own_path)

    identity: dict[str, object] = {
        "executables": [
            file_identity(path, "executable")
            for path in (args.executable or [None])
        ],
        "fixture_manifests": [
            file_identity(path, "fixture manifest")
            for path in (args.manifest or [None])
        ],
        "payload_command_binary": file_identity(
            resolve_payload_binary(command), "payload command binary"
        ),
    }

    started = time.monotonic()
    pre_survival = survival_snapshot(own_path)
    if nested:
        outcome = run_nested_slice(args, command, started)
    else:
        outcome = run_in_scope(args, command, own_path, started)
    post_survival = survival_snapshot(str(outcome["measured_relative_path"]))

    resource_events = local_resource_events(outcome["terminal_snapshot"])
    unit_state = outcome["unit_state"]
    assert isinstance(unit_state, dict)
    pre_outer = pre_survival["outer_oom"]
    post_outer = post_survival["outer_oom"]
    assert isinstance(pre_outer, dict) and isinstance(post_outer, dict)
    result = {
        "schema": SCHEMA_VERSION,
        "containment": outcome["containment"],
        "unit": outcome["unit"],
        "command": command,
        "working_directory": str(Path.cwd()),
        "memory_max": args.memory_max,
        "swap_max": args.swap_max,
        "elapsed_seconds": round(time.monotonic() - started, 6),
        "samples": outcome["samples"],
        "payload_returncode": outcome["payload_returncode"],
        "systemd_run_returncode": outcome["systemd_run_returncode"],
        "timed_out": outcome["timed_out"],
        "oom_kill_count": resource_events["oom_kill"],
        "local_resource_events": resource_events,
        "unit_state": unit_state,
        "terminal_snapshot": outcome["terminal_snapshot"],
        "identity": identity,
        "survival": {
            "pre": pre_survival,
            "post": post_survival,
            "boot_changed": pre_survival["boot"] != post_survival["boot"],
            "session_changed": pre_survival["session"] != post_survival["session"],
            "outer_oom_increased": outer_oom_increased(pre_outer, post_outer),
        },
        "verdict": classify_verdict(
            outcome["payload_returncode"],
            outcome["systemd_run_returncode"],
            outcome["timed_out"],
            resource_events,
            unit_state.get("Result", ""),
        ),
    }
    encoded = json.dumps(result, sort_keys=True)
    print(f"RESOURCE {encoded}")
    if args.json_out is not None:
        args.json_out.parent.mkdir(parents=True, exist_ok=True)
        args.json_out.write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
    if result["verdict"] == "PASS":
        return 0
    payload_rc = outcome["payload_returncode"]
    return payload_rc if isinstance(payload_rc, int) and payload_rc != 0 else 1


def main() -> int:
    try:
        if sys.argv[1:2] == ["__child__"]:
            return child_main(sys.argv[2:])
        if sys.argv[1:2] == ["__boundary_probe__"]:
            return boundary_probe_main(sys.argv[2:])
        return controller_main(sys.argv[1:])
    except (MeasureError, OSError, ValueError) as error:
        print(f"MEASUREMENT ERROR — {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
