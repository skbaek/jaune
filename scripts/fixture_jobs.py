#!/usr/bin/env python3
"""Choose conservative fixture concurrency from effective CPU and memory.

The three fixture harnesses remain sequential unless the caller explicitly
passes ``--jobs auto``.  In that mode this program caps logical CPU capacity by
memory that is actually available to the current job.  On Linux that is the
minimum of host ``MemAvailable`` and every finite cgroup-v2 ancestor's remaining
allowance; CPU affinity, cpusets, and finite CPU quotas are capped similarly.

The constants are deliberately workload-level budgets rather than a claim that
every fixture consumes this much: one GiB stays outside the worker pool and
each worker is provisioned 2.4 GiB.  Thus a clean 6 or 8 GiB job resolves to at
most two workers.  Explicit numeric ``--jobs`` values are not routed through
this selector and retain their documented override meaning.
"""

from __future__ import annotations

import argparse
import math
import os
from pathlib import Path
import platform
import re
import subprocess
import sys
from typing import Iterable, NamedTuple


GIB = 1024**3
POOL_RESERVE_BYTES = 1 * GIB
PER_WORKER_BYTES = 12 * GIB // 5
CONSERVATIVE_FALLBACK_JOBS = 1


class DetectionError(RuntimeError):
    pass


class Capacity(NamedTuple):
    value: int | None
    sources: tuple[str, ...]


class Resources(NamedTuple):
    cpu: Capacity
    memory: Capacity


def parse_bytes(value: str) -> int:
    text = value.strip().lower()
    multipliers = {"k": 1024, "m": 1024**2, "g": GIB, "t": 1024**4}
    if text[-1:] in multipliers:
        number = text[:-1]
        multiplier = multipliers[text[-1]]
    else:
        number = text
        multiplier = 1
    if not number.isdigit() or int(number) <= 0:
        raise argparse.ArgumentTypeError(
            f"expected positive bytes or K/M/G/T value, got {value!r}"
        )
    return int(number) * multiplier


def parse_positive_int(value: str) -> int:
    if not value.isdigit() or int(value) <= 0:
        raise argparse.ArgumentTypeError(f"expected a positive integer, got {value!r}")
    return int(value)


def parse_cpuset(specification: str) -> int:
    cpus: set[int] = set()
    for raw_part in specification.strip().split(","):
        part = raw_part.strip()
        if not part:
            continue
        if "-" in part:
            start_text, separator, end_text = part.partition("-")
            if not separator or not start_text.isdigit() or not end_text.isdigit():
                raise DetectionError(f"invalid cpuset range {part!r}")
            start, end = int(start_text), int(end_text)
            if end < start:
                raise DetectionError(f"descending cpuset range {part!r}")
            cpus.update(range(start, end + 1))
        elif part.isdigit():
            cpus.add(int(part))
        else:
            raise DetectionError(f"invalid cpuset item {part!r}")
    if not cpus:
        raise DetectionError("empty cpuset")
    return len(cpus)


def read_text(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8").strip()
    except (FileNotFoundError, PermissionError, OSError):
        return None


def cgroup_v2_relative_path(proc_cgroup: Path = Path("/proc/self/cgroup")) -> str | None:
    text = read_text(proc_cgroup)
    if text is None:
        return None
    for raw in text.splitlines():
        fields = raw.split(":", 2)
        if len(fields) == 3 and fields[0] == "0":
            return fields[2]
    return None


def cgroup_ancestors(root: Path, relative_path: str) -> Iterable[Path]:
    root = root.resolve()
    current = (root / relative_path.lstrip("/")).resolve()
    try:
        current.relative_to(root)
    except ValueError as error:
        raise DetectionError(f"cgroup path escapes its root: {relative_path!r}") from error
    while True:
        yield current
        if current == root:
            break
        current = current.parent


def linux_cgroup_memory_capacity(
    root: Path, relative_path: str
) -> Capacity:
    candidates: list[tuple[int, str]] = []
    for directory in cgroup_ancestors(root, relative_path):
        limit_text = read_text(directory / "memory.max")
        current_text = read_text(directory / "memory.current")
        if limit_text is None or limit_text == "max" or not limit_text.isdigit():
            continue
        if current_text is None or not current_text.isdigit():
            continue
        limit, current = int(limit_text), int(current_text)
        inactive_file = 0
        stat_text = read_text(directory / "memory.stat")
        if stat_text is not None:
            for raw in stat_text.splitlines():
                fields = raw.split()
                if len(fields) == 2 and fields[0] == "inactive_file" and fields[1].isdigit():
                    inactive_file = int(fields[1])
                    break
        charged_working_set = max(0, current - inactive_file)
        candidates.append(
            (
                max(0, limit - charged_working_set),
                f"cgroup:{directory}:remaining-after-inactive-file",
            )
        )
    if not candidates:
        return Capacity(None, ())
    value = min(candidate[0] for candidate in candidates)
    sources = tuple(source for candidate, source in candidates if candidate == value)
    return Capacity(value, sources)


def linux_cgroup_cpu_capacity(root: Path, relative_path: str) -> Capacity:
    candidates: list[tuple[int, str]] = []
    for directory in cgroup_ancestors(root, relative_path):
        cpuset = read_text(directory / "cpuset.cpus.effective")
        if cpuset:
            try:
                candidates.append((parse_cpuset(cpuset), f"cpuset:{directory}"))
            except DetectionError:
                pass
        maximum = read_text(directory / "cpu.max")
        if maximum:
            fields = maximum.split()
            if (
                len(fields) == 2
                and fields[0].isdigit()
                and fields[1].isdigit()
                and int(fields[1]) > 0
            ):
                quota, period = int(fields[0]), int(fields[1])
                candidates.append(
                    (max(1, math.ceil(quota / period)), f"cpu.max:{directory}")
                )
    if not candidates:
        return Capacity(None, ())
    value = min(candidate[0] for candidate in candidates)
    sources = tuple(source for candidate, source in candidates if candidate == value)
    return Capacity(value, sources)


def linux_mem_available(path: Path = Path("/proc/meminfo")) -> Capacity:
    text = read_text(path)
    if text is None:
        return Capacity(None, ())
    for raw in text.splitlines():
        fields = raw.split()
        if len(fields) >= 2 and fields[0] == "MemAvailable:" and fields[1].isdigit():
            return Capacity(int(fields[1]) * 1024, ("/proc/meminfo:MemAvailable",))
    return Capacity(None, ())


def sysconf_available_memory() -> Capacity:
    try:
        pages = int(os.sysconf("SC_AVPHYS_PAGES"))
        page_size = int(os.sysconf("SC_PAGE_SIZE"))
    except (AttributeError, OSError, ValueError):
        return Capacity(None, ())
    if pages <= 0 or page_size <= 0:
        return Capacity(None, ())
    return Capacity(pages * page_size, ("sysconf:available-pages",))


def macos_available_memory() -> Capacity:
    try:
        completed = subprocess.run(
            ["vm_stat"], check=False, text=True, capture_output=True, timeout=5
        )
    except (FileNotFoundError, OSError, subprocess.TimeoutExpired):
        return Capacity(None, ())
    if completed.returncode != 0:
        return Capacity(None, ())
    size_match = re.search(r"page size of (\d+) bytes", completed.stdout)
    if size_match is None:
        return Capacity(None, ())
    page_size = int(size_match.group(1))
    available_labels = {
        "Pages free",
        "Pages inactive",
        "Pages speculative",
        "Pages purgeable",
    }
    pages = 0
    for raw in completed.stdout.splitlines():
        label, separator, value = raw.partition(":")
        digits = value.strip().rstrip(".")
        if separator and label in available_labels and digits.isdigit():
            pages += int(digits)
    if pages <= 0:
        return Capacity(None, ())
    return Capacity(pages * page_size, ("vm_stat:reclaimable-pages",))


def minimum_capacity(capacities: Iterable[Capacity]) -> Capacity:
    known = [capacity for capacity in capacities if capacity.value is not None]
    if not known:
        return Capacity(None, ())
    value = min(capacity.value for capacity in known if capacity.value is not None)
    sources = tuple(
        source
        for capacity in known
        if capacity.value == value
        for source in capacity.sources
    )
    return Capacity(value, sources)


def detect_resources(
    cgroup_root: Path = Path("/sys/fs/cgroup"),
    proc_cgroup: Path = Path("/proc/self/cgroup"),
) -> Resources:
    cpu_candidates: list[Capacity] = []
    logical = os.cpu_count()
    if logical is not None and logical > 0:
        cpu_candidates.append(Capacity(logical, ("os.cpu_count",)))
    try:
        affinity = len(os.sched_getaffinity(0))
        if affinity > 0:
            cpu_candidates.append(Capacity(affinity, ("sched_getaffinity",)))
    except (AttributeError, OSError):
        pass

    memory_candidates: list[Capacity] = []
    system = platform.system()
    if system == "Linux":
        host_memory = linux_mem_available()
        memory_candidates.append(host_memory)
        if host_memory.value is None:
            memory_candidates.append(sysconf_available_memory())
        relative = cgroup_v2_relative_path(proc_cgroup)
        if relative is not None:
            memory_candidates.append(linux_cgroup_memory_capacity(cgroup_root, relative))
            cpu_candidates.append(linux_cgroup_cpu_capacity(cgroup_root, relative))
    elif system == "Darwin":
        memory_candidates.append(macos_available_memory())
    else:
        memory_candidates.append(sysconf_available_memory())

    return Resources(
        cpu=minimum_capacity(cpu_candidates),
        memory=minimum_capacity(memory_candidates),
    )


def choose_jobs(
    cpu: int | None,
    memory_bytes: int | None,
    *,
    reserve_bytes: int = POOL_RESERVE_BYTES,
    per_worker_bytes: int = PER_WORKER_BYTES,
) -> int:
    cpu_jobs = cpu if cpu is not None and cpu > 0 else CONSERVATIVE_FALLBACK_JOBS
    if memory_bytes is None:
        return min(cpu_jobs, CONSERVATIVE_FALLBACK_JOBS)
    usable = max(0, memory_bytes - reserve_bytes)
    memory_jobs = max(1, usable // per_worker_bytes)
    return max(1, min(cpu_jobs, memory_jobs))


def format_gib(value: int | None) -> str:
    return "unknown" if value is None else f"{value / GIB:.2f} GiB"


def main(arguments: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--cpu", type=parse_positive_int)
    parser.add_argument("--memory-bytes", type=parse_bytes)
    parser.add_argument("--explain", action="store_true")
    args = parser.parse_args(arguments)

    detected = detect_resources()
    cpu = args.cpu if args.cpu is not None else detected.cpu.value
    memory = args.memory_bytes if args.memory_bytes is not None else detected.memory.value
    jobs = choose_jobs(cpu, memory)

    if args.explain:
        cpu_sources = "override" if args.cpu is not None else ",".join(detected.cpu.sources)
        memory_sources = (
            "override"
            if args.memory_bytes is not None
            else ",".join(detected.memory.sources)
        )
        print(
            "auto jobs resolved to "
            f"{jobs} (cpu={cpu or 'unknown'} from {cpu_sources or 'fallback'}; "
            f"effective memory={format_gib(memory)} from "
            f"{memory_sources or 'conservative fallback'}; "
            f"reserve={format_gib(POOL_RESERVE_BYTES)}; "
            f"per-worker={format_gib(PER_WORKER_BYTES)})",
            file=sys.stderr,
        )
    print(jobs)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
