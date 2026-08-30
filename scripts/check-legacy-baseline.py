#!/usr/bin/env python3
"""Correctness and host-local timing state for ``check-legacy.sh``.

Tracked fixture baselines contain only portable ``STATUS<TAB>path`` rows.
Per-host wall times live in ignored ``TIME<TAB>path`` files beside them.  This
helper owns parsing, comparison, atomic writes, first-run timing genesis, and
the longest-first dispatch order so those two kinds of evidence cannot be
accidentally recombined by the shell harness.
"""

from __future__ import annotations

import argparse
import contextlib
import io
import math
import os
import tempfile
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable


class BaselineError(RuntimeError):
    pass


@dataclass(frozen=True)
class ReportRow:
    status: str
    elapsed: str
    path: str


def seconds(value: str) -> float:
    raw = value[:-1] if value.endswith("s") else value
    try:
        parsed = float(raw)
    except ValueError as error:
        raise BaselineError(f"invalid time {value!r}") from error
    if not math.isfinite(parsed) or parsed < 0:
        raise BaselineError(f"invalid time {value!r}")
    return parsed


def unique(rows: Iterable[tuple[str, object]], label: str) -> None:
    seen: set[str] = set()
    for path, _ in rows:
        if path in seen:
            raise BaselineError(f"duplicate {label} path: {path}")
        seen.add(path)


def read_report(path: Path) -> list[ReportRow]:
    rows: list[ReportRow] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise BaselineError(f"cannot read report {path}: {error}") from error
    for number, line in enumerate(lines, start=1):
        fields = line.split("\t")
        if len(fields) != 3 or fields[0] not in {"PASS", "FAIL"}:
            raise BaselineError(
                f"{path}:{number}: expected STATUS<TAB>TIME<TAB>path"
            )
        seconds(fields[1])
        if not fields[2]:
            raise BaselineError(f"{path}:{number}: empty fixture path")
        rows.append(ReportRow(*fields))
    unique(((row.path, row) for row in rows), "report")
    return rows


def read_correctness(path: Path) -> tuple[list[str], dict[str, str]]:
    comments: list[str] = []
    rows: list[tuple[str, str]] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise BaselineError(f"cannot read correctness baseline {path}: {error}") from error
    for number, line in enumerate(lines, start=1):
        if not line.strip() or line.lstrip().startswith("#"):
            comments.append(line)
            continue
        fields = line.split("\t")
        if len(fields) != 2 or fields[0] not in {"PASS", "FAIL"} or not fields[1]:
            raise BaselineError(
                f"{path}:{number}: expected STATUS<TAB>path"
            )
        rows.append((fields[1], fields[0]))
    unique(rows, "correctness baseline")
    return comments, dict(rows)


def read_timings(path: Path) -> dict[str, str]:
    rows: list[tuple[str, str]] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise BaselineError(f"cannot read timing baseline {path}: {error}") from error
    for number, line in enumerate(lines, start=1):
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        fields = line.split("\t")
        if len(fields) != 2 or not fields[1]:
            raise BaselineError(f"{path}:{number}: expected TIME<TAB>path")
        seconds(fields[0])
        rows.append((fields[1], fields[0]))
    unique(rows, "timing baseline")
    return dict(rows)


def atomic_write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8") as handle:
            handle.write(text)
        mode = (path.stat().st_mode & 0o777) if path.exists() else 0o644
        os.chmod(temporary, mode)
        os.replace(temporary, path)
    except BaseException:
        with contextlib.suppress(OSError):
            os.unlink(temporary)
        raise


def write_correctness(path: Path, rows: list[ReportRow]) -> None:
    atomic_write(path, "".join(f"{row.status}\t{row.path}\n" for row in rows))


def write_timings(path: Path, rows: list[ReportRow]) -> None:
    text = (
        "# Host-local fixture timing baseline — scripts/check-legacy.sh\n"
        "# TIME<TAB>path. Gitignored; initialized on this host's first complete run.\n"
        + "".join(f"{row.elapsed}\t{row.path}\n" for row in rows)
    )
    atomic_write(path, text)


def extend_timings(path: Path, timings: dict[str, str], report: list[ReportRow]) -> int:
    missing = [row for row in report if row.path not in timings]
    if not missing:
        return 0
    merged = dict(timings)
    merged.update((row.path, row.elapsed) for row in missing)
    text = (
        "# Host-local fixture timing baseline — scripts/check-legacy.sh\n"
        "# TIME<TAB>path. Gitignored; initialized on this host's first complete run.\n"
        + "".join(f"{elapsed}\t{fixture}\n" for fixture, elapsed in merged.items())
    )
    atomic_write(path, text)
    return len(missing)


def changes(correctness: dict[str, str], report: list[ReportRow]) -> list[tuple[str, str, str]]:
    remaining = dict(correctness)
    result: list[tuple[str, str, str]] = []
    for row in report:
        old = remaining.pop(row.path, "MISSING")
        if old != row.status:
            result.append((old, row.status, row.path))
    result.extend((old, "MISSING", path) for path, old in remaining.items())
    return sorted(result, key=lambda item: item[2])


def emit_drift(timings: dict[str, str], report: list[ReportRow]) -> None:
    for row in report:
        old = timings.get(row.path)
        if old is None:
            continue
        baseline = seconds(old)
        current = seconds(row.elapsed)
        if baseline >= 1.0 and current > 2 * baseline:
            print(
                f"DRIFT — {row.path}: {current:g}s vs {baseline:.2f}s "
                f"host-local reference ({current / baseline:.1f}x); informational only"
            )


def load_or_initialize_timings(path: Path, report: list[ReportRow]) -> dict[str, str] | None:
    if path.is_file():
        try:
            timings = read_timings(path)
            added = extend_timings(path, timings, report)
            if added:
                print(f"NOTE — host-local timing baseline initialized for {added} new fixture(s)")
            return timings
        except BaselineError as error:
            print(f"NOTE — timing baseline is invalid and will be reinitialized: {error}")
    write_timings(path, report)
    print(f"NOTE — host-local timing baseline initialized at {path}")
    return None


def evaluate(args: argparse.Namespace) -> int:
    report = read_report(args.report)
    if len(report) != args.total:
        raise BaselineError(
            f"{args.report} holds {len(report)} rows for a {args.total}-file selection"
        )
    observed_pass = sum(row.status == "PASS" for row in report)
    observed_fail = len(report) - observed_pass
    if (observed_pass, observed_fail) != (args.npass, args.nfail):
        raise BaselineError(
            "report classifications disagree with the harness summary: "
            f"report={observed_pass}/{observed_fail}, summary={args.npass}/{args.nfail}"
        )

    timings: dict[str, str] | None = None
    if args.jobs == 1:
        if args.refresh_times:
            if args.timings.is_file():
                try:
                    timings = read_timings(args.timings)
                except BaselineError as error:
                    print(f"NOTE — timing baseline is invalid and will be replaced only if classifications match: {error}")
            if timings is not None:
                emit_drift(timings, report)
        else:
            timings = load_or_initialize_timings(args.timings, report)
            if timings is not None:
                emit_drift(timings, report)

    if not args.baseline.is_file():
        if args.rebase:
            write_correctness(args.baseline, report)
            if args.jobs == 1:
                write_timings(args.timings, report)
            print(
                f"OK — {args.tier}: correctness baseline created with {args.total} files; "
                f"no prior classification delta ({args.summary})"
            )
            return 0
        if args.refresh_times:
            print(
                f"REGRESSION — {args.tier}: --refresh-times needs the tracked "
                f"correctness baseline {args.baseline}"
            )
            return 1
        if args.tier == "dir":
            if args.nfail == 0:
                print(f"OK — dir: {args.total} files, all PASS, no correctness baseline ({args.summary})")
                return 0
            print(f"REGRESSION — dir: {args.nfail} FAIL with no correctness baseline; see {args.report}")
            return 1
        if args.tier == "bls":
            print(f"REGRESSION — bls: no tracked target baseline at {args.baseline}")
            return 1
        print(f"REGRESSION — {args.tier}: tracked correctness baseline missing at {args.baseline}")
        return 1

    try:
        _, correctness = read_correctness(args.baseline)
    except BaselineError as error:
        print(error)
        if args.rebase:
            write_correctness(args.baseline, report)
            if args.jobs == 1:
                write_timings(args.timings, report)
            print(
                f"OK — {args.tier}: correctness baseline repaired with {args.total} files; "
                f"the malformed prior baseline had no trustworthy delta ({args.summary})"
            )
            return 0
        hint = (
            "it is hand-maintained; repair it directly"
            if args.tier == "bls"
            else "regenerate it with --rebase"
        )
        print(f"REGRESSION — {args.tier}: malformed correctness baseline ({hint})")
        return 1

    delta = changes(correctness, report)
    if args.rebase:
        if delta:
            for old, new, path in delta:
                print(f"REBASE — {path}: {old} -> {new}")
        else:
            print(f"REBASE — {args.tier}: no classification changes to absorb")
        write_correctness(args.baseline, report)
        if args.jobs == 1:
            write_timings(args.timings, report)
        print(
            f"OK — {args.tier}: correctness baseline rebased with {args.total} files, "
            f"{len(delta)} classification change(s) absorbed ({args.summary})"
        )
        return 0

    if args.refresh_times:
        if delta:
            for old, new, path in delta:
                print(f"CHANGE — {path}: {old} -> {new}")
            print(
                f"REGRESSION — {args.tier}: {len(delta)} classification change(s) vs "
                f"baseline; --refresh-times wrote nothing; see {args.report}"
            )
            return 1
        write_timings(args.timings, report)
        print(
            f"OK — {args.tier}: {args.total} files match correctness baseline; "
            "host-local times refreshed"
        )
        return 0

    if not delta:
        print(f"OK — {args.tier}: {args.total} files match correctness baseline ({args.summary})")
        return 0
    for old, new, path in delta:
        print(f"CHANGE — {path}: {old} -> {new}")
    print(f"REGRESSION — {len(delta)} classification changes vs baseline; see {args.report}")
    return 1


def dispatch(args: argparse.Namespace) -> int:
    lines = args.numbered.read_text(encoding="utf-8").splitlines()
    numbered: list[tuple[int, str]] = []
    for number, line in enumerate(lines, start=1):
        fields = line.split(" ", 1)
        if len(fields) != 2 or not fields[0].isdigit() or not fields[1]:
            raise BaselineError(f"{args.numbered}:{number}: malformed numbered fixture row")
        numbered.append((int(fields[0]), fields[1]))
    timings: dict[str, str] = {}
    if args.timings.is_file():
        try:
            timings = read_timings(args.timings)
        except BaselineError as error:
            print(f"NOTE — ignoring invalid host-local timing baseline for dispatch: {error}")
    ordered = sorted(
        numbered,
        key=lambda item: (-seconds(timings.get(item[1], "0")), item[0]),
    )
    atomic_write(args.output, "".join(f"{index} {path}\n" for index, path in ordered))
    return 0


def self_test() -> int:
    controls = 0
    with tempfile.TemporaryDirectory(prefix="jaune-legacy-baseline-") as directory:
        root = Path(directory)
        report_path = root / "report.txt"
        correctness_path = root / "baseline.txt"
        timings_path = root / "baseline-times.txt"
        numbered_path = root / "numbered"
        dispatch_path = root / "dispatch"
        report_path.write_text("PASS\t1.00s\ta.json\nFAIL\t3.00s\tb.json\n", encoding="utf-8")
        report = read_report(report_path)
        write_correctness(correctness_path, report)
        assert read_correctness(correctness_path)[1] == {"a.json": "PASS", "b.json": "FAIL"}
        controls += 1
        write_timings(timings_path, report)
        assert read_timings(timings_path) == {"a.json": "1.00s", "b.json": "3.00s"}
        controls += 1
        atomic_write(timings_path, "1.00s\ta.json\n")
        assert extend_timings(timings_path, read_timings(timings_path), report) == 1
        assert read_timings(timings_path)["b.json"] == "3.00s"
        controls += 1
        assert changes({"a.json": "PASS", "b.json": "FAIL"}, report) == []
        assert changes({"a.json": "FAIL"}, report) == [
            ("FAIL", "PASS", "a.json"), ("MISSING", "FAIL", "b.json")
        ]
        controls += 1
        drift = io.StringIO()
        with contextlib.redirect_stdout(drift):
            emit_drift({"a.json": "0.20s", "b.json": "1.00s"}, report)
        assert "b.json" in drift.getvalue() and "a.json" not in drift.getvalue()
        controls += 1
        numbered_path.write_text("1 a.json\n2 b.json\n3 c.json\n", encoding="utf-8")
        dispatch(argparse.Namespace(
            timings=timings_path, numbered=numbered_path, output=dispatch_path
        ))
        assert dispatch_path.read_text(encoding="utf-8").splitlines() == [
            "2 b.json", "1 a.json", "3 c.json"
        ]
        controls += 1
        timings_path.write_text("not-a-time\tb.json\n", encoding="utf-8")
        regenerated = io.StringIO()
        with contextlib.redirect_stdout(regenerated):
            assert load_or_initialize_timings(timings_path, report) is None
        assert "reinitialized" in regenerated.getvalue()
        assert read_timings(timings_path)["b.json"] == "3.00s"
        controls += 1
        try:
            report_path.write_text("PASS\t1.00s\ta.json\nFAIL\t2.00s\ta.json\n", encoding="utf-8")
            read_report(report_path)
        except BaselineError as error:
            assert "duplicate report path" in str(error)
        else:
            raise AssertionError("duplicate report path was accepted")
        controls += 1
        report_path.write_text("PASS\t1.00s\ta.json\nPASS\t2.00s\tb.json\n", encoding="utf-8")
        before = timings_path.read_bytes()
        refresh_args = argparse.Namespace(
            tier="smoke", report=report_path, baseline=correctness_path,
            timings=timings_path, total=2, npass=2, nfail=0, jobs=1,
            summary="2 PASS, 0 FAIL", rebase=False, refresh_times=True,
        )
        refused = io.StringIO()
        with contextlib.redirect_stdout(refused):
            assert evaluate(refresh_args) == 1
        assert timings_path.read_bytes() == before
        assert "--refresh-times wrote nothing" in refused.getvalue()
        controls += 1
        timings_path.unlink()
        with contextlib.redirect_stdout(io.StringIO()):
            assert evaluate(refresh_args) == 1
        assert not timings_path.exists()
        controls += 1
        rebase_args = argparse.Namespace(**{
            **vars(refresh_args), "rebase": True, "refresh_times": False,
        })
        with contextlib.redirect_stdout(io.StringIO()):
            assert evaluate(rebase_args) == 0
        assert read_correctness(correctness_path)[1]["b.json"] == "PASS"
        assert read_timings(timings_path)["b.json"] == "2.00s"
        controls += 1
    print(f"OK — legacy baselines: {controls} separation/genesis controls passed")
    return 0


def parser() -> argparse.ArgumentParser:
    root = argparse.ArgumentParser()
    commands = root.add_subparsers(dest="command", required=True)
    run = commands.add_parser("evaluate")
    run.add_argument("--tier", required=True)
    run.add_argument("--report", type=Path, required=True)
    run.add_argument("--baseline", type=Path, required=True)
    run.add_argument("--timings", type=Path, required=True)
    run.add_argument("--total", type=int, required=True)
    run.add_argument("--npass", type=int, required=True)
    run.add_argument("--nfail", type=int, required=True)
    run.add_argument("--jobs", type=int, required=True)
    run.add_argument("--summary", required=True)
    run.add_argument("--rebase", action="store_true")
    run.add_argument("--refresh-times", action="store_true")
    order = commands.add_parser("dispatch")
    order.add_argument("--timings", type=Path, required=True)
    order.add_argument("--numbered", type=Path, required=True)
    order.add_argument("--output", type=Path, required=True)
    commands.add_parser("self-test")
    return root


def main() -> int:
    args = parser().parse_args()
    try:
        if args.command == "evaluate":
            return evaluate(args)
        if args.command == "dispatch":
            return dispatch(args)
        return self_test()
    except (BaselineError, OSError) as error:
        print(f"HARNESS ERROR — legacy baseline: {error}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
