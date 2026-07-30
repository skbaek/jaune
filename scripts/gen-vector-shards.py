#!/usr/bin/env python3
"""Generate and verify the shard partition of an oversized precompile vector file.

``scripts/check-vectors.sh`` runs one process per vector file, so a single large
file is an indivisible unit of latency: ``blsPairing.json`` alone is ~80% of that
gate's sequential wall time, and no job count can split one process. Sharding it
makes the gate parallelisable.

Sharding is only sound because a vector case is independent of every other case
in its file: ``processVector`` in ``Main.lean`` builds a fresh minimal EVM per
case from that case's own Input/Expected/Gas and evaluates a pure term, so a
file's verdict is exactly the conjunction of its cases' verdicts. Splitting the
conjunction across processes therefore cannot change it.

What sharding *can* silently break is coverage: a slice that drops, duplicates,
or overlaps cases still reports every case it ran as passing. This generator is
the guard. ``--check`` re-derives nothing and instead compares the committed
shards against the committed source as a multiset of canonical case encodings,
so a dropped case, a duplicated case, an extra case, and two shards sharing a
case are all failures. Run it whenever the source or the shards change.

Shards are balanced by input length rather than cut into contiguous slices.
Pairing cost scales with the number of pairs in the input, and the source file is
sorted ascending by pair count, so contiguous slices would put every heavy case
in the last shard and set the gate's makespan to roughly twice the balanced one.
Balancing is a longest-processing-time-first assignment, which is deterministic:
the same source always yields the same shards.

Case order across shards is not preserved, and does not need to be — see the
independence argument above. Coverage is what is checked, and it is checked
exactly.
"""
from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parent
DEFAULT_SOURCE = ROOT / "vectors" / "blsPairing.json"
DEFAULT_SHARDS = 8


def canonical(case: object) -> str:
    """A stable encoding of one case, used only for set comparison."""
    return json.dumps(case, sort_keys=True, separators=(",", ":"))


def cost(case: object) -> int:
    """Relative cost proxy: pairing work scales with the input length."""
    if isinstance(case, dict):
        return len(case.get("Input", "") or "")
    return 0


def load_cases(path: Path) -> list:
    with path.open() as handle:
        cases = json.load(handle)
    if not isinstance(cases, list):
        raise SystemExit(f"error: {path} is not a JSON list of cases")
    if not cases:
        raise SystemExit(f"error: {path} holds no cases")
    return cases


def shard_path(source: Path, index: int) -> Path:
    """`blsPairing.json` -> `blsPairing.shard3.json`."""
    return source.with_name(f"{source.stem}.shard{index}.json")


def partition(cases: list, count: int) -> list[list]:
    """Longest-processing-time-first assignment into `count` balanced shards."""
    shards: list[list] = [[] for _ in range(count)]
    loads = [0] * count
    # Descending cost, index breaking ties, so the result is deterministic.
    order = sorted(range(len(cases)), key=lambda i: (-cost(cases[i]), i))
    for i in order:
        target = min(range(count), key=lambda s: (loads[s], s))
        shards[target].append(cases[i])
        loads[target] += cost(cases[i])
    empty = [n + 1 for n, s in enumerate(shards) if not s]
    if empty:
        raise SystemExit(
            f"error: {count} shards over {len(cases)} cases leaves shard(s) "
            f"{empty} empty; an empty vector file is a manifest error"
        )
    return shards


def verify(source: Path, cases: list, shards: list[list], where: str) -> None:
    """Require the shards to be an exact partition of the source's cases."""
    want = Counter(canonical(c) for c in cases)
    got: Counter[str] = Counter()
    for shard in shards:
        got.update(canonical(c) for c in shard)
    if want == got:
        n = sum(len(s) for s in shards)
        print(f"OK — shards: {n}/{len(cases)} cases, exact partition of {source.name} ({where})")
        return
    missing = want - got
    extra = got - want
    for enc, n in list(missing.items())[:5]:
        print(f"MISSING x{n}: {enc[:110]}", file=sys.stderr)
    for enc, n in list(extra.items())[:5]:
        print(f"UNEXPECTED x{n}: {enc[:110]}", file=sys.stderr)
    total_missing = sum(missing.values())
    total_extra = sum(extra.values())
    raise SystemExit(
        f"RED — shards do not partition {source.name}: "
        f"{total_missing} case(s) missing, {total_extra} case(s) duplicated or unexpected"
    )


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--source", type=Path, default=DEFAULT_SOURCE,
                    help="vector file to shard (default: vectors/blsPairing.json)")
    ap.add_argument("--shards", type=int, default=DEFAULT_SHARDS,
                    help=f"number of shards (default: {DEFAULT_SHARDS})")
    ap.add_argument("--check", action="store_true",
                    help="verify the committed shards partition the source; write nothing")
    args = ap.parse_args(argv)

    if args.shards < 1:
        raise SystemExit("error: --shards must be at least 1")
    cases = load_cases(args.source)

    if args.check:
        shards = []
        for i in range(1, args.shards + 1):
            path = shard_path(args.source, i)
            if not path.exists():
                raise SystemExit(f"RED — missing shard file: {path}")
            shards.append(load_cases(path))
        verify(args.source, cases, shards, "committed")
        for i, shard in enumerate(shards, 1):
            print(f"  {shard_path(args.source, i).name}\t{len(shard)} cases"
                  f"\tcost {sum(cost(c) for c in shard)}")
        return 0

    shards = partition(cases, args.shards)
    verify(args.source, cases, shards, "generated")
    for i, shard in enumerate(shards, 1):
        path = shard_path(args.source, i)
        with path.open("w") as handle:
            json.dump(shard, handle, indent=2)
            handle.write("\n")
        print(f"  wrote {path.name}\t{len(shard)} cases"
              f"\tcost {sum(cost(c) for c in shard)}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
