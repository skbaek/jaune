#!/usr/bin/env python3
"""Emit the keccak permutation equivalence block for Jaune/Hash.lean.

The block is inserted inside `namespace KECCAK`, after `f1600`. Every lane
expression below is DERIVED from the rotc/piln tables, never transcribed, so a
typo cannot be mistaken for a proof failure. The tables here must agree with
`Jaune/Hash.lean`'s; if they ever drift, the generated proof stops compiling
rather than silently proving something else — and `--check` refuses before that,
by re-reading both tables out of `Jaune/Hash.lean` and comparing them to the
ones below.

Usage:

    python3 scripts/gen-keccak-spec.py            # print the block to stdout
    python3 scripts/gen-keccak-spec.py --write    # insert/replace it in Hash.lean
    python3 scripts/gen-keccak-spec.py --check    # verify the committed block

`--check` regenerates the block and diffs it against what is committed between
the `-- BEGIN GENERATED` / `-- END GENERATED` markers, exiting nonzero on drift.
It matches the convention of `gen_mainnet_manifest.py --check` and
`gen-vector-shards.py --check`.
"""
from __future__ import annotations

import argparse
import difflib
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_TARGET = ROOT / "Jaune" / "Hash.lean"

BEGIN = "-- BEGIN GENERATED (scripts/gen-keccak-spec.py) -- do not hand-edit."
END = "-- END GENERATED"

ROTC = [1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14,
        27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44]
PILN = [10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
        15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1]

XS = [f"x{i}" for i in range(25)]
BINDERS = " ".join(XS)


def vec(entries, indent=6):
    pad = "\n" + " " * indent
    return "#v[" + ("," + pad).join(entries) + "]"


# ---- theta ---------------------------------------------------------------
def col(i):
    """`prep i` — the column parity, in the reference's own flat syntax."""
    return " ^^^ ".join(XS[i + 5 * j] for j in range(5))


def delta(i):
    """The reference's `t` for column i: bc[(i+4)%5] ^^^ rol bc[(i+1)%5] 1."""
    return f"(({col((i + 4) % 5)}) ^^^ UInt64.rol ({col((i + 1) % 5)}) 1)"


def theta_lanes():
    return [f"{XS[j]} ^^^ {delta(j % 5)}" for j in range(25)]


# ---- rho-pi --------------------------------------------------------------
def rhopi_lanes():
    """`t` starts at ws[1]; step i writes `rol t rotc[i]` into lane piln[i] and
    then takes `t := ws[piln[i]]`, read BEFORE that step's write. The piln
    entries are distinct, so every read still sees the original lane."""
    out = list(XS)
    t = XS[1]
    for i in range(24):
        j = PILN[i]
        nxt = XS[j]
        out[j] = f"UInt64.rol ({t}) {ROTC[i]}"
        t = nxt
    return out


# ---- chi -----------------------------------------------------------------
def chi_lanes():
    out = []
    for k in range(5):
        for i in range(5):
            b0 = XS[k * 5 + i]
            b1 = XS[k * 5 + (i + 1) % 5]
            b2 = XS[k * 5 + (i + 2) % 5]
            out.append(f"{b0} ^^^ ((~~~ {b1}) &&& {b2})")
    return out


def block() -> str:
    """The generated block, marker to marker, newline-terminated."""
    fields = ", ".join(f"s.a{i}" for i in range(25))
    etavec = ", ".join(f"v[{i}]" for i in range(25))
    ws = ", ".join(f"ws[{i}]" for i in range(25))
    chain = f"(⟨{ws}⟩ : State1600)"
    for i in range(24):
        chain = f"(round1600 rndc[{i}] {chain})"
    eta_cases = "\n".join(f"  | {i}, _ => rfl" for i in range(25))

    return f"""{BEGIN}
--
-- `f1600`'s doc comment above claims it is semantically identical to
-- `f rndc · UInt64.rol` over the reference transcription. `f1600_eq` at the
-- end of this block is that claim, as a theorem. The three lemmas before it
-- give each reference pass its closed form on an explicit 25-lane state; ι is
-- a single `xorLane` on lane 0 and is unfolded inline.

/-- Bridge from the unboxed round state to the 25-lane vector the reference
definitions operate on. Used by the equivalence theorems and once per
permutation, never inside a round — the same role `Blake2.Vec.toArray` plays in
`Jaune/Precompiles.lean`. -/
def State1600.toVec (s : State1600) : Vector UInt64 25 :=
  #v[{fields}]

/-- θ in closed form: lane `j` gains the column delta for column `j % 5`. -/
theorem theta_lit ({BINDERS} : UInt64) :
    θ UInt64.rol {vec(XS, 8)} =
    {vec(theta_lanes())} := by
  simp [θ, θ.outer, θ.inner, xorLane]

/-- ρπ in closed form. The reference walks a single carry `t` through the 24
`piln` lanes; because the table's entries are distinct, the value written into
lane `piln[i]` is a rotation of the ORIGINAL lane `piln[i-1]`. -/
theorem rhopi_lit ({BINDERS} : UInt64) :
    ρπ UInt64.rol {vec(XS, 8)} =
    {vec(rhopi_lanes())} := by
  simp [ρπ, ρπ.aux, piln, rotc]

/-- χ in closed form, row by row. Each row's five lanes are combined from the
row's pre-update values, which the reference snapshots into `bc`. -/
theorem chi_lit ({BINDERS} : UInt64) :
    χ {vec(XS, 6)} =
    {vec(chi_lanes())} := by
  simp [χ, χ.outer, χ.inner, xorLane]

/-- The fused unrolled round equals ι ∘ χ ∘ ρπ ∘ θ over the reference
transcription. This is the whole content of the equivalence: `round1600`'s
hand-derived `b` bindings ARE the ρπ carry chain, and its `c`/`d` bindings are
θ's column parities and deltas. -/
theorem round_eq (r : Nat) (h : r < 24) (s : State1600) :
    (round1600 (rndc[r]'h) s).toVec =
      ι r h rndc (χ (ρπ UInt64.rol (θ UInt64.rol s.toVec))) := by
  cases s
  simp [State1600.toVec, round1600, rolc, theta_lit, rhopi_lit, chi_lit,
    ι, xorLane, UInt64.rol]

/-- Any 25-lane vector is the vector of its own twenty-five lanes. This is what
lets the closed forms above, stated over explicit lanes, apply to `f1600`'s
opaque argument. -/
theorem vec_eta (v : Vector UInt64 25) : v = #v[{etavec}] := by
  apply Vector.ext
  intro i hi
  match i, hi with
{eta_cases}
  | _ + 25, h => omega

/-- `f1600` is exactly the twenty-four nested rounds, bridged out once at the
end; the `let` chain in its body is definitionally this nesting. -/
theorem f1600_toVec (ws : Vector UInt64 25) :
    f1600 ws = {chain}.toVec := rfl

/-- **The retained reference transcription and the production kernel compute
the same permutation.** `f1600`'s doc comment asserted this; this is the
proof. It says the optimization preserved the transcribed algorithm — it does
not say the transcription is FIPS-202, which remains a conformance question
answered by the differential oracle and the fixture corpora. -/
theorem f1600_eq (ws : Vector UInt64 25) :
    f1600 ws = f rndc ws UInt64.rol := by
  rw [f1600_toVec]
  simp only [round_eq, f, f.aux, Nat.reduceSub]
  rw [show State1600.toVec ⟨{ws}⟩ = ws from (vec_eta ws).symm]
{END}
"""


# ---- table cross-check ---------------------------------------------------
def read_table(text: str, name: str) -> list[int]:
    """Read `def <name> : Vector Nat 24 := #v[...]` out of Hash.lean."""
    match = re.search(rf"^def {name} : Vector Nat 24 :=\s*#v\[([^\]]*)\]",
                      text, re.MULTILINE)
    if not match:
        raise SystemExit(
            f"RED — cannot find `def {name} : Vector Nat 24` in the target; "
            f"the generator can no longer prove its tables match the source")
    return [int(entry) for entry in match.group(1).split(",")]


def check_tables(text: str) -> None:
    for name, ours in (("rotc", ROTC), ("piln", PILN)):
        theirs = read_table(text, name)
        if theirs != ours:
            raise SystemExit(
                f"RED — `{name}` in Hash.lean does not match the generator's "
                f"table.\n  Hash.lean: {theirs}\n  generator: {ours}")
    print("OK — rotc/piln in the generator match Jaune/Hash.lean's tables")


# ---- block location ------------------------------------------------------
def split_target(text: str, target: Path) -> tuple[str, str | None, str]:
    """Split the target into (before, committed block or None, after).

    With markers present the block is whatever sits between them. Without them
    the insertion point is immediately after `f1600` — i.e. before the next
    top-level `def`, which is `Bytes.run`.
    """
    begin = text.find(BEGIN)
    if begin != -1:
        end = text.find(END, begin)
        if end == -1:
            raise SystemExit(f"RED — {target} has a BEGIN marker with no END")
        end += len(END) + 1
        return text[:begin], text[begin:end], text[end:]

    anchor = re.search(r"^def f1600 \(", text, re.MULTILINE)
    if not anchor:
        raise SystemExit(f"RED — cannot find `def f1600 (` in {target}")
    following = re.search(r"^def ", text[anchor.end():], re.MULTILINE)
    if not following:
        raise SystemExit(f"RED — no declaration follows `f1600` in {target}")
    at = anchor.end() + following.start()
    return text[:at], None, text[at:]


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--target", type=Path, default=DEFAULT_TARGET,
                    help=f"Lean file carrying the block (default: {DEFAULT_TARGET})")
    ap.add_argument("--write", action="store_true",
                    help="insert or replace the block in the target file")
    ap.add_argument("--check", action="store_true",
                    help="verify the committed block matches; write nothing")
    args = ap.parse_args(argv)

    if args.write and args.check:
        raise SystemExit("error: --write and --check are mutually exclusive")

    generated = block()

    if not (args.write or args.check):
        sys.stdout.write(generated)
        return 0

    text = args.target.read_text()
    check_tables(text)
    before, committed, after = split_target(text, args.target)

    if args.check:
        if committed is None:
            raise SystemExit(
                f"RED — {args.target} carries no generated block "
                f"(no `{BEGIN}` marker)")
        if committed == generated:
            print(f"OK — keccak spec block: {len(generated.splitlines())} lines, "
                  f"byte-identical to the generator's output")
            return 0
        diff = difflib.unified_diff(
            committed.splitlines(keepends=True),
            generated.splitlines(keepends=True),
            fromfile=f"{args.target} (committed)", tofile="gen-keccak-spec.py",
        )
        sys.stderr.writelines(diff)
        raise SystemExit(
            f"RED — the block in {args.target} has drifted from the generator")

    # On a first insertion the block needs a blank line separating it from the
    # declaration that follows; on a replacement that line is already in `after`.
    spacer = "" if committed is not None else "\n"
    args.target.write_text(before + generated + spacer + after)
    verb = "replaced" if committed is not None else "inserted"
    print(f"{verb} {len(generated.splitlines())} generated lines in {args.target}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
