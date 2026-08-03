# What you are trusting

When a Jaune or Blanc theorem says something is true, this document says what
that claim rests on. It is written to be used as a checklist by a reader who
wants to attack the claim, and it tries not to omit anything such a reader
would find on their own.

Every figure below is regenerable. Where a number appears, the command that
produces it appears with it — prefer running the command to trusting the
number, because the command is current and the number is a snapshot. The
snapshot was taken on 2026-08-04 against Jaune
`4e6a655591ca56583a5fca20782e80a3b9df1777` and Blanc
`a7db98b918938e7e89b308209d1f864381bddf0c` — the `codex/sweep` tips of the
Blanc → Jaune upstream sweep, proposed for merge and not yet merged.

This document is the base for both repositories. Blanc's trusted base is this
one plus three additions — the pinned Jaune revision, the axiom audit, and
Blanc's own ungated source — which are stated in
[Blanc's README](https://github.com/skbaek/blanc/blob/main/README.md#verification-status)
rather than duplicated here.

## The one-paragraph version

A Jaune or Blanc theorem is checked by the Lean 4 kernel at the pinned
toolchain version, on top of Mathlib at a pinned revision, and depends on the
three standard classical axioms — `propext`, `Classical.choice`, `Quot.sound` —
and nothing else. Nothing in the Jaune library is `@[extern]`, `opaque`,
`partial`, `native_decide`-backed, or `sorry`-ed, and there is no `panic` in
its import closure; the one `bv_decide` in the library is kernel-checked and
contributes no axiom. What the theorems do *not* cover is
the fixture harness (`Main.lean`, which no theorem mentions), the two harness
modules outside the library's import closure, and the question of whether the
theorems state the properties you actually care about. Conformance with the
Ethereum fixture corpora is evidence from testing, not from proof, and this
document keeps that line sharp.

## The kernel and the pins

Trusting a Jaune theorem means trusting:

| | |
|---|---|
| the Lean 4 kernel | `leanprover/lean4:v4.32.1` (`lean-toolchain`) |
| Mathlib | `v4.32.1`, revision `520045ab14e26149ee970e2e617ca04b09bde5d6` |

Trusting a Blanc theorem additionally means trusting a specific Jaune:

| | |
|---|---|
| Jaune | `4e6a655591ca56583a5fca20782e80a3b9df1777` (`lakefile.lean`, agreeing with `lake-manifest.json` and the Lake-managed checkout) |

Blanc consumes Jaune from Git at that pinned revision, not from a sibling
checkout, so a fresh clone reproduces the build and bumping Jaune is a reviewed
one-line change.

```
cat lean-toolchain
python3 -c "import json;print([(p['name'],p['rev'],p.get('inputRev')) for p in json.load(open('lake-manifest.json'))['packages']])"
```

## The axioms

Blanc's audit ([`scripts/AxiomCheck.lean`](https://github.com/skbaek/blanc/blob/main/scripts/AxiomCheck.lean),
driven by `scripts/check.sh`) is the sharpest statement of the trusted base
either repository makes, so it is worth being precise about what it does.

Eight theorems are audited: the seven headline solvency results and the compile
witness `Blanc.wethCode_compile`. Each row carries its **own pinned expected
axiom set**, and a theorem's axiom closure must equal that set *exactly*,
order-insensitively. An unexpected axiom fails the gate — and so does a
*missing* one, so a proof cannot quietly become vacuous or be replaced by a
stronger-looking statement without the pin moving in a reviewable diff. A
secondary pattern net independently rejects `sorryAx`, `ofReduceBool`,
`ofReduceNat`, and any `_native.` axiom, on the grounds that the last of these
adds the Lean compiler to the trusted code base.

All eight rows currently pin exactly `[propext, Classical.choice, Quot.sound]`
— standard classical Lean, present in essentially every Mathlib-using
development, and no more than that.

```
cd ~/blanc && scripts/check.sh --no-build
```

`Blanc.wethCode_compile` is proved by `decide +kernel` — kernel evaluation of
the same reduction, with no raised elaboration limit and nothing added to the
trusted base. In particular it is not `native_decide`.

## What is deliberately absent, and what enforces the absence

An exhaustive scan of `Jaune/` and `Main.lean` finds **zero** occurrences of
each of the following:

| | |
|---|---|
| `@[extern]` | no compiled implementation replaces a Lean definition |
| `axiom` | no bespoke axiom |
| `opaque` | no declaration without a definition |
| `sorry` | no incomplete proof |
| `partial def` | no unverified recursion |
| `implemented_by` | no substituted implementation |
| `native_decide` | no compiler-evaluated decision procedure |
| `dbg_trace` | no tracing on a code path |

```
grep -rEn '@\[extern|^axiom |^opaque |sorry|partial def|implemented_by|native_decide|dbg_trace' Jaune/ Main.lean
```

Run the same scan unanchored — matching the bare words anywhere, comments
included — and it returns twenty hits, all prose: eleven where `extern` sits
inside the English word "external" (opcode comments for `EXTCODESIZE` and its
neighbours, and remarks about externally observed bytes and labels), eight uses
of "opaque" in comments describing typed-envelope bytes that stay undecoded,
and one comment about keeping axiom sets exact. No declaration of any of these
kinds exists.

```
grep -rEn 'extern|axiom|opaque|sorry|partial def|implemented_by|native_decide|dbg_trace' Jaune/ Main.lean
```

The stricter scan is worth running yourself; it is the one a skeptical reader
reaches for, and it is better that this document has already told you what it
returns.

**Two gates keep a subset of that true, and it is important to know which
subset.** The absences are all real today; they are not all mechanically
defended, and a reader is entitled to know where the guarantee is a gate and
where it is a fact.

[`scripts/check-hygiene.sh`](scripts/check-hygiene.sh) — forbids `dbg_trace`
and `sorry` under `Jaune/`, fail-closed against the committed allowlist
[`scripts/hygiene-allow.txt`](scripts/hygiene-allow.txt). **That allowlist
contains only comments.** It has no entries because there is nothing to exempt.
Matching is line-number independent, so the gate survives edits above an
occurrence but forces re-review if the matched text changes. It needs no Lean
toolchain and **runs in CI on every push and pull request**.

[`scripts/check-integrity.sh`](scripts/check-integrity.sh) — four fail-closed
rules, computed over the **transitive local import closure of `Jaune.lean`**,
traversed from `import Jaune.*` lines rather than hardcoded, so the gate can
never be satisfied by moving code out of reach:

- **R1** — no `partial def`, `implemented_by`, or `dbg_trace` under `Jaune/` or
  in `Main.lean`. Absence with **no allowlist at all**: there is deliberately
  no carve-out and no row to add.
- **R2** — no `panic`/`panic!` in the closure, except exact allowlist rows.
- **R3** — no raw bang operation (`get!`, `set!`, `xs[i]!`, …) in the closure,
  except exact allowlist rows.
- **R4** — no stringly-typed semantic error carrier or string-driven semantic
  branch. Its scope is the closure *plus* the runner boundary
  (`Jaune/ChainStore.lean`, `Jaune/FixtureException.lean`, `Main.lean`), and it
  refuses a `PENDING` row outright: a new stringly semantic carrier can no
  longer be deferred, only reviewed in or rejected.

The allowlist for R2/R3/R4 is a **budget that only shrinks**.

```
scripts/check-hygiene.sh
scripts/check-integrity.sh
```

Today: hygiene reports 0 occurrences, all allowlisted; integrity reports 56
occurrences allowlisted, 0 pending, pending budget 0.

**What no gate enforces.** `@[extern]`, `axiom`, `opaque`, and `native_decide`
are absent from Jaune as a matter of fact, not as a matter of enforcement — no
Jaune gate forbids them, and a future commit introducing one would not be
caught by `check-hygiene.sh` or `check-integrity.sh`. Blanc's axiom audit
catches such a thing only if it enters the eight audited theorems' dependency
cones. **Also: `check-integrity.sh` is not a CI gate.** The push/pull-request
workflow ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs exactly
three jobs — the portable-environment unit tests, `check-hygiene.sh`, and
`lake build` — and the nightly workflow runs the `--full` and `--bls`
conformance tiers. The integrity gate is in neither; it is run locally and
before merge. Arc discipline is what has kept it green, which is a process
guarantee, not a mechanical one.

## The known exceptions

**One `bv_decide`, and it costs nothing.** `Jaune/Basic.lean` closes the codec
equation lemma `Bytes.toB256_pair` with `bv_decide`; it is the only occurrence
in the library. Measured 2026-08-03:

```
$ echo 'import Jaune.Basic
#print axioms Jaune.Bytes.toB256_pair' > /tmp/probe.lean && lake env lean /tmp/probe.lean
'Jaune.Bytes.toB256_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
```

So this `bv_decide` produced a kernel-checked proof and no per-declaration
`_native.bv_decide.ax_*` axiom. It adds nothing to the trusted base. Blanc's
gate nonetheless rejects `_native.` axioms by name, because other `bv_decide`
configurations can produce them; and `bv_decide` remains banned by project
policy inside the protected-theorem cone. Both remain sensible guards. Neither
is presently doing any work on this lemma.

**56 retained allowlist rows, zero pending.** 43 R3 rows for explicitly
justified optimized or reference operations and 13 R4 rows for legacy renderers
and external parser boundaries — and **no R2 rows at all**, so there is no
`panic` anywhere in the closure. Every retained row is a reviewed `KEEP` naming
its wrapper, theorem, adapter, or boundary; no `PENDING` row remains and the
budget is 0. A retained row is a **scoped, mechanically checked exception**, not
an unclassified defect — but it is an exception, and 56 of them is the honest
count of places where the strong reading of "no raw bang operations, no
stringly-typed errors" does not literally hold.

**Two modules are outside the gate's closure.** `Jaune/ChainStore.lean` and
`Jaune/FixtureException.lean` are not in `Jaune.lean`'s transitive import
closure, so R1–R3 do not inventory them. This is deliberate — they are harness
surface, not consensus surface — and R4 does reach them, but a reader auditing
"which code do these rules cover" deserves the boundary stated rather than
inferred from a comment in a shell script.

**`Main.lean` is in no proof cone.** The fixture harness is 840 lines of `IO`
that parse JSON, select cases, and compare roots. Every conformance claim this
project makes passes through code that no theorem covers. R1 and R4 reach it;
no proof does. It is tested, not proved, and that distinction is the point of
the next section.

## Testing versus proof

Everything in this section is evidence of a different kind from everything
above it. None of it is a theorem.

**The fixture corpora** are pinned by commit and SHA-256 in
[`scripts/sources.json`](scripts/sources.json), with the bootstrap and
verification procedure in
[`scripts/vectors/SOURCES.md`](scripts/vectors/SOURCES.md), and
`scripts/env_doctor.py` verifies a checkout's identity against the pin rather
than trusting a path. That is good provenance. What the corpora establish is
agreement with the reference implementation **on the cases its authors thought
to write**. They establish nothing about unreached paths.

**The reference itself is pinned, and does not cover everything Jaune claims.**
`execution_specs.commit` is `4198b9c5996713b268aed602739d5aa40e277694`, which
ends at Prague — it contains no Osaka. Jaune's Osaka and BPO support was built
from EIP text and validated against the `tests@v20.0.1` fixture release, not
transliterated from the pinned Python. That is a reasonable thing to have done
and the fixture evidence is strong, but "mirrors execution-specs at
`4198…7694`" is precise for Prague and structurally cannot be true for Osaka.

**The differential oracles** — 21,593 U256/word/hash cases
(`scripts/check-u256.sh`), 240 fake-exponential cases
(`scripts/check-fake-exp.sh`), the EC oracle (`scripts/check-ec.sh`), and 1,824
generated vector cases with 5 controls (`scripts/check-vectors.sh`) — compare
Jaune against a **frozen Python implementation**. It shares no code with the
Lean, which is what makes the comparison meaningful, but it does share the
possibility of a common misreading of a specification. Two independent
implementations of the same misunderstanding agree perfectly.

[`scripts/GATES.md`](scripts/GATES.md) is the authoritative catalogue of every
gate, its exact command, pass criteria, and runtime.

## What the theorems actually say — and what this document does not answer

This document is about whether the proofs are **sound**. It is not about
whether they are the **right theorems**.

Those are different questions and conflating them produces a document that
answers neither. A proof can be impeccable — standard axioms, no `sorry`, no
compiler in the trusted base — and still establish a property weaker or
narrower than a reader assumes from its name. Blanc's solvency results are
conditioned on hypotheses (notably that the WETH account's code is what
`Prog.compile weth` emits, which is exactly why `wethCode_compile` is audited
alongside them), and what "preserves solvency" quantifies over is a matter of
reading the statements.

Two open questions are tracked and deliberately not answered here: whether the
compiled contract is convincingly *the* WETH contract in every relevant aspect,
and whether the currently verified safety property is the strongest one worth
stating. Read the statements in
[`Blanc/Solvent.lean`](https://github.com/skbaek/blanc/blob/main/Blanc/Solvent.lean);
do not infer them from this document or from a theorem's name.

## Regenerating everything above

```
cd ~/jaune
cat lean-toolchain
grep -rEn '@\[extern|^axiom |^opaque |sorry|partial def|implemented_by|native_decide|dbg_trace' Jaune/ Main.lean
scripts/check-hygiene.sh
scripts/check-integrity.sh

cd ~/blanc
scripts/check.sh --no-build
```

If any figure in this document disagrees with those commands, the commands are
right.
