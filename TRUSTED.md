# What you are trusting

When a Jaune or Blanc theorem says something is true, this document says what
that claim rests on. It is written to be used as a checklist by a reader who
wants to attack the claim, and it tries not to omit anything such a reader
would find on their own.

Every figure below is regenerable. Where a number appears, the command that
produces it appears with it — prefer running the command to trusting the
number, because the command is current and the number is only a snapshot.
Repository identity for any regenerated result is `git rev-parse HEAD` in the
repository whose gate owns it.

This document is the base for both repositories. Each repository audits what
it owns. Jaune audits its own trust surface and the axiom closure of its
canonical execution proof layer (see [The axioms](#the-axioms)). Blanc's
trusted base is this one plus three additions — the pinned Jaune revision,
Blanc's axiom and claim audits over its own results, and Blanc's
imported-source trust gate — which are stated in
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
| the Lean 4 kernel | the toolchain named in `lean-toolchain` (`leanprover/lean4:v4.34.0` when this was written) |
| Mathlib | the tag required in `lakefile.lean` and the revision `lake-manifest.json` resolves (`v4.34.0`, `5ed2965256430c3649e86755f9576b54eca72435` when this was written) |

The files are the record; the commands below read them.

Trusting a Blanc theorem additionally means trusting the specific Jaune commit
Blanc pins in its `lakefile.lean`, agreeing with its `lake-manifest.json` and
recorded in Blanc's README. Blanc consumes Jaune from Git at that revision,
not from a sibling checkout, so a fresh clone reproduces the build and bumping
Jaune is a reviewed one-line change. That pin moves independently of this
repository, so it is not copied here.

```
cat lean-toolchain
python3 -c "import json;print([(p['name'],p['rev'],p.get('inputRev')) for p in json.load(open('lake-manifest.json'))['packages']])"
```

## The axioms

Axiom auditing follows ownership. Each repository checks the axiom closure of
the results it owns, and neither audit covers the other repository's results.

**Jaune audits its canonical execution proof layer.**
[`scripts/ExecutionAxioms.lean`](scripts/ExecutionAxioms.lean) holds 53
`#expect_axioms` rows. They cover `Jaune.Exec` and its constructors, adequacy
(`exec_iff_exec_eq`), derivation and chronology operations, settlement
lemmas, frame spawn lemmas, the symbolic PUSH and arithmetic rules, and the
observations of the two execution examples. Every row pins exactly
`Classical.choice`, `Quot.sound`, `propext`. A declaration whose closure
differs **in either direction** fails elaboration at its row. Because the
`Assurance` library that holds the rows is a default build target, it also
fails the ordinary `lake build`. The closure is computed by a from-scratch walk
over every reachable constant's type and value and every inductive's
constructors (`Jaune.AxiomAudit.walk` in
[`scripts/AxiomAudit.lean`](scripts/AxiomAudit.lean)). It never calls
`Lean.collectAxioms` or `#print axioms`, which on current Lean can under-report
axioms reached through an imported inductive (lean4#15226).
[`scripts/assurance-manifest.json`](scripts/assurance-manifest.json) records
every row's provenance. That includes the fifteen obligations Blanc pinned
under their former `Blanc.*` names before these declarations moved into Jaune.
`python3 scripts/check-assurance-manifest.py` runs in CI. It fails when a row
and the manifest disagree, when either loses an entry, or when a public rule of
a symbolic-rule module has no row. Adding, removing or re-pinning a row is a
reviewed decision, never a routine edit; see
[`scripts/GATES.md`](scripts/GATES.md#destination-axiom-audit).

This audit's scope is that proof layer, not the whole library. A Jaune
theorem outside it — `Bytes.sha256_eq_fips`, for example — has no pinned row
here. Its axioms are stated in this document from `#print axioms`, which
lean4#15226 makes advisory. The walker is a metaprogram under `scripts/`,
outside the hygiene and integrity scopes, like the other `scripts/*.lean`
tools.

**Blanc audits its own results, downstream.** Blanc's audit
([`scripts/AxiomCheck.lean`](https://github.com/skbaek/blanc/blob/main/scripts/AxiomCheck.lean),
driven by `scripts/check.sh`) checks Blanc's theorems, and with them whatever
Jaune closure those theorems reach at the Jaune revision Blanc pins. It does not
audit Jaune's library as a whole, and it is not a substitute for Jaune's own
audit. Blanc keeps its downstream claim and axiom checks.

Every audited Blanc row carries its **own pinned expected axiom set**, and a
theorem's axiom closure must equal that set *exactly*, order-insensitively. An
unexpected axiom fails the gate, and so does a missing one: dependency-closure
changes in either direction are reviewable, including the no-axiom
trivialization direction. Neither repository's axiom signal pins a theorem
statement, and it does not by itself prevent a weaker or vacuous statement.
Blanc separately Lean-checks the exact statements of its protected claim
families with `scripts/check-claims.sh`. A secondary pattern net independently
rejects `sorryAx`, `ofReduceBool`, `ofReduceNat`, and any `_native.` axiom, on
the grounds that the last of these adds the Lean compiler to the trusted code
base.

Blanc's live audit membership, total, and axiom-set distribution belong to
[Blanc's README trust section](https://github.com/skbaek/blanc/blob/main/README.md#verification-status)
and [Blanc's gate catalogue](https://github.com/skbaek/blanc/blob/main/scripts/GATES.md),
not to a duplicated count here. Most rows use the standard three axioms;
the rest pin smaller sets, down to none.

```
cd ~/jaune && python3 scripts/check-assurance-manifest.py   # rows and manifest agree
# the rows themselves are checked by the ordinary build (library `Assurance`)
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
rg -n '^\s*@\[extern|^\s*axiom\s|^\s*opaque\s+\S+\s*:|\bsorry\b|^\s*partial\s+def|\bimplemented_by\b|\bnative_decide\b|\bdbg_trace\b' Jaune Main.lean
```

Run the same scan unanchored — matching the bare words anywhere, comments
included — and it returns twenty-four hits, all prose: thirteen where `extern`
sits inside the English word "external" (opcode comments for `EXTCODESIZE` and
its neighbours, and remarks about externally observed bytes and labels), ten
uses of "opaque" in comments (mostly typed-envelope bytes that stay
undecoded), and one comment about keeping axiom sets exact. No declaration of
any of these kinds exists.

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
and `sorry` under `Jaune/` and `Examples/`, fail-closed against the committed
allowlist [`scripts/hygiene-allow.txt`](scripts/hygiene-allow.txt). Matching
is line-number independent, so the gate survives edits above an occurrence
but forces re-review if the matched text changes. It needs no Lean
toolchain and **runs in CI on every push and pull request**.

[`scripts/check-integrity.sh`](scripts/check-integrity.sh) — four fail-closed
rules, computed over the **transitive local import closure of `Jaune.lean`**,
traversed from `import Jaune.*` lines rather than hardcoded, so the gate can
never be satisfied by moving code out of reach:

- **R1** — no `partial def`, `implemented_by`, or `dbg_trace` under `Jaune/` or
  `Examples/`, in their roots, in `Main.lean`, or in `MemoryProbe.lean`.
  Absence with **no allowlist at all**: there is deliberately no carve-out and
  no row to add.
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

Today: hygiene reports 1 occurrence, allowlisted (the `@[csimp]` row below);
integrity reports 58 occurrences allowlisted, 0 pending, pending budget 0.

**The trust surface is now enforced, not merely reported.** `check-hygiene.sh`
fails on any un-allowlisted `axiom`, `opaque`, `@[extern]`, `@[implemented_by]`,
`@[csimp]`, `partial def`, `unsafe` or `native_decide` under `Jaune/` and
`Examples/`, in `Jaune.lean`, `Examples.lean` and `MemoryProbe.lean`, and in
the external-consumer smoke source, alongside the original `dbg_trace` and
`sorry`. Every one of these counts is zero except one: the allowlist carries
exactly one row, the proved `@[csimp]` substitution `execFueled_eq_cached`
in `Jaune/Execution.lean`. It is a kernel-checked equality
`execFueled = execFueledCached`, and it makes the compiled binary run the
calldata-sharing implementation. The row's written justification is in the
allowlist. So the claim this document makes about Jaune's trusted path is
defended by a gate on every push rather than being a property of the source at
the moment someone last looked. Adding an allowlist entry is the only way to
introduce another, and that is a reviewable act with a written justification.

Three residual limits, stated so the gate is not read as more than it is.
`Main.lean` is outside its scope and is clean today as a matter of fact only.
It is a syntactic scan of this repository's own text, so it cannot see a
construct reached through a dependency — that is what the axiom audit is for. And it is not comment-aware,
so prose can trip it; the fix is to reword the prose, not to allowlist it.

**Why the syntactic scan is not redundant with the axiom audit.** `#print
axioms` is non-discriminating on exactly this surface: a declaration whose body
is supplied by `@[extern]` behind an `opaque` reports as depending on no axioms,
because the kernel never sees a body to collect from. (On current Lean it can
also under-report axioms reached through an imported inductive, lean4#15226,
which is why Jaune's audit uses its own walker.) A clean axiom audit is
therefore compatible with an arbitrarily large hole, and neither check implies
the other. The claim worth making is the conjunction — the audited axiom sets
are exactly as pinned, *and* nothing in the tree steps outside the kernel to
get there — and it is the conjunction that this repository gates.

Blanc has a separate `scripts/check-trust-surface.sh` for these forms in
`Blanc.lean`'s transitive import closure, and its axiom audit catches
dependency-closure changes for the named audited results. Neither Blanc gate
expands the scope of Jaune's gates.

**CI coverage.** The push/pull-request workflow
([`.github/workflows/ci.yml`](.github/workflows/ci.yml)) runs four jobs: the
portable-environment unit tests; a static job running `check-hygiene.sh`,
`check-integrity.sh`, `check-consumer-boundary.py` and
`check-assurance-manifest.py`; `lake build`, which includes the axiom rows,
followed by `check-t8n.sh` and `check-u256.sh`; and the exact-revision Git
consumer smoke test. The nightly workflow runs the `--full` and `--bls`
conformance tiers.

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
`_native.bv_decide.ax_*` axiom. (That reading comes from `#print axioms`, which
lean4#15226 makes advisory; `Bytes.toB256_pair` has no row in Jaune's
from-scratch audit.) It adds nothing to the trusted base. Blanc's
gate nonetheless rejects `_native.` axioms by name, because other `bv_decide`
configurations can produce them; and `bv_decide` remains banned by project
policy inside the protected-theorem cone. Both remain sensible guards. Neither
is presently doing any work on this lemma.

**58 retained allowlist rows, zero pending.** 43 R3 rows for explicitly
justified optimized or reference operations and 15 R4 rows for legacy renderers
and external parser boundaries — and **no R2 rows at all**, so there is no
`panic` anywhere in the closure. Every retained row is a reviewed `KEEP` naming
its wrapper, theorem, adapter, or boundary; no `PENDING` row remains and the
budget is 0. A retained row is a **scoped, mechanically checked exception**, not
an unclassified defect — but it is an exception, and 58 of them is the honest
count of places where the strong reading of "no raw bang operations, no
stringly-typed errors" does not literally hold.

**Two modules are outside the gate's closure.** `Jaune/ChainStore.lean` and
`Jaune/FixtureException.lean` are not in `Jaune.lean`'s transitive import
closure, so R1–R3 do not inventory them. This is deliberate — they are harness
surface, not consensus surface — and R4 does reach them, but a reader auditing
"which code do these rules cover" deserves the boundary stated rather than
inferred from a comment in a shell script.

**`Main.lean` is in no proof cone.** The fixture harness is 1,300 lines of `IO`
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

**The reference pins have distinct scopes.** The frozen Python oracle
`execution_specs.commit`, `4198b9c5996713b268aed602739d5aa40e277694`, ends at
Prague and remains the input to its registered vector generators. It is not
an identity claim for Jaune's whole current semantics. Osaka and BPO support
was originally built from EIP text and validated against `tests@v20.0.1`;
the current-mainnet fixture lane now uses `tests@v20.0.2`. The separate
transition-tool/Amsterdam anchor remains `7341820b5b394b1934dfe7bb6f621fcdab7baf7f`.
Jaune retains fixture-compatible rejection of storage-only creation collisions
as an intentional difference from that transition-tool snapshot; the current
upstream fixtures exclude this ambiguous account shape. Agreement on generated arithmetic vectors
or fixtures does not establish equivalence to every part of any one Python
revision, nor final Amsterdam support.

**The differential oracles** — 21,593 U256/word/hash cases
(`scripts/check-u256.sh`), 240 fake-exponential cases
(`scripts/check-fake-exp.sh`), the EC oracle (`scripts/check-ec.sh`), and 1,990
generated vector cases with 5 controls (`scripts/check-vectors.sh`, which since
2026-08-28 includes boundary-length sweeps at precompile addresses `0x02` and
`0x03`) — compare
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

**`Jaune.KECCAK.f1600_eq` in `Jaune/Hash.lean`** is a second example, and its
name invites the same overreading. The theorem is

```lean
theorem f1600_eq (ws : Vector UInt64 25) : f1600 ws = f rndc ws UInt64.rol
```

with axioms `[propext, Quot.sound]`. It says the monomorphized production
kernel `f1600` computes **exactly the same permutation** as the polymorphic
reference transcription (`θ`/`ρπ`/`χ`/`ι`/`f`) retained above it in the same
file — and that reference is itself a port of Andrey Jivsov's C
implementation, not a restatement of FIPS 202. `f1600_eq` is evidence that the
optimization preserved the transcribed algorithm; it is **not** a proof that
the transcription implements the Keccak-f[1600] standard, and it should not be
read or cited as "keccak is verified" or "verified keccak". Conformance with
the standard is addressed the way every hash function in this library except
SHA-256 is: `scripts/check-u256.sh`'s differential oracle and the fixture
corpora — testing, not proof, exactly as the previous section describes.

**`Jaune.Bytes.sha256_eq_fips` in `Jaune/SHA256Spec.lean` is a stronger claim
than `f1600_eq`, and the whole of the difference is the reference.** The
theorem is

```lean
theorem Bytes.sha256_eq_fips (m : Bytes) : Bytes.sha256 m = SHA256.FIPS.hash m
```

with axioms `[propext, Classical.choice, Quot.sound]`. `SHA256.FIPS.hash` is a
transcription of **NIST FIPS 180-4** itself — the six logical functions of
§4.1.2, the constant tables of §4.2.2 and §5.3.3, the padding condition of
§5.1.1, the block parsing of §5.2.1, and the sixty-four-entry message schedule
and round assignment of §6.2.2 — written from the published standard and citing
it declaration by declaration, rather than being a port of someone's C. It
shares no declaration with the kernel's `SHA256` namespace, and its constant
tables are independent transcriptions rather than reads of `roundConstants` and
`initChunk` — which is what `SHA256.roundConstants_eq` and
`SHA256.initChunk_eq`, both `rfl`, record.

So for SHA-256, and so far for SHA-256 alone, the caveat above does not apply:
the theorem says the optimized kernel computes the published function on every
input, and a reader who knows SHA-256 can check its right-hand side against the
document rather than against other Jaune code. What the theorem cannot do is
excuse that reader from reading — whether the transcription is faithful to the
standard is a human judgement, which is why it cites its sections and is kept
readable rather than convenient. The differential vectors at precompile
addresses `0x02` and `0x03` are untouched by the theorem and are kept: they
check a different thing, the precompile's gas and output framing around the
hash.

## Regenerating everything above

```
cd ~/jaune
cat lean-toolchain
python3 -c "import json;print([(p['name'],p['rev'],p.get('inputRev')) for p in json.load(open('lake-manifest.json'))['packages']])"
rg -n '^\s*@\[extern|^\s*axiom\s|^\s*opaque\s+\S+\s*:|\bsorry\b|^\s*partial\s+def|\bimplemented_by\b|\bnative_decide\b|\bdbg_trace\b' Jaune Main.lean
scripts/check-hygiene.sh
scripts/check-integrity.sh
python3 scripts/check-assurance-manifest.py
lake build        # elaborates the axiom rows; on a coordinated host use its build launcher

cd ~/blanc
scripts/check-trust-surface.sh
scripts/check.sh --no-build
scripts/check-claims.sh
```

If any figure in this document disagrees with those commands, the commands are
right.
