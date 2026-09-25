# Step 7 projective-pairing residual decision

Date: 2026-07-22 (Asia/Seoul)

Verdict: **BN254 NO-GO. BLS12-381 NO-GO. Skip Step 8.**

## Reviewed boundary and scope

The decision was measured on the reviewed Step-5 boundary (Step 6 was skipped):

- branch: `main`, aligned with `origin/main`;
- commit: `811f27a55fd503e896bd44fd444e81ebaea212c4`;
- toolchain: `leanprover/lean4:v4.23.0`;
- initial working tree: clean;
- native `elevm` SHA-256:
  `ff573c7a8fa7c1f752d810e9753b16f17b6992e86c5442d09112d3694095f845`;
- native `elevm` size: 172,138,960 bytes; and
- native pairing benchmark SHA-256 and size:
  `1bf9780b1f89524a73c0b29959f838825808048d9995bd8bada4456d055de829`,
  172,057,552 bytes.

The committed EC benchmark had no pairing row, so the only executable-code
change is a benchmark-only extension to `scripts/bench-ec.lean`. It adds
separate full-pairing and final-exponentiation-disabled Miller rows for BN254
and BLS12-381. The BN254 G2 benchmark generator is copied from the pinned local
authority and checked on-curve before timing. Results are forced coefficient by
coefficient through the existing sink boundary. No production Lean module,
baseline, target manifest, vector, fixture, or gas behavior changed.

Raw benchmark tables, `nm` output, standard fixture reports, and sample files
are under `/tmp/elevm-step7`. The raw 1 ms sample trees are large and remain
untracked.

## Pinned algorithm authority and coordinates

The execution-specs virtual environment reports exactly `py_ecc 8.0.0`. The
four inspected source files are:

```text
~/execution-specs/venv/lib/python3.11/site-packages/py_ecc/optimized_bls12_381/optimized_curve.py
~/execution-specs/venv/lib/python3.11/site-packages/py_ecc/optimized_bls12_381/optimized_pairing.py
~/execution-specs/venv/lib/python3.11/site-packages/py_ecc/optimized_bn128/optimized_curve.py
~/execution-specs/venv/lib/python3.11/site-packages/py_ecc/optimized_bn128/optimized_pairing.py
```

These optimized modules use homogeneous projective points `(x, y, z)` with
affine interpretation **`(x/z, y/z)`**, not Jacobian `(X/Z², Y/Z³)`. This is
confirmed both by `normalize`, which returns `(x / z, y / z)`, and by the
on-curve equation `y² z - x³ = b z³`. Their projective `linefunc` accepts
three-coordinate points and incorporates all three `z` coordinates. A future
port could therefore not combine projective `double`/`add` with ELeVM's current
affine `linefunc`; the loop point operations, line function, twist/cast, and
state transitions would have to move together.

## Pairing benchmark

The benchmark was compiled through standalone Lean C generation and
`leanc -O2`, reusing the current Lake native dependency-object trace. Five
identical process-level repetitions used:

```sh
cd ~/elevm
for i in 1 2 3 4 5; do
  ELEVM_REPORT_DIR=/tmp/elevm-step7 \
    scripts/run-bench-ec.sh "step7-pairing-$i"
done
```

All five runs reproduced the same sinks:

- BN254 full pairing: `932325511`;
- BN254 Miller without final exponentiation: `430113242`;
- BLS12-381 full pairing: `703386250`; and
- BLS12-381 Miller without final exponentiation: `921348946`.

| row | run 1 | run 2 | run 3 | run 4 | run 5 | median |
|---|---:|---:|---:|---:|---:|---:|
| BN254 pairing | 606,358,167 ns | 607,818,250 ns | 595,210,667 ns | 588,232,500 ns | 587,475,750 ns | **595,210,667 ns** |
| BN254 Miller | 71,710,500 ns | 71,144,750 ns | 70,721,375 ns | 69,561,625 ns | 69,818,875 ns | **70,721,375 ns** |
| BLS12-381 pairing | 926,368,625 ns | 939,101,500 ns | 919,137,750 ns | 920,009,792 ns | 913,975,791 ns | **920,009,792 ns** |
| BLS12-381 Miller | 55,506,042 ns | 56,161,583 ns | 55,134,584 ns | 55,132,166 ns | 54,313,083 ns | **55,134,584 ns** |

Thus the entire Miller-only computation is 11.88% of the BN254 full-pairing
median and 5.99% of the BLS12-381 full-pairing median. Even the impossible
model in which a projective rewrite deletes the whole Miller computation at
zero cost cannot reach the required 15% end-to-end reduction.

## Fixture workloads and wall time

The required pairing workloads were run directly through the reviewed native
binary with `--network Prague`. Standard, unsampled harness runs were:

| family | exact fixture | verdict | wall time |
|---|---|---:|---:|
| BN254 | `GeneralStateTests/stZeroKnowledge/ecpairing_inputs.json` | PASS | **54.41 s** |
| BLS12-381 | `prague/eip2537_bls_12_381_precompiles/test_valid.json` | PASS | **69.02 s** |

The corresponding successful profiled runs took 57.24 s and 71.79 s. The BLS
fixture contains 514 cases and runs pairing cases only at its end. An initial
25-second attachment at process start sampled the earlier G1/G2 precompiles and
contained no `blsMillerLoop` frame, so it was not used for the pairing decision.
The fixture was repeated and `sample` was attached when its output first
entered `test_bls12_pairing.py`; this pairing-phase profile is the BLS decision
input. This phase-selection correction is recorded rather than pretending the
first profile measured pairing.

## Symbol and profile method

`nm` was checked on both `.lake/build/bin/elevm` and the freshly linked
benchmark. Both contain resolvable specialized symbols for:

- `millerLoop`, `blsMillerLoop`, `linefunc`, and `blsLinefunc`;
- the BN254 and BLS-specialized affine `EllipticCurve_double` and
  `EllipticCurve_add` used by those loops;
- `GaloisField_inv`, `GaloisField_pow`, and `extEuclid`; and
- the benchmark's `bn254G2Generator` and `fieldSink` in the benchmark binary.

Each workload used macOS `sample` on the main ELeVM process for 25 seconds at a
1 ms interval with `-mayDie`. Attribution uses the main-thread inclusive call
tree. Recursive or repeated categories count only their top-most occurrence on
each collapsed branch. Categories overlap and are not additive; in particular,
field arithmetic and allocation below a curve operation remain included in
that curve operation.

| workload/profile phase | samples | Miller loop | affine double | affine add | affine double/add union | `GaloisField.inv` | `extEuclid` | `GaloisField.pow` | allocation/refcount/free |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| BN254 `ecpairing_inputs` | 20,683 | 24.37% | 3.08% | 1.06% | **4.14%** | 3.62% | 5.06% | 81.87% | 64.96% |
| BLS `test_valid`, pairing phase | 20,580 | 15.92% | 3.16% | 0.26% | **3.42%** | 2.99% | 4.73% | 89.72% | 60.57% |

The affine double/add union is the relevant inclusive number: it already
contains the extension-field inversions and their descendants caused by those
operations. The separate inversion columns are whole-profile inclusive
diagnostics and overlap with other columns. The dominant residual is large
extension-field exponentiation plus its field arithmetic and allocation, not
affine loop-point inversion.

## Pinned operation model

ELeVM's loops perform these point operations for one non-infinity pairing:

- BN254: 64 affine doubles, 25 signed-digit affine adds, and one Frobenius-tail
  affine add: **90 affine point-operation inversions** total; and
- BLS12-381: 63 affine doubles and five set-bit affine adds: **68 affine
  point-operation inversions** total.

Counting multiplication expressions in the pinned optimized formulas,
including multiplication by small constants, homogeneous projective `double`
uses 17 field multiplications and `add` uses 15, with no division. That gives
1,478 point-operation multiplications for BN254 and 1,146 for BLS. BN254 runs
these point operations after twisting into FQ12. The pinned optimized BLS loop
instead retains `R` in FQ2 and re-twists it after every double/add; the counts
above deliberately omit that additional twist work, making the upper bound
more favorable to a port.
The projective `linefunc` is also more expensive than the affine one because it
must cross-multiply the `z` coordinates: 12 multiplications on a generic line
and 16 on a doubling line, versus approximately 2 and 5 respectively in the
current affine line function. Those extra line products are mandatory and are
why the affine point-operation share cannot simply be treated as pure gain.

A deliberately generous upper bound deletes every measured affine
double/add sample and charges no projective point or line overhead:

| family | generous maximum time reduction | generous maximum speedup |
|---|---:|---:|
| BN254 | 4.14% | 1.043x |
| BLS12-381 | 3.42% | 1.035x |

The independent full-Miller deletion ceilings from the benchmark are 11.88%
(1.135x) and 5.99% (1.064x). Both ceilings are below the plan's required 15%
time reduction (1.176x speedup), before accounting for the pinned project's
additional multiplications, representation conversion, selection, and
allocation. A conservative projective-operation prediction is therefore less
than 4.14% for BN254 and less than 3.42% for BLS, not at least 15%.

## Literal gate application

Step 7 requires both (per curve family):

1. affine `double`/`add` and the extension-field inversions they cause account
   for at least 20% inclusive; and
2. pinned projective operation counts conservatively predict at least 15%
   end-to-end improvement.

BN254:

- threshold 1: **FAIL** (4.14%, not at least 20%);
- threshold 2: **FAIL** (less than 4.14% conservatively; even deleting the
  entire Miller row gives only 11.88%).

BLS12-381:

- threshold 1: **FAIL** (3.42%, not at least 20%);
- threshold 2: **FAIL** (less than 3.42% conservatively; even deleting the
  entire Miller row gives only 5.99%).

Therefore the literal decisions are **BN254 NO-GO** and **BLS12-381 NO-GO**.
Step 8 is skipped for both families. The evidence does not justify broadening
this work into final exponentiation, polynomial-field representation, or
allocation changes.

## Verification and handoff

After the benchmark-only edit:

- Lean LSP reports no diagnostics in `scripts/bench-ec.lean`, `Elevm/EC.lean`,
  or `Elevm/BLS.lean`;
- `scripts/check-ec.sh` passed **573/573**;
- the representative BN254 fixture passed in 54.41 s; and
- the required BLS `test_valid.json` fixture passed in 69.02 s.

The 14.5-minute `scripts/check-vectors.sh` review-boundary gate was **not run**;
it remains explicitly user-owned and must report 42/42 vectors plus 5/5
controls. No FULL run belongs to this benchmark-only decision gate. The final
worktree scope is intended to contain only `scripts/bench-ec.lean` and this
decision report, with no production diff. The next plan action is Step 9 after
the user reviews this NO-GO boundary and, if desired, creates the single
benchmark/report commit (`bench: add pairing residual rows`).
