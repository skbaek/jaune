# Silence arc closure report

## Candidates

- Jaune source candidate: `c9808a575bb97491f64b178630e5616c7cee5350`
  on `codex/silence`.
- Blanc source candidate: `12c2ccf68fb2d36a351556c8d67f652008e9be54`
  on `codex/silence`, pinning that Jaune commit.
- Toolchain: `leanprover/lean4:v4.32.1`.

Jaune's source candidate is published at `origin/codex/silence`. Blanc's
candidate is locally committed and green, but the execution environment's
egress reviewer rejected its non-protected-branch push. That publication-only
gap is recorded as a green handoff; it is not a source or verification failure.

## Complete deletion inventory

The source commit removes 467 lines and adds none:

| File | Before | After | Removed |
|---|---:|---:|---:|
| `Jaune/Basic.lean` | 1,615 | 1,487 | 128 |
| `Jaune/Execution.lean` | 4,757 | 4,475 | 282 |
| `Jaune/Transaction.lean` | 1,944 | 1,922 | 22 |
| `Jaune/Types.lean` | 1,291 | 1,264 | 27 |
| `Main.lean` | 666 | 665 | 1 |
| `scripts/hygiene-allow.txt` | 16 | 9 | 7 |

Declarations removed from `Jaune/Basic.lean`:

- Layout helpers: `pad`, `padMid`, `padsMid`, `padsEnd`, `padss`, `addComma`,
  `addCommas`, the exact tree-layout identifier `fork`, `encloseStrings`, and
  `List.toStrings`.
- BLT layout: `BLT.toStrings`, `BLTs.toStringss`, and its tree-layout
  `ToString BLT` instance.
- JSON layout: the four `partial def`s `StringJson.toStrings`,
  `StringJsons.toStrings`, `Lean.Jsons.toStrings`, and `Lean.Json.toStrings`,
  plus their `Lean.Json.toString` sink.
- Verbosity and trace sinks: `verbosityRef`, `verboseImpl`, `verbose`,
  `cprint`, and `Except.print`.

Declarations removed from `Jaune/Execution.lean`:

- Layout renderers: `State.toStrings`, `AccessItem.toStrings`,
  `AccessList.toStrings`, `Header.toStrings`, `Auth.toStrings`,
  `Auths.toStrings`, `TxType.toStrings`, `Tx.toStrings`, `NTB.toStrings`,
  `Stack.toStrings`, `Mem.toStrings`, `Log.toStrings`, `Tra.toStrings`,
  `Msg.toStrings`, `BenvStat.toStrings`, `Benv.toStrings`, `Evm.toStrings`,
  `KeySet.toStrings`, `Test.toStrings`, `Withdrawal.toStrings`, and
  `Block.toStrings`.
- Layout instances: `ToString AccessList`, `Header`, `TxType`, `Tx`, `Log`,
  `KeySet`, `Test`, `State`, `BLT`, `Withdrawal`, and `Block`.
- The unused singleton-layout helper `mkSingleton`.

Declarations removed from `Jaune/Transaction.lean`:

- `Receipt.toStrings` and its tree-layout `ToString Receipt` instance.
- Eleven `cprint` call sites: seven in `applyBody` and four in
  `addBlockToChain.go`.

Declarations removed from `Jaune/Types.lean`:

- `Stor.toStrings`, `Acct.toStrings`, and their tree-layout `ToString`
  instances.

`Main.lean` no longer parses or installs `--verbose`. The plan prose called the
enumerated Transaction set “12 call sites,” but both the enumerated coordinates
and the exact source diff contain eleven; this report records the source-truth
count. No stub or no-op replacement remains.

## Ambiguous-name classification

- `ToString Ninst` — **retained**. Its scalar `Ninst.toString` is consumed by
  `Repr Ninst`; it is outside the tree-layout printer family.
- `ToString Receipt` — **deleted**. Its only source consumer was
  `Receipt.toStrings`, which was itself tracing-only.
- `String.joinln` — **retained**. `Jaune/EC.lean` uses it in the Galois-field
  formatter.
- Exact identifier `fork` — **deleted**. Its consumers were only the deleted
  layout renderers. Protocol-fork declarations and Blanc's
  `DispatchTree.fork` were not touched.
- `List.toStrings` — **deleted**. Its consumers were only deleted tree-layout
  code.
- `mkSingleton` — **deleted**. Its consumers were only deleted tree-layout
  code.

The scalar/enum instances for `Fork`, `ForkTransition`, `NetworkSpec`,
`FixtureException`, `UInt8`, `UInt16`, `UInt32`, `UInt64`, `B128`, `B256`,
`Adr`, and `Ninst` remain. No rendered diagnostic changed.

## Hygiene movement

Before this arc, the hygiene gate allowed two `dbg_trace` occurrences through
the single `Jaune/Basic.lean dbg_trace msg` row and its justification comment.
The trace sinks and that seven-line allowlist block were deleted together.

Afterwards:

```text
OK — hygiene: all 0 occurrence(s) of {dbg_trace, sorry} under Jaune/ are allowlisted; no new ones
```

There is no `partial def`, `implemented_by`, or `dbg_trace` in the library, and
no tracing row remains in `scripts/hygiene-allow.txt`.

## Blanc coupling and proof repair

The source coupling has two proof-local consequences in
`Blanc/Solvent.lean`:

1. `applyBody_preserves_solvent`: the preamble
   `simp only [cprint, verbose, Bool.false_eq_true, if_false, pure_bind] at h_run`
   became `simp only at h_run` (same one line, five stale simp arguments
   removed).
2. `addBlockToChainWith_preserves_solvent`: four trace calls had contributed
   five bind-inversion lines around the hash/transition proof. Those five
   `obtain` lines and a stale two-line comment were removed; one `change` line
   exposes the now-leading hash test, and the final chain equality was shortened
   from a transitive equality to the direct injected equality.

The protected wrapper theorem `addBlockToChain_preserves_solvent` and the other
three protected proofs were not restructured. Overall `Solvent.lean` changed by
3 insertions and 10 deletions. Lean goal inspection showed both edited proof
regions closed, and post-edit diagnostics were empty.

## Protected statements and axioms

The statements below are verbatim and textually identical to Blanc
`996f3bf1ec9c1afd3aae8fd3ba1854b371705854`.

```lean
theorem weth_preserves_solvent (wa : Adr) :
    ∀ sevm pre post,
      Exec 0 sevm pre (.ok post)  →
      (sevm.currentTarget = wa → some sevm.code.toList = Prog.compile weth) →
      Precond wa sevm pre →
      Postcond wa sevm post := by
```

```lean
theorem stateTransition_preserves_solvent (wa : Adr)
    (ch ch' : BlockChain) (block : Block)
    (h_run : stateTransition ch block = .ok ch')
    (h_wds : sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state :=
```

```lean
theorem chain_preserves_solvent (wa : Adr) (ch ch' : BlockChain)
    (h_reach : BlockChain.Reach ch ch')
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state := by
```

```lean
theorem addBlockToChain_preserves_solvent (wa : Adr)
    (ch ch' : BlockChain) (rlp : Bytes)
    (h_run : addBlockToChain ch rlp = .ok (.inl ch'))
    (h_wds : ∀ block hash, rlpToBlock rlp = .ok ⟨block, hash⟩ →
      sum ch.state.bal + wdsum block.wds < 2 ^ 256)
    (h_inv : State.Inv wa ch.state) : State.Inv wa ch'.state :=
```

Both `lean_verify` and `blanc/scripts/check.sh --no-build` report exactly:

```text
[propext, Classical.choice, Quot.sound]
```

for each of the four declarations. The source scan found no suspicious proof
constructs.

## Verification on exact source candidates

Jaune commands ran at
`c9808a575bb97491f64b178630e5616c7cee5350`; Blanc commands ran at
`12c2ccf68fb2d36a351556c8d67f652008e9be54`.

| Command | Verdict |
|---|---|
| Jaune `lake build` | PASS, 1,764 jobs (before and after: 1,764) |
| Blanc `lake build` | PASS, 909 jobs (before and after: 909) |
| Blanc `scripts/check.sh --no-build` | PASS, exact axiom audit 4/4 |
| `scripts/check-hygiene.sh` | PASS, 0 occurrences |
| `scripts/check-u256.sh` | PASS, 21,593/21,593 |
| `scripts/check.sh --patch --no-build --jobs auto` | PASS, 10/10 |
| `scripts/check.sh --rlp4 --no-build --jobs auto` | PASS, 4/4 |
| `scripts/check.sh --depth --no-build --jobs auto` | PASS, 67/67 |
| `python3 -m unittest discover -s scripts/tests` | PASS, 121 tests |
| `scripts/check.sh --smoke --no-build --jobs auto` | PASS, baseline-identical 174 (173 PASS, 1 expected FAIL) |
| `scripts/check.sh --bls --no-build --jobs auto` | PASS, baseline-identical 29/29 |
| `scripts/check-ec.sh` | PASS, 573/573 |
| `scripts/check-mainnet.sh --suite smoke --no-build --jobs auto` | PASS, 16/16 |
| `scripts/check-mainnet.sh --suite transitions --no-build --jobs auto` | PASS, 13/13 |
| `scripts/check-vectors.sh --jobs auto` | PASS, 51/51 files and 5/5 controls |
| `scripts/check-mainnet.sh --suite prague --no-build --jobs auto` | PASS, 2,573/2,573 |
| `scripts/check-mainnet.sh --suite osaka --no-build --jobs auto` | PASS, 2,514/2,514 |
| `scripts/check-mainnet.sh --suite full --no-build --jobs auto` | PASS, 5,100/5,100 |
| `scripts/check.sh --full --no-build --jobs auto` | PASS, baseline-identical 2,983 (2,978 PASS, 5 expected FAIL) |

The final binary SHA-256 is
`d0d263034e0cb86cd3069d334b93fb5a980f02ee98d3b1ede0b17f4d156b5203`.
Its change is expected by construction because code was deleted; fixture and
vector classification identity, not binary identity, is the invariant.
Hygiene 2 → 0 and loss of `--verbose` are the only intended observable
movements.

The only diagnostic observed during a build is the pre-existing
`Jaune/Types.lean` unused-simp warning for `toUInt32_toUInt64`.

## Commit ledger

| Repository | Branch | Commit | Purpose | Gates before commit | Pushed | Diagnostic |
|---|---|---|---|---|---|---|
| Jaune | `codex/silence` | `c9808a575bb97491f64b178630e5616c7cee5350` | Delete tracing machinery and allowlist row | 1,764-job build, LSP, hygiene, U256, PATCH, RLP4, DEPTH, Python; full Step-1 battery before handoff | yes | no |
| Blanc | `codex/silence` | `41ce8f5c221738c91785b02f46669679c37bac7b` | Normal Lake pin bump to published Jaune candidate | Three-way pin agreement; expected breakage census | no | yes |
| Blanc | `codex/silence` | `12c2ccf68fb2d36a351556c8d67f652008e9be54` | Shorten stale solvent-proof preambles | LSP goals/diagnostics, 909-job build, exact 4/4 axiom audit | no (egress denied) | no |

No history was rewritten, no protected/default branch was merged, and the
diagnostic pin checkpoint retains Blanc main
`996f3bf1ec9c1afd3aae8fd3ba1854b371705854` as its named recovery point.

## Scope and deferred findings

- No semantic code, rendered error text, baseline, manifest, timeout, guard, or
  fixture was changed.
- There is no deprecated stub, commented-out trace block, substring sweep, new
  axiom, `sorry`, `admit`, `ofReduce*`, `bv_decide`, or raised elaboration
  limit.
- No README or maintained documentation mentioned `--verbose` or tracing
  output, so no stale user-facing reference required removal.
- `scripts/bench-ec.lean` is byte-identical to the pre-arc commit. The plan's
  note that line 126 still held a `String`/`String.Slice` comparison was already
  stale at the branch point: the file instead documents and uses `Adr.toNat`
  for comparison. This arc made no change to it.
- No new defect was found that requires an `integrity.md` repair.

Human decisions remaining are publication of Blanc's already-green ordinary
branch if the environment permits it, followed by the user-owned merge order:
Jaune first, Blanc second.
