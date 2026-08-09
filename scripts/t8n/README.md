# The `check-t8n.sh` corpus

Nine cases, each a complete `t8n` invocation, with goldens generated from the
pinned conformance target. `scripts/check-t8n.sh` runs them; this file says
what they are and how to change them.

## Layout

```
scripts/t8n/
  cases/<name>/case.json          mode, fork, chain id, reward, description
  cases/<name>/alloc.json         pre-state            (authored)
  cases/<name>/env.json           environment          (authored)
  cases/<name>/txs.src.json       transactions         (authored; may carry secretKey)
  cases/<name>/txs.json           transactions, signed (GENERATED)
  cases/<name>/expected/*.json    result / alloc / body (GENERATED, verbatim)
  provenance.json                 generating revision + every generated digest
  deviations.json                 the registry of declared differences
```

Only the four authored files are edited by hand. Everything else comes from
`scripts/gen-t8n-goldens.py`, which drives the conformance target's
`ethereum-spec-evm t8n` and copies its output unchanged. A golden that agreed
with Jaune because someone copied it from Jaune would test nothing, so the
generator never reads Jaune and the gate refuses a golden whose digest does
not match `provenance.json`.

`txs.json` is generated too: the target's own `Transaction.sign` signs
`txs.src.json`, so both tools consume one identical, fully signed list rather
than each signing its own.

## The cases

| case | what it pins |
|---|---|
| `transfer-blockchain` | the default mode end to end: system operations, one successful transaction, empty withdrawals and requests |
| `transfer-state-test` | the same inputs under `--state-test`: one transaction, no system operations |
| `call-logs` | receipt logs, the receipt bloom, the block bloom and `logsHash` |
| `reject-parse` | a transaction that never becomes a `Tx`, reported in `rejected`, with a later transaction still executing |
| `reject-execution` | a transaction rejected during execution — and, through `txRoot`, that its entry stays in the transactions trie |
| `reject-middle` | three transactions with the middle one rejected, and the receipts of the other two |
| `withdrawals` | the withdrawals trie and `withdrawalsRoot` |
| `requests` | a real EIP-7002 withdrawal request, so `requests` is non-empty and `requestsHash` is not the empty digest |
| `block-exception` | a failing checked system transaction landing in `blockException` instead of aborting the run |

Every case runs at Prague. The lane's other three forks differ from Prague in
their blob schedule, which no case here exercises; a BPO case would need blob
transactions and is a fair successor rather than a gap this corpus pretends to
cover.

Each `alloc.json` carries four of the five Prague system contracts — history
storage, beacon roots, the withdrawal-request predeploy and the
consolidation-request predeploy — taken from the target's own
`pre_allocation_blockchain()`. The deposit contract is omitted deliberately:
it is 6.3 KB of bytecode, nothing reads it unless a transaction logs a deposit,
and no case here does.

## Changing a case

1. Edit the authored files.
2. Regenerate: `python3 scripts/gen-t8n-goldens.py [--case <name>]`.
3. Run the gate: `scripts/check-t8n.sh --red-test`.

`python3 scripts/gen-t8n-goldens.py --check` reports whether the committed
goldens still match the target without writing anything. The generator refuses
to run against a checkout whose commit is not the one `scripts/sources.json`
pins, so goldens and emission always come from one revision.

## `deviations.json`

The registry of every declared difference between `jaune t8n` and the target on
this corpus. The gate applies each entry to the **golden** side before
comparing and applies nothing to Jaune's side, so Jaune's bytes are always
compared as written. Each entry pins Jaune's exact expected bytes as well as
the target's: an unregistered difference fails, and so does a registered one
whose either side changed.

There are two kinds, and `scripts/report-t8n.md` carries the full argument for
both:

- **Message strings.** `rejected[].error` and `blockException` carry free text
  with no normative content. Every transition tool writes its own, and the
  framework maps the text to a canonical identity through the registered
  wrapper's exception mapper rather than comparing it. Jaune writes its own
  canonical vocabulary — the official identity `Jaune/FixtureException.lean`
  already assigns to each typed reason — rather than imitating another tool's
  wording. Every registered pair maps to the same official identity on both
  sides.
- **Field exemptions.** Two, both in `reject-parse`, both caused by a
  transaction shape Jaune's types cannot represent. See the entry's own `why`.

Beyond the registry, the gate applies one **canonicalisation** to `alloc`: both
sides are sorted, addresses lexically and storage keys numerically. The target
emits Python dictionary insertion order and Jaune emits ascending key order;
neither is normative and no consumer reads either.
