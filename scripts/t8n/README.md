# The `check-t8n.sh` corpus

Seventy-six cases, each a complete `t8n` invocation, with goldens generated
from the pinned conformance target. `scripts/check-t8n.sh` runs them; this
file says what they are and how to change them. All 76 conform, with no
registered refusal cases. The exact approved CLI adapter used by ommer cases
is recorded per case; it does not move the semantic reference pin.

## Layout

```
scripts/t8n/
  cases/<name>/case.json          mode, fork, chain id, reward, description
  cases/<name>/alloc.json         case-local pre-state (authored)
  cases/<name>/env.json           environment          (authored)
  cases/<name>/txs.src.json       transactions         (authored; may carry secretKey)
  cases/<name>/txs.json           transactions, signed (GENERATED)
  cases/<name>/expected/*.json    result / alloc / body (GENERATED, verbatim)
  provenance.json                 generating revision + every generated digest
  deviations.json                 the registry of declared differences
  amsterdam-system-alloc.json     shared Amsterdam system state (authored)
```

Only the four authored files and `deviations.json` are edited by hand.
Everything else comes from `scripts/gen-t8n-goldens.py`, which drives the
conformance target's `ethereum-spec-evm t8n` and copies its output unchanged.
A golden that agreed with Jaune because someone copied it from Jaune would
test nothing, so the generator never reads Jaune and the gate refuses a golden
whose digest does not match `provenance.json`.

`txs.json` is generated too: the target's own `Transaction.sign` signs the
authored transaction source, so both tools consume one identical, fully signed
list rather than each signing its own. A state-test mirror's local
`txs.src.json` is an explicit one-file include of its blockchain twin; that
keeps the two modes byte-identical without hiding how inputs are composed.

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

These nine cases run at Prague. The thirty `am-*` cases below exercise
Amsterdam's metering in both tool modes. Ten further cases cover storage-only
creation and empty-account deletion on Prague, Osaka, BPO1, BPO2 and Amsterdam.
Five further cases cover zero-value transaction, CALL and STATICCALL entry on
those same forks. Together these are 54 cases. The historical corpus adds
eleven transfers, one Berlin SELFDESTRUCT case, seven ommer cases and three
Muir difficulty cases, for 76 total.

### Storage semantics at the v21 pin

`storage-create-<fork>` contains eighteen transactions: creation transactions,
CREATE and CREATE2, each with zero/nonzero pre-existing target balance and
successful, reverting or out-of-gas initcode. The target has zero nonce, no
code, and pre-existing storage. Successful initcode reads a wiped slot, writes
that slot again (checking original-value gas accounting), and leaves another
old slot untouched. The failing variants check rollback of the wipe.

`storage-delete-<fork>` gives an empty coinbase pre-existing storage. A zero-tip
fee credit deletes that storage, then a later transaction funds the account
again. Amsterdam results also check that implicit deletion does not appear as
SSTORE-to-zero entries in the block access list.

`zero-value-storage-<fork>` calls three distinct storage-only empty accounts
through a zero-value transaction, CALL and STATICCALL. Both slots survive in
the pinned reference. The final alloc and state root directly observe storage
preservation; caller storage also records successful CALL and STATICCALL.

These are authored differential inputs, not release fixtures. For the ten
creation/deletion cases, the corresponding `test_create_collision.py` storage-only cases
at the pinned EELS commit
and `test_deleted_account_storage.py` are explicitly skipped as undefined until
EIP-8253 and absent from the release archive. The goldens here record the
pinned implementation's actual behavior on those five authored forks; they
do not claim Frontier-through-Amsterdam release coverage.

## Amsterdam lane

`jaune t8n --state.fork Amsterdam` resolves Amsterdam through `Fork.rules?`
like every other fork, and since goal `jaune-amsterdam-currency-v1`
`jaune t8n --forks` advertises it: the lane printed there is `Fork.supported`
restricted to target-backed labels, with synthetic `Constantinople` omitted.
It advertises 16 forks, Byzantium through Amsterdam; `scripts/sources.json`'s
`conformance_target.fork_lane` is the same list (pinned by
`scripts/check-cli.sh`), and `jaune t8n --info` states the lane, its basis
(the fixture corpora of `check-mainnet.sh` and the differential of
`check-t8n.sh`), and the resolved set. (Goal C kept `--forks` at four forks
and had `--info` call Amsterdam "not yet advertised, pending" this goal.) The result's `gasUsed` is the maximum of execution and state block
gas; receipts already carry the post-refund `cumulativeGasUsed` produced by
the transaction pipeline.

The Appendix-F metering corpus has fifteen scenarios, each in `blockchain` and
`state-test` mode: transfer, self-transfer, creation, successful and reverting
new-account CALL, state-reservoir spill/repayment, cross-frame repayment,
SSTORE's original/current/new lattice, SELFDESTRUCT settlement, external code
reads, delegation, reservoir allocation above the execution cap, calldata and
access-list floor gas, the refund cap, and intrinsic rejection above
`TX_MAX_GAS_LIMIT`. The scenario and its coverage labels are part of each
`case.json`; unit tests require the exact 15-by-2 matrix.

Every Amsterdam case explicitly names `amsterdam-system-alloc.json` through
`allocIncludes`; the generator and checker compose that file with the local
`alloc.json` and reject duplicate accounts or paths outside this corpus. The
shared file is the target fixture's exact six Amsterdam system predeploys, not
an implicit runner default.

The pinned target also writes EIP-7928 `blockAccessList` and
`blockAccessListHash` in every Amsterdam result, and Jaune now writes both
itself. They are compared byte for byte like every other result key: the
registry carries no Amsterdam entry, and the generator no longer writes one.
Two of the thirty cases -- `am-reject-intrinsic-blockchain` and its
`-state-test` mirror -- have their single transaction rejected, so the target's
own list shows that a rejected transaction contributes nothing to it; the
agreement is what the gate checks.

The original nine Prague cases retain their own complete allocs. Each carries
four of the five Prague system contracts — history storage, beacon roots, the
withdrawal-request predeploy and the consolidation-request predeploy — taken
from the target's own `pre_allocation_blockchain()`. The deposit contract is
omitted deliberately: it is 6.3 KB of bytecode, nothing reads it unless a
transaction logs a deposit, and no case here does.

## Changing a case

1. Edit the authored files.
2. Regenerate: `python3 scripts/gen-t8n-goldens.py [--case <name>]`.
3. Run the gate: `scripts/check-t8n.sh --red-test`.

`python3 scripts/gen-t8n-goldens.py --check` reports whether the committed
goldens still match the target without writing anything. The generator refuses
to run against a checkout whose commit is not the one `scripts/sources.json`
pins, so goldens and emission always come from one revision.

## Historical cases (goal U10)

Eleven cases cover the target-backed pre-Prague forks, one transfer per fork;
all conform against their registered goldens:

| case | fork label | reward |
|---|---|---|
| `hist-transfer-byzantium` | `Byzantium` | 3 ETH, honored |
| `hist-transfer-constantinoplefix` | `ConstantinopleFix` | 2 ETH, honored |
| `hist-transfer-istanbul` | `Istanbul` | 2 ETH, honored |
| `hist-transfer-muirglacier` | `MuirGlacier` | 2 ETH, honored |
| `hist-transfer-berlin` | `Berlin` | 2 ETH, honored |
| `hist-transfer-london` | `London` | 2 ETH, honored |
| `hist-transfer-arrowglacier` | `ArrowGlacier` | 2 ETH, honored |
| `hist-transfer-grayglacier` | `GrayGlacier` | 2 ETH, honored |
| `hist-transfer-merge` | `Merge` (Paris) | proof of stake, `-1` |
| `hist-transfer-shanghai` | `Shanghai` | proof of stake, `-1` |
| `hist-transfer-cancun` | `Cancun` | proof of stake, `-1` |

Labels are the target's `--state.fork` names (`ConstantinopleFix` for its
`constantinople` module, `Merge` for Paris); Jaune parses the same labels.
All eleven labels resolve. Before London no base fee is read from `env`,
and before the merge `DIFFICULTY` reads the resolved difficulty. The result
carries `currentDifficulty` pre-merge, and `currentBaseFee`, withdrawals,
blob and request fields exactly when the selected fork carries them.
There is no synthetic `Constantinople` (EIP-1283) golden: the target refuses
that label (`UNSUPPORTED_FORKS`), even though Jaune can execute it. Its
finite evidence is the separate legacy tier; dormant constants are classified,
not treated as independent EELS comparisons.

`hist-selfdestruct-empty-berlin` (goal U6b) is a twelfth historical case,
originally refused until the Berlin wave and now conforming. Two contracts self-destruct with zero
balance to two storage-only beneficiaries (`0x0300`, `0x0400`), and the parent
then sends `0x0300` 1 wei. Before Paris `modify_state` does not erase an
account it leaves empty (`settle.eraseEmptyOnModify`), so both beneficiaries
stay, storage and all, and are touched: in the target's alloc `0x0300`
survives the EIP-161 sweep funded and with its slot, and `0x0400` is swept.
Under an always-erasing credit `0x0300` would lose its storage.

Environment field boundaries are independent: no `currentBaseFee` before
London, no withdrawals before Shanghai, and no blob fields before Cancun.
London, ArrowGlacier and GrayGlacier are pre-Merge and do carry a base fee.
The authored pre-Merge cases supply `parentTimestamp` and `parentDifficulty`
for the target's difficulty step, together with `parentGasUsed` as parent
block context.

### Ommer rewards and Muir difficulty

Seven `hist-ommers-*` cases cover Byzantium, ConstantinopleFix, Istanbul,
Berlin, London, ArrowGlacier and GrayGlacier. Three `hist-muir-difficulty-*`
cases cover Muir's difficulty boundary, including one with ommers. These ten
cases were added through the registered generator and exact approved golden
adoption; the original 66 cases and provenance output rows were preserved.

The unmodified pinned CLI has incompatible validation and raw reward-parser
shapes for `env.ommers`. The eight nonempty-ommer cases therefore record the
approved `ommer-reward-summary-cli-v1` adapter at its exact file/blob/hash
identity. It removes reward tuples only from the copy passed to the typed
Environment validator; the original raw reward-parser input remains intact.
The semantic EELS base remains 1562e2f; the dedicated
adapter checkout is 247cc2ae. The two empty-ommer Muir cases retain their
original unadapted provenance. This compatibility boundary is explicit,
not an upstream CLI fix or a new semantic reference revision.

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
  sides. A row is that identity on its own, or an object carrying it under
  `jaune` beside the `owner` and `recorded` metadata of the goal that ruled on
  the row.
- **Field exemptions.** Two, both in `reject-parse` and both caused by a
  transaction shape Jaune's types cannot represent. See each entry's own `why`
  and `upstream` metadata.

Beyond the registry, the gate applies one **canonicalisation** to `alloc`: both
sides are sorted, addresses lexically and storage keys numerically. The target
emits Python dictionary insertion order and Jaune emits ascending key order;
neither is normative and no consumer reads either.
