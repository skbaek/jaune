# Jaune naming rules and rename map schema

This document specifies the naming rules, allowed abbreviations, per-layer case
conventions, retired tokens, and machine-readable rename map schema for Jaune
(`Jaune/` and `JauneConsensus/`).

## 1. Naming rules

Every identifier in Jaune follows these seven rules in priority order:

1. **Protocol names first.** Use opcode mnemonics, constant and function names
   from EIPs, field names from `ethereum/execution-apis` JSON-RPC and Engine API
   schemas, and—for the consensus layer—names from the Ethereum consensus
   pyspec and Beacon API, verbatim up to the layer's case style (rule 7).
2. **When community sources disagree, record the user's choice.** Six execution
   names with divergent community spellings are settled:
   - `Header.coinbase` (JSON-RPC `miner`, Engine API `feeRecipient`)
   - `Header.prevRandao` (JSON-RPC `mixHash`)
   - `Header.ommersHash` (JSON-RPC `sha3Uncles`)
   - `Block.ommers` (JSON-RPC `uncles`)
   - `Transaction.gasLimit` (JSON-RPC `gas`, EIP payloads `gas_limit`)
   - `Transaction.data` (JSON-RPC `input`)
   The doc comment on each settled declaration records the alternate spellings.
   Any new disagreement of this kind is escalated as a decision.
3. **Clients' shared working vocabulary.** When no protocol schema fixes the
   name, prefer a word used by a cross-client interface (EVMC, EIP-3155 traces,
   tracing hooks) or by at least two independent client lineages, citing the
   source in the rename map.
4. **Plain English words.** Otherwise choose plain words that state what the
   thing is at its own level (for example `step`, `enter`, `settle`, `resume`).
5. **No private short forms.** Only community-standard abbreviations are allowed
   (section 2). Private contractions such as `Adr`, `Acct`, `Stor`, `Tra`,
   `B256`, `B128`, `BLT`, `NTB`, `hp`, `Devm`, `Sevm`, `Benv`, `Tenv`, `Rinst`,
   `Xinst`, `Ninst`, `Linst`, `Jinst`, `bal`, `txsRoot`, `wds`, `Ctx`, `CFork`,
   `Gated`, `vbytes`, `Pres`, `WQ` are retired.
6. **One word, one meaning; one concept, one name.** No token carries two
   meanings across declarations or layers (`bal` must not mean both `balance`
   and `blockAccessList`). A community name is used only when Jaune's
   definition matches the community's meaning (`depthLeft` rather than `depth`
   for the remaining call-depth allowance).
7. **Lean conventions and layer case styles.**
   - **Execution layer (`Jaune/`):** Types and type-like inductives/structures
     use `UpperCamelCase`. Functions, values, and execution-apis / JSON-RPC
     record fields use `lowerCamelCase`. Theorems use `snake_case` built from
     the names of the definitions they state properties of. Namespaces replace
     Python-style verb prefixes (e.g., `Transaction.intrinsicGas` rather than
     `calculateIntrinsicCost`) unless an EIP names the function directly.
   - **Consensus layer (`JauneConsensus/`):** Spec-port container types, fields,
     and constants keep pyspec names verbatim (`UpperCamelCase` containers,
     `snake_case` fields, `UPPER_SNAKE_CASE` constants). Spec-port functions
     are transliterated from pyspec `snake_case` to `lowerCamelCase`. Jaune's
     own names in `JauneConsensus/` (`Facts`, glue, and harness) follow rules
     4–7 (`UpperCamelCase` types, `lowerCamelCase` definitions, `snake_case`
     theorems).

## 2. Allowed abbreviations

In names chosen by Jaune (rule 4), every identifier token must be a whole word
or one of the following community abbreviations:

- Core Ethereum / Lean tokens: `tx`, `pc`, `EVM`, `RLP`, `EOA`, `BLS`, `KZG`,
  `SSZ`, `EIP`, `BPO`, `EC`, `API`, `CLI`, `JSON`, `YAML`
- Cryptographic / field / curve tokens: `Fp`, `Fp2`, `G1`, `G2`, `SHA256`,
  `KECCAK`, `RIPEMD160`, `BLAKE2`, `secp256k1`, `Modexp`, `Ecrecover`
- Standard Lean / type tokens: `UInt8`, `UInt16`, `UInt32`, `UInt64`, `U256`,
  `U128`, `Hash32`, `Nat`, `Int`, `Bool`, `ByteArray`, `Bytes`

Names adopted verbatim from a registered source (rules 1–3, such as opcode
mnemonics `sload` or pyspec fields `eth1_data`) are checked against their
registered source rather than this list.

## 3. Machine-readable rename map (`scripts/naming-map.json`)

The canonical rename map lives at `scripts/naming-map.json` and is validated by
`python3 scripts/check-naming-map.py`.

Top-level object fields:

- `schema_version`: integer `1`.
- `retired_tokens`: list of retired private short-form tokens enforced by the
  name lint (`N3`).
- `allowed_abbreviations`: list of allowed abbreviation tokens (`section 2`).
- `entries`: list of rename entries.

Each entry in `entries` is a JSON object with required non-empty string fields:

- `old`: old qualified Lean name (declaration, field, constructor, or module).
- `new`: new qualified Lean name.
- `kind`: one of `"declaration"`, `"field"`, `"constructor"`, `"module"`,
  `"relocation"`.
- `layer`: one of `"execution"`, `"consensus"`, `"adapter"`.
- `rule`: rule number `"1"`–`"7"` (or comma-separated primary + secondary rule
  numbers, e.g. `"1, 7"`).
- `source`: non-empty citation of the authoritative naming source (EIP number,
  execution-apis/Engine schema file, EVMC header, consensus pyspec function,
  user decision, or `"Plain English (rule 4)"`).

Optional entry fields:

- `notes`: free-text clarification (for example alternate community spellings
  preserved in doc comments).

Validation invariants enforced by `scripts/check-naming-map.py`:

1. Every entry has non-empty `old`, `new`, `kind`, `layer`, `rule`, and `source`,
   with `old != new`. Missing or empty `source` fails closed.
2. `kind`, `layer`, and `rule` contain only valid registered values.
3. The map is a one-to-one bijection on `old -> new`: no duplicate `old` names
   and no duplicate `new` names.
4. No `new` identifier segment introduces a token from `retired_tokens` (exact
   camelCase/snake_case token match).

## 4. Compiler-resolved apply tooling

Build the optional `jaune-naming-references` target with the host's owned-build
launcher. It is a metaprogram, outside the specification import closure. With
the selected source's imports current, export its references:

```sh
lake env .lake/build/bin/jaune-naming-references Jaune/Machine.lean Jaune.Machine .lake/naming/Machine.references.json
python3 scripts/apply-naming-map.py plan --tree . --map scripts/naming-map.json --file Jaune/Machine.lean .lake/naming/Machine.references.json > plan.json
python3 scripts/apply-naming-map.py apply --tree . --map scripts/naming-map.json --plan plan.json
```

The export elaborates one file and needs the host's Lean resource admission;
it never builds imports. Keep the import-build receipt with the export. The
bundle contains the exact elaborated source and compiler references, including
locals (the ordinary `.ilean` deliberately omits them). A source mismatch is a
refusal. Planning and applying are light Python operations.

Repeat `--file SOURCE REFERENCES_JSON` for every selected source in the tree.
The report states that explicit scope: it is not evidence for unselected
files. The tool resolves shared field names by declaration identity. It keeps
UTF-16 source positions, qualified references, local variables and other
structures' fields distinct. It reports every affected token it cannot resolve,
including tactic labels or namespace syntax absent from the compiler index.
Any unresolved token prevents application; exit 1 means an unresolved plan,
exit 2 a setup/input refusal. No spelling-based global replacement is used.
Namespace-depth changes and module relocation are currently refused and need
separate tooling before the full migration. Every renamed descendant needs its
own map row; a parent rename never silently skips a qualified descendant.

Before applying, the tool rechecks all selected source and bundle digests, the
map digest, and the entire recomputed edit plan. It validates all files before
writing the first. Filesystem I/O failures can still interrupt a multi-file
write, as in an editor: retain the plan and a Git checkpoint. A successful
application still requires elaboration and the N4 fidelity check; it is not a
type/value or attribute-preservation verdict.

### Whole Lean tree planning

`naming-tree.py` adds complete source accounting around the same semantic
planner. Run `needs` first to discover which modules contain candidate tokens,
then capture those roots with `naming-candidate.py capture` (section 6):

```sh
python3 scripts/naming-tree.py needs --tree CHECKOUT --map MAP.json --source-dir . --source-dir scripts --source-dir scripts/tests/naming
python3 scripts/naming-tree.py plan --tree CHECKOUT --snapshot CAPTURE/snapshot.json --map MAP.json
python3 scripts/naming-tree.py apply --tree CHECKOUT --plan PLAN.json --map MAP.json
```

Save the plan outside the checkout or in an ignored directory. It binds every
tracked/unignored input to the snapshot and lists every Lean source, including
`lakefile.lean`. A file containing an affected identifier needs compiler
references; missing exports produce unresolved entries and prevent applying
any file. An unexported file with no candidate identifiers remains explicitly
accounted for by its source digest. This is a lexical absence check, not an
inferred semantic reference. The selected-file planner's handling of comments,
strings and unresolved syntax still applies. Non-Lean documents and external
policy/source files remain separate migration obligations.

Before writing, application recomputes the whole plan, checks the map, snapshot,
tool sources, complete file inventory and current imported artifact digests.
A newly added file, a change to an unindexed file, a stale import or an edited
plan refuses before the first write. Source identity is the captured bytes,
not Git HEAD alone; committing identical bytes does not invalidate a plan.
Successful application is still followed by an owned build and N4 comparison.
Namespace syntax, depth changes, module/relocation rows and other unresolved
constructs remain refusals; whole-tree accounting does not waive them.

The exporters share `NamingReferencesCore` so candidate captures retain the
same constructor-case provenance as standalone reference exports. The optional
core library is outside production imports. Whole-tree preflight controls are
in `scripts/tests/test_naming_tree.py`.

`python3 scripts/check-naming-tool.py` exercises a synthetic shared-field
fixture end to end: compiler export, six transaction-field edits with four
message-field references preserved, elaboration of both versions (including
record literals, updates, projections, guards and `simp` proofs), independent
tampered-plan and stale-source refusals, and an inverse rename restoring exact
bytes. `--output FRESH_DIRECTORY` retains the raw compiler outputs, reference
bundles, maps and plan. This is a tool control, not the goal's real Jaune pilot
or the N4 fidelity checker. The focused Python controls are in
`scripts/tests/test_naming_apply.py`.

The reference exporter also resolves simple `case` labels whose proof goal
descends from an ordinary constructor `cases` goal. It checks the builtin
elaborator, the actual `casesOn` use, the constructor in the original goal,
and the direct/delayed metavariable assignment chain to the selected case.
This keeps a GAS opcode case unchanged when `Tx.gas` is renamed, while a
constructor rename updates its own case label. Leading-dot constructor
patterns retain the dot. Explicit/custom eliminators, compound case labels
and ambiguous or unavailable provenance remain unresolved; no spelling-based
exception suppresses these reports.

`scripts/tests/naming/RealSharedField.lean` imports the actual `Jaune.Machine`
module. Its optional `RealSharedField` build target checks inferred projections,
a transaction literal, Tx and Msg record updates, and downstream `simp` proofs.
For the real rename pilot, export references for both Machine and this client,
apply one map to both files in a disposable worktree, then build the client
against the renamed Machine artifact. Compare both modules with the fidelity
checker and retain the build/import receipts. This two-module pilot does not
establish complete migration coverage for every other client.

## 5. Retired names, whole words and source spellings

`scripts/check-naming.py` checks the compiler's declaration inventory, including
field and constructor definitions from the reference table (these are absent
from the declaration table alone). Private names are checked using their
user-written namespace, after removing the compiler's module/counter prefix.
Local variables, comments and strings are not declaration names. It uses the
canonical map's retired tokens directly, including compound tokens inside
longer camelCase or snake_case names. A registered source cannot exempt a
retired token.

The checker requires a reviewed JSON policy; it never guesses a dictionary
from the current identifiers or silently accepts an unknown token. The policy
has `schema_version: 1`, `words` (distinct lowercase whole English words),
`sources` and `bindings`. Each source is an object with a tree-relative `path`,
the exact file's `sha256`, and a nonempty `citation`. Each binding is keyed by
the full Lean name and contains `rule` (`"1"`, `"2"` or `"3"`), a `source`
key, its original `spelling`, and `style` (`"verbatim"`, `"lowerCamel"` or
`"upperCamel"`). The spelling must occur as an exact identifier in the pinned
source bytes and transliterate to the last component of the bound name.
Bindings cover that component only; a namespace needs its own binding or
whole words. Map rows whose primary rule is 1–3 require a matching binding.
Unbound components must consist of policy words, map-approved abbreviations
or numeric indices. Unsupported characters fail rather than disappear.

Source membership is a lexical check, not a claim that the cited source is
authoritative or the identifier means the same thing. Those are review inputs
under the naming rules. The policy must classify unchanged source-derived
names as well as renamed ones; the map alone cannot identify every pyspec
name. At this tooling checkpoint no production policy is registered. Building
that complete reviewed vocabulary and source inventory remains WN-a/WN-b
work; no whole-tree N3 result is claimed. The development controls use clearly
synthetic policy/source files. Policy additions must not be used to exempt a
retired token or disguise a private contraction as an English word.

With current compiler bundles for every file, run:

```sh
python3 scripts/check-naming.py --tree . --policy POLICY.json --source-root SOURCE_ROOT --root Jaune --root JauneConsensus --file Jaune/FILE.lean FILE.references.json
```

Repeat `--file` for every Lean file under both roots. Missing, extra or duplicate
files fail. Source bytes must equal their bundle's bytes. Whole-tree runs also
reject unused bindings. Selected-file and selected-root diagnostic runs are
explicitly labelled; only exactly the `Jaune` and `JauneConsensus` root set
receives the `whole-tree` scope label. Reports bind files, bundles, policy and
map by SHA-256. Exit 0 means no naming findings in that scope, 1 means naming
findings, and 2 means an unusable input or incomplete coverage. This lint does
not establish N2's semantic naming correctness or N4's rename fidelity.

`python3 scripts/check-naming-lint-tool.py [--output FRESH_DIRECTORY]` elaborates
a small fixture, confirms field/constructor coverage, then independently
reintroduces `bal` in execution and `Ctx` in consensus. Both mutations still
elaborate and fail the retired-name control. Restoring the baseline bytes is
the restoration evidence; it is not recompiled. The command needs the built
reference exporter and host Lean admission. The ordinary Python unit suite
does not launch Lean.

## 6. Compiler fidelity comparison

Build the optional `jaune-naming-fidelity` target through the owned-build
launcher. With current imports and Lean admission, export each source on each
side of a rename:

```sh
lake env .lake/build/bin/jaune-naming-fidelity SOURCE.lean MODULE BEFORE.json
python3 scripts/check-naming-fidelity.py --map MAP.json --before BEFORE.json --after AFTER.json
```

Repeat `--before` and `--after` for every exported module in the comparison.
Exports include the exact source, compiler navigation index, Lean version,
checked kernel constants, guard expressions, and attribute-bearing commands.
Reports bind every bundle and its source plus the map by SHA-256. Exit 0 is
equality within the exported scope, 1 a failed comparison, and 2 unusable or
unsupported input. The exporter never builds imports and fails on elaboration
errors or unsupported expressions/commands.

The comparison checks authored constant names under the exact map, the types
of all constants, and definition/opaque bodies. It includes inductive,
constructor and recursor metadata and definition safety. Bound variable names
and expression metadata are erased; universe parameters are indexed by
position. Theorem proof terms are not compared: theorem types and attributes
are checked, while the repository's axiom audit retains its separate job.
Generated constants are matched by their finite type/body/attribute graphs,
with a consistent bijection, rather than by generated names. Unreferenced
generated nodes are included too. A conservative matching failure is a refusal
to establish fidelity, not evidence that the two definitions differ.

Effective attributes include simp direction/priority, unfolding entries,
`csimp` and its replacement, inline settings, reducibility, instance priority/
scope/synthesis order and `implemented_by`. Whole commands carrying explicit
attributes are additionally compared with compiler-resolved identifiers; this
catches unfamiliar explicit attributes without treating their arguments as
free text. It is deliberately stronger than comparing only final attribute
flags. Local/scoped attribute commands are currently refused because their
scope histories need a separate comparison.

Guards are compared as a multiset of elaborated closed Boolean or proposition
expressions,
so moving a guard to another exported module preserves it, while changing or
dropping it fails. Parsed and expanded command information is inspected.
The original syntax node selects the complete guard; macro-generated branches
that share its source span do not substitute for it.
Proposition guards retain the proposition before Lean inserts its Bool coercion,
with a distinct tag from Boolean guards. Both still execute through Lean's
original guard elaborator. Ambiguous or unavailable information fails closed.
Schema 5 also retains additional checked commands:
`#guard_msgs`, the two axiom-audit commands, `run_cmd`, `#eval`/`#eval!`, and
`#count_heartbeats`. Their complete parsed syntax is compared, including options,
expected diagnostics, and enclosed commands. Source invocations and option
wrappers are retained too, so repeated macro checks cannot collapse merely
because their expansions share a source span. Compiler-resolved identifiers are
compared under the rename map. The audit commands read literal qualified names
with `getId`; those identifiers are mapped as literal names. Expected failures
are not misreported as successful Boolean guards or missing kernel constants.
Changes to a checked expression, audit target, allowed set or message filter
cannot disappear merely because the command creates no constant.

This syntax check is deliberately stricter than expression equality: diagnostic
text remains literal and changed spellings inside expected messages are not
silently accepted. Those golden changes still need their reserved gate packet
and a justified comparison. Local/scoped attribute histories remain unsupported.
Other hash commands (such as `#guard_expr`) are refused. The `#[...]` array
notation is not a hash command.

The low-level comparator's verdict remains `exported-modules`. It can compare
archived schema-3 and schema-4 exports as well as schema 5, but neither a list
of bundles nor an import list alone binds a candidate. Schema 4 introduced
records of the transitive
imports actually loaded by the frontend, with the logical paths of each
`.olean`, `.olean.server`, `.olean.private`, `.ir.sig` and `.ir` part (including
absent optional parts). `--imports` discovers this environment without
elaborating the source body.

### Candidate and dependency binding

`naming-candidate.py` adds source/import binding around the same comparator:

```sh
python3 scripts/naming-candidate.py capture --root CHECKOUT --source-dir . --source-dir scripts --source-dir scripts/tests/naming --module ROOT_MODULE --build-prefix BUILD_ARGV_JSON --admit-command ADMIT_ARGV_JSON --release-command RELEASE_ARGV_JSON --output FRESH_DIRECTORY
python3 scripts/naming-candidate.py compare --before BEFORE/snapshot.json --after AFTER/snapshot.json --map MAP.json
```

Repeat `--module` for multiple roots. For a standalone file that has no Lake
module target, also pass `--source-only MODULE`. This is allowed only for an
explicit root that no inventoried local source imports. Its imports still need
owned builds and artifact binding; its own source is fully elaborated by the
exporter, including checked commands. It produces no `.olean` for other files
to import. An imported local module cannot use this option to bypass its build.
If every selected module is such a leaf, capture records that no producer build
was needed; it never calls the build prefix with an empty target list.

The source directories describe Lean's
module layout; the longest matching directory wins. Every tracked or unignored
Lean source must be inventoried, including sources outside the selected roots.
Lean's own parser reads every header in one batch, including unchanged sources
outside the export set; a line scanner cannot silently miss a multiline import.
The compiler header inventory is retained and bound to the source inventory.
Hyphenated script filenames remain inventoried. Selected sources using Lean's
`module` visibility system are currently refused because that visibility has
not yet been added to the constant exporter.

All three command arguments are nonempty JSON argv arrays, never shell text.
The build prefix is the host's authorized owned-build invocation, ending just
before its targets (for Creme, through the `--` separator). Capture first builds
`jaune-naming-fidelity`, then uses an admitted compiler header pass to determine
the graph. It builds all selected producer modules through the same
prefix. It has no bare Lake build default. After that build succeeds, it takes
admission again, discovers imports, hashes their artifacts, exports the source
closure, checks that source/tool/artifact bytes stayed fixed, and releases in a
`finally` block. The header pass likewise always releases its own admission.
The caller provides host containment and admission commands appropriate to the
machine. Comparison itself requires neither Lean nor a hold.

Capture output must be outside the checkout. It retains the exact build/export
commands, terminal exits, logs, full candidate file inventory, module graph,
source-bound exports, exporter digest and resolved import artifact digests.
Local imports must resolve to the artifacts just built in that checkout;
uninventoried or shadowed local imports fail. Optional artifact parts cannot
appear or disappear unnoticed. The logical module path is retained before
following file symlinks, matching Lean's loading of separately cached parts.

Snapshot schema 3 records the standalone roots and producer set explicitly.
Schema 2 captures remain readable as all-producer captures. Fidelity is checked
separately for each maximal selected root and its transitive local imports.
Independent executables can each define `main`; their kernel constants and
checked commands are never pooled into one global namespace. A duplicate
constant within a single import environment still refuses. Shared dependency
objects are parsed once and reused across environments. The verdict reports
each environment rather than summing overlapping dependency counts. Moving a
check between independent environments fails comparison. Environment-root or
standalone-classification changes require explicit relocation support and
currently refuse.

Comparison checks both old and new graphs. Every changed Lean source and every
transitively affected local importer must be exported, even when the importer's
source did not change. Missing coverage is a setup failure, not an equality
verdict. The external artifact boundary must match by module/part digest;
absolute host paths may differ. Tool sources (including the map/apply helpers),
toolchain, Lake manifest and Lake configuration must agree. Changing
source-directory layout or build configuration
requires explicit relocation support and is currently refused.

A successful result is labelled `candidate-affected-local-closure`, with both
candidate inventory digests. The Git HEAD alone is not the input identity: a
capture may describe an uncommitted control candidate. The source graph and
fixed external artifacts justify leaving unaffected, byte-identical modules
outside the export set. Unknown hash commands, module-system visibility and
local/scoped attribute histories still fail closed; an affected importer using
one must be supported before a whole-candidate verdict can pass. No theorem bridge, cache
integrity check, axiom audit or full production rename verdict follows merely
from installing this tooling.

`python3 scripts/check-naming-fidelity-tool.py [--output FRESH_DIRECTORY]`
exercises the compiler and comparison with a shared-field rename, definition
body and attribute mutations, altered/dropped guards, guard moves within and
between modules, array literals and an unsupported-command refusal. The
altered supported files still elaborate: the comparison is the failing
control. Source restoration is byte-for-byte against the compiled baseline.
This is tooling evidence; it does not replace WP's two real EVM executions or
its actual `execFueled_eq_cached` attribute control.

`python3 scripts/check-naming-command-tool.py [--output FRESH_DIRECTORY]`
checks the supported command forms with the compiler. It requires the current
exporter, `AxiomAudit`, `UnionAxiomsFixture.Good` and
`Mathlib.Util.CountHeartbeats` artifacts and host admission. A rename passes;
changed expressions, removed or retargeted audits, widened union expectations,
changed message options and a removed heartbeat wrapper fail comparison after
successful elaboration. It never changes the production checks or builds.
