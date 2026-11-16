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
- Standard Lean / type tokens: `UInt8`, `UInt16`, `UInt32`, `UInt64`, `U8`,
  `U16`, `U32`, `U64`, `U256`, `U128`, `Hash32`, `Nat`, `Int`, `Bool`,
  `ByteArray`, `Bytes`

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

- `old`: old qualified Lean name (declaration, field, constructor, namespace or
  module).
- `new`: new qualified Lean name.
- `kind`: one of `"declaration"`, `"field"`, `"constructor"`, `"namespace"`,
  `"module"`, `"relocation"`.
- `layer`: one of `"execution"`, `"consensus"`, `"adapter"`.
- `rule`: rule number `"1"`–`"7"` (or comma-separated primary + secondary rule
  numbers, e.g. `"1, 7"`).
- `source`: non-empty citation of the authoritative naming source (EIP number,
  execution-apis/Engine schema file, EVMC header, consensus pyspec function,
  user decision, or `"Plain English (rule 4)"`).

Optional entry fields:

- `notes`: free-text clarification (for example alternate community spellings
  preserved in doc comments).
- `from_module`, `to_module`: required for, and only allowed on, `relocation`
  rows: the module the declaration leaves and the module it moves to.

Row semantics (`Renamer` in `scripts/check-naming-map.py`, shared by the
planner, N4 and N3):

- `declaration`, `field`, `constructor`: rename exactly one constant. A
  qualified descendant is not renamed by its parent's row; a source reference
  to such a descendant is reported until it has its own row. The namespace
  that bears a renamed declaration's name follows it in `namespace`, `end`,
  `open` and `export` syntax (the `B256` namespace follows the `B256` type);
  a declaration spelled inside that namespace without a row under the new
  namespace is reported.
- `field` rows keyed by a constructor binder path (`Jaune.TxType.three.receiver`
  -> `Jaune.TransactionType.eip4844.to`) rename a constructor argument: its
  binder in the inductive declaration, that binder's dependent uses (same
  compiler identity) and named arguments `TxType.three (receiver := ...)`.
  Binder names are erased in kernel terms, so N4 sees no change from them.
- A declaration Lean names itself (an anonymous `instance`) regenerates its
  name from renamed types without a source edit. N4 pairs it by kernel graph,
  trying its mapped name first; a row for it renames spelled references. A
  spelled reference to such a name containing a renamed word, without a row,
  is reported.
- `namespace`: rename the name and every descendant by prefix (`Jaune.B256`
  -> `Jaune.U256` renames `Jaune.B256.toNat` too), including the namespace in
  `namespace`, `end`, `open` and `export` syntax. The longest enclosing
  namespace row applies; an exact row for a descendant overrides it
  (`Jaune.Tx` namespace row plus `Jaune.Tx.gas` -> `Jaune.Transaction.gasLimit`).
  Nested namespace rows must agree.
- `module`: rename a module: its file moves within the same source directory,
  every import is rewritten, and private names change module prefix.
- `relocation`: move one declaration's command from `from_module` to
  `to_module`; `new` may equal `old` (a pure move) or rename it as well.
  Private names keep their counter and take the target module's prefix.

Private names (`_private.<module>.<counter>.<name>`) are renamed through their
user name. Module and constant names live in separate name spaces for the
one-to-one check.

Validation invariants enforced by `scripts/check-naming-map.py`:

1. Every entry has non-empty `old`, `new`, `kind`, `layer`, `rule`, and `source`,
   with `old != new` except on a relocation row. Missing or empty `source` fails
   closed. Relocation rows name two different modules.
2. `kind`, `layer`, and `rule` contain only valid registered values.
3. The map is a one-to-one bijection on `old -> new` within each name space
   (modules; constants and namespaces): no duplicate `old` names and no
   duplicate `new` names. The complete expanded bijection (namespace rows over
   every descendant) is checked by N4's authored-constant comparison.
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
with the exporter's reason where one exists. Any unresolved token prevents
application; exit 1 means an unresolved plan, exit 2 a setup/input refusal. No
spelling-based global replacement is used. The selected-file planner refuses
`module` and `relocation` rows; they need whole-tree planning (below).

Only an identifier occurrence covers a candidate word: a compiler reference
whose range is a dotted identifier, with the word as one component (a local
variable covers only its first component). Lean records a lifted `(← e)`
discriminant as one local variable spanning the whole expression; such a
compound range is not an occurrence of the identifiers inside it, so it never
covers an inner token that lacks its own provenance and never blocks a valid
inner edit. A renamed constant with a compound range is unresolved.

New spellings: a leading-dot constructor and a generalized projection (`x.f`)
resolve through a type, so they keep their component count. A lexical
spelling resolves in the namespace formed by the unspelled prefix of the old
name; that namespace is itself renamed by namespace rows, and the new name must
stay inside it. Depth below it may change (`gVerylow` -> `Gas.veryLow` inside
`namespace Jaune`); leaving it needs explicit qualification and is reported.
Every renamed descendant of an exact row needs its own map row; a parent rename
never silently skips a qualified descendant.

Name capture: renaming can make a spelling denote another constant (execution
`B256` -> `U256` inside `namespace JauneConsensus`, which has its own `U256`,
with `open Jaune`). Whole-tree planning therefore re-resolves every lexical
constant reference, renamed or not, in the scope it elaborated in (the
command's namespace and open declarations, after renaming) against the union
of all exported and referenced constants, using Lean's resolution order
(innermost namespace, exact name, root and open declarations). It first checks
that the same model reproduces the compiler's own answer before the rename;
references outside the model (aliases, term-level `open`, projections) are
counted as unverifiable and left to the build and N4. A captured or ambiguous
spelling is qualified with more components of its target (`Jaune.U256`); when
no qualification resolves uniquely, it is unresolved. Plans report checked,
unverifiable and requalified counts. An inverse rename keeps such
qualification.

Version-2 syntax metadata (both exporters) adds compiler-derived rows:

- `namespaces`: every `namespace`, `end`, `open` (also `open ... in` and
  term/tactic `open`) and `export` namespace identifier with its resolved full
  namespace. The exporter replays the scope stack and resolves with Lean's own
  `resolveNamespace` against the final environment; namespaces are only ever
  added, so a unique answer is the one Lean found. Ambiguous or `_root_`
  spellings are reported. Section labels name nothing and are left unchanged.
- `named_arguments`: each `(x := e)` with the function's constant head from the
  elaborator's own info for the function syntax, checked against the
  function's binder names. A binder of a structure constructor is that
  structure's field, so a field rename renames it; other binders are unchanged.
  A local or unresolved function head is reported with its reason.
- `commands`: every top-level command's range, the namespace and open
  declarations it elaborated under, and whether section variables, options or
  universes were in scope (used by relocation), plus `eof_scope` and `imports`.
- `unresolved_syntax`: precise reasons for `case` labels without provenance
  (compound label, several selected goals, no ordinary `cases` origin).
- `constructor_binders`: constructor argument binders with their constructor's
  identifier range (binder-path rows, section 3).
- `quotation_identifiers`: identifiers inside syntax quotations (outside
  antiquotations). Lean pre-resolves them as global names when the quotation
  elaborates; they carry no ordinary reference. The planner resolves each with
  the capture model below in the quoting command's scope and renames it. One
  that resolves to no constant of the capture universe (every exported and
  referenced name, so every renamed one) before the rename, and to none after
  it, pre-resolves to no renamed declaration (a quoted local binder such as
  `hx`) and stays as written; plans count these as `quotation_no_global`. A
  resolution the model cannot see (an alias, a term-level `open`) would change
  the quotation's pre-resolution, which N4 compares. An ambiguous spelling, one
  outside the modelled scope, or one a rename would make resolve is reported.
  A quoted generalized field projection (`(e).pres`) resolves through the type
  of `e`, which the quotation does not record: it is renamed only when every
  constant of the universe whose last component is that word gets the same new
  last component (or none is renamed), and is otherwise reported.

A definition spelled `def _root_.N.x` is compared as the full name and, when
renamed, respelled as `_root_.` plus the full new name. A renamed
declaration whose definition range spells its last component in any other
form the planner does not model is unresolved; only a definition whose range
does not spell its name at all (an anonymous `instance`) is skipped as
compiler-named.

Lean-generated constructor auxiliaries `C.injEq` and `C.inj` follow an
exact row for the constructor `C` without a row of their own; authorable
descendants such as `ext` still need rows.

A wildcard alternative `| _ => ...` that Lean expands into the constructors it
covers carries their references, but spells no name; a constructor rename
leaves it unchanged.

Numeric literals (`0x7f`) and import module names are not candidate
identifiers. A namespace renamed only through its members (at least two rows
agreeing on a rename of its last component, `Gloas.Inv` -> `Gloas.Invariant`)
is renamed in its syntax and lexical contexts; a lone moved member renames no
namespace.

Constructor case labels: the origin of a goal created by an ordinary `cases`
is the position of the `casesOn` minor premise that the goal's metavariable
chain descends from, in the elaborated proof term. The goal's target need not
mention the constructor (`cases r <;> simp only [...] at h` followed by
`case gas =>` resolves to `Jaune.Rinst.gas`).

Both exporters supplement the index with versioned, source-bound literal
ranges from Lean's original parse tree. Plain strings, character literals and
interpolated literal chunks remain unchanged; embedded expressions still need
compiler references, including nested interpolations and quoted terms. Byte
ranges are checked against the original UTF-8 text before masking. Without this
metadata, a string with an unescaped opening brace conservatively scans the
remaining source as words, so nested quotes cannot hide an affected use. This can overselect files during
initial inventory; a fresh export supplies the precise literal classification.

The registered `AxiomAudit` elaborators also supply references for literal
constant names in `#expect_axioms` and the allowed-axiom list of
`#union_axioms_of_modules`. The resolver uses the command kind, the elaborator's
owning module, the exact identifier and its environment entry. It never applies
namespace resolution to these names. The union's module prefix remains a
module-relocation obligation. A replacement elaborator, absent constant or
unavailable original source range leaves the token unresolved. Resolving an
audit name does not authorize changes to production audit rows or expectations.
`check-naming-syntax-tool.py` exercises these cases with the real compiler,
including literal-output changes and an unregistered replacement elaborator.

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
Unresolved constructs remain refusals; whole-tree accounting does not waive
them.

A project that requires the renamed project as a Lake package (Blanc
consuming Jaune) plans with `--consumer --dependency-snapshot DEP/snapshot.json`,
where the dependency snapshot is the dependency's own whole-tree capture at the
revision the consumer imports. Every consumer import from that package must be
a captured module whose package source (`.lake/packages/...`) has the captured
digest. The dependency's constants complete the capture universe, so a new
name that would be captured by a dependency constant the consumer never
mentions is still qualified. A module row naming a dependency module moves no
file; the consumer's imports of it are rewritten and other spellings are
reported as usual. Relocation rows of dependency modules are refused for a
consumer. The plan records `consumer` and the bound dependency captures, and
apply recomputes with them.

Consumer declarations inside renamed dependency namespaces: a consumer may
author declarations inside a namespace the map renames (Blanc's
`Jaune.Ninst.RunWith` under Jaune's `Jaune.Ninst`). They follow that
namespace, but never by silent inference: `naming-tree.py consumer-map --tree
CONSUMER --snapshot CAPTURE/snapshot.json --map MAP.json --dependency-snapshot
DEP/snapshot.json --output FILE` writes one explicit row per such declaration
(the new namespace prefix, the consumer's own last component; layer and rule
of the cited dependency row; the source names that row), refusing private
names, declarations in two modules and any collision with an existing or
renamed name. `plan --consumer-map FILE` rederives the rows from the same
capture and map and refuses a file that differs, so the file is reviewable
and part of the migration kit but cannot be hand-edited into the plan. The
plan records its path, digest and row count.

A consumer's reviewed sites live outside its tree: `plan --sites FILE` takes
the same schema as `scripts/naming-sites.json` and binds the file's digest in
the plan (apply recomputes with it). An external file may also decide
`replace`, with `new`, for a token the compiler index gives no reference at
all (a name literal such as `` `Jaune.gCallStipend `` or a spelling in an
unelaborated simp discharger); the replacement becomes a plan edit. `replace`
on a token reported for any other reason is itself unresolved, so it cannot
hide a map gap. A compound (parenthesized) reference range whose inner
identifiers carry their own references is decided `unchanged`: the plan
already respells the identifiers inside it.

Module rows move the file within its source directory and rewrite every import
whose lexed position matches Lean's header parse of that file (a mismatch
refuses). A namespace that shares the module's name (`namespace M` in `M.lean`)
is namespace syntax, renamed by namespace rows like any other. Any other
spelling of the old module name in code (lakefile roots, the audit command's
module prefix, name literals) is reported for a manual edit followed by N4.

Reviewed sites: `scripts/naming-sites.json` (optional, `schema_version` 1)
records individual tokens the tool cannot resolve and a reviewer decided, such
as a local binder the compiler index records no reference for or a user-named
goal (`?x`, `case x`). Each site has the file's `sha256`, a 1-based `line` and
`column` (code points), the exact `token`, a `decision` (only `unchanged`) and
a nonempty `reason`. A listed site moves from the file's `unresolved` list to
its `reviewed` list in the plan. A site whose file bytes differ, or that matches
no unresolved token, is itself unresolved, so the list never goes stale
silently, and any unlisted use still fails the plan. Relocation rows move the declaration's whole top-level command
(doc comment and attributes included, renames inside it applied) to the end of
the target module inside `section`/`open .../namespace ...`/`end` that restores
its namespace and open declarations. The planner reports, and never invents:
a command that also declares other names, section variables/options/universes
in scope, a target ending inside an open scope, a target that does not already
import a module the command references, an indexed module (the old module
included) still using the declaration without importing the target, and a
private declaration still used in its old module. Guards and other checks are
moved by hand; N4 compares them as expressions (section 6).

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
name. The registered production inputs are `scripts/naming-policy.json` (a
draft vocabulary regenerated by `python3 scripts/naming-census.py vocabulary`
from the repository's own prose, with no source bindings yet) and
`scripts/naming-inventory.json` (lint roots, policy provenance and explicitly
excluded sources such as the historical, non-elaborating
`scripts/flatten-pilot.lean`, whose affected tokens whole-tree plans count
rather than omit). `naming-census.py census` runs the lint in report mode over
both layers from a capture's exports and writes every flagged name. The policy
is a review input: until it is reviewed and source bindings are added, the
census is a report and no whole-tree N3 verdict is claimed. Declarations whose
range spells a keyword rather than their name (anonymous instances, syntax and
macro kinds) are not linted: notation keywords are out of N3 scope. The development controls use clearly
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

The map is applied as a function on compiler names (namespace prefixes,
private names, module rows). A declaration that Lean names itself — an
anonymous `instance`, whose definition range is the `instance` keyword — is
not authored by spelling: its name follows other names and changes without a
source edit, so it is matched by its kernel graph like a generated constant.
Each authored constant must stay in its (module-renamed) module unless a
relocation row moves it to the row's target; an unrecorded move fails
comparison, as does a relocation row whose source module is wrong. A
generated constant must stay in the modules that hold it (several, for a
realized copy), up to module rows and relocation links (below).

Effective attributes include simp direction/priority, unfolding entries,
`csimp` and its replacement, inline settings, reducibility, instance priority/
scope/synthesis order and `implemented_by`. Schema 7 adds the attributes
outside that set that change elaboration or compilation: `match_pattern`,
`default_instance` (class, priority and position in the class's list),
custom `induction`/`cases` eliminators, `ext` entries, elaborator and macro
registrations (`macro`, `term_elab`, `command_elab`, `tactic`, with their
syntax kinds), `elab_as_elim`, `elab_without_expected_type`, `specialize`,
`nospecialize`, `never_extract`, `export`, and the `protected` and
`noncomputable` modifiers. It also records instance order: each instance's
rank among the module's instances with the same discrimination-tree keys.
Lean tries equal-priority instances latest first, so swapping two anonymous
instances whose kernel graphs differ fails comparison even though their
compiler names swap with them.

Explicit attribute syntax is additionally compared with compiler-resolved
identifiers, keyed per declaration: the attribute list in each declaration's
modifiers is recorded with that declaration's name, and for a declaration
Lean names itself (an anonymous `instance`) with the name the index records at
its keyword. An attribute moved between the declarations of one `mutual`
block, or between two anonymous instances, fails even when no effective
record tracks it. Other attribute syntax in a command (`attribute [...]`
commands) is recorded with the command's declaration names. This catches
unfamiliar explicit attributes without treating their arguments as free text,
and is deliberately stronger than comparing only final attribute flags.
Local/scoped attribute commands are currently refused because their scope
histories need a separate comparison.

Guards are compared as a multiset of elaborated closed Boolean or proposition
expressions, each tagged with its module, so changing or dropping a guard
fails, and so does moving it to another module unless a relocation row links
the two modules (below). Parsed and expanded command information is inspected.
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

Module scope: every guard, checked command and attribute record keeps the
module it is in. Module rows rename modules; a relocation row links its two
modules, so checks and generated constants may move between them and
nowhere else. The direct imports of every module that no relocation row
touches are compared under module rows; a relocation module's imports may
change, and elsewhere only edges to relocation modules may be added or
dropped (a user of the moved declaration imports its new module).

This syntax check is deliberately stricter than expression equality: diagnostic
text remains literal and changed spellings inside expected messages are not
silently accepted. The one respelling admitted is the map's own: a
`#guard_msgs` expected text compares equal when it is exactly the before text
with every whole qualified-name token respelled under the names-only rule of
the quoted-spelling check (master decision 2026-11-16); a token several
constants could denote must respell one way, and any other change, or an old
name left unrenamed, fails. Those golden changes still need their reserved gate packet
and a justified comparison. Local/scoped attribute histories remain unsupported.
Other hash commands (such as `#guard_expr`) are refused. The `#[...]` array
notation is not a hash command.

Derived text (master decisions 2026-11-16). A deriving handler writes names
into string literals: `deriving Repr` prints each constructor's fully
qualified name and each structure field's label, and nests a field's value by
the label's width. A constant is *derived* when the exported compiler data
says so: an instance with no source declaration range whose value is `C.mk T`
for `C` in Repr/ToJson/FromJson, where `T` is declared in the same module by a
command whose deriving clause names `C` (or a `deriving instance` command
names both), plus that instance's auxiliaries by name prefix (no range
either). A hand-written instance, anonymous or not, has a range and is never
derived. In a derived constant, and only there, a string literal that is
exactly an old fully qualified constant name the map renames is compared as
its new name; in a derived Repr only, a literal that is exactly the old label
of a field of `T` whose field row changes the leaf is compared as the new
label, and the `Std.Format.nest` width of that field (label length + 4)
follows it. Every respelling is listed in the verdict
(`derived_literals_respelled`). Any other literal change fails, a hand-written
literal is compared as written, and other handlers' unqualified keys
(ToJson/FromJson) stay literal; the tree derives no ToJson/FromJson at G0a.
Derived Repr text of a renamed type therefore changes what `repr` prints;
user-visible output is held byte-identical by the catalogue (t8n, cli, golden
messages, trace, fixture lanes), not by N4.

The low-level comparator's verdict remains `exported-modules`. It can compare
archived schema-3 to schema-6 exports as well as schema 7 (the candidate
workflow below requires schema 7), but neither a list
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

A Lake project that consumes Jaune as a package (Blanc) has no exporter
target of its own. Pass `--tool-root JAUNE_TOOL_CHECKOUT --tool-build-prefix
BUILD_ARGV_JSON`: the exporter (which imports only Lean) is built there with
that checkout's owned-build prefix and runs in the candidate's `lake env`. The
two `lean-toolchain` files must be byte-identical. The snapshot records
`tool_root`, and its `tool_sources` digests are read from that checkout and
rechecked after export.

`--plan-only` captures for rename planning only: the bundles and imports are
bound as usual, but the kernel-graph reader is not run, so forms N4 does not
yet support (a `local`/`scoped` attribute command in a consumer) do not block
planning. The snapshot records `purpose: plan`, and `compare` refuses it.

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
authored constant within a single import environment still refuses. Schema 6
adds each local equation theorem's parent from Lean's equation registry. Copies
of a generated constant may coalesce only when neither is authored and their
complete kernel and attribute records (equation parent included) are identical:
Lean realizes auxiliaries such as equation lemmas, `_sparseCasesOn`
equations and `congr_simp` lemmas in every module that needs them, and an
importing environment holds one of the agreeing copies. Any difference, or an
authored name, still refuses. The parent reference
is itself compared under the map, and verdicts list the equations coalesced
on each side. Conflicting copies still refuse. Shared dependency
objects are parsed once and reused across environments. The verdict reports
each environment rather than summing overlapping dependency counts. With an
unchanged root set, moving a check between independent environments fails
comparison. A standalone-classification change still refuses.

Module rows may rename an environment root; each environment is then
compared with its image. When relocation changes the set of maximal
environment roots beyond that (a new test module that nothing imports), and
only when the map has module or relocation rows, comparison uses all
exported modules as one scope. That scope does not pool unrelated roots:
every check stays tagged with its module, so a hand-moved guard is compared
as an expression only where a relocation row links its old and new modules;
a guard, `#eval` or axiom-audit command moved between unrelated roots fails,
and so does a generated constant (an anonymous instance) moved between them.
Identical non-authored copies of one name coalesce as within an import
environment; any other name defined in two independent modules (each
executable's `main`) is keyed per module.

Comparison checks both old and new graphs. Every changed Lean source and every
transitively affected local importer must be exported, even when the importer's
source did not change. Missing coverage is a setup failure, not an equality
verdict. The external artifact boundary must match by module/part digest;
absolute host paths may differ. Tool sources (including the map/apply helpers),
toolchain, Lake manifest and Lake configuration must agree. Changing
source-directory layout or build configuration
requires explicit relocation support and is currently refused.

`--inventory scripts/naming-inventory.json` lets a registered, digest-pinned
exclusion that both candidates hold byte-identical (the historical
`flatten-pilot.lean`) stand in for an affected importer that cannot be
exported; the verdict lists it under `excluded_importers`.

Identifiers inside elaborated syntax quotations (`Lean.Syntax.ident`) that
pre-resolve to declarations are compared twice. The pre-resolved declarations
are compared under the map. The spelling is observable (`Syntax.getId`
returns it), so it must be exactly the apply tool's names-only respelling of
the old spelling under the map, at the depth the map implies; the raw text
may differ from it only by `«»` escapes. A capture qualification inside a
quotation (`B256` -> `Jaune.U256`) therefore fails comparison: it changes
what a consumer that inspects the identifier sees. Such a site needs a
separate, reviewed change (or a map that avoids the capture). Without
pre-resolution the whole quotation is compared literally.

Captures must come from the schema-7 exporter on both sides; `compare`
refuses older exports (recapture with the current tooling). Planning reads
only sources and references and still accepts schema 4 to 7.

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
