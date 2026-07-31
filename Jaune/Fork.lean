-- Fork.lean : protocol fork identities, fork rule data, and chain
-- configuration.
--
-- Three ideas are kept deliberately separate here.
--
--   * A `Fork` is an *identity*: a name for one set of execution rules in the
--     supported transition chain. It carries no semantics of its own.
--   * `ForkRules` is *data*: the constants, limits, schedules, and activation
--     sets that the one interpreter reads while it runs. Execution consumes
--     rules, never a fork identity, so there is no `if fork ≥ …` anywhere in
--     `Execution.lean`.
--   * A `ChainConfig` is an *activation schedule*: which rules a real chain
--     uses at which block. Mainnet timestamps belong in a named configuration,
--     never in reusable rule semantics.
--
-- `Fork.rules?` below is the single place where a fork identity becomes rule
-- data. Adding a fork's semantics means adding a case there and the rule data
-- it names -- not a second interpreter, and not a comparison at a use site.
--
-- Note for readers coming from the display code: the unrelated helper `fork`
-- in `Basic.lean` builds indented report sections and has nothing to do with
-- protocol forks.

import Jaune.Types

namespace Jaune

/-- One protocol rule set in the supported transition chain.

The chain begins at Prague; earlier mainnet forks are out of scope and are not
enumerated. Being listed here means the *identity* is known, not that its rules
are implemented: see `Fork.rules?`. -/
inductive Fork : Type
  | prague
  | osaka
  | bpo1
  | bpo2
deriving DecidableEq, Repr, Inhabited

namespace Fork

/-- The canonical label. These are the strings that fixture `network` fields
and the `--network` command-line option use. -/
def toString : Fork → String
  | .prague => "Prague"
  | .osaka => "Osaka"
  | .bpo1 => "BPO1"
  | .bpo2 => "BPO2"

instance : ToString Fork := ⟨Fork.toString⟩

/-- Strict label parsing. There is no fallback and no case folding: an
unrecognised label is an error at every caller, never Prague. -/
def ofString? : String → Option Fork
  | "Prague" => some .prague
  | "Osaka" => some .osaka
  | "BPO1" => some .bpo1
  | "BPO2" => some .bpo2
  | _ => none

/-- Every supported fork, in activation order. -/
def all : List Fork := [.prague, .osaka, .bpo1, .bpo2]

/-- Position in the supported transition chain.

This is the *only* ordering notion on forks, and it exists so that a
`ChainConfig` schedule can be checked for monotonicity. It is not a licence to
compare forks inside execution. -/
def index : Fork → Nat
  | .prague => 0
  | .osaka => 1
  | .bpo1 => 2
  | .bpo2 => 3

end Fork

/-- The blob-gas schedule (EIP-4844 and its later reparameterisations).

BPO1 and BPO2 are, on the execution layer, exactly a change to these three
numbers, which is why they are data and not code. -/
structure BlobSchedule : Type where
  /-- `TARGET_BLOB_GAS_PER_BLOCK`: the excess-blob-gas set point. -/
  target : Nat
  /-- `MAX_BLOB_GAS_PER_BLOCK`: the per-block blob gas ceiling. -/
  max : Nat
  /-- `BLOB_BASE_FEE_UPDATE_FRACTION`: the blob base-fee decay constant. -/
  baseFeeUpdateFraction : Nat
  /-- EIP-7918's `BLOB_BASE_COST`, or `none` before its reserve-price branch
  activates. -/
  reserveBaseCost : Option Nat
deriving DecidableEq, Repr

/-- Deployed-code and initcode size limits (EIP-170 and EIP-3860). -/
structure CodeLimits : Type where
  /-- `MAX_CODE_SIZE`: the largest code a contract creation may deposit. -/
  maxCodeSize : Nat
  /-- `MAX_INITCODE_SIZE`: the largest initcode a creation may run. -/
  maxInitCodeSize : Nat
deriving DecidableEq, Repr

/-- Per-transaction protocol limits.

`none` states that a limit is not active at the fork; it is not an unbounded
sentinel. This lets Prague retain its exact validation path while Osaka adds
EIP-7825 and EIP-7594 without a fork comparison at either use site. -/
structure TransactionLimits : Type where
  /-- EIP-7825: the largest gas limit a transaction may specify. -/
  maxGas : Option Nat
  /-- EIP-7594: the largest number of blobs one type-3 transaction may carry. -/
  maxBlobCount : Option Nat
deriving DecidableEq, Repr

/-- Limits on the encoded block envelope. -/
structure BlockLimits : Type where
  /-- EIP-7934: the largest accepted original RLP block encoding. -/
  maxRlpSize : Option Nat
deriving DecidableEq, Repr

/-- The `MODEXP` input bounds and gas schedule (EIP-198, EIP-2565, EIP-7823,
and EIP-7883).

Every number the precompile's pricing reads lives here, so a repricing fork is
a new record rather than a branch inside the precompile. -/
structure ModexpRules : Type where
  /-- EIP-7823: the largest value each of the three length headers may take.
  `none` before Osaka, where a header of any size was accepted and only the
  gas schedule bounded the work. -/
  maxLength : Option Nat
  /-- EIP-7883: the flat multiplication complexity charged when
  `max baseLength modulusLength ≤ 32`. `none` before Osaka, where the
  quadratic term applied at every size. -/
  flatComplexity : Option Nat
  /-- The multiplier on `words ^ 2` in the multiplication complexity. -/
  complexityCoeff : Nat
  /-- The per-byte weight of the exponent-length term beyond the first 32
  bytes. -/
  iterationCoeff : Nat
  /-- `GQUADDIVISOR`: the divisor applied to the complexity/iteration product.
  EIP-7883 removes the division by folding it into the other coefficients, so
  Osaka carries `1` rather than dropping the field. -/
  gasDivisor : Nat
  /-- The gas floor charged however cheap the computed cost is. -/
  minGas : Nat
deriving DecidableEq, Repr

/-- Opcodes whose availability changes along the supported transition chain.

An opcode this record switches off is not merely unimplemented: its byte is
undefined at that fork, so a contract reaching it halts on an invalid
instruction exactly as it would on any other unassigned byte. -/
structure OpcodeRules : Type where
  /-- EIP-7939 `CLZ` (0x1E), new at Osaka. -/
  clz : Bool
deriving DecidableEq, Repr

/-- Everything the interpreter needs to know about *which* rules it is running.

Execution reads this record and nothing else about the fork. The `fork` field
is the identity these rules were built for; it is provenance for reports and
error messages, not a dispatch key. -/
structure ForkRules : Type where
  /-- The fork identity these rules realise. -/
  fork : Fork
  /-- Blob gas target, ceiling, and base-fee update fraction. -/
  blob : BlobSchedule
  /-- Deployed-code and initcode size limits. -/
  code : CodeLimits
  /-- Per-transaction limits. -/
  tx : TransactionLimits
  /-- Encoded-block limits. -/
  block : BlockLimits
  /-- The `MODEXP` input bounds and gas schedule. -/
  modexp : ModexpRules
  /-- Which fork-gated opcodes are defined. -/
  op : OpcodeRules
  /-- The addresses at which a precompiled contract is active. -/
  precompiles : List Adr
deriving DecidableEq

/-- An address carries a precompile under these rules.

This replaces the former global `Adr.isPrecomp`, whose hard-wired `1 ≤ n ≤ 17`
range was a Prague fact stated at a use site. Precompile sets are not
contiguous in general -- Osaka's P256VERIFY sits at 0x100 -- so the rule is
carried as the activation set itself. -/
abbrev ForkRules.isPrecomp (rules : ForkRules) (a : Adr) : Prop :=
  a ∈ rules.precompiles

instance {rules : ForkRules} {a : Adr} : Decidable (rules.isPrecomp a) :=
  List.instDecidableMemOfLawfulBEq _ _

/-- Prague's blob schedule (EIP-4844 as amended for Prague). -/
def pragueBlobSchedule : BlobSchedule := {
  target := 0xC0000 -- 786432
  max := 1179648
  baseFeeUpdateFraction := 5007716
  reserveBaseCost := none
}

/-- Prague's code size limits. -/
def pragueCodeLimits : CodeLimits := {
  maxCodeSize := 24576 -- 0x6000
  maxInitCodeSize := 49152 -- 2 * 0x6000
}

/-- Prague has neither Osaka per-transaction limit. -/
def pragueTransactionLimits : TransactionLimits :=
  { maxGas := none, maxBlobCount := none }

/-- Prague has no protocol-level RLP block-size limit. -/
def pragueBlockLimits : BlockLimits :=
  { maxRlpSize := none }

/-- Prague's `MODEXP` schedule: EIP-2565 unchanged since Berlin. -/
def pragueModexpRules : ModexpRules := {
  maxLength := none
  flatComplexity := none
  complexityCoeff := 1
  iterationCoeff := 8
  gasDivisor := 3
  minGas := 200
}

/-- Prague's opcode set: 0x1E is still an unassigned byte. -/
def pragueOpcodeRules : OpcodeRules := { clz := false }

/-- The precompiles active at Prague: 0x01 through 0x11, contiguous.

Written out rather than computed from a range so that the set stays readable
against the specification's address table and so that later forks extend it by
appending an address, not by widening a bound. -/
def praguePrecompiles : List Adr := [
  0x01, -- ECRECOVER
  0x02, -- SHA256
  0x03, -- RIPEMD160
  0x04, -- IDENTITY
  0x05, -- MODEXP
  0x06, -- ALT_BN128_ADD
  0x07, -- ALT_BN128_MUL
  0x08, -- ALT_BN128_PAIRING
  0x09, -- BLAKE2F
  0x0a, -- POINT_EVALUATION
  0x0b, -- BLS12_G1ADD
  0x0c, -- BLS12_G1MSM
  0x0d, -- BLS12_G2ADD
  0x0e, -- BLS12_G2MSM
  0x0f, -- BLS12_PAIRING_CHECK
  0x10, -- BLS12_MAP_FP_TO_G1
  0x11  -- BLS12_MAP_FP2_TO_G2
]

/-- The Prague rule set. -/
def pragueRules : ForkRules := {
  fork := .prague
  blob := pragueBlobSchedule
  code := pragueCodeLimits
  tx := pragueTransactionLimits
  block := pragueBlockLimits
  modexp := pragueModexpRules
  op := pragueOpcodeRules
  precompiles := praguePrecompiles
}

instance : Inhabited ForkRules := ⟨pragueRules⟩

/-- Osaka's blob schedule.

EIP-7892 restates the schedule as blob *counts* — `BLOB_SCHEDULE_TARGET = 6`
and `BLOB_SCHEDULE_MAX = 9`, each multiplied by `GAS_PER_BLOB = 2 ^ 17` — which
evaluates to exactly the three numbers Prague already used. The
reparameterisation is what BPO1 and BPO2 later vary; Osaka itself does not move
the blob schedule. -/
def osakaBlobSchedule : BlobSchedule := {
  target := 6 * 131072
  max := 9 * 131072
  baseFeeUpdateFraction := 5007716
  reserveBaseCost := some (2 ^ 13)
}

/-- Osaka caps transaction gas at `2 ^ 24` (EIP-7825) and blobs at six
(EIP-7594). -/
def osakaTransactionLimits : TransactionLimits :=
  { maxGas := some 16777216, maxBlobCount := some 6 }

/-- Osaka's 10 MiB envelope minus the 2 MiB beacon-block safety margin
(EIP-7934). -/
def osakaBlockLimits : BlockLimits :=
  { maxRlpSize := some (10485760 - 2097152) }

/-- Osaka's `MODEXP` schedule: EIP-7823 bounds the three length headers and
EIP-7883 raises the price.

The repricing replaces the `words ^ 2 / 3` shape with `2 * words ^ 2` above 32
bytes and a flat `16` at or below it, doubles the exponent-length weight, and
lifts the floor from 200 to 500. -/
def osakaModexpRules : ModexpRules := {
  maxLength := some 1024
  flatComplexity := some 16
  complexityCoeff := 2
  iterationCoeff := 16
  gasDivisor := 1
  minGas := 500
}

/-- Osaka's opcode set: EIP-7939 assigns `CLZ` to 0x1E. -/
def osakaOpcodeRules : OpcodeRules := { clz := true }

/-- The precompiles active at Osaka: Prague's contiguous block plus EIP-7951's
`P256VERIFY`.

It sits at 0x100 rather than continuing the run, which is exactly why the
activation set is carried as a set: appending one address is the whole rule,
and no bound anywhere has to learn about the gap. -/
def osakaPrecompiles : List Adr := praguePrecompiles ++ [
  0x100 -- P256VERIFY
]

/-- The Osaka rule set.

Only the fields Osaka actually moves differ from Prague; the shared ones are
named through Prague's definitions so that a later Prague correction cannot
silently desynchronise the two. -/
def osakaRules : ForkRules := {
  fork := .osaka
  blob := osakaBlobSchedule
  code := pragueCodeLimits
  tx := osakaTransactionLimits
  block := osakaBlockLimits
  modexp := osakaModexpRules
  op := osakaOpcodeRules
  precompiles := osakaPrecompiles
}

/-- BPO1's blob schedule (EIP-7892's first blob-parameter-only fork).

A BPO fork is, on the execution layer, *only* these numbers. The pinned EELS
revision confirms it: the entire `osaka` to `bpo1` module diff outside
docstrings and import formatting is `BLOB_SCHEDULE_TARGET` 6 to 10,
`BLOB_SCHEDULE_MAX` 9 to 15, and `BLOB_BASE_FEE_UPDATE_FRACTION` 5007716 to
8346193. The counts are multiplied by `GAS_PER_BLOB = 2 ^ 17` here because
`BlobSchedule` carries gas, not blobs. -/
def bpo1BlobSchedule : BlobSchedule := {
  target := 10 * 131072
  max := 15 * 131072
  baseFeeUpdateFraction := 8346193
  reserveBaseCost := osakaBlobSchedule.reserveBaseCost
}

/-- BPO2's blob schedule: the same three numbers moved again, to 14 blobs, 21
blobs, and 11684671. -/
def bpo2BlobSchedule : BlobSchedule := {
  target := 14 * 131072
  max := 21 * 131072
  baseFeeUpdateFraction := 11684671
  reserveBaseCost := osakaBlobSchedule.reserveBaseCost
}

/-- The BPO1 rule set: Osaka's rules with Osaka's blob schedule replaced.

Written as an update of `osakaRules` rather than as a fresh record so that the
"blob parameter only" claim is enforced by construction. A later Osaka
correction reaches BPO1 automatically, and no BPO fork can silently acquire an
execution rule of its own. -/
def bpo1Rules : ForkRules :=
  { osakaRules with fork := .bpo1, blob := bpo1BlobSchedule }

/-- The BPO2 rule set: Osaka's rules with BPO2's blob schedule. -/
def bpo2Rules : ForkRules :=
  { osakaRules with fork := .bpo2, blob := bpo2BlobSchedule }

/-- Error tag for a fork whose identity is known but whose rules this build
does not implement.

Every fork this build declares now resolves, so nothing reaches this branch
today. It is retained because it is the only correct answer for the next
declared-but-unimplemented fork: falling back to another fork's rules would
turn a missing implementation into a silent consensus fault. -/
def unsupportedForkTag : String := "UnsupportedForkError"

/-- The single place where a fork identity becomes rule data.

`none` means the fork is declared but not yet executable. It must never be
answered with another fork's rules: running Osaka blocks under Prague semantics
because Osaka is unfinished would turn a missing implementation into a silent
consensus fault. -/
def Fork.rules? : Fork → Option ForkRules
  | .prague => some pragueRules
  | .osaka => some osakaRules
  | .bpo1 => some bpo1Rules
  | .bpo2 => some bpo2Rules

/-- `Fork.rules?` as a failing lookup, with the error every explicit-fork entry
point reports for an unimplemented fork. -/
def Fork.rules (f : Fork) : Except String ForkRules :=
  match f.rules? with
  | some rules => .ok rules
  | none =>
    .error
      s!"{unsupportedForkTag} : fork {f} is a declared protocol fork whose \
         execution rules are not implemented in this build"

/-- A fork's rules become active at this timestamp. -/
structure ForkActivation : Type where
  fork : Fork
  timestamp : Nat
deriving DecidableEq, Repr

/-- A chain's identity and its fork activation schedule.

Kept apart from `ForkRules` on purpose: the rules say what Osaka *is*, the
configuration says when a particular chain switched to it. Mainnet timestamps
belong in a named configuration built from this structure, never inside rule
semantics. -/
structure ChainConfig : Type where
  chainId : UInt64
  activations : List ForkActivation
deriving DecidableEq, Repr

/-- Error tag for a schedule that does not determine an unambiguous fork. -/
def invalidChainConfigTag : String := "InvalidChainConfigError"

------------------ TYPED SEMANTIC REASONS: CONTEXT ------------------

-- P0.7 of ~/plans/integrity.md replaces text used as a semantic discriminant
-- with typed reasons. Declared here, ahead of `ChainConfig`, precisely so its
-- own producers can build them directly: Step 2 of the integrity arc (P0.1,
-- P0.5) wires `ChainConfig.validate` and `ChainConfig.forkAt` below to
-- construct these reasons and cross back to the legacy `String`-carrying
-- `Except` with `Except.mapError`, applied to the renderer named here -- never
-- a hand-written duplicate of its text. `ChainConfig.checkChainId`
-- (`Jaune/Transaction.lean`, the first module downstream where `BlockChain`
-- exists alongside `ChainConfig`) does the same for `chainIdMismatch`. The
-- remaining producer corpus (~100 other `String`-carrying `Except` sites) is
-- untouched until Steps 9 and 10; every renderer arm without a producer yet
-- still reproduces the exact byte-for-byte message its future producer will
-- emit.
--
-- Placement is frozen by `scripts/report-integrity-design.md` section 6.
-- Context and support reasons live in this module because
-- `ChainConfig.validate`, `ChainConfig.forkAt`, `ChainConfig.rulesAt`, and
-- `Fork.rules` are their first producers, and this module imports only
-- `Jaune/Types.lean`, so nothing downstream can create an import cycle by
-- naming them. The shared diagnostic vocabulary is declared here for the same
-- reason: this is the most upstream module that names an error tag. It
-- precedes `ChainConfig` itself in this file so `validate`/`forkAt` can name
-- it directly.

/-- Diagnostic-only context text carried beneath a typed reason.

Only a renderer may read it. No semantic branch, no routing decision, and no
fixture classifier is permitted to inspect it -- constructor identity is the
discriminant, and this is the free text that follows it. It is deliberately
its own two-constructor type rather than an optional string: an optional
string is precisely the carrier the semantic-integrity gate keeps out of the
`Jaune.lean` import closure, and this is not an error channel. -/
inductive ErrorDetail : Type
  | none
  | text (s : String)
deriving DecidableEq, Repr, Inhabited

/-- The rendering convention every tag in this executable already follows: a
bare tag, or a tag opening free diagnostic text at a fixed `" : "`. Every
renderer in the typed skeleton goes through this one function, so a tag can
never acquire a second spelling. -/
def renderTagged (tag : String) : ErrorDetail → String
  | .none => tag
  | .text s => s!"{tag} : {s}"

#guard renderTagged "SomeTag" .none = "SomeTag"
#guard renderTagged "SomeTag" (.text "why") = "SomeTag : why"

/-- Error tag for a configured call whose chain identity contradicts the
snapshot it was handed.

Separate from `invalidChainConfigTag`: the schedule can be perfectly valid and
still describe a different chain than the snapshot. Produced by
`ChainConfig.checkChainId`; deliberately not routed to any fixture identity,
because a contradictory caller context is not evidence that a candidate block
is invalid. -/
def chainIdMismatchTag : String := "ChainIdMismatchError"

/-- Error tag for a timestamp that precedes the first activation of an
otherwise valid schedule.

Separate from `invalidChainConfigTag` for the reason P0.5 gives: a block from
an era this build does not implement is outside the declared domain, not a
malformed configuration, and never an invalid block. Produced by
`ChainConfig.forkAt`, together with the nonzero mainnet floor. -/
def unsupportedEraTag : String := "UnsupportedEraError"

/-- Why a configuration, or the pairing of a configuration with a snapshot, is
not a usable execution context.

This is the outer channel: none of these is a verdict about a candidate
block. -/
inductive ChainContextError : Type
  /-- The activation schedule names no fork at all. -/
  | emptySchedule
  /-- Two adjacent activations do not move strictly forward in time. -/
  | nonIncreasingActivations (prev next : ForkActivation)
  /-- Two adjacent activations do not move forward through the fork order. -/
  | nonForwardActivations (prev next : ForkActivation)
  /-- The configured chain identity is not the snapshot's. -/
  | chainIdMismatch (configured actual : UInt64)
deriving DecidableEq, Repr

/-- The one renderer for `ChainContextError`.

The first three arms reproduce today's `ChainConfig.validate` messages exactly;
the golden guards below pin them against the live producer as well as against
the literal text. -/
def ChainContextError.render : ChainContextError → String
  | .emptySchedule =>
    s!"{invalidChainConfigTag} : the activation schedule is empty"
  | .nonIncreasingActivations prev next =>
    s!"{invalidChainConfigTag} : activation timestamps must strictly \
       increase, but {next.fork} at {next.timestamp} does not follow \
       {prev.fork} at {prev.timestamp}"
  | .nonForwardActivations prev next =>
    s!"{invalidChainConfigTag} : activations must move forward through the \
       fork order, but {next.fork} does not follow {prev.fork}"
  | .chainIdMismatch configured actual =>
    s!"{chainIdMismatchTag} : the configuration names chain \
       {configured.toNat}, but the snapshot is chain {actual.toNat}"

/-- Why an input is outside the domain this build implements.

Not a configuration fault and not a block verdict: the configuration may be
exactly right and the block perfectly valid, and this build still cannot say
what executing it means. -/
inductive SupportError : Type
  /-- A declared fork whose rules are not implemented in this build. -/
  | unsupportedFork (fork : Fork)
  /-- A timestamp before the earliest era this configuration supports. -/
  | unsupportedEra (timestamp floor : Nat)
deriving DecidableEq, Repr

/-- The one renderer for `SupportError`. The first arm reproduces today's
`Fork.rules` message exactly. -/
def SupportError.render : SupportError → String
  | .unsupportedFork f =>
    s!"{unsupportedForkTag} : fork {f} is a declared protocol fork whose \
       execution rules are not implemented in this build"
  | .unsupportedEra timestamp floor =>
    s!"{unsupportedEraTag} : timestamp {timestamp} precedes the earliest \
       era this configuration supports, which begins at {floor}"

-- Golden guards, one representative per constructor. Each pins the exact
-- rendered bytes, so a later step cannot change an externally observed
-- message by accident while migrating a producer.
#guard ChainContextError.render .emptySchedule
  = "InvalidChainConfigError : the activation schedule is empty"
#guard ChainContextError.render (.nonIncreasingActivations ⟨.prague, 5⟩ ⟨.osaka, 5⟩)
  = "InvalidChainConfigError : activation timestamps must strictly increase, \
     but Osaka at 5 does not follow Prague at 5"
#guard ChainContextError.render (.nonForwardActivations ⟨.osaka, 5⟩ ⟨.prague, 9⟩)
  = "InvalidChainConfigError : activations must move forward through the fork \
     order, but Prague does not follow Osaka"
#guard ChainContextError.render (.chainIdMismatch 7 1)
  = "ChainIdMismatchError : the configuration names chain 7, but the snapshot \
     is chain 1"
#guard SupportError.render (.unsupportedFork .osaka)
  = "UnsupportedForkError : fork Osaka is a declared protocol fork whose \
     execution rules are not implemented in this build"
#guard SupportError.render (.unsupportedEra 100 200)
  = "UnsupportedEraError : timestamp 100 precedes the earliest era this \
     configuration supports, which begins at 200"


namespace ChainConfig

/-- Every activation after the first must move strictly forward in both time
and fork order. Equal timestamps would make the active fork depend on list
order, and a non-increasing fork sequence would describe a chain that goes
backwards. -/
private def validateSteps : List ForkActivation → Except String Unit
  | [] => .ok ()
  | [_] => .ok ()
  | prev :: next :: rest => do
    if next.timestamp ≤ prev.timestamp then
      .error
        s!"{invalidChainConfigTag} : activation timestamps must strictly \
           increase, but {next.fork} at {next.timestamp} does not follow \
           {prev.fork} at {prev.timestamp}"
    if next.fork.index ≤ prev.fork.index then
      .error
        s!"{invalidChainConfigTag} : activations must move forward through the \
           fork order, but {next.fork} does not follow {prev.fork}"
    validateSteps (next :: rest)

/-- A schedule is usable when it covers every block unambiguously: it names at
least one fork, and every later activation moves strictly forward in time and
fork order. There is deliberately no requirement that the first activation
begin at timestamp 0 -- a configuration may support only eras from some later
floor onward, and a timestamp before that floor is `SupportError.unsupportedEra`
(from `forkAt` below), never `InvalidChainConfigError`. -/
def validate (cfg : ChainConfig) : Except String Unit := do
  match cfg.activations with
  | [] =>
    .error s!"{invalidChainConfigTag} : the activation schedule is empty"
  | _ :: _ =>
    validateSteps cfg.activations

/-- The last activation at or before `timestamp`, without validating the
schedule. Callers should prefer `forkAt`. -/
def forkAt? (cfg : ChainConfig) (timestamp : Nat) : Option Fork :=
  (cfg.activations.filter (·.timestamp ≤ timestamp)).getLast?.map
    ForkActivation.fork

/-- The fork active at `timestamp`, rejecting schedules that do not determine
one and timestamps that precede this configuration's earliest supported era.
A timestamp before the first activation is `SupportError.unsupportedEra`, not
an invalid configuration: the schedule is exactly as usable as any other, this
build simply does not implement anything before its declared floor. -/
def forkAt (cfg : ChainConfig) (timestamp : Nat) : Except String Fork := do
  cfg.validate
  match cfg.forkAt? timestamp with
  | some f => .ok f
  | none =>
    -- `cfg.validate` above guarantees `cfg.activations` is nonempty, so
    -- `head?` always finds the floor; the fallback is unreachable in practice
    -- but keeps this total without threading a nonemptiness proof through.
    let floor := (cfg.activations.head?.map (·.timestamp)).getD 0
    Except.mapError SupportError.render (.error (.unsupportedEra timestamp floor))

/-- The rules active at `timestamp`. Fails if the schedule is unusable or if
the selected fork's rules are not implemented. -/
def rulesAt (cfg : ChainConfig) (timestamp : Nat) : Except String ForkRules := do
  (← cfg.forkAt timestamp).rules

/-- The configuration of a chain that is at Prague from genesis and never
transitions. -/
def pragueOnly (chainId : UInt64) : ChainConfig :=
  { chainId := chainId, activations := [⟨.prague, 0⟩] }

end ChainConfig

/-- Mainnet's activation timestamps, read from the `FORK_CRITERIA` of the EELS
fork modules at the pinned fixture-release revision.

They are recorded as named constants, and used only by `mainnetChainConfig`
below, because an activation timestamp is a fact about one chain and never a
rule: nothing in `ForkRules` may learn them. -/
def mainnetPragueTimestamp : Nat := 1746612311

/-- Mainnet's Osaka activation (EIP-7607), 2025-12-03 21:49:11 UTC. -/
def mainnetOsakaTimestamp : Nat := 1764798551

/-- Mainnet's BPO1 activation, 2025-12-09 14:21:11 UTC. -/
def mainnetBpo1Timestamp : Nat := 1765290071

/-- Mainnet's BPO2 activation, 2026-01-07 01:01:11 UTC. -/
def mainnetBpo2Timestamp : Nat := 1767747671

/-- Ethereum mainnet, over the chain of forks this build supports.

The supported transition chain begins at Prague, at its real historical
activation `mainnetPragueTimestamp` -- not at genesis. This build implements no
pre-Prague era, so a configured mainnet block timestamped before that floor
must not silently run under Prague rules: `ChainConfig.forkAt` reports it as
`SupportError.unsupportedEra` rather than resolving it to any fork at all. -/
def mainnetChainConfig : ChainConfig := {
  chainId := 1
  activations := [
    ⟨.prague, mainnetPragueTimestamp⟩,
    ⟨.osaka, mainnetOsakaTimestamp⟩,
    ⟨.bpo1, mainnetBpo1Timestamp⟩,
    ⟨.bpo2, mainnetBpo2Timestamp⟩
  ]
}

/-- One activation boundary, as named by a fixture `network` label of the form
`<before>To<after>AtTime<n>`.

A transition is a *schedule*, not a fork: it is turned into a `ChainConfig` by
`chainConfig` below, and execution then reads rules from the block timestamp
exactly as it does on a configured chain. -/
structure ForkTransition : Type where
  /-- The fork active from genesis up to, but excluding, `timestamp`. -/
  before : Fork
  /-- The fork active from `timestamp` onwards. -/
  after : Fork
  /-- The activation timestamp. -/
  timestamp : Nat
deriving DecidableEq, Repr

namespace ForkTransition

/-- Split on the *only* occurrence of `sep`. A second occurrence is a parse
failure rather than a choice of split point. -/
private def splitPair? (sep s : String) : Option (String × String) :=
  match s.splitOn sep with
  | [before, after] => some ⟨before, after⟩
  | _ => none

/-- The `AtTime` suffix is a decimal count of seconds, optionally abbreviated
with a `k` for the thousands the fixture labels actually use. -/
private def timestampOfString? (s : String) : Option Nat :=
  match s.splitOn "k" with
  | [digits, ""] => digits.toNat?.map (· * 1000)
  | [digits] => digits.toNat?
  | _ => none

private def timestampToString (timestamp : Nat) : String :=
  if timestamp ≠ 0 ∧ timestamp % 1000 = 0 then
    s!"{timestamp / 1000}k"
  else
    ToString.toString timestamp

/-- The canonical label. -/
def toString (t : ForkTransition) : String :=
  s!"{t.before}To{t.after}AtTime{timestampToString t.timestamp}"

instance : ToString ForkTransition := ⟨ForkTransition.toString⟩

/-- Strict label parsing. Both fork names must be forks this build knows, so a
historical transition such as `CancunToPragueAtTime15k` fails here rather than
being run through one of its endpoints. -/
def ofString? (label : String) : Option ForkTransition := do
  let ⟨forkLabels, timeLabel⟩ ← splitPair? "AtTime" label
  let timestamp ← timestampOfString? timeLabel
  let ⟨beforeLabel, afterLabel⟩ ← splitPair? "To" forkLabels
  let before ← Fork.ofString? beforeLabel
  let after ← Fork.ofString? afterLabel
  return ⟨before, after, timestamp⟩

/-- The schedule a transition label names.

Whether it is *usable* is `ChainConfig.validate`'s answer, not this function's:
a label may name an activation at genesis or a backwards step, and those are
rejected where every other unusable schedule is. Exposed independent of any
chain identity: whether a transition names a usable schedule does not depend
on which chain runs it, so a caller that only wants to check the schedule
shape (`Main.lean`'s `--network` validation, before any fixture supplies a
concrete chain ID) needs no placeholder identity to construct one. -/
def activations (t : ForkTransition) : List ForkActivation :=
  [⟨t.before, 0⟩, ⟨t.after, t.timestamp⟩]

def chainConfig (chainId : UInt64) (t : ForkTransition) : ChainConfig :=
  { chainId := chainId, activations := t.activations }

end ForkTransition

/-- What a fixture suite's `network` label names: one static fork, or one
supported transition schedule.

Static suites keep passing an explicit `Fork` to the explicit-fork entry
points; only a transition builds a `ChainConfig` and lets the block timestamp
choose. -/
inductive NetworkSpec : Type
  | static (f : Fork)
  | transition (t : ForkTransition)
deriving DecidableEq, Repr

namespace NetworkSpec

/-- The canonical label. -/
def toString : NetworkSpec → String
  | .static f => f.toString
  | .transition t => t.toString

instance : ToString NetworkSpec := ⟨NetworkSpec.toString⟩

/-- Strict label parsing: a static fork name first, then a transition label.
Anything else is `none`, at every caller. -/
def ofString? (label : String) : Option NetworkSpec :=
  match Fork.ofString? label with
  | some f => some (.static f)
  | none => (ForkTransition.ofString? label).map .transition

/-- The forks a label can select. A static label can only ever run its own
fork; a transition can run either endpoint, depending on the block. -/
def forks : NetworkSpec → List Fork
  | .static f => [f]
  | .transition t => [t.before, t.after]

end NetworkSpec

-- Guard helper. `Execution.lean` has the same pair for its own `#guard`s, but
-- it sits downstream of this file, so the check is restated rather than
-- imported backwards.
private def guardErrOf {α : Type} : Except String α → String
  | .error e => e
  | .ok _ => "unexpected success"

private def guardHasTag {α : Type} (tag : String) (e : Except String α) : Bool :=
  let err := guardErrOf e
  err = tag || String.isPrefixOf (tag ++ " : ") err

-- Fork labels round-trip, and nothing else parses.
#guard Fork.all.all (fun f => Fork.ofString? f.toString = some f)
#guard Fork.ofString? "Prague" = some .prague
#guard Fork.ofString? "Osaka" = some .osaka
#guard Fork.ofString? "BPO1" = some .bpo1
#guard Fork.ofString? "BPO2" = some .bpo2
#guard (Fork.ofString? "Cancun").isNone
#guard (Fork.ofString? "prague").isNone
#guard (Fork.ofString? "").isNone
#guard Fork.all.length = 4
#guard Fork.all.map Fork.index = [0, 1, 2, 3]

-- The central rule values are the Prague constants this build has always used.
#guard pragueRules.fork = .prague
#guard pragueRules.blob.target = 786432
#guard pragueRules.blob.max = 1179648
#guard pragueRules.blob.baseFeeUpdateFraction = 5007716
#guard pragueRules.blob.reserveBaseCost = none
#guard pragueRules.code.maxCodeSize = 24576
#guard pragueRules.code.maxInitCodeSize = 2 * pragueRules.code.maxCodeSize
#guard pragueRules.tx.maxGas = none
#guard pragueRules.tx.maxBlobCount = none
#guard pragueRules.block.maxRlpSize = none
#guard pragueRules.modexp.maxLength = none
#guard pragueRules.modexp.flatComplexity = none
#guard pragueRules.modexp.gasDivisor = 3
#guard pragueRules.modexp.minGas = 200
#guard pragueRules.op.clz = false

-- Prague's precompile activation set is exactly 0x01 through 0x11, which is
-- what the former `1 ≤ a.toNat ∧ a.toNat ≤ 17` range said.
#guard pragueRules.precompiles.length = 17
#guard (List.range' 1 17).all (fun n => pragueRules.isPrecomp (Nat.toAdr n))
#guard ¬ pragueRules.isPrecomp (0x00 : Adr)
#guard ¬ pragueRules.isPrecomp (0x12 : Adr)
#guard ¬ pragueRules.isPrecomp (0x100 : Adr)

-- Osaka shares the Prague blob target/max/update fraction, stated through the
-- EIP-7892 blob-count product rather than assumed, and adds EIP-7918's reserve
-- base cost.
#guard osakaRules.fork = .osaka
#guard osakaRules.code = pragueRules.code
#guard osakaBlobSchedule.target = 786432
#guard osakaBlobSchedule.max = 1179648
#guard osakaBlobSchedule.baseFeeUpdateFraction =
  pragueBlobSchedule.baseFeeUpdateFraction
#guard osakaBlobSchedule.reserveBaseCost = some 8192
#guard osakaRules.tx.maxGas = some (2 ^ 24)
#guard osakaRules.tx.maxBlobCount = some 6
#guard osakaRules.block.maxRlpSize = some 8388608
#guard osakaRules.modexp.maxLength = some 1024
#guard osakaRules.modexp.flatComplexity = some 16
#guard osakaRules.modexp.complexityCoeff = 2
#guard osakaRules.modexp.iterationCoeff = 2 * pragueRules.modexp.iterationCoeff
#guard osakaRules.modexp.gasDivisor = 1
#guard osakaRules.modexp.minGas = 500
#guard osakaRules.op.clz = true

-- P256VERIFY is appended, so Prague's seventeen keep their addresses and the
-- eighteenth is reachable only under Osaka rules. Nothing in between becomes a
-- precompile by widening a range.
#guard osakaRules.precompiles.length = 18
#guard osakaRules.precompiles.take 17 = pragueRules.precompiles
#guard osakaRules.isPrecomp (0x100 : Adr)
#guard ¬ pragueRules.isPrecomp (0x100 : Adr)
#guard ¬ osakaRules.isPrecomp (0x12 : Adr)
#guard ¬ osakaRules.isPrecomp (0xFF : Adr)
#guard ¬ osakaRules.isPrecomp (0x101 : Adr)
#guard (List.range' 1 17).all (fun n => osakaRules.isPrecomp (Nat.toAdr n))

-- A BPO fork is Osaka with three different blob numbers. These two guards say
-- exactly that, and they say it about the whole record: undoing the identity
-- and the blob schedule must give Osaka back, so no BPO fork can acquire a
-- transaction limit, opcode, precompile, or gas rule of its own.
#guard { bpo1Rules with fork := .osaka, blob := osakaBlobSchedule } = osakaRules
#guard { bpo2Rules with fork := .osaka, blob := osakaBlobSchedule } = osakaRules
#guard bpo1Rules.fork = .bpo1
#guard bpo2Rules.fork = .bpo2

-- The three moving numbers, as blob counts times `GAS_PER_BLOB`, and the
-- reserve base cost EIP-7918 introduced at Osaka and no BPO fork changes.
#guard bpo1Rules.blob.target = 10 * 131072
#guard bpo1Rules.blob.max = 15 * 131072
#guard bpo1Rules.blob.baseFeeUpdateFraction = 8346193
#guard bpo2Rules.blob.target = 14 * 131072
#guard bpo2Rules.blob.max = 21 * 131072
#guard bpo2Rules.blob.baseFeeUpdateFraction = 11684671
#guard bpo1Rules.blob.reserveBaseCost = some 8192
#guard bpo2Rules.blob.reserveBaseCost = some 8192

-- Each fork's blob schedule is distinct from its neighbour's, and the target
-- and ceiling both move strictly upwards along the supported chain.
#guard osakaBlobSchedule ≠ bpo1BlobSchedule
#guard bpo1BlobSchedule ≠ bpo2BlobSchedule
#guard [pragueBlobSchedule, osakaBlobSchedule, bpo1BlobSchedule,
    bpo2BlobSchedule].map BlobSchedule.target = [786432, 786432, 1310720, 1835008]
#guard [pragueBlobSchedule, osakaBlobSchedule, bpo1BlobSchedule,
    bpo2BlobSchedule].map BlobSchedule.max = [1179648, 1179648, 1966080, 2752512]
#guard [pragueBlobSchedule, osakaBlobSchedule, bpo1BlobSchedule,
    bpo2BlobSchedule].map BlobSchedule.baseFeeUpdateFraction
  = [5007716, 5007716, 8346193, 11684671]

-- Every declared fork resolves in this build, so `Fork.rules` is total here and
-- the unsupported-fork branch is unreachable rather than merely untaken.
#guard Fork.all.all (fun f => f.rules?.isSome)
#guard Fork.all.all (fun f => (f.rules?.map ForkRules.fork) = some f)
#guard Fork.prague.rules = .ok pragueRules
#guard Fork.osaka.rules = .ok osakaRules
#guard Fork.bpo1.rules = .ok bpo1Rules
#guard Fork.bpo2.rules = .ok bpo2Rules

-- A usable schedule is non-empty and moves strictly forward in both time and
-- fork order. It need not start at genesis: a schedule may support only eras
-- from some later floor onward, and that is a usable schedule, not an invalid
-- one -- `ChainConfig.forkAt` is where a too-early timestamp is refused.
#guard (ChainConfig.pragueOnly 1).validate.toOption.isSome
#guard guardHasTag invalidChainConfigTag (ChainConfig.mk 1 []).validate
#guard (ChainConfig.mk 1 [⟨.prague, 1⟩]).validate.toOption.isSome
#guard guardHasTag invalidChainConfigTag
  (ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 0⟩]).validate
#guard guardHasTag invalidChainConfigTag
  (ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 100⟩, ⟨.bpo1, 100⟩]).validate
#guard guardHasTag invalidChainConfigTag
  (ChainConfig.mk 1 [⟨.osaka, 0⟩, ⟨.prague, 100⟩]).validate
#guard guardHasTag invalidChainConfigTag
  (ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 100⟩, ⟨.osaka, 200⟩]).validate
#guard (ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 100⟩, ⟨.bpo1, 200⟩,
  ⟨.bpo2, 300⟩]).validate.toOption.isSome

-- Selection is by the last activation at or before the block timestamp, so the
-- activation block itself already runs the new rules.
private def guardSchedule : ChainConfig :=
  ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 100⟩, ⟨.bpo1, 200⟩, ⟨.bpo2, 300⟩]

#guard guardSchedule.forkAt 0 = .ok .prague
#guard guardSchedule.forkAt 99 = .ok .prague
#guard guardSchedule.forkAt 100 = .ok .osaka
#guard guardSchedule.forkAt 101 = .ok .osaka
#guard guardSchedule.forkAt 199 = .ok .osaka
#guard guardSchedule.forkAt 200 = .ok .bpo1
#guard guardSchedule.forkAt 299 = .ok .bpo1
#guard guardSchedule.forkAt 300 = .ok .bpo2
#guard guardSchedule.forkAt 1000000 = .ok .bpo2

-- A schedule whose first activation is not at genesis is usable, and a
-- timestamp before its floor is `SupportError.unsupportedEra`, not
-- `InvalidChainConfigError` -- the exact P0.5 boundary, independent of
-- mainnet's own timestamps below. One before the floor fails; the floor
-- itself, and everything after, selects normally.
private def guardFloorSchedule : ChainConfig :=
  ChainConfig.mk 1 [⟨.prague, 1000⟩, ⟨.osaka, 2000⟩]

#guard guardFloorSchedule.validate.toOption.isSome
#guard guardHasTag unsupportedEraTag (guardFloorSchedule.forkAt 999)
#guard guardFloorSchedule.forkAt 999
  = .error (SupportError.render (.unsupportedEra 999 1000))
#guard guardFloorSchedule.forkAt 1000 = .ok .prague
#guard guardFloorSchedule.forkAt 1999 = .ok .prague
#guard guardFloorSchedule.forkAt 2000 = .ok .osaka
#guard ¬ guardHasTag invalidChainConfigTag (guardFloorSchedule.forkAt 999)

-- The whole supported chain is now executable, so every point of the schedule
-- resolves to rules, and each segment resolves to its own.
#guard guardSchedule.rulesAt 0 = .ok pragueRules
#guard guardSchedule.rulesAt 99 = .ok pragueRules
#guard guardSchedule.rulesAt 100 = .ok osakaRules
#guard guardSchedule.rulesAt 199 = .ok osakaRules
#guard guardSchedule.rulesAt 200 = .ok bpo1Rules
#guard guardSchedule.rulesAt 299 = .ok bpo1Rules
#guard guardSchedule.rulesAt 300 = .ok bpo2Rules
#guard (ChainConfig.pragueOnly 1).rulesAt 0 = .ok pragueRules
#guard (ChainConfig.pragueOnly 1).rulesAt 999999 = .ok pragueRules

-- The blob schedule a block runs under is decided by its timestamp alone, and
-- the three BPO-visible numbers change at exactly the two BPO boundaries.
#guard (guardSchedule.rulesAt 199).map (ForkRules.blob) = .ok osakaBlobSchedule
#guard (guardSchedule.rulesAt 200).map (ForkRules.blob) = .ok bpo1BlobSchedule
#guard (guardSchedule.rulesAt 299).map (ForkRules.blob) = .ok bpo1BlobSchedule
#guard (guardSchedule.rulesAt 300).map (ForkRules.blob) = .ok bpo2BlobSchedule

-- An invalid schedule fails before any fork is selected, rather than silently
-- resolving to whichever activation happens to sort first.
#guard guardHasTag invalidChainConfigTag ((ChainConfig.mk 1 []).forkAt 0)
#guard guardHasTag invalidChainConfigTag ((ChainConfig.mk 1 []).rulesAt 0)

-- Mainnet's schedule is usable, and each of its recorded activation timestamps
-- is a boundary: the second before it still runs the old rules. Genesis, and
-- everything up to one second before the real Prague activation, is outside
-- this build's declared domain -- the exact P0.5 fix, since Jaune implements
-- no pre-Prague era and must not silently answer those blocks as Prague.
#guard mainnetChainConfig.validate.toOption.isSome
#guard mainnetChainConfig.chainId = 1
#guard guardHasTag unsupportedEraTag (mainnetChainConfig.forkAt 0)
#guard guardHasTag unsupportedEraTag
  (mainnetChainConfig.forkAt (mainnetPragueTimestamp - 1))
#guard mainnetChainConfig.forkAt (mainnetPragueTimestamp - 1)
  = .error (SupportError.render (.unsupportedEra (mainnetPragueTimestamp - 1)
      mainnetPragueTimestamp))
#guard mainnetChainConfig.forkAt mainnetPragueTimestamp = .ok .prague
#guard mainnetChainConfig.forkAt (mainnetOsakaTimestamp - 1) = .ok .prague
#guard mainnetChainConfig.forkAt mainnetOsakaTimestamp = .ok .osaka
#guard mainnetChainConfig.forkAt (mainnetBpo1Timestamp - 1) = .ok .osaka
#guard mainnetChainConfig.forkAt mainnetBpo1Timestamp = .ok .bpo1
#guard mainnetChainConfig.forkAt (mainnetBpo2Timestamp - 1) = .ok .bpo1
#guard mainnetChainConfig.forkAt mainnetBpo2Timestamp = .ok .bpo2
#guard mainnetChainConfig.rulesAt mainnetBpo2Timestamp = .ok bpo2Rules
#guard mainnetChainConfig.activations.map ForkActivation.fork = Fork.all

-- The mainnet activations are strictly ordered in the same direction as the
-- fork chain, which is the fact `validate` enforces and the reason the four
-- timestamps may not be reordered by a later edit.
#guard mainnetPragueTimestamp < mainnetOsakaTimestamp
#guard mainnetOsakaTimestamp < mainnetBpo1Timestamp
#guard mainnetBpo1Timestamp < mainnetBpo2Timestamp

-- Transition labels parse into schedules. Both endpoints must be forks this
-- build knows: a historical transition names one it does not.
#guard ForkTransition.ofString? "PragueToOsakaAtTime15k"
  = some ⟨.prague, .osaka, 15000⟩
#guard ForkTransition.ofString? "OsakaToBPO1AtTime15k"
  = some ⟨.osaka, .bpo1, 15000⟩
#guard ForkTransition.ofString? "BPO1ToBPO2AtTime15k"
  = some ⟨.bpo1, .bpo2, 15000⟩
#guard ForkTransition.ofString? "PragueToOsakaAtTime15000"
  = some ⟨.prague, .osaka, 15000⟩
#guard (ForkTransition.ofString? "CancunToPragueAtTime15k").isNone
#guard (ForkTransition.ofString? "BPO2ToBPO3AtTime15k").isNone
#guard (ForkTransition.ofString? "ShanghaiToCancunAtTime15k").isNone
#guard (ForkTransition.ofString? "Prague").isNone
#guard (ForkTransition.ofString? "PragueToOsaka").isNone
#guard (ForkTransition.ofString? "PragueToOsakaAtTime").isNone
#guard (ForkTransition.ofString? "PragueToOsakaAtTimek").isNone
#guard (ForkTransition.ofString? "PragueToOsakaAtTime15kk").isNone
#guard (ForkTransition.ofString? "PragueToOsakaAtTime15k ").isNone
#guard (ForkTransition.ofString? "PragueToOsakaToBPO1AtTime15k").isNone
#guard (ForkTransition.ofString? "PragueToOsakaAtTime15kAtTime20k").isNone

-- Labels round-trip through the canonical printer, which is what lets fixture
-- case selection stay an exact string comparison.
private def guardTransitions : List ForkTransition := [
  ⟨.prague, .osaka, 15000⟩, ⟨.osaka, .bpo1, 15000⟩, ⟨.bpo1, .bpo2, 15000⟩,
  ⟨.prague, .bpo2, 1⟩, ⟨.osaka, .bpo2, 1234567⟩
]

#guard guardTransitions.all
  (fun t => ForkTransition.ofString? t.toString = some t)
#guard (⟨.prague, .osaka, 15000⟩ : ForkTransition).toString
  = "PragueToOsakaAtTime15k"
#guard (⟨.osaka, .bpo1, 1234567⟩ : ForkTransition).toString
  = "OsakaToBPO1AtTime1234567"

-- A transition is a schedule: the `before` fork runs from genesis and the
-- `after` fork from the named timestamp, with no third possibility.
private def guardOsakaToBpo1 : ForkTransition := ⟨.osaka, .bpo1, 15000⟩

#guard (guardOsakaToBpo1.chainConfig 1).validate.toOption.isSome
#guard (guardOsakaToBpo1.chainConfig 1).rulesAt 0 = .ok osakaRules
#guard (guardOsakaToBpo1.chainConfig 1).rulesAt 14999 = .ok osakaRules
#guard (guardOsakaToBpo1.chainConfig 1).rulesAt 15000 = .ok bpo1Rules
#guard (guardOsakaToBpo1.chainConfig 1).rulesAt 15001 = .ok bpo1Rules
#guard (guardOsakaToBpo1.chainConfig 7).chainId = 7

-- A parseable label may still name an unusable schedule; it is refused where
-- every other unusable schedule is, rather than at the parser.
#guard ForkTransition.ofString? "OsakaToPragueAtTime15k"
  = some ⟨.osaka, .prague, 15000⟩
#guard guardHasTag invalidChainConfigTag
  (((⟨.osaka, .prague, 15000⟩ : ForkTransition).chainConfig 1).rulesAt 0)
#guard guardHasTag invalidChainConfigTag
  (((⟨.prague, .osaka, 0⟩ : ForkTransition).chainConfig 1).rulesAt 0)

-- A `network` label is either a static fork or a transition, and the two
-- parsers do not overlap.
#guard NetworkSpec.ofString? "Prague" = some (.static .prague)
#guard NetworkSpec.ofString? "BPO2" = some (.static .bpo2)
#guard NetworkSpec.ofString? "OsakaToBPO1AtTime15k"
  = some (.transition ⟨.osaka, .bpo1, 15000⟩)
#guard (NetworkSpec.ofString? "Cancun").isNone
#guard (NetworkSpec.ofString? "CancunToPragueAtTime15k").isNone
#guard (NetworkSpec.ofString? "").isNone
#guard Fork.all.all
  (fun f => NetworkSpec.ofString? f.toString = some (.static f))
#guard guardTransitions.all
  (fun t => NetworkSpec.ofString? (NetworkSpec.transition t).toString
    = some (.transition t))
#guard (NetworkSpec.static .osaka).forks = [.osaka]
#guard (NetworkSpec.transition guardOsakaToBpo1).forks = [.osaka, .bpo1]

-- The three renderer arms that already have a live producer agree with it
-- byte for byte. This is the property Steps 9 and 10 must preserve when the
-- producers themselves start returning typed reasons, and it is checked here
-- against the real function rather than against a transcription of it.
#guard (match (ChainConfig.mk 1 []).validate with
  | .error e => e == ChainContextError.render .emptySchedule
  | .ok _ => false)
#guard (match (ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 0⟩]).validate with
  | .error e =>
    e == ChainContextError.render (.nonIncreasingActivations ⟨.prague, 0⟩ ⟨.osaka, 0⟩)
  | .ok _ => false)
#guard (match (ChainConfig.mk 1 [⟨.osaka, 0⟩, ⟨.prague, 9⟩]).validate with
  | .error e =>
    e == ChainContextError.render (.nonForwardActivations ⟨.osaka, 0⟩ ⟨.prague, 9⟩)
  | .ok _ => false)

-- `forkAt`'s new unsupported-era arm agrees with `SupportError.render` too,
-- against the real function rather than a transcription of it.
#guard (match guardFloorSchedule.forkAt 999 with
  | .error e => e == SupportError.render (.unsupportedEra 999 1000)
  | .ok _ => false)
#guard (match mainnetChainConfig.forkAt 0 with
  | .error e => e == SupportError.render (.unsupportedEra 0 mainnetPragueTimestamp)
  | .ok _ => false)

end Jaune
