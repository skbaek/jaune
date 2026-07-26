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

import Elevm.Types

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
deriving DecidableEq, Repr

/-- Deployed-code and initcode size limits (EIP-170 and EIP-3860). -/
structure CodeLimits : Type where
  /-- `MAX_CODE_SIZE`: the largest code a contract creation may deposit. -/
  maxCodeSize : Nat
  /-- `MAX_INITCODE_SIZE`: the largest initcode a creation may run. -/
  maxInitCodeSize : Nat
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
}

/-- Prague's code size limits. -/
def pragueCodeLimits : CodeLimits := {
  maxCodeSize := 24576 -- 0x6000
  maxInitCodeSize := 49152 -- 2 * 0x6000
}

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
}

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

/-- The Osaka rule set.

Only the fields Osaka actually moves differ from Prague; the shared ones are
named through Prague's definitions so that a later Prague correction cannot
silently desynchronise the two. -/
def osakaRules : ForkRules := {
  fork := .osaka
  blob := osakaBlobSchedule
  code := pragueCodeLimits
  modexp := osakaModexpRules
  op := osakaOpcodeRules
  precompiles := praguePrecompiles
}

/-- Error tag for a fork whose identity is known but whose rules this build
does not implement. -/
def unsupportedForkTag : String := "UnsupportedForkError"

/-- The single place where a fork identity becomes rule data.

`none` means the fork is declared but not yet executable. It must never be
answered with another fork's rules: running Osaka blocks under Prague semantics
because Osaka is unfinished would turn a missing implementation into a silent
consensus fault. -/
def Fork.rules? : Fork → Option ForkRules
  | .prague => some pragueRules
  | .osaka => some osakaRules
  | .bpo1 => none
  | .bpo2 => none

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
  chainId : B64
  activations : List ForkActivation
deriving DecidableEq, Repr

/-- Error tag for a schedule that does not determine an unambiguous fork. -/
def invalidChainConfigTag : String := "InvalidChainConfigError"

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
least one fork, that first fork is active from the genesis timestamp, and every
later activation moves strictly forward. -/
def validate (cfg : ChainConfig) : Except String Unit := do
  match cfg.activations with
  | [] =>
    .error s!"{invalidChainConfigTag} : the activation schedule is empty"
  | first :: _ =>
    if first.timestamp ≠ 0 then
      .error
        s!"{invalidChainConfigTag} : the first activation ({first.fork}) must \
           be active from timestamp 0, but starts at {first.timestamp}"
    validateSteps cfg.activations

/-- The last activation at or before `timestamp`, without validating the
schedule. Callers should prefer `forkAt`. -/
def forkAt? (cfg : ChainConfig) (timestamp : Nat) : Option Fork :=
  (cfg.activations.filter (·.timestamp ≤ timestamp)).getLast?.map
    ForkActivation.fork

/-- The fork active at `timestamp`, rejecting schedules that do not determine
one. -/
def forkAt (cfg : ChainConfig) (timestamp : Nat) : Except String Fork := do
  cfg.validate
  match cfg.forkAt? timestamp with
  | some f => .ok f
  | none =>
    .error
      s!"{invalidChainConfigTag} : no fork is active at timestamp {timestamp}"

/-- The rules active at `timestamp`. Fails if the schedule is unusable or if
the selected fork's rules are not implemented. -/
def rulesAt (cfg : ChainConfig) (timestamp : Nat) : Except String ForkRules := do
  (← cfg.forkAt timestamp).rules

/-- The configuration of a chain that is at Prague from genesis and never
transitions. -/
def pragueOnly (chainId : B64) : ChainConfig :=
  { chainId := chainId, activations := [⟨.prague, 0⟩] }

end ChainConfig

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
#guard pragueRules.code.maxCodeSize = 24576
#guard pragueRules.code.maxInitCodeSize = 2 * pragueRules.code.maxCodeSize
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

-- Osaka shares every rule value with Prague except the ones EIP-7607's
-- execution-layer delta actually moves. The shared blob schedule is stated as
-- the EIP-7892 blob-count product rather than assumed.
#guard osakaRules.fork = .osaka
#guard osakaRules.blob = pragueRules.blob
#guard osakaRules.code = pragueRules.code
#guard osakaBlobSchedule.target = 786432
#guard osakaBlobSchedule.max = 1179648
#guard osakaRules.modexp.maxLength = some 1024
#guard osakaRules.modexp.flatComplexity = some 16
#guard osakaRules.modexp.complexityCoeff = 2
#guard osakaRules.modexp.iterationCoeff = 2 * pragueRules.modexp.iterationCoeff
#guard osakaRules.modexp.gasDivisor = 1
#guard osakaRules.modexp.minGas = 500
#guard osakaRules.op.clz = true

-- Prague and Osaka are executable in this build; the BPO forks are identities
-- without rules, and asking for them fails rather than falling back.
#guard Fork.prague.rules?.isSome
#guard Fork.osaka.rules?.isSome
#guard Fork.bpo1.rules?.isNone
#guard Fork.bpo2.rules?.isNone
#guard Fork.prague.rules = .ok pragueRules
#guard Fork.osaka.rules = .ok osakaRules
#guard guardHasTag unsupportedForkTag Fork.bpo1.rules
#guard guardHasTag unsupportedForkTag Fork.bpo2.rules

-- A usable schedule is non-empty, starts at genesis, and moves strictly
-- forward in both time and fork order.
#guard (ChainConfig.pragueOnly 1).validate.toOption.isSome
#guard guardHasTag invalidChainConfigTag (ChainConfig.mk 1 []).validate
#guard guardHasTag invalidChainConfigTag (ChainConfig.mk 1 [⟨.prague, 1⟩]).validate
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

-- A configured chain reports the same unsupported-fork error as an explicit
-- one; a schedule may name a fork this build cannot yet run.
#guard guardSchedule.rulesAt 0 = .ok pragueRules
#guard guardSchedule.rulesAt 99 = .ok pragueRules
#guard guardSchedule.rulesAt 100 = .ok osakaRules
#guard guardHasTag unsupportedForkTag (guardSchedule.rulesAt 200)
#guard guardHasTag unsupportedForkTag (guardSchedule.rulesAt 300)
#guard (ChainConfig.pragueOnly 1).rulesAt 0 = .ok pragueRules
#guard (ChainConfig.pragueOnly 1).rulesAt 999999 = .ok pragueRules

-- An invalid schedule fails before any fork is selected, rather than silently
-- resolving to whichever activation happens to sort first.
#guard guardHasTag invalidChainConfigTag ((ChainConfig.mk 1 []).forkAt 0)
#guard guardHasTag invalidChainConfigTag ((ChainConfig.mk 1 []).rulesAt 0)
