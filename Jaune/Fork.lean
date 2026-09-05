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
  | amsterdam
deriving DecidableEq, Repr, Inhabited

namespace Fork

/-- The canonical label. These are the strings that fixture `network` fields
and the `--network` command-line option use. -/
def toString : Fork → String
  | .prague => "Prague"
  | .osaka => "Osaka"
  | .bpo1 => "BPO1"
  | .bpo2 => "BPO2"
  | .amsterdam => "Amsterdam"

instance : ToString Fork := ⟨Fork.toString⟩

/-- Strict label parsing. There is no fallback and no case folding: an
unrecognised label is an error at every caller, never Prague. -/
def ofString? : String → Option Fork
  | "Prague" => some .prague
  | "Osaka" => some .osaka
  | "BPO1" => some .bpo1
  | "BPO2" => some .bpo2
  | "Amsterdam" => some .amsterdam
  | _ => none

/-- Every *declared* fork, in activation order.

Declared is not implemented: `Fork.amsterdam` is here because its label,
its position in the chain, and the transitions naming it are facts this build
knows, while `Fork.rules?` answers `none` for it. The list of forks whose rules
this build can actually run is `Fork.supported` below, and the two must not be
confused at a user-facing message: a label this build parses and refuses is a
different answer from one it does not recognise at all. -/
def all : List Fork := [.prague, .osaka, .bpo1, .bpo2, .amsterdam]

/-- Position in the supported transition chain.

This is the *only* ordering notion on forks, and it exists so that a
`ChainConfig` schedule can be checked for monotonicity. It is not a licence to
compare forks inside execution. -/
def index : Fork → Nat
  | .prague => 0
  | .osaka => 1
  | .bpo1 => 2
  | .bpo2 => 3
  | .amsterdam => 4

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

/-- The gas numbers a supported fork moves inside a formula both forks share.

This is exactly the scope decision D2 of the Amsterdam programme fixes, and it
is deliberately narrow. A number belongs here when Amsterdam reprices it *and*
Prague and Amsterdam compute with it in the same formula, so that one record
field can serve both without a branch. Numbers Amsterdam leaves alone stay
global; numbers only one fork's formula mentions -- `gasStorageSet`,
`gasStorageUpdate`, `gNewAccount`, `gasCodeDeposit`, the 12,500 authorisation
refund -- stay global too, because moving them here would state a fork
difference that does not exist.

Every field's Prague value is `rfl`-equal to the global constant that has
always held it (`pragueRules_gas_*` below), so no Prague-stated proof and no
Prague fixture can observe that the number now arrives through a record. The
Amsterdam values in the comments are the pinned upstream commit's and are
checked mechanically by `scripts/check-fork-constants.sh`; they are recorded
here as documentation, not as a rule this build implements. -/
structure GasSchedule : Type where
  /-- EIP-2929's cold account access. Prague 2600; Amsterdam 3000. -/
  coldAccountAccess : Nat
  /-- The surcharge a value-bearing call pays. Prague 9000; Amsterdam 11300. -/
  callValue : Nat
  /-- The `CREATE`/`CREATE2` base cost, which is also the creation
  transaction's recipient cost. Prague 32000; Amsterdam 12000, where
  EIP-8037 moves most of the creation cost into state gas. -/
  createAccess : Nat
  /-- The refund for clearing a storage slot. Prague 4800; Amsterdam 11616. -/
  storageClearRefund : Nat
  /-- The intrinsic cost every transaction pays. Prague 21000; Amsterdam
  12000, with EIP-2780 charging the difference per resource instead. -/
  txBase : Nat
  /-- Per access-list address. Prague 2400; Amsterdam 2900. -/
  txAccessListAddress : Nat
  /-- Per access-list storage key. Prague 1900; Amsterdam 2000. -/
  txAccessListStorageKey : Nat
  /-- The per-token calldata floor (EIP-7623). Prague 10; Amsterdam 16. -/
  floorTokenCost : Nat
  /-- The intrinsic cost of one EIP-7702 authorisation tuple. Prague 25000;
  Amsterdam 7816. -/
  perAuthIntrinsic : Nat
  /-- EIP-8038's additive code-reading surcharge at `EXTCODESIZE` and
  `EXTCODECOPY`. Prague 0; Amsterdam 100.

  Stated as an additive term whose identity is 0 rather than as an optional
  cost, because that is what makes the Prague formula literally unchanged: the
  surcharge is added at both forks and contributes nothing at Prague. Upstream
  gives this number no name of its own -- it is `WARM_ACCESS` added inline at
  the two opcodes -- so the constants gate reads it as a source-presence fact
  and records the derivation. -/
  codeReadSurcharge : Nat
deriving DecidableEq, Repr

/-- EIP-8037's state-gas dimension, and the numbers only the Amsterdam metering
shape reads.

`ForkRules.stateGas` carries this record under an `Option`, and that `Option` is
the whole metering switch: `none` selects today's single-dimension formulas
unchanged, `some r` selects the Amsterdam shape. EIP-2780, 7778, 8037 and 8038
are co-designed and not separately deployable -- 2780's decomposition assumes
8037's state gas for creation, and 8038's `STORAGE_WRITE` assumes `STORAGE_SET`
moved to state gas -- so one switch is the honest shape for all four.

The division of labour against `GasSchedule` is exact: a number Amsterdam moves
inside a formula *both* forks compute lives there, because one field can serve
both without a branch. A number that exists only under the Amsterdam shape
lives here, because Prague has nowhere to put it. Nothing Amsterdam-only
becomes a global.

The three derived state costs are definitions over these fields rather than
second literals, so `NEW_ACCOUNT`, `STORAGE_SET` and `AUTH_BASE` cannot drift
from the byte counts they are products of. The Amsterdam values in the comments
are the pinned upstream commit's and are checked mechanically by
`scripts/check-fork-constants.sh`. -/
structure StateGasRules : Type where
  /-- `COST_PER_STATE_BYTE`: gas per byte of new state. Amsterdam 1530. -/
  costPerStateByte : Nat
  /-- `STATE_BYTES_PER_NEW_ACCOUNT`. Amsterdam 120, so `NEW_ACCOUNT` is
  183,600. -/
  stateBytesPerNewAccount : Nat
  /-- `STATE_BYTES_PER_STORAGE_SET`. Amsterdam 64, so `STORAGE_SET` is
  97,920. -/
  stateBytesPerStorageSet : Nat
  /-- `STATE_BYTES_PER_AUTH_BASE`. Amsterdam 23, so `AUTH_BASE` is 35,190. -/
  stateBytesPerAuthBase : Nat
  /-- `STORAGE_WRITE` (EIP-8038), the execution-gas charge a slot's first
  change pays. Amsterdam 10000. -/
  storageWrite : Nat
  /-- `ACCOUNT_WRITE` (EIP-8038). Amsterdam 9000. -/
  accountWrite : Nat
  /-- `TX_VALUE_COST` (EIP-2780), the intrinsic charge a value-bearing
  non-self-transfer pays. Amsterdam 6000. -/
  txValueCost : Nat
  /-- `ACCESS_LIST_ADDRESS_FLOOR_TOKENS` (EIP-7981). Amsterdam 80. -/
  accessListAddressFloorTokens : Nat
  /-- `ACCESS_LIST_STORAGE_KEY_FLOOR_TOKENS` (EIP-7981). Amsterdam 128. -/
  accessListStorageKeyFloorTokens : Nat
  /-- `SYSTEM_MAX_SSTORES_PER_CALL`, the reservoir a system transaction is
  granted, in `STORAGE_SET` units. Amsterdam 16. -/
  systemMaxSstoresPerCall : Nat
deriving DecidableEq, Repr

/-- `STORAGE_SET`: the state gas a first-time set of a zero slot pays. -/
def StateGasRules.storageSet (r : StateGasRules) : Nat :=
  r.stateBytesPerStorageSet * r.costPerStateByte

/-- `NEW_ACCOUNT`: the state gas creating an account pays. -/
def StateGasRules.newAccount (r : StateGasRules) : Nat :=
  r.stateBytesPerNewAccount * r.costPerStateByte

/-- `AUTH_BASE`: the state gas one net-new EIP-7702 delegation pays. -/
def StateGasRules.authBase (r : StateGasRules) : Nat :=
  r.stateBytesPerAuthBase * r.costPerStateByte

/-- The state gas a system transaction's reservoir is granted. -/
def StateGasRules.systemReservoir (r : StateGasRules) : Nat :=
  r.systemMaxSstoresPerCall * r.storageSet

/-- Which fork-dependent header fields a block must carry.

Two booleans rather than one, because the two EIPs are separate: EIP-7928
introduces `blockAccessListHash` and EIP-7843 `slotNumber`, and nothing in the
protocol makes them arrive together. Presence is required exactly when the
flag is set, in both directions -- a header carrying a field the rules do not
name is as invalid as one missing a field they do. -/
structure HeaderRules : Type where
  /-- EIP-7928: the header commits to the block-level access list. -/
  blockAccessListHash : Bool
  /-- EIP-7843: the header carries the consensus slot number. -/
  slotNumber : Bool
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
  /-- The gas numbers a supported fork moves inside a shared formula. -/
  gas : GasSchedule
  /-- EIP-8037's state-gas dimension, or `none` for a fork that meters in one
  dimension.

  This `Option` is the metering switch. Under `none` the interpreter runs the
  formulas it has always run, textually; under `some r` it runs Amsterdam's
  two-reservoir shape with `r`'s numbers. Prague, Osaka, BPO1 and BPO2 all
  carry `none`, so nothing the supported chain does can observe that the field
  exists. -/
  stateGas : Option StateGasRules
  /-- Which fork-dependent header fields a block must carry. -/
  header : HeaderRules
  /-- The request-producing system contracts, as `(type byte, address)` pairs,
  in the order `processGeneralPurposeRequests` must call them.

  The order is the rule, not an implementation detail: the request bytes are
  concatenated in call order and hashed into `requestsHash`, so a reordering
  would be a consensus change. The receipt-derived deposit request (type 0) is
  deliberately absent -- it is parsed out of the block's logs rather than
  produced by a system call, so it is not one of these. -/
  requests : List (UInt8 × Adr)
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

--------------- STRUCTURALLY USABLE RULE PARAMETERS ---------------

-- `ForkRules` is a plain record, so nothing in its *type* stops a caller from
-- handing execution a zero divisor. The predicates below name exactly the
-- structural facts the semantics divides or subtracts by. They are not
-- consensus validity: a rule set can satisfy every one of them and still
-- describe no real fork. They are the facts a total function needs.

/-- The blob schedule's parameters are usable by the blob-fee arithmetic.

Three conditions, one per place the schedule reaches division or `Nat`
subtraction:
- `baseFeeUpdateFraction` is `fakeExp`'s denominator, in both `(numAcc * num) /
  (den * i)` and the final `out / den`;
- `max` is the divisor on EIP-7918's reserve-price branch of
  `calculateExcessBlobGas`; and
- `target ≤ max` keeps `max - target` on that same branch a real difference
  rather than a truncated `Nat` subtraction, which an inverted schedule would
  silently answer with `0`. -/
def BlobSchedule.Valid (b : BlobSchedule) : Prop :=
  0 < b.baseFeeUpdateFraction ∧ 0 < b.max ∧ b.target ≤ b.max

instance {b : BlobSchedule} : Decidable b.Valid := by
  unfold BlobSchedule.Valid; infer_instance

/-- The gas schedule's numbers are large enough for the interpreter's
termination argument to go through.

Not consensus validity, and not "these are the right prices": these are the
three facts the *totality* proof consumes, and they were discovered rather than
guessed -- the `Jaune.Sufficiency` family was instantiated at a zero-valued
schedule and these are the obligations that failed.

- `100 ≤ coldAccountAccess` is what makes an account access cost at least the
  warm access, which every `gasLt` obligation at a cold `EXTCODESIZE`,
  `BALANCE`, `EXTCODEHASH` or `CALL` needs in order to charge *something*
  strictly positive. The literal is `gasWarmAccess`, spelled out because this
  module is upstream of the globals; `pragueRules_gas_warmAccess_le` in
  `Jaune/Machine.lean` is the `rfl` bridge.
- `0 < createAccess` is the same fact for an empty-initcode `CREATE`, whose
  only other charge can be zero.
- `2300 ≤ callValue` is what makes a value-bearing `CALL` charge at least the
  stipend it hands the child, so that the parent's measure still falls across
  the spawn. The literal is `gCallStipend`.

Prague's schedule satisfies all three at 2,600 / 32,000 / 9,000, and
Amsterdam's at 3,000 / 12,000 / 11,300; the numbers move, the inequalities do
not. -/
def GasSchedule.Valid (g : GasSchedule) : Prop :=
  100 ≤ g.coldAccountAccess ∧ 0 < g.createAccess ∧ 2300 ≤ g.callValue

instance {g : GasSchedule} : Decidable g.Valid := by
  unfold GasSchedule.Valid; infer_instance

/-- The rule set's parameters are usable by the semantics that reads them.

Three groups, one per thing the semantics needs of a number it did not choose:
the blob schedule's divisors and its target/ceiling ordering, `MODEXP`'s
`GQUADDIVISOR`, and -- since Amsterdam reprices the numbers the interpreter's
own termination argument leans on -- the gas schedule's three inequalities.
Every other divisor in the interpreter -- `elasticityMultiplier`,
`gasLimitAdjustmentFactor`, `baseFeeMaxChangeDenominator` -- is a global
constant rather than rule data, so its positivity is a closed fact proved next
to it in `Jaune/Machine.lean` and not a hypothesis anything must carry. -/
def ForkRules.Valid (r : ForkRules) : Prop :=
  r.blob.Valid ∧ 0 < r.modexp.gasDivisor ∧ r.gas.Valid

instance {r : ForkRules} : Decidable r.Valid := by
  unfold ForkRules.Valid; infer_instance

/-- The three projections, named so that a Sufficiency obligation can say which
part of validity it consumes rather than indexing into a conjunction. -/
theorem ForkRules.Valid.blob {r : ForkRules} (h : r.Valid) : r.blob.Valid := h.1

theorem ForkRules.Valid.modexpGasDivisor_pos {r : ForkRules} (h : r.Valid) :
    0 < r.modexp.gasDivisor := h.2.1

theorem ForkRules.Valid.gas {r : ForkRules} (h : r.Valid) : r.gas.Valid := h.2.2

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

/-- Prague's shared-formula gas numbers.

Each value is the global constant that has always held it, and
`Jaune/Machine.lean` states that equality as an `rfl` lemma next to those
globals -- it cannot be stated here, because this module is upstream of them.
The literals are written out rather than imported for exactly that reason, and
the lemmas are what stop the two copies from drifting. -/
def pragueGasSchedule : GasSchedule := {
  coldAccountAccess := 2600
  callValue := 9000
  createAccess := 32000
  storageClearRefund := 4800
  txBase := 21000
  txAccessListAddress := 2400
  txAccessListStorageKey := 1900
  floorTokenCost := 10
  perAuthIntrinsic := 25000
  -- Additive with identity 0: EIP-8038 is not active, so the code-reading
  -- surcharge contributes nothing and the Prague formula is unchanged.
  codeReadSurcharge := 0
}

/-- Prague's header carries neither Amsterdam field. -/
def pragueHeaderRules : HeaderRules :=
  { blockAccessListHash := false, slotNumber := false }

/-- Prague's request-producing system contracts, in call order: the EIP-7002
withdrawal contract, then the EIP-7251 consolidation contract.

`Jaune/Machine.lean` states that these are the same two addresses, in the same
order, that its `processGeneralPurposeRequests` fold has always called. -/
def pragueRequests : List (UInt8 × Adr) := [
  (1, 0x00000961Ef480Eb55e80D19ad83579A64c007002), -- EIP-7002 withdrawals
  (2, 0x0000BBdDc7CE488642fb579F8B00f3a590007251)  -- EIP-7251 consolidations
]

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
  gas := pragueGasSchedule
  -- Prague meters in one dimension, so there is no state-gas record to carry.
  stateGas := none
  header := pragueHeaderRules
  requests := pragueRequests
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
  -- Osaka moves none of the three new categories: EIP-7939 is an opcode, and
  -- the repricings, the header fields, and the two extra request contracts are
  -- all Amsterdam's. Naming Prague's records rather than repeating them is
  -- what makes that a fact of the source instead of a claim about it.
  gas := pragueGasSchedule
  stateGas := none
  header := pragueHeaderRules
  requests := pragueRequests
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

/-- Amsterdam's shared-formula gas numbers (EIP-8038, 2780, 7976, 7981).

Every value is the pinned `execution-specs` revision's, and
`scripts/check-fork-constants.sh` is what says so: it compares this record's
fields against the extraction the generator takes from that revision. The
derivations upstream states, recorded here so a future repricing is checked
against the same identity rather than a copied number:

* `callValue` = `ACCOUNT_WRITE` + `CALL_STIPEND` = 9000 + 2300;
* `createAccess` = `ACCOUNT_WRITE` + `COLD_ACCOUNT_ACCESS` = 9000 + 3000;
* `storageClearRefund` = (`STORAGE_WRITE` + `COLD_STORAGE_ACCESS`) * 4800 / 5000
  = (10000 + 2100) * 4800 / 5000;
* `txAccessListAddress` = `COLD_ACCOUNT_ACCESS` - `WARM_ACCESS` = 3000 - 100;
* `txAccessListStorageKey` = `COLD_STORAGE_ACCESS` - `WARM_ACCESS` = 2100 - 100;
* `perAuthIntrinsic` = 101 * 16 + 3000 + 3000 + 2 * 100.

`codeReadSurcharge` has no name of its own upstream: EIP-8038 adds `WARM_ACCESS`
inline at `EXTCODESIZE` and `EXTCODECOPY`, so the extraction reads it as a
source-presence fact and records that derivation. -/
def amsterdamGasSchedule : GasSchedule := {
  coldAccountAccess := 3000
  callValue := 11300
  createAccess := 12000
  storageClearRefund := 11616
  txBase := 12000
  txAccessListAddress := 2900
  txAccessListStorageKey := 2000
  floorTokenCost := 16
  perAuthIntrinsic := 7816
  codeReadSurcharge := 100
}

/-- Amsterdam's state-gas dimension (EIP-8037), and the four numbers only its
metering shape reads (EIP-2780's transaction value cost, EIP-7981's two floor
token counts, and the system-transaction reservoir).

`STORAGE_SET`, `NEW_ACCOUNT` and `AUTH_BASE` are not fields: they are the
`StateGasRules` products 64 * 1530 = 97,920, 120 * 1530 = 183,600 and
23 * 1530 = 35,190, guarded as such below. -/
def amsterdamStateGasRules : StateGasRules := {
  costPerStateByte := 1530
  stateBytesPerNewAccount := 120
  stateBytesPerStorageSet := 64
  stateBytesPerAuthBase := 23
  storageWrite := 10000
  accountWrite := 9000
  txValueCost := 6000
  accessListAddressFloorTokens := 80
  accessListStorageKeyFloorTokens := 128
  systemMaxSstoresPerCall := 16
}

/-- The rules an Amsterdam *transaction* is metered by, without the block-level
rules a later goal adds.

This is a **vehicle**, not `Fork.amsterdam`'s rule set. `Fork.amsterdam.rules?`
is still `none` and `Fork.supported` is still four forks, because the
block-level rules EIP-7928, EIP-8282, EIP-7843, EIP-8024 and EIP-7954 carry
have no reader in this build yet: a record that resolved would promise a
semantics that does not exist. What does exist is the metering shape, and it
needs a `ForkRules` to be exercised against.

So the vehicle is BPO2's record with exactly the three fields this goal
implements moved -- the identity, the shared-formula numbers, and the state-gas
switch. Everything else is deliberately BPO2's: the header flags stay `false`,
the request list stays Prague's two contracts, and the code limits and opcode
set stay BPO2's, because each of those belongs to the block-level goal and
would be a false claim here.

It is reachable from exactly two places: the `#guard` tables below, which is
where the metering numbers are pinned, and `jaune t8n --state.fork Amsterdam`,
which resolves it through a table local to the transition-tool frontend rather
than through `Fork.rules?`. `t8n --forks` keeps printing `Fork.supported`.

The block-level goal composes a real `amsterdamRules` from
`amsterdamGasSchedule` and `amsterdamStateGasRules` and retires this. -/
def amsterdamMeteringRules : ForkRules :=
  { bpo2Rules with
    fork := .amsterdam
    gas := amsterdamGasSchedule
    stateGas := some amsterdamStateGasRules }

-- Every named rule set carries the structural witness, so no in-tree execution
-- path ever needs to check it. `decide` is the whole proof: the predicates are
-- decidable and the parameters are literals.

theorem pragueBlobSchedule_valid : pragueBlobSchedule.Valid := by decide
theorem osakaBlobSchedule_valid : osakaBlobSchedule.Valid := by decide
theorem bpo1BlobSchedule_valid : bpo1BlobSchedule.Valid := by decide
theorem bpo2BlobSchedule_valid : bpo2BlobSchedule.Valid := by decide

theorem pragueRules_valid : pragueRules.Valid := by decide
theorem osakaRules_valid : osakaRules.Valid := by decide
theorem bpo1Rules_valid : bpo1Rules.Valid := by decide
theorem bpo2Rules_valid : bpo2Rules.Valid := by decide

/-- The metering vehicle carries the witness too, which is what lets the
Sufficiency family be instantiated at Amsterdam's numbers rather than only at
Prague's. Amsterdam moves all three of `GasSchedule.Valid`'s numbers --
`createAccess` *downwards*, from 32,000 to 12,000 -- and the inequalities still
hold, which is the fact this `decide` records. -/
theorem amsterdamMeteringRules_valid : amsterdamMeteringRules.Valid := by decide

theorem amsterdamGasSchedule_valid : amsterdamGasSchedule.Valid := by decide
theorem pragueGasSchedule_valid : pragueGasSchedule.Valid := by decide

-- The three obligations, and what a schedule that failed one would be refused
-- for. Stated as guards so that the discovery recorded in `GasSchedule.Valid`'s
-- docstring is checked rather than remembered.
#guard ¬ ({ pragueGasSchedule with coldAccountAccess := 99 } : GasSchedule).Valid
#guard ¬ ({ pragueGasSchedule with createAccess := 0 } : GasSchedule).Valid
#guard ¬ ({ pragueGasSchedule with callValue := 2299 } : GasSchedule).Valid
#guard ({ pragueGasSchedule with callValue := 2300 } : GasSchedule).Valid

-- The three premises, spelled out once per named schedule, so a future
-- reparameterisation that zeroes a divisor or inverts the target/ceiling pair
-- fails here rather than inside `fakeExp`.
#guard 0 < pragueBlobSchedule.baseFeeUpdateFraction
#guard 0 < osakaBlobSchedule.baseFeeUpdateFraction
#guard 0 < bpo1BlobSchedule.baseFeeUpdateFraction
#guard 0 < bpo2BlobSchedule.baseFeeUpdateFraction
#guard pragueBlobSchedule.target ≤ pragueBlobSchedule.max
#guard osakaBlobSchedule.target ≤ osakaBlobSchedule.max
#guard bpo1BlobSchedule.target ≤ bpo1BlobSchedule.max
#guard bpo2BlobSchedule.target ≤ bpo2BlobSchedule.max
#guard 0 < pragueModexpRules.gasDivisor
#guard 0 < osakaModexpRules.gasDivisor
-- A zero divisor and an inverted schedule are both refused.
#guard ¬ ({ pragueBlobSchedule with baseFeeUpdateFraction := 0 } : BlobSchedule).Valid
#guard ¬ ({ pragueBlobSchedule with max := 0 } : BlobSchedule).Valid
#guard ¬ ({ pragueBlobSchedule with
              target := pragueBlobSchedule.max + 1 } : BlobSchedule).Valid
#guard ¬ ({ pragueRules with
              modexp := { pragueModexpRules with gasDivisor := 0 } }
            : ForkRules).Valid

/-- Error tag for a fork whose identity is known but whose rules this build
does not implement.

`Fork.amsterdam` is declared and unresolved, so this branch is reachable: it
is the answer every entry point gives for an Amsterdam input. Falling back to
another fork's rules would turn a missing implementation into a silent
consensus fault, so there is deliberately no fallback to fall back to. -/
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
  | .amsterdam => none

/-- The declared forks this build can actually run.

Derived from `Fork.rules?` rather than written out, so it cannot drift from
what resolves. This is the list a message means when it says "supported":
`Fork.all` is what this build *parses*, and these are the labels it will also
execute. -/
def Fork.supported : List Fork := Fork.all.filter (fun f => f.rules?.isSome)

/-- The declared forks whose rules this build does not implement.

The complement of `Fork.supported` within `Fork.all`, for the diagnostics that
have to name exactly which labels parse and are then refused. -/
def Fork.unimplemented : List Fork := Fork.all.filter (fun f => f.rules?.isNone)

/-- Every rule set a fork identity resolves to is structurally usable.

This is what makes `ForkRules.Valid` free at the fork-selected entry points:
`stateTransitionAt`, `addBlockToChainAt`, and everything reached through
`ChainConfig.rulesAt` obtain their rules from here, so they carry the witness
without checking for it. Only a caller supplying a rule record of its own has
anything to prove. -/
theorem Fork.rules?_valid {f : Fork} {r : ForkRules} (h : f.rules? = some r) :
    r.Valid := by
  cases f <;> rw [Fork.rules?] at h <;> cases h
  · exact pragueRules_valid
  · exact osakaRules_valid
  · exact bpo1Rules_valid
  · exact bpo2Rules_valid

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

/-- Error tag for an explicitly supplied rule record whose parameters the
semantics cannot use.

Separate from `invalidChainConfigTag`: the schedule is not at fault, and
separate from `unsupportedEraTag`: the era is implemented. Produced only by
`ValidRules.check`, the checked entry point for a caller-built `ForkRules`;
every fork-selected path obtains rules that already carry the witness.
Deliberately not routed to any fixture identity -- invalid rule parameters are
never evidence that a candidate block is invalid. -/
def invalidForkRulesTag : String := "InvalidForkRulesError"

/-- Which structural premise a supplied `ForkRules` fails.

Typed rather than a message: the reason is a fact about the record, and only
`ChainContextError.render` may turn it into text. -/
inductive RuleDefect : Type
  /-- `fakeExp`'s denominator is zero. -/
  | zeroBlobBaseFeeUpdateFraction
  /-- EIP-7918's reserve-price branch would divide by a zero blob ceiling. -/
  | zeroBlobMax
  /-- The blob target exceeds the ceiling, so `max - target` truncates to `0`. -/
  | blobTargetAboveMax (target max : Nat)
  /-- `MODEXP`'s `GQUADDIVISOR` is zero. -/
  | zeroModexpGasDivisor
  /-- An account access would cost less than a warm one, so a cold access at
  `BALANCE`, `EXTCODE*` or a `CALL` need charge nothing. -/
  | accountAccessBelowWarm (coldAccountAccess : Nat)
  /-- `CREATE` would cost nothing, so an empty-initcode creation need charge
  nothing. -/
  | zeroCreateAccess
  /-- A value-bearing call would hand its child more stipend than it charges
  its parent. -/
  | callValueBelowStipend (callValue : Nat)
deriving DecidableEq, Repr

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
  /-- A supplied rule record carries a parameter the semantics cannot use. -/
  | invalidForkRules (defect : RuleDefect)
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
  | .invalidForkRules defect =>
    renderTagged invalidForkRulesTag <| .text <|
      match defect with
      | .zeroBlobBaseFeeUpdateFraction =>
        "the blob base-fee update fraction is zero"
      | .zeroBlobMax => "the blob gas ceiling is zero"
      | .blobTargetAboveMax target max =>
        s!"the blob gas target {target} exceeds the ceiling {max}"
      | .zeroModexpGasDivisor => "the MODEXP gas divisor is zero"
      | .accountAccessBelowWarm cold =>
        s!"a cold account access costs {cold}, below the warm access cost 100"
      | .zeroCreateAccess => "the CREATE base cost is zero"
      | .callValueBelowStipend callValue =>
        s!"a value-bearing call costs {callValue}, below the 2300 stipend it \
           hands the child"

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
#guard ChainContextError.render (.invalidForkRules .zeroBlobBaseFeeUpdateFraction)
  = "InvalidForkRulesError : the blob base-fee update fraction is zero"
#guard ChainContextError.render (.invalidForkRules .zeroBlobMax)
  = "InvalidForkRulesError : the blob gas ceiling is zero"
#guard ChainContextError.render (.invalidForkRules (.blobTargetAboveMax 9 4))
  = "InvalidForkRulesError : the blob gas target 9 exceeds the ceiling 4"
#guard ChainContextError.render (.invalidForkRules .zeroModexpGasDivisor)
  = "InvalidForkRulesError : the MODEXP gas divisor is zero"

/-- `Fork.rules?` as a failing lookup, with the typed reason every
explicit-fork entry point reports for an unimplemented fork. Declared here,
after the support vocabulary, because Step 10 made the reason a constructor:
the rendered message is byte-for-byte the one this function always emitted. -/
def Fork.rules (f : Fork) : Except SupportError ForkRules :=
  match f.rules? with
  | some rules => .ok rules
  | none => .error (.unsupportedFork f)

theorem Fork.rules_valid {f : Fork} {r : ForkRules} (h : f.rules = .ok r) :
    r.Valid := by
  rw [Fork.rules] at h
  cases hr : f.rules? with
  | none => rw [hr] at h; cases h
  | some r' => rw [hr] at h; cases h; exact Fork.rules?_valid hr

/-- Why a configured fork or rules lookup failed: the schedule itself is not a
usable context, or the input is outside the supported domain. The two channels
stay distinct because the import layer routes them distinctly -- neither may
ever read as a candidate-block verdict. -/
inductive RulesLookupError : Type
  | context (reason : ChainContextError)
  | support (reason : SupportError)
deriving DecidableEq, Repr

/-- The one renderer for `RulesLookupError`: pure delegation. -/
def RulesLookupError.render : RulesLookupError → String
  | .context reason => reason.render
  | .support reason => reason.render

--------------- THE CHECKED ARBITRARY-RULE CONSTRUCTOR ---------------

/-- The first structural premise a rule record fails, or `none` if it fails
none. The order is the order the premises are stated in `ForkRules.Valid`, so
one defect is reported rather than a list. -/
def ForkRules.defect? (r : ForkRules) : Option RuleDefect :=
  if r.blob.baseFeeUpdateFraction = 0 then
    some .zeroBlobBaseFeeUpdateFraction
  else if r.blob.max = 0 then
    some .zeroBlobMax
  else if r.blob.max < r.blob.target then
    some (.blobTargetAboveMax r.blob.target r.blob.max)
  else if r.modexp.gasDivisor = 0 then
    some .zeroModexpGasDivisor
  else if r.gas.coldAccountAccess < 100 then
    some (.accountAccessBelowWarm r.gas.coldAccountAccess)
  else if r.gas.createAccess = 0 then
    some .zeroCreateAccess
  else if r.gas.callValue < 2300 then
    some (.callValueBelowStipend r.gas.callValue)
  else
    none

/-- `defect?` decides `Valid`: it answers `none` exactly on the valid records,
so the check below neither over- nor under-reports. -/
theorem ForkRules.defect?_eq_none_iff {r : ForkRules} :
    r.defect? = none ↔ r.Valid := by
  rw [ForkRules.defect?, ForkRules.Valid, BlobSchedule.Valid, GasSchedule.Valid]
  repeat' split
  all_goals simp_all
  all_goals omega

-- Each gas-schedule obligation is refused under its own name, so a failure
-- says which number the semantics cannot use rather than "the record is
-- invalid". The vehicle passes all of them.
#guard ForkRules.defect? { pragueRules with
    gas := { pragueGasSchedule with coldAccountAccess := 99 } }
  = some (.accountAccessBelowWarm 99)
#guard ForkRules.defect? { pragueRules with
    gas := { pragueGasSchedule with createAccess := 0 } }
  = some .zeroCreateAccess
#guard ForkRules.defect? { pragueRules with
    gas := { pragueGasSchedule with callValue := 2299 } }
  = some (.callValueBelowStipend 2299)
#guard ForkRules.defect? amsterdamMeteringRules = none

/-- A rule set together with the proof that its parameters are usable.

This is what an entry point should demand of a caller-supplied `ForkRules`:
the witness travels with the record instead of being rechecked, or worse,
assumed. The named fork rules are exported as `ValidRules` below, so nothing
in-tree pays for the check. -/
structure ValidRules : Type where
  rules : ForkRules
  valid : rules.Valid

/-- The checked constructor for an arbitrary explicit rule record. It is the
only way to obtain a `ValidRules` from a record this module did not build. -/
def ValidRules.check (r : ForkRules) : Except ChainContextError ValidRules :=
  match h : r.defect? with
  | some defect => .error (.invalidForkRules defect)
  | none => .ok ⟨r, ForkRules.defect?_eq_none_iff.mp h⟩

theorem ValidRules.check_eq_ok_iff {r : ForkRules} :
    (∃ vr, ValidRules.check r = .ok vr) ↔ r.Valid := by
  constructor
  · rintro ⟨vr, h⟩
    rw [ValidRules.check] at h
    split at h
    · cases h
    · rename_i hd; cases h; exact ForkRules.defect?_eq_none_iff.mp hd
  · intro hv
    refine ⟨⟨r, hv⟩, ?_⟩
    rw [ValidRules.check]
    split
    · rename_i hd
      exact absurd (ForkRules.defect?_eq_none_iff.mpr hv) (by simp [hd])
    · rfl

/-- The named rule sets, with their witnesses attached. -/
def pragueValidRules : ValidRules := ⟨pragueRules, pragueRules_valid⟩
def osakaValidRules : ValidRules := ⟨osakaRules, osakaRules_valid⟩
def bpo1ValidRules : ValidRules := ⟨bpo1Rules, bpo1Rules_valid⟩
def bpo2ValidRules : ValidRules := ⟨bpo2Rules, bpo2Rules_valid⟩

/-- A fork identity resolves straight to checked rules. -/
def Fork.validRules? (f : Fork) : Option ValidRules :=
  match h : f.rules? with
  | some r => some ⟨r, Fork.rules?_valid h⟩
  | none => none

theorem Fork.validRules?_rules (f : Fork) :
    (f.validRules?.map ValidRules.rules) = f.rules? := by
  rw [Fork.validRules?]; split <;> simp_all

-- The check accepts every named rule set and reports the first defect of a
-- record that carries one.
#guard (ValidRules.check pragueRules).toOption.isSome
#guard (ValidRules.check osakaRules).toOption.isSome
#guard (ValidRules.check bpo1Rules).toOption.isSome
#guard (ValidRules.check bpo2Rules).toOption.isSome
#guard ValidRules.check
    { pragueRules with
      blob := { pragueBlobSchedule with baseFeeUpdateFraction := 0 } }
  |>.toOption.isNone
#guard ({ pragueRules with
          blob := { pragueBlobSchedule with baseFeeUpdateFraction := 0 } }
        : ForkRules).defect? = some .zeroBlobBaseFeeUpdateFraction
#guard ({ pragueRules with blob := { pragueBlobSchedule with max := 0 } }
        : ForkRules).defect? = some .zeroBlobMax
#guard ({ pragueRules with
          blob := { pragueBlobSchedule with
                    target := pragueBlobSchedule.max + 1 } }
        : ForkRules).defect?
  = some (.blobTargetAboveMax (pragueBlobSchedule.max + 1) pragueBlobSchedule.max)
#guard ({ pragueRules with
          modexp := { pragueModexpRules with gasDivisor := 0 } }
        : ForkRules).defect? = some .zeroModexpGasDivisor
#guard pragueRules.defect?.isNone
-- The boundary: target equal to the ceiling is usable, one above it is not.
#guard ({ pragueRules with
          blob := { pragueBlobSchedule with
                    target := pragueBlobSchedule.max } } : ForkRules).defect?.isNone


namespace ChainConfig

/-- Every activation after the first must move strictly forward in both time
and fork order. Equal timestamps would make the active fork depend on list
order, and a non-increasing fork sequence would describe a chain that goes
backwards. -/
private def validateSteps : List ForkActivation → Except ChainContextError Unit
  | [] => .ok ()
  | [_] => .ok ()
  | prev :: next :: rest => do
    if next.timestamp ≤ prev.timestamp then
      .error (.nonIncreasingActivations prev next)
    if next.fork.index ≤ prev.fork.index then
      .error (.nonForwardActivations prev next)
    validateSteps (next :: rest)

/-- A schedule is usable when it covers every block unambiguously: it names at
least one fork, and every later activation moves strictly forward in time and
fork order. There is deliberately no requirement that the first activation
begin at timestamp 0 -- a configuration may support only eras from some later
floor onward, and a timestamp before that floor is `SupportError.unsupportedEra`
(from `forkAt` below), never `InvalidChainConfigError`. -/
def validate (cfg : ChainConfig) : Except ChainContextError Unit := do
  match cfg.activations with
  | [] => .error .emptySchedule
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
def forkAt (cfg : ChainConfig) (timestamp : Nat) :
    Except RulesLookupError Fork := do
  Except.mapError RulesLookupError.context cfg.validate
  match cfg.forkAt? timestamp with
  | some f => .ok f
  | none =>
    -- `cfg.validate` above guarantees `cfg.activations` is nonempty, so
    -- `head?` always finds the floor; the fallback is unreachable in practice
    -- but keeps this total without threading a nonemptiness proof through.
    let floor := (cfg.activations.head?.map (·.timestamp)).getD 0
    .error (.support (.unsupportedEra timestamp floor))

/-- The rules active at `timestamp`. Fails if the schedule is unusable or if
the selected fork's rules are not implemented. -/
def rulesAt (cfg : ChainConfig) (timestamp : Nat) :
    Except RulesLookupError ForkRules := do
  Except.mapError RulesLookupError.support (← cfg.forkAt timestamp).rules

/-- Every rule set a configured lookup produces is structurally usable, so the
configured entry points carry `ForkRules.Valid` without checking for it. -/
theorem rulesAt_valid {cfg : ChainConfig} {timestamp : Nat} {r : ForkRules}
    (h : cfg.rulesAt timestamp = .ok r) : r.Valid := by
  rw [ChainConfig.rulesAt] at h
  cases hf : cfg.forkAt timestamp with
  | error e => rw [hf] at h; cases h
  | ok f =>
    rw [hf] at h
    simp only [bind, Except.bind] at h
    cases hr : f.rules with
    | error e => rw [hr] at h; simp [Except.mapError] at h
    | ok rr =>
      rw [hr] at h
      simp only [Except.mapError, Except.ok.injEq] at h
      exact h ▸ Fork.rules_valid hr

/-- A schedule that `validate` accepts, as a decidable proposition.

This is the `Prop` face of `ChainConfig.validate`, and it exists for the
proof-carrying configured chain (P0.1 item 4): a witness that a schedule has
already been checked travels with the pair, so a repeated configured client
neither rechecks it nor silently proceeds with one that was never checked. It
deliberately says nothing about `chainId`; agreement with a snapshot is
`checkChainId`'s separate question. -/
def Valid (cfg : ChainConfig) : Prop :=
  cfg.validate.toOption.isSome = true

instance (cfg : ChainConfig) : Decidable cfg.Valid := by
  unfold ChainConfig.Valid; infer_instance

theorem valid_iff {cfg : ChainConfig} : cfg.Valid ↔ cfg.validate = .ok () := by
  unfold ChainConfig.Valid
  cases h : cfg.validate with
  | error e => simp [Except.toOption]
  | ok u => cases u; simp [Except.toOption]

-- There is deliberately no `ChainConfig.validRulesAt` packaging a `ValidRules`
-- behind the configured lookup's current error channel: its signature would be
-- a new stringly-typed carrier, which is exactly what `check-integrity.sh` R4
-- keeps out of this closure, and the allowlist is a shrink-only budget with
-- nothing spare. The witness is available on demand from `rulesAt_valid` above,
-- and packaging it at the configured entry points belongs with the
-- error-carrier retyping in Step 10.

/-- The configuration of a chain that is at Prague from genesis and never
transitions. -/
def pragueOnly (chainId : UInt64) : ChainConfig :=
  { chainId := chainId, activations := [⟨.prague, 0⟩] }

-- The two `pragueOnly` bridge facts below exist for downstream proof clients
-- (Blanc's `BlockChain.Reach.toReachUsing` connects the fixed-Prague
-- reachability ladder to the configured one): a Prague-only schedule is valid
-- for every chain identity and selects Prague's rules at every timestamp, and
-- a client should consume these rather than unfold `validate`/`forkAt`
-- (fixed decision 10).

/-- A Prague-only schedule is a valid schedule for every chain identity:
`validate` never reads `chainId`, and the singleton activation list has no
step to reject. -/
theorem pragueOnly_validate (chainId : UInt64) :
    (pragueOnly chainId).validate = .ok () := rfl

theorem pragueOnly_valid (chainId : UInt64) : (pragueOnly chainId).Valid :=
  valid_iff.mpr (pragueOnly_validate chainId)

/-- A Prague-only schedule selects Prague's rules at every timestamp: its
single activation floor is 0, so no timestamp precedes the supported era. -/
theorem pragueOnly_rulesAt (chainId : UInt64) (timestamp : Nat) :
    (pragueOnly chainId).rulesAt timestamp = .ok pragueRules := rfl

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

-- Guard helpers: the boundary checks below match typed reasons directly.
private def ctxFails {α : Type} (p : ChainContextError → Bool) :
    Except ChainContextError α → Bool
  | .error e => p e
  | .ok _ => false

private def lookupFails {α : Type} (p : RulesLookupError → Bool) :
    Except RulesLookupError α → Bool
  | .error e => p e
  | .ok _ => false

private def isContextL : RulesLookupError → Bool
  | .context _ => true | _ => false
private def isEraL : RulesLookupError → Bool
  | .support (.unsupportedEra _ _) => true | _ => false

-- Fork labels round-trip, and nothing else parses.
#guard Fork.all.all (fun f => Fork.ofString? f.toString = some f)
#guard Fork.ofString? "Prague" = some .prague
#guard Fork.ofString? "Osaka" = some .osaka
#guard Fork.ofString? "BPO1" = some .bpo1
#guard Fork.ofString? "BPO2" = some .bpo2
#guard Fork.ofString? "Amsterdam" = some .amsterdam
#guard (Fork.ofString? "Cancun").isNone
#guard (Fork.ofString? "prague").isNone
#guard (Fork.ofString? "amsterdam").isNone
#guard (Fork.ofString? "").isNone
#guard Fork.all.length = 5
#guard Fork.all.map Fork.index = [0, 1, 2, 3, 4]

-- The declared set and the runnable set are different lists, and both are
-- derived from `Fork.rules?` rather than restated. Amsterdam is the whole
-- difference: it is declared, it parses, it has a position in the chain, and
-- it does not resolve.
#guard Fork.supported = [.prague, .osaka, .bpo1, .bpo2]
#guard Fork.unimplemented = [.amsterdam]
#guard Fork.supported.length + Fork.unimplemented.length = Fork.all.length
#guard Fork.amsterdam.index = 4
#guard Fork.amsterdam.rules? = none

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

-- The ten shared-formula gas numbers, pinned as literals here and tied to the
-- global constants they came from by the `rfl` lemmas in `Jaune/Machine.lean`.
-- Both halves are needed: these say what the numbers are, those say that
-- nothing observing the old globals can tell the difference.
#guard pragueRules.gas.coldAccountAccess = 2600
#guard pragueRules.gas.callValue = 9000
#guard pragueRules.gas.createAccess = 32000
#guard pragueRules.gas.storageClearRefund = 4800
#guard pragueRules.gas.txBase = 21000
#guard pragueRules.gas.txAccessListAddress = 2400
#guard pragueRules.gas.txAccessListStorageKey = 1900
#guard pragueRules.gas.floorTokenCost = 10
#guard pragueRules.gas.perAuthIntrinsic = 25000
#guard pragueRules.gas.codeReadSurcharge = 0

-- The metering switch is off for every fork this build runs. Stated on Prague
-- here and on the whole supported chain below; the `rfl` lemma in
-- `Jaune/Machine.lean` is what lets a Prague-stated proof unfold it away.
#guard pragueRules.stateGas = none

-- Prague's header carries neither Amsterdam field, and its request list is the
-- two contracts today's fold calls, in today's order.
#guard pragueRules.header.blockAccessListHash = false
#guard pragueRules.header.slotNumber = false
#guard pragueRules.requests.length = 2
#guard pragueRules.requests.map Prod.fst = [1, 2]
#guard pragueRules.requests =
  [(1, (0x00000961Ef480Eb55e80D19ad83579A64c007002 : Adr)),
   (2, (0x0000BBdDc7CE488642fb579F8B00f3a590007251 : Adr))]

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

-- Osaka moves none of the three new categories. Stated about the whole record
-- rather than field by field, so a future edit that gives Osaka a gas, header,
-- or request rule of its own fails here.
#guard osakaRules.gas = pragueRules.gas
#guard osakaRules.header = pragueRules.header
#guard osakaRules.requests = pragueRules.requests

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
-- transaction limit, opcode, precompile, gas, header, or request rule of its
-- own. Because they compare whole records, they extend to the three
-- categories added for Amsterdam without being restated for them -- which is
-- the point of writing a BPO record as an update of Osaka's.
#guard { bpo1Rules with fork := .osaka, blob := osakaBlobSchedule } = osakaRules
#guard { bpo2Rules with fork := .osaka, blob := osakaBlobSchedule } = osakaRules
#guard bpo1Rules.fork = .bpo1
#guard bpo2Rules.fork = .bpo2

-- The same fact stated field by field for the three new categories, so that a
-- failure names the category rather than "the records differ".
#guard bpo1Rules.gas = pragueGasSchedule
#guard bpo2Rules.gas = pragueGasSchedule
#guard bpo1Rules.stateGas = none
#guard bpo2Rules.stateGas = none
#guard bpo1Rules.header = pragueHeaderRules
#guard bpo2Rules.header = pragueHeaderRules
#guard bpo1Rules.requests = pragueRequests
#guard bpo2Rules.requests = pragueRequests

-- Every fork this build runs shares one gas schedule, one header rule, and one
-- request list: the whole supported chain is Prague's in these three
-- categories. Amsterdam is what makes them vary, and it does not resolve here.
#guard Fork.supported.all (fun f =>
  match f.rules? with
  | some r => r.gas == pragueGasSchedule && r.header == pragueHeaderRules
      && r.requests == pragueRequests && r.stateGas == none
  | none => false)

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

-- Amsterdam's numbers, pinned as literals against the metering vehicle. This
-- is the only place in the build where they are written down; the constants
-- gate compares each of them against the pinned upstream revision, and the
-- `#guard`s here are what a mutation of one has to get past first.
#guard amsterdamMeteringRules.gas.coldAccountAccess = 3000
#guard amsterdamMeteringRules.gas.callValue = 11300
#guard amsterdamMeteringRules.gas.createAccess = 12000
#guard amsterdamMeteringRules.gas.storageClearRefund = 11616
#guard amsterdamMeteringRules.gas.txBase = 12000
#guard amsterdamMeteringRules.gas.txAccessListAddress = 2900
#guard amsterdamMeteringRules.gas.txAccessListStorageKey = 2000
#guard amsterdamMeteringRules.gas.floorTokenCost = 16
#guard amsterdamMeteringRules.gas.perAuthIntrinsic = 7816
#guard amsterdamMeteringRules.gas.codeReadSurcharge = 100

-- The four derivations upstream states as sums and differences, checked as
-- arithmetic rather than restated as literals: if a repricing moves one side,
-- the identity is what fails.
#guard amsterdamGasSchedule.callValue = 9000 + 2300
#guard amsterdamGasSchedule.createAccess
  = 9000 + amsterdamGasSchedule.coldAccountAccess
#guard amsterdamGasSchedule.storageClearRefund = (10000 + 2100) * 4800 / 5000
#guard amsterdamGasSchedule.txAccessListAddress
  = amsterdamGasSchedule.coldAccountAccess - 100
#guard amsterdamGasSchedule.txAccessListStorageKey = 2100 - 100
#guard amsterdamGasSchedule.perAuthIntrinsic
  = 101 * amsterdamGasSchedule.floorTokenCost + 3000 + 3000 + 2 * 100

-- The state-gas dimension: the ten fields, and the three costs derived from
-- them. The products are guarded rather than the products' values being
-- fields, so that a change to `costPerStateByte` moves all three at once.
#guard amsterdamStateGasRules.costPerStateByte = 1530
#guard amsterdamStateGasRules.stateBytesPerNewAccount = 120
#guard amsterdamStateGasRules.stateBytesPerStorageSet = 64
#guard amsterdamStateGasRules.stateBytesPerAuthBase = 23
#guard amsterdamStateGasRules.storageWrite = 10000
#guard amsterdamStateGasRules.accountWrite = 9000
#guard amsterdamStateGasRules.txValueCost = 6000
#guard amsterdamStateGasRules.accessListAddressFloorTokens = 80
#guard amsterdamStateGasRules.accessListStorageKeyFloorTokens = 128
#guard amsterdamStateGasRules.systemMaxSstoresPerCall = 16
#guard amsterdamStateGasRules.storageSet = 97920
#guard amsterdamStateGasRules.newAccount = 183600
#guard amsterdamStateGasRules.authBase = 35190
#guard amsterdamStateGasRules.systemReservoir = 16 * 97920

-- The two identities `CALL_VALUE` and `CREATE_ACCESS` are built from, stated
-- across the two records so that the split between `GasSchedule` and
-- `StateGasRules` is checked rather than assumed.
#guard amsterdamGasSchedule.callValue
  = amsterdamStateGasRules.accountWrite + 2300
#guard amsterdamGasSchedule.createAccess
  = amsterdamStateGasRules.accountWrite + amsterdamGasSchedule.coldAccountAccess
#guard amsterdamGasSchedule.storageClearRefund
  = (amsterdamStateGasRules.storageWrite + 2100) * 4800 / 5000

-- A plain Amsterdam value transfer still costs 21,000 intrinsic gas, as three
-- numbers rather than one: EIP-2780 decomposes the old base, it does not
-- reprice the common case.
#guard amsterdamGasSchedule.txBase + amsterdamGasSchedule.coldAccountAccess
  + amsterdamStateGasRules.txValueCost = 21000

-- The vehicle is BPO2's record with exactly three fields moved. Stated as a
-- record update in both directions, so it cannot silently acquire a
-- block-level rule that belongs to a later goal: undoing the identity, the gas
-- schedule and the switch must give BPO2 back.
#guard { amsterdamMeteringRules with
  fork := .bpo2, gas := pragueGasSchedule, stateGas := none } = bpo2Rules
#guard amsterdamMeteringRules.fork = .amsterdam
#guard amsterdamMeteringRules.stateGas = some amsterdamStateGasRules
#guard amsterdamMeteringRules.blob = bpo2BlobSchedule
#guard amsterdamMeteringRules.code = pragueCodeLimits
#guard amsterdamMeteringRules.op = osakaOpcodeRules
#guard amsterdamMeteringRules.tx = osakaTransactionLimits
#guard amsterdamMeteringRules.precompiles = osakaPrecompiles

-- What the vehicle deliberately does NOT claim. Each of these is a rule the
-- block-level goal `jaune-amsterdam-block-v1` owns, and each is BPO2's here.
-- A guard rather than a comment, so that adding one of them to this record
-- without moving the goal boundary fails.
#guard amsterdamMeteringRules.header.blockAccessListHash = false
#guard amsterdamMeteringRules.header.slotNumber = false
#guard amsterdamMeteringRules.requests = pragueRequests
#guard amsterdamMeteringRules.code.maxCodeSize = 24576
#guard amsterdamMeteringRules.op.clz = true

-- And the vehicle is not reachable through fork identity: this is what keeps
-- it a metering vehicle rather than a declaration that Amsterdam is supported.
#guard Fork.amsterdam.rules? = none
#guard Fork.amsterdam.rules?.isNone
#guard ¬ Fork.supported.contains .amsterdam

-- Every fork this build runs resolves to rules that name it back, and the one
-- it does not run is refused with its own identity rather than with another
-- fork's rules. The unsupported-fork branch is reachable again, which is the
-- point: `Fork.amsterdam` is a declared identity whose semantics belong to a
-- later goal, and until then every entry point must say so.
#guard Fork.supported.all (fun f => f.rules?.isSome)
#guard Fork.supported.all (fun f => (f.rules?.map ForkRules.fork) = some f)
#guard Fork.unimplemented.all (fun f => f.rules?.isNone)
#guard Fork.prague.rules = .ok pragueRules
#guard Fork.osaka.rules = .ok osakaRules
#guard Fork.bpo1.rules = .ok bpo1Rules
#guard Fork.bpo2.rules = .ok bpo2Rules
#guard Fork.amsterdam.rules = .error (.unsupportedFork .amsterdam)
#guard Fork.amsterdam.validRules?.isNone
#guard Fork.supported.all (fun f => f.validRules?.isSome)
-- The refusal a user actually reads, from the live producer, on the exact
-- label the devnet corpus carries.
#guard (match Fork.amsterdam.rules with
  | .error e => e.render ==
      "UnsupportedForkError : fork Amsterdam is a declared protocol fork whose \
       execution rules are not implemented in this build"
  | .ok _ => false)
#guard SupportError.render (.unsupportedFork .amsterdam)
  = "UnsupportedForkError : fork Amsterdam is a declared protocol fork whose \
     execution rules are not implemented in this build"

-- A usable schedule is non-empty and moves strictly forward in both time and
-- fork order. It need not start at genesis: a schedule may support only eras
-- from some later floor onward, and that is a usable schedule, not an invalid
-- one -- `ChainConfig.forkAt` is where a too-early timestamp is refused.
#guard (ChainConfig.pragueOnly 1).validate.toOption.isSome
#guard (ChainConfig.mk 1 []).validate = .error .emptySchedule
#guard (ChainConfig.mk 1 [⟨.prague, 1⟩]).validate.toOption.isSome
#guard (ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 0⟩]).validate
  = .error (.nonIncreasingActivations ⟨.prague, 0⟩ ⟨.osaka, 0⟩)
#guard (ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 100⟩, ⟨.bpo1, 100⟩]).validate
  = .error (.nonIncreasingActivations ⟨.osaka, 100⟩ ⟨.bpo1, 100⟩)
#guard (ChainConfig.mk 1 [⟨.osaka, 0⟩, ⟨.prague, 100⟩]).validate
  = .error (.nonForwardActivations ⟨.osaka, 0⟩ ⟨.prague, 100⟩)
#guard (ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 100⟩, ⟨.osaka, 200⟩]).validate
  = .error (.nonForwardActivations ⟨.osaka, 100⟩ ⟨.osaka, 200⟩)
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
#guard lookupFails isEraL (guardFloorSchedule.forkAt 999)
#guard guardFloorSchedule.forkAt 999
  = .error (.support (.unsupportedEra 999 1000))
#guard guardFloorSchedule.forkAt 1000 = .ok .prague
#guard guardFloorSchedule.forkAt 1999 = .ok .prague
#guard guardFloorSchedule.forkAt 2000 = .ok .osaka
#guard ¬ lookupFails isContextL (guardFloorSchedule.forkAt 999)

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
#guard (ChainConfig.mk 1 []).forkAt 0 = .error (.context .emptySchedule)
#guard (ChainConfig.mk 1 []).rulesAt 0 = .error (.context .emptySchedule)

-- Mainnet's schedule is usable, and each of its recorded activation timestamps
-- is a boundary: the second before it still runs the old rules. Genesis, and
-- everything up to one second before the real Prague activation, is outside
-- this build's declared domain -- the exact P0.5 fix, since Jaune implements
-- no pre-Prague era and must not silently answer those blocks as Prague.
#guard mainnetChainConfig.validate.toOption.isSome
#guard mainnetChainConfig.Valid
#guard ¬ (ChainConfig.mk 1 []).Valid
#guard mainnetChainConfig.chainId = 1
#guard lookupFails isEraL (mainnetChainConfig.forkAt 0)
#guard lookupFails isEraL
  (mainnetChainConfig.forkAt (mainnetPragueTimestamp - 1))
#guard mainnetChainConfig.forkAt (mainnetPragueTimestamp - 1)
  = .error (.support (.unsupportedEra (mainnetPragueTimestamp - 1)
      mainnetPragueTimestamp))
#guard mainnetChainConfig.forkAt mainnetPragueTimestamp = .ok .prague
#guard mainnetChainConfig.forkAt (mainnetOsakaTimestamp - 1) = .ok .prague
#guard mainnetChainConfig.forkAt mainnetOsakaTimestamp = .ok .osaka
#guard mainnetChainConfig.forkAt (mainnetBpo1Timestamp - 1) = .ok .osaka
#guard mainnetChainConfig.forkAt mainnetBpo1Timestamp = .ok .bpo1
#guard mainnetChainConfig.forkAt (mainnetBpo2Timestamp - 1) = .ok .bpo1
#guard mainnetChainConfig.forkAt mainnetBpo2Timestamp = .ok .bpo2
#guard mainnetChainConfig.rulesAt mainnetBpo2Timestamp = .ok bpo2Rules
-- D13 of the Amsterdam programme: the mainnet schedule keeps its four
-- activations until upstream `FORK_CRITERIA` carries a real Amsterdam
-- timestamp. Declaring the identity must not add an activation, so this is
-- stated against the supported list and against Amsterdam's absence directly,
-- never against `Fork.all`.
#guard mainnetChainConfig.activations.map ForkActivation.fork = Fork.supported
#guard mainnetChainConfig.activations.length = 4
#guard ¬ (mainnetChainConfig.activations.map ForkActivation.fork).contains
  .amsterdam

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
#guard ForkTransition.ofString? "BPO2ToAmsterdamAtTime15k"
  = some ⟨.bpo2, .amsterdam, 15000⟩
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

-- The devnet corpus's transition label. Its schedule is usable -- both
-- endpoints are declared and the pair moves forward -- and the refusal lands
-- exactly at the activation timestamp, as a support failure naming Amsterdam.
-- Everything before it still runs BPO2's rules, which is what makes a
-- transition fixture's pre-fork blocks meaningful rather than skipped.
private def guardBpo2ToAmsterdam : ForkTransition := ⟨.bpo2, .amsterdam, 15000⟩

#guard NetworkSpec.ofString? "BPO2ToAmsterdamAtTime15k"
  = some (.transition guardBpo2ToAmsterdam)
#guard (NetworkSpec.transition guardBpo2ToAmsterdam).forks = [.bpo2, .amsterdam]
#guard (guardBpo2ToAmsterdam.chainConfig 1).validate.toOption.isSome
#guard (guardBpo2ToAmsterdam.chainConfig 1).rulesAt 0 = .ok bpo2Rules
#guard (guardBpo2ToAmsterdam.chainConfig 1).rulesAt 14999 = .ok bpo2Rules
#guard (guardBpo2ToAmsterdam.chainConfig 1).forkAt 15000 = .ok .amsterdam
#guard (guardBpo2ToAmsterdam.chainConfig 1).rulesAt 15000
  = .error (.support (.unsupportedFork .amsterdam))
-- The refusal is a support failure, never a context failure: the schedule is
-- not at fault and the block is not being called invalid.
#guard ¬ lookupFails isContextL ((guardBpo2ToAmsterdam.chainConfig 1).rulesAt 15000)

-- A parseable label may still name an unusable schedule; it is refused where
-- every other unusable schedule is, rather than at the parser.
#guard ForkTransition.ofString? "OsakaToPragueAtTime15k"
  = some ⟨.osaka, .prague, 15000⟩
#guard lookupFails isContextL
  (((⟨.osaka, .prague, 15000⟩ : ForkTransition).chainConfig 1).rulesAt 0)
#guard lookupFails isContextL
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

-- The producers now return the reasons themselves; what remains to pin here is
-- that rendering a live producer's reason still yields the exact goldens.
#guard (match (ChainConfig.mk 1 []).validate with
  | .error e => e.render == "InvalidChainConfigError : the activation schedule is empty"
  | .ok _ => false)
#guard (match (ChainConfig.mk 1 [⟨.prague, 0⟩, ⟨.osaka, 0⟩]).validate with
  | .error e => e.render ==
      "InvalidChainConfigError : activation timestamps must strictly increase, \
       but Osaka at 0 does not follow Prague at 0"
  | .ok _ => false)
#guard (match guardFloorSchedule.forkAt 999 with
  | .error e => e.render ==
      "UnsupportedEraError : timestamp 999 precedes the earliest era this \
       configuration supports, which begins at 1000"
  | .ok _ => false)
#guard (match mainnetChainConfig.forkAt 0 with
  | .error e => e ==
      .support (.unsupportedEra 0 mainnetPragueTimestamp)
  | .ok _ => false)

end Jaune
