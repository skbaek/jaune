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

The chain begins at Byzantium, runs through the twelve pre-Prague historical
forks, and continues to Amsterdam. `constantinople` names the EIP-1283 rule
set, which never activated on mainnet (mainnet went from Byzantium straight to
Petersburg at block 7,280,000); it is carried for the legacy corpus, which runs
about 21k cases under the `Constantinople` network label. Being listed here
means the *identity* is known, not that its rules are implemented: see
`Fork.rules?`. -/
inductive Fork : Type
  | byzantium
  | constantinople
  | petersburg
  | istanbul
  | muirGlacier
  | berlin
  | london
  | arrowGlacier
  | grayGlacier
  | paris
  | shanghai
  | cancun
  | prague
  | osaka
  | bpo1
  | bpo2
  | amsterdam
deriving DecidableEq, Repr

namespace Fork

/-- The default fork is Prague: generic code that needs a fork without choosing
one keeps the historical single-fork behaviour. -/
instance : Inhabited Fork := ⟨.prague⟩

/-- The canonical label. These are the strings that fixture `network` fields
and the `--network` command-line option use. -/
def toString : Fork → String
  | .byzantium => "Byzantium"
  | .constantinople => "Constantinople"
  | .petersburg => "Petersburg"
  | .istanbul => "Istanbul"
  | .muirGlacier => "MuirGlacier"
  | .berlin => "Berlin"
  | .london => "London"
  | .arrowGlacier => "ArrowGlacier"
  | .grayGlacier => "GrayGlacier"
  | .paris => "Paris"
  | .shanghai => "Shanghai"
  | .cancun => "Cancun"
  | .prague => "Prague"
  | .osaka => "Osaka"
  | .bpo1 => "BPO1"
  | .bpo2 => "BPO2"
  | .amsterdam => "Amsterdam"

instance : ToString Fork := ⟨Fork.toString⟩

/-- Strict label parsing. There is no fallback and no case folding: an
unrecognised label is an error at every caller, never Prague.

Four legacy aliases parse to their canonical fork: `ConstantinopleFix` (the
legacy fixture label) alongside `Petersburg`, `Merge` (the consensus-layer
name) alongside `Paris`, and `Constantinople` to the EIP-1283 rule set. -/
def ofString? : String → Option Fork
  | "Byzantium" => some .byzantium
  | "Constantinople" => some .constantinople
  | "Petersburg" => some .petersburg
  | "ConstantinopleFix" => some .petersburg
  | "Istanbul" => some .istanbul
  | "MuirGlacier" => some .muirGlacier
  | "Berlin" => some .berlin
  | "London" => some .london
  | "ArrowGlacier" => some .arrowGlacier
  | "GrayGlacier" => some .grayGlacier
  | "Paris" => some .paris
  | "Merge" => some .paris
  | "Shanghai" => some .shanghai
  | "Cancun" => some .cancun
  | "Prague" => some .prague
  | "Osaka" => some .osaka
  | "BPO1" => some .bpo1
  | "BPO2" => some .bpo2
  | "Amsterdam" => some .amsterdam
  | _ => none

/-- Every *declared* fork, in activation order.

Being listed here means the *identity* is known, not that its rules are
implemented. This candidate resolves each declared fork's existing record
(see `Fork.rules?`). The two names are kept apart because
they answer different questions -- what this build *parses* against what it
will also *execute* -- and because a user-facing message must keep
distinguishing a label this build does not recognise from one it recognises
and refuses. -/
def all : List Fork :=
  [.byzantium, .constantinople, .petersburg, .istanbul, .muirGlacier, .berlin,
   .london, .arrowGlacier, .grayGlacier, .paris, .shanghai, .cancun,
   .prague, .osaka, .bpo1, .bpo2, .amsterdam]

/-- Position in the supported transition chain.

This is the *only* ordering notion on forks, and it exists so that a
`ChainConfig` schedule can be checked for monotonicity. It is not a licence to
compare forks inside execution. -/
def index : Fork → Nat
  | .byzantium => 0
  | .constantinople => 1
  | .petersburg => 2
  | .istanbul => 3
  | .muirGlacier => 4
  | .berlin => 5
  | .london => 6
  | .arrowGlacier => 7
  | .grayGlacier => 8
  | .paris => 9
  | .shanghai => 10
  | .cancun => 11
  | .prague => 12
  | .osaka => 13
  | .bpo1 => 14
  | .bpo2 => 15
  | .amsterdam => 16

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
  /-- EIP-7825: whole-transaction cap before Amsterdam; execution-gas cap thereafter. -/
  maxGas : Option Nat
  /-- EIP-8037: total transaction gas, including the state-gas reservoir. -/
  maxTotalGas : Option Nat := none
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

/-- Account- and slot-access prices before EIP-2929 (Berlin): one flat price
per opcode family, no warm/cold distinction. Under this shape the accessed
sets are not consulted for gas. -/
structure FlatAccessGas : Type where
  /-- `BALANCE`: 400 (Byzantium), 700 (EIP-1884, Istanbul). -/
  balance : Nat
  /-- `EXTCODESIZE` and `EXTCODECOPY`'s base: 700 (EIP-150) throughout. -/
  extCode : Nat
  /-- `EXTCODEHASH`: 400 (EIP-1052, Constantinople), 700 (EIP-1884). -/
  extCodeHash : Nat
  /-- `SLOAD`, and the no-op `SSTORE` price under net metering: 200, then
  800 (EIP-1884). -/
  sload : Nat
  /-- The `CALL`-family base: 700 (EIP-150) throughout. -/
  call : Nat
deriving DecidableEq, Repr

/-- The access-pricing shape. `eip2929` is today's code, textually: warm
`gasWarmAccess`, cold `gas.coldAccountAccess` / `gasColdSload`. -/
inductive AccessSchedule : Type
  | flat (g : FlatAccessGas)
  | eip2929
deriving DecidableEq, Repr

/-- The `SSTORE` shape. `netMetering = false` is the Byzantium/Petersburg
rule (20000 if zero to nonzero, else 5000; 15000 refund on clearing).
`netMetering = true` is EIP-1283 / EIP-2200 / EIP-2929 net metering, whose
no-op and cold numbers come from the access schedule. -/
structure SstoreRules : Type where
  /-- EIP-1283 net metering (Constantinople's rule set), kept through EIP-2200
  and EIP-2929. -/
  netMetering : Bool
  /-- EIP-2200's `gas_left <= GAS_CALL_STIPEND` sentry (Istanbul onwards;
  absent in EIP-1283 Constantinople). -/
  stipendSentry : Bool
deriving DecidableEq, Repr

/-- Transaction settlement numbers that move before Prague. -/
structure SettlementRules : Type where
  /-- The refund cap's divisor: 2 before EIP-3529 (London), 5 after. -/
  refundQuotient : Nat
  /-- `REFUND_SELF_DESTRUCT`: 24000 before EIP-3529, 0 after. -/
  selfdestructRefund : Nat
  /-- EIP-6780 (Cancun): `SELFDESTRUCT` deletes only an account created in the
  same transaction. Decoupled from `stateGas`. -/
  selfdestructOnlyCreated : Bool
  /-- EIP-161's end-of-transaction sweep of touched empty accounts;
  EELS drops it from Paris. -/
  touchedSweep : Bool
  /-- EELS `modify_state` destroys an account the modification leaves empty
  (`account_exists_and_is_empty`, then `destroy_account`) from Paris on.
  Before Paris it is `set_account` alone: the emptied account, with its
  storage, stays until the EIP-161 sweep removes it if it was touched. -/
  eraseEmptyOnModify : Bool
deriving DecidableEq, Repr

/-- Transaction admission and intrinsic-cost switches that move before Prague. -/
structure TransactionRules : Type where
  /-- The largest admitted EIP-2718 type: 0 before Berlin, 1 Berlin, 2 London,
  3 Cancun, 4 Prague. Monotone along the chain, so one number suffices. -/
  maxType : Nat
  /-- `TX_DATA_COST_PER_NON_ZERO`: 68, then 16 (EIP-2028, Istanbul). The zero
  byte stays 4. -/
  dataNonZero : Nat
  /-- EIP-7623's calldata floor (Prague). -/
  calldataFloor : Bool
  /-- EIP-3651: the coinbase starts warm (Shanghai). -/
  warmCoinbase : Bool
deriving DecidableEq, Repr

/-- Creation-time switches. -/
structure CreationRules : Type where
  /-- EIP-3860 (Shanghai): `code.maxInitCodeSize` is enforced and initcode is
  metered per word. When false the field is dormant. -/
  initCodeLimit : Bool
  /-- EIP-3541 (London): deposited code may not start with 0xEF. -/
  rejectEf : Bool
deriving DecidableEq, Repr

/-- Proof-of-work consensus numbers (Byzantium .. Gray Glacier). `none` from
Paris, where the seal leaves the execution layer. -/
structure ProofOfWorkRules : Type where
  /-- `BLOCK_REWARD`, in wei: 3 ETH (Byzantium), 2 ETH (Constantinople on). -/
  blockReward : Nat
  /-- `BOMB_DELAY_BLOCKS`: 3M, 5M, 9M, 9.7M, 10.7M, 11.4M. -/
  bombDelay : Nat
deriving DecidableEq, Repr

/-- The pre-transaction system calls. Withdrawals are gated by
`header.withdrawalsRoot` and the request pass by `header.requestsHash`. -/
structure SystemCallRules : Type where
  /-- EIP-4788 beacon-roots call (Cancun). -/
  beaconRoots : Bool
  /-- EIP-2935 history-storage call (Prague). -/
  historyStorage : Bool
deriving DecidableEq, Repr

/-- alt_bn128 precompile prices (EIP-196/197, repriced by EIP-1108). -/
structure Bn254Gas : Type where
  add : Nat
  mul : Nat
  pairingBase : Nat
  pairingPerPair : Nat
deriving DecidableEq, Repr

/-- `MODEXP`'s complexity function: EIP-198's piecewise polynomial, or
EIP-2565's `words ^ 2` (Berlin on; Osaka's EIP-7883 is the existing
`ModexpRules` coefficients over it). Nothing reads this yet (U8 owns the
EIP-198 shape); it is carried so the rule set names which formula it is. -/
inductive ModexpComplexity : Type
  | eip198
  | eip2565
deriving DecidableEq, Repr

/-- Opcodes whose availability changes along the supported transition chain.

An opcode this record switches off is not merely unimplemented: its byte is
undefined at that fork, so a contract reaching it halts on an invalid
instruction exactly as it would on any other unassigned byte. -/
structure OpcodeRules : Type where
  /-- EIP-145 `SHL`/`SHR`/`SAR` (Constantinople). -/
  shifts : Bool
  /-- EIP-1052 `EXTCODEHASH` (Constantinople). -/
  extCodeHash : Bool
  /-- EIP-1014 `CREATE2` (Constantinople). -/
  create2 : Bool
  /-- EIP-1344 `CHAINID` (Istanbul). -/
  chainId : Bool
  /-- EIP-1884 `SELFBALANCE` (Istanbul). -/
  selfBalance : Bool
  /-- EIP-3198 `BASEFEE` (London). -/
  baseFee : Bool
  /-- EIP-3855 `PUSH0` (Shanghai). -/
  push0 : Bool
  /-- EIP-1153 `TLOAD`/`TSTORE` (Cancun). -/
  transient : Bool
  /-- EIP-5656 `MCOPY` (Cancun). -/
  mcopy : Bool
  /-- EIP-4844 `BLOBHASH` (Cancun). -/
  blobHash : Bool
  /-- EIP-7516 `BLOBBASEFEE` (Cancun). -/
  blobBaseFee : Bool
  /-- EIP-7939 `CLZ` (0x1E), new at Osaka. -/
  clz : Bool
  /-- EIP-7843 `SLOTNUM` (0x4B), new at Amsterdam. -/
  slotnum : Bool
  /-- EIP-8024 `DUPN`, `SWAPN` and `EXCHANGE` (0xE6, 0xE7, 0xE8), new at
  Amsterdam. One flag for the three because EIP-8024 assigns them together and
  the pinned `vm/instructions/__init__.py` has no state in which one is defined
  without the others. -/
  stackAccess : Bool
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
  perAuthorizationIntrinsic : Nat
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
  /-- EIP-1559 `baseFeePerGas` (London). -/
  baseFee : Bool
  /-- EIP-4895 `withdrawalsRoot` (Shanghai); also gates withdrawals. -/
  withdrawalsRoot : Bool
  /-- EIP-4844 `blobGasUsed` and `excessBlobGas` (Cancun). -/
  blobGas : Bool
  /-- EIP-4788 `parentBeaconBlockRoot` (Cancun). -/
  parentBeaconBlockRoot : Bool
  /-- EIP-7685 `requestsHash` (Prague); also gates the request pass. -/
  requestsHash : Bool
deriving DecidableEq, Repr

/-- EIP-7928's block-level access-list rule data.

`ForkRules.bal` carries this record under an `Option`, and the `Option` is the
whole switch: `none` at Prague through BPO2, where no header commits to a
block-level access list and the block pipeline builds none; `some r` at
Amsterdam, where the pipeline records every state read and write, encodes the
list, compares its hash to `header.blockAccessListHash`, and refuses a block
whose item count exceeds `gasLimit / r.itemCost`. Nothing under `none`
allocates the builder, which is the bridge Prague-stated proofs use. -/
structure BlockAccessListRules : Type where
  /-- `GasCosts.BLOCK_ACCESS_LIST_ITEM`: the gas each address and each unique
  storage key of the list is deemed to cost, so that `gasLimit / itemCost`
  bounds the item count. Amsterdam 2000. -/
  itemCost : Nat
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
  opcodes : OpcodeRules
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
  requests : List (UInt8 × Address)
  /-- EIP-7928's block-level access-list rules, or `none` for a fork whose
  header does not commit to one. Independent of `header.blockAccessListHash`
  in type but not in fact: `ForkRules.Valid` ties the two together, because a
  header field with nothing to compare against, or a computed list with no
  header to check it, would each be half a rule. -/
  blockAccessListRules : Option BlockAccessListRules
  /-- The addresses at which a precompiled contract is active. -/
  precompiles : List Address
  /-- Access-pricing shape (EIP-2929 switch): flat before Berlin. -/
  access : AccessSchedule
  /-- `SSTORE` shape: plain before Constantinople's rule set, net metering on. -/
  sstore : SstoreRules
  /-- Settlement numbers and switches (refund quotient, selfdestruct, sweep). -/
  settlement : SettlementRules
  /-- Admission and intrinsic-cost switches (max type, nonzero price, floor,
  warm coinbase). -/
  transactionRules : TransactionRules
  /-- Creation switches (init-code limit, 0xEF rejection). -/
  creation : CreationRules
  /-- Proof-of-work consensus numbers, `none` from Paris. -/
  proofOfWork : Option ProofOfWorkRules
  /-- The pre-transaction system calls. -/
  systemCalls : SystemCallRules
  /-- alt_bn128 precompile prices. -/
  bn254 : Bn254Gas
  /-- `MODEXP` complexity function. -/
  modexpComplexity : ModexpComplexity
deriving DecidableEq

/-- EIP-7702 code delegation activates with type-4 transaction admission. -/
def ForkRules.delegationEnabled (rules : ForkRules) : Bool :=
  decide (4 ≤ rules.transactionRules.maxType)

/-- An address carries a precompile under these rules.

This replaces the former global `Adr.isPrecomp`, whose hard-wired `1 ≤ n ≤ 17`
range was a Prague fact stated at a use site. Precompile sets are not
contiguous in general -- Osaka's P256VERIFY sits at 0x100 -- so the rule is
carried as the activation set itself. -/
abbrev ForkRules.isPrecompile (rules : ForkRules) (a : Address) : Prop :=
  a ∈ rules.precompiles

instance {rules : ForkRules} {a : Address} : Decidable (rules.isPrecompile a) :=
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

/-- The block-level access-list rules are usable: `itemCost` is the divisor of
the item rule, so it must be positive. -/
def BlockAccessListRules.Valid (b : BlockAccessListRules) : Prop := 0 < b.itemCost

instance {b : BlockAccessListRules} : Decidable b.Valid := by
  unfold BlockAccessListRules.Valid; infer_instance

/-- A fork's optional access-list rules are usable: trivially when absent. -/
def ForkRules.blockAccessListRulesValid (r : ForkRules) : Prop :=
  match r.blockAccessListRules with
  | none => True
  | some b => b.Valid

instance {r : ForkRules} : Decidable r.blockAccessListRulesValid := by
  unfold ForkRules.blockAccessListRulesValid; cases r.blockAccessListRules <;> infer_instance

/-- A flat access schedule charges something for every family: the
termination argument's need under the pre-Berlin shape. -/
def FlatAccessGas.Valid (g : FlatAccessGas) : Prop :=
  0 < g.balance ∧ 0 < g.extCode ∧ 0 < g.extCodeHash ∧ 0 < g.sload ∧ 0 < g.call

instance {g : FlatAccessGas} : Decidable g.Valid := by
  unfold FlatAccessGas.Valid; infer_instance

def AccessSchedule.Valid : AccessSchedule → Prop
  | .flat g => g.Valid
  | .eip2929 => True

instance {a : AccessSchedule} : Decidable a.Valid := by
  cases a <;> unfold AccessSchedule.Valid <;> infer_instance

/-- The rule set's parameters are usable by the semantics that reads them.

Six groups, one per thing the semantics needs of a number it did not choose:
the blob schedule's divisors and its target/ceiling ordering, `MODEXP`'s
`GQUADDIVISOR`, -- since Amsterdam reprices the numbers the interpreter's own
termination argument leans on -- the gas schedule's three inequalities,
EIP-7928's item-cost divisor together with the fact that a fork commits to a
block-level access list in its header exactly when it carries the rules to
build one, the access schedule's positivity together with its agreement with
type admission and a positive refund divisor, and the exclusivity of
proof-of-work numbers with the beacon-root header field. Every other divisor
in the interpreter -- `elasticityMultiplier`, `gasLimitAdjustmentFactor`,
`baseFeeMaxChangeDenominator` -- is a global constant rather than rule data,
so its positivity is a closed fact proved next to it in `Jaune/Machine.lean`
and not a hypothesis anything must carry. -/
def ForkRules.Valid (r : ForkRules) : Prop :=
  r.blob.Valid ∧ 0 < r.modexp.gasDivisor ∧ r.gas.Valid ∧ r.blockAccessListRulesValid
    ∧ r.blockAccessListRules.isSome = r.header.blockAccessListHash
    ∧ r.access.Valid ∧ 0 < r.settlement.refundQuotient
    ∧ (r.access = .eip2929 ↔ 1 ≤ r.transactionRules.maxType)
    ∧ (r.proofOfWork.isSome → r.header.parentBeaconBlockRoot = false)

instance {r : ForkRules} : Decidable r.Valid := by
  unfold ForkRules.Valid; infer_instance

/-- The three projections, named so that a Sufficiency obligation can say which
part of validity it consumes rather than indexing into a conjunction. -/
theorem ForkRules.Valid.blob {r : ForkRules} (h : r.Valid) : r.blob.Valid := h.1

theorem ForkRules.Valid.modexpGasDivisor_pos {r : ForkRules} (h : r.Valid) :
    0 < r.modexp.gasDivisor := h.2.1

theorem ForkRules.Valid.gas {r : ForkRules} (h : r.Valid) : r.gas.Valid := h.2.2.1

theorem ForkRules.Valid.blockAccessListRules {r : ForkRules} (h : r.Valid) : r.blockAccessListRulesValid := h.2.2.2.1

theorem ForkRules.Valid.blockAccessListRules_iff_header {r : ForkRules} (h : r.Valid) :
    r.blockAccessListRules.isSome = r.header.blockAccessListHash := h.2.2.2.2.1

theorem ForkRules.Valid.access {r : ForkRules} (h : r.Valid) :
    r.access.Valid := h.2.2.2.2.2.1

theorem ForkRules.Valid.refundQuotient_pos {r : ForkRules} (h : r.Valid) :
    0 < r.settlement.refundQuotient := h.2.2.2.2.2.2.1

theorem ForkRules.Valid.access_iff_type {r : ForkRules} (h : r.Valid) :
    (r.access = .eip2929 ↔ 1 ≤ r.transactionRules.maxType) := h.2.2.2.2.2.2.2.1

theorem ForkRules.Valid.pow_beacon {r : ForkRules} (h : r.Valid) :
    (r.proofOfWork.isSome → r.header.parentBeaconBlockRoot = false) :=
  h.2.2.2.2.2.2.2.2

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

/-- Prague's opcode set: 0x1E is still an unassigned byte; every pre-Osaka
fork-gated opcode is defined. -/
def pragueOpcodeRules : OpcodeRules :=
  { shifts := true, extCodeHash := true, create2 := true
    chainId := true, selfBalance := true, baseFee := true, push0 := true
    transient := true, mcopy := true, blobHash := true, blobBaseFee := true
    clz := false, slotnum := false, stackAccess := false }

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
  perAuthorizationIntrinsic := 25000
  -- Additive with identity 0: EIP-8038 is not active, so the code-reading
  -- surcharge contributes nothing and the Prague formula is unchanged.
  codeReadSurcharge := 0
}

/-- Prague's header carries neither Amsterdam field, and every pre-Prague
fork-dependent field. -/
def pragueHeaderRules : HeaderRules :=
  { blockAccessListHash := false, slotNumber := false
    baseFee := true, withdrawalsRoot := true, blobGas := true
    parentBeaconBlockRoot := true, requestsHash := true }

/-- Prague's request-producing system contracts, in call order: the EIP-7002
withdrawal contract, then the EIP-7251 consolidation contract.

`Jaune/Machine.lean` states that these are the same two addresses, in the same
order, that its `processGeneralPurposeRequests` fold has always called. -/
def pragueRequests : List (UInt8 × Address) := [
  (1, 0x00000961Ef480Eb55e80D19ad83579A64c007002), -- EIP-7002 withdrawals
  (2, 0x0000BBdDc7CE488642fb579F8B00f3a590007251)  -- EIP-7251 consolidations
]

/-- The precompiles active at Prague: 0x01 through 0x11, contiguous.

Written out rather than computed from a range so that the set stays readable
against the specification's address table and so that later forks extend it by
appending an address, not by widening a bound. -/
def praguePrecompiles : List Address := [
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

--------------- HISTORICAL SUB-RECORDS (BYZANTIUM .. CANCUN) ---------------

-- Each definition below is shared by every fork that carries its value, so a
-- later correction lands once. Fork-specific records point at these; the
-- twelve rule literals point at the fork-specific ones.

/-- Byzantium's opcode set: nothing fork-gated after Byzantium is defined. -/
def byzantiumOpcodeRules : OpcodeRules :=
  { shifts := false, extCodeHash := false, create2 := false
    chainId := false, selfBalance := false, baseFee := false, push0 := false
    transient := false, mcopy := false, blobHash := false, blobBaseFee := false
    clz := false, slotnum := false, stackAccess := false }

/-- Constantinople/Petersburg: EIP-145, EIP-1052, EIP-1014. -/
def petersburgOpcodeRules : OpcodeRules :=
  { byzantiumOpcodeRules with shifts := true, extCodeHash := true, create2 := true }

/-- Istanbul (and Muir Glacier, Berlin): EIP-1344 `CHAINID` and EIP-1884
`SELFBALANCE`. -/
def istanbulOpcodeRules : OpcodeRules :=
  { petersburgOpcodeRules with chainId := true, selfBalance := true }

/-- London (through Paris): EIP-3198 `BASEFEE`. -/
def londonOpcodeRules : OpcodeRules :=
  { istanbulOpcodeRules with baseFee := true }

/-- Shanghai: EIP-3855 `PUSH0`. -/
def shanghaiOpcodeRules : OpcodeRules :=
  { londonOpcodeRules with push0 := true }

/-- Cancun: EIP-1153, EIP-5656, EIP-4844, EIP-7516. -/
def cancunOpcodeRules : OpcodeRules :=
  { shanghaiOpcodeRules with
    transient := true
    mcopy := true
    blobHash := true
    blobBaseFee := true }

/-- A pre-London header: the fifteen original fields only. -/
def preLondonHeaderRules : HeaderRules :=
  { blockAccessListHash := false, slotNumber := false
    baseFee := false, withdrawalsRoot := false, blobGas := false
    parentBeaconBlockRoot := false, requestsHash := false }

/-- London (through Paris): EIP-1559 `baseFeePerGas`. -/
def londonHeaderRules : HeaderRules :=
  { preLondonHeaderRules with baseFee := true }

/-- Shanghai: EIP-4895 `withdrawalsRoot`. -/
def shanghaiHeaderRules : HeaderRules :=
  { londonHeaderRules with withdrawalsRoot := true }

/-- Cancun: EIP-4844 blob-gas fields and EIP-4788 `parentBeaconBlockRoot`. -/
def cancunHeaderRules : HeaderRules :=
  { shanghaiHeaderRules with blobGas := true, parentBeaconBlockRoot := true }

/-- Byzantium/Petersburg flat access prices (EIP-150, EIP-1052). -/
def byzantiumAccessGas : FlatAccessGas :=
  { balance := 400, extCode := 700, extCodeHash := 400, sload := 200,
    call := 700 }

/-- EIP-1884's flat access prices (Istanbul, Muir Glacier). -/
def istanbulAccessGas : FlatAccessGas :=
  { balance := 700, extCode := 700, extCodeHash := 700, sload := 800,
    call := 700 }

/-- The pre-EIP-3529 shared-formula gas numbers: Prague's schedule with the
15000 clearing refund. Every other field is dormant before its first
activation and carries that value (Berlin's access-list prices, Prague's
floor token and authorisation cost), so `GasSchedule.Valid` is unchanged. -/
def byzantiumGasSchedule : GasSchedule :=
  { pragueGasSchedule with storageClearRefund := 15000 }

/-- EIP-198's `MODEXP` (Byzantium .. Muir Glacier): `GQUADDIVISOR = 20`, no
floor, exponent weight 8. `maxLength`/`flatComplexity` are unread before
Osaka; `complexityCoeff` is unread under `.eip198` (U8 owns that shape). -/
def eip198ModexpRules : ModexpRules :=
  { maxLength := none, flatComplexity := none, complexityCoeff := 1
    iterationCoeff := 8, gasDivisor := 20, minGas := 0 }

/-- Cancun's blob schedule (EIP-4844): the target, ceiling and update fraction
are live from Cancun; the reserve price is still absent (EIP-7918, Osaka). -/
def cancunBlobSchedule : BlobSchedule := {
  target := 393216
  max := 786432
  baseFeeUpdateFraction := 3338477
  reserveBaseCost := none
}

/-- The precompiles active at Byzantium through Petersburg: 0x01 .. 0x08
(EIP-198 `MODEXP`, EIP-196/197 alt_bn128; no `BLAKE2F` yet). -/
def byzantiumPrecompiles : List Address := praguePrecompiles.take 8

/-- The precompiles active at Istanbul through Shanghai: 0x01 .. 0x09
(EIP-152 `BLAKE2F` added). -/
def istanbulPrecompiles : List Address := praguePrecompiles.take 9

/-- The precompiles active at Cancun: 0x01 .. 0x0a (EIP-4844
point evaluation added). -/
def cancunPrecompiles : List Address := praguePrecompiles.take 10

/-- Byzantium/Petersburg `SSTORE`: plain SET/UPDATE, no net metering. -/
def byzantiumSstore : SstoreRules := { netMetering := false, stipendSentry := false }

/-- Constantinople's rule set: EIP-1283 net metering without the stipend
sentry. Fixture-grounded only: the pinned EELS `constantinople` module is
already the plain Petersburg `SSTORE`, so no EELS differential exercises this
record; the legacy corpus carries it under the `Constantinople` network label. -/
def constantinopleSstore : SstoreRules := { netMetering := true, stipendSentry := false }

/-- Istanbul onwards: EIP-2200 net metering with the stipend sentry. -/
def istanbulSstore : SstoreRules := { netMetering := true, stipendSentry := true }

/-- Settlement before EIP-3529 (London): halved refunds, 24000 selfdestruct
refund, EIP-161 sweep, and no erase on modification (the sweep does it). -/
def byzantiumSettlement : SettlementRules :=
  { refundQuotient := 2, selfdestructRefund := 24000,
    selfdestructOnlyCreated := false, touchedSweep := true,
    eraseEmptyOnModify := false }

/-- London (through Gray Glacier): EIP-3529 fifths, no selfdestruct refund. -/
def londonSettlement : SettlementRules :=
  { refundQuotient := 5, selfdestructRefund := 0,
    selfdestructOnlyCreated := false, touchedSweep := true,
    eraseEmptyOnModify := false }

/-- Paris (through Shanghai): the touched sweep is gone, and `modify_state`
erases an account it empties at once. -/
def parisSettlement : SettlementRules :=
  { refundQuotient := 5, selfdestructRefund := 0,
    selfdestructOnlyCreated := false, touchedSweep := false,
    eraseEmptyOnModify := true }

/-- Cancun onwards: EIP-6780 same-transaction-only selfdestruct. -/
def cancunSettlement : SettlementRules :=
  { refundQuotient := 5, selfdestructRefund := 0,
    selfdestructOnlyCreated := true, touchedSweep := false,
    eraseEmptyOnModify := true }

/-- Byzantium through Petersburg admission: no typed transactions, 68-gas
nonzero bytes. -/
def byzantiumTransactionRules : TransactionRules :=
  { maxType := 0, dataNonZero := 68, calldataFloor := false,
    warmCoinbase := false }

/-- Istanbul (through Berlin's eve): EIP-2028 reprices nonzero bytes to 16. -/
def istanbulTransactionRules : TransactionRules :=
  { maxType := 0, dataNonZero := 16, calldataFloor := false,
    warmCoinbase := false }

/-- Berlin: EIP-2930 type-1 admission. -/
def berlinTransactionRules : TransactionRules :=
  { istanbulTransactionRules with maxType := 1 }

/-- London (through Shanghai's eve): EIP-1559 type-2 admission. -/
def londonTransactionRules : TransactionRules :=
  { istanbulTransactionRules with maxType := 2 }

/-- Shanghai: EIP-3651 warms the coinbase. -/
def shanghaiTransactionRules : TransactionRules :=
  { londonTransactionRules with warmCoinbase := true }

/-- Cancun: EIP-4844 type-3 admission. -/
def cancunTransactionRules : TransactionRules :=
  { shanghaiTransactionRules with maxType := 3 }

/-- Before London: no init-code limit, no 0xEF rejection. -/
def byzantiumCreation : CreationRules :=
  { initCodeLimit := false, rejectEf := false }

/-- London (through Shanghai's eve): EIP-3541 rejects 0xEF-leading deposits. -/
def londonCreation : CreationRules :=
  { initCodeLimit := false, rejectEf := true }

/-- Shanghai onwards: EIP-3860 bounds and meters initcode. -/
def shanghaiCreation : CreationRules :=
  { initCodeLimit := true, rejectEf := true }

/-- No pre-transaction system calls before Cancun. -/
def byzantiumSystemCalls : SystemCallRules :=
  { beaconRoots := false, historyStorage := false }

/-- Cancun: EIP-4788 beacon-roots call. -/
def cancunSystemCalls : SystemCallRules :=
  { beaconRoots := true, historyStorage := false }

/-- alt_bn128 prices before EIP-1108 (Istanbul). -/
def byzantiumBn254Gas : Bn254Gas :=
  { add := 500, mul := 40000, pairingBase := 100000, pairingPerPair := 80000 }

/-- alt_bn128 prices from EIP-1108 (Istanbul) on. -/
def istanbulBn254Gas : Bn254Gas :=
  { add := 150, mul := 6000, pairingBase := 45000, pairingPerPair := 34000 }

/-- The Prague projection of the extension: every new switch at its Prague
value. The five existing literals carry exactly these fields. -/
def pragueAccess : AccessSchedule := .eip2929
def pragueSstore : SstoreRules := istanbulSstore
def pragueSettlement : SettlementRules := cancunSettlement
def pragueTransactionRules : TransactionRules :=
  { maxType := 4, dataNonZero := 16, calldataFloor := true, warmCoinbase := true }
def pragueCreation : CreationRules := shanghaiCreation
def pragueSystemCalls : SystemCallRules := { beaconRoots := true, historyStorage := true }
def pragueBn254 : Bn254Gas := istanbulBn254Gas

/-- The Prague rule set. -/
def pragueRules : ForkRules := {
  fork := .prague
  blob := pragueBlobSchedule
  code := pragueCodeLimits
  tx := pragueTransactionLimits
  block := pragueBlockLimits
  modexp := pragueModexpRules
  opcodes := pragueOpcodeRules
  gas := pragueGasSchedule
  -- Prague meters in one dimension, so there is no state-gas record to carry.
  stateGas := none
  header := pragueHeaderRules
  requests := pragueRequests
  -- No header commits to a block-level access list before Amsterdam.
  blockAccessListRules := none
  precompiles := praguePrecompiles
  access := pragueAccess
  sstore := pragueSstore
  settlement := pragueSettlement
  transactionRules := pragueTransactionRules
  creation := pragueCreation
  proofOfWork := none
  systemCalls := pragueSystemCalls
  bn254 := pragueBn254
  modexpComplexity := .eip2565
}

--------------- HISTORICAL RULE LITERALS (BYZANTIUM .. CANCUN) ---------------

-- `istanbulRules` is written out in full; every other historical fork is a
-- record update of its predecessor, so a "bomb-only" or "blob-only" claim
-- holds by construction (the BPO precedent). Byzantium has no predecessor and
-- is written out in full beside Istanbul.

/-- The Byzantium rule set. Fields Byzantium cannot read are dormant and carry
the value they take when they first activate, exactly as `istanbulRules`
below documents. -/
def byzantiumRules : ForkRules := {
  fork := .byzantium
  blob := pragueBlobSchedule
  code := pragueCodeLimits
  tx := pragueTransactionLimits
  block := pragueBlockLimits
  modexp := eip198ModexpRules
  opcodes := byzantiumOpcodeRules
  gas := byzantiumGasSchedule
  stateGas := none
  header := preLondonHeaderRules
  requests := []
  blockAccessListRules := none
  precompiles := byzantiumPrecompiles
  access := .flat byzantiumAccessGas
  sstore := byzantiumSstore
  settlement := byzantiumSettlement
  transactionRules := byzantiumTransactionRules
  creation := byzantiumCreation
  proofOfWork := some { blockReward := 3 * 10 ^ 18, bombDelay := 3000000 }
  systemCalls := byzantiumSystemCalls
  bn254 := byzantiumBn254Gas
  modexpComplexity := .eip198
}

/-- Petersburg: Byzantium with the Constantinople opcode set, the 2 ETH reward
and the 5M bomb delay. A record update, so "opcodes, reward and bomb only" is
a fact of the source. -/
def petersburgRules : ForkRules :=
  { byzantiumRules with
    fork := .petersburg
    opcodes := petersburgOpcodeRules
    proofOfWork := some { blockReward := 2 * 10 ^ 18, bombDelay := 5000000 } }

/-- Constantinople: Petersburg with EIP-1283 net metering. See
`constantinopleSstore`: fixture-grounded only, no EELS differential. -/
def constantinopleRules : ForkRules :=
  { petersburgRules with
    fork := .constantinople
    sstore := constantinopleSstore }

/-- The Istanbul rule set, written out in full.

Fields Istanbul cannot read are *dormant* and carry the value they take when
they first activate (Berlin's access-list prices, Prague's floor token and
authorisation cost), so that `GasSchedule.Valid` is unchanged. The live ones:
`storageClearRefund` (15000 before EIP-3529); `callValue`, `createAccess`,
`txBase`, `codeReadSurcharge` at their Prague values. -/
def istanbulRules : ForkRules := {
  fork := .istanbul
  -- Dormant until Cancun (no blob header field, no type-3 admission, no
  -- blob opcodes); carries Prague's schedule so `BlobSchedule.Valid` holds.
  blob := pragueBlobSchedule
  -- `maxInitCodeSize` dormant until Shanghai (`creation.initCodeLimit`).
  code := pragueCodeLimits
  tx := pragueTransactionLimits
  block := pragueBlockLimits
  modexp := eip198ModexpRules
  opcodes := istanbulOpcodeRules
  gas := byzantiumGasSchedule
  stateGas := none
  header := preLondonHeaderRules
  requests := []
  blockAccessListRules := none
  precompiles := istanbulPrecompiles
  access := .flat istanbulAccessGas
  sstore := istanbulSstore
  settlement := byzantiumSettlement
  transactionRules := istanbulTransactionRules
  creation := byzantiumCreation
  proofOfWork := some { blockReward := 2 * 10 ^ 18, bombDelay := 5000000 }
  systemCalls := byzantiumSystemCalls
  bn254 := istanbulBn254Gas
  modexpComplexity := .eip198
}

/-- Muir Glacier: Istanbul with the bomb delay moved to 9M (EIP-2384). A
record update, so "bomb only" is a fact of the source. -/
def muirGlacierRules : ForkRules :=
  { istanbulRules with
    fork := .muirGlacier
    proofOfWork := some { blockReward := 2 * 10 ^ 18, bombDelay := 9000000 } }

/-- Berlin: EIP-2929 access shape, EIP-2930 type-1 admission, EIP-2565
complexity over Prague's `MODEXP` coefficients. -/
def berlinRules : ForkRules :=
  { muirGlacierRules with
    fork := .berlin
    modexp := pragueModexpRules
    modexpComplexity := .eip2565
    access := .eip2929
    transactionRules := berlinTransactionRules }

/-- London: EIP-1559 (header base fee, type-2 admission), EIP-3529 (fifths, no
selfdestruct refund), EIP-3541 (0xEF rejection), EIP-3198 `BASEFEE`, and the
bomb moved to 9.7M. -/
def londonRules : ForkRules :=
  { berlinRules with
    fork := .london
    opcodes := londonOpcodeRules
    gas := pragueGasSchedule
    header := londonHeaderRules
    settlement := londonSettlement
    transactionRules := londonTransactionRules
    creation := londonCreation
    proofOfWork := some { blockReward := 2 * 10 ^ 18, bombDelay := 9700000 } }

/-- Arrow Glacier: London with the bomb delay moved to 10.7M. -/
def arrowGlacierRules : ForkRules :=
  { londonRules with
    fork := .arrowGlacier
    proofOfWork := some { blockReward := 2 * 10 ^ 18, bombDelay := 10700000 } }

/-- Gray Glacier: Arrow Glacier with the bomb delay moved to 11.4M. -/
def grayGlacierRules : ForkRules :=
  { arrowGlacierRules with
    fork := .grayGlacier
    proofOfWork := some { blockReward := 2 * 10 ^ 18, bombDelay := 11400000 } }

/-- Paris: Gray Glacier without proof of work and without the touched sweep
(EIP-161 gone); `PREVRANDAO` replaces `DIFFICULTY` at the use site (a later
unit). -/
def parisRules : ForkRules :=
  { grayGlacierRules with
    fork := .paris
    settlement := parisSettlement
    proofOfWork := none }

/-- Shanghai: Paris with `PUSH0`, withdrawals, EIP-3651 warm coinbase and
EIP-3860 init-code limits. -/
def shanghaiRules : ForkRules :=
  { parisRules with
    fork := .shanghai
    opcodes := shanghaiOpcodeRules
    header := shanghaiHeaderRules
    transactionRules := shanghaiTransactionRules
    creation := shanghaiCreation }

/-- Cancun: Shanghai with the blob schedule live, blob and beacon header
fields, the Cancun opcode set, type-3 admission, the beacon-roots system call
and EIP-6780 selfdestruct. -/
def cancunRules : ForkRules :=
  { shanghaiRules with
    fork := .cancun
    blob := cancunBlobSchedule
    opcodes := cancunOpcodeRules
    header := cancunHeaderRules
    precompiles := cancunPrecompiles
    settlement := cancunSettlement
    transactionRules := cancunTransactionRules
    systemCalls := cancunSystemCalls }

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

/-- Osaka's opcode set: EIP-7939 assigns `CLZ` to 0x1E; 0x4B and 0xE6–0xE8 are
still unassigned bytes; every pre-Osaka fork-gated opcode stays defined. -/
def osakaOpcodeRules : OpcodeRules :=
  { shifts := true, extCodeHash := true, create2 := true
    chainId := true, selfBalance := true, baseFee := true, push0 := true
    transient := true, mcopy := true, blobHash := true, blobBaseFee := true
    clz := true, slotnum := false, stackAccess := false }

/-- The precompiles active at Osaka: Prague's contiguous block plus EIP-7951's
`P256VERIFY`.

It sits at 0x100 rather than continuing the run, which is exactly why the
activation set is carried as a set: appending one address is the whole rule,
and no bound anywhere has to learn about the gap. -/
def osakaPrecompiles : List Address := praguePrecompiles ++ [
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
  opcodes := osakaOpcodeRules
  -- Osaka moves none of the three new categories: EIP-7939 is an opcode, and
  -- the repricings, the header fields, and the two extra request contracts are
  -- all Amsterdam's. Naming Prague's records rather than repeating them is
  -- what makes that a fact of the source instead of a claim about it.
  gas := pragueGasSchedule
  stateGas := none
  header := pragueHeaderRules
  requests := pragueRequests
  blockAccessListRules := none
  precompiles := osakaPrecompiles
  access := pragueAccess
  sstore := pragueSstore
  settlement := pragueSettlement
  transactionRules := pragueTransactionRules
  creation := pragueCreation
  proofOfWork := none
  systemCalls := pragueSystemCalls
  bn254 := pragueBn254
  modexpComplexity := .eip2565
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
  perAuthorizationIntrinsic := 7816
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

/-- Amsterdam's code size limits (EIP-7954): `MAX_CODE_SIZE = 0x10000` and
`MAX_INIT_CODE_SIZE = 2 * MAX_CODE_SIZE`, read at the deposit check, the
creation-transaction data check, and both `CREATE`-family memory checks
through `rules.code`. -/
def amsterdamCodeLimits : CodeLimits := {
  maxCodeSize := 65536 -- 0x10000
  maxInitCodeSize := 131072 -- 2 * 0x10000
}

/-- Amsterdam's opcode set: Osaka's `CLZ`, plus EIP-7843's `SLOTNUM` and
EIP-8024's `DUPN`/`SWAPN`/`EXCHANGE`; every pre-Osaka fork-gated opcode stays
defined. -/
def amsterdamOpcodeRules : OpcodeRules :=
  { shifts := true, extCodeHash := true, create2 := true
    chainId := true, selfBalance := true, baseFee := true, push0 := true
    transient := true, mcopy := true, blobHash := true, blobBaseFee := true
    clz := true, slotnum := true, stackAccess := true }

/-- Amsterdam's header carries both fork-dependent fields: EIP-7928's
`blockAccessListHash` and EIP-7843's `slotNumber`, and every pre-Prague
fork-dependent field. -/
def amsterdamHeaderRules : HeaderRules :=
  { blockAccessListHash := true, slotNumber := true
    baseFee := true, withdrawalsRoot := true, blobGas := true
    parentBeaconBlockRoot := true, requestsHash := true }

/-- Amsterdam's request-producing system contracts, in call order: Prague's two
followed by EIP-8282's builder deposit (type 3) and builder exit (type 4)
contracts. The order is the pinned `process_general_purpose_requests`'s
source-call order, which the constants gate checks. -/
def amsterdamRequests : List (UInt8 × Address) := pragueRequests ++ [
  (3, 0x0000BFF46984E3725691FA540A8C7589300D8282), -- EIP-8282 builder deposits
  (4, 0x000064D678505AD48F8CCB093BC65613800E8282)  -- EIP-8282 builder exits
]

/-- Amsterdam's block-level access-list rules (EIP-7928):
`GasCosts.BLOCK_ACCESS_LIST_ITEM = 2000`. -/
def amsterdamBlockAccessListRules : BlockAccessListRules := { itemCost := 2000 }

/-- Amsterdam retains the execution cap and adds the EIP-8037 total cap. -/
def amsterdamTransactionLimits : TransactionLimits :=
  { osakaTransactionLimits with maxTotalGas := some (2 ^ 32 - 1) }

/-- The Amsterdam rule set, composed from the sub-records the goals that own
them introduced: goal A's header flags and request list shape, goal B's
shared-formula gas schedule and state-gas dimension, and this goal's
block-level rules -- the access-list item cost, the two opcode flags, the raised
code limits, the total transaction gas cap, the two further request contracts,
and both header fields.

Written as an update of `bpo2Rules` so that every field Amsterdam does *not*
move -- the blob schedule, the block limits, `MODEXP`, the
precompile set -- is BPO2's by construction, and the record-update guards below
state, field by field and as a whole, exactly which fields moved. Nothing here
is inherited by accident: the anonymous-constructor `example` beside those
guards names all thirteen fields positionally, so a `ForkRules` field added
later fails the build until it is classified as moved or inherited. (The
`with`-update guards alone cannot see such a field -- goal C's independent
review, finding F1 -- because an inherited `bpo2Rules.newField` sits on both
sides of both of them.)

This retires goal B's transaction-metering vehicle (`amsterdamMeteringRules`)
and the transition-tool-local resolver that reached it. `Fork.amsterdam.rules?`
answers this record, so `jaune t8n --state.fork Amsterdam`, `jaune --rules
Amsterdam`, and every block-validation entry point resolve Amsterdam the way
they resolve every other fork. -/
def amsterdamRules : ForkRules :=
  { bpo2Rules with
    fork := .amsterdam
    code := amsterdamCodeLimits
    tx := amsterdamTransactionLimits
    opcodes := amsterdamOpcodeRules
    gas := amsterdamGasSchedule
    stateGas := some amsterdamStateGasRules
    header := amsterdamHeaderRules
    requests := amsterdamRequests
    blockAccessListRules := some amsterdamBlockAccessListRules }

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
theorem cancunBlobSchedule_valid : cancunBlobSchedule.Valid := by decide

theorem byzantiumRules_valid : byzantiumRules.Valid := by decide
theorem constantinopleRules_valid : constantinopleRules.Valid := by decide
theorem petersburgRules_valid : petersburgRules.Valid := by decide
theorem istanbulRules_valid : istanbulRules.Valid := by decide
theorem muirGlacierRules_valid : muirGlacierRules.Valid := by decide
theorem berlinRules_valid : berlinRules.Valid := by decide
theorem londonRules_valid : londonRules.Valid := by decide
theorem arrowGlacierRules_valid : arrowGlacierRules.Valid := by decide
theorem grayGlacierRules_valid : grayGlacierRules.Valid := by decide
theorem parisRules_valid : parisRules.Valid := by decide
theorem shanghaiRules_valid : shanghaiRules.Valid := by decide
theorem cancunRules_valid : cancunRules.Valid := by decide

/-- Amsterdam's witness. Amsterdam moves all three of `GasSchedule.Valid`'s
numbers -- `createAccess` *downwards*, from 32,000 to 12,000 -- and the
inequalities still hold; it is also the one fork whose `bal` is `some`, and its
header flag agrees. This `decide` records both facts. -/
theorem amsterdamRules_valid : amsterdamRules.Valid := by decide

theorem amsterdamGasSchedule_valid : amsterdamGasSchedule.Valid := by decide
theorem pragueGasSchedule_valid : pragueGasSchedule.Valid := by decide
theorem byzantiumGasSchedule_valid : byzantiumGasSchedule.Valid := by decide
theorem istanbulAccessGas_valid : istanbulAccessGas.Valid := by decide
theorem byzantiumAccessGas_valid : byzantiumAccessGas.Valid := by decide

/-- Error tag for a fork whose identity is known but whose rules this build
does not implement.

Earlier historical waves produced this error for unresolved pre-Berlin
records. This candidate resolves those records, while the error vocabulary
and renderer remain available for absent rule lookup. Falling back to another
fork's rules would turn a missing implementation into a silent consensus
fault, so there is deliberately no fallback. -/
def unsupportedForkTag : String := "UnsupportedForkError"

/-- The single place where a fork identity becomes rule data.

This is a **total** function: every declared fork names the rule record built
for it, including the pre-Prague forks. The resolving lookups --
`Fork.rules?`, `Fork.rules`, and everything reached through
`ChainConfig.rulesAt` -- retain their fallible interfaces, and this candidate
resolves every declared record. `BenvStat.rules` reads it
directly for the fork the entry point already resolved, so
`Fork.ruleSet_valid` below discharges `ForkRules.Valid` once for every rule
set any machine can carry.

The name is `ruleSet` rather than `rules` because `Fork.rules` is the public
`Except`-returning entry point (below) and keeps its name and type. -/
def Fork.ruleSet : Fork → ForkRules
  | .byzantium => byzantiumRules
  | .constantinople => constantinopleRules
  | .petersburg => petersburgRules
  | .istanbul => istanbulRules
  | .muirGlacier => muirGlacierRules
  | .berlin => berlinRules
  | .london => londonRules
  | .arrowGlacier => arrowGlacierRules
  | .grayGlacier => grayGlacierRules
  | .paris => parisRules
  | .shanghai => shanghaiRules
  | .cancun => cancunRules
  | .prague => pragueRules
  | .osaka => osakaRules
  | .bpo1 => bpo1Rules
  | .bpo2 => bpo2Rules
  | .amsterdam => amsterdamRules

/-- Delegation is disabled on every pre-Prague rule set. -/
theorem Fork.ruleSet_delegationEnabled (f : Fork) :
    f.ruleSet.delegationEnabled = (match f with
      | .prague | .osaka | .bpo1 | .bpo2 | .amsterdam => true
      | _ => false) := by
  cases f <;> rfl

/-- **Rule validity, proved once, for every fork.**

This is the theorem the rest of the tree lives off. Because `BenvStat` carries
a `Fork` and derives its rules through `Fork.ruleSet`, every machine's rule set
is one of these seventeen records, so no statement about a machine needs a
`ForkRules.Valid` premise: `BenvStat.rules_valid`, `Sevm.rules_valid` and
`Evm.rules_valid` in `Jaune/Machine.lean` are one-line corollaries.

`cases f <;> decide` rather than a bare `decide`: the per-constructor form is
what the `*_valid` theorems above already use, and it keeps a failure
pointing at the fork whose record broke rather than at an opaque `∀`. -/
theorem Fork.ruleSet_valid (f : Fork) : f.ruleSet.Valid := by
  cases f <;> decide

/-- The rules a fork selects name that fork back.

`ForkRules.fork` is provenance -- the identity a record was built for -- and
this says the two agree, so a machine indexed by a `Fork` and the record it
reads never disagree about which fork is running. -/
theorem Fork.ruleSet_fork (f : Fork) : f.ruleSet.fork = f := by
  cases f <;> rfl

/-- Rule lookup as an `Option`, kept for its callers and its vocabulary.

Every declared fork in this source candidate resolves to its existing rule
record. The `Option` interface is retained: an absent implementation must not
fall back to another fork's record. Resolver admission here does not establish
fixture conformance. -/
def Fork.rules? : Fork → Option ForkRules
  | .byzantium => some byzantiumRules
  | .constantinople => some constantinopleRules
  | .petersburg => some petersburgRules
  | .istanbul => some istanbulRules
  | .muirGlacier => some muirGlacierRules
  | .berlin => some berlinRules
  | .london => some londonRules
  | .arrowGlacier => some arrowGlacierRules
  | .grayGlacier => some grayGlacierRules
  | .paris => some parisRules
  | .shanghai => some shanghaiRules
  | .cancun => some cancunRules
  | .prague => some pragueRules
  | .osaka => some osakaRules
  | .bpo1 => some bpo1Rules
  | .bpo2 => some bpo2Rules
  | .amsterdam => some amsterdamRules

/-- The declared forks whose rule records this candidate resolves.

Derived from `Fork.rules?` rather than written out, so it cannot drift from
what resolves. `Fork.all` names known identities; this filter names the ones
that resolve. They currently coincide, and the exact inventory below records
that resolver state without claiming conformance. -/
def Fork.supported : List Fork := Fork.all.filter (fun f => f.rules?.isSome)

/-- The declared forks whose rule lookup is absent.

The complement of `Fork.supported` within `Fork.all`, retained for diagnostics
that distinguish a known identity from an available rule record. It is empty
in this candidate; the snapshot below records that lookup boundary. -/
def Fork.unimplemented : List Fork := Fork.all.filter (fun f => f.rules?.isNone)

/-- Every rule set a fork identity resolves to is structurally usable.

This is what makes `ForkRules.Valid` free at the fork-selected entry points:
`stateTransitionAt`, `addBlockToChainAt`, and everything reached through
`ChainConfig.rulesAt` obtain their rules from here, so they carry the witness
without checking for it. Since `Fork.ruleSet` is total this is a corollary of
`Fork.ruleSet_valid`; it is kept under its own name for the callers that hold
an `Option` rather than a `Fork`. -/
theorem Fork.rules?_valid {f : Fork} {r : ForkRules} (h : f.rules? = some r) :
    r.Valid := by
  cases f with
  | byzantium => simp only [Fork.rules?] at h; cases h; exact byzantiumRules_valid
  | constantinople => simp only [Fork.rules?] at h; cases h; exact constantinopleRules_valid
  | petersburg => simp only [Fork.rules?] at h; cases h; exact petersburgRules_valid
  | istanbul => simp only [Fork.rules?] at h; cases h; exact istanbulRules_valid
  | muirGlacier => simp only [Fork.rules?] at h; cases h; exact muirGlacierRules_valid
  | berlin => simp only [Fork.rules?] at h; cases h; exact berlinRules_valid
  | london => simp only [Fork.rules?] at h; cases h; exact londonRules_valid
  | arrowGlacier => simp only [Fork.rules?] at h; cases h; exact arrowGlacierRules_valid
  | grayGlacier => simp only [Fork.rules?] at h; cases h; exact grayGlacierRules_valid
  | paris => simp only [Fork.rules?] at h; cases h; exact parisRules_valid
  | shanghai => simp only [Fork.rules?] at h; cases h; exact shanghaiRules_valid
  | cancun => simp only [Fork.rules?] at h; cases h; exact cancunRules_valid
  | prague => simp only [Fork.rules?] at h; cases h; exact pragueRules_valid
  | osaka => simp only [Fork.rules?] at h; cases h; exact osakaRules_valid
  | bpo1 => simp only [Fork.rules?] at h; cases h; exact bpo1Rules_valid
  | bpo2 => simp only [Fork.rules?] at h; cases h; exact bpo2Rules_valid
  | amsterdam => simp only [Fork.rules?] at h; cases h; exact amsterdamRules_valid

/-- When a fork activates, in the two kinds EELS's `FORK_CRITERIA` uses.

Byzantium through Paris activate at a block number (`ByBlockNumber`; Paris
too, since EELS does not model the terminal total difficulty), Shanghai and
later at a timestamp (`ByTimestamp`). EELS orders every block-number criterion
before every timestamp criterion, and `ChainConfig.validate` requires a
schedule to do the same. -/
inductive ForkCriterion : Type
  /-- Active from this block number on. -/
  | byBlock (number : Nat)
  /-- Active from this timestamp on. -/
  | byTimestamp (timestamp : Nat)
deriving DecidableEq, Repr

namespace ForkCriterion

/-- Whether a block at `number` and `timestamp` has reached the criterion. -/
def reached : ForkCriterion → Nat → Nat → Bool
  | .byBlock n, number, _ => decide (n ≤ number)
  | .byTimestamp t, _, timestamp => decide (t ≤ timestamp)

/-- The criterion's number, of whichever kind. -/
def value : ForkCriterion → Nat
  | .byBlock n => n
  | .byTimestamp t => t

/-- Whether the criterion is a block number. -/
def isBlock : ForkCriterion → Bool
  | .byBlock _ => true
  | .byTimestamp _ => false

/-- How a criterion reads in a message: `block 5` or `5` (a bare timestamp, the
spelling the configured-chain messages have always used). -/
def render : ForkCriterion → String
  | .byBlock n => s!"block {n}"
  | .byTimestamp t => s!"{t}"

end ForkCriterion

/-- A fork's rules become active once a block reaches `criterion`.

The field is `criterion` rather than design §4's `at`, which is a Lean
keyword. -/
structure ForkActivation : Type where
  fork : Fork
  criterion : ForkCriterion
deriving DecidableEq, Repr

/-- A timestamp activation, the only kind before the Byzantium extension. -/
abbrev ForkActivation.atTime (fork : Fork) (timestamp : Nat) : ForkActivation :=
  ⟨fork, .byTimestamp timestamp⟩

/-- A block-number activation. -/
abbrev ForkActivation.atBlock (fork : Fork) (number : Nat) : ForkActivation :=
  ⟨fork, .byBlock number⟩

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

-- P0.7 of the integrity plan replaces text used as a semantic discriminant
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
  /-- EIP-7928's item rule would divide by a zero item cost. -/
  | zeroBlockAccessListItemCost
  /-- The header commits to a block-level access list the rules cannot build,
  or the rules build one no header field is compared against. -/
  | blockAccessListHeaderMismatch (hasRules hasHeaderField : Bool)
  /-- A flat access schedule charges nothing for some family, so a cold access
  at `BALANCE`, `EXTCODE*`, `SLOAD` or a `CALL` need charge nothing. -/
  | zeroFlatAccessPrice (g : FlatAccessGas)
  /-- The settlement refund divisor is zero. -/
  | zeroRefundQuotient
  /-- The access shape and type admission disagree: EIP-2929 pricing without a
  typed transaction, or flat pricing with one. -/
  | accessTypeMismatch (isEip2929 : Bool) (maxType : Nat)
  /-- The rules carry proof-of-work numbers and a parent beacon block root. -/
  | powBeaconRootConflict
deriving DecidableEq, Repr

/-- Why a configuration, or the pairing of a configuration with a snapshot, is
not a usable execution context.

This is the outer channel: none of these is a verdict about a candidate
block. -/
inductive ChainContextError : Type
  /-- The activation schedule names no fork at all. -/
  | emptySchedule
  /-- Two adjacent activations of the same kind do not move strictly forward
  (in time, or in block number). -/
  | nonIncreasingActivations (prev next : ForkActivation)
  /-- A block-number activation follows a timestamp activation: EELS orders
  every block-number criterion first. -/
  | blockAfterTimestamp (prev next : ForkActivation)
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
    s!"{invalidChainConfigTag} : activation \
       {if next.criterion.isBlock then "block numbers" else "timestamps"} \
       must strictly increase, but {next.fork} at {next.criterion.render} \
       does not follow {prev.fork} at {prev.criterion.render}"
  | .blockAfterTimestamp prev next =>
    s!"{invalidChainConfigTag} : block-number activations must precede every \
       timestamp activation, but {next.fork} at {next.criterion.render} \
       follows {prev.fork} at timestamp {prev.criterion.render}"
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
      | .zeroBlockAccessListItemCost => "the block-level access-list item cost is zero"
      | .blockAccessListHeaderMismatch hasRules hasHeaderField =>
        s!"the rules {if hasRules then "carry" else "do not carry"} \
           block-level access-list rules, but the header \
           {if hasHeaderField then "commits" else "does not commit"} to one"
      | .zeroFlatAccessPrice g =>
        s!"a flat access price is zero in {repr g}"
      | .zeroRefundQuotient => "the settlement refund quotient is zero"
      | .accessTypeMismatch true maxType =>
        s!"the rules price EIP-2929 access but admit no typed transaction \
           (maxType {maxType})"
      | .accessTypeMismatch false maxType =>
        s!"the rules price flat access but admit typed transactions \
           (maxType {maxType})"
      | .powBeaconRootConflict =>
        "the rules carry proof-of-work numbers and a parent beacon block root"

/-- Why an input is outside the domain this build implements.

Not a configuration fault and not a block verdict: the configuration may be
exactly right and the block perfectly valid, and this build still cannot say
what executing it means. -/
inductive SupportError : Type
  /-- A declared fork whose rules are not implemented in this build. -/
  | unsupportedFork (fork : Fork)
  /-- A timestamp before the earliest era this configuration supports. -/
  | unsupportedEra (timestamp floor : Nat)
  /-- A block number before the earliest era this configuration supports,
  when that era begins at a block number (mainnet: Byzantium, 4,370,000). -/
  | unsupportedBlockEra (number floor : Nat)
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
  | .unsupportedBlockEra number floor =>
    s!"{unsupportedEraTag} : block {number} precedes the earliest era this \
       configuration supports, which begins at block {floor}"

/-- Rule lookup in the `Except` shape the explicit-fork entry points use.

It delegates to `Fork.rules?` above, with `.unsupportedFork` for an absent
record. Every declared record resolves in this candidate. The CLI, transition
tool and configured lookup share that resolver; their label parsers retain
their respective vocabularies. The name, the type and the
rendered message
are unchanged: the shape is what ten call sites and the CLI's refusal surface
are written against. -/
def Fork.rules (f : Fork) : Except SupportError ForkRules :=
  match f.rules? with
  | some r => .ok r
  | none => .error (.unsupportedFork f)

theorem Fork.rules_valid {f : Fork} {r : ForkRules} (h : f.rules = .ok r) :
    r.Valid := by
  rw [Fork.rules] at h
  cases hr : f.rules? with
  | none => simp [hr] at h
  | some r' => simp [hr] at h; subst h; exact Fork.rules?_valid hr

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

/-- The post-block-list checks of `defect?`: the access shape, the refund
divisor, type admission, and proof-of-work exclusivity, in `Valid` order.
Split out so both `bal`-clean leaves of `defect?` share them. -/
def ForkRules.postBlockAccessListDefect? (r : ForkRules) : Option RuleDefect :=
  match r.access with
  | .flat g =>
    if g.balance = 0 ∨ g.extCode = 0 ∨ g.extCodeHash = 0 ∨ g.sload = 0
        ∨ g.call = 0 then
      some (.zeroFlatAccessPrice g)
    else if r.settlement.refundQuotient = 0 then
      some .zeroRefundQuotient
    else if 1 ≤ r.transactionRules.maxType then
      some (.accessTypeMismatch false r.transactionRules.maxType)
    else
      match r.proofOfWork, r.header.parentBeaconBlockRoot with
      | some _, true => some .powBeaconRootConflict
      | _, _ => none
  | .eip2929 =>
    if r.settlement.refundQuotient = 0 then
      some .zeroRefundQuotient
    else if 1 ≤ r.transactionRules.maxType then
      match r.proofOfWork, r.header.parentBeaconBlockRoot with
      | some _, true => some .powBeaconRootConflict
      | _, _ => none
    else
      some (.accessTypeMismatch true r.transactionRules.maxType)

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
    match r.blockAccessListRules, r.header.blockAccessListHash with
    | some b, true =>
      if b.itemCost = 0 then some .zeroBlockAccessListItemCost else r.postBlockAccessListDefect?
    | some b, false =>
      if b.itemCost = 0 then some .zeroBlockAccessListItemCost
      else some (.blockAccessListHeaderMismatch true false)
    | none, true => some (.blockAccessListHeaderMismatch false true)
    | none, false => r.postBlockAccessListDefect?

/-- `defect?` decides `Valid`: it answers `none` exactly on the valid records,
so the check below neither over- nor under-reports. -/
theorem ForkRules.postBlockAccessListDefect?_eq_none_iff {r : ForkRules} :
    r.postBlockAccessListDefect? = none ↔
      (r.access.Valid ∧ 0 < r.settlement.refundQuotient
        ∧ (r.access = .eip2929 ↔ 1 ≤ r.transactionRules.maxType)
        ∧ (r.proofOfWork.isSome → r.header.parentBeaconBlockRoot = false)) := by
  cases hac : r.access with
  | eip2929 =>
    simp only [ForkRules.postBlockAccessListDefect?, hac, AccessSchedule.Valid]
    cases hpow : r.proofOfWork <;> cases hbeacon : r.header.parentBeaconBlockRoot <;>
      (repeat' split) <;> simp_all <;> omega
  | flat g =>
    simp only [ForkRules.postBlockAccessListDefect?, hac, AccessSchedule.Valid,
      FlatAccessGas.Valid]
    cases hpow : r.proofOfWork <;> cases hbeacon : r.header.parentBeaconBlockRoot <;>
      (repeat' split) <;> simp_all <;> omega

theorem ForkRules.defect?_eq_none_iff {r : ForkRules} :
    r.defect? = none ↔ r.Valid := by
  rw [ForkRules.defect?, ForkRules.Valid, BlobSchedule.Valid, GasSchedule.Valid,
    ForkRules.blockAccessListRulesValid]
  repeat' split
  all_goals simp_all [BlockAccessListRules.Valid, ForkRules.postBlockAccessListDefect?_eq_none_iff]
  -- Two `bal`-clean leaves remain as `tail ↔ early ∧ tail`: the tail is the
  -- helper's conjunction on both sides, and the early numbers are hypotheses.
  all_goals (
    constructor
    · intro h
      simp_all
      omega
    · intro h
      simp_all)

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

/-- A supported fork identity resolves straight to checked rules. -/
def Fork.validRules? (f : Fork) : Option ValidRules :=
  match h : f.rules? with
  | some r => some ⟨r, Fork.rules?_valid h⟩
  | none => none

theorem Fork.validRules?_rules (f : Fork) :
    (f.validRules?.map ValidRules.rules) = f.rules? := by
  rw [Fork.validRules?]; split <;> simp_all

namespace ChainConfig

/-- Every activation after the first must move strictly forward in fork order
and in its criterion, and EELS's order of kinds holds: every block-number
activation precedes every timestamp activation. Equal criteria of one kind
would make the active fork depend on list order, and a non-increasing fork
sequence would describe a chain that goes backwards. A step from a block
number to a timestamp is always forward in its criterion: the two kinds are
not compared with each other. -/
private def validateSteps : List ForkActivation → Except ChainContextError Unit
  | [] => .ok ()
  | [_] => .ok ()
  | prev :: next :: rest => do
    match prev.criterion, next.criterion with
    | .byTimestamp _, .byBlock _ => .error (.blockAfterTimestamp prev next)
    | .byBlock a, .byBlock b =>
      if b ≤ a then .error (.nonIncreasingActivations prev next)
    | .byTimestamp a, .byTimestamp b =>
      if b ≤ a then .error (.nonIncreasingActivations prev next)
    | .byBlock _, .byTimestamp _ => pure ()
    if next.fork.index ≤ prev.fork.index then
      .error (.nonForwardActivations prev next)
    validateSteps (next :: rest)

/-- A schedule is usable when it covers every block unambiguously: it names at
least one fork, and every later activation moves strictly forward in its
criterion and in fork order, block numbers first. There is deliberately no
requirement that the first activation begin at genesis -- a configuration may
support only eras from some later floor onward, and a block before that floor
is `SupportError.unsupportedEra` or `unsupportedBlockEra` (from `forkAt`
below), never `InvalidChainConfigError`. -/
def validate (cfg : ChainConfig) : Except ChainContextError Unit := do
  match cfg.activations with
  | [] => .error .emptySchedule
  | _ :: _ =>
    validateSteps cfg.activations

/-- The last activation a block at `number` and `timestamp` has reached,
without validating the schedule. Callers should prefer `forkAt`. On a valid
schedule the reached activations of each kind are a prefix of that kind's
entries, so the last reached one is EELS's choice: the latest fork whose
`FORK_CRITERIA` the block meets. -/
def forkAt? (cfg : ChainConfig) (number timestamp : Nat) : Option Fork :=
  (cfg.activations.filter (·.criterion.reached number timestamp)).getLast?.map
    ForkActivation.fork

/-- The era error for a block that reaches no activation: the first
activation's criterion is the floor, of whichever kind it is. -/
def eraError (first : ForkCriterion) (number timestamp : Nat) : SupportError :=
  match first with
  | .byBlock floor => .unsupportedBlockEra number floor
  | .byTimestamp floor => .unsupportedEra timestamp floor

/-- The fork active for a block at `number` and `timestamp`, rejecting
schedules that do not determine one and blocks that precede this
configuration's earliest supported era. A block before the first activation is
`SupportError.unsupportedEra` (a timestamp floor) or `unsupportedBlockEra` (a
block-number floor), not an invalid configuration: the schedule is exactly as
usable as any other, this build simply does not implement anything before its
declared floor. -/
def forkAt (cfg : ChainConfig) (number timestamp : Nat) :
    Except RulesLookupError Fork := do
  Except.mapError RulesLookupError.context cfg.validate
  match cfg.forkAt? number timestamp with
  | some f => .ok f
  | none =>
    -- `cfg.validate` above guarantees `cfg.activations` is nonempty, so
    -- `head?` always finds the floor; the fallback is unreachable in practice
    -- but keeps this total without threading a nonemptiness proof through.
    let first := (cfg.activations.head?.map (·.criterion)).getD (.byTimestamp 0)
    .error (.support (eraError first number timestamp))

/-- The rules active for a block at `number` and `timestamp`. Fails if the
schedule is unusable or if the selected fork's rules are not implemented. -/
def rulesAt (cfg : ChainConfig) (number timestamp : Nat) :
    Except RulesLookupError ForkRules := do
  Except.mapError RulesLookupError.support (← cfg.forkAt number timestamp).rules

/-- Every activation is a timestamp activation: the only schedules before the
Byzantium extension, and the ones `forkAtTime`/`rulesAtTime` are for. -/
def TimestampOnly (cfg : ChainConfig) : Prop :=
  ∀ a ∈ cfg.activations, a.criterion.isBlock = false

instance (cfg : ChainConfig) : Decidable cfg.TimestampOnly := by
  unfold ChainConfig.TimestampOnly; infer_instance

/-- The timestamp-only lookup, kept for one release as a wrapper over `forkAt`
for timestamp-only schedules. The block number is read as `0`, which a
timestamp-only schedule never consults (`forkAt_timestampOnly`). -/
def forkAtTime (cfg : ChainConfig) (timestamp : Nat) :
    Except RulesLookupError Fork :=
  cfg.forkAt 0 timestamp

/-- The timestamp-only rule lookup, kept for one release as a wrapper over
`rulesAt` for timestamp-only schedules. -/
def rulesAtTime (cfg : ChainConfig) (timestamp : Nat) :
    Except RulesLookupError ForkRules :=
  cfg.rulesAt 0 timestamp

private theorem filter_reached_timestampOnly {as : List ForkActivation}
    (h : ∀ a ∈ as, a.criterion.isBlock = false) (n n' t : Nat) :
    as.filter (·.criterion.reached n t) = as.filter (·.criterion.reached n' t) := by
  apply List.filter_congr
  intro a ha
  have := h a ha
  cases hc : a.criterion with
  | byBlock _ => rw [hc] at this; cases this
  | byTimestamp _ => rfl

/-- On a timestamp-only schedule the block number is never consulted, so the
wrappers agree with the two-argument lookups at every block number. -/
theorem forkAt_timestampOnly {cfg : ChainConfig} (h : cfg.TimestampOnly)
    (number timestamp : Nat) :
    cfg.forkAt number timestamp = cfg.forkAtTime timestamp := by
  have hq : cfg.forkAt? number timestamp = cfg.forkAt? 0 timestamp := by
    unfold ChainConfig.forkAt?
    rw [filter_reached_timestampOnly h number 0 timestamp]
  have hfirst : ∃ t, (cfg.activations.head?.map (·.criterion)).getD
      (.byTimestamp 0) = .byTimestamp t := by
    cases hh : cfg.activations with
    | nil => exact ⟨0, rfl⟩
    | cons a rest =>
      have ha := h a (by simp [hh])
      cases hc : a.criterion with
      | byBlock _ => rw [hc] at ha; cases ha
      | byTimestamp t => exact ⟨t, by simp [hc]⟩
  obtain ⟨t, ht⟩ := hfirst
  unfold ChainConfig.forkAtTime ChainConfig.forkAt
  simp only [hq, ht, eraError]

theorem rulesAt_timestampOnly {cfg : ChainConfig} (h : cfg.TimestampOnly)
    (number timestamp : Nat) :
    cfg.rulesAt number timestamp = cfg.rulesAtTime timestamp := by
  unfold ChainConfig.rulesAt ChainConfig.rulesAtTime ChainConfig.rulesAt
  rw [forkAt_timestampOnly h number timestamp, forkAtTime]

/-- Every rule set a configured lookup produces is structurally usable, so the
configured entry points carry `ForkRules.Valid` without checking for it. -/
theorem rulesAt_valid {cfg : ChainConfig} {number timestamp : Nat} {r : ForkRules}
    (h : cfg.rulesAt number timestamp = .ok r) : r.Valid := by
  rw [ChainConfig.rulesAt] at h
  cases hf : cfg.forkAt number timestamp with
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
  { chainId := chainId, activations := [.atTime .prague 0] }

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
theorem pragueOnly_rulesAt (chainId : UInt64) (number timestamp : Nat) :
    (pragueOnly chainId).rulesAt number timestamp = .ok pragueRules := rfl

/-- A Prague-only schedule selects Prague at every block. -/
theorem pragueOnly_forkAt (chainId : UInt64) (number timestamp : Nat) :
    (pragueOnly chainId).forkAt number timestamp = .ok .prague := rfl

/-- A Prague-only schedule is timestamp-only. -/
theorem pragueOnly_timestampOnly (chainId : UInt64) :
    (pragueOnly chainId).TimestampOnly := by
  simp [TimestampOnly, pragueOnly, ForkCriterion.isBlock]

end ChainConfig

/-- Mainnet's activation criteria, read from the `FORK_CRITERIA` of the EELS
fork modules at the pinned fixture-release revision: block numbers from
Byzantium through Paris (EELS Paris is `ByBlockNumber`, not the terminal total
difficulty), timestamps from Shanghai on.

They are recorded as named constants, and used only by `mainnetChainConfig`
below, because an activation is a fact about one chain and never a rule:
nothing in `ForkRules` may learn them. -/
def mainnetByzantiumBlock : Nat := 4370000

/-- Mainnet's Constantinople activation, which ran EELS's `constantinople`
module: Petersburg's rules (EIP-1283 never activated on mainnet). -/
def mainnetPetersburgBlock : Nat := 7280000

/-- Mainnet's Istanbul activation. -/
def mainnetIstanbulBlock : Nat := 9069000

/-- Mainnet's Muir Glacier activation. -/
def mainnetMuirGlacierBlock : Nat := 9200000

/-- Mainnet's Berlin activation. -/
def mainnetBerlinBlock : Nat := 12244000

/-- Mainnet's London activation. -/
def mainnetLondonBlock : Nat := 12965000

/-- Mainnet's Arrow Glacier activation. -/
def mainnetArrowGlacierBlock : Nat := 13773000

/-- Mainnet's Gray Glacier activation. -/
def mainnetGrayGlacierBlock : Nat := 15050000

/-- Mainnet's Paris activation, the first proof-of-stake block. -/
def mainnetParisBlock : Nat := 15537394

/-- Mainnet's Shanghai activation, 2023-04-12 22:27:35 UTC. -/
def mainnetShanghaiTimestamp : Nat := 1681338455

/-- Mainnet's Cancun activation, 2024-03-13 13:55:35 UTC. -/
def mainnetCancunTimestamp : Nat := 1710338135

/-- Mainnet's Prague activation, 2025-05-07 10:05:11 UTC. -/
def mainnetPragueTimestamp : Nat := 1746612311

/-- Mainnet's Osaka activation (EIP-7607), 2025-12-03 21:49:11 UTC. -/
def mainnetOsakaTimestamp : Nat := 1764798551

/-- Mainnet's BPO1 activation, 2025-12-09 14:21:11 UTC. -/
def mainnetBpo1Timestamp : Nat := 1765290071

/-- Mainnet's BPO2 activation, 2026-01-07 01:01:11 UTC. -/
def mainnetBpo2Timestamp : Nat := 1767747671

/-- Ethereum mainnet, from Byzantium.

The schedule begins at Byzantium, at its real activation block
`mainnetByzantiumBlock` -- not at genesis. This build implements no
pre-Byzantium era, so a configured mainnet block numbered before that floor
must not silently run under any rules: `ChainConfig.forkAt` reports it as
`SupportError.unsupportedBlockEra` rather than resolving it to a fork. A
scheduled fork still passes through `Fork.rules?`; this candidate resolves
its declared eras to their existing records. Schedule selection alone is not
a conformance claim. -/
def mainnetChainConfig : ChainConfig := {
  chainId := 1
  activations := [
    .atBlock .byzantium mainnetByzantiumBlock,
    .atBlock .petersburg mainnetPetersburgBlock,
    .atBlock .istanbul mainnetIstanbulBlock,
    .atBlock .muirGlacier mainnetMuirGlacierBlock,
    .atBlock .berlin mainnetBerlinBlock,
    .atBlock .london mainnetLondonBlock,
    .atBlock .arrowGlacier mainnetArrowGlacierBlock,
    .atBlock .grayGlacier mainnetGrayGlacierBlock,
    .atBlock .paris mainnetParisBlock,
    .atTime .shanghai mainnetShanghaiTimestamp,
    .atTime .cancun mainnetCancunTimestamp,
    .atTime .prague mainnetPragueTimestamp,
    .atTime .osaka mainnetOsakaTimestamp,
    .atTime .bpo1 mainnetBpo1Timestamp,
    .atTime .bpo2 mainnetBpo2Timestamp
  ]
}

/-- One activation boundary, as named by a fixture `network` label of the form
`<before>To<after>AtTime<n>` (a timestamp activation, Shanghai on) or
`<before>To<after>At<n>` (a block-number activation, the fork-block form of the
legacy corpus: `BerlinToLondonAt5`, `ByzantiumToConstantinopleFixAt5`). The
terminal-total-difficulty form `...AtDiffC0000` is not modelled, because EELS
does not model the terminal total difficulty.

A transition is a *schedule*, not a fork: it is turned into a `ChainConfig` by
`chainConfig` below, and execution then reads rules from the block number and
timestamp exactly as it does on a configured chain. -/
structure ForkTransition : Type where
  /-- The fork active from genesis up to, but excluding, `criterion`. -/
  before : Fork
  /-- The fork active from `criterion` onwards. -/
  after : Fork
  /-- The activation criterion. -/
  criterion : ForkCriterion
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

/-- The `At` suffix of the fork-block form: plain decimal digits, as every
corpus label spells it. -/
private def blockOfString? (s : String) : Option Nat :=
  if s.all Char.isDigit then s.toNat? else none

/-- The canonical label. -/
def toString (t : ForkTransition) : String :=
  match t.criterion with
  | .byTimestamp ts => s!"{t.before}To{t.after}AtTime{timestampToString ts}"
  | .byBlock n => s!"{t.before}To{t.after}At{n}"

instance : ToString ForkTransition := ⟨ForkTransition.toString⟩

/-- The two endpoint labels, both forks this build knows. -/
private def forksOfString? (forkLabels : String) : Option (Fork × Fork) := do
  let ⟨beforeLabel, afterLabel⟩ ← splitPair? "To" forkLabels
  let before ← Fork.ofString? beforeLabel
  let after ← Fork.ofString? afterLabel
  return ⟨before, after⟩

/-- Strict label parsing. Both fork names must be forks this build knows, so a
transition such as `EIP158ToByzantiumAt5` fails here rather than being run
through one of its endpoints. A label containing `AtTime` is the timestamp
form and nothing else; only a label without it is read as the fork-block form,
so `...AtTime15k` can never be misread as a block number. -/
def ofString? (label : String) : Option ForkTransition := do
  if (label.splitOn "AtTime").length > 1 then
    let ⟨forkLabels, timeLabel⟩ ← splitPair? "AtTime" label
    let timestamp ← timestampOfString? timeLabel
    let ⟨before, after⟩ ← forksOfString? forkLabels
    return ⟨before, after, .byTimestamp timestamp⟩
  else
    let ⟨forkLabels, blockLabel⟩ ← splitPair? "At" label
    let number ← blockOfString? blockLabel
    let ⟨before, after⟩ ← forksOfString? forkLabels
    return ⟨before, after, .byBlock number⟩

/-- The schedule a transition label names: the `before` fork from genesis --
block 0 for the fork-block form, timestamp 0 for the timestamp form, as
before -- and the `after` fork from the label's criterion.

Whether it is *usable* is `ChainConfig.validate`'s answer, not this function's:
a label may name an activation at genesis or a backwards step, and those are
rejected where every other unusable schedule is. Exposed independent of any
chain identity: whether a transition names a usable schedule does not depend
on which chain runs it, so a caller that only wants to check the schedule
shape (`Main.lean`'s `--network` validation, before any fixture supplies a
concrete chain ID) needs no placeholder identity to construct one. -/
def activations (t : ForkTransition) : List ForkActivation :=
  match t.criterion with
  | .byTimestamp _ => [.atTime t.before 0, ⟨t.after, t.criterion⟩]
  | .byBlock _ => [.atBlock t.before 0, ⟨t.after, t.criterion⟩]

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

namespace ChainConfig

/-- A chain at one fork from genesis; `pragueOnly` is its Prague instance. -/
def single (chainId : UInt64) (f : Fork) : ChainConfig :=
  { chainId := chainId, activations := [.atTime f 0] }

theorem pragueOnly_eq_single (chainId : UInt64) :
    pragueOnly chainId = single chainId .prague := rfl

theorem single_valid (chainId : UInt64) (f : Fork) : (single chainId f).Valid :=
  valid_iff.mpr rfl

theorem single_forkAt (chainId : UInt64) (f : Fork) (number timestamp : Nat) :
    (single chainId f).forkAt number timestamp = .ok f := rfl

private theorem forkAt_some {cfg : ChainConfig} {number timestamp : Nat} {f : Fork}
    (h : cfg.forkAt number timestamp = .ok f) : cfg.forkAt? number timestamp = some f := by
  unfold ChainConfig.forkAt at h
  cases hv : cfg.validate with
  | error e =>
    simp only [bind, Except.bind, Except.mapError, hv, reduceCtorEq] at h
  | ok u =>
    cases hq : cfg.forkAt? number timestamp with
    | none => simp only [bind, Except.bind, Except.mapError, hv, hq, reduceCtorEq] at h
    | some g =>
      simp only [bind, Except.bind, Except.mapError, hv, hq, Except.ok.injEq] at h
      rw [h]

/-- Hoisted from Blanc, with both schedule coordinates. -/
theorem forkAt_mem {cfg : ChainConfig} {number timestamp : Nat} {f : Fork}
    (h : cfg.forkAt number timestamp = .ok f) : f ∈ cfg.activations.map (·.fork) := by
  have hsome := forkAt_some h
  unfold ChainConfig.forkAt? at hsome
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hsome
  exact List.mem_map.mpr
    ⟨a, List.mem_of_mem_filter (List.mem_of_getLast? ha), rfl⟩

private theorem validateSteps_pairwise {activations : List ForkActivation}
    (h : validateSteps activations = .ok ()) :
    activations.Pairwise (fun a b => a.fork.index < b.fork.index) := by
  induction activations with
  | nil => exact .nil
  | cons a rest ih =>
    cases rest with
    | nil => exact .cons (by intro b hb; cases hb) .nil
    | cons b rest =>
      unfold validateSteps at h
      have hh : a.fork.index < b.fork.index ∧ validateSteps (b :: rest) = .ok () := by
        cases ha : a.criterion <;> cases hb : b.criterion <;>
          simp only [ha, hb, bind, Except.bind, reduceCtorEq] at h <;>
          split_ifs at h <;> exact ⟨by omega, h⟩
      have hp := ih hh.2
      refine List.pairwise_cons.mpr ⟨?_, hp⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact hh.1
      · have hbc := (List.pairwise_cons.mp hp).1 c hc
        omega

private theorem forkAt_pairwise {cfg : ChainConfig} {n t : Nat} {f : Fork}
    (h : cfg.forkAt n t = .ok f) :
    cfg.activations.Pairwise (fun a b => a.fork.index < b.fork.index) := by
  unfold forkAt at h
  cases hv : cfg.validate with
  | error e =>
    simp only [hv, Except.mapError, bind, Except.bind, reduceCtorEq] at h
  | ok u =>
    cases u
    apply validateSteps_pairwise
    unfold validate at hv
    cases ha : cfg.activations with
    | nil => simp only [ha, reduceCtorEq] at hv
    | cons a rest => simpa only [ha] using hv

private theorem index_le_last {activations : List ForkActivation} {a b : ForkActivation}
    (hp : activations.Pairwise (fun a b => a.fork.index < b.fork.index))
    (ha : a ∈ activations) (hb : activations.getLast? = some b) :
    a.fork.index ≤ b.fork.index := by
  obtain ⟨rest, rfl⟩ := List.getLast?_eq_some_iff.mp hb
  rcases List.mem_append.mp ha with ha | ha
  · exact Nat.le_of_lt (hp.rel_of_mem_append ha (by simp only [List.mem_singleton]))
  · rw [List.mem_singleton.mp ha]

private theorem reached_mono (criterion : ForkCriterion) {n n' t t' : Nat}
    (hn : n ≤ n') (ht : t ≤ t') (h : criterion.reached n t = true) :
    criterion.reached n' t' = true := by
  cases criterion <;> simp only [ForkCriterion.reached, decide_eq_true_eq] at h ⊢ <;> omega

/-- Forks only move forward: a later block (in both coordinates) runs a fork no earlier. -/
theorem forkAt_index_mono {cfg : ChainConfig} {n n' t t' : Nat} {f f' : Fork}
    (hn : n ≤ n') (ht : t ≤ t')
    (h : cfg.forkAt n t = .ok f) (h' : cfg.forkAt n' t' = .ok f') :
    f.index ≤ f'.index := by
  obtain ⟨a, ha, hfa⟩ := Option.map_eq_some_iff.mp (forkAt_some h)
  obtain ⟨b, hb, hfb⟩ := Option.map_eq_some_iff.mp (forkAt_some h')
  have ham := List.mem_filter.mp (List.mem_of_getLast? ha)
  have hanew : a ∈ cfg.activations.filter (·.criterion.reached n' t') :=
    List.mem_filter.mpr ⟨ham.1, reached_mono a.criterion hn ht ham.2⟩
  have hp := (forkAt_pairwise h').filter (·.criterion.reached n' t')
  simpa only [hfa, hfb] using index_le_last hp hanew hb

private theorem fork_index_injective : Function.Injective Fork.index := by
  intro a b
  cases a <;> cases b <;> decide

/-- A fork changes only at a scheduled activation of the new fork, reached at the later block
and not at the earlier one. -/
theorem forkAt_change {cfg : ChainConfig} {n n' t t' : Nat} {f f' : Fork}
    (hn : n ≤ n') (ht : t ≤ t')
    (h : cfg.forkAt n t = .ok f) (h' : cfg.forkAt n' t' = .ok f') (hne : f ≠ f') :
    ∃ a ∈ cfg.activations, a.fork = f' ∧
      a.criterion.reached n' t' = true ∧ a.criterion.reached n t = false := by
  obtain ⟨a, ha, hfa⟩ := Option.map_eq_some_iff.mp (forkAt_some h)
  obtain ⟨b, hb, hfb⟩ := Option.map_eq_some_iff.mp (forkAt_some h')
  have hbm := List.mem_filter.mp (List.mem_of_getLast? hb)
  refine ⟨b, hbm.1, hfb, hbm.2, ?_⟩
  cases hold : b.criterion.reached n t with
  | false => rfl
  | true =>
    have hbmem : b ∈ cfg.activations.filter (·.criterion.reached n t) :=
      List.mem_filter.mpr ⟨hbm.1, hold⟩
    have hp := (forkAt_pairwise h).filter (·.criterion.reached n t)
    have hle : f'.index ≤ f.index := by
      simpa only [hfa, hfb] using index_le_last hp hbmem ha
    have hmono := forkAt_index_mono hn ht h h'
    exact False.elim (hne (fork_index_injective (Nat.le_antisymm hmono hle)))

theorem mainnetChainConfig_valid : mainnetChainConfig.Valid := by decide

end ChainConfig

end Jaune
