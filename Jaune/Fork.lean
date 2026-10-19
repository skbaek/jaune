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
implemented: only Berlin through Amsterdam resolve (see `Fork.rules?`), and
the five pre-Berlin forks stay refused. The two names are kept apart because
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
structure TxRules : Type where
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
structure PowRules : Type where
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
structure BalRules : Type where
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
  /-- EIP-7928's block-level access-list rules, or `none` for a fork whose
  header does not commit to one. Independent of `header.blockAccessListHash`
  in type but not in fact: `ForkRules.Valid` ties the two together, because a
  header field with nothing to compare against, or a computed list with no
  header to check it, would each be half a rule. -/
  bal : Option BalRules
  /-- The addresses at which a precompiled contract is active. -/
  precompiles : List Adr
  /-- Access-pricing shape (EIP-2929 switch): flat before Berlin. -/
  access : AccessSchedule
  /-- `SSTORE` shape: plain before Constantinople's rule set, net metering on. -/
  sstore : SstoreRules
  /-- Settlement numbers and switches (refund quotient, selfdestruct, sweep). -/
  settle : SettlementRules
  /-- Admission and intrinsic-cost switches (max type, nonzero price, floor,
  warm coinbase). -/
  txr : TxRules
  /-- Creation switches (init-code limit, 0xEF rejection). -/
  creation : CreationRules
  /-- Proof-of-work consensus numbers, `none` from Paris. -/
  pow : Option PowRules
  /-- The pre-transaction system calls. -/
  sys : SystemCallRules
  /-- alt_bn128 precompile prices. -/
  bn254 : Bn254Gas
  /-- `MODEXP` complexity function. -/
  modexpComplexity : ModexpComplexity
deriving DecidableEq

/-- EIP-7702 code delegation activates with type-4 transaction admission. -/
def ForkRules.delegationEnabled (rules : ForkRules) : Bool :=
  decide (4 ≤ rules.txr.maxType)

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

/-- The block-level access-list rules are usable: `itemCost` is the divisor of
the item rule, so it must be positive. -/
def BalRules.Valid (b : BalRules) : Prop := 0 < b.itemCost

instance {b : BalRules} : Decidable b.Valid := by
  unfold BalRules.Valid; infer_instance

/-- A fork's optional access-list rules are usable: trivially when absent. -/
def ForkRules.balValid (r : ForkRules) : Prop :=
  match r.bal with
  | none => True
  | some b => b.Valid

instance {r : ForkRules} : Decidable r.balValid := by
  unfold ForkRules.balValid; cases r.bal <;> infer_instance

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
  r.blob.Valid ∧ 0 < r.modexp.gasDivisor ∧ r.gas.Valid ∧ r.balValid
    ∧ r.bal.isSome = r.header.blockAccessListHash
    ∧ r.access.Valid ∧ 0 < r.settle.refundQuotient
    ∧ (r.access = .eip2929 ↔ 1 ≤ r.txr.maxType)
    ∧ (r.pow.isSome → r.header.parentBeaconBlockRoot = false)

instance {r : ForkRules} : Decidable r.Valid := by
  unfold ForkRules.Valid; infer_instance

/-- The three projections, named so that a Sufficiency obligation can say which
part of validity it consumes rather than indexing into a conjunction. -/
theorem ForkRules.Valid.blob {r : ForkRules} (h : r.Valid) : r.blob.Valid := h.1

theorem ForkRules.Valid.modexpGasDivisor_pos {r : ForkRules} (h : r.Valid) :
    0 < r.modexp.gasDivisor := h.2.1

theorem ForkRules.Valid.gas {r : ForkRules} (h : r.Valid) : r.gas.Valid := h.2.2.1

theorem ForkRules.Valid.bal {r : ForkRules} (h : r.Valid) : r.balValid := h.2.2.2.1

theorem ForkRules.Valid.bal_iff_header {r : ForkRules} (h : r.Valid) :
    r.bal.isSome = r.header.blockAccessListHash := h.2.2.2.2.1

theorem ForkRules.Valid.access {r : ForkRules} (h : r.Valid) :
    r.access.Valid := h.2.2.2.2.2.1

theorem ForkRules.Valid.refundQuotient_pos {r : ForkRules} (h : r.Valid) :
    0 < r.settle.refundQuotient := h.2.2.2.2.2.2.1

theorem ForkRules.Valid.access_iff_type {r : ForkRules} (h : r.Valid) :
    (r.access = .eip2929 ↔ 1 ≤ r.txr.maxType) := h.2.2.2.2.2.2.2.1

theorem ForkRules.Valid.pow_beacon {r : ForkRules} (h : r.Valid) :
    (r.pow.isSome → r.header.parentBeaconBlockRoot = false) :=
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
  perAuthIntrinsic := 25000
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
def byzantiumPrecompiles : List Adr := praguePrecompiles.take 8

/-- The precompiles active at Istanbul through Shanghai: 0x01 .. 0x09
(EIP-152 `BLAKE2F` added). -/
def istanbulPrecompiles : List Adr := praguePrecompiles.take 9

/-- The precompiles active at Cancun: 0x01 .. 0x0a (EIP-4844
point evaluation added). -/
def cancunPrecompiles : List Adr := praguePrecompiles.take 10

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
def byzantiumSettle : SettlementRules :=
  { refundQuotient := 2, selfdestructRefund := 24000,
    selfdestructOnlyCreated := false, touchedSweep := true,
    eraseEmptyOnModify := false }

/-- London (through Gray Glacier): EIP-3529 fifths, no selfdestruct refund. -/
def londonSettle : SettlementRules :=
  { refundQuotient := 5, selfdestructRefund := 0,
    selfdestructOnlyCreated := false, touchedSweep := true,
    eraseEmptyOnModify := false }

/-- Paris (through Shanghai): the touched sweep is gone, and `modify_state`
erases an account it empties at once. -/
def parisSettle : SettlementRules :=
  { refundQuotient := 5, selfdestructRefund := 0,
    selfdestructOnlyCreated := false, touchedSweep := false,
    eraseEmptyOnModify := true }

/-- Cancun onwards: EIP-6780 same-transaction-only selfdestruct. -/
def cancunSettle : SettlementRules :=
  { refundQuotient := 5, selfdestructRefund := 0,
    selfdestructOnlyCreated := true, touchedSweep := false,
    eraseEmptyOnModify := true }

/-- Byzantium through Petersburg admission: no typed transactions, 68-gas
nonzero bytes. -/
def byzantiumTxr : TxRules :=
  { maxType := 0, dataNonZero := 68, calldataFloor := false,
    warmCoinbase := false }

/-- Istanbul (through Berlin's eve): EIP-2028 reprices nonzero bytes to 16. -/
def istanbulTxr : TxRules :=
  { maxType := 0, dataNonZero := 16, calldataFloor := false,
    warmCoinbase := false }

/-- Berlin: EIP-2930 type-1 admission. -/
def berlinTxr : TxRules :=
  { istanbulTxr with maxType := 1 }

/-- London (through Shanghai's eve): EIP-1559 type-2 admission. -/
def londonTxr : TxRules :=
  { istanbulTxr with maxType := 2 }

/-- Shanghai: EIP-3651 warms the coinbase. -/
def shanghaiTxr : TxRules :=
  { londonTxr with warmCoinbase := true }

/-- Cancun: EIP-4844 type-3 admission. -/
def cancunTxr : TxRules :=
  { shanghaiTxr with maxType := 3 }

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
def byzantiumSys : SystemCallRules :=
  { beaconRoots := false, historyStorage := false }

/-- Cancun: EIP-4788 beacon-roots call. -/
def cancunSys : SystemCallRules :=
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
def pragueSettle : SettlementRules := cancunSettle
def pragueTxr : TxRules :=
  { maxType := 4, dataNonZero := 16, calldataFloor := true, warmCoinbase := true }
def pragueCreation : CreationRules := shanghaiCreation
def pragueSys : SystemCallRules := { beaconRoots := true, historyStorage := true }
def pragueBn254 : Bn254Gas := istanbulBn254Gas

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
  -- No header commits to a block-level access list before Amsterdam.
  bal := none
  precompiles := praguePrecompiles
  access := pragueAccess
  sstore := pragueSstore
  settle := pragueSettle
  txr := pragueTxr
  creation := pragueCreation
  pow := none
  sys := pragueSys
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
  op := byzantiumOpcodeRules
  gas := byzantiumGasSchedule
  stateGas := none
  header := preLondonHeaderRules
  requests := []
  bal := none
  precompiles := byzantiumPrecompiles
  access := .flat byzantiumAccessGas
  sstore := byzantiumSstore
  settle := byzantiumSettle
  txr := byzantiumTxr
  creation := byzantiumCreation
  pow := some { blockReward := 3 * 10 ^ 18, bombDelay := 3000000 }
  sys := byzantiumSys
  bn254 := byzantiumBn254Gas
  modexpComplexity := .eip198
}

/-- Petersburg: Byzantium with the Constantinople opcode set, the 2 ETH reward
and the 5M bomb delay. A record update, so "opcodes, reward and bomb only" is
a fact of the source. -/
def petersburgRules : ForkRules :=
  { byzantiumRules with
    fork := .petersburg
    op := petersburgOpcodeRules
    pow := some { blockReward := 2 * 10 ^ 18, bombDelay := 5000000 } }

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
  op := istanbulOpcodeRules
  gas := byzantiumGasSchedule
  stateGas := none
  header := preLondonHeaderRules
  requests := []
  bal := none
  precompiles := istanbulPrecompiles
  access := .flat istanbulAccessGas
  sstore := istanbulSstore
  settle := byzantiumSettle
  txr := istanbulTxr
  creation := byzantiumCreation
  pow := some { blockReward := 2 * 10 ^ 18, bombDelay := 5000000 }
  sys := byzantiumSys
  bn254 := istanbulBn254Gas
  modexpComplexity := .eip198
}

/-- Muir Glacier: Istanbul with the bomb delay moved to 9M (EIP-2384). A
record update, so "bomb only" is a fact of the source. -/
def muirGlacierRules : ForkRules :=
  { istanbulRules with
    fork := .muirGlacier
    pow := some { blockReward := 2 * 10 ^ 18, bombDelay := 9000000 } }

/-- Berlin: EIP-2929 access shape, EIP-2930 type-1 admission, EIP-2565
complexity over Prague's `MODEXP` coefficients. -/
def berlinRules : ForkRules :=
  { muirGlacierRules with
    fork := .berlin
    modexp := pragueModexpRules
    modexpComplexity := .eip2565
    access := .eip2929
    txr := berlinTxr }

/-- London: EIP-1559 (header base fee, type-2 admission), EIP-3529 (fifths, no
selfdestruct refund), EIP-3541 (0xEF rejection), EIP-3198 `BASEFEE`, and the
bomb moved to 9.7M. -/
def londonRules : ForkRules :=
  { berlinRules with
    fork := .london
    op := londonOpcodeRules
    gas := pragueGasSchedule
    header := londonHeaderRules
    settle := londonSettle
    txr := londonTxr
    creation := londonCreation
    pow := some { blockReward := 2 * 10 ^ 18, bombDelay := 9700000 } }

/-- Arrow Glacier: London with the bomb delay moved to 10.7M. -/
def arrowGlacierRules : ForkRules :=
  { londonRules with
    fork := .arrowGlacier
    pow := some { blockReward := 2 * 10 ^ 18, bombDelay := 10700000 } }

/-- Gray Glacier: Arrow Glacier with the bomb delay moved to 11.4M. -/
def grayGlacierRules : ForkRules :=
  { arrowGlacierRules with
    fork := .grayGlacier
    pow := some { blockReward := 2 * 10 ^ 18, bombDelay := 11400000 } }

/-- Paris: Gray Glacier without proof of work and without the touched sweep
(EIP-161 gone); `PREVRANDAO` replaces `DIFFICULTY` at the use site (a later
unit). -/
def parisRules : ForkRules :=
  { grayGlacierRules with
    fork := .paris
    settle := parisSettle
    pow := none }

/-- Shanghai: Paris with `PUSH0`, withdrawals, EIP-3651 warm coinbase and
EIP-3860 init-code limits. -/
def shanghaiRules : ForkRules :=
  { parisRules with
    fork := .shanghai
    op := shanghaiOpcodeRules
    header := shanghaiHeaderRules
    txr := shanghaiTxr
    creation := shanghaiCreation }

/-- Cancun: Shanghai with the blob schedule live, blob and beacon header
fields, the Cancun opcode set, type-3 admission, the beacon-roots system call
and EIP-6780 selfdestruct. -/
def cancunRules : ForkRules :=
  { shanghaiRules with
    fork := .cancun
    blob := cancunBlobSchedule
    op := cancunOpcodeRules
    header := cancunHeaderRules
    precompiles := cancunPrecompiles
    settle := cancunSettle
    txr := cancunTxr
    sys := cancunSys }

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
  bal := none
  precompiles := osakaPrecompiles
  access := pragueAccess
  sstore := pragueSstore
  settle := pragueSettle
  txr := pragueTxr
  creation := pragueCreation
  pow := none
  sys := pragueSys
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
def amsterdamRequests : List (UInt8 × Adr) := pragueRequests ++ [
  (3, 0x0000BFF46984E3725691FA540A8C7589300D8282), -- EIP-8282 builder deposits
  (4, 0x000064D678505AD48F8CCB093BC65613800E8282)  -- EIP-8282 builder exits
]

/-- Amsterdam's block-level access-list rules (EIP-7928):
`GasCosts.BLOCK_ACCESS_LIST_ITEM = 2000`. -/
def amsterdamBalRules : BalRules := { itemCost := 2000 }

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
    op := amsterdamOpcodeRules
    gas := amsterdamGasSchedule
    stateGas := some amsterdamStateGasRules
    header := amsterdamHeaderRules
    requests := amsterdamRequests
    bal := some amsterdamBalRules }

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

-- The three obligations, and what a schedule that failed one would be refused
-- for. Stated as guards so that the discovery recorded in `GasSchedule.Valid`'s
-- docstring is checked rather than remembered.
#guard ¬ ({ pragueGasSchedule with coldAccountAccess := 99 } : GasSchedule).Valid
#guard ¬ ({ pragueGasSchedule with createAccess := 0 } : GasSchedule).Valid
#guard ¬ ({ pragueGasSchedule with callValue := 2299 } : GasSchedule).Valid
#guard ({ pragueGasSchedule with callValue := 2300 } : GasSchedule).Valid

-- The premises themselves hold for every named schedule by the `*_valid`
-- theorems above; what no theorem states is that `Valid` refuses a schedule
-- that breaks one. A zero divisor and an inverted schedule are both refused.
#guard ¬ ({ pragueBlobSchedule with baseFeeUpdateFraction := 0 } : BlobSchedule).Valid
#guard ¬ ({ pragueBlobSchedule with max := 0 } : BlobSchedule).Valid
#guard ¬ ({ pragueBlobSchedule with
              target := pragueBlobSchedule.max + 1 } : BlobSchedule).Valid
#guard ¬ ({ pragueRules with
              modexp := { pragueModexpRules with gasDivisor := 0 } }
            : ForkRules).Valid

/-- Error tag for a fork whose identity is known but whose rules this build
does not implement.

The five still-refused pre-Berlin forks produce it through `Fork.rules` and
`Fork.rules?`; the guards at the end of this file record each refusal. It is
kept because
`scripts/check-fork-constants.sh` and `scripts/check-cli.sh` assert this exact
refusal text, and because the CLI's declared-versus-runnable distinction is
user-facing vocabulary. Falling back to another fork's rules would turn a missing
implementation into a silent consensus fault, so there is deliberately no
fallback to fall back to. -/
def unsupportedForkTag : String := "UnsupportedForkError"

/-- The single place where a fork identity becomes rule data.

This is a **total** function: every declared fork names the rule record built
for it, including the twelve pre-Prague forks, five of which this build
parses but does not run. The resolving lookups -- `Fork.rules?`,
`Fork.rules`, and everything reached through `ChainConfig.rulesAt` -- are
partial over it and refuse those five (see `Fork.rules?`), while
`BenvStat.rules` reads it
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

/-- Delegation is disabled on every pre-Prague rule set, including refused forks. -/
theorem Fork.ruleSet_delegationEnabled (f : Fork) :
    f.ruleSet.delegationEnabled = (match f with
      | .prague | .osaka | .bpo1 | .bpo2 | .amsterdam => true
      | _ => false) := by
  cases f <;> rfl

/-- **Rule validity, proved once, for every fork.**

This is the theorem the rest of the tree lives off. Because `BenvStat` carries
a `Fork` and derives its rules through `Fork.ruleSet`, every machine's rule set
is one of these twelve records, so no statement about a machine needs a
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

`some` for the twelve forks this build runs, `none` for the five pre-Berlin
forks whose identities it parses but whose rules it does not implement. The
literals stay total under `Fork.ruleSet` beside this lookup, so the rule data
is still reviewed in place; what changed is that no caller resolves a
still-refused fork to them. Falling back to another fork's record would turn a
missing implementation into a silent consensus fault, so there is deliberately
no fallback. -/
def Fork.rules? : Fork → Option ForkRules
  | .byzantium => none
  | .constantinople => none
  | .petersburg => none
  | .istanbul => none
  | .muirGlacier => none
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

/-- The declared forks this build can actually run.

Derived from `Fork.rules?` rather than written out, so it cannot drift from
what resolves. This is the list a message means when it says "supported":
`Fork.all` is what this build *parses*, and these are the labels it will also
execute. The two are different lists -- the five still-refused pre-Berlin
forks parse and are refused -- and the guard below pins the runnable one as it
reads today. -/
def Fork.supported : List Fork := Fork.all.filter (fun f => f.rules?.isSome)

/-- The declared forks whose rules this build does not implement.

The complement of `Fork.supported` within `Fork.all`, for the diagnostics that
have to name exactly which labels parse and are then refused. It is the five
still-refused pre-Berlin forks, and the guard below pins the list as it reads
today. -/
def Fork.unimplemented : List Fork := Fork.all.filter (fun f => f.rules?.isNone)

-- The runnable forks, as they read today: Berlin through Amsterdam. A guard,
-- not a theorem -- a theorem would claim parsing and executing admit the same
-- labels, which they do not while five declared forks stay refused.
#guard Fork.supported = [.berlin, .london, .arrowGlacier, .grayGlacier, .paris,
  .shanghai, .cancun, .prague, .osaka, .bpo1, .bpo2, .amsterdam]

-- The refused forks, as they read today: the five pre-Berlin forks whose
-- rules stay unresolved. A guard, not a theorem, for the same reason as
-- `Fork.supported` above.
#guard Fork.unimplemented = [.byzantium, .constantinople, .petersburg, .istanbul,
  .muirGlacier]

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
  | byzantium => simp [Fork.rules?] at h
  | constantinople => simp [Fork.rules?] at h
  | petersburg => simp [Fork.rules?] at h
  | istanbul => simp [Fork.rules?] at h
  | muirGlacier => simp [Fork.rules?] at h
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
  /-- EIP-7928's item rule would divide by a zero item cost. -/
  | zeroBalItemCost
  /-- The header commits to a block-level access list the rules cannot build,
  or the rules build one no header field is compared against. -/
  | balHeaderMismatch (hasRules hasHeaderField : Bool)
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
      | .zeroBalItemCost => "the block-level access-list item cost is zero"
      | .balHeaderMismatch hasRules hasHeaderField =>
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

-- Golden guards, one representative per constructor. Each pins the exact
-- rendered bytes, so a later step cannot change an externally observed
-- message by accident while migrating a producer.
#guard ChainContextError.render .emptySchedule
  = "InvalidChainConfigError : the activation schedule is empty"
#guard ChainContextError.render (.nonIncreasingActivations (.atTime .prague 5) (.atTime .osaka 5))
  = "InvalidChainConfigError : activation timestamps must strictly increase, \
     but Osaka at 5 does not follow Prague at 5"
#guard ChainContextError.render (.nonForwardActivations (.atTime .osaka 5) (.atTime .prague 9))
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
#guard ChainContextError.render (.invalidForkRules .zeroBalItemCost)
  = "InvalidForkRulesError : the block-level access-list item cost is zero"
#guard ChainContextError.render (.invalidForkRules .zeroRefundQuotient)
  = "InvalidForkRulesError : the settlement refund quotient is zero"
#guard ChainContextError.render (.invalidForkRules .powBeaconRootConflict)
  = "InvalidForkRulesError : the rules carry proof-of-work numbers and a \
     parent beacon block root"
#guard ChainContextError.render (.invalidForkRules (.accessTypeMismatch true 0))
  = "InvalidForkRulesError : the rules price EIP-2929 access but admit no \
     typed transaction (maxType 0)"
#guard ChainContextError.render (.invalidForkRules (.accessTypeMismatch false 2))
  = "InvalidForkRulesError : the rules price flat access but admit typed \
     transactions (maxType 2)"
#guard (ChainContextError.render
    (.invalidForkRules (.zeroFlatAccessPrice byzantiumAccessGas))).startsWith
  "InvalidForkRulesError : a flat access price is zero"
#guard ChainContextError.render (.invalidForkRules (.balHeaderMismatch false true))
  = "InvalidForkRulesError : the rules do not carry block-level access-list \
     rules, but the header commits to one"

/-- Rule lookup in the `Except` shape the explicit-fork entry points use.

It succeeds for the twelve forks this build runs and refuses the five
still-refused pre-Berlin forks with `.unsupportedFork`, through `Fork.rules?`
above -- one resolver for every label, so the CLI, the transition tool, and
the configured lookup all refuse the same labels. The name, the type and the
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
def ForkRules.postBalDefect? (r : ForkRules) : Option RuleDefect :=
  match r.access with
  | .flat g =>
    if g.balance = 0 ∨ g.extCode = 0 ∨ g.extCodeHash = 0 ∨ g.sload = 0
        ∨ g.call = 0 then
      some (.zeroFlatAccessPrice g)
    else if r.settle.refundQuotient = 0 then
      some .zeroRefundQuotient
    else if 1 ≤ r.txr.maxType then
      some (.accessTypeMismatch false r.txr.maxType)
    else
      match r.pow, r.header.parentBeaconBlockRoot with
      | some _, true => some .powBeaconRootConflict
      | _, _ => none
  | .eip2929 =>
    if r.settle.refundQuotient = 0 then
      some .zeroRefundQuotient
    else if 1 ≤ r.txr.maxType then
      match r.pow, r.header.parentBeaconBlockRoot with
      | some _, true => some .powBeaconRootConflict
      | _, _ => none
    else
      some (.accessTypeMismatch true r.txr.maxType)

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
    match r.bal, r.header.blockAccessListHash with
    | some b, true =>
      if b.itemCost = 0 then some .zeroBalItemCost else r.postBalDefect?
    | some b, false =>
      if b.itemCost = 0 then some .zeroBalItemCost
      else some (.balHeaderMismatch true false)
    | none, true => some (.balHeaderMismatch false true)
    | none, false => r.postBalDefect?

/-- `defect?` decides `Valid`: it answers `none` exactly on the valid records,
so the check below neither over- nor under-reports. -/
theorem ForkRules.postBalDefect?_eq_none_iff {r : ForkRules} :
    r.postBalDefect? = none ↔
      (r.access.Valid ∧ 0 < r.settle.refundQuotient
        ∧ (r.access = .eip2929 ↔ 1 ≤ r.txr.maxType)
        ∧ (r.pow.isSome → r.header.parentBeaconBlockRoot = false)) := by
  cases hac : r.access with
  | eip2929 =>
    simp only [ForkRules.postBalDefect?, hac, AccessSchedule.Valid]
    cases hpow : r.pow <;> cases hbeacon : r.header.parentBeaconBlockRoot <;>
      (repeat' split) <;> simp_all <;> omega
  | flat g =>
    simp only [ForkRules.postBalDefect?, hac, AccessSchedule.Valid,
      FlatAccessGas.Valid]
    cases hpow : r.pow <;> cases hbeacon : r.header.parentBeaconBlockRoot <;>
      (repeat' split) <;> simp_all <;> omega

theorem ForkRules.defect?_eq_none_iff {r : ForkRules} :
    r.defect? = none ↔ r.Valid := by
  rw [ForkRules.defect?, ForkRules.Valid, BlobSchedule.Valid, GasSchedule.Valid,
    ForkRules.balValid]
  repeat' split
  all_goals simp_all [BalRules.Valid, ForkRules.postBalDefect?_eq_none_iff]
  -- Two `bal`-clean leaves remain as `tail ↔ early ∧ tail`: the tail is the
  -- helper's conjunction on both sides, and the early numbers are hypotheses.
  all_goals (
    constructor
    · intro h
      simp_all
      omega
    · intro h
      simp_all)

-- Each gas-schedule obligation is refused under its own name, so a failure
-- says which number the semantics cannot use rather than "the record is
-- invalid". The composed Amsterdam record passes all of them.
#guard ForkRules.defect? { pragueRules with
    gas := { pragueGasSchedule with coldAccountAccess := 99 } }
  = some (.accountAccessBelowWarm 99)
#guard ForkRules.defect? { pragueRules with
    gas := { pragueGasSchedule with createAccess := 0 } }
  = some .zeroCreateAccess
#guard ForkRules.defect? { pragueRules with
    gas := { pragueGasSchedule with callValue := 2299 } }
  = some (.callValueBelowStipend 2299)
#guard ForkRules.defect? amsterdamRules = none
-- The two EIP-7928 premises: a zero item cost, and a header/rules disagreement
-- in either direction.
#guard ForkRules.defect? { amsterdamRules with bal := some { itemCost := 0 } }
  = some .zeroBalItemCost
#guard ForkRules.defect? { amsterdamRules with bal := none }
  = some (.balHeaderMismatch false true)
#guard ForkRules.defect? { bpo2Rules with bal := some amsterdamBalRules }
  = some (.balHeaderMismatch true false)
-- Every named rule set is defect-free, including the twelve historical ones.
#guard ForkRules.defect? byzantiumRules = none
#guard ForkRules.defect? constantinopleRules = none
#guard ForkRules.defect? petersburgRules = none
#guard ForkRules.defect? istanbulRules = none
#guard ForkRules.defect? muirGlacierRules = none
#guard ForkRules.defect? berlinRules = none
#guard ForkRules.defect? londonRules = none
#guard ForkRules.defect? arrowGlacierRules = none
#guard ForkRules.defect? grayGlacierRules = none
#guard ForkRules.defect? parisRules = none
#guard ForkRules.defect? shanghaiRules = none
#guard ForkRules.defect? cancunRules = none
-- The validity extension refuses each new bad shape under its own name: an
-- EIP-2929/type-0 mismatch and a zero refund divisor (the two conjuncts the
-- sketch pins), a zero flat price, a flat/type admission mismatch in the
-- other direction, and proof of work beside a beacon root.
#guard ¬ ({ istanbulRules with access := .eip2929 } : ForkRules).Valid
#guard ¬ ({ istanbulRules with
  settle := { istanbulRules.settle with refundQuotient := 0 } }
  : ForkRules).Valid
#guard ¬ ({ istanbulRules with
  access := .flat { istanbulAccessGas with sload := 0 } } : ForkRules).Valid
#guard ¬ ({ cancunRules with
  pow := some { blockReward := 2 * 10 ^ 18, bombDelay := 11400000 } }
  : ForkRules).Valid
#guard ForkRules.defect? { istanbulRules with access := .eip2929 }
  = some (.accessTypeMismatch true 0)
#guard ForkRules.defect? { istanbulRules with
  settle := { istanbulRules.settle with refundQuotient := 0 } }
  = some .zeroRefundQuotient
#guard ForkRules.defect? { istanbulRules with
  access := .flat { istanbulAccessGas with sload := 0 } }
  = some (.zeroFlatAccessPrice { istanbulAccessGas with sload := 0 })
#guard ForkRules.defect? { byzantiumRules with
  txr := { byzantiumTxr with maxType := 1 } }
  = some (.accessTypeMismatch false 1)
#guard ForkRules.defect? { berlinRules with
  txr := { berlinRules.txr with maxType := 0 } }
  = some (.accessTypeMismatch true 0)
#guard ForkRules.defect? { cancunRules with
  pow := some { blockReward := 2 * 10 ^ 18, bombDelay := 11400000 } }
  = some .powBeaconRootConflict

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

-- The check accepts every named rule set and reports the first defect of a
-- record that carries one.
#guard (ValidRules.check pragueRules).toOption.isSome
#guard (ValidRules.check osakaRules).toOption.isSome
#guard (ValidRules.check bpo1Rules).toOption.isSome
#guard (ValidRules.check bpo2Rules).toOption.isSome
#guard (ValidRules.check byzantiumRules).toOption.isSome
#guard (ValidRules.check constantinopleRules).toOption.isSome
#guard (ValidRules.check petersburgRules).toOption.isSome
#guard (ValidRules.check istanbulRules).toOption.isSome
#guard (ValidRules.check muirGlacierRules).toOption.isSome
#guard (ValidRules.check berlinRules).toOption.isSome
#guard (ValidRules.check londonRules).toOption.isSome
#guard (ValidRules.check arrowGlacierRules).toOption.isSome
#guard (ValidRules.check grayGlacierRules).toOption.isSome
#guard (ValidRules.check parisRules).toOption.isSome
#guard (ValidRules.check shanghaiRules).toOption.isSome
#guard (ValidRules.check cancunRules).toOption.isSome
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
scheduled fork is not thereby a runnable one: the five still-refused
pre-Berlin forks are refused at `Fork.rules?`, so `rulesAt` reports a block in
their era as `SupportError.unsupportedFork`. -/
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
  | .support (.unsupportedEra _ _) => true
  | .support (.unsupportedBlockEra _ _) => true
  | _ => false

-- Fork labels round-trip, and nothing else parses.
#guard Fork.all.all (fun f => Fork.ofString? f.toString = some f)
#guard Fork.ofString? "Prague" = some .prague
#guard Fork.ofString? "Osaka" = some .osaka
#guard Fork.ofString? "BPO1" = some .bpo1
#guard Fork.ofString? "BPO2" = some .bpo2
#guard Fork.ofString? "Amsterdam" = some .amsterdam
#guard Fork.ofString? "Byzantium" = some .byzantium
#guard Fork.ofString? "Constantinople" = some .constantinople
#guard Fork.ofString? "Petersburg" = some .petersburg
#guard Fork.ofString? "ConstantinopleFix" = some .petersburg
#guard Fork.ofString? "Istanbul" = some .istanbul
#guard Fork.ofString? "MuirGlacier" = some .muirGlacier
#guard Fork.ofString? "Berlin" = some .berlin
#guard Fork.ofString? "London" = some .london
#guard Fork.ofString? "ArrowGlacier" = some .arrowGlacier
#guard Fork.ofString? "GrayGlacier" = some .grayGlacier
#guard Fork.ofString? "Paris" = some .paris
#guard Fork.ofString? "Merge" = some .paris
#guard Fork.ofString? "Shanghai" = some .shanghai
#guard Fork.ofString? "Cancun" = some .cancun
#guard (Fork.ofString? "prague").isNone
#guard (Fork.ofString? "amsterdam").isNone
#guard (Fork.ofString? "cancun").isNone
#guard (Fork.ofString? "BPO3").isNone
#guard (Fork.ofString? "").isNone
#guard Fork.all.length = 17
#guard Fork.all.map Fork.index = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12,
  13, 14, 15, 16]

-- The declared set and the runnable set are both derived from `Fork.rules?`
-- rather than restated, and they differ by exactly the five still-refused
-- pre-Berlin forks. The runnable and refused lists *as they read today* are
-- guarded where
-- `Fork.supported` and `Fork.unimplemented` are defined above; what is
-- re-guarded here is that the two partition the declared set.
-- (Goal A's guards here asserted `Fork.supported = [.prague, .osaka, .bpo1,
-- .bpo2]`, `Fork.unimplemented = [.amsterdam]` and
-- `Fork.amsterdam.rules? = none`; each is rewritten to the statement that
-- replaced it rather than deleted.)
#guard Fork.supported.length + Fork.unimplemented.length = Fork.all.length
#guard Fork.amsterdam.index = 16
#guard Fork.byzantium.index = 0
#guard Fork.cancun.index = 11
#guard Fork.prague.index = 12
#guard Fork.amsterdam.rules? = some amsterdamRules

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

-- The historical chain, undone predecessor by predecessor: each record is its
-- predecessor with exactly the named fields moved, so no fork along the chain
-- can silently acquire or lose a rule.
#guard { petersburgRules with fork := .byzantium, op := byzantiumRules.op, pow := byzantiumRules.pow } = byzantiumRules
#guard { constantinopleRules with fork := .petersburg, sstore := petersburgRules.sstore } = petersburgRules
#guard { muirGlacierRules with fork := .istanbul, pow := istanbulRules.pow } = istanbulRules
#guard { berlinRules with fork := .muirGlacier, modexp := muirGlacierRules.modexp, modexpComplexity := muirGlacierRules.modexpComplexity, access := muirGlacierRules.access, txr := muirGlacierRules.txr } = muirGlacierRules
#guard { londonRules with fork := .berlin, op := berlinRules.op, gas := berlinRules.gas, header := berlinRules.header, settle := berlinRules.settle, txr := berlinRules.txr, creation := berlinRules.creation, pow := berlinRules.pow } = berlinRules
#guard { arrowGlacierRules with fork := .london, pow := londonRules.pow } = londonRules
#guard { grayGlacierRules with fork := .arrowGlacier, pow := arrowGlacierRules.pow } = arrowGlacierRules
#guard { parisRules with fork := .grayGlacier, settle := grayGlacierRules.settle, pow := grayGlacierRules.pow } = grayGlacierRules
#guard { shanghaiRules with fork := .paris, op := parisRules.op, header := parisRules.header, txr := parisRules.txr, creation := parisRules.creation } = parisRules
#guard { cancunRules with fork := .shanghai, blob := shanghaiRules.blob, op := shanghaiRules.op, header := shanghaiRules.header, precompiles := shanghaiRules.precompiles, settle := shanghaiRules.settle, txr := shanghaiRules.txr, sys := shanghaiRules.sys } = shanghaiRules

-- Each fork's record names it back.
#guard byzantiumRules.fork = .byzantium
#guard constantinopleRules.fork = .constantinople
#guard petersburgRules.fork = .petersburg
#guard istanbulRules.fork = .istanbul
#guard muirGlacierRules.fork = .muirGlacier
#guard berlinRules.fork = .berlin
#guard londonRules.fork = .london
#guard arrowGlacierRules.fork = .arrowGlacier
#guard grayGlacierRules.fork = .grayGlacier
#guard parisRules.fork = .paris
#guard shanghaiRules.fork = .shanghai
#guard cancunRules.fork = .cancun

-- Precompile activation sets grow 8 → 9 → 10 → 17 (+1 at Osaka).
#guard byzantiumRules.precompiles.length = 8
#guard byzantiumPrecompiles = praguePrecompiles.take 8
#guard istanbulRules.precompiles = [0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07,
  0x08, 0x09]
#guard cancunRules.precompiles.length = 10
#guard cancunRules.precompiles.take 9 = istanbulRules.precompiles
#guard parisRules.precompiles = istanbulRules.precompiles

-- Proof of work: 3 ETH at Byzantium, 2 ETH through Gray Glacier, none after.
#guard byzantiumRules.pow.map PowRules.blockReward = some (3 * 10 ^ 18)
#guard petersburgRules.pow.map PowRules.blockReward = some (2 * 10 ^ 18)
#guard istanbulRules.pow.map PowRules.bombDelay = some 5000000
#guard muirGlacierRules.pow.map PowRules.bombDelay = some 9000000
#guard berlinRules.pow.map PowRules.bombDelay = some 9000000
#guard londonRules.pow.map PowRules.bombDelay = some 9700000
#guard arrowGlacierRules.pow.map PowRules.bombDelay = some 10700000
#guard grayGlacierRules.pow.map PowRules.bombDelay = some 11400000
#guard parisRules.pow = none
#guard shanghaiRules.pow = none
#guard cancunRules.pow = none

-- Istanbul's shared-formula numbers, the full literal's live fields.
#guard istanbulRules.gas.storageClearRefund = 15000
#guard istanbulRules.txr.dataNonZero = 16
-- EIP-2200 is the EIP-2929 SSTORE formula with cold surcharge 0 and no-op
-- price `SLOAD = 800`: set 20000, update 5000 - 0, restore refunds
-- 20000 - 800 and 5000 - 0 - 800, as in EELS `istanbul/vm/instructions/storage.py`.
#guard (20000 - 800, 5000 - 0 - 800) = (19200, 4200)

-- Access shape: flat until Muir Glacier, EIP-2929 from Berlin.
#guard byzantiumRules.access = AccessSchedule.flat byzantiumAccessGas
#guard istanbulRules.access = AccessSchedule.flat istanbulAccessGas
#guard muirGlacierRules.access = AccessSchedule.flat istanbulAccessGas
#guard berlinRules.access = .eip2929
#guard cancunRules.access = .eip2929

-- SSTORE shape: plain, EIP-1283, EIP-2200.
#guard byzantiumRules.sstore.netMetering = false
#guard petersburgRules.sstore.netMetering = false
#guard constantinopleRules.sstore =
  { netMetering := true, stipendSentry := false }
#guard istanbulRules.sstore.stipendSentry = true
#guard berlinRules.sstore.stipendSentry = true

-- Settlement: halves then fifths, sweep until Paris, erase-on-modify from
-- Paris, 6780 from Cancun.
#guard byzantiumRules.settle.refundQuotient = 2
#guard byzantiumRules.settle.selfdestructRefund = 24000
#guard londonRules.settle.refundQuotient = 5
#guard londonRules.settle.selfdestructRefund = 0
#guard grayGlacierRules.settle.touchedSweep = true
#guard parisRules.settle.touchedSweep = false
#guard grayGlacierRules.settle.eraseEmptyOnModify = false
#guard parisRules.settle.eraseEmptyOnModify = true
#guard cancunRules.settle.selfdestructOnlyCreated = true
#guard londonRules.settle.selfdestructOnlyCreated = false

-- Admission: maxType 0/1/2/3/4 at Byzantium/Berlin/London/Cancun/Prague.
#guard byzantiumRules.txr.maxType = 0
#guard berlinRules.txr.maxType = 1
#guard londonRules.txr.maxType = 2
#guard cancunRules.txr.maxType = 3
#guard pragueRules.txr.maxType = 4
#guard byzantiumRules.txr.dataNonZero = 68
#guard parisRules.txr.warmCoinbase = false
#guard shanghaiRules.txr.warmCoinbase = true
#guard cancunRules.txr.calldataFloor = false
#guard pragueRules.txr.calldataFloor = true

-- Creation: 0xEF rejection at London, init-code limit at Shanghai.
#guard berlinRules.creation.rejectEf = false
#guard parisRules.creation.rejectEf = true
#guard londonRules.creation.initCodeLimit = false
#guard shanghaiRules.creation.initCodeLimit = true

-- Opcode availability along the chain.
#guard byzantiumRules.op.shifts = false
#guard petersburgRules.op.create2 = true
#guard petersburgRules.op.extCodeHash = true
#guard istanbulRules.op.chainId = true
#guard istanbulRules.op.selfBalance = true
#guard berlinRules.op.baseFee = false
#guard londonRules.op.baseFee = true
#guard parisRules.op.push0 = false
#guard shanghaiRules.op.push0 = true
#guard shanghaiRules.op.transient = false
#guard cancunRules.op.transient = true
#guard cancunRules.op.mcopy = true
#guard cancunRules.op.blobHash = true
#guard cancunRules.op.blobBaseFee = true

-- Header fields along the chain.
#guard berlinRules.header.baseFee = false
#guard londonRules.header.baseFee = true
#guard parisRules.header.withdrawalsRoot = false
#guard shanghaiRules.header.withdrawalsRoot = true
#guard shanghaiRules.header.blobGas = false
#guard cancunRules.header.blobGas = true
#guard cancunRules.header.parentBeaconBlockRoot = true
#guard shanghaiRules.header.parentBeaconBlockRoot = false
#guard cancunRules.header.requestsHash = false
#guard pragueRules.header.requestsHash = true

-- Cancun's blob schedule is live; every earlier fork carries Prague's.
#guard cancunRules.blob = cancunBlobSchedule
#guard cancunBlobSchedule.target = 393216
#guard cancunBlobSchedule.max = 786432
#guard cancunBlobSchedule.baseFeeUpdateFraction = 3338477
#guard cancunBlobSchedule.reserveBaseCost = none
#guard shanghaiRules.blob = pragueBlobSchedule
#guard istanbulRules.blob = pragueBlobSchedule

-- alt_bn128 repricing at Istanbul (EIP-1108).
#guard byzantiumRules.bn254.add = 500
#guard byzantiumRules.bn254.mul = 40000
#guard byzantiumRules.bn254.pairingBase = 100000
#guard byzantiumRules.bn254.pairingPerPair = 80000
#guard istanbulRules.bn254.add = 150
#guard istanbulRules.bn254.mul = 6000
#guard istanbulRules.bn254.pairingBase = 45000
#guard istanbulRules.bn254.pairingPerPair = 34000

-- MODEXP: EIP-198 numbers until Muir Glacier, Prague's from Berlin.
#guard byzantiumRules.modexp.gasDivisor = 20
#guard byzantiumRules.modexp.minGas = 0
#guard berlinRules.modexp.gasDivisor = 3
#guard byzantiumRules.modexpComplexity = .eip198
#guard muirGlacierRules.modexpComplexity = .eip198
#guard berlinRules.modexpComplexity = .eip2565

-- System calls: beacon roots at Cancun, history storage at Prague.
#guard shanghaiRules.sys.beaconRoots = false
#guard cancunRules.sys.beaconRoots = true
#guard cancunRules.sys.historyStorage = false
#guard pragueRules.sys.historyStorage = true

-- No request-producing system contracts before Prague.
#guard byzantiumRules.requests = []
#guard cancunRules.requests = []
#guard pragueRules.requests.length = 2

-- The refund boundary: 15000 through Berlin, 4800 from London.
#guard berlinRules.gas.storageClearRefund = 15000
#guard londonRules.gas.storageClearRefund = 4800

-- F1 (goal D): each earlier fork's record spelled with the anonymous
-- constructor over all thirteen fields, so a field added to `ForkRules` later
-- cannot be inherited by any fork without being named here. The `with`-update
-- guards above compare records that would both carry the new field, so they
-- cannot see it; these can.
example : pragueRules =
    ⟨.prague, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, pragueModexpRules, pragueOpcodeRules, pragueGasSchedule,
     none, pragueHeaderRules, pragueRequests, none, praguePrecompiles,
     pragueAccess, pragueSstore, pragueSettle, pragueTxr, pragueCreation,
     none, pragueSys, pragueBn254, .eip2565⟩ := rfl
example : osakaRules =
    ⟨.osaka, osakaBlobSchedule, pragueCodeLimits, osakaTransactionLimits,
     osakaBlockLimits, osakaModexpRules, osakaOpcodeRules, pragueGasSchedule,
     none, pragueHeaderRules, pragueRequests, none, osakaPrecompiles,
     pragueAccess, pragueSstore, pragueSettle, pragueTxr, pragueCreation,
     none, pragueSys, pragueBn254, .eip2565⟩ := rfl
example : bpo1Rules =
    ⟨.bpo1, bpo1BlobSchedule, pragueCodeLimits, osakaTransactionLimits,
     osakaBlockLimits, osakaModexpRules, osakaOpcodeRules, pragueGasSchedule,
     none, pragueHeaderRules, pragueRequests, none, osakaPrecompiles,
     pragueAccess, pragueSstore, pragueSettle, pragueTxr, pragueCreation,
     none, pragueSys, pragueBn254, .eip2565⟩ := rfl
example : bpo2Rules =
    ⟨.bpo2, bpo2BlobSchedule, pragueCodeLimits, osakaTransactionLimits,
     osakaBlockLimits, osakaModexpRules, osakaOpcodeRules, pragueGasSchedule,
     none, pragueHeaderRules, pragueRequests, none, osakaPrecompiles,
     pragueAccess, pragueSstore, pragueSettle, pragueTxr, pragueCreation,
     none, pragueSys, pragueBn254, .eip2565⟩ := rfl
-- F1 for the twelve historical forks: the whole record, so a field added to
-- `ForkRules` later cannot be inherited by any of them without being named.
example : byzantiumRules =
    ⟨.byzantium, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, eip198ModexpRules, byzantiumOpcodeRules,
     byzantiumGasSchedule, none, preLondonHeaderRules, [], none,
     byzantiumPrecompiles, AccessSchedule.flat byzantiumAccessGas,
     byzantiumSstore, byzantiumSettle, byzantiumTxr, byzantiumCreation,
     some ⟨3 * 10 ^ 18, 3000000⟩, byzantiumSys, byzantiumBn254Gas,
     ModexpComplexity.eip198⟩ := rfl
example : petersburgRules =
    ⟨.petersburg, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, eip198ModexpRules, petersburgOpcodeRules,
     byzantiumGasSchedule, none, preLondonHeaderRules, [], none,
     byzantiumPrecompiles, AccessSchedule.flat byzantiumAccessGas,
     byzantiumSstore, byzantiumSettle, byzantiumTxr, byzantiumCreation,
     some ⟨2 * 10 ^ 18, 5000000⟩, byzantiumSys, byzantiumBn254Gas,
     ModexpComplexity.eip198⟩ := rfl
example : constantinopleRules =
    ⟨.constantinople, pragueBlobSchedule, pragueCodeLimits,
     pragueTransactionLimits, pragueBlockLimits, eip198ModexpRules,
     petersburgOpcodeRules, byzantiumGasSchedule, none, preLondonHeaderRules,
     [], none, byzantiumPrecompiles,
     AccessSchedule.flat byzantiumAccessGas, constantinopleSstore,
     byzantiumSettle, byzantiumTxr, byzantiumCreation,
     some ⟨2 * 10 ^ 18, 5000000⟩, byzantiumSys, byzantiumBn254Gas,
     ModexpComplexity.eip198⟩ := rfl
example : istanbulRules =
    ⟨.istanbul, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, eip198ModexpRules, istanbulOpcodeRules,
     byzantiumGasSchedule, none, preLondonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.flat istanbulAccessGas,
     istanbulSstore, byzantiumSettle, istanbulTxr, byzantiumCreation,
     some ⟨2 * 10 ^ 18, 5000000⟩, byzantiumSys, istanbulBn254Gas,
     ModexpComplexity.eip198⟩ := rfl
example : muirGlacierRules =
    ⟨.muirGlacier, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, eip198ModexpRules, istanbulOpcodeRules,
     byzantiumGasSchedule, none, preLondonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.flat istanbulAccessGas,
     istanbulSstore, byzantiumSettle, istanbulTxr, byzantiumCreation,
     some ⟨2 * 10 ^ 18, 9000000⟩, byzantiumSys, istanbulBn254Gas,
     ModexpComplexity.eip198⟩ := rfl
example : berlinRules =
    ⟨.berlin, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, pragueModexpRules, istanbulOpcodeRules,
     byzantiumGasSchedule, none, preLondonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, byzantiumSettle, berlinTxr, byzantiumCreation,
     some ⟨2 * 10 ^ 18, 9000000⟩, byzantiumSys, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl
example : londonRules =
    ⟨.london, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, pragueModexpRules, londonOpcodeRules,
     pragueGasSchedule, none, londonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, londonSettle, londonTxr, londonCreation,
     some ⟨2 * 10 ^ 18, 9700000⟩, byzantiumSys, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl
example : arrowGlacierRules =
    ⟨.arrowGlacier, pragueBlobSchedule, pragueCodeLimits,
     pragueTransactionLimits, pragueBlockLimits, pragueModexpRules,
     londonOpcodeRules, pragueGasSchedule, none, londonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, londonSettle, londonTxr, londonCreation,
     some ⟨2 * 10 ^ 18, 10700000⟩, byzantiumSys, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl
example : grayGlacierRules =
    ⟨.grayGlacier, pragueBlobSchedule, pragueCodeLimits,
     pragueTransactionLimits, pragueBlockLimits, pragueModexpRules,
     londonOpcodeRules, pragueGasSchedule, none, londonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, londonSettle, londonTxr, londonCreation,
     some ⟨2 * 10 ^ 18, 11400000⟩, byzantiumSys, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl
example : parisRules =
    ⟨.paris, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, pragueModexpRules, londonOpcodeRules,
     pragueGasSchedule, none, londonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, parisSettle, londonTxr, londonCreation,
     none, byzantiumSys, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl
example : shanghaiRules =
    ⟨.shanghai, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, pragueModexpRules, shanghaiOpcodeRules,
     pragueGasSchedule, none, shanghaiHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, parisSettle, shanghaiTxr, shanghaiCreation,
     none, byzantiumSys, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl
example : cancunRules =
    ⟨.cancun, cancunBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, pragueModexpRules, cancunOpcodeRules,
     pragueGasSchedule, none, cancunHeaderRules, [], none,
     cancunPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, cancunSettle, cancunTxr, shanghaiCreation,
     none, cancunSys, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl

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

-- Every fork before Amsterdam shares one gas schedule, one header rule, one
-- request list, no state-gas dimension and no block-level access list: the
-- Prague-to-BPO2 chain is Prague's in all five categories. Amsterdam is what
-- makes each of them vary, and it now resolves -- so the guard is stated on
-- the four forks it always described, and its complement is stated next.
-- (Goal A stated the first half over all of `Fork.supported`; Amsterdam
-- resolving is what made that spelling false.)
#guard [Fork.prague, .osaka, .bpo1, .bpo2].all (fun f =>
  match f.rules? with
  | some r => r.gas == pragueGasSchedule && r.header == pragueHeaderRules
      && r.requests == pragueRequests && r.stateGas == none && r.bal == none
  | none => false)
#guard amsterdamRules.gas ≠ pragueGasSchedule
#guard amsterdamRules.header ≠ pragueHeaderRules
#guard amsterdamRules.requests ≠ pragueRequests
#guard amsterdamRules.stateGas ≠ none
#guard amsterdamRules.bal ≠ none

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

-- Amsterdam's numbers, pinned as literals against the composed rule set. This
-- is the only place in the build where they are written down; the constants
-- gate compares each of them against the pinned upstream revision, and the
-- `#guard`s here are what a mutation of one has to get past first.
#guard amsterdamRules.gas.coldAccountAccess = 3000
#guard amsterdamRules.gas.callValue = 11300
#guard amsterdamRules.gas.createAccess = 12000
#guard amsterdamRules.gas.storageClearRefund = 11616
#guard amsterdamRules.gas.txBase = 12000
#guard amsterdamRules.gas.txAccessListAddress = 2900
#guard amsterdamRules.gas.txAccessListStorageKey = 2000
#guard amsterdamRules.gas.floorTokenCost = 16
#guard amsterdamRules.gas.perAuthIntrinsic = 7816
#guard amsterdamRules.gas.codeReadSurcharge = 100

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

-- The composed record is BPO2's with exactly eight fields moved, stated as a
-- record update in both directions so that it cannot silently acquire or lose
-- a rule: undoing all eight must give BPO2 back. The forward guard is the one
-- that bites on a ninth field silently differing from BPO2; the backward one
-- is the definition restated and reduces to `rfl`. Neither sees a field added
-- to `ForkRules` later and inherited from BPO2 (goal C's review, F1) -- that
-- is what the anonymous-constructor `example` after the per-field guards is
-- for: it is the G1 "no silent inheritance" rule made executable.
#guard { amsterdamRules with
  fork := .bpo2, code := pragueCodeLimits, tx := osakaTransactionLimits,
  op := osakaOpcodeRules,
  gas := pragueGasSchedule, stateGas := none, header := pragueHeaderRules,
  requests := pragueRequests, bal := none } = bpo2Rules
#guard { bpo2Rules with
  fork := .amsterdam, code := amsterdamCodeLimits, tx := amsterdamTransactionLimits,
  op := amsterdamOpcodeRules,
  gas := amsterdamGasSchedule, stateGas := some amsterdamStateGasRules,
  header := amsterdamHeaderRules, requests := amsterdamRequests,
  bal := some amsterdamBalRules } = amsterdamRules
-- The moved fields, one guard each, so a failure names the field.
#guard amsterdamRules.fork = .amsterdam
#guard amsterdamRules.code = amsterdamCodeLimits
#guard amsterdamRules.op = amsterdamOpcodeRules
#guard amsterdamRules.gas = amsterdamGasSchedule
#guard amsterdamRules.stateGas = some amsterdamStateGasRules
#guard amsterdamRules.header = amsterdamHeaderRules
#guard amsterdamRules.requests = amsterdamRequests
#guard amsterdamRules.bal = some amsterdamBalRules
-- The inherited fields and the distinct Amsterdam transaction limits.
#guard amsterdamRules.blob = bpo2BlobSchedule
#guard amsterdamRules.tx = amsterdamTransactionLimits
#guard amsterdamRules.tx.maxGas = some (2 ^ 24)
#guard amsterdamRules.tx.maxTotalGas = some (2 ^ 32 - 1)
#guard amsterdamRules.block = osakaBlockLimits
#guard amsterdamRules.modexp = osakaModexpRules
#guard amsterdamRules.precompiles = osakaPrecompiles
-- F1 (goal D, inherited from goal C's independent review): the whole record,
-- spelled with the anonymous constructor over all thirteen `ForkRules` fields
-- in declaration order. Unlike a `with`-update, this cannot inherit a field
-- silently: adding a fourteenth field makes this `example` fail to elaborate
-- until the field is placed here as moved or inherited. Its siblings for
-- Prague, Osaka, BPO1 and BPO2 sit beside their own record guards above.
example : amsterdamRules =
    ⟨.amsterdam, bpo2BlobSchedule, amsterdamCodeLimits, amsterdamTransactionLimits,
     osakaBlockLimits, osakaModexpRules, amsterdamOpcodeRules,
     amsterdamGasSchedule, some amsterdamStateGasRules, amsterdamHeaderRules,
     amsterdamRequests, some amsterdamBalRules, osakaPrecompiles,
     pragueAccess, pragueSstore, pragueSettle, pragueTxr, pragueCreation,
     none, pragueSys, pragueBn254, .eip2565⟩ := rfl

-- The block-level values themselves (EIP-7954, 7843, 8024, 7928, 8282), each
-- of which goal B's vehicle guarded as *absent* (`header.blockAccessListHash =
-- false`, `slotNumber = false`, `requests = pragueRequests`, `code.maxCodeSize =
-- 24576`); each is rewritten here to the value this goal implements.
#guard amsterdamRules.header.blockAccessListHash = true
#guard amsterdamRules.header.slotNumber = true
#guard amsterdamRules.code.maxCodeSize = 65536
#guard amsterdamRules.code.maxCodeSize = 0x10000
#guard amsterdamRules.code.maxInitCodeSize = 131072
#guard amsterdamRules.code.maxInitCodeSize = 2 * amsterdamRules.code.maxCodeSize
#guard amsterdamRules.op.clz = true
#guard amsterdamRules.op.slotnum = true
#guard amsterdamRules.op.stackAccess = true
#guard amsterdamRules.bal = some { itemCost := 2000 }
#guard (amsterdamRules.bal.map BalRules.itemCost) = some 2000
-- The request list: Prague's two calls in Prague's order (goal A's guard,
-- unchanged in meaning), followed by EIP-8282's two in the pinned
-- `process_general_purpose_requests` source-call order.
#guard amsterdamRules.requests.length = 4
#guard amsterdamRules.requests.take 2 = pragueRequests
#guard amsterdamRules.requests.map Prod.fst = [1, 2, 3, 4]
#guard amsterdamRules.requests =
  [(1, (0x00000961Ef480Eb55e80D19ad83579A64c007002 : Adr)),
   (2, (0x0000BBdDc7CE488642fb579F8B00f3a590007251 : Adr)),
   (3, (0x0000BFF46984E3725691FA540A8C7589300D8282 : Adr)),
   (4, (0x000064D678505AD48F8CCB093BC65613800E8282 : Adr))]
-- Only Amsterdam carries a block-level access list, and it is the only fork
-- whose header commits to one: the `Valid` conjunct is checked on all nine.
#guard Fork.supported.all (fun f =>
  match f.rules? with
  | some r => r.bal.isSome == r.header.blockAccessListHash
  | none => false)
#guard ¬ ({ amsterdamRules with bal := none } : ForkRules).Valid
#guard ¬ ({ bpo2Rules with bal := some amsterdamBalRules } : ForkRules).Valid
#guard ¬ ({ amsterdamRules with bal := some { itemCost := 0 } } : ForkRules).Valid

-- And the composed record is reachable through fork identity, which is what
-- makes Amsterdam a supported fork rather than a metering vehicle. (Goal B
-- guarded the negation of each of these three.)
#guard Fork.amsterdam.rules? = some amsterdamRules
#guard Fork.amsterdam.rules?.isSome
#guard Fork.supported.contains .amsterdam

-- The twelve forks this build runs resolve to rules that name them back, and
-- the five still-refused pre-Berlin forks are refused with
-- `UnsupportedForkError` through both lookups. (Goal A guarded here that
-- `Fork.amsterdam.rules = .error (.unsupportedFork .amsterdam)` and that the
-- refusal rendered the `UnsupportedForkError` golden; both were rewritten to
-- the admission that replaced them when Amsterdam resolved, and the twelve
-- rows below are that same refusal in its new place; units U11a/U11b/U11d
-- rewrite the seven rows of Berlin through Cancun to the admission that
-- replaces them.) That `rules?` resolves and names the fork back is
-- `Fork.rules?`'s definition with `Fork.ruleSet_fork`; that the five do not
-- resolve is the rows below, which pin `rules` and `validRules?` fork by
-- fork.
#guard Fork.byzantium.rules = .error (.unsupportedFork .byzantium)
#guard Fork.constantinople.rules = .error (.unsupportedFork .constantinople)
#guard Fork.petersburg.rules = .error (.unsupportedFork .petersburg)
#guard Fork.istanbul.rules = .error (.unsupportedFork .istanbul)
#guard Fork.muirGlacier.rules = .error (.unsupportedFork .muirGlacier)
#guard Fork.berlin.rules = .ok berlinRules
#guard Fork.london.rules = .ok londonRules
#guard Fork.arrowGlacier.rules = .ok arrowGlacierRules
#guard Fork.grayGlacier.rules = .ok grayGlacierRules
#guard Fork.paris.rules = .ok parisRules
#guard Fork.shanghai.rules = .ok shanghaiRules
#guard Fork.cancun.rules = .ok cancunRules
#guard Fork.prague.rules = .ok pragueRules
#guard Fork.osaka.rules = .ok osakaRules
#guard Fork.bpo1.rules = .ok bpo1Rules
#guard Fork.bpo2.rules = .ok bpo2Rules
#guard Fork.amsterdam.rules = .ok amsterdamRules
#guard Fork.byzantium.rules? = none
#guard Fork.constantinople.rules? = none
#guard Fork.petersburg.rules? = none
#guard Fork.istanbul.rules? = none
#guard Fork.muirGlacier.rules? = none
#guard Fork.berlin.rules? = some berlinRules
#guard Fork.london.rules? = some londonRules
#guard Fork.arrowGlacier.rules? = some arrowGlacierRules
#guard Fork.grayGlacier.rules? = some grayGlacierRules
#guard Fork.paris.rules? = some parisRules
#guard Fork.shanghai.rules? = some shanghaiRules
#guard Fork.cancun.rules? = some cancunRules
#guard Fork.amsterdam.validRules?.isSome
#guard Fork.supported.all (fun f => f.validRules?.isSome)
-- The admission a user actually gets, from the live producer, on the exact
-- label the devnet corpus carries: no refusal is rendered.
#guard (match Fork.amsterdam.rules with
  | .error _ => false
  | .ok r => r == amsterdamRules)
-- The renderer's bytes for the constructor are unchanged (the Osaka golden
-- above pins the same text); this guard records that the label Amsterdam no
-- longer reaches it through any lookup rather than that it would read so.
#guard (Fork.all.filter (fun f => f.rules = .error (.unsupportedFork f)))
  = [.byzantium, .constantinople, .petersburg, .istanbul, .muirGlacier]

-- A usable schedule is non-empty and moves strictly forward in both time and
-- fork order. It need not start at genesis: a schedule may support only eras
-- from some later floor onward, and that is a usable schedule, not an invalid
-- one -- `ChainConfig.forkAt` is where a too-early timestamp is refused.
#guard (ChainConfig.pragueOnly 1).validate.toOption.isSome
#guard (ChainConfig.mk 1 []).validate = .error .emptySchedule
#guard (ChainConfig.mk 1 [⟨.prague, .byTimestamp 1⟩]).validate.toOption.isSome
#guard (ChainConfig.mk 1 [⟨.prague, .byTimestamp 0⟩, ⟨.osaka, .byTimestamp 0⟩]).validate
  = .error (.nonIncreasingActivations ⟨.prague, .byTimestamp 0⟩ ⟨.osaka, .byTimestamp 0⟩)
#guard (ChainConfig.mk 1 [⟨.prague, .byTimestamp 0⟩, ⟨.osaka, .byTimestamp 100⟩, ⟨.bpo1, .byTimestamp 100⟩]).validate
  = .error (.nonIncreasingActivations ⟨.osaka, .byTimestamp 100⟩ ⟨.bpo1, .byTimestamp 100⟩)
#guard (ChainConfig.mk 1 [⟨.osaka, .byTimestamp 0⟩, ⟨.prague, .byTimestamp 100⟩]).validate
  = .error (.nonForwardActivations ⟨.osaka, .byTimestamp 0⟩ ⟨.prague, .byTimestamp 100⟩)
#guard (ChainConfig.mk 1 [⟨.prague, .byTimestamp 0⟩, ⟨.osaka, .byTimestamp 100⟩, ⟨.osaka, .byTimestamp 200⟩]).validate
  = .error (.nonForwardActivations ⟨.osaka, .byTimestamp 100⟩ ⟨.osaka, .byTimestamp 200⟩)
#guard (ChainConfig.mk 1 [⟨.prague, .byTimestamp 0⟩, ⟨.osaka, .byTimestamp 100⟩, ⟨.bpo1, .byTimestamp 200⟩,
  ⟨.bpo2, .byTimestamp 300⟩]).validate.toOption.isSome

-- Selection is by the last activation at or before the block timestamp, so the
-- activation block itself already runs the new rules.
private def guardSchedule : ChainConfig :=
  ChainConfig.mk 1 [⟨.prague, .byTimestamp 0⟩, ⟨.osaka, .byTimestamp 100⟩, ⟨.bpo1, .byTimestamp 200⟩, ⟨.bpo2, .byTimestamp 300⟩]

#guard guardSchedule.forkAt 0 0 = .ok .prague
#guard guardSchedule.forkAt 0 99 = .ok .prague
#guard guardSchedule.forkAt 0 100 = .ok .osaka
#guard guardSchedule.forkAt 0 101 = .ok .osaka
#guard guardSchedule.forkAt 0 199 = .ok .osaka
#guard guardSchedule.forkAt 0 200 = .ok .bpo1
#guard guardSchedule.forkAt 0 299 = .ok .bpo1
#guard guardSchedule.forkAt 0 300 = .ok .bpo2
#guard guardSchedule.forkAt 0 1000000 = .ok .bpo2

-- A schedule whose first activation is not at genesis is usable, and a
-- timestamp before its floor is `SupportError.unsupportedEra`, not
-- `InvalidChainConfigError` -- the exact P0.5 boundary, independent of
-- mainnet's own timestamps below. One before the floor fails; the floor
-- itself, and everything after, selects normally.
private def guardFloorSchedule : ChainConfig :=
  ChainConfig.mk 1 [⟨.prague, .byTimestamp 1000⟩, ⟨.osaka, .byTimestamp 2000⟩]

#guard guardFloorSchedule.validate.toOption.isSome
#guard lookupFails isEraL (guardFloorSchedule.forkAt 0 999)
#guard guardFloorSchedule.forkAt 0 999
  = .error (.support (.unsupportedEra 999 1000))
#guard guardFloorSchedule.forkAt 0 1000 = .ok .prague
#guard guardFloorSchedule.forkAt 0 1999 = .ok .prague
#guard guardFloorSchedule.forkAt 0 2000 = .ok .osaka
#guard ¬ lookupFails isContextL (guardFloorSchedule.forkAt 0 999)

-- The whole supported chain is now executable, so every point of the schedule
-- resolves to rules, and each segment resolves to its own.
#guard guardSchedule.rulesAt 0 0 = .ok pragueRules
#guard guardSchedule.rulesAt 0 99 = .ok pragueRules
#guard guardSchedule.rulesAt 0 100 = .ok osakaRules
#guard guardSchedule.rulesAt 0 199 = .ok osakaRules
#guard guardSchedule.rulesAt 0 200 = .ok bpo1Rules
#guard guardSchedule.rulesAt 0 299 = .ok bpo1Rules
#guard guardSchedule.rulesAt 0 300 = .ok bpo2Rules
#guard (ChainConfig.pragueOnly 1).rulesAt 0 0 = .ok pragueRules
#guard (ChainConfig.pragueOnly 1).rulesAt 0 999999 = .ok pragueRules

-- The blob schedule a block runs under is decided by its timestamp alone, and
-- the three BPO-visible numbers change at exactly the two BPO boundaries.
#guard (guardSchedule.rulesAt 0 199).map (ForkRules.blob) = .ok osakaBlobSchedule
#guard (guardSchedule.rulesAt 0 200).map (ForkRules.blob) = .ok bpo1BlobSchedule
#guard (guardSchedule.rulesAt 0 299).map (ForkRules.blob) = .ok bpo1BlobSchedule
#guard (guardSchedule.rulesAt 0 300).map (ForkRules.blob) = .ok bpo2BlobSchedule

-- An invalid schedule fails before any fork is selected, rather than silently
-- resolving to whichever activation happens to sort first.
#guard (ChainConfig.mk 1 []).forkAt 0 0 = .error (.context .emptySchedule)
#guard (ChainConfig.mk 1 []).rulesAt 0 0 = .error (.context .emptySchedule)

-- Mainnet's schedule is usable, and each of its recorded activations is a
-- boundary: the block (or second) before it still runs the old fork. Genesis,
-- and every block before Byzantium's, is outside this build's declared domain
-- -- the P0.5 fix with its floor moved from Prague's timestamp to Byzantium's
-- block (design §4): Jaune implements no pre-Byzantium era and must not
-- silently answer those blocks. A scheduled fork is not a runnable one: the
-- five still-refused pre-Berlin eras resolve to their fork and are then
-- refused at `Fork.rules?`, as `unsupportedFork`, never run under another
-- fork's rules.
#guard mainnetChainConfig.validate.toOption.isSome
#guard mainnetChainConfig.Valid
#guard ¬ (ChainConfig.mk 1 []).Valid
#guard mainnetChainConfig.chainId = 1
#guard ¬ mainnetChainConfig.TimestampOnly
#guard lookupFails isEraL (mainnetChainConfig.forkAt 0 0)
#guard mainnetChainConfig.forkAt (mainnetByzantiumBlock - 1) 0
  = .error (.support (.unsupportedBlockEra (mainnetByzantiumBlock - 1)
      mainnetByzantiumBlock))
#guard mainnetChainConfig.forkAt mainnetByzantiumBlock 0 = .ok .byzantium
#guard mainnetChainConfig.forkAt (mainnetPetersburgBlock - 1) 0 = .ok .byzantium
#guard mainnetChainConfig.forkAt mainnetPetersburgBlock 0 = .ok .petersburg
#guard mainnetChainConfig.forkAt mainnetIstanbulBlock 0 = .ok .istanbul
#guard mainnetChainConfig.forkAt mainnetMuirGlacierBlock 0 = .ok .muirGlacier
#guard mainnetChainConfig.forkAt mainnetBerlinBlock 0 = .ok .berlin
#guard mainnetChainConfig.forkAt mainnetLondonBlock 0 = .ok .london
#guard mainnetChainConfig.forkAt mainnetArrowGlacierBlock 0 = .ok .arrowGlacier
#guard mainnetChainConfig.forkAt mainnetGrayGlacierBlock 0 = .ok .grayGlacier
#guard mainnetChainConfig.forkAt (mainnetParisBlock - 1) 0 = .ok .grayGlacier
#guard mainnetChainConfig.forkAt mainnetParisBlock 0 = .ok .paris
-- Past Paris the timestamp decides: the last Paris second, then Shanghai.
#guard mainnetChainConfig.forkAt mainnetParisBlock (mainnetShanghaiTimestamp - 1)
  = .ok .paris
#guard mainnetChainConfig.forkAt mainnetParisBlock mainnetShanghaiTimestamp
  = .ok .shanghai
#guard mainnetChainConfig.forkAt mainnetParisBlock mainnetCancunTimestamp = .ok .cancun
#guard mainnetChainConfig.forkAt mainnetParisBlock (mainnetPragueTimestamp - 1)
  = .ok .cancun
-- Mainnet block 22,431,084 is the first Prague block.
#guard mainnetChainConfig.forkAt 22431084 mainnetPragueTimestamp = .ok .prague
#guard mainnetChainConfig.forkAt 22431084 (mainnetOsakaTimestamp - 1) = .ok .prague
#guard mainnetChainConfig.forkAt 22431084 mainnetOsakaTimestamp = .ok .osaka
#guard mainnetChainConfig.forkAt 22431084 (mainnetBpo1Timestamp - 1) = .ok .osaka
#guard mainnetChainConfig.forkAt 22431084 mainnetBpo1Timestamp = .ok .bpo1
#guard mainnetChainConfig.forkAt 22431084 (mainnetBpo2Timestamp - 1) = .ok .bpo1
#guard mainnetChainConfig.forkAt 22431084 mainnetBpo2Timestamp = .ok .bpo2
#guard mainnetChainConfig.rulesAt 22431084 mainnetBpo2Timestamp = .ok bpo2Rules
#guard mainnetChainConfig.rulesAt 22431084 mainnetPragueTimestamp = .ok pragueRules
-- Scheduled but refused: a Byzantium-era block is an `unsupportedFork`
-- refusal naming its own fork, not an era error and never Prague's rules. A
-- block of any era from Berlin through Cancun resolves to its own fork's
-- rules (units U11a/U11b/U11d).
#guard mainnetChainConfig.rulesAt mainnetByzantiumBlock 0
  = .error (.support (.unsupportedFork .byzantium))
#guard mainnetChainConfig.rulesAt mainnetParisBlock 0 = .ok parisRules
#guard mainnetChainConfig.rulesAt mainnetBerlinBlock 0 = .ok berlinRules
#guard mainnetChainConfig.rulesAt mainnetGrayGlacierBlock 0 = .ok grayGlacierRules
#guard mainnetChainConfig.rulesAt mainnetParisBlock mainnetShanghaiTimestamp
  = .ok shanghaiRules
#guard mainnetChainConfig.rulesAt mainnetParisBlock mainnetCancunTimestamp
  = .ok cancunRules
-- D13 of the Amsterdam programme: the mainnet schedule names no Amsterdam
-- activation until upstream `FORK_CRITERIA` carries a real Amsterdam
-- timestamp. It names, in order, every fork mainnet ran from Byzantium, with
-- Petersburg (EELS's `constantinople` module) and never EIP-1283's
-- `constantinople`.
#guard mainnetChainConfig.activations.map ForkActivation.fork
  = [.byzantium, .petersburg, .istanbul, .muirGlacier, .berlin, .london,
    .arrowGlacier, .grayGlacier, .paris, .shanghai, .cancun, .prague, .osaka,
    .bpo1, .bpo2]
#guard mainnetChainConfig.activations.length = 15
#guard ¬ (mainnetChainConfig.activations.map ForkActivation.fork).contains
  .amsterdam
#guard ¬ (mainnetChainConfig.activations.map ForkActivation.fork).contains
  .constantinople
#guard (mainnetChainConfig.activations.filter (·.criterion.isBlock)).length = 9

-- The mainnet activations are strictly ordered in the same direction as the
-- fork chain within each kind, which is the fact `validate` enforces and the
-- reason the numbers may not be reordered by a later edit.
#guard mainnetParisBlock < 22431084
#guard mainnetShanghaiTimestamp < mainnetCancunTimestamp
#guard mainnetCancunTimestamp < mainnetPragueTimestamp
#guard mainnetPragueTimestamp < mainnetOsakaTimestamp
#guard mainnetOsakaTimestamp < mainnetBpo1Timestamp
#guard mainnetBpo1Timestamp < mainnetBpo2Timestamp

-- A mixed schedule: block activations first, strictly increasing within each
-- kind. A block activation after a timestamp one is refused, and so is a
-- repeated block number; the step from a block to a timestamp compares
-- nothing across kinds.
#guard (ChainConfig.mk 1 [.atBlock .berlin 0, .atBlock .london 5]).validate = .ok ()
#guard (ChainConfig.mk 1 [.atBlock .paris 100, .atTime .shanghai 0]).validate = .ok ()
#guard (ChainConfig.mk 1 [.atTime .shanghai 0, .atBlock .cancun 5]).validate
  = .error (.blockAfterTimestamp (.atTime .shanghai 0) (.atBlock .cancun 5))
#guard (ChainConfig.mk 1 [.atBlock .berlin 5, .atBlock .london 5]).validate
  = .error (.nonIncreasingActivations (.atBlock .berlin 5) (.atBlock .london 5))
#guard (ChainConfig.mk 1 [.atBlock .london 0, .atBlock .berlin 5]).validate
  = .error (.nonForwardActivations (.atBlock .london 0) (.atBlock .berlin 5))
#guard ((ChainConfig.mk 1 [.atBlock .london 0, .atBlock .berlin 5]).validate
  |>.mapError ChainContextError.render)
  == .error "InvalidChainConfigError : activations must move forward through \
     the fork order, but Berlin does not follow London"
#guard ChainContextError.render
    (.nonIncreasingActivations (.atBlock .berlin 5) (.atBlock .london 5))
  = "InvalidChainConfigError : activation block numbers must strictly \
     increase, but London at block 5 does not follow Berlin at block 5"
#guard ChainContextError.render
    (.blockAfterTimestamp (.atTime .shanghai 0) (.atBlock .cancun 5))
  = "InvalidChainConfigError : block-number activations must precede every \
     timestamp activation, but Cancun at block 5 follows Shanghai at timestamp 0"
#guard SupportError.render (.unsupportedBlockEra 4369999 4370000)
  = "UnsupportedEraError : block 4369999 precedes the earliest era this \
     configuration supports, which begins at block 4370000"
-- The timestamp-only wrappers agree with the two-argument lookup on the
-- timestamp-only schedules they are kept for.
#guard guardSchedule.TimestampOnly
#guard guardSchedule.forkAtTime 150 = guardSchedule.forkAt 99999 150
#guard guardSchedule.rulesAtTime 250 = .ok bpo1Rules

-- Transition labels parse into schedules. Both endpoints must be forks this
-- build knows: a historical transition names one it does not.
#guard ForkTransition.ofString? "PragueToOsakaAtTime15k"
  = some ⟨.prague, .osaka, .byTimestamp 15000⟩
#guard ForkTransition.ofString? "OsakaToBPO1AtTime15k"
  = some ⟨.osaka, .bpo1, .byTimestamp 15000⟩
#guard ForkTransition.ofString? "BPO1ToBPO2AtTime15k"
  = some ⟨.bpo1, .bpo2, .byTimestamp 15000⟩
#guard ForkTransition.ofString? "PragueToOsakaAtTime15000"
  = some ⟨.prague, .osaka, .byTimestamp 15000⟩
#guard ForkTransition.ofString? "BPO2ToAmsterdamAtTime15k"
  = some ⟨.bpo2, .amsterdam, .byTimestamp 15000⟩
#guard ForkTransition.ofString? "CancunToPragueAtTime15k"
  = some ⟨.cancun, .prague, .byTimestamp 15000⟩
#guard (ForkTransition.ofString? "BPO2ToBPO3AtTime15k").isNone
#guard ForkTransition.ofString? "ShanghaiToCancunAtTime15k"
  = some ⟨.shanghai, .cancun, .byTimestamp 15000⟩
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
  ⟨.prague, .osaka, .byTimestamp 15000⟩, ⟨.osaka, .bpo1, .byTimestamp 15000⟩, ⟨.bpo1, .bpo2, .byTimestamp 15000⟩,
  ⟨.prague, .bpo2, .byTimestamp 1⟩, ⟨.osaka, .bpo2, .byTimestamp 1234567⟩
]

#guard guardTransitions.all
  (fun t => ForkTransition.ofString? t.toString = some t)
#guard (⟨.prague, .osaka, .byTimestamp 15000⟩ : ForkTransition).toString
  = "PragueToOsakaAtTime15k"
#guard (⟨.osaka, .bpo1, .byTimestamp 1234567⟩ : ForkTransition).toString
  = "OsakaToBPO1AtTime1234567"

-- The fork-block form (design §4, S3): `<A>To<B>At<n>`, a block-number
-- activation with the `before` fork from block 0. `ConstantinopleFix` is
-- Petersburg, so the canonical spelling of that label names Petersburg and
-- still parses back to the same transition. The TTD form is not modelled, and
-- a label containing `AtTime` is never read as a block number.
#guard ForkTransition.ofString? "BerlinToLondonAt5"
  = some ⟨.berlin, .london, .byBlock 5⟩
#guard ForkTransition.ofString? "ByzantiumToConstantinopleFixAt5"
  = some ⟨.byzantium, .petersburg, .byBlock 5⟩
#guard (⟨.byzantium, .petersburg, .byBlock 5⟩ : ForkTransition).toString
  = "ByzantiumToPetersburgAt5"
#guard (⟨.berlin, .london, .byBlock 5⟩ : ForkTransition).toString
  = "BerlinToLondonAt5"
#guard (ForkTransition.ofString? "ArrowGlacierToParisAtDiffC0000").isNone
#guard (ForkTransition.ofString? "EIP158ToByzantiumAt5").isNone
#guard (ForkTransition.ofString? "BerlinToLondonAt").isNone
#guard (ForkTransition.ofString? "BerlinToLondonAt5k").isNone
#guard (ForkTransition.ofString? "BerlinToLondonAt5At6").isNone
#guard (ForkTransition.ofString? "BerlinToLondonAtTime5At6").isNone
#guard [(⟨.berlin, .london, .byBlock 5⟩ : ForkTransition),
    ⟨.byzantium, .petersburg, .byBlock 5⟩, ⟨.petersburg, .istanbul, .byBlock 1000⟩].all
  (fun t => ForkTransition.ofString? t.toString = some t)
#guard NetworkSpec.ofString? "BerlinToLondonAt5"
  = some (.transition ⟨.berlin, .london, .byBlock 5⟩)
-- Its schedule starts Berlin at block 0 and London at block 5, whatever the
-- timestamp; block 5 itself is the first London block.
private def guardBerlinToLondon : ForkTransition := ⟨.berlin, .london, .byBlock 5⟩
#guard guardBerlinToLondon.activations = [.atBlock .berlin 0, .atBlock .london 5]
#guard (guardBerlinToLondon.chainConfig 1).validate = .ok ()
#guard (guardBerlinToLondon.chainConfig 1).forkAt 0 0 = .ok .berlin
#guard (guardBerlinToLondon.chainConfig 1).forkAt 4 (10 ^ 12) = .ok .berlin
#guard (guardBerlinToLondon.chainConfig 1).forkAt 5 0 = .ok .london
#guard (guardBerlinToLondon.chainConfig 1).forkAt 6 0 = .ok .london
-- Both endpoints resolve at rule lookup (unit U11d).
#guard (guardBerlinToLondon.chainConfig 1).rulesAt 4 0 = .ok berlinRules
#guard (guardBerlinToLondon.chainConfig 1).rulesAt 5 0 = .ok londonRules
-- A fork block at genesis is the unusable schedule it is in the timestamp form.
#guard lookupFails isContextL
  (((⟨.berlin, .london, .byBlock 0⟩ : ForkTransition).chainConfig 1).forkAt 0 0)

-- A transition is a schedule: the `before` fork runs from genesis and the
-- `after` fork from the named timestamp, with no third possibility.
private def guardOsakaToBpo1 : ForkTransition := ⟨.osaka, .bpo1, .byTimestamp 15000⟩

#guard (guardOsakaToBpo1.chainConfig 1).validate.toOption.isSome
#guard (guardOsakaToBpo1.chainConfig 1).rulesAt 0 0 = .ok osakaRules
#guard (guardOsakaToBpo1.chainConfig 1).rulesAt 0 14999 = .ok osakaRules
#guard (guardOsakaToBpo1.chainConfig 1).rulesAt 0 15000 = .ok bpo1Rules
#guard (guardOsakaToBpo1.chainConfig 1).rulesAt 0 15001 = .ok bpo1Rules
#guard (guardOsakaToBpo1.chainConfig 7).chainId = 7

-- The devnet corpus's transition label. Its schedule is usable -- both
-- endpoints are declared and the pair moves forward -- and Amsterdam's rules
-- take effect exactly at the activation timestamp. Everything before it still
-- runs BPO2's rules, which is what makes a transition fixture's pre-fork
-- blocks meaningful rather than skipped. (Goal A guarded that `rulesAt 15000`
-- was the support refusal naming Amsterdam; rewritten to the resolution.)
private def guardBpo2ToAmsterdam : ForkTransition := ⟨.bpo2, .amsterdam, .byTimestamp 15000⟩

#guard NetworkSpec.ofString? "BPO2ToAmsterdamAtTime15k"
  = some (.transition guardBpo2ToAmsterdam)
#guard (NetworkSpec.transition guardBpo2ToAmsterdam).forks = [.bpo2, .amsterdam]
#guard (guardBpo2ToAmsterdam.chainConfig 1).validate.toOption.isSome
#guard (guardBpo2ToAmsterdam.chainConfig 1).rulesAt 0 0 = .ok bpo2Rules
#guard (guardBpo2ToAmsterdam.chainConfig 1).rulesAt 0 14999 = .ok bpo2Rules
#guard (guardBpo2ToAmsterdam.chainConfig 1).forkAt 0 15000 = .ok .amsterdam
#guard (guardBpo2ToAmsterdam.chainConfig 1).rulesAt 0 15000 = .ok amsterdamRules
#guard (guardBpo2ToAmsterdam.chainConfig 1).rulesAt 0 15001 = .ok amsterdamRules
-- Neither side of the boundary is a context failure: the schedule is usable.
#guard ¬ lookupFails isContextL ((guardBpo2ToAmsterdam.chainConfig 1).rulesAt 0 15000)

-- A parseable label may still name an unusable schedule; it is refused where
-- every other unusable schedule is, rather than at the parser.
#guard ForkTransition.ofString? "OsakaToPragueAtTime15k"
  = some ⟨.osaka, .prague, .byTimestamp 15000⟩
#guard lookupFails isContextL
  (((⟨.osaka, .prague, .byTimestamp 15000⟩ : ForkTransition).chainConfig 1).rulesAt 0 0)
#guard lookupFails isContextL
  (((⟨.prague, .osaka, .byTimestamp 0⟩ : ForkTransition).chainConfig 1).rulesAt 0 0)

-- A `network` label is either a static fork or a transition, and the two
-- parsers do not overlap.
#guard NetworkSpec.ofString? "Prague" = some (.static .prague)
#guard NetworkSpec.ofString? "BPO2" = some (.static .bpo2)
#guard NetworkSpec.ofString? "OsakaToBPO1AtTime15k"
  = some (.transition ⟨.osaka, .bpo1, .byTimestamp 15000⟩)
#guard NetworkSpec.ofString? "Cancun" = some (.static .cancun)
#guard NetworkSpec.ofString? "ConstantinopleFix" = some (.static .petersburg)
#guard NetworkSpec.ofString? "Merge" = some (.static .paris)
#guard NetworkSpec.ofString? "CancunToPragueAtTime15k"
  = some (.transition ⟨.cancun, .prague, .byTimestamp 15000⟩)
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
#guard (match (ChainConfig.mk 1 [⟨.prague, .byTimestamp 0⟩, ⟨.osaka, .byTimestamp 0⟩]).validate with
  | .error e => e.render ==
      "InvalidChainConfigError : activation timestamps must strictly increase, \
       but Osaka at 0 does not follow Prague at 0"
  | .ok _ => false)
#guard (match guardFloorSchedule.forkAt 0 999 with
  | .error e => e.render ==
      "UnsupportedEraError : timestamp 999 precedes the earliest era this \
       configuration supports, which begins at 1000"
  | .ok _ => false)
#guard (match mainnetChainConfig.forkAt 0 0 with
  | .error e => e ==
      .support (.unsupportedBlockEra 0 mainnetByzantiumBlock)
  | .ok _ => false)

----------------- THE BPO2-TO-AMSTERDAM ACTIVATION BOUNDARY (goal D) -----------------

-- The rules at 0, 14999, 15000 and 15001 are guarded with the label's parse
-- above (`guardBpo2ToAmsterdam`). These are the remaining points Appendix B of
-- the `jaune-amsterdam-currency-v1` goal requires, each falsifiable without a
-- fixture; the fixture corpus (`--suite amsterdam-transitions`) is what shows
-- every rule keyed on these records switches with them. A transition label is
-- a schedule that starts at genesis, unlike `mainnetChainConfig`, so block 0
-- already resolves to the `before` fork rather than an unsupported era.
#guard ForkTransition.ofString? "BPO2ToAmsterdamAtTime15k" = some guardBpo2ToAmsterdam
#guard (guardBpo2ToAmsterdam.chainConfig 1).validate = .ok ()
#guard (guardBpo2ToAmsterdam.chainConfig 1).forkAt 0 0 = .ok .bpo2
#guard (guardBpo2ToAmsterdam.chainConfig 1).forkAt 0 14999 = .ok .bpo2
-- The schedule is chain-neutral: the same answers on another chain identity.
#guard (guardBpo2ToAmsterdam.chainConfig 12345).rulesAt 0 14999 = .ok bpo2Rules
#guard (guardBpo2ToAmsterdam.chainConfig 12345).rulesAt 0 15000 = .ok amsterdamRules

-- What switches at that second. Header-field presence: `validateHeader` keys
-- on these two flags, so a pre-activation block carrying either field and an
-- activation block missing either are both rejected with `headerFieldPresence`.
#guard bpo2Rules.header.blockAccessListHash = false
#guard bpo2Rules.header.slotNumber = false
#guard amsterdamRules.header.blockAccessListHash = true
#guard amsterdamRules.header.slotNumber = true
-- The block-level access list: `bal = none` builds nothing (goal C's bridge
-- lemma), so the last BPO2 block has an empty list and index zero, and the
-- first Amsterdam block is the first to build and commit one.
#guard bpo2Rules.bal = none
#guard amsterdamRules.bal = some amsterdamBalRules
-- Excess blob gas is carried across the boundary from the parent header under
-- the block's own rules' blob schedule (`calculateExcessBlobGas rules.blob
-- parent`); at this boundary that schedule does not move.
#guard amsterdamRules.blob = bpo2Rules.blob
-- The two EIP-8282 request contracts are called only from the first Amsterdam
-- block on: BPO2's list is Prague's two.
#guard bpo2Rules.requests.length = 2
#guard amsterdamRules.requests.length = 4

-- D13 (goal D, G5): mainnet's schedule names no Amsterdam activation while the
-- pinned `FORK_CRITERIA` is `Unscheduled` -- the shape is guarded with the
-- schedule above (`activations.length = 15`, the
-- fork list, `¬ contains .amsterdam`). What goal D adds is the gate:
-- `scripts/check-fork-constants.sh` compares that criterion against this
-- schedule through the `mainnetActivation` row of `--rules`, so the day the
-- number exists the red gate names the missing `mainnetAmsterdamTimestamp`;
-- nothing here pre-empts it. Until then BPO2 is the last era, however far
-- ahead the block timestamp lies.
#guard mainnetChainConfig.forkAt? 22431084 mainnetBpo2Timestamp = some .bpo2
#guard mainnetChainConfig.forkAt? 22431084 (mainnetBpo2Timestamp + 10 ^ 9) = some .bpo2

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
