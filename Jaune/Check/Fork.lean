-- Check/Fork.lean : executable checks of `Jaune/Fork.lean`.
--
-- Check module (see `scripts/layering.json`). The `#guard`s, `example`s and test
-- helpers below were relocated unchanged from `Jaune/Fork.lean` so that the
-- specification module defines only the specification (goal
-- `jaune-shape-and-names-v1`, unit W0). The default build compiles this module
-- through `JauneChecks.lean`.
import Jaune.Fork

namespace Jaune

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

-- Exact candidate resolver inventory, in declared order. This snapshot
-- checks admission to rule records, not per-fork execution conformance.
#guard Fork.supported = [.byzantium, .constantinople, .petersburg, .istanbul,
  .muirGlacier, .berlin, .london, .arrowGlacier, .grayGlacier, .paris, .shanghai,
  .cancun, .prague, .osaka, .bpo1, .bpo2, .amsterdam]

-- No declared rule record remains absent in this candidate. Retain the
-- complement snapshot alongside the exact resolver inventory.
#guard Fork.unimplemented = []

#guard renderTagged "SomeTag" .none = "SomeTag"
#guard renderTagged "SomeTag" (.text "why") = "SomeTag : why"

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
#guard ChainContextError.render (.invalidForkRules .zeroBlockAccessListItemCost)
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
#guard ChainContextError.render (.invalidForkRules (.blockAccessListHeaderMismatch false true))
  = "InvalidForkRulesError : the rules do not carry block-level access-list \
     rules, but the header commits to one"

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
#guard ForkRules.defect? { amsterdamRules with blockAccessListRules := some { itemCost := 0 } }
  = some .zeroBlockAccessListItemCost
#guard ForkRules.defect? { amsterdamRules with blockAccessListRules := none }
  = some (.blockAccessListHeaderMismatch false true)
#guard ForkRules.defect? { bpo2Rules with blockAccessListRules := some amsterdamBlockAccessListRules }
  = some (.blockAccessListHeaderMismatch true false)
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
  settlement := { istanbulRules.settlement with refundQuotient := 0 } }
  : ForkRules).Valid
#guard ¬ ({ istanbulRules with
  access := .flat { istanbulAccessGas with sload := 0 } } : ForkRules).Valid
#guard ¬ ({ cancunRules with
  proofOfWork := some { blockReward := 2 * 10 ^ 18, bombDelay := 11400000 } }
  : ForkRules).Valid
#guard ForkRules.defect? { istanbulRules with access := .eip2929 }
  = some (.accessTypeMismatch true 0)
#guard ForkRules.defect? { istanbulRules with
  settlement := { istanbulRules.settlement with refundQuotient := 0 } }
  = some .zeroRefundQuotient
#guard ForkRules.defect? { istanbulRules with
  access := .flat { istanbulAccessGas with sload := 0 } }
  = some (.zeroFlatAccessPrice { istanbulAccessGas with sload := 0 })
#guard ForkRules.defect? { byzantiumRules with
  transactionRules := { byzantiumTransactionRules with maxType := 1 } }
  = some (.accessTypeMismatch false 1)
#guard ForkRules.defect? { berlinRules with
  transactionRules := { berlinRules.transactionRules with maxType := 0 } }
  = some (.accessTypeMismatch true 0)
#guard ForkRules.defect? { cancunRules with
  proofOfWork := some { blockReward := 2 * 10 ^ 18, bombDelay := 11400000 } }
  = some .powBeaconRootConflict

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

-- The runnable and absent-record sets are derived by filtering Fork.all
-- through Fork.rules?. Their exact inventories, including this candidate's
-- empty absent-record set, are guarded where
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
#guard pragueRules.opcodes.clz = false

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
#guard pragueRules.gas.perAuthorizationIntrinsic = 25000
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
  [(1, (0x00000961Ef480Eb55e80D19ad83579A64c007002 : Address)),
   (2, (0x0000BBdDc7CE488642fb579F8B00f3a590007251 : Address))]

-- Prague's precompile activation set is exactly 0x01 through 0x11, which is
-- what the former `1 ≤ a.toNat ∧ a.toNat ≤ 17` range said.
#guard pragueRules.precompiles.length = 17
#guard (List.range' 1 17).all (fun n => pragueRules.isPrecompile (Nat.toAddress n))
#guard ¬ pragueRules.isPrecompile (0x00 : Address)
#guard ¬ pragueRules.isPrecompile (0x12 : Address)
#guard ¬ pragueRules.isPrecompile (0x100 : Address)

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
#guard osakaRules.opcodes.clz = true

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
#guard osakaRules.isPrecompile (0x100 : Address)
#guard ¬ pragueRules.isPrecompile (0x100 : Address)
#guard ¬ osakaRules.isPrecompile (0x12 : Address)
#guard ¬ osakaRules.isPrecompile (0xFF : Address)
#guard ¬ osakaRules.isPrecompile (0x101 : Address)
#guard (List.range' 1 17).all (fun n => osakaRules.isPrecompile (Nat.toAddress n))

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
#guard { petersburgRules with fork := .byzantium, opcodes := byzantiumRules.opcodes, proofOfWork := byzantiumRules.proofOfWork } = byzantiumRules
#guard { constantinopleRules with fork := .petersburg, sstore := petersburgRules.sstore } = petersburgRules
#guard { muirGlacierRules with fork := .istanbul, proofOfWork := istanbulRules.proofOfWork } = istanbulRules
#guard { berlinRules with fork := .muirGlacier, modexp := muirGlacierRules.modexp, modexpComplexity := muirGlacierRules.modexpComplexity, access := muirGlacierRules.access, transactionRules := muirGlacierRules.transactionRules } = muirGlacierRules
#guard { londonRules with fork := .berlin, opcodes := berlinRules.opcodes, gas := berlinRules.gas, header := berlinRules.header, settlement := berlinRules.settlement, transactionRules := berlinRules.transactionRules, creation := berlinRules.creation, proofOfWork := berlinRules.proofOfWork } = berlinRules
#guard { arrowGlacierRules with fork := .london, proofOfWork := londonRules.proofOfWork } = londonRules
#guard { grayGlacierRules with fork := .arrowGlacier, proofOfWork := arrowGlacierRules.proofOfWork } = arrowGlacierRules
#guard { parisRules with fork := .grayGlacier, settlement := grayGlacierRules.settlement, proofOfWork := grayGlacierRules.proofOfWork } = grayGlacierRules
#guard { shanghaiRules with fork := .paris, opcodes := parisRules.opcodes, header := parisRules.header, transactionRules := parisRules.transactionRules, creation := parisRules.creation } = parisRules
#guard { cancunRules with fork := .shanghai, blob := shanghaiRules.blob, opcodes := shanghaiRules.opcodes, header := shanghaiRules.header, precompiles := shanghaiRules.precompiles, settlement := shanghaiRules.settlement, transactionRules := shanghaiRules.transactionRules, systemCalls := shanghaiRules.systemCalls } = shanghaiRules

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
#guard byzantiumRules.proofOfWork.map ProofOfWorkRules.blockReward = some (3 * 10 ^ 18)
#guard petersburgRules.proofOfWork.map ProofOfWorkRules.blockReward = some (2 * 10 ^ 18)
#guard istanbulRules.proofOfWork.map ProofOfWorkRules.bombDelay = some 5000000
#guard muirGlacierRules.proofOfWork.map ProofOfWorkRules.bombDelay = some 9000000
#guard berlinRules.proofOfWork.map ProofOfWorkRules.bombDelay = some 9000000
#guard londonRules.proofOfWork.map ProofOfWorkRules.bombDelay = some 9700000
#guard arrowGlacierRules.proofOfWork.map ProofOfWorkRules.bombDelay = some 10700000
#guard grayGlacierRules.proofOfWork.map ProofOfWorkRules.bombDelay = some 11400000
#guard parisRules.proofOfWork = none
#guard shanghaiRules.proofOfWork = none
#guard cancunRules.proofOfWork = none

-- Istanbul's shared-formula numbers, the full literal's live fields.
#guard istanbulRules.gas.storageClearRefund = 15000
#guard istanbulRules.transactionRules.dataNonZero = 16
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
#guard byzantiumRules.settlement.refundQuotient = 2
#guard byzantiumRules.settlement.selfdestructRefund = 24000
#guard londonRules.settlement.refundQuotient = 5
#guard londonRules.settlement.selfdestructRefund = 0
#guard grayGlacierRules.settlement.touchedSweep = true
#guard parisRules.settlement.touchedSweep = false
#guard grayGlacierRules.settlement.eraseEmptyOnModify = false
#guard parisRules.settlement.eraseEmptyOnModify = true
#guard cancunRules.settlement.selfdestructOnlyCreated = true
#guard londonRules.settlement.selfdestructOnlyCreated = false

-- Admission: maxType 0/1/2/3/4 at Byzantium/Berlin/London/Cancun/Prague.
#guard byzantiumRules.transactionRules.maxType = 0
#guard berlinRules.transactionRules.maxType = 1
#guard londonRules.transactionRules.maxType = 2
#guard cancunRules.transactionRules.maxType = 3
#guard pragueRules.transactionRules.maxType = 4
#guard byzantiumRules.transactionRules.dataNonZero = 68
#guard parisRules.transactionRules.warmCoinbase = false
#guard shanghaiRules.transactionRules.warmCoinbase = true
#guard cancunRules.transactionRules.calldataFloor = false
#guard pragueRules.transactionRules.calldataFloor = true

-- Creation: 0xEF rejection at London, init-code limit at Shanghai.
#guard berlinRules.creation.rejectEf = false
#guard parisRules.creation.rejectEf = true
#guard londonRules.creation.initCodeLimit = false
#guard shanghaiRules.creation.initCodeLimit = true

-- Opcode availability along the chain.
#guard byzantiumRules.opcodes.shifts = false
#guard petersburgRules.opcodes.create2 = true
#guard petersburgRules.opcodes.extCodeHash = true
#guard istanbulRules.opcodes.chainId = true
#guard istanbulRules.opcodes.selfBalance = true
#guard berlinRules.opcodes.baseFee = false
#guard londonRules.opcodes.baseFee = true
#guard parisRules.opcodes.push0 = false
#guard shanghaiRules.opcodes.push0 = true
#guard shanghaiRules.opcodes.transient = false
#guard cancunRules.opcodes.transient = true
#guard cancunRules.opcodes.mcopy = true
#guard cancunRules.opcodes.blobHash = true
#guard cancunRules.opcodes.blobBaseFee = true

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
#guard shanghaiRules.systemCalls.beaconRoots = false
#guard cancunRules.systemCalls.beaconRoots = true
#guard cancunRules.systemCalls.historyStorage = false
#guard pragueRules.systemCalls.historyStorage = true

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
     pragueAccess, pragueSstore, pragueSettlement, pragueTransactionRules, pragueCreation,
     none, pragueSystemCalls, pragueBn254, .eip2565⟩ := rfl
example : osakaRules =
    ⟨.osaka, osakaBlobSchedule, pragueCodeLimits, osakaTransactionLimits,
     osakaBlockLimits, osakaModexpRules, osakaOpcodeRules, pragueGasSchedule,
     none, pragueHeaderRules, pragueRequests, none, osakaPrecompiles,
     pragueAccess, pragueSstore, pragueSettlement, pragueTransactionRules, pragueCreation,
     none, pragueSystemCalls, pragueBn254, .eip2565⟩ := rfl
example : bpo1Rules =
    ⟨.bpo1, bpo1BlobSchedule, pragueCodeLimits, osakaTransactionLimits,
     osakaBlockLimits, osakaModexpRules, osakaOpcodeRules, pragueGasSchedule,
     none, pragueHeaderRules, pragueRequests, none, osakaPrecompiles,
     pragueAccess, pragueSstore, pragueSettlement, pragueTransactionRules, pragueCreation,
     none, pragueSystemCalls, pragueBn254, .eip2565⟩ := rfl
example : bpo2Rules =
    ⟨.bpo2, bpo2BlobSchedule, pragueCodeLimits, osakaTransactionLimits,
     osakaBlockLimits, osakaModexpRules, osakaOpcodeRules, pragueGasSchedule,
     none, pragueHeaderRules, pragueRequests, none, osakaPrecompiles,
     pragueAccess, pragueSstore, pragueSettlement, pragueTransactionRules, pragueCreation,
     none, pragueSystemCalls, pragueBn254, .eip2565⟩ := rfl
-- F1 for the twelve historical forks: the whole record, so a field added to
-- `ForkRules` later cannot be inherited by any of them without being named.
example : byzantiumRules =
    ⟨.byzantium, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, eip198ModexpRules, byzantiumOpcodeRules,
     byzantiumGasSchedule, none, preLondonHeaderRules, [], none,
     byzantiumPrecompiles, AccessSchedule.flat byzantiumAccessGas,
     byzantiumSstore, byzantiumSettlement, byzantiumTransactionRules, byzantiumCreation,
     some ⟨3 * 10 ^ 18, 3000000⟩, byzantiumSystemCalls, byzantiumBn254Gas,
     ModexpComplexity.eip198⟩ := rfl
example : petersburgRules =
    ⟨.petersburg, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, eip198ModexpRules, petersburgOpcodeRules,
     byzantiumGasSchedule, none, preLondonHeaderRules, [], none,
     byzantiumPrecompiles, AccessSchedule.flat byzantiumAccessGas,
     byzantiumSstore, byzantiumSettlement, byzantiumTransactionRules, byzantiumCreation,
     some ⟨2 * 10 ^ 18, 5000000⟩, byzantiumSystemCalls, byzantiumBn254Gas,
     ModexpComplexity.eip198⟩ := rfl
example : constantinopleRules =
    ⟨.constantinople, pragueBlobSchedule, pragueCodeLimits,
     pragueTransactionLimits, pragueBlockLimits, eip198ModexpRules,
     petersburgOpcodeRules, byzantiumGasSchedule, none, preLondonHeaderRules,
     [], none, byzantiumPrecompiles,
     AccessSchedule.flat byzantiumAccessGas, constantinopleSstore,
     byzantiumSettlement, byzantiumTransactionRules, byzantiumCreation,
     some ⟨2 * 10 ^ 18, 5000000⟩, byzantiumSystemCalls, byzantiumBn254Gas,
     ModexpComplexity.eip198⟩ := rfl
example : istanbulRules =
    ⟨.istanbul, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, eip198ModexpRules, istanbulOpcodeRules,
     byzantiumGasSchedule, none, preLondonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.flat istanbulAccessGas,
     istanbulSstore, byzantiumSettlement, istanbulTransactionRules, byzantiumCreation,
     some ⟨2 * 10 ^ 18, 5000000⟩, byzantiumSystemCalls, istanbulBn254Gas,
     ModexpComplexity.eip198⟩ := rfl
example : muirGlacierRules =
    ⟨.muirGlacier, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, eip198ModexpRules, istanbulOpcodeRules,
     byzantiumGasSchedule, none, preLondonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.flat istanbulAccessGas,
     istanbulSstore, byzantiumSettlement, istanbulTransactionRules, byzantiumCreation,
     some ⟨2 * 10 ^ 18, 9000000⟩, byzantiumSystemCalls, istanbulBn254Gas,
     ModexpComplexity.eip198⟩ := rfl
example : berlinRules =
    ⟨.berlin, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, pragueModexpRules, istanbulOpcodeRules,
     byzantiumGasSchedule, none, preLondonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, byzantiumSettlement, berlinTransactionRules, byzantiumCreation,
     some ⟨2 * 10 ^ 18, 9000000⟩, byzantiumSystemCalls, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl
example : londonRules =
    ⟨.london, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, pragueModexpRules, londonOpcodeRules,
     pragueGasSchedule, none, londonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, londonSettlement, londonTransactionRules, londonCreation,
     some ⟨2 * 10 ^ 18, 9700000⟩, byzantiumSystemCalls, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl
example : arrowGlacierRules =
    ⟨.arrowGlacier, pragueBlobSchedule, pragueCodeLimits,
     pragueTransactionLimits, pragueBlockLimits, pragueModexpRules,
     londonOpcodeRules, pragueGasSchedule, none, londonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, londonSettlement, londonTransactionRules, londonCreation,
     some ⟨2 * 10 ^ 18, 10700000⟩, byzantiumSystemCalls, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl
example : grayGlacierRules =
    ⟨.grayGlacier, pragueBlobSchedule, pragueCodeLimits,
     pragueTransactionLimits, pragueBlockLimits, pragueModexpRules,
     londonOpcodeRules, pragueGasSchedule, none, londonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, londonSettlement, londonTransactionRules, londonCreation,
     some ⟨2 * 10 ^ 18, 11400000⟩, byzantiumSystemCalls, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl
example : parisRules =
    ⟨.paris, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, pragueModexpRules, londonOpcodeRules,
     pragueGasSchedule, none, londonHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, parisSettlement, londonTransactionRules, londonCreation,
     none, byzantiumSystemCalls, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl
example : shanghaiRules =
    ⟨.shanghai, pragueBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, pragueModexpRules, shanghaiOpcodeRules,
     pragueGasSchedule, none, shanghaiHeaderRules, [], none,
     istanbulPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, parisSettlement, shanghaiTransactionRules, shanghaiCreation,
     none, byzantiumSystemCalls, istanbulBn254Gas,
     ModexpComplexity.eip2565⟩ := rfl
example : cancunRules =
    ⟨.cancun, cancunBlobSchedule, pragueCodeLimits, pragueTransactionLimits,
     pragueBlockLimits, pragueModexpRules, cancunOpcodeRules,
     pragueGasSchedule, none, cancunHeaderRules, [], none,
     cancunPrecompiles, AccessSchedule.eip2929,
     istanbulSstore, cancunSettlement, cancunTransactionRules, shanghaiCreation,
     none, cancunSystemCalls, istanbulBn254Gas,
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
      && r.requests == pragueRequests && r.stateGas == none && r.blockAccessListRules == none
  | none => false)
#guard amsterdamRules.gas ≠ pragueGasSchedule
#guard amsterdamRules.header ≠ pragueHeaderRules
#guard amsterdamRules.requests ≠ pragueRequests
#guard amsterdamRules.stateGas ≠ none
#guard amsterdamRules.blockAccessListRules ≠ none

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
#guard amsterdamRules.gas.perAuthorizationIntrinsic = 7816
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
#guard amsterdamGasSchedule.perAuthorizationIntrinsic
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
  opcodes := osakaOpcodeRules,
  gas := pragueGasSchedule, stateGas := none, header := pragueHeaderRules,
  requests := pragueRequests, blockAccessListRules := none } = bpo2Rules
#guard { bpo2Rules with
  fork := .amsterdam, code := amsterdamCodeLimits, tx := amsterdamTransactionLimits,
  opcodes := amsterdamOpcodeRules,
  gas := amsterdamGasSchedule, stateGas := some amsterdamStateGasRules,
  header := amsterdamHeaderRules, requests := amsterdamRequests,
  blockAccessListRules := some amsterdamBlockAccessListRules } = amsterdamRules
-- The moved fields, one guard each, so a failure names the field.
#guard amsterdamRules.fork = .amsterdam
#guard amsterdamRules.code = amsterdamCodeLimits
#guard amsterdamRules.opcodes = amsterdamOpcodeRules
#guard amsterdamRules.gas = amsterdamGasSchedule
#guard amsterdamRules.stateGas = some amsterdamStateGasRules
#guard amsterdamRules.header = amsterdamHeaderRules
#guard amsterdamRules.requests = amsterdamRequests
#guard amsterdamRules.blockAccessListRules = some amsterdamBlockAccessListRules
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
     amsterdamRequests, some amsterdamBlockAccessListRules, osakaPrecompiles,
     pragueAccess, pragueSstore, pragueSettlement, pragueTransactionRules, pragueCreation,
     none, pragueSystemCalls, pragueBn254, .eip2565⟩ := rfl

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
#guard amsterdamRules.opcodes.clz = true
#guard amsterdamRules.opcodes.slotnum = true
#guard amsterdamRules.opcodes.stackAccess = true
#guard amsterdamRules.blockAccessListRules = some { itemCost := 2000 }
#guard (amsterdamRules.blockAccessListRules.map BlockAccessListRules.itemCost) = some 2000
-- The request list: Prague's two calls in Prague's order (goal A's guard,
-- unchanged in meaning), followed by EIP-8282's two in the pinned
-- `process_general_purpose_requests` source-call order.
#guard amsterdamRules.requests.length = 4
#guard amsterdamRules.requests.take 2 = pragueRequests
#guard amsterdamRules.requests.map Prod.fst = [1, 2, 3, 4]
#guard amsterdamRules.requests =
  [(1, (0x00000961Ef480Eb55e80D19ad83579A64c007002 : Address)),
   (2, (0x0000BBdDc7CE488642fb579F8B00f3a590007251 : Address)),
   (3, (0x0000BFF46984E3725691FA540A8C7589300D8282 : Address)),
   (4, (0x000064D678505AD48F8CCB093BC65613800E8282 : Address))]
-- Only Amsterdam carries a block-level access list, and it is the only fork
-- whose header commits to one: the `Valid` conjunct is checked on all nine.
#guard Fork.supported.all (fun f =>
  match f.rules? with
  | some r => r.blockAccessListRules.isSome == r.header.blockAccessListHash
  | none => false)
#guard ¬ ({ amsterdamRules with blockAccessListRules := none } : ForkRules).Valid
#guard ¬ ({ bpo2Rules with blockAccessListRules := some amsterdamBlockAccessListRules } : ForkRules).Valid
#guard ¬ ({ amsterdamRules with blockAccessListRules := some { itemCost := 0 } } : ForkRules).Valid

-- And the composed record is reachable through fork identity, which is what
-- makes Amsterdam a supported fork rather than a metering vehicle. (Goal B
-- guarded the negation of each of these three.)
#guard Fork.amsterdam.rules? = some amsterdamRules
#guard Fork.amsterdam.rules?.isSome
#guard Fork.supported.contains .amsterdam

-- Every declared fork now resolves to its own record through both lookups.
-- Goal A guarded Amsterdam's support refusal here; that row became an
-- admission when Amsterdam resolved. U11a/U11b/U11d similarly moved Berlin
-- through Cancun to admission, and this candidate admits the remaining
-- pre-Berlin records. The rows retain the exact lookup inventory; they do
-- not establish fixture conformance.
#guard Fork.byzantium.rules = .ok byzantiumRules
#guard Fork.constantinople.rules = .ok constantinopleRules
#guard Fork.petersburg.rules = .ok petersburgRules
#guard Fork.istanbul.rules = .ok istanbulRules
#guard Fork.muirGlacier.rules = .ok muirGlacierRules
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
#guard Fork.byzantium.rules? = some byzantiumRules
#guard Fork.constantinople.rules? = some constantinopleRules
#guard Fork.petersburg.rules? = some petersburgRules
#guard Fork.istanbul.rules? = some istanbulRules
#guard Fork.muirGlacier.rules? = some muirGlacierRules
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
#guard (Fork.all.filter (fun f => f.rules = .error (.unsupportedFork f))) = []

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
-- silently answer those blocks. Schedule selection and rule availability
-- remain separate lookups: this candidate resolves each declared era to its
-- own record, while the pre-Byzantium floor remains refused.
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
-- A Byzantium-era block now resolves to its own rules. The Berlin-through-
-- Cancun admissions from U11a/U11b/U11d remain unchanged; the earlier floor
-- refusal above still distinguishes an unsupported era from a named fork.
#guard mainnetChainConfig.rulesAt mainnetByzantiumBlock 0 = .ok byzantiumRules
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
#guard bpo2Rules.blockAccessListRules = none
#guard amsterdamRules.blockAccessListRules = some amsterdamBlockAccessListRules
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

end Jaune

