"""Decision tables for the consensus-layer rename map (goal jaune-shape-and-names-v1, N5).

Three layers, applied in this order to a Jaune-own name (pyspec-derived names are
recognised first, from the pinned pyspec text, and are never renamed):

  PART_OVERRIDE  exact spelling of one underscore-delimited part -> replacement part
  SEGMENT_OVERRIDE exact spelling of one dot-delimited segment -> replacement segment
  EXPAND         token (camelCase/snake_case token, lower-cased) -> whole words

A part is what is left of a name segment after splitting on `_`; theorem names are
snake_case joins of definition names, so each part is a definition-style name.
"""

# ---------------------------------------------------------------------------------------------
# Tokens that stay although a dictionary would not list them.  Each is justified; the generator
# prints this list as evidence and the master carries the policy-word decision.
# ---------------------------------------------------------------------------------------------

# Lean / Mathlib naming vocabulary (rule 7: Lean conventions).  Theorem names built from these.
LEAN_TOKENS = {
    "ok", "ite", "dite", "bind", "pure", "refl", "trans", "symm", "congr", "ext", "iff", "eq", "ne",
    "le", "lt", "ge", "gt", "beq", "bne", "mk", "fst", "snd", "nil", "cons", "snoc", "foldl", "foldr",
    "foldlm", "forin", "mem", "elim", "imp", "inj", "mod", "div", "mul", "succ", "add", "sub", "neg",
    "get", "set", "of", "to", "io", "ofnat", "tolist", "toarray", "tonat", "min", "max", "pos", "neg",
    "cmp_placeholder",
}

# Names and tokens taken verbatim from a registered protocol source other than the pyspec
# function/container/constant tables (rule 1 and 3).  Token -> citation.
PROTOCOL_TOKENS = {
    "i2osp": "RFC 9380 section 5 (I2OSP), RFC 8017",
    "os2ip": "RFC 9380 section 5 (OS2IP), RFC 8017",
    "strxor": "RFC 9380 section 5.3.1 (strxor)",
    "xmd": "RFC 9380 section 5.3.1 (expand_message_xmd)",
    "xi": "BLS12-381 twist constant xi (Greek letter)",
    "psi": "BLS12-381 untwist-Frobenius-twist endomorphism psi (Greek letter)",
    "fk20": "Feist-Khovratovich FK20 multiproofs (the algorithm's published name)",
    "fr": "BLS12-381 scalar field Fr (as Fp, Fp2)",
    "frs": "plural of Fr",
    "msm": "multi-scalar multiplication (community abbreviation, ZK/KZG literature)",
    "dst": "domain separation tag (RFC 9380 section 3.1, pyspec uses dst)",
    "fft": "fast Fourier transform (pyspec fft_field)",
    "g1": "BLS12-381 group G1", "g2": "BLS12-381 group G2", "fp": "BLS12-381 field Fp", "fp2": "field Fp2",
    "u64": "pyspec uint64 (Jaune type U64)", "u8": "pyspec uint8 (U8)", "u16": "pyspec uint16 (U16)",
    "u32": "pyspec uint32 (U32)", "u128": "pyspec uint128 (U128)", "u256": "pyspec uint256 (U256)",
    "uint64": "pyspec uint64", "uint8": "pyspec uint8", "uint16": "pyspec uint16",
    "uint32": "pyspec uint32", "uint128": "pyspec uint128", "uint256": "pyspec uint256",
    "sha256": "SHA-256", "hash32": "SSZ Hash32", "bytes32": "SSZ Bytes32",
    "ceil32": "pyspec ceil",
    "b0": "hex byte 0xB0 (EIP-8282 builder prefix literal)",
    "eth1": "pyspec eth1_data (Eth1)",
}

# ---------------------------------------------------------------------------------------------
# Token expansions (lower-cased token -> space separated whole words; first word lowerCamel start).
# ---------------------------------------------------------------------------------------------
EXPAND = {
    # glue
    "ctx": "context", "cfg": "config", "cfork": "consensus fork", "gated": "fork field", "meta": "metadata",
    "vbytes": "vector bytes",
    # facts: relation and preservation vocabulary
    "pres": "preservation", "cpres": "corpus preservation", "bpres": "builder preservation",
    "csub": "common substep", "rel": "relation", "proj": "projection", "jp": "join point",
    "inv": "invariant", "ctrl": "control", "arr": "array", "eqs": "equalities",
    "excl": "exclusive", "reg": "registration", "sat": "saturation", "expo": "exposure",
    "src": "source", "wf": "withdrawals frame", "vlen": "validators length",
    # protocol words
    "addr": "address", "adr": "address", "amt": "amount", "att": "attestation", "bal": "balance",
    "bld": "builder", "cred": "credential", "creds": "credentials", "dep": "deposit",
    "eb": "effective balance", "ep": "epoch", "hdr": "header", "pk": "pubkey", "sig": "signature",
    "st": "state", "env": "environment", "ver": "version", "wc": "withdrawal credentials",
    "wds": "withdrawals", "pend": "pending", "pay": "payment", "sv": "ssz vector",
    "recs": "records", "fin": "finalized", "pew": "payload expected withdrawals",
    "act": "activation balance", "acc": "accumulator", "opt": "optional", "qty": "quantity",
    "tr": "transition", "ex": "exit request", "pw": "pending withdrawal", "fc": "fork choice",
    "fcr": "fast confirmation", "consol": "consolidation", "dup": "duplicate", "lit": "literal",
    "bv": "bitvector", "bmv": "balances match validators", "pcd": "pending consolidations distinct",
    "lbh": "latest block header", "lep": "latest execution payload header",
    "pc": "pending consolidations", "pd": "pending deposits", "cmp": "compare", "ord": "ordinal",
    "dir": "directory", "obj": "object", "nl": "newline", "del": "delete",
    "col": "column", "pl": "progressive list", "pts": "points", "scs": "scalars",
    "sk": "secret key", "frob": "frobenius", "coeffs": "coefficients", "brp": "bit reversal",
    "hb": "hex bytes32", "hx": "hex bytes", "fmt": "format", "rp": "recorded pairs",
    "mp": "mainnet preset", "ind": "induction",
    "tx": None,  # lower-case tx is allowed; capital Tx is expanded in the generator
    "gs": "minimal gloas state", "sm": "minimal gloas state", "pm": "minimal preset",
    "xr": "exit request", "wq": "withdrawal queue", "bq": "builders and queues equal", "qe": "queues equal",
    "cx": "coefficient x", "cy": "coefficient y",
    "req": "request", "reqs": "requests", "fs": "finalized slot", "fe": "finalized epoch",
    "fna": "finalized not ahead", "s1": "selector1", "s2": "selector2", "s3": "selector3",
    "s4": "selector4", "cur": "current", "prev": "previous", "x04": "exited have no pending", "cmd": "command", "el": "element", "err": "error",
    "fn": "function", "hi": "high", "lo": "low", "jp2": "join point2", "jp3": "join point3",
    "pref": "prefix", "ops": "operations", "mono": "monotone", "val": "value", "vec": "vector",
    "ws": "whitespace", "dict": "dictionary", "exec": "execution", "seq": "sequence",
    "ref": "reference", "f2": "fp2", "refs": "references", "yval": "yaml value",
    "c64": "uint64 constant", "n64": "u64 literal",
    "b256": "bytes32", "jb256": "json bytes32", "ju256": "json u256", "ju64": "json u64",
    "jadr": "json address", "jarr": "json array", "jdec": "json decimal", "jfield": "json field",
    "jhex": "json hex", "jstr": "json string", "jpubkey": "json pubkey", "jsig": "json signature",
    "hex64": "hex digest", "sums": "sums", "sha": "sha256", "irrel": "irrelevant",
    "indep": "independent", "iter": "iteration", "memo": "memoized",
    # hidden ids and fixture labels
    "i3": "carried triple", "seed23": "seed 23",
    # single letter suffix / prefix conventions
    "z": "zero", "g": "gloas", "m": "fallible", "e": "except",
}

# Whole parts whose meaning is not the token-wise one.  key: exact part (case sensitive).
PART_OVERRIDE = {
    # AnchorInv / corpus
    "switchCred": "switchCredential",
    "ValRel": "ValidatorRelation", "valRel": "validatorRelation",
    "ArrRel": "ValidatorArrayRelation", "arrRel": "validatorArrayRelation",
    "isJpName": "isJoinPointName", "isJpNameC": "isJoinPointNameCorpus", "mkPostC": "mkPostCorpus",
    "findStateC": "findStateCorpus", "okPartsC?": "okPartsCorpus?", "csubParts": "commonSubstepParts",
    "presParts": "preservationParts",
    "s_pc_self": "stateSelfConsolidation", "s_bm_over": "stateBalancesMatchValidatorsOver",
    "s_bm_under": "stateBalancesMatchValidatorsUnder",
    "repVec": "replicateVector", "zeroBv": "zeroBitvector", "zeroVer": "zeroVersion",
    "zeroSig": "zeroSignature",
    "okParts?": "okParts?",
    "CFork": "ConsensusFork", "CForkData": "ConsensusForkData",
    "foldlM": "foldlM", "getElem?": "getElem?", "getElem?'": "getElem?'", "findIdx": "findIdx",
    "val": "validators", "hexVal": "hexValue", "YVal": "YamlValue", "idx": "index",
    "shiftVals": "shiftValues", "okL": "okLeaf", "okT": "okTrans",
    "fmtB": "formatBytes32", "DC": "CollectionMonad", "res": "resultToExcept", "Res": "Result",
    "str": "getString", "ch": "charByte", "GloasOps": "GloasListAccessors", "InvariantsVLen": "InvariantsValidatorsLength", "InvariantsGen": "InvariantsPreservation", "w": "witness",
    "builder1": "builderOne", "initiate0": "initiateZero", "resite": "replaceSite", "toB256": "toU256",
    "B256": "Bytes32", "EnvelopeChecksB": "EnvelopeChecksWithBls",
    "verifyExecutionPayloadEnvelopeB": "verifyExecutionPayloadEnvelopeWithBls",
    "verifyExecutionPayloadEnvelopeSignatureB": "verifyExecutionPayloadEnvelopeSignatureWithBls",
    "blockBeforeOps": "blockBeforeOperations", "withPF": "withPresetAndFork", "y": "yamlResult",
    "appendK": "appendKept", "appendX": "appendDropped", "appendR": "appendRegistered",
    "appendT": "appendToppedUp", "G1J": "G1Jacobian", "fk20H": "fk20Points", "fk20HFft": "fk20PointsFft",
    "L": "leaf", "l4": "fourLeaves", "n2": "leftNode", "n3": "rightNode", "r4": "fourLeafRoot",
    "l8": "eightLeaves", "p": "parseToOption", "q": "quotedScalar", "sc": "plainScalar",
    "processSlot_eqF": "processSlot_eqForkIndexed",
    # joint / fork-indexed variants
    "FinalizedNotAheadF": "FinalizedNotAheadForkIndexed", "FinSlotF": "FinalizedSlotForkIndexed",
    "finSlotF": "finalizedSlotForkIndexed", "FinEpF": "FinalizedEpochForkIndexed",
    "finEpF": "finalizedEpochForkIndexed",
    "processSlotH": "processSlotAbstractedHashes", "processSlotHF": "processSlotAbstractedHashesForkIndexed",
    "getCurrentEpochF": "getCurrentEpochForkIndexed",
    "GSt": "GloasState", "GS": "MinimalGloasState", "Sm": "MinimalGloasState", "Pm": "MinimalPreset",
    "MP": "MainnetPreset", "XR": "ExitRequest",
    # fixtures
    "wExpected": "expectedWithdrawal", "wOther": "otherWithdrawal", "wAmt": "withdrawalAmount",
    "wQ": "quorumWithdrawal", "wS": "subQuorumWithdrawal", "w5": "withdrawalOfFive",
    "zEnvelope": "zeroEnvelope", "zAdr": "zeroAddress", "zCheckpoint": "zeroCheckpoint",
    "zHeader": "zeroHeader", "zPubkey": "zeroPubkey", "zBid": "zeroBid", "zPayment": "zeroPayment",
    "b5Base": "balanceFlowBase", "satBuilder": "saturationBuilder",
    "satWithdrawal": "saturationWithdrawal", "satState": "saturationState",
    "rotState": "rotationState", "bidBuilder": "bidBuilder",
    "bid9": "bidAtSlotNine", "bid9msg": "bidMessageAtSlotNine", "proposer0": "proposerZero",
    "ctxOff": "contextBlsOff", "bidEntry": "bidEntry", "pre01": "prefix01", "preB0": "prefixB0",
    "vrep": "replicateVector", "lnil": "emptyList", "bvz": "zeroBitvector", "z32": "zeroRoot",
    "sExit": "stateExit", "sPendW": "statePendingWithdrawal", "sPendP": "statePendingPayment",
    "sDep": "stateDeposit", "sDup": "stateDuplicate", "depK": "depositKey", "pk": "pubkey",
    "addr": "address", "bld": "builder", "st": "state", "ex": "exitRequest", "pw": "pendingWithdrawal",
    "dep": "deposit", "sig": "signature", "wc": "withdrawalCredentials",
    "G301": "BuilderPubkeysUnique",
    "g301": "builderPubkeysUnique", "g303": "pendingReferencesInRange", "g304": "exitedHaveNoPending",
    "g306": "nextBuilderIndexInRange", "g307": "noLiveWeightOnLatestBid",
    "s03": "stateUnknownBuilderWithdrawal", "s04": "stateExitedSweptWithdrawal",
    "s06": "stateSweepIndexOutOfRange", "s07": "stateLiveEntryAboveQuorum",
    "bid07": "latestBid", "pay07": "latestPayment",
    # builder item labels of EIP-8282 statements (B1 registration, B3 exit authorization, ...)
    "b1": "registrationAuthorization", "b3": "exitAuthorization", "b7": "separationConservation",
    "B5Controls": "BalanceFlowControls", "B5Witnesses": "BalanceFlowWitnesses",
    "StepB1": "StepRegistrationAuthorization", "StepB246": "StepFateAndLatency",
    "StepB3": "StepExitAuthorization", "StepB5": "StepBalanceFlow", "StepB7": "StepSeparationConservation",
    "WithdrawalsB5": "WithdrawalsBalanceFlow",
    # invariants
    "PendLe": "PendingBalanceLe", "pendLe": "pendingBalanceLe", "pend": "pendingBalance",
    "pendW": "pendingWithdrawalBalance", "pendP": "pendingPaymentBalance",
    "PayStepP": "PaymentStep", "AttPay": "AttestationPayment", "PayEntryStep": "PaymentEntryStep",
    "OpsRel": "OperationsRelation", "opsRel": "operationsRelation", "WQ": "WithdrawalQueue",
    "BQ": "BuildersAndQueuesEqual", "QE": "QueuesEqual", "BIdW": "BuilderIdentityWithdrawableEpoch",
    "WFrame": "WithdrawalsFrame", "wFrame": "withdrawalsFrame", "VLen": "ValidatorsLength",
    "vLen": "validatorsLength", "PayKeep": "PaymentKeep", "BPresAt": "BuilderPreservationAt",
    "DepInv": "DepositInvariant", "RegInv": "RegistrationInvariant", "DepositSlotInv": "DepositSlotInvariant",
    "ExitSlotInv": "ExitSlotInvariant", "CrossClean": "CrossingClean", "PewEq": "PayloadExpectedWithdrawalsEq",
    "pewEq": "payloadExpectedWithdrawalsEq", "HdrEq": "HeaderEq", "hdrEq": "headerEq",
    "BuildersPkWe": "BuildersPubkeyWithdrawableEpoch", "pkWe": "pubkeyWithdrawableEpoch",
    "SrcLe": "SourceLe", "Loop1Witness": "FirstLoopWitness", "Loop1EntryOk": "FirstLoopEntryOk",
    "Loop1Floor": "FirstLoopFloor", "loop1": "firstLoop",
    "PendingDepositsAcc": "PendingDepositsAccumulator",
    "JpOk2": "JoinPointOk2", "JpOk3": "JoinPointOk3", "ok2": "ok2", "ok3": "ok3",
    "minAct": "minActivationBalance", "maxEb": "maxEffectiveBalance",
    "balOf": "balanceOf", "GStepView": "GloasStepView",
    # consensus glue
    "M": "Fallible", "H": "Action", "GM": "Validation", "NodeSet": "NodeSet",
    "SSeen": "SeenWithStore", "GSeen": "SeenWithStore",
    "ProgressiveListS": "ProgressiveListOnSpine", "ProgressiveListR": "ProgressiveListRightSpine",
    "ProgressiveBitlistS": "ProgressiveBitlistOnSpine", "ProgressiveBitlistR": "ProgressiveBitlistRightSpine",
    "FcMode": "ForkChoiceMode", "FcrView": "FastConfirmationView", "fcrKeys": "fastConfirmationKeys",
    "kzgVOfYVal": "kzgValueOfYamlValue", "KzgV": "KzgValue", "vBytes": "valueBytes", "vOf": "valueOf",
    "hexF": "hexField", "hexListF": "hexListField", "natListF": "natListField",
    "hexN": "hexBytesOfLength", "isHex64": "isHexDigest", "asStr": "asString", "optNat": "optionalNat",
    "optStr": "optionalString", "optBool": "optionalBool", "reqStr": "requiredString",
    "storeDep": "storeDependent", "u64Of": "u64Of", "defaultVectorsDir": "defaultVectorsDirectory",
    "listDir": "listDirectory", "DirName": "DirectoryName", "RPError": "RecordedPairsError",
    "mkVec": "mkVector", "parseTx": "parseTransaction", "engineTxDecodeNote": "engineTransactionDecodeNote",
    "hashToFieldL": "hashToFieldLength", "bytesToBlsFieldK": "bytesToBlsFieldKernel",
    "verifyKzgProofImplK": "verifyKzgProofImplKernel",
    "dstK1": "dstExpandMessageXmd", "dstJ10": "dstHashToCurveG2",
    "g1m0": "g1Generator", "g1m1": "g1Point", "g2m0": "g2Generator", "g2m1": "g2Point",
    "q0": "quotientZero", "q1": "quotientOne",
    "isSpaceOrNl": "isSpaceOrNewline", "singleQ": "singleQuoted", "doubleQ": "doubleQuoted",
    "ethAggregatePubkeysM": "ethAggregatePubkeysFallible",
    "I3": "CarriedTriple", "depReq_I3": "depositRequest_carriedTriple",
    "payloadExpectedWithdrawals": "payloadExpectedWithdrawals",
    "u64": "u64", "U64": "U64", "UIntN": "UIntN", "U8": "U8", "U16": "U16", "U32": "U32",
    "U128": "U128", "U256": "U256",
    "pre": "pre", "post": "post",
}

SEGMENT_OVERRIDE = {
    "s_pc_self": "stateSelfConsolidation", "s_bm_over": "stateBalancesMatchValidatorsOver",
    "s_bm_under": "stateBalancesMatchValidatorsUnder",
    "ctrlExit_t1": "controlExit_pendingBalanceZero", "ctrlExit_t2": "controlExit_currentEpochZero",
    "ctrlExit_t4": "controlExit_initiateBuilderExit",
}

# Exact qualified old name -> replacement of its last segment only (namespaces still follow the
# generic rules).  For fixtures and fields whose short name has no token-wise expansion.
LAST_OVERRIDE = {
    "JauneConsensus.Harness.Run.opt": "optimisticStore",
    "JauneConsensus.Facts.Gloas.StepRel.R": "relation",
    "JauneConsensus.Facts.Gloas.Onboarding.OnboardingSpec.K": "kept",
}

# Whole last components taken from a registered protocol source that is not the pyspec API
# tables (rule 1/3): name -> citation.
PROTOCOL_NAMES = {
    "CompatibleUnionA": "consensus-spec-tests v1.6.1 general/phase0/ssz_generic/compatible_unions case names",
    "CompatibleUnionBC": "consensus-spec-tests v1.6.1 general/phase0/ssz_generic/compatible_unions case names",
    "CompatibleUnionABCA": "consensus-spec-tests v1.6.1 general/phase0/ssz_generic/compatible_unions case names",
    "PayloadStatusV1": "execution-apis Engine API PayloadStatusV1 (src/engine/paris.md)",
    "UIntN": "pyspec uintN (ssz/simple-serialize.md), Lean case",
    "skToPk": "draft-irtf-cfrg-bls-signature section 2.3 SkToPk (pyspec specs/phase0/beacon-chain.md bls)",
    "keyValidate": "draft-irtf-cfrg-bls-signature section 2.5 KeyValidate",
    "coreVerify": "draft-irtf-cfrg-bls-signature section 2.6 CoreVerify",
    "aggregateVerify": "draft-irtf-cfrg-bls-signature section 2.9 AggregateVerify",
    "fastAggregateVerify": "draft-irtf-cfrg-bls-signature section 3.3.4 FastAggregateVerify",
    "i2osp": "RFC 8017 section 4.1 I2OSP, used by RFC 9380 section 5",
    "os2ip": "RFC 8017 section 4.2 OS2IP, used by RFC 9380 section 5",
    "strxor": "RFC 9380 section 5.3.1 strxor",
    "expandMessageXmd": "RFC 9380 section 5.3.1 expand_message_xmd",
    "mapToCurveG2": "RFC 9380 section 6.6.3 map_to_curve (BLS12381G2)",
    "hashToG2": "RFC 9380 section 3 hash_to_curve (BLS12381G2)",
    "hashToFieldFp2": "RFC 9380 section 5.2 hash_to_field (Fp2)",
    "clearCofactorG2": "RFC 9380 section 7 clear_cofactor",
}


# Tactic keywords (the string tokens of `macro`/`syntax`/`elab ... : tactic`).  They are neither
# declarations nor fields, so the map cannot carry them and the compiler-resolved apply tool
# cannot resolve them: a decision for the master.  Proposed spellings, for the packet only.
TACTIC_KEYWORDS = {
    "vcg_step": "verification_step", "jvcg": "join_point_verification", "gvcg": "gloas_verification",
    "pres_of": "preservation_of", "pres_close": "preservation_close", "pres_step": "preservation_step",
    "pstep": "preservation_walk", "cstep": "corpus_walk", "jstep": "join_point_walk",
    "gstep": "gloas_walk", "gstep_close": "gloas_walk_close", "gstep_of": "gloas_walk_of",
    "gstep_rebase": "gloas_walk_rebase", "hdr_tail": "header_tail", "ftail": "finalized_tail",
    "ftail_of": "finalized_tail_of", "jp_intro": "join_point_intro", "jp_call": "join_point_call",
    "jp_abs": "join_point_abstract", "jp_intro_c": "join_point_intro_corpus",
    "jp_call_c": "join_point_call_corpus", "loop_pres": "loop_preservation",
    "loop_csub": "loop_common_substep", "csub_of": "common_substep_of",
    "csub_close": "common_substep_close",
}


# Meaning audit after the cross-family N2 review (hydrogen-review.md): each entry below was
# checked against the definition it names.
PART_OVERRIDE.update({
    "balBytes": "blockAccessListBytes",             # bytes of payload.block_access_list, not a balance (rule 6)
    "q0": "mapToCurveOutput0", "q1": "mapToCurveOutput1",   # RFC 9380 J.10.1 map_to_curve outputs
    "g1m0": "g1SetupMonomial0", "g1m1": "g1SetupMonomial1",  # KZG setup monomial[0], monomial[1]
    "g2m0": "g2SetupMonomial0", "g2m1": "g2SetupMonomial1",
    "vBytes": "kzgValueOfBytes", "vOf": "kzgValueOfExcept",  # they build a KzgV
    "I3": "PendingBalanceReferencesExited",         # PendLe and G3-03 and G3-04, conjoined
    "c64": "u64Checked", "n64": "u64Literal",       # one u64 spelling for the helper family
    "findIdx": "findIndex", "bal": "balances",      # commonSubstep_{set,modify}_bal act on `balances`
    "b256GoAt": "u256GoAt", "b256Eq": "u256Eq", "b256OfBytes": "bytes32OfBytes",
    "elField": "executionLayerField", "dep": "depositRequest",
})
SEGMENT_OVERRIDE.update({
    "b256_toBytes_toB256": "bytes_toU256_toBytes",  # (Bytes.toB256 l).toBytes = l
})
