"""Decisions behind the execution-layer map rows (goal jaune-shape-and-names-v1).

Each table entry is a naming decision with its rule and source.  Status codes
(appended to the map row's `source` as `[B]` / `[M]`; the map schema defines no
status field and no checker reads them):
`B` settled: accepted in goal Appendix B (decision 10), or decided by the user
(a source that starts `user decision`: `Tx.gas`, `gasStorageUpdate`), or a
rule-1 gas constant spelled as its EIP names it, or a row derived from such a
decision (an instance or member that follows a settled rename); `M` added by
this map under the same rules, for review (choices are named in the row's
notes).
"""

# Token -> (replacement, rule, source, status).  Applied to camelCase tokens of
# an in-scope name (rule 5: no private short forms).
TOKENS = {
    'Acct': ('Account', '1', 'Yellow Paper account state; execution-apis AccountProof (balance, nonce, codeHash, storageHash)', 'B'),
    'Adr': ('Address', '1', 'opcode ADDRESS; execution-apis base-types.yaml `address`', 'B'),
    'Stor': ('Storage', '1', 'Yellow Paper account storage; execution-apis `storageHash`; EIP-1153 vocabulary', 'B'),
    'Tra': ('TransientStorage', '1', 'EIP-1153 (transient storage)', 'B'),
    'B256': ('U256', '3', 'alloy `U256` is the number; EELS `U256`; execution-apis `uint256`', 'B'),
    'B128': ('U128', '3', 'one-to-one with `B256`->`U256`; alloy `U128`', 'B'),
    'Tx': ('Transaction', '4', 'plain word (`tx` stays the binder); execution-apis transaction.yaml; EIP-2718 `Transaction`', 'B'),
    'Txs': ('Transactions', '1', 'execution-apis block.yaml `transactions`', 'B'),
    'BLT': ('RlpItem', '1', 'the RLP definition speaks of items (Yellow Paper Appendix B)', 'B'),
    'BLTs': ('RlpItems', '1', 'plural of `BLT`->`Rlp.Item`', 'M'),
    'Rinst': ('PlainOp', '4', 'Appendix B opcode class names; the class gives each step its return type', 'B'),
    'Jinst': ('JumpOp', '4', 'Appendix B opcode class names', 'B'),
    'Linst': ('HaltOp', '4', 'Appendix B opcode class names', 'B'),
    'Ninst': ('NextOp', '4', 'Appendix B opcode class names', 'B'),
    'Xinst': ('MessageOp', '3', 'EVMC `evmc_message`; EELS `Message`; geth tracing hooks (decision 10)', 'B'),
    'Inst': ('Op', '4', 'Appendix B: `Inst` -> `Op` with constructors `next`, `jump`, `halt`', 'B'),
    'InstType': ('OpClass', '4', 'the tag of an opcode byte\'s class (`PlainOp`, `MessageOp`, ...); follows the class names', 'M'),
    'Instrs': ('Ops', '4', 'follows `Inst` -> `Op`', 'M'),
    'Precomp': ('Precompile', '1', 'Appendix B `Precomp...` -> `Precompile...`; EIP-198 etc. say precompile', 'B'),
    'NTB': ('TrieBuilder', '4', 'Appendix B: whole words for the trie builder', 'B'),
    'NTBs': ('TrieBranches', '4', 'sixteen child builders of a branch node', 'M'),
    'blobHashes': ('blobVersionedHashes', '1', 'execution-apis transaction.yaml `blobVersionedHashes`', 'B'),
    'BlobHashes': ('BlobVersionedHashes', '1', 'execution-apis transaction.yaml `blobVersionedHashes`', 'B'),
    'fakeExp': ('fakeExponential', '1', 'EIP-4844 `fake_exponential`', 'B'),
    'FakeExp': ('FakeExponential', '1', 'EIP-4844 `fake_exponential`', 'B'),
    'Ex': ('Except', '5', 'whole word: `toExHeader` returns `Except _ Header`', 'M'),
    'B8L': ('Bytes', '5', 'whole word: `B8L` is a list of bytes', 'M'),
    'Auth': ('Authorization', '1', 'EIP-7702 (authorization list); EIP-spelled names (`perAuthBase...`) keep `Auth`', 'B'),
    'B64': ('UInt64', '5', 'whole word: the value is a `UInt64`', 'M'),
    'B32s': ('UInt32s', '5', 'whole word: a list of 32-bit words', 'M'),
    'B4L': ('Nibbles', '5', 'whole word: a list of 4-bit nibbles', 'M'),
    'B4': ('Nibble', '5', 'whole word: a 4-bit value', 'M'),
    'Opts': ('Options', '5', 'whole word: command-line options', 'M'),
    'Req': ('Required', '5', 'whole word: `natReq` reads a required natural field (audit: not `Request`)', 'M'),
    'bexp': ('exp', '1', 'EVM opcode EXP: word exponentiation modulo 2^256', 'M'),
    'mulr': ('mulRounded', '5', '`(z * x + c) / s`: multiply, add the rounding constant, rescale (the Maker `rmul` pattern)', 'M'),
    'smin': ('signedMin', '5', 'the minimum two\'s-complement value, 0x80...0', 'M'),
    'Val': ('Value', '5', 'whole word', 'M'),
    # curve standards' vocabulary (Appendix A, curves row): Fp, Fp2, G1, G2
    'BNF': ('Bn254Fp', '1', 'EIP-196/197 alt_bn128 base field F_p; curve-standard `Fp`', 'M'),
    'BNF2': ('Bn254Fp2', '1', 'EIP-197 F_p^2; curve-standard `Fp2`', 'M'),
    'BNF12': ('Bn254Fp12', '1', 'EIP-197 F_p^12; curve-standard `Fp12`', 'M'),
    'BNP': ('Bn254G1', '1', 'EIP-197 `G_1`', 'M'),
    'BNP2': ('Bn254G2', '1', 'EIP-197 `G_2`', 'M'),
    'BNP12': ('Bn254Fp12Pair', '4', 'an (x, y) pair over F_p^12; it is both the twisted curve point and `linefunc`\'s (numerator, denominator) result, so a name true of both uses (review B4)', 'M'),
    'BLSF': ('Bls12Fp', '1', 'EIP-2537 BLS12-381 base field; curve-standard `Fp`', 'M'),
    'BLSF2': ('Bls12Fp2', '1', 'EIP-2537; curve-standard `Fp2`', 'M'),
    'BLSF12': ('Bls12Fp12', '1', 'curve-standard `Fp12`', 'M'),
    'BLSP': ('Bls12G1', '1', 'EIP-2537 `G1`', 'M'),
    'BLSP2': ('Bls12G2', '1', 'EIP-2537 `G2`', 'M'),
    'BLSP12': ('Bls12Fp12Pair', '4', 'an (x, y) pair over F_p^12; also `blsLinefunc`\'s (numerator, denominator) result (review B4)', 'M'),
    'BLSJ2': ('Bls12G2Jacobian', '4', 'a G2 point in Jacobian coordinates', 'M'),
}

# Lower-case tokens that head a name part (field names such as `bal`).
LOWER_HEAD = {
    'txs': ('transactions', '1', 'execution-apis block.yaml `transactions`', 'B'),
    'wds': ('withdrawals', '1', 'execution-apis block.yaml `withdrawals`', 'B'),
    'hp': ('hexPrefix', '1', 'Yellow Paper hex-prefix encoding', 'B'),
    'stor': ('storage', '1', 'Yellow Paper account storage', 'B'),
    'acct': ('account', '1', 'follows `Acct` -> `Account`', 'B'),
    'adr': ('address', '1', 'follows `Adr` -> `Address`', 'B'),
    'bal': ('balance', '1, 6', 'execution-apis AccountProof `balance`; `bal` no longer also means block access list', 'B'),
}

# Tokens that apply only inside a module.
MODULE_TOKENS = {
    'Jaune.Fork': {
        'Bal': ('BlockAccessList', '4, 6', 'EIP-7928; `bal` no longer means two things (rule 6)', 'B'),
        'bal': ('blockAccessList', '4, 6', 'EIP-7928; `bal` no longer means two things (rule 6)', 'B'),
        'Txr': ('TransactionRules', '4', 'follows `ForkRules.txr` -> `transactionRules`; `Tx` is retired as a token', 'B'),
        'Sys': ('SystemCalls', '4', 'follows `ForkRules.sys` -> `systemCalls`', 'B'),
        'Settle': ('Settlement', '4', 'follows `ForkRules.settle` -> `settlement`', 'B'),
    },
    'Jaune.T8n': {
        'Bal': ('BlockAccessList', '4, 6', 'EIP-7928; `bal` is retired (rule 6)', 'M'),
        'bal': ('blockAccessList', '4, 6', 'EIP-7928; `bal` is retired (rule 6)', 'M'),
    },
}
MODULE_LOWER_HEAD = {}
DEFAULT_TOKENS = {
    'Bal': ('Balance', '1, 6', 'execution-apis AccountProof `balance`', 'B'),
}
# `Bal` means balance only after `with`/`set`/`add`/`sub` in the account writers;
# everywhere else it is a block access list (Amsterdam), which is left for its cut.
DEFAULT_TOKENS = {}
# Whole-type namespaces whose descendants (fields, constructors, theorems) follow
# a type rename even when their own family is reshaped.
KEPT_TYPES = {
    'Acct', 'Adr', 'Stor', 'Tra', 'B256', 'B128', 'BLT', 'BLTs', 'NTB', 'NTBs', 'Tx', 'TxType', 'Auth',
    'Rinst', 'Jinst', 'Linst', 'Ninst', 'Xinst', 'Inst', 'InstType', 'Instrs',
    'BNF', 'BNF2', 'BNF12', 'BNP', 'BNP2', 'BNP12', 'BLSF', 'BLSF2', 'BLSF12', 'BLSP', 'BLSP2', 'BLSP12', 'BLSJ2',
    'TxRules', 'PowRules', 'BalRules', 'PrecompResult', 'Dead',
}

# A whole segment renamed as a namespace, while the token stays elsewhere.
SEGMENT_EXACT = {
    'PowRules': ('ProofOfWorkRules', '4, 6', 'follows `ForkRules.pow` -> `proofOfWork`; `pow` also means power (rule 6)', 'M'),
}

# Namespace moves that change depth (the apply tool refuses these today).
PREFIX = {
    'Jaune.BLT': ('Jaune.Rlp.Item', '1', 'the RLP definition speaks of items', 'B'),
    'Jaune.BLTs': ('Jaune.Rlp.Items', '1', 'plural of `Rlp.Item`', 'M'),
}

# A name carrying one of these tokens belongs to a reshaped record; it is left
# for its cut.  Whole segments (namespaces, types) of the same kind are listed too.
OUT_TOKENS = {'Msg', 'Sevm', 'Devm', 'Mach', 'Meta', 'Benv', 'Tenv', 'Evm', 'BenvStat', 'TenvStat', 'MsgCallOutput'}
OUT_SEGMENTS = {
    'World', 'Execution', 'Exec', 'exec', 'Frame', 'Step', 'Resume', 'XStep', 'Xlot', 'Mem', 'BlockOutput',
    'FrameEntry', 'Fueled', 'Meta', 'Mach', 'Sevm', 'Devm', 'Benv', 'Tenv', 'Evm', 'Msg',
}
# Wire-type namespaces: their codecs are K2 even where the survey's line ranges say otherwise.
WIRE_ROOTS = {'BlockAccessList', 'Receipt', 'Header', 'Block', 'Withdrawal', 'Log', 'Tx', 'TxType', 'Auth', 'AccessList',
              'Fork', 'ForkRules', 'HeaderOptionals'}
# Modules the survey sorted whole (classify.py WHOLE), for constants it did not list.
MODULE_FAMILY = {
    'Jaune.Basic': 'K6', 'Jaune.RlpEval': 'K6', 'Jaune.WordFacts': 'K6', 'Jaune.MulDiv': 'K6', 'Jaune.RPow': 'K6',
    'Jaune.Fork': 'K5', 'Jaune.Hash': 'K7', 'Jaune.SHA256Spec': 'K7', 'Jaune.KeccakSpec': 'K7',
    'Jaune.RIPEMD160Spec': 'K7', 'Jaune.Blake2Spec': 'K7', 'Jaune.EC': 'R15', 'Jaune.BLS': 'R15',
    'Jaune.BLSConst': 'R15', 'Jaune.Precompiles': 'R15', 'Jaune.NativePrecompile': 'R15',
}

# Survey families (goal Appendix A) whose names this map renames.
IN_FAMILIES = {'K1', 'K2', 'K3', 'K4', 'K5', 'K6', 'K7', 'K8', 'A', 'R15'}
ADAPTER_MODULES = {
    'Jaune.T8n', 'Jaune.ChainStore', 'Jaune.FixtureTransition', 'Jaune.FixtureException',
    'Jaune.Trace', 'Jaune.TraceJson', 'Jaune.TraceTransaction', 'Jaune.BLSGuards', 'Main',
}
# Modules whose unclassified names are in scope though the survey did not sort them.
EXTRA_IN_MODULES = ADAPTER_MODULES | {'Jaune.NativePrecompile'}

# ---------------------------------------------------------------------------
# Explicit rows.  Keys are full old names; value = (new, rule, source, status,
# notes).  `J(x)` abbreviates `Jaune.x`.
# ---------------------------------------------------------------------------
def J(x):
    return 'Jaune.' + x


_EIP_API = 'execution-apis transaction.yaml'
EXPLICIT = {}


def explicit(old, new, rule, source, status, notes=''):
    EXPLICIT[J(old)] = (J(new), rule, source, status, notes)


# -- transactions (Appendix B) ------------------------------------------------
explicit('Tx.gas', 'Transaction.gasLimit', '2', 'user decision 8 (2026-11-15): EIP payloads say `gas_limit`; JSON-RPC says `gas`', 'B',
         'JSON-RPC `gas`, EIP payload `gas_limit`; record both spellings in the doc comment')
for old, new, eip in [('zero', 'legacy', 'Legacy transaction'), ('one', 'eip2930', 'EIP-2930 transaction'),
                      ('two', 'eip1559', 'EIP-1559 transaction'), ('three', 'eip4844', 'EIP-4844 transaction'),
                      ('four', 'eip7702', 'EIP-7702 transaction')]:
    explicit('TxType.' + old, 'TransactionType.' + new, '1',
             f'{_EIP_API} schema title "{eip}"', 'B', 'constructor')
explicit('BlockOutput.bal', 'BlockOutput.blockAccessListBuilder', '4, 6', 'EIP-7928 block access list; `bal` is retired (rule 6); the field holds the `BalBuilder` (the sibling field `blockAccessList` holds the built list), so it takes the builder name', 'M', 'field of a reshaped record (`BlockOutput`, W2); only the leaf changes')
explicit('natBLT', 'natRlpItem', '1', 'follows `BLT` -> `Rlp.Item`', 'M')
explicit('BlockAccessList.toBLT', 'BlockAccessList.toRlpItem', '1, 7', 'follows `BLT` -> `RlpItem` (the RLP definition speaks of items, Yellow Paper Appendix B), as its siblings `BlockAccessListAccountChanges.toRlpItem` and `Block.toRlpItem` (G0a landing review, finding 18)', 'M')
explicit('RIPEMD160.Spec.mMsg', 'RIPEMD160.Spec.mMessageDigest', '5', 'the RIPEMD-160 paper\'s test message "message digest" (audit: not a bare `Message`)', 'M')
explicit('RIPEMD160.Spec.dMsg', 'RIPEMD160.Spec.dMessageDigest', '5', 'the digest of the test message "message digest"', 'M')
explicit('B256.Nof', 'U256.AddNoOverflow', '5', 'predicate: the sum of two words stays below 2^256 (review S2); Prop-valued defs are UpperCamelCase', 'M')
explicit('B256.Nofm', 'U256.MulNoOverflow', '5', 'predicate: the product of two words stays below 2^256 (review S2)', 'M')
explicit('B256.Slt', 'U256.SignedLt', '1', 'EVM SLT: two\'s-complement less-than (review S2); Prop-valued defs are UpperCamelCase', 'M')
explicit('B256.Sgt', 'U256.SignedGt', '1', 'EVM SGT: two\'s-complement greater-than (review S2)', 'M')
explicit('instDecidableSlt', 'instDecidableSignedLt', '7', 'auto name Lean derives from `Decidable (U256.SignedLt ..)`', 'M')
explicit('instDecidableSgt', 'instDecidableSignedGt', '7', 'auto name Lean derives from `Decidable (U256.SignedGt ..)`', 'M')
explicit('Acct.withBal', 'Account.withBalance', '1', 'follows `Acct.bal` -> `Account.balance` (execution-apis AccountProof `balance`)', 'B')
explicit('Tx.isTypeThree', 'Transaction.isEip4844', '1, 7', f'{_EIP_API} schema title "EIP-4844 transaction"', 'M',
         'follows the constructor rename `TxType.three` -> `eip4844`')
explicit('TxType.receiver?', 'TransactionType.to?', '1, 7', f'{_EIP_API} `to`', 'M', 'accessor of the constructor parameter `receiver` -> `to`')
explicit('Tx.auths', 'Transaction.authorizationList', '1', f'{_EIP_API} `authorizationList`; EIP-7702', 'B', 'accessor of the constructor parameter `auths`')

# Constructor parameters of `TxType` (binder names, not constants): the key is
# `TxType.<constructor>.<parameter>`.  The apply tool resolves binders by
# identity; the map names them by this qualified path.
_PARAMS = {
    'receiver': ('to', f'{_EIP_API} `to`'),
    'maxFee': ('maxFeePerGas', f'{_EIP_API} `maxFeePerGas`; EIP-1559'),
    'maxPriorityFee': ('maxPriorityFeePerGas', f'{_EIP_API} `maxPriorityFeePerGas`; EIP-1559'),
    'maxBlobFee': ('maxFeePerBlobGas', f'{_EIP_API} `maxFeePerBlobGas`; EIP-4844'),
    'blobHashes': ('blobVersionedHashes', f'{_EIP_API} `blobVersionedHashes`; EIP-4844'),
    'auths': ('authorizationList', f'{_EIP_API} `authorizationList`; EIP-7702'),
}
TXTYPE_PARAMS = {
    'zero': ['receiver'],
    'one': ['receiver'],
    'two': ['maxFee', 'maxPriorityFee', 'receiver'],
    'three': ['maxFee', 'maxPriorityFee', 'maxBlobFee', 'blobHashes', 'receiver'],
    'four': ['maxFee', 'maxPriorityFee', 'receiver', 'auths'],
}
_CTOR = {'zero': 'legacy', 'one': 'eip2930', 'two': 'eip1559', 'three': 'eip4844', 'four': 'eip7702'}
for c, params in TXTYPE_PARAMS.items():
    for p in params:
        new, src = _PARAMS[p]
        explicit(f'TxType.{c}.{p}', f'TransactionType.{_CTOR[c]}.{new}', '1', src, 'B',
                 'constructor parameter (binder), not a constant: the tool needs a binder key')

# -- header, block, withdrawal, receipt (Appendix B) ---------------------------
explicit('Header.txsRoot', 'Header.transactionsRoot', '1', 'execution-apis block.yaml `transactionsRoot`', 'B')
explicit('Header.receiptRoot', 'Header.receiptsRoot', '1', 'execution-apis block.yaml `receiptsRoot`; Engine API ExecutionPayloadV1 `receiptsRoot`', 'B')
explicit('Header.bloom', 'Header.logsBloom', '1', 'execution-apis block.yaml `logsBloom`; Engine API `logsBloom`', 'B')
explicit('Withdrawal.globalIndex', 'Withdrawal.index', '1', 'EIP-4895 `index`; execution-apis withdrawal.yaml `index`', 'B')
explicit('Withdrawal.recipient', 'Withdrawal.address', '1', 'EIP-4895 `address`; execution-apis withdrawal.yaml `address`', 'B')
explicit('Receipt.succeeded', 'Receipt.status', '1', 'EIP-658 `status`; execution-apis receipt.yaml `status`', 'B',
         'a `Bool` is exact: Jaune forks start at Byzantium where EIP-658 replaced the intermediate state root; say so in the doc comment')
explicit('Receipt.gasUsed', 'Receipt.cumulativeGasUsed', '1, 6', 'execution-apis receipt.yaml `cumulativeGasUsed`', 'B',
         'meaning checked: `makeReceipt` is given the cumulative gas of the block so far (EELS `cumulative_gas_used`)')
explicit('Receipt.bloom', 'Receipt.logsBloom', '1', 'execution-apis receipt.yaml `logsBloom`', 'B')
explicit('receiptRoot', 'receiptsRoot', '1, 7', 'follows `Header.receiptRoot` -> `receiptsRoot` (execution-apis block.yaml)', 'M')

# -- opcode classes ------------------------------------------------------------
explicit('Inst.last', 'Op.halt', '4', 'Appendix B: `Op`\'s constructors are `next`, `jump`, `halt`', 'B')
explicit('Ninst.reg', 'NextOp.plain', '4, 6', 'follows `Rinst` -> `PlainOp` (the constructor carries a `PlainOp`)', 'M')
explicit('Ninst.exec', 'NextOp.message', '4, 6', 'follows `Xinst` -> `MessageOp` (the constructor carries a `MessageOp`)', 'M')
for old, new in [('R', 'plain'), ('X', 'message'), ('J', 'jump'), ('L', 'halt'), ('P', 'push')]:
    explicit('InstType.' + old, 'OpClass.' + new, '5', 'whole words for the five classes of an opcode byte (`PlainOp`, `MessageOp`, `JumpOp`, `HaltOp`, push)', 'M',
             'constructor; single-letter private forms')
explicit('instStarts', 'opStarts', '5, 7', 'follows `Inst` -> `Op`', 'M')
explicit('instStartAt', 'opStartAt', '5, 7', 'follows `Inst` -> `Op`', 'M')

# -- trie builder ----------------------------------------------------------------
for d in '0123456789ABCDEF':
    explicit('NTBs.x' + d, 'TrieBranches.child' + d, '4', 'one field per nibble: the child builder under that nibble', 'M',
             'field; `x0`..`xF` are private short forms')
explicit('hp', 'hexPrefix', '1', 'Yellow Paper Appendix C hex-prefix encoding `HP`', 'B', 'from memory in Appendix B; source not yet re-verified')
explicit('hpAux', 'hexPrefixAux', '1, 7', 'follows `hp` -> `hexPrefix`', 'B')

# -- qualified descendants spelled in source (G0a whole-tree plan) ---------------------
# A renamed type's spelled descendant needs its own row. These two were left for their
# cut by token; `machMeta` keeps retired tokens (`Mach`, `Meta`) until W3, so the
# theorem's leaf says what it states in plain words instead.
explicit('Rinst.balanceCore_machMetaResultGas', 'PlainOp.balanceCore_resultGasLe', '4, 7',
         'follows `Rinst` -> `PlainOp`; leaf in plain words (the gas left by `balanceCore` is at most the gas before), since `machMetaResultGas` keeps the retired `Mach`/`Meta` tokens until its W3 cut', 'M',
         'G0a map gap (jsn-u9): spelled qualified descendant of a renamed type')
explicit('T8n.TxParseError.render', 'T8n.TransactionParseError.render', '7',
         'follows `TxParseError` -> `TransactionParseError` (rule 7: descendants follow their definitions)', 'B',
         'G0a map gap (jsn-u9): spelled qualified descendant of a renamed type')

# -- namespace moves of accepted functions (Appendix B) ----------------------------
explicit('calculateIntrinsicCost', 'Transaction.intrinsicGas', '1, 7', 'Yellow Paper intrinsic gas g_0; rule 7 namespaces replace verb prefixes', 'B',
         'depth change (new namespace member); the apply tool refuses namespace-depth changes today')
explicit('calculateExcessBlobGas', 'calcExcessBlobGas', '1', 'EIP-4844 `calc_excess_blob_gas` (verified in the EIP text)', 'B')
explicit('calculateBlobGasPrice', 'getBaseFeePerBlobGas', '1', 'EIP-4844 `get_base_fee_per_blob_gas` (verified in the EIP text)', 'M',
         'meaning: the per-blob-gas price from excess blob gas, as EIP-4844 defines it')
explicit('calculateTotalBlobGas', 'getTotalBlobGas', '1', 'EIP-4844 `get_total_blob_gas` (verified in the EIP text)', 'M')
explicit('getLast256BlockHashes', 'BlockChain.recentBlockHashes', '4, 7', 'Appendix B proposal', 'B',
         'depth change (new namespace member); the apply tool refuses namespace-depth changes today')
explicit('Dead', 'State.isDead', '1, 7', 'EIP-161 (dead account: nonexistent or empty); rule 7 namespace', 'B',
         'depth change (new namespace member)')
explicit('instDecidableDead', 'instDecidableIsDead', '7', 'auto name Lean derives from `Decidable (State.isDead w a)`', 'M', 'authored instance; the name is Lean-generated')
explicit('Acct.Empty', 'Account.isEmpty', '1, 7', 'EIP-161 (empty account)', 'B')
explicit('initCodeCost', 'initcodeCost', '1', 'EIP-3860 `initcode_cost(initcode)`: a function of the initcode, so it stays out of the `Gas` constants (review B7); `gasInitCodeWordCost` is the constant `INITCODE_WORD_COST`', 'M')

# -- fork rules (Appendix B, decision-listed) -----------------------------------------
# Each field is named for the record it holds (review B9: one real source per row).
for old, new, rule, src in [
    ('txr', 'transactionRules', '4', 'holds a `TxRules` (now `TransactionRules`: max type, calldata floor, warm coinbase; EIP-1559/2930/4844/7623 transaction-format rules); `tx` already names the `TransactionLimits` field, and `txRules` read as a limit (review S5; Appendix B proposed `txRules`)'),
    ('sys', 'systemCalls', '4', 'holds a `SystemCallRules`: which system calls run (EIP-4788 beacon roots, EIP-2935 history storage; `SYSTEM_ADDRESS`)'),
    ('settle', 'settlement', '4', 'holds a `SettlementRules`: refund quotient (EIP-3529), selfdestruct (EIP-6780), touched-account sweep (EIP-161)'),
    ('op', 'opcodes', '4', 'holds an `OpcodeRules`: which opcodes exist at the fork (EIP-145 shifts, EIP-1153, EIP-3855 PUSH0, EIP-5656 MCOPY, ...)'),
    ('pow', 'proofOfWork', '4, 6', 'holds a `PowRules`: block reward and difficulty-bomb delay (EIP-649/1234/2384; ends at Paris, EIP-3675); `pow` also means power (rule 6)'),
    ('bal', 'blockAccessListRules', '4, 6', 'holds a `BalRules` (now `BlockAccessListRules`: item cost, EIP-7928); `bal` also meant balance (rule 6); the `Rules` suffix keeps the field from reading as a block access list payload (review S5; Appendix B proposed `blockAccessList`)'),
]:
    explicit('ForkRules.' + old, 'ForkRules.' + new, rule, src, 'M' if old in ('txr', 'bal') else 'B')
explicit('ForkRules.balValid', 'ForkRules.blockAccessListRulesValid', '4, 6', 'follows `ForkRules.bal` -> `blockAccessListRules`', 'M')
explicit('ForkRules.Valid.bal', 'ForkRules.Valid.blockAccessListRules', '4, 6', 'follows `ForkRules.bal` -> `blockAccessListRules`', 'M')
explicit('ForkRules.Valid.bal_iff_header', 'ForkRules.Valid.blockAccessListRules_iff_header', '4, 6', 'follows `ForkRules.bal` -> `blockAccessListRules`', 'M')
explicit('ForkRules.isPrecomp', 'ForkRules.isPrecompile', '1', 'Appendix B `isPrecomp` -> `isPrecompile`', 'B')
explicit('instDecidableBalValid', 'instDecidableBlockAccessListRulesValid', '7', 'auto name Lean derives from `Decidable (ForkRules.blockAccessListRulesValid ..)`', 'M')
explicit('instDecidableIsPrecomp', 'instDecidableIsPrecompile', '1, 7', 'follows `ForkRules.isPrecomp` -> `isPrecompile`', 'B')
explicit('ForkRules.postBalDefect?', 'ForkRules.postBlockAccessListDefect?', '4, 6', 'follows `ForkRules.bal` -> `blockAccessListRules`', 'M')

# -- gas constants under one `Gas` vocabulary (Appendix B) -----------------------------
# new leaf, rule, source
_YP = 'Yellow Paper Appendix G fee schedule'
_GAS = [
    ('gHigh', 'high', '1', _YP + ' G_high (tier word)'),
    ('gMid', 'mid', '1', _YP + ' G_mid (tier word)'),
    ('gLow', 'low', '1', _YP + ' G_low (tier word)'),
    ('gVerylow', 'veryLow', '1', _YP + ' G_verylow (tier word)'),
    ('gBase', 'base', '1', _YP + ' G_base (tier word)'),
    ('gJumpdest', 'jumpdest', '1', _YP + ' G_jumpdest'),
    ('gExp', 'exp', '1', _YP + ' G_exp'),
    ('gExpbyte', 'expByte', '1', _YP + ' G_expbyte'),
    ('gMemory', 'memory', '1', _YP + ' G_memory'),
    ('gKeccak256', 'keccak256', '1', _YP + ' G_keccak256'),
    ('gasKeccak256Word', 'keccak256Word', '1', _YP + ' G_keccak256word'),
    ('gasCopy', 'copy', '1', _YP + ' G_copy'),
    ('gReturnDataCopy', 'returnDataCopy', '1', _YP + ' G_copy (applied to RETURNDATACOPY)'),
    ('gBlockhash', 'blockhash', '1', _YP + ' G_blockhash'),
    ('gLog', 'log', '1', _YP + ' G_log'),
    ('gLogdata', 'logData', '1', _YP + ' G_logdata'),
    ('gLogtopic', 'logTopic', '1', _YP + ' G_logtopic'),
    ('gNewAccount', 'newAccount', '1', _YP + ' G_newaccount'),
    ('gCallStipend', 'callStipend', '1', _YP + ' G_callstipend; EIP-8037 `GAS_CALL_STIPEND`'),
    ('gasCallValue', 'callValue', '1', _YP + ' G_callvalue'),
    ('gasCreate', 'create', '1', _YP + ' G_create; EIP-8037 `GAS_CREATE`'),
    ('gasCodeDeposit', 'codeDeposit', '1', _YP + ' G_codedeposit; EIP-8037 `GAS_CODE_DEPOSIT`'),
    ('gasSelfDestruct', 'selfdestruct', '1', _YP + ' G_selfdestruct'),
    ('gasSelfDestructNewAccount', 'selfdestructNewAccount', '4', 'G_newaccount charged by SELFDESTRUCT (geth `CreateBySelfdestructGas`)'),
    ('txBaseCost', 'transaction', '1', _YP + ' G_transaction'),
    ('txCreateCost', 'txCreate', '1', _YP + ' G_txcreate'),
    ('rSClear', 'storageClearRefund', '1', _YP + ' R_sclear; matches the rule field `GasSchedule.storageClearRefund`'),
    ('gasColdSload', 'coldSloadCost', '1', 'EIP-2929 `COLD_SLOAD_COST` (verified)'),
    ('gasColdAccountAccess', 'coldAccountAccessCost', '1', 'EIP-2929 `COLD_ACCOUNT_ACCESS_COST` (verified)'),
    ('gasWarmAccess', 'warmStorageReadCost', '1', 'EIP-2929 `WARM_STORAGE_READ_COST` (verified)'),
    ('gasStorageSet', 'sstoreSetGas', '1', 'EIP-2200 `SSTORE_SET_GAS` = 20000, unchanged by EIP-2929 (verified in both texts)'),
    ('gasStorageUpdate', 'sstoreResetGas', '2', 'user decision jsn-g0b-packet-user (2026-11-17): EIP-2200 `SSTORE_RESET_GAS` = 5000, the same suffix as `sstoreSetGas`. EIP-2929 redefines `SSTORE_RESET_GAS` as 5000 - COLD_SLOAD_COST = 2900, which is how Jaune charges it from Berlin (`sstoreResetGas - coldSloadCost`); Yellow Paper `G_sreset` (5000 before Berlin, 2900 from Berlin); EELS `GAS_STORAGE_UPDATE` (older layout), `GasCosts.COLD_STORAGE_WRITE` (pin e27f097e); geth `SstoreResetGasEIP2200`; revm `SSTORE_RESET` (G0b packet; supersedes review B1)'),
    ('gasInitCodeWordCost', 'initcodeWordCost', '1', 'EIP-3860 `INITCODE_WORD_COST` (verified)'),
    ('standardCallDataTokenCost', 'standardTokenCost', '1', 'EIP-7623 `STANDARD_TOKEN_COST` (verified)'),
    ('floorCalldataCost', 'totalCostFloorPerToken', '1', 'EIP-7623 `TOTAL_COST_FLOOR_PER_TOKEN` (verified)'),
    ('txAccessListAddressCost', 'accessListAddressCost', '1', 'EIP-2930 `ACCESS_LIST_ADDRESS_COST` (verified)'),
    ('txAccessListStorageKeyCost', 'accessListStorageKeyCost', '1', 'EIP-2930 `ACCESS_LIST_STORAGE_KEY_COST` (verified)'),
    ('perAuthBaseCost', 'perAuthBaseCost', '1', 'EIP-7702 `PER_AUTH_BASE_COST` (verified)'),
    ('perEmptyAccountCost', 'perEmptyAccountCost', '1', 'EIP-7702 `PER_EMPTY_ACCOUNT_COST` (verified)'),
    ('gasPerBlob', 'perBlob', '1', 'EIP-4844 `GAS_PER_BLOB` (verified)'),
    ('gHashopcode', 'hashOpcodeGas', '1', 'EIP-4844 `HASH_OPCODE_GAS` (verified; the BLOBHASH cost)'),
    ('gasEcrecover', 'ecrecover', '1', _YP + ' (ECRECOVER precompile cost 3000)'),
    ('gasP256Verify', 'p256Verify', '3', 'EIP-7951: P256VERIFY costs 6900 gas (verified); the EIP names no constant'),
    ('gasBlake2PerRound', 'gfround', '1', 'EIP-152 `GFROUND` = 1 gas per round (verified)'),
]
GAS_LEAVES = {}
for old, new, rule, src in _GAS:
    explicit(old, 'Gas.' + new, rule, src,
             'B' if (rule == '1' and 'EIP' in src) or src.startswith('user decision') else 'M',
             'depth change (new `Gas` namespace member)')
    GAS_LEAVES[old] = new

# Functions that move under a namespace; theorems named from them follow.
RELOCATE = {
    'calculateIntrinsicCost': 'Transaction.intrinsicGas',
    'getLast256BlockHashes': 'BlockChain.recentBlockHashes',
    'Dead': 'State.isDead',
    'initCodeCost': 'initcodeCost',
}

# Parts spelled by an EIP verbatim keep their tokens (rule 1 beats rule 5 when the
# token is not retired): `PER_AUTH_BASE_COST`, `STATE_BYTES_PER_AUTH_BASE`.
VERBATIM_PARTS = ('perAuthBase', 'PerAuthBase', 'AuthBase', 'authBase')

# Auto-generated instance names use only the last component of a type's name
# (verified with Lean 4.35: `instance : DecidableEq Rlp.Item` is `instDecidableEqItem`).
INSTANCE_TOKENS = {
    'BLT': 'Item',
    'BLTs': 'Items',
}

EXPLICIT_LEAVES = {old.split('.')[-1] for old in EXPLICIT}

# Block access list (EIP-7928; EELS `BlockAccessListBuilder`, `AccountData`,
# `AccountChanges`) names.  Master directive (2026-11-16): all `Bal*`/`bal*`
# declarations of the block access list are kept-family names and get whole
# words.  `Bal` in `getBal`/`setBal`/`addBal`/`subBal`/`withBal` and the `_bal`
# theorem suffixes means balance and is NOT matched here.
import re as _re
BAL_PATTERNS = [
    (_re.compile(r'(?<![A-Za-z])bal(?=(Read|Pipeline|Guard|Valid|Header))'), 'blockAccessList'),
    (_re.compile(r'Bal(?=(Rules|Account|IndexStart|Builder|Valid|ItemCost|HeaderMismatch|Defect|Hi|Lo|Hash|Read))'), 'BlockAccessList'),
]
BAL_SOURCE = ('EIP-7928 block access list; EELS `BlockAccessListBuilder` (`BalBuilder`), `AccountData` (`BalAccount`), '
              '`AccountChanges` (`BalAccountChanges`); `bal` is retired (rule 6: it also meant balance)')

# Raw-name rows (declarations outside the `Jaune` namespace, in `Main.lean`).
def explicit_raw(old, new, rule, source, status, notes=''):
    EXPLICIT[old] = (new, rule, source, status, notes)


for old, new, why in [('net', 'network', 'the `--network` selection'), ('testIdx', 'testIndex', 'the `--test-idx`-style case index'),
                      ('incls', 'includes', 'the include filters (`--name`)'), ('excls', 'excludes', 'the exclude filters')]:
    explicit_raw('FixtureOpts.' + old, 'FixtureOptions.' + new, '5', f'whole word: {why} (review S1)', 'M', 'field')

# Snake-case parts of theorem names built from renamed predicates.
PART_RENAMES = {'nof': 'add_no_overflow', 'nofm': 'mul_no_overflow'}
EXPLICIT_LEAVES = {old.split('.')[-1] for old in EXPLICIT}


# Generated constants that downstream proofs spell (Blanc uses `Jaune.Acct.ext`), whose parent is
# renamed: `@[ext]` lemmas follow their structure. Only spelled generated names get rows (N4
# matches the rest by graph).
GENERATED_ROWS = {
    J('Acct.ext'): (J('Account.ext'), '7', 'follows `Acct` -> `Account` (the `@[ext]` lemma of the structure)', 'B'),
    J('Acct.ext_iff'): (J('Account.ext_iff'), '7', 'follows `Acct` -> `Account` (the `@[ext]` lemma of the structure)', 'B'),
}
