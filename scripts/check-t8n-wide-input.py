#!/usr/bin/env python3
"""`jaune t8n` refuses a quantity too wide for its field; invoked by check-cli.sh.

Each row edits one field of a signed corpus case. Until this gate the frontend
reduced such a value modulo the field's width, so a chain ID of 2^64 + 1 ran as
chain 1 with no error. No golden can pin this: the pinned target ends the run
with `OverflowError` on these inputs, so check-t8n.sh has nothing to compare and
its corpus stays refusal-free. The rows do record what that target did when run
on the same edits, field by field:

  refused    the target exits non-zero
  rejected   the target rejects the transaction and exits 0, with the same root
  same root  the target does not read the field, and writes the case's golden root

The last two kinds keep the refusal from overreaching: a value that fits, a
field a fork never reads and a transaction `--state-test` never selects all run.
Needs the built binary and the committed corpus, and no reference install.
"""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT / 'scripts'))
from t8n_inputs import materialize_alloc  # noqa: E402

CASES = ROOT / 'scripts' / 't8n' / 'cases'

TYPE2 = 'am-transfer-state-test'
TYPE2_BLOCK = 'am-transfer-blockchain'
TYPE4 = 'am-delegation-state-test'
LEGACY = 'transfer-state-test'
PRAGUE_BLOCK = 'transfer-blockchain'
WITHDRAWALS = 'withdrawals'
BERLIN = 'hist-transfer-berlin'

W64 = 2 ** 64
W256 = 2 ** 256


def refused(label, bits, n):
    return 'refused', f't8n {label} is {n}, which does not fit in {bits} bits'


def rejected(identity):
    return 'rejected', identity


SAME_ROOT = ('same root', None)


def tx(field, value):
    def edit(doc):
        doc['txs'][0][field] = hex(value)
    return edit


def second_tx(field, value):
    """Append a copy of the first transaction with one field edited."""
    def edit(doc):
        doc['txs'].append(copy.deepcopy(doc['txs'][0]))
        doc['txs'][1][field] = hex(value)
    return edit


def auth(field, value):
    def edit(doc):
        doc['txs'][0]['authorizationList'][0][field] = hex(value)
    return edit


def env(field, value):
    def edit(doc):
        doc['env'][field] = hex(value)
    return edit


def withdrawal(field, value):
    def edit(doc):
        doc['env']['withdrawals'][0][field] = hex(value)
    return edit


INVALID_CHAINID = 'TransactionException.INVALID_CHAINID'
NONCE_IS_MAX = 'TransactionException.NONCE_IS_MAX'
NO_FUNDS = 'TransactionException.INSUFFICIENT_ACCOUNT_FUNDS'
AUTH_CHAIN = 'txs[0].authorizationList.chainId'

# label, case, edit of the input documents, CLI overrides, expectation
ROWS = [
    # The three inputs of the original finding, and the first value past each.
    ('type-2 chainId 2^64 + 1', TYPE2, tx('chainId', W64 + 1), {}, refused('txs[0].chainId', 64, W64 + 1)),
    ('type-2 chainId 2^64', TYPE2, tx('chainId', W64), {}, refused('txs[0].chainId', 64, W64)),
    ('--state.chainid 2^64 + 1', TYPE2, None, {'chainid': W64 + 1}, refused('--state.chainid', 64, W64 + 1)),
    ('--state.chainid 2^64', TYPE2, None, {'chainid': W64}, refused('--state.chainid', 64, W64)),
    ('authorization chainId 2^256 + 1', TYPE4, auth('chainId', W256 + 1), {}, refused(AUTH_CHAIN, 256, W256 + 1)),
    ('authorization chainId 2^256', TYPE4, auth('chainId', W256), {}, refused(AUTH_CHAIN, 256, W256)),
    # The largest value each of the three holds still reaches its ordinary verdict.
    ('type-2 chainId 2^64 - 1', TYPE2, tx('chainId', W64 - 1), {}, rejected(INVALID_CHAINID)),
    ('--state.chainid 2^64 - 1', TYPE2, None, {'chainid': W64 - 1}, rejected(INVALID_CHAINID)),
    ('authorization chainId 2^256 - 1', TYPE4, auth('chainId', W256 - 1), {}, rejected(NO_FUNDS)),
    # The frontend's other narrowings of a wire quantity.
    ('nonce 2^256', TYPE2, tx('nonce', W256), {}, refused('txs[0].nonce', 256, W256)),
    ('type-2 r 2^256 + 1', TYPE2, tx('r', W256 + 1), {}, refused('txs[0].r', 256, W256 + 1)),
    ('type-2 s 2^256 + 1', TYPE2, tx('s', W256 + 1), {}, refused('txs[0].s', 256, W256 + 1)),
    ('authorization nonce 2^64', TYPE4, auth('nonce', W64), {}, refused('txs[0].authorizationList.nonce', 64, W64)),
    ('authorization r 2^256 + 1', TYPE4, auth('r', W256 + 1), {}, refused('txs[0].authorizationList.r', 256, W256 + 1)),
    ('authorization s 2^256 + 1', TYPE4, auth('s', W256 + 1), {}, refused('txs[0].authorizationList.s', 256, W256 + 1)),
    ('currentTimestamp 2^256 + 1000', TYPE2, env('currentTimestamp', W256 + 1000), {},
     refused('env.currentTimestamp', 256, W256 + 1000)),
    ('currentRandom 2^256 + 1, read', PRAGUE_BLOCK, env('currentRandom', W256 + 1), {},
     refused('env.currentRandom', 256, W256 + 1)),
    ('slotNumber 2^64 + 1, read', TYPE2, env('slotNumber', W64 + 1), {}, refused('env.slotNumber', 64, W64 + 1)),
    ('withdrawal index 2^64 + 1', WITHDRAWALS, withdrawal('index', W64 + 1), {},
     refused('withdrawal index', 64, W64 + 1)),
    ('withdrawal validatorIndex 2^64 + 1', WITHDRAWALS, withdrawal('validatorIndex', W64 + 1), {},
     refused('withdrawal validatorIndex', 64, W64 + 1)),
    ('withdrawal amount 2^64 + 1', WITHDRAWALS, withdrawal('amount', W64 + 1), {},
     refused('withdrawal amount', 64, W64 + 1)),
    ('--state.reward 2^256 + 1, paid', BERLIN, None, {'reward': W256 + 1}, refused('--state.reward', 256, W256 + 1)),
    ('second transaction, block mode', TYPE2_BLOCK, second_tx('chainId', W64 + 1), {},
     refused('txs[1].chainId', 64, W64 + 1)),
    # The target holds a transaction nonce in U256: this is its rejection, not a crash.
    ('type-2 nonce 2^64', TYPE2, tx('nonce', W64), {}, rejected(NONCE_IS_MAX)),
    ('type-2 nonce 2^256 - 1', TYPE2, tx('nonce', W256 - 1), {}, rejected(NONCE_IS_MAX)),
    ('legacy nonce 2^64', LEGACY, tx('nonce', W64), {}, rejected(NONCE_IS_MAX)),
    ('Berlin legacy nonce 2^64', BERLIN, tx('nonce', W64), {}, rejected(NONCE_IS_MAX)),
    # Unedited cases, values that fit, and fields neither tool reads.
    ('type-2 control', TYPE2, None, {}, SAME_ROOT),
    ('type-4 control', TYPE4, None, {}, SAME_ROOT),
    ('withdrawals control', WITHDRAWALS, None, {}, SAME_ROOT),
    ('currentTimestamp 2^256 - 1', TYPE2, env('currentTimestamp', W256 - 1), {}, SAME_ROOT),
    ('slotNumber 2^64 - 1', TYPE2, env('slotNumber', W64 - 1), {}, SAME_ROOT),
    ('legacy chainId 2^64 + 1, unread', LEGACY, tx('chainId', W64 + 1), {}, SAME_ROOT),
    ('slotNumber 2^64 + 1, before Amsterdam', PRAGUE_BLOCK, env('slotNumber', W64 + 1), {}, SAME_ROOT),
    ('currentRandom 2^256 + 1, before the merge', BERLIN, env('currentRandom', W256 + 1), {}, SAME_ROOT),
    ('--state.reward 2^256 + 1, proof of stake', LEGACY, None, {'reward': W256 + 1}, SAME_ROOT),
    ('second transaction, --state-test', TYPE2, second_tx('chainId', W64 + 1), {}, SAME_ROOT),
]


def run_row(binary, case, edit, overrides, work):
    """Run one edited case; the process, and its result document if it wrote one."""
    case_dir = CASES / case
    spec = json.loads((case_dir / 'case.json').read_text())
    doc = {'env': json.loads((case_dir / 'env.json').read_text()),
           'txs': json.loads((case_dir / 'txs.json').read_text())}
    if edit is not None:
        edit(doc)
    materialize_alloc(case_dir, ROOT / 'scripts' / 't8n', work / 'input.alloc.json')
    (work / 'input.env.json').write_text(json.dumps(doc['env']))
    (work / 'input.txs.json').write_text(json.dumps(doc['txs']))
    args = [str(binary), 't8n',
            f"--input.alloc={work / 'input.alloc.json'}",
            f"--input.env={work / 'input.env.json'}",
            f"--input.txs={work / 'input.txs.json'}",
            '--output.result=result.json', '--output.alloc=alloc.json', '--output.body=body.json',
            f"--state.fork={spec['fork']}",
            f"--state.chainid={overrides.get('chainid', spec['chainid'])}",
            f"--state.reward={overrides.get('reward', spec['reward'])}",
            f'--output.basedir={work}']
    if spec['mode'] == 'state-test':
        args.append('--state-test')
    process = subprocess.run(args, capture_output=True, text=True)
    result = work / 'result.json'
    return process, json.loads(result.read_text()) if result.exists() else None


def verdict(row, process, result):
    """Why this row failed, or None."""
    _, case, _, _, (kind, expected) = row
    if kind == 'refused':
        if process.returncode != 1:
            return f'expected a refusal, got exit {process.returncode}'
        if expected not in process.stderr:
            return f'refusal does not say: {expected}; got: {process.stderr.strip()}'
        return 'a refused run wrote a result document' if result is not None else None
    if process.returncode != 0 or result is None:
        return f'expected a run, got exit {process.returncode}: {process.stderr.strip()}'
    if kind == 'rejected':
        got = [entry.get('error') for entry in result.get('rejected', [])]
        return None if got == [expected] else f'expected rejected {[expected]}, got {got}'
    golden = json.loads((CASES / case / 'expected' / 'result.json').read_text())['stateRoot']
    if result['stateRoot'] != golden:
        return f"expected the golden root {golden}, got {result['stateRoot']}"
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', type=Path, required=True)
    binary = parser.parse_args().binary
    failures = 0
    for row in ROWS:
        with tempfile.TemporaryDirectory() as tmp:
            process, result = run_row(binary, row[1], row[2], row[3], Path(tmp))
        reason = verdict(row, process, result)
        if reason is not None:
            failures += 1
            print(f'T8N WIDE — {row[0]}: {reason}')
    if failures:
        print(f'REGRESSION — t8n wide input: {failures} of {len(ROWS)} row(s) failed')
        return 1
    print(f'OK — t8n wide input: {len(ROWS)} rows; out-of-range quantities refused, '
          'values that fit and unread fields unaffected')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
