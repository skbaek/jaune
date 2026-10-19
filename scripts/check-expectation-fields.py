#!/usr/bin/env python3
"""Focused compiled fixture-ingress controls; invoked by check-cli.sh.

No corpus or reference install is required. This is selector/wiring coverage,
not a second finite campaign for FixtureClosure.score_continue_iff.
"""
import argparse
import copy
import json
from pathlib import Path
import subprocess
import tempfile

# Unchanged checked-genesis/first-import witness from legacytests41404287:
# Cancun/BlockchainTests/InvalidBlocks/bcUncleHeaderValidity/gasLimitLTGasUsageUncle.json
# Berlin case, block0. Only this prefix is used; no ommer/rejection claim follows.
# Source original SHA256: 405935ea21a8ce91a824d56392fa22f50a94335133bb451f271d2cef4834e47f
# This is a hand-authored ingress fixture, not a golden or conformance baseline.
BASE = json.loads(r'''{"blocks": [{"rlp": "0xf90260f901f7a08bb845a80da3e699cb4c212998c14db4f2c49225c8c20df716a5768128076409a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347948888f1f195afa192cfee860698584c030f4c9db1a0f52ec6538593f973eb7bc0990f35185d73cb701c2534ee493f158c919070c7a0a0ffaa3736dfb643087cb20308a8b016ebba03684b555114d6533b5c2f9951e252a0056b23fbba480696b65fe5a59b8f2148a1299103c4f57df839233af2cf4ca2d2b90100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008302000001832fefd88252088203e942a00000000000000000000000000000000000000000000000000000000000000000880000000000000000f863f861808203e88304cb2f94095e7baea6a6c7c4c2dfeb977efac326af552d870a801ba025d49a54362b5ae38cf895fa9a1d3ded6f7d5577e572c9a93cdebff6e33ceaf79f773806df18e22db29acde1dd96c0418e28738af7f520e5e2c5c673494029e5c0"}], "genesisBlockHeader": {"bloom": "0x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000", "coinbase": "0x8888f1f195afa192cfee860698584c030f4c9db1", "difficulty": "0x020000", "extraData": "0x42", "gasLimit": "0x2fefd8", "gasUsed": "0x00", "hash": "0x8bb845a80da3e699cb4c212998c14db4f2c49225c8c20df716a5768128076409", "mixHash": "0x0000000000000000000000000000000000000000000000000000000000000000", "nonce": "0x0000000000000000", "number": "0x00", "parentHash": "0x0000000000000000000000000000000000000000000000000000000000000000", "receiptTrie": "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421", "stateRoot": "0x7dba07d6b448a186e9612e5f737d1c909dce473e53199901a302c00646d523c1", "timestamp": "0x01", "transactionsTrie": "0x56e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421", "uncleHash": "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347"}, "genesisRLP": "0xf901f8f901f3a00000000000000000000000000000000000000000000000000000000000000000a01dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347948888f1f195afa192cfee860698584c030f4c9db1a07dba07d6b448a186e9612e5f737d1c909dce473e53199901a302c00646d523c1a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421a056e81f171bcc55a6ff8345e692c0f86e5b48e01b996cadc001622fb5e363b421b90100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000008302000080832fefd8800142a00000000000000000000000000000000000000000000000000000000000000000880000000000000000c0c0", "lastblockhash": "0xbaf30d600fcc5dd778dfca93407b96a3e9dca3a89147d62917be4bca2f7858a6", "network": "Berlin", "postStateHash": "0xf52ec6538593f973eb7bc0990f35185d73cb701c2534ee493f158c919070c7a0", "pre": {"0xa94f5374fce5edbc8e2a8697c15331677e6ebf0b": {"balance": "0x09184e72a000", "code": "0x", "nonce": "0x00", "storage": {}}}, "sealEngine": "NoProof"}''')
GOOD = 'BlockException.RLP_STRUCTURES_ENCODING'
FOREIGN = 'BlockException.INVALID_LOG_BLOOM'
DETAILS = {'unsupported_field': 'unsupported expectation field: exceptions',
           'multiple_applicable': 'multiple applicable expectation fields',
           'non_string': 'selected expectation field must be a JSON string'}


def check(ok, label):
    if not ok:
        raise AssertionError(label)


def metadata(network, block):
    fields = [{'key': k, 'value': v} for k, v in sorted(block.items())
              if k.startswith('expectException') or k == 'exceptions']
    applicable = [f for f in fields if f['key'] in
                  {'expectException', 'expectExceptionALL', 'expectException' + network}]
    key, raw, tag = None, None, None
    if 'exceptions' in block:
        tag = 'unsupported_field'
    elif len(applicable) > 1:
        tag = 'multiple_applicable'
    elif applicable:
        key, raw = applicable[0]['key'], applicable[0]['value']
        if not isinstance(raw, str):
            tag = 'non_string'
    return {'case_network': network, 'fields': fields, 'applicable': applicable,
            'present': bool(applicable), 'selected_key': key, 'raw': raw,
            'selection_error': None if tag is None else {'tag': tag, 'detail': DETAILS[tag]}}


def fixture(fields=None, network='Berlin', invalid=True):
    case = copy.deepcopy(BASE)
    case['network'] = network
    if invalid:
        case['blocks'].insert(0, dict(rlp='0xc0', **(fields or {})))
    else:
        case['blocks'][0].update(fields or {})
    return case


class Controls:
    def __init__(self, binary, directory):
        self.binary, self.directory, self.count, self.serial = binary, directory, 0, 0

    def run(self, label, cases, *, diagnostic=False, expected_exit=0, needle=None, network='Berlin'):
        self.serial += 1
        path = self.directory / f'{self.serial:02d}.json'
        path.write_text(json.dumps(cases))
        original = path.read_bytes()
        argv = [str(self.binary), str(path), '--network', network]
        report = self.directory / f'{self.serial:02d}.report.json'
        if diagnostic:
            argv += ['--identity-closure', str(report)]
        result = subprocess.run(argv, capture_output=True, text=True, check=False)
        self.count += 1
        check(result.returncode == expected_exit,
              f'{label}: expected exit{expected_exit}, got{result.returncode}; '
              f'stdout={result.stdout!r}; stderr={result.stderr!r}')
        check(path.read_bytes() == original, f'{label}: input bytes changed')
        if needle:
            check(needle in result.stderr, f'{label}: missing strict ingress refusal {needle!r}: {result.stderr!r}')
        if not diagnostic:
            return None
        raw = json.loads(report.read_text())
        check(raw['schema'] == 'jaune-original-identity-closure-v2', f'{label}: schema v2')
        check(raw['input_path'] == str(path) and raw['network_filter'] == network, f'{label}: original/command identity')
        check(len(raw['cases']) == len(cases), f'{label}: all selected cases')
        for index, (key, source) in enumerate(sorted(cases.items())):
            observed = raw['cases'][index]
            check(observed['case_key'] == key and observed['original_case_index_sorted_keys'] == index,
                  f'{label}: original selected key/index')
            check(len(observed['candidates']) == len(source['blocks']), f'{label}: all candidate metadata')
            for block_index, block in enumerate(source['blocks']):
                row = observed['candidates'][block_index]
                expected = metadata(source['network'], block)
                check(json.dumps(row['expectation'], sort_keys=True) == json.dumps(expected, sort_keys=True),
                      f'{label}#{block_index}: exact typed field selection metadata')
        return raw

    def complete(self, label, cases, network='Berlin'):
        self.run(label + ' strict', cases, network=network)
        raw = self.run(label + ' diagnostic', cases, diagnostic=True, network=network)
        for case in raw['cases']:
            check(case['genesis_checks_complete'] and case['case_complete'], f'{label}: complete shared path')
            check(all(row['reached'] for row in case['candidates']), f'{label}: required later rows reached')
            check(case['final_assertions']['post_root_checked'] is True, f'{label}: final assertion reached')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--binary', required=True, type=Path)
    args = parser.parse_args()
    with tempfile.TemporaryDirectory() as temporary:
        tests = Controls(args.binary.resolve(), Path(temporary).resolve())
        tests.complete('modern shared path', {'case': fixture({'expectException': GOOD})})
        tests.complete('ALL ingress wiring', {'case': fixture({'expectExceptionALL': GOOD})})
        # JSON object ordering cannot select the deliberately wrong sibling.
        for reverse in [False, True]:
            fields = [('expectExceptionBerlin', GOOD), ('expectExceptionAmsterdam', FOREIGN)]
            tests.complete(f'selected-network ingress wiring order{reverse}',
                           {'case': fixture(dict(reversed(fields) if reverse else fields))})
        # Active per-block rules are Berlin while the original case label is
        # the whole transition. That original label owns field selection.
        transition = 'BerlinToLondonAt5'
        tests.complete('original transition label wiring', {'case': fixture(
            {'expectException' + transition: GOOD, 'expectExceptionBerlin': FOREIGN}, network=transition)}, network=transition)
        tests.complete('foreign-only isolation', {'case': fixture(
            {'expectExceptionAmsterdam': FOREIGN}, invalid=False)})
        keys = ['expectException', 'expectExceptionALL', 'expectExceptionBerlin']
        conflicts = {}
        for left, right in [(0, 1), (0, 2), (1, 2)]:
            conflicts[f'pair-{left}-{right}'] = fixture({keys[left]: GOOD, keys[right]: GOOD})
        conflicts['three-way'] = fixture(dict.fromkeys(keys, GOOD))
        raw = tests.run('all equal-value applicable conflicts', conflicts, diagnostic=True, expected_exit=1)
        for case in raw['cases']:
            row, suffix = case['candidates']
            check(row['expected_parse']['status'] == 'malformed' and not row['reached'] and
                  row['identity_status'] == 'malformedExpected', 'conflict: refused before evaluation')
            check(not suffix['reached'] and not case['case_complete'] and case['final_assertions'] is None,
                  'conflict: unreached suffix/finals retained')
        tests.run('strict applicable conflict', {'case': conflicts['pair-0-1']}, expected_exit=1,
                  needle='expectation field format error (multiple_applicable)')
        malformed = {}
        for key_index, key in enumerate(keys):
            for value_index, value in enumerate([None, False, 7, [], {}]):
                malformed[f'type-{key_index}-{value_index}'] = fixture({key: value})
        raw = tests.run('selected JSON type table', malformed, diagnostic=True, expected_exit=1)
        check(all(c['genesis_checks_complete'] and not c['case_complete'] and
                  c['candidates'][0]['expected_parse']['status'] == 'malformed' and
                  not c['candidates'][0]['reached'] for c in raw['cases']), 'type table: no evaluation')
        tests.run('strict selected null', {'case': fixture({'expectExceptionALL': None})}, expected_exit=1,
                  needle='expectation field format error (non_string)')
        unsupported = {'case': fixture({'exceptions': ['legacy unsupported'], 'expectExceptionAmsterdam': FOREIGN})}
        raw = tests.run('unsupported legacy field', unsupported, diagnostic=True, expected_exit=1)
        row = raw['cases'][0]['candidates'][0]
        check(raw['cases'][0]['genesis_checks_complete'] and row['identity_status'] == 'malformedExpected' and
              row['expectation']['present'] is False and row['expected_parse']['status'] == 'malformed',
              'unsupported: not permission and not absence')
        tests.run('strict unsupported legacy field', unsupported, expected_exit=1,
                  needle='expectation field format error (unsupported_field)')
        raw = tests.run('selected empty string stays malformed', {'case': fixture({'expectExceptionALL': ''})},
                        diagnostic=True, expected_exit=1)
        row = raw['cases'][0]['candidates'][0]
        check(row['expectation']['selection_error'] is None and row['expectation']['raw'] == '' and
              row['expected_parse']['status'] == 'malformed', 'empty: reader does not normalize/parser remains owner')
        fallback = fixture({'expectExceptionALL': GOOD, 'expectExceptionAmsterdam': FOREIGN})
        del fallback['genesisBlockHeader']
        raw = tests.run('pre-traversal fallback provenance', {'case': fallback}, diagnostic=True, expected_exit=1)
        check(not raw['cases'][0]['genesis_checks_complete'] and
              all(not r['reached'] for r in raw['cases'][0]['candidates']), 'fallback: no invented reached rows')
        print(f'OK — expectation fields: {tests.count} focused native ingress invocations; shared selection and provenance hold')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (AssertionError, OSError, ValueError, KeyError, TypeError) as error:
        print(f'REGRESSION — expectation fields: {error}')
        raise SystemExit(1)
