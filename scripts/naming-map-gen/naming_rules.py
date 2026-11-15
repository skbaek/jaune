"""Rename engine for the execution-layer and adapter-layer map rows.

Pure data and string functions: no I/O.  `gen_execution_map.py` applies them to
the environment inventory.
"""
import re
import bisect
import collections

# --- tokenisation ----------------------------------------------------------

# Acronym-like tokens that the generic camelCase splitter would cut wrongly.
# Each ends where the next character is not a lower-case letter.
KNOWN = sorted([
    'BLTs', 'BLT', 'NTBs', 'NTB', 'B256s', 'B256', 'B128', 'B64', 'B32s', 'B4L', 'B8L', 'B4', 'B8',
    'BNF12', 'BNF2', 'BNF', 'BNP12', 'BNP2', 'BNP',
    'BLSF12', 'BLSF2', 'BLSF', 'BLSP12', 'BLSP2', 'BLSP', 'BLSJ2',
    'Txs', 'Tx', 'Auths', 'Rinst', 'Jinst', 'Linst', 'Ninst', 'Xinst', 'InstType', 'Instrs', 'Inst',
    'fakeExp', 'FakeExp', 'blobHashes', 'BlobHashes',
], key=len, reverse=True)
GENERIC = re.compile(r"[A-Z]+(?=[A-Z][a-z0-9]|[^A-Za-z0-9]|$)|[A-Z]?[a-z0-9]+|.", re.S)


def split_part(part):
    """Split one underscore-free name part into camelCase tokens."""
    tokens, i = [], 0
    while i < len(part):
        for known in KNOWN:
            end = i + len(known)
            if part.startswith(known, i) and (end == len(part) or not part[end].islower()):
                tokens.append(known)
                i = end
                break
        else:
            match = GENERIC.match(part, i)
            tokens.append(match.group(0))
            i = match.end()
    return tokens


def rename_segment(segment, table, lower_head=None):
    """Apply the token table to one dotted segment.

    `lower_head` maps a lower-case token that heads a segment or an underscore
    part (e.g. the field `bal`); lower-case tokens elsewhere are left alone,
    since a camelCase token inside a word is capitalised.
    """
    out_parts = []
    for p, part in enumerate(segment.split('_')):
        tokens = split_part(part)
        new = []
        for k, token in enumerate(tokens):
            if token in table:
                new.append(table[token])
            elif k == 0 and lower_head and token in lower_head:
                new.append(lower_head[token])
            else:
                new.append(token)
        out_parts.append(''.join(new))
    return '_'.join(out_parts)


def rename_name(name, table, lower_head=None):
    return '.'.join(rename_segment(seg, table, lower_head) for seg in name.split('.'))
