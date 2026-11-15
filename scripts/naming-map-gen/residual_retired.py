#!/usr/bin/env python3
"""List authored constants whose name still has a retired token after the map.

Usage: residual_retired.py INVENTORY.tsv [MAP.json]
Prints `family<TAB>count` and the names, grouped by survey family.
"""
import collections
import json
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import gen_execution_map as G  # noqa: E402


def main(inventory, map_path=None):
    map_path = map_path or str(HERE.parent / 'naming-map.json')
    data = json.load(open(map_path))
    mapping = {e['old']: e['new'] for e in data['entries']}
    rows = G.load_inventory(inventory)
    surv, lines = G.load_families()
    groups = collections.defaultdict(list)
    for c in rows:
        if not c['authored']:
            continue
        final = mapping.get(c['name'], c['name'])
        hits = G.CHECK.find_retired_tokens(final, data['retired_tokens'])
        if hits:
            fam = G.family(c, surv, lines, {})
            groups[fam.split()[0]].append((final.replace('Jaune.', ''), sorted(set(hits)), c['kind']))
    return groups


if __name__ == '__main__':
    groups = main(*sys.argv[1:3])
    total = sum(len(v) for v in groups.values())
    print(f'{total} authored constants keep a retired token after the map')
    for fam in sorted(groups):
        print(f'== {fam}: {len(groups[fam])}')
        for name, hits, kind in groups[fam]:
            print(f'  {kind[:3]} {name}  {",".join(hits)}')
