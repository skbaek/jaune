#!/usr/bin/env python3
"""Generate the execution- and adapter-layer rows of scripts/naming-map.json.

Usage: gen_execution_map.py INVENTORY.tsv [--out MAP.json] [--report DIR]
"""
import argparse
import bisect
import collections
import csv
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import naming_rules as R  # noqa: E402


def load_inventory(path):
    rows = []
    for line in open(path):
        mod, num, kind, flags, name, authored, referenced = line.rstrip('\n').split('\t')
        rows.append(dict(mod=mod, line=int(num), kind=kind, flags=flags, name=name,
                         authored=authored == 'y', referenced=referenced == 'y'))
    return rows


def strip(n):
    return n[6:] if n.startswith('Jaune.') else n


def load_families():
    surv, lines = {}, collections.defaultdict(list)
    for r in csv.DictReader(open(HERE / 'survey-families.tsv'), delimiter='\t'):
        mod = r['module'][:-5].replace('/', '.')
        surv[(mod, strip(r['name']))] = r['family']
        lines[mod].append((int(r['line']), r['family']))
    for mod in lines:
        lines[mod].sort()
    return surv, lines


def family(c, surv, lines, byname):
    """Survey family of a constant, or `N` when only its name can decide."""
    import rename_tables as T
    name = strip(c['name'])
    if name.split('.')[0] in T.WIRE_ROOTS:
        return 'K2'
    key = (c['mod'], name)
    if key in surv:
        return surv[key]
    if c['kind'] in ('field', 'ctor'):
        parent = name.rsplit('.', 1)[0]
        if (c['mod'], parent) in surv:
            return surv[(c['mod'], parent)]
    if c['mod'] in T.MODULE_FAMILY and c['kind'] != 'thm':
        return T.MODULE_FAMILY[c['mod']]
    return 'N'


import rename_tables as T  # noqa: E402

sys.path.insert(0, str(HERE.parent))
import importlib.util  # noqa: E402
_spec = importlib.util.spec_from_file_location('check_naming_map', HERE.parent / 'check-naming-map.py')
CHECK = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(CHECK)
RETIRED = json.load(open(HERE.parent / 'naming-map.json'))['retired_tokens']

PRIVATE = re.compile(r'^_private\.')


def tables_for(mod):
    tokens = dict(T.DEFAULT_TOKENS)
    tokens.update(T.TOKENS)
    tokens.update(T.MODULE_TOKENS.get(mod, {}))
    lower = dict(T.LOWER_HEAD)
    lower.update(T.MODULE_LOWER_HEAD.get(mod, {}))
    return tokens, lower


def bal_part(part, applied):
    new = part
    for rx, repl in T.BAL_PATTERNS:
        new = rx.sub(repl, new)
    if new != part:
        applied.append((part, (new, '4, 6', T.BAL_SOURCE, 'M')))
    return new


def has_bal(name):
    return any(rx.search(part) for seg in name.split('.') for part in seg.split('_') for rx, _ in T.BAL_PATTERNS)


def rename_part(part, tokens, lower, applied):
    out = []
    part = bal_part(part, applied)
    if any(v in part for v in T.VERBATIM_PARTS):
        return part
    is_instance = part.startswith('inst') and len(part) > 4 and part[4].isupper()
    for k, token in enumerate(R.split_part(part)):
        if is_instance and token in T.INSTANCE_TOKENS:
            spec = (T.INSTANCE_TOKENS[token], '7', 'Lean names an instance after the last component of the type', 'B')
            applied.append((token, spec))
            out.append(spec[0])
        elif token in tokens:
            applied.append((token, tokens[token]))
            out.append(tokens[token][0])
        elif k == 0 and token in lower and len(R.split_part(part)) == 1:
            applied.append((token, lower[token]))
            out.append(lower[token][0])
        else:
            out.append(token)
    return ''.join(out)


def rename_segment(seg, tokens, lower, applied, leaf_thm=False):
    if seg in T.SEGMENT_EXACT:
        applied.append((seg, T.SEGMENT_EXACT[seg]))
        return T.SEGMENT_EXACT[seg][0]
    return '_'.join(rename_part(p, tokens, lower, applied) for p in seg.split('_'))


def root_segment(name):
    segs = name.split('.')
    return segs[1] if segs[0] == 'Jaune' and len(segs) > 1 else segs[0]


def kept_root(name, tokens):
    return root_segment(name) in T.KEPT_TYPES


OUT_DEF_PARTS = set()
OUT_DEF_FULL = set()


def init_out_parts():
    """Leaf names of reshaped definitions (survey families R*, K9): a theorem or
    instance that embeds one is named at that definition's cut."""
    kept, out = set(), set()
    kept_full, out_full = set(), set()
    for r in csv.DictReader(open(HERE / 'survey-families.tsv'), delimiter='\t'):
        fam = r['family'].split()[0]
        leaf = strip(r['name']).split('.')[-1]
        (kept if fam in T.IN_FAMILIES else out).add(leaf)
        (kept_full if fam in T.IN_FAMILIES else out_full).add(strip(r['name']))
    OUT_DEF_FULL.update(out_full - kept_full)
    kept_roots = {n.split('.')[0] for n in kept_full}
    OUT_DEF_FULL.update({n.split('.')[0] for n in out_full} - kept_roots - T.KEPT_TYPES)
    for leaf in out - kept:
        if len(leaf) >= 5 and any(ch.isupper() for ch in leaf[1:]) and leaf not in T.EXPLICIT_LEAVES:
            OUT_DEF_PARTS.add(leaf)


def has_out_token(name, mod):
    module_keys = set(T.MODULE_TOKENS.get(mod, {}))
    stripped = strip(name)
    for i, ch in enumerate(stripped):
        if ch == '_' and stripped[:i] in OUT_DEF_FULL:
            return True
    for seg in name.split('.'):
        if seg in T.OUT_SEGMENTS:
            return True
        for part in seg.split('_'):
            if part in OUT_DEF_PARTS:
                return True
            for token in R.split_part(part):
                if token in T.OUT_TOKENS and token not in module_keys:
                    return True
    return False


def derive(c, fam):
    """Return (new, applied, mode) or None when the name is left for its cut."""
    old = c['name']
    mod = c['mod']
    tokens, lower = tables_for(mod)
    f = fam.split()[0]
    bal = has_bal(old)
    kept = kept_root(old, tokens) or bal
    free = f.startswith('F') and not kept
    full = (mod in T.EXTRA_IN_MODULES or f in T.IN_FAMILIES or f == 'N' or kept) and not free
    if free or (has_out_token(old, mod) and not kept):
        return None
    if not full and not any(seg in T.KEPT_TYPES for seg in old.split('.')[:-1]):
        return None
    applied = []
    segs = old.split('.')
    # namespace moves
    for old_prefix, spec in T.PREFIX.items():
        if old == old_prefix or old.startswith(old_prefix + '.'):
            rest = old[len(old_prefix):]
            applied.append((old_prefix, spec))
            new_prefix = spec[0]
            restsegs = [x for x in rest.split('.') if x]
            n = len(restsegs)
            out = []
            for i, seg in enumerate(restsegs):
                if full or i < n - 1:
                    out.append(rename_segment(seg, tokens, lower, applied))
                else:
                    out.append(seg)
            new = new_prefix + ''.join('.' + x for x in out)
            return new, applied, 'full' if full else 'ns'
    # functions that move under a namespace; theorems named from them follow
    leaf = segs[-1]
    for old_leaf, target in T.RELOCATE.items():
        if c['kind'] == 'thm' and leaf.startswith(old_leaf + '_'):
            head = segs[:-1]
            new = '.'.join(head + [target + leaf[len(old_leaf):]])
            applied.append((old_leaf, (target, '1, 7', f'follows `{old_leaf}` -> `{target}`', 'B')))
            return new, applied, 'full'
    n = len(segs)
    out = []
    for i, seg in enumerate(segs):
        if full or (i < n - 1 and seg in T.KEPT_TYPES):
            if c['kind'] == 'thm' and i == n - 1:
                parts = []
                for part in seg.split('_'):
                    if part in T.PART_RENAMES:
                        parts.append(T.PART_RENAMES[part])
                        applied.append((part, (T.PART_RENAMES[part], '5', f'follows the predicate rename (`{part}`)', 'M')))
                    elif part in T.GAS_LEAVES:
                        parts.append(T.GAS_LEAVES[part])
                        applied.append((part, (T.GAS_LEAVES[part], '1, 7', f'follows `{part}` -> `Gas.{T.GAS_LEAVES[part]}`', 'B')))
                    else:
                        parts.append(rename_part(part, tokens, lower, applied))
                out.append('_'.join(parts))
            else:
                out.append(rename_segment(seg, tokens, lower, applied))
        else:
            out.append(seg)
    if c['kind'] == 'thm' and len(segs) == 2 and any(a[0] in T.GAS_LEAVES for a in applied):
        out = [out[0], 'Gas', out[-1]]
    return '.'.join(out), applied, 'full' if full else 'ns'


def kind_of(c):
    return {'field': 'field', 'ctor': 'constructor'}.get(c['kind'], 'declaration')


def layer_of(c):
    return 'adapter' if c['mod'] in T.ADAPTER_MODULES else 'execution'


def merge_rules(rules):
    seen = []
    for r in rules:
        for part in r.split(','):
            part = part.strip()
            if part and part not in seen:
                seen.append(part)
    return ', '.join(sorted(seen, key=int))


def build(rows):
    surv, lines = load_families()
    init_out_parts()
    universe = [c for c in rows if c['authored'] or c['referenced']]
    entries, left = [], []
    for c in universe:
        c['fam'] = family(c, surv, lines, {})
    seen_old = set()
    for c in universe:
        old = c['name']
        if old in seen_old:
            continue
        seen_old.add(old)
        # Auxiliary constants Lean names itself (`instDecidableEqAdr._aux_1`) are not map
        # rows: no source spells them, and N4 matches generated constants by graph.
        if any(seg.startswith('_') for seg in old.split('.')):
            continue
        note_private = '' if old == c['name'] else ''
        if old in T.EXPLICIT:
            new, rule, source, status, notes = T.EXPLICIT[old]
            entries.append(dict(old=old, new=new, kind=kind_of(c), layer=layer_of(c), rule=rule,
                                source=source + f' [{status}]', **({'notes': notes} if notes else {}),
                                _mod=c['mod'], _line=c['line'], _fam=c['fam'].split()[0], _derived=False))
            continue
        res = derive(c, c['fam'])
        if res is None:
            if any(t in T.TOKENS or t in T.LOWER_HEAD for seg in old.split('.') for p in seg.split('_') for t in R.split_part(p)):
                left.append(c)
            continue
        new, applied, mode = res
        if new == old:
            continue
        retired = CHECK.find_retired_tokens(new, RETIRED)
        if retired:
            # The leaf of a reshaped definition inside a renamed namespace keeps a
            # retired token until its cut; the row would be refused, so it waits.
            left.append(c)
            continue
        rules = [a[1][1] for a in applied] + ['7']
        srcs = []
        seen = set()
        for tok, spec in applied:
            key = (tok, spec[0])
            if key in seen:
                continue
            seen.add(key)
            srcs.append(f'`{tok}` -> `{spec[0].split(".")[-1] if spec[0].startswith("Jaune.") else spec[0]}` ({spec[2]}) [{spec[3]}]')
        source = 'Derived by token (rule 7: descendants and theorems follow their definitions): ' + '; '.join(srcs)
        notes = []
        if c['flags'] and 'p' in c['flags']:
            notes.append('private declaration')
        if mode == 'ns':
            notes.append('namespace only: the leaf belongs to a reshaped family and is named at its cut')
        if 'Jaune.Rlp.' in new and not old.startswith('Jaune.Rlp.'):
            notes.append('depth change (new `Rlp` namespace member)')
        entries.append(dict(old=old, new=new, kind=kind_of(c), layer=layer_of(c), rule=merge_rules(rules),
                            source=source, **({'notes': '; '.join(notes)} if notes else {}),
                            _mod=c['mod'], _line=c['line'], _fam=c['fam'].split()[0], _derived=True))
    # generated constants spelled downstream (not in the authored/referenced universe)
    for old, (new, rule, source, status) in T.GENERATED_ROWS.items():
        if old not in seen_old:
            entries.append(dict(old=old, new=new, kind='declaration', layer='execution', rule=rule,
                                source=source + f' [{status}]', notes='generated constant spelled by Blanc',
                                _mod='Jaune.Types', _line=0, _fam='K1', _derived=False))
    # constructor parameters (binders) that are not constants
    for old, (new, rule, source, status, notes) in T.EXPLICIT.items():
        if old not in seen_old:
            entries.append(dict(old=old, new=new, kind='field', layer='execution', rule=rule,
                                source=source + f' [{status}]', notes=notes,
                                _mod='Jaune.Machine', _line=0, _fam='K2', _derived=False))
    return entries, left


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument('inventory')
    ap.add_argument('--out')
    ap.add_argument('--tsv')
    args = ap.parse_args(argv)
    rows = load_inventory(args.inventory)
    entries, left = build(rows)
    entries.sort(key=lambda e: (e['_mod'], e['_line'], e['old']))
    if args.tsv:
        with open(args.tsv, 'w') as f:
            for e in entries:
                f.write('\t'.join([e['_mod'], str(e['_line']), e['_fam'], e['kind'], e['layer'], e['old'], e['new'], e['rule'], 'D' if e['_derived'] else 'X']) + '\n')
    print(f'{len(entries)} rows ({sum(e["_derived"] for e in entries)} derived); {len(left)} constants left for their cut with kept tokens')
    if args.out:
        out = [{k: v for k, v in e.items() if not k.startswith('_')} for e in entries]
        base = json.load(open(args.out))
        kept = [e for e in base['entries'] if e.get('layer') == 'consensus']
        # Keep the order of rows already in the map (consensus first); new rows go last.
        mine = {(e['old'], e['layer']): e for e in out}
        ordered = []
        for e in base['entries']:
            key = (e['old'], e['layer'])
            if e.get('layer') == 'consensus':
                ordered.append(e)
            elif key in mine:
                ordered.append(mine.pop(key))
        base['entries'] = ordered + list(mine.values())
        json.dump(base, open(args.out, 'w'), indent=2)
        open(args.out, 'a').write('\n')


if __name__ == '__main__':
    main()
