#!/usr/bin/env python3
"""Compare compiler fidelity exports under a validated one-to-one rename map.

Scope is the explicitly exported modules. Current imports/build receipts and
complete migration coverage are separate obligations; no source is edited.
"""
import argparse
from collections import Counter, defaultdict
import hashlib
import importlib.util
import json
import re
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
# Schema 8 stores per-module level/expr DAG pools, path-free import module
# lists, deterministic equation provenance, and optional --from-olean metadata.
SCHEMAS = (3, 4, 5, 6, 7, 8)
CURRENT_SCHEMA = 8


def load(filename):
    spec = importlib.util.spec_from_file_location(filename, ROOT / 'scripts' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


MAP = load('check-naming-map.py')
APPLY = load('apply-naming-map.py')


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


_NONE_DIGEST = hashlib.sha256(b'N').digest()
_TRUE_DIGEST = hashlib.sha256(b'T').digest()
_FALSE_DIGEST = hashlib.sha256(b'F').digest()


def _atom_digest(x):
    if x is None:
        return _NONE_DIGEST
    if isinstance(x, bool):
        return _TRUE_DIGEST if x else _FALSE_DIGEST
    if isinstance(x, int):
        b = str(x).encode('ascii')
        return hashlib.sha256(b'I' + len(b).to_bytes(8, 'little') + b).digest()
    if isinstance(x, float):
        b = repr(x).encode('ascii')
        return hashlib.sha256(b'R' + len(b).to_bytes(8, 'little') + b).digest()
    if isinstance(x, str):
        b = x.encode('utf-8')
        return hashlib.sha256(b'S' + len(b).to_bytes(8, 'little') + b).digest()
    raise TypeError(f'unsupported dag_digest atom: {type(x).__name__}')


def dag_digest(value):
    """Injective, type-tagged, DAG-memoized structural SHA-256 hex digest."""
    if not isinstance(value, (list, dict)):
        return _atom_digest(value).hex()
    memo = {}
    str_cache = {}
    stack = [(value, False)]
    while stack:
        cur, ready = stack.pop()
        if isinstance(cur, list):
            cid = id(cur)
            if cid in memo:
                continue
            if not ready:
                stack.append((cur, True))
                for x in cur:
                    if isinstance(x, (list, dict)) and id(x) not in memo:
                        stack.append((x, False))
            else:
                h = hashlib.sha256(b'L' + len(cur).to_bytes(8, 'little'))
                for x in cur:
                    if isinstance(x, (list, dict)):
                        h.update(memo[id(x)])
                    elif isinstance(x, str):
                        sd = str_cache.get(x)
                        if sd is None:
                            sb = x.encode('utf-8')
                            sd = hashlib.sha256(b'S' + len(sb).to_bytes(8, 'little') + sb).digest()
                            str_cache[x] = sd
                        h.update(sd)
                    else:
                        h.update(_atom_digest(x))
                memo[cid] = h.digest()
        elif isinstance(cur, dict):
            cid = id(cur)
            if cid in memo:
                continue
            if not ready:
                stack.append((cur, True))
                for v in cur.values():
                    if isinstance(v, (list, dict)) and id(v) not in memo:
                        stack.append((v, False))
            else:
                items = sorted(cur.items())
                h = hashlib.sha256(b'D' + len(items).to_bytes(8, 'little'))
                for k, v in items:
                    kd = str_cache.get(k) if isinstance(k, str) else None
                    if kd is None:
                        kd = _atom_digest(k)
                        if isinstance(k, str):
                            str_cache[k] = kd
                    h.update(kd)
                    h.update(memo[id(v)] if isinstance(v, (list, dict)) else _atom_digest(v))
                memo[cid] = h.digest()
    return memo[id(value)].hex()


def dag_equal(left, right):
    """Exact structural equality over potentially DAG-shared JSON graphs."""
    seen = set()
    stack = [(left, right)]
    while stack:
        a, b = stack.pop()
        if a is b:
            continue
        if type(a) is not type(b):
            return False
        if isinstance(a, list):
            if len(a) != len(b):
                return False
            pair_id = (id(a), id(b))
            if pair_id in seen:
                continue
            seen.add(pair_id)
            stack.extend(zip(a, b))
        elif isinstance(a, dict):
            if a.keys() != b.keys():
                return False
            pair_id = (id(a), id(b))
            if pair_id in seen:
                continue
            seen.add(pair_id)
            for k in a:
                stack.append((a[k], b[k]))
        elif a != b:
            return False
    return True


class Mismatch(ValueError):
    pass


def _unwind(e):
    args = []
    while isinstance(e, list) and len(e) == 3 and e[0] == 'app':
        args.append(e[2])
        e = e[1]
    head = e[1][1] if isinstance(e, list) and len(e) == 3 and e[0] == 'const' else None
    return head, args[::-1]


def _lit(e):
    return e[1] if isinstance(e, list) and len(e) == 2 and e[0] == 'str' else None


def _name(e):
    """Decode an elaborated `Lean.Name` expression, or None."""
    head, args = _unwind(e)
    if head == 'Lean.Name.anonymous' and not args:
        return []
    if head in ('Lean.Name.mkStr', 'Lean.Name.str') and len(args) == 2:
        prefix, part = _name(args[0]), _lit(args[1])
        return None if prefix is None or part is None else prefix + [part]
    if head and head.startswith('Lean.Name.mkStr') and head[len('Lean.Name.mkStr'):].isdigit():
        parts = [_lit(a) for a in args]
        return None if None in parts else parts
    return None


def _list(e):
    head, args = _unwind(e)
    if head == 'List.nil' and len(args) == 1:
        return []
    if head == 'List.cons' and len(args) == 3:
        rest = _list(args[2])
        return None if rest is None else [args[1]] + rest
    return None


def _preresolved(e):
    head, args = _unwind(e)
    if head == 'Lean.Syntax.Preresolved.decl' and len(args) == 2:
        name, fields = _name(args[0]), _list(args[1])
        if name is None or fields is None or None in [_lit(f) for f in fields]:
            return None
        return ['decl', ['name', '.'.join(name)], [_lit(f) for f in fields]]
    if head == 'Lean.Syntax.Preresolved.namespace' and len(args) == 1:
        name = _name(args[0])
        # Namespaces renamed with their declaration compare under the map too.
        return None if name is None else ['namespace', ['name', '.'.join(name)]]
    return None


RAW_SUBSTRING = ('String.toRawSubstring', "String.toRawSubstring'")


def plain_spelling(raw):
    """A raw identifier spelling without `«»` escapes, as `getId` reports it."""
    return '.'.join(part[1:-1] if part.startswith('«') and part.endswith('»') else part
                    for part in APPLY.split_name(raw)) if raw else raw


def _spelling_parts(val):
    """(components, wrapper) of a quotation's `val` when subtrees are already transformed."""
    head, args = _unwind(val)
    if head == 'Lean.addMacroScope' and len(args) == 3:
        parts = _name(args[1])
        return (None, None) if parts is None else (parts, ['addMacroScope', args[0], args[2]])
    parts = _name(val)
    return parts, None


def quoted_identifiers_node(e):
    """Recognize an already-decoded `['app', ...]` syntax identifier quotation node."""
    if isinstance(e, list) and len(e) == 3 and e[0] == 'app':
        head, args = _unwind(e)
        if head == 'Lean.Syntax.ident' and len(args) == 4:
            items = _list(args[3])
            decoded = None if items is None else [_preresolved(x) for x in items]
            if decoded == []:
                info, raw, val, _ = args
                raw_head, raw_args = _unwind(raw)
                raw_text = _lit(raw_args[0]) if raw_head in RAW_SUBSTRING and len(raw_args) == 1 else None
                parts = _name(val)
                if raw_text is not None and parts is not None and plain_spelling(raw_text) == '.'.join(parts):
                    return ['unhygienicIdentifier', '.'.join(parts), raw_text, [raw_head, info]]
            if decoded and None not in decoded and any(d[0] == 'decl' for d in decoded):
                info, raw, val, _ = args
                raw_head, raw_args = _unwind(raw)
                raw_text = _lit(raw_args[0]) if raw_head in RAW_SUBSTRING and len(raw_args) == 1 else None
                parts, wrapper = _spelling_parts(val)
                if raw_text is not None and parts is not None and all('.' not in p for p in parts):
                    return ['quotedIdentifier', decoded, '.'.join(parts), raw_text, [raw_head, wrapper, info]]
    return e


def quoted_identifiers(e):
    """Canonical form of identifiers inside elaborated syntax quotations.

    `Lean.Syntax.ident info raw val preresolved`. Expansion uses the
    pre-resolved global declarations, and a consumer can observe the spelling
    (`Syntax.getId` returns `val`; reprinting uses `raw`). Both are kept: the
    pre-resolved declarations are compared under the map, and the spelling
    must be exactly the apply tool's names-only respelling of the old spelling
    under the map (`Comparison.respell`). A capture qualification (`B256` ->
    `Jaune.U256`) changes what `getId` returns, so it is a difference. Without
    pre-resolved declarations the whole expression is compared literally.
    """
    if not isinstance(e, (list, dict)):
        return e
    results = {}
    stack = [(e, False)]
    while stack:
        cur, ready = stack.pop()
        cid = id(cur)
        if cid in results:
            continue
        if isinstance(cur, dict):
            if not ready:
                stack.append((cur, True))
                for v in cur.values():
                    if isinstance(v, (list, dict)) and id(v) not in results:
                        stack.append((v, False))
            else:
                out = {k: (results[id(v)] if isinstance(v, (list, dict)) else v) for k, v in cur.items()}
                results[cid] = cur if all(out[k] is cur[k] for k in cur) else out
        elif isinstance(cur, list):
            if not ready:
                stack.append((cur, True))
                for x in cur:
                    if isinstance(x, (list, dict)) and id(x) not in results:
                        stack.append((x, False))
            else:
                changed = False
                items = []
                for x in cur:
                    if isinstance(x, (list, dict)):
                        nx = results[id(x)]
                        if nx is not x:
                            changed = True
                        items.append(nx)
                    else:
                        items.append(x)
                cand = items if changed else cur
                converted = quoted_identifiers_node(cand)
                results[cid] = converted
    return results[id(e)]


def find_special_ids(constants, guards=()):
    """Collect Python object IDs of quotation nodes and every ancestor container."""
    special = set()
    visited = set()

    def scan(root):
        if not isinstance(root, (list, dict)) or id(root) in visited:
            return
        stack = [(root, False)]
        while stack:
            cur, ready = stack.pop()
            cid = id(cur)
            if ready:
                if isinstance(cur, list):
                    if ((len(cur) in (4, 5) and cur[0] in ('unhygienicIdentifier', 'quotedIdentifier')) or
                            any(isinstance(x, (list, dict)) and id(x) in special for x in cur)):
                        special.add(cid)
                elif any(isinstance(v, (list, dict)) and id(v) in special for v in cur.values()):
                    special.add(cid)
                continue
            if cid in visited:
                continue
            visited.add(cid)
            stack.append((cur, True))
            children = cur if isinstance(cur, list) else cur.values()
            for ch in children:
                if isinstance(ch, (list, dict)) and id(ch) not in visited:
                    stack.append((ch, False))

    for rec in constants.values():
        scan(rec)
    for g in guards:
        scan(g)
    return special


def _clone_special_spine(root, special_ids):
    """Iteratively clone only containers in `special_ids`, keeping non-special sub-DAGs shared."""
    if not isinstance(root, (list, dict)) or id(root) not in special_ids:
        return root
    clones = {}
    stack = [(root, False)]
    while stack:
        cur, ready = stack.pop()
        cid = id(cur)
        if not ready:
            stack.append((cur, True))
            children = cur if isinstance(cur, list) else cur.values()
            for ch in children:
                if isinstance(ch, (list, dict)) and id(ch) in special_ids and id(ch) not in clones:
                    stack.append((ch, False))
        else:
            if isinstance(cur, list):
                out = [clones[id(x)] if isinstance(x, (list, dict)) and id(x) in special_ids else x for x in cur]
            else:
                out = {k: (clones[id(v)] if isinstance(v, (list, dict)) and id(v) in special_ids else v)
                       for k, v in cur.items()}
            special_ids.add(id(out))
            clones[cid] = out
    return clones[id(root)]


def decode_schema8_data(data, pools_keep, special_ids):
    """Decode Schema 8 level_pool/expr_pool bottom-up into shared DAG structures."""
    raw_levels = data.get('level_pool')
    raw_exprs = data.get('expr_pool')
    if not isinstance(raw_levels, list) or not isinstance(raw_exprs, list):
        raise ValueError('schema 8 export requires level_pool and expr_pool')
    levels = []
    for idx, node in enumerate(raw_levels):
        if not isinstance(node, list) or not node:
            raise ValueError(f'invalid level_pool node at {idx}')
        tag = node[0]
        if tag in ('zero', 'param'):
            levels.append(node)
        elif tag == 'succ':
            uid = node[1]
            if not isinstance(uid, int) or uid < 0 or uid >= idx:
                raise ValueError(f'invalid level_pool ref {uid} at {idx}')
            levels.append(['succ', levels[uid]])
        elif tag in ('max', 'imax'):
            u1, u2 = node[1], node[2]
            if not (isinstance(u1, int) and 0 <= u1 < idx and isinstance(u2, int) and 0 <= u2 < idx):
                raise ValueError(f'invalid level_pool refs {(u1, u2)} at {idx}')
            levels.append([tag, levels[u1], levels[u2]])
        else:
            raise ValueError(f'unknown level_pool tag {tag!r}')

    n_levels = len(levels)

    def ref_level(uid):
        if not isinstance(uid, int) or uid < 0 or uid >= n_levels:
            raise ValueError(f'invalid level index {uid}')
        return levels[uid]

    exprs = []
    special_pool = []
    attached_special = set()

    def attach_special(obj):
        oid = id(obj)
        if oid not in attached_special:
            attached_special.add(oid)
            return obj
        cloned = _clone_special_spine(obj, special_ids)
        attached_special.add(id(cloned))
        return cloned

    def ref_expr_in_pool(eid, limit):
        if not isinstance(eid, int) or eid < 0 or eid >= limit:
            raise ValueError(f'invalid expr_pool ref {eid} at {limit}')
        obj = exprs[eid]
        if special_pool[eid]:
            return attach_special(obj)
        return obj

    for idx, node in enumerate(raw_exprs):
        if not isinstance(node, list) or not node:
            raise ValueError(f'invalid expr_pool node at {idx}')
        tag = node[0]
        if tag in ('bvar', 'nat', 'str'):
            obj, is_sp = node, False
        elif tag == 'sort':
            obj, is_sp = ['sort', ref_level(node[1])], False
        elif tag == 'const':
            obj, is_sp = ['const', node[1], [ref_level(u) for u in node[2]]], False
        elif tag == 'app':
            f_obj = ref_expr_in_pool(node[1], idx)
            a_obj = ref_expr_in_pool(node[2], idx)
            cand = ['app', f_obj, a_obj]
            conv = quoted_identifiers_node(cand)
            if conv is not cand:
                obj = conv
                is_sp = True
                special_ids.add(id(obj))
            else:
                obj = cand
                is_sp = special_pool[node[1]] or special_pool[node[2]]
                if is_sp:
                    special_ids.add(id(obj))
        elif tag in ('lam', 'forall'):
            t_obj = ref_expr_in_pool(node[2], idx)
            b_obj = ref_expr_in_pool(node[3], idx)
            obj = [tag, node[1], t_obj, b_obj]
            is_sp = special_pool[node[2]] or special_pool[node[3]]
            if is_sp:
                special_ids.add(id(obj))
        elif tag == 'let':
            t_obj = ref_expr_in_pool(node[2], idx)
            v_obj = ref_expr_in_pool(node[3], idx)
            b_obj = ref_expr_in_pool(node[4], idx)
            obj = ['let', node[1], t_obj, v_obj, b_obj]
            is_sp = special_pool[node[2]] or special_pool[node[3]] or special_pool[node[4]]
            if is_sp:
                special_ids.add(id(obj))
        elif tag == 'proj':
            s_obj = ref_expr_in_pool(node[3], idx)
            obj = ['proj', node[1], node[2], s_obj]
            is_sp = special_pool[node[3]]
            if is_sp:
                special_ids.add(id(obj))
        else:
            raise ValueError(f'unknown expr_pool tag {tag!r}')
        exprs.append(obj)
        special_pool.append(is_sp)

    n_exprs = len(exprs)

    def attach_id(eid):
        if not isinstance(eid, int) or eid < 0 or eid >= n_exprs:
            raise ValueError(f'invalid expr index {eid}')
        return ref_expr_in_pool(eid, n_exprs), special_pool[eid]

    new_constants = {}
    for name, c in data['constants'].items():
        k = c['kernel']
        type_expr, sp_t = attach_id(k['type'])
        p = k['payload']
        sp_p = False
        if isinstance(p, list) and p:
            ptag = p[0]
            if ptag in ('definition', 'opaque'):
                val_expr, sp_v = attach_id(p[2])
                new_payload = [ptag, p[1], val_expr]
                if sp_v:
                    special_ids.add(id(new_payload))
                    sp_p = True
            elif ptag == 'recursor':
                new_rules = []
                for rule in p[6]:
                    rhs_expr, sp_r = attach_id(rule[3])
                    nr = [rule[0], rule[1], rule[2], rhs_expr]
                    if sp_r:
                        special_ids.add(id(nr))
                        sp_p = True
                    new_rules.append(nr)
                if sp_p:
                    special_ids.add(id(new_rules))
                new_payload = [p[0], p[1], p[2], p[3], p[4], p[5], new_rules, p[7], p[8]]
                if sp_p:
                    special_ids.add(id(new_payload))
            else:
                new_payload = p
        else:
            new_payload = p
        new_kernel = {'universes': k['universes'], 'type': type_expr, 'payload': new_payload}
        new_const = {'kernel': new_kernel, 'attributes': c['attributes']}
        if 'equation_origin' in c:
            new_const['equation_origin'] = c['equation_origin']
        if sp_t or sp_p:
            special_ids.add(id(new_kernel))
            special_ids.add(id(new_const))
        new_constants[name] = new_const

    new_guards = []
    for g in data['guards']:
        g_expr, sp_g = attach_id(g[1])
        ng = [g[0], g_expr]
        if sp_g:
            special_ids.add(id(ng))
        new_guards.append(ng)

    pools_keep.append((levels, exprs))
    return new_constants, new_guards


REALIZED_THM_LEAF = re.compile(r'^(eq_\d+|eq_def|else_eq|splitter|congr_simp|_?proof_\d+(?:_\d+)*|_?simp_\d+(?:_\d+)*)$')

DEFAULT_ATTR_KEYS = {
    'simp': [], 'simp_unfold': False, 'simp_equations': None,
    'csimp': False, 'csimp_replacement': None, 'inline': None,
    'instance': None, 'implemented_by': None, 'match_pattern': False,
    'default_instance': [], 'eliminator': [], 'ext': [], 'elaborator': [],
    'elab_as_elim': False, 'elab_without_expected_type': False,
    'specialize': None, 'nospecialize': False, 'never_extract': False,
    'export': None, 'protected': False, 'noncomputable': False,
}


def has_nondefault_attributes(attrs):
    """Return True if a constant has any non-default elaboration/compilation attribute."""
    if not attrs:
        return False
    for k, v in attrs.items():
        if k == 'reducibility':
            if v is not None and v != 'Lean.ReducibilityStatus.semireducible':
                return True
        elif k in DEFAULT_ATTR_KEYS:
            if v != DEFAULT_ATTR_KEYS[k]:
                return True
        elif v:
            return True
    return False


def is_realized_theorem_candidate(name, rec, roots):
    """Whether `name` is an un-annotated generated realized theorem eligible for closure exclusion."""
    if name in roots:
        return False
    leaf = name.rsplit('@', 1)[0].rsplit('.', 1)[-1]
    if not REALIZED_THM_LEAF.match(leaf):
        return False
    kernel = rec.get('kernel')
    payload = kernel.get('payload') if isinstance(kernel, dict) else kernel
    if payload != ['theorem']:
        return False
    return not has_nondefault_attributes(rec.get('attributes'))


def _mkstr_literal(e):
    """Extract dotted Name literal if `e` is `Lean.Name.mkStrK s1 ... sK` with plain string parts."""
    if not (isinstance(e, list) and len(e) == 3 and e[0] == 'app'):
        return None
    parts = []
    cur = e
    for _ in range(9):
        if isinstance(cur, list) and len(cur) == 3 and cur[0] == 'app':
            arg = cur[2]
            if not (isinstance(arg, list) and len(arg) == 2 and arg[0] == 'str' and isinstance(arg[1], str)):
                return None
            if not arg[1] or '.' in arg[1] or '«' in arg[1]:
                return None
            parts.append(arg[1])
            cur = cur[1]
        else:
            break
    if (parts and isinstance(cur, list) and len(cur) >= 2 and cur[0] == 'const' and
            isinstance(cur[1], list) and len(cur[1]) == 2 and cur[1][0] == 'name' and
            cur[1][1] == f'Lean.Name.mkStr{len(parts)}'):
        parts.reverse()
        return '.'.join(parts)
    return None


def collect_const_refs(value, found=None, visited=None):
    """Iteratively extract all referenced `['name', N]` and `Lean.Name.mkStrK` literals."""
    if found is None:
        found = set()
    if visited is None:
        visited = set()
    stack = [value]
    while stack:
        cur = stack.pop()
        if isinstance(cur, list):
            cid = id(cur)
            if cid in visited:
                continue
            visited.add(cid)
            if len(cur) == 2 and cur[0] == 'name' and isinstance(cur[1], str):
                found.add(cur[1])
                continue
            if len(cur) == 4 and cur[0] == 'unhygienicIdentifier' and isinstance(cur[1], str):
                found.add(cur[1])
                continue
            if len(cur) == 5 and cur[0] == 'quotedIdentifier' and isinstance(cur[2], str):
                found.add(cur[2])
            if len(cur) == 3 and cur[0] == 'app':
                lit = _mkstr_literal(cur)
                if lit is not None:
                    found.add(lit)
            for x in cur:
                if isinstance(x, (list, dict)) and id(x) not in visited:
                    stack.append(x)
        elif isinstance(cur, dict):
            cid = id(cur)
            if cid in visited:
                continue
            visited.add(cid)
            for v in cur.values():
                if isinstance(v, (list, dict)) and id(v) not in visited:
                    stack.append(v)
    return found


def merge_constants(existing, roots, incoming, incoming_roots):
    """Union compiler-registered equation copies, never authored collisions."""
    overlap = existing.keys() & incoming.keys()
    for name in sorted(overlap):
        origin = existing[name].get('equation_origin')
        # Lean realizes reserved auxiliaries (equation lemmas, `_sparseCasesOn`
        # equations, `congr_simp` lemmas) on demand in each module; one environment
        # can import both only because the copies agree. A non-authored copy
        # with an identical kernel and attribute record therefore coalesces;
        # registered equation copies must also agree on their parent.
        # Any non-authored identical copy qualifies: an importing environment
        # (here the capture itself elaborated one) only admits agreeing copies.
        realized = origin is None and incoming[name].get('equation_origin') is None
        if (name in roots or name in incoming_roots or
                (origin is None and not realized) or
                origin != incoming[name].get('equation_origin') or
                not dag_equal(existing[name], incoming[name])):
            raise ValueError(f'duplicate constants without identical generated-equation provenance: {name}')
    existing.update(incoming)
    return overlap


def spelled_name(source, a, b, name):
    """Whether the definition range spells the declaration's own name.

    Lean records anonymous instances (`instance : C T`) and other compiler-named
    declarations at a keyword. Their names derive from other names, so a rename
    changes them without any source edit: they are matched by kernel graph,
    like generated constants, not by the map.
    """
    spans = APPLY.components(source, a, b)
    if spans is None:
        return False
    spelled = [source[x:y] for x, y in spans]
    private = MAP.split_private(name)
    parts = APPLY.split_name(private[2] if private else name)
    return parts[-len(spelled):] == spelled


ITEMS = ('guards', 'attributes', 'checks')


def expansion_declarations(before, module, spelling):
    """Declarations of `module` whose source invokes a local macro that
    quotes `spelling`: the macro command is the one whose source contains the
    quoted range; its keyword's other occurrences lie in these declarations,
    whose kernel terms N4 compares under the map."""
    source = (before.get('module_sources') or {}).get(module)
    decls = (before.get('module_decls') or {}).get(module) or {}
    sites = [(a, b) for a, b, n in (before.get('quotation_sites') or {}).get(module, []) if n == spelling]
    if source is None or not sites:
        return []
    found = set()
    for a, _ in sites:
        line_start = source.rfind('\n', 0, a)
        macro_start = source.rfind('\nlocal macro "', 0, a)
        if macro_start < 0:
            macro_start = source.rfind('\nmacro "', 0, a)
        if macro_start < 0:
            continue
        key_start = source.index('"', macro_start) + 1
        keyword = source[key_start:source.index('"', key_start)]
        for m in re.finditer(r'(?<![\w"])' + re.escape(keyword) + r'(?![\w"])', source):
            for name, (s, e) in decls.items():
                if s <= m.start() < e:
                    found.add(name)
    return sorted(found)

def code_text(text):
    """`text` with comments, string literals and `«»`-escaped identifiers
    blanked (same length): only Lean's own keywords and tokens remain, so a
    commented-out or quoted `deriving Repr` is not a deriving clause."""
    out, i = list(text), 0

    def blank(a, b):
        for k in range(a, min(b, len(out))):
            if out[k] != '\n':
                out[k] = ' '
    while i < len(text):
        if text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            blank(i, end)
            i = end
        elif text.startswith('/-', i):
            depth, j = 1, i + 2
            while depth and j < len(text):
                if text.startswith('/-', j):
                    depth, j = depth + 1, j + 2
                elif text.startswith('-/', j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            blank(i, j)
            i = j
        elif (text[i] == "'" and (i == 0 or not (text[i - 1].isalnum() or text[i - 1] in "_'?!")) and
              re.match(r"'(\\.|[^\\'\n])'", text[i:i + 4])):
            # A character literal (`'"'`) is skipped whole, never a string start.
            i += len(re.match(r"'(\\.|[^\\'\n])'", text[i:i + 4]).group(0))
        elif text[i] == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            blank(i, j + 1)
            i = j + 1
        elif text[i] == '«':
            j = text.find('»', i + 1)
            j = len(text) if j < 0 else j + 1
            blank(i, j)
            i = j
        else:
            i += 1
    return ''.join(out)


SINGLE_BACKTICK = re.compile(r"(?<![`\w.'?!])`(?![`(\[])((?:«[^»]*»|[^\W\d][\w'?!]*)(?:\.(?:«[^»]*»|[^\W\d][\w'?!]*))*)")


def single_backtick_literals(source):
    """[(start, end, plain spelling)] of the single-backtick `Name` literals in
    `source` (character offsets of the spelling, after the backtick), outside
    comments and strings. Lean does not resolve these: they are data."""
    code = code_text(source.replace('«', '\0').replace('»', '\1')).replace('\0', '«').replace('\1', '»')
    return [(m.start(1), m.end(1), plain_spelling(m.group(1))) for m in SINGLE_BACKTICK.finditer(code)]


# Classes whose deriving handlers write constructor and field names into string
# literals (`deriving Repr` prints `Jaune.T.ctor` and `{ field := ... }`).
DERIVING_CLASSES = {'Repr': 'Repr', 'Lean.ToJson': 'ToJson', 'Lean.FromJson': 'FromJson'}


def _consts(e, found):
    stack = [e]
    while stack:
        cur = stack.pop()
        if isinstance(cur, list):
            if len(cur) == 3 and cur[0] == 'const' and isinstance(cur[1], list) and cur[1][:1] == ['name']:
                found.append(cur[1][1])
            for x in reversed(cur):
                stack.append(x)
    return found


def derived_constants(data, authored_ranges, byte_offsets, positions):
    """Constants a deriving handler produced, from compiler data alone: an
    instance with no source declaration range whose value is `C.mk T ...` for a
    class C in DERIVING_CLASSES, where T is declared in this module by a
    command whose deriving clause names C (or a `deriving instance C for T`
    command names both), together with the instance's auxiliaries by name
    prefix (`inst.repr`, `inst.repr.match_1`), also without a declaration
    range. A hand-written instance, even an anonymous one, has a range (its
    keyword) and is never derived. Returns {constant: (target type, class)}."""
    decls = data['index']['decls']
    commands = [(r[0], r[1], r[2]) for r in data['index'].get('naming_syntax', {}).get('commands', [])]
    source_bytes = data['source'].encode()
    roots = {}
    for name, constant in data['constants'].items():
        if name in decls:
            continue
        kernel = constant['kernel']
        payload = kernel['payload'] if isinstance(kernel, dict) else kernel
        if not (isinstance(payload, list) and len(payload) >= 3 and payload[0] == 'definition'):
            continue
        names = _consts(payload[2], [])
        if len(names) < 2 or not names[0].endswith('.mk') or names[0][:-3] not in DERIVING_CLASSES:
            continue
        cls = DERIVING_CLASSES[names[0][:-3]]
        target = next((n for n in names[1:] if n in decls), None)
        if target is None:
            continue
        a, b = APPLY.span(positions, decls[target][:4])
        start = byte_offsets[a]
        text = [code_text(source_bytes[x:y].decode('utf-8', 'replace')) for x, y, kind in commands if x <= start < y]
        clause = re.compile(r'\bderiving\b[^\n]*\b' + re.escape(cls) + r'\b')
        leaf = re.escape(target.split('.')[-1])
        instance_cmd = [code_text(source_bytes[x:y].decode('utf-8', 'replace')) for x, y, kind in commands
                        if kind == 'Lean.Parser.Command.deriving']
        if (text and clause.search(text[0])) or any(
                re.search(r'\b' + re.escape(cls) + r'\b', t) and re.search(r'\b' + leaf + r'\b', t)
                for t in instance_cmd):
            roots[name] = (target, cls)
    derived = {}
    for name in data['constants']:
        if name in decls:
            continue
        for root, target in roots.items():
            if name == root or name.startswith(root + '.'):
                derived[name] = target
    return derived



def read_exports(paths):
    constants, roots, guards, attributes, modules, receipts = {}, set(), [], [], {}, []
    owners, holders = {}, {}
    checks = []
    derived = {}
    dot_resolved = []
    quotation_sites, module_sources, module_decls, module_commands = {}, {}, {}, {}
    item_modules = {key: [] for key in ITEMS}
    coalesced = set()
    pools_keep, special_ids, ilean_refs, import_modules, from_olean = [], set(), set(), {}, {}
    version = None
    schemas = set()
    for path in paths:
        raw = Path(path).read_bytes()
        data = json.loads(raw)
        schemas.add(data['schema_version'])
        if data['schema_version'] not in SCHEMAS or data['index']['version'] != 5:
            raise ValueError('unsupported fidelity/index schema')
        if version is not None and version != data['lean_version']:
            raise ValueError('mixed Lean versions')
        version = data['lean_version']
        module = APPLY.module_name(data['index']['module'])
        if module in modules:
            raise ValueError(f'duplicate module {module}')
        modules[module] = data['index']['directImports']
        if 'import_modules' in data:
            import_modules[module] = data['import_modules']
        from_olean[module] = bool(data['index'].get('naming_syntax', {}).get('from_olean', False))
        for name, constant in data['constants'].items():
            if data['schema_version'] >= 6:
                origin = constant['equation_origin']
                if origin is not None and not (isinstance(origin, list) and len(origin) == 2 and
                                               origin[0] == 'name' and isinstance(origin[1], str) and origin[1]):
                    raise ValueError(f'{name}: invalid equation provenance')
            elif 'equation_origin' in constant:
                raise ValueError('equation provenance requires schema 6')
        command_checks = data['checked_commands'] if data['schema_version'] >= 5 else []
        failure_scopes = [(row['start'], row['end']) for row in command_checks
                          if row['expected_failure_scope']]
        decl_positions = APPLY.Positions(data['source'])
        names = {name for name, loc in data['index']['decls'].items()
                 if spelled_name(data['source'], *APPLY.span(decl_positions, loc[4:] if len(loc) == 8 else loc), name)}
        ilean_refs.update(data['index']['decls'].keys())
        failed_names = set()
        locations = defaultdict(set)
        positions = APPLY.Positions(data['source'])
        byte_offsets = [0]
        for char in data['source']:
            byte_offsets.append(byte_offsets[-1] + len(char.encode('utf-8')))
        for key, info in data['index']['references'].items():
            const = json.loads(key).get('c')
            if not const:
                continue
            ilean_refs.add(const['n'])
            if info.get('definition') is not None:
                a, b = APPLY.span(positions, info['definition'])
                pseudo_example = (const['n'].endswith('._example') and
                                  data['source'][a:b] == 'example' and not info['usages'])
                if any(start is not None and end is not None and
                       start <= byte_offsets[a] and byte_offsets[b] <= end
                       for start, end in failure_scopes) and const['n'] not in data['constants']:
                    failed_names.add(const['n'])
                elif not pseudo_example and spelled_name(data['source'], a, b, const['n']):
                    names.add(const['n'])
            for loc in info['usages'] + ([info['definition']] if info.get('definition') else []):
                start, end = APPLY.span(positions, loc)
                locations[byte_offsets[start], byte_offsets[end]].add(const['n'])
        names -= failed_names
        missing = names - data['constants'].keys()
        if missing:
            raise ValueError(f'{module}: authored definitions missing from kernel export: {sorted(missing)}')
        char_of = {b: i for i, b in enumerate(byte_offsets)}
        quotation_sites[module] = [(char_of[a], char_of[b], n) for a, b, n in
                                   data['index'].get('naming_syntax', {}).get('quotation_identifiers', [])
                                   if a in char_of and b in char_of]
        module_sources[module] = data['source']
        module_commands[module] = [(char_of[r[0]], char_of[r[1]]) for r in
                                   data['index'].get('naming_syntax', {}).get('commands', [])
                                   if r[0] in char_of and r[1] in char_of]
        module_decls[module] = {n: APPLY.span(positions, loc[:4]) for n, loc in data['index']['decls'].items()}
        if data['schema_version'] == 8:
            data['constants'], data['guards'] = decode_schema8_data(data, pools_keep, special_ids)
        else:
            data['constants'] = {n: quoted_identifiers(c) for n, c in data['constants'].items()}
            data['guards'] = [quoted_identifiers(g) for g in data['guards']]
            special_ids.update(find_special_ids(data['constants'], data['guards']))
        derived.update(derived_constants(data, None, byte_offsets, positions))
        coalesced |= merge_constants(constants, roots, data['constants'], names)
        roots.update(names)
        for name in data['constants']:
            owners.setdefault(name, module)
            holders.setdefault(name, set()).add(module)

        source_bytes = data['source'].encode()

        def dot_ident(value):
            """An ident directly under `Lean.Parser.Term.dotIdent`: the compiler
            records its reference over `.name` (from the dot), one byte before
            the ident's own range. Resolve it there, and only there."""
            ident = value[2][1]
            s, e = ident[2], ident[3]
            found = locations[s, e] - failed_names
            if not found and s > 0 and source_bytes[s - 1:s] == b'.':
                found = locations[s - 1, e] - failed_names
                if found:
                    dot_resolved.append(ident[1])
            # Whichever range resolved it, a dot identifier names a constant
            # with its own leaf (a constructor or a field); anything else is
            # some other reference that happens to share the range.
            if found and any(MAP.split_private(n)[2].rsplit('.', 1)[-1] != plain_spelling(ident[1])
                             if MAP.split_private(n) else n.rsplit('.', 1)[-1] != plain_spelling(ident[1])
                             for n in found):
                raise ValueError(f'{module}: dot identifier .{ident[1]} resolves to {sorted(found)}')
            if len(found) > 1:
                raise ValueError('ambiguous compiler reference in a dot identifier')
            name = ['name', next(iter(found))] if found else ['token', ident[1]]
            return [value[0], value[1], [syntax(value[2][0]), name]]

        def syntax(value, literal_names=False):
            if not isinstance(value, list):
                return value
            if (len(value) == 3 and value[:2] == ['syntax', 'Lean.Parser.Term.dotIdent'] and
                    isinstance(value[2], list) and len(value[2]) == 2 and isinstance(value[2][1], list) and
                    len(value[2][1]) == 4 and value[2][1][0] == 'ident' and not literal_names):
                return dot_ident(value)
            if len(value) == 4 and value[0] == 'ident':
                if literal_names:
                    # AxiomAudit reads these identifiers with getId, without
                    # namespace resolution; its literal qualified names are the semantics.
                    return ['name', value[1]]
                found = locations[value[2], value[3]] - failed_names
                if len(found) > 1:
                    raise ValueError('ambiguous compiler reference in attribute command')
                return ['name', next(iter(found))] if found else ['token', value[1]]
            if len(value) == 3 and value[0] == 'declTarget':
                # A declaration Lean names itself (an anonymous instance): its
                # definition range is the keyword, resolved like any reference.
                found = locations[value[1], value[2]] - failed_names
                if len(found) != 1:
                    raise ValueError(f'{module}: attribute target at bytes {value[1]}..{value[2]} '
                                     f'resolves to {sorted(found)}')
                return ['name', next(iter(found))]
            if value in (['atom', 'local'], ['atom', 'scoped']):
                raise ValueError('local/scoped attribute commands require scope-history support')
            return [syntax(item, literal_names) for item in value]

        rows = dict(checks=[syntax(row['syntax'], row['literal_names']) for row in command_checks],
                    guards=data['guards'], attributes=[syntax(item) for item in data['attribute_syntax']])
        checks.extend(rows['checks'])
        guards.extend(rows['guards'])
        attributes.extend(rows['attributes'])
        for key in ITEMS:
            item_modules[key].extend([module] * len(rows[key]))
        receipts.append(dict(path=str(path), sha256=hashlib.sha256(raw).hexdigest(),
                             source_sha256=hashlib.sha256(data['source'].encode()).hexdigest(), module=module))
    if not modules:
        raise ValueError('no exported modules')
    return dict(constants=constants, roots=roots, guards=guards, attributes=attributes,
                modules=modules, receipts=receipts, version=version, checks=checks,
                coalesced_equations=sorted(coalesced), owners=owners, holders=holders,
                item_modules=item_modules, schemas=schemas, derived=derived,
                dot_identifiers_resolved=len(dot_resolved), quotation_sites=quotation_sites,
                module_sources=module_sources, module_decls=module_decls, module_commands=module_commands,
                _pools=pools_keep, _special_ids=special_ids, ilean_refs=ilean_refs,
                import_modules=import_modules, from_olean=from_olean)


def extract_module_meta(export_path, export_sha256=None):
    """Extract lightweight verified `.meta.json` sidecar from a single `.export.json`."""
    export_path = Path(export_path)
    actual_sha = hashlib.sha256(export_path.read_bytes()).hexdigest()
    if export_sha256 is not None and actual_sha != export_sha256:
        raise ValueError(f'{export_path}: export digest changed before metadata extraction')
    bundle = read_exports([export_path])
    module = next(iter(bundle['modules']))
    kernel_refs = set()
    visited = set()
    for name, rec in bundle['constants'].items():
        if not is_realized_theorem_candidate(name, rec, bundle['roots']):
            collect_const_refs(rec, kernel_refs, visited)
    for field in ('guards', 'checks', 'attributes'):
        collect_const_refs(bundle[field], kernel_refs, visited)
    referenced = sorted(kernel_refs | bundle['ilean_refs'])
    return dict(
        schema_version=next(iter(bundle['schemas'])),
        meta_version=1,
        export_sha256=actual_sha,
        module=module,
        lean_version=bundle['version'],
        from_olean=bundle['from_olean'][module],
        source_sha256=bundle['receipts'][0]['source_sha256'],
        direct_imports=bundle['modules'][module],
        import_modules=bundle['import_modules'].get(module),
        authored_roots=sorted(bundle['roots']),
        all_constants=sorted(bundle['constants'].keys()),
        referenced_constants=referenced,
        kernel_referenced_constants=sorted(kernel_refs),
        guard_count=len(bundle['guards']),
        check_count=len(bundle['checks']),
        attr_count=len(bundle['attributes']),
    )


class Comparison:
    def __init__(self, before, after, mapping, reviewed=None, reviewed_used=None, collect=False,
                 plan_edits=None, global_context=None, external=None):
        self.before, self.after = before, after
        self._global_context = global_context
        gc = global_context or {}
        ext = external or {}
        self.collect, self.problems = collect, []
        self.plan_edits = plan_edits or set()
        self.plan_index = {}
        for edit in self.plan_edits:
            self.plan_index.setdefault(edit[:3], []).append(edit)
        self.unhygienic_sites = {}
        self.reviewed = reviewed
        self.reviewed_used = reviewed_used if reviewed_used is not None else set()
        # Reviewed records accepted in this comparison: each at one occurrence.
        self.reviewed_here = set()
        # The constants whose kernel terms are being compared (innermost last).
        self.holders = []
        self._unhygienic_bindings = {}
        if isinstance(mapping, dict):  # An exact old -> new table.
            mapping = MAP.Renamer([dict(old=a, new=b, kind='declaration') for a, b in mapping.items()])
        self.mapping = mapping
        self._aux_modules = self.aux_module_table(mapping)

        self.all_before_roots = gc['before_roots'] if 'before_roots' in gc else before['roots']
        self.all_after_roots = gc['after_roots'] if 'after_roots' in gc else after['roots']
        self.all_before_constants = gc['before_constants'] if 'before_constants' in gc else before['constants']
        self.all_after_constants = gc['after_constants'] if 'after_constants' in gc else after['constants']
        self.all_before_owners = gc['before_owners'] if 'before_owners' in gc else (before.get('owners') or {})
        self.all_after_owners = gc['after_owners'] if 'after_owners' in gc else (after.get('owners') or {})
        self.all_before_holders = gc['before_holders'] if 'before_holders' in gc else (before.get('holders') or {})
        self.all_after_holders = gc['after_holders'] if 'after_holders' in gc else (after.get('holders') or {})
        self._has_holders_info = ((before.get('holders') is not None or 'before_holders' in gc) and
                                  (after.get('holders') is not None or 'after_holders' in gc))

        self.external_gen_pairs = dict(ext.get('gen_pairs') or {})
        self.external_aux_classes = {k: set(v) for k, v in (ext.get('aux_classes') or {}).items()}
        self.external_before_aux_rep = dict(ext.get('before_aux_rep') or {})
        self.external_after_aux_rep = dict(ext.get('after_aux_rep') or {})
        self.external_after_gen = set(ext.get('after_gen') or set())
        self.externally_referenced_before = set(ext.get('referenced_before') or set())
        self.externally_referenced_after = set(ext.get('referenced_after') or set())
        self.scoped_relocations = ext['scoped_relocations'] if 'scoped_relocations' in ext else self.mapping.relocations
        self.scoped_public_from = ext['scoped_public_from'] if 'scoped_public_from' in ext else self.mapping.public_from

        self._special_left = (set(before['_special_ids']) if '_special_ids' in before
                              else find_special_ids(before['constants'], before.get('guards', ())))
        self._special_right = (set(after['_special_ids']) if '_special_ids' in after
                               else find_special_ids(after['constants'], after.get('guards', ())))
        self._undo = []
        self._expr_eq_cache = {}
        self._clean_respell_by_mod = {}
        self._norm_coarse_cache = {}
        self._gen_right_by_parent = None
        self.ignored_realized_before = []
        self.ignored_realized_after = []

        self.left = dict(before['constants'])
        self.right = after['constants']
        self.respelled_literals = []
        for name in list(self.left):
            respelled = self.respell_name_literals(name, self.left[name])
            if respelled is not self.left[name]:
                self.left[name] = respelled
        for name, (target, cls) in sorted((before.get('derived') or {}).items()):
            if name in self.left:
                self.left[name] = self.respell_derived(name, target, cls, self.left[name])
        self.generated_left = self.left.keys() - before['roots']
        self.generated_right = self.right.keys() - after['roots']
        self.pairs, self.reverse, self.checked = {}, {}, set()
        self.aux_pairs, self.aux_left, self.aux_right = set(), set(), set()
        self.realized_matcher_pairs = set()
        self.holder_pairs = []
        # Modules (after naming) that a relocation row links: a row moves its
        # declaration, and checks or generated constants may move with it,
        # between its two modules and nowhere else.
        self.parent = {}
        self.relocated_modules = set()
        for source, target in mapping.relocations.values():
            self.relocated_modules |= {mapping.module(source), target}
            self.join(mapping.module(source), target)
        self._reloc_targets = {self.mapping(k) for k in self.mapping.relocations}
        owners = self.all_before_owners
        for private in self.mapping.public_from:
            user = MAP.split_private(private)[2]
            mod = owners.get(private) or MAP.split_private(private)[0]
            if mod and self.module_of(private, mod) != self.mapping.module(mod):
                self._reloc_targets.add(self.mapping(user))

    def respell_name_literals(self, name, value):
        """A `Name` literal (`Lean.Name.mkStrN "A" ... "Z"`) whose full name is
        exactly an old constant the map renames is that constant's name: Lean
        resolves a double-backtick literal (``Pres``) to the full name, and
        renaming the constant respells it. It is compared as the new name
        (fewer or more components change N); every respelling is recorded."""
        if not isinstance(value, (list, dict)):
            return value
        known = self.all_before_constants
        module = self.holder_module(name)
        clean_ids = self._clean_respell_by_mod.setdefault(module, set())
        if id(value) in clean_ids:
            return value
        special = self._special_left
        memo = {}  # id(node) -> (out_node, lits_added_here)
        stack = [(value, False)]
        while stack:
            cur, ready = stack.pop()
            cid = id(cur)
            if cid in memo or cid in clean_ids:
                continue
            if isinstance(cur, list):
                if not ready:
                    if len(cur) == 3 and cur[0] == 'app':
                        lit = _mkstr_literal(cur)
                        if lit is not None:
                            new_full = self.name(lit) if lit in known else lit
                            why = 'name literal'
                            if new_full == lit:
                                new_full, why = self.namespace_literal(lit, name), 'namespace literal'
                            if new_full != lit and '«' not in new_full and not self.data_literal(name, lit, new_full):
                                parts = new_full.split('.')
                                if len(parts) <= 8:
                                    # Reach the outermost head node (`const Lean.Name.mkStrK levels`).
                                    head = cur
                                    while isinstance(head, list) and len(head) == 3 and head[0] == 'app':
                                        head = head[1]
                                    out = ['const', ['name', f'Lean.Name.mkStr{len(parts)}'], head[2]]
                                    for part in parts:
                                        out = ['app', out, ['str', part]]
                                    self.respelled_literals.append([name, lit, new_full, why])
                                    memo[cid] = (out, True)
                                    continue
                            # Plain Name.mkStr literal that did not change: never contains sub-literals.
                            clean_ids.add(cid)
                            continue
                    stack.append((cur, True))
                    for x in reversed(cur):
                        if isinstance(x, (list, dict)) and id(x) not in memo and id(x) not in clean_ids:
                            stack.append((x, False))
                else:
                    changed = False
                    any_lits = False
                    has_sp = False
                    out = []
                    for x in cur:
                        if isinstance(x, (list, dict)):
                            xid = id(x)
                            if xid in clean_ids:
                                nx = x
                            else:
                                nx, lit_flag = memo[xid]
                                if lit_flag:
                                    any_lits = True
                                if nx is not x:
                                    changed = True
                            if id(nx) in special or xid in special:
                                has_sp = True
                            out.append(nx)
                        else:
                            out.append(x)
                    if not changed:
                        if not any_lits:
                            clean_ids.add(cid)
                        else:
                            memo[cid] = (cur, True)
                    else:
                        if has_sp or cid in special:
                            special.add(id(out))
                        memo[cid] = (out, True)
            elif isinstance(cur, dict):
                if not ready:
                    stack.append((cur, True))
                    for v in cur.values():
                        if isinstance(v, (list, dict)) and id(v) not in memo and id(v) not in clean_ids:
                            stack.append((v, False))
                else:
                    changed = False
                    any_lits = False
                    has_sp = False
                    out = {}
                    for k, v in cur.items():
                        if isinstance(v, (list, dict)):
                            vid = id(v)
                            if vid in clean_ids:
                                nv = v
                            else:
                                nv, lit_flag = memo[vid]
                                if lit_flag:
                                    any_lits = True
                                if nv is not v:
                                    changed = True
                            if id(nv) in special or vid in special:
                                has_sp = True
                            out[k] = nv
                        else:
                            out[k] = v
                    if not changed:
                        if not any_lits:
                            clean_ids.add(cid)
                        else:
                            memo[cid] = (cur, True)
                    else:
                        if has_sp or cid in special:
                            special.add(id(out))
                        memo[cid] = (out, True)
        if id(value) in clean_ids:
            return value
        return memo[id(value)][0]

    def renamed_namespace(self, namespace):
        """The new namespace, when the map renames `namespace` by a namespace
        row or by derivation (its member rows agree); else None."""
        scoped = self.mapping.scope(namespace)
        if scoped == namespace or namespace in self.mapping.exact:
            return None
        if any(namespace == ns or namespace.startswith(ns + '.') for ns in self.mapping.namespaces):
            return scoped
        if namespace in self.mapping.derived() and self.uniform_namespace(namespace):
            return scoped
        return None

    def uniform_namespace(self, namespace):
        """A namespace the map renames only through its members (derived)
        moves as a whole only when every authored declaration directly in it
        moves into the new namespace (its own row may rename its leaf), and a declaration
        named like the namespace itself moves to the new name. Otherwise the
        namespace was partly moved and nothing follows it without a row."""
        if not hasattr(self, '_uniform'):
            self._uniform = {}
        if namespace not in self._uniform:
            target = self.mapping.derived().get(namespace)
            ok = target is not None
            for root in self.all_before_roots if ok else ():
                base = root.rsplit('@', 1)[0]
                private = MAP.split_private(base)
                user = private[2] if private else base
                if user == namespace:
                    ok = self.mapping(user) == target
                elif '.' in user and user.rsplit('.', 1)[0] == namespace:
                    # Its own row may rename the leaf; it must move into the
                    # new namespace (a member left behind, or moved elsewhere,
                    # means the namespace was only partly moved).
                    ok = self.mapping(user).rsplit('.', 1)[0] == target
                if not ok:
                    break
            self._uniform[namespace] = ok
        return self._uniform[namespace]

    def holder_module(self, holder):
        if holder is None:
            return None
        if self.before.get('owners') is None and not (self._global_context and 'before_owners' in self._global_context):
            return None
        return (self.before.get('owners') or {}).get(holder) or self.all_before_owners.get(holder)

    def data_literal(self, holder, full, new_full):
        """Whether the module holding `holder` spells `full` as a single-backtick
        `Name` literal that the applied plan did not respell to `new_full`.
        Lean does not resolve such a literal: it is runtime data, compared as
        written; only a plan edit at the literal itself admits its respelling.
        A capture without module sources (archived fixtures) has none."""
        sources = self.before.get('module_sources')
        if sources is None:
            return False
        module = self.holder_module(holder)
        source = sources.get(module) if module is not None else None
        if source is None:
            return True  # unknown provenance: fail closed
        if not hasattr(self, '_data_literals'):
            self._data_literals = {}
        if module not in self._data_literals:
            self._data_literals[module] = single_backtick_literals(source)
        for start, end, spelling in self._data_literals[module]:
            if spelling != full:
                continue
            respelled = any(start <= edit[1] and edit[2] <= end and
                            plain_spelling(source[start:edit[1]] + edit[4] + source[edit[2]:end]) == new_full
                            for edit in self.plan_edits if edit[0] == module)
            if not respelled:
                return True
        return False

    def namespace_literal(self, full, holder=None):
        """Rule D (master decision 2026-11-16): a Name literal that is exactly a
        namespace the map renames respells to its new namespace; one whose plain
        or private form is a generated, non-authored constant under such a
        namespace respells to the new namespace with the same leaf. Anything
        else stays literal (returned unchanged)."""
        renamed = self.renamed_namespace(full)
        if renamed is not None:
            return renamed
        if '.' not in full:
            return full
        parent, leaf = full.rsplit('.', 1)
        renamed = self.renamed_namespace(parent)
        if renamed is None:
            return full
        if not hasattr(self, '_private_users'):
            self._private_users = {}
            for key in self.all_before_constants:
                split = MAP.split_private(key) if key.startswith('_private.') else None
                if split:
                    self._private_users.setdefault((split[0], split[2]), []).append(key)
        # A private form counts only in the module that holds the literal:
        # another module's private declaration says nothing about it.
        module = self.holder_module(holder)
        forms = ([full] if full in self.all_before_constants else []) + (
            self._private_users.get((module, full), []) if module is not None else [])
        if forms and all(form not in self.all_before_roots for form in forms):
            return f'{renamed}.{leaf}'
        return full

    def respell_derived(self, name, target, cls, value):
        """A deriving handler's output follows the rename (master decisions
        2026-11-16): a string literal that is exactly an old fully qualified
        constant name the map renames becomes its new name; a literal that is
        exactly the old label of a field of the derived target structure,
        whose field row changes the leaf, becomes the new label. Any other
        literal is compared as written. Each respelling is recorded."""
        if not isinstance(value, (list, dict)):
            return value
        mapping = self.mapping
        known_consts = self.all_before_constants
        special = self._special_left

        def literal(text):
            if '.' in text and mapping.renames(text) and text in known_consts:
                return mapping(text), 'qualified name'
            field = f'{target}.{text}'
            # Field labels follow the rename only in derived Repr text; a
            # handler's unqualified keys (ToJson/FromJson) stay as written.
            if cls == 'Repr' and field in mapping.exact:
                old_leaf, new_leaf = text, mapping.exact[field].split('.')[-1]
                if new_leaf != old_leaf:
                    return new_leaf, 'field label'
            return None, None

        def renamed_field(body):
            """The field row (old leaf, new leaf) of the derived target whose
            projection `target.f` the nest body reads, when it changes the leaf."""
            for const in _consts(body, []):
                if const.startswith(target + '.') and const in mapping.exact:
                    old_leaf, new_leaf = const.split('.')[-1], mapping.exact[const].split('.')[-1]
                    if old_leaf != new_leaf:
                        return old_leaf, new_leaf
            return None

        def rewrite_width(x, width_old, width_new):
            w_memo = {}
            w_stack = [(x, False)]
            while w_stack:
                cur, ready = w_stack.pop()
                if not isinstance(cur, list):
                    continue
                cid = id(cur)
                if cid in w_memo:
                    continue
                if cur == ['nat', width_old]:
                    w_memo[cid] = ['nat', width_new]
                    continue
                if not ready:
                    w_stack.append((cur, True))
                    for item in reversed(cur):
                        if isinstance(item, list) and id(item) not in w_memo:
                            w_stack.append((item, False))
                else:
                    out = [w_memo[id(y)] if isinstance(y, list) else y for y in cur]
                    w_memo[cid] = cur if all(a is b for a, b in zip(out, cur)) else out
            return w_memo[id(x)] if isinstance(x, list) else x

        memo = {}
        stack = [(value, False)]
        while stack:
            cur, ready = stack.pop()
            cid = id(cur)
            if cid in memo:
                continue
            if isinstance(cur, list):
                if not ready:
                    if (len(cur) == 3 and cur[0] == 'app' and isinstance(cur[1], list) and len(cur[1]) == 3 and
                            cur[1][0] == 'app' and cur[1][1][:2] == ['const', ['name', 'Std.Format.nest']]):
                        field = renamed_field(cur[2]) if cls == 'Repr' else None
                        if field is not None:
                            stack.append((cur, ('nest', field)))
                            if isinstance(cur[2], (list, dict)) and id(cur[2]) not in memo:
                                stack.append((cur[2], False))
                            continue
                    if len(cur) == 2 and cur[0] == 'str' and isinstance(cur[1], str):
                        new, why = literal(cur[1])
                        if new is not None:
                            self.respelled_literals.append([name, cur[1], new, why])
                            memo[cid] = ['str', new]
                        else:
                            memo[cid] = cur
                        continue
                    stack.append((cur, True))
                    for item in reversed(cur):
                        if isinstance(item, (list, dict)) and id(item) not in memo:
                            stack.append((item, False))
                elif isinstance(ready, tuple) and ready[0] == 'nest':
                    field = ready[1]
                    width_old, width_new = len(field[0]) + 4, len(field[1]) + 4
                    indent = rewrite_width(cur[1][2], width_old, width_new)
                    if indent != cur[1][2]:
                        self.respelled_literals.append([name, width_old, width_new, 'field label width'])
                    rhs = memo[id(cur[2])] if isinstance(cur[2], (list, dict)) else cur[2]
                    out = ['app', ['app', cur[1][1], indent], rhs]
                    if cid in special or (isinstance(rhs, (list, dict)) and id(rhs) in special):
                        special.add(id(out))
                    memo[cid] = out
                else:
                    changed = False
                    has_sp = False
                    out = []
                    for item in cur:
                        if isinstance(item, (list, dict)):
                            nx = memo[id(item)]
                            if nx is not item:
                                changed = True
                            if id(nx) in special or id(item) in special:
                                has_sp = True
                            out.append(nx)
                        else:
                            out.append(item)
                    if changed and (has_sp or cid in special):
                        special.add(id(out))
                    memo[cid] = out if changed else cur
            elif isinstance(cur, dict):
                if not ready:
                    stack.append((cur, True))
                    for v in cur.values():
                        if isinstance(v, (list, dict)) and id(v) not in memo:
                            stack.append((v, False))
                else:
                    changed = False
                    has_sp = False
                    out = {}
                    for k, v in cur.items():
                        if isinstance(v, (list, dict)):
                            nv = memo[id(v)]
                            if nv is not v:
                                changed = True
                            if id(nv) in special or id(v) in special:
                                has_sp = True
                            out[k] = nv
                        else:
                            out[k] = v
                    if changed and (has_sp or cid in special):
                        special.add(id(out))
                    memo[cid] = out if changed else cur
        return memo[id(value)]

    def reviewed_quotation(self, left, right, path):
        """A registered, reviewed capture-qualified quotation (master decision
        2026-11-16; scripts/naming-quotations.json): accepted only when a record
        names this generated constant, the before and after spellings, and a
        map row whose old name the quotation pre-resolves to and whose fully
        qualified new name is exactly the after spelling. Pre-resolution is
        still compared. Used records are counted; unused ones are stale."""
        decls = {d[1][1] for d in left[1] if d[0] == 'decl'}
        holder = self.holders[-1] if self.holders else None
        for index, row in enumerate(self.reviewed or []):
            # Bound to the exact constant being compared (not one whose name
            # it prefixes), to the module the record names, and to one
            # occurrence in this comparison.
            if (holder == row['constant'] and self.holder_module(holder) == row['module'] and
                    row['before'] == left[2] and
                    row['after'] == right[2] and row['map_old'] in decls and
                    self.mapping(row['map_old']) == row['map_new'] == right[2]):
                if index in self.reviewed_here:
                    raise Mismatch(f'{path}: reviewed quotation {row["before"]!r} -> {row["after"]!r} of '
                                   f'{row["constant"]} occurs more than once')
                self._undo.append(('rev_here', index))
                self.reviewed_here.add(index)
                if index not in self.reviewed_used:
                    self._undo.append(('rev_used', index))
                    self.reviewed_used.add(index)
                return True
        return False

    def unhygienic_edited(self, module, spelling):
        """Whether the applied plan edits any quoted-identifier range of
        `spelling` in `module`."""
        return any(name == spelling and any(e[3] == spelling for e in self.plan_index.get((module, a, b), []))
                   for a, b, name in (self.before.get('quotation_sites') or {}).get(module, []))

    def unhygienic_binding(self, holder):
        """Bind each unhygienic quoted identifier of the before constant
        `holder` to its own source range (rule E per site): the constant's
        unhygienic identifiers, in kernel order, must be exactly the
        quoted-identifier sequence of one command of its module (`[anonymous]`
        as the empty name). Returns {id(node): (module, start, end)}; raises
        when no command, or several with different plan edits, match."""
        if holder in self._unhygienic_bindings:
            return self._unhygienic_bindings[holder]
        nodes = []
        root_val = self.left.get(holder)
        if root_val is not None:
            stack = [root_val]
            while stack:
                cur = stack.pop()
                if isinstance(cur, list):
                    if len(cur) == 4 and cur[0] == 'unhygienicIdentifier':
                        nodes.append(cur)
                    else:
                        for x in reversed(cur):
                            if isinstance(x, (list, dict)):
                                stack.append(x)
                elif isinstance(cur, dict):
                    for v in reversed(list(cur.values())):
                        if isinstance(v, (list, dict)):
                            stack.append(v)
        module = self.holder_module(holder)
        sites = (self.before.get('quotation_sites') or {}).get(module, [])
        spellings = [n[1] for n in nodes]
        matches = []
        for a, b in (self.before.get('module_commands') or {}).get(module, []):
            inside = [(s, e, '' if n == '[anonymous]' else n) for s, e, n in sites if a <= s < b]
            if [n for _, _, n in inside] == spellings:
                matches.append(inside)
        outcome = lambda inside: [tuple(sorted(e[4] for e in self.plan_index.get((module, s, t), [])
                                               if e[3] == n)) for s, t, n in inside]
        if not matches or any(outcome(m) != outcome(matches[0]) for m in matches[1:]):
            raise Mismatch(f'constant {holder}: unhygienic quoted identifiers {spellings[:8]}... cannot be '
                           f'bound to the quoted ranges of one command of {module} '
                           f'({len(matches)} matching commands)')
        binding = {id(node): (module, s, t) for node, (s, t, _) in zip(nodes, matches[0])}
        self._unhygienic_bindings[holder] = binding
        return binding

    def find(self, module):
        while self.parent.get(module, module) != module:
            module = self.parent[module]
        return module

    def join(self, a, b):
        a, b = self.find(a), self.find(b)
        if a != b:
            self.parent[max(a, b)] = min(a, b)

    def component(self, module, side):
        if module is None:
            return None
        return self.find(self.mapping.module(module) if side == 'before' else module)

    def respell(self, spelling, decl, path):
        """The apply tool's names-only respelling of a quoted spelling of `decl`."""
        new = self.name(decl)
        if new == decl:
            return spelling
        try:
            return APPLY.replacement(spelling, decl, new, self.mapping)
        except ValueError as error:
            raise Mismatch(f'{path}: quoted spelling {spelling!r} of {decl} has no names-only '
                           f'respelling under the map: {error}') from error

    def quoted(self, value, path):
        """Expected after-side spelling and raw marker of a before-side quotation."""
        decoded, spelling, raw = value[1], value[2], value[3]
        expected = set()
        for d in decoded:
            if d[0] != 'decl':
                continue
            fields = d[2] if len(d) > 2 else []
            tail = '.'.join(fields)
            if fields and spelling.endswith('.' + tail) and spelling != tail:
                # Pre-resolved with projections (`coreFrame.trans`): the
                # declaration part respells names-only; the field components
                # stay byte-identical (a renamed field therefore fails).
                head = spelling[:-len(tail) - 1]
                expected.add(self.respell(head, d[1][1], path) + '.' + tail)
            else:
                expected.add(self.respell(spelling, d[1][1], path))
        if len(expected) != 1:
            raise Mismatch(f'{path}: quoted spelling {spelling!r} respells ambiguously: {sorted(expected)}')
        return next(iter(expected)), self.raw_marker(raw, spelling)

    @staticmethod
    def raw_marker(raw, spelling):
        # The raw text is the spelling up to `«»` escapes, or else literal.
        return ['rawSpelling'] if raw and plain_spelling(raw) == spelling else ['raw', raw]

    GENERATED_SUFFIX = re.compile(r'^(match_\d+|eq_\d+|eq_def|splitter|proof_\d+|injEq|inj|sizeOf_spec|'
                                  r'noConfusion|noConfusionType|casesOn|recOn|rec|brecOn|below|ibelow|'
                                  r'binductionOn|ctorIdx|congr_simp|_unfold|_sunfold)$')

    def name(self, name):
        if '@' in name:  # A per-module key for colliding independent roots.
            base, module = name.rsplit('@', 1)
            return f'{self.mapping(base)}@{self.module_of(base, module)}'
        mapped = self.mapping(name)
        if '._aux_' in '.' + mapped and self._aux_modules[1] is not None:
            # Lean names macro/elab auxiliaries after their module
            # (`_aux_<Module_with_underscores>___elabRules_...`): a module row
            # renames that component too, in one pass (a renamed module's
            # new name is never renamed again).
            table, pattern = self._aux_modules
            mapped = pattern.sub(lambda m: m.group(1) + '_aux_' + table[m.group(2)] + '___', mapped)
        if (mapped == name and name in self.all_before_constants and name not in self.all_before_roots and
                '.' in name and not name.startswith('_private.')):
            # A compiler-named constant (a syntax kind `Ns.tacticFoo`) declared
            # inside a namespace the map renames through its members (derived
            # namespace) moves with the namespace syntax, without a row.
            parent, leaf = name.rsplit('.', 1)
            scoped = self.mapping.scope(parent)
            if scoped != parent and parent in self.mapping.derived() and self.uniform_namespace(parent):
                return f'{scoped}.{leaf}'
        if mapped == name and name not in self.all_before_constants:
            # A constant Lean realizes on demand and no export holds (a matcher
            # `P.match_8` behind a private equation lemma) is named after its
            # parent: it follows the parent's exact row when every further
            # component is a compiler-generated suffix.
            parts = name.split('.')
            for i in range(len(parts) - 1, 0, -1):
                parent = '.'.join(parts[:i])
                if parent in self.mapping.exact and all(self.GENERATED_SUFFIX.match(x) for x in parts[i:]):
                    renamed = '.'.join([self.mapping(parent)] + parts[i:])
                    if renamed not in self.all_after_constants:  # absent from both exports
                        return renamed
        return mapped

    @staticmethod
    def aux_module_table(mapping):
        """({mangled old: mangled new}, pattern) for the module component of
        `_aux_` names. Mangling (`.` -> `_`) must be injective over the map's
        module rows on both sides, or the component cannot be read back."""
        table = {}
        for side in (mapping.modules.keys(), mapping.modules.values()):
            seen = {}
            for module in side:
                mangled = module.replace('.', '_')
                if seen.setdefault(mangled, module) != module:
                    raise ValueError(f'module rows {seen[mangled]} and {module} mangle alike in _aux_ names')
        for old, new in mapping.modules.items():
            table[old.replace('.', '_')] = new.replace('.', '_')
        if not table:
            return table, None
        alternatives = '|'.join(re.escape(k) for k in sorted(table, key=len, reverse=True))
        return table, re.compile(r'(^|\.)_aux_(' + alternatives + r')___')

    def module_of(self, name, module):
        private = MAP.split_private(name)
        user = private[2] if private else name
        if user in self.mapping.relocations:
            source, target = self.mapping.relocations[user]
            if source != module:
                raise Mismatch(f'{name}: relocation row names module {source}, but it is in {module}')
            return target
        return self.mapping.module(module)

    RELOC_AUX_LEAF = re.compile(
        r'^(match_\d+|_sparseCasesOn_\d+|eq_\d+|eq_def|else_eq|splitter|congr_simp|_sunfold|_unsafe_rec|_f)$'
    )
    MATCHER_LEAF = re.compile(r'^match_\d+$')
    DOWNSTREAM_EQ_LEAF = re.compile(r'^(eq_\d+|eq_def|else_eq|splitter|congr_simp)$')

    def is_downstream_reloc_eq(self, name, side):
        """A downstream realized equation or splitter auxiliary of a declaration
        in a relocation component (never an anonymous instance or csimp
        replacement), whose references to relocated-component `.match_N`
        helpers may reindex when modules split.

        Memoized per comparison on `(name, side)`: the answer reads only state
        fixed when the comparison is constructed (the map, both constant
        tables, roots, owners and the relocated modules)."""
        cache = self.__dict__.setdefault('_downstream_reloc_eq_cache', {})
        key = (name, side)
        if key not in cache:
            cache[key] = self._is_downstream_reloc_eq(name, side)
        return cache[key]

    def _is_downstream_reloc_eq(self, name, side):
        if not self.mapping.relocations:
            return False
        table = self.left if side == 'before' else self.right
        generated = self.generated_left if side == 'before' else self.generated_right
        if name not in generated:
            return False
        base = name.rsplit('@', 1)[0]
        if '.' not in base:
            return False
        parent, leaf = base.rsplit('.', 1)
        if not self.DOWNSTREAM_EQ_LEAF.match(leaf):
            return False
        attrs = table[name].get('attributes') or {}
        if attrs.get('instance') is not None or attrs.get('csimp'):
            return False
        roots = self.all_before_roots if side == 'before' else self.all_after_roots
        owners = self.all_before_owners if side == 'before' else self.all_after_owners
        private = MAP.split_private(parent) if parent.startswith('_private.') else None
        raw_bases = [parent]
        if private is not None:
            raw_bases.append(private[2])
        cands = []
        for b in raw_bases:
            cands.append(b)
            if '.' in b and self.MATCHER_LEAF.match(b.rsplit('.', 1)[1]):
                cands.append(b.rsplit('.', 1)[0])
        for decl in cands:
            if decl in roots and decl in owners:
                mod = owners[decl]
                mapped = self.mapping.module(mod) if side == 'before' else mod
                if mapped in self.relocated_modules:
                    return True
            if side == 'before':
                for p in self.mapping.public_from:
                    pm = MAP.split_private(p)
                    if pm and pm[2] == decl:
                        mod = owners.get(p) or pm[0]
                        if self.mapping.module(mod) in self.relocated_modules:
                            return True
        return False

    def reloc_matcher_component(self, name, side):
        """If `name` is `.match_N` on a declaration belonging to a relocated
        module component, return that component identifier; otherwise None."""
        if not self.mapping.relocations or '.' not in name:
            return None
        parent, leaf = name.rsplit('.', 1)
        if not self.MATCHER_LEAF.match(leaf):
            return None
        roots = self.all_before_roots if side == 'before' else self.all_after_roots
        owners = self.all_before_owners if side == 'before' else self.all_after_owners
        if parent not in roots or parent not in owners:
            return None
        owner = owners[parent]
        mapped = self.mapping.module(owner) if side == 'before' else owner
        if mapped not in self.relocated_modules:
            return None
        return self.component(owner, side)

    def is_reloc_aux(self, name, side):
        """A compiler-generated pattern-match or equation auxiliary scoped
        entirely to relocation-linked modules (never an anonymous instance or
        csimp replacement), which Lean's per-module deduplication cache may
        split across a module boundary."""
        if not self.mapping.relocations:
            return False
        table = self.left if side == 'before' else self.right
        generated = self.generated_left if side == 'before' else self.generated_right
        if name not in generated:
            return False
        leaf = name.rsplit('@', 1)[0].rsplit('.', 1)[-1]
        if not self.RELOC_AUX_LEAF.match(leaf):
            return False
        attrs = table[name].get('attributes') or {}
        if attrs.get('instance') is not None or attrs.get('csimp'):
            return False
        holders = self.all_before_holders if side == 'before' else self.all_after_holders
        mods = holders.get(name)
        if not mods:
            return False
        mapped = {self.mapping.module(m) if side == 'before' else m for m in mods}
        return bool(mapped <= self.relocated_modules)

    def is_promoted_matcher(self, a, b=None):
        """A `match_N` helper of a `private` declaration promoted via
        `public_from`: Lean gives private matchers `semireducible` and public
        matchers `instanceReducible`."""
        if a not in self.generated_left or not a.startswith('_private.') or '.' not in a:
            return False
        parent, leaf = a.rsplit('.', 1)
        if not (self.MATCHER_LEAF.match(leaf) and parent in self.mapping.public_from):
            return False
        if b is None:
            return True
        return (b in self.generated_right and not b.startswith('_private.') and
                self.MATCHER_LEAF.match(b.rsplit('.', 1)[-1]) is not None)

    def is_realized_reloc_matcher(self, b, a=None):
        """An unexported `match_N` of a relocated declaration realized on demand
        behind its `eq_def`, paired to a verified generated matcher of that
        declaration on the before side."""
        if not self.mapping.relocations or b in self.right or '.' not in b or b.startswith('_private.'):
            return False
        parent, leaf = b.rsplit('.', 1)
        if not (self.MATCHER_LEAF.match(leaf) and parent in self._reloc_targets):
            return False
        if a is None:
            return True
        if a not in self.generated_left or '.' not in a:
            return False
        ap, aleaf = a.rsplit('.', 1)
        return bool(self.MATCHER_LEAF.match(aleaf) and self.name(ap) == parent)

    def pair_realized_matcher(self, a, new_parent):
        if a in self.pairs or a in self.aux_left:
            return True
        by_parent = self._gen_right_by_parent
        if by_parent is None:
            by_parent = defaultdict(list)
            for exported in sorted(self.generated_right):
                if '.' in exported and self.MATCHER_LEAF.match(exported.rsplit('.', 1)[-1]):
                    by_parent[exported.rsplit('.', 1)[0]].append(exported)
            self._gen_right_by_parent = by_parent
        for exported in by_parent.get(new_parent, ()):
            saved = self.save()
            try:
                self.pair(a, exported)
                return True
            except Mismatch:
                self.restore(saved)
        return False

    @staticmethod
    def _fmt_path(p):
        parts = []
        while isinstance(p, tuple):
            parts.append(p[1])
            p = p[0]
        parts.append(str(p))
        parts.reverse()
        return ''.join(parts)

    def coarse_record(self, name, side):
        rec = (self.left if side == 'before' else self.right)[name]
        norm = self.normalize(rec, side, True, downstream_eq=self.is_downstream_reloc_eq(name, side))
        if side == 'before' and self.is_promoted_matcher(name):
            attrs = dict(norm.get('attributes') or {})
            if attrs.get('reducibility') == 'Lean.ReducibilityStatus.semireducible':
                attrs['reducibility'] = 'Lean.ReducibilityStatus.instanceReducible'
                norm = dict(norm, attributes=attrs)
        return dag_digest(norm)

    def compare(self, left, right, path):
        downstream_flag = bool(
            self.holder_pairs and
            self.is_downstream_reloc_eq(self.holder_pairs[-1][0], 'before') and
            self.is_downstream_reloc_eq(self.holder_pairs[-1][1], 'after')
        )
        reloc_aux_holder_flag = bool(self.holders and self.is_reloc_aux(self.holders[-1], 'before'))
        ctx_key = (downstream_flag, reloc_aux_holder_flag)
        special_left, special_right = self._special_left, self._special_right
        eq_cache = self._expr_eq_cache
        stack = [('cmp', left, right, path, False)]
        while stack:
            frame = stack.pop()
            if frame[0] == 'cache':
                _, ck, c_left, c_right = frame
                if ck not in eq_cache:
                    self._undo.append(('eq_cache', ck))
                    eq_cache[ck] = (c_left, c_right)
                continue
            _, cur_l, cur_r, cur_p, in_kernel = frame
            if in_kernel and isinstance(cur_l, (list, dict)) and isinstance(cur_r, (list, dict)):
                lid, rid = id(cur_l), id(cur_r)
                if lid not in special_left and rid not in special_right:
                    if (lid, rid, ctx_key) in eq_cache:
                        continue
            if isinstance(cur_l, list) and len(cur_l) == 4 and cur_l[0] == 'unhygienicIdentifier':
                p_str = self._fmt_path(cur_p)
                if not (isinstance(cur_r, list) and len(cur_r) == 4 and cur_r[0] == 'unhygienicIdentifier'):
                    raise Mismatch(f'{p_str}: unhygienic quoted identifier changed kind')
                # What the applied plan did at this identifier's own quoted range
                # decides (rule E per site): never edited -> unchanged; edited ->
                # the plan's new text, which must also be the names-only
                # respelling. A spelling the plan edits nowhere in the holder's
                # module needs no binding: it stays as written.
                holder = self.holders[-1] if self.holders else None
                module = self.holder_module(holder)
                expected, site = cur_l[1], None
                if module is not None and self.unhygienic_edited(module, cur_l[1]):
                    site = self.unhygienic_binding(holder).get(id(cur_l))
                    if site is None:
                        raise Mismatch(f'{p_str}: unhygienic quoted identifier {cur_l[1]!r} has no bound source range')
                    news = {e[4] for e in self.plan_index.get(site, []) if e[3] == cur_l[1]}
                    if len(news) > 1:
                        raise Mismatch(f'{p_str}: plan respells unhygienic {cur_l[1]!r} at {site} ambiguously: {sorted(news)}')
                    if news:
                        expected = news.pop()
                        if expected != self.respell_message(cur_l[1], p_str):
                            raise Mismatch(f'{p_str}: plan respelled unhygienic {cur_l[1]!r} to {expected!r}, '
                                           f'not its names-only respelling')
                elif module is None and self.plan_edits:
                    raise Mismatch(f'{p_str}: unhygienic quoted identifier {cur_l[1]!r} outside a known module')
                if cur_r[1] != expected:
                    raise Mismatch(f'{p_str}: unhygienic quoted spelling {cur_l[1]!r} became {cur_r[1]!r}, '
                                   f'expected {expected!r} (its own quoted range {site})')
                if self.raw_marker(cur_r[2], cur_r[1]) != self.raw_marker(cur_l[2], cur_l[1]):
                    raise Mismatch(f'{p_str}: unhygienic quoted raw text {cur_l[2]!r} became {cur_r[2]!r}')
                if cur_r[1] != cur_l[1]:
                    ukey = (cur_l[1], cur_r[1], site)
                    if ukey not in self.unhygienic_sites:
                        self._undo.append(('unhyg', ukey))
                        self.unhygienic_sites[ukey] = site
                stack.append(('cmp', cur_l[3], cur_r[3], (cur_p, '.syntax'), in_kernel))
                continue
            if isinstance(cur_l, list) and len(cur_l) == 5 and cur_l[0] == 'quotedIdentifier':
                p_str = self._fmt_path(cur_p)
                if not (isinstance(cur_r, list) and len(cur_r) == 5 and cur_r[0] == 'quotedIdentifier'):
                    raise Mismatch(f'{p_str}: quoted identifier changed kind')
                spelling, raw = self.quoted(cur_l, p_str)
                if cur_r[2] != spelling and self.reviewed_quotation(cur_l, cur_r, p_str):
                    spelling = cur_r[2]
                if cur_r[2] != spelling:
                    raise Mismatch(f'{p_str}: quoted spelling {cur_l[2]!r} became {cur_r[2]!r}, '
                                   f'expected {spelling!r} (Syntax.getId observes it)')
                if self.raw_marker(cur_r[3], cur_r[2]) != raw:
                    raise Mismatch(f'{p_str}: quoted raw text {cur_l[3]!r} became {cur_r[3]!r}')
                if cur_r[2] == cur_l[2] and cur_r[3] != cur_l[3]:
                    # An unchanged spelling keeps its raw text, `«»` escapes included.
                    raise Mismatch(f'{p_str}: quoted raw text {cur_l[3]!r} became {cur_r[3]!r} under an unchanged spelling')
                stack.append(('cmp', cur_l[4], cur_r[4], (cur_p, '.syntax'), in_kernel))
                stack.append(('cmp', cur_l[1], cur_r[1], (cur_p, '.preresolved'), in_kernel))
                continue
            if isinstance(cur_l, list) and len(cur_l) == 2 and cur_l[0] == 'name':
                if not isinstance(cur_r, list) or len(cur_r) != 2 or cur_r[0] != 'name':
                    raise Mismatch(f'{self._fmt_path(cur_p)}: name reference changed kind')
                a, b = cur_l[1], cur_r[1]
                if downstream_flag:
                    ca = self.reloc_matcher_component(a, 'before')
                    cb = self.reloc_matcher_component(b, 'after')
                    if ca is not None and cb is not None and ca == cb:
                        if (a, b) not in self.realized_matcher_pairs:
                            self._undo.append(('realized', (a, b)))
                            self.realized_matcher_pairs.add((a, b))
                        continue
                if a in self.generated_left:
                    holder = self.holders[-1] if self.holders else None
                    if (b not in self.generated_right and holder is not None and
                            reloc_aux_holder_flag and
                            self.is_realized_reloc_matcher(b, a) and
                            self.pair_realized_matcher(a, b.rsplit('.', 1)[0])):
                        continue
                    if b not in self.generated_right:
                        raise Mismatch(f'{self._fmt_path(cur_p)}: generated reference became named/external')
                    self.pair(a, b)
                elif a in self.external_aux_classes:
                    if b not in self.external_aux_classes[a]:
                        raise Mismatch(f'{self._fmt_path(cur_p)}: external generated auxiliary {a} became {b}')
                elif a in self.external_gen_pairs:
                    if self.external_gen_pairs[a] != b:
                        raise Mismatch(f'{self._fmt_path(cur_p)}: external generated constant {a} became {b}')
                elif self.name(a) != b:
                    raise Mismatch(f'{self._fmt_path(cur_p)}: reference {a} became {b}')
                continue
            if (not in_kernel and
                    cur_l == 'Lean.ReducibilityStatus.semireducible' and
                    cur_r == 'Lean.ReducibilityStatus.instanceReducible' and
                    self.holder_pairs and self.is_promoted_matcher(*self.holder_pairs[-1]) and
                    self._fmt_path(cur_p).endswith('.attributes.reducibility')):
                continue
            if type(cur_l) is not type(cur_r):
                raise Mismatch(f'{self._fmt_path(cur_p)}: node kind changed')
            if isinstance(cur_l, dict):
                if cur_l.keys() != cur_r.keys():
                    raise Mismatch(f'{self._fmt_path(cur_p)}: object fields changed')
                if in_kernel and id(cur_l) not in special_left and id(cur_r) not in special_right:
                    stack.append(('cache', (id(cur_l), id(cur_r), ctx_key), cur_l, cur_r))
                for key in reversed(list(cur_l.keys())):
                    child_kernel = in_kernel or (key == 'kernel')
                    stack.append(('cmp', cur_l[key], cur_r[key], (cur_p, f'.{key}'), child_kernel))
            elif isinstance(cur_l, list):
                if len(cur_l) != len(cur_r):
                    raise Mismatch(f'{self._fmt_path(cur_p)}: array length changed')
                if in_kernel and id(cur_l) not in special_left and id(cur_r) not in special_right:
                    stack.append(('cache', (id(cur_l), id(cur_r), ctx_key), cur_l, cur_r))
                for i in range(len(cur_l) - 1, -1, -1):
                    stack.append(('cmp', cur_l[i], cur_r[i], (cur_p, f'[{i}]'), in_kernel))
            elif cur_l != cur_r:
                raise Mismatch(f'{self._fmt_path(cur_p)}: {cur_l!r} became {cur_r!r}')

    def pair(self, a, b):
        left_holders, right_holders = self.all_before_holders, self.all_after_holders
        same_reloc_component = (
            self._has_holders_info and
            {self.component(m, 'before') for m in left_holders.get(a, ())} ==
            {self.component(m, 'after') for m in right_holders.get(b, ())}
        )
        if self.is_reloc_aux(a, 'before') and self.is_reloc_aux(b, 'after') and same_reloc_component:
            if a in self.pairs or b in self.reverse:
                raise Mismatch(f'inconsistent generated-constant correspondence: {a}, {b}')
            if (a, b) not in self.aux_pairs:
                self._undo.append(('aux_pair', a, b, a in self.aux_left, b in self.aux_right))
                self.aux_pairs.add((a, b))
                self.aux_left.add(a)
                self.aux_right.add(b)
        else:
            if (self.pairs.get(a, b) != b or self.reverse.get(b, a) != a or
                    a in self.aux_left or b in self.aux_right):
                raise Mismatch(f'inconsistent generated-constant correspondence: {a}, {b}')
            if a not in self.pairs:
                self._undo.append(('pair', a, b))
                self.pairs[a], self.reverse[b] = b, a
        if (a, b) in self.checked:
            return
        self._undo.append(('checked', (a, b)))
        self.checked.add((a, b))
        self.holders.append(a)
        self.holder_pairs.append((a, b))
        try:
            self.compare(self.left[a], self.right[b], f'constant {a}')
        finally:
            self.holder_pairs.pop()
            self.holders.pop()

    GUARD_TOKEN = re.compile(r"(?<![\w.'?!])[A-Za-z_][\w'?!]*(?:\.[A-Za-z_][\w'?!]*)*")

    def respell_message(self, text, path):
        """A `#guard_msgs` expected text with every whole qualified-name token
        respelled by the map, under the names-only rule of `respell` (master
        decision 2026-11-16, G0a). A token that still ends some constant name
        after the rename (or a local variable's) stays; a stale token denotes
        the before constants whose names it ends with (component-wise), and
        all of them must give one respelling, or it is ambiguous."""
        if not hasattr(self, '_suffixes'):
            self._suffixes = {}
            for name in self.all_before_constants:
                base = name.rsplit('@', 1)[0]
                private = MAP.split_private(base)
                user = private[2] if private else base
                parts = APPLY.split_name(user)
                for k in range(1, len(parts) + 1):
                    self._suffixes.setdefault('.'.join(parts[-k:]), set()).add(base)

        if not hasattr(self, '_after_suffixes'):
            self._after_suffixes = set()
            for name in self.all_after_constants:
                base = name.rsplit('@', 1)[0]
                private = MAP.split_private(base)
                parts = APPLY.split_name(private[2] if private else base)
                self._after_suffixes.update('.'.join(parts[-k:]) for k in range(1, len(parts) + 1))

        def one(match):
            token = match.group(0)
            if token in self._after_suffixes:
                # Still a name after the rename (a local such as `y`, an
                # unrenamed constant): kept as written.
                return token
            spellings = set()
            for decl in self._suffixes.get(token, ()):
                spellings.add(self.respell(token, decl, path))
            if len(spellings) > 1:
                raise Mismatch(f'{path}: #guard_msgs token {token!r} respells ambiguously: {sorted(spellings)}')
            return spellings.pop() if spellings else token
        return self.GUARD_TOKEN.sub(one, text)

    def aux_canonical(self):
        if not hasattr(self, '_aux_rep_cache') or self._aux_rep_key != len(self.aux_pairs):
            parent = {}
            def find(x):
                while parent.get(x, x) != x:
                    x = parent[x]
                return x
            rights = defaultdict(set)
            for a, b in self.aux_pairs:
                parent.setdefault(a, a)
                parent.setdefault(b, b)
                ra, rb = find(a), find(b)
                if ra != rb:
                    parent[rb] = ra
            for _, b in self.aux_pairs:
                rights[find(b)].add(b)
            rep = {r: min(bs) for r, bs in rights.items()}
            self._aux_rep_cache = ({x: rep[find(x)] for x in parent}, len(self.aux_pairs))
            self._aux_rep_key = len(self.aux_pairs)
        return self._aux_rep_cache[0]

    def normalize(self, value, side, coarse=False, downstream_eq=False):
        if not isinstance(value, (list, dict)):
            return value
        memo = self._norm_coarse_cache.setdefault((side, downstream_eq), {}) if coarse else {}
        if id(value) in memo:
            return memo[id(value)]
        generated = self.generated_left if side == 'before' else self.generated_right
        aux_side = (self.aux_left if side == 'before' else self.aux_right) if not coarse else ()
        aux_canon = self.aux_canonical() if (not coarse and aux_side) else {}
        stack = [(value, False)]
        while stack:
            cur, ready = stack.pop()
            cid = id(cur)
            if cid in memo:
                continue
            if isinstance(cur, dict):
                if not ready:
                    stack.append((cur, True))
                    for v in cur.values():
                        if isinstance(v, (list, dict)) and id(v) not in memo:
                            stack.append((v, False))
                else:
                    memo[cid] = {k: (memo[id(v)] if isinstance(v, (list, dict)) else v) for k, v in cur.items()}
            elif isinstance(cur, list):
                if not ready:
                    if (side == 'before' and len(cur) == 3 and cur[:2] == ['syntax', 'Lean.guardMsgsCmd'] and
                            isinstance(cur[2], list) and cur[2] and isinstance(cur[2][0], list)):
                        doc = cur[2][0]
                        if (len(doc) == 3 and doc[:2] == ['syntax', 'null'] and len(doc[2]) == 1 and
                                isinstance(doc[2][0], list) and
                                doc[2][0][:2] == ['syntax', 'Lean.Parser.Command.docComment'] and
                                len(doc[2][0][2]) == 2 and doc[2][0][2][1][0] == 'atom'):
                            text = doc[2][0][2][1][1]
                            respelled = ['syntax', 'null', [['syntax', 'Lean.Parser.Command.docComment',
                                                             [doc[2][0][2][0], ['atom', self.respell_message(text, 'guard_msgs')]]]]]
                            stack.append((cur, ('guardMsgs', respelled)))
                            for item in reversed(cur[2][1:]):
                                if isinstance(item, (list, dict)) and id(item) not in memo:
                                    stack.append((item, False))
                            continue
                    if len(cur) == 4 and cur[0] == 'unhygienicIdentifier':
                        stack.append((cur, 'unhyg'))
                        if isinstance(cur[3], (list, dict)) and id(cur[3]) not in memo:
                            stack.append((cur[3], False))
                        continue
                    if len(cur) == 5 and cur[0] == 'quotedIdentifier':
                        stack.append((cur, 'quoted'))
                        for idx in (4, 1):
                            if isinstance(cur[idx], (list, dict)) and id(cur[idx]) not in memo:
                                stack.append((cur[idx], False))
                        continue
                    if len(cur) == 2 and cur[0] == 'name':
                        name = cur[1]
                        if coarse and downstream_eq and self.reloc_matcher_component(name, side) is not None:
                            memo[cid] = ['generated']
                        elif coarse and side == 'after' and self.is_realized_reloc_matcher(name):
                            memo[cid] = ['generated']
                        elif name in generated and coarse:
                            memo[cid] = ['generated']
                        elif side == 'before' and name in self.external_before_aux_rep:
                            memo[cid] = ['name', self.external_before_aux_rep[name]]
                        elif side == 'after' and name in self.external_after_aux_rep:
                            memo[cid] = ['name', self.external_after_aux_rep[name]]
                        elif side == 'before' and name in self.external_gen_pairs:
                            memo[cid] = ['name', self.external_gen_pairs[name]]
                        elif not coarse and name in aux_side and aux_canon.get(name) is not None:
                            memo[cid] = ['name', aux_canon[name]]
                        else:
                            mapped_gen = self.pairs.get(name)
                            memo[cid] = ['name', mapped_gen if side == 'before' and name in generated and mapped_gen is not None
                                         else self.name(name) if side == 'before' else name]
                        continue
                    stack.append((cur, True))
                    for item in reversed(cur):
                        if isinstance(item, (list, dict)) and id(item) not in memo:
                            stack.append((item, False))
                elif isinstance(ready, tuple) and ready[0] == 'guardMsgs':
                    memo[cid] = ['syntax', 'Lean.guardMsgsCmd',
                                 [ready[1]] + [memo[id(it)] if isinstance(it, (list, dict)) else it
                                               for it in cur[2][1:]]]
                elif ready == 'unhyg':
                    sub = memo[id(cur[3])] if isinstance(cur[3], (list, dict)) else cur[3]
                    if coarse:
                        memo[cid] = ['unhygienicIdentifier', sub]
                    else:
                        memo[cid] = ['unhygienicIdentifier', cur[1], self.raw_marker(cur[2], cur[1]), sub]
                elif ready == 'quoted':
                    c1 = memo[id(cur[1])] if isinstance(cur[1], (list, dict)) else cur[1]
                    c4 = memo[id(cur[4])] if isinstance(cur[4], (list, dict)) else cur[4]
                    spelling, raw = (self.quoted(cur, 'normalize') if side == 'before'
                                     else (cur[2], self.raw_marker(cur[3], cur[2])))
                    memo[cid] = ['quotedIdentifier', c1, spelling, raw, c4]
                else:
                    memo[cid] = [memo[id(it)] if isinstance(it, (list, dict)) else it for it in cur]
        return memo[id(value)]

    def compare_imports(self):
        """Direct imports of every module that no relocation row touches are
        unchanged under module rows. Imports of relocation modules may change
        (a moved declaration brings its imports), elsewhere only by edges to
        relocation modules (a user of the moved declaration imports its new
        module), except `Batteries.Tactic.OpenPrivate` when a private helper was
        promoted via `public_from`."""
        touched = self.relocated_modules
        after = self.after.get('modules') or {}
        for module, imports in sorted((self.before.get('modules') or {}).items()):
            target = self.mapping.module(module)
            if target in touched:
                continue
            if target not in after:
                raise Mismatch(f'module {module} (as {target}) is missing after renaming')
            expected = [[self.mapping.module(entry[0])] + list(entry[1:]) for entry in imports
                        if self.mapping.module(entry[0]) not in touched]
            actual = [list(entry) for entry in after[target] if entry[0] not in touched]
            if self.mapping.public_from and 'Batteries.Tactic.OpenPrivate' not in [e[0] for e in actual]:
                expected = [e for e in expected if e[0] != 'Batteries.Tactic.OpenPrivate']
            if expected != actual:
                raise Mismatch(f'module {module}: direct imports changed: expected '
                               f'{[e[0] for e in expected]}, found {[e[0] for e in actual]}')

    def preferred_generated(self, name):
        mapped = self.name(name)
        if mapped != name:
            return mapped
        private = MAP.split_private(name) if name.startswith('_private.') else None
        user = private[2] if private else name
        parts = user.split('.')
        for i in range(len(parts) - 1, 0, -1):
            parent = '.'.join(parts[:i])
            if parent in self.mapping.exact and all(self.GENERATED_SUFFIX.match(x) for x in parts[i:]):
                renamed = '.'.join([self.mapping(parent)] + parts[i:])
                if private:
                    return f'_private.{self.mapping.module(private[0])}.{private[1]}.{renamed}'
                return renamed
        return mapped

    def save(self):
        """Record O(1) journal watermark before a speculative `pair()`."""
        return len(self._undo), len(self.respelled_literals)

    def restore(self, saved):
        undo_len, lit_len = saved
        while len(self._undo) > undo_len:
            op = self._undo.pop()
            kind = op[0]
            if kind == 'pair':
                self.pairs.pop(op[1], None)
                self.reverse.pop(op[2], None)
            elif kind == 'checked':
                self.checked.discard(op[1])
            elif kind == 'aux_pair':
                self.aux_pairs.discard((op[1], op[2]))
                if not op[3]:
                    self.aux_left.discard(op[1])
                if not op[4]:
                    self.aux_right.discard(op[2])
            elif kind == 'realized':
                self.realized_matcher_pairs.discard(op[1])
            elif kind == 'rev_here':
                self.reviewed_here.discard(op[1])
            elif kind == 'rev_used':
                self.reviewed_used.discard(op[1])
            elif kind == 'unhyg':
                self.unhygienic_sites.pop(op[1], None)
            elif kind == 'eq_cache':
                self._expr_eq_cache.pop(op[1], None)
        del self.respelled_literals[lit_len:]

    def fail(self, message):
        """Raise at the first mismatch, or with `collect` record every one and
        raise them together at the end (the verdict fails either way)."""
        if not self.collect:
            raise Mismatch(message)
        self.problems.append(message)

    def _substantive_closure(self, table, roots, guards, attributes, checks, external_refs):
        """Compute all constants required by N4 matching: roots, non-theorem or
        attributed constants, outside REALIZED_THM_LEAF, externally referenced names,
        and anything transitively reachable from them or guards/checks/attributes."""
        substantive = set(roots) & table.keys()
        for name, rec in table.items():
            if not is_realized_theorem_candidate(name, rec, roots):
                substantive.add(name)
            elif name in external_refs:
                substantive.add(name)
        item_refs = set()
        item_visited = set()
        for seq in (guards, attributes, checks):
            collect_const_refs(seq, item_refs, item_visited)
        for ref in item_refs:
            if ref in table:
                substantive.add(ref)
        queue = list(substantive)
        seen_recs = set(queue)
        visited_nodes = set()
        while queue:
            cur = queue.pop()
            refs = set()
            collect_const_refs(table[cur], refs, visited_nodes)
            for ref in refs:
                if ref in table and ref not in seen_recs:
                    seen_recs.add(ref)
                    substantive.add(ref)
                    queue.append(ref)
        return substantive

    def run(self):
        substantive_before = self._substantive_closure(
            self.before['constants'], self.before['roots'],
            self.before.get('guards', ()), self.before.get('attributes', ()),
            self.before.get('checks', ()), self.externally_referenced_before)
        substantive_after = self._substantive_closure(
            self.after['constants'], self.after['roots'],
            self.after.get('guards', ()), self.after.get('attributes', ()),
            self.after.get('checks', ()), self.externally_referenced_after)
        self.generated_left = (self.left.keys() & substantive_before) - self.before['roots']
        self.generated_right = (self.right.keys() & substantive_after) - self.after['roots']
        self.ignored_realized_before = sorted(self.left.keys() - substantive_before)
        self.ignored_realized_after = sorted(self.right.keys() - substantive_after)
        self._downstream_reloc_eq_cache = {}
        self._norm_coarse_cache = {}
        self._gen_right_by_parent = defaultdict(list)
        for g in sorted(self.generated_right):
            if '.' in g and self.MATCHER_LEAF.match(g.rsplit('.', 1)[-1]):
                self._gen_right_by_parent[g.rsplit('.', 1)[0]].append(g)

        expected = {self.name(n) for n in self.before['roots']}
        if len(expected) != len(self.before['roots']) or expected != self.after['roots']:
            self.fail(f'authored constant set changed: missing={sorted(expected - self.after["roots"])}, extra={sorted(self.after["roots"] - expected)}')
        for name in sorted(self.before['roots']):
            try:
                self.pair(name, self.name(name))
            except (Mismatch, KeyError) as error:
                self.fail(f'constant {name}: {error}')
        # Moving a declaration is part of the map: every authored constant
        # stays in its (renamed) module unless a relocation row moves it.
        left_owner, right_owner = self.all_before_owners, self.all_after_owners
        if (self.before.get('owners') is not None or (self._global_context and 'before_owners' in self._global_context)) and \
                (self.after.get('owners') is not None or (self._global_context and 'after_owners' in self._global_context)):
            for name in sorted(self.before['roots']):
                base = name.rsplit('@', 1)[0]
                if name in left_owner and self.name(name) in right_owner:
                    expected = self.module_of(base, left_owner[name])
                    if right_owner[self.name(name)] != expected:
                        self.fail(f'{name}: module {left_owner[name]} became '
                                  f'{right_owner[self.name(name)]}, expected {expected}')
        for private in self.scoped_public_from:
            if private not in self.before['roots']:
                self.fail(f'public_from names no authored private declaration in scope: {private}')
        for row in sorted(self.scoped_relocations):
            if not any(MAP.split_private(n)[2] == row if MAP.split_private(n) else n == row
                       for n in self.before['roots']):
                self.fail(f'relocation row {row} names no authored constant in scope')
        # Generated constants are not compared by name. Match their finite
        # kernel/attribute graphs bijectively (modulo relocation-scoped pattern
        # and equation auxiliaries, which Lean may split across module boundaries).
        left_holders, right_holders = self.all_before_holders, self.all_after_holders
        buckets = defaultdict(list)
        for name in sorted(self.generated_right):
            try:
                buckets[self.coarse_record(name, 'after')].append(name)
            except Mismatch as error:
                self.fail(f'constant {name} (after): {error}')
        for name in sorted(self.generated_left):
            if name in self.pairs or name in self.aux_left:
                continue
            try:
                key = self.coarse_record(name, 'before')
            except Mismatch as error:
                self.fail(f'constant {name}: {error}')
                continue
            is_aux = self.is_reloc_aux(name, 'before')
            fresh = [n for n in buckets[key] if n not in self.reverse and n not in self.aux_right]
            shared = [n for n in buckets[key] if n in self.aux_right] if is_aux else []
            candidates = fresh + shared
            if self.is_downstream_reloc_eq(name, 'before') and self._has_holders_info and name in left_holders:
                wanted_holders = {self.component(m, 'before') for m in left_holders[name]}
                same_h = [c for c in candidates if c in right_holders and
                          {self.component(m, 'after') for m in right_holders[c]} == wanted_holders]
                other_h = [c for c in candidates if c not in same_h]
                candidates = same_h + other_h
            same, same_error = self.preferred_generated(name), None
            if same in self.generated_right and same not in self.reverse and (is_aux or same not in self.aux_right):
                candidates = [n for n in candidates if n != same]
                saved = self.save()
                try:
                    self.pair(name, same)
                    continue
                except Mismatch as error:
                    same_error = error
                    self.restore(saved)
            for candidate in candidates:
                saved = self.save()
                try:
                    self.pair(name, candidate)
                    break
                except Mismatch:
                    self.restore(saved)
            else:
                self.fail(f'no verified generated-constant match for {name}' +
                          (f'; same-name comparison: {same_error}' if same_error else ''))
        left_buckets = None
        for name in sorted(self.generated_right):
            if name in self.reverse or name in self.aux_right:
                continue
            if not self.is_reloc_aux(name, 'after'):
                continue
            if left_buckets is None:
                left_buckets = defaultdict(list)
                for lname in sorted(self.generated_left):
                    if self.is_reloc_aux(lname, 'before'):
                        left_buckets[self.coarse_record(lname, 'before')].append(lname)
            key = self.coarse_record(name, 'after')
            for candidate in left_buckets[key]:
                saved = self.save()
                try:
                    self.pair(candidate, name)
                    break
                except Mismatch:
                    self.restore(saved)
        if (self.after['roots'] | self.generated_right) != (self.reverse.keys() | self.aux_right):
            self.fail('additional generated constants after renaming')
        # Generated constants (equation lemmas, compiler-named instances) stay
        # in the modules that hold them, up to module and relocation rows.
        if self._has_holders_info:
            for a, b in sorted(self.pairs.items() | self.aux_pairs):
                if a not in self.generated_left or a not in left_holders or b not in right_holders:
                    continue
                was = {self.component(m, 'before') for m in left_holders[a]}
                now = {self.component(m, 'after') for m in right_holders[b]}
                if was != now:
                    self.fail(f'generated constant {a} (now {b}): modules {sorted(left_holders[a])} '
                              f'became {sorted(right_holders[b])}')
        # Checks, guards and attribute commands stay in their (renamed) module,
        # or move only between the two modules of a relocation row.
        for key in ITEMS:
            def tagged(snapshot, side):
                items = snapshot.get(key, [])
                owners = (snapshot.get('item_modules') or {}).get(key) or [None] * len(items)
                if len(owners) != len(items):
                    raise ValueError(f'{key}: module record does not match its items')
                counted = Counter()
                for index, (m, item) in enumerate(zip(owners, items)):
                    try:
                        counted[(self.component(m, side), dag_digest(self.normalize(item, side)))] += 1
                    except Mismatch as error:
                        if not self.collect:
                            raise
                        self.fail(f'{key}[{side} {index}, module {m}]: {error}')
                return counted
            left, right = tagged(self.before, 'before'), tagged(self.after, 'after')
            if left != right:
                where = sorted({comp or '<module unrecorded>' for comp, _ in (left - right) + (right - left)})
                self.fail(f'{key}: expression/command multiset changed (missing {sum((left-right).values())}, '
                          f'extra {sum((right-left).values())}; modules {where})')
        try:
            self.compare_imports()
        except Mismatch as error:
            self.fail(str(error))
        if self.problems:
            raise Mismatch(f'{len(self.problems)} mismatch(es):\n' + '\n'.join(self.problems))
        return dict(status='OK', scope='exported-modules',
                    authored_constants=len(self.before['roots']), generated_constants=len(self.generated_left),
                    relocated_auxiliary_pairs=len(self.aux_pairs),
                    guards=len(self.before['guards']), attribute_commands=len(self.before['attributes']),
                    checked_commands=len(self.before.get('checks', [])),
                    derived_literals_respelled=self.respelled_literals,
                    ignored_unreferenced_realized_theorems=dict(
                        before=self.ignored_realized_before,
                        after=self.ignored_realized_after))


def check(before, after, mapping, reviewed=None, reviewed_used=None, collect=False, plan_edits=None,
          global_context=None, external=None, state=None):
    MAP.validate_map(mapping)
    if before['version'] != after['version']:
        raise ValueError('Lean versions differ')
    renames = MAP.Renamer(mapping['entries'])
    # Imports are reported, not silently treated as a proof about their contents.
    comparison = Comparison(before, after, renames, reviewed, reviewed_used, collect, plan_edits,
                            global_context=global_context, external=external)
    result = comparison.run()
    if state is not None:
        state['comparison'] = comparison
    result['unhygienic_respellings'] = [
        dict(old=old, new=new, module=site[0], range=[site[1], site[2]],
             expansion_declarations=expansion_declarations(before, site[0], old))
        for (old, new, _), site in sorted(comparison.unhygienic_sites.items(), key=lambda kv: (kv[0][0], kv[0][1], kv[1]))]
    result.update(before=before['receipts'], after=after['receipts'],
                  before_imports=before['modules'], after_imports=after['modules'],
                  before_dot_identifiers_resolved=before.get('dot_identifiers_resolved', 0),
                  after_dot_identifiers_resolved=after.get('dot_identifiers_resolved', 0),
                  before_coalesced_equations=before.get('coalesced_equations', []),
                  after_coalesced_equations=after.get('coalesced_equations', []))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--map', type=Path, required=True)
    parser.add_argument('--before', type=Path, action='append', required=True)
    parser.add_argument('--after', type=Path, action='append', required=True)
    args = parser.parse_args()
    try:
        raw = args.map.read_bytes()
        result = check(read_exports(args.before), read_exports(args.after), json.loads(raw))
        result['map_sha256'] = hashlib.sha256(raw).hexdigest()
        print(json.dumps(result, indent=2))
        return 0
    except Mismatch as error:
        print(f'REGRESSION — naming fidelity: {error}', file=sys.stderr)
        return 1
    except (OSError, ValueError, KeyError, TypeError, RecursionError) as error:
        print(f'SETUP — naming fidelity: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
