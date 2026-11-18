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
# Schema 7 keys explicit attributes per declaration and records elaboration
# attributes beyond the first tracked set and instance order; the candidate
# workflow requires it, the low-level comparator still reads archived exports.
SCHEMAS = (3, 4, 5, 6, 7)
CURRENT_SCHEMA = 7


def load(filename):
    spec = importlib.util.spec_from_file_location(filename, ROOT / 'scripts' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


MAP = load('check-naming-map.py')
APPLY = load('apply-naming-map.py')


def encoded(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


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


def _spelling(val):
    """(components, wrapper) of a quotation's `val`: a name literal, possibly
    under `Lean.addMacroScope mainModule NAME scopes`."""
    head, args = _unwind(val)
    if head == 'Lean.addMacroScope' and len(args) == 3:
        parts = _name(args[1])
        return (None, None) if parts is None else (parts, ['addMacroScope', quoted_identifiers(args[0]),
                                                           quoted_identifiers(args[2])])
    parts = _name(val)
    return parts, None


def plain_spelling(raw):
    """A raw identifier spelling without `«»` escapes, as `getId` reports it."""
    return '.'.join(part[1:-1] if part.startswith('«') and part.endswith('»') else part
                    for part in APPLY.split_name(raw)) if raw else raw


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
    if isinstance(e, dict):
        return {k: quoted_identifiers(v) for k, v in e.items()}
    if not isinstance(e, list):
        return e
    if e and e[0] == 'app':
        head, args = _unwind(e)
        if head == 'Lean.Syntax.ident' and len(args) == 4:
            items = _list(args[3])
            decoded = None if items is None else [_preresolved(x) for x in items]
            if decoded == []:
                # Unhygienic quotation (`local macro` without hygiene): no
                # pre-resolution and a plain Name value. Resolved by spelling
                # at the expansion site; rule E compares the spelling.
                info, raw, val, _ = args
                raw_head, raw_args = _unwind(raw)
                raw_text = _lit(raw_args[0]) if raw_head in RAW_SUBSTRING and len(raw_args) == 1 else None
                parts = _name(val)
                if raw_text is not None and parts is not None and plain_spelling(raw_text) == '.'.join(parts):
                    return ['unhygienicIdentifier', '.'.join(parts), raw_text, [raw_head, quoted_identifiers(info)]]
            if decoded and None not in decoded and any(d[0] == 'decl' for d in decoded):
                info, raw, val, _ = args
                raw_head, raw_args = _unwind(raw)
                raw_text = _lit(raw_args[0]) if raw_head in RAW_SUBSTRING and len(raw_args) == 1 else None
                parts, wrapper = _spelling(val)
                if raw_text is not None and parts is not None and all('.' not in p for p in parts):
                    return ['quotedIdentifier', decoded, '.'.join(parts), raw_text,
                            [raw_head, wrapper, quoted_identifiers(info)]]
                # An unrecognized spelling shape keeps the literal expression
                # (fails closed under any rename of the declaration it names).
    return [quoted_identifiers(x) for x in e]


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
                existing[name] != incoming[name]):
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
    if isinstance(e, list):
        if len(e) == 3 and e[0] == 'const' and isinstance(e[1], list) and e[1][:1] == ['name']:
            found.append(e[1][1])
        for x in e:
            _consts(x, found)
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
        if not (isinstance(kernel, list) and kernel and kernel[0] == 'definition'):
            continue
        names = _consts(kernel[2], [])
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
        derived.update(derived_constants(data, None, byte_offsets, positions))
        char_of = {b: i for i, b in enumerate(byte_offsets)}
        quotation_sites[module] = [(char_of[a], char_of[b], n) for a, b, n in
                                   data['index'].get('naming_syntax', {}).get('quotation_identifiers', [])
                                   if a in char_of and b in char_of]
        module_sources[module] = data['source']
        module_commands[module] = [(char_of[r[0]], char_of[r[1]]) for r in
                                   data['index'].get('naming_syntax', {}).get('commands', [])
                                   if r[0] in char_of and r[1] in char_of]
        module_decls[module] = {n: APPLY.span(positions, loc[:4]) for n, loc in data['index']['decls'].items()}
        data['constants'] = {n: quoted_identifiers(c) for n, c in data['constants'].items()}
        data['guards'] = [quoted_identifiers(g) for g in data['guards']]
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
                module_sources=module_sources, module_decls=module_decls, module_commands=module_commands)


class Comparison:
    def __init__(self, before, after, mapping, reviewed=None, reviewed_used=None, collect=False, plan_edits=None):
        self.before, self.after = before, after
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
        # Modules (after naming) that a relocation row links: a row moves its
        # declaration, and checks or generated constants may move with it,
        # between its two modules and nowhere else.
        self.parent = {}
        self.relocated_modules = set()
        for source, target in mapping.relocations.values():
            self.relocated_modules |= {mapping.module(source), target}
            self.join(mapping.module(source), target)

    def respell_name_literals(self, name, value):
        """A `Name` literal (`Lean.Name.mkStrN "A" ... "Z"`) whose full name is
        exactly an old constant the map renames is that constant's name: Lean
        resolves a double-backtick literal (``Pres``) to the full name, and
        renaming the constant respells it. It is compared as the new name
        (fewer or more components change N); every respelling is recorded."""
        mapping, known = self.mapping, self.before['constants']

        def chain(e):
            args = []
            while isinstance(e, list) and len(e) == 3 and e[0] == 'app':
                args.append(e[2])
                e = e[1]
            return e, list(reversed(args))

        def walk(e):
            # Copy on change only: an unchanged subtree is returned as is, so
            # comparing many environments does not duplicate their graphs.
            if isinstance(e, dict):
                out = {k: walk(v) for k, v in e.items()}
                return e if all(out[k] is e[k] for k in e) else out
            if not isinstance(e, list):
                return e
            if len(e) == 3 and e[0] == 'app':
                head, args = chain(e)
                if (isinstance(head, list) and head[:1] == ['const'] and isinstance(head[1], list) and
                        re.fullmatch(r'Lean\.Name\.mkStr[1-8]', head[1][1]) and
                        len(args) == int(head[1][1][-1]) and
                        all(isinstance(a, list) and len(a) == 2 and a[0] == 'str' for a in args) and
                        # Each argument must be one plain component: a
                        # component holding a dot (`Name.mkStr1 "A.B"`) is not
                        # the dotted name `A.B` and stays literal.
                        all(a[1] and '.' not in a[1] and '«' not in a[1] for a in args)):
                    full = '.'.join(a[1] for a in args)
                    new_full = self.name(full) if full in known else full
                    why = 'name literal'
                    if new_full == full:
                        new_full, why = self.namespace_literal(full, name), 'namespace literal'
                    if new_full != full and '«' not in new_full and not self.data_literal(name, full, new_full):
                        parts = new_full.split('.')
                        if len(parts) <= 8:
                            self.respelled_literals.append([name, full, new_full, why])
                            out = ['const', ['name', f'Lean.Name.mkStr{len(parts)}'], head[2]]
                            for part in parts:
                                out = ['app', out, ['str', part]]
                            return out
            out = [walk(x) for x in e]
            return e if all(a is b for a, b in zip(out, e)) else out
        return walk(value)

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
            for root in self.before['roots'] if ok else ():
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
        owners = self.before.get('owners')
        return None if owners is None or holder is None else owners.get(holder)

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
            for key in self.left:
                split = MAP.split_private(key) if key.startswith('_private.') else None
                if split:
                    self._private_users.setdefault((split[0], split[2]), []).append(key)
        # A private form counts only in the module that holds the literal:
        # another module's private declaration says nothing about it.
        module = self.holder_module(holder)
        forms = ([full] if full in self.left else []) + (
            self._private_users.get((module, full), []) if module is not None else [])
        if forms and all(form not in self.before['roots'] for form in forms):
            return f'{renamed}.{leaf}'
        return full

    def respell_derived(self, name, target, cls, value):
        """A deriving handler's output follows the rename (master decisions
        2026-11-16): a string literal that is exactly an old fully qualified
        constant name the map renames becomes its new name; a literal that is
        exactly the old label of a field of the derived target structure,
        whose field row changes the leaf, becomes the new label. Any other
        literal is compared as written. Each respelling is recorded."""
        mapping = self.mapping

        def literal(text):
            if '.' in text and mapping.renames(text) and text in self.before['constants']:
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

        def walk(e):
            if isinstance(e, list):
                # `{ f := v }` in a derived Repr nests v by the label's width
                # (`f := ` is len(f) + 4): it follows the label's respelling.
                if (len(e) == 3 and e[0] == 'app' and isinstance(e[1], list) and len(e[1]) == 3 and
                        e[1][0] == 'app' and e[1][1][:2] == ['const', ['name', 'Std.Format.nest']]):
                    field = renamed_field(e[2]) if cls == 'Repr' else None
                    if field is not None:
                        width_old, width_new = len(field[0]) + 4, len(field[1]) + 4
                        def width(x):
                            if x == ['nat', width_old]:
                                return ['nat', width_new]
                            return [width(y) for y in x] if isinstance(x, list) else x
                        indent = width(e[1][2])
                        if indent != e[1][2]:
                            self.respelled_literals.append([name, width_old, width_new, 'field label width'])
                        return ['app', ['app', e[1][1], indent], walk(e[2])]
                if len(e) == 2 and e[0] == 'str' and isinstance(e[1], str):
                    new, why = literal(e[1])
                    if new is not None:
                        self.respelled_literals.append([name, e[1], new, why])
                        return ['str', new]
                    return e
                out = [walk(x) for x in e]
                return e if all(a is b for a, b in zip(out, e)) else out
            if isinstance(e, dict):
                out = {k: walk(v) for k, v in e.items()}
                return e if all(out[k] is e[k] for k in e) else out
            return e
        return walk(value)

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
                self.reviewed_here.add(index)
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

        def walk(e):
            if isinstance(e, list):
                if len(e) == 4 and e[0] == 'unhygienicIdentifier':
                    nodes.append(e)
                    return
                for x in e:
                    walk(x)
            elif isinstance(e, dict):
                for v in e.values():
                    walk(v)
        walk(self.left.get(holder))
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
        if (mapped == name and name in self.left and name not in self.before['roots'] and '.' in name
                and not name.startswith('_private.')):
            # A compiler-named constant (a syntax kind `Ns.tacticFoo`) declared
            # inside a namespace the map renames through its members (derived
            # namespace) moves with the namespace syntax, without a row.
            parent, leaf = name.rsplit('.', 1)
            scoped = self.mapping.scope(parent)
            if scoped != parent and parent in self.mapping.derived() and self.uniform_namespace(parent):
                return f'{scoped}.{leaf}'
        if mapped == name and name not in self.left:
            # A constant Lean realizes on demand and no export holds (a matcher
            # `P.match_8` behind a private equation lemma) is named after its
            # parent: it follows the parent's exact row when every further
            # component is a compiler-generated suffix.
            parts = name.split('.')
            for i in range(len(parts) - 1, 0, -1):
                parent = '.'.join(parts[:i])
                if parent in self.mapping.exact and all(self.GENERATED_SUFFIX.match(x) for x in parts[i:]):
                    renamed = '.'.join([self.mapping(parent)] + parts[i:])
                    if renamed not in self.right:  # absent from both exports
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

    def compare(self, left, right, path):
        if isinstance(left, list) and len(left) == 4 and left[0] == 'unhygienicIdentifier':
            if not (isinstance(right, list) and len(right) == 4 and right[0] == 'unhygienicIdentifier'):
                raise Mismatch(f'{path}: unhygienic quoted identifier changed kind')
            # What the applied plan did at this identifier's own quoted range
            # decides (rule E per site): never edited -> unchanged; edited ->
            # the plan's new text, which must also be the names-only
            # respelling. A spelling the plan edits nowhere in the holder's
            # module needs no binding: it stays as written.
            holder = self.holders[-1] if self.holders else None
            module = self.holder_module(holder)
            expected, site = left[1], None
            if module is not None and self.unhygienic_edited(module, left[1]):
                site = self.unhygienic_binding(holder).get(id(left))
                if site is None:
                    raise Mismatch(f'{path}: unhygienic quoted identifier {left[1]!r} has no bound source range')
                news = {e[4] for e in self.plan_index.get(site, []) if e[3] == left[1]}
                if len(news) > 1:
                    raise Mismatch(f'{path}: plan respells unhygienic {left[1]!r} at {site} ambiguously: {sorted(news)}')
                if news:
                    expected = news.pop()
                    if expected != self.respell_message(left[1], path):
                        raise Mismatch(f'{path}: plan respelled unhygienic {left[1]!r} to {expected!r}, '
                                       f'not its names-only respelling')
            elif module is None and self.plan_edits:
                raise Mismatch(f'{path}: unhygienic quoted identifier {left[1]!r} outside a known module')
            if right[1] != expected:
                raise Mismatch(f'{path}: unhygienic quoted spelling {left[1]!r} became {right[1]!r}, '
                               f'expected {expected!r} (its own quoted range {site})')
            if self.raw_marker(right[2], right[1]) != self.raw_marker(left[2], left[1]):
                raise Mismatch(f'{path}: unhygienic quoted raw text {left[2]!r} became {right[2]!r}')
            if right[1] != left[1]:
                self.unhygienic_sites.setdefault((left[1], right[1], site), site)
            self.compare(left[3], right[3], f'{path}.syntax')
            return
        if isinstance(left, list) and len(left) == 5 and left[0] == 'quotedIdentifier':
            if not (isinstance(right, list) and len(right) == 5 and right[0] == 'quotedIdentifier'):
                raise Mismatch(f'{path}: quoted identifier changed kind')
            spelling, raw = self.quoted(left, path)
            if right[2] != spelling and self.reviewed_quotation(left, right, path):
                spelling = right[2]
            if right[2] != spelling:
                raise Mismatch(f'{path}: quoted spelling {left[2]!r} became {right[2]!r}, '
                               f'expected {spelling!r} (Syntax.getId observes it)')
            if self.raw_marker(right[3], right[2]) != raw:
                raise Mismatch(f'{path}: quoted raw text {left[3]!r} became {right[3]!r}')
            if right[2] == left[2] and right[3] != left[3]:
                # An unchanged spelling keeps its raw text, `«»` escapes included.
                raise Mismatch(f'{path}: quoted raw text {left[3]!r} became {right[3]!r} under an unchanged spelling')
            self.compare(left[1], right[1], f'{path}.preresolved')
            self.compare(left[4], right[4], f'{path}.syntax')
            return
        if isinstance(left, list) and len(left) == 2 and left[0] == 'name':
            if not isinstance(right, list) or len(right) != 2 or right[0] != 'name':
                raise Mismatch(f'{path}: name reference changed kind')
            a, b = left[1], right[1]
            if a in self.generated_left:
                if b not in self.generated_right:
                    raise Mismatch(f'{path}: generated reference became named/external')
                self.pair(a, b)
            elif self.name(a) != b:
                raise Mismatch(f'{path}: reference {a} became {b}')
            return
        if type(left) is not type(right):
            raise Mismatch(f'{path}: node kind changed')
        if isinstance(left, dict):
            if left.keys() != right.keys():
                raise Mismatch(f'{path}: object fields changed')
            for key in left:
                self.compare(left[key], right[key], f'{path}.{key}')
        elif isinstance(left, list):
            if len(left) != len(right):
                raise Mismatch(f'{path}: array length changed')
            for i, (a, b) in enumerate(zip(left, right)):
                self.compare(a, b, f'{path}[{i}]')
        elif left != right:
            raise Mismatch(f'{path}: {left!r} became {right!r}')

    def pair(self, a, b):
        if self.pairs.get(a, b) != b or self.reverse.get(b, a) != a:
            raise Mismatch(f'inconsistent generated-constant correspondence: {a}, {b}')
        self.pairs[a], self.reverse[b] = b, a
        if (a, b) in self.checked:
            return
        self.checked.add((a, b))
        self.holders.append(a)
        try:
            self.compare(self.left[a], self.right[b], f'constant {a}')
        finally:
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
            for name in self.left:
                base = name.rsplit('@', 1)[0]
                private = MAP.split_private(base)
                user = private[2] if private else base
                parts = APPLY.split_name(user)
                for k in range(1, len(parts) + 1):
                    self._suffixes.setdefault('.'.join(parts[-k:]), set()).add(base)

        if not hasattr(self, '_after_suffixes'):
            self._after_suffixes = set()
            for name in self.right:
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

    def normalize(self, value, side, coarse=False):
        if isinstance(value, dict):
            return {k: self.normalize(v, side, coarse) for k, v in value.items()}
        if not isinstance(value, list):
            return value
        if (side == 'before' and len(value) == 3 and value[:2] == ['syntax', 'Lean.guardMsgsCmd'] and
                isinstance(value[2], list) and value[2] and isinstance(value[2][0], list)):
            # The expected messages are compared as the before text respelled
            # by the map; anything beyond that respelling is a difference.
            doc = value[2][0]
            if (len(doc) == 3 and doc[:2] == ['syntax', 'null'] and len(doc[2]) == 1 and
                    doc[2][0][:2] == ['syntax', 'Lean.Parser.Command.docComment'] and
                    len(doc[2][0][2]) == 2 and doc[2][0][2][1][0] == 'atom'):
                text = doc[2][0][2][1][1]
                respelled = ['syntax', 'null', [['syntax', 'Lean.Parser.Command.docComment',
                                                 [doc[2][0][2][0], ['atom', self.respell_message(text, 'guard_msgs')]]]]]
                return ['syntax', 'Lean.guardMsgsCmd',
                        [respelled] + [self.normalize(item, side, coarse) for item in value[2][1:]]]
        if len(value) == 4 and value[0] == 'unhygienicIdentifier':
            if coarse:  # bucketing only; the exact rule runs in compare()
                return ['unhygienicIdentifier', self.normalize(value[3], side, coarse)]
            # Outside a compared constant (guards, checks) no source range can
            # bind it: the spelling is compared as written.
            spelling = value[1]
            return ['unhygienicIdentifier', spelling, self.raw_marker(value[2], value[1]),
                    self.normalize(value[3], side, coarse)]
        if len(value) == 5 and value[0] == 'quotedIdentifier':
            spelling, raw = (self.quoted(value, 'normalize') if side == 'before'
                             else (value[2], self.raw_marker(value[3], value[2])))
            return ['quotedIdentifier', self.normalize(value[1], side, coarse), spelling, raw,
                    self.normalize(value[4], side, coarse)]
        if len(value) == 2 and value[0] == 'name':
            name = value[1]
            generated = self.generated_left if side == 'before' else self.generated_right
            if name in generated and coarse:
                return ['generated']
            return ['name', self.pairs[name] if side == 'before' and name in generated
                    else self.name(name) if side == 'before' else name]
        return [self.normalize(item, side, coarse) for item in value]

    def compare_imports(self):
        """Direct imports of every module that no relocation row touches are
        unchanged under module rows. Imports of relocation modules may change
        (a moved declaration brings its imports), elsewhere only by edges to
        relocation modules (a user of the moved declaration imports its new
        module)."""
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
        """Every piece of state a speculative `pair()` may change."""
        return (self.pairs.copy(), self.reverse.copy(), self.checked.copy(), set(self.reviewed_used),
                set(self.reviewed_here), dict(self.unhygienic_sites), list(self.respelled_literals))

    def restore(self, saved):
        (self.pairs, self.reverse, self.checked, used, here, sites, literals) = saved
        # reviewed_used is shared with the caller across environments: restore in place.
        self.reviewed_used.clear()
        self.reviewed_used.update(used)
        self.reviewed_here, self.unhygienic_sites, self.respelled_literals = here, sites, literals

    def fail(self, message):
        """Raise at the first mismatch, or with `collect` record every one and
        raise them together at the end (the verdict fails either way)."""
        if not self.collect:
            raise Mismatch(message)
        self.problems.append(message)

    def run(self):
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
        left_owner, right_owner = self.before.get('owners'), self.after.get('owners')
        if left_owner is not None and right_owner is not None:
            for name in sorted(self.before['roots']):
                base = name.rsplit('@', 1)[0]
                if name in left_owner and self.name(name) in right_owner:
                    expected = self.module_of(base, left_owner[name])
                    if right_owner[self.name(name)] != expected:
                        self.fail(f'{name}: module {left_owner[name]} became '
                                       f'{right_owner[self.name(name)]}, expected {expected}')
        for private in self.mapping.public_from:
            if private not in self.before['roots']:
                self.fail(f'public_from names no authored private declaration in scope: {private}')
        for row, (source, target) in sorted(self.mapping.relocations.items()):
            if not any(MAP.split_private(n)[2] == row if MAP.split_private(n) else n == row
                       for n in self.before['roots']):
                self.fail(f'relocation row {row} names no authored constant in scope')
        # Generated constants are not compared by name. Match their finite
        # kernel/attribute graphs bijectively, including unreferenced nodes.
        buckets = defaultdict(list)
        for name in sorted(self.generated_right):
            try:
                buckets[encoded(self.normalize(self.right[name], 'after', True))].append(name)
            except Mismatch as error:
                self.fail(f'constant {name} (after): {error}')
        for name in sorted(self.generated_left):
            if name in self.pairs:
                continue
            try:
                key = encoded(self.normalize(self.left[name], 'before', True))
            except Mismatch as error:
                self.fail(f'constant {name}: {error}')
                continue
            candidates = [n for n in buckets[key] if n not in self.reverse]
            # Try the same (mapped) name first: for a compiler-named declaration
            # (an anonymous instance) its comparison explains a failure. A
            # generated auxiliary (`P.match_5`) is tried first as its renamed
            # parent's auxiliary with the same suffix: structurally identical
            # matchers of different modules must not cross (a preference only;
            # equality and holders are still checked).
            same, same_error = self.preferred_generated(name), None
            if same in self.generated_right and same not in self.reverse:
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
        if self.right.keys() != self.reverse.keys():
            self.fail('additional generated constants after renaming')
        # Generated constants (equation lemmas, compiler-named instances) stay
        # in the modules that hold them, up to module and relocation rows.
        left_holders, right_holders = self.before.get('holders'), self.after.get('holders')
        if left_holders is not None and right_holders is not None:
            for a, b in sorted(self.pairs.items()):
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
                # The after side keeps its names; normalizing it only reduces a
                # quoted identifier's raw text to its spelling marker.
                counted = Counter()
                for index, (m, item) in enumerate(zip(owners, items)):
                    try:
                        counted[encoded([self.component(m, side), self.normalize(item, side)])] += 1
                    except Mismatch as error:
                        if not self.collect:
                            raise
                        self.fail(f'{key}[{side} {index}, module {m}]: {error}')
                return counted
            left, right = tagged(self.before, 'before'), tagged(self.after, 'after')
            if left != right:
                where = sorted({json.loads(k)[0] or '<module unrecorded>' for k in (left - right) + (right - left)})
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
                    guards=len(self.before['guards']), attribute_commands=len(self.before['attributes']),
                    checked_commands=len(self.before.get('checks', [])),
                    derived_literals_respelled=self.respelled_literals)


def check(before, after, mapping, reviewed=None, reviewed_used=None, collect=False, plan_edits=None):
    MAP.validate_map(mapping)
    if before['version'] != after['version']:
        raise ValueError('Lean versions differ')
    renames = MAP.Renamer(mapping['entries'])
    # Imports are reported, not silently treated as a proof about their contents.
    comparison = Comparison(before, after, renames, reviewed, reviewed_used, collect, plan_edits)
    result = comparison.run()
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
