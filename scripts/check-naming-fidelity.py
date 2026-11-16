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
        text = [source_bytes[x:y].decode('utf-8', 'replace') for x, y, kind in commands if x <= start < y]
        clause = re.compile(r'\bderiving\b[^\n]*\b' + re.escape(cls) + r'\b')
        leaf = re.escape(target.split('.')[-1])
        instance_cmd = [source_bytes[x:y].decode('utf-8', 'replace') for x, y, kind in commands
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
        data['constants'] = {n: quoted_identifiers(c) for n, c in data['constants'].items()}
        data['guards'] = [quoted_identifiers(g) for g in data['guards']]
        coalesced |= merge_constants(constants, roots, data['constants'], names)
        roots.update(names)
        for name in data['constants']:
            owners.setdefault(name, module)
            holders.setdefault(name, set()).add(module)

        def syntax(value, literal_names=False):
            if not isinstance(value, list):
                return value
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
                item_modules=item_modules, schemas=schemas, derived=derived)


class Comparison:
    def __init__(self, before, after, mapping, reviewed=None, reviewed_used=None):
        self.before, self.after = before, after
        self.reviewed = reviewed
        self.reviewed_used = reviewed_used if reviewed_used is not None else set()
        if isinstance(mapping, dict):  # An exact old -> new table.
            mapping = MAP.Renamer([dict(old=a, new=b, kind='declaration') for a, b in mapping.items()])
        self.mapping = mapping
        self.left = dict(before['constants'])
        self.right = after['constants']
        self.respelled_literals = []
        for name in list(self.left):
            self.left[name] = self.respell_name_literals(name, self.left[name])
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
            if isinstance(e, dict):
                return {k: walk(v) for k, v in e.items()}
            if not isinstance(e, list):
                return e
            if len(e) == 3 and e[0] == 'app':
                head, args = chain(e)
                if (isinstance(head, list) and head[:1] == ['const'] and isinstance(head[1], list) and
                        re.fullmatch(r'Lean\.Name\.mkStr[1-8]', head[1][1]) and
                        len(args) == int(head[1][1][-1]) and
                        all(isinstance(a, list) and len(a) == 2 and a[0] == 'str' for a in args)):
                    full = '.'.join(a[1] for a in args)
                    new_full = self.name(full) if full in known else full
                    if new_full != full:
                        parts = new_full.split('.')
                        if len(parts) <= 8:
                            self.respelled_literals.append([name, full, new_full, 'name literal'])
                            out = ['const', ['name', f'Lean.Name.mkStr{len(parts)}'], head[2]]
                            for part in parts:
                                out = ['app', out, ['str', part]]
                            return out
            return [walk(x) for x in e]
        return walk(value)

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
                return [walk(x) for x in e]
            if isinstance(e, dict):
                return {k: walk(v) for k, v in e.items()}
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
        for index, row in enumerate(self.reviewed or []):
            if (path.startswith(f'constant {row["constant"]}.') and row['before'] == left[2] and
                    row['after'] == right[2] and row['map_old'] in decls and
                    self.mapping(row['map_old']) == row['map_new'] == right[2]):
                self.reviewed_used.add(index)
                return True
        return False

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
        decls = [d[1][1] for d in decoded if d[0] == 'decl']
        expected = {self.respell(spelling, d, path) for d in decls}
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
        if '._aux_' in '.' + mapped:
            # Lean names macro/elab auxiliaries after their module
            # (`_aux_<Module_with_underscores>___elabRules_...`): a module row
            # renames that component too.
            for old, new in self.mapping.modules.items():
                mangled_old, mangled_new = old.replace('.', '_'), new.replace('.', '_')
                mapped = re.sub(r'(^|\.)_aux_' + re.escape(mangled_old) + r'___',
                                lambda m: m.group(1) + '_aux_' + mangled_new + '___', mapped)
        if (mapped == name and name in self.left and name not in self.before['roots'] and '.' in name
                and not name.startswith('_private.')):
            # A compiler-named constant (a syntax kind `Ns.tacticFoo`) declared
            # inside a namespace the map renames through its members (derived
            # namespace) moves with the namespace syntax, without a row.
            parent, leaf = name.rsplit('.', 1)
            scoped = self.mapping.scope(parent)
            if scoped != parent and parent in self.mapping.derived():
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
        self.compare(self.left[a], self.right[b], f'constant {a}')

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

    def run(self):
        expected = {self.name(n) for n in self.before['roots']}
        if len(expected) != len(self.before['roots']) or expected != self.after['roots']:
            raise Mismatch(f'authored constant set changed: missing={sorted(expected - self.after["roots"])}, extra={sorted(self.after["roots"] - expected)}')
        for name in sorted(self.before['roots']):
            self.pair(name, self.name(name))
        # Moving a declaration is part of the map: every authored constant
        # stays in its (renamed) module unless a relocation row moves it.
        left_owner, right_owner = self.before.get('owners'), self.after.get('owners')
        if left_owner is not None and right_owner is not None:
            for name in sorted(self.before['roots']):
                base = name.rsplit('@', 1)[0]
                if name in left_owner and self.name(name) in right_owner:
                    expected = self.module_of(base, left_owner[name])
                    if right_owner[self.name(name)] != expected:
                        raise Mismatch(f'{name}: module {left_owner[name]} became '
                                       f'{right_owner[self.name(name)]}, expected {expected}')
        for row, (source, target) in sorted(self.mapping.relocations.items()):
            if not any(MAP.split_private(n)[2] == row if MAP.split_private(n) else n == row
                       for n in self.before['roots']):
                raise Mismatch(f'relocation row {row} names no authored constant in scope')
        # Generated constants are not compared by name. Match their finite
        # kernel/attribute graphs bijectively, including unreferenced nodes.
        buckets = defaultdict(list)
        for name in sorted(self.generated_right):
            buckets[encoded(self.normalize(self.right[name], 'after', True))].append(name)
        for name in sorted(self.generated_left):
            if name in self.pairs:
                continue
            key = encoded(self.normalize(self.left[name], 'before', True))
            candidates = [n for n in buckets[key] if n not in self.reverse]
            # Try the same (mapped) name first: for a compiler-named declaration
            # (an anonymous instance) its comparison explains a failure.
            same, same_error = self.name(name), None
            if same in self.generated_right and same not in self.reverse and same not in candidates:
                saved = self.pairs.copy(), self.reverse.copy(), self.checked.copy()
                try:
                    self.pair(name, same)
                    continue
                except Mismatch as error:
                    same_error = error
                    self.pairs, self.reverse, self.checked = saved
            for candidate in candidates:
                saved = self.pairs.copy(), self.reverse.copy(), self.checked.copy()
                try:
                    self.pair(name, candidate)
                    break
                except Mismatch:
                    self.pairs, self.reverse, self.checked = saved
            else:
                raise Mismatch(f'no verified generated-constant match for {name}' +
                               (f'; same-name comparison: {same_error}' if same_error else ''))
        if self.right.keys() != self.reverse.keys():
            raise Mismatch('additional generated constants after renaming')
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
                    raise Mismatch(f'generated constant {a} (now {b}): modules {sorted(left_holders[a])} '
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
                return Counter(encoded([self.component(m, side), self.normalize(item, side)])
                               for m, item in zip(owners, items))
            left, right = tagged(self.before, 'before'), tagged(self.after, 'after')
            if left != right:
                where = sorted({json.loads(k)[0] or '<module unrecorded>' for k in (left - right) + (right - left)})
                raise Mismatch(f'{key}: expression/command multiset changed (missing {sum((left-right).values())}, '
                               f'extra {sum((right-left).values())}; modules {where})')
        self.compare_imports()
        return dict(status='OK', scope='exported-modules',
                    authored_constants=len(self.before['roots']), generated_constants=len(self.generated_left),
                    guards=len(self.before['guards']), attribute_commands=len(self.before['attributes']),
                    checked_commands=len(self.before.get('checks', [])),
                    derived_literals_respelled=self.respelled_literals)


def check(before, after, mapping, reviewed=None, reviewed_used=None):
    MAP.validate_map(mapping)
    if before['version'] != after['version']:
        raise ValueError('Lean versions differ')
    renames = MAP.Renamer(mapping['entries'])
    # Imports are reported, not silently treated as a proof about their contents.
    result = Comparison(before, after, renames, reviewed, reviewed_used).run()
    result.update(before=before['receipts'], after=after['receipts'],
                  before_imports=before['modules'], after_imports=after['modules'],
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
