#!/usr/bin/env python3
"""Plan conservative Lean renames from compiler references; apply a reviewed plan.

Run the NamingReferences exporter against current owned-build imports first.
Each bundle carries the exact source it elaborated, including local references.
Preserve the import build receipt with the plan. Planning
never edits sources. Unknown spellings, missing indices and overlapping edits
are failures, not invitations to replace a word globally.
"""
import argparse
import hashlib
import importlib.util
import bisect
import json
from pathlib import Path
import re
import sys


def _load_validator():
    path = Path(__file__).with_name('check-naming-map.py')
    spec = importlib.util.spec_from_file_location('naming_schema', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


MAP = _load_validator()
IDENT_PART = re.compile(r"«[^»]*»|[^\W\d][\w'!?]*")


def components(text, start, end):
    """Component spans of an identifier-shaped reference; None for a compound span.

    Only an identifier occurrence can cover a candidate word. A compiler
    reference whose range spans a whole expression (Lean records a lifted
    `(← e)` discriminant as one local variable) is not an occurrence of the
    identifiers inside it and neither covers nor conflicts with them.
    """
    i = start + (1 if text.startswith('.', start) else 0)
    spans = []
    while i < end:
        match = IDENT_PART.match(text, i, end)
        if not match:
            return None
        spans.append((match.start(), match.end()))
        i = match.end()
        if i < end:
            if text[i] != '.':
                return None
            i += 1
            if i == end:
                return None
    return spans or None


def digest(data):
    return hashlib.sha256(data).hexdigest()


def safe_path(root, relative):
    path = Path(relative)
    if path.is_absolute() or '..' in path.parts:
        raise ValueError(f'not a tree-relative path: {relative}')
    result = root / path
    if result.resolve() != result.absolute():
        raise ValueError(f'symlink path refused: {relative}')
    return result


class Positions:
    """Index source once; large modules have tens of thousands of references."""
    def __init__(self, text):
        self.lines = text.splitlines(keepends=True)
        self.starts = [0]
        for line in self.lines:
            self.starts.append(self.starts[-1] + len(line))
        self.cache = {}

    def __call__(self, line, column):
        if not isinstance(line, int) or not isinstance(column, int) or line < 0 or column < 0:
            raise ValueError('invalid LSP position')
        if line == len(self.lines) and column == 0:
            return self.starts[-1]
        if line >= len(self.lines):
            raise ValueError('LSP line outside source (stale index)')
        if line not in self.cache:
            offsets, units = {0: self.starts[line]}, 0
            for index, char in enumerate(self.lines[line]):
                units += 2 if ord(char) > 0xffff else 1
                offsets[units] = self.starts[line] + index + 1
            self.cache[line] = offsets
        if column not in self.cache[line]:
            raise ValueError('LSP column outside source or splits a surrogate pair (stale index)')
        return self.cache[line][column]


def position(text, line, column):
    return Positions(text)(line, column)


def span(positions, location):
    if not isinstance(location, list) or len(location) not in (4, 5):
        raise ValueError('unsupported ilean location')
    start = positions(*location[:2])
    end = positions(*location[2:4])
    if start >= end:
        raise ValueError('empty or inverted reference range')
    return start, end


def raw_identifier_words(text, start):
    """Conservative candidate discovery when no parser classification exists."""
    i = start
    while i < len(text):
        if text[i].isalpha() or text[i] == '_':
            begin = i
            i += 1
            while i < len(text) and (text[i].isalnum() or text[i] in "_'?!"):
                i += 1
            yield begin, i, text[begin:i]
        else:
            i += 1


def mask_literals(text, index):
    metadata = index.get('naming_syntax')
    if metadata is None:
        return text, []
    if metadata.get('version') not in (1, 2):
        raise ValueError('unsupported naming syntax metadata')
    offsets = byte_offsets(text)
    spans = []
    for row in metadata['literal_ranges']:
        if (not isinstance(row, list) or len(row) != 4 or
                type(row[0]) is not int or type(row[1]) is not int or
                row[2] not in ('str', 'char', 'interpolatedStrLitKind') or
                not isinstance(row[3], str)):
            raise ValueError('invalid literal range')
        a, b, _, raw = row
        if a not in offsets or b not in offsets or a >= b:
            raise ValueError('literal range outside source or splits UTF-8')
        a, b = offsets[a], offsets[b]
        if text[a:b] != raw:
            raise ValueError('literal range source mismatch')
        spans.append((a, b))
    spans.sort()
    if any(right[0] < left[1] for left, right in zip(spans, spans[1:])):
        raise ValueError('overlapping literal ranges')
    masked = list(text)
    for a, b in spans:
        for i in range(a, b):
            if masked[i] not in '\r\n':
                masked[i] = ' '
    return ''.join(masked), spans


def identifiers(text):
    """Lex identifier components, skipping nested comments and plain strings.

    Compiler-proven literal ranges are masked before indexed planning. Without
    that metadata, a string with an unescaped opening brace triggers raw scanning
    of the remaining source: nested quotes must not hide embedded uses or later declarations.
    This may overselect unindexed files; it grants no semantic resolution.
    """
    i = 0
    while i < len(text):
        if text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end + 1
        elif text.startswith('/-', i):
            depth = 1
            i += 2
            while depth and i < len(text):
                if text.startswith('/-', i):
                    depth += 1
                    i += 2
                elif text.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError('unterminated comment')
        elif text[i] == '"':
            end = i + 1
            while end < len(text) and text[end] != '"':
                if text[end] == '{':
                    # The parser may be invoked by any syntax, not only s!.
                    # Without its ranges, this can be an embedded expression.
                    yield from raw_identifier_words(text, i + 1)
                    return
                end += 2 if text[end] == '\\' else 1
            if end >= len(text):
                raise ValueError('unterminated string')
            i = end + 1
        elif text[i] == '«':
            end = text.find('»', i + 1)
            if end < 0:
                raise ValueError('unterminated escaped identifier')
            yield i, end + 1, text[i + 1:end]
            i = end + 1
        elif text[i].isdigit():
            # A numeric literal (`0x7f`, `1e5`, `0b1`) contains no identifier.
            i += 1
            while i < len(text) and (text[i].isalnum() or text[i] == '_'):
                i += 1
        elif text[i].isalpha() or text[i] == '_':
            start = i
            i += 1
            while i < len(text) and (text[i].isalnum() or text[i] in "_'?!"):
                i += 1
            yield start, i, text[start:i]
        else:
            i += 1


def module_name(name):
    """Lean prints a module component that is not an identifier (`bench-ec`)
    as `«bench-ec»`; inventories spell the file's module plainly."""
    return '.'.join(part[1:-1] if part.startswith('«') and part.endswith('»') else part
                    for part in split_name(name))


# Lean tokens that cannot be identifiers unescaped (a new name `to` must be
# spelled `«to»`). The list covers command, term and tactic keywords a field or
# binder rename can plausibly hit; the build still catches anything else.
KEYWORDS = frozenset("""at by calc do else end export from fun have if import in let match
mut namespace open show suffices then to universe variable where with deriving
instance structure inductive class theorem lemma def abbrev example section
private protected noncomputable partial unsafe macro syntax local scoped attribute
set_option exact intro intros apply""".split())


def escape_keywords(spelling):
    dot = '.' if spelling.startswith('.') else ''
    parts = split_name(spelling[len(dot):])
    return dot + '.'.join(f'«{p}»' if p in KEYWORDS else p for p in parts)


def split_name(name):
    return [part for part in IDENT_PART.findall(name)] if '«' in name else name.split('.')


def replacement(spelling, old, new, renamer=None, type_directed=False):
    """New spelling for one compiler reference.

    A leading-dot constructor and a generalized field projection (`x.f`) are
    resolved through a type, so they keep their component count. A lexical
    spelling resolves in a namespace: the unspelled prefix of the old name. That
    namespace is renamed by namespace rows (as its `namespace`/`open` syntax is),
    and the new name must stay inside it; namespace depth below it may change.
    """
    leading_dot = spelling.startswith('.')
    bare = spelling[1:] if leading_dot else spelling
    if old.startswith('_private.') and new.startswith('_private.'):
        old, new = MAP.split_private(old)[2], MAP.split_private(new)[2]
    old_parts, new_parts = split_name(old), split_name(new)
    parts = split_name(bare)
    if parts != old_parts[-len(parts):]:
        raise ValueError(f'indexed spelling {spelling!r} is not a suffix of {old}')
    if leading_dot or type_directed:
        if leading_dot and len(parts) != 1:
            raise ValueError(f'unsupported qualified leading-dot spelling {spelling!r}')
        return ('.' if leading_dot else '') + '.'.join(new_parts[-len(parts):])
    context = '.'.join(old_parts[:-len(parts)])
    renamed = renamer.scope(context) if renamer is not None and context else context
    prefix = renamed.split('.') if renamed else []
    if new_parts[:len(prefix)] != prefix or len(new_parts) == len(prefix):
        raise ValueError(f'rename {old} -> {new} leaves the namespace {context or "<root>"!r} '
                         f'that spelling {spelling!r} resolves in; needs explicit qualification or relocation')
    return '.'.join(new_parts[len(prefix):])


def byte_offsets(text):
    offsets, byte = {0: 0}, 0
    for i, char in enumerate(text):
        byte += len(char.encode('utf-8'))
        offsets[byte] = i + 1
    return offsets


def syntax_rows(index, key, width):
    metadata = index.get('naming_syntax') or {}
    if metadata.get('version', 1) not in (1, 2):
        raise ValueError('unsupported naming syntax metadata')
    if metadata.get('version', 1) < 2:
        return []
    rows = metadata.get(key)
    if not isinstance(rows, list) or any(not isinstance(r, list) or len(r) != width for r in rows):
        raise ValueError(f'invalid naming syntax {key}')
    return rows


def char_span(offsets, a, b, text):
    if type(a) is not int or type(b) is not int or a not in offsets or b not in offsets or a >= b:
        raise ValueError('syntax range outside source or splits UTF-8')
    return offsets[a], offsets[b]


class Universe:
    """Constant names visible for capture checks: one set before and one after
    renaming, plus the current module's private names under their user names."""

    def __init__(self, names, renamer, compiler_named=()):
        self.compiler_named = set(compiler_named)
        self.before = set(names)
        self.after = {renamer(name) for name in self.before}
        self.private = {}
        for side, names in (('before', self.before), ('after', self.after)):
            for name in names:
                split = MAP.split_private(name) if name.startswith('_private.') else None
                if split:
                    self.private.setdefault((side, split[0]), {})[split[2]] = name

    def lookup(self, side, module, renamer=None):
        names = self.before if side == 'before' else self.after
        target = module if side == 'before' or renamer is None else renamer.module(module)
        return names, self.private.get((side, target), {})


def resolve(lookup, spelling, ns, opens):
    """Lean's global constant resolution (ResolveName.resolveGlobalName) over a
    known name set: the innermost enclosing namespace wins, then an exact
    qualified name, then the root name together with every open declaration.
    Aliases, projections and local scopes are not modelled; callers first check
    that the result reproduces the compiler's own answer before relying on it."""
    names, private = lookup
    def has(name):
        return name if name in names else private.get(name)
    if spelling.startswith('_root_.'):
        found = has(spelling[len('_root_.'):])
        return {found} if found else set()
    parts = split_name(spelling)
    scope = [] if ns in ('', '[anonymous]') else ns.split('.')
    for i in range(len(scope), 0, -1):
        found = has('.'.join(scope[:i] + parts))
        if found:
            return {found}
    if len(parts) > 1 and has(spelling):
        return {has(spelling)}
    result = {has(spelling)} - {None}
    for row in opens:
        if row[0] == 'simple':
            if spelling not in row[2]:
                found = has(row[1] + '.' + spelling)
                if found:
                    result.add(found)
        elif row[1] == spelling:
            result.add(row[2])
        elif spelling.startswith(row[1] + '.'):
            found = has(row[2] + spelling[len(row[1]):])
            if found:
                result.add(found)
    return result


def renamed_opens(opens, renamer):
    result = []
    for row in opens:
        if row[0] == 'simple':
            result.append([row[0], renamer.scope(row[1]), row[2]])
        else:
            # `open N (x)`: the alias is spelled as the declaration's last
            # component, so the reference edit renames it with the declaration.
            new = renamer(row[2])
            alias = split_name(new)[-1] if row[1] == split_name(row[2])[-1] else row[1]
            result.append([row[0], alias, new])
    return result


def plan_file(text, index, entries, renamer=None, universe=None, stats=None):
    if index.get('version') != 5:
        raise ValueError('requires Lean ilean format 5')
    renamer = renamer or MAP.Renamer(entries)
    candidates = renamer.words()
    index_module = module_name(index['module'])
    positions = Positions(text)
    offsets = byte_offsets(text)
    # (start, end, const, component spans, local)
    references, definitions, local_uses = [], set(), {}
    for key, info in index['references'].items():
        ident = json.loads(key)
        const = ident.get('c', {}).get('n')
        locations = list(info['usages'])
        if info['definition'] is not None:
            locations.append(info['definition'])
        for location in locations:
            start, end = span(positions, location)
            references.append((start, end, const, components(text, start, end), 'f' in ident))
            if location is info['definition']:
                definitions.add((start, end))
        if 'f' in ident and info['definition'] is not None:
            local_uses[span(positions, info['definition'])] = [span(positions, u) for u in info['usages']]
    edits, problems, cover = {}, [], {}
    local_spans = {(r[0], r[1]) for r in references if r[4]}

    def add_cover(spans, what):
        for item in spans:
            cover.setdefault(item, []).append(what)

    def add_edit(start, end, spelling, renamed, declaration):
        if ' := ' in renamed:
            head, tail = renamed.split(' := ', 1)
            renamed = escape_keywords(head) + ' := ' + tail
        else:
            renamed = escape_keywords(renamed)
        edit = {'start': start, 'end': end, 'old': spelling, 'new': renamed, 'declaration': declaration}
        previous = edits.get((start, end))
        if previous and previous['new'] != renamed:
            problems.append({'start': start, 'end': end, 'reason': 'conflicting compiler references'})
        edits[start, end] = edit

    for start, end, const, comps, local in references:
        if comps is not None:
            # A local variable denotes its first component only; any further
            # components are projections with their own references.
            add_cover(comps[:1] if local else comps, ('local', None) if local else ('const', const))
        spelling = text[start:end]
        if spelling == '_':
            # A wildcard alternative (`| _ => ...`) that the elaborator expanded
            # into the constructors it covers carries their references, but it
            # spells no name: renaming a constructor leaves it unchanged.
            continue
        if const is not None and (start, end) in definitions and comps is not None:
            parts, name_parts = split_name(spelling.lstrip('.')), split_name(const)
            private = MAP.split_private(const) if const.startswith('_private.') else None
            if private:
                name_parts = split_name(private[2])
            if parts != name_parts[-len(parts):]:
                continue  # Compiler-named (an anonymous instance): nothing spelled.
            context = '.'.join(name_parts[:-len(parts)])
            if context and renamer.scope(context) != context:
                target = renamer(private[2] if private else const)
                if not target.startswith(renamer.scope(context) + '.'):
                    problems.append({'start': start, 'end': end, 'reason':
                        f'declaration {const} inside renamed namespace {context} -> '
                        f'{renamer.scope(context)} needs a map row under the new namespace'})
                    continue
        if const is None or not renamer.renames(const):
            if const is not None and universe is not None and const in universe.compiler_named:
                last = MAP.tokenize_identifier(split_name(const)[-1])
                renamed_words = {t for w in candidates for t in [w] if MAP.tokenize_identifier(w)}
                hit = next((w for w in renamed_words
                            if any(last[i:i + len(MAP.tokenize_identifier(w))] == MAP.tokenize_identifier(w)
                                   for i in range(len(last)))), None)
                if hit:
                    problems.append({'start': start, 'end': end, 'reason':
                        f'reference to compiler-named {const}, whose name Lean derives from '
                        f'renamed {hit!r}: name it explicitly or add its map row'})
            continue
        new = renamer(const)
        if new == const:
            continue  # A relocation that keeps its name changes no spelling.
        try:
            if comps is None:
                raise ValueError(f'compound reference range {spelling!r} for renamed {const}')
            renamed = replacement(spelling, const, new, renamer,
                                  type_directed=start > 0 and text[start - 1] == '.' and not spelling.startswith('.'))
            if (start, end) in local_spans and len(comps) == 1:
                # Field abbreviation `{ gas }` is `{ gas := gas }`: the field is
                # renamed, the local variable it reads is not.
                renamed = f'{renamed} := {spelling}'
        except ValueError as error:
            problems.append({'start': start, 'end': end, 'reason': str(error)})
            continue
        if renamed != spelling:
            add_edit(start, end, spelling, renamed, const)
    # Name capture: after renaming, every lexically resolved reference must
    # still resolve to its (renamed) constant in the scope it elaborated in.
    # A spelling that would be captured (or become ambiguous) is qualified
    # with more components of its target; failing that, it is unresolved.
    commands = sorted((*char_span(offsets, r[0], r[1], text), r[3], r[4])
                      for r in syntax_rows(index, 'commands', 6) if r[0] < r[1])
    if universe is not None and commands:
        module = module_name(index['module'])
        before = universe.lookup('before', module)
        after = universe.lookup('after', module, renamer)
        starts = [c[0] for c in commands]
        checked = unverifiable = requalified = unverifiable_edited = 0
        for start, end, const, comps, local in references:
            if (local or const is None or comps is None or (start, end) in definitions or
                    text.startswith('.', start) or (start > 0 and text[start - 1] == '.')):
                continue
            i = bisect.bisect_right(starts, start) - 1
            if i < 0 or not (commands[i][0] <= start and end <= commands[i][1]):
                continue
            _, _, ns, opens = commands[i]
            spelling = text[start:end]
            if resolve(before, spelling, ns, opens) != {const}:
                unverifiable += 1  # Outside the modelled resolution; build and N4 decide.
                if (start, end) in edits:
                    unverifiable_edited += 1
                continue
            target = renamer(const)
            current = edits[start, end]['new'] if (start, end) in edits else spelling
            new_ns, new_opens = renamer.scope(ns) if ns != '[anonymous]' else ns, renamed_opens(opens, renamer)
            checked += 1
            if resolve(after, current, new_ns, new_opens) == {target}:
                continue
            parts = split_name(target)
            for k in range(len(split_name(current)) + 1, len(parts) + 1):
                candidate = '.'.join(parts[-k:])
                if resolve(after, candidate, new_ns, new_opens) == {target}:
                    edits[start, end] = {'start': start, 'end': end, 'old': spelling, 'new': candidate,
                                         'declaration': const}
                    requalified += 1
                    break
            else:
                problems.append({'start': start, 'end': end, 'reason':
                                 f'name capture: {current!r} would not resolve uniquely to {target} '
                                 f'in namespace {new_ns}; no qualification resolves'})
        if stats is not None:
            stats.update(capture_checked=checked, capture_unverifiable=unverifiable,
                         capture_requalified=requalified, capture_unverifiable_edited=unverifiable_edited)
    # Namespace syntax: `namespace`, `end`, `open`, `export` resolved by the exporter.
    for a, b, kind, full, reason in syntax_rows(index, 'namespaces', 5):
        start, end = char_span(offsets, a, b, text)
        comps = components(text, start, end)
        spelling = text[start:end]
        if kind == 'section' or comps is None:
            # A section label names no constant or namespace.
            if kind == 'section' and comps is not None:
                add_cover(comps, ('section', None))
            continue
        if full is None:
            add_cover(comps, ('unresolved', f'{kind} syntax: {reason}'))
            continue
        add_cover(comps, ('namespace', full))
        new = renamer.scope(full)
        if new != full:
            try:
                renamed = replacement(spelling, full, new, renamer)
            except ValueError as error:
                problems.append({'start': start, 'end': end, 'reason': str(error)})
                continue
            if renamed != spelling:
                add_edit(start, end, spelling, renamed, f'namespace {full}')
    # Named arguments: a constructor binder is its structure field's name.
    for a, b, function, param, field, reason in syntax_rows(index, 'named_arguments', 6):
        start, end = char_span(offsets, a, b, text)
        comps = components(text, start, end)
        if comps is None or text[start:end] != param:
            raise ValueError('named argument range does not match its binder')
        if reason is not None:
            add_cover(comps, ('unresolved', reason))
            continue
        add_cover(comps, ('binder', function))
        binder_key = f'{function}.{param}'
        if binder_key in renamer.exact:
            add_edit(start, end, param, split_name(renamer(binder_key))[-1], binder_key)
            continue
        if field is not None and renamer.renames(field):
            new_field = renamer(field)
            parent = field.rsplit('.', 1)[0]
            if new_field.rsplit('.', 1)[0] != renamer(parent):
                problems.append({'start': start, 'end': end,
                                 'reason': f'field {field} -> {new_field} leaves its structure'})
                continue
            add_edit(start, end, param, new_field.rsplit('.', 1)[1], field)
    definition_at = {(r[0], r[1]): r[2] for r in references if r[2] and (r[0], r[1]) in definitions}
    metadata = index.get('naming_syntax') or {}
    for ca, cb, a, b, name in (metadata.get('constructor_binders', []) if metadata.get('version') == 2 else []):
        cstart, cend = char_span(offsets, ca, cb, text)
        start, end = char_span(offsets, a, b, text)
        comps = components(text, start, end)
        ctor = definition_at.get((cstart, cend))
        if comps is None or text[start:end] != name:
            raise ValueError('constructor binder range does not match its name')
        if ctor is None:
            add_cover(comps, ('unresolved', 'constructor binder without a constructor definition reference'))
            continue
        add_cover(comps, ('binder', ctor))
        key = f'{ctor}.{name}'
        if key in renamer.exact:
            add_edit(start, end, name, split_name(renamer(key))[-1], key)
            # Later binders or the result type may use it: the same local
            # variable's uses (same compiler identity) are renamed with it.
            for use in local_uses.get((start, end), []):
                add_edit(*use, name, split_name(renamer(key))[-1], key)
    for a, b, name in (metadata.get('imports', []) if metadata.get('version') == 2 else []):
        start, end = char_span(offsets, a, b, text)
        add_cover(components(text, start, end) or [], ('module', name))  # Module rows edit imports.
    quoted = metadata.get('quotation_identifiers', []) if metadata.get('version') == 2 else []
    if quoted:
        commands_q = sorted((*char_span(offsets, r[0], r[1], text), r[3], r[4])
                            for r in syntax_rows(index, 'commands', 6) if r[0] < r[1])
        starts_q = [c[0] for c in commands_q]
    for a, b, name in quoted:
        if a >= b:
            continue  # A missing (zero-width) identifier inside a quotation.
        start, end = char_span(offsets, a, b, text)
        comps = components(text, start, end)
        spelling = text[start:end]
        if comps is None or not any(text[x:y] in candidates for x, y in comps):
            continue
        # Lean pre-resolves quoted identifiers as global names in the quoting
        # command's scope; the same resolution model decides them here.
        i = bisect.bisect_right(starts_q, start) - 1
        found = set()
        if universe is not None and i >= 0 and commands_q[i][0] <= start < commands_q[i][1]:
            found = resolve(universe.lookup('before', index_module), spelling, commands_q[i][2], commands_q[i][3])
        if len(found) != 1:
            add_cover(comps, ('unresolved', 'quotation identifier with no unique global resolution '
                                            '(a quoted local binder, or outside the modelled scope)'))
            continue
        const = next(iter(found))
        add_cover(comps, ('const', const))
        target = renamer(const)
        scope_ns, scope_opens = commands_q[i][2], commands_q[i][3]
        new_ns = renamer.scope(scope_ns) if scope_ns != '[anonymous]' else scope_ns
        after_lookup = universe.lookup('after', index_module, renamer)
        try:
            renamed = replacement(spelling, const, target, renamer) if target != const else spelling
        except ValueError as error:
            problems.append({'start': start, 'end': end, 'reason': str(error)})
            continue
        # Pre-resolution happens in the quoting scope after the rename too:
        # the new spelling must not be captured (execution `U256` inside
        # `namespace JauneConsensus`).
        if resolve(after_lookup, renamed, new_ns, renamed_opens(scope_opens, renamer)) != {target}:
            parts = split_name(target)
            for k in range(len(split_name(renamed)) + 1, len(parts) + 1):
                candidate = '.'.join(parts[-k:])
                if resolve(after_lookup, candidate, new_ns, renamed_opens(scope_opens, renamer)) == {target}:
                    renamed = candidate
                    break
            else:
                problems.append({'start': start, 'end': end, 'reason':
                                 f'name capture in quotation: {renamed!r} would not pre-resolve to {target}'})
                continue
        if renamed != spelling:
            add_edit(start, end, spelling, renamed, const)
    reasons = []
    for a, b, reason in syntax_rows(index, 'unresolved_syntax', 3):
        reasons.append((*char_span(offsets, a, b, text), reason))
    ordered = sorted(edits.values(), key=lambda e: (e['start'], e['end']))
    shaped = sorted((r for r in references if r[3] is not None), key=lambda r: r[0])
    starts = [r[0] for r in shaped]
    longest = max((r[1] - r[0] for r in shaped), default=0)
    for edit in ordered:
        lo = bisect.bisect_left(starts, edit['start'] - longest)
        hi = bisect.bisect_left(starts, edit['end'])
        for start, end, const, _, local in shaped[lo:hi]:
            if (start < edit['end'] and edit['start'] < end and
                    (local or const is None or not renamer.renames(const)) and
                    not (start == edit['start'] and end == edit['end'] and
                         (const == edit['declaration'] or (local and edit['declaration'] in renamer.exact) or
                          (local and edit['new'].endswith(' := ' + edit['old']))))):
                problems.append({'start': edit['start'], 'end': edit['end'],
                                 'reason': 'edit overlaps an unchanged compiler reference'})
                break
    for left, right in zip(ordered, ordered[1:]):
        if right['start'] < left['end']:
            problems.append({'start': right['start'], 'end': left['end'], 'reason': 'overlapping edits'})
    masked, literals = mask_literals(text, index)
    literal_starts = [a for a, _ in literals]
    for start, end, const, comps, _ in shaped:
        if const is None:
            continue
        i = bisect.bisect_right(literal_starts, start) - 1
        for a, b in literals[max(i, 0):i + 2]:
            if a < end and start < b:
                raise ValueError('literal range overlaps a compiler reference')
    for start, end, word in identifiers(masked):
        if word not in candidates:
            continue
        covering = cover.get((start, end), [])
        resolved = [what for what in covering if what[0] != 'unresolved']
        if not resolved:
            reason = next((r for _, r in [what for what in covering if what[0] == 'unresolved']), None)
            reason = reason or next((r for a, b, r in reasons if a <= start and end <= b), None)
            problems.append({'start': start, 'end': end,
                             'reason': f'unresolved token {word!r}' + (f': {reason}' if reason else '')})
            continue
        for kind, const in resolved:
            if (kind == 'const' and const and renamer.explain(const)[1] != 'exact' and
                    renamer.exact_ancestor(const)):
                problems.append({'start': start, 'end': end,
                                 'reason': 'descendant of renamed declaration needs its own map row'})
                break
    return ordered, problems


def build_plan(root, map_path, files):
    map_bytes = map_path.read_bytes()
    data = json.loads(map_bytes)
    MAP.validate_map(data)
    if any(row['kind'] in ('module', 'relocation') for row in data['entries']):
        raise ValueError('module/relocation rows need whole-tree planning (naming-tree.py)')
    records = []
    for relative, artifact in files:
        source = safe_path(root, relative)
        source_bytes = source.read_bytes()
        # Preserve CRLF exactly; positions are independent of the newline width.
        text = source_bytes.decode('utf-8')
        index_bytes = safe_path(root, artifact).read_bytes()
        bundle = json.loads(index_bytes)
        if bundle.get('source') != text:
            raise ValueError(f'{relative}: reference bundle source mismatch; re-export')
        edits, problems = plan_file(text, bundle['index'], data['entries'])
        records.append({'path': relative, 'sha256': digest(source_bytes),
                        'index': artifact, 'index_sha256': digest(index_bytes),
                        'edits': edits, 'unresolved': problems})
    if not records or len({r['path'] for r in records}) != len(records):
        raise ValueError('select at least one source, without duplicates')
    return {'schema_version': 1, 'map_sha256': digest(map_bytes), 'files': records,
            'scope': 'explicit selected files; source-bound references; current imports required',
            'status': 'unresolved' if any(r['unresolved'] for r in records) else 'planned'}


def apply_plan(root, plan, map_path):
    if plan.get('schema_version') != 1 or plan.get('status') != 'planned':
        raise ValueError('only a fully resolved version-1 plan may be applied')
    if digest(map_path.read_bytes()) != plan['map_sha256']:
        raise ValueError('rename map changed since planning')
    records = plan['files']
    if not records or len({r['path'] for r in records}) != len(records):
        raise ValueError('empty or duplicate source selection')
    # Recompute the plan, rather than trusting editable replacement strings.
    expected = build_plan(root, map_path, [(r['path'], r['index']) for r in records])
    if expected != plan:
        raise ValueError('source, index or plan changed since planning')
    pending = []
    for record in records:
        path = safe_path(root, record['path'])
        text = path.read_bytes().decode('utf-8')
        for edit in reversed(record['edits']):
            text = text[:edit['start']] + edit['new'] + text[edit['end']:]
        if record['edits']:
            pending.append((path, text.encode('utf-8')))
    # All inputs checked before the first write. Like an editor, filesystem I/O
    # failure can interrupt a multi-file application; the plan identifies every
    # original digest and should be kept with the Git checkpoint.
    for path, content in pending:
        path.write_bytes(content)
    return len(pending)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    for command in ('plan', 'apply'):
        p = sub.add_parser(command)
        p.add_argument('--tree', type=Path, required=True)
        p.add_argument('--map', type=Path, required=True)
        if command == 'plan':
            p.add_argument('--file', nargs=2, action='append', required=True,
                           metavar=('SOURCE', 'REFERENCES_JSON'))
        else:
            p.add_argument('--plan', type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        root = args.tree.resolve(strict=True)
        if args.command == 'plan':
            result = build_plan(root, args.map, args.file)
            print(json.dumps(result, indent=2, ensure_ascii=False))
            return 1 if result['status'] == 'unresolved' else 0
        count = apply_plan(root, json.loads(args.plan.read_text()), args.map)
        print(f'OK — naming apply: {count} files changed; build and fidelity checks still required')
        return 0
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'REFUSED — naming apply: {error}', file=sys.stderr)
        return 2


if __name__ == '__main__':
    sys.exit(main())
