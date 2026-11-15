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
import json
from pathlib import Path
import sys


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
    if metadata.get('version') != 1:
        raise ValueError('unsupported naming syntax metadata')
    offsets, byte = {0: 0}, 0
    for i, char in enumerate(text):
        byte += len(char.encode('utf-8'))
        offsets[byte] = i + 1
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
        elif text[i].isalpha() or text[i] == '_':
            start = i
            i += 1
            while i < len(text) and (text[i].isalnum() or text[i] in "_'?!"):
                i += 1
            yield start, i, text[start:i]
        else:
            i += 1


def replacement(spelling, old, new):
    """Keep a reference's qualification level only when it is unambiguous."""
    # Lean includes the leading dot in constructor-pattern references.
    leading_dot = spelling.startswith('.')
    bare = spelling[1:] if leading_dot else spelling
    old_parts, new_parts = old.split('.'), new.split('.')
    parts = bare.split('.')
    if parts != old_parts[-len(parts):]:
        raise ValueError(f'indexed spelling {spelling!r} is not a suffix of {old}')
    # Changing namespace depth needs a separate relocation plan.
    if len(old_parts) != len(new_parts):
        raise ValueError(f'namespace-depth change needs explicit relocation: {old} -> {new}')
    return ('.' if leading_dot else '') + '.'.join(new_parts[-len(parts):])


def plan_file(text, index, entries):
    if index.get('version') != 5:
        raise ValueError('requires Lean ilean format 5')
    mappings = {entry['old']: entry['new'] for entry in entries}
    # Include only components that actually change, not a shared namespace.
    candidates = {part for old, new in mappings.items()
                  for i, part in enumerate(old.split('.'))
                  if i >= len(new.split('.')) or part != new.split('.')[i]}
    references = []
    positions = Positions(text)
    edits = {}
    problems = []
    for key, info in index['references'].items():
        ident = json.loads(key)
        const = ident.get('c', {}).get('n')
        locations = list(info['usages'])
        if info['definition'] is not None:
            locations.append(info['definition'])
        for location in locations:
            start, end = span(positions, location)
            references.append((start, end, const))
            if const not in mappings:
                continue
            spelling = text[start:end]
            try:
                renamed = replacement(spelling, const, mappings[const])
            except ValueError as error:
                problems.append({'start': start, 'end': end, 'reason': str(error)})
                continue
            if renamed == spelling:
                continue
            edit = {'start': start, 'end': end, 'old': spelling,
                    'new': renamed, 'declaration': const}
            previous = edits.get((start, end))
            if previous and previous['new'] != renamed:
                problems.append({'start': start, 'end': end, 'reason': 'conflicting compiler references'})
            edits[start, end] = edit
    ordered = sorted(edits.values(), key=lambda e: (e['start'], e['end']))
    for edit in ordered:
        for start, end, const in references:
            if start < edit['end'] and edit['start'] < end and const not in mappings:
                problems.append({'start': edit['start'], 'end': edit['end'],
                                 'reason': 'edit overlaps an unchanged compiler reference'})
                break
    for left, right in zip(ordered, ordered[1:]):
        if right['start'] < left['end']:
            problems.append({'start': right['start'], 'end': left['end'], 'reason': 'overlapping edits'})
    masked, literals = mask_literals(text, index)
    if any(const is not None and a < end and start < b
           for a, b in literals for start, end, const in references):
        raise ValueError('literal range overlaps a compiler reference')
    for start, end, word in identifiers(masked):
        if word not in candidates:
            continue
        covering = [ref for ref in references if ref[0] <= start and end <= ref[1]]
        if not covering:
            problems.append({'start': start, 'end': end, 'reason': f'unresolved token {word!r}'})
        elif any(const and const not in mappings and
                 any(const.startswith(old + '.') for old in mappings)
                 for _, _, const in covering):
            problems.append({'start': start, 'end': end,
                             'reason': 'descendant of renamed declaration needs its own map row'})
    return ordered, problems


def build_plan(root, map_path, files):
    map_bytes = map_path.read_bytes()
    data = json.loads(map_bytes)
    validator_path = Path(__file__).with_name('check-naming-map.py')
    spec = importlib.util.spec_from_file_location('naming_schema', validator_path)
    validator = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(validator)
    validator.validate_map(data)
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
