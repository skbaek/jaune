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
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent


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


def merge_constants(existing, roots, incoming, incoming_roots):
    """Union compiler-registered equation copies, never authored collisions."""
    overlap = existing.keys() & incoming.keys()
    for name in sorted(overlap):
        origin = existing[name].get('equation_origin')
        if (name in roots or name in incoming_roots or origin is None or
                origin != incoming[name].get('equation_origin') or
                existing[name] != incoming[name]):
            raise ValueError(f'duplicate constants without identical generated-equation provenance: {name}')
    existing.update(incoming)
    return overlap


def read_exports(paths):
    constants, roots, guards, attributes, modules, receipts = {}, set(), [], [], {}, []
    checks = []
    coalesced = set()
    version = None
    for path in paths:
        raw = Path(path).read_bytes()
        data = json.loads(raw)
        if data['schema_version'] not in (3, 4, 5, 6) or data['index']['version'] != 5:
            raise ValueError('unsupported fidelity/index schema')
        if version is not None and version != data['lean_version']:
            raise ValueError('mixed Lean versions')
        version = data['lean_version']
        module = data['index']['module']
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
        names = set(data['index']['decls'])
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
                elif not pseudo_example:
                    names.add(const['n'])
            for loc in info['usages'] + ([info['definition']] if info.get('definition') else []):
                start, end = APPLY.span(positions, loc)
                locations[byte_offsets[start], byte_offsets[end]].add(const['n'])
        names -= failed_names
        missing = names - data['constants'].keys()
        if missing:
            raise ValueError(f'{module}: authored definitions missing from kernel export: {sorted(missing)}')
        coalesced |= merge_constants(constants, roots, data['constants'], names)
        roots.update(names)

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
            if value in (['atom', 'local'], ['atom', 'scoped']):
                raise ValueError('local/scoped attribute commands require scope-history support')
            return [syntax(item, literal_names) for item in value]

        checks.extend(syntax(row['syntax'], row['literal_names']) for row in command_checks)
        guards.extend(data['guards'])
        attributes.extend(syntax(item) for item in data['attribute_syntax'])
        receipts.append(dict(path=str(path), sha256=hashlib.sha256(raw).hexdigest(),
                             source_sha256=hashlib.sha256(data['source'].encode()).hexdigest(), module=module))
    if not modules:
        raise ValueError('no exported modules')
    return dict(constants=constants, roots=roots, guards=guards, attributes=attributes,
                modules=modules, receipts=receipts, version=version, checks=checks,
                coalesced_equations=sorted(coalesced))


class Comparison:
    def __init__(self, before, after, mapping):
        self.before, self.after = before, after
        self.mapping = mapping
        self.left = before['constants']
        self.right = after['constants']
        self.generated_left = self.left.keys() - before['roots']
        self.generated_right = self.right.keys() - after['roots']
        self.pairs, self.reverse, self.checked = {}, {}, set()

    def name(self, name):
        return self.mapping.get(name, name)

    def compare(self, left, right, path):
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

    def normalize(self, value, side, coarse=False):
        if isinstance(value, dict):
            return {k: self.normalize(v, side, coarse) for k, v in value.items()}
        if not isinstance(value, list):
            return value
        if len(value) == 2 and value[0] == 'name':
            name = value[1]
            generated = self.generated_left if side == 'before' else self.generated_right
            if name in generated and coarse:
                return ['generated']
            return ['name', self.pairs[name] if side == 'before' and name in generated
                    else self.name(name) if side == 'before' else name]
        return [self.normalize(item, side, coarse) for item in value]

    def run(self):
        expected = {self.name(n) for n in self.before['roots']}
        if len(expected) != len(self.before['roots']) or expected != self.after['roots']:
            raise Mismatch(f'authored constant set changed: missing={sorted(expected - self.after["roots"])}, extra={sorted(self.after["roots"] - expected)}')
        for name in sorted(self.before['roots']):
            self.pair(name, self.name(name))
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
            for candidate in candidates:
                saved = self.pairs.copy(), self.reverse.copy(), self.checked.copy()
                try:
                    self.pair(name, candidate)
                    break
                except Mismatch:
                    self.pairs, self.reverse, self.checked = saved
            else:
                raise Mismatch(f'no verified generated-constant match for {name}')
        if self.right.keys() != self.reverse.keys():
            raise Mismatch('additional generated constants after renaming')
        for key in ('guards', 'attributes', 'checks'):
            left = Counter(encoded(self.normalize(item, 'before')) for item in self.before.get(key, []))
            right = Counter(encoded(item) for item in self.after.get(key, []))
            if left != right:
                raise Mismatch(f'{key}: expression/command multiset changed (missing {sum((left-right).values())}, extra {sum((right-left).values())})')
        return dict(status='OK', scope='exported-modules',
                    authored_constants=len(self.before['roots']), generated_constants=len(self.generated_left),
                    guards=len(self.before['guards']), attribute_commands=len(self.before['attributes']),
                    checked_commands=len(self.before.get('checks', [])))


def check(before, after, mapping):
    MAP.validate_map(mapping)
    if before['version'] != after['version']:
        raise ValueError('Lean versions differ')
    renames = {entry['old']: entry['new'] for entry in mapping['entries']}
    # Imports are reported, not silently treated as a proof about their contents.
    result = Comparison(before, after, renames).run()
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
