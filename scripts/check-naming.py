#!/usr/bin/env python3
"""Check compiler-indexed names against retired tokens, retired names and a reviewed policy.

This checker does not infer that an abbreviation is English or that a citation
is authoritative. Its word vocabulary and exact source bindings are explicit
review inputs. Bundles must be freshly exported against current imports.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent


def load_tool(filename):
    spec = importlib.util.spec_from_file_location(filename, ROOT / 'scripts' / filename)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


MAP = load_tool('check-naming-map.py')
APPLY = load_tool('apply-naming-map.py')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    return json.loads(Path(path).read_bytes())


def user_name(name, module):
    prefix = '_private.' + module + '.'
    if name.startswith(prefix):
        counter, sep, rest = name[len(prefix):].partition('.')
        if not sep or not counter.isdigit():
            raise ValueError(f'unsupported private name: {name}')
        return rest
    if name.startswith('_private.'):
        raise ValueError(f'private name belongs to another module: {name}')
    return name


def declarations(text, index):
    """Include fields/constructors, which ilean's decls table alone omits."""
    if index.get('version') != 5:
        raise ValueError('requires Lean ilean format 5')
    module = APPLY.module_name(index['module'])
    positions = APPLY.Positions(text)
    names = {}
    compiler_named = set()
    for name, loc in index['decls'].items():
        if len(loc) != 8:
            raise ValueError('unsupported declaration location')
        a, b = APPLY.span(positions, loc[4:])
        # Lean names anonymous instances and syntax/macro kinds itself; their
        # ranges spell a keyword, not the name. They follow other names (or are
        # notation keywords, out of N3 scope) and are not linted.
        if not spelled(text, a, b, user_name(name, module)):
            compiler_named.add(name)
            continue
        names[user_name(name, module)] = loc[4:]
    for key, info in index['references'].items():
        const = json.loads(key).get('c')
        loc = info.get('definition')
        if const and loc is not None:
            if const['m'] != module:
                raise ValueError('foreign definition in module reference bundle')
            start, end = APPLY.span(positions, loc)
            if const['n'].endswith('._example') and text[start:end] == 'example' and not info['usages']:
                continue  # Lean gives anonymous examples a navigation-only pseudo-name.
            if const['n'] in compiler_named or not spelled(text, start, end, user_name(const['n'], module)):
                continue
            names[user_name(const['n'], module)] = loc[:4]
    return names


def spelled(text, a, b, name):
    spans = APPLY.components(text, a, b)
    if spans is None:
        return False
    parts = [text[x:y] for x, y in spans]
    return APPLY.split_name(name)[-len(parts):] == parts


def transliterate(name, style):
    if style == 'verbatim':
        return name
    if style not in ('lowerCamel', 'upperCamel'):
        raise ValueError(f'unsupported source case style: {style}')
    parts = name.split('_')
    if any(not p for p in parts):
        raise ValueError('empty component in source spelling')
    if name.isupper():
        parts = [p.lower() for p in parts]
    first = parts[0]
    first = (first[:1].lower() if style == 'lowerCamel' else first[:1].upper()) + first[1:]
    return first + ''.join(p[:1].upper() + p[1:] for p in parts[1:])


def validate_policy(policy, source_root):
    if not isinstance(policy, dict) or policy.get('schema_version') != 1 or set(policy) != {'schema_version', 'words', 'sources', 'bindings'}:
        raise ValueError('policy requires schema_version 1, words, sources and bindings')
    words = policy['words']
    if (not isinstance(words, list) or any(not isinstance(w, str) or
            not re.fullmatch('[a-z]+', w) for w in words) or len(words) != len(set(words))):
        raise ValueError('words must be distinct lowercase English vocabulary entries')
    if not isinstance(policy['sources'], dict) or not isinstance(policy['bindings'], dict):
        raise ValueError('sources and bindings must be objects')
    sources = {}
    for key, row in policy['sources'].items():
        if (not isinstance(row, dict) or set(row) != {'path', 'sha256', 'citation'}
                or any(not isinstance(value, str) or not value.strip() for value in row.values())):
            raise ValueError(f'{key}: source requires path, sha256 and citation')
        data = APPLY.safe_path(source_root, row['path']).read_bytes()
        if sha(data) != row['sha256']:
            raise ValueError(f'{key}: source digest mismatch')
        sources[key] = data.decode('utf-8')
    for name, row in policy['bindings'].items():
        if (not isinstance(row, dict) or set(row) != {'rule', 'source', 'spelling', 'style'}
                or any(not isinstance(value, str) for value in row.values())
                or row['rule'] not in ('1', '2', '3')):
            raise ValueError(f'{name}: invalid source binding')
        spelling = row['spelling']
        if not isinstance(spelling, str) or not re.fullmatch('[A-Za-z][A-Za-z0-9_]*', spelling):
            raise ValueError(f'{name}: invalid source spelling')
        if row['source'] not in sources:
            raise ValueError(f'{name}: unregistered source')
        # Exact identifier boundary, never a substring or a free-text citation.
        if not re.search(r'(?<![\w])' + re.escape(spelling) + r'(?![\w])', sources[row['source']]):
            raise ValueError(f'{name}: spelling absent from registered source')
        if name.split('.')[-1] != transliterate(spelling, row['style']):
            raise ValueError(f'{name}: source spelling/case mismatch')
    return set(words)


TOKEN = re.compile(r'[A-Z]{2,}(?=s(?:[A-Z0-9_]|$))|[A-Z]+(?=[A-Z][a-z]|[0-9]|$)|[A-Z]?[a-z]+|[0-9]+')


def unknown_words(segment, words, abbreviations):
    """Never silently drop Unicode, punctuation, or unrecognized characters."""
    segment = segment.rstrip("'?!")
    unknown = []
    for part in segment.split('_'):
        if not part:
            unknown.append('<empty>')
            continue
        if part in abbreviations:
            continue
        tokens = TOKEN.findall(part)
        if ''.join(tokens) != part:
            unknown.append(part)
            continue
        allowed = sorted((TOKEN.findall(a) for a in abbreviations
                          if ''.join(TOKEN.findall(a)) == a), key=len, reverse=True)
        i = 0
        while i < len(tokens):
            match = next((a for a in allowed if a and tokens[i:i + len(a)] == a), None)
            if match:
                i += len(match)
            else:
                token = tokens[i]
                # The plural `s` of an acronym (`EIPs`) is not a word of its own.
                plural = token == 's' and i > 0 and tokens[i - 1].isupper()
                if not token.isdigit() and not plural and token.lower() not in words:
                    unknown.append(token)
                i += 1
    return unknown


def lint_names(names, mapping, policy, words, final=False):
    """(problems, used source bindings, pending findings). A pending retired
    name is reported without failing, except in a final run, which enforces it."""
    problems, pending = [], []
    used_bindings = set()
    enforced_names, pending_names = MAP.retired_name_lists(mapping)
    if final:
        enforced_names, pending_names = enforced_names + pending_names, []
    abbreviations = set(mapping['allowed_abbreviations'])
    mapped = {entry['new']: entry for entry in mapping['entries']}
    for name, location in sorted(names.items()):
        entry = mapped.get(name)
        if entry and entry['rule'].split(',')[0].strip() in ('1', '2', '3'):
            binding = policy['bindings'].get(name)
            if not binding or binding['rule'] != entry['rule'].split(',')[0].strip():
                problems.append(dict(name=name, location=location, reason='map requires matching source binding'))
        retired = MAP.find_retired_tokens(name, mapping['retired_tokens'])
        if retired:
            problems.append(dict(name=name, location=location, reason='retired token', tokens=retired))
        held = MAP.find_retired_names(name, enforced_names)
        if held:
            problems.append(dict(name=name, location=location, reason='retired name', names=held))
        held = MAP.find_retired_names(name, pending_names)
        if held:
            pending.append(dict(name=name, location=location, reason='pending retired name', names=held))
        parts = name.split('.')
        for i, part in enumerate(parts):
            if i == 0 and part in ('Jaune', 'JauneConsensus'):
                continue
            prefix = '.'.join(parts[:i + 1])
            if prefix in policy['bindings']:
                used_bindings.add(prefix)
                continue
            unknown = unknown_words(part, words, abbreviations)
            if unknown:
                problems.append(dict(name=name, location=location,
                                     reason='unregistered word or source', segment=prefix, tokens=unknown))
    return problems, used_bindings, pending


def check(tree, mapping, policy, source_root, files, roots, final=False):
    MAP.validate_map(mapping)
    registered_pending = MAP.retired_name_lists(mapping)[1]
    words = validate_policy(policy, source_root)
    selected = [source for source, _ in files]
    if len(selected) != len(set(selected)):
        raise ValueError('duplicate selected source')
    # An explicitly partial run cannot masquerade as a whole-tree green verdict.
    if roots:
        expected = set()
        for root in roots:
            directory = APPLY.safe_path(tree, root)
            if not directory.is_dir():
                raise ValueError(f'missing source root: {root}')
            expected.update(p.relative_to(tree).as_posix() for p in directory.rglob('*.lean'))
        if not expected or set(selected) != expected:
            raise ValueError(f'incomplete tree coverage: missing={sorted(expected - set(selected))}, extra={sorted(set(selected) - expected)}')
    elif not selected:
        raise ValueError('no selected files')
    problems, pending, rows, used = [], [], [], set()
    for source, bundle_path in files:
        raw = APPLY.safe_path(tree, source).read_bytes()
        bundle_raw = Path(bundle_path).read_bytes()
        bundle = json.loads(bundle_raw)
        text = raw.decode('utf-8')
        if bundle.get('source') != text:
            raise ValueError(f'{source}: reference bundle source mismatch; re-export')
        names = declarations(text, bundle['index'])
        found, bindings, waiting = lint_names(names, mapping, policy, words, final)
        used.update(bindings)
        problems.extend(dict(source=source, **problem) for problem in found)
        pending.extend(dict(source=source, **problem) for problem in waiting)
        rows.append(dict(source=source, source_sha256=sha(raw), bundle_sha256=sha(bundle_raw), declarations=len(names)))
    if roots:
        for stale in sorted(set(policy['bindings']) - used):
            problems.append(dict(name=stale, reason='unused source binding'))
    if final:
        # The landing map registers no pending name: each one left is a finding of its own.
        for name in registered_pending:
            problems.append(dict(name=name, reason='retired name still registered as pending'))
    return dict(status='REGRESSION' if problems else 'OK', final=final,
                pending_retired_names=registered_pending, pending=pending,
                scope=('whole-tree' if set(roots) == {'Jaune', 'JauneConsensus'}
                       else 'selected-roots' if roots else 'selected-files'), roots=roots,
                files=rows, problems=problems)


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--tree', type=Path, default=Path('.'))
    parser.add_argument('--map', type=Path, default=ROOT / 'scripts/naming-map.json')
    parser.add_argument('--policy', type=Path, required=True)
    parser.add_argument('--source-root', type=Path, required=True)
    parser.add_argument('--file', nargs=2, action='append', default=[], metavar=('SOURCE', 'BUNDLE'))
    parser.add_argument('--root', action='append', default=[], help='require exact .lean coverage of this tree-relative root')
    parser.add_argument('--final', action='store_true',
                        help='landing verdict: pending retired names are enforced, and one still '
                             'registered as pending in the map is a finding')
    parser.add_argument('--report', action='store_true',
                        help='report mode: naming findings exit 0 (setup and coverage failures still exit 2)')
    args = parser.parse_args(argv)
    try:
        map_raw, policy_raw = args.map.read_bytes(), args.policy.read_bytes()
        result = check(args.tree.resolve(), json.loads(map_raw), json.loads(policy_raw),
                       args.source_root.resolve(), args.file, args.root, args.final)
        result['map_sha256'] = sha(map_raw)
        result['policy_sha256'] = sha(policy_raw)
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'SETUP — naming lint: {error}', file=sys.stderr)
        return 2
    result['mode'] = 'report' if args.report else 'gate'
    print(json.dumps(result, indent=2))
    return 1 if result['problems'] and not args.report else 0


if __name__ == '__main__':
    sys.exit(main())
