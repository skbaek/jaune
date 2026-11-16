#!/usr/bin/env python3
"""Stale-name scan and identifier substitution for Jaune's documents (D1).

    naming-docs.py scan  --snapshot CAPTURE/snapshot.json --map MAP.json FILE...
    naming-docs.py apply --snapshot CAPTURE/snapshot.json --map MAP.json FILE...

The capture (taken before the rename) supplies every constant of the tree. A
dotted identifier in a document is *stale* when it is the trailing components
of a renamed constant's old name (or an old module name, dotted or as a
`.lean` path) and of no constant name after the rename: it names something
that no longer exists. Code spans (inline backticks and fenced blocks) are
scanned for every such spelling; prose is scanned for identifier-shaped
spellings (an uppercase letter after the first character, a digit, `_` or
`.`), since plain lowercase words in prose are English.

`scan` exits 0 when no stale spelling remains, 1 otherwise, and lists each with
its file, line and candidate replacements. `apply` substitutes every stale
spelling whose candidate constants all give one replacement (the same number
of trailing components of the new names; decision 7 approves identifier
substitution on these surfaces) and reports the rest for a manual edit.
Exit 2 is a setup refusal. Only spellings change; a passage that a later cut
makes false is a separate review obligation (D1).
"""
import argparse
import importlib.util
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location('check_naming_map', ROOT / 'scripts/check-naming-map.py')
MAP = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(MAP)

IDENT = re.compile(r"(?<![\w.'?!/])[A-Za-z_][\w'?!]*(?:\.[A-Za-z_][\w'?!]*)*")
PATH = re.compile(r"(?<![\w./])(?:[A-Za-z_]\w*/)+[A-Za-z_]\w*\.lean\b")
CODE = re.compile(r'```.*?```|`[^`\n]+`', re.S)


def user(name):
    private = MAP.split_private(name) if name.startswith('_private.') else None
    return private[2] if private else name


def suffixes(name):
    parts = name.split('.')
    return ['.'.join(parts[-k:]) for k in range(1, len(parts) + 1)]


class Index:
    def __init__(self, snapshot, mapping):
        renamer = MAP.Renamer(mapping['entries'])
        base = Path(snapshot).parent
        data = json.loads(Path(snapshot).read_bytes())
        names = set()
        for row in data['exports'].values():
            names.update(json.loads((base / row['path']).read_bytes()).get('constants', {}))
        self.old = {}   # trailing spelling -> {replacement spelling: {old constant}}
        self.renamer = renamer
        after = set()
        for name in names:
            new = user(renamer(name))
            old = user(name)
            after.update(suffixes(new))
            if old == new:
                continue
            o, n = old.split('.'), new.split('.')
            for k in range(1, len(o) + 1):
                spelling = '.'.join(o[-k:])
                # As the apply tool spells it: the unspelled prefix of the old
                # name is the namespace the spelling resolves in; it is renamed
                # by namespace rows, and the new name is spelled below it
                # (`BLT` -> `Rlp.Item`, `gasCreate` -> `Gas.create` in `Jaune`).
                context = '.'.join(o[:-k])
                scope = renamer.scope(context).split('.') if context else []
                replacement = ('.'.join(n[len(scope):]) if n[:len(scope)] == scope and len(n) > len(scope)
                               else new)
                self.old.setdefault(spelling, {}).setdefault(replacement, set()).add(name)
        self.after = after
        self.modules = dict(renamer.modules)
        self.constants = len(names)

    def row(self, name):
        """The map row that renames a constant: its exact row, else the
        longest namespace row over it (with private names by user name)."""
        if name.startswith('module '):
            return name
        name = user(name)
        if name in self.renamer.exact:
            return name
        parts = name.split('.')
        for i in range(len(parts), 0, -1):
            if '.'.join(parts[:i]) in self.renamer.namespaces:
                return 'namespace ' + '.'.join(parts[:i])
        return None

    def stale(self, spelling):
        """None if not stale, else {candidate replacement: {old constant}}."""
        if spelling in self.modules:
            return {self.modules[spelling]: {'module ' + spelling}}
        if spelling.endswith('.lean') and '/' in spelling:
            module = spelling[:-5].replace('/', '.')
            if module in self.modules:
                return {self.modules[module].replace('.', '/') + '.lean': {'module ' + module}}
            return None
        if spelling in self.old and spelling not in self.after:
            return self.old[spelling]
        return None


def identifier_shaped(word):
    return bool(re.search(r"[A-Z]", word[1:]) or re.search(r"[\d_.]", word))


def stale_span(word, start, index):
    """(start, end, spelling, candidates) of the stale part of an identifier
    token, or None: the whole token; else its longest stale identifier-shaped
    leading components (`B256.lt_of_{lt,gt}Check`); else one stale
    identifier-shaped component (`block.toBLT.toBytes`)."""
    found = index.stale(word)
    if found is not None:
        return start, start + len(word), word, found
    if '.' not in word:
        return None
    parts = word.split('.')
    for i in range(len(parts) - 1, 0, -1):
        head = '.'.join(parts[:i])
        if identifier_shaped(head) and index.stale(head) is not None:
            return start, start + len(head), head, index.stale(head)
    offset = start
    for part in parts:
        if identifier_shaped(part) and index.stale(part) is not None:
            return offset, offset + len(part), part, index.stale(part)
        offset += len(part) + 1
    return None


def findings(text, index, all_code=False, path_key=None, keep=frozenset()):
    code = [(0, len(text))] if all_code else [(m.start(), m.end()) for m in CODE.finditer(text)]
    out = []
    taken = []
    for pattern in (PATH, IDENT):
        for m in pattern.finditer(text):
            if any(a < m.end() and m.start() < b for a, b in taken):
                continue
            word = m.group(0)
            if '.' not in word and len(word) < 3:
                continue  # one- and two-letter words (`p`, `M`, `P`) are variables in prose and code
            if (path_key, word) in keep:
                continue
            in_code = any(a <= m.start() < b for a, b in code)
            if not in_code and not identifier_shaped(word):
                continue
            span = stale_span(word, m.start(), index)
            if span is None:
                continue
            start, end, word, candidates = span
            if (path_key, word) in keep:
                continue
            taken.append((m.start(), m.end()))
            out.append(dict(start=start, end=end, old=word, line=text.count('\n', 0, start) + 1,
                            in_code=in_code, candidates=sorted(c for c in candidates if c is not None),
                            unique=len(candidates) == 1 and None not in candidates,
                            rows=sorted({str(index.row(c)) for cs in candidates.values() for c in cs})))
    return sorted(out, key=lambda f: f['start'])


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('command', choices=('scan', 'apply'))
    parser.add_argument('--snapshot', type=Path, required=True)
    parser.add_argument('--map', type=Path, required=True)
    parser.add_argument('--all-code', action='store_true',
                        help='treat each file as code throughout (allowlists, manifests, coverage tables)')
    parser.add_argument('--keep', type=Path,
                        help='registered JSON list of {file, spelling, reason}: a spelling that names an external '
                             'interface rather than a renamed constant (the t8n input `txs`)')
    parser.add_argument('files', nargs='+', type=Path)
    args = parser.parse_args(argv)
    try:
        mapping = json.loads(args.map.read_bytes())
        MAP.validate_map(mapping)
        index = Index(args.snapshot, mapping)
        keep = set()
        if args.keep:
            for row in json.loads(args.keep.read_bytes())['keep']:
                if not row.get('reason', '').strip():
                    raise ValueError(f'keep row without a reason: {row}')
                keep.add((row['file'], row['spelling']))
    except (OSError, ValueError, KeyError) as error:
        print(f'REFUSED — naming docs: {error}', file=sys.stderr)
        return 2
    report, remaining, substituted, edits = [], 0, 0, []
    for path in args.files:
        text = path.read_text(encoding='utf-8')
        found = findings(text, index, args.all_code, str(path), keep)
        if args.command == 'apply':
            for f in reversed(found):
                if f['unique']:
                    text = text[:f['start']] + f['candidates'][0] + text[f['end']:]
                    substituted += 1
                    edits.append(dict(file=str(path), line=f['line'], old=f['old'], new=f['candidates'][0],
                                      rows=f['rows']))
            path.write_text(text, encoding='utf-8')
            found = findings(text, index, args.all_code, str(path), keep)
        remaining += len(found)
        for f in found:
            report.append(dict(file=str(path), line=f['line'], old=f['old'], code=f['in_code'],
                               candidates=f['candidates'], rows=f['rows']))
    print(json.dumps(dict(command=args.command, constants=index.constants, files=[str(p) for p in args.files],
                          substituted=substituted, edits=sorted(edits, key=lambda e: (e['file'], e['line'])),
                          stale=report), indent=1))
    verdict = 'OK' if not remaining else 'STALE'
    print(f'{verdict} — naming docs: {remaining} stale spelling(s) in {len(args.files)} file(s)'
          + (f'; {substituted} substituted' if args.command == 'apply' else ''), file=sys.stderr)
    return 0 if not remaining else 1


if __name__ == '__main__':
    sys.exit(main())
