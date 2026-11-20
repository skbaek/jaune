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

Four forms read context (jsn-u16, after the G0a review):
- a brace pattern in code (`Nat.toB256_{add,mul}_toB256`) is expanded; when
  every expansion is stale with one replacement and the replacements share
  the pattern's shape, the pattern is respelled as one;
- a member list after a code span naming a type (`Account` (`nonce`, `bal`))
  qualifies each plain member by the type (as it was named before the rename
  or after it): `bal` is stale when `Acct.bal` was renamed and `Account.bal`
  names nothing;
- a two-character code token starting with an uppercase letter (`Tx`) is a
  name, not a variable (one-letter tokens still are);
- with `--plan` (the applied whole-tree plan, bound to this snapshot and map
  by digest), a dotted code token headed by a variable (`rules.pow`) is stale
  when the tree spelled it exactly so and the plan respelled every such
  occurrence one way (`rules.proofOfWork`).
With `--delete-receipt`, the scan also reports retired declarations and module
paths. A name reused on the candidate is still valid. Removed names have no
automatic replacement.

Modules under `scripts/tests/` (naming-tool fixtures) are not indexed: no
document describes them, and their names must not keep a product name alive.

`scan` exits 0 when no stale spelling remains, 1 otherwise, and lists each with
its file, line and candidate replacements. `apply` substitutes every stale
spelling whose candidate constants all give one replacement (the same number
of trailing components of the new names; decision 7 approves identifier
substitution on these surfaces) and reports the rest for a manual edit.
Exit 2 is a setup refusal. Only spellings change; a passage that a later cut
makes false is a separate review obligation (D1).
"""
import argparse
import hashlib
import importlib.util
import itertools
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
_spec = importlib.util.spec_from_file_location('check_naming_map', ROOT / 'scripts/check-naming-map.py')
MAP = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(MAP)

IDENT = re.compile(r"(?<![\w.'?!/])[A-Za-z_][\w'?!]*(?:\.[A-Za-z_][\w'?!]*)*")
PATH = re.compile(r"(?<![\w./])(?:[A-Za-z_]\w*/)*[A-Za-z_]\w*\.lean\b")
CODE = re.compile(r'```.*?```|`[^`\n]+`', re.S)
BRACE = re.compile(r"(?<![\w.'?!/{,])[A-Za-z_][\w'?!.]*(?:\{[\w'?!]+(?:,[\w'?!]+)+\}[\w'?!.]*)+")
MEMBERS = re.compile(r"`([A-Z][\w'?!.]*)`\s*\(((?:\s*`[^`\n]+`\s*(?:,|\bor\b|\band\b)?)+)\s*\)")
WILDCARD = re.compile(r"`([A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*)\*`")
VARFIELD = re.compile(r"(?<![\w.'?!/])[a-z][\w'?!]*(?:\.[A-Za-z_][\w'?!]*)+")
TOKEN = re.compile(r"[A-Za-z_][\w'?!]*(?:\.[A-Za-z_][\w'?!]*)*")
FIXTURES = 'scripts/tests/'


def sha(data):
    return hashlib.sha256(data).hexdigest()


def lean_code(text):
    """Lean source with comments and string literals blanked (same length):
    a comment that quotes a spelling is documentation, not a live use."""
    out, i, depth = list(text), 0, 0
    while i < len(text):
        if depth == 0 and text.startswith('--', i):
            j = text.find('\n', i)
            j = len(text) if j < 0 else j
            out[i:j] = ' ' * (j - i)
            i = j
        elif text.startswith('/-', i):
            depth, out[i:i + 2], i = depth + 1, '  ', i + 2
        elif depth and text.startswith('-/', i):
            depth, out[i:i + 2], i = depth - 1, '  ', i + 2
        elif depth:
            out[i] = out[i] if out[i] == '\n' else ' '
            i += 1
        elif text[i] == '"':
            j = i + 1
            while j < len(text) and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            for k in range(i, min(j + 1, len(text))):
                out[k] = out[k] if out[k] == '\n' else ' '
            i = j + 1
        else:
            i += 1
    return ''.join(out)


def user(name):
    private = MAP.split_private(name) if name.startswith('_private.') else None
    return private[2] if private else name


def suffixes(name):
    parts = name.split('.')
    return ['.'.join(parts[-k:]) for k in range(1, len(parts) + 1)]


class Index:
    def __init__(self, snapshot, mapping, plan=None, deletion=None):
        renamer = MAP.Renamer(mapping['entries'])
        base = Path(snapshot).parent
        data = json.loads(Path(snapshot).read_bytes())
        if deletion is not None:
            validate_deletion(deletion, data['candidate']['head'])
        names = set()
        sources = {}
        for module, row in data['exports'].items():
            path = data['candidate']['modules'].get(module, {}).get('path', '')
            if path.startswith(FIXTURES):
                continue
            export = json.loads((base / row['path']).read_bytes())
            names.update(export.get('constants', {}))
            if path and plan is not None:
                sources[path] = export.get('source', '')
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
        # Old spellings, by the spelling they became (`Account` <- `Acct`).
        self.before_of = {}
        for spelling, replacements in self.old.items():
            for replacement in replacements:
                self.before_of.setdefault(replacement, set()).add(spelling)
        self.variable_tokens = self.plan_tokens(plan, sources) if plan is not None else {}
        self.modules = dict(renamer.modules)
        self.unrenamed_modules = set(data['candidate']['modules']) - set(self.modules)
        self.constants = len(names)
        self.deleted = {}
        if deletion is not None:
            self.index_deletions(deletion)

    def index_deletions(self, receipt):
        """A retired name has no automatic substitution. Reused names stay live."""
        rows = receipt['deleted']
        live_modules = self.unrenamed_modules | set(self.modules.values())
        live_paths = {m.replace('.', '/') + '.lean' for m in live_modules}
        live_basenames = {path.rsplit('/', 1)[-1] for path in live_paths}
        live = self.after | live_modules | live_paths | live_basenames

        def record(spelling, source):
            if spelling not in live:
                self.deleted.setdefault(spelling, set()).add(source)

        for group in rows.values():
            for row in group:
                name = user(row['name'])
                for spelling in suffixes(name):
                    record(spelling, 'deleted ' + name)
        for module in receipt['modules']['deleted']:
            path = module.replace('.', '/') + '.lean'
            for spelling in (module, path, path.rsplit('/', 1)[-1]):
                record(spelling, 'deleted module ' + module)

    @staticmethod
    def plan_tokens(plan, sources):
        """{old dotted token: {new token}} for tokens headed by a variable
        (`rules.pow`) whose every occurrence in the before tree the applied
        plan respelled; a token left anywhere unedited is still live."""
        edited, tokens = {}, {}
        for row in plan['files']:
            text = sources.get(row['path'])
            if text is None:
                continue
            for edit in row['edits']:
                a, b = edit['start'], edit['end']
                left, right = a, b
                while left > 0 and (text[left - 1].isalnum() or text[left - 1] in "_'?!."):
                    left -= 1
                while right < len(text) and (text[right].isalnum() or text[right] in "_'?!."):
                    right += 1
                old = text[left:right].rstrip('.')
                if left == a or '.' not in old or not re.fullmatch(VARFIELD, old):
                    continue
                new = text[left:a] + edit['new'] + text[b:left + len(old)]
                edited.setdefault((row['path'], left), (old, new, set()))[2].add(edit.get('declaration'))
        for (path, left), (old, new, decls) in edited.items():
            tokens.setdefault(old, {}).setdefault(new, set()).update(d for d in decls if d)
        live = {}
        for text in sources.values():
            for m in VARFIELD.finditer(lean_code(text)):
                if m.group(0) in tokens:
                    live[m.group(0)] = live.get(m.group(0), 0) + 1
        counts = {}
        for old, _, _ in edited.values():
            counts[old] = counts.get(old, 0) + 1
        return {old: news for old, news in tokens.items() if live.get(old) == counts[old]}

    def member(self, owner, member):
        """None, or {new leaf: {old constant}} when `member` of the type the
        document names `owner` is stale: `owner.member` names nothing after
        the rename, and the type's old name qualified by `member` was renamed
        to one leaf."""
        if f'{owner}.{member}' in self.after:
            return None
        found = {}
        for old_owner in {owner} | self.before_of.get(owner, set()):
            for replacement, constants in self.old.get(f'{old_owner}.{member}', {}).items():
                found.setdefault(replacement.split('.')[-1], set()).update(constants)
            deleted = self.deleted.get(f'{old_owner}.{member}')
            if deleted:
                found.setdefault(None, set()).update(deleted)
        return found or None

    def family(self, prefix):
        """None, or {new prefix: {old constant}} for a wildcard family `P*`:
        at least two renamed one-component spellings start with P, each became
        Q + the same rest for one Q, and no constant of their namespaces
        spelled P... is left after the rename."""
        removed = {name for word, names in self.deleted.items() if word.startswith(prefix)
                   and '.' not in word[len(prefix):] for name in names}
        if removed:
            if any(word.startswith(prefix) and '.' not in word[len(prefix):] for word in self.after):
                return None
            return {None: removed}
        hits, news, parents = {}, set(), set()
        for spelling, replacements in self.old.items():
            if '.' in spelling or not spelling.startswith(prefix) or spelling in self.after:
                continue
            for replacement, constants in replacements.items():
                rest = spelling[len(prefix):]
                if '.' in replacement or not replacement.endswith(rest):
                    return None
                news.add(replacement[:len(replacement) - len(rest)] if rest else replacement)
                hits.setdefault(spelling, set()).update(constants)
                parents.update(user(c).rsplit('.', 1)[0] for c in constants if '.' in user(c))
        if len(hits) < 2 or len(news) != 1:
            return None
        for name in self.after:
            if any(name.startswith(f'{parent}.{prefix}') and '.' not in name[len(parent) + 1:] for parent in parents):
                return None
        return {news.pop(): set().union(*hits.values())}

    def row(self, name):
        """The map row that renames a constant: its exact row, else the
        longest namespace row over it (with private names by user name)."""
        if name.startswith(('module ', 'deleted ')):
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
        if spelling.endswith('.lean'):
            module = spelling[:-5].replace('/', '.')
            if module in self.modules:
                return {self.modules[module].replace('.', '/') + '.lean': {'module ' + module}}
            if '/' not in spelling:
                # A bare file name (`GloasOps.lean`): the renamed modules whose
                # last component it is, when they agree, and no unrenamed module
                # of that file name (the module set is the capture's).
                stem = spelling[:-5]
                hits = {old: new for old, new in self.modules.items() if old.split('.')[-1] == stem}
                news = {new.split('.')[-1] + '.lean' for new in hits.values()}
                if hits and len(news) == 1 and not any(m.split('.')[-1] == stem for m in self.unrenamed_modules):
                    return {news.pop(): {'module ' + old for old in hits}}
        if spelling in self.deleted:
            return {None: self.deleted[spelling]}
        if spelling in self.old and spelling not in self.after:
            return self.old[spelling]
        return None


def identifier_shaped(word):
    return bool(re.search(r"[A-Z]", word[1:]) or re.search(r"[\d_.]", word))


def validate_deletion(receipt, head):
    """The delete can be followed by other commits before the rename capture."""
    if (receipt.get('schema_version') != 1 or receipt.get('verdict') != 'OK'
            or receipt.get('unbound_rehearsal') is not False
            or not all(receipt[side]['bound'] is True for side in ('before', 'after'))):
        raise ValueError('a bound, passing delete-preservation receipt is required')
    if sum(len(group) for group in receipt['deleted'].values()) != receipt['deleted_declarations']:
        raise ValueError('deleted-name inventory does not match receipt total')
    after = receipt['after']['revision']
    if not all(isinstance(rev, str) and re.fullmatch('[0-9a-f]{40}', rev) for rev in (after, head)):
        raise ValueError('expected full delete and snapshot commits')
    if after != head and subprocess.run(
            ['git', 'merge-base', '--is-ancestor', after, head], cwd=ROOT).returncode != 0:
        raise ValueError('delete receipt is not an ancestor of the rename snapshot')


def stale_span(word, start, index):
    """(start, end, spelling, candidates) of the stale part of an identifier
    token, or None: the whole token; else its longest stale identifier-shaped
    leading components (`B256.lt_of_{lt,gt}Check`); else one stale
    identifier-shaped component (`block.toBLT.toBytes`)."""
    found = index.stale(word)
    if found is not None:
        return start, start + len(word), word, found
    if '.' not in word or word in index.after:
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


def brace_finding(word, start, index):
    """A finding for a stale brace pattern, or None when no expansion is stale."""
    pieces = re.split(r'\{([^{}]*)\}', word)
    literals, groups = pieces[0::2], [g.split(',') for g in pieces[1::2]]
    results = {}
    for combo in itertools.product(*groups):
        spelling = literals[0] + ''.join(c + l for c, l in zip(combo, literals[1:]))
        found = index.stale(spelling)
        results[combo] = found
    if all(v is None for v in results.values()):
        return None
    def candidate():
        if any(v is None or len(v) != 1 or None in v for v in results.values()):
            return None
        news = {combo: next(iter(v)) for combo, v in results.items()}
        first = tuple(g[0] for g in groups)
        target = news[first]
        # Find the new literals: positions of the first alternatives, in order.
        def splits(text, alternatives, at=0):
            if not alternatives:
                yield [text[at:]]
                return
            i = text.find(alternatives[0], at)
            while i >= 0:
                for rest in splits(text, alternatives[1:], i + len(alternatives[0])):
                    yield [text[at:i]] + rest
                i = text.find(alternatives[0], i + 1)
        for new_literals in splits(target, list(first)):
            if all(new_literals[0] + ''.join(c + l for c, l in zip(combo, new_literals[1:])) == new
                   for combo, new in news.items()):
                return new_literals[0] + ''.join('{' + ','.join(g) + '}' + l
                                                 for g, l in zip(groups, new_literals[1:]))
        return None
    new = candidate()
    constants = set().union(*[c for v in results.values() if v for c in v.values()])
    return dict(start=start, end=start + len(word), old=word, candidates={new: constants} if new else
                {('<expansions not uniformly stale>' if None in results.values() else '<no common shape>'): constants},
                unique=new is not None)


def context_findings(text, index, code):
    """Findings of the brace, member-list and variable-field forms."""
    out = []
    for a, b in code:
        span = text[a:b]
        for m in BRACE.finditer(span):
            found = brace_finding(m.group(0), a + m.start(), index)
            if found:
                out.append(found)
        for m in VARFIELD.finditer(span):
            word = m.group(0)
            news = index.variable_tokens.get(word)
            if news:
                out.append(dict(start=a + m.start(), end=a + m.end(), old=word,
                                candidates=news, unique=len(news) == 1))
    for a, b in code:
        for m in WILDCARD.finditer(text, a, b):
            found = index.family(m.group(1))
            if found:
                out.append(dict(start=m.start(1), end=m.end(1), old=m.group(1), candidates=found,
                                unique=len(found) == 1))
    for m in MEMBERS.finditer(text):
        owner = m.group(1)
        inner_start = m.start(2)
        for item in re.finditer(r'`([^`\n]+)`', m.group(2)):
            member = item.group(1)
            if not re.fullmatch(r"[a-z_][\w'?!]*", member):
                continue
            found = index.member(owner, member)
            if found:
                out.append(dict(start=inner_start + item.start(1), end=inner_start + item.end(1), old=member,
                                candidates=found, unique=len(found) == 1))
    return out


def findings(text, index, all_code=False, path_key=None, keep=frozenset()):
    code = [(0, len(text))] if all_code else [(m.start(), m.end()) for m in CODE.finditer(text)]
    out = []
    taken = []
    for f in context_findings(text, index, code):
        if (path_key, f['old']) in keep or any(a < f['end'] and f['start'] < b for a, b in taken):
            continue
        taken.append((f['start'], f['end']))
        candidates = f['candidates']
        out.append(dict(start=f['start'], end=f['end'], old=f['old'], line=text.count('\n', 0, f['start']) + 1,
                        in_code=True, candidates=sorted(c for c in candidates if c is not None),
                        unique=f['unique'] and None not in candidates,
                        rows=sorted({str(index.row(c)) for cs in candidates.values() for c in cs})))
    for pattern in (PATH, IDENT):
        for m in pattern.finditer(text):
            if any(a < m.end() and m.start() < b for a, b in taken):
                continue
            word = m.group(0)
            in_code = any(a <= m.start() < b for a, b in code)
            if '.' not in word and (len(word) < 2 or (len(word) == 2 and not (in_code and word[0].isupper()))):
                continue  # one-letter words (`p`, `M`, `P`) and lowercase or prose two-letter words are variables
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
    parser.add_argument('--delete-receipt', type=Path,
                        help='bound check-delete-preservation receipt from before the rename; '
                             'report removed names and module paths that the rename did not restore')
    parser.add_argument('--all-code', action='store_true',
                        help='treat each file as code throughout (allowlists, manifests, coverage tables)')
    parser.add_argument('--keep', type=Path,
                        help='registered JSON list of {file, spelling, reason}: a spelling that names an external '
                             'interface rather than a renamed constant (the t8n input `txs`)')
    parser.add_argument('--plan', type=Path,
                        help='the applied whole-tree plan (bound to --snapshot and --map by digest): '
                             'variable-headed code tokens it respelled everywhere (`rules.pow`)')
    parser.add_argument('files', nargs='+', type=Path)
    args = parser.parse_args(argv)
    try:
        raw_map = args.map.read_bytes()
        mapping = json.loads(raw_map)
        MAP.validate_map(mapping)
        plan = None
        if args.plan:
            plan = json.loads(args.plan.read_bytes())
            if plan.get('status') != 'planned' or plan.get('map_sha256') != sha(raw_map) or \
                    plan.get('snapshot_sha256') != sha(args.snapshot.read_bytes()):
                raise ValueError('plan is not a planned plan of this snapshot and map')
        deletion = json.loads(args.delete_receipt.read_bytes()) if args.delete_receipt else None
        index = Index(args.snapshot, mapping, plan, deletion)
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
