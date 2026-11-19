#!/usr/bin/env python3
"""Check the bridge ledger of goal `jaune-shape-and-names-v1` (X1, section 8).

`scripts/bridge-ledger.json` records, per cut or per map, the bridge theorem,
the module and gate tag where it builds, its axiom audit, the old side (the
revision it is taken from, its roots, where it waits at the tag), the rename
maps that join the two revisions and the N4 receipts that checked those maps.

Mode A (default; light, git and text only): the ledger's schema; each gate tag
resolves to its recorded commit; each theorem, old root, old side at the tag
and new name is declared in its module at the cited revision (the gate's
commit, or `--head` while the gate is pending); each theorem has an audit row
(`#expect_axioms` with the standard axioms, `#union_axioms_of_modules`, or the
union walk's import closure) at that revision; every exemption names the
ledger entry that bridges it; every committed map has its recorded sha256 at
its revision and every N4 receipt names one of the entry's maps; a Mode B
receipt present for a gate is bound to the ledger, the tag and a clean
verdict. Open gaps are listed and counted; `--require-closed GATE` fails while
the gate has any.

Mode B (`--closure`; heavy, once per gate at the tag candidate): from an N4
capture of the old revision and one of the tag (`naming-candidate.py
capture`, `--reuse` the N4 snapshots), walk each old root's dependency closure
in the old export, stopping at exempt and non-Jaune (unexported) constants;
map it through the entry's maps, composed in order; compare every closure
member with N4's per-constant comparator; write
`scripts/bridge-ledger-receipts/<gate>.json` (or `--receipt`) binding the tag
commit, the snapshot and export digests, the map digests and the verdict.

Exit 0 iff the verdict is OK; 1 on a finding (REGRESSION); 2 on SETUP.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
LEDGER = ROOT / 'scripts' / 'bridge-ledger.json'
RECEIPTS = ROOT / 'scripts' / 'bridge-ledger-receipts'
SCHEMA = 1
STANDARD_AXIOMS = ['Classical.choice', 'Quot.sound', 'propext']
KINDS = ('theorem', 'map')
GATE_STATUS = ('tagged', 'pending')
AUDIT_KINDS = ('expect_axioms', 'union_modules', 'union_walk', 'receipt')
N4_STATUS = ('OK', 'RESIDUAL')
SHA = re.compile(r'[0-9a-f]{40}')
SHA256 = re.compile(r'[0-9a-f]{64}')
NAME = re.compile(r"[A-Za-z_][\w'!?]*(\.[A-Za-z_][\w'!?]*)*")


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


# One copy of the naming library: the candidate module's comparator is the
# one whose `Mismatch` its readers raise.
CANDIDATE = load('naming-candidate.py')
FIDELITY = CANDIDATE.FIDELITY
MAP = FIDELITY.MAP


class Finding(ValueError):
    """A ledger or closure finding (REGRESSION)."""


def sha256(data):
    return hashlib.sha256(data).hexdigest()


# ---------------------------------------------------------------- git (text)

class Git:
    """Blob and commit reads through one `git cat-file --batch` process."""

    def __init__(self, root):
        self.root = root
        self.proc = subprocess.Popen(['git', '-C', str(root), 'cat-file', '--batch'],
                                     stdin=subprocess.PIPE, stdout=subprocess.PIPE)
        self.cache = {}

    def close(self):
        if self.proc.poll() is None:
            self.proc.stdin.close()
            self.proc.wait()
        self.proc.stdout.close()

    def object(self, spec):
        if spec not in self.cache:
            self.proc.stdin.write(spec.encode() + b'\n')
            self.proc.stdin.flush()
            header = self.proc.stdout.readline().decode().split()
            if len(header) != 3:
                self.cache[spec] = None
            else:
                data = self.proc.stdout.read(int(header[2]))
                self.proc.stdout.read(1)
                self.cache[spec] = (header[0], header[1], data)
        return self.cache[spec]

    def commit(self, rev):
        found = self.object(f'{rev}^{{commit}}')
        return found[0] if found else None

    def blob(self, rev, path):
        found = self.object(f'{rev}:{path}')
        return found[2] if found and found[1] == 'blob' else None

    def paths(self, rev):
        raw = subprocess.check_output(['git', '-C', str(self.root), 'ls-tree', '-r', '--name-only', '-z', rev])
        return set(raw.decode().split('\0')) - {''}


def module_paths(module):
    base = module.replace('.', '/') + '.lean'
    return [base, 'scripts/' + base]


def module_source(git, rev, module):
    for path in module_paths(module):
        data = git.blob(rev, path)
        if data is not None:
            return path, data.decode('utf-8', 'replace')
    return None, None


SCOPE = re.compile(r'^\s*(namespace|section|mutual|end)\b[ \t]*([^\s]*)')
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*"
                  r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+"
                  r"([A-Za-z_][\w'!?.]*)")


TOKEN = re.compile(r'/-|-/|--|"|\n')


def code(source):
    """`source` with comments and string literals blanked, newlines kept: a
    regular-expression pass (`check-naming-fidelity.code_text` walks every
    character, too slow for a sub-second gate over whole revisions)."""
    out, depth, start, pos = [], 0, 0, 0
    while True:
        m = TOKEN.search(source, pos)
        if m is None:
            if depth == 0:
                out.append(source[start:])
            else:
                out.append(re.sub(r'[^\n]', ' ', source[start:]))
            return ''.join(out)
        token, at = m.group(0), m.start()
        if depth:
            if token == '/-':
                depth += 1
            elif token == '-/':
                depth -= 1
                if depth == 0:
                    out.append(re.sub(r'[^\n]', ' ', source[start:m.end()]))
                    start = m.end()
            pos = m.end()
        elif token == '/-':
            out.append(source[start:at])
            start, depth, pos = at, 1, m.end()
        elif token == '--':
            end = source.find('\n', at)
            end = len(source) if end < 0 else end
            out.append(source[start:at])
            start = pos = end
        elif token == '"':
            if at > 0 and source[at - 1] == "'" and source[at + 1:at + 2] == "'":
                pos = at + 2  # the character literal '"'
                continue
            close = re.compile(r'(?:\\.|[^"\\])*"', re.S).match(source, at + 1)
            end = close.end() if close else len(source)
            out.append(source[start:at])
            out.append(re.sub(r'[^\n]', ' ', source[at:end]))
            start = pos = end
        else:
            pos = m.end()


def declared_names(source):
    """Fully qualified names declared by `theorem`/`def`/... commands, by a
    line scan with comments and strings blanked and namespaces tracked."""
    scopes, names = [], set()
    for line in code(source).split('\n'):
        scope = SCOPE.match(line)
        if scope:
            word, arg = scope.groups()
            if word == 'namespace' and arg:
                scopes.append(arg.split('.'))
            elif word in ('section', 'mutual'):
                scopes.append([])
            elif word == 'end' and scopes:
                scopes.pop()
            continue
        decl = DECL.match(line)
        if decl:
            name = decl.group(1)
            if name.startswith('_root_.'):
                names.add(name[len('_root_.'):])
            else:
                names.add('.'.join([p for s in scopes for p in s] + [name]))
    return names


def directives(source, keyword):
    """[(argument line)] of each `keyword` command outside comments."""
    return [line.strip()[len(keyword):].strip() for line in code(source).split('\n')
            if line.strip().startswith(keyword + ' ')]


def header_imports(source):
    """The module header's imports (Lean admits them only before any other
    command): the scan ends at the first other code line."""
    imports = []
    for line in code(source[:header_end(source)]).split('\n'):
        words = line.split()
        if words[:1] == ['import'] and len(words) == 2:
            imports.append(words[1])
    return imports


def header_end(source):
    """An offset past the header: the first line that is neither blank, a
    comment, nor an import, outside block comments (an over-long prefix only
    costs time)."""
    depth, offset = 0, 0
    for line in source.split('\n'):
        stripped = line.strip()
        if depth == 0 and stripped and not stripped.startswith(('import ', '--', '/-')):
            return offset
        depth = max(0, depth + line.count('/-') - line.count('-/'))
        offset += len(line) + 1
    return len(source)


def import_closure(git, rev, roots):
    seen, todo = set(), list(roots)
    while todo:
        module = todo.pop()
        if module in seen:
            continue
        seen.add(module)
        _, source = module_source(git, rev, module)
        if source is not None:
            todo.extend(header_imports(source))
    return seen


# ---------------------------------------------------------------- schema

def _strings(value, nonempty=False):
    return isinstance(value, list) and all(isinstance(x, str) and x for x in value) and (value or not nonempty)


def validate(ledger):
    """Schema problems (strings); empty when the ledger is well formed."""
    problems = []

    def need(cond, message):
        if not cond:
            problems.append(message)
        return cond

    if not need(isinstance(ledger, dict) and ledger.get('schema_version') == SCHEMA, 'schema_version must be 1'):
        return problems
    need(ledger.get('standard_axioms') == STANDARD_AXIOMS, f'standard_axioms must be {STANDARD_AXIOMS}')
    gates = ledger.get('gates')
    if not need(isinstance(gates, dict) and gates, 'gates must be a nonempty object'):
        return problems
    for name, gate in gates.items():
        where = f'gate {name}'
        if not need(isinstance(gate, dict) and set(gate) == {'tag', 'commit', 'status'}, f'{where}: keys tag, commit, status'):
            continue
        need(isinstance(gate['tag'], str) and gate['tag'].startswith('gate/'), f'{where}: tag gate/...')
        need(gate['status'] in GATE_STATUS, f'{where}: status in {GATE_STATUS}')
        need(gate['commit'] is None and gate['status'] == 'pending' or
             isinstance(gate['commit'], str) and SHA.fullmatch(gate['commit']),
             f'{where}: commit is a full sha (null only while pending)')
    entries = ledger.get('entries')
    if not need(isinstance(entries, list), 'entries must be a list'):
        return problems
    ids = [e.get('id') for e in entries if isinstance(e, dict)]
    need(len(ids) == len(set(ids)) == len(entries), 'entry ids must be present and unique')
    keys = {'id', 'gate', 'kind', 'theorem', 'module', 'audit', 'old', 'new', 'exempt', 'maps',
            'n4_receipts', 'accepted', 'gaps', 'notes'}
    for entry in entries:
        if not isinstance(entry, dict):
            continue
        where = f'entry {entry.get("id")}'
        if not need(set(entry) == keys, f'{where}: keys must be exactly {sorted(keys)}'):
            continue
        need(entry['gate'] in gates, f'{where}: unknown gate {entry["gate"]!r}')
        need(entry['kind'] in KINDS, f'{where}: kind in {KINDS}')
        if entry['kind'] == 'theorem':
            need(isinstance(entry['theorem'], str) and NAME.fullmatch(entry['theorem']), f'{where}: theorem name')
            need(isinstance(entry['module'], str) and NAME.fullmatch(entry['module']), f'{where}: module name')
            need(isinstance(entry['audit'], list) and entry['audit'], f'{where}: audit rows required')
        else:
            need(entry['theorem'] is None and entry['module'] is None, f'{where}: a map bridge has no theorem')
            need(isinstance(entry['n4_receipts'], list) and entry['n4_receipts'],
                 f'{where}: a map bridge needs its N4 receipt')
        for row in entry['audit'] if isinstance(entry['audit'], list) else [None]:
            if not need(isinstance(row, dict) and row.get('kind') in AUDIT_KINDS, f'{where}: audit kind in {AUDIT_KINDS}'):
                continue
            if row['kind'] == 'receipt':
                need(set(row) == {'kind', 'axioms', 'record'} and _strings(row['axioms']) and
                     isinstance(row['record'], str) and row['record'], f'{where}: receipt audit {{axioms, record}}')
            else:
                need(set(row) == {'kind', 'file'} and isinstance(row['file'], str) and row['file'].endswith('.lean'),
                     f'{where}: {row["kind"]} audit {{file}}')
        old = entry['old']
        if need(isinstance(old, dict) and set(old) == {'revision', 'roots', 'modules', 'at_tag', 'modules_at_tag'},
                f'{where}: old keys revision, roots, modules, at_tag, modules_at_tag'):
            need(isinstance(old['revision'], str) and SHA.fullmatch(old['revision']), f'{where}: old revision full sha')
            for key in ('roots', 'modules', 'at_tag', 'modules_at_tag'):
                need(_strings(old[key]), f'{where}: old {key} is a list of names')
            need(len(old['roots']) == len(old['at_tag']), f'{where}: old roots and at_tag pair up')
            need(bool(old['roots']) == bool(old['modules']) == bool(old['modules_at_tag']),
                 f'{where}: old roots need their modules at both revisions')
            need(entry['kind'] == 'map' or old['roots'], f'{where}: a theorem bridge names its old roots')
        new = entry['new']
        need(isinstance(new, dict) and set(new) == {'names', 'modules'} and _strings(new['names']) and
             _strings(new['modules']) and bool(new['names']) == bool(new['modules']),
             f'{where}: new {{names, modules}}')
        for row in entry['exempt'] if isinstance(entry['exempt'], list) else [None]:
            need(isinstance(row, dict) and {'name', 'bridged_by'} <= set(row) <= {'name', 'bridged_by', 'replacement'} and
                 isinstance(row['name'], str) and row['name'] and isinstance(row.get('bridged_by'), str) and
                 row['bridged_by'] and isinstance(row.get('replacement', ''), str),
                 f'{where}: exempt rows are {{name, bridged_by[, replacement]}}')
        for row in entry['maps'] if isinstance(entry['maps'], list) else [None]:
            if need(isinstance(row, dict) and set(row) in ({'path', 'revision', 'sha256'},
                                                            {'path', 'revision', 'sha256', 'gap'}),
                    f'{where}: map rows are {{path, revision, sha256[, gap]}}'):
                need(isinstance(row['sha256'], str) and SHA256.fullmatch(row['sha256']), f'{where}: map sha256')
                need(isinstance(row['revision'], str) and SHA.fullmatch(row['revision']) and 'gap' not in row or
                     row['revision'] is None and isinstance(row.get('gap'), str) and row['gap'],
                     f'{where}: a map is committed at a full-sha revision, or uncommitted with its gap stated')
        receipt_keys = {'map_sha256', 'before_candidate', 'after_candidate', 'status', 'record'}
        for row in entry['n4_receipts'] if isinstance(entry['n4_receipts'], list) else [None]:
            if need(isinstance(row, dict) and receipt_keys <= set(row) <= receipt_keys | {'residual', 'environments'},
                    f'{where}: N4 receipts are {sorted(receipt_keys)} [+ residual, environments]'):
                need(row['status'] in N4_STATUS, f'{where}: N4 status in {N4_STATUS}')
                need((row['status'] == 'RESIDUAL') == bool(row.get('residual')), f'{where}: a RESIDUAL states its residual')
                need(all(isinstance(row[k], str) and SHA.fullmatch(row[k]) for k in ('before_candidate', 'after_candidate')),
                     f'{where}: N4 candidates are full shas')
        for row in entry['accepted'] if isinstance(entry['accepted'], list) else [None]:
            need(isinstance(row, dict) and set(row) == {'decision', 'covers', 'text'} and
                 all(isinstance(row[k], str) and row[k] for k in row), f'{where}: accepted rows {{decision, covers, text}}')
        need(_strings(entry['gaps']) and _strings(entry['notes']), f'{where}: gaps and notes are string lists')
    if problems:
        return problems
    by_id = {e['id']: e for e in entries}
    for entry in entries:
        for row in entry['exempt']:
            problem = exemption_problem(by_id, entry, row)
            if problem:
                problems.append(problem)
    return problems


# ---------------------------------------------------------------- Mode A

def gate_revision(ledger, gate, head):
    record = ledger['gates'][gate]
    return record['commit'] if record['commit'] else head


def mode_a(ledger, git, head='HEAD', receipts=RECEIPTS, require_closed=()):
    problems = list(validate(ledger))
    if problems:
        raise Finding('\n'.join(problems))
    gaps = []
    for name, gate in ledger['gates'].items():
        tagged = git.commit(gate['tag'])
        if gate['status'] == 'tagged' and tagged != gate['commit']:
            problems.append(f'gate {name}: {gate["tag"]} resolves to {tagged}, ledger records {gate["commit"]}')
        if gate['status'] == 'pending' and tagged is not None and gate['commit'] not in (None, tagged):
            problems.append(f'gate {name}: {gate["tag"]} exists at {tagged}, ledger records {gate["commit"]}')
        if gate['commit'] and git.commit(gate['commit']) != gate['commit']:
            problems.append(f'gate {name}: commit {gate["commit"]} is not in the repository')
    if git.commit(head) is None:
        raise ValueError(f'--head {head} does not resolve')
    declared = {}

    def names_at(rev, module):
        if (rev, module) not in declared:
            path, source = module_source(git, rev, module)
            declared[rev, module] = (path, declared_names(source) if source is not None else None)
        return declared[rev, module]

    def check_declared(where, rev, names, modules):
        found = set()
        for module in modules:
            path, names_here = names_at(rev, module)
            if names_here is None:
                problems.append(f'{where}: module {module} has no source at {rev[:12]}')
                continue
            found |= names_here
        for name in names:
            if name not in found:
                problems.append(f'{where}: {name} is not declared in {", ".join(modules)} at {rev[:12]}')

    for entry in ledger['entries']:
        where = f'entry {entry["id"]}'
        rev = gate_revision(ledger, entry['gate'], head)
        old = entry['old']
        if git.commit(old['revision']) != old['revision']:
            problems.append(f'{where}: old revision {old["revision"]} is not in the repository')
        else:
            check_declared(f'{where} (old roots)', old['revision'], old['roots'], old['modules'])
        check_declared(f'{where} (old side at the tag)', rev, old['at_tag'], old['modules_at_tag'])
        check_declared(f'{where} (new side)', rev, entry['new']['names'], entry['new']['modules'])
        if entry['kind'] == 'theorem':
            check_declared(where, rev, [entry['theorem']], [entry['module']])
            rows = 0
            for row in entry['audit']:
                if row['kind'] == 'receipt':
                    if set(row['axioms']) - set(STANDARD_AXIOMS):
                        problems.append(f'{where}: receipt axioms {row["axioms"]} beyond the standard three')
                    continue
                data = git.blob(rev, row['file'])
                if data is None:
                    problems.append(f'{where}: audit file {row["file"]} missing at {rev[:12]}')
                    continue
                source = data.decode('utf-8', 'replace')
                if row['kind'] == 'expect_axioms':
                    hits = [line for line in directives(source, '#expect_axioms')
                            if line.split()[:1] == [entry['theorem']]]
                    for line in hits:
                        listed = sorted(x.strip() for x in line.split('[', 1)[-1].rstrip(']').split(',') if x.strip())
                        if listed != STANDARD_AXIOMS:
                            problems.append(f'{where}: audit row expects {listed}, not the standard axioms')
                    rows += bool(hits)
                    if not hits:
                        problems.append(f'{where}: no #expect_axioms row for {entry["theorem"]} in {row["file"]}')
                elif row['kind'] == 'union_modules':
                    prefixes = [line.split()[0] for line in directives(source, '#union_axioms_of_modules') if line]
                    hit = any(entry['module'] == p or entry['module'].startswith(p + '.') for p in prefixes)
                    rows += hit
                    if not hit:
                        problems.append(f'{where}: no #union_axioms_of_modules row covers {entry["module"]} in {row["file"]}')
                else:
                    reached = import_closure(git, rev, header_imports(source))
                    rows += entry['module'] in reached
                    if entry['module'] not in reached:
                        problems.append(f'{where}: {row["file"]} does not import {entry["module"]} at {rev[:12]}')
            if not rows:
                problems.append(f'{where}: no audit row present')
        shas = set()
        for row in entry['maps']:
            shas.add(row['sha256'])
            if row['revision'] is None:
                gaps.append(f'{where}: map {row["path"]} uncommitted ({row["gap"]})')
                continue
            data = git.blob(row['revision'], row['path'])
            if data is None:
                problems.append(f'{where}: map {row["path"]} missing at {row["revision"][:12]}')
            elif sha256(data) != row['sha256']:
                problems.append(f'{where}: map {row["path"]} at {row["revision"][:12]} has sha256 '
                                f'{sha256(data)}, ledger records {row["sha256"]}')
        for row in entry['n4_receipts']:
            if row['map_sha256'] not in shas:
                problems.append(f'{where}: N4 receipt map {row["map_sha256"][:12]} is none of the entry\'s maps')
        gaps.extend(f'{where}: {gap}' for gap in entry['gaps'])
    for name, gate in ledger['gates'].items():
        path = Path(receipts) / f'{name}.json'
        entries = [e for e in ledger['entries'] if e['gate'] == name and e['kind'] == 'theorem']
        if path.is_file():
            problems.extend(check_receipt(ledger, name, json.loads(path.read_bytes())))
        else:
            for entry in entries:
                if not any(a['covers'] == 'closure' for a in entry['accepted']):
                    gaps.append(f'entry {entry["id"]}: no Mode B closure receipt ({path.name})')
    for name in require_closed:
        if name not in ledger['gates']:
            raise ValueError(f'--require-closed: unknown gate {name}')
        if ledger['gates'][name]['status'] != 'tagged':
            problems.append(f'gate {name} not closed: its tag is pending')
        open_here = [g for g in gaps if any(g.startswith(f'entry {e["id"]}:') for e in ledger['entries']
                                             if e['gate'] == name)]
        problems.extend(f'gate {name} not closed: {g}' for g in open_here)
    if problems:
        raise Finding('\n'.join(problems))
    return dict(status='OK', entries=len(ledger['entries']), gates=sorted(ledger['gates']), gaps=gaps)


def closure_scope_sha256(entry):
    """Bind the inputs that affect this theorem's closure comparison."""
    scope = dict(old=entry['old'], exempt=entry['exempt'],
                 maps=[row['sha256'] for row in entry['maps']])
    return sha256(FIDELITY.encoded(scope).encode())


def check_receipt(ledger, gate, receipt):
    where = f'receipt {gate}'
    problems = []
    entries = {e['id']: e for e in ledger['entries'] if e['gate'] == gate and e['kind'] == 'theorem'}
    if receipt.get('schema_version') != SCHEMA or receipt.get('gate') != gate:
        return [f'{where}: schema_version {SCHEMA} for gate {gate} required']
    if receipt.get('verdict') != 'OK':
        problems.append(f'{where}: verdict {receipt.get("verdict")!r}')
    commit = ledger['gates'][gate]['commit']
    if commit is None or receipt.get('tag_commit') != commit:
        problems.append(f'{where}: bound to {receipt.get("tag_commit")}, gate commit is {commit}')
    before, after = receipt.get('before', {}), receipt.get('after', {})
    if before.get('bound') is not True or after.get('bound') is not True:
        problems.append(f'{where}: captures are not bound to the old revision and the tag')
    seen = set()
    for row in receipt.get('entries', []):
        entry = entries.get(row.get('id'))
        if entry is None or entry['id'] in seen:
            problems.append(f'{where}: expected one closure result per {gate} theorem, got {row.get("id")}')
            continue
        seen.add(entry['id'])
        if row.get('verdict') != 'OK' or row.get('mismatches') != []:
            problems.append(f'{where}: entry {entry["id"]} closure did not pass')
        if row.get('maps') != [m['sha256'] for m in entry['maps']] or row.get('roots') != entry['old']['roots']:
            problems.append(f'{where}: entry {entry["id"]} maps or roots differ from the ledger')
        old_rev = entry['old']['revision']
        if row.get('old_revision') != old_rev or before.get('head') != old_rev:
            problems.append(f'{where}: entry {entry["id"]} old revision differs from the ledger')
        if row.get('closure_scope_sha256') != closure_scope_sha256(entry):
            problems.append(f'{where}: entry {entry["id"]} closure scope differs from the ledger; run Mode B again')
    if after.get('head') != commit:
        problems.append(f'{where}: after capture is not at the gate commit')
    missing = entries.keys() - seen
    if missing:
        problems.append(f'{where}: no closure result for {sorted(missing)}')
    return problems


# ---------------------------------------------------------------- Mode B

class Composed(MAP.Renamer):
    """The entry's maps applied in order, with exempt replacements first.

    Each map supplies its naming rules. Authored declarations carry their
    moves and promotions through the intermediate names and modules. An
    exempt `replacement` renames a bridged helper reference to its tag-side
    name without adding a compared declaration."""

    def __init__(self, renamers, overrides, authored_owners):
        self.parts, self.overrides = list(renamers), dict(overrides)
        self.relocations, self.public_from = {}, {}
        if len(self.parts) == 1:
            one = self.parts[0]
            self.exact, self.namespaces, self.modules = dict(one.exact), one.namespaces, one.modules
        else:
            self.namespaces = {}
            self.exact = {old: self._through(old) for one in self.parts for old in one.exact}
            self.modules = {old: self._module(old) for one in self.parts for old in one.modules}
        if any(one.relocations or getattr(one, 'public_from', {}) for one in self.parts):
            for name, owner in authored_owners.items():
                self.record_placement(name.rsplit('@', 1)[0], owner)
        self.exact.update(self.overrides)

    def record_placement(self, old, owner):
        name, current = old, owner
        old_private = MAP.split_private(old)
        moved, promoted = False, False
        for one in self.parts:
            private = MAP.split_private(name)
            user = private[2] if private else name
            move = one.relocations.get(user)
            if move is not None:
                moved = True
                source, target = move
                if source != current:
                    raise Finding(f'relocation of {name} names {source}, expected owner {current}')
                current = target
            elif current is not None:
                current = one.module(current)
            promoted |= name in getattr(one, 'public_from', {})
            name = one(name)
        if moved:
            user = old_private[2] if old_private else old
            move = (owner, current)
            if self.relocations.setdefault(user, move) != move:
                raise Finding(f'inconsistent composed relocations for {user}')
        if promoted:
            self.public_from[old] = name

    def __getattr__(self, attr):
        # One map: any further table a (newer) comparator reads is that map's.
        parts = self.__dict__.get('parts')
        if parts is not None and len(parts) == 1:
            return getattr(parts[0], attr)
        raise AttributeError(attr)

    def _through(self, name):
        for one in self.parts:
            name = one(name)
        return name

    def _module(self, name):
        for one in self.parts:
            name = one.module(name)
        return name

    def derived(self):
        return self.parts[0].derived() if len(self.parts) == 1 else {}

    def explain(self, name):
        if name in self.overrides:
            return self.overrides[name], 'exact'
        if len(self.parts) == 1:
            return self.parts[0].explain(name)
        new = self._through(name)
        return new, 'exact' if new != name else 'unchanged'


def references(record, seen):
    """Names reached through nodes not yet visited in this closure walk."""
    found = set()
    pending = [record]
    while pending:
        node = pending.pop()
        if not isinstance(node, (list, tuple, dict)) or id(node) in seen:
            continue
        seen.add(id(node))
        if isinstance(node, dict):
            pending.extend(node.values())
        elif len(node) == 2 and node[0] == 'name' and isinstance(node[1], str):
            found.add(node[1])
        else:
            pending.extend(node)
    return found


def walk(constants, roots, stop):
    """The roots' dependency closure in `constants`, not entering `stop`
    names or names the export does not hold (non-Jaune constants)."""
    members, stopped, external, todo = set(), set(), set(), list(roots)
    # A decoded expression pool may share nodes across declarations. The
    # environment keeps them alive for the walk, so their identities are stable.
    seen = set()
    while todo:
        name = todo.pop()
        if name in members:
            continue
        if name in stop:
            stopped.add(name)
            continue
        if name not in constants:
            external.add(name)
            continue
        members.add(name)
        todo.extend(references(constants[name], seen) - members)
    return members, stopped, external


def exemption_problem(entries, entry, row):
    name = row['name']
    where = f'entry {entry["id"]}: exempt {name}'
    bridge_id = row.get('bridged_by')
    bridge = entries.get(bridge_id)
    if bridge is None or bridge_id == entry['id']:
        return f'{where} needs another ledger entry'
    if name in entry['old']['roots']:
        return f'{where} is an old root of this entry'
    if bridge['kind'] != 'theorem' or name not in bridge['old']['roots']:
        return f'{where} needs a theorem bridge that names it as an old root ({bridge_id})'
    replacement = row.get('replacement')
    if replacement and replacement not in bridge['new']['names']:
        return f'{where} replacement {replacement} is not named by bridge {bridge_id}'
    return None


def exemptions(ledger, entry):
    """Validate the bridge for each dependency that the closure may skip."""
    by_id = {e['id']: e for e in ledger['entries']}
    rows = {}
    for row in entry['exempt']:
        problem = exemption_problem(by_id, entry, row)
        if problem:
            raise Finding(problem)
        rows[row['name']] = row
    return rows


def scoped_maps(maps, names):
    """Each map's rows that concern the names as they reach that stage:
    namespace and module rows always; an exact row when it renames a current
    name, or the user part of a private one, or names it `public_from`.
    The comparator's map-scope checks (every relocation row names an authored
    constant in scope) then hold for the closure, as they do for N4's scope."""
    current, scoped = set(names), []
    for entries in maps:
        users = current | {MAP.split_private(n)[2] for n in current if MAP.split_private(n)}
        rows = [row for row in entries if row['kind'] in ('namespace', 'module') or
                row['old'] in users or row.get('public_from') in current]
        scoped.append(rows)
        one = MAP.Renamer(rows)
        current = {one(n) for n in current}
    return scoped


def closure_compare(before, after, maps, roots, at_tag, exempt, plan_edits=None, reviewed=None):
    """N4's comparator run on the old roots' dependency closure.

    `before`/`after` are comparator environments (`read_exports` /
    `naming-candidate` shapes), `maps` the entry lists of the entry's maps in
    order. The old closure is walked from the roots, the tag closure from the
    old side the ledger names at the tag, each stopping at exempt names (on
    the tag side at their replacement or image) and at constants no export
    holds. `Comparison.run` then compares the two scopes exactly as N4
    compares a whole capture: authored constants under the map, generated
    constants matched bijectively by graph, attributes, owners and holders.
    Guards, attribute commands, checks and imports are module-level, not
    closure members, and are left out."""
    missing = [r for r in roots if r not in before['constants']]
    if missing:
        raise ValueError(f'old roots not in the old export: {missing}')
    skipped_roots = set(roots) & exempt.keys()
    if skipped_roots:
        raise Finding(f'old roots cannot be exempt: {sorted(skipped_roots)}')
    members, stopped, external = walk(before['constants'], roots, set(exempt))
    overrides = {name: row['replacement'] for name, row in exempt.items() if row.get('replacement')}
    renamers = [MAP.Renamer(rows) for rows in scoped_maps(maps, members | set(exempt))]
    owners = before.get('owners') or {}
    authored_owners = {name: owners.get(name) for name in sorted(members & before['roots'])}
    mapping = Composed(renamers or [MAP.Renamer([])], overrides, authored_owners)
    mismatches = []
    for root, expected in zip(roots, at_tag):
        if mapping(root) != expected:
            mismatches.append(f'old root {root} maps to {mapping(root)}, ledger names {expected} at the tag')
    images = {mapping(name) for name in exempt}
    skipped_roots = set(at_tag) & images
    if skipped_roots:
        raise Finding(f'tag-side old roots cannot be exempt: {sorted(skipped_roots)}')
    tag_members, _, _ = walk(after['constants'], at_tag, images)

    def scope(env, names):
        return dict(env, constants={n: env['constants'][n] for n in names}, roots=env['roots'] & names,
                    guards=[], attributes=[], checks=[], modules={},
                    item_modules={key: [] for key in FIDELITY.ITEMS},
                    derived={n: v for n, v in (env.get('derived') or {}).items() if n in names})

    comparison = FIDELITY.Comparison(scope(before, members), scope(after, tag_members), mapping,
                                     reviewed=reviewed, collect=True, plan_edits=plan_edits)
    try:
        comparison.run()
    except FIDELITY.Mismatch as error:
        lines = str(error).split('\n')
        mismatches.extend(lines[1:] if lines[0].endswith('mismatch(es):') else lines)
    authored = members & before['roots']
    return dict(verdict='REGRESSION' if mismatches else 'OK', closure=len(members), authored=len(authored),
                generated=len(members) - len(authored), tag_closure=len(tag_members),
                stopped_exempt=sorted(stopped), external_references=len(external), mismatches=mismatches)


def load_maps(git, entry, supplied):
    """The entry's maps as validated entry lists, each bound to its sha256: a
    committed map is read at its revision, an uncommitted one from `--map`."""
    by_sha = {}
    for path in supplied:
        raw = Path(path).read_bytes()
        by_sha[sha256(raw)] = raw
    renamers = []
    for row in entry['maps']:
        raw = git.blob(row['revision'], row['path']) if row['revision'] else by_sha.get(row['sha256'])
        if raw is None:
            raise ValueError(f'entry {entry["id"]}: map {row["path"]} ({row["sha256"][:12]}) unavailable; '
                             'pass the file with --map')
        if sha256(raw) != row['sha256']:
            raise ValueError(f'entry {entry["id"]}: map {row["path"]} sha256 differs from the ledger')
        data = json.loads(raw)
        MAP.validate_map(data)
        renamers.append(data['entries'])
    return renamers


def bound(git, snapshot, revision):
    """Bind the complete inventory of paths and file bytes to `revision`."""
    candidate = snapshot['candidate']
    files = candidate['files']
    if candidate['head'] != revision or git.commit(revision) != revision or not files:
        return False
    if git.paths(revision) != files.keys():
        return False
    for path, digest in files.items():
        blob = git.blob(revision, path)
        if blob is None or sha256(blob) != digest:
            return False
    return True


def environment(snapshot, modules):
    selected = CANDIDATE.closure(snapshot['candidate']['modules'], modules)
    paths = {m: snapshot['export_paths'][m] for m in selected}
    bundles = CANDIDATE.read_bundles(paths)
    envs = CANDIDATE.environments(snapshot['candidate']['modules'], selected)
    if len(envs) == 1:
        return CANDIDATE.read_environments(paths, snapshot['candidate']['modules'], selected, bundles)[next(iter(envs))], selected
    return CANDIDATE.union_environment(bundles), selected


def preconditions(before, after):
    left, right = before['candidate'], after['candidate']
    if left['source_dirs'] != right['source_dirs']:
        raise ValueError('module source layout changed between captures')
    for config in CANDIDATE.CONFIG:
        if left['files'].get(config) != right['files'].get(config):
            raise ValueError(f'build/dependency configuration changed: {config}')
    if before['tool_sources'] != after['tool_sources']:
        raise ValueError('capture implementation changed between captures')
    external = [{n: CANDIDATE.artifact_identity(p) for n, p in side['artifacts'].items()
                 if n not in side['candidate']['modules']} for side in (before, after)]
    if external[0] != external[1]:
        # Non-Jaune constants end the walk; they must be the same artifacts.
        raise ValueError('external import artifact boundary changed')


def mode_b(ledger, git, gate, before_path, after_path, ids=(), maps=(), plan=None, reviewed=None):
    start = time.monotonic()
    problems = validate(ledger)
    if problems:
        raise Finding('\n'.join(problems))
    if gate not in ledger['gates']:
        raise ValueError(f'unknown gate {gate}')
    entries = [e for e in ledger['entries'] if e['gate'] == gate and e['kind'] == 'theorem' and (not ids or e['id'] in ids)]
    if ids and {e['id'] for e in entries} != set(ids):
        raise ValueError(f'entries not theorem bridges of {gate}: {sorted(set(ids) - {e["id"] for e in entries})}')
    if not entries:
        raise ValueError(f'gate {gate} has no theorem bridge entries')
    before = CANDIDATE.read_snapshot(before_path, fidelity=False)
    after = CANDIDATE.read_snapshot(after_path, fidelity=False)
    preconditions(before, after)
    revisions = {e['old']['revision'] for e in entries}
    if len(revisions) != 1:
        raise ValueError(f'one old revision per Mode B run; {gate} entries cite {sorted(revisions)}')
    revision = revisions.pop()
    commit = ledger['gates'][gate]['commit']
    reviewed_rows = None
    if reviewed is not None:
        reviewed_rows = json.loads(Path(reviewed).read_bytes())['quotations']
    results, comparisons = [], {}
    for entry in entries:
        renamers = load_maps(git, entry, maps)
        exempt = exemptions(ledger, entry)
        scope = closure_scope_sha256(entry)
        if scope not in comparisons:
            edits = None
            if plan is not None:
                if len(entry['maps']) != 1:
                    raise ValueError('--plan binds to exactly one map')
                row = entry['maps'][0]
                raw_map = (git.blob(row['revision'], row['path']) if row['revision'] else
                           next(Path(p).read_bytes() for p in maps if sha256(Path(p).read_bytes()) == row['sha256']))
                edits = CANDIDATE.plan_edits(Path(plan).read_bytes(), raw_map, Path(before_path).read_bytes())
            old_env, old_selected = environment(before, entry['old']['modules'])
            new_env, new_selected = environment(after, entry['old']['modules_at_tag'])
            result = closure_compare(old_env, new_env, renamers, entry['old']['roots'], entry['old']['at_tag'],
                                     exempt, edits, reviewed_rows)
            comparisons[scope] = dict(result, old_modules=len(old_selected), tag_modules=len(new_selected))
            del old_env, new_env
        # Multiple theorems can observe the same old root under the same
        # closure rules. Keep their receipt rows separate without rereading
        # the exports or running the kernel comparison again.
        results.append(dict(comparisons[scope], id=entry['id'], roots=entry['old']['roots'],
                            old_revision=revision, closure_scope_sha256=scope,
                            maps=[m['sha256'] for m in entry['maps']]))

    def side(snapshot, path, rev):
        return dict(head=snapshot['candidate']['head'], bound=bool(rev) and bound(git, snapshot, rev),
                    snapshot_sha256=CANDIDATE.file_sha(path),
                    inventory_sha256=sha256(FIDELITY.encoded(snapshot['candidate']).encode()),
                    exports_sha256=sha256(FIDELITY.encoded({m: r['sha256'] for m, r in sorted(snapshot['exports'].items())}).encode()))

    verdict = 'OK' if all(r['verdict'] == 'OK' for r in results) else 'REGRESSION'
    return dict(schema_version=SCHEMA, gate=gate, tag=ledger['gates'][gate]['tag'], tag_commit=commit,
                verdict=verdict, ledger_sha256=sha256(FIDELITY.encoded(ledger).encode()),
                tool_sha256=CANDIDATE.file_sha(Path(__file__)),
                before=side(before, before_path, revision), after=side(after, after_path, commit),
                entries=results, seconds=round(time.monotonic() - start, 1))


# ---------------------------------------------------------------- CLI

def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--ledger', type=Path, default=LEDGER)
    parser.add_argument('--repo', type=Path, default=ROOT)
    parser.add_argument('--head', default='HEAD', help='revision for pending gates (Mode A)')
    parser.add_argument('--receipts', type=Path, default=None, help='Mode B receipt directory (Mode A reads it)')
    parser.add_argument('--require-closed', action='append', default=[], metavar='GATE')
    parser.add_argument('--closure', action='store_true', help='Mode B')
    parser.add_argument('--gate')
    parser.add_argument('--entry', action='append', default=[])
    parser.add_argument('--before', type=Path, help='N4 capture snapshot.json of the old revision')
    parser.add_argument('--after', type=Path, help='N4 capture snapshot.json of the tag')
    parser.add_argument('--map', action='append', default=[], type=Path, help='an uncommitted map, bound by sha256')
    parser.add_argument('--plan', type=Path, help='the applied rename plan (one map)')
    parser.add_argument('--reviewed-quotations', type=Path)
    parser.add_argument('--receipt', type=Path, help='Mode B output (default scripts/bridge-ledger-receipts/GATE.json)')
    args = parser.parse_args(argv)
    git = None
    try:
        ledger = json.loads(args.ledger.read_bytes())
        repo = args.repo.resolve()
        git = Git(repo)
        receipts = args.receipts if args.receipts is not None else repo / 'scripts' / 'bridge-ledger-receipts'
        if args.closure:
            if not (args.gate and args.before and args.after):
                raise ValueError('--closure needs --gate, --before and --after')
            result = mode_b(ledger, git, args.gate, args.before, args.after, args.entry, args.map, args.plan,
                            args.reviewed_quotations)
            out = args.receipt or receipts / f'{args.gate}.json'
            out.parent.mkdir(parents=True, exist_ok=True)
            out.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
            print(json.dumps(dict(receipt=str(out), verdict=result['verdict'], seconds=result['seconds'],
                                  entries=[{k: r[k] for k in ('id', 'closure', 'authored', 'generated', 'verdict')}
                                           for r in result['entries']]), indent=2))
            if result['verdict'] != 'OK':
                for row in result['entries']:
                    for line in row['mismatches']:
                        print(f'  [{row["id"]}] {line}', file=sys.stderr)
                print(f'REGRESSION — bridge ledger closure {args.gate}', file=sys.stderr)
                return 1
            print(f'OK — bridge ledger closure {args.gate}: {sum(r["closure"] for r in result["entries"])} '
                  f'closure members compared; before bound {result["before"]["bound"]}, '
                  f'after bound {result["after"]["bound"]}')
            return 0
        result = mode_a(ledger, git, args.head, receipts, args.require_closed)
        for gap in result['gaps']:
            print(f'  gap: {gap}')
        print(f'OK — bridge ledger: {result["entries"]} entries over gates {", ".join(result["gates"])}; '
              f'{len(result["gaps"])} open gaps')
        return 0
    except (Finding, FIDELITY.Mismatch) as error:
        print(f'REGRESSION — bridge ledger: {error}', file=sys.stderr)
        return 1
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'SETUP — bridge ledger: {error}', file=sys.stderr)
        return 2
    finally:
        if git is not None:
            git.close()


if __name__ == '__main__':
    sys.exit(main())
