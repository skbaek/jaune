#!/usr/bin/env python3
"""Kernel preservation across an in-place delete (goal `jaune-shape-and-names-v1`, X1).

After a gate tag, the delete commit removes the old side in place: whole old
modules, and old declarations inside modules that also hold kept ones. Mode B
of the bridge ledger stops at the tag and the next N4 comparison starts after
the delete, so this check covers the commit between them. From two
`naming-candidate.py capture` snapshots (before = the tag, after = the delete
commit) it verifies, with N4's per-constant comparator and no rename map:

1. Kept. Every authored constant of the after capture is an authored constant
   of the before capture, in the same module, with the same kernel type and
   payload (theorem proofs are not exported, as in N4), the same attribute
   record (simp, csimp, inline, reducibility, instance, ...) and equation
   provenance. Compiler-generated constants are matched by graph, not by name
   (a kept declaration that reused a deleted declaration's matcher gets its
   own), each within its module; an on-demand auxiliary (equation lemma,
   splitter, sparse cases) that another module realized before may be
   realized in this one after, and is compared with that copy. Lean sets a
   matcher's reducibility by the visibility of the declaration that first
   made it: a kept declaration whose matcher came from a deleted declaration
   of the other visibility gets one with the other reducibility, which
   needs a `matcher_reducibility` row. Every kept `#guard` (as its
   elaborated expression), checked command and attribute syntax is unchanged.
   A module whose export is byte-identical is taken as unchanged, provided
   every generated constant it names is still that constant after the delete.

2. Deleted. `deleted = before - after` is computed per module: authored
   constants, declarations Lean names itself (anonymous instances) and
   generated constants without a declared parent (derived instances, macro
   auxiliaries). Each must be classified by the committed classification file:
   (a) old-side: it is one of the listed old-side constants or lies in a
       listed old-side namespace, or its kernel type or value reaches one
       through references to deleted constants only (decided from the
       exported kernel terms, never from its own name);
   (b) `replaced`: a row naming its kept counterpart, which must exist after;
   (c) `retired`: a row with a reason.
   A `replaced` or `retired` row with `with_dependents` also covers the deleted
   declarations that reach it. Anything else fails. A generated constant
   that vanishes must belong to a deleted declaration, or be an on-demand
   auxiliary Lean realizes again when needed.

3. Guards. Every deleted `#guard` must appear in the guard ledger (module and
   digest of its elaborated expression in the before capture). A deleted
   checked command or attribute command is accounted for when it names a
   deleted declaration; otherwise it needs a ledger row too. Checks that
   appear only after need an `added` ledger row.

Files (JSON, `schema_version` 1; every row must be used, a stale row fails):
  --classification  {"old_side": {"constants": [...], "namespaces": [...]},
                     "replaced": [{"module", "name", "by", "with_dependents"?}],
                     "retired": [{"module", "name", "reason", "with_dependents"?}],
                     "rewritten": [{"module", "name", "reason"}],
                     "added": [{"module", "name", "reason"}],
                     "matcher_reducibility": [{"module", "name", "after", "reason"}]}
                    `rewritten` lists a kept constant whose value was rewritten
                    (type, kind and attributes must still be equal); `added`
                    lists a declaration that exists only after;
                    `matcher_reducibility` acknowledges a matcher (`name`
                    before, `after` after) whose reducibility follows its new
                    owner's visibility.
  --guard-ledger    {"deleted": [{"module", "kind": "guard"|"check"|"attribute",
                                  "digest", "disposition": "restated"|
                                  "deleted-with-old-side"|"retired",
                                  "replacement" | "reason", "count"?,
                                  "replacement_module"?}],
                     "added": [{"module", "kind", "digest", "reason"}]}
                    `restated` needs `replacement`, the others `reason`; a
                    `replacement_module` must hold guards or checks after.
  --map             an N4 map holding only `public_from` declaration rows with
                    `old == new` (a `private` declaration made public).
  --inventory       `scripts/naming-inventory.json`, as in N4's compare: its
                    registered exclusions (sources outside the exports).

The receipt (`--receipt`) holds the full machine-computed deleted set grouped
by module with each class and its witness, the unclassified declarations and
unledgered checks as rows ready to complete, and the digests of both
snapshots, their exports and every input file.

The verdict needs both captures bound to their revisions (`--before-rev`,
`--after-rev`: the capture's file inventory is the revision's clean tree) and
the input files to be the ones in the after capture. `--allow-unbound` is for
rehearsals while the classification is being written.

Exit 0 iff the verdict is OK; 1 on a finding (REGRESSION); 2 on SETUP.
Read-only: no Lean, no build, no host admission.
"""
import argparse
from collections import Counter, OrderedDict, defaultdict
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
SCHEMA = 1


def load(name):
    spec = importlib.util.spec_from_file_location(name.replace('-', '_'), ROOT / 'scripts' / name)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


LEDGER = load('check-bridge-ledger.py')
CANDIDATE = LEDGER.CANDIDATE
FIDELITY = CANDIDATE.FIDELITY
MAP = FIDELITY.MAP
APPLY = FIDELITY.APPLY

# Auxiliaries Lean derives from their parent whenever a use needs them. One
# that vanishes with its last user, or is realized in another module, is no
# change to any declaration.
ON_DEMAND = re.compile(r'^(eq_\d+|eq_def|else_eq|splitter|congr_simp|congr_eq_\d+|_sparseCasesOn_\d+|_arg_pusher)$')
# Leaves of compiler auxiliaries. One with no named parent belongs to an
# anonymous command (`#guard`, `#eval`, `example`), which the ledger covers.
AUXILIARY = re.compile(r'^(match_\d+(?:_\d+)*|_?proof_\d+(?:_\d+)*|_?simp_\d+(?:_\d+)*|_unsafe_rec|_sunfold|_unfold|'
                       r'_f|_unary|_mutual|_eval(?:_\d+)?|_example|_nativeDecide_\d+(?:_\d+)*)$')
MATCHER = FIDELITY.Comparison.MATCHER_LEAF
SEMIREDUCIBLE, INSTANCE_REDUCIBLE = 'Lean.ReducibilityStatus.semireducible', 'Lean.ReducibilityStatus.instanceReducible'
SECTIONS = ('replaced', 'retired', 'rewritten', 'added', 'matcher_reducibility')
ITEM_KINDS = dict(guards='guard', checks='check', attributes='attribute')
DISPOSITIONS = ('restated', 'deleted-with-old-side', 'retired')
EMPTY_MAP = dict(schema_version=1, retired_tokens=[], allowed_abbreviations=[], entries=[])
EMPTY_CLASSIFICATION = dict(schema_version=SCHEMA, old_side=dict(constants=[], namespaces=[]),
                            replaced=[], retired=[], rewritten=[], added=[], matcher_reducibility=[])
EMPTY_LEDGER = dict(schema_version=SCHEMA, deleted=[], added=[])


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def user_name(name):
    """A compiler name without its `_private.<module>.<n>.` prefix."""
    name = name.rsplit('@', 1)[0]
    if name.startswith('_private.'):
        try:
            private = MAP.split_private(name)
        except ValueError:
            return name
        if private:
            return private[2]
    return name


def components(name):
    return APPLY.split_name(user_name(name))


def on_demand(name):
    return any(ON_DEMAND.match(part) for part in components(name))


# ---------------------------------------------------------------- input files

def _text(row, field, where):
    value = row.get(field)
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f'{where}: missing non-empty {field!r}')
    return value


def validate_classification(data):
    if not isinstance(data, dict) or data.get('schema_version') != SCHEMA:
        raise ValueError('classification: unsupported schema_version')
    unknown = set(data) - {'schema_version', 'old_side', 'notes', *SECTIONS}
    if unknown:
        raise ValueError(f'classification: unknown fields {sorted(unknown)}')
    old = data.get('old_side', {})
    if not isinstance(old, dict) or set(old) - {'constants', 'namespaces'}:
        raise ValueError('classification: old_side holds `constants` and `namespaces`')
    for field in ('constants', 'namespaces'):
        names = old.get(field, [])
        if not isinstance(names, list) or not all(isinstance(n, str) and n.strip() for n in names) \
                or len(set(names)) != len(names):
            raise ValueError(f'classification: old_side.{field} must be a list of distinct names')
    seen = {}
    required = dict(replaced=('by',), retired=('reason',), rewritten=('reason',), added=('reason',),
                    matcher_reducibility=('after', 'reason'))
    for section, fields in required.items():
        rows = data.get(section, [])
        if not isinstance(rows, list):
            raise ValueError(f'classification: {section} must be a list')
        for index, row in enumerate(rows):
            where = f'classification: {section}[{index}]'
            if not isinstance(row, dict):
                raise ValueError(f'{where}: not an object')
            allowed = {'module', 'name', 'note', *fields}
            if section in ('replaced', 'retired'):
                allowed.add('with_dependents')
                if not isinstance(row.get('with_dependents', False), bool):
                    raise ValueError(f'{where}: with_dependents must be a boolean')
            if set(row) - allowed:
                raise ValueError(f'{where}: unknown fields {sorted(set(row) - allowed)}')
            key = (_text(row, 'module', where), _text(row, 'name', where))
            for field in fields:
                _text(row, field, where)
            group = 'deleted' if section in ('replaced', 'retired') else section
            if seen.setdefault((group, key), section) != section or \
                    sum(1 for r in rows if (r.get('module'), r.get('name')) == key) > 1:
                raise ValueError(f'{where}: {key[1]} of {key[0]} is listed twice')
    return data


def validate_ledger(data):
    if not isinstance(data, dict) or data.get('schema_version') != SCHEMA:
        raise ValueError('guard ledger: unsupported schema_version')
    if set(data) - {'schema_version', 'deleted', 'added', 'notes'}:
        raise ValueError('guard ledger: unknown fields')
    for section in ('deleted', 'added'):
        rows = data.get(section, [])
        if not isinstance(rows, list):
            raise ValueError(f'guard ledger: {section} must be a list')
        for index, row in enumerate(rows):
            where = f'guard ledger: {section}[{index}]'
            if not isinstance(row, dict):
                raise ValueError(f'{where}: not an object')
            _text(row, 'module', where)
            if row.get('kind') not in ITEM_KINDS.values():
                raise ValueError(f'{where}: kind must be one of {sorted(ITEM_KINDS.values())}')
            if not re.fullmatch(r'[0-9a-f]{64}', str(row.get('digest'))):
                raise ValueError(f'{where}: digest must be a sha256')
            count = row.get('count', 1)
            if not isinstance(count, int) or isinstance(count, bool) or count < 1:
                raise ValueError(f'{where}: count must be a positive integer')
            if section == 'added':
                _text(row, 'reason', where)
                continue
            if row.get('disposition') not in DISPOSITIONS:
                raise ValueError(f'{where}: disposition must be one of {list(DISPOSITIONS)}')
            _text(row, 'replacement' if row['disposition'] == 'restated' else 'reason', where)
    return data


def validate_visibility_map(mapping):
    """The optional map: `public_from` declaration rows that keep the name."""
    MAP.validate_map(mapping)
    for row in mapping['entries']:
        if row['kind'] != 'declaration' or 'public_from' not in row or row['old'] != row['new']:
            raise ValueError(f'map row {row["old"]} -> {row["new"]}: only a `public_from` declaration row that '
                             'keeps its name is allowed here; renames and relocations are N4 comparisons')
    return mapping


# ---------------------------------------------------------------- one module

def render(item, limit=200):
    """The atoms and names of a syntax item, in order, for a report."""
    words, todo = [], [item]
    while todo and sum(map(len, words)) < limit:
        node = todo.pop()
        if isinstance(node, list):
            if len(node) == 2 and node[0] in ('atom', 'name', 'token') and isinstance(node[1], str):
                words.append(node[1])
            elif len(node) == 4 and node[0] == 'ident' and isinstance(node[1], str):
                words.append(node[1])
            else:
                todo.extend(reversed([n for n in node if isinstance(n, (list, dict))]))
        elif isinstance(node, dict):
            todo.extend(reversed([n for n in node.values() if isinstance(n, (list, dict))]))
    return ' '.join(words)[:limit]


def guard_sites(env, module, count):
    """(line, source) of each guard, when the module's `#guard` commands
    account for exactly its exported guards (in source order); else None."""
    source = (env.get('module_sources') or {}).get(module)
    commands = (env.get('module_commands') or {}).get(module) or []
    if source is None:
        return None
    sites = []
    for start, end in sorted(commands):
        text = source[start:end]
        if re.match(r'(?:set_option\s+\S+\s+\S+\s+in\s+)*#guard(?![\w_])', text):
            sites.append((source.count('\n', 0, start) + 1, ' '.join(text.split())[:240]))
    return sites if len(sites) == count else None


class ModuleCheck(FIDELITY.Comparison):
    """N4's comparator on one module's two exports, driven from the after
    side: every after constant needs its before counterpart; what is left on
    the before side is the module's deleted set."""

    def __init__(self, module, before, after, context):
        external = dict(gen_pairs=context.renamed, referenced_before=context.referenced('before', module, before),
                        referenced_after=context.referenced('after', module, after))
        super().__init__(before, after, context.renamer, collect=True,
                         global_context=context.global_context, external=external)
        self.module, self.context = module, context
        self.found = []
        self._kept_bundles = []
        self._original, self._swapped = {}, set()
        b, a = self.before, self.after
        closure_before = self._substantive_closure(b['constants'], b['roots'], b['guards'], b['attributes'],
                                                   b['checks'], self.externally_referenced_before)
        closure_after = self._substantive_closure(a['constants'], a['roots'], a['guards'], a['attributes'],
                                                  a['checks'], self.externally_referenced_after)
        self.generated_left = (self.left.keys() & closure_before) - b['roots']
        self.generated_right = (self.right.keys() & closure_after) - a['roots']
        self._downstream_reloc_eq_cache = {}
        self._norm_coarse_cache = {}
        self._gen_right_by_parent = defaultdict(list)
        self.declared = {side: set((env.get('module_decls') or {}).get(module) or ()) & env['constants'].keys()
                         for side, env in (('before', b), ('after', a))}
        self.named, self.unnamed = {}, {}
        for side, env in (('before', b), ('after', a)):
            named = env['roots'] | self.declared[side]
            self.named[side] = {user_name(n): n for n in sorted(named)}
            self.unnamed[side] = {user_name(n): n for n in sorted(env['constants'].keys() - named)}
        self.rehome()

    def rehome(self):
        """An on-demand auxiliary this module holds only after, and another
        module held before, is compared with that module's copy."""
        self.rehomed = {}
        for name in sorted(self.generated_right):
            if name in self.left or not on_demand(name):
                continue
            found = self.context.foreign(name, self.module)
            if found is None:
                continue
            holder, bundle = found
            self._kept_bundles.append(bundle)
            self.left[name] = bundle['constants'][name]
            self.generated_left.add(name)
            self._special_left |= set(bundle.get('_special_ids') or ())
            self.rehomed[name] = holder

    def pair(self, a, b):
        """Lean makes a private declaration's matcher semireducible and a
        public one's instance-reducible. Across that one difference the pair
        is compared with the after reducibility, and recorded."""
        if a in self.generated_left and MATCHER.match(components(a)[-1]):
            original = self._original.setdefault(a, self.left[a])
            right = self.right.get(b)
            self.left[a] = original
            if right is not None and MATCHER.match(components(b)[-1]):
                expected = {True: SEMIREDUCIBLE, False: INSTANCE_REDUCIBLE}
                private = a.startswith('_private.'), b.startswith('_private.')
                was = (original.get('attributes') or {}).get('reducibility')
                now = (right.get('attributes') or {}).get('reducibility')
                if private[0] != private[1] and (was, now) == (expected[private[0]], expected[private[1]]):
                    self.left[a] = dict(original, attributes=dict(original['attributes'], reducibility=now))
                    self._swapped.add((a, b))
        super().pair(a, b)

    def other_visibility(self, name):
        """The graph key of an after matcher as the other visibility has it."""
        record = self.right[name]
        now = (record.get('attributes') or {}).get('reducibility')
        if not MATCHER.match(components(name)[-1]) or now not in (SEMIREDUCIBLE, INSTANCE_REDUCIBLE):
            return None
        coarse = self.normalize(record, 'after', True)
        other = SEMIREDUCIBLE if now == INSTANCE_REDUCIBLE else INSTANCE_REDUCIBLE
        return FIDELITY.dag_digest(dict(coarse, attributes=dict(coarse['attributes'], reducibility=other)))

    def head(self, name, side):
        """The declaration a generated constant belongs to: ('named', full
        name) for an authored or declared constant of this module, ('global',
        user name) for an authored constant of another module, ('generated',
        full name) for the outermost generated constant that prefixes it."""
        parts = components(name)
        top = None
        for i in range(len(parts) - 1, 0, -1):
            prefix = '.'.join(parts[:i])
            if prefix in self.named[side]:
                return 'named', self.named[side][prefix]
            if prefix in self.context.root_users[side]:
                return 'global', prefix
            if prefix in self.unnamed[side]:
                top = self.unnamed[side][prefix]
        return ('generated', top) if top is not None else None

    def pair_rewritten(self, a, b):
        """A listed rewrite: the value is exempt; the kind, type, universe
        parameters, attributes and equation provenance are compared."""
        left, right = self.left[a], self.right[b]
        self.pairs[a], self.reverse[b] = b, a
        self.checked.add((a, b))

        def shell(record):
            kernel = record.get('kernel')
            if not isinstance(kernel, dict) or not isinstance(kernel.get('payload'), list):
                raise FIDELITY.Mismatch('unsupported kernel record')
            return dict(record, kernel=dict({k: v for k, v in kernel.items() if k != 'payload'},
                                            kind=kernel['payload'][0]))
        self.holders.append(a)
        self.holder_pairs.append((a, b))
        try:
            self.compare(shell(left), shell(right), f'constant {a}')
        finally:
            self.holder_pairs.pop()
            self.holders.pop()

    def run(self, rows):
        module, b, a = self.module, self.before, self.after
        rewritten = {name for (mod, name) in rows.rewritten if mod == module}
        kept, deleted, images = [], [], {}
        for name in sorted(b['roots']):
            target = self.name(name)
            if target in a['roots']:
                kept.append((name, target))
                images[target] = name
            else:
                deleted.append(name)
        added = sorted(a['roots'] - images.keys())
        used_rewritten = set()
        for name in sorted(rewritten):
            target = self.name(name) if name in self.left else name
            if name not in self.left or target not in self.right:
                continue  # Reported as a stale row.
            used_rewritten.add(name)
            rows.use('rewritten', module, name)
            try:
                self.pair_rewritten(name, target)
            except (FIDELITY.Mismatch, KeyError) as error:
                self.found.append(f'rewritten constant {name}: {error}')
        for name, target in kept:
            if name in used_rewritten:
                continue
            try:
                self.pair(name, target)
            except (FIDELITY.Mismatch, KeyError) as error:
                self.found.append(f'kept constant {name} changed: {error}')

        # After side: every generated constant needs a before counterpart,
        # the same name first, then any unpaired one with the same graph.
        preferred = {}
        for name in sorted(self.generated_left):
            preferred.setdefault(self.preferred_generated(name), name)
        buckets = None
        unmatched_after = []
        for name in sorted(self.generated_right):
            if name in self.reverse or name in self.aux_right:
                continue
            candidates = []
            same = preferred.get(name)
            if same is not None and same not in self.pairs:
                candidates.append(same)
            if buckets is None:
                buckets = defaultdict(list)
                for left in sorted(self.generated_left):
                    if left not in self.pairs:
                        try:
                            buckets[self.coarse_record(left, 'before')].append(left)
                        except FIDELITY.Mismatch:
                            pass
            try:
                keys = [self.coarse_record(name, 'after'), self.other_visibility(name)]
                candidates += [n for key in keys if key is not None for n in buckets[key]
                               if n != same and n not in self.pairs]
            except FIDELITY.Mismatch:
                pass
            for candidate in candidates:
                saved = self.save()
                try:
                    self.pair(candidate, name)
                    break
                except (FIDELITY.Mismatch, KeyError):
                    self.restore(saved)
            else:
                unmatched_after.append(name)

        added_heads = set()
        for name in added:
            if rows.use('added', module, name):
                added_heads.add(name)
            else:
                self.found.append(f'authored constant {name} exists only after the delete')
        for name in unmatched_after:
            if rows.use('added', module, name):
                added_heads.add(name)
                continue
            head = self.head(name, 'after')
            if head and head[0] == 'named' and (head[1] in added_heads or images.get(head[1]) in used_rewritten
                                                or self.reverse.get(head[1]) in used_rewritten):
                continue
            if head and head[0] == 'generated' and head[1] in added_heads:
                continue
            self.found.append(f'generated constant {name} has no counterpart before the delete')

        acknowledge = []
        for left, right in sorted(self._swapped):
            if self.pairs.get(left) != right:
                continue
            row = rows.use('matcher_reducibility', module, left)
            if row is None or row['after'] != right:
                acknowledge.append(dict(module=module, name=left, after=right, reason=''))
                self.found.append(f'matcher {left} is {right} after the delete, with the reducibility of its new '
                                  'owner\'s visibility; this needs a matcher_reducibility row')

        # Before side: what is unpaired vanished with the delete.
        vanishing = [n for n in self.generated_left
                     if n not in self.pairs and n not in self.aux_left and n not in self.rehomed]
        vanishing.sort(key=lambda n: (len(components(n)), n))
        vanished = set(vanishing)
        heads = {name: 'authored' for name in deleted}
        attached, realized, anonymous = {}, set(), set()
        deleted_users = self.context.deleted_users
        for name in vanishing:
            if name in self.declared['before']:
                heads[name] = 'declared'
                continue
            head = self.head(name, 'before')
            if head is None:
                if on_demand(name):
                    realized.add(name)
                elif AUXILIARY.match(components(name)[-1]):
                    anonymous.add(name)
                else:
                    heads[name] = 'generated'
                continue
            kind, parent = head
            if kind == 'global':
                gone = parent in deleted_users
            elif parent in heads:
                gone = True
            elif parent in used_rewritten:
                continue
            elif parent in anonymous:
                anonymous.add(name)
                continue
            elif parent in realized:
                realized.add(name)
                continue
            else:
                gone = False
            if gone:
                attached[name] = parent
            elif on_demand(name):
                realized.add(name)
            else:
                self.found.append(f'generated constant {name} of kept declaration {parent} disappeared')

        # Kernel references of each deleted declaration, through the generated
        # constants that vanish with it (a theorem exports its type only).
        refs_of = {}

        def references(name):
            if name not in refs_of:
                refs_of[name] = FIDELITY.collect_const_refs(self.left[name], set(), set())
            return refs_of[name]

        entries = []
        decls = (b.get('module_decls') or {}).get(module) or {}
        source = (b.get('module_sources') or {}).get(module)
        for name in sorted(heads):
            seen, todo, reached = {name}, [name], set()
            while todo:
                for ref in references(todo.pop()):
                    if ref in seen:
                        continue
                    seen.add(ref)
                    if ref in vanished and ref not in heads:
                        todo.append(ref)
                    else:
                        reached.add(ref)
            record = self.left[name]
            payload = record['kernel'].get('payload') if isinstance(record.get('kernel'), dict) else None
            kind = payload[0] if isinstance(payload, list) and payload else 'unknown'
            if (record.get('attributes') or {}).get('instance') is not None:
                kind += ' (instance)'
            line = source.count('\n', 0, decls[name][0]) + 1 if source is not None and name in decls else None
            entries.append(dict(module=module, name=name, origin=heads[name], kind=kind, line=line, refs=reached,
                                generated=sum(1 for parent in attached.values() if parent == name)))

        items = {}
        gone_names = set(heads) | vanished
        for key in FIDELITY.ITEMS:
            items[key] = self.items(key, gone_names)
        renamed = {x: y for x, y in self.pairs.items() if x in self.generated_left and x != y}
        return dict(kept=len(kept), entries=entries, attached=attached, problems=self.found, items=items,
                    renamed=renamed, rehomed=dict(self.rehomed), realized=sorted(realized), acknowledge=acknowledge,
                    anonymous=sorted(anonymous), generated_kept=len(self.generated_right))

    def items(self, key, gone_names):
        """Guards, checked commands or attribute syntax: the after multiset
        must be the before one minus deletions (compared as N4 compares them)."""
        before, after = self.before.get(key) or [], self.after.get(key) or []
        available = defaultdict(list)
        for index, item in enumerate(after):
            try:
                available[FIDELITY.dag_digest(self.normalize(item, 'after'))].append(index)
            except FIDELITY.Mismatch as error:
                self.found.append(f'{key}[after {index}]: {error}')
        sites = guard_sites(self.before, self.module, len(before)) if key == 'guards' else None
        deleted, kept = [], 0
        for index, item in enumerate(before):
            try:
                digest = FIDELITY.dag_digest(self.normalize(item, 'before'))
            except FIDELITY.Mismatch as error:
                self.found.append(f'{key}[before {index}]: {error}')
                continue
            if available.get(digest):
                available[digest].pop(0)
                kept += 1
                continue
            row = dict(module=self.module, kind=ITEM_KINDS[key], digest=FIDELITY.dag_digest(item))
            if sites is not None:
                row['line'], row['source'] = sites[index]
            elif key != 'guards':
                row['source'] = render(item)
            if key != 'guards':
                refs = FIDELITY.collect_const_refs(item, set(), set())
                targets = sorted(r for r in refs if r in gone_names or user_name(r) in self.context.deleted_users)
                if targets:
                    row['deleted_targets'] = targets[:8]
            deleted.append(row)
        extra = []
        for index in sorted(i for rest in available.values() for i in rest):
            row = dict(module=self.module, kind=ITEM_KINDS[key], digest=FIDELITY.dag_digest(after[index]))
            if key != 'guards':
                row['source'] = render(after[index])
            extra.append(row)
        return dict(kept=kept, deleted=deleted, added=extra)


# ---------------------------------------------------------------- whole tree

class Rows:
    """The classification rows, each of which must be used."""

    def __init__(self, classification):
        self.data = classification
        self.tables = {section: {(r['module'], r['name']): r for r in classification.get(section, [])}
                       for section in SECTIONS}
        self.rewritten = self.tables['rewritten']
        self.used = set()

    def use(self, section, module, name):
        row = self.tables[section].get((module, name))
        if row is not None:
            self.used.add((section, module, name))
        return row

    def stale(self):
        return sorted((section, module, name) for section, table in self.tables.items()
                      for module, name in table if (section, module, name) not in self.used)


def global_tables(selected, metas):
    """Whole-capture tables from the per-module metadata, keyed as N4 keys
    them: a name authored in two independent modules also has a
    `name@module` key per module. Returns the authored names, all names,
    each name's first holder, its holders, and who refers to it."""
    occurrences, referrers = {}, {}
    for module in sorted(selected):
        meta = metas[module]
        roots = set(meta['authored_roots'])
        for name in meta['all_constants']:
            occurrences.setdefault(name, []).append((module, name in roots))
        for name in meta['kernel_referenced_constants']:
            referrers.setdefault(name, set()).add(module)
    all_roots, all_names, owners, holders = set(), set(), {}, {}
    for name, rows in occurrences.items():
        all_names.add(name)
        if len(rows) == 1 or not any(root for _, root in rows):
            owners[name] = rows[0][0]
            holders[name] = {module for module, _ in rows}
            if rows[0][1]:
                all_roots.add(name)
            continue
        all_roots.add(name)
        holders[name] = {module for module, _ in rows}
        for module, root in rows:
            key = f'{name}@{module}'
            all_names.add(key)
            owners[key] = module
            holders[key] = {module}
            if root:
                all_roots.add(key)
    return all_roots, all_names, owners, holders, referrers


class Context:
    def __init__(self, before, after, renamer, metas):
        self.snapshots = dict(before=before, after=after)
        self.renamer, self.metas = renamer, metas
        sides = {side: global_tables(snap['selected'], metas[side]) for side, snap in self.snapshots.items()}
        (b_roots, b_all, b_owners, b_holders, b_refs), (a_roots, a_all, a_owners, a_holders, a_refs) = \
            sides['before'], sides['after']
        self.global_context = dict(before_roots=b_roots, after_roots=a_roots, before_constants=b_all,
                                   after_constants=a_all, before_owners=b_owners, after_owners=a_owners,
                                   before_holders=b_holders, after_holders=a_holders)
        self.referenced_by = dict(before=b_refs, after=a_refs)
        self.holders = b_holders
        self.root_users = dict(before={user_name(n) for n in b_roots}, after={user_name(n) for n in a_roots})
        self.after_users = {user_name(n) for n in a_all} | set(a_all)
        after_names = {n.rsplit('@', 1)[0] for n in a_roots}
        self.deleted_users = {user_name(n) for n in b_roots
                              if renamer(n.rsplit('@', 1)[0]) not in after_names} - self.root_users['after']
        self.renamed = {}
        self._bundles = OrderedDict()
        self._closures = {}

    def referenced(self, side, module, env):
        table = self.referenced_by[side]
        return {name for name in env['constants'] if table.get(name, set()) - {module}}

    def bundle(self, side, module):
        key = (side, module)
        if key in self._bundles:
            self._bundles.move_to_end(key)
            return self._bundles[key]
        data = FIDELITY.read_exports([self.snapshots[side]['export_paths'][module]])
        self._bundles[key] = data
        while len(self._bundles) > 6:
            self._bundles.popitem(last=False)
        return data

    def environment(self, side, module):
        if module not in self.snapshots[side]['export_paths']:
            env = CANDIDATE.empty_environment()
            env['version'] = None
            return env
        return CANDIDATE.union_environment({module: self.bundle(side, module)})

    def foreign(self, name, module):
        """A before copy of `name` in another module: one this module
        imported before, if any."""
        holders = sorted(m for m in self.holders.get(name, ()) if m != module)
        if not holders:
            return None
        graph = self.snapshots['before']['candidate']['modules']
        if module in graph:
            if module not in self._closures:
                self._closures = {module: set(CANDIDATE.closure(graph, [module]))}
            imported = [m for m in holders if m in self._closures[module]]
            holders = imported or holders
        return holders[0], self.bundle('before', holders[0])


def classify(entries, attached, classification, rows, after_users, problems):
    """Class and witness of every deleted declaration; unclassified ones fail."""
    by_name = defaultdict(list)
    for entry in entries:
        by_name[entry['name']].append(entry)
    old = classification.get('old_side', {})
    constants, namespaces = set(old.get('constants', [])), list(old.get('namespaces', []))
    anchors, hit = {}, set()
    for name in by_name:
        user = user_name(name)
        if name in constants or user in constants:
            anchors[name] = name if name in constants else user
            hit.add(anchors[name])
        else:
            for space in namespaces:
                if user == space or user.startswith(space + '.'):
                    anchors[name] = space + '.*'
                    hit.add(space)
                    break
    for name in sorted(constants - hit):
        where = 'still exists after the delete' if name in after_users else 'is not a deleted declaration'
        problems.append(f'classification: old-side constant {name} {where}')
    for space in sorted(set(namespaces) - hit):
        problems.append(f'classification: old-side namespace {space} holds no deleted declaration')
    for name in sorted(constants & hit):
        if name in after_users:
            problems.append(f'classification: old-side constant {name} still exists after the delete')
    dependents = defaultdict(set)
    for entry in entries:
        for ref in entry['refs']:
            target = attached.get(ref, ref)
            if target in by_name and target != entry['name']:
                dependents[target].add(entry['name'])

    def reach(seeds):
        via, todo = {name: None for name in seeds}, sorted(seeds)
        while todo:
            current = todo.pop(0)
            for name in sorted(dependents[current]):
                if name not in via:
                    via[name] = current
                    todo.append(name)
        return via

    def chain(via, name):
        path = [name]
        while via[path[-1]] is not None and len(path) < 12:
            path.append(via[path[-1]])
        return path[1:]
    old_side = reach(anchors)
    covering = {}
    for section in ('replaced', 'retired'):
        for (module, name), row in rows.tables[section].items():
            if row.get('with_dependents') and name in by_name and any(e['module'] == module for e in by_name[name]):
                covering[name] = section
    inherited = reach(covering)
    counts = Counter()
    for entry in entries:
        name, module = entry['name'], entry['module']
        for section in ('replaced', 'retired'):
            row = rows.use(section, module, name)
            if row is not None:
                entry['class'] = section
                entry['row'] = {k: v for k, v in row.items() if k not in ('module', 'name')}
                if section == 'replaced' and row['by'] not in after_users:
                    problems.append(f'classification: {name} of {module} is replaced by {row["by"]}, '
                                    'which does not exist after the delete')
                break
        else:
            if name in anchors:
                entry['class'], entry['via'] = 'old-side', [f'listed: {anchors[name]}']
            elif name in old_side:
                path = chain(old_side, name)
                entry['class'], entry['via'] = 'old-side', path + [f'listed: {anchors[path[-1]]}']
            elif inherited.get(name) is not None:
                path = chain(inherited, name)
                entry['class'], entry['via'] = f'{covering[path[-1]]} (dependent)', path
            else:
                entry['class'] = None
        counts[entry['class'] or 'unclassified'] += 1
    return counts


def preconditions(before, after, inventory):
    """N4's capture preconditions, for a delete: the same layout,
    configuration and capture tools; every changed or deleted Lean source and
    every importer of one is exported (or a registered exclusion); the
    external artifacts both captures import are identical (a delete may
    import fewer)."""
    left, right = before['candidate'], after['candidate']
    if left['source_dirs'] != right['source_dirs']:
        raise ValueError('module source layout changed between captures')
    for config in CANDIDATE.CONFIG:
        if left['files'].get(config) != right['files'].get(config):
            raise ValueError(f'build/dependency configuration changed: {config}')
    if before['tool_sources'] != after['tool_sources']:
        raise ValueError('capture implementation changed between captures')
    covered = {row['path'] for side in (before, after) for m, row in side['candidate']['modules'].items()
               if m in side['selected']}
    changed = {path for path in left['files'].keys() | right['files'].keys()
               if path.endswith('.lean') and left['files'].get(path) != right['files'].get(path)}
    if changed - covered:
        raise ValueError(f'changed Lean sources outside exports: {sorted(changed - covered)}')
    excluded = set()
    if inventory is not None:
        raw, rows = inventory
        for side in (left, right):
            if side['files'].get('scripts/naming-inventory.json') != sha256(raw):
                raise ValueError('naming inventory differs from a candidate\'s registered inventory')
        for row in rows['excluded_sources']:
            if left['files'].get(row['path']) == right['files'].get(row['path']) == row['sha256']:
                excluded |= {m for m, r in left['modules'].items() if r['path'] == row['path']}
    affected = CANDIDATE.affected_modules(left['modules'], right['modules'])
    for side in (before, after):
        missing = (affected & side['candidate']['modules'].keys()) - set(side['selected']) - excluded
        if missing:
            raise ValueError(f'affected importers outside exports: {sorted(missing)}')
    external = [{name: CANDIDATE.artifact_identity(parts) for name, parts in side['artifacts'].items()
                 if name not in side['candidate']['modules']} for side in (before, after)]
    differing = sorted(n for n in external[0].keys() & external[1].keys() if external[0][n] != external[1][n])
    if differing:
        raise ValueError(f'external import artifacts changed: {differing[:8]}')
    stale = sorted(n for n in external[1] if n in left['modules'])
    if stale:
        raise ValueError(f'the after capture imports artifacts of modules without a source: {stale[:8]}')
    only_before, only_after = set(before.get('source_only', [])), set(after.get('source_only', []))
    if only_after - only_before or {m for m in only_before - only_after if m in right['modules']}:
        raise ValueError('source-only root classification changed between captures')
    return dict(only_before=len(external[0].keys() - external[1].keys()),
                only_after=sorted(external[1].keys() - external[0].keys()))


def check(before, after, classification=None, ledger=None, mapping=None, fast_path=True, inventory=None):
    """`before`/`after`: `naming-candidate.read_snapshot(path, light=True)`;
    `inventory`: (bytes, parsed) of the registered naming inventory, as in N4."""
    start = time.monotonic()
    classification = validate_classification(classification or EMPTY_CLASSIFICATION)
    ledger = validate_ledger(ledger or EMPTY_LEDGER)
    mapping = validate_visibility_map(mapping or EMPTY_MAP)
    external = preconditions(before, after, inventory)
    renamer = MAP.Renamer(mapping['entries'])
    metas = {}
    for side, snap in (('before', before), ('after', after)):
        metas[side] = dict(snap.get('metas') or {})
        for module in snap['selected']:
            if metas[side].get(module) is None:
                metas[side][module] = FIDELITY.extract_module_meta(snap['export_paths'][module])
    versions = {meta['lean_version'] for side in metas.values() for meta in side.values()}
    if len(versions) > 1:
        raise ValueError('Lean versions differ')
    context = Context(before, after, renamer, metas)
    rows = Rows(classification)
    b_set, a_set = set(before['selected']), set(after['selected'])
    identical = {m for m in b_set & a_set
                 if fast_path and before['exports'][m]['sha256'] == after['exports'][m]['sha256']}
    for module in sorted((b_set & a_set) - identical):
        modes = [bool(metas[side][module].get('from_olean', False)) for side in ('before', 'after')]
        if modes[0] != modes[1]:
            raise ValueError(f'export mode mismatch for {module} (from_olean={modes[0]} vs {modes[1]}); '
                             'recapture the --from-olean side with --full-elab-module')
    order = [m for m in after['selected'] if m not in identical] + [m for m in before['selected'] if m not in a_set]
    problems, entries, attached, modules = [], [], {}, {}
    item_rows = dict(deleted=[], added=[])
    totals = Counter(kept_authored=sum(len(metas['after'][m]['authored_roots']) for m in identical),
                     kept_guards=sum(metas['after'][m]['guard_count'] for m in identical),
                     kept_checks=sum(metas['after'][m]['check_count'] for m in identical),
                     kept_attribute_syntax=sum(metas['after'][m]['attr_count'] for m in identical))
    import_changes, rehomed, renamed, acknowledge = {}, {}, {}, []
    for module in order:
        checker = ModuleCheck(module, context.environment('before', module),
                              context.environment('after', module), context)
        result = checker.run(rows)
        problems += [f'[{module}] {line}' for line in result['problems']]
        entries += result['entries']
        attached.update(result['attached'])
        context.renamed.update(result['renamed'])
        renamed.update(result['renamed'])
        acknowledge += result['acknowledge']
        rehomed.update({name: dict(module=module, before_module=holder) for name, holder in result['rehomed'].items()})
        totals['kept_authored'] += result['kept']
        for key, label in (('guards', 'kept_guards'), ('checks', 'kept_checks'),
                           ('attributes', 'kept_attribute_syntax')):
            totals[label] += result['items'][key]['kept']
            item_rows['deleted'] += result['items'][key]['deleted']
            item_rows['added'] += result['items'][key]['added']
        totals['vanished_generated'] += len(result['attached'])
        totals['vanished_on_demand'] += len(result['realized'])
        totals['vanished_anonymous'] += len(result['anonymous'])
        modules[module] = dict(status='deleted' if module not in a_set else 'added' if module not in b_set
                               else 'compared', kept_authored=result['kept'], deleted=len(result['entries']),
                               vanished_generated=len(result['attached']),
                               vanished_on_demand=len(result['realized']),
                               vanished_anonymous=len(result['anonymous']))
        if module in b_set and module in a_set:
            left = before['candidate']['modules'][module]['imports']
            right = after['candidate']['modules'][module]['imports']
            if left != right:
                import_changes[module] = dict(removed=sorted(set(left) - set(right)),
                                              added=sorted(set(right) - set(left)))
        del checker, result
    # A byte-identical export names its references; a generated constant it
    # names must still be the same constant.
    for module in sorted(identical):
        for name in metas['before'][module]['kernel_referenced_constants']:
            if name in renamed:
                problems.append(f'[{module}] unchanged export names generated constant {name}, '
                                f'which is {renamed[name]} after the delete')

    counts = classify(entries, attached, classification, rows, context.after_users, problems)
    unclassified = [dict(module=e['module'], name=e['name'], kind=e['kind'], line=e['line'], reason='')
                    for e in entries if e['class'] is None]
    for row in unclassified:
        problems.append(f'[{row["module"]}] deleted {row["kind"]} {row["name"]} is unclassified')
    for section, module, name in rows.stale():
        problems.append(f'classification: stale {section} row {name} of {module}')

    # The guard ledger: every deleted guard, every deleted check or attribute
    # command that names no deleted declaration, and every added one.
    unledgered = dict(deleted=[], added=[])
    accounted = Counter()
    for section in ('deleted', 'added'):
        budget = Counter()
        for row in ledger.get(section, []):
            budget[row['module'], row['kind'], row['digest']] += row.get('count', 1)
        for row in item_rows[section]:
            key = (row['module'], row['kind'], row['digest'])
            if section == 'deleted' and row['kind'] != 'guard' and row.get('deleted_targets'):
                accounted[row['kind']] += 1
                row['accounted'] = 'names a deleted declaration'
            elif budget[key] > 0:
                budget[key] -= 1
                row['accounted'] = 'ledger'
                totals[f'ledgered_{section}_{row["kind"]}s'] += 1
            else:
                unledgered[section].append(row)
                what = 'deleted' if section == 'deleted' else 'added (or changed)'
                problems.append(f'[{row["module"]}] {what} {row["kind"]} {row["digest"][:16]} is not in the guard '
                                f'ledger' + (f': {row["source"]}' if row.get('source') else ''))
        for (module, kind, digest), left in sorted(budget.items()):
            if left > 0:
                problems.append(f'guard ledger: stale {section} row ({left}x) {kind} {digest[:16]} of {module}')
    for row in ledger.get('deleted', []):
        target = row.get('replacement_module')
        if target is not None and (target not in a_set or metas['after'][target]['guard_count'] +
                                   metas['after'][target]['check_count'] == 0):
            problems.append(f'guard ledger: replacement module {target} holds no guard or check after the delete')

    deleted = defaultdict(list)
    for entry in entries:
        deleted[entry['module']].append({k: v for k, v in entry.items() if k not in ('refs', 'module')})
    return dict(
        schema_version=SCHEMA, verdict='REGRESSION' if problems else 'OK', problems=problems,
        before_candidate=before['candidate']['head'], after_candidate=after['candidate']['head'],
        modules=dict(before=len(b_set), after=len(a_set), identical_exports=len(identical),
                     compared=len((b_set & a_set) - identical), deleted=sorted(b_set - a_set),
                     added=sorted(a_set - b_set)),
        totals=dict(sorted(totals.items())), deleted_declarations=len(entries),
        classes=dict(sorted(counts.items())), deleted=dict(sorted(deleted.items())),
        unclassified=unclassified, unacknowledged_matcher_reducibility=acknowledge,
        deleted_checks=item_rows['deleted'], added_checks=item_rows['added'],
        deleted_checks_naming_deleted_declarations=dict(accounted), unledgered=unledgered,
        rehomed_generated=rehomed, renamed_generated=renamed, import_changes=import_changes,
        external_artifacts=external,
        compared_modules=modules, seconds=round(time.monotonic() - start, 1))


# ---------------------------------------------------------------- CLI

def side_receipt(git, snapshot, path, revision):
    return dict(head=snapshot['candidate']['head'], revision=revision,
                bound=bool(revision) and LEDGER.bound(git, snapshot, git.commit(revision)),
                snapshot_sha256=CANDIDATE.file_sha(path),
                inventory_sha256=sha256(FIDELITY.encoded(snapshot['candidate']).encode()),
                exports_sha256=sha256(FIDELITY.encoded(
                    {m: r['sha256'] for m, r in sorted(snapshot['exports'].items())}).encode()))


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument('--before', type=Path, required=True, help='capture snapshot.json of the tag')
    parser.add_argument('--after', type=Path, required=True, help='capture snapshot.json of the delete commit')
    parser.add_argument('--classification', type=Path, help='committed classification of the deleted declarations')
    parser.add_argument('--guard-ledger', type=Path, help='committed ledger of deleted and added checks')
    parser.add_argument('--map', type=Path, help='N4 map of `public_from` rows (a private declaration made public)')
    parser.add_argument('--inventory', type=Path,
                        help='scripts/naming-inventory.json of both candidates: registered exclusions (as in N4)')
    parser.add_argument('--repo', type=Path, default=ROOT)
    parser.add_argument('--before-rev', help='revision the before capture must be the clean tree of')
    parser.add_argument('--after-rev', help='revision the after capture must be the clean tree of')
    parser.add_argument('--allow-unbound', action='store_true',
                        help='a rehearsal: do not require the revisions, nor the input files in the after capture')
    parser.add_argument('--receipt', type=Path, help='write the full result here')
    parser.add_argument('--compare-identical', action='store_true',
                        help='also run the comparator on modules whose exports are byte-identical (a self-check)')
    parser.add_argument('--max-problems', type=int, default=60, help='problems printed (the receipt holds all)')
    args = parser.parse_args(argv)
    git = None
    try:
        if not args.allow_unbound and not (args.before_rev and args.after_rev):
            raise ValueError('pass --before-rev and --after-rev (or --allow-unbound for a rehearsal)')
        inputs = {}
        for label, path, default in (('classification', args.classification, EMPTY_CLASSIFICATION),
                                     ('guard_ledger', args.guard_ledger, EMPTY_LEDGER), ('map', args.map, EMPTY_MAP)):
            raw = path.read_bytes() if path else None
            inputs[label] = (json.loads(raw) if raw is not None else default, sha256(raw) if raw is not None else None)
        before = CANDIDATE.read_snapshot(args.before, light=True)
        after = CANDIDATE.read_snapshot(args.after, light=True)
        inventory = None
        if args.inventory:
            raw = args.inventory.read_bytes()
            inventory = (raw, json.loads(raw))
        result = check(before, after, inputs['classification'][0], inputs['guard_ledger'][0], inputs['map'][0],
                       fast_path=not args.compare_identical, inventory=inventory)
        git = LEDGER.Git(args.repo.resolve())
        result['before'] = side_receipt(git, before, args.before, args.before_rev)
        result['after'] = side_receipt(git, after, args.after, args.after_rev)
        for label, revision in (('before', args.before_rev), ('after', args.after_rev)):
            if revision and not result[label]['bound']:
                result['problems'].append(f'the {label} capture is not the clean tree of {revision}')
                result['verdict'] = 'REGRESSION'
        repo = args.repo.resolve()
        for label, path in (('classification', args.classification), ('guard_ledger', args.guard_ledger),
                            ('map', args.map)):
            if path is None or args.allow_unbound:
                continue
            located = path.resolve()
            relative = str(located.relative_to(repo)) if located.is_relative_to(repo) else None
            if after['candidate']['files'].get(relative) != inputs[label][1]:
                result['problems'].append(f'{path} is not a file of the after capture with these bytes')
                result['verdict'] = 'REGRESSION'
        result['unbound_rehearsal'] = bool(args.allow_unbound)
        result.update({f'{label}_sha256': digest for label, (_, digest) in inputs.items()})
        result['tool_sha256'] = CANDIDATE.file_sha(Path(__file__))
        if args.receipt:
            args.receipt.parent.mkdir(parents=True, exist_ok=True)
            args.receipt.write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
        summary = {k: result[k] for k in ('verdict', 'modules', 'totals', 'deleted_declarations', 'classes', 'seconds')}
        summary['modules'] = dict(summary['modules'], deleted=len(summary['modules']['deleted']),
                                  added=len(summary['modules']['added']))
        summary.update(unclassified=len(result['unclassified']), receipt=str(args.receipt) if args.receipt else None,
                       unledgered={k: len(v) for k, v in result['unledgered'].items()},
                       before_bound=result['before']['bound'], after_bound=result['after']['bound'])
        print(json.dumps(summary, indent=2))
        if result['verdict'] != 'OK':
            for line in result['problems'][:args.max_problems]:
                print(f'  {line}', file=sys.stderr)
            if len(result['problems']) > args.max_problems:
                print(f'  ... {len(result["problems"]) - args.max_problems} more (see the receipt)', file=sys.stderr)
            print(f'REGRESSION — delete preservation: {len(result["problems"])} finding(s)', file=sys.stderr)
            return 1
        totals = result['totals']
        if args.allow_unbound:
            print('REHEARSAL (--allow-unbound): not a gate verdict')
        print(f'OK — delete preservation: {totals.get("kept_authored", 0)} kept authored constants and '
              f'{totals.get("kept_guards", 0)} kept guards unchanged; {result["deleted_declarations"]} deleted '
              f'declarations classified; before bound {result["before"]["bound"]}, '
              f'after bound {result["after"]["bound"]}')
        return 0
    except FIDELITY.Mismatch as error:
        print(f'REGRESSION — delete preservation: {error}', file=sys.stderr)
        return 1
    except (OSError, ValueError, KeyError, TypeError) as error:
        print(f'SETUP — delete preservation: {error}', file=sys.stderr)
        return 2
    finally:
        if git is not None:
            git.close()


if __name__ == '__main__':
    sys.exit(main())
