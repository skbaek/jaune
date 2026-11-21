#!/usr/bin/env python3
"""Check compiler-indexed names against retired tokens, retired names and a reviewed policy.

This checker does not infer that an abbreviation is English or that a citation
is authoritative. Its word vocabulary and exact source bindings are explicit
review inputs. Optional policy.derived rows map each final name to its exact
old name and a directly bound base. The base and derived rename must agree on
their source citation, primary rule, and changed component. Other name parts
still require ordinary words or source evidence. Bundles must be freshly
exported against current imports.

Rule 7 builds a theorem's name from the definitions its statement uses. A
theorem or proof constructor may therefore spell, at camel/snake token
boundaries, the final component of a Lean core, Std, Batteries or Mathlib
constant that its kernel statement references (`le` for `LE.le`, `getElem?`
for `GetElem?.getElem?`, `nat` for `Nat`). It may also use, as a whole snake
component, a Lean naming-convention keyword (`refl`, `trans`, `congr`, ...)
whose pinned source is registered in the policy and spells it. A punctuated
final component of a referenced Jaune constant (`take?`) keeps its punctuation
and is linted as words. Each further Lean convention below is active only
when its pinned source is registered: `ge`/`gt` for a swapped `≤`/`<`,
`concat` for `l ++ [a]`, `mk` for a constructor or a definition building its
own namespace's type, `val` for a structure projection, and a definition an
instance passes as the method named after a Lean class (`U256.neg` in
`⟨U256.neg⟩ : Neg U256`). A proposition's definition is named from its body,
and a Jaune namespace may mirror the namespace of a Lean constant its
declaration's statement uses (`Jaune.Std.TreeMap`).

A source binding may state how its registered spelling relates to the Lean
name: `segments` splits a run-together source compound into registered words,
`namespace_prefix` names a source prefix that the enclosing namespace replaces,
`component` names the one token-bounded part of the final segment the source
spells, and a hyphen in a spelling separates words. A derived row may cite
several `bases` in place of one `base`: each is a directly bound name whose
own rename the map row cites and whose old and new spellings occur in the old
and new names. Every rule 1-3 the row lists then needs a base of that rule.

Word splitting follows Lean's spelling conventions. A one-token all-capitals
abbreviation (`IO`) may run into a following capital (`toIOU256`), and such a
run is split only at that abbreviation. A leading all-capitals abbreviation is
lowered by lowerCamel (`bpo1Rules`, `g1MsmLengthPerPair`). The plural `s` of a
registered abbreviation ending in digits (`UInt32s`) is not a word, nor is the
trailing `_` that escapes a Lean keyword (`HaltOp.return_`). When its pinned
Lean core source is registered, a final `D` after a word (`sliceD`) is Lean's
"with default" suffix (`Array.getD`); the map review renames any definition
whose `D` does not return a supplied or default value.

A binding may also cite rule 7: the name is the one Lean core, Std, Batteries
or Mathlib gives the same definition (`BitVec.neg` for `U256.neg`,
`decEq` for a `DecidableEq` implementation). Its source must be a registered
file of one of those repositories, and the review states that the meanings
agree. Within the product, a theorem may also spell the final component of a
Jaune constant its statement references, and any name may use as a namespace
a Jaune declaration of another file, when that constant's own final
component passes this lint where it is declared: whatever is wrong with that
name is reported there. `check` lints twice to learn those names.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import sys
from dataclasses import dataclass, replace

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


BINDING_KEYS = frozenset({'rule', 'source', 'spelling', 'style'})
# Rule 7 binds a name to the Lean ecosystem's own name for the same definition.
LEAN_REPOSITORIES = ('leanprover/lean4 ', 'leanprover-community/batteries ', 'leanprover-community/mathlib4 ')
BINDING_OPTIONS = frozenset({'segments', 'namespace_prefix', 'component'})


def source_form(name, row):
    """Check a binding's spelling against its name; return its component, if any.

    The default is the whole final segment, transliterated. `segments` must
    rejoin to the exact source spelling; the lint checks each against the
    registered vocabulary. `namespace_prefix` must start the spelling and
    transliterate to the
    enclosing namespace segment. `component` must be the transliterated
    spelling and occur in the final segment at token boundaries; the other
    tokens of that segment stay under the ordinary word check.
    """
    parts = name.split('.')
    spelled = row['spelling'].replace('-', '_')
    if 'segments' in row:
        segments = row['segments']
        if (not isinstance(segments, list) or len(segments) < 2
                or any(not isinstance(s, str) or not s for s in segments)
                or ''.join(segments) != row['spelling']):
            raise ValueError(f'{name}: segments must split the exact source spelling')
        spelled = '_'.join(segments)
    if 'namespace_prefix' in row:
        prefix = row['namespace_prefix']
        if (not isinstance(prefix, str) or not prefix or not spelled.startswith(prefix + '_')
                or len(parts) < 2 or parts[-2] != transliterate(prefix, 'upperCamel')):
            raise ValueError(f'{name}: namespace does not replace the source prefix')
        spelled = spelled[len(prefix) + 1:]
    form = transliterate(spelled, row['style'])
    if 'component' not in row:
        if parts[-1] != form:
            raise ValueError(f'{name}: source spelling/case mismatch')
        return None
    if row['component'] != form or not part_spans(parts[-1], form):
        raise ValueError(f'{name}: source spelling/case mismatch')
    return form


def validate_policy(policy, source_root):
    required = {'schema_version', 'words', 'sources', 'bindings'}
    if (not isinstance(policy, dict) or policy.get('schema_version') != 1
            or set(policy) - {'derived'} != required):
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
        if (not isinstance(row, dict) or not BINDING_KEYS <= set(row) <= BINDING_KEYS | BINDING_OPTIONS
                or any(not isinstance(row[key], str) for key in BINDING_KEYS)
                or row['rule'] not in ('1', '2', '3', '7')):
            raise ValueError(f'{name}: invalid source binding')
        spelling = row['spelling']
        # A hyphenated source compound (`hex-prefix`, `EIP-1559`) is word-separated.
        if not re.fullmatch('[A-Za-z][A-Za-z0-9_]*(?:-[A-Za-z0-9_]+)*', spelling):
            raise ValueError(f'{name}: invalid source spelling')
        if row['source'] not in sources:
            raise ValueError(f'{name}: unregistered source')
        if row['rule'] == '7' and not policy['sources'][row['source']]['citation'].startswith(LEAN_REPOSITORIES):
            raise ValueError(f'{name}: a rule 7 binding needs a Lean core, Std, Batteries or Mathlib source')
        # Exact identifier boundary, never a substring or a free-text citation.
        if not re.search(r'(?<![\w])' + re.escape(spelling) + r'(?![\w])', sources[row['source']]):
            raise ValueError(f'{name}: spelling absent from registered source')
        source_form(name, row)
    vocabulary = Vocabulary(words)
    vocabulary.keywords = frozenset(word for word, (key, spelling) in LEAN_KEYWORDS.items()
                                    if key in sources and attested(sources[key], spelling))
    vocabulary.swapped = frozenset(word for word, (_, key, spelling) in SWAPPED.items()
                                   if key in sources and attested(sources[key], spelling))
    word, key, spelling = CONCAT
    vocabulary.concat = key in sources and attested(sources[key], spelling)
    word, key, spelling = CONSTRUCTOR_NAME
    vocabulary.constructor = key in sources and attested(sources[key], spelling)
    word, key, spelling = FIELD_NAME
    vocabulary.field = key in sources and attested(sources[key], spelling)
    word, key, spelling = DEFAULT_SUFFIX
    vocabulary.default_suffix = key in sources and attested(sources[key], spelling)
    key, spelling = CORE_TYPE_CASE
    if key in sources and attested(sources[key], spelling):
        vocabulary.core_types = frozenset(word for word, (key, spelling) in CORE_TYPES.items()
                                          if key in sources and attested(sources[key], spelling))
    key, spelling = INSTANCE_NAME
    vocabulary.instance_name = key in sources and attested(sources[key], spelling)
    key, spelling = AUX_DEF
    vocabulary.aux_def = key in sources and attested(sources[key], spelling)
    return vocabulary


# Lean naming-convention keywords. Each is active only when the policy
# registers its pinned source (leanprover/lean4 at the v4.35.0 tag) and that
# source spells the given attestation at a word boundary.
LEAN_KEYWORDS = {
    **{word: ('lean4-std-naming', '`' + word + '`') for word in (
        'def', 'refl', 'rfl', 'irrefl', 'symm', 'trans', 'congr', 'comm', 'assoc',
        'distrib', 'self', 'inj', 'cancel', 'ext', 'mono')},
    'antisymm': ('lean4-std-naming', 'Nat.le_antisymm'),
    'imp': ('lean4-std-naming', 'imp_congr_left'),
    'pos': ('lean4-nat-basic', 'theorem pos_of_ne_zero'),
    'asymm': ('lean4-bool', 'theorem lt_asymm'),
    'succ': ('lean4-nat-basic', 'theorem add_succ'),
    'irrel': ('lean4-nat-log2', 'private theorem log2_rec_irrel'),
    'wf': ('lean4-std-dhashmap', 'wf : inner.WF'),
    # Boolean equality (`BEq.beq`, `Nat.beq`) and elimination from a contradiction (`False.elim`).
    'beq': ('lean4-prelude', 'def Nat.beq'),
    'elim': ('lean4-prelude', 'def False.elim'),
}
# Lean writes a type in lower camel case where a name leads with it (doc/std/naming.md:
# "When encountering a name, put it in lower camel case", as in `natAbs`). The leading
# token of a declaration's own component may so name a Lean core type; each type is
# active only when its pinned definition is registered and spelled, with the convention.
CORE_TYPE_CASE = ('lean4-std-naming', 'When encountering a name, put it in lower camel case.')
CORE_TYPES = {
    'nat': ('lean4-prelude', 'inductive Nat'),
    'bool': ('lean4-prelude', 'inductive Bool'),
    'string': ('lean4-prelude', 'structure String'),
    'list': ('lean4-prelude', 'inductive List'),
    'array': ('lean4-prelude', 'structure Array'),
    'option': ('lean4-prelude', 'inductive Option'),
    'int': ('lean4-int-basic', 'inductive Int'),
}
# An instance declared under the name Lean itself would give it (`instBEqForkField` for
# `instance : BEq (ForkField c α)`): Lean.Elab.mkInstanceName, emulated by `instance_name`.
INSTANCE_NAME = ('lean4-decl-name-gen', 'NameGen.mkBaseNameWithSuffix\' "inst" binders type')
# Lean names the definitions an `elab_rules`/`macro_rules` command generates
# `_aux_<module>___<suggestion>` (Lean.Elab.AuxDef); a local worker inside one keeps that
# compiler-generated namespace, which is not a word of the author's.
AUX_DEF = ('lean4-elab-auxdef', 'let id := `_aux ++ (← getMainModule) ++ `_ ++ id')
# Lean core reads a swapped `≤` or `<` as `ge` or `gt` (`List.not_lt_iff_ge :
# ¬ l₁ < l₂ ↔ l₂ ≤ l₁`); the statement must use the relation itself.
SWAPPED = {'ge': ('le', 'lean4-list-lex', 'protected theorem not_lt_iff_ge'),
           'gt': ('lt', 'lean4-list-lex', 'protected theorem not_le_iff_gt')}
# Lean core names a theorem about `l ++ [a]` with `concat` (`List.reverse_concat`).
CONCAT = ('concat', 'lean4-list-lemmas', 'theorem reverse_concat')
CONSTRUCTOR_NAME = ('mk', 'lean4-elab-structure', 'defaultCtorName := `mk')
# The field holding the underlying value of a wrapper structure (`Subtype.val`).
FIELD_NAME = ('val', 'lean4-prelude', 'val : α')
LEAN_SCOPE = ('Jaune', 'JauneConsensus')


class Vocabulary(set):
    """Whole words, with the Lean keywords whose sources are registered."""
    keywords = frozenset()
    swapped = frozenset()
    concat = False
    constructor = False
    field = False
    default_suffix = False
    core_types = frozenset()
    instance_name = False
    aux_def = False


def attested(text, spelling):
    return re.search(r'(?<![A-Za-z0-9_])' + re.escape(spelling) + r'(?![A-Za-z0-9_])', text) is not None


TOKEN = re.compile(r'[A-Z]{2,}(?=s(?:[A-Z0-9_]|$))|[A-Z]+(?=[A-Z][a-z]|[0-9]|$)|[A-Z]?[a-z]+|[0-9]+')


def component_spans(name, component):
    """Literal matches at whole camel/snake token boundaries, including digits."""
    tokens = list(TOKEN.finditer(name))
    starts = {t.start() for t in tokens}
    ends = {t.end() for t in tokens}
    return [m.span() for m in re.finditer(re.escape(component), name)
            if m.start() in starts and m.end() in ends]


def part_spans(segment, component):
    """`component_spans` within each snake_case part, as the word check tokenizes a segment."""
    if '_' in component:
        return component_spans(segment, component)
    spans, offset = [], 0
    for part in segment.split('_'):
        spans += [(offset + a, offset + b) for a, b in component_spans(part.rstrip("'?!"), component)]
        offset += len(part) + 1
    return spans


def derive_name(entry, base):
    """Prove this row changes just the sourced prefix or just its named tokens.

    Return the spans in the final segment which the source authenticates.
    An inherited namespace is checked by its own direct policy binding.
    """
    old, new = entry['old'], entry['new']
    if base['old'] == base['new']:
        return None
    if old.startswith(base['old'] + '.') and new == base['new'] + old[len(base['old']):]:
        return []
    scope, _, leaf = old.rpartition('.')
    new_scope, _, new_leaf = new.rpartition('.')
    base_scope, _, before = base['old'].rpartition('.')
    new_base_scope, _, after = base['new'].rpartition('.')
    if (scope != new_scope or base_scope != new_base_scope
            or not (scope == base_scope or scope.startswith(base_scope + '.'))
            or before == after or not before.isalnum() or not after.isalnum()):
        return None
    replaced = component_spans(leaf, before)
    if not replaced:
        return None
    pieces, covered, previous = [], [], 0
    for i, (start, end) in enumerate(replaced):
        pieces.extend((leaf[previous:start], after))
        target_start = start + i * (len(after) - len(before))
        covered.append((target_start, target_start + len(after)))
        previous = end
    pieces.append(leaf[previous:])
    if ''.join(pieces) != new_leaf or not set(covered) <= set(component_spans(new_leaf, after)):
        return None
    return covered


CLAUSE = re.compile(r"`([A-Za-z0-9_.?!']+)` ?-> ?`([A-Za-z0-9_.?!']+)`")


def derived_bases(row):
    """The directly bound names a derived row cites."""
    if 'base' in row:
        return [row['base']]
    return [item if isinstance(item, str) else item['name'] for item in row['bases']]


def _either_case(token):
    return {token, token[:1].swapcase() + token[1:]}


def _suffixes(name):
    parts = name.split('.')
    return ['.'.join(parts[i:]) for i in range(len(parts))]


def derive_compound(name, row, mapped, policy):
    """Check a map row whose rename combines several sourced components.

    Each base is a directly bound name. A base with a map row brings its own
    old name; a bound namespace without one states the old namespace or token
    it replaced. The row must cite that rename, either by repeating the base
    row's citation or by naming it as `old` -> `new`. The row's names must
    carry it: the old name descends from the base's old name where the new
    one descends from the base, or a segment of the old name holds the base's
    old final token as often as the matching segment of the new name holds
    its bound spelling at token boundaries. Every
    rule 1-3 the row lists needs a base bound under that rule, and no base
    may bring a rule the row does not list. Only the bound spellings in the
    final segment are credited; every other token keeps the word check.
    """
    entry, bases = mapped.get(name), row['bases']
    if (not isinstance(row['old'], str) or not isinstance(bases, list) or not bases
            or entry is None or entry['old'] != row['old'] or name in policy['bindings']):
        raise ValueError(f'{name}: derived binding lacks matching map row')
    listed = [rule.strip() for rule in entry['rule'].split(',')]
    untagged = lambda text: re.sub(r' \[[A-Z]\]$', '', text)
    rules, covered = set(), set()
    for item in bases:
        if isinstance(item, str):
            base, given = item, None
        elif (isinstance(item, dict) and set(item) == {'name', 'old'}
              and all(isinstance(v, str) and v for v in item.values())):
            base, given = item['name'], item['old']
        else:
            raise ValueError(f'{name}: invalid derived base')
        binding, parent = policy['bindings'].get(base), mapped.get(base)
        if binding is None or base == name or (parent is None) == (given is None):
            raise ValueError(f'{name}: derived base {base} is not a directly bound name with one known old name')
        if parent is not None and parent['layer'] != entry['layer'] and (
                parent['layer'], entry['layer']) != ('execution', 'adapter'):
            raise ValueError(f'{name}: derived base {base} belongs to another layer')
        if binding['rule'] not in listed:
            raise ValueError(f'{name}: map row does not list the rule of {base}')
        old_base = parent['old'] if parent is not None else given
        before, after = old_base.rsplit('.', 1)[-1], base.rsplit('.', 1)[-1]
        olds = set(_suffixes(old_base)) | _either_case(before)
        news = set()
        for suffix in _suffixes(base):
            news |= {suffix} | _either_case(suffix.replace('.', ''))
        if not ((parent is not None and untagged(entry['source']) == untagged(parent['source']))
                or any(a in olds and b in news for a, b in CLAUSE.findall(entry['source']))):
            raise ValueError(f'{name}: map citation does not name the rename of {base}')
        inherited = ('.' in old_base and entry['old'].startswith(old_base + '.')
                     and name.startswith(base + '.'))
        old_rest = (entry['old'][len(old_base) + 1:] if inherited else entry['old']).split('.')
        new_rest = (name[len(base) + 1:] if inherited else name).split('.')
        carried = False
        for depth, (old_part, new_part) in enumerate(zip(reversed(old_rest), reversed(new_rest))):
            for a, b in {(before, after), (before[:1].swapcase() + before[1:], after[:1].swapcase() + after[1:])}:
                replaced, spans = old_part.count(a), part_spans(new_part, b)
                if not replaced:
                    continue
                if replaced != len(spans):
                    # An inherited namespace already carries the rename; elsewhere it must be exact.
                    if inherited:
                        continue
                    raise ValueError(f'{name}: change extends beyond sourced component {base}')
                carried = True
                if depth == 0:
                    part = binding.get('component')
                    # A base whose own name is only partly sourced credits that part alone.
                    inner = ([(0, len(b))] if part is None else component_spans(b, part)
                             or component_spans(b, part[:1].swapcase() + part[1:]))
                    covered.update((start + x, start + y) for start, _ in spans for x, y in inner)
        if not inherited and not carried:
            raise ValueError(f'{name}: change extends beyond sourced component {base}')
        rules.add(binding['rule'])
    if {rule for rule in listed if rule in ('1', '2', '3')} - rules:
        raise ValueError(f'{name}: derived binding lacks a base for each sourced rule it lists')
    return sorted(covered)


def binding_backs_listed_rule(name, entry, binding, policy, mapped):
    """Master ruling R15 (G2b U9). A map row may list several rules, its
    first for the token it renames (rule 3 for `B256` -> `U256`) and another
    for a token the rename keeps (rule 7 for the leaf `neg`, Lean's
    `BitVec.neg`). A direct binding then evidences the kept token under its
    own rule when (a) the row lists that rule and the binding's spelling
    covers a token of the new name (`source_form`, as policy validation
    checks), and (b) every other listed rule that needs a source (1-3) is
    backed for the renamed namespace token as today: a proper prefix of the
    name bound under that rule, which the map renames with that rule listed,
    from the prefix of the row's old name."""
    rules = [r.strip() for r in entry['rule'].split(',')]
    if binding['rule'] not in rules:
        return False
    try:
        source_form(name, binding)
    except ValueError:
        return False
    parts = name.split('.')
    for rule in rules:
        if rule not in ('1', '2', '3') or rule == binding['rule']:
            continue
        for k in range(len(parts) - 1, 0, -1):
            prefix = '.'.join(parts[:k])
            base, row = policy['bindings'].get(prefix), mapped.get(prefix)
            if (base is not None and base['rule'] == rule and row is not None and
                    rule in [r.strip() for r in row['rule'].split(',')] and
                    entry['old'].startswith(row['old'] + '.')):
                break
        else:
            return False
    return True


def derived_bindings(policy, mapping):
    """Resolve opt-in derived rows against directly bound roots and the actual rename map."""
    derived = policy.get('derived', {})
    if not isinstance(derived, dict):
        raise ValueError('derived must be an object')
    mapped = {r['new']: r for r in mapping['entries'] if r['kind'] != 'module'}
    result = {}
    for name, row in derived.items():
        if isinstance(row, dict) and set(row) == {'old', 'bases'}:
            result[name] = derive_compound(name, row, mapped, policy)
            continue
        if (not isinstance(row, dict) or set(row) != {'old', 'base'}
                or not all(isinstance(v, str) and v for v in row.values())
                or name in policy['bindings']):
            raise ValueError(f'{name}: invalid derived binding')
        entry = mapped.get(name)
        base_name = row['base']
        base = mapped.get(base_name)
        binding = policy['bindings'].get(base_name)
        if (entry is None or entry['old'] != row['old'] or base is None or binding is None
                or entry['layer'] != base['layer'] or entry['source'] != base['source']
                or entry['rule'].split(',')[0].strip() != binding['rule']
                or base['rule'].split(',')[0].strip() != binding['rule']):
            raise ValueError(f'{name}: derived binding lacks matching map row, source and directly bound base')
        spans = derive_name(entry, base)
        if spans is None:
            raise ValueError(f'{name}: change extends beyond sourced component {base_name}')
        result[name] = spans
    return result


@dataclass(frozen=True)
class Statement:
    """Compiler evidence for one declaration's name.

    endings: lengths of referenced punctuated targets that prefix a theorem.
    names: final components of non-Jaune constants in the kernel statement.
    marks: punctuated final components of any constant in the kernel statement.
    proof: a theorem, or a constructor of an inductive proposition.
    builds: a constructor, or a definition whose statement concludes in its
    own namespace's type (or an `Option` of it).
    field: a structure projection.
    implements: a definition that an instance in this module passes, as the
    method named after the class, to a Lean core, Std, Batteries or Mathlib
    class constructor (`instance : Neg U256 := ⟨U256.neg⟩`).
    conventional: final components `mk` or `val` of statement constants.
    namespaces: namespaces of non-Jaune statement constants (`Std.TreeMap`),
    which a Jaune namespace may mirror.
    singleton_append: the statement appends a one-element list (`l ++ [a]`).
    predicate: a definition of a proposition; its defining body supplies names.
    own: Jaune constants of the kernel statement, which a theorem may spell
    when their own names pass the lint (`lint_names` `product`).
    instance_name: for an instance, the name Lean would generate for it.
    """
    endings: frozenset = frozenset()
    names: frozenset = frozenset()
    marks: frozenset = frozenset()
    proof: bool = False
    builds: bool = False
    field: bool = False
    implements: bool = False
    conventional: frozenset = frozenset()
    namespaces: frozenset = frozenset()
    singleton_append: bool = False
    predicate: bool = False
    own: frozenset = frozenset()
    instance_name: str = ''

    def __contains__(self, item):
        return item in self.endings


def statement_constants(pool, root):
    """Every constant a kernel expression mentions, structure projections included."""
    seen, found, stack = set(), set(), [root]
    while stack:
        i = stack.pop()
        if i in seen:
            continue
        seen.add(i)
        node = pool[i]
        kind = node[0]
        if kind == 'const':
            found.add(node[1][1])
        elif kind == 'app':
            stack += [node[1], node[2]]
        elif kind in ('forall', 'lam'):
            stack += [node[2], node[3]]
        elif kind == 'let':
            stack += [node[2], node[3], node[4]]
        elif kind == 'proj':
            found.add(node[1][1])
            stack.append(node[3])
        elif kind == 'mdata':
            stack.append(node[-1])
        elif kind not in ('bvar', 'fvar', 'mvar', 'sort', 'nat', 'str', 'lit'):
            raise ValueError(f'unsupported kernel expression: {kind}')
    return found


def conclusion(pool, root):
    while pool[root][0] == 'forall':
        root = pool[root][3]
    return root


def head(pool, i):
    args = []
    while pool[i][0] == 'app':
        args.append(pool[i][2])
        i = pool[i][1]
    node = pool[i]
    return (node[1][1] if node[0] == 'const' else ''), args[::-1]


def theorem_reference_endings(bundle):
    """Statement evidence for each declaration of a reference bundle.

    The compiler identifies the enclosing declaration of each constant use, so
    punctuation inside a theorem's name may belong to its referenced definition
    when the full qualified prefix of that theorem is the definition. The
    kernel statement supplies the referenced constants of rule 7. A constant
    counts as Jaune's when this module declares it, the index places it in a
    Jaune module, or it lies in a Jaune namespace.
    """
    index = bundle['index']
    module = APPLY.module_name(index['module'])
    constants = bundle.get('constants', {})
    pool = bundle.get('expr_pool', [])
    levels = bundle.get('level_pool', [])
    endings = {}
    own = set(constants)
    for key, info in index['references'].items():
        ref = json.loads(key).get('c')
        if not ref:
            continue
        if ref['m'].split('.')[0] in LEAN_SCOPE:
            own.add(ref['n'])
        if not ref['n'].endswith(("'", '?', '!')):
            continue
        target = user_name(ref['n'], ref['m'])
        for usage in info.get('usages', []):
            if len(usage) != 5 or not isinstance(usage[4], str):
                continue
            owner = usage[4]
            if constants.get(owner, {}).get('kernel', {}).get('payload') != ['theorem']:
                continue
            theorem = user_name(owner, module)
            if theorem.startswith(target + '_') and '.' not in theorem[len(target):]:
                endings.setdefault(theorem, set()).add(len(target.rsplit('.', 1)[-1]))

    def is_own(name):
        return name in own or name.split('.')[0] in LEAN_SCOPE

    def proposition(name):
        kernel = constants.get(name, {}).get('kernel', {})
        if kernel.get('payload', [None])[0] != 'inductive' or 'type' not in kernel:
            return False
        node = pool[conclusion(pool, kernel['type'])]
        return node[0] == 'sort' and levels[node[1]] == ['zero']

    def lambda_body(i):
        while pool[i][0] == 'lam':
            i = pool[i][3]
        return i

    implemented = set()
    for owner, decl in constants.items():
        kernel = decl.get('kernel', {})
        payload = kernel.get('payload') or [None]
        if (payload[0] != 'definition' or len(payload) < 3 or not pool
                or (decl.get('attributes') or {}).get('instance') is None):
            continue
        target, args = head(pool, lambda_body(payload[2]))
        scope, _, last = target.rpartition('.')
        if last != 'mk' or not scope or is_own(target):
            continue
        cls = scope.rsplit('.', 1)[-1]
        for arg in args:
            name = head(pool, lambda_body(arg))[0]
            if name and is_own(name) and name.rsplit('.', 1)[-1] in (cls, lower_first(cls)):
                implemented.add(name)

    result = {}
    for owner, decl in constants.items():
        try:
            name = user_name(owner, module)
        except ValueError:
            continue
        kernel = decl.get('kernel', {})
        payload = kernel.get('payload') or [None]
        kind = payload[0]
        names, marks, proof, builds, field = set(), set(), False, False, False
        conventional, namespaces, singleton, predicate = set(), set(), False, False
        product = set()
        if 'type' in kernel and pool:
            referenced = statement_constants(pool, kernel['type'])
            singleton = singleton_append(pool, kernel['type'])
            if kind == 'definition' and len(payload) > 2:
                node = pool[conclusion(pool, kernel['type'])]
                if node[0] == 'sort' and levels[node[1]] == ['zero']:
                    predicate = True
                    referenced = referenced | statement_constants(pool, payload[2])
            for constant in referenced:
                last = constant.rsplit('.', 1)[-1]
                if last.endswith(("'", '?', '!')):
                    marks.add(last)
                if not is_own(constant):
                    names.add(last)
                    parts = constant.split('.')
                    namespaces.update('.'.join(parts[:i]) for i in range(1, len(parts) + 1))
                elif not constant.startswith('_private.') or constant.startswith('_private.' + module + '.'):
                    product.add(user_name(constant, module))
                if last in (CONSTRUCTOR_NAME[0], FIELD_NAME[0]):
                    conventional.add(last)
            if kind == 'constructor':
                builds = True
                proof = proposition(payload[1][1])
            elif kind == 'definition':
                scope = owner.rpartition('.')[0]
                target, args = head(pool, conclusion(pool, kernel['type']))
                if target == 'Option' and args:
                    target = head(pool, args[-1])[0]
                builds = bool(scope) and target == scope
                field = len(payload) > 2 and pool[lambda_body(payload[2])][0] == 'proj'
        proof = proof or kind == 'theorem'
        ends = frozenset(endings.get(name, ()))
        implements = owner in implemented
        generated = ''
        if (kind == 'definition' and 'type' in kernel and pool
                and (decl.get('attributes') or {}).get('instance') is not None):
            generated = instance_name(pool, levels, kernel['type'], name, module, is_own)
        if (ends or names or marks or proof or builds or field or implements or conventional or namespaces or product
                or generated):
            result[name] = Statement(ends, frozenset(names), frozenset(marks), proof, builds,
                                     field, implements, frozenset(conventional), frozenset(namespaces),
                                     singleton, predicate, frozenset(product), generated)
    return result


def _loose(pool, i, depth=0, memo=None):
    """The de Bruijn indices free in pool[i], relative to its own binder depth."""
    memo = {} if memo is None else memo
    if (i, depth) in memo:
        return memo[i, depth]
    node, found = pool[i], set()
    kind = node[0]
    if kind == 'bvar':
        if node[1] >= depth:
            found.add(node[1] - depth)
    elif kind == 'app':
        found = _loose(pool, node[1], depth, memo) | _loose(pool, node[2], depth, memo)
    elif kind in ('forall', 'lam'):
        found = _loose(pool, node[2], depth, memo) | _loose(pool, node[3], depth + 1, memo)
    elif kind == 'let':
        found = (_loose(pool, node[2], depth, memo) | _loose(pool, node[3], depth, memo)
                 | _loose(pool, node[4], depth + 1, memo))
    elif kind == 'proj':
        found = _loose(pool, node[3], depth, memo)
    elif kind == 'mdata':
        found = _loose(pool, node[-1], depth, memo)
    memo[i, depth] = frozenset(found)
    return memo[i, depth]


def instance_name(pool, levels, root, name, module, is_own):
    """The name Lean.Elab.mkInstanceName gives an anonymous instance of this type.

    `inst`, then the conclusion rendered by its constants (last components,
    capitalized; sorts as Prop/Type/Sort; each subexpression once), then `Of`
    and each non-dependent binder type that renders to something, outermost
    first. Constants of the enclosing namespace are not repeated, and a name
    mentioning nothing of this project takes its suffix. Implicit non-type
    arguments, proofs and macro scopes, which Lean omits, are not modelled:
    the emulation can only come out longer than Lean's name, never shorter.
    """
    seen, consts = set(), set()
    namespace = name.split('.')[:-1]

    def render(i, omit_top_forall=False):
        node = pool[i]
        key = ('const', node[1][1]) if node[0] == 'const' else i
        if key in seen:
            return ''
        if node[0] == 'const':
            consts.add(node[1][1])
            last = node[1][1].rsplit('.', 1)[-1]
            text = last[:1].upper() + last[1:]
        elif node[0] == 'app':
            text = render(node[1]) + render(node[2])
        elif node[0] == 'forall':
            ty = '' if 0 in _loose(pool, node[3]) else render(node[2])
            text = render(node[3], True) if omit_top_forall and not ty else 'Forall' + ty + render(node[3])
        elif node[0] == 'sort':
            level = levels[node[1]] if isinstance(node[1], int) and node[1] < len(levels) else None
            text = 'Prop' if level == ['zero'] else 'Type' if level and level[0] == 'succ' else 'Sort'
        elif node[0] in ('lam', 'mdata', 'let'):
            text = render(node[3] if node[0] == 'lam' else node[-1] if node[0] == 'mdata' else node[4])
        else:
            text = ''
        seen.add(key)
        return text

    binders, i = [], root
    while pool[i][0] == 'forall':
        binders.append((pool[i][2], 0 in _loose(pool, pool[i][3])))
        i = pool[i][3]
    referenced = statement_constants(pool, root)
    for k in range(1, len(namespace) + 1):
        prefix = '.'.join(namespace[:k])
        if prefix in referenced:
            seen.add(('const', prefix))
            consts.add(prefix)
    text = render(i)
    ofs = []
    for ty, dependent in reversed(binders):
        part = '' if dependent else render(ty, True)
        if part:
            ofs.append('Of' + part)
    text += ''.join(reversed(ofs))
    root_module = module.split('.')[0]
    if not any(is_own(c) and (c.split('.')[0] == root_module or not c.split('.')[0] in LEAN_SCOPE)
               for c in consts):
        text += '_' + root_module[:1].lower() + root_module[1:]
    return 'inst' + text


def singleton_append(pool, root):
    """Whether an expression appends a one-element list: `HAppend.hAppend _ _ _ _ l [a]`."""
    seen, stack = set(), [root]
    while stack:
        i = stack.pop()
        if i in seen:
            continue
        seen.add(i)
        node = pool[i]
        if node[0] == 'app':
            target, args = head(pool, i)
            if target == 'HAppend.hAppend' and len(args) == 6:
                last, inner = head(pool, args[5])
                if last == 'List.cons' and len(inner) == 3 and head(pool, inner[2])[0] == 'List.nil':
                    return True
            stack += [node[1], node[2]]
        elif node[0] in ('forall', 'lam'):
            stack += [node[2], node[3]]
        elif node[0] == 'let':
            stack += [node[2], node[3], node[4]]
        elif node[0] == 'proj':
            stack.append(node[3])
        elif node[0] == 'mdata':
            stack.append(node[-1])
    return False


def lower_first(text):
    return text[:1].lower() + text[1:]


def statement_spans(part, start, evidence, words=()):
    """Token spans of one name component that spell a referenced constant (rule 7)."""
    if not (getattr(evidence, 'proof', False) or getattr(evidence, 'predicate', False)):
        return []
    names = set(getattr(evidence, 'names', ()))
    if getattr(evidence, 'proof', False):
        names.update(word for word, (relation, _, _) in SWAPPED.items()
                     if word in getattr(words, 'swapped', ()) and relation in names)
    for word, active in ((CONSTRUCTOR_NAME[0], getattr(words, 'constructor', False)),
                         (FIELD_NAME[0], getattr(words, 'field', False))):
        if active and word in getattr(evidence, 'conventional', ()):
            names.add(word)
    if not names:
        return []
    matches = list(TOKEN.finditer(part))
    folded = [lower_first(m.group()) for m in matches]
    spans = []
    for name in names:
        tokens = TOKEN.findall(name)
        if not tokens or ''.join(tokens) != name:
            continue
        tokens = [lower_first(token) for token in tokens]
        for i in range(len(folded) - len(tokens) + 1):
            if folded[i:i + len(tokens)] == tokens:
                spans.append((start + matches[i].start(), start + matches[i + len(tokens) - 1].end()))
    return spans


# Lean 4 keywords a declaration can take only with an escape: the trailing `_`
# of `HaltOp.return_` (opcode RETURN) is that escape, not a word.
ESCAPED_KEYWORDS = frozenset(
    'at by do else end fun have if in let match open return show then where with'.split())
# Lean core's `D` suffix: the variant that returns a supplied or default value
# where the plain operation has none (`Option.getD`, `Array.getD`, `List.headD`).
# Active only when its pinned source is registered; the map review checks that
# each such definition really returns a default (rule 7), and renames it otherwise.
DEFAULT_SUFFIX = ('D', 'lean4-prelude', 'abbrev Array.getD')


def unknown_words(segment, words, abbreviations, covered=(), reference_endings=()):
    """Never silently drop Unicode, punctuation, or unrecognized characters."""
    stripped = segment.rstrip("'?!")
    trailing = segment[len(stripped):]
    segment = stripped
    unknown = []
    offset = 0
    names = getattr(reference_endings, 'names', frozenset())
    marks = getattr(reference_endings, 'marks', frozenset())
    proof = getattr(reference_endings, 'proof', False)
    keywords = getattr(words, 'keywords', frozenset())
    default_suffix = getattr(words, 'default_suffix', False)
    parts = segment.split('_')
    for index, part in enumerate(parts):
        start = offset
        offset += len(part) + 1
        if start + len(part) in reference_endings:
            part = part.rstrip("'?!")
        # The final component ends in the referenced Lean constant's own punctuation
        # (`mem_toList_of_getElem?` for `GetElem?.getElem?`).
        if proof and trailing and index == len(parts) - 1 and part + trailing in marks and part + trailing in names:
            continue
        if proof and part in marks:
            if part in names:
                continue
            part = part.rstrip("'?!")
        if proof and part.rstrip("'") in keywords:
            continue
        if (proof and part.rstrip("'") == CONCAT[0] and getattr(words, 'concat', False)
                and getattr(reference_endings, 'singleton_append', False)):
            continue
        if not part:
            if len(parts) == 2 and index == 1 and parts[0] in ESCAPED_KEYWORDS:
                continue
            unknown.append('<empty>')
            continue
        if part in abbreviations:
            continue
        covered = list(covered) + statement_spans(part, start, reference_endings, words)
        spans = [m.span() for m in TOKEN.finditer(part)]
        tokens = [part[x:y] for x, y in spans]
        if ''.join(tokens) != part:
            unknown.append(part)
            continue
        allowed = sorted((TOKEN.findall(a) for a in abbreviations
                          if ''.join(TOKEN.findall(a)) == a), key=len, reverse=True)
        # Lean writes a short acronym in one case (`IORef`), so an allowed
        # one-token acronym can run into a following capital (`toIOU256` is
        # IO + U256). Split such a run only at an allowed acronym; the rest
        # of the run is still checked as its own token.
        heads = sorted((a[0] for a in allowed if len(a) == 1 and a[0].isupper() and len(a[0]) > 1),
                       key=len, reverse=True)
        k = 0
        while k < len(tokens):
            token = tokens[k]
            head = next((h for h in heads if token.isupper() and len(token) > len(h) and token.startswith(h)
                         and not any(tokens[k:k + len(a)] == a for a in allowed)), None)
            if head:
                x, y = spans[k]
                spans[k:k + 1] = [(x, x + len(head)), (x + len(head), y)]
                tokens[k:k + 1] = [head, token[len(head):]]
            k += 1
        i = 0
        abbreviation_end = None
        while i < len(tokens):
            if any(a <= start + spans[i][0] and start + spans[i][1] <= b for a, b in covered):
                i += 1
                continue
            match = next((a for a in allowed if a and tokens[i:i + len(a)] == a), None)
            # lowerCamel lowers a leading all-capitals abbreviation (`BPO1` -> `bpo1Rules`,
            # `G1` -> `g1MsmLengthPerPair`), as the map already writes `rlpFieldCount`.
            if match is None and i == 0 and tokens[0].islower():
                match = next((a for a in allowed if a and a[0].isupper() and a[0].lower() == tokens[0]
                              and tokens[1:len(a)] == a[1:]), None)
            # A Lean core type leading the component in lower camel case (`natOf`, `bool`).
            if match is None and i == 0 and index == 0 and tokens[0] in getattr(words, 'core_types', ()):
                match = [tokens[0]]
            if match:
                i += len(match)
                abbreviation_end = i
            else:
                token = tokens[i]
                # The plural `s` of an acronym (`EIPs`) or of a registered
                # abbreviation ending in digits (`UInt32s`) is not a word of its own.
                plural = token == 's' and i > 0 and (tokens[i - 1].isupper() or abbreviation_end == i)
                # `D` closing a component after a word (`sliceD`, `takeRightD`).
                default = (default_suffix and token == DEFAULT_SUFFIX[0] and i == len(tokens) - 1
                           and i > 0 and tokens[i - 1][:1].isalpha() and tokens[i - 1][1:].islower())
                if not token.isdigit() and not plural and not default and token.lower() not in words:
                    unknown.append(token)
                i += 1
    return unknown


def passing_names(names, problems):
    """The linted names whose own final component and source binding passed."""
    failed = {p['segment'] for p in problems if p['reason'] == 'unregistered word or source'}
    failed |= {p['name'] for p in problems if p['reason'] != 'unregistered word or source'}
    return frozenset(names) - failed


def lint_names(names, mapping, policy, words, final=False, derived=None, reference_endings=None, product=None,
               module=None):
    """(problems, used source bindings, pending findings). A pending retired
    name is reported without failing, except in a final run, which enforces it.
    `product` holds the product names known to pass where they are declared.
    `module` is the declaring module, which compiler-generated `_aux_` names spell."""
    if reference_endings is None:
        reference_endings = {}
    product = product or frozenset()
    if derived is None:
        derived = derived_bindings(policy, mapping)
    problems, pending = [], []
    used_bindings = set()
    enforced_names, pending_names = MAP.retired_name_lists(mapping)
    if final:
        enforced_names, pending_names = enforced_names + pending_names, []
    abbreviations = set(mapping['allowed_abbreviations'])
    mapped = {entry['new']: entry for entry in mapping['entries'] if entry['kind'] != 'module'}
    for name, location in sorted(names.items()):
        entry = mapped.get(name)
        if entry and entry['rule'].split(',')[0].strip() in ('1', '2', '3'):
            binding = policy['bindings'].get(name)
            if name not in derived and (not binding or (binding['rule'] != entry['rule'].split(',')[0].strip()
                                                        and not binding_backs_listed_rule(name, entry, binding,
                                                                                          policy, mapped))):
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
            if (module and getattr(words, 'aux_def', False)
                    and part.startswith('_aux_' + module.replace('.', '_') + '___')):
                continue
            prefix = '.'.join(parts[:i + 1])
            evidence = reference_endings.get(prefix, ())
            if prefix in policy['bindings']:
                used_bindings.add(prefix)
                binding = policy['bindings'][prefix]
                # The words a binding splits its source spelling into are vocabulary like any other.
                unknown = [token for segment in binding.get('segments', ())
                           for token in unknown_words(segment, words, abbreviations)]
                if 'component' in binding:
                    unknown += unknown_words(part, words, abbreviations,
                                             part_spans(part, binding['component']), evidence)
                if unknown:
                    problems.append(dict(name=name, location=location,
                                         reason='unregistered word or source', segment=prefix, tokens=unknown))
                continue
            mirrored = getattr(reference_endings.get(name, ()), 'namespaces', ())
            if i < len(parts) - 1 and parts[0] in LEAN_SCOPE and '.'.join(parts[1:i + 1]) in mirrored:
                continue
            # A namespace that is a product declaration passing where it is declared.
            if i < len(parts) - 1 and prefix in product:
                continue
            if i == len(parts) - 1 and getattr(evidence, 'proof', False):
                spelled = {own.rsplit('.', 1)[-1] for own in evidence.own if own in product}
                if spelled:
                    evidence = replace(evidence, names=evidence.names | spelled)
            covered = derived.get(prefix, ())
            if prefix in derived:
                used_bindings.update((prefix, *derived_bases(policy['derived'][prefix])))
            if i == len(parts) - 1 and (
                    (part.rstrip('?') == CONSTRUCTOR_NAME[0] and getattr(words, 'constructor', False)
                     and getattr(evidence, 'builds', False))
                    or (part == FIELD_NAME[0] and getattr(words, 'field', False)
                        and getattr(evidence, 'field', False))
                    or getattr(evidence, 'implements', False)
                    or (part.startswith('inst') and getattr(words, 'instance_name', False)
                        and getattr(evidence, 'instance_name', '') == part)):
                continue
            unknown = unknown_words(part, words, abbreviations, covered, evidence)
            if unknown:
                problems.append(dict(name=name, location=location,
                                     reason='unregistered word or source', segment=prefix, tokens=unknown))
    return problems, used_bindings, pending


def check(tree, mapping, policy, source_root, files, roots, final=False):
    MAP.validate_map(mapping)
    registered_pending = MAP.retired_name_lists(mapping)[1]
    words = validate_policy(policy, source_root)
    derived = derived_bindings(policy, mapping)
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
    loaded = []
    for source, bundle_path in files:
        raw = APPLY.safe_path(tree, source).read_bytes()
        bundle_raw = Path(bundle_path).read_bytes()
        bundle = json.loads(bundle_raw)
        text = raw.decode('utf-8')
        if bundle.get('source') != text:
            raise ValueError(f'{source}: reference bundle source mismatch; re-export')
        names = declarations(text, bundle['index'])
        loaded.append((source, raw, bundle_raw, names, theorem_reference_endings(bundle),
                       APPLY.module_name(bundle['index']['module'])))
    # First pass: the product names that pass where they are declared.
    product = set()
    for source, raw, bundle_raw, names, evidence, module in loaded:
        product |= passing_names(names, lint_names(names, mapping, policy, words, final, derived, evidence,
                                                   module=module)[0])
    for source, raw, bundle_raw, names, evidence, module in loaded:
        found, bindings, waiting = lint_names(names, mapping, policy, words, final, derived, evidence,
                                              frozenset(product), module=module)
        used.update(bindings)
        problems.extend(dict(source=source, **problem) for problem in found)
        pending.extend(dict(source=source, **problem) for problem in waiting)
        rows.append(dict(source=source, source_sha256=sha(raw), bundle_sha256=sha(bundle_raw), declarations=len(names)))
    if roots:
        for stale in sorted((set(policy['bindings']) | set(derived)) - used):
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
