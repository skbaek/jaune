#!/usr/bin/env python3
"""Validate Jaune's machine-readable rename map (scripts/naming-map.json)."""
import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_MAP = ROOT / "scripts" / "naming-map.json"
VALID_KINDS = frozenset({"declaration", "field", "constructor", "namespace", "module", "relocation"})
# Rows in the module namespace; every other kind names a Lean constant/namespace.
MODULE_KINDS = frozenset({"module"})
VALID_LAYERS = frozenset({"execution", "consensus", "adapter"})
VALID_RULES = frozenset({"1", "2", "3", "4", "5", "6", "7"})
REQUIRED_FIELDS = ("old", "new", "kind", "layer", "rule", "source")
OPTIONAL_FIELDS = ("notes", "from_module", "to_module", "public_from")
ALLOWED_ENTRY_FIELDS = frozenset(REQUIRED_FIELDS + OPTIONAL_FIELDS)
# An acronym with a plural `s` (`BLTs`, `NTBs`) is the acronym and `s`, not `BL` + `Ts`.
TOKEN_RE = re.compile(r"[A-Z]{2,}(?=s(?:[A-Z0-9_]|$))|[A-Z]+(?=[A-Z][a-z0-9]|$)|[A-Z]?[a-z0-9]+")


def tokenize_identifier(qualified_name):
    """Split a qualified Lean identifier into camelCase/snake_case tokens."""
    tokens = []
    for segment in qualified_name.split("."):
        for part in segment.split("_"):
            if not part:
                continue
            tokens.extend(TOKEN_RE.findall(part))
    return tokens


def find_retired_tokens(qualified_name, retired_tokens):
    """Return retired tokens appearing as identifier tokens in qualified_name."""
    hits = []
    patterns = {token: tokenize_identifier(token) for token in retired_tokens}
    for segment in qualified_name.split("."):
        tokens = tokenize_identifier(segment)
        for retired, pattern in patterns.items():
            if segment == retired or (pattern and any(
                    tokens[i:i + len(pattern)] == pattern
                    for i in range(len(tokens) - len(pattern) + 1))):
                hits.append(retired)
    return hits


def _require_string_list(data, key):
    value = data.get(key)
    if not isinstance(value, list) or not all(isinstance(item, str) and item.strip() for item in value):
        raise ValueError(f"top-level '{key}' must be a list of non-empty strings")
    if len(set(value)) != len(value):
        raise ValueError(f"top-level '{key}' contains duplicate entries")
    return value


def _parse_rules(raw_rule):
    parts = [part.strip() for part in raw_rule.split(",") if part.strip()]
    if not parts or any(part not in VALID_RULES for part in parts):
        raise ValueError(f"invalid rule specification: {raw_rule!r}")
    return parts


def validate_map(data):
    """Validate rename-map schema, one-to-one bijection, sources, and retired tokens."""
    if not isinstance(data, dict):
        raise ValueError("rename map root must be a JSON object")
    if data.get("schema_version") != 1:
        raise ValueError(f"unsupported schema_version: {data.get('schema_version')!r}")

    retired_tokens = _require_string_list(data, "retired_tokens")
    _require_string_list(data, "allowed_abbreviations")

    entries = data.get("entries")
    if not isinstance(entries, list):
        raise ValueError("top-level 'entries' must be a list")

    seen_old = {}
    seen_new = {}
    for index, entry in enumerate(entries):
        if not isinstance(entry, dict):
            raise ValueError(f"entry {index} must be a JSON object")
        unknown = set(entry) - ALLOWED_ENTRY_FIELDS
        if unknown:
            raise ValueError(f"entry {index} has unknown fields: {', '.join(sorted(unknown))}")

        for field in REQUIRED_FIELDS:
            value = entry.get(field)
            if not isinstance(value, str) or not value.strip():
                raise ValueError(f"entry {index} missing non-empty '{field}'")

        if "notes" in entry and not isinstance(entry["notes"], str):
            raise ValueError(f"entry {index} 'notes' must be a string")

        old_name = entry["old"].strip()
        new_name = entry["new"].strip()
        if entry["kind"] not in VALID_KINDS:
            raise ValueError(f"entry {index} invalid kind: {entry['kind']!r}")
        relocation = entry["kind"] == "relocation"
        for field in ("from_module", "to_module"):
            if relocation:
                if not isinstance(entry.get(field), str) or not entry[field].strip():
                    raise ValueError(f"entry {index} relocation requires non-empty '{field}'")
            elif field in entry:
                raise ValueError(f"entry {index} '{field}' is only valid for relocation rows")
        if "public_from" in entry:
            private = split_private(entry["public_from"]) if isinstance(entry["public_from"], str) else None
            if (entry["kind"] not in ("declaration", "relocation") or not private
                    or (relocation and private[0] != entry["from_module"])
                    or private[2] != old_name or new_name.startswith("_private.")):
                raise ValueError(f"entry {index} public_from must name the relocated private declaration")
        if relocation and entry["from_module"] == entry["to_module"]:
            raise ValueError(f"entry {index} relocates within one module")
        # A relocation may keep its name: the module is what changes.
        if old_name == new_name and not relocation and "public_from" not in entry:
            raise ValueError(f"entry {index} maps '{old_name}' to itself")
        if entry["layer"] not in VALID_LAYERS:
            raise ValueError(f"entry {index} invalid layer: {entry['layer']!r}")
        _parse_rules(entry["rule"])

        space = "module" if entry["kind"] in MODULE_KINDS else "name"
        if (space, old_name) in seen_old:
            raise ValueError(f"duplicate old name: {old_name}")
        if (space, new_name) in seen_new:
            raise ValueError(f"duplicate new name: {new_name}")
        seen_old[space, old_name] = entry
        seen_new[space, new_name] = entry

        retired_hits = find_retired_tokens(new_name, retired_tokens)
        if retired_hits:
            raise ValueError(
                f"entry {index} new name '{new_name}' contains retired token(s): "
                + ", ".join(sorted(set(retired_hits)))
            )
    # Namespace rows rename every descendant; an explicit row for a descendant
    # overrides it. Two namespace rows may nest only consistently.
    namespaces = {e["old"]: e["new"] for e in entries if e["kind"] == "namespace"}
    for old_name, new_name in namespaces.items():
        renamed = Renamer(entries).namespace(old_name)
        if renamed != new_name:
            raise ValueError(f"namespace row {old_name} conflicts with an enclosing namespace row")

    return len(entries), len(retired_tokens)


def split_private(name):
    """`_private.<module>.<counter>.<user name>` -> (module, counter, user name)."""
    if not name.startswith("_private."):
        return None
    parts = name.split(".")
    for i in range(1, len(parts)):
        if parts[i].isdigit():
            if i + 1 >= len(parts):
                break
            return ".".join(parts[1:i]), parts[i], ".".join(parts[i + 1:])
    raise ValueError(f"unsupported private name: {name}")


class Renamer:
    """The map as a function on compiler names.

    Exact rows (declaration, field, constructor, relocation) rename one name.
    A namespace row renames its name and every descendant by prefix; the
    longest enclosing namespace row applies, and an exact row wins over it.
    Private names keep their counter; their module prefix follows module rows
    and, for a relocated declaration, the row's target module.
    """

    def __init__(self, entries):
        self.exact, self.namespaces, self.modules, self.relocations = {}, {}, {}, {}
        self.public_from = {e["public_from"]: e["new"] for e in entries if "public_from" in e}
        for entry in entries:
            kind = entry["kind"]
            if kind == "module":
                self.modules[entry["old"]] = entry["new"]
            elif kind == "namespace":
                self.namespaces[entry["old"]] = entry["new"]
            else:
                self.exact[entry["old"]] = entry["new"]
                if kind == "relocation":
                    self.relocations[entry["old"]] = (entry["from_module"], entry["to_module"])

    def namespace(self, name):
        parts = name.split(".")
        for i in range(len(parts), 0, -1):
            prefix = ".".join(parts[:i])
            if prefix in self.namespaces:
                return ".".join([self.namespaces[prefix]] + parts[i:])
        return name

    def derived(self):
        """Namespaces renamed only through their members: every exact row whose
        old parent is P gives the same new parent P'. Ambiguous parents derive
        nothing (their syntax stays and spellings report)."""
        if not hasattr(self, '_derived'):
            parents = {}
            for old, new in self.exact.items():
                if old in self.relocations or "." not in old or "." not in new or old.startswith("_private."):
                    continue
                parents.setdefault(old.rsplit(".", 1)[0], []).append(new.rsplit(".", 1)[0])
            # Only a rename of the namespace's own last component (`Gloas.Inv` ->
            # `Gloas.Invariant`); a member moved deeper renames no namespace.
            self._derived = {}
            for parent, news in parents.items():
                # At least two member rows must agree; one moved member is not
                # evidence that the namespace itself is renamed.
                if len(news) < 2 or len(set(news)) != 1:
                    continue
                target = news[0]
                a, b = parent.split("."), target.split(".")
                if len(a) == len(b) and a[:-1] == b[:-1] and a[-1] != b[-1]:
                    self._derived[parent] = target
        return self._derived

    def scope(self, name):
        """A namespace as `namespace`/`open` syntax and lexical resolution see it:
        a namespace row, or else the exact row of the declaration that bears
        the namespace's name (the `B256` namespace follows the `B256` type)."""
        parts = name.split(".")
        for i in range(len(parts), 0, -1):
            prefix = ".".join(parts[:i])
            if prefix in self.namespaces:
                return ".".join([self.namespaces[prefix]] + parts[i:])
            if prefix in self.exact and prefix not in self.relocations:
                return ".".join([self.exact[prefix]] + parts[i:])
            if prefix in self.derived():
                return ".".join([self.derived()[prefix]] + parts[i:])
        return name

    def explain(self, name):
        """(new name, 'exact' | 'namespace' | 'unchanged')."""
        if name in self.public_from:
            return self.public_from[name], "exact"
        private = split_private(name)
        if private:
            module, counter, user = private
            new_user, how = self.explain(user)
            if user in self.relocations:
                source, target = self.relocations[user]
                if source != module:
                    raise ValueError(f"relocation row for {user} names module {source}, not {module}")
                module, how = target, "exact"
            elif module in self.modules:
                module, how = self.modules[module], how if how != "unchanged" else "module"
            return f"_private.{module}.{counter}.{new_user}", how
        if name in self.exact:
            return self.exact[name], "exact"
        renamed = self.namespace(name)
        return renamed, "namespace" if renamed != name else "unchanged"

    def __call__(self, name):
        return self.explain(name)[0]

    def renames(self, name):
        return self.explain(name)[1] != "unchanged"

    def module(self, name):
        return self.modules.get(name, name)

    def exact_ancestor(self, name):
        """A proper ancestor renamed by an exact row, which this name's own
        rename does not follow (descendants need their own rows)."""
        parts = name.split(".")
        for i in range(len(parts) - 1, 0, -1):
            prefix = ".".join(parts[:i])
            if prefix in self.exact and self.exact[prefix] != prefix:
                return prefix
        return None

    def words(self):
        """Identifier components whose spelling may change."""
        result = set()
        for old, new in list(self.exact.items()) + list(self.namespaces.items()):
            a, b = old.split("."), new.split(".")
            result.update(part for i, part in enumerate(a) if i >= len(b) or part != b[i])
        return result


def check_file(map_path=DEFAULT_MAP):
    """Load and validate a rename-map JSON file."""
    text = Path(map_path).read_text(encoding="utf-8")
    data = json.loads(text)
    return validate_map(data)


def main(argv=None):
    parser = argparse.ArgumentParser(description="Validate Jaune's rename map schema.")
    parser.add_argument("--map", type=Path, default=DEFAULT_MAP,
                        help="path to rename-map JSON (default: scripts/naming-map.json)")
    args = parser.parse_args(argv)
    try:
        entry_count, retired_count = check_file(args.map)
    except (OSError, json.JSONDecodeError) as error:
        print(f"SETUP — naming-map: {error}", file=sys.stderr)
        return 2
    except ValueError as error:
        print(f"REGRESSION — naming-map: {error}", file=sys.stderr)
        return 1
    print(f"OK — naming-map: {entry_count} entries, {retired_count} retired tokens, schema valid")
    return 0


if __name__ == "__main__":
    sys.exit(main())
