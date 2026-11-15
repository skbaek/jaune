#!/usr/bin/env python3
"""Validate Jaune's machine-readable rename map (scripts/naming-map.json)."""
import argparse
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_MAP = ROOT / "scripts" / "naming-map.json"
VALID_KINDS = frozenset({"declaration", "field", "constructor", "module", "relocation"})
VALID_LAYERS = frozenset({"execution", "consensus", "adapter"})
VALID_RULES = frozenset({"1", "2", "3", "4", "5", "6", "7"})
REQUIRED_FIELDS = ("old", "new", "kind", "layer", "rule", "source")
OPTIONAL_FIELDS = ("notes",)
ALLOWED_ENTRY_FIELDS = frozenset(REQUIRED_FIELDS + OPTIONAL_FIELDS)
TOKEN_RE = re.compile(r"[A-Z]+(?=[A-Z][a-z0-9]|$)|[A-Z]?[a-z0-9]+")


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

    seen_old = set()
    seen_new = set()
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
        if old_name == new_name:
            raise ValueError(f"entry {index} maps '{old_name}' to itself")
        if entry["kind"] not in VALID_KINDS:
            raise ValueError(f"entry {index} invalid kind: {entry['kind']!r}")
        if entry["layer"] not in VALID_LAYERS:
            raise ValueError(f"entry {index} invalid layer: {entry['layer']!r}")
        _parse_rules(entry["rule"])

        if old_name in seen_old:
            raise ValueError(f"duplicate old name: {old_name}")
        if new_name in seen_new:
            raise ValueError(f"duplicate new name: {new_name}")
        seen_old.add(old_name)
        seen_new.add(new_name)

        retired_hits = find_retired_tokens(new_name, retired_tokens)
        if retired_hits:
            raise ValueError(
                f"entry {index} new name '{new_name}' contains retired token(s): "
                + ", ".join(sorted(set(retired_hits)))
            )

    return len(entries), len(retired_tokens)


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
