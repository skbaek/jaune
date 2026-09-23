#!/usr/bin/env python3
"""Check that the destination axiom rows and the assurance manifest agree.

Fails when a `#expect_axioms` row in the manifest's axiom file has no manifest
entry, when a manifest entry has no row, when a row's expected set differs from
its entry's, when either side repeats a declaration, or when a public rule of a
coverage module has no row. It reads source only; the Lean build decides whether
each row's set is the declaration's actual axiom closure.
"""
import importlib.util
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "scripts" / "assurance-manifest.json"
FIELDS = ("declaration", "expected_axioms", "origin", "original_check",
          "property", "destination_check", "downstream_check")

_spec = importlib.util.spec_from_file_location(
    "consumer_boundary", ROOT / "scripts" / "check-consumer-boundary.py")
_boundary = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_boundary)
source_text = _boundary.source_text

ROW = re.compile(r"#expect_axioms\s+(\S+)\s*\[([^\]]*)\]")
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?P<mods>(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*)"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|inductive|structure|opaque|axiom)\s+"
    r"(?P<name>[^\s:({\[]+)", re.M)
SCOPE = re.compile(r"^(namespace|end|section)\b\s*(\S*)", re.M)


def rows(path):
    """Declaration -> sorted expected set, from comment-stripped source."""
    found = {}
    for match in ROW.finditer(source_text(path)):
        name = match[1]
        if name in found:
            raise ValueError(f"duplicate #expect_axioms row: {name}")
        found[name] = sorted(a.strip() for a in match[2].split(",") if a.strip())
    return found


def public_rules(path):
    """Fully qualified public theorems/lemmas and Exec-valued defs of a module."""
    text = source_text(path)
    events = sorted([(m.start(), "scope", m) for m in SCOPE.finditer(text)] +
                    [(m.start(), "decl", m) for m in DECL.finditer(text)],
                    key=lambda e: e[0])
    stack, result = [], []
    starts = [m.start() for m in DECL.finditer(text)] + [len(text)]
    for pos, kind, match in events:
        if kind == "scope":
            word, arg = match[1], match[2]
            if word == "namespace":
                stack.append(("namespace", arg.split(".")))
            elif word == "section":
                stack.append(("section", []))
            elif stack:
                stack.pop()
            continue
        if "private" in match["mods"].split():
            continue
        if match["kind"] in ("axiom", "opaque"):
            raise ValueError(f"trust-surface declaration in coverage module: {match['name']}")
        end = min(s for s in starts if s > pos)
        header = re.split(r":=|\n\s*\|", text[pos:end], maxsplit=1)[0]
        rule = match["kind"] in ("theorem", "lemma") or (
            match["kind"] == "def" and re.search(r"\bExec\b", header))
        if rule:
            prefix = [p for _, parts in stack for p in parts]
            result.append(".".join(prefix + [match["name"]]))
    if stack:
        raise ValueError(f"unclosed namespace/section in {path.relative_to(ROOT)}")
    return result


def check(root=ROOT):
    manifest_path = root / "scripts" / "assurance-manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if manifest.get("schema") != "jaune-assurance-manifest/1":
        raise ValueError("unknown manifest schema")
    audited = rows(root / manifest["axiom_file"])
    entries = {}
    for entry in manifest["entries"]:
        missing = [f for f in FIELDS if f not in entry]
        if missing:
            raise ValueError(f"manifest entry {entry.get('declaration')} lacks {missing}")
        name = entry["declaration"]
        if name in entries:
            raise ValueError(f"duplicate manifest entry: {name}")
        if entry["origin"] == "carried" and not entry["original_check"]:
            raise ValueError(f"carried entry without original check: {name}")
        entries[name] = sorted(entry["expected_axioms"])
    only_rows = sorted(set(audited) - set(entries))
    only_entries = sorted(set(entries) - set(audited))
    if only_rows:
        raise ValueError("rows without manifest entry: " + ", ".join(only_rows))
    if only_entries:
        raise ValueError("manifest entries without row: " + ", ".join(only_entries))
    differing = sorted(n for n in audited if audited[n] != entries[n])
    if differing:
        raise ValueError("expected sets differ: " + ", ".join(differing))
    covered = 0
    for module in manifest["coverage_modules"]:
        rules = public_rules(root / module)
        if not rules:
            raise ValueError(f"coverage module declares no rule: {module}")
        unaudited = [r for r in rules if r not in audited]
        if unaudited:
            raise ValueError(f"public rules without row in {module}: " + ", ".join(unaudited))
        covered += len(rules)
    return len(audited), covered, len(manifest["coverage_modules"])


if __name__ == "__main__":
    if len(sys.argv) != 1:
        print("usage: scripts/check-assurance-manifest.py", file=sys.stderr)
        sys.exit(2)
    try:
        n, covered, modules = check()
    except (OSError, ValueError, KeyError, json.JSONDecodeError) as error:
        print(f"REGRESSION — assurance manifest: {error}", file=sys.stderr)
        sys.exit(1)
    print(f"OK — assurance manifest: {n} rows match {n} entries; "
          f"{covered} public rules in {modules} coverage modules all audited")
