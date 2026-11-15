#!/usr/bin/env python3
"""Extract pyspec API names from consensus-specs checkouts, with citations.

Usage: pyspec_symbols.py SPECS_ROOT [SPECS_ROOT ...] > pyspec-api.json

`api` maps each name to the first `checkout/file:line` that defines it:
  * python function names (`def name(`) and class names (`class Name(`) of the spec markdown,
  * fields of spec classes (`    name: Type` inside a class),
  * constants (`NAME = ...`, `NAME: T = ...`, and table rows `| `NAME` |`),
  * preset and config YAML keys.
Local variables and arbitrary identifiers are NOT included: membership here is a claim that
the spec itself defines the name.
"""
import json
import re
import sys
from pathlib import Path


def main():
    api = {}
    fields = {}
    cur_class = None

    def add(name, where, kind):
        e = api.setdefault(name, {"kinds": [], "at": where})
        if kind not in e["kinds"]:
            e["kinds"].append(kind)

    for root in map(Path, sys.argv[1:]):
        for md in sorted((root / "specs").rglob("*.md"), key=lambda p: ("_features" in p.parts, str(p))):
            rel = f"{root.name}/{md.relative_to(root)}"
            in_code = in_class = False
            for n, line in enumerate(md.read_text().split("\n"), 1):
                if line.startswith("```"):
                    in_code = (not in_code) and line.strip().startswith("```python")
                    in_class = False
                    continue
                if in_code:
                    m = re.match(r"class (\w+)[(:]", line)
                    if m:
                        cur_class = m.group(1)
                        add(m.group(1), f"{rel}:{n}", "class")
                        in_class = True
                        continue
                    if line and not line.startswith((" ", "\t")):
                        in_class = False
                    m = re.match(r"def (\w+)\(", line)
                    if m:
                        add(m.group(1), f"{rel}:{n}", "func")
                    if in_class:
                        m = re.match(r"    (\w+): ", line)
                        if m:
                            add(m.group(1), f"{rel}:{n}", "field")
                            fields.setdefault(cur_class, set()).add(m.group(1))
                    m = re.match(r"([A-Z][A-Z0-9_]+) ?[:=]", line)
                    if m:
                        add(m.group(1), f"{rel}:{n}", "const")
                else:
                    for m in re.finditer(r"\|\s*`([A-Za-z][A-Za-z0-9_]*)`\s*\|", line):
                        nm = m.group(1)
                        add(nm, f"{rel}:{n}", "const" if nm.isupper() or "_" in nm and nm.upper() == nm else "type")
        for y in sorted(list((root / "presets").rglob("*.yaml")) + list((root / "configs").glob("*.yaml"))):
            rel = f"{root.name}/{y.relative_to(root)}"
            for n, line in enumerate(y.read_text().split("\n"), 1):
                m = re.match(r"([A-Za-z_][A-Za-z0-9_]*):", line)
                if m:
                    add(m.group(1), f"{rel}:{n}", "config")
    json.dump({"api": api, "fields": {k: sorted(v) for k, v in fields.items()}}, sys.stdout, indent=0, sort_keys=True)


main()
