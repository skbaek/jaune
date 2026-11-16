#!/usr/bin/env python3
"""Textual inventory of every declaration, structure field and constructor in
JauneConsensus/ (goal jaune-shape-and-names-v1, map row source for G0a).

Output: TSV  module, line, kind, qualified-name, short-name
This is a source survey, not a compiler walk: it tracks `namespace`/`section`/`end`,
declaration keywords, structure fields and inductive constructors.  Names produced
by `deriving`, auto-generated instance names and macro-generated declarations are
not listed (the rename tool is compiler-resolved and handles those; they are
derived from the names listed here).
"""
import re
import sys
from pathlib import Path

ROOT = Path(sys.argv[1] if len(sys.argv) > 1 else "JauneConsensus")

MODS = r"(?:(?:private|protected|noncomputable|partial|unsafe|scoped|local|nonrec)\s+)*"
ATTR = r"(?:@\[[^\]]*\]\s*)*"
DECL = re.compile(r"^(?P<ind>\s*)" + ATTR + MODS +
                  r"(?P<kw>def|theorem|lemma|abbrev|instance|structure|class inductive|class|inductive|opaque|axiom|macro|elab|syntax|notation|abbrev)\s+(?P<rest>.*)$")
NS = re.compile(r"^namespace\s+(\S+)")
SEC = re.compile(r"^section(?:\s+(\S+))?\s*$")
END = re.compile(r"^end(?:\s+(\S+))?\s*$")
NAME = re.compile(r"^([A-Za-z_Ͱ-Ͽᴀ-ᶿ℀-⅏][A-Za-z0-9_'!?Ͱ-Ͽᴀ-ᶿ₀-ₜ.]*)")
FIELD = re.compile(r"^(\s+)(?:\(|\{|\[)?([A-Za-z_][A-Za-z0-9_'!?]*(?:\s+[A-Za-z_][A-Za-z0-9_'!?]*)*)\s*(?::|:=)")
CTOR = re.compile(r"^(\s*)\|\s+([A-Za-z_][A-Za-z0-9_'!?.]*)")
# Further constructors on the same line: `| a | b | c` (a constructor without arguments).
CTOR_MORE = re.compile(r"\|\s+([A-Za-z_][A-Za-z0-9_'!?.]*)")
# `mutual ... end` opens a scope whose bare `end` must not close an enclosing section.
MUTUAL = re.compile(r"^mutual\s*$")


def strip_comments(text):
    out = []
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and text.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth:
            out.append("\n" if text[i] == "\n" else " ")
            i += 1
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                i += 1
            continue
        out.append(text[i])
        i += 1
    return "".join(out)


def scan(path):
    mod = ".".join(path.with_suffix("").parts)
    text = strip_comments(path.read_text())
    stack = []  # (kind, name-or-None, ns-components)
    ns = []
    rows = []
    cur = None  # (kind, qname) of an open structure/inductive/class
    in_fields = False  # structure/class: past the `where` that ends the header (params are not fields)
    for lineno, line in enumerate(text.split("\n"), 1):
        if not line.strip():
            continue
        m = NS.match(line)
        if m:
            comps = m.group(1).split(".")
            stack.append(("ns", comps))
            ns.extend(comps)
            cur = None
            continue
        if MUTUAL.match(line):
            stack.append(("mutual", None))
            cur = None
            continue
        m = SEC.match(line)
        if m:
            stack.append(("sec", [m.group(1)] if m.group(1) else None))
            cur = None
            continue
        m = END.match(line)
        if m:
            if stack:
                k, comps = stack.pop()
                if k == "ns":
                    del ns[-len(comps):]
            cur = None
            continue
        m = DECL.match(line)
        if m and m.group("ind") == "":
            kw = m.group("kw")
            rest = m.group("rest")
            nm = NAME.match(rest)
            name = nm.group(1) if nm else None
            if kw in ("instance", "macro", "elab", "syntax", "notation"):
                if kw == "instance" and name and not name.startswith("["):
                    pass
                else:
                    name = None
            if name is None:
                cur = None
                if kw == "instance":
                    rows.append((mod, lineno, "instance", "<anonymous>", "<anonymous>"))
                continue
            if name.startswith("_root_."):
                q = name[len("_root_."):]
            else:
                q = ".".join(ns + [name])
            rows.append((mod, lineno, kw, q, name))
            cur = (kw, q) if kw in ("structure", "class", "inductive", "class inductive") else None
            in_fields = bool(cur) and cur[0] in ("structure", "class") and rest.rstrip().endswith("where")
            continue
        if cur:
            kw, q = cur
            if kw in ("inductive", "class inductive"):
                m = CTOR.match(line)
                if m:
                    # `| a | b | c`: every constructor on the line (arguments, if any, follow
                    # the last one; a `|` inside parentheses is not a constructor bar).
                    depth, flat = 0, []
                    for ch in line:
                        depth += ch in "([{"
                        depth -= ch in ")]}"
                        flat.append(ch if depth == 0 else " ")
                    for name in CTOR_MORE.findall("".join(flat)):
                        rows.append((mod, lineno, "constructor", q + "." + name, name))
            else:
                if not in_fields:
                    if line.rstrip().endswith("where"):
                        in_fields = True
                    continue
                m = FIELD.match(line)
                if m and not line.lstrip().startswith(("deriving", "extends")):
                    for f in m.group(2).split():
                        rows.append((mod, lineno, "field", q + "." + f, f))
        if cur and not line.startswith((" ", "\t", "|")):
            cur = None
    return rows


def main():
    for path in sorted(ROOT.rglob("*.lean")):
        for row in scan(path):
            print("\t".join(map(str, row)))


if __name__ == "__main__":
    main()
