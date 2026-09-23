#!/usr/bin/env python3
"""Check execution-library and ambient-example import connectivity without Lean."""
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
# These modules implement the canonical execution surface. A dropped umbrella
# import must not silently remove that surface from the default library build.
EXECUTION_MODULES = {
    "Jaune.ExecFrame", "Jaune.Exec", "Jaune.ExecDeriv",
    "Jaune.ExecSettlement", "Jaune.ExecChronology",
    "Jaune.MessageExecution", "Jaune.SymbolicPush", "Jaune.SymbolicArith",
}


def source_text(path):
    """Remove nested Lean comments, preserving newlines and quoted strings."""
    text = path.read_text(encoding="utf-8")
    out, i, depth, quoted = [], 0, 0, False
    while i < len(text):
        pair = text[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif quoted:
            out.append(text[i])
            if text[i] == "\\" and i + 1 < len(text):
                i += 1
                out.append(text[i])
            elif text[i] == '"':
                quoted = False
            i += 1
        elif pair == "/-":
            out.append(" ")
            depth = 1
            i += 2
        elif pair == "--":
            end = text.find("\n", i)
            i = len(text) if end < 0 else end
        else:
            quoted = text[i] == '"'
            out.append(text[i])
            i += 1
    if depth or quoted:
        raise ValueError(f"unterminated comment/string: {path.relative_to(ROOT)}")
    return "".join(out)


def imports(path):
    result = []
    for line in source_text(path).splitlines():
        if re.match(r"\s*(?:(?:public|private|meta)\s+)*import\b", line):
            match = re.fullmatch(
                r"\s*(?:(?:public|private|meta)\s+)*import\s+"
                r"([A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*)\s*", line)
            if not match:
                raise ValueError(f"unsupported import syntax: {path.relative_to(ROOT)}: {line}")
            result.append(match[1])
    return result


def check():
    paths = [ROOT / "Jaune.lean", ROOT / "Examples.lean"]
    for directory in ("Jaune", "Examples"):
        if not (ROOT / directory).is_dir():
            raise ValueError(f"missing source tree: {directory}")
        paths.extend(sorted((ROOT / directory).rglob("*.lean")))
    graph = {}
    for path in paths:
        module = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        graph[module] = imports(path)
        for dependency in graph[module]:
            if dependency.split(".")[0] in {"Blanc", "Creme", "creme"}:
                raise ValueError(f"forbidden dependency: {module} imports {dependency}")

    def closure(root):
        seen, pending = set(), [root]
        while pending:
            module = pending.pop()
            if module in seen:
                continue
            seen.add(module)
            if module not in graph:
                raise ValueError(f"missing local module: {module}")
            pending.extend(d for d in graph[module]
                           if d.split(".")[0] in {"Jaune", "Examples"})
        return seen

    library = closure("Jaune")
    missing = EXECUTION_MODULES - library
    if missing:
        raise ValueError("unreachable execution modules: " + ", ".join(sorted(missing)))
    if any(m.startswith("Examples") for m in library):
        raise ValueError("production library imports consumer examples")
    examples = {m for m in graph if m.startswith("Examples.")}
    if not examples:
        raise ValueError("no consumer examples")
    missing = examples - closure("Examples")
    if missing:
        raise ValueError("unreachable examples: " + ", ".join(sorted(missing)))
    # The maintained Lake declaration is intentionally simple and checked
    # structurally: unrecognized registration fails rather than being guessed.
    lakefile = source_text(ROOT / "lakefile.lean")
    for name in ("Jaune", "Examples"):
        if not re.search(r"@\[default_target\]\s*lean_lib\s+(?:«" + name + r"»|" + name + r")\s+where\b", lakefile):
            raise ValueError(f"missing default library registration: {name}")
    print(f"OK — consumer boundary: {len(EXECUTION_MODULES)} execution modules reachable; "
          f"{len(examples)} examples reachable; source imports independent of Blanc/Creme")


if __name__ == "__main__":
    if len(sys.argv) != 1:
        sys.exit("usage: python3 scripts/check-consumer-boundary.py")
    try:
        check()
    except (OSError, ValueError) as error:
        print(f"REGRESSION — consumer boundary: {error}", file=sys.stderr)
        sys.exit(1)
