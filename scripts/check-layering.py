#!/usr/bin/env python3
"""Check the module layering of Jaune (goal jaune-shape-and-names-v1, S0).

Every Jaune module is classified in `scripts/layering.json` as one of
specification, proof, check, adapter, implementation or bridge. The check fails

* on a module that is not classified, or a classification with no module;
* on a `#guard` (any `#guard_*` form, `#guard_msgs` included), `#eval`,
  `#reduce`, `#synth` or `example` command, or on a test helper (a declaration
  whose name says guard, fixture, golden or probe), in a specification module.
  Commands and declarations are found at any indentation and behind modifiers,
  attributes, doc comments and `set_option ... in` / `open ... in` prefixes;
* on a fixture-vocabulary declaration (a rejection tag or renderer) in a
  specification module that `fixture_vocabulary_residue` does not list. The
  residue is the vocabulary that specification functions still call; it only
  shrinks;
* on an import of an implementation module by a specification module that
  `implementation_imports` does not register, and on a registered import that is
  absent (the cached driver must sit below `exec`);
* on an import that points the wrong way: specification imports only
  specification, proof imports specification and proof, implementation and bridge
  import anything but check and adapter modules, check and adapter import any;
* on a check, adapter or implementation module that the default build's targets
  do not reach, on an umbrella root that declares anything, and on an import by
  the `Jaune` umbrella (the library a consumer imports) of anything but
  specification, proof and bridge modules. Imports are read in every header form
  (`public`, `meta`, `import all`).

It reads source and `lakefile.lean` only. Usage:
    python3 scripts/check-layering.py [--root DIR]
"""
import importlib.util
import json
from pathlib import Path
import re
import sys

HERE = Path(__file__).resolve().parent
_spec = importlib.util.spec_from_file_location(
    "consumer_boundary", HERE / "check-consumer-boundary.py")
_boundary = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(_boundary)
source_text = _boundary.source_text

CLASSES = ("specification", "proof", "check", "adapter", "implementation", "bridge")
# importer class -> classes it may import. Implementation modules a specification
# module may import are registered one by one in `implementation_imports`.
ALLOWED = {
    "specification": {"specification"},
    "proof": {"specification", "proof"},
    "implementation": {"specification", "proof", "implementation"},
    "bridge": {"specification", "proof", "implementation", "bridge"},
    "check": set(CLASSES),
    "adapter": set(CLASSES),
}
# The `Jaune` umbrella is the library a consumer imports: it reaches only
# specification, proof and bridge modules directly (implementation modules only
# through a registered specification import). Other umbrellas are unrestricted.
UMBRELLA_ALLOWED = {"Jaune": {"specification", "proof", "bridge"}}
FORBIDDEN_COMMANDS = ("#guard", "#guard_msgs", "#eval", "#reduce", "#synth", "example")
HELPER_NAME = re.compile(r"Guard|guard[A-Z]|[Ff]ixture|[Gg]olden|[Pp]robe")
# A renderer is `render` or a camel-case `renderThing`, at the top level or as
# the last component of a namespaced name; `Foo.render_lemma` is a statement
# about a renderer, not vocabulary.
VOCAB_NAME = re.compile(r"(?:Tags?|\.tag|^render\w*|\.render(?:[A-Z]\w*)?)$")
# What may precede a command or declaration keyword on its line or the lines
# before it: indentation, `set_option ... in` / `open ... in`, attributes and
# modifiers. Comments (doc comments included) are already blanked by source_text.
_LEAD = r"^[ \t]*(?:(?:set_option|open)\b[^\n]*?\bin\s+)*(?:@\[[^\]]*\]\s*)*"
_MODS = r"(?:(?:private|protected|public|noncomputable|nonrec|partial|unsafe|meta)\s+)*"
DECL = re.compile(
    _LEAD + r"(?P<mods>" + _MODS + r")"
    r"(?P<kind>theorem|lemma|def|abbrev|instance|inductive|structure|class|opaque|axiom)\s+"
    r"(?P<name>[^\s:({\[]+)", re.M)
SCOPE = re.compile(r"^[ \t]*(namespace|end|section|mutual)\b[ \t]*(\S*)", re.M)
COMMAND = re.compile(_LEAD + _MODS + r"(#guard\w*|#eval|#reduce|#synth|example)\b", re.M)
IMPORT = re.compile(
    r"^[ \t]*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?(\S+)\s*$", re.M)
TOP_DECL = re.compile(
    _LEAD + _MODS +
    r"(?:theorem|lemma|def|abbrev|instance|inductive|structure|class|opaque|axiom"
    r"|#guard\w*|#eval|#reduce|#synth|example|variable)\b", re.M)


def module_name(root, path):
    return ".".join(path.relative_to(root).with_suffix("").parts)


def local_modules(root):
    """Module name -> path for the classified source tree."""
    found = {}
    for name in ("Jaune.lean", "Examples.lean", "JauneChecks.lean", "Main.lean",
                 "MemoryProbe.lean", "TraceMain.lean"):
        if (root / name).is_file():
            found[module_name(root, root / name)] = root / name
    for directory in ("Jaune", "Examples"):
        if (root / directory).is_dir():
            for path in sorted((root / directory).rglob("*.lean")):
                found[module_name(root, path)] = path
    return found


def imports_of(path):
    return [i.replace("«", "").replace("»", "") for i in IMPORT.findall(source_text(path))]


def declarations(text):
    """(qualified name, kind, private) for each declaration of comment-stripped text."""
    events = sorted([(m.start(), "scope", m) for m in SCOPE.finditer(text)] +
                    [(m.start(), "decl", m) for m in DECL.finditer(text)],
                    key=lambda e: e[0])
    stack, result = [], []
    for _, kind, match in events:
        if kind == "scope":
            word, arg = match[1], match[2]
            if word == "namespace":
                stack.append(("namespace", arg.split(".") if arg else []))
            elif word in ("section", "mutual"):
                stack.append((word, []))
            elif stack:
                stack.pop()
            continue
        prefix = [p for _, parts in stack for p in parts]
        private = "private" in match["mods"].split()
        qualified = ".".join(prefix + [match["name"]])
        result.append((qualified[len("Jaune."):] if qualified.startswith("Jaune.") else qualified,
                       match["kind"], private))
    return result


def lake_targets(root):
    """Default-target roots: [(srcDir, [root module, ...])]."""
    text = source_text(root / "lakefile.lean")
    targets = []
    blocks = re.split(r"(?m)^(?=@\[default_target\])", text)
    for block in blocks[1:]:
        head = re.match(r"@\[default_target\]\s*(lean_lib|lean_exe)\s+(?:«([^»]+)»|(\w+))", block)
        if not head:
            continue
        nxt = re.search(r"(?m)^(?:@\[|lean_lib|lean_exe|/--)", block[head.end():])
        body = block[:head.end() + nxt.start()] if nxt else block
        name = head.group(2) or head.group(3)
        src = re.search(r'srcDir\s*:=\s*"([^"]*)"', body)
        src_dir = src.group(1) if src else "."
        if head.group(1) == "lean_exe":
            r = re.search(r"root\s*:=\s*`(\S+)", body)
            targets.append((src_dir, [r.group(1) if r else "Main"]))
        else:
            r = re.search(r"roots\s*:=\s*#\[([^\]]*)\]", body)
            roots = re.findall(r"`([\w.]+)", r.group(1)) if r else [name]
            targets.append((src_dir, roots))
    return targets


def reachable(root, modules):
    graph = {m: imports_of(p) for m, p in modules.items()}
    seen, pending = set(), []
    for src_dir, roots in lake_targets(root):
        for r in roots:
            if r in modules:
                pending.append(r)
    while pending:
        m = pending.pop()
        if m in seen or m not in graph:
            continue
        seen.add(m)
        pending.extend(graph[m])
    return seen


def check(root):
    root = Path(root)
    data = json.loads((root / "scripts" / "layering.json").read_text(encoding="utf-8"))
    problems = []
    classes = data["modules"]
    umbrellas = set(data["umbrellas"])
    registered = {(r["importer"], r["imported"]) for r in data["implementation_imports"]}
    residue = {n for names in data["fixture_vocabulary_residue"].values() for n in names}
    modules = local_modules(root)
    for m in sorted(set(modules) - set(classes) - umbrellas):
        problems.append(f"unclassified module: {m}")
    for m in sorted((set(classes) | umbrellas) - set(modules)):
        problems.append(f"classified module has no source file: {m}")
    for m, c in sorted(classes.items()):
        if c not in CLASSES:
            problems.append(f"{m}: unknown class {c!r}")
    used = set()
    for m, path in sorted(modules.items()):
        text = source_text(path)
        deps = imports_of(path)
        if m in umbrellas:
            stripped = IMPORT.sub("", text)
            if TOP_DECL.search(stripped):
                problems.append(f"{m}: umbrella root declares something")
            allowed = UMBRELLA_ALLOWED.get(m)
            for d in deps if allowed is not None else ():
                dc = classes.get(d)
                if dc is not None and dc not in allowed:
                    problems.append(f"{m} (umbrella) imports {d} ({dc})")
            continue
        cls = classes.get(m)
        if cls not in CLASSES:
            continue
        for d in deps:
            dc = classes.get(d)
            if dc is None:
                if d in umbrellas:
                    if cls not in ("check", "adapter"):
                        problems.append(f"{m} ({cls}) imports the umbrella root {d}")
                continue
            if cls == "specification" and dc == "implementation":
                if (m, d) in registered:
                    used.add((m, d))
                else:
                    problems.append(
                        f"{m}: specification module imports implementation module {d} "
                        f"(not in implementation_imports)")
            elif dc not in ALLOWED[cls]:
                problems.append(f"{m} ({cls}) imports {d} ({dc})")
        if cls == "specification":
            for match in COMMAND.finditer(text):
                line = text.count("\n", 0, match.start(1)) + 1
                problems.append(f"{m}:{line}: {match.group(1)} in a specification module")
            for name, kind, private in declarations(text):
                last = name.split(".")[-1]
                if HELPER_NAME.search(last):
                    problems.append(f"{m}: test helper in a specification module: {name}")
                if VOCAB_NAME.search(name) and name not in residue:
                    problems.append(
                        f"{m}: fixture vocabulary not in fixture_vocabulary_residue: {name}")
    for pair in sorted(registered - used):
        problems.append(f"registered implementation import absent: {pair[0]} -> {pair[1]}")
    reach = reachable(root, modules)
    for m, c in sorted(classes.items()):
        if c in ("check", "adapter", "implementation") and m in modules and m not in reach:
            problems.append(f"{m} ({c}) is not reached by a default build target")
    return problems, classes


def main(argv):
    root = HERE.parent
    if argv[:1] == ["--root"] and len(argv) == 2:
        root = Path(argv[1])
    elif argv:
        sys.exit("usage: python3 scripts/check-layering.py [--root DIR]")
    try:
        problems, classes = check(root)
    except (OSError, ValueError, KeyError) as error:
        print(f"REGRESSION — layering: {error}", file=sys.stderr)
        return 1
    if problems:
        for p in problems:
            print(f"LAYERING — {p}", file=sys.stderr)
        print(f"REGRESSION — layering: {len(problems)} problem(s)", file=sys.stderr)
        return 1
    counts = {c: sum(1 for v in classes.values() if v == c) for c in CLASSES}
    summary = ", ".join(f"{n} {c}" for c, n in counts.items())
    print(f"OK — layering: {len(classes)} modules classified ({summary})")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
