#!/usr/bin/env python3
"""Generate the consensus-layer rows of scripts/naming-map.json (goal jaune-shape-and-names-v1, N5).

    consensus_map.py --tree . --specs SPECS_ROOT [SPECS_ROOT ...] [--write] [--report DIR]

1. Inventory every declaration, structure field, constructor and module of JauneConsensus/
   (consensus_inventory.py; a source survey, the compiler-resolved apply tool resolves uses).
2. Classify each name: pyspec-derived (the last component is a name the pinned pyspec text
   defines, verbatim or transliterated to camelCase) stays; Jaune-own names keep or change by token.
3. Jaune-own tokens that are not whole words get the expansion in consensus_names_data.py.
   A namespace rename gives every qualified descendant its own row (apply-tool rule).
4. Merge the `consensus` rows into scripts/naming-map.json, sorted by `old`, leaving other layers.
"""
import argparse
import collections
import json
import re
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
sys.path.insert(0, str(HERE.parent))
import consensus_inventory as inv  # noqa: E402
import consensus_names_data as D  # noqa: E402

TOKEN_RE = re.compile(r"[A-Z]+(?=[A-Z][a-z0-9]|$)|[A-Z]?[a-z0-9]+")


def snake(s):
    s = re.sub(r"([a-z0-9])([A-Z])", r"\1_\2", s)
    s = re.sub(r"([A-Z]+)([A-Z][a-z])", r"\1_\2", s)
    return s.lower()


class Namer:
    def __init__(self, api):
        self.api = api
        self.token_hits = collections.Counter()
        self.part_cache = {}
        self.upper_renamed = set()

    # ----- spec classification -------------------------------------------------------------
    # The namespaces that hold the spec port itself (functions and types of the pyspec).
    SPEC_NAMESPACES = ("JauneConsensus", "JauneConsensus.Gloas", "JauneConsensus.Gossip")

    def spec_source(self, q, kind):
        """Citation if the declaration is pyspec-derived, else None.

        function: namespace is a spec-port namespace and the snake_case form is a pyspec `def`;
        constant: UPPER_SNAKE name the pyspec (or its preset/config files) defines;
        type: UpperCamel name of a pyspec class or custom type in a spec-port namespace;
        field: the parent is a pyspec class that declares that field (or Config/Preset keys).
        """
        parent, _, last = q.rpartition(".")
        pe = lambda n: self.api.get(n)
        if kind == "field":
            pname = parent.rpartition(".")[2]
            if pname in ("Config", "Preset", "BlobScheduleEntry", "GasLimitScheduleEntry") and last == last.upper():
                e = pe(last)
                return f"{e['at']} ({last}, {pname} key)" if e else None
            cls = pe(pname)
            if cls and "class" in cls["kinds"] and last in self.fields.get(pname, {}):
                return f"{self.fields[pname][last]} ({last}, field of {pname})"
            return None
        if parent not in self.SPEC_NAMESPACES:
            return None
        if kind == "def" and last == last.upper() and pe(last) and any(k in ("const", "config") for k in pe(last)["kinds"]):
            return f"{pe(last)['at']} ({last}, constant)"
        if kind == "def":
            e = pe(snake(last))
            if e and "func" in e["kinds"]:
                return f"{e['at']} ({snake(last)}, snake_case transliteration)"
            return None
        if kind in ("structure", "inductive", "abbrev", "class"):
            e = pe(last)
            if e and any(k in ("class", "type") for k in e["kinds"]):
                return f"{e['at']} ({last}, verbatim)"
            if e and kind == "abbrev" and "const" in e["kinds"]:
                return None
        return None

    # ----- renaming ------------------------------------------------------------------------
    def rename_part(self, part):
        if part in self.part_cache:
            return self.part_cache[part]
        if part in D.PART_OVERRIDE:
            new = D.PART_OVERRIDE[part]
            self.part_cache[part] = new
            return new
        out, last = [], 0
        for m in TOKEN_RE.finditer(part):
            t = m.group()
            out.append(part[last:m.start()])
            last = m.end()
            key = t.lower()
            if t == "Tx":
                words = "transaction"
            elif t == "F" and m.start() > 0:
                words = "fork indexed"
            else:
                words = D.EXPAND.get(key)
            if not words:
                out.append(t)
                continue
            self.token_hits[key] += 1
            ws = words.split()
            first = ws[0][0].upper() + ws[0][1:] if t[0].isupper() else ws[0]
            out.append(first + "".join(w[0].upper() + w[1:] for w in ws[1:]))
        out.append(part[last:])
        new = "".join(out)
        self.part_cache[part] = new
        return new

    def rename_segment(self, seg):
        if seg in D.SEGMENT_OVERRIDE:
            return D.SEGMENT_OVERRIDE[seg]
        return "_".join(self.rename_part(p) for p in seg.split("_"))

    def rename_qualified(self, q, spec_last):
        segs = q.split(".")
        new = [self.rename_segment(s) for s in segs[:-1]]
        if q in D.LAST_OVERRIDE:
            new.append(D.LAST_OVERRIDE[q])
        elif spec_last:
            new.append(segs[-1])
        elif re.fullmatch(r"[A-Z][A-Z0-9]*(_[A-Z0-9]+)*", segs[-1]) and "_" in segs[-1]:
            # Jaune-own constant spelled like a pyspec constant: rule 7 gives it lowerCamel
            words = [w.lower() for w in segs[-1].split("_")]
            self.upper_renamed.add(segs[-1])
            new.append(self.rename_segment(words[0] + "".join(w[0].upper() + w[1:] for w in words[1:])))
        else:
            new.append(self.rename_segment(segs[-1]))
        return ".".join(new)


def kind_of(inv_kind):
    return {"field": "field", "constructor": "constructor"}.get(inv_kind, "declaration")


def load_inventory(tree):
    rows = []
    base = tree / "JauneConsensus"
    old_cwd = Path.cwd()
    import os
    os.chdir(tree)
    try:
        for path in sorted(Path("JauneConsensus").rglob("*.lean")):
            rows.extend(inv.scan(path))
    finally:
        os.chdir(old_cwd)
    return rows


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tree", default=".")
    ap.add_argument("--api", required=True, help="pyspec-api.json from pyspec_symbols.py")
    ap.add_argument("--map", default=None)
    ap.add_argument("--write", action="store_true")
    ap.add_argument("--report", default=None)
    args = ap.parse_args()
    tree = Path(args.tree).resolve()
    spec = json.load(open(args.api))
    namer = Namer(spec["api"])
    namer.fields = spec["fields"]

    rows = load_inventory(tree)
    entries = {}  # old -> entry
    stats = collections.Counter()
    kept = collections.defaultdict(list)
    anonymous = collections.Counter()
    for mod, line, kind, q, short in rows:
        if q == "<anonymous>":
            anonymous[mod] += 1
            continue
        last = q.split(".")[-1]
        spec = D.PROTOCOL_NAMES.get(last) if hasattr(D, "PROTOCOL_NAMES") else None
        spec_cite = namer.spec_source(q, kind) or spec
        # a declaration is only pyspec-derived if it is a structure/def/field... of the layer's own
        # spec port; Jaune-own definitions never get here with a matching spec name by accident
        # because `Facts`/`Harness` helper names are not spec names; the generator records the
        # citation so every claim can be checked.
        new = namer.rename_qualified(q, spec_cite is not None)
        key_group = "Facts" if ".Facts" in mod else "Harness" if ".Harness" in mod else "Core"
        if spec_cite is not None:
            stats[(key_group, "pyspec-derived", "kept" if new == q else "namespace-renamed")] += 1
        else:
            stats[(key_group, "jaune-own", "kept" if new == q else "renamed")] += 1
        kept[(key_group, "spec" if spec_cite else "own")].append((mod, line, kind, q, new, spec_cite))
        if new == q:
            continue
        old = q
        e = entries.get(old)
        if e is None:
            entries[old] = {"old": old, "new": new, "kind": kind_of(kind), "layer": "consensus",
                            "_mods": [f"{mod.replace('JauneConsensus.', '')}:{line}"],
                            "_spec": spec_cite}
        else:
            if e["new"] != new:
                raise SystemExit(f"conflicting renames for {old}: {e['new']} vs {new}")
            e["_mods"].append(f"{mod.replace('JauneConsensus.', '')}:{line}")

    # modules
    mod_rows = []
    for path in sorted((tree / "JauneConsensus").rglob("*.lean")):
        rel = path.relative_to(tree).with_suffix("")
        m = ".".join(rel.parts)
        n = ".".join(namer.rename_segment(s) for s in rel.parts)
        mod_rows.append((m, n))
        if m != n:
            entries[m] = {"old": m, "new": n, "kind": "module", "layer": "consensus", "_mods": [], "_spec": None}

    json.dump({"stats": {"/".join(k): v for k, v in stats.items()}}, sys.stderr)
    sys.stderr.write("\n")
    # write evidence
    if args.report:
        rep = Path(args.report)
        rep.mkdir(parents=True, exist_ok=True)
        with open(rep / "classification.tsv", "w") as f:
            for (grp, cls), items in sorted(kept.items()):
                for mod, line, kind, q, new, cite in items:
                    f.write("\t".join([grp, cls, mod.replace("JauneConsensus.", ""), str(line), kind, q, new, cite or ""]) + "\n")
        with open(rep / "token-hits.txt", "w") as f:
            for t, n in sorted(namer.token_hits.items()):
                f.write(f"{t}\t{n}\t{D.EXPAND.get(t)}\n")
        with open(rep / "kept-tokens.tsv", "w") as f:
            toks = collections.Counter()
            where = {}
            for items in kept.values():
                for mod, line, kind, q, new, cite in items:
                    if cite:
                        continue
                    for seg in new.split("."):
                        for part in seg.split("_"):
                            for tk in TOKEN_RE.findall(part):
                                toks[tk.lower()] += 1
                                where.setdefault(tk.lower(), new.replace("JauneConsensus.", ""))
            for tk, n in sorted(toks.items()):
                cat = ("lean" if tk in D.LEAN_TOKENS else "protocol" if tk in D.PROTOCOL_TOKENS else "word-unreviewed")
                f.write(f"{tk}\t{n}\t{cat}\t{where[tk]}\n")
        with open(rep / "anonymous-instances.txt", "w") as f:
            for m, n in sorted(anonymous.items()):
                f.write(f"{m}\t{n}\n")
        json.dump({"modules": mod_rows}, open(rep / "modules.json", "w"), indent=0)

    out = finalize(entries, namer, rows, kept)
    outdir = Path(args.report) if args.report else Path(".")
    json.dump(out, open(outdir / "entries.json", "w"), indent=1)
    problems = check(out, kept, tree)
    for p in problems:
        print("PROBLEM:", p, file=sys.stderr)
    print(f"{len(out)} changed consensus names; stats {dict(stats)}", file=sys.stderr)
    if args.write:
        if problems:
            raise SystemExit("refusing to write the map with problems")
        mp = Path(args.map or tree / "scripts" / "naming-map.json")
        data = json.load(open(mp))
        data["entries"] = [e for e in data["entries"] if e.get("layer") != "consensus"] + out
        data["entries"].sort(key=lambda e: (e["old"], e["layer"]))
        json.dump(data, open(mp, "w"), indent=2)
        open(mp, "a").write("\n")
        print(f"wrote {len(out)} consensus rows to {mp}", file=sys.stderr)


def part_pairs(old, new):
    pairs = []
    for a, b in zip(old.split("."), new.split(".")):
        for x, y in zip(a.split("_"), b.split("_")):
            if x != y:
                pairs.append(f"{x}>{y}")
    return pairs


def finalize(entries, namer, rows, kept):
    out = []
    for old in sorted(entries):
        e = entries[old]
        new = e["new"]
        pairs = part_pairs(old, new) if e["kind"] != "module" else part_pairs(old, new)
        low = old.lower()
        if "b256" in low:
            rule, source = "1, 6", "pyspec Bytes32 (ssz/simple-serialize.md); Jaune's B256 is retired (rule 6, one concept one name)"
        elif re.search(r"(^|[._])(g30[1-7]|b[1357])($|[._])", old) or "B5" in old or "StepB" in old or "WithdrawalsB5" in old:
            rule, source = "4", "Plain English (rule 4); the invariant or statement named in the declaration's own doc comment"
        elif re.search(r"Tx", old) and "Tx" not in new:
            rule, source = "6", "Plain English (rule 4); one concept one name with the execution layer's Tx to Transaction (rule 6)"
        else:
            rule, source = "5, 4", "Plain English (rule 4)"
        entry = {"old": old, "new": new, "kind": e["kind"], "layer": "consensus", "rule": rule, "source": source}
        notes = []
        if pairs:
            notes.append("parts: " + ", ".join(sorted(set(pairs))))
        mods = e.get("_mods", [])
        if len(set(m.split(":")[0] for m in mods)) > 1:
            notes.append("private or repeated name declared in modules: " + ", ".join(sorted(set(m.split(":")[0] for m in mods))))
        if e.get("_spec"):
            notes.append("pyspec-derived last component kept; a renamed namespace gives this row (" + e["_spec"] + ")")
        if notes:
            entry["notes"] = "; ".join(notes)
        out.append(entry)
    return out


def check(out, kept, tree):
    problems = []
    import check_naming_map_shim as shim
    data = json.load(open(tree / "scripts" / "naming-map.json"))
    retired = data["retired_tokens"]
    news = collections.Counter(e["new"] for e in out)
    olds = {e["old"] for e in out}
    for n, c in news.items():
        if c > 1:
            problems.append(f"duplicate new name {n}")
    existing = set()
    for items in kept.values():
        for mod, line, kind, q, new, cite in items:
            existing.add(q)
    for e in out:
        if e["kind"] == "module":
            continue
        if e["new"] in existing and e["new"] not in olds:
            problems.append(f"new name {e['new']} (from {e['old']}) collides with an unchanged declaration")
    # unchanged and changed names must not carry retired tokens
    for items in kept.values():
        for mod, line, kind, q, new, cite in items:
            hits = shim.find_retired_tokens(new, retired)
            if hits:
                problems.append(f"retired token {hits} in {new} (from {q})")
    return problems


if __name__ == "__main__":
    main()
