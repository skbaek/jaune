#!/usr/bin/env python3
"""Generate the consensus preset and config records from the pinned pyspec.

Reads ``presets/{minimal,mainnet}/<fork>.yaml`` for the forks phase0 through
fulu, and ``configs/{minimal,mainnet}.yaml``, from an
``ethereum/consensus-specs`` checkout at the tag commit recorded in
``scripts/consensus-vectors.json`` (``v1.6.1``), and writes:

* ``JauneConsensus/Preset.lean``: ``structure Preset`` (one field per preset
  variable, spec spelling) and ``Preset.minimal`` / ``Preset.mainnet``;
* ``JauneConsensus/Config.lean``: ``structure Config`` (one field per config
  variable that ``specs/{phase0..fulu}`` mention, spec spelling, plus
  ``PRESET_BASE``; ``BLOB_SCHEDULE`` as a list of entries) and
  ``Config.minimal`` / ``Config.mainnet``;
* ``JauneConsensus/Harness/ConfigOverride.lean``: one typed setter per config
  field, used by the runner to apply a vector case's ``config.yaml``.

Config variables no phase0..fulu spec file mentions (Gloas and feature-fork
versions, epochs and timings, ``CONFIG_NAME``) are left out and listed in the
generated header; a case ``config.yaml`` naming one is refused.

Field types follow the value form, identically in both presets: a decimal is
``Nat``; ``0x`` + 4 bytes is ``Bytes`` (``Version``, ``DomainType``); 20 bytes
is ``Adr`` (``ExecutionAddress``); 32 bytes is ``B256`` (``Hash32``); a quoted
string is ``String``. The YAML files are read by a small strict parser for the
subset they use; anything else fails.

Usage (run with ``python3 -I``)::

    python3 -I scripts/consensus-preset-generate.py [--specs DIR] [--check]

``--check`` regenerates in memory and fails if any committed file differs.
Exit status: 0 on success, 1 on a parse, pin or ``--check`` failure.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
REPO = os.path.dirname(HERE)
PRESETS = ("minimal", "mainnet")
FORKS = ("phase0", "altair", "bellatrix", "capella", "deneb", "electra", "fulu")
OUT_PRESET = os.path.join(REPO, "JauneConsensus", "Preset.lean")
OUT_CONFIG = os.path.join(REPO, "JauneConsensus", "Config.lean")
OUT_OVERRIDE = os.path.join(REPO, "JauneConsensus", "Harness", "ConfigOverride.lean")

KEY_RE = re.compile(r"^([A-Z][A-Z0-9_]*):(?: (.*))?$")


def fail(msg: str) -> "NoReturn":  # type: ignore[name-defined]
    print(f"consensus-preset-generate: FAIL: {msg}", file=sys.stderr)
    sys.exit(1)


def strip_comment(line: str) -> str:
    i = line.find("#")
    if i == 0 or (i > 0 and line[i - 1] == " "):
        line = line[:i]
    elif i > 0:
        fail(f"'#' inside a value: {line!r}")
    return line.rstrip()


def parse_value(raw: str, where: str):
    if re.fullmatch(r"[0-9]+", raw):
        if len(raw) > 1 and raw[0] == "0":
            fail(f"{where}: leading zero {raw!r}")
        return ("nat", int(raw))
    m = re.fullmatch(r"0x([0-9a-fA-F]*)", raw)
    if m:
        h = m.group(1)
        if len(h) % 2:
            fail(f"{where}: odd hex {raw!r}")
        n = len(h) // 2
        kind = {4: "bytes4", 20: "adr", 32: "b256"}.get(n)
        if kind is None:
            fail(f"{where}: hex of {n} bytes has no type")
        return (kind, h.lower())
    m = re.fullmatch(r"'([a-z0-9_]+)'", raw)
    if m:
        return ("string", m.group(1))
    fail(f"{where}: unsupported value {raw!r}")


def parse_yaml(path: str) -> list[tuple[str, object]]:
    """Ordered ``(key, value)`` pairs; ``BLOB_SCHEDULE`` becomes a list of
    ``(epoch, max_blobs)``."""
    with open(path, encoding="ascii") as f:
        lines = [strip_comment(l.rstrip("\n")) for l in f]
    out: list[tuple[str, object]] = []
    i = 0
    while i < len(lines):
        line = lines[i]
        i += 1
        if not line:
            continue
        if line.startswith(" "):
            fail(f"{path}: unexpected indentation: {line!r}")
        m = KEY_RE.match(line)
        if not m:
            fail(f"{path}: unparsed line {line!r}")
        key, raw = m.group(1), (m.group(2) or "").strip()
        if any(k == key for k, _ in out):
            fail(f"{path}: duplicate key {key}")
        if key == "BLOB_SCHEDULE":
            entries: list[tuple[int, int]] = []
            if raw == "[]":
                pass
            elif raw == "":
                while i + 1 < len(lines) and lines[i].startswith("  - "):
                    a = re.fullmatch(r"  - EPOCH: ([0-9]+)", lines[i])
                    b = re.fullmatch(r"    MAX_BLOBS_PER_BLOCK: ([0-9]+)", lines[i + 1])
                    if not a or not b:
                        fail(f"{path}: bad BLOB_SCHEDULE entry at line {i + 1}")
                    entries.append((int(a.group(1)), int(b.group(1))))
                    i += 2
                if not entries:
                    fail(f"{path}: empty block BLOB_SCHEDULE")
            else:
                fail(f"{path}: bad BLOB_SCHEDULE value {raw!r}")
            out.append((key, ("schedule", entries)))
        else:
            if raw == "":
                fail(f"{path}: empty value for {key}")
            out.append((key, parse_value(raw, f"{path}:{key}")))
    return out


def sha256(path: str) -> str:
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


LEAN_TYPE = {"nat": "Nat", "bytes4": "Bytes", "adr": "Adr", "b256": "B256",
             "string": "String", "schedule": "List BlobScheduleEntry"}


def lean_lit(v) -> str:
    kind, x = v
    if kind == "nat":
        return str(x)
    if kind == "bytes4":
        return "[" + ", ".join(f"0x{x[j:j + 2]}" for j in range(0, len(x), 2)) + "]"
    if kind in ("adr", "b256"):
        return f"0x{x}"
    if kind == "string":
        return f'"{x}"'
    if kind == "schedule":
        if not x:
            return "[]"
        return "[" + ", ".join(f"⟨{e}, {m}⟩" for e, m in x) + "]"
    raise AssertionError(kind)


def mentioned_by_specs(specs: str, key: str) -> bool:
    pat = re.compile(r"\b" + re.escape(key) + r"\b")
    for fork in FORKS:
        for dp, _dn, fn in os.walk(os.path.join(specs, "specs", fork)):
            for f in fn:
                if f.endswith(".md"):
                    with open(os.path.join(dp, f), encoding="utf-8") as h:
                        if pat.search(h.read()):
                            return True
    return False


def header(title: str, sources: list[str], specs: str, tag: str, commit: str) -> str:
    lines = [
        "/-!",
        f"# {title}",
        "",
        "Generated by `scripts/consensus-preset-generate.py`. Do not edit by hand; regenerate, and",
        "check with `python3 -I scripts/consensus-preset-generate.py --check`.",
        "",
        f"Source: `ethereum/consensus-specs` `{tag}` (commit `{commit}`), files and SHA-256:",
        "",
    ]
    for s in sources:
        lines.append(f"* `{s}` `{sha256(os.path.join(specs, s))}`")
    return "\n".join(lines)


def generate(specs: str, prov: dict) -> dict[str, str]:
    tag, commit = prov["release"], prov["tag_commit"]
    try:
        head = subprocess.run(["git", "-C", specs, "rev-parse", "HEAD"], check=True,
                              capture_output=True, text=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError) as e:
        fail(f"{specs}: not a git checkout ({e})")
    if head != commit:
        fail(f"{specs}: HEAD {head} is not the pinned tag commit {commit}")

    # presets
    preset_fields: list[tuple[str, str, str]] = []  # (key, fork, kind)
    preset_vals: dict[str, dict[str, object]] = {p: {} for p in PRESETS}
    preset_sources: list[str] = []
    for fork in FORKS:
        per = {}
        for p in PRESETS:
            rel = f"presets/{p}/{fork}.yaml"
            preset_sources.append(rel)
            per[p] = parse_yaml(os.path.join(specs, rel))
        keys = [k for k, _ in per[PRESETS[0]]]
        if keys != [k for k, _ in per[PRESETS[1]]]:
            fail(f"preset keys differ between presets for {fork}")
        for k in keys:
            if any(k == f for f, _, _ in preset_fields):
                fail(f"preset key {k} repeated across forks")
            kinds = {dict(per[p])[k][0] for p in PRESETS}
            if kinds != {"nat"}:
                fail(f"preset {k} is not a natural number")
            preset_fields.append((k, fork, "nat"))
            for p in PRESETS:
                preset_vals[p][k] = dict(per[p])[k]

    # configs
    cfg = {p: parse_yaml(os.path.join(specs, f"configs/{p}.yaml")) for p in PRESETS}
    ckeys = [k for k, _ in cfg["mainnet"]]
    if sorted(ckeys) != sorted(k for k, _ in cfg["minimal"]):
        fail("config keys differ between minimal and mainnet")
    config_fields: list[tuple[str, str]] = []
    excluded: list[str] = []
    for k in ckeys:
        kinds = {dict(cfg[p])[k][0] for p in PRESETS}
        if len(kinds) != 1:
            fail(f"config {k} has different value forms across presets")
        kind = kinds.pop()
        if k == "PRESET_BASE" or mentioned_by_specs(specs, k):
            config_fields.append((k, kind))
        else:
            excluded.append(k)
    config_sources = [f"configs/{p}.yaml" for p in PRESETS]

    # Preset.lean
    L = [header("Consensus presets (phase0 through Fulu)", preset_sources, specs, tag, commit)]
    L += [
        "",
        "A preset fixes the compile-time sizes of the specification (`presets/README.md`). The",
        "`minimal` and `mainnet` records hold every variable of the phase0 to Fulu preset files,",
        "spelled as in the specification. Feature-fork and Gloas preset files are not read.",
        "-/",
        "",
        "namespace JauneConsensus",
        "",
        "/-- A consensus preset: the variables of `presets/<name>/<fork>.yaml`, phase0 to Fulu. -/",
        "structure Preset where",
        "  /-- The preset's name (`PRESET_BASE`). -/",
        "  name : String",
    ]
    for k, fork, _ in preset_fields:
        L.append(f"  /-- `presets/*/{fork}.yaml` -/")
        L.append(f"  {k} : Nat")
    L.append("  deriving Repr, DecidableEq")
    L.append("")
    for p in PRESETS:
        L.append(f"/-- `presets/{p}/`. -/")
        L.append(f"def Preset.{p} : Preset where")
        L.append(f'  name := "{p}"')
        for k, _, _ in preset_fields:
            L.append(f"  {k} := {lean_lit(preset_vals[p][k])}")
        L.append("")
    L += [
        "/-- The preset named `n`, strictly. -/",
        "def Preset.ofName? : String → Option Preset",
    ]
    for p in PRESETS:
        L.append(f'  | "{p}" => some Preset.{p}')
    L += ["  | _ => none", "", "end JauneConsensus", ""]
    preset_lean = "\n".join(L)

    # Config.lean
    L = [header("Consensus runtime configuration (phase0 through Fulu)", config_sources, specs,
                tag, commit)]
    L += [
        "",
        "A configuration holds the run-time variables of the specification (`configs/README.md`).",
        "`Config` has one field per variable of `configs/<name>.yaml` that a phase0 to Fulu",
        "specification file mentions, spelled as in the specification. Left out, because no",
        "phase0 to Fulu specification file mentions them:",
        "",
        ", ".join(f"`{k}`" for k in excluded) + ".",
        "",
        "Types follow the value form: decimal `Nat`; four bytes `Bytes`; an execution address",
        "`Adr`; a 32-byte hash `B256`; `BLOB_SCHEDULE` a list of `BlobScheduleEntry`.",
        "-/",
        "",
        "import Jaune.Types",
    ]
    # `import` must precede the module doc; rebuild order
    doc = "\n".join(L[:-1])
    L = ["import Jaune.Types", "", doc, "",
         "namespace JauneConsensus", "", "open Jaune", "",
         "/-- One entry of `BLOB_SCHEDULE` (`specs/fulu/beacon-chain.md`, `get_blob_parameters`). -/",
         "structure BlobScheduleEntry where",
         "  EPOCH : Nat",
         "  MAX_BLOBS_PER_BLOCK : Nat",
         "  deriving Repr, DecidableEq", "",
         "/-- A consensus configuration (`configs/<name>.yaml`), phase0 to Fulu variables. -/",
         "structure Config where"]
    for k, kind in config_fields:
        L.append(f"  {k} : {LEAN_TYPE[kind]}")
    L.append("")
    for p in PRESETS:
        d = dict(cfg[p])
        L.append(f"/-- `configs/{p}.yaml`. -/")
        L.append(f"def Config.{p} : Config where")
        for k, _ in config_fields:
            L.append(f"  {k} := {lean_lit(d[k])}")
        L.append("")
    L += ["/-- The base configuration for the preset named `n`, strictly. -/",
          "def Config.ofPreset? : String → Option Config"]
    for p in PRESETS:
        L.append(f'  | "{p}" => some Config.{p}')
    L += ["  | _ => none", "", "end JauneConsensus", ""]
    config_lean = "\n".join(L)

    # ConfigOverride.lean
    L = [
        "import JauneConsensus.Config",
        "import JauneConsensus.Harness.Yaml",
        "",
        "/-!",
        "# Per-case configuration overrides (conformance harness)",
        "",
        "Generated by `scripts/consensus-preset-generate.py`. Do not edit by hand.",
        "",
        "A vector case may carry a `config.yaml` (`tests/formats/README.md`, \"Config\"): the",
        "configuration the case was generated with. The runner starts from the base `Config` of the",
        "case's preset and sets every key the file names, with the field's type. `PRESET_BASE` must",
        "equal the base's. A key that is not a `Config` field, a value of the wrong form, or a",
        "malformed `BLOB_SCHEDULE` is refused.",
        "-/",
        "",
        "namespace JauneConsensus.Harness",
        "",
        "open Jaune Yaml JauneConsensus",
        "",
        "private def hexN (v : YVal) (n : Nat) (k : String) : Except String (List UInt8) := do",
        "  let bs ← v.asHex",
        "  if bs.length == n then pure bs else throw s!\"config: {k} must be {n} bytes\"",
        "",
        "private def natOfBytes (bs : List UInt8) : Nat :=",
        "  bs.foldl (fun (n : Nat) (b : UInt8) => 256 * n + b.toNat) 0",
        "",
        "private def scheduleOf (v : YVal) : Except String (List BlobScheduleEntry) := do",
        "  (← v.asSeq).mapM fun e => do",
        "    e.expectKeys [\"EPOCH\", \"MAX_BLOBS_PER_BLOCK\"]",
        "    pure ⟨← (← e.field \"EPOCH\").asNat, ← (← e.field \"MAX_BLOBS_PER_BLOCK\").asNat⟩",
        "",
        "/-- Set one configuration key from its YAML value. -/",
        "def _root_.JauneConsensus.Config.setKey (c : Config) (k : String) (v : YVal) : Except String Config :=",
        "  match k with",
    ]
    for k, kind in config_fields:
        if k == "PRESET_BASE":
            L.append(f'  | "{k}" => match v with')
            L.append("    | .scalar s _ => if s == c.PRESET_BASE then .ok c")
            L.append('      else .error s!"config: PRESET_BASE {s} differs from the case preset {c.PRESET_BASE}"')
            L.append('    | _ => .error "config: PRESET_BASE is not a scalar"')
            continue
        rhs = {
            "nat": "v.asNat",
            "bytes4": f'hexN v 4 "{k}"',
            "adr": f'(fun bs => (natOfBytes bs).toAdr) <$> hexN v 20 "{k}"',
            "b256": f'(fun bs => (natOfBytes bs).toB256) <$> hexN v 32 "{k}"',
            "string": None,
            "schedule": "scheduleOf v",
        }[kind]
        if rhs is None:
            fail(f"no setter for string field {k}")
        L.append(f'  | "{k}" => (fun x => {{ c with {k} := x }}) <$> {rhs}')
    L += [
        '  | _ => .error s!"config: {k} is not a phase0 to Fulu configuration variable"',
        "",
        "/-- Apply a case `config.yaml` (a mapping) on top of `base`. -/",
        "def _root_.JauneConsensus.Config.applyOverrides (base : Config) (doc : YVal) : Except String Config :=",
        "  match doc with",
        "  | .map kvs => kvs.foldlM (fun c (k, v) => c.setKey k v) base",
        '  | _ => .error "config: config.yaml is not a mapping"',
        "",
        "end JauneConsensus.Harness",
        "",
    ]
    override_lean = "\n".join(L)
    return {OUT_PRESET: preset_lean, OUT_CONFIG: config_lean, OUT_OVERRIDE: override_lean}


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--specs", default=os.path.expanduser("~/consensus-specs-v1.6.1"))
    ap.add_argument("--provenance", default=os.path.join(HERE, "consensus-vectors.json"))
    ap.add_argument("--check", action="store_true")
    a = ap.parse_args()
    with open(a.provenance, encoding="utf-8") as f:
        prov = json.load(f)
    out = generate(a.specs, prov)
    bad = False
    for path, text in out.items():
        rel = os.path.relpath(path, REPO)
        if a.check:
            try:
                with open(path, encoding="utf-8") as f:
                    cur = f.read()
            except FileNotFoundError:
                cur = None
            if cur != text:
                print(f"consensus-preset-generate: {rel} differs from the generator", file=sys.stderr)
                bad = True
        else:
            with open(path, "w", encoding="utf-8") as f:
                f.write(text)
            print(f"wrote {rel}")
    if bad:
        fail("committed files differ; regenerate")
    if a.check:
        print("consensus-preset-generate: committed files match")
    return 0


if __name__ == "__main__":
    sys.exit(main())
