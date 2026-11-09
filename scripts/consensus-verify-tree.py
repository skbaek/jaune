#!/usr/bin/env python3
"""Verify an extracted consensus vector tree against the pinned tarballs, byte for byte.

``lake exe jaune-consensus`` checks an extracted tree's *names* (cases, files,
``bls_setting``, per-case ``config.yaml``) against the committed inventory, but
it reads file *contents* from disk. This script closes that gap: it checks
each tarball's size and SHA-256 against ``scripts/consensus-vectors.json``,
then streams it and compares every in-scope member under the selection with
the extracted file of the same path (regular file, same size, same SHA-256).
It also walks the extracted in-scope directories under the selection and
refuses any file, symlink or other entry that is not a tarball member.

The scope rule and the digest check are those of
``scripts/consensus-vector-inventory.py`` (imported from it, not restated).

Usage (run with ``python3 -I``)::

    python3 -I scripts/consensus-verify-tree.py --tarballs DIR --tree ROOT \\
        [--preset P ...] [--select FORK[/RUNNER[/HANDLER[/SUITE]]]]

``ROOT`` holds ``<tarball>/tests/<preset>/...`` (the default extraction layout:
one directory per tarball, for example
``~/consensus-spec-tests-v1.7.0-beta.4/extracted/comptests/tests/minimal/...``).
``--preset`` names tarballs (``general``, ``minimal``, ``mainnet``,
``comptests``); the default is every tarball of the pinned release. The
``general`` tarball belongs to the general-only provenance entry, an earlier
release with its own extraction, so it is verified in a separate run:
``--preset general --tarballs ~/consensus-spec-tests-v1.6.1/tarballs --tree
~/consensus-spec-tests-v1.6.1/extracted``.

Exit status: 0 when every selected file matches; 1 on any digest, size,
missing, extra or type mismatch, or an empty selection.
"""

from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
import stat
import sys
import tarfile

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location(
    "consensus_vector_inventory", os.path.join(HERE, "consensus-vector-inventory.py"))
assert _spec is not None and _spec.loader is not None
inv = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(inv)


def fail(msg: str) -> "NoReturn":  # type: ignore[name-defined]
    print(f"consensus-verify-tree: FAIL: {msg}", file=sys.stderr)
    sys.exit(1)


def selected(parts: list[str], select: list[str]) -> bool:
    """``parts`` is ``[fork, runner, handler, suite, ...]``."""
    return parts[: len(select)] == select


def file_sha256(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def verify_preset(tar_path: str, tree: str, key: str, select: list[str]) -> int:
    preset = inv.TARBALL_PRESET[key]
    skip = inv.SOURCE_PREFIX.get(key, ())
    expected: set[str] = set()
    with tarfile.open(tar_path, mode="r|gz") as tar:
        for m in tar:
            if not m.isfile():
                continue
            parts = [p for p in m.name.split("/") if p not in ("", ".")]
            if ".." not in parts and any("/".join(parts).startswith(q) for q in skip):
                continue
            if ".." in parts or len(parts) < 8 or parts[0] != "tests" or parts[1] != preset:
                fail(f"{tar_path}: unexpected member {m.name!r}")
            if not inv.in_scope(key, parts[2], parts[3]) or not selected(parts[2:], select):
                continue
            rel = "/".join(parts)
            local = os.path.join(tree, key, rel)
            try:
                st = os.lstat(local)
            except FileNotFoundError:
                fail(f"{key}/{rel}: missing from the tree")
            if not stat.S_ISREG(st.st_mode):
                fail(f"{key}/{rel}: not a regular file in the tree")
            if st.st_size != m.size:
                fail(f"{key}/{rel}: size {st.st_size} != tarball {m.size}")
            fh = tar.extractfile(m)
            if fh is None:
                fail(f"{tar_path}: unreadable {m.name!r}")
            want = hashlib.sha256(fh.read()).hexdigest()
            got = file_sha256(local)
            if got != want:
                fail(f"{key}/{rel}: sha256 {got} != tarball {want}")
            expected.add(rel)
    # nothing extra in the extracted in-scope directories under the selection
    base = os.path.join(tree, key)
    top = os.path.join(base, "tests", preset)
    if not os.path.isdir(top):
        fail(f"{top}: not a directory")
    seen = 0
    for fork in sorted(os.listdir(top)):
        fdir = os.path.join(top, fork)
        if not os.path.isdir(fdir) or os.path.islink(fdir):
            fail(f"{fdir}: unexpected entry")
        for runner in sorted(os.listdir(fdir)):
            if not inv.in_scope(key, fork, runner):
                continue
            if not (selected([fork, runner], select[:2])):
                continue
            for dp, dn, fn in os.walk(os.path.join(fdir, runner), followlinks=False):
                for d in dn:
                    if os.path.islink(os.path.join(dp, d)):
                        fail(f"{os.path.join(dp, d)}: symlink in the tree")
                for f in fn:
                    p = os.path.join(dp, f)
                    rel = os.path.relpath(p, base).replace(os.sep, "/")
                    rparts = rel.split("/")
                    if not selected(rparts[2:], select):
                        continue
                    if rel not in expected:
                        fail(f"{key}/{rel}: in the tree but not a selected tarball member")
                    seen += 1
    if seen != len(expected):
        fail(f"{key}: {seen} files in the tree, {len(expected)} expected")
    return len(expected)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("--tarballs", required=True)
    ap.add_argument("--tree", required=True)
    ap.add_argument("--provenance", default=os.path.join(HERE, "consensus-vectors.json"))
    ap.add_argument("--preset", action="append", choices=inv.PRESETS)
    ap.add_argument("--select", default="", help="FORK[/RUNNER[/HANDLER[/SUITE]]]")
    a = ap.parse_args()
    select = [s for s in a.select.split("/") if s]
    if len(select) > 4:
        fail("--select has at most four components")
    with open(a.provenance, encoding="utf-8") as f:
        prov = json.load(f)
    total = 0
    for preset in a.preset or list(prov["tarballs"]):
        meta, _release, _tag = inv.tarball_meta(prov, preset)
        path = os.path.join(a.tarballs, meta["name"])
        if not os.path.isfile(path):
            fail(f"missing tarball {path}")
        inv.check_tarball(path, meta)
        n = verify_preset(path, a.tree, preset, select)
        print(f"{preset}: {n} files match the pinned tarball")
        total += n
    if total == 0:
        fail("empty selection")
    print(f"consensus-verify-tree: OK, {total} files")
    return 0


if __name__ == "__main__":
    sys.exit(main())
