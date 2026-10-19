#!/usr/bin/env python3
"""Verify and route a separately identified, bounded Amsterdam fixture correction.

The official release is never edited. Registration authenticates a portable
package; it does not prove historical generation or authorize corpus adoption.
Only an explicit sources.json pointer activates a package.
"""
from __future__ import annotations

import argparse
import copy
import gzip
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import sys
import tarfile
import tempfile

SCRIPTS = Path(__file__).resolve().parent
ID = "bal-header-format-v1"
KIND = "jaune-eest-fixture-correction-v1"
NETWORK = "BPO2ToAmsterdamAtTime15k"
SOURCE = "tests/amsterdam/eip7928_block_level_access_lists/test_fork_transition.py"
PREFIX = "for_bpo2toamsterdamattime15k/amsterdam/eip7928_block_level_access_lists/fork_transition/"
DELTAS = {
    PREFIX + "invalid_post_fork_block_without_bal_hash_field.json": "BlockException.INVALID_BAL_HASH",
    PREFIX + "invalid_pre_fork_block_with_bal_hash_field.json": "BlockException.INVALID_BLOCK_HASH",
}
NEW = "BlockException.INCORRECT_BLOCK_FORMAT"
CASE_PREFIX = "tests/amsterdam/eip7928_block_level_access_lists/test_fork_transition.py::test_"
MAX_ARCHIVE_BYTES = 2 * 1024 * 1024
MAX_MEMBER_BYTES = 1024 * 1024


class CorrectionError(Exception):
    pass


def need(ok, message):
    if not ok:
        raise CorrectionError(message)


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False,
                       allow_nan=False) + "\n").encode()


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def regular_bytes(path):
    path = Path(path)
    need(path.is_file() and not path.is_symlink(), f"missing or linked correction input: {path}")
    need(stat.S_ISREG(path.stat().st_mode) and path.stat().st_nlink == 1,
         f"correction input must be a regular unlinked file: {path}")
    return path.read_bytes()


def sha(path):
    return digest(regular_bytes(path))


def parse(raw):
    def unique(pairs):
        value = {}
        for key, child in pairs:
            need(key not in value, f"duplicate JSON key: {key}")
            value[key] = child
        return value
    try:
        return json.loads(raw, object_pairs_hook=unique,
                          parse_constant=lambda value: (_ for _ in ()).throw(CorrectionError("non-finite JSON")))
    except (ValueError, UnicodeDecodeError) as error:
        raise CorrectionError(f"invalid correction JSON: {error}") from error


def read(path):
    return parse(regular_bytes(path))


def load_sources(path):
    import env_doctor
    try:
        return env_doctor.load_manifest(path)
    except env_doctor.ManifestError as error:
        raise CorrectionError(str(error)) from error


def keys(value, expected, label):
    need(isinstance(value, dict) and set(value) == set(expected), f"{label}: exact fields required")


def hex_digest(value, length=64):
    need(isinstance(value, str) and re.fullmatch(r"[0-9a-f]{%d}" % length, value) is not None,
         "invalid correction digest/commit")


def relative(value):
    need(isinstance(value, str) and value and not any(c in value for c in "\\\x00\t\r\n"),
         "invalid correction path")
    path = PurePosixPath(value)
    need(not path.is_absolute() and path.as_posix() == value and
         all(part not in ("", ".", "..") for part in value.split("/")), "unsafe correction path")
    return path


def repo_file(repo, value):
    path = Path(repo) / str(relative(value))
    need(path.resolve().is_relative_to(Path(repo).resolve()), "correction path escapes repository")
    for parent in [path, *path.parents]:
        if parent == Path(repo):
            break
        need(not parent.is_symlink(), "linked correction repository path")
    return path


def base_identity(release):
    return {key: release[key] for key in ("release_tag", "release_commit", "archive_sha256", "metadata_json_expected")}


def validate_pointer(pointer):
    keys(pointer, ("id", "registration", "registration_sha256"), "correction pointer")
    need(pointer["id"] == ID, "unknown fixture correction ID")
    relative(pointer["registration"])
    need(pointer["registration"] == f"scripts/amsterdam/corrections/{ID}/registration.json",
         "wrong correction registration destination")
    hex_digest(pointer["registration_sha256"])


def validate_sources(sources, repo):
    for name, section in sources.items():
        if isinstance(section, dict) and "fixture_correction" in section:
            need(name == "amsterdam", "fixture correction is Amsterdam-only")
            load_registration(section["fixture_correction"], repo)


def validate_entry(entry):
    keys(entry, ("path", "network", "case", "original_sha256", "generated_sha256",
                 "wire_sha256", "old", "new", "metadata_changed_keys"), "correction entry")
    need(entry["path"] in DELTAS, "correction entry outside exact two paths")
    need(entry["network"] == NETWORK and entry["old"] == DELTAS[entry["path"]] and entry["new"] == NEW,
         "correction entry network/expected-name contract differs")
    expected_case = CASE_PREFIX + Path(entry["path"]).stem + "[fork_" + NETWORK + "-blockchain_test]"
    need(entry["case"] == expected_case, "correction entry case identity differs")
    for key in ("original_sha256", "generated_sha256", "wire_sha256"):
        hex_digest(entry[key])
    need(entry["metadata_changed_keys"] == ["description", "hash", "url"],
         "unexpected correction metadata change set")


def validate_entries(entries):
    need(isinstance(entries, list) and len(entries) == 2, "exactly two correction entries required")
    for entry in entries:
        validate_entry(entry)
    need([e["path"] for e in entries] == sorted(DELTAS), "missing/duplicate/unsorted correction entries")


def semantic(case):
    return {k: v for k, v in case.items() if k != "_info"}


def verify_fixture_delta(original_raw, generated_raw, entry):
    validate_entry(entry)
    need(digest(original_raw) == entry["original_sha256"], "base original file hash differs")
    need(digest(generated_raw) == entry["generated_sha256"], "corrected file hash differs")
    original, generated = parse(original_raw), parse(generated_raw)
    need(isinstance(original, dict) and isinstance(generated, dict) and
         list(original) == list(generated) == [entry["case"]], "correction case population differs")
    left, right = original[entry["case"]], generated[entry["case"]]
    need(isinstance(left, dict) and isinstance(right, dict), "correction case is not an object")
    need(left.get("network") == right.get("network") == NETWORK, "correction fixture network differs")
    need(isinstance(left.get("blocks"), list) and isinstance(right.get("blocks"), list) and
         len(left["blocks"]) == len(right["blocks"]) == 1, "correction candidate population differs")
    need(left["blocks"][0].get("expectException") == entry["old"] and
         right["blocks"][0].get("expectException") == NEW, "correction expected-name delta differs")
    expected = copy.deepcopy(semantic(left))
    expected["blocks"][0]["expectException"] = NEW
    need(canonical(semantic(right)) == canonical(expected), "correction semantic drift outside expected name")
    for case in (left, right):
        info = case.get("_info")
        need(isinstance(info, dict) and info.get("fixture-format") == "blockchain_test", "not a raw blockchain fixture")
        # Exact pinned BaseFixture.hash encoding, separate from file SHA-256.
        semantic_hash = digest(json.dumps(semantic(case), sort_keys=True, separators=(",", ":")).encode())
        need(info.get("hash") == "0x" + semantic_hash, "fixture semantic metadata hash differs")
    changed = sorted(k for k in set(left["_info"]) | set(right["_info"])
                     if left["_info"].get(k) != right["_info"].get(k))
    need(changed == entry["metadata_changed_keys"], "fixture metadata change set differs")
    try:
        wire_left = bytes.fromhex(left["blocks"][0]["rlp"].removeprefix("0x"))
        wire_right = bytes.fromhex(right["blocks"][0]["rlp"].removeprefix("0x"))
    except (ValueError, AttributeError, KeyError) as error:
        raise CorrectionError("invalid raw correction wire") from error
    need(wire_left == wire_right and digest(wire_right) == entry["wire_sha256"], "correction raw RLP differs")


def load_registration(pointer, repo):
    validate_pointer(pointer)
    path = repo_file(repo, pointer["registration"])
    raw = regular_bytes(path)
    need(digest(raw) == pointer["registration_sha256"], "correction registration hash differs")
    reg = parse(raw)
    keys(reg, ("kind", "id", "base", "generation_receipt_sha256", "source_patch_sha256",
               "archive_sha256", "archive_size_bytes", "index_sha256", "entries"), "registration")
    need(raw == canonical(reg) and reg["kind"] == KIND and reg["id"] == ID, "noncanonical/unknown registration")
    keys(reg["base"], ("release_tag", "release_commit", "archive_sha256", "metadata_json_expected"), "base identity")
    for key in ("generation_receipt_sha256", "source_patch_sha256", "archive_sha256", "index_sha256"):
        hex_digest(reg[key])
    need(type(reg["archive_size_bytes"]) is int and 0 < reg["archive_size_bytes"] <= MAX_ARCHIVE_BYTES,
         "correction archive size out of bounds")
    validate_entries(reg["entries"])
    return reg, path.parent


def verify_receipt(raw, reg):
    need(digest(raw) == reg["generation_receipt_sha256"], "generation receipt hash differs")
    receipt = parse(raw)
    keys(receipt, ("kind", "id", "source", "environment", "evidence", "commands", "formats", "limits"),
         "generation receipt")
    need(raw == canonical(receipt) and receipt["kind"] == "jaune-correction-generation-receipt-v1" and
         receipt["id"] == ID, "unknown/noncanonical generation receipt")
    source = receipt["source"]
    keys(source, ("base_commit", "base_tree", "commit", "tree", "path", "before_blob", "after_blob",
                  "before_sha256", "after_sha256", "mode", "patch_sha256"), "receipt source")
    need(source["path"] == SOURCE and source["mode"] == "100644" and
         source["base_commit"] == reg["base"]["release_commit"] and
         source["commit"] != source["base_commit"] and source["patch_sha256"] == reg["source_patch_sha256"],
         "generation source contract differs")
    for key in ("base_commit", "base_tree", "commit", "tree", "before_blob", "after_blob"):
        hex_digest(source[key], 40)
    for key in ("before_sha256", "after_sha256", "patch_sha256"):
        hex_digest(source[key])
    keys(receipt["environment"], ("uv_lock_sha256", "python", "packages", "files"), "receipt environment")
    hex_digest(receipt["environment"]["uv_lock_sha256"])
    need(isinstance(receipt["environment"]["python"], str) and receipt["environment"]["python"].startswith("3.11.9"),
         "generation interpreter differs")
    need(isinstance(receipt["environment"]["packages"], list) and bool(receipt["environment"]["packages"]),
         "missing generation package identity")
    for name in ("evidence", "commands", "formats", "limits"):
        need(isinstance(receipt[name], (dict, list)) and bool(receipt[name]), "missing generation " + name)
    need(all(isinstance(p, list) and len(p) == 2 and all(isinstance(s, str) and s for s in p)
             for p in receipt["environment"]["packages"]), "invalid generation package inventory")
    need(isinstance(receipt["environment"]["files"], list) and bool(receipt["environment"]["files"]),
         "missing generation environment file identities")
    for item in receipt["environment"]["files"]:
        keys(item, ("role", "sha256", "bytes"), "environment file")
        hex_digest(item["sha256"])
        need(isinstance(item["role"], str) and bool(item["role"]) and type(item["bytes"]) is int and item["bytes"] >= 0,
             "invalid environment file identity")
    evidence = receipt["evidence"]
    keys(evidence, ("experiment_manifest_sha256", "experiment_acceptance_sha256", "accepted_report_sha256",
                    "artifacts", "packager_sha256", "verifier_sha256"), "receipt evidence")
    for key in set(evidence) - {"artifacts"}:
        hex_digest(evidence[key])
    need(isinstance(evidence["artifacts"], list) and bool(evidence["artifacts"]), "missing evidence inventory")
    names = set()
    for item in evidence["artifacts"]:
        keys(item, ("path", "sha256", "bytes"), "evidence artifact")
        relative(item["path"])
        hex_digest(item["sha256"])
        need(item["path"] not in names and type(item["bytes"]) is int and item["bytes"] >= 0, "duplicate/invalid evidence identity")
        names.add(item["path"])
    need(isinstance(receipt["commands"], list), "invalid generation commands")
    for command in receipt["commands"]:
        keys(command, ("record", "argv", "cwd", "exit", "started_utc", "timing_scope", "stdout_sha256", "stderr_sha256"),
             "generation command")
        relative(command["record"])
        need(isinstance(command["argv"], list) and bool(command["argv"]) and
             all(isinstance(v, str) for v in command["argv"]) and type(command["exit"]) is int,
             "invalid generation command result")
        for key in ("stdout_sha256", "stderr_sha256"):
            hex_digest(command[key])
    keys(receipt["formats"], ("two_phase", "ordinary", "stateful", "sync"), "observed formats")
    need(receipt["formats"]["two_phase"] == {"blockchain_test": 2, "blockchain_test_engine": 2, "blockchain_test_engine_x": 2} and
         receipt["formats"]["ordinary"] == {"blockchain_test": 2, "blockchain_test_engine": 2}, "observed generation population differs")
    need(isinstance(receipt["limits"], list) and all(isinstance(v, str) and v for v in receipt["limits"]),
         "invalid generation limitations")
    # The production package is portable: private source locations are neither
    # required at runtime nor copied into the receipt's data.
    need(b"/Users/" not in raw and b"/home/" not in raw and b"/master/" not in raw, "nonportable generation receipt")
    return receipt


def tar_bytes(members):
    buffer = io.BytesIO()
    with tarfile.open(fileobj=buffer, mode="w", format=tarfile.USTAR_FORMAT) as archive:
        for name, raw in sorted(members.items()):
            info = tarfile.TarInfo(name)
            info.size, info.mode, info.uid, info.gid, info.mtime = len(raw), 0o644, 0, 0, 0
            info.uname = info.gname = ""
            archive.addfile(info, io.BytesIO(raw))
    return buffer.getvalue()


def archive_bytes(members):
    buffer = io.BytesIO()
    with gzip.GzipFile(fileobj=buffer, mode="wb", filename="", mtime=0, compresslevel=9) as zipped:
        zipped.write(tar_bytes(members))
    return buffer.getvalue()


def verify_package(reg, directory):
    directory = Path(directory)
    receipt = verify_receipt(regular_bytes(directory / "generation-receipt.json"), reg)
    patch = regular_bytes(directory / "source.patch")
    need(digest(patch) == reg["source_patch_sha256"], "source patch hash differs")
    expected_header = f"diff --git a/{SOURCE} b/{SOURCE}\n".encode()
    blob_line = re.search(rb"^index ([0-9a-f]{7,40})\.\.([0-9a-f]{7,40}) 100644$", patch, re.MULTILINE)
    need(patch.startswith(expected_header) and patch.count(b"diff --git ") == 1 and blob_line is not None and
         receipt["source"]["before_blob"].startswith(blob_line[1].decode()) and
         receipt["source"]["after_blob"].startswith(blob_line[2].decode()), "source patch/blob identity differs")
    raw = regular_bytes(directory / "artifact.tar.gz")
    need(len(raw) == reg["archive_size_bytes"] and digest(raw) == reg["archive_sha256"], "correction archive hash/size differs")
    need(raw[:4] == b"\x1f\x8b\x08\x00" and raw[4:8] == b"\0" * 4, "noncanonical gzip header")
    expected = ["correction-index.json"] + ["fixtures/blockchain_tests/" + e["path"] for e in reg["entries"]]
    members = {}
    try:
        # Bound decompression and reject data hidden after tar end markers.
        limit = len(expected) * (MAX_MEMBER_BYTES + 1024) + 10240
        with gzip.GzipFile(fileobj=io.BytesIO(raw), mode="rb") as zipped:
            unpacked = zipped.read(limit + 1)
        need(len(unpacked) <= limit, "correction archive decompressed size out of bounds")
        with tarfile.open(fileobj=io.BytesIO(unpacked), mode="r:") as archive:
            for member in archive:
                relative(member.name)
                need(member.name in expected and member.name not in members and member.isreg() and
                     member.type == tarfile.REGTYPE and not member.pax_headers, "correction archive member integrity")
                need(0 <= member.size <= MAX_MEMBER_BYTES and member.mode == 0o644 and
                     member.uid == member.gid == member.mtime == 0 and not member.uname and not member.gname,
                     "correction archive metadata differs")
                members[member.name] = archive.extractfile(member).read()
    except (tarfile.TarError, OSError, EOFError) as error:
        raise CorrectionError(f"cannot read correction archive: {error}") from error
    need(list(members) == sorted(expected), "missing/extra/unsorted correction archive members")
    need(unpacked == tar_bytes(members), "noncanonical/trailing correction tar content")
    index_raw = members["correction-index.json"]
    need(digest(index_raw) == reg["index_sha256"], "correction index hash differs")
    index = parse(index_raw)
    keys(index, ("kind", "id", "base", "generation_receipt_sha256", "entries"), "correction index")
    need(index_raw == canonical(index) and index == {k: reg[k] for k in index}, "correction index identity differs")
    for entry in reg["entries"]:
        need(digest(members["fixtures/blockchain_tests/" + entry["path"]]) == entry["generated_sha256"],
             "archive fixture file hash differs")
    return {"registration": reg, "receipt": receipt, "index": index, "members": members, "directory": directory}


def verify_base_bindings(package, release, fixtures):
    reg = package["registration"]
    need(reg["base"] == base_identity(release), "correction base release identity differs")
    for entry in reg["entries"]:
        original = regular_bytes(repo_file(Path(fixtures) / "blockchain_tests", entry["path"]))
        verify_fixture_delta(original, package["members"]["fixtures/blockchain_tests/" + entry["path"]], entry)


def cache_path(package, cache_root=None):
    parent = Path(cache_root or os.environ.get("JAUNE_FIXTURE_CORRECTION_CACHE",
                  str(Path.home() / ".cache/jaune/fixture-corrections"))).expanduser().absolute()
    return parent / package["registration"]["archive_sha256"]


def verify_installed(package, fixtures, cache_root=None):
    path = cache_path(package, cache_root)
    need(not path.resolve().is_relative_to(Path(fixtures).resolve()) and
         not Path(fixtures).resolve().is_relative_to(path.resolve()), "correction cache overlaps official fixtures")
    need(path.is_dir() and not path.is_symlink(),
         "missing correction setup; run python3 scripts/fixture_corrections.py install --lane amsterdam")
    actual = set()
    for item in path.rglob("*"):
        need(not item.is_symlink(), "linked correction cache member")
        if item.is_file():
            name = item.relative_to(path).as_posix()
            actual.add(name)
            need(name in package["members"] and regular_bytes(item) == package["members"][name],
                 "installed correction bytes differ")
        else:
            need(item.is_dir(), "special correction cache member")
    need(actual == set(package["members"]), "missing/extra correction cache members")
    return path


def active_package(sources, lane, repo, fixtures, cache_root=None, installed=True):
    key = "amsterdam" if lane == "amsterdam" else "current_mainnet"
    need(lane in ("mainnet", "historical", "amsterdam"), "unknown correction lane")
    pointer = sources[key].get("fixture_correction")
    if pointer is None:
        return None
    need(lane == "amsterdam", "fixture correction is Amsterdam-only")
    reg, directory = load_registration(pointer, repo)
    package = verify_package(reg, directory)
    verify_base_bindings(package, sources[key], fixtures)
    if installed:
        package["cache"] = verify_installed(package, fixtures, cache_root)
    return package


def install(package, fixtures, cache_root=None):
    path = cache_path(package, cache_root)
    need(not path.resolve().is_relative_to(Path(fixtures).resolve()) and
         not Path(fixtures).resolve().is_relative_to(path.resolve()), "correction cache overlaps official fixtures")
    if path.exists() or path.is_symlink():
        return verify_installed(package, fixtures, cache_root)
    path.parent.mkdir(parents=True, exist_ok=True)
    lock = path.with_name(path.name + ".install-lock")
    try:
        lock.mkdir()
    except FileExistsError as error:
        raise CorrectionError("correction installation already in progress; no cache changed") from error
    staging = None
    try:
        need(not path.exists() and not path.is_symlink(), "correction cache destination became occupied")
        staging = Path(tempfile.mkdtemp(prefix=".correction-", dir=path.parent))
        for name, raw in package["members"].items():
            output = staging / name
            output.parent.mkdir(parents=True, exist_ok=True)
            output.write_bytes(raw)
        # A concurrent occupied destination is refused, never overwritten.
        need(not path.exists() and not path.is_symlink(), "correction cache destination became occupied")
        staging.rename(path)
        return verify_installed(package, fixtures, cache_root)
    finally:
        if staging is not None and staging.exists():
            shutil.rmtree(staging)
        lock.rmdir()


def correction_identity(package):
    return {key: package["registration"][key] for key in ("id", "archive_sha256", "index_sha256", "generation_receipt_sha256")}


def suite_entries(manifest, suite):
    value = manifest["suites"].get(suite)
    need(isinstance(value, dict), "unknown dispatch suite")
    files = value.get("files")
    if files is None:
        files = sorted((e for name in value["component_suites"] for e in manifest["suites"][name]["files"]),
                       key=lambda e: e["path"])
    need(isinstance(files, list) and bool(files), "zero dispatch selection")
    need(len({(e["path"], e["network"]) for e in files}) == len(files), "duplicate dispatch selection")
    return files


def resolve_inputs(sources, lane, repo, fixtures, manifest, selected, start_at=1, cache_root=None):
    package = active_package(sources, lane, repo, fixtures, cache_root)
    expected_identity = correction_identity(package) if package else None
    need(manifest["source"].get("fixture_correction") == expected_identity, "manifest correction identity differs")
    replacements = {e["path"]: e for e in package["registration"]["entries"]} if package else {}
    rows = []
    for index, entry in enumerate(selected, 1):
        path, network = entry["path"], entry["network"]
        relative(path)
        need(isinstance(network, str) and not any(c in network for c in " \t\r\n\0"), "invalid dispatch network")
        base_file = repo_file(Path(fixtures) / "blockchain_tests", path).absolute()
        base_sha = sha(base_file)
        need(entry.get("content_sha256", base_sha) == base_sha, "manifest base content hash differs")
        replacement = replacements.get(path)
        effective_sha, physical, kind = base_sha, base_file, "official-base"
        if replacement is not None:
            need(network == replacement["network"] and entry.get("fixture_correction") ==
                 {"id": ID, "effective_content_sha256": replacement["generated_sha256"]}, "missing/wrong correction mapping")
            effective_sha = replacement["generated_sha256"]
            physical = package["cache"] / "fixtures/blockchain_tests" / path
            kind = "fixture-correction"
        else:
            need("fixture_correction" not in entry, "unregistered correction mapping")
        need(sha(physical) == effective_sha, "physical fixture content hash differs")
        if index >= start_at:
            rows.append({"index": index, "path": path, "network": network, "base_path": str(base_file),
                         "original_sha256": base_sha, "effective_sha256": effective_sha,
                         "physical_path": str(physical), "source_kind": kind})
    need(bool(rows), "empty dispatch after start-at")
    return rows, package


def prepare_dispatch(args):
    sources = load_sources(args.sources)
    manifest_raw = regular_bytes(args.manifest)
    manifest = parse(manifest_raw)
    files = suite_entries(manifest, args.suite)
    if args.subdir:
        prefix = str(relative(args.subdir.rstrip("/"))) + "/"
        files = [e for e in files if e["path"].startswith(prefix)]
    selected = [(e["path"], e["network"]) for e in files]
    actual = []
    for line in regular_bytes(args.selection).decode().splitlines():
        fields = line.split("\t")
        need(len(fields) == 2, "malformed dispatch selection")
        actual.append(tuple(fields))
    need(actual == selected and bool(selected), "dispatch selection differs from committed manifest")
    need(1 <= args.start_at <= len(files), "invalid dispatch start-at")
    allowed = args.allowed_networks.split()
    need(all(e["network"] in allowed for e in files), "unknown manifest network")
    rows, package = resolve_inputs(sources, args.lane, args.sources.parent.parent, args.fixtures_root,
                                   manifest, files, args.start_at, args.cache_root)
    release = sources["amsterdam" if args.lane == "amsterdam" else "current_mainnet"]
    index_subpath = release.get("metadata_json_file_subpath")
    index_sha = sha(repo_file(args.fixtures_root, index_subpath)) if index_subpath else None
    receipt = {"kind": "jaune-fixture-dispatch-v1", "lane": args.lane, "suite": args.suite,
        "subdir": args.subdir, "start_at": args.start_at, "selection_count": len(files),
        "sources_path": str(args.sources.absolute()), "sources_sha256": sha(args.sources),
        "manifest_path": str(args.manifest.absolute()), "manifest_sha256": digest(manifest_raw),
        "fixtures_root": str(args.fixtures_root.absolute()),
        "cache_root": str(package["cache"].parent) if package else None,
        "base": base_identity(release), "release_index_sha256": index_sha,
        "fixture_correction": correction_identity(package) if package else None,
        "applied_replacements": sum(row["source_kind"] == "fixture-correction" for row in rows), "rows": rows}
    with args.receipt.open("xb") as stream:
        stream.write(canonical(receipt))
    for row in rows:
        for field in (str(row["index"]), row["path"], row["network"], row["physical_path"]):
            sys.stdout.buffer.write(field.encode() + b"\0")


def verify_dispatch(path, expected_sha):
    need(sha(path) == expected_sha, "dispatch receipt hash differs")
    receipt = read(path)
    keys(receipt, ("kind", "lane", "suite", "subdir", "start_at", "selection_count", "sources_path", "sources_sha256",
         "manifest_path", "manifest_sha256", "fixtures_root", "cache_root", "base", "release_index_sha256", "fixture_correction", "applied_replacements", "rows"), "dispatch receipt")
    need(receipt["kind"] == "jaune-fixture-dispatch-v1", "wrong dispatch receipt kind")
    need(sha(receipt["sources_path"]) == receipt["sources_sha256"] and
         sha(receipt["manifest_path"]) == receipt["manifest_sha256"], "post-run source/manifest input changed")
    sources_path = Path(receipt["sources_path"])
    sources = load_sources(sources_path)
    release = sources["amsterdam" if receipt["lane"] == "amsterdam" else "current_mainnet"]
    index_subpath = release.get("metadata_json_file_subpath")
    index_sha = sha(repo_file(Path(receipt["fixtures_root"]), index_subpath)) if index_subpath else None
    need(index_sha == receipt["release_index_sha256"], "post-run release index changed")
    manifest = read(receipt["manifest_path"])
    files = suite_entries(manifest, receipt["suite"])
    if receipt["subdir"]:
        prefix = str(relative(receipt["subdir"].rstrip("/"))) + "/"
        files = [e for e in files if e["path"].startswith(prefix)]
    rows, package = resolve_inputs(sources, receipt["lane"], sources_path.parent.parent,
        Path(receipt["fixtures_root"]), manifest, files, receipt["start_at"], receipt["cache_root"])
    need(receipt["selection_count"] == len(files) and receipt["rows"] == rows and
         receipt["applied_replacements"] == sum(row["source_kind"] == "fixture-correction" for row in rows) and
         receipt["fixture_correction"] == (correction_identity(package) if package else None),
         "post-run dispatch identity differs")
    need(receipt["base"] == base_identity(sources["amsterdam" if receipt["lane"] == "amsterdam" else "current_mainnet"]),
         "post-run base identity differs")
    return receipt


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)
    install_parser = sub.add_parser("install")
    install_parser.add_argument("--lane", choices=["amsterdam"], required=True)
    install_parser.add_argument("--sources", type=Path, default=SCRIPTS / "sources.json")
    install_parser.add_argument("--base-root", type=Path, required=True)
    install_parser.add_argument("--cache-root", type=Path)
    dispatch = sub.add_parser("prepare-dispatch")
    for name in ("sources", "manifest", "fixtures-root", "selection", "receipt"):
        dispatch.add_argument("--" + name, type=Path, required=True)
    for name in ("lane", "suite", "allowed-networks"):
        dispatch.add_argument("--" + name, required=True)
    dispatch.add_argument("--subdir", default="")
    dispatch.add_argument("--start-at", type=int, default=1)
    dispatch.add_argument("--cache-root", type=Path)
    verify = sub.add_parser("verify-dispatch")
    verify.add_argument("--receipt", type=Path, required=True)
    verify.add_argument("--sha256", required=True)
    args = parser.parse_args(argv)
    try:
        if args.command == "install":
            sources = load_sources(args.sources)
            fixtures = args.base_root / sources["amsterdam"]["fixtures_subpath"]
            package = active_package(sources, args.lane, args.sources.parent.parent, fixtures, installed=False)
            need(package is not None, "no registered Amsterdam correction to install")
            path = install(package, fixtures, args.cache_root)
            print(f"OK — installed explicit correction {ID}: {path}")
        elif args.command == "prepare-dispatch":
            prepare_dispatch(args)
        else:
            receipt = verify_dispatch(args.receipt, args.sha256)
            identity = receipt["fixture_correction"]
            print("OK — post-run input identity verified" +
                  (f"; explicit correction {identity['id']} archive {identity['archive_sha256']} index {identity['index_sha256']}" if identity else ""))
        return 0
    except (CorrectionError, OSError, KeyError, TypeError, ValueError) as error:
        print(f"correction setup error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
