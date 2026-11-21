"""Materialize the naming sources that scripts/naming-policy.json cites, from scripts/naming-sources.lock.json.

Each source is cached under SOURCE_ROOT/sha256/<sha256>, the path the policy names, and is the
`--source-root` of scripts/check-naming.py and scripts/naming-census.py. A Git-hosted file is fetched
from its pinned revision; a standard published elsewhere is pinned by URL and digest, and a PDF is
bound through the text extract that scripts/pdf_text.py (pinned by its digest in the lock) makes.
`--offline` verifies an existing cache without network access and fails on any digest mismatch.

    python3 scripts/naming_sources.py --source-root SOURCE_ROOT [--offline]
"""
import argparse
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
from pathlib import Path, PurePosixPath
import re
import sys
from tempfile import NamedTemporaryFile
import unicodedata
from urllib.parse import quote
from urllib.request import Request, urlopen

# A standard published outside a Git host is pinned by its canonical URL and
# the SHA-256 of the fetched bytes. A PDF is bound through a text extract made
# by the pinned extractor beside this file; the lock pins the extract too.
EXTRACTORS = {"pdf-text-v1": "pdf_text.py"}
TRANSLITERATIONS = ("greek-letter-names",)
GIT_KEYS = {"repository", "revision", "path", "sha256"}
URL_KEYS = {"url", "sha256"}
URL_OPTIONS = {"content_sha256", "extract"}
EXTRACT_KEYS = {"method", "tool_sha256"}
EXTRACT_OPTIONS = {"transliteration"}
HEX64 = r"[a-f0-9]{64}"


def load_lock(path):
    rows = json.loads(path.read_bytes())
    for key, row in rows.items():
        if "url" in row:
            extract = row.get("extract")
            if (not URL_KEYS <= set(row) <= URL_KEYS | URL_OPTIONS
                    or not re.fullmatch(r"https://[a-z0-9.-]+/[A-Za-z0-9_./~%-]+", row["url"])
                    or not re.fullmatch(HEX64, row["sha256"])
                    or ("extract" in row) != ("content_sha256" in row)
                    or (extract is not None and (
                        not isinstance(extract, dict)
                        or not EXTRACT_KEYS <= set(extract) <= EXTRACT_KEYS | EXTRACT_OPTIONS
                        or extract["method"] not in EXTRACTORS
                        or not re.fullmatch(HEX64, extract["tool_sha256"])
                        or extract.get("transliteration", TRANSLITERATIONS[0]) not in TRANSLITERATIONS
                        or not re.fullmatch(HEX64, row["content_sha256"])))):
                raise ValueError(f"invalid source record for {key}")
            continue
        source = PurePosixPath(row.get("path", ""))
        if (set(row) != GIT_KEYS or str(source) != row["path"] or source.is_absolute() or not source.parts
                or ".." in source.parts
                or not re.fullmatch(r"[A-Za-z0-9_-]+/[A-Za-z0-9_.-]+", row["repository"])
                or not re.fullmatch(r"[a-f0-9]{40}", row["revision"])
                or not re.fullmatch(HEX64, row["sha256"])):
            raise ValueError(f"invalid source record for {key}")
    return rows


def cache_path(row):
    return Path("sha256") / row["sha256"]


def bind_sources(sources, lock):
    if set(sources) != set(lock):
        raise ValueError("source IDs differ between the policy and source lock")
    result = {}
    for key, source in sources.items():
        if source["sha256"] != lock[key]["sha256"]:
            raise ValueError(f"policy and source lock disagree for {key}")
        result[key] = {**source, "path": cache_path(lock[key]).as_posix()}
    return result


def greek_letter_names(text):
    """Write each Greek letter as its Unicode letter name: theta, Sigma, ..."""
    def name(match):
        parts = unicodedata.name(match.group()).split()
        if parts[:1] != ["GREEK"] or "LETTER" not in parts or parts[1] not in ("SMALL", "CAPITAL"):
            return match.group()
        word = parts[-1].lower()
        return word.capitalize() if parts[1] == "CAPITAL" else word
    return re.sub("[Ͱ-Ͽ]", name, text)


def derive(row, content):
    """The bindable UTF-8 text of a fetched standard."""
    extract = row.get("extract")
    if extract is None:
        return content
    tool = Path(__file__).with_name(EXTRACTORS[extract["method"]])
    if hashlib.sha256(tool.read_bytes()).hexdigest() != extract["tool_sha256"]:
        raise ValueError(f"extractor differs from the locked tool for {row['url']}")
    spec = importlib.util.spec_from_file_location("naming_source_extractor", tool)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    text = module.extract(content)[1].decode("utf-8")
    if "transliteration" in extract:
        text = greek_letter_names(text)
    return text.encode("utf-8")


def store(path, data):
    if path.exists():
        return
    with NamedTemporaryFile(dir=path.parent, delete=False) as temp:
        temp_path = Path(temp.name)
        try:
            temp.write(data)
            temp.close()
            temp_path.replace(path)
        finally:
            temp_path.unlink(missing_ok=True)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def materialize(root, row, offline):
    path = root / cache_path(row)
    if "url" not in row:
        if path.exists():
            data = path.read_bytes()
        elif offline:
            raise ValueError(f"missing cached source {path}")
        else:
            url = (f"https://raw.githubusercontent.com/{row['repository']}/"
                   f"{row['revision']}/{quote(row['path'])}")
            with urlopen(url, timeout=45) as response:
                data = response.read()
        if digest(data) != row["sha256"]:
            raise ValueError(f"source digest mismatch for {row['repository']} {row['path']}")
        store(path, data)
        return len(data)
    if path.exists() and digest(path.read_bytes()) != row["sha256"]:
        raise ValueError(f"cached bound text digest mismatch for {row['url']}")
    content_sha = row.get("content_sha256", row["sha256"])
    content_path = root / "sha256" / content_sha
    if content_path.exists():
        content = content_path.read_bytes()
    elif offline and path.exists() and "extract" in row:
        # The verified extract is the bound text; the PDF is re-derived when cached.
        content = None
    elif offline:
        raise ValueError(f"missing cached source {content_path}")
    else:
        request = Request(row["url"], headers={"User-Agent": "naming-sources/1"})
        with urlopen(request, timeout=90) as response:
            content = response.read()
    if content is not None:
        if digest(content) != content_sha:
            raise ValueError(f"source digest mismatch for {row['url']}")
        store(content_path, content)
        data = derive(row, content)
    else:
        data = path.read_bytes()
    if digest(data) != row["sha256"]:
        raise ValueError(f"bound text digest mismatch for {row['url']}")
    store(path, data)
    return len(data)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lock", type=Path, default=Path(__file__).with_name("naming-sources.lock.json"))
    parser.add_argument("--source-root", type=Path, required=True)
    parser.add_argument("--offline", action="store_true", help="verify existing cache without network access")
    args = parser.parse_args()
    try:
        lock = load_lock(args.lock)
    except (OSError, ValueError, KeyError) as error:
        print(f"SETUP — naming sources: {error}", file=sys.stderr)
        return 2
    (args.source_root / "sha256").mkdir(parents=True, exist_ok=True)
    unique = {row["sha256"]: row for row in lock.values()}
    try:
        with ThreadPoolExecutor(max_workers=4) as pool:
            sizes = list(pool.map(lambda row: materialize(args.source_root, row, args.offline), unique.values()))
    except (OSError, ValueError) as error:
        print(f"FAIL — naming sources: {error}", file=sys.stderr)
        return 1
    print(f"OK — naming sources: {len(lock)} source IDs, {len(unique)} distinct files, {sum(sizes)} verified bytes")
    return 0


if __name__ == "__main__":
    sys.exit(main())
