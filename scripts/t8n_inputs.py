#!/usr/bin/env python3
"""Shared input composition for the committed t8n corpus."""

from __future__ import annotations

import json
from pathlib import Path


class T8nInputError(ValueError):
    """An authored t8n input is ambiguous or escapes the corpus root."""


def composed_alloc(case_dir: Path, corpus_root: Path) -> dict:
    """Return one alloc assembled from declared bases plus the local file.

    Amsterdam blockchain cases share six system predeploys. Keeping those
    exact bytes in one authored file makes review possible; ``allocIncludes``
    names that file explicitly rather than teaching either runner a hidden
    fork default. Duplicate account keys are rejected, so a case cannot
    silently override shared state.
    """
    case_dir = case_dir.resolve()
    corpus_root = corpus_root.resolve()
    spec = json.loads((case_dir / "case.json").read_text())
    sources = [case_dir / relative for relative in spec.get("allocIncludes", [])]
    sources.append(case_dir / "alloc.json")

    merged: dict = {}
    for source in sources:
        resolved = source.resolve()
        try:
            resolved.relative_to(corpus_root)
        except ValueError as error:
            raise T8nInputError(
                f"{case_dir.name}: alloc include escapes {corpus_root}: {source}"
            ) from error
        try:
            document = json.loads(resolved.read_text())
        except (OSError, json.JSONDecodeError) as error:
            raise T8nInputError(
                f"{case_dir.name}: cannot read alloc input {resolved}: {error}"
            ) from error
        if not isinstance(document, dict):
            raise T8nInputError(
                f"{case_dir.name}: alloc input {resolved} is not an object"
            )
        duplicates = sorted(set(merged) & set(document))
        if duplicates:
            raise T8nInputError(
                f"{case_dir.name}: duplicate alloc account(s): {', '.join(duplicates)}"
            )
        merged.update(document)
    return merged


def materialize_alloc(case_dir: Path, corpus_root: Path, destination: Path) -> None:
    """Write the composed target/Jaune input into an isolated work directory."""
    destination.write_text(json.dumps(composed_alloc(case_dir, corpus_root), indent=2) + "\n")


def materialize_txs_source(
    case_dir: Path, corpus_root: Path, destination: Path
) -> None:
    """Materialize a transaction source list, following one explicit include.

    State-test mirrors intentionally share the blockchain case's transaction
    bytes. Their local ``txs.src.json`` is an authored ``{"include": ...}``
    descriptor, so the two modes cannot drift while every case still owns the
    four source files required by the corpus contract.
    """
    case_dir = case_dir.resolve()
    corpus_root = corpus_root.resolve()
    source = case_dir / "txs.src.json"
    try:
        document = json.loads(source.read_text())
    except (OSError, json.JSONDecodeError) as error:
        raise T8nInputError(
            f"{case_dir.name}: cannot read transaction source {source}: {error}"
        ) from error
    if isinstance(document, dict) and set(document) == {"include"}:
        source = (case_dir / document["include"]).resolve()
        try:
            source.relative_to(corpus_root)
        except ValueError as error:
            raise T8nInputError(
                f"{case_dir.name}: transaction include escapes {corpus_root}: {source}"
            ) from error
        try:
            document = json.loads(source.read_text())
        except (OSError, json.JSONDecodeError) as error:
            raise T8nInputError(
                f"{case_dir.name}: cannot read transaction include {source}: {error}"
            ) from error
    if not isinstance(document, list):
        raise T8nInputError(
            f"{case_dir.name}: transaction source must be a list or one include"
        )
    destination.write_text(json.dumps(document, indent=2) + "\n")
