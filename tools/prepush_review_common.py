#!/usr/bin/env python3
from __future__ import annotations

import json
from pathlib import Path

FORMAL_REVIEW_CONTRACT_PATH = Path(__file__).resolve().with_name(
    "prepush_review_contract.json"
)
FORMAL_REVIEW_CONTRACT_SCHEMA_VERSION = 1
FORMAL_LENS_DESCRIPTIONS = {
    "code-review": "baseline correctness/regression pass over the changed claim surface.",
    "diff-scan": "strict diff-grounded pass; do not invent hidden changes.",
    "formal-proof-soundness": "look for vacuity, too-weak theorem statements, and proof gaps.",
    "theorem-classification": "check LIVE/BRIDGE/MODEL/WRAPPER classification against real proof semantics.",
    "bridge-consistency": "check proof_coverage/refinement/docs/bridge metadata drift.",
    "repo-read": "use read-only repo access for coupled context before concluding findings=[].",
    "doc-verification": "changed docs/coverage metadata must not overclaim proof state.",
    "trace-consistency": "changed traces/replay artifacts must stay fresh and coupled to current inputs.",
}


def require_canonical_nonempty_string(value: object, *, label: str) -> str:
    if not isinstance(value, str):
        raise ValueError(f"{label} must be a string")
    canonical = value.strip()
    if not canonical:
        raise ValueError(f"{label} must be a non-empty string")
    if value != canonical:
        raise ValueError(
            f"{label} must not have leading/trailing whitespace: {value!r}"
        )
    return canonical


def require_unique_canonical_string_list(
    value: object,
    *,
    label: str,
) -> list[str]:
    if not isinstance(value, list):
        raise ValueError(f"{label} must be a list of non-empty strings")
    items: list[str] = []
    seen: set[str] = set()
    for position, item in enumerate(value, start=1):
        canonical = require_canonical_nonempty_string(
            item,
            label=f"{label}[{position}]",
        )
        if canonical in seen:
            raise ValueError(f"{label} contains duplicate entry: {canonical!r}")
        seen.add(canonical)
        items.append(canonical)
    return items


def parse_unique_csv(
    raw: str,
    *,
    reject_empty: bool = False,
    reject_duplicates: bool = False,
) -> list[str]:
    if not raw or raw.strip().lower() == "none":
        return []
    values: list[str] = []
    for position, item in enumerate(raw.split(","), start=1):
        value = item.strip()
        if not value:
            if reject_empty:
                raise ValueError(f"CSV contains empty entry at position {position}")
            continue
        if value in values:
            if reject_duplicates:
                raise ValueError(f"CSV contains duplicate entry: {value!r}")
            continue
        values.append(value)
    return values


def load_formal_review_contract(path: Path | None = None) -> dict[str, object]:
    contract_path = FORMAL_REVIEW_CONTRACT_PATH if path is None else path
    try:
        raw = contract_path.read_text(encoding="utf-8")
    except OSError as exc:
        raise ValueError(f"unable to read review contract: {exc}") from exc
    try:
        payload = json.loads(raw)
    except json.JSONDecodeError as exc:
        raise ValueError(f"invalid review contract JSON: {exc}") from exc
    if not isinstance(payload, dict):
        raise ValueError("review contract must be a JSON object")
    schema_version = payload.get("schema_version")
    if schema_version != FORMAL_REVIEW_CONTRACT_SCHEMA_VERSION:
        raise ValueError(
            "unsupported review contract schema_version: "
            f"expected {FORMAL_REVIEW_CONTRACT_SCHEMA_VERSION}, got {schema_version!r}"
        )
    return payload


def allowed_formal_check_types(path: Path | None = None) -> set[str]:
    payload = load_formal_review_contract(path)
    profiles = payload.get("profiles")
    if not isinstance(profiles, dict) or not profiles:
        raise ValueError("review contract missing non-empty object profiles")
    names = set()
    for profile_name in profiles:
        names.add(
            require_canonical_nonempty_string(
                profile_name,
                label="review contract profile name",
            )
        )
    return {"auto", *names}


def describe_formal_lens(lens_name: str) -> str:
    try:
        return FORMAL_LENS_DESCRIPTIONS[lens_name]
    except KeyError as exc:
        raise ValueError(f"missing formal lens description for {lens_name!r}") from exc


def read_required_text(path: Path, label: str) -> str:
    if not path.exists():
        raise FileNotFoundError(f"{label} file is missing: {path}")
    return path.read_text(encoding="utf-8")


def read_nonempty_lines(path: Path, label: str) -> list[str]:
    if not path.exists():
        raise FileNotFoundError(f"{label} file is missing: {path}")
    return [
        line.strip()
        for line in path.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
