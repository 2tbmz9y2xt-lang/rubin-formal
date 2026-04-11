#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path


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
