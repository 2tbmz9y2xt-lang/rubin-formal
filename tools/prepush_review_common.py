#!/usr/bin/env python3
from __future__ import annotations

from pathlib import Path


def parse_unique_csv(raw: str) -> list[str]:
    if not raw or raw.strip().lower() == "none":
        return []
    values: list[str] = []
    for item in raw.split(","):
        value = item.strip()
        if value and value not in values:
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
