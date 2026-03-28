#!/usr/bin/env python3
from __future__ import annotations

import json
import re
import sys
from functools import lru_cache
from pathlib import Path


REPO_PREFIX = "rubin-formal/"
MODULE_PREFIX = "RubinFormal/"

# Intentionally narrow shared-op parity scope after Q-FORMAL-REGISTRY-EVIDENCE-LEVEL-ALIGN-01.
# `retarget_v1` and `fork_choice_select` remain honest supplemental bridge lanes whose
# bridge evidence level is narrower than the broader section row on purpose.
SHARED_OP_PARITY = {
    "sighash_v1": "sighash_v1",
    "da_set_integrity": "da_set_integrity",
    "weight_accounting": "weight_accounting",
}

DECL_KINDS = ("theorem", "lemma", "def", "abbrev")


def fail(msg: str) -> int:
    print(f"ERROR: {msg}", file=sys.stderr)
    return 1


def short_name(qualified: str) -> str:
    return qualified.split(".")[-1]


def declaration_regex(name: str) -> re.Pattern[str]:
    kinds = "|".join(DECL_KINDS)
    return re.compile(rf"(?m)^\s*(?:private\s+|protected\s+)?(?:{kinds})\s+{re.escape(name)}\b")


def rel_repo_path(repo_root: Path, path: Path) -> str:
    return str(path.resolve().relative_to(repo_root.resolve()))


def lean_repo_path(repo_root: Path, rel_path: str) -> Path:
    if rel_path.startswith(REPO_PREFIX):
        return repo_root / rel_path[len(REPO_PREFIX) :]
    if rel_path.startswith(MODULE_PREFIX):
        return repo_root / rel_path
    raise ValueError(f"unsupported non-repo path in registry: {rel_path}")


def olean_path(repo_root: Path, rel_path: str) -> Path:
    normalized = rel_path
    if normalized.startswith(REPO_PREFIX):
        normalized = normalized[len(REPO_PREFIX) :]
    if not normalized.startswith(MODULE_PREFIX) or not normalized.endswith(".lean"):
        raise ValueError(f"registered file is outside RubinFormal build graph surface: {rel_path}")
    suffix = normalized[: -len(".lean")]
    return repo_root / ".lake" / "build" / "lib" / f"{suffix}.olean"


def iter_registry_paths(coverage: dict, bridge: dict) -> set[str]:
    refs: set[str] = set()
    for row in coverage.get("coverage", []):
        if not isinstance(row, dict):
            continue
        if isinstance(row.get("file"), str):
            refs.add(row["file"])
        theorem_files = row.get("theorem_files", {})
        if isinstance(theorem_files, dict):
            for path in theorem_files.values():
                if isinstance(path, str):
                    refs.add(path)
    for row in bridge.get("critical_ops", []):
        if not isinstance(row, dict):
            continue
        for key in ("lean_file", "theorem_file"):
            if isinstance(row.get(key), str):
                refs.add(row[key])
    return refs


def iter_registered_theorems(coverage: dict, bridge: dict) -> tuple[list[tuple[str, str | None]], list[tuple[str, str | None]]]:
    coverage_theorems: list[tuple[str, str | None]] = []
    for row in coverage.get("coverage", []):
        if not isinstance(row, dict):
            continue
        theorem_files = row.get("theorem_files", {})
        theorem_map = theorem_files if isinstance(theorem_files, dict) else {}
        for theorem in row.get("theorems", []):
            if isinstance(theorem, str):
                coverage_theorems.append((theorem, theorem_map.get(theorem)))

    bridge_theorems: list[tuple[str, str | None]] = []
    for row in bridge.get("critical_ops", []):
        if not isinstance(row, dict):
            continue
        lean_file = row.get("lean_file") if isinstance(row.get("lean_file"), str) else None
        theorem_file = row.get("theorem_file") if isinstance(row.get("theorem_file"), str) else None
        model_theorem = row.get("model_theorem")
        if isinstance(model_theorem, str):
            bridge_theorems.append((model_theorem, lean_file))
        for theorem in row.get("supporting_theorems", []):
            if isinstance(theorem, str):
                bridge_theorems.append((theorem, theorem_file))
    return coverage_theorems, bridge_theorems


def main() -> int:
    repo_root = Path(__file__).resolve().parents[1]
    coverage_path = repo_root / "proof_coverage.json"
    bridge_path = repo_root / "refinement_bridge.json"

    if not coverage_path.exists():
        return fail("proof_coverage.json not found")
    if not bridge_path.exists():
        return fail("refinement_bridge.json not found")

    coverage = json.loads(coverage_path.read_text(encoding="utf-8"))
    bridge = json.loads(bridge_path.read_text(encoding="utf-8"))
    lean_files = sorted((repo_root / "RubinFormal").rglob("*.lean"))
    if not lean_files:
        return fail("no Lean files found under RubinFormal/")

    @lru_cache(maxsize=None)
    def file_text(path: Path) -> str:
        return path.read_text(encoding="utf-8")

    @lru_cache(maxsize=None)
    def theorem_exists_anywhere(qualified: str) -> bool:
        pattern = declaration_regex(short_name(qualified))
        return any(pattern.search(file_text(path)) for path in lean_files)

    @lru_cache(maxsize=None)
    def theorem_exists_in_file(qualified: str, rel_path: str) -> bool:
        abs_path = lean_repo_path(repo_root, rel_path)
        if not abs_path.exists():
            return False
        return bool(declaration_regex(short_name(qualified)).search(file_text(abs_path)))

    bad = False

    for rel_path in sorted(iter_registry_paths(coverage, bridge)):
        try:
            abs_path = lean_repo_path(repo_root, rel_path)
        except ValueError as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
            bad = True
            continue
        if not abs_path.exists():
            print(f"ERROR: referenced Lean file does not exist: {rel_path}", file=sys.stderr)
            bad = True
            continue
        try:
            built = olean_path(repo_root, rel_path)
        except ValueError as exc:
            print(f"ERROR: {exc}", file=sys.stderr)
            bad = True
            continue
        if not built.exists():
            print(
                f"ERROR: registered Lean file is outside the default build graph or failed to build: "
                f"{rel_path} (missing {rel_repo_path(repo_root, built)})",
                file=sys.stderr,
            )
            bad = True

    coverage_theorems, bridge_theorems = iter_registered_theorems(coverage, bridge)

    for theorem, rel_path in coverage_theorems:
        if rel_path:
            if not theorem_exists_in_file(theorem, rel_path):
                print(
                    f"ERROR: proof_coverage theorem `{theorem}` not found in declared file `{rel_path}`",
                    file=sys.stderr,
                )
                bad = True
        elif not theorem_exists_anywhere(theorem):
            print(f"ERROR: proof_coverage theorem `{theorem}` not found in RubinFormal/", file=sys.stderr)
            bad = True

    for theorem, rel_path in bridge_theorems:
        if rel_path and theorem_exists_in_file(theorem, rel_path):
            continue
        if theorem_exists_anywhere(theorem):
            continue
        location = rel_path if rel_path else "RubinFormal/"
        print(f"ERROR: refinement_bridge theorem `{theorem}` not found in `{location}`", file=sys.stderr)
        bad = True

    coverage_rows = {
        row["section_key"]: row
        for row in coverage.get("coverage", [])
        if isinstance(row, dict) and isinstance(row.get("section_key"), str)
    }
    bridge_rows = {
        row["op"]: row
        for row in bridge.get("critical_ops", [])
        if isinstance(row, dict) and isinstance(row.get("op"), str)
    }

    for op, section_key in SHARED_OP_PARITY.items():
        bridge_row = bridge_rows.get(op)
        coverage_row = coverage_rows.get(section_key)
        if bridge_row is None:
            print(f"ERROR: shared-op parity row missing in refinement_bridge.json: {op}", file=sys.stderr)
            bad = True
            continue
        if coverage_row is None:
            print(f"ERROR: shared-op parity row missing in proof_coverage.json: {section_key}", file=sys.stderr)
            bad = True
            continue
        if bridge_row.get("evidence_level") != coverage_row.get("evidence_level"):
            print(
                f"ERROR: shared-op evidence level drift for {op}: "
                f"refinement_bridge={bridge_row.get('evidence_level')} vs "
                f"proof_coverage[{section_key}]={coverage_row.get('evidence_level')}",
                file=sys.stderr,
            )
            bad = True

    if bad:
        return 1

    print(
        "OK: formal registry truth passed "
        f"({len(iter_registry_paths(coverage, bridge))} registered Lean files reachable, "
        f"{len(coverage_theorems)} proof_coverage theorem refs, "
        f"{len(bridge_theorems)} refinement_bridge theorem refs, "
        f"{len(SHARED_OP_PARITY)} shared-op parity rows)."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
