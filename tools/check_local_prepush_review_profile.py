#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path

CONTRACT_PATH = Path(__file__).resolve().with_name("prepush_review_contract.json")
ALLOWED_CHECK_TYPES = {"auto", "formal_repo_review"}


@dataclass(frozen=True)
class ReviewProfile:
    name: str
    model: str
    model_reasoning_effort: str
    stall_seconds: int
    combine_review_units_when_at_most: int
    required_lenses: tuple[str, ...]
    conditional_lenses: tuple[str, ...]


def parse_changed_files(path: Path) -> set[str]:
    if not path.exists():
        return set()
    raw = path.read_text(encoding="utf-8")
    parts = raw.split("\0") if "\0" in raw else raw.splitlines()
    return {part for part in parts if part}


def load_profile(path: Path = CONTRACT_PATH) -> ReviewProfile:
    payload = json.loads(path.read_text(encoding="utf-8"))
    profiles = payload["profiles"]
    data = profiles["formal_repo_review"]
    return ReviewProfile(
        name="formal_repo_review",
        model=str(data["model"]),
        model_reasoning_effort=str(data["model_reasoning_effort"]).lower(),
        stall_seconds=int(data["stall_seconds"]),
        combine_review_units_when_at_most=int(data["combine_review_units_when_at_most"]),
        required_lenses=tuple(str(item) for item in data["required_lenses"]),
        conditional_lenses=tuple(str(item) for item in data["conditional_lenses"]),
    )


def active_lenses_for(changed: set[str], profile: ReviewProfile) -> list[str]:
    active = list(profile.required_lenses)
    if any(path.endswith(".md") or path.endswith("proof_coverage.json") or path.endswith("refinement_bridge.json") for path in changed):
        active.append("doc-verification")
    if any(path.startswith("traces/") or path.endswith(".jsonl") for path in changed):
        active.append("trace-consistency")
    return active


def focus_lines_for(changed: set[str]) -> list[str]:
    focus: list[str] = []
    if any(path.endswith(".lean") for path in changed):
        focus.append("Attack theorem statement strength, vacuity, and hidden assumptions.")
        focus.append("Check LIVE/BRIDGE/MODEL/WRAPPER classification against what the theorem actually proves.")
    if "proof_coverage.json" in changed or "PROOF_COVERAGE.md" in changed:
        focus.append("Check proof coverage labels and evidence taxonomy against actual theorem state.")
    if "refinement_bridge.json" in changed or any(path.startswith("RubinFormal/Refinement/") for path in changed):
        focus.append("Check refinement bridge claims against executable/runtime binding and trace assumptions.")
    if any(path.startswith("traces/") or path.endswith(".jsonl") for path in changed):
        focus.append("Check trace freshness, fixture digest, and replay assumptions.")
    if any(path.endswith(".md") for path in changed):
        focus.append("Block docs that overclaim machine-checked status, coverage, or parser/live binding.")
    if not focus:
        focus.append("Perform hostile formal review over the changed claim surface and directly coupled repo files.")
    return focus


def write_fullscan(path: Path, changed: set[str], profile: ReviewProfile, active_lenses: list[str]) -> None:
    lines = [
        "Skill-backed full-scan supplement:",
        "- This is a local formal pre-push review plan for rubin-formal.",
        "- The reviewer may inspect the repository read-only for context, but findings must stay grounded in the changed claim surface.",
        f"- Selected review profile: {profile.name}.",
        f"- Model route: {profile.model} ({profile.model_reasoning_effort}), combine-if-paths<={profile.combine_review_units_when_at_most}.",
        f"- ACTIVE_LENSES: {','.join(active_lenses)}",
        "",
        "Changed files in scope:",
    ]
    if changed:
        lines.extend(f"- {path}" for path in sorted(changed))
    else:
        lines.append("- none")
    lines.extend(
        [
            "",
            "PROFILE-REQUIRED review lenses:",
            "- code-review: baseline correctness/regression pass over the changed claim surface.",
            "- diff-scan: strict diff-grounded pass; do not invent hidden changes.",
            "- formal-proof-soundness: look for vacuity, too-weak theorem statements, and proof gaps.",
            "- theorem-classification: check LIVE/BRIDGE/MODEL/WRAPPER classification against real proof semantics.",
            "- bridge-consistency: check proof_coverage/refinement/docs/bridge metadata drift.",
            "- repo-read: use read-only repo access for coupled context before concluding findings=[].",
        ]
    )
    if "doc-verification" in active_lenses:
        lines.append("- doc-verification: changed docs/coverage metadata must not overclaim proof state.")
    if "trace-consistency" in active_lenses:
        lines.append("- trace-consistency: changed traces/replay artifacts must stay fresh and coupled to current inputs.")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Select rubin-formal local pre-push review profile and write prompt supplements.")
    parser.add_argument("--changed-files", required=True)
    parser.add_argument("--focus-output", required=True)
    parser.add_argument("--fullscan-output", required=True)
    parser.add_argument("--check-type", required=True)
    parser.add_argument("--profile-output", required=True)
    args = parser.parse_args(argv)

    requested = args.check_type.strip()
    if requested not in ALLOWED_CHECK_TYPES:
        allowed = ", ".join(sorted(ALLOWED_CHECK_TYPES))
        raise SystemExit(f"unsupported check_type {requested!r}; expected one of: {allowed}")

    changed = parse_changed_files(Path(args.changed_files))
    profile = load_profile()
    active_lenses = active_lenses_for(changed, profile)
    focus_lines = focus_lines_for(changed)

    Path(args.focus_output).write_text("\n".join(focus_lines) + "\n", encoding="utf-8")
    write_fullscan(Path(args.fullscan_output), changed, profile, active_lenses)

    profile_payload = {
        "profile": profile.name,
        "check_type": "formal_repo_review",
        "why": "Formal repo requires hostile theorem/metadata review with read-only repo context.",
        "model": profile.model,
        "model_reasoning_effort": profile.model_reasoning_effort,
        "stall_seconds": profile.stall_seconds,
        "combine_review_units_when_at_most": profile.combine_review_units_when_at_most,
        "required_lenses": list(profile.required_lenses),
        "conditional_lenses": list(profile.conditional_lenses),
        "active_lenses": active_lenses,
    }
    Path(args.profile_output).write_text(json.dumps(profile_payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
