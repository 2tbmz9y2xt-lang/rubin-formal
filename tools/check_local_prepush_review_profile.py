#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
from dataclasses import dataclass
from pathlib import Path
from typing import Callable

try:
    from tools.prepush_review_common import (
        describe_formal_lens,
        FORMAL_REVIEW_CONTRACT_PATH,
        load_formal_review_contract,
        require_canonical_nonempty_string,
        require_unique_canonical_string_list,
    )
except ImportError:
    from prepush_review_common import (
        describe_formal_lens,
        FORMAL_REVIEW_CONTRACT_PATH,
        load_formal_review_contract,
        require_canonical_nonempty_string,
        require_unique_canonical_string_list,
    )

CONTRACT_PATH = FORMAL_REVIEW_CONTRACT_PATH
ChangedPredicate = Callable[[set[str]], bool]


@dataclass(frozen=True)
class ReviewProfile:
    name: str
    model: str
    model_reasoning_effort: str
    stall_seconds: int
    combine_review_units_when_at_most: int
    required_lenses: tuple[str, ...]
    conditional_lenses: tuple[str, ...]


def load_contract_payload(path: Path | None = None) -> dict[str, object]:
    contract_path = CONTRACT_PATH if path is None else path
    payload = load_formal_review_contract(contract_path)

    default_profile = payload.get("default_profile")
    require_canonical_nonempty_string(
        default_profile,
        label="review contract default_profile",
    )

    profiles = payload.get("profiles")
    if not isinstance(profiles, dict) or not profiles:
        raise ValueError("review contract missing non-empty object profiles")

    required_fields = (
        "model",
        "model_reasoning_effort",
        "stall_seconds",
        "combine_review_units_when_at_most",
        "required_lenses",
        "conditional_lenses",
    )
    for profile_name, profile_data in profiles.items():
        canonical_profile_name = require_canonical_nonempty_string(
            profile_name,
            label="review contract profile name",
        )
        if not isinstance(profile_data, dict):
            raise ValueError(
                f"review contract profile {canonical_profile_name!r} must be an object"
            )
        missing = [field for field in required_fields if field not in profile_data]
        if missing:
            raise ValueError(
                f"review contract profile {canonical_profile_name!r} missing fields: {', '.join(missing)}"
            )
        for field_name in ("model", "model_reasoning_effort"):
            value = profile_data[field_name]
            if not isinstance(value, str) or not value.strip():
                raise ValueError(
                    f"review contract profile {canonical_profile_name!r} field {field_name!r} must be a non-empty string"
                )
        for field_name in ("stall_seconds", "combine_review_units_when_at_most"):
            value = profile_data[field_name]
            if isinstance(value, bool) or not isinstance(value, int):
                raise ValueError(
                    f"review contract profile {canonical_profile_name!r} field {field_name!r} must be an integer"
                )
            if value < 1:
                raise ValueError(
                    f"review contract profile {canonical_profile_name!r} field {field_name!r} must be an integer >= 1"
                )
        for field_name in ("required_lenses", "conditional_lenses"):
            require_unique_canonical_string_list(
                profile_data[field_name],
                label=(
                    f"review contract profile {canonical_profile_name!r} "
                    f"field {field_name!r}"
                ),
            )

    return payload


def allowed_check_types(path: Path | None = None) -> set[str]:
    contract_path = CONTRACT_PATH if path is None else path
    payload = load_contract_payload(contract_path)
    profiles = payload["profiles"]
    assert isinstance(profiles, dict)
    return {"auto", *(str(name) for name in profiles)}


def changed_contains_suffix(changed: set[str], suffix: str) -> bool:
    return any(path.endswith(suffix) for path in changed)


def has_doc_scope(changed: set[str]) -> bool:
    return (
        any(path.endswith(".md") for path in changed)
        or changed_contains_suffix(changed, "proof_coverage.json")
        or changed_contains_suffix(changed, "refinement_bridge.json")
    )


def has_trace_scope(changed: set[str]) -> bool:
    return any(
        path.startswith("traces/") or path.endswith(".jsonl")
        for path in changed
    )


def has_lean_scope(changed: set[str]) -> bool:
    return any(path.endswith(".lean") for path in changed)


def has_proof_coverage_scope(changed: set[str]) -> bool:
    return changed_contains_suffix(changed, "proof_coverage.json") or changed_contains_suffix(
        changed, "PROOF_COVERAGE.md"
    )


def has_refinement_scope(changed: set[str]) -> bool:
    return changed_contains_suffix(changed, "refinement_bridge.json") or any(
        path.startswith("RubinFormal/Refinement/") for path in changed
    )


def has_markdown_scope(changed: set[str]) -> bool:
    return any(path.endswith(".md") for path in changed)


FOCUS_RULES: tuple[tuple[ChangedPredicate, str], ...] = (
    (
        has_lean_scope,
        "Attack theorem statement strength, vacuity, and hidden assumptions.",
    ),
    (
        has_lean_scope,
        "Check LIVE/BRIDGE/MODEL/WRAPPER classification against what the theorem actually proves.",
    ),
    (
        has_proof_coverage_scope,
        "Check proof coverage labels and evidence taxonomy against actual theorem state.",
    ),
    (
        has_refinement_scope,
        "Check refinement bridge claims against executable/runtime binding and trace assumptions.",
    ),
    (
        has_trace_scope,
        "Check trace freshness, fixture digest, and replay assumptions.",
    ),
    (
        has_markdown_scope,
        "Block docs that overclaim machine-checked status, coverage, or parser/live binding.",
    ),
)


def parse_changed_files(path: Path) -> set[str]:
    if not path.exists():
        raise SystemExit(f"Missing changed-files manifest: {path}")
    raw = path.read_text(encoding="utf-8")
    parts = raw.split("\0") if "\0" in raw else raw.splitlines()
    return {part.strip() for part in parts if part.strip()}


def load_profile(
    requested_check_type: str = "auto",
    path: Path | None = None,
) -> ReviewProfile:
    payload = load_contract_payload(path)
    default_profile = str(payload["default_profile"])
    profiles = payload["profiles"]
    assert isinstance(profiles, dict)
    profile_name = default_profile if requested_check_type == "auto" else requested_check_type
    if profile_name not in profiles:
        raise ValueError(f"unknown review profile: {profile_name!r}")
    data = profiles[profile_name]
    return ReviewProfile(
        name=profile_name,
        model=str(data["model"]),
        model_reasoning_effort=str(data["model_reasoning_effort"]).lower(),
        stall_seconds=int(data["stall_seconds"]),
        combine_review_units_when_at_most=int(data["combine_review_units_when_at_most"]),
        required_lenses=tuple(str(item) for item in data["required_lenses"]),
        conditional_lenses=tuple(str(item) for item in data["conditional_lenses"]),
    )


def active_lenses_for(changed: set[str], profile: ReviewProfile) -> list[str]:
    active = list(profile.required_lenses)
    conditional_rules: dict[str, ChangedPredicate] = {
        "doc-verification": has_doc_scope,
        "trace-consistency": has_trace_scope,
    }
    unknown_lenses = sorted(
        lens for lens in profile.conditional_lenses if lens not in conditional_rules
    )
    if unknown_lenses:
        joined = ", ".join(unknown_lenses)
        raise ValueError(
            f"unknown conditional lens(es) in review profile {profile.name}: {joined}"
        )
    for lens in profile.conditional_lenses:
        predicate = conditional_rules[lens]
        if predicate(changed) and lens not in active:
            active.append(lens)
    return active


def focus_lines_for(changed: set[str]) -> list[str]:
    focus = [message for predicate, message in FOCUS_RULES if predicate(changed)]
    if not focus:
        focus.append(
            "Perform hostile formal review over the changed claim surface "
            "and directly coupled repo files."
        )
    return focus


def write_fullscan(
    path: Path,
    changed: set[str],
    profile: ReviewProfile,
    active_lenses: list[str],
) -> None:
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
        lines.extend(f"- {changed_path}" for changed_path in sorted(changed))
    else:
        lines.append("- none")
    lines.extend(
        [
            "",
            "PROFILE-REQUIRED review lenses:",
        ]
    )
    required_lens_set = set(profile.required_lenses)
    for lens_name in profile.required_lenses:
        lines.append(f"- {lens_name}: {describe_formal_lens(lens_name)}")
    for lens_name in active_lenses:
        if lens_name not in required_lens_set:
            lines.append(f"- {lens_name}: {describe_formal_lens(lens_name)}")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Select rubin-formal local pre-push review profile "
            "and write prompt supplements."
        )
    )
    parser.add_argument("--changed-files", required=True)
    parser.add_argument("--focus-output", required=True)
    parser.add_argument("--fullscan-output", required=True)
    parser.add_argument("--check-type", required=True)
    parser.add_argument("--profile-output", required=True)
    args = parser.parse_args(argv)

    changed_path = Path(args.changed_files)
    focus_output = Path(args.focus_output)
    fullscan_output = Path(args.fullscan_output)
    profile_output = Path(args.profile_output)

    try:
        requested = args.check_type.strip()
        allowed = allowed_check_types()
        if requested not in allowed:
            allowed_joined = ", ".join(sorted(allowed))
            raise ValueError(
                f"unsupported check_type {requested!r}; expected one of: {allowed_joined}"
            )
        changed = parse_changed_files(changed_path)
        profile = load_profile(requested)
        active_lenses = active_lenses_for(changed, profile)
        write_fullscan(fullscan_output, changed, profile, active_lenses)
        focus_lines = focus_lines_for(changed)
        focus_output.write_text(
            "\n".join(focus_lines) + "\n",
            encoding="utf-8",
        )

        profile_payload = {
            "profile": profile.name,
            "check_type": profile.name,
            "why": "Formal repo requires hostile theorem/metadata review with read-only repo context.",
            "model": profile.model,
            "model_reasoning_effort": profile.model_reasoning_effort,
            "stall_seconds": profile.stall_seconds,
            "combine_review_units_when_at_most": profile.combine_review_units_when_at_most,
            "required_lenses": list(profile.required_lenses),
            "conditional_lenses": list(profile.conditional_lenses),
            "active_lenses": active_lenses,
        }
        profile_output.write_text(
            json.dumps(profile_payload, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )
    except (OSError, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
