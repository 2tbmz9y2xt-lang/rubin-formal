#!/usr/bin/env python3
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

try:
    from tools.prepush_review_common import parse_unique_csv
except ImportError:
    from prepush_review_common import parse_unique_csv

REQUIRED_KEYS = ("CHECK_TYPE", "ACTIVE_LENSES", "LENSES_COVERED", "NO_FINDINGS", "RATIONALE")
ALLOWED_CHECK_TYPES = {"formal_repo_review"}
REQUIRED_FINDING_KEYS = (
    "severity",
    "file",
    "line",
    "title",
    "details",
    "suggestion",
)
ALLOWED_LENS_STATUSES = {"ok"}
ALLOWED_SEVERITIES = {"CRITICAL", "HIGH", "MEDIUM", "LOW", "INFO", "PERF", "STYLE"}


def parse_summary(summary: str) -> dict[str, str]:
    if not isinstance(summary, str) or not summary.strip():
        raise ValueError("summary must be a non-empty string")
    if "\n" in summary or "\r" in summary:
        raise ValueError("summary must be single-line")
    fields: dict[str, str] = {}
    for token in summary.split("|"):
        key, sep, value = token.partition("=")
        if not sep:
            raise ValueError(f"summary token missing '=': {token!r}")
        norm_key = key.strip()
        if not norm_key:
            raise ValueError("summary key must be non-empty")
        if norm_key in fields:
            raise ValueError(f"duplicate summary key: {norm_key}")
        fields[norm_key] = value.strip()
    missing = [key for key in REQUIRED_KEYS if key not in fields]
    if missing:
        raise ValueError(f"summary missing required keys: {', '.join(missing)}")
    return fields


def parse_lenses_covered(raw: str) -> dict[str, str]:
    covered: dict[str, str] = {}
    for item in raw.split(";"):
        pair = item.strip()
        if not pair:
            continue
        lens, sep, status = pair.partition(":")
        if not sep:
            raise ValueError(f"LENSES_COVERED item missing ':': {pair!r}")
        lens_name = lens.strip()
        if not re.fullmatch(r"[a-z0-9._-]+", lens_name):
            raise ValueError(f"LENSES_COVERED lens name has unsupported chars: {lens_name!r}")
        if lens_name in covered:
            raise ValueError(f"LENSES_COVERED duplicate lens: {lens_name!r}")
        status_val = status.strip().lower()
        if status_val not in ALLOWED_LENS_STATUSES:
            raise ValueError(
                f"LENSES_COVERED status not allowed: {status_val!r} for lens {lens_name!r}"
            )
        covered[lens_name] = status_val
    return covered


def validate_model(model: object) -> list[str]:
    if not isinstance(model, str) or not model.strip():
        return ["result payload missing model field or model is not a non-empty string"]
    return []


def validate_findings_payload(findings: list[object]) -> list[str]:
    errors: list[str] = []
    for index, finding in enumerate(findings):
        prefix = f"findings[{index}]"
        if not isinstance(finding, dict):
            errors.append(f"{prefix} must be an object")
            continue
        missing = [key for key in REQUIRED_FINDING_KEYS if key not in finding]
        if missing:
            errors.append(f"{prefix} missing required keys: {', '.join(missing)}")
            continue

        severity = finding["severity"]
        if not isinstance(severity, str) or severity not in ALLOWED_SEVERITIES:
            errors.append(
                f"{prefix}.severity must be one of: {', '.join(sorted(ALLOWED_SEVERITIES))}"
            )

        file_path = finding["file"]
        if not isinstance(file_path, str) or not file_path.strip():
            errors.append(f"{prefix}.file must be a non-empty string")

        line = finding["line"]
        if not isinstance(line, int) or isinstance(line, bool) or line < 1:
            errors.append(f"{prefix}.line must be a positive integer")

        for field_name in ("title", "details", "suggestion"):
            value = finding[field_name]
            if not isinstance(value, str) or not value.strip():
                errors.append(f"{prefix}.{field_name} must be a non-empty string")
    return errors


def validate_findings_flag(
    *,
    no_findings_raw: str,
    findings_empty: bool,
) -> tuple[bool, list[str]]:
    errors: list[str] = []
    if no_findings_raw not in {"true", "false"}:
        errors.append(f"NO_FINDINGS must be true|false, got {no_findings_raw!r}")
        return False, errors
    no_findings = no_findings_raw == "true"
    if no_findings != findings_empty:
        errors.append(
            "NO_FINDINGS mismatch with findings payload: "
            f"no_findings={no_findings} findings_empty={findings_empty}"
        )
    return no_findings, errors


def validate_rationale_mentions(
    *,
    rationale: str,
    active_lenses: list[str],
    no_findings: bool,
) -> list[str]:
    errors: list[str] = []
    if not rationale:
        return ["RATIONALE must be non-empty"]
    if not no_findings:
        return errors
    rationale_lc = rationale.lower()
    for lens in active_lenses:
        if lens.lower() not in rationale_lc:
            errors.append(
                "RATIONALE must mention active lens when "
                f"NO_FINDINGS=true: {lens!r}"
            )
    return errors


def validate_contract(
    *,
    summary: str,
    findings: list[object],
    expected_check_type: str,
    expected_active_lenses: list[str],
) -> list[str]:
    errors: list[str] = []
    if expected_check_type not in ALLOWED_CHECK_TYPES:
        errors.append(f"unsupported expected_check_type: {expected_check_type!r}")
        return errors
    try:
        fields = parse_summary(summary)
    except ValueError as exc:
        errors.append(str(exc))
        return errors

    if fields["CHECK_TYPE"] != expected_check_type:
        errors.append(
            "CHECK_TYPE mismatch: "
            f"expected={expected_check_type} actual={fields['CHECK_TYPE']}"
        )
    summary_active_lenses = parse_unique_csv(fields["ACTIVE_LENSES"])
    summary_active_set = set(summary_active_lenses)
    expected_active_set = set(expected_active_lenses)
    if summary_active_set != expected_active_set:
        errors.append(
            "ACTIVE_LENSES mismatch: expected="
            f"{','.join(expected_active_lenses)} actual={','.join(summary_active_lenses)}"
        )
    try:
        covered = parse_lenses_covered(fields["LENSES_COVERED"])
    except ValueError as exc:
        errors.append(str(exc))
        covered = {}

    extra_covered_lenses = sorted(set(covered) - summary_active_set)
    if extra_covered_lenses:
        errors.append(
            "LENSES_COVERED includes lenses outside ACTIVE_LENSES: "
            f"{','.join(extra_covered_lenses)}"
        )

    for lens in summary_active_lenses:
        if covered.get(lens) != "ok":
            errors.append(f"LENSES_COVERED missing ok status for lens={lens!r}")

    no_findings, no_findings_errors = validate_findings_flag(
        no_findings_raw=fields["NO_FINDINGS"].lower(),
        findings_empty=len(findings) == 0,
    )
    errors.extend(no_findings_errors)
    errors.extend(
        validate_rationale_mentions(
            rationale=fields["RATIONALE"],
            active_lenses=summary_active_lenses,
            no_findings=no_findings,
        )
    )
    return errors


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate rubin-formal local pre-push summary contract.")
    parser.add_argument("--result-json", required=True)
    parser.add_argument("--expected-check-type", required=True)
    parser.add_argument("--active-lenses", required=True)
    args = parser.parse_args(argv)

    try:
        raw_text = Path(args.result_json).read_text(encoding="utf-8")
        result = json.loads(raw_text)
    except (OSError, json.JSONDecodeError) as exc:
        print(f"summary-contract: unable to read result-json: {exc}", file=sys.stderr)
        return 2
    if not isinstance(result, dict):
        print("summary-contract: result payload must be a JSON object", file=sys.stderr)
        return 2

    payload_errors: list[str] = []
    payload_errors.extend(validate_model(result.get("model")))
    if "summary" not in result or not isinstance(result.get("summary"), str):
        payload_errors.append("result payload missing summary field or summary is not a string")

    if "findings" not in result:
        payload_errors.append("result payload missing findings field")
        findings: object = []
    else:
        findings = result["findings"]

    if not isinstance(findings, list):
        payload_errors.append("findings must be a list")
    else:
        payload_errors.extend(validate_findings_payload(findings))

    if payload_errors:
        print("summary-contract: FAIL", file=sys.stderr)
        for err in payload_errors:
            print(f"- {err}", file=sys.stderr)
        return 2

    errors = validate_contract(
        summary=result.get("summary", ""),
        findings=findings,
        expected_check_type=args.expected_check_type.strip(),
        expected_active_lenses=parse_unique_csv(args.active_lenses),
    )
    if errors:
        print("summary-contract: FAIL", file=sys.stderr)
        for err in errors:
            print(f"- {err}", file=sys.stderr)
        return 2
    print("summary-contract: PASS", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
