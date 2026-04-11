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


def validate_summary_text(summary: object) -> str | None:
    if not isinstance(summary, str) or not summary.strip():
        return "summary must be a non-empty string"
    if "\n" in summary or "\r" in summary:
        return "summary must be single-line"
    return None


def add_summary_field(fields: dict[str, str], token: str) -> None:
    key, sep, value = token.partition("=")
    if not sep:
        raise ValueError(f"summary token missing '=': {token!r}")
    norm_key = key.strip()
    if not norm_key:
        raise ValueError("summary key must be non-empty")
    if norm_key in fields:
        raise ValueError(f"duplicate summary key: {norm_key}")
    fields[norm_key] = value.strip()


def parse_summary(summary: str) -> dict[str, str]:
    summary_error = validate_summary_text(summary)
    if summary_error is not None:
        raise ValueError(summary_error)

    fields: dict[str, str] = {}
    for token in summary.split("|"):
        add_summary_field(fields, token)

    missing = [key for key in REQUIRED_KEYS if key not in fields]
    if missing:
        raise ValueError(f"summary missing required keys: {', '.join(missing)}")
    extra = sorted(key for key in fields if key not in REQUIRED_KEYS)
    if extra:
        raise ValueError(f"summary contains unsupported keys: {', '.join(extra)}")
    return fields


def validate_lens_name(lens_name: str) -> None:
    if not re.fullmatch(r"[a-z0-9._-]+", lens_name):
        raise ValueError(f"LENSES_COVERED lens name has unsupported chars: {lens_name!r}")


def validate_lens_status(lens_name: str, status_val: str) -> None:
    if status_val not in ALLOWED_LENS_STATUSES:
        raise ValueError(
            f"LENSES_COVERED status not allowed: {status_val!r} for lens {lens_name!r}"
        )


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
        validate_lens_name(lens_name)
        if lens_name in covered:
            raise ValueError(f"LENSES_COVERED duplicate lens: {lens_name!r}")
        status_val = status.strip().lower()
        validate_lens_status(lens_name, status_val)
        covered[lens_name] = status_val
    return covered


def validate_model(model: object) -> list[str]:
    if not isinstance(model, str) or not model.strip():
        return ["result payload missing model field or model is not a non-empty string"]
    return []


def validate_severity(prefix: str, severity: object) -> list[str]:
    if isinstance(severity, str) and severity in ALLOWED_SEVERITIES:
        return []
    allowed = ", ".join(sorted(ALLOWED_SEVERITIES))
    return [f"{prefix}.severity must be one of: {allowed}"]


def validate_nonempty_string(prefix: str, field_name: str, value: object) -> list[str]:
    if isinstance(value, str) and value.strip():
        return []
    return [f"{prefix}.{field_name} must be a non-empty string"]


def validate_line_number(prefix: str, line: object) -> list[str]:
    if isinstance(line, int) and not isinstance(line, bool) and line >= 1:
        return []
    return [f"{prefix}.line must be a positive integer"]


def validate_finding_entry(index: int, finding: object) -> list[str]:
    prefix = f"findings[{index}]"
    if not isinstance(finding, dict):
        return [f"{prefix} must be an object"]

    missing = [key for key in REQUIRED_FINDING_KEYS if key not in finding]
    if missing:
        return [f"{prefix} missing required keys: {', '.join(missing)}"]

    errors: list[str] = []
    errors.extend(validate_severity(prefix, finding["severity"]))
    errors.extend(validate_nonempty_string(prefix, "file", finding["file"]))
    errors.extend(validate_line_number(prefix, finding["line"]))
    for field_name in ("title", "details", "suggestion"):
        errors.extend(validate_nonempty_string(prefix, field_name, finding[field_name]))
    return errors


def validate_findings_payload(findings: list[object]) -> list[str]:
    errors: list[str] = []
    for index, finding in enumerate(findings):
        errors.extend(validate_finding_entry(index, finding))
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
    if not rationale:
        return ["RATIONALE must be non-empty"]
    if not no_findings:
        return []

    errors: list[str] = []
    rationale_lc = rationale.lower()
    for lens in active_lenses:
        if lens.lower() not in rationale_lc:
            errors.append(
                "RATIONALE must mention active lens when "
                f"NO_FINDINGS=true: {lens!r}"
            )
    return errors


def validate_check_type(
    fields: dict[str, str],
    expected_check_type: str,
) -> list[str]:
    if fields["CHECK_TYPE"] == expected_check_type:
        return []
    return [
        "CHECK_TYPE mismatch: "
        f"expected={expected_check_type} actual={fields['CHECK_TYPE']}"
    ]


def validate_active_lenses(
    fields: dict[str, str],
    expected_active_lenses: list[str],
) -> tuple[list[str], list[str]]:
    try:
        summary_active_lenses = parse_unique_csv(
            fields["ACTIVE_LENSES"],
            reject_empty=True,
            reject_duplicates=True,
        )
    except ValueError as exc:
        return [], [str(exc)]
    summary_active_set = set(summary_active_lenses)
    expected_active_set = set(expected_active_lenses)
    if summary_active_set == expected_active_set:
        return summary_active_lenses, []
    return summary_active_lenses, [
        "ACTIVE_LENSES mismatch: expected="
        f"{','.join(expected_active_lenses)} actual={','.join(summary_active_lenses)}"
    ]


def parse_covered_or_errors(raw: str) -> tuple[dict[str, str], list[str]]:
    try:
        return parse_lenses_covered(raw), []
    except ValueError as exc:
        return {}, [str(exc)]


def validate_covered_lenses(
    summary_active_lenses: list[str],
    covered: dict[str, str],
) -> list[str]:
    errors: list[str] = []
    summary_active_set = set(summary_active_lenses)
    extra_covered_lenses = sorted(set(covered) - summary_active_set)
    if extra_covered_lenses:
        errors.append(
            "LENSES_COVERED includes lenses outside ACTIVE_LENSES: "
            f"{','.join(extra_covered_lenses)}"
        )
    for lens in summary_active_lenses:
        if covered.get(lens) != "ok":
            errors.append(f"LENSES_COVERED missing ok status for lens={lens!r}")
    return errors


def validate_contract(
    *,
    summary: str,
    findings: list[object],
    expected_check_type: str,
    expected_active_lenses: list[str],
) -> list[str]:
    if expected_check_type not in ALLOWED_CHECK_TYPES:
        return [f"unsupported expected_check_type: {expected_check_type!r}"]

    try:
        fields = parse_summary(summary)
    except ValueError as exc:
        return [str(exc)]

    summary_active_lenses, active_lens_errors = validate_active_lenses(
        fields,
        expected_active_lenses,
    )
    covered, covered_errors = parse_covered_or_errors(fields["LENSES_COVERED"])
    no_findings, no_findings_errors = validate_findings_flag(
        no_findings_raw=fields["NO_FINDINGS"].lower(),
        findings_empty=len(findings) == 0,
    )

    errors: list[str] = []
    errors.extend(validate_check_type(fields, expected_check_type))
    errors.extend(active_lens_errors)
    errors.extend(covered_errors)
    errors.extend(validate_covered_lenses(summary_active_lenses, covered))
    errors.extend(no_findings_errors)
    errors.extend(
        validate_rationale_mentions(
            rationale=fields["RATIONALE"],
            active_lenses=summary_active_lenses,
            no_findings=no_findings,
        )
    )
    return errors


def load_result_payload(path: str) -> tuple[dict[str, object] | None, list[str]]:
    try:
        raw_text = Path(path).read_text(encoding="utf-8")
        result = json.loads(raw_text)
    except (OSError, json.JSONDecodeError) as exc:
        return None, [f"summary-contract: unable to read result-json: {exc}"]
    if not isinstance(result, dict):
        return None, ["summary-contract: result payload must be a JSON object"]
    return result, []


def extract_findings(result: dict[str, object]) -> tuple[list[object], list[str]]:
    if "findings" not in result:
        return [], ["result payload missing findings field"]
    findings = result["findings"]
    if not isinstance(findings, list):
        return [], ["findings must be a list"]
    return findings, validate_findings_payload(findings)


def payload_validation_errors(result: dict[str, object]) -> tuple[str, list[object], list[str]]:
    errors: list[str] = []
    errors.extend(validate_model(result.get("model")))

    summary_obj = result.get("summary")
    if not isinstance(summary_obj, str):
        errors.append("result payload missing summary field or summary is not a string")
        summary = ""
    else:
        summary = summary_obj

    findings, finding_errors = extract_findings(result)
    errors.extend(finding_errors)
    return summary, findings, errors


def print_fail(errors: list[str]) -> int:
    print("summary-contract: FAIL", file=sys.stderr)
    for err in errors:
        print(f"- {err}", file=sys.stderr)
    return 2


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Validate rubin-formal local pre-push summary contract.")
    parser.add_argument("--result-json", required=True)
    parser.add_argument("--expected-check-type", required=True)
    parser.add_argument("--active-lenses", required=True)
    args = parser.parse_args(argv)

    result, load_errors = load_result_payload(args.result_json)
    if load_errors:
        for err in load_errors:
            print(err, file=sys.stderr)
        return 2
    assert result is not None

    summary, findings, payload_errors = payload_validation_errors(result)
    if payload_errors:
        return print_fail(payload_errors)

    try:
        expected_active_lenses = parse_unique_csv(
            args.active_lenses,
            reject_empty=True,
            reject_duplicates=True,
        )
    except ValueError as exc:
        return print_fail([str(exc)])

    errors = validate_contract(
        summary=summary,
        findings=findings,
        expected_check_type=args.expected_check_type.strip(),
        expected_active_lenses=expected_active_lenses,
    )
    if errors:
        return print_fail(errors)
    print("summary-contract: PASS", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
