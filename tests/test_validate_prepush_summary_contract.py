#!/usr/bin/env python3
from __future__ import annotations

import contextlib
import io
import unittest
from json import dumps
from pathlib import Path
from tempfile import TemporaryDirectory

from tools import validate_prepush_summary_contract as m


class FormalValidatePrepushSummaryContractTests(unittest.TestCase):
    def test_validate_contract_accepts_future_contract_profile(self) -> None:
        original = m.allowed_formal_check_types
        m.allowed_formal_check_types = lambda: {"auto", "future_profile"}
        try:
            errors = m.validate_contract(
                summary=(
                    "CHECK_TYPE=future_profile|ACTIVE_LENSES=code-review|"
                    "LENSES_COVERED=code-review:ok|NO_FINDINGS=true|RATIONALE=code-review ok"
                ),
                findings=[],
                expected_check_type="future_profile",
                expected_active_lenses=["code-review"],
            )
        finally:
            m.allowed_formal_check_types = original
        self.assertEqual(errors, [])

    def test_validate_contract_reports_invalid_contract_helper_cleanly(self) -> None:
        original = m.allowed_formal_check_types
        m.allowed_formal_check_types = lambda: (_ for _ in ()).throw(
            ValueError("invalid review contract JSON")
        )
        try:
            errors = m.validate_contract(
                summary=(
                    "CHECK_TYPE=formal_repo_review|ACTIVE_LENSES=code-review|"
                    "LENSES_COVERED=code-review:ok|NO_FINDINGS=true|RATIONALE=code-review ok"
                ),
                findings=[],
                expected_check_type="formal_repo_review",
                expected_active_lenses=["code-review"],
            )
        finally:
            m.allowed_formal_check_types = original
        self.assertTrue(any("invalid review contract JSON" in err for err in errors))

    def test_validate_contract_passes_for_valid_summary(self) -> None:
        summary = (
            "CHECK_TYPE=formal_repo_review|ACTIVE_LENSES=code-review,formal-proof-soundness|"
            "LENSES_COVERED=code-review:ok;formal-proof-soundness:ok|"
            "NO_FINDINGS=true|RATIONALE=code-review ok; formal-proof-soundness ok"
        )
        errors = m.validate_contract(
            summary=summary,
            findings=[],
            expected_check_type="formal_repo_review",
            expected_active_lenses=["code-review", "formal-proof-soundness"],
        )
        self.assertEqual(errors, [])

    def test_validate_contract_rejects_wrong_check_type(self) -> None:
        summary = (
            "CHECK_TYPE=diff_only|ACTIVE_LENSES=code-review|"
            "LENSES_COVERED=code-review:ok|NO_FINDINGS=true|RATIONALE=code-review ok"
        )
        errors = m.validate_contract(
            summary=summary,
            findings=[],
            expected_check_type="formal_repo_review",
            expected_active_lenses=["code-review"],
        )
        self.assertTrue(any("CHECK_TYPE mismatch" in err for err in errors))

    def test_validate_contract_rejects_extra_active_lenses(self) -> None:
        summary = (
            "CHECK_TYPE=formal_repo_review|"
            "ACTIVE_LENSES=code-review,formal-proof-soundness,doc-verification|"
            "LENSES_COVERED=code-review:ok;formal-proof-soundness:ok;doc-verification:ok|"
            "NO_FINDINGS=true|"
            "RATIONALE=code-review ok; formal-proof-soundness ok; doc-verification ok"
        )
        errors = m.validate_contract(
            summary=summary,
            findings=[],
            expected_check_type="formal_repo_review",
            expected_active_lenses=["code-review", "formal-proof-soundness"],
        )
        self.assertTrue(any("ACTIVE_LENSES mismatch" in err for err in errors))

    def test_main_rejects_missing_findings_field(self) -> None:
        with TemporaryDirectory() as td:
            result = Path(td) / "result.json"
            result.write_text(dumps({"summary": "x"}), encoding="utf-8")
            rc = m.main(
                [
                    "--result-json",
                    str(result),
                    "--expected-check-type",
                    "formal_repo_review",
                    "--active-lenses",
                    "code-review",
                ]
            )
            self.assertEqual(rc, 2)

    def test_main_reports_load_errors_via_print_fail(self) -> None:
        with TemporaryDirectory() as td:
            stderr = io.StringIO()
            missing = Path(td) / "missing.json"
            with contextlib.redirect_stderr(stderr):
                rc = m.main(
                    [
                        "--result-json",
                        str(missing),
                        "--expected-check-type",
                        "formal_repo_review",
                        "--active-lenses",
                        "code-review",
                    ]
                )
            self.assertEqual(rc, 2)
            err = stderr.getvalue()
            self.assertIn("summary-contract: FAIL", err)
            self.assertIn("unable to read result-json", err)
            self.assertIn(str(missing), err)

    def test_load_result_payload_reports_decode_path(self) -> None:
        with TemporaryDirectory() as td:
            result = Path(td) / "result.json"
            result.write_text("{", encoding="utf-8")
            payload, errors = m.load_result_payload(str(result))
            self.assertIsNone(payload)
            self.assertTrue(
                any(
                    "unable to decode result-json" in err and str(result) in err
                    for err in errors
                )
            )

    def test_main_rejects_missing_model_field(self) -> None:
        with TemporaryDirectory() as td:
            result = Path(td) / "result.json"
            result.write_text(
                dumps(
                    {
                        "summary": (
                            "CHECK_TYPE=formal_repo_review|ACTIVE_LENSES=code-review|"
                            "LENSES_COVERED=code-review:ok|NO_FINDINGS=true|"
                            "RATIONALE=code-review ok"
                        ),
                        "findings": [],
                    }
                ),
                encoding="utf-8",
            )
            rc = m.main(
                [
                    "--result-json",
                    str(result),
                    "--expected-check-type",
                    "formal_repo_review",
                    "--active-lenses",
                    "code-review",
                ]
            )
            self.assertEqual(rc, 2)

    def test_main_rejects_malformed_finding_entry(self) -> None:
        with TemporaryDirectory() as td:
            result = Path(td) / "result.json"
            result.write_text(
                dumps(
                    {
                        "model": "gpt-5.4-mini",
                        "summary": (
                            "CHECK_TYPE=formal_repo_review|ACTIVE_LENSES=code-review|"
                            "LENSES_COVERED=code-review:ok|NO_FINDINGS=false|"
                            "RATIONALE=code-review found issue"
                        ),
                        "findings": [{}],
                    }
                ),
                encoding="utf-8",
            )
            rc = m.main(
                [
                    "--result-json",
                    str(result),
                    "--expected-check-type",
                    "formal_repo_review",
                    "--active-lenses",
                    "code-review",
                ]
            )
            self.assertEqual(rc, 2)

    def test_parse_lenses_covered_accepts_ok_status(self) -> None:
        result = m.parse_lenses_covered(
            "code-review:ok;formal-proof-soundness:ok",
        )
        self.assertEqual(
            result,
            {
                "code-review": "ok",
                "formal-proof-soundness": "ok",
            },
        )

    def test_parse_lenses_covered_rejects_duplicate_lens(self) -> None:
        with self.assertRaisesRegex(ValueError, "duplicate lens"):
            m.parse_lenses_covered("code-review:ok;code-review:ok")

    def test_parse_lenses_covered_rejects_invalid_status(self) -> None:
        with self.assertRaisesRegex(ValueError, "status not allowed"):
            m.parse_lenses_covered("code-review:passed")

    def test_parse_lenses_covered_rejects_empty_entries(self) -> None:
        with self.assertRaisesRegex(ValueError, "empty entry"):
            m.parse_lenses_covered("code-review:ok;;formal-proof-soundness:ok")

    def test_validate_contract_rejects_non_ok_lens_status(self) -> None:
        summary = (
            "CHECK_TYPE=formal_repo_review|ACTIVE_LENSES=code-review|"
            "LENSES_COVERED=code-review:skip|NO_FINDINGS=true|RATIONALE=code-review ok"
        )
        errors = m.validate_contract(
            summary=summary,
            findings=[],
            expected_check_type="formal_repo_review",
            expected_active_lenses=["code-review"],
        )
        self.assertTrue(any("status not allowed" in err for err in errors))
        self.assertFalse(
            any("missing ok status" in err for err in errors),
            msg=f"unexpected cascading errors: {errors}",
        )

    def test_validate_contract_rejects_duplicate_active_lenses(self) -> None:
        summary = (
            "CHECK_TYPE=formal_repo_review|ACTIVE_LENSES=code-review,code-review|"
            "LENSES_COVERED=code-review:ok|NO_FINDINGS=true|RATIONALE=code-review ok"
        )
        errors = m.validate_contract(
            summary=summary,
            findings=[],
            expected_check_type="formal_repo_review",
            expected_active_lenses=["code-review"],
        )
        self.assertTrue(any("duplicate entry" in err for err in errors))
        self.assertFalse(
            any("outside ACTIVE_LENSES" in err for err in errors),
            msg=f"unexpected cascading errors: {errors}",
        )

    def test_validate_contract_rejects_empty_active_lens_entries(self) -> None:
        summary = (
            "CHECK_TYPE=formal_repo_review|ACTIVE_LENSES=code-review,,formal-proof-soundness|"
            "LENSES_COVERED=code-review:ok;formal-proof-soundness:ok|"
            "NO_FINDINGS=true|RATIONALE=code-review ok; formal-proof-soundness ok"
        )
        errors = m.validate_contract(
            summary=summary,
            findings=[],
            expected_check_type="formal_repo_review",
            expected_active_lenses=["code-review", "formal-proof-soundness"],
        )
        self.assertTrue(any("empty entry" in err for err in errors))

    def test_validate_contract_rejects_extra_summary_key(self) -> None:
        summary = (
            "CHECK_TYPE=formal_repo_review|ACTIVE_LENSES=code-review|"
            "LENSES_COVERED=code-review:ok|NO_FINDINGS=true|RATIONALE=code-review ok|"
            "EXTRA=spoof"
        )
        errors = m.validate_contract(
            summary=summary,
            findings=[],
            expected_check_type="formal_repo_review",
            expected_active_lenses=["code-review"],
        )
        self.assertTrue(any("unsupported keys" in err for err in errors))

    def test_main_rejects_finding_with_extra_key(self) -> None:
        with TemporaryDirectory() as td:
            result = Path(td) / "result.json"
            result.write_text(
                dumps(
                    {
                        "model": "gpt-5.4-mini",
                        "summary": (
                            "CHECK_TYPE=formal_repo_review|ACTIVE_LENSES=code-review|"
                            "LENSES_COVERED=code-review:ok|NO_FINDINGS=false|"
                            "RATIONALE=code-review found issue"
                        ),
                        "findings": [
                            {
                                "severity": "LOW",
                                "file": "RubinFormal/Foo.lean",
                                "line": 1,
                                "title": "x",
                                "details": "y",
                                "suggestion": "z",
                                "extra": "oops",
                            }
                        ],
                    }
                ),
                encoding="utf-8",
            )
            rc = m.main(
                [
                    "--result-json",
                    str(result),
                    "--expected-check-type",
                    "formal_repo_review",
                    "--active-lenses",
                    "code-review",
                ]
            )
            self.assertEqual(rc, 2)


if __name__ == "__main__":
    unittest.main()
