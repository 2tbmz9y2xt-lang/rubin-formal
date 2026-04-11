#!/usr/bin/env python3
from __future__ import annotations

import unittest
from json import dumps
from pathlib import Path
from tempfile import TemporaryDirectory

from tools import validate_prepush_summary_contract as m


class FormalValidatePrepushSummaryContractTests(unittest.TestCase):
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


if __name__ == "__main__":
    unittest.main()
