#!/usr/bin/env python3
from __future__ import annotations

import unittest

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

    def test_validate_contract_allows_extra_active_lenses(self) -> None:
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
        self.assertEqual(errors, [])

    def test_parse_lenses_covered_rejects_duplicate_lens(self) -> None:
        with self.assertRaisesRegex(ValueError, "duplicate lens"):
            m.parse_lenses_covered("code-review:ok;code-review:ok")

    def test_parse_lenses_covered_rejects_invalid_status(self) -> None:
        with self.assertRaisesRegex(ValueError, "status not allowed"):
            m.parse_lenses_covered("code-review:passed")

    def test_parse_lenses_covered_accepts_allowed_statuses(self) -> None:
        result = m.parse_lenses_covered("code-review:ok;diff-scan:skip;formal-proof-soundness:na")
        self.assertEqual(result, {"code-review": "ok", "diff-scan": "skip", "formal-proof-soundness": "na"})


if __name__ == "__main__":
    unittest.main()
