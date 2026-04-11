#!/usr/bin/env python3
from __future__ import annotations

import sys
import unittest
from pathlib import Path

TOOLS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS_DIR))

import validate_prepush_summary_contract as m


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


if __name__ == "__main__":
    unittest.main()
