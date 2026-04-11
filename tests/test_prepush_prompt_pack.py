#!/usr/bin/env python3
from __future__ import annotations

import tempfile
import unittest
from pathlib import Path

from tools import prepush_prompt_pack as m


class FormalPrepushPromptPackTests(unittest.TestCase):
    def test_compose_prompt_includes_formal_contract(self) -> None:
        prompt = m.compose_prompt(
            check_type="formal_repo_review",
            active_lenses=["code-review", "formal-proof-soundness"],
            fullscan_text="Skill-backed full-scan supplement:",
            focus_lines=["Focus A"],
            bundle_text="=== PUSH TARGET ===\n...",
        )
        self.assertIn("RUBIN formal pre-push reviewer", prompt)
        self.assertIn("Prompt Pack: formal-prepush-v1", prompt)
        self.assertIn("ACTIVE_LENSES=code-review,formal-proof-soundness", prompt)
        self.assertIn("Attack this diff like a hostile formal reviewer", prompt)

    def test_compose_prompt_rejects_unknown_check_type(self) -> None:
        with self.assertRaisesRegex(ValueError, "unsupported check_type"):
            m.compose_prompt(
                check_type="diff_only",
                active_lenses=[],
                fullscan_text="",
                focus_lines=[],
                bundle_text="=== PUSH TARGET ===\n...",
            )

    def test_read_required_text_fails_closed_when_missing(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            missing = Path(td) / "missing.txt"
            with self.assertRaisesRegex(FileNotFoundError, "fullscan file is missing"):
                m.read_required_text(missing, "fullscan")


if __name__ == "__main__":
    unittest.main()
