#!/usr/bin/env python3
from __future__ import annotations

import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tools import prepush_prompt_pack as m


class FormalPromptPackTests(unittest.TestCase):
    def test_compose_prompt_mentions_all_active_lenses(self) -> None:
        prompt = m.compose_prompt(
            check_type="formal_repo_review",
            active_lenses=[
                "code-review",
                "formal-proof-soundness",
                "doc-verification",
            ],
            fullscan_text=(
                "Skill-backed full-scan supplement:\n"
                "- ACTIVE_LENSES=code-review,formal-proof-soundness,doc-verification\n"
            ),
            focus_lines=["Attack theorem statement strength."],
            bundle_text="=== PUSH TARGET ===\nPath: RubinFormal/Foo.lean\n",
        )
        self.assertIn("Prompt Pack: formal-prepush-v1", prompt)
        self.assertIn("CHECK_TYPE=formal_repo_review", prompt)
        self.assertIn(
            "ACTIVE_LENSES=code-review,formal-proof-soundness,doc-verification",
            prompt,
        )

    def test_compose_prompt_rejects_unknown_check_type(self) -> None:
        with self.assertRaisesRegex(ValueError, "unsupported check_type"):
            m.compose_prompt(
                check_type="diff_only",
                active_lenses=[],
                fullscan_text="",
                focus_lines=[],
                bundle_text="=== PUSH TARGET ===\n...",
            )

    def test_missing_bundle_raises(self) -> None:
        with TemporaryDirectory() as td:
            td_path = Path(td)
            focus = td_path / "focus.txt"
            focus.write_text("x\n", encoding="utf-8")
            fullscan = td_path / "fullscan.txt"
            fullscan.write_text("y\n", encoding="utf-8")
            with self.assertRaises(FileNotFoundError):
                m.main(
                    [
                        "--check-type",
                        "formal_repo_review",
                        "--active-lenses",
                        "code-review",
                        "--fullscan-path",
                        str(fullscan),
                        "--focus-path",
                        str(focus),
                        "--bundle-path",
                        str(td_path / "missing.txt"),
                        "--output",
                        str(td_path / "out.txt"),
                    ]
                )


if __name__ == "__main__":
    unittest.main()
