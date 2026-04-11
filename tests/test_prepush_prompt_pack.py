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
                "- Review plan selected by the formal pre-push profile planner.\n"
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
        self.assertIn("relevant `AGENTS.md` files", prompt)

    def test_compose_prompt_rejects_unknown_check_type(self) -> None:
        with self.assertRaisesRegex(ValueError, "unsupported check_type"):
            m.compose_prompt(
                check_type="diff_only",
                active_lenses=[],
                fullscan_text="",
                focus_lines=[],
                bundle_text="=== PUSH TARGET ===\n...",
            )

    def test_compose_prompt_accepts_future_contract_profile(self) -> None:
        original = m.allowed_formal_check_types
        m.allowed_formal_check_types = lambda: {"auto", "future_profile"}
        try:
            prompt = m.compose_prompt(
                check_type="future_profile",
                active_lenses=["code-review"],
                fullscan_text="fullscan",
                focus_lines=["focus"],
                bundle_text="=== PUSH TARGET ===\nPath: RubinFormal/Foo.lean\n",
            )
        finally:
            m.allowed_formal_check_types = original
        self.assertIn("CHECK_TYPE=future_profile", prompt)

    def test_missing_bundle_raises(self) -> None:
        with TemporaryDirectory() as td:
            td_path = Path(td)
            focus = td_path / "focus.txt"
            focus.write_text("x\n", encoding="utf-8")
            fullscan = td_path / "fullscan.txt"
            fullscan.write_text("y\n", encoding="utf-8")
            with self.assertRaisesRegex(SystemExit, "bundle file is missing"):
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

    def test_main_rejects_duplicate_active_lenses(self) -> None:
        with TemporaryDirectory() as td:
            td_path = Path(td)
            focus = td_path / "focus.txt"
            focus.write_text("x\n", encoding="utf-8")
            fullscan = td_path / "fullscan.txt"
            fullscan.write_text("y\n", encoding="utf-8")
            bundle = td_path / "bundle.txt"
            bundle.write_text("=== PUSH TARGET ===\nPath: RubinFormal/Foo.lean\n", encoding="utf-8")
            with self.assertRaisesRegex(SystemExit, "duplicate entry"):
                m.main(
                    [
                        "--check-type",
                        "formal_repo_review",
                        "--active-lenses",
                        "code-review,code-review",
                        "--fullscan-path",
                        str(fullscan),
                        "--focus-path",
                        str(focus),
                        "--bundle-path",
                        str(bundle),
                        "--output",
                        str(td_path / "out.txt"),
                    ]
                )

    def test_main_reports_invalid_contract_cleanly(self) -> None:
        original = m.allowed_formal_check_types
        m.allowed_formal_check_types = lambda: (_ for _ in ()).throw(
            ValueError("invalid review contract JSON")
        )
        try:
            with TemporaryDirectory() as td:
                td_path = Path(td)
                focus = td_path / "focus.txt"
                focus.write_text("x\n", encoding="utf-8")
                fullscan = td_path / "fullscan.txt"
                fullscan.write_text("y\n", encoding="utf-8")
                bundle = td_path / "bundle.txt"
                bundle.write_text("=== PUSH TARGET ===\nPath: RubinFormal/Foo.lean\n", encoding="utf-8")
                with self.assertRaisesRegex(SystemExit, "invalid review contract JSON"):
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
                            str(bundle),
                            "--output",
                            str(td_path / "out.txt"),
                        ]
                    )
        finally:
            m.allowed_formal_check_types = original

    def test_main_reports_missing_fullscan_cleanly(self) -> None:
        with TemporaryDirectory() as td:
            td_path = Path(td)
            focus = td_path / "focus.txt"
            focus.write_text("x\n", encoding="utf-8")
            bundle = td_path / "bundle.txt"
            bundle.write_text("=== PUSH TARGET ===\nPath: RubinFormal/Foo.lean\n", encoding="utf-8")
            with self.assertRaisesRegex(SystemExit, "fullscan file is missing"):
                m.main(
                    [
                        "--check-type",
                        "formal_repo_review",
                        "--active-lenses",
                        "code-review",
                        "--fullscan-path",
                        str(td_path / "missing-fullscan.txt"),
                        "--focus-path",
                        str(focus),
                        "--bundle-path",
                        str(bundle),
                        "--output",
                        str(td_path / "out.txt"),
                    ]
                )


if __name__ == "__main__":
    unittest.main()
