#!/usr/bin/env python3
from __future__ import annotations

import json
import unittest
from pathlib import Path
from tempfile import TemporaryDirectory

from tools import check_local_prepush_review_profile as m


class FormalReviewProfileTests(unittest.TestCase):
    def test_active_lenses_follow_configured_conditional_lenses(self) -> None:
        profile = m.ReviewProfile(
            name="formal_repo_review",
            model="gpt-5.4-mini",
            model_reasoning_effort="xhigh",
            stall_seconds=240,
            combine_review_units_when_at_most=1,
            required_lenses=("code-review",),
            conditional_lenses=("doc-verification",),
        )
        active = m.active_lenses_for({"nested/proof_coverage.json"}, profile)
        self.assertEqual(active, ["code-review", "doc-verification"])

        without_conditionals = m.ReviewProfile(
            name="formal_repo_review",
            model="gpt-5.4-mini",
            model_reasoning_effort="xhigh",
            stall_seconds=240,
            combine_review_units_when_at_most=1,
            required_lenses=("code-review",),
            conditional_lenses=(),
        )
        active = m.active_lenses_for({"nested/proof_coverage.json"}, without_conditionals)
        self.assertEqual(active, ["code-review"])

    def test_active_lenses_include_doc_verification_for_docs(self) -> None:
        profile = m.load_profile()
        active = m.active_lenses_for(
            {"proof_coverage.json", "RubinFormal/Foo.lean"},
            profile,
        )
        self.assertIn("doc-verification", active)

    def test_active_lenses_reject_unknown_conditional_lens(self) -> None:
        profile = m.ReviewProfile(
            name="formal_repo_review",
            model="gpt-5.4-mini",
            model_reasoning_effort="xhigh",
            stall_seconds=240,
            combine_review_units_when_at_most=1,
            required_lenses=("code-review",),
            conditional_lenses=("unknown-lens",),
        )
        with self.assertRaisesRegex(ValueError, "unknown conditional lens"):
            m.active_lenses_for({"RubinFormal/Foo.lean"}, profile)

    def test_load_profile_uses_default_profile(self) -> None:
        profile = m.load_profile("auto")
        self.assertEqual(profile.name, "formal_repo_review")

    def test_allowed_check_types_follow_contract_profiles(self) -> None:
        with TemporaryDirectory() as td:
            contract = Path(td) / "prepush_review_contract.json"
            contract.write_text(
                json.dumps(
                    {
                        "default_profile": "formal_repo_review",
                        "profiles": {
                            "formal_repo_review": {
                                "model": "gpt-5.4-mini",
                                "model_reasoning_effort": "xhigh",
                                "stall_seconds": 240,
                                "combine_review_units_when_at_most": 1,
                                "required_lenses": ["code-review"],
                                "conditional_lenses": [],
                            },
                            "future_profile": {
                                "model": "gpt-5.4-mini",
                                "model_reasoning_effort": "high",
                                "stall_seconds": 120,
                                "combine_review_units_when_at_most": 2,
                                "required_lenses": ["code-review"],
                                "conditional_lenses": [],
                            },
                        },
                    }
                ),
                encoding="utf-8",
            )
            self.assertEqual(
                m.allowed_check_types(contract),
                {"auto", "formal_repo_review", "future_profile"},
            )

    def test_focus_lines_use_suffix_match_for_metadata_files(self) -> None:
        focus = m.focus_lines_for(
            {"nested/proof_coverage.json", "nested/refinement_bridge.json"},
        )
        joined = "\n".join(focus)
        self.assertIn("Check proof coverage labels", joined)
        self.assertIn("Check refinement bridge claims", joined)

    def test_main_writes_profile_output(self) -> None:
        with TemporaryDirectory() as td:
            td_path = Path(td)
            changed = td_path / "changed.txt"
            changed.write_text(
                "RubinFormal/Foo.lean\nproof_coverage.json\n",
                encoding="utf-8",
            )
            focus = td_path / "focus.txt"
            fullscan = td_path / "fullscan.txt"
            profile = td_path / "profile.json"
            argv = [
                "--changed-files",
                str(changed),
                "--focus-output",
                str(focus),
                "--fullscan-output",
                str(fullscan),
                "--check-type",
                "auto",
                "--profile-output",
                str(profile),
            ]
            self.assertEqual(m.main(argv), 0)
            payload = json.loads(profile.read_text(encoding="utf-8"))
            self.assertEqual(payload["check_type"], "formal_repo_review")
            self.assertIn("doc-verification", payload["active_lenses"])

    def test_write_fullscan_keeps_path_parameter_as_path(self) -> None:
        with TemporaryDirectory() as td:
            output = Path(td) / "fullscan.txt"
            profile = m.load_profile()
            m.write_fullscan(output, {"RubinFormal/Foo.lean"}, profile, ["code-review"])
            self.assertTrue(output.exists())
            self.assertIn("RubinFormal/Foo.lean", output.read_text(encoding="utf-8"))

    def test_write_fullscan_uses_profile_required_lenses(self) -> None:
        with TemporaryDirectory() as td:
            output = Path(td) / "fullscan.txt"
            profile = m.ReviewProfile(
                name="future_profile",
                model="gpt-5.4-mini",
                model_reasoning_effort="high",
                stall_seconds=120,
                combine_review_units_when_at_most=2,
                required_lenses=("code-review", "diff-scan"),
                conditional_lenses=(),
            )
            m.write_fullscan(output, {"RubinFormal/Foo.lean"}, profile, ["code-review"])
            text = output.read_text(encoding="utf-8")
            self.assertIn("- code-review: baseline correctness/regression pass", text)
            self.assertIn("- diff-scan: strict diff-grounded pass", text)
            self.assertNotIn("formal-proof-soundness", text)

    def test_write_fullscan_does_not_duplicate_required_optional_lenses(self) -> None:
        with TemporaryDirectory() as td:
            output = Path(td) / "fullscan.txt"
            profile = m.ReviewProfile(
                name="future_profile",
                model="gpt-5.4-mini",
                model_reasoning_effort="high",
                stall_seconds=120,
                combine_review_units_when_at_most=2,
                required_lenses=("code-review", "doc-verification"),
                conditional_lenses=(),
            )
            m.write_fullscan(output, {"notes.md"}, profile, ["code-review", "doc-verification"])
            text = output.read_text(encoding="utf-8")
            self.assertEqual(text.count("doc-verification:"), 1)

    def test_main_rejects_unknown_conditional_lens_in_contract(self) -> None:
        with TemporaryDirectory() as td:
            td_path = Path(td)
            contract = td_path / "prepush_review_contract.json"
            contract.write_text(
                json.dumps(
                    {
                        "default_profile": "formal_repo_review",
                        "profiles": {
                            "formal_repo_review": {
                                "model": "gpt-5.4-mini",
                                "model_reasoning_effort": "xhigh",
                                "stall_seconds": 240,
                                "combine_review_units_when_at_most": 1,
                                "required_lenses": ["code-review"],
                                "conditional_lenses": ["unknown-lens"],
                            }
                        },
                    }
                ),
                encoding="utf-8",
            )
            changed = td_path / "changed.txt"
            changed.write_text("RubinFormal/Foo.lean\n", encoding="utf-8")
            focus = td_path / "focus.txt"
            fullscan = td_path / "fullscan.txt"
            profile = td_path / "profile.json"
            original_contract = m.CONTRACT_PATH
            m.CONTRACT_PATH = contract
            try:
                with self.assertRaisesRegex(SystemExit, "unknown conditional lens"):
                    m.main(
                        [
                            "--changed-files",
                            str(changed),
                            "--focus-output",
                            str(focus),
                            "--fullscan-output",
                            str(fullscan),
                            "--check-type",
                            "auto",
                            "--profile-output",
                            str(profile),
                        ]
                    )
            finally:
                m.CONTRACT_PATH = original_contract

    def test_main_reports_invalid_contract_json_cleanly(self) -> None:
        with TemporaryDirectory() as td:
            td_path = Path(td)
            contract = td_path / "prepush_review_contract.json"
            contract.write_text("{not-json", encoding="utf-8")
            changed = td_path / "changed.txt"
            changed.write_text("RubinFormal/Foo.lean\n", encoding="utf-8")
            focus = td_path / "focus.txt"
            fullscan = td_path / "fullscan.txt"
            profile = td_path / "profile.json"
            original_contract = m.CONTRACT_PATH
            m.CONTRACT_PATH = contract
            try:
                with self.assertRaisesRegex(SystemExit, "invalid review contract JSON"):
                    m.main(
                        [
                            "--changed-files",
                            str(changed),
                            "--focus-output",
                            str(focus),
                            "--fullscan-output",
                            str(fullscan),
                            "--check-type",
                            "auto",
                            "--profile-output",
                            str(profile),
                        ]
                    )
            finally:
                m.CONTRACT_PATH = original_contract

    def test_parse_changed_files_requires_manifest(self) -> None:
        with TemporaryDirectory() as td:
            missing = Path(td) / "missing.txt"
            with self.assertRaisesRegex(SystemExit, "Missing changed-files manifest"):
                m.parse_changed_files(missing)

    def test_parse_changed_files_strips_whitespace(self) -> None:
        with TemporaryDirectory() as td:
            manifest = Path(td) / "changed.txt"
            manifest.write_text(
                "  RubinFormal/Foo.lean  \n  tools/bar.py \n",
                encoding="utf-8",
            )
            result = m.parse_changed_files(manifest)
            self.assertIn("RubinFormal/Foo.lean", result)
            self.assertIn("tools/bar.py", result)
            self.assertNotIn("  RubinFormal/Foo.lean  ", result)


if __name__ == "__main__":
    unittest.main()
