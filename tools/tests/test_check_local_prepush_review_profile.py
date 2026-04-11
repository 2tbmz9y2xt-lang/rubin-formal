#!/usr/bin/env python3
from __future__ import annotations

import json
import sys
import tempfile
import unittest
from pathlib import Path

TOOLS_DIR = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(TOOLS_DIR))

import check_local_prepush_review_profile as m


class FormalReviewProfileTests(unittest.TestCase):
    def test_active_lenses_include_doc_verification_for_docs(self) -> None:
        profile = m.load_profile()
        active = m.active_lenses_for({"proof_coverage.json", "RubinFormal/Foo.lean"}, profile)
        self.assertIn("doc-verification", active)

    def test_main_writes_profile_output(self) -> None:
        with tempfile.TemporaryDirectory() as td:
            td_path = Path(td)
            changed = td_path / "changed.txt"
            changed.write_text("RubinFormal/Foo.lean\nproof_coverage.json\n", encoding="utf-8")
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


if __name__ == "__main__":
    unittest.main()
