#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path

ALLOWED_CHECK_TYPES = {"formal_repo_review"}

BASE_PROMPT = """You are RUBIN formal pre-push reviewer operating in FAIL-CLOSED mode.

INPUT BOUNDARY (HARD):
- You may inspect the repository read-only for context.
- Findings MUST stay grounded in the provided diff bundle and changed claim surface.
- If an unchanged companion file proves the changed claim false, anchor the finding to the changed file line that introduced the wrong claim or omission.
- Do NOT invent spec rules, theorem obligations, or hidden repo state.
- This run reviews a single shard. Default to the diff bundle only.
- If extra context is required, use at most 3 targeted repo reads/grep commands total.
- Do NOT open `AGENTS.md`, any `SKILL.md`, `~/.agents`, `~/.codex`, or files outside the current repo.
- Lens names are review dimensions, not file paths to inspect.
- Valid repo-root metadata companions are exactly: `proof_coverage.json`, `refinement_bridge.json`, `PROOF_COVERAGE.md`, `REGISTRY_COMPLETENESS_POLICY.md`, `RISK_MODEL.md`.
- Do not prepend `RubinFormal/` to those repo-root metadata files.
- If a path probe fails once, do not retry broader variants; continue with the evidence already available.
- After the command budget is exhausted, return the final JSON immediately.

REVIEW CONTRACT (HARD):
- Attack this diff like a hostile formal reviewer.
- Look for vacuous proofs, theorem overclaim, wrapper inflation, parser/live disconnect, bridge drift, registry drift, stale trace assumptions, and docs ahead of proof reality.
- Every finding MUST include exact file+line.
- If evidence is insufficient, do not assert.

OUTPUT CONTRACT (HARD):
- Return JSON only, matching schema:
  {model:string, findings:[{severity,file,line,title,details,suggestion}], summary:string}
- Allowed severities: CRITICAL,HIGH,MEDIUM,LOW,INFO,PERF,STYLE.
- summary MUST be single-line machine-readable:
  CHECK_TYPE=<type>|ACTIVE_LENSES=<csv>|LENSES_COVERED=<lens:ok;...>|NO_FINDINGS=<true|false>|RATIONALE=<text>
- If NO_FINDINGS=true, RATIONALE must explicitly mention every ACTIVE lens.

BLOCK POLICY REMINDER:
- Blocking severities: CRITICAL,HIGH,MEDIUM,LOW,PERF.
- Advisory only: INFO,STYLE.
"""

FORMAL_OVERLAY = """FORMAL HOSTILE PASS:
- Prefer semantic attacks over style notes.
- Check whether theorem names, comments, coverage rows, and docs claim more than the proof actually establishes.
- Check whether the proof is tied to parsed/live behavior or only to wrappers/models.
- Check LIVE vs BRIDGE vs MODEL vs WRAPPER classification explicitly.
- Check metadata and docs for stale claims if theorem/bridge state changed.
- Repository read access is allowed for coupled context, but findings must stay tied to the changed claim surface.
- Prefer no extra tool calls when the diff bundle already proves the point.
"""


def parse_active_lenses(raw: str) -> list[str]:
    if not raw:
        return []
    if raw.strip().lower() == "none":
        return []
    values: list[str] = []
    for item in raw.split(","):
        value = item.strip()
        if value and value not in values:
            values.append(value)
    return values


def read_required_text(path: Path, label: str) -> str:
    if not path.exists():
        raise FileNotFoundError(f"{label} file is missing: {path}")
    return path.read_text(encoding="utf-8")


def read_focus_lines(path: Path) -> list[str]:
    if not path.exists():
        raise FileNotFoundError(f"focus file is missing: {path}")
    return [line.strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip()]


def compose_prompt(*, check_type: str, active_lenses: list[str], fullscan_text: str, focus_lines: list[str], bundle_text: str) -> str:
    if check_type not in ALLOWED_CHECK_TYPES:
        raise ValueError(f"unsupported check_type {check_type!r}")
    if not bundle_text.strip():
        raise ValueError("diff bundle is empty")

    lines: list[str] = []
    if fullscan_text.strip():
        lines.append(fullscan_text.rstrip())
        lines.append("")
    lines.append("Prompt Pack: formal-prepush-v1")
    lines.append(f"CHECK_TYPE={check_type}")
    lines.append(f"ACTIVE_LENSES={','.join(active_lenses) if active_lenses else 'none'}")
    lines.append("")
    lines.append(BASE_PROMPT.strip())
    lines.append("")
    lines.append("CHECK-TYPE OVERLAY:")
    lines.append(FORMAL_OVERLAY.strip())
    lines.append("")
    lines.append("Mandatory review focuses for this diff:")
    if focus_lines:
        lines.extend(f"- {line}" for line in focus_lines)
    else:
        lines.append("- No extra mandatory focus triggers.")
    lines.append("")
    lines.append("Diff bundle follows.")
    lines.append("")
    lines.append(bundle_text.rstrip())
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description="Build rubin-formal pre-push prompt pack.")
    parser.add_argument("--check-type", required=True)
    parser.add_argument("--active-lenses", required=True)
    parser.add_argument("--fullscan-path", required=True)
    parser.add_argument("--focus-path", required=True)
    parser.add_argument("--bundle-path", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args()

    prompt = compose_prompt(
        check_type=args.check_type.strip(),
        active_lenses=parse_active_lenses(args.active_lenses),
        fullscan_text=read_required_text(Path(args.fullscan_path), "fullscan"),
        focus_lines=read_focus_lines(Path(args.focus_path)),
        bundle_text=read_required_text(Path(args.bundle_path), "bundle"),
    )
    Path(args.output).write_text(prompt, encoding="utf-8")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
