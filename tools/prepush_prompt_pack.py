#!/usr/bin/env python3
from __future__ import annotations

import argparse
from pathlib import Path

try:
    from tools.prepush_review_common import (
        allowed_formal_check_types,
        parse_unique_csv,
        read_nonempty_lines,
        read_required_text,
    )
except ImportError:
    from prepush_review_common import (
        allowed_formal_check_types,
        parse_unique_csv,
        read_nonempty_lines,
        read_required_text,
    )

BASE_PROMPT = """You are RUBIN formal pre-push reviewer operating in FAIL-CLOSED mode.

INPUT BOUNDARY (HARD):
- You may inspect the repository read-only for context.
- Findings MUST stay grounded in the provided diff bundle and changed claim surface.
- If an unchanged companion file proves the changed claim false,
  anchor the finding to the changed file line that introduced
  the wrong claim or omission.
- Do NOT invent spec rules, theorem obligations, or hidden repo state.
- This run reviews a single shard. Default to the diff bundle only.
- If extra context is required, use at most 3 targeted repo reads/grep commands total.
- You may open the current repo's `AGENTS.md` for repo-specific review rules.
- Do NOT open any `SKILL.md`, `~/.agents`, `~/.codex`, or files outside the current repo.
- Lens names are review dimensions, not file paths to inspect.
- Valid repo-root metadata companions are exactly:
  `proof_coverage.json`, `refinement_bridge.json`,
  `PROOF_COVERAGE.md`, `REGISTRY_COMPLETENESS_POLICY.md`,
  `RISK_MODEL.md`.
- Do not prepend `RubinFormal/` to those repo-root metadata files.
- If a path probe fails once, do not retry broader variants; continue with the evidence already available.
- After the command budget is exhausted, return the final JSON immediately.

REVIEW CONTRACT (HARD):
- Attack this diff like a hostile formal reviewer.
- Look for vacuous proofs, theorem overclaim, wrapper inflation,
  parser/live disconnect, bridge drift, registry drift,
  stale trace assumptions, and docs ahead of proof reality.
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


def compose_prompt(
    *,
    check_type: str,
    active_lenses: list[str],
    fullscan_text: str,
    focus_lines: list[str],
    bundle_text: str,
) -> str:
    allowed = allowed_formal_check_types()
    if check_type not in allowed:
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


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Build rubin-formal pre-push prompt pack.")
    parser.add_argument("--check-type", required=True)
    parser.add_argument("--active-lenses", required=True)
    parser.add_argument("--fullscan-path", required=True)
    parser.add_argument("--focus-path", required=True)
    parser.add_argument("--bundle-path", required=True)
    parser.add_argument("--output", required=True)
    args = parser.parse_args(argv)

    fullscan_path = Path(args.fullscan_path)
    focus_path = Path(args.focus_path)
    bundle_path = Path(args.bundle_path)
    output_path = Path(args.output)

    try:
        prompt = compose_prompt(
            check_type=args.check_type.strip(),
            active_lenses=parse_unique_csv(
                args.active_lenses,
                reject_empty=True,
                reject_duplicates=True,
            ),
            fullscan_text=read_required_text(fullscan_path, "fullscan"),
            focus_lines=read_nonempty_lines(focus_path, "focus"),
            bundle_text=read_required_text(bundle_path, "bundle"),
        )
    except (OSError, ValueError) as exc:
        raise SystemExit(str(exc)) from exc
    try:
        output_path.write_text(prompt, encoding="utf-8")
    except OSError as exc:
        raise SystemExit(f"failed to write output to {output_path}: {exc}") from exc
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
