# Local Codex Exec Pre-Push Review for `rubin-formal`

The sanctioned local push path for `rubin-formal` on this machine is:

1. run the usual formal validation you owe for the change (`lake build`, replay checks, metadata updates)
2. call `cl push ...`
3. let `$(git rev-parse --git-path hooks-disabled/pre-push)` build the hostile
   formal review bundle
4. let that hook run isolated local `codex exec` in read-only mode with repository access
5. allow the real network push only if there are no blocking findings

## Runtime contract

- Entry command: `cl push ...`
- Hook: `$(git rev-parse --git-path hooks-disabled/pre-push)`
- Review contract: `tools/prepush_review_contract.json`
- Prompt builder: `tools/prepush_prompt_pack.py`
- Profile planner: `tools/check_local_prepush_review_profile.py`
- Summary validator: `tools/validate_prepush_summary_contract.py`

## Model/profile

- Default profile: `formal_repo_review`
- Model: `gpt-5.4-mini`
- Reasoning: `xhigh`
- Sandbox: read-only
- Repo access: enabled via `codex exec -C <repo-root>`
- Human-readable local profile mirror: local Codex profile `formal-review`
- Fast mode: smaller frontier model route, still fail-closed and repo-aware

If the local reviewer hits a `no-json stall`, the sanctioned runtime may retry
the same shard with lower reasoning (`xhigh -> high -> medium`) before giving
up. That retry path is still the same sanctioned `cl push` -> `pre-push` ->
`codex exec` flow.

This path is intentionally repo-aware. The reviewer may inspect the repository
for coupled context, but findings must stay grounded in the changed claim
surface and point to exact file+line locations.

## Hostile review themes

- vacuous or too-weak theorem statements
- LIVE vs BRIDGE vs MODEL vs WRAPPER misclassification
- parser/live disconnect
- `proof_coverage.json` / `refinement_bridge.json` / docs ahead of proof reality
- replay/trace assumptions that are no longer justified
- theorem names/comments that claim more than the proof establishes

## Blocking policy

- Blocking severities: `CRITICAL`, `HIGH`, `MEDIUM`, `LOW`, `PERF`
- Advisory only: `INFO`, `STYLE`

## Evidence files

The worktree-local artifacts live under the current git-dir:

- `local-security-review/last-run-id`
- `local-security-review/last-run-status`
- `local-security-review/last-run-meta.txt`
- `local-security-review/last-review-bundle.txt`
- `local-security-review/last-prompt.txt`
- `local-security-review/last-codex.log`
- `local-security-review/last-result-raw.json`
- `local-security-review/last-result.json`
