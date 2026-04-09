# RUBIN Formal (Lean 4)

Machine-checked formal proof surface for the RUBIN L1 blockchain protocol.

## Contents

- Lean 4 package `RubinFormal`
- `proof_coverage.json` — machine-readable coverage registry with 28 section entries
- Each registry entry carries explicit `evidence_level`, `notes`, and `limitations` so that public claims never outrun the actual proof boundary

## Claim boundary (critical)

This proof pack is an executable replay/refinement surface for conformance fixtures (CV-*.json) and live Lean theorems over select canonical sections. It provides reproducible machine-checked evidence but **is not** a universal formal verification of the entire CANONICAL spec.

Current machine-readable status: `proof_level=refinement`, `claim_level=refined`.

Permitted claim formulations (OK):

- "Lean executable semantics replay all conformance fixtures (CV-*.json)"
- "Go (reference) → Lean refinement is checked for critical ops over the conformance fixture set"
- "Pinned-section coverage is machine-readable with explicit evidence levels: universal, behavioral, assumption-backed, and contract-level"

Prohibited claim formulations (NOT OK):

- "formal verification of RUBIN consensus / CANONICAL"
- "bit-exact wire/serialization proven"
- "universal mechanized equivalence between spec text and Go/Rust implementations"

Source of truth for claim boundary: `proof_coverage.json` (`proof_level`, `claims`).
`claim_level` (`toy|byte|refined`) is CI-validated for consistency against `proof_level`.

Wire model notes:

- `RubinFormal.ByteWireV2` — real CompactSize / byte-accurate proof surface for current wire claims
- `RubinFormal.ByteWireLegacy` — toy bootstrap model for single-byte CompactSize only (`n < 253`) and `TxMini`

## Risk model / CI gate

- Documentation: `RISK_MODEL.md`
- Lean validation (standalone): `lake build`
- Registry/claims linting (integrated workspace): sibling tooling from `../rubin-protocol/tools/`

## What this means

- This is **not** a freeze-ready package at the level of "universal byte-accurate wire + state transition model for all sections"
- Consensus rules are not changed by this repository
- The formal coverage registry currently contains 28 machine-checked section entries
- Claim strength breakdown: 21 universal, 4 assumption-backed, 2 behavioral, 1 contract-level
- A unified `proved` status in the registry does not imply uniform claim strength — the honest boundary is set by `evidence_level` and `limitations` in `proof_coverage.json`
- Extra formal-only theorems are not counted as pinned-section claims unless registered in the machine-readable registry

## Local build

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake env lean --version
lake build
```

Integrated workspace wrapper:

```bash
cd ../rubin-protocol && scripts/dev-env.sh -- bash -lc 'cd ../rubin-formal && lake build'
```

## Roadmap

1. Keep `proof_coverage.json`, public narrative, and closeout evidence in sync
2. Do not elevate formal-only extra theorems to public pinned-section claims without an explicit registry update
3. Theorem-level traceability (`theorem_refs`) is tracked as a separate hygiene/improvement effort, not mixed with truth-correction
