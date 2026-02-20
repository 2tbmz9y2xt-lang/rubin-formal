# rubin-formal (Lean 4) - RUBIN L1 v1.1

Status: DEVELOPMENT (non-normative). This repository hosts Lean 4 proofs for RUBIN L1.

Goals (pre-freeze minimum):
- Provide machine-checked Lean 4 proofs for:
  - T-004 ApplyBlock determinism
  - T-005 Value conservation (non-coinbase)
  - T-007 VERSION_BITS monotonicity / terminal states

Notes:
- This is intentionally a minimal, dependency-free Lean 4 project (Std-only).
- The theorems here are "model-level" proofs: they establish determinism / monotonicity
  properties for a well-defined abstract model that matches the spec structure.
- This repo is referenced by `rubin-protocol/formal/RUBIN_FORMAL_APPENDIX_v1.1.md` (pinned commit).
