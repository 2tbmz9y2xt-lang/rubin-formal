## Summary

<!-- What does this PR do? Which issue does it close? -->

Closes #

## Formal Verification Checklist

> **Mandatory for any PR touching `.lean` files. Do not skip.**

### Invariant completeness

- [ ] For every `def ... : Prop` — all constraints from the canonical spec are included (list spec section)
- [ ] For every `≠` / `∉` / bound in a theorem hypothesis — verified that it **cannot** be derived from existing invariants. If it can → strengthen the invariant, don't add a separate hypothesis
- [ ] If a theorem requires `h : X ≠ Y` but X comes from a structure that should guarantee this — the structure's well-formedness predicate is incomplete. **Fix the predicate first.**

### Soundness

- [ ] 0 `sorry` / `admit` in all changed files
- [ ] 0 new `axiom` (or justified in PR description why axiom is necessary)
- [ ] All theorem statements match canonical spec semantics (cite spec section)
- [ ] `lake env lean` PASS on every changed `.lean` file

### Proof quality

- [ ] No `native_decide` on universally quantified theorems (use structural proofs)
- [ ] `native_decide` only for concrete/finite checks (specific values, pre-rotation constants)
- [ ] Private helpers that encode security invariants are public (accessible to downstream proofs)

## Spec references

<!-- List which sections of RUBIN_L1_CANONICAL.md this PR covers -->

## Test evidence

<!-- lake build output, CI link, etc. -->
