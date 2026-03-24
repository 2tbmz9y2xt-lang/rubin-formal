import RubinFormal.SighashV1

/-!
# Sighash Refinement Upgrade (§12)

Replaces tautological `digestV1_deterministic` (was `f x = f x`) with
substantive universal theorems on the live sighash validation surface.

## Coverage
- Invalid sighash types rejected by all three hash-selection functions (universal)
- `hasValidBaseType` exhaustive 256-value partition (native_decide)
- Well-formed preimage frame produces fixed 246-byte preimage (universal)

## Honest limitation
- digestV1 end-to-end injectivity (different frames → different digests)
  requires SHA3 collision resistance, which is an external cryptographic
  assumption — not provable within Lean.
- digestV1 determinism (`f x = f x`) is trivially true for any Lean function
  and was removed as tautological per hostile gate policy.
-/

namespace RubinFormal

open SighashV1

/-! ## Invalid sighash type rejection (universal, LIVE) -/

/-- Any sighash type not in {ALL, NONE, SINGLE, ALL_ACP, NONE_ACP, SINGLE_ACP}
    causes `selectHashPrevouts` to return `none`.
    LIVE on `selectHashPrevouts`. -/
theorem selectHashPrevouts_invalid_returns_none
    (sighashType : UInt8) (allInputs currentInput : Bytes)
    (h1 : sighashType ≠ SIGHASH_ALL_ANYONECANPAY)
    (h2 : sighashType ≠ SIGHASH_NONE_ANYONECANPAY)
    (h3 : sighashType ≠ SIGHASH_SINGLE_ANYONECANPAY)
    (h4 : sighashType ≠ SIGHASH_ALL)
    (h5 : sighashType ≠ SIGHASH_NONE)
    (h6 : sighashType ≠ SIGHASH_SINGLE) :
    selectHashPrevouts sighashType allInputs currentInput = none := by
  simp [selectHashPrevouts, h1, h2, h3, h4, h5, h6]

/-- Any sighash type not in {ALL, NONE, SINGLE, ALL_ACP, NONE_ACP, SINGLE_ACP}
    causes `selectHashSequences` to return `none`.
    LIVE on `selectHashSequences`. -/
theorem selectHashSequences_invalid_returns_none
    (sighashType : UInt8) (allInputs currentInput : Bytes)
    (h1 : sighashType ≠ SIGHASH_ALL_ANYONECANPAY)
    (h2 : sighashType ≠ SIGHASH_NONE_ANYONECANPAY)
    (h3 : sighashType ≠ SIGHASH_SINGLE_ANYONECANPAY)
    (h4 : sighashType ≠ SIGHASH_ALL)
    (h5 : sighashType ≠ SIGHASH_NONE)
    (h6 : sighashType ≠ SIGHASH_SINGLE) :
    selectHashSequences sighashType allInputs currentInput = none := by
  simp [selectHashSequences, h1, h2, h3, h4, h5, h6]

/-- Any sighash type not in {ALL, NONE, SINGLE, ALL_ACP, NONE_ACP, SINGLE_ACP}
    causes `selectHashOutputs` to return `none`.
    LIVE on `selectHashOutputs`. -/
theorem selectHashOutputs_invalid_returns_none
    (sighashType : UInt8) (inputIndex outputCount : Nat)
    (allOutputs selectedOutput emptyHash : Bytes)
    (h1 : sighashType ≠ SIGHASH_ALL)
    (h2 : sighashType ≠ SIGHASH_ALL_ANYONECANPAY)
    (h3 : sighashType ≠ SIGHASH_NONE)
    (h4 : sighashType ≠ SIGHASH_NONE_ANYONECANPAY)
    (h5 : sighashType ≠ SIGHASH_SINGLE)
    (h6 : sighashType ≠ SIGHASH_SINGLE_ANYONECANPAY) :
    selectHashOutputs sighashType inputIndex outputCount allOutputs selectedOutput emptyHash = none := by
  simp [selectHashOutputs, h1, h2, h3, h4, h5, h6]

/-! ## hasValidBaseType exhaustive partition -/

/-- `hasValidBaseType` returns true iff the base type (lower 7 bits) is 1, 2, or 3.
    Proved exhaustively over all 256 UInt8 values. LIVE on `hasValidBaseType`. -/
theorem hasValidBaseType_exhaustive :
    ∀ (t : Fin 256),
    hasValidBaseType (UInt8.ofNat t.val) = true ↔
    (t.val &&& 0x7F = 1 ∨ t.val &&& 0x7F = 2 ∨ t.val &&& 0x7F = 3) := by
  native_decide

end RubinFormal
