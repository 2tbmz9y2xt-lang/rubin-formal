import RubinFormal.SighashV1

/-!
# Sighash Refinement Upgrade (§12)

Replaces tautological `digestV1_deterministic` (was `f x = f x`) with
substantive universal theorems on the live sighash validation surface.

## Coverage
- digestV1 error characterization: parse failure → error, OOB index → error (universal LIVE)
- digestV1 success characterization: parse ok + in bounds → ∃ digest (universal LIVE)
- Invalid sighash types rejected by all three hash-selection functions (universal LIVE)
- `hasValidBaseType` exhaustive 256-value partition (native_decide LIVE)
- Preimage frame field positions (rfl, structural LIVE)

## Honest limitation
- digestV1 end-to-end injectivity (different frames → different digests)
  requires SHA3 collision resistance — external cryptographic assumption.
- Tautological `digestV1_deterministic` (`f x = f x`) removed.
- 5 wrapper `buildPreimageFrameParts_commits_*` theorems removed from
  SighashV1.lean (were congrArg corollaries of injective).
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

/-! ## digestV1 error characterization (universal, LIVE) -/

/-- **Parse failure propagates:** if `parseTxCoreForSighash` fails, `digestV1` returns
    the same error. Universal over all inputs. LIVE on `digestV1`. -/
theorem digestV1_parse_failure
    (tx chainId : Bytes) (idx val : Nat) (e : String)
    (hFail : parseTxCoreForSighash tx = .error e) :
    digestV1 tx chainId idx val = .error e := by
  show (parseTxCoreForSighash tx >>= fun core => _) = .error e
  rw [hFail]; rfl

/-- **OOB index rejected:** if parse succeeds but `inputIndex ≥ inputs.length`,
    `digestV1` returns TX_ERR_PARSE. Universal. LIVE on `digestV1`. -/
theorem digestV1_oob_index
    (tx chainId : Bytes) (idx val : Nat)
    (core : TxCoreForSighash)
    (hParse : parseTxCoreForSighash tx = .ok core)
    (hOOB : idx ≥ core.inputs.length) :
    digestV1 tx chainId idx val = .error "TX_ERR_PARSE" := by
  show (parseTxCoreForSighash tx >>= fun core => _) = _
  rw [hParse]; simp only [ge_iff_le, Bind.bind, Except.bind]; rw [if_pos hOOB]

/-- **In-bounds succeeds:** if parse succeeds and index is in bounds,
    `digestV1` returns some digest. Universal. LIVE on `digestV1`. -/
theorem digestV1_success
    (tx chainId : Bytes) (idx val : Nat)
    (core : TxCoreForSighash)
    (hParse : parseTxCoreForSighash tx = .ok core)
    (hInBounds : idx < core.inputs.length) :
    ∃ digest, digestV1 tx chainId idx val = .ok digest := by
  show ∃ d, (parseTxCoreForSighash tx >>= fun core => _) = .ok d
  rw [hParse]; simp only [ge_iff_le, Bind.bind, Except.bind]
  rw [if_neg (show ¬(core.inputs.length ≤ idx) from by omega)]
  exact ⟨_, rfl⟩

/-! ## Preimage frame field positions (structural, LIVE) -/

/-- The preimage frame parts list has exactly 16 elements. -/
theorem buildPreimageFrameParts_length (f : SighashPreimageFrame) :
    (buildPreimageFrameParts f).length = 16 := by rfl

/-- Version field is at index 2 in the preimage parts. -/
theorem buildPreimageFrameParts_version_at_2 (f : SighashPreimageFrame) :
    (buildPreimageFrameParts f).get? 2 = some f.versionLE := by rfl

/-- ChainId is at index 1 in the preimage parts. -/
theorem buildPreimageFrameParts_chainId_at_1 (f : SighashPreimageFrame) :
    (buildPreimageFrameParts f).get? 1 = some f.chainId := by rfl

/-- Locktime is at index 14 in the preimage parts. -/
theorem buildPreimageFrameParts_locktime_at_14 (f : SighashPreimageFrame) :
    (buildPreimageFrameParts f).get? 14 = some f.locktimeLE := by rfl

/-- SighashType byte is at index 15 (last) in the preimage parts. -/
theorem buildPreimageFrameParts_sighashType_at_15 (f : SighashPreimageFrame) :
    (buildPreimageFrameParts f).get? 15 = some (RubinFormal.bytes #[f.sighashType]) := by rfl

end RubinFormal
