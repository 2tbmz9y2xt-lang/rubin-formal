import RubinFormal.UtxoApplyGenesisV1

/-!
# Transaction Structural Rules Behavioral Proofs (§16)

Universal behavioral theorems on the live `validateWitnessItemLengths`
and `validateThresholdSigSpendNoCrypto` validators.

## Coverage summary
- R1: unknown suite universal rejection (∀ suiteId ∉ {SENTINEL, ML_DSA_87})
- R2: sentinel non-empty pubkey/sig universal rejection
- R3: sentinel empty pubkey+sig universal acceptance
- R4: ML-DSA-87 wrong pubkey size universal rejection
- R5a: ML-DSA-87 empty sig universal rejection
- R5b: ML-DSA-87 sig too large universal rejection
- R6: ML-DSA-87 valid lengths universal acceptance
- R7: threshold sig spend wrong witness count universal rejection
- Concrete examples retained as regression tests.
-/

namespace RubinFormal

open UtxoBasicV1

/-! ## Concrete regression tests -/

/-- Concrete: unknown suite ID 0x05 is rejected. -/
theorem unknown_suite_0x05_rejected :
    UtxoApplyGenesisV1.validateWitnessItemLengths ⟨0x05, ByteArray.empty, ByteArray.empty⟩ 0 =
    .error "TX_ERR_SIG_ALG_INVALID" := by rfl

/-- Concrete: sentinel with non-empty pubkey is rejected. -/
theorem sentinel_nonempty_pubkey_rejected :
    UtxoApplyGenesisV1.validateWitnessItemLengths
      ⟨UtxoApplyGenesisV1.SUITE_ID_SENTINEL, ⟨#[0x01]⟩, ByteArray.empty⟩ 0 =
    .error "TX_ERR_PARSE" := by rfl

/-- Concrete: sentinel with empty pubkey+sig is accepted. -/
theorem sentinel_empty_accepted :
    UtxoApplyGenesisV1.validateWitnessItemLengths
      ⟨UtxoApplyGenesisV1.SUITE_ID_SENTINEL, ByteArray.empty, ByteArray.empty⟩ 0 =
    .ok () := by rfl

/-! ## R1: Unknown suite — universal rejection -/

/-- **R1 (universal):** Any suite ID ∉ {SENTINEL, ML_DSA_87} is rejected
    with TX_ERR_SIG_ALG_INVALID. LIVE on `validateWitnessItemLengths`. -/
theorem unknown_suite_rejected_universal
    (w : WitnessItem) (h : Nat)
    (hNotS : w.suiteId ≠ UtxoApplyGenesisV1.SUITE_ID_SENTINEL)
    (hNotM : w.suiteId ≠ UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) :
    UtxoApplyGenesisV1.validateWitnessItemLengths w h = .error "TX_ERR_SIG_ALG_INVALID" := by
  have hS : w.suiteId ≠ 0 := by
    simp [UtxoApplyGenesisV1.SUITE_ID_SENTINEL, CovenantGenesisV1.SUITE_ID_SENTINEL] at hNotS; exact hNotS
  have hM : w.suiteId ≠ 1 := by
    simp [UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87, CovenantGenesisV1.SUITE_ID_ML_DSA_87] at hNotM; exact hNotM
  simp only [UtxoApplyGenesisV1.validateWitnessItemLengths,
    UtxoApplyGenesisV1.SUITE_ID_SENTINEL, UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87,
    CovenantGenesisV1.SUITE_ID_SENTINEL, CovenantGenesisV1.SUITE_ID_ML_DSA_87]
  simp [hS, hM]; rfl

/-! ## R2: Sentinel — non-empty pubkey or sig rejected -/

/-- **R2 (universal):** Sentinel with non-empty pubkey or sig is rejected
    with TX_ERR_PARSE. LIVE on `validateWitnessItemLengths`. -/
theorem sentinel_nonempty_rejected_universal
    (w : WitnessItem) (h : Nat)
    (hS : w.suiteId = UtxoApplyGenesisV1.SUITE_ID_SENTINEL)
    (hNE : w.pubkey.size ≠ 0 ∨ w.signature.size ≠ 0) :
    UtxoApplyGenesisV1.validateWitnessItemLengths w h = .error "TX_ERR_PARSE" := by
  simp only [UtxoApplyGenesisV1.validateWitnessItemLengths,
    UtxoApplyGenesisV1.SUITE_ID_SENTINEL, CovenantGenesisV1.SUITE_ID_SENTINEL] at *
  simp only [hS, beq_self_eq_true, ite_true]
  rcases hNE with hp | hs
  · simp [bne_iff_ne, hp, Bool.true_or]; rfl
  · simp [bne_iff_ne, hs, Bool.or_true]; rfl

/-! ## R3: Sentinel — empty pubkey+sig accepted -/

/-- **R3 (universal):** Sentinel with both empty is accepted.
    LIVE on `validateWitnessItemLengths`. -/
theorem sentinel_empty_accepted_universal
    (w : WitnessItem) (h : Nat)
    (hS : w.suiteId = UtxoApplyGenesisV1.SUITE_ID_SENTINEL)
    (hPE : w.pubkey.size = 0)
    (hSE : w.signature.size = 0) :
    UtxoApplyGenesisV1.validateWitnessItemLengths w h = .ok () := by
  simp only [UtxoApplyGenesisV1.validateWitnessItemLengths,
    UtxoApplyGenesisV1.SUITE_ID_SENTINEL, CovenantGenesisV1.SUITE_ID_SENTINEL] at *
  simp only [hS, beq_self_eq_true, ite_true]
  simp [bne_iff_ne, hPE, hSE]; rfl

/-! ## R4: ML-DSA-87 — wrong pubkey size rejected -/

/-- **R4 (universal):** ML-DSA-87 with wrong pubkey size is rejected.
    LIVE on `validateWitnessItemLengths`. -/
theorem mldsa87_wrong_pubkey_rejected_universal
    (w : WitnessItem) (h : Nat)
    (hM : w.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87)
    (hBad : w.pubkey.size ≠ UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES) :
    UtxoApplyGenesisV1.validateWitnessItemLengths w h = .error "TX_ERR_SIG_NONCANONICAL" := by
  simp only [UtxoApplyGenesisV1.validateWitnessItemLengths,
    UtxoApplyGenesisV1.SUITE_ID_SENTINEL, UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87,
    UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES, UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES,
    CovenantGenesisV1.SUITE_ID_SENTINEL, CovenantGenesisV1.SUITE_ID_ML_DSA_87] at *
  simp [show w.suiteId ≠ 0 from by omega, hM, bne_iff_ne, hBad, Bool.true_or]; rfl

/-! ## R5: ML-DSA-87 — sig bounds rejected -/

/-- **R5a (universal):** ML-DSA-87 with empty sig is rejected.
    LIVE on `validateWitnessItemLengths`. -/
theorem mldsa87_empty_sig_rejected_universal
    (w : WitnessItem) (h : Nat)
    (hM : w.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87)
    (hPOk : w.pubkey.size = UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES)
    (hSig0 : w.signature.size = 0) :
    UtxoApplyGenesisV1.validateWitnessItemLengths w h = .error "TX_ERR_SIG_NONCANONICAL" := by
  simp only [UtxoApplyGenesisV1.validateWitnessItemLengths,
    UtxoApplyGenesisV1.SUITE_ID_SENTINEL, UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87,
    UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES, UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES,
    CovenantGenesisV1.SUITE_ID_SENTINEL, CovenantGenesisV1.SUITE_ID_ML_DSA_87] at *
  simp [show w.suiteId ≠ 0 from by omega, hM, bne_iff_ne, hPOk, hSig0]; rfl

/-- **R5b (universal):** ML-DSA-87 with sig too large is rejected.
    LIVE on `validateWitnessItemLengths`. -/
theorem mldsa87_sig_too_large_rejected_universal
    (w : WitnessItem) (h : Nat)
    (hM : w.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87)
    (hPOk : w.pubkey.size = UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES)
    (hBig : w.signature.size > UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES + 1) :
    UtxoApplyGenesisV1.validateWitnessItemLengths w h = .error "TX_ERR_SIG_NONCANONICAL" := by
  simp only [UtxoApplyGenesisV1.validateWitnessItemLengths,
    UtxoApplyGenesisV1.SUITE_ID_SENTINEL, UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87,
    UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES, UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES,
    CovenantGenesisV1.SUITE_ID_SENTINEL, CovenantGenesisV1.SUITE_ID_ML_DSA_87] at *
  simp [show w.suiteId ≠ 0 from by omega, hM]
  split
  · rfl
  · exfalso; rename_i hf; simp only [bne_iff_ne, hPOk, not_true_eq_false, Bool.false_or,
      Bool.or_eq_true, decide_eq_true_eq] at hf; omega

/-! ## R6: ML-DSA-87 — valid lengths accepted -/

/-- **R6 (universal):** ML-DSA-87 with valid lengths is accepted.
    LIVE on `validateWitnessItemLengths`. -/
theorem mldsa87_valid_accepted_universal
    (w : WitnessItem) (h : Nat)
    (hM : w.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87)
    (hPOk : w.pubkey.size = UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES)
    (hSPos : w.signature.size > 0)
    (hSBound : w.signature.size ≤ UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES + 1) :
    UtxoApplyGenesisV1.validateWitnessItemLengths w h = .ok () := by
  simp only [UtxoApplyGenesisV1.validateWitnessItemLengths,
    UtxoApplyGenesisV1.SUITE_ID_SENTINEL, UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87,
    UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES, UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES,
    CovenantGenesisV1.SUITE_ID_SENTINEL, CovenantGenesisV1.SUITE_ID_ML_DSA_87] at *
  simp [show w.suiteId ≠ 0 from by omega, hM, bne_iff_ne, hPOk,
        show w.signature.size ≠ 0 from by omega]
  simp [show ¬(4628 < w.signature.size) from by omega]; rfl

/-! ## R7: Threshold sig spend — wrong witness count -/

/-- **R7 (universal):** Wrong witness count in threshold spend is rejected
    with TX_ERR_PARSE. LIVE on `validateThresholdSigSpendNoCrypto`. -/
theorem threshold_wrong_count_rejected_universal
    (keys : List Bytes) (threshold : Nat)
    (ws : List WitnessItem) (h : Nat) (ctx : String)
    (hMismatch : ws.length ≠ keys.length) :
    UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto keys threshold ws h ctx =
    .error "TX_ERR_PARSE" := by
  unfold UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto
  simp [hMismatch]; rfl

/-! ## R8: Threshold sig spend — unknown suite in witness rejected -/

/-- **R8 (universal):** If the first witness in a threshold spend has unknown
    suite, the function rejects with TX_ERR_SIG_ALG_INVALID — regardless of
    list length, key content, threshold, or block height.
    LIVE on `validateThresholdSigSpendNoCrypto`. -/
theorem threshold_unknown_suite_head_rejected
    (k : Bytes) (krest : List Bytes) (w : WitnessItem) (wrest : List WitnessItem)
    (h : Nat) (ctx : String) (threshold : Nat)
    (hLen : (w :: wrest).length = (k :: krest).length)
    (hNotS : w.suiteId ≠ UtxoApplyGenesisV1.SUITE_ID_SENTINEL)
    (hNotM : w.suiteId ≠ UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) :
    UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto (k :: krest) threshold (w :: wrest) h ctx =
    .error "TX_ERR_SIG_ALG_INVALID" := by
  simp only [UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto,
    UtxoApplyGenesisV1.SUITE_ID_SENTINEL, UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87,
    CovenantGenesisV1.SUITE_ID_SENTINEL, CovenantGenesisV1.SUITE_ID_ML_DSA_87] at *
  have hLen' : wrest.length = krest.length := by simp [List.length] at hLen; omega
  simp [hLen', hNotS, hNotM]
  show Except.error "TX_ERR_SIG_ALG_INVALID" = Except.error "TX_ERR_SIG_ALG_INVALID"; rfl

/-! ## forIn.loop infrastructure for threshold loop induction -/

/-- forIn.loop on cons where body yields → recurse on tail. -/
private theorem forIn_loop_yield {α β : Type}
    {body : α → β → Except String (ForInStep β)}
    {a : α} {as : List α} {b b' : β}
    (hYield : body a b = .ok (.yield b')) :
    List.forIn.loop body (a :: as) b = List.forIn.loop body as b' := by
  show body a b >>= _ = _; rw [hYield]; rfl

/-- forIn.loop on cons where body errors → error propagates. -/
private theorem forIn_loop_error {α β : Type}
    {body : α → β → Except String (ForInStep β)}
    {a : α} {as : List α} {b : β} {e : String}
    (hErr : body a b = .error e) :
    List.forIn.loop body (a :: as) b = (Except.error e : Except String β) := by
  show body a b >>= _ = _; rw [hErr]; rfl

/-- **First-error-wins for forIn on List+Except:** if all elements in `safe`
    prefix yield, and `bad` element errors, the whole forIn returns that error.
    Proved by induction on the prefix list. -/
theorem forIn_loop_safe_then_error
    {body : (WitnessItem × Bytes) → Nat → Except String (ForInStep Nat)}
    (safe : List (WitnessItem × Bytes))
    (bad : WitnessItem × Bytes)
    (rest : List (WitnessItem × Bytes))
    (init : Nat)
    (hSafe : ∀ (p : WitnessItem × Bytes) (acc : Nat), p ∈ safe →
      ∃ acc', body p acc = .ok (.yield acc'))
    (hBad : ∀ acc, body bad acc = .error "TX_ERR_SIG_ALG_INVALID") :
    List.forIn.loop body (safe ++ bad :: rest) init =
    (Except.error "TX_ERR_SIG_ALG_INVALID" : Except String Nat) := by
  induction safe generalizing init with
  | nil => simp; exact forIn_loop_error (hBad init)
  | cons p ps ih =>
    simp only [List.cons_append]
    have ⟨acc', hYield⟩ := hSafe p init (List.mem_cons_self _ _)
    rw [forIn_loop_yield hYield]
    exact ih acc' (fun q acc hq => hSafe q acc (List.mem_cons_of_mem _ hq))

end RubinFormal
