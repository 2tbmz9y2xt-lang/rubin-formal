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
- R8: threshold sig spend unknown suite anywhere universal rejection
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
      ⟨RubinFormal.SUITE_ID_SENTINEL, ⟨#[0x01]⟩, ByteArray.empty⟩ 0 =
    .error "TX_ERR_PARSE" := by rfl

/-- Concrete: sentinel with empty pubkey+sig is accepted. -/
theorem sentinel_empty_accepted :
    UtxoApplyGenesisV1.validateWitnessItemLengths
      ⟨RubinFormal.SUITE_ID_SENTINEL, ByteArray.empty, ByteArray.empty⟩ 0 =
    .ok () := by rfl

/-! ## R1: Unknown suite — universal rejection -/

/-- **R1 (universal):** Any suite ID ∉ {SENTINEL, ML_DSA_87} is rejected
    with TX_ERR_SIG_ALG_INVALID. LIVE on `validateWitnessItemLengths`. -/
theorem unknown_suite_rejected_universal
    (w : WitnessItem) (h : Nat)
    (hNotS : w.suiteId ≠ RubinFormal.SUITE_ID_SENTINEL)
    (hNotM : w.suiteId ≠ UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) :
    UtxoApplyGenesisV1.validateWitnessItemLengths w h = .error "TX_ERR_SIG_ALG_INVALID" := by
  have hS : w.suiteId ≠ 0 := by
    simp [RubinFormal.SUITE_ID_SENTINEL] at hNotS; exact hNotS
  have hM : w.suiteId ≠ 1 := by
    simp [UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87, CovenantGenesisV1.SUITE_ID_ML_DSA_87] at hNotM; exact hNotM
  simp only [UtxoApplyGenesisV1.validateWitnessItemLengths,
    RubinFormal.SUITE_ID_SENTINEL, UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87,
    CovenantGenesisV1.SUITE_ID_ML_DSA_87]
  simp [hS, hM]; rfl

/-! ## R2: Sentinel — non-empty pubkey or sig rejected -/

/-- **R2 (universal):** Sentinel with non-empty pubkey or sig is rejected
    with TX_ERR_PARSE. LIVE on `validateWitnessItemLengths`. -/
theorem sentinel_nonempty_rejected_universal
    (w : WitnessItem) (h : Nat)
    (hS : w.suiteId = RubinFormal.SUITE_ID_SENTINEL)
    (hNE : w.pubkey.size ≠ 0 ∨ w.signature.size ≠ 0) :
    UtxoApplyGenesisV1.validateWitnessItemLengths w h = .error "TX_ERR_PARSE" := by
  simp only [UtxoApplyGenesisV1.validateWitnessItemLengths,
    RubinFormal.SUITE_ID_SENTINEL] at *
  simp only [hS, beq_self_eq_true, ite_true]
  rcases hNE with hp | hs
  · simp [bne_iff_ne, hp, Bool.true_or]; rfl
  · simp [bne_iff_ne, hs, Bool.or_true]; rfl

/-! ## R3: Sentinel — empty pubkey+sig accepted -/

/-- **R3 (universal):** Sentinel with both empty is accepted.
    LIVE on `validateWitnessItemLengths`. -/
theorem sentinel_empty_accepted_universal
    (w : WitnessItem) (h : Nat)
    (hS : w.suiteId = RubinFormal.SUITE_ID_SENTINEL)
    (hPE : w.pubkey.size = 0)
    (hSE : w.signature.size = 0) :
    UtxoApplyGenesisV1.validateWitnessItemLengths w h = .ok () := by
  simp only [UtxoApplyGenesisV1.validateWitnessItemLengths,
    RubinFormal.SUITE_ID_SENTINEL] at *
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
    RubinFormal.SUITE_ID_SENTINEL, UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87,
    UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES, UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES,
    CovenantGenesisV1.SUITE_ID_ML_DSA_87] at *
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
    RubinFormal.SUITE_ID_SENTINEL, UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87,
    UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES, UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES,
    CovenantGenesisV1.SUITE_ID_ML_DSA_87] at *
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
    RubinFormal.SUITE_ID_SENTINEL, UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87,
    UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES, UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES,
    CovenantGenesisV1.SUITE_ID_ML_DSA_87] at *
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
    RubinFormal.SUITE_ID_SENTINEL, UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87,
    UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES, UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES,
    CovenantGenesisV1.SUITE_ID_ML_DSA_87] at *
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
    (hNotS : w.suiteId ≠ RubinFormal.SUITE_ID_SENTINEL)
    (hNotM : w.suiteId ≠ UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) :
    UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto (k :: krest) threshold (w :: wrest) h ctx =
    .error "TX_ERR_SIG_ALG_INVALID" := by
  simp only [UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto,
    RubinFormal.SUITE_ID_SENTINEL, UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87,
    CovenantGenesisV1.SUITE_ID_ML_DSA_87] at *
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
    (err : String)
    (hSafe : ∀ (p : WitnessItem × Bytes) (acc : Nat), p ∈ safe →
      ∃ acc', body p acc = .ok (.yield acc'))
    (hBad : ∀ acc, body bad acc = .error err) :
    List.forIn.loop body (safe ++ bad :: rest) init =
    (Except.error err : Except String Nat) := by
  induction safe generalizing init with
  | nil => simp; exact forIn_loop_error (hBad init)
  | cons p ps ih =>
    simp only [List.cons_append]
    have ⟨acc', hYield⟩ := hSafe p init (List.mem_cons_self _ _)
    rw [forIn_loop_yield hYield]
    exact ih acc' (fun q acc hq => hSafe q acc (List.mem_cons_of_mem _ hq))

private theorem uint8_beq_eq_decide (x y : UInt8) :
    BEq.beq x y = decide (x = y) := by
  cases x with
  | mk xv =>
    cases y with
    | mk yv =>
      simp [BEq.beq]

private theorem bytes_beq_refl (a : Bytes) : (a == a) = true := by
  cases a with
  | mk ad =>
      show Array.isEqv ad ad BEq.beq = true
      have h :
          (fun (x y : UInt8) => @BEq.beq UInt8 _ x y) =
          (fun x y => decide (x = y)) := by
        funext x y
        exact uint8_beq_eq_decide x y
      have hrw :
          Array.isEqv ad ad BEq.beq =
          Array.isEqv ad ad (fun x y => decide (x = y)) := by
        congr 1
      rw [hrw]
      exact Array.isEqv_self ad

private theorem bytes_bne_self_false (a : Bytes) : (a != a) = false := by
  show (!(a == a)) = false
  rw [bytes_beq_refl]
  rfl

private theorem bytes_beq_true_eq
    (a b : Bytes)
    (h : (a == b) = true) :
    a = b := by
  cases a with
  | mk ad =>
      cases b with
      | mk bd =>
          change Array.isEqv ad bd BEq.beq = true at h
          have hData : ad = bd := by
            apply Array.eq_of_isEqv
            simpa using h
          cases hData
          rfl

private theorem bytes_bne_false_eq
    (a b : Bytes)
    (h : (a != b) = false) :
    a = b := by
  change (!(a == b)) = false at h
  cases hEq : (a == b) with
  | false =>
      simp [hEq] at h
  | true =>
      exact bytes_beq_true_eq a b hEq

private def thresholdPairSafe (x : WitnessItem × Bytes) : Prop :=
  x.fst.suiteId = RubinFormal.SUITE_ID_SENTINEL ∨
    (x.fst.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 ∧
      SHA3.sha3_256 x.fst.pubkey = x.snd)

private def thresholdPairUnknownSuite (x : WitnessItem × Bytes) : Prop :=
  x.fst.suiteId ≠ RubinFormal.SUITE_ID_SENTINEL ∧
    x.fst.suiteId ≠ UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87

private def thresholdPairMismatch (x : WitnessItem × Bytes) : Prop :=
  x.fst.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 ∧
    SHA3.sha3_256 x.fst.pubkey ≠ x.snd

private def thresholdBody
    (x : WitnessItem × Bytes) (r : Nat) : Except String (ForInStep Nat) :=
  if x.fst.suiteId == RubinFormal.SUITE_ID_SENTINEL then
    pure (.yield r)
  else if x.fst.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 then
    if SHA3.sha3_256 x.fst.pubkey != x.snd then do
      throw "TX_ERR_SIG_INVALID"
      pure (.yield (r + 1))
    else
      pure (.yield (r + 1))
  else do
    throw "TX_ERR_SIG_ALG_INVALID"
    pure (.yield r)

private theorem thresholdForIn_eq_live (keys : List Bytes) (ws : List WitnessItem) :
    List.forIn (List.zip ws keys) 0
      (fun x r =>
        if x.fst.suiteId == RubinFormal.SUITE_ID_SENTINEL then
          pure (.yield r)
        else if x.fst.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 then
          if SHA3.sha3_256 x.fst.pubkey != x.snd then do
            throw "TX_ERR_SIG_INVALID"
            pure (.yield (r + 1))
          else
            pure (.yield (r + 1))
        else do
          throw "TX_ERR_SIG_ALG_INVALID"
          pure (.yield r))
      = List.forIn (List.zip ws keys) 0 thresholdBody := by
  apply congrArg (fun f => List.forIn (List.zip ws keys) 0 f)
  funext x r
  rfl

set_option maxHeartbeats 1000000 in
private theorem thresholdBody_safe_yield (x : WitnessItem × Bytes) (r : Nat)
    (hSafe : thresholdPairSafe x) :
    ∃ r', thresholdBody x r = .ok (.yield r') := by
  rcases hSafe with hS | ⟨hM, hHash⟩
  · refine ⟨r, ?_⟩
    have hSTrue : (x.fst.suiteId == RubinFormal.SUITE_ID_SENTINEL) = true := by
      simp [hS]
    rw [thresholdBody]
    simp [hSTrue]
    change (Except.ok (ForInStep.yield r) : Except String (ForInStep Nat)) =
      Except.ok (ForInStep.yield r)
    rfl
  · refine ⟨r + 1, ?_⟩
    have hSentNe : x.fst.suiteId ≠ RubinFormal.SUITE_ID_SENTINEL := by
      rw [hM]
      native_decide
    have hSentFalse : (x.fst.suiteId == RubinFormal.SUITE_ID_SENTINEL) = false := by
      simp [hSentNe]
    have hMTrue : (x.fst.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) = true := by
      simp [hM]
    have hHashFalse : (SHA3.sha3_256 x.fst.pubkey != x.snd) = false := by
      rw [hHash]
      exact bytes_bne_self_false x.snd
    rw [thresholdBody]
    simp [hSentFalse, hMTrue, hHashFalse, Except.bind]
    change (Except.ok (ForInStep.yield (r + 1)) : Except String (ForInStep Nat)) =
      Except.ok (ForInStep.yield (r + 1))
    rfl

private def thresholdPairIncrement (x : WitnessItem × Bytes) : Nat :=
  if x.fst.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 then 1 else 0

private def thresholdSafeCount : List (WitnessItem × Bytes) → Nat
  | [] => 0
  | x :: xs => thresholdPairIncrement x + thresholdSafeCount xs

private theorem thresholdBody_safe_yield_exact (x : WitnessItem × Bytes) (r : Nat)
    (hSafe : thresholdPairSafe x) :
    thresholdBody x r = .ok (.yield (r + thresholdPairIncrement x)) := by
  rcases hSafe with hS | ⟨hM, hHash⟩
  · have hSTrue : (x.fst.suiteId == RubinFormal.SUITE_ID_SENTINEL) = true := by
      simp [hS]
    have hMFalse : (x.fst.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) = false := by
      rw [hS]
      native_decide
    rw [thresholdBody]
    simp [hSTrue, hMFalse, thresholdPairIncrement]
    change (Except.ok (ForInStep.yield r) : Except String (ForInStep Nat)) =
      Except.ok (ForInStep.yield r)
    rfl
  · have hSentNe : x.fst.suiteId ≠ RubinFormal.SUITE_ID_SENTINEL := by
      rw [hM]
      native_decide
    have hSentFalse : (x.fst.suiteId == RubinFormal.SUITE_ID_SENTINEL) = false := by
      simp [hSentNe]
    have hMTrue : (x.fst.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) = true := by
      simp [hM]
    have hHashFalse : (SHA3.sha3_256 x.fst.pubkey != x.snd) = false := by
      rw [hHash]
      exact bytes_bne_self_false x.snd
    rw [thresholdBody]
    simp [hSentFalse, hMTrue, hHashFalse, thresholdPairIncrement, Except.bind]
    change (Except.ok (ForInStep.yield (r + 1)) : Except String (ForInStep Nat)) =
      Except.ok (ForInStep.yield (r + 1))
    rfl

private theorem forIn_loop_all_safe_counts
    (safe : List (WitnessItem × Bytes))
    (init : Nat)
    (hSafe : ∀ p ∈ safe, thresholdPairSafe p) :
    List.forIn.loop thresholdBody safe init = Except.ok (init + thresholdSafeCount safe) := by
  induction safe generalizing init with
  | nil =>
      change (Except.ok init : Except String Nat) =
        Except.ok (init + thresholdSafeCount [])
      simp [thresholdSafeCount]
  | cons p ps ih =>
      have hYield : thresholdBody p init = .ok (.yield (init + thresholdPairIncrement p)) := by
        exact thresholdBody_safe_yield_exact p init (hSafe p (List.mem_cons_self _ _))
      rw [forIn_loop_yield hYield]
      have hRest :
          List.forIn.loop thresholdBody ps (init + thresholdPairIncrement p) =
            Except.ok ((init + thresholdPairIncrement p) + thresholdSafeCount ps) := by
        exact ih (init + thresholdPairIncrement p)
          (fun q hq => hSafe q (List.mem_cons_of_mem _ hq))
      rw [hRest]
      simp [thresholdSafeCount, Nat.add_assoc]

private theorem thresholdBody_unknown_suite_error
    (bad : WitnessItem × Bytes) (acc : Nat)
    (hBad : thresholdPairUnknownSuite bad) :
    thresholdBody bad acc = .error "TX_ERR_SIG_ALG_INVALID" := by
  have hNotS : bad.fst.suiteId ≠ RubinFormal.SUITE_ID_SENTINEL := hBad.1
  have hNotM : bad.fst.suiteId ≠ UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 := hBad.2
  have hSentFalse : (bad.fst.suiteId == RubinFormal.SUITE_ID_SENTINEL) = false := by
    simp [hNotS]
  have hMFalse : (bad.fst.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) = false := by
    simp [hNotM]
  rw [thresholdBody]
  simp [hSentFalse, hMFalse, Except.bind]
  change (Except.error "TX_ERR_SIG_ALG_INVALID" : Except String (ForInStep Nat)) =
    Except.error "TX_ERR_SIG_ALG_INVALID"
  rfl

private theorem thresholdBody_mismatch_error
    (bad : WitnessItem × Bytes) (acc : Nat)
    (hBad : thresholdPairMismatch bad) :
    thresholdBody bad acc = .error "TX_ERR_SIG_INVALID" := by
  have hM : bad.fst.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 := hBad.1
  have hSentNe : bad.fst.suiteId ≠ RubinFormal.SUITE_ID_SENTINEL := by
    rw [hM]
    native_decide
  have hSentFalse : (bad.fst.suiteId == RubinFormal.SUITE_ID_SENTINEL) = false := by
    simp [hSentNe]
  have hMTrue : (bad.fst.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) = true := by
    simp [hM]
  have hHashTrue : (SHA3.sha3_256 bad.fst.pubkey != bad.snd) = true := by
    cases hCmp : (SHA3.sha3_256 bad.fst.pubkey != bad.snd)
    · exfalso
      have : SHA3.sha3_256 bad.fst.pubkey = bad.snd := by
        exact bytes_bne_false_eq _ _ hCmp
      exact hBad.2 this
    · rfl
  rw [thresholdBody]
  simp [hSentFalse, hMTrue, hHashTrue, Except.bind]
  change (Except.error "TX_ERR_SIG_INVALID" : Except String (ForInStep Nat)) =
    Except.error "TX_ERR_SIG_INVALID"
  rfl

/-- **R8 (universal):** Any unknown suite appearing anywhere in the threshold
    witness/key zip causes live threshold dispatch to reject with
    TX_ERR_SIG_ALG_INVALID. Earlier safe prefix items may yield, but they
    cannot suppress the first unknown-suite error. LIVE on
    `validateThresholdSigSpendNoCrypto`. -/
theorem threshold_unknown_suite_anywhere_rejected_universal
    (keys : List Bytes) (threshold : Nat)
    (ws : List WitnessItem) (h : Nat) (ctx : String)
    (safe : List (WitnessItem × Bytes))
    (bad : WitnessItem × Bytes)
    (rest : List (WitnessItem × Bytes))
    (hLen : ws.length = keys.length)
    (hZip : List.zip ws keys = safe ++ bad :: rest)
    (hSafe : ∀ p ∈ safe, thresholdPairSafe p)
    (hBad : thresholdPairUnknownSuite bad) :
    UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto keys threshold ws h ctx =
    .error "TX_ERR_SIG_ALG_INVALID" := by
  have hLenFalse : (ws.length != keys.length) = false := by
    simp [hLen]
  have hLoop : List.forIn.loop thresholdBody (safe ++ bad :: rest) 0 =
      (Except.error "TX_ERR_SIG_ALG_INVALID" : Except String Nat) := by
    apply forIn_loop_safe_then_error
      (safe := safe) (bad := bad) (rest := rest) (init := 0) (err := "TX_ERR_SIG_ALG_INVALID")
    · intro p acc hp
      exact thresholdBody_safe_yield p acc (hSafe p hp)
    · intro acc
      exact thresholdBody_unknown_suite_error bad acc hBad
  simp [UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto, hLenFalse, Except.bind]
  have hFinal :
      (do
        let r ← List.forIn (List.zip ws keys) 0
          (fun x r =>
            if x.fst.suiteId == RubinFormal.SUITE_ID_SENTINEL then
              pure (.yield r)
            else if x.fst.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 then
              if SHA3.sha3_256 x.fst.pubkey != x.snd then do
                throw "TX_ERR_SIG_INVALID"
                pure (.yield (r + 1))
              else
                pure (.yield (r + 1))
            else do
              throw "TX_ERR_SIG_ALG_INVALID"
              pure (.yield r))
        if r < threshold then
          throw "TX_ERR_SIG_INVALID"
        else
          pure ()) = Except.error "TX_ERR_SIG_ALG_INVALID" := by
    rw [thresholdForIn_eq_live]
    rw [hZip]
    simp [List.forIn, hLoop, Except.bind]
    rfl
  simpa using hFinal

/-- Follow-up theorem surface: any ML-DSA-87/key mismatch appearing anywhere
    in the threshold witness/key zip causes live threshold dispatch to reject
    with TX_ERR_SIG_INVALID. Earlier safe prefix items may yield, but they
    cannot suppress the first mismatch error. LIVE on
    `validateThresholdSigSpendNoCrypto`. -/
theorem threshold_hash_mismatch_anywhere_rejected
    (keys : List Bytes) (threshold : Nat)
    (ws : List WitnessItem) (h : Nat) (ctx : String)
    (safe : List (WitnessItem × Bytes))
    (bad : WitnessItem × Bytes)
    (rest : List (WitnessItem × Bytes))
    (hLen : ws.length = keys.length)
    (hZip : List.zip ws keys = safe ++ bad :: rest)
    (hSafe : ∀ p ∈ safe, thresholdPairSafe p)
    (hBad : thresholdPairMismatch bad) :
    UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto keys threshold ws h ctx =
    .error "TX_ERR_SIG_INVALID" := by
  have hLenFalse : (ws.length != keys.length) = false := by
    simp [hLen]
  have hLoop : List.forIn.loop thresholdBody (safe ++ bad :: rest) 0 =
      (Except.error "TX_ERR_SIG_INVALID" : Except String Nat) := by
    apply forIn_loop_safe_then_error
      (safe := safe) (bad := bad) (rest := rest) (init := 0) (err := "TX_ERR_SIG_INVALID")
    · intro p acc hp
      exact thresholdBody_safe_yield p acc (hSafe p hp)
    · intro acc
      exact thresholdBody_mismatch_error bad acc hBad
  simp [UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto, hLenFalse, Except.bind]
  have hFinal :
      (do
        let r ← List.forIn (List.zip ws keys) 0
          (fun x r =>
            if x.fst.suiteId == RubinFormal.SUITE_ID_SENTINEL then
              pure (.yield r)
            else if x.fst.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 then
              if SHA3.sha3_256 x.fst.pubkey != x.snd then do
                throw "TX_ERR_SIG_INVALID"
                pure (.yield (r + 1))
              else
                pure (.yield (r + 1))
            else do
              throw "TX_ERR_SIG_ALG_INVALID"
              pure (.yield r))
        if r < threshold then
          throw "TX_ERR_SIG_INVALID"
        else
          pure ()) = Except.error "TX_ERR_SIG_INVALID" := by
    rw [thresholdForIn_eq_live]
    rw [hZip]
    simp [List.forIn, hLoop, Except.bind]
    rfl
  simpa using hFinal

/-- Follow-up theorem surface: if every threshold witness/key pair is
    structurally safe but the accumulated number of ML-DSA-87 matches stays
    below `threshold`, the live validator rejects with `TX_ERR_SIG_INVALID`.
    LIVE on `validateThresholdSigSpendNoCrypto`. -/
theorem threshold_below_required_count_rejected
    (keys : List Bytes) (threshold : Nat)
    (ws : List WitnessItem) (h : Nat) (ctx : String)
    (hLen : ws.length = keys.length)
    (hSafe : ∀ p ∈ List.zip ws keys, thresholdPairSafe p)
    (hBelow : thresholdSafeCount (List.zip ws keys) < threshold) :
    UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto keys threshold ws h ctx =
    .error "TX_ERR_SIG_INVALID" := by
  have hLenFalse : (ws.length != keys.length) = false := by
    simp [hLen]
  have hLoop :
      List.forIn.loop thresholdBody (List.zip ws keys) 0 =
        Except.ok (thresholdSafeCount (List.zip ws keys)) := by
    simpa using forIn_loop_all_safe_counts (safe := List.zip ws keys) (init := 0) hSafe
  simp [UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto, hLenFalse, Except.bind]
  have hFinal :
      (do
        let r ← List.forIn (List.zip ws keys) 0
          (fun x r =>
            if x.fst.suiteId == RubinFormal.SUITE_ID_SENTINEL then
              pure (.yield r)
            else if x.fst.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 then
              if SHA3.sha3_256 x.fst.pubkey != x.snd then do
                throw "TX_ERR_SIG_INVALID"
                pure (.yield (r + 1))
              else
                pure (.yield (r + 1))
            else do
              throw "TX_ERR_SIG_ALG_INVALID"
              pure (.yield r))
        if r < threshold then
          throw "TX_ERR_SIG_INVALID"
        else
          pure ()) = Except.error "TX_ERR_SIG_INVALID" := by
    rw [thresholdForIn_eq_live]
    simp [List.forIn]
    rw [hLoop]
    change
      (if thresholdSafeCount (List.zip ws keys) < threshold then
        Except.error "TX_ERR_SIG_INVALID"
      else
        Except.ok ()) = Except.error "TX_ERR_SIG_INVALID"
    simp [Except.bind, hBelow]
  simpa using hFinal

/-- Follow-up theorem surface: if every threshold witness/key pair is
    structurally safe and the accumulated number of ML-DSA-87 matches reaches
    `threshold`, the live validator accepts. LIVE on
    `validateThresholdSigSpendNoCrypto`. -/
theorem threshold_required_count_accepts
    (keys : List Bytes) (threshold : Nat)
    (ws : List WitnessItem) (h : Nat) (ctx : String)
    (hLen : ws.length = keys.length)
    (hSafe : ∀ p ∈ List.zip ws keys, thresholdPairSafe p)
    (hEnough : threshold ≤ thresholdSafeCount (List.zip ws keys)) :
    UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto keys threshold ws h ctx =
    .ok () := by
  have hLenFalse : (ws.length != keys.length) = false := by
    simp [hLen]
  have hLoop :
      List.forIn.loop thresholdBody (List.zip ws keys) 0 =
        Except.ok (thresholdSafeCount (List.zip ws keys)) := by
    simpa using forIn_loop_all_safe_counts (safe := List.zip ws keys) (init := 0) hSafe
  have hNotBelow : ¬ thresholdSafeCount (List.zip ws keys) < threshold := by
    exact Nat.not_lt_of_ge hEnough
  simp [UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto, hLenFalse, Except.bind]
  have hFinal :
      (do
        let r ← List.forIn (List.zip ws keys) 0
          (fun x r =>
            if x.fst.suiteId == RubinFormal.SUITE_ID_SENTINEL then
              pure (.yield r)
            else if x.fst.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 then
              if SHA3.sha3_256 x.fst.pubkey != x.snd then do
                throw "TX_ERR_SIG_INVALID"
                pure (.yield (r + 1))
              else
                pure (.yield (r + 1))
            else do
              throw "TX_ERR_SIG_ALG_INVALID"
              pure (.yield r))
        if r < threshold then
          throw "TX_ERR_SIG_INVALID"
        else
          pure ()) = Except.ok () := by
    rw [thresholdForIn_eq_live]
    simp [List.forIn]
    rw [hLoop]
    change
      (if thresholdSafeCount (List.zip ws keys) < threshold then
        Except.error "TX_ERR_SIG_INVALID"
      else
        Except.ok ()) = Except.ok ()
    simp [Except.bind, hNotBelow]
  simpa using hFinal

/-- Follow-up outer live layer: when vault sponsor checks pass, any threshold
    hash mismatch anywhere propagates through `validateVaultSpend` as
    `TX_ERR_SIG_INVALID`. -/
theorem vault_threshold_hash_mismatch_anywhere_rejected
    (lids : List Bytes) (covs : List Nat) (vOwnLid : Bytes)
    (vKeys : List Bytes) (vThr : Nat) (vWit : List WitnessItem) (h : Nat)
    (outs : List UtxoBasicV1.TxOut) (wl : List Bytes)
    (safe : List (WitnessItem × Bytes))
    (bad : WitnessItem × Bytes)
    (rest : List (WitnessItem × Bytes))
    (hSponsorOk : (List.zip covs lids).all (fun (cov, lid) =>
      cov == CovenantGenesisV1.COV_TYPE_VAULT || lid == vOwnLid) = true)
    (hLen : vWit.length = vKeys.length)
    (hZip : List.zip vWit vKeys = safe ++ bad :: rest)
    (hSafe : ∀ p ∈ safe, thresholdPairSafe p)
    (hBad : thresholdPairMismatch bad) :
    UtxoApplyGenesisV1.validateVaultSpend true lids covs vOwnLid vKeys vThr vWit h outs wl =
      .error "TX_ERR_SIG_INVALID" := by
  have hSig :
      UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto vKeys vThr vWit h "CORE_VAULT" =
        .error "TX_ERR_SIG_INVALID" := by
    exact threshold_hash_mismatch_anywhere_rejected
      vKeys vThr vWit h "CORE_VAULT" safe bad rest hLen hZip hSafe hBad
  simp [UtxoApplyGenesisV1.validateVaultSpend, hSponsorOk, hSig]

/-- Follow-up outer live layer: when vault sponsor checks pass and the zipped
    threshold witness/key loop stays structurally safe but below threshold,
    `validateVaultSpend` rejects with `TX_ERR_SIG_INVALID`. -/
theorem vault_threshold_below_required_count_rejected
    (lids : List Bytes) (covs : List Nat) (vOwnLid : Bytes)
    (vKeys : List Bytes) (vThr : Nat) (vWit : List WitnessItem) (h : Nat)
    (outs : List UtxoBasicV1.TxOut) (wl : List Bytes)
    (hSponsorOk : (List.zip covs lids).all (fun (cov, lid) =>
      cov == CovenantGenesisV1.COV_TYPE_VAULT || lid == vOwnLid) = true)
    (hLen : vWit.length = vKeys.length)
    (hSafe : ∀ p ∈ List.zip vWit vKeys, thresholdPairSafe p)
    (hBelow : thresholdSafeCount (List.zip vWit vKeys) < vThr) :
    UtxoApplyGenesisV1.validateVaultSpend true lids covs vOwnLid vKeys vThr vWit h outs wl =
      .error "TX_ERR_SIG_INVALID" := by
  have hSig :
      UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto vKeys vThr vWit h "CORE_VAULT" =
        .error "TX_ERR_SIG_INVALID" := by
    exact threshold_below_required_count_rejected vKeys vThr vWit h "CORE_VAULT" hLen hSafe hBelow
  simp [UtxoApplyGenesisV1.validateVaultSpend, hSponsorOk, hSig]

/-- Follow-up outer live layer: when vault sponsor checks pass, the threshold
    witness/key loop is structurally safe, enough ML-DSA-87 items match, and
    the whitelist passes, `validateVaultSpend` accepts. -/
theorem vault_threshold_required_count_accepts
    (lids : List Bytes) (covs : List Nat) (vOwnLid : Bytes)
    (vKeys : List Bytes) (vThr : Nat) (vWit : List WitnessItem) (h : Nat)
    (outs : List UtxoBasicV1.TxOut) (wl : List Bytes)
    (hSponsorOk : (List.zip covs lids).all (fun (cov, lid) =>
      cov == CovenantGenesisV1.COV_TYPE_VAULT || lid == vOwnLid) = true)
    (hLen : vWit.length = vKeys.length)
    (hSafe : ∀ p ∈ List.zip vWit vKeys, thresholdPairSafe p)
    (hEnough : vThr ≤ thresholdSafeCount (List.zip vWit vKeys))
    (hWL : UtxoApplyGenesisV1.vaultSpendOutputsAllowed wl outs = true) :
    UtxoApplyGenesisV1.validateVaultSpend true lids covs vOwnLid vKeys vThr vWit h outs wl =
      .ok () := by
  have hSig :
      UtxoApplyGenesisV1.validateThresholdSigSpendNoCrypto vKeys vThr vWit h "CORE_VAULT" =
        .ok () := by
    exact threshold_required_count_accepts vKeys vThr vWit h "CORE_VAULT" hLen hSafe hEnough
  exact UtxoApplyGenesisV1.vault_all_pass lids covs vOwnLid vKeys vThr vWit h outs wl
    hSponsorOk hSig hWL

end RubinFormal
