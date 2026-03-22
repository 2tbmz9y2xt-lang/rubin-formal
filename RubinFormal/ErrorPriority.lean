import RubinFormal.BlockValidationOrder

/-!
# Error Priority Ordering (§13 / §25)

Proves deterministic error-priority ordering for `validateBlockBasic`.

The key property: when a validation stage fails, `validateBlockBasic`
returns EXACTLY that stage's error code. Later stages are never reached.

This is proved via DIRECT error propagation through the `do` block,
not just contrapositive (success → check passed).

Combined with existing theorems:
- `section25_order_complete`: success implies all checks passed in §25 order
- `section25_validation_total_proved`: totality (accept or reject)
- pairwise error code distinctness: unambiguous error attribution
-/

namespace RubinFormal

open RubinFormal.BlockBasicV1

/-! ## Direct error propagation (§25 stage ordering)

Each theorem proves: if stage N fails, `validateBlockBasic` returns
exactly stage N's error code. This is the DIRECT direction, not just
the contrapositive.
-/

/-- Stage 1: parse failure → validateBlockBasic returns the parse error. -/
theorem error_priority_parse
    (blockBytes : Bytes) (ph pt : Option Bytes) (err : String)
    (hFail : parseBlock blockBytes = .error err) :
    validateBlockBasic blockBytes ph pt = .error err := by
  unfold validateBlockBasic
  rw [hFail]
  rfl

/-- Stage 2: PoW failure (parse ok) → validateBlockBasic returns the PoW error. -/
theorem error_priority_pow
    (blockBytes : Bytes) (ph pt : Option Bytes)
    (pb : ParsedBlock) (err : String)
    (hParse : parseBlock blockBytes = .ok pb)
    (hFail : powCheck pb.header = .error err) :
    validateBlockBasic blockBytes ph pt = .error err := by
  unfold validateBlockBasic
  rw [hParse]
  show (do powCheck pb.header; _) = _
  rw [hFail]
  rfl

/-- Stage 3: target mismatch (parse+PoW ok) → returns BLOCK_ERR_TARGET_INVALID. -/
theorem error_priority_target
    (blockBytes : Bytes) (ph : Option Bytes)
    (pb : ParsedBlock) (expTarget : Bytes)
    (hParse : parseBlock blockBytes = .ok pb)
    (hPow : powCheck pb.header = .ok ())
    (hFail : (pb.header.target != expTarget) = true) :
    validateBlockBasic blockBytes ph (some expTarget) =
    .error "BLOCK_ERR_TARGET_INVALID" := by
  unfold validateBlockBasic
  rw [hParse]
  show (do powCheck pb.header; _) = _
  rw [hPow]
  simp only [hFail, ite_true]
  rfl

/-- Stage 4: linkage mismatch (parse+PoW+target ok) → returns BLOCK_ERR_LINKAGE_INVALID. -/
theorem error_priority_linkage
    (blockBytes : Bytes) (expPrev : Bytes)
    (pb : ParsedBlock)
    (hParse : parseBlock blockBytes = .ok pb)
    (hPow : powCheck pb.header = .ok ())
    (hFail : (pb.header.prevHash != expPrev) = true) :
    validateBlockBasic blockBytes (some expPrev) none =
    .error "BLOCK_ERR_LINKAGE_INVALID" := by
  unfold validateBlockBasic
  rw [hParse]
  show (do powCheck pb.header; _) = _
  rw [hPow]
  simp only [hFail, ite_true]
  rfl

/-! ## Monadic error propagation -/

/-- Generic short-circuit: `Except.error.bind f = Except.error`. -/
theorem except_error_bind {α β : Type} {err : String}
    (f : α → Except String β) :
    (Except.error err : Except String α).bind f = Except.error err := rfl

/-! ## Success-implies-check-passed chain (contrapositives) -/

/-- Success implies parse succeeded. -/
theorem validate_success_parse
    (b : Bytes) (ph pt : Option Bytes)
    (h : validateBlockBasic b ph pt = .ok ()) :
    ∃ pb, parseBlock b = .ok pb :=
  let ⟨pb, hp, _⟩ := validateBlockBasic_parses b ph pt h
  ⟨pb, hp⟩

/-- Success implies PoW succeeded. -/
theorem validate_success_pow
    (b : Bytes) (ph pt : Option Bytes)
    (h : validateBlockBasic b ph pt = .ok ()) :
    ∃ pb, parseBlock b = .ok pb ∧ powCheck pb.header = .ok () :=
  let ⟨pb, hp, hpow, _⟩ := validateBlockBasic_pow_passes b ph pt h
  ⟨pb, hp, hpow⟩

/-! ## Error code distinctness (§13) -/

theorem err_ne_parse_target : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_TARGET_INVALID" := by decide
theorem err_ne_parse_linkage : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_LINKAGE_INVALID" := by decide
theorem err_ne_parse_merkle : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_MERKLE_INVALID" := by decide
theorem err_ne_parse_witness : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_WITNESS_COMMITMENT" := by decide
theorem err_ne_target_linkage : ("BLOCK_ERR_TARGET_INVALID" : String) ≠ "BLOCK_ERR_LINKAGE_INVALID" := by decide
theorem err_ne_target_merkle : ("BLOCK_ERR_TARGET_INVALID" : String) ≠ "BLOCK_ERR_MERKLE_INVALID" := by decide
theorem err_ne_target_witness : ("BLOCK_ERR_TARGET_INVALID" : String) ≠ "BLOCK_ERR_WITNESS_COMMITMENT" := by decide
theorem err_ne_linkage_merkle : ("BLOCK_ERR_LINKAGE_INVALID" : String) ≠ "BLOCK_ERR_MERKLE_INVALID" := by decide
theorem err_ne_linkage_witness : ("BLOCK_ERR_LINKAGE_INVALID" : String) ≠ "BLOCK_ERR_WITNESS_COMMITMENT" := by decide
theorem err_ne_merkle_witness : ("BLOCK_ERR_MERKLE_INVALID" : String) ≠ "BLOCK_ERR_WITNESS_COMMITMENT" := by decide
theorem err_ne_ts_old_future : ("BLOCK_ERR_TIMESTAMP_OLD" : String) ≠ "BLOCK_ERR_TIMESTAMP_FUTURE" := by decide
theorem err_ne_parse_ts_old : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_TIMESTAMP_OLD" := by decide
theorem err_ne_parse_ts_future : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_TIMESTAMP_FUTURE" := by decide
theorem err_ne_tx_parse_nonce : ("TX_ERR_PARSE" : String) ≠ "TX_ERR_NONCE_REPLAY" := by decide

end RubinFormal
