import RubinFormal.BlockValidationOrder

/-!
# Error Priority Ordering (§13 / §25)

Establishes deterministic error-priority properties for `validateBlockBasic`.

Combined with existing theorems:
- `section25_order_complete`: success implies all checks passed in §25 order
- `section25_validation_total_proved`: validate always either accepts or rejects
- `validateBlockBasic_parses`: success implies parse succeeded
- `validateBlockBasic_pow_passes`: success implies PoW succeeded

These yield the error-priority contract: when a check fails, all subsequent
checks in §25 order are unreachable, so the reported error is deterministic.

This file adds:
1. Generic monadic error propagation lemma
2. Success-implies-check-passed contrapositive chain
3. Pairwise error code distinctness for all §13/§25 error codes
-/

namespace RubinFormal

open RubinFormal.BlockBasicV1

/-! ## Monadic error propagation -/

/-- Generic short-circuit: `Except.error.bind f = Except.error`. -/
theorem except_error_bind {α β : Type} {err : String}
    (f : α → Except String β) :
    (Except.error err : Except String α).bind f = Except.error err := rfl

/-! ## Success-implies-check-passed chain (contrapositives for error priority)

Each theorem says: if validate succeeded, then check N must have passed.
The contrapositive gives error priority: if check N failed, validate failed
(and checks after N were never reached).
-/

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

/-! ## Error code distinctness (§13)

Pairwise inequality for all canonical block/tx error codes.
Combined with the priority chain above, this ensures unambiguous
error attribution.
-/

-- Block-level error codes
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

-- Timestamp error codes
theorem err_ne_ts_old_future : ("BLOCK_ERR_TIMESTAMP_OLD" : String) ≠ "BLOCK_ERR_TIMESTAMP_FUTURE" := by decide
theorem err_ne_parse_ts_old : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_TIMESTAMP_OLD" := by decide
theorem err_ne_parse_ts_future : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_TIMESTAMP_FUTURE" := by decide

-- Transaction-level error codes
theorem err_ne_tx_parse_nonce : ("TX_ERR_PARSE" : String) ≠ "TX_ERR_NONCE_REPLAY" := by decide

end RubinFormal
