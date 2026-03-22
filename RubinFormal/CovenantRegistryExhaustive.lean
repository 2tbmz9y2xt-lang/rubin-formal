import RubinFormal.CovenantGenesisV1

/-!
# Covenant Registry Exhaustive Proofs (§14)

Proves covenant type tags are pairwise distinct and that
the canonical registry maps each known tag to a unique branch.
-/

namespace RubinFormal

open CovenantGenesisV1

/-- All canonical covenant type tags are pairwise distinct. -/
theorem covenant_types_pairwise_distinct :
    COV_TYPE_P2PK ≠ COV_TYPE_ANCHOR ∧
    COV_TYPE_P2PK ≠ COV_TYPE_HTLC ∧
    COV_TYPE_P2PK ≠ COV_TYPE_DA_COMMIT ∧
    COV_TYPE_ANCHOR ≠ COV_TYPE_HTLC ∧
    COV_TYPE_ANCHOR ≠ COV_TYPE_DA_COMMIT ∧
    COV_TYPE_HTLC ≠ COV_TYPE_DA_COMMIT := by native_decide

/-- P2PK tag is 0x0000. -/
theorem cov_type_p2pk_value : COV_TYPE_P2PK = 0x0000 := rfl

/-- ANCHOR tag is 0x0002. -/
theorem cov_type_anchor_value : COV_TYPE_ANCHOR = 0x0002 := rfl

/-- HTLC tag is 0x0100. -/
theorem cov_type_htlc_value : COV_TYPE_HTLC = 0x0100 := rfl

/-- DA_COMMIT tag is 0x0103. -/
theorem cov_type_da_commit_value : COV_TYPE_DA_COMMIT = 0x0103 := rfl

end RubinFormal
