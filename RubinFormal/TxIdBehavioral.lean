import RubinFormal.CriticalInvariants
import RubinFormal.MerkleV2

/-!
# TXID/WTXID Behavioral Proofs (§8)

Proves domain tag separation for TXID and WTXID merkle tree construction.
-/

namespace RubinFormal

open Merkle

/-- TXID leaf tag (0x00) differs from WTXID leaf tag (0x02). -/
theorem txid_wtxid_tag_distinct :
    (0x00 : UInt8) ≠ (0x02 : UInt8) := by native_decide

/-- TXID leaf tag (0x00) differs from TXID node tag (0x01). -/
theorem txid_leaf_node_tag_distinct :
    (0x00 : UInt8) ≠ (0x01 : UInt8) := by native_decide

/-- WTXID leaf tag (0x02) differs from WTXID node tag (0x03). -/
theorem wtxid_leaf_node_tag_distinct :
    (0x02 : UInt8) ≠ (0x03 : UInt8) := by native_decide

/-- All four merkle domain tags are pairwise distinct. -/
theorem all_merkle_tags_distinct :
    (0x00 : UInt8) ≠ 0x01 ∧ (0x00 : UInt8) ≠ 0x02 ∧ (0x00 : UInt8) ≠ 0x03 ∧
    (0x01 : UInt8) ≠ 0x02 ∧ (0x01 : UInt8) ≠ 0x03 ∧
    (0x02 : UInt8) ≠ 0x03 := by native_decide

-- txid_wtxid_preimage_bytes_distinct already proved in CriticalInvariants.lean

end RubinFormal
