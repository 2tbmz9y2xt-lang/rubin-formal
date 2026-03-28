import RubinFormal.CriticalInvariants
import RubinFormal.MerkleV2
import RubinFormal.MerkleStructure

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

/-- For transactions with a non-empty witness section, the actual txid preimage
    bytes (`tx.extract 0 coreEnd`) differ from the full-transaction wtxid
    preimage bytes (`tx`). This is the non-fixture structural core of §8. -/
theorem txid_wtxid_payloads_distinct_when_witness_present
    (tx : ByteArray) (coreEnd : Nat) (h : coreEnd < tx.size) :
    tx.extract 0 coreEnd ≠ tx := by
  exact txid_wtxid_preimage_bytes_distinct tx coreEnd h

/-- Section-level contract for identifier-domain separation:
    when witness is present, the raw txid and wtxid payloads already diverge,
    and the tagged leaf-preimage domains used by the Merkle layer are disjoint. -/
theorem txid_wtxid_identifier_domain_contract
    (tx : ByteArray) (coreEnd : Nat) (h : coreEnd < tx.size) :
    tx.extract 0 coreEnd ≠ tx ∧
    Merkle.txidLeafPreimage (tx.extract 0 coreEnd) ≠ Merkle.wtxidLeafPreimage tx := by
  constructor
  · exact txid_wtxid_payloads_distinct_when_witness_present tx coreEnd h
  · exact Merkle.merkle_tag_equivalence_leaf_domains_disjoint (tx.extract 0 coreEnd) tx

end RubinFormal
