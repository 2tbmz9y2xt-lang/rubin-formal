import Std
import RubinFormal.MerkleV2

namespace RubinFormal

namespace Merkle

theorem merkleRoot_singleton (txid : Bytes) :
    merkleRoot [txid] = some (leafHash txid) := by
  simp [merkleRoot]
  rfl

theorem reduceLevel_singleton (x : Bytes) :
    reduceLevel [x] = [x] := rfl

theorem reduceLevel_pair (x y : Bytes) :
    reduceLevel [x, y] = [nodeHash x y] := rfl

theorem reduceLevel_length_le (xs : List Bytes) :
    (reduceLevel xs).length ≤ xs.length := by
  cases xs with
  | nil =>
      simp [reduceLevel]
  | cons x xs =>
      cases xs with
      | nil =>
          simp [reduceLevel]
      | cons y rest =>
          have hLe : (reduceLevel rest).length ≤ rest.length := reduceLevel_length_le rest
          simp [reduceLevel]
          omega

theorem reduceLevel_length_lt (xs : List Bytes) (h : 2 ≤ xs.length) :
    (reduceLevel xs).length < xs.length := by
  cases xs with
  | nil =>
      simp at h
  | cons x xs =>
      cases xs with
      | nil =>
          simp at h
      | cons y rest =>
          have hLe : (reduceLevel rest).length ≤ rest.length := reduceLevel_length_le rest
          simp [reduceLevel]
          omega

theorem leafTag_ne_nodeTag : (0x00 : UInt8) ≠ 0x01 := by
  decide

theorem leafHash_nodeHash_tag_domain (txid l r : Bytes) :
    leafHash txid = SHA3.sha3_256 ((ByteArray.empty.push 0x00) ++ txid) ∧
    nodeHash l r = SHA3.sha3_256 ((ByteArray.empty.push 0x01) ++ l ++ r) := by
  constructor <;> rfl

end Merkle
end RubinFormal
