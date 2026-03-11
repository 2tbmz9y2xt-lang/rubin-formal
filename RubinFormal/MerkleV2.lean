import Std
import RubinFormal.Types
import RubinFormal.SHA3_256

namespace RubinFormal

namespace Merkle

def leafHash (txid : Bytes) : Bytes :=
  SHA3.sha3_256 ((ByteArray.empty.push 0x00) ++ txid)

def nodeHash (l r : Bytes) : Bytes :=
  SHA3.sha3_256 ((ByteArray.empty.push 0x01) ++ l ++ r)

def reduceLevel (xs : List Bytes) : List Bytes :=
  match xs with
  | [] => []
  | [x] => [x]
  | x :: y :: rest => nodeHash x y :: reduceLevel rest

private theorem reduceLevel_length_le_internal (xs : List Bytes) :
    (reduceLevel xs).length ≤ xs.length := by
  cases xs with
  | nil =>
      simp [reduceLevel]
  | cons x xs =>
      cases xs with
      | nil =>
          simp [reduceLevel]
      | cons y rest =>
          have hLe : (reduceLevel rest).length ≤ rest.length := reduceLevel_length_le_internal rest
          simp [reduceLevel]
          omega

private theorem reduceLevel_length_lt_internal (xs : List Bytes) (h : 2 ≤ xs.length) :
    (reduceLevel xs).length < xs.length := by
  cases xs with
  | nil =>
      simp at h
  | cons x xs =>
      cases xs with
      | nil =>
          simp at h
      | cons y rest =>
          have hLe : (reduceLevel rest).length ≤ rest.length := reduceLevel_length_le_internal rest
          simp [reduceLevel]
          omega

def merkleRootFromLevel : List Bytes → Option Bytes
  | [] => none
  | [r] => some r
  | x :: y :: rest => merkleRootFromLevel (reduceLevel (x :: y :: rest))
termination_by level => level.length
decreasing_by
  simpa using
    reduceLevel_length_lt_internal (x :: y :: rest)
      (Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le _)))

def merkleRoot (txids : List Bytes) : Option Bytes :=
  merkleRootFromLevel (txids.map leafHash)

end Merkle
end RubinFormal
