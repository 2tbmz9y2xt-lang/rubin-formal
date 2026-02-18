import Std
import RubinFormal.Wire
import RubinFormal.Hash

namespace RubinFormal

structure BlockHeader where
  version : UInt32
  prev_block_hash : Bytes -- MUST be 32 bytes
  merkle_root : Bytes     -- MUST be 32 bytes
  timestamp : UInt64
  target : Bytes          -- MUST be 32 bytes (big-endian integer when compared; raw bytes in encoding)
  nonce : UInt64
  deriving DecidableEq, Repr

-- Spec: `BlockHeaderBytes` serializes fields in order; integer fields are LE except target (raw 32 bytes).
def BlockHeaderBytes (h : BlockHeader) : Bytes :=
  concat
    [ u32le h.version
    , h.prev_block_hash
    , h.merkle_root
    , u64le h.timestamp
    , h.target
    , u64le h.nonce
    ]

-- Determinism is definitional (pure function), but we keep a named lemma as a "formal hook".
theorem BlockHeaderBytes_deterministic (h : BlockHeader) :
    BlockHeaderBytes h = BlockHeaderBytes h := by rfl

-- Fixed length holds if the 32-byte fields are well-formed.
theorem BlockHeaderBytes_len (h : BlockHeader)
    (hp : h.prev_block_hash.length = 32)
    (hm : h.merkle_root.length = 32)
    (ht : h.target.length = 32) :
    (BlockHeaderBytes h).length = 116 := by
  unfold BlockHeaderBytes concat u32le u64le
  -- u32le = 4 bytes, u64le = 8 bytes, plus 32+32+32
  -- We rely on the fact `leBytesOfNat` returns exactly k bytes.
  -- Since `u32le/u64le` are defined via `leBytesOfNat`, their lengths are definitional.
  -- This proof is intentionally lightweight for v1.1 dev formalization.
  simp [Wire.leBytesOfNat, hp, hm, ht]

-- Merkle tree hashing per spec §5.1.1 (modeled with SHA3_256 axiom).
def MerkleLeaf (txid : Bytes) : Bytes :=
  SHA3_256 (0x00 :: txid)

def MerkleNode (l r : Bytes) : Bytes :=
  SHA3_256 (0x01 :: (l ++ r))

end RubinFormal

