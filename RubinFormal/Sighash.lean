import Std
import RubinFormal.Hash
import RubinFormal.Wire

namespace RubinFormal

abbrev Bytes32 := Bytes

-- Sighash v1 preimage (spec §4.2) modeled as a pure byte-concatenation function.
-- Hash inputs (hash_of_all_prevouts, sequences, outputs) are provided as bytes32.

structure SighashCtx where
  chain_id : Bytes32
  version : UInt32
  tx_nonce : UInt64
  hash_prevouts : Bytes32
  hash_sequences : Bytes32
  input_index : UInt32
  prev_txid : Bytes32
  prev_vout : UInt32
  input_value : UInt64
  sequence : UInt32
  hash_outputs : Bytes32
  locktime : UInt32
  deriving DecidableEq, Repr

def SIGHASH_DOMAIN_TAG : Bytes :=
  -- ASCII("RUBIN-SIGHASH-v1")
  [ 82, 85, 66, 73, 78, 45, 83, 73, 71, 72, 65, 83, 72, 45, 118, 49 ].map UInt8.ofNat

def SighashPreimage (c : SighashCtx) : Bytes :=
  concat
    [ SIGHASH_DOMAIN_TAG
    , c.chain_id
    , u32le c.version
    , u64le c.tx_nonce
    , c.hash_prevouts
    , c.hash_sequences
    , u32le c.input_index
    , c.prev_txid
    , u32le c.prev_vout
    , u64le c.input_value
    , u32le c.sequence
    , c.hash_outputs
    , u32le c.locktime
    ]

def SighashDigest (c : SighashCtx) : Bytes :=
  SHA3_256 (SighashPreimage c)

theorem SighashPreimage_deterministic (c : SighashCtx) :
    SighashPreimage c = SighashPreimage c := by rfl

end RubinFormal

