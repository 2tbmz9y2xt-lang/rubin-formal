import Std
import RubinFormal.Wire
import RubinFormal.CompactSize
import RubinFormal.TxWire
import RubinFormal.BlockWire
import RubinFormal.Hash

namespace RubinFormal

abbrev Byte := UInt8
abbrev Bytes := List Byte

def bytesOfAscii (xs : List Nat) : Bytes :=
  xs.map UInt8.ofNat

-- ASCII("RUBIN-GENESIS-v1")
def GENESIS_PREFIX : Bytes :=
  bytesOfAscii
    [ 82, 85, 66, 73, 78, 45, 71, 69, 78, 69, 83, 73, 83, 45, 118, 49 ]

-- Spec §1.1.1: serialized_genesis_without_chain_id_field =
-- ASCII("RUBIN-GENESIS-v1") || BlockHeaderBytes || CompactSize(tx_count) || TxBytes(txs...)
def GenesisBytes (hdr : BlockHeader) (txs : List Tx) : Option Bytes := do
  let txCount ← encodeCompactSize txs.length
  let txBytes : List Bytes ← txs.mapM TxBytes
  pure <| concat ([GENESIS_PREFIX, BlockHeaderBytes hdr, txCount] ++ txBytes)

def chain_id (hdr : BlockHeader) (txs : List Tx) : Option Bytes := do
  let gb ← GenesisBytes hdr txs
  pure (SHA3_256 gb)

theorem GenesisBytes_deterministic (hdr : BlockHeader) (txs : List Tx) :
    GenesisBytes hdr txs = GenesisBytes hdr txs := by rfl

end RubinFormal

