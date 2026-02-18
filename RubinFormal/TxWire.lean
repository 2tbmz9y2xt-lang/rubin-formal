import Std
import RubinFormal.Wire

namespace RubinFormal

structure TxInput where
  prev_txid : Bytes     -- MUST be 32 bytes in the spec (checked by validation, not by type here)
  prev_vout : UInt32
  script_sig : Bytes
  sequence : UInt32
  deriving DecidableEq, Repr

structure TxOutput where
  value : UInt64
  covenant_type : UInt16
  covenant_data : Bytes
  deriving DecidableEq, Repr

structure WitnessItem where
  suite_id : UInt8
  pubkey : Bytes
  signature : Bytes
  deriving DecidableEq, Repr

structure Tx where
  version : UInt32
  tx_nonce : UInt64
  inputs : List TxInput
  outputs : List TxOutput
  locktime : UInt32
  witnesses : List WitnessItem
  deriving DecidableEq, Repr

-- Encode helpers
def TxInput.bytes (i : TxInput) : Option Bytes := do
  let scLen ← encCompactSize i.script_sig.length
  pure <|
    concat
      [ i.prev_txid
      , u32le i.prev_vout
      , scLen
      , i.script_sig
      , u32le i.sequence
      ]

def TxOutput.bytes (o : TxOutput) : Option Bytes := do
  let cdLen ← encCompactSize o.covenant_data.length
  pure <|
    concat
      [ u64le o.value
      , u16le o.covenant_type
      , cdLen
      , o.covenant_data
      ]

def WitnessItem.bytes (w : WitnessItem) : Option Bytes := do
  let pkLen ← encCompactSize w.pubkey.length
  let sigLen ← encCompactSize w.signature.length
  pure <|
    concat
      [ [w.suite_id]
      , pkLen
      , w.pubkey
      , sigLen
      , w.signature
      ]

-- Spec: TxNoWitnessBytes excludes the witness section entirely.
def TxNoWitnessBytes (t : Tx) : Option Bytes := do
  let inCount ← encCompactSize t.inputs.length
  let outCount ← encCompactSize t.outputs.length
  let inBytes : List Bytes ← t.inputs.mapM TxInput.bytes
  let outBytes : List Bytes ← t.outputs.mapM TxOutput.bytes
  pure <|
    concat
      ( [ u32le t.version
        , u64le t.tx_nonce
        , inCount
        ]
        ++ inBytes
        ++ [ outCount ]
        ++ outBytes
        ++ [ u32le t.locktime ]
      )

def TxWitnessBytes (t : Tx) : Option Bytes := do
  let wCount ← encCompactSize t.witnesses.length
  let wBytes : List Bytes ← t.witnesses.mapM WitnessItem.bytes
  pure <| concat ([wCount] ++ wBytes)

-- Spec: TxBytes is full tx encoding including witness section.
def TxBytes (t : Tx) : Option Bytes := do
  let nw ← TxNoWitnessBytes t
  let w ← TxWitnessBytes t
  pure (nw ++ w)

-- Spec-aligned lemma for SIGHASH determinism basis:
-- the preimage for "hashOutputs" is the concatenation of output bytes.
def outputsPreimage (t : Tx) : Option Bytes := do
  let outBytes : List Bytes ← t.outputs.mapM TxOutput.bytes
  pure (concat outBytes)

theorem outputsPreimage_empty (t : Tx) (h : t.outputs = []) :
    outputsPreimage t = some [] := by
  unfold outputsPreimage
  simp [h]

end RubinFormal

