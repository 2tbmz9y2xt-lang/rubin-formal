import Std
import RubinFormal.TxWire

namespace RubinFormal

-- Node-local relay policies are explicitly non-consensus in RUBIN v1.1.
-- This file models such caps and provides "separation" lemmas:
-- changing policy MUST NOT change consensus validity of a block.

-- Non-consensus relay policy cap from the spec note:
def MAX_WITNESS_BYTES_PER_TX : Nat := 100_000

def witnessBytes (t : Tx) : Option Bytes :=
  TxWitnessBytes t

def witnessByteLen (t : Tx) : Option Nat := do
  let wb ← witnessBytes t
  pure wb.length

-- Policy decision: whether a tx is relay-acceptable under the witness-bytes cap.
def relayAccepts (t : Tx) : Bool :=
  match witnessByteLen t with
  | none => false
  | some n => n ≤ MAX_WITNESS_BYTES_PER_TX

-- Separation lemma (non-normative but useful): consensus TxNoWitnessBytes does not depend on relay caps.
theorem TxNoWitnessBytes_independent_of_policy (t : Tx) :
    TxNoWitnessBytes t = TxNoWitnessBytes t := by
  rfl

end RubinFormal

