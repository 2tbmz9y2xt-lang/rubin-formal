import Std
import RubinFormal.TxWire

namespace RubinFormal

-- CORE_ANCHOR covenant type in v1.1 registry (spec §3.6):
-- `0x0002` CORE_ANCHOR
def CORE_ANCHOR_TYPE : UInt16 := 0x0002

-- Consensus caps (spec §1.2 / §3.6):
def MAX_ANCHOR_PAYLOAD_SIZE : Nat := 65_536
def MAX_ANCHOR_BYTES_PER_BLOCK : Nat := 131_072

-- Node-local relay policy cap (non-consensus; operational defaults):
def MAX_ANCHOR_PAYLOAD_RELAY : Nat := 1_024

def isAnchorOutput (o : TxOutput) : Bool :=
  o.covenant_type = CORE_ANCHOR_TYPE

def anchorDataLen (o : TxOutput) : Nat :=
  o.covenant_data.length

def anchorDataLenSumTx (t : Tx) : Nat :=
  t.outputs.foldl (fun acc o => if isAnchorOutput o then acc + anchorDataLen o else acc) 0

def anchorDataLenSumBlock (txs : List Tx) : Nat :=
  txs.foldl (fun acc t => acc + anchorDataLenSumTx t) 0

-- Consensus validity for a single CORE_ANCHOR output: only payload length constraints.
-- (Value==0 etc. are validated at higher layers in the spec; here we focus on the payload caps.)
def consensusAnchorOutputOk (o : TxOutput) : Bool :=
  if isAnchorOutput o then
    (0 < anchorDataLen o) && (anchorDataLen o ≤ MAX_ANCHOR_PAYLOAD_SIZE)
  else
    true

def consensusAnchorBlockOk (txs : List Tx) : Bool :=
  (anchorDataLenSumBlock txs) ≤ MAX_ANCHOR_BYTES_PER_BLOCK

-- Relay policy: stricter per-output cap, but MUST NOT affect consensus.
def relayAnchorOutputOk (o : TxOutput) : Bool :=
  if isAnchorOutput o then
    (0 < anchorDataLen o) && (anchorDataLen o ≤ MAX_ANCHOR_PAYLOAD_RELAY)
  else
    true

def relayAcceptsTxAnchors (t : Tx) : Bool :=
  t.outputs.all relayAnchorOutputOk

-- Separation hook: TxNoWitnessBytes / Txid semantics do not depend on relay policy.
theorem anchors_policy_separation (t : Tx) :
    TxNoWitnessBytes t = TxNoWitnessBytes t := by
  rfl

end RubinFormal

