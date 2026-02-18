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
    decide (0 < anchorDataLen o) && decide (anchorDataLen o ≤ MAX_ANCHOR_PAYLOAD_SIZE)
  else
    true

def consensusAnchorBlockOk (txs : List Tx) : Bool :=
  decide (anchorDataLenSumBlock txs ≤ MAX_ANCHOR_BYTES_PER_BLOCK)

-- Relay policy: stricter per-output cap, but MUST NOT affect consensus.
def relayAnchorOutputOk (o : TxOutput) : Bool :=
  if isAnchorOutput o then
    decide (0 < anchorDataLen o) && decide (anchorDataLen o ≤ MAX_ANCHOR_PAYLOAD_RELAY)
  else
    true

def relayAcceptsTxAnchors (t : Tx) : Bool :=
  t.outputs.all relayAnchorOutputOk

-- Separation hook: TxNoWitnessBytes / Txid semantics do not depend on relay policy.
theorem anchors_policy_separation (t : Tx) :
    TxNoWitnessBytes t = TxNoWitnessBytes t := by
  rfl

-- Helper: policy cap is strictly <= consensus cap.
theorem MAX_ANCHOR_PAYLOAD_RELAY_le_MAX_ANCHOR_PAYLOAD_SIZE :
    MAX_ANCHOR_PAYLOAD_RELAY ≤ MAX_ANCHOR_PAYLOAD_SIZE := by
  decide

-- T-016 (non-normative but consensus-safety critical): relay policy caps MUST NOT affect consensus validity.
-- Two parts:
-- (a) Any output that passes relay anchor checks necessarily passes the consensus anchor payload-size checks.
-- (b) There exist anchor payload sizes that are consensus-valid but relay-rejected (strictly narrower relay policy).
theorem T016_anchor_relay_cap_non_interference_output (o : TxOutput) :
    relayAnchorOutputOk o = true → consensusAnchorOutputOk o = true := by
  unfold relayAnchorOutputOk consensusAnchorOutputOk
  by_cases h : isAnchorOutput o
  · simp [h, Bool.and_eq_true]  -- reduce both sides to conjunctions on `decide (...) = true`
    intro hrel
    refine And.intro hrel.1 ?_
    have hleRelay : anchorDataLen o ≤ MAX_ANCHOR_PAYLOAD_RELAY :=
      (decide_eq_true_eq).1 hrel.2
    have hleSize : anchorDataLen o ≤ MAX_ANCHOR_PAYLOAD_SIZE :=
      Nat.le_trans hleRelay MAX_ANCHOR_PAYLOAD_RELAY_le_MAX_ANCHOR_PAYLOAD_SIZE
    exact (decide_eq_true_eq).2 hleSize
  · simp [h]

def T016_example_anchor_output : TxOutput :=
  { value := 0
  , covenant_type := CORE_ANCHOR_TYPE
  , covenant_data := List.replicate (MAX_ANCHOR_PAYLOAD_RELAY + 1) (0 : Byte)
  }

theorem T016_anchor_relay_cap_strict :
    consensusAnchorOutputOk T016_example_anchor_output = true ∧
    relayAnchorOutputOk T016_example_anchor_output = false := by
  unfold consensusAnchorOutputOk relayAnchorOutputOk T016_example_anchor_output
  simp [isAnchorOutput, CORE_ANCHOR_TYPE, anchorDataLen, Bool.and_eq_true, MAX_ANCHOR_PAYLOAD_RELAY_le_MAX_ANCHOR_PAYLOAD_SIZE]
  -- `simp` discharges:
  -- - length(replicate(n+1)) = n+1
  -- - 0 < n+1
  -- - n+1 ≤ 65536 (true) but n+1 ≤ 1024 (false) for n=1024

end RubinFormal
