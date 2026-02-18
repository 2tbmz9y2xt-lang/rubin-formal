import Std
import RubinFormal.TxWire
import RubinFormal.CovenantParse

namespace RubinFormal

-- This module models additional consensus-level validation rules from:
-- - spec/RUBIN_L1_CANONICAL_v1.1.md §3.1 (syntax limits, witness invariants)
-- - spec/RUBIN_L1_CANONICAL_v1.1.md §3.6 (CORE_ANCHOR output constraints)
--
-- Goal: cover the missing deterministic error codes not yet enforced by the simplified UTXO model.

inductive TxErr where
  | TX_ERR_PARSE
  | TX_ERR_WITNESS_OVERFLOW
  | TX_ERR_SIG_NONCANONICAL
  | TX_ERR_COVENANT_TYPE_INVALID
  deriving DecidableEq, Repr

inductive BlockErr where
  | BLOCK_ERR_ANCHOR_BYTES_EXCEEDED
  deriving DecidableEq, Repr

-- v1.1 constants
def MAX_WITNESS_ITEMS : Nat := 1_024
def MAX_ML_DSA_SIGNATURE_BYTES : Nat := 4_627
def MAX_SLH_DSA_SIG_BYTES : Nat := 49_856

def MAX_ANCHOR_PAYLOAD_SIZE : Nat := 65_536
def MAX_ANCHOR_BYTES_PER_BLOCK : Nat := 131_072

def validateWitnessItem (w : WitnessItem) : Except TxErr Unit :=
  -- Syntax limit rule: signature lengths MUST be bounded by suite profile; violations => TX_ERR_SIG_NONCANONICAL.
  -- Sentinel encoding well-formedness is handled elsewhere; here we only treat length constraints.
  if w.suite_id = 0x01 then
    if w.signature.length = MAX_ML_DSA_SIGNATURE_BYTES then
      Except.ok ()
    else
      Except.error TxErr.TX_ERR_SIG_NONCANONICAL
  else if w.suite_id = 0x02 then
    if (0 < w.signature.length) && (w.signature.length ≤ MAX_SLH_DSA_SIG_BYTES) then
      Except.ok ()
    else
      Except.error TxErr.TX_ERR_SIG_NONCANONICAL
  else if w.suite_id = 0x00 then
    -- Sentinel: suite_id=0x00 implies pubkey_len=0 and sig_len=0, otherwise parse error.
    if w.pubkey.length = 0 && w.signature.length = 0 then
      Except.ok ()
    else
      Except.error TxErr.TX_ERR_PARSE
  else
    -- Unknown suite_id: treated as parse-level violation in v1.1 profiles.
    Except.error TxErr.TX_ERR_PARSE

def validateWitnessSection (isCoinbase : Bool) (t : Tx) : Except TxErr Unit := do
  if t.witnesses.length > MAX_WITNESS_ITEMS then
    throw TxErr.TX_ERR_WITNESS_OVERFLOW
  if isCoinbase then
    if t.witnesses.length = 0 then
      pure ()
    else
      throw TxErr.TX_ERR_PARSE
  else
    if t.witnesses.length = t.inputs.length then
      pure ()
    else
      throw TxErr.TX_ERR_PARSE
  -- Per-item profile checks
  for w in t.witnesses do
    validateWitnessItem w

def isAnchorOutput (o : TxOutput) : Bool :=
  o.covenant_type = CORE_ANCHOR_TAG

def validateAnchorOutput (o : TxOutput) : Except TxErr Unit :=
  if isAnchorOutput o then
    -- Spec: value MUST be exactly 0 and 0 < covenant_data_len <= MAX_ANCHOR_PAYLOAD_SIZE.
    if o.value != 0 then
      throw TxErr.TX_ERR_COVENANT_TYPE_INVALID
    else if o.covenant_data.length = 0 then
      throw TxErr.TX_ERR_COVENANT_TYPE_INVALID
    else if o.covenant_data.length > MAX_ANCHOR_PAYLOAD_SIZE then
      throw TxErr.TX_ERR_COVENANT_TYPE_INVALID
    else
      pure ()
  else
    pure ()

def anchorBytesInTx (t : Tx) : Nat :=
  t.outputs.foldl (fun acc o => if isAnchorOutput o then acc + o.covenant_data.length else acc) 0

def validateAnchorBlockBytes (txs : List Tx) : Except BlockErr Unit :=
  let total := txs.foldl (fun acc t => acc + anchorBytesInTx t) 0
  if total > MAX_ANCHOR_BYTES_PER_BLOCK then
    throw BlockErr.BLOCK_ERR_ANCHOR_BYTES_EXCEEDED
  else
    pure ()

end RubinFormal

