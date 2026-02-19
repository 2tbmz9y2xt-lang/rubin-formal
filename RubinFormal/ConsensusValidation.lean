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

-- ----------------------------
-- Phase 1 invariants (theorems)
-- ----------------------------

theorem validateAnchorOutput_ok_of_not_anchor (o : TxOutput) (h : isAnchorOutput o = false) :
    validateAnchorOutput o = Except.ok () := by
  unfold validateAnchorOutput
  simp [h]

theorem validateAnchorOutput_ok_implies_guards_false (o : TxOutput) (h : isAnchorOutput o = true)
    (hok : validateAnchorOutput o = Except.ok ()) :
    (o.value != 0) = false ∧
      (o.covenant_data.length = 0) = false ∧
      (o.covenant_data.length > MAX_ANCHOR_PAYLOAD_SIZE) = false := by
  unfold validateAnchorOutput at hok
  -- Reduce the outer if via h, then peel nested guards one by one.
  simp [h] at hok
  by_cases hv : (o.value != 0)
  · -- If the first guard is true we would return error, contradicting hok.
    simp [hv] at hok
  · have hvf : (o.value != 0) = false := by simp [hv]
    -- Continue to second guard.
    have hok2 : (if o.covenant_data.length = 0 then Except.error TxErr.TX_ERR_COVENANT_TYPE_INVALID
      else if o.covenant_data.length > MAX_ANCHOR_PAYLOAD_SIZE then Except.error TxErr.TX_ERR_COVENANT_TYPE_INVALID
      else Except.ok ()) = Except.ok () := by
        simpa [hv, hvf] using hok
    by_cases hz : (o.covenant_data.length = 0)
    · simp [hz] at hok2
    · have hzf : (o.covenant_data.length = 0) = false := by simp [hz]
      -- Third guard.
      have hok3 : (if o.covenant_data.length > MAX_ANCHOR_PAYLOAD_SIZE then Except.error TxErr.TX_ERR_COVENANT_TYPE_INVALID
        else Except.ok ()) = Except.ok () := by
          simpa [hz, hzf] using hok2
      by_cases hgt : (o.covenant_data.length > MAX_ANCHOR_PAYLOAD_SIZE)
      · simp [hgt] at hok3
      · have hgtf : (o.covenant_data.length > MAX_ANCHOR_PAYLOAD_SIZE) = false := by simp [hgt]
        exact ⟨hvf, hzf, hgtf⟩

theorem validateAnchorBlockBytes_ok_implies_le (txs : List Tx)
    (hok : validateAnchorBlockBytes txs = Except.ok ()) :
    (txs.foldl (fun acc t => acc + anchorBytesInTx t) 0) ≤ MAX_ANCHOR_BYTES_PER_BLOCK := by
  unfold validateAnchorBlockBytes at hok
  by_cases hgt : (txs.foldl (fun acc t => acc + anchorBytesInTx t) 0) > MAX_ANCHOR_BYTES_PER_BLOCK
  · simp [hgt] at hok
  · exact Nat.le_of_not_gt hgt

theorem validateWitnessSection_ok_implies_lengths (isCoinbase : Bool) (t : Tx)
    (hok : validateWitnessSection isCoinbase t = Except.ok ()) :
    t.witnesses.length ≤ MAX_WITNESS_ITEMS ∧
      (isCoinbase = true → t.witnesses.length = 0) ∧
      (isCoinbase = false → t.witnesses.length = t.inputs.length) := by
  -- This is "weight-adjacent": it covers witness_count bounds and basic shape.
  unfold validateWitnessSection at hok
  by_cases hcap : t.witnesses.length > MAX_WITNESS_ITEMS
  · simp [hcap] at hok
  · have hle : t.witnesses.length ≤ MAX_WITNESS_ITEMS := Nat.le_of_not_gt hcap
    by_cases hcb : isCoinbase
    · have : (if t.witnesses.length = 0 then (pure ()) else throw TxErr.TX_ERR_PARSE) = Except.ok () := by
        simpa [hcap, hcb] using hok
      have hw0 : t.witnesses.length = 0 := by
        by_cases hw : t.witnesses.length = 0
        · exact hw
        · simp [hw] at this
      refine And.intro hle ?_
      refine And.intro (by intro _; simpa [hcb] using hw0) ?_
      intro hfalse
      cases hfalse
    · have : (if t.witnesses.length = t.inputs.length then (pure ()) else throw TxErr.TX_ERR_PARSE) = Except.ok () := by
        simpa [hcap, hcb] using hok
      have hweq : t.witnesses.length = t.inputs.length := by
        by_cases hw : t.witnesses.length = t.inputs.length
        · exact hw
        · simp [hw] at this
      refine And.intro hle ?_
      refine And.intro (by intro htrue; cases (by simpa using htrue)) ?_
      intro _; exact hweq

end RubinFormal
