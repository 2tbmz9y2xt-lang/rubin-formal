import RubinFormal.VersionBits
import RubinFormal.TxWire
import RubinFormal.Sighash
import RubinFormal.UTXO
import RubinFormal.DeploymentGate

namespace RubinFormal

-- This file provides "assertion-level" linkage between conformance vectors and formal lemmas.
-- It does not parse YAML fixtures; instead, it encodes the essential preconditions as theorem inputs.

-- -----------------------------------------------------------------------------
-- CV-SIGHASH
-- -----------------------------------------------------------------------------

-- CV-SIGHASH SIGHASH-01 / SIGHASH-03: txid excludes witness bytes.
-- In our model this is reflected by `TxNoWitnessBytes` ignoring `t.witnesses`.
theorem CV_SIGHASH_01_txid_excludes_witness (t : TxWire.Tx) (ws : List TxWire.WitnessItem) :
    TxWire.TxNoWitnessBytes { t with witnesses := ws } = TxWire.TxNoWitnessBytes t := by
  rfl

-- CV-SIGHASH SIGHASH-06: output_count=0 => outputsPreimage = empty.
theorem CV_SIGHASH_06_outputs_empty (t : TxWire.Tx) (h : t.outputs = []) :
    TxWire.outputsPreimage t = some [] := by
  exact TxWire.outputsPreimage_empty t h

-- -----------------------------------------------------------------------------
-- CV-UTXO
-- -----------------------------------------------------------------------------

-- CV-UTXO UTXO-01: spend of missing outpoint rejected.
-- We encode the essential precondition `lookupInputValues u t.inputs = none`.
theorem CV_UTXO_01_missing_outpoint
    (u : UTXO.UTXOSet) (t : UTXO.Tx)
    (hcb : t.isCoinbase = false)
    (hwc : t.witness_count = t.inputs.length)
    (hdup : UTXO.hasDuplicateOutpoints t.inputs = false)
    (hmiss : UTXO.lookupInputValues u t.inputs = none) :
    UTXO.validateTx u t = Except.error UTXO.TxErr.TX_ERR_MISSING_UTXO := by
  -- unfold the validator to the point where it consults the UTXO map
  unfold UTXO.validateTx
  -- discharge the early structural checks by rewriting the supplied equalities
  simp [hcb, hwc, hdup, hmiss]

-- CV-UTXO UTXO-02: intra-tx duplicate outpoint rejected deterministically as TX_ERR_PARSE
-- before any UTXO lookup.
theorem CV_UTXO_02_duplicate_outpoint
    (u : UTXO.UTXOSet) (t : UTXO.Tx)
    (hcb : t.isCoinbase = false)
    (hwc : t.witness_count = t.inputs.length)
    (hdup : UTXO.hasDuplicateOutpoints t.inputs = true) :
    UTXO.validateTx u t = Except.error UTXO.TxErr.TX_ERR_PARSE := by
  unfold UTXO.validateTx
  simp [hcb, hwc, hdup]

-- CV-UTXO UTXO-03: value conservation error when sum(outputs) > sum(inputs).
-- We encode the essential preconditions: inputs are present, sums are defined, and sumOut > sumIn.
theorem CV_UTXO_03_value_conservation
    (u : UTXO.UTXOSet) (t : UTXO.Tx)
    (hcb : t.isCoinbase = false)
    (hwc : t.witness_count = t.inputs.length)
    (hdup : UTXO.hasDuplicateOutpoints t.inputs = false)
    (ins : List U64) (hins : UTXO.lookupInputValues u t.inputs = some ins)
    (sumIn sumOut : U64)
    (hsIn : U64.sum? ins = some sumIn)
    (hsOut : U64.sum? (UTXO.valuesOfOutputs t.outputs) = some sumOut)
    (hgt : sumOut.val > sumIn.val) :
    UTXO.validateTx u t = Except.error UTXO.TxErr.TX_ERR_VALUE_CONSERVATION := by
  unfold UTXO.validateTx
  -- reach the value-conservation branch by rewriting lookup and sum results
  simp [hcb, hwc, hdup, hins, hsIn, hsOut, hgt]

-- -----------------------------------------------------------------------------
-- CV-DEP / VERSION_BITS
-- -----------------------------------------------------------------------------

-- CV-DEP DEP-01: Suite 0x02 spend rejected when suite not ACTIVE.
theorem CV_DEP_01_suite02_rejected_when_not_active (d : DeployCtx) (h : d.slh_dsa_suite_active = false) :
    gateSuiteId d 0x02 = Except.error TxErr.TX_ERR_DEPLOYMENT_INACTIVE := by
  unfold gateSuiteId
  simp [h]

-- CV-DEP DEP-02: Suite 0x02 spend accepted when suite ACTIVE.
theorem CV_DEP_02_suite02_accepted_when_active (d : DeployCtx) (h : d.slh_dsa_suite_active = true) :
    gateSuiteId d 0x02 = Except.ok () := by
  unfold gateSuiteId
  simp [h]

-- CV-DEP DEP-03: Suite 0x01 valid regardless of suite 0x02 activation.
theorem CV_DEP_03_suite01_always_allowed (d : DeployCtx) :
    gateSuiteId d 0x01 = Except.ok () := by
  unfold gateSuiteId
  simp

-- CV-DEP DEP-04: Unknown suite_id rejected as non-consensus algorithm.
theorem CV_DEP_04_unknown_suite_rejected (d : DeployCtx) (sid : UInt8)
    (h0 : sid ≠ 0x00) (h1 : sid ≠ 0x01) (h2 : sid ≠ 0x02) :
    gateSuiteId d sid = Except.error TxErr.TX_ERR_SIG_ALG_INVALID := by
  unfold gateSuiteId
  simp [h0, h1, h2]

-- CV-DEP DEP-05: ordering at boundary; LOCKED_IN takes precedence over FAILED.
theorem CV_DEP_05_ordering_lockedin_over_failed
    (d : Deployment) (sig : SignalAt) (h : Nat)
    (ws : VBWorkState)
    (hws : ws.state = VBState.STARTED)
    (windowStart : Nat)
    (hs : windowStart = (if h >= d.signal_window then h - d.signal_window else 0))
    (hcnt : countSignalsInWindow sig windowStart d.signal_window ≥ d.threshold)
    (htimeout : h ≥ d.timeout_height) :
    (vbStepAtBoundary d sig h ws).state = VBState.LOCKED_IN := by
  exact T003_started_boundary_ordering_lockedin_over_failed d sig h ws hws windowStart hs hcnt htimeout

-- CV-DEP DEP-04 style: strong ACTIVE monotonicity.
theorem CV_DEP_ACTIVE_monotone
    (d : Deployment) (sig : SignalAt) (h1 h2 : Nat)
    (hw : d.signal_window ≠ 0)
    (hle : h1 ≤ h2)
    (ha : vbStateAtHeight d sig h1 = VBState.ACTIVE) :
    vbStateAtHeight d sig h2 = VBState.ACTIVE := by
  exact T007_version_bits_monotonicity_strong d sig h1 h2 hw hle ha

end RubinFormal
