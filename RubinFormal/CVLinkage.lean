import RubinFormal.VersionBits
import RubinFormal.TxWire
import RubinFormal.Sighash

namespace RubinFormal

-- This file provides "assertion-level" linkage between conformance vectors and formal lemmas.
-- It does not parse YAML fixtures; instead, it encodes the essential preconditions as theorem inputs.

-- CV-SIGHASH SIGHASH-06: output_count=0 => outputsPreimage = empty.
theorem CV_SIGHASH_06_outputs_empty (t : TxWire.Tx) (h : t.outputs = []) :
    TxWire.outputsPreimage t = some [] := by
  exact TxWire.outputsPreimage_empty t h

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

