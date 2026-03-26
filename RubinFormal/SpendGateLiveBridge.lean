/-
  RubinFormal/SpendGateLiveBridge.lean — Q-FORMAL-ROTATION-SPEND-GATE-LIVE-BRIDGE-01

  Bridges the model-level nativeSpendGate (NativeSpendCreateGate.lean) to the
  live validateP2PKSpendPreSig suite check (UtxoApplyGenesisV1.lean).

  Pre-rotation scope: NativeSpendSuites(h) = {ML_DSA_87}.
  The model gate accepting ↔ suiteId = SUITE_ID_ML_DSA_87 ↔ live check passes.

  Spec: CANONICAL §5.4 (witness suite gating), §4.1.2 (rotation phases).
  Depends: NativeSpendCreateGate.lean (FI-ROT-04).
  Closes #285.
-/

import RubinFormal.NativeSpendCreateGate

namespace RubinFormal

namespace SpendGateLiveBridge

open NativeSuiteRotation
open NativeSpendCreateGate

/-! ### Pre-rotation spend suite characterization -/

/-- Pre-rotation: when h < d.h1, the only active spend suite is oldSuiteId.
    This is the foundational observation: before rotation activates,
    NativeSpendSuites collapses to a singleton. -/
theorem pre_rotation_spend_suites
    (d : RotationDeploymentDescriptor) (h : Nat)
    (hPhase1 : h < d.h1) :
    NativeSpendSuites h d = [d.oldSuiteId] := by
  simp [NativeSpendSuites, hPhase1]

/-! ### Model → Live bridge (forward direction)

  nativeSpendGate accept → suiteId = SUITE_ID_ML_DSA_87
  when NativeSpendSuites = [SUITE_ID_ML_DSA_87].

  This direction proves: if the model says "accept", the live hardcoded
  check `suite != SUITE_ID_ML_DSA_87 → reject` does NOT fire. -/

/-- When spend suites are exactly {ML_DSA_87}, model gate acceptance implies
    suiteId = SUITE_ID_ML_DSA_87, matching the live hardcoded check. -/
theorem gate_accept_implies_ml_dsa_87
    (d : RotationDeploymentDescriptor) (h suiteId : Nat)
    (hSuites : NativeSpendSuites h d = [SUITE_ID_ML_DSA_87])
    (hAccept : nativeSpendGate d h suiteId = GateResult.accept) :
    suiteId = SUITE_ID_ML_DSA_87 := by
  have hmem := fi_rot_04_spend_gate_sound d h suiteId hAccept
  rw [hSuites] at hmem
  simp [List.mem_singleton] at hmem
  exact hmem

/-! ### Live → Model bridge (backward direction)

  suiteId = SUITE_ID_ML_DSA_87 → nativeSpendGate accept
  when NativeSpendSuites = [SUITE_ID_ML_DSA_87].

  This direction proves: if the live check passes (suite is ML_DSA_87),
  the model also accepts. -/

/-- When suiteId = ML_DSA_87 and spend suites contain it, the model gate accepts. -/
theorem ml_dsa_87_implies_gate_accept
    (d : RotationDeploymentDescriptor) (h suiteId : Nat)
    (hSuites : NativeSpendSuites h d = [SUITE_ID_ML_DSA_87])
    (hSuite : suiteId = SUITE_ID_ML_DSA_87) :
    nativeSpendGate d h suiteId = GateResult.accept := by
  apply (fi_rot_04_spend_gate_iff d h suiteId).mpr
  rw [hSuites, hSuite]
  exact List.Mem.head _

/-! ### Full equivalence -/

/-- Full bridge: model gate ↔ live hardcoded suite check, pre-rotation scope.
    This is the FI-285 formal invariant: the model-level nativeSpendGate is
    semantically equivalent to the live hardcoded `suite != SUITE_ID_ML_DSA_87`
    check when NativeSpendSuites(h) = {ML_DSA_87}. -/
theorem spend_gate_live_equivalence
    (d : RotationDeploymentDescriptor) (h suiteId : Nat)
    (hSuites : NativeSpendSuites h d = [SUITE_ID_ML_DSA_87]) :
    nativeSpendGate d h suiteId = GateResult.accept ↔
    suiteId = SUITE_ID_ML_DSA_87 :=
  ⟨gate_accept_implies_ml_dsa_87 d h suiteId hSuites,
   ml_dsa_87_implies_gate_accept d h suiteId hSuites⟩

/-- Concrete Phase 1 bridge: when d.oldSuiteId = ML_DSA_87 and h < h1,
    the model gate is equivalent to the live suite check.
    This is the most common usage: genesis-era descriptor with ML_DSA_87
    as the sole native spend suite. -/
theorem spend_gate_phase1_bridge
    (d : RotationDeploymentDescriptor) (h suiteId : Nat)
    (hOld : d.oldSuiteId = SUITE_ID_ML_DSA_87)
    (hPhase1 : h < d.h1) :
    nativeSpendGate d h suiteId = GateResult.accept ↔
    suiteId = SUITE_ID_ML_DSA_87 := by
  have hSuites : NativeSpendSuites h d = [SUITE_ID_ML_DSA_87] := by
    rw [← hOld]; exact pre_rotation_spend_suites d h hPhase1
  exact spend_gate_live_equivalence d h suiteId hSuites

/-! ### Rejection bridge

  Completes the model ↔ live picture: when the live check rejects
  (suite ≠ ML_DSA_87), the model gate also rejects with the same
  error classification (TX_ERR_SIG_ALG_INVALID). -/

/-- Rejection bridge: suite ≠ ML_DSA_87 in pre-rotation scope → model gate
    rejects with reject_sig_alg_invalid, matching the live error code. -/
theorem spend_gate_rejection_bridge
    (d : RotationDeploymentDescriptor) (h suiteId : Nat)
    (hSuites : NativeSpendSuites h d = [SUITE_ID_ML_DSA_87])
    (hNeq : suiteId ≠ SUITE_ID_ML_DSA_87) :
    nativeSpendGate d h suiteId = GateResult.reject_sig_alg_invalid := by
  apply fi_rot_04_spend_gate_rejects
  rw [hSuites]
  simp [List.mem_singleton]
  exact hNeq

/-! ### Post-rotation generalization

  After rotation activates, NativeSpendSuites may contain {old, new} or {new}.
  The model gate remains the correct abstraction — these theorems show the
  gate remains sound for any phase, not just pre-rotation. -/

/-- General bridge: for ANY phase, model gate acceptance means the suite
    is one of the active spend suites (oldSuiteId or newSuiteId).
    The live code post-rotation would check `suite ∈ NATIVE_SPEND_SUITES(h)`
    instead of hardcoding ML_DSA_87. -/
theorem gate_accept_is_spend_suite
    (d : RotationDeploymentDescriptor) (h suiteId : Nat)
    (hAccept : nativeSpendGate d h suiteId = GateResult.accept) :
    suiteId ∈ NativeSpendSuites h d :=
  fi_rot_04_spend_gate_sound d h suiteId hAccept

/-- General bridge (converse): membership in NativeSpendSuites guarantees
    the model gate accepts. This is the post-rotation live code's logic. -/
theorem spend_suite_implies_gate_accept
    (d : RotationDeploymentDescriptor) (h suiteId : Nat)
    (hMem : suiteId ∈ NativeSpendSuites h d) :
    nativeSpendGate d h suiteId = GateResult.accept :=
  (fi_rot_04_spend_gate_iff d h suiteId).mpr hMem

end SpendGateLiveBridge

end RubinFormal
