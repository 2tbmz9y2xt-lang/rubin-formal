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
import RubinFormal.UtxoApplyGenesisV1

namespace RubinFormal

namespace SpendGateLiveBridge

open NativeSuiteRotation
open NativeSpendCreateGate
open UtxoApplyGenesisV1

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

/-! ### Live function bridge — validateP2PKSpendPreSig

  The theorems above establish: model gate accept ↔ suiteId = SUITE_ID_ML_DSA_87.
  The theorems below connect this to the LIVE function validateP2PKSpendPreSig
  (UtxoApplyGenesisV1.lean), proving that the model gate verdict determines
  whether the live suite check fires or not.

  validateP2PKSpendPreSig (line 44):
    `if suite != SUITE_ID_ML_DSA_87 then throw "TX_ERR_SIG_ALG_INVALID"`

  The bridge proves: model gate accept ↔ this `!=` check evaluates to false. -/

/-- The UtxoApplyGenesisV1 module's SUITE_ID_ML_DSA_87 is definitionally
    the same as the canonical RubinFormal.SUITE_ID_ML_DSA_87.
    This grounds cross-module suite ID references. -/
private theorem utxo_suite_eq_canonical :
    UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 = RubinFormal.SUITE_ID_ML_DSA_87 := by
  native_decide

/-- Live suite check does not fire when model gate accepts.
    validateP2PKSpendPreSig line 44: `if suite != SUITE_ID_ML_DSA_87 then throw`.
    When model gate accepts (pre-rotation), suiteId = ML_DSA_87,
    so `suite != SUITE_ID_ML_DSA_87` evaluates to false — no throw. -/
theorem live_suite_check_passes_on_gate_accept
    (d : RotationDeploymentDescriptor) (h : Nat) (w : UtxoBasicV1.WitnessItem)
    (hSuites : NativeSpendSuites h d = [SUITE_ID_ML_DSA_87])
    (hAccept : nativeSpendGate d h w.suiteId = GateResult.accept) :
    (w.suiteId != UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) = false := by
  have hSuite := gate_accept_implies_ml_dsa_87 d h w.suiteId hSuites hAccept
  rw [hSuite, utxo_suite_eq_canonical]
  native_decide

/-- Live suite check fires when model gate rejects.
    When model gate rejects (pre-rotation), suiteId ≠ ML_DSA_87,
    so `suite != SUITE_ID_ML_DSA_87` evaluates to true → throw. -/
theorem live_suite_check_rejects_on_gate_reject
    (d : RotationDeploymentDescriptor) (h : Nat) (w : UtxoBasicV1.WitnessItem)
    (hSuites : NativeSpendSuites h d = [SUITE_ID_ML_DSA_87])
    (hReject : nativeSpendGate d h w.suiteId = GateResult.reject_sig_alg_invalid) :
    (w.suiteId != UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) = true := by
  -- Extract w.suiteId ≠ SUITE_ID_ML_DSA_87 from rejection
  have hNotMem : w.suiteId ∉ NativeSpendSuites h d := by
    intro hmem
    have hAcc := (fi_rot_04_spend_gate_iff d h w.suiteId).mpr hmem
    rw [hAcc] at hReject; exact absurd hReject (by decide)
  rw [hSuites] at hNotMem
  simp [List.mem_singleton] at hNotMem
  -- hNotMem : w.suiteId ≠ SUITE_ID_ML_DSA_87
  -- Convert propositional ≠ to computational != via BEq
  show (!(w.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87)) = true
  rw [utxo_suite_eq_canonical, Bool.not_eq_true']
  -- goal: (w.suiteId == SUITE_ID_ML_DSA_87) = false
  cases hbeq : (w.suiteId == SUITE_ID_ML_DSA_87)
  · rfl
  · exact absurd (eq_of_beq hbeq) hNotMem

/-- Full model-to-live bridge: nativeSpendGate accept ↔ validateP2PKSpendPreSig
    suite check passes. This is the complete bridge from model to live for #285.
    Pre-rotation scope: NativeSpendSuites(h) = {ML_DSA_87}. -/
theorem gate_iff_live_suite_check
    (d : RotationDeploymentDescriptor) (h : Nat) (w : UtxoBasicV1.WitnessItem)
    (hSuites : NativeSpendSuites h d = [SUITE_ID_ML_DSA_87]) :
    nativeSpendGate d h w.suiteId = GateResult.accept ↔
    (w.suiteId != UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) = false :=
  ⟨live_suite_check_passes_on_gate_accept d h w hSuites,
   fun hCheck => by
     have hbeq : (w.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) = true := by
       cases hb : w.suiteId == UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87
       · simp [bne, hb] at hCheck
       · rfl
     have hSuiteEq := (eq_of_beq hbeq).trans utxo_suite_eq_canonical
     exact ml_dsa_87_implies_gate_accept d h w.suiteId hSuites hSuiteEq⟩

end SpendGateLiveBridge

end RubinFormal
