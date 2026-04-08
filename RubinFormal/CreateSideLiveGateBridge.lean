import RubinFormal.CovenantGenesisV1
import RubinFormal.NativeSpendCreateGate

namespace RubinFormal

namespace CreateSideLiveGateBridge

open CovenantGenesisV1
open NativeSpendCreateGate

/-- Descriptor-aware live P2PK create-side gate extracted from the runtime
    `ValidateTxCovenantsGenesis` P2PK branch.
    Ordering mirrors the live checks:
    value/length structural guards first, then native create-suite gating. -/
def validateP2PKCreateWithRotation
    (out : TxOut)
    (blockHeight : Nat)
    (rotDesc? : Option NativeSuiteRotation.RotationDeploymentDescriptor := none) :
    Except String Unit := do
  if out.value == 0 then
    throw "TX_ERR_COVENANT_TYPE_INVALID"
  if out.covenantData.size != MAX_P2PK_COVENANT_DATA then
    throw "TX_ERR_COVENANT_TYPE_INVALID"
  let suiteId := (out.covenantData.get! 0).toNat
  if !NativeSpendCreateGate.liveCreateGateAllows rotDesc? blockHeight suiteId then
    throw "TX_ERR_SIG_ALG_INVALID"
  pure ()

/-- On the descriptor-aware branch, once the same preceding structural guards
    as the live create path pass, an inactive create suite is rejected with
    `TX_ERR_SIG_ALG_INVALID`. -/
theorem validateP2PKCreateWithRotation_rejects_inactive_suite
    (d : NativeSuiteRotation.RotationDeploymentDescriptor)
    (out : TxOut)
    (blockHeight : Nat)
    (hValue : out.value ≠ 0)
    (hSize : out.covenantData.size = MAX_P2PK_COVENANT_DATA)
    (hNotMem : (out.covenantData.get! 0).toNat ∉ NativeSuiteRotation.NativeCreateSuites blockHeight d) :
    validateP2PKCreateWithRotation out blockHeight (some d) =
      .error "TX_ERR_SIG_ALG_INVALID" := by
  have hGate :
      NativeSpendCreateGate.liveCreateGateAllows (some d) blockHeight (out.covenantData.get! 0).toNat = false :=
    (NativeSpendCreateGate.liveCreateGateAllows_some_false_iff d blockHeight
      (out.covenantData.get! 0).toNat).mpr hNotMem
  unfold validateP2PKCreateWithRotation
  simp [hValue, hSize, hGate]
  rfl

/-- Descriptor-aware live P2PK create bridge:
    under the same structural preconditions as the real create path,
    `.ok ()` is equivalent to create-suite membership. -/
theorem validateP2PKCreateWithRotation_ok_constrained
    (d : NativeSuiteRotation.RotationDeploymentDescriptor)
    (out : TxOut)
    (blockHeight : Nat)
    (hValue : out.value ≠ 0)
    (hSize : out.covenantData.size = MAX_P2PK_COVENANT_DATA) :
    validateP2PKCreateWithRotation out blockHeight (some d) = .ok () ↔
      (out.covenantData.get! 0).toNat ∈ NativeSuiteRotation.NativeCreateSuites blockHeight d := by
  constructor
  · intro hOk
    by_contra hNotMem
    have hErr :=
      validateP2PKCreateWithRotation_rejects_inactive_suite d out blockHeight hValue hSize hNotMem
    rw [hErr] at hOk
    cases hOk
  · intro hMem
    have hGate :
        NativeSpendCreateGate.liveCreateGateAllows (some d) blockHeight (out.covenantData.get! 0).toNat = true :=
      (NativeSpendCreateGate.liveCreateGateAllows_some_iff d blockHeight
        (out.covenantData.get! 0).toNat).mpr hMem
    unfold validateP2PKCreateWithRotation
    simp [hValue, hSize, hGate]
    rfl

/-- Pre-rotation fallback branch: once structural guards pass, acceptance is
    exactly the canonical `ML_DSA_87` singleton check. -/
theorem validateP2PKCreateWithRotation_none_ok_iff
    (out : TxOut)
    (blockHeight : Nat)
    (hValue : out.value ≠ 0)
    (hSize : out.covenantData.size = MAX_P2PK_COVENANT_DATA) :
    validateP2PKCreateWithRotation out blockHeight none = .ok () ↔
      (out.covenantData.get! 0).toNat = RubinFormal.SUITE_ID_ML_DSA_87 := by
  constructor
  · intro hOk
    unfold validateP2PKCreateWithRotation at hOk
    have hAllow :
        NativeSpendCreateGate.liveCreateGateAllows none blockHeight (out.covenantData.get! 0).toNat = true := by
      cases hGate : NativeSpendCreateGate.liveCreateGateAllows none blockHeight (out.covenantData.get! 0).toNat with
      | false =>
          simp [hValue, hSize, hGate] at hOk
      | true =>
          simp [hGate]
    exact (NativeSpendCreateGate.liveCreateGateAllows_none_iff blockHeight
      (out.covenantData.get! 0).toNat).mp hAllow
  · intro hSuite
    have hAllow :
        NativeSpendCreateGate.liveCreateGateAllows none blockHeight (out.covenantData.get! 0).toNat = true :=
      (NativeSpendCreateGate.liveCreateGateAllows_none_iff blockHeight
        (out.covenantData.get! 0).toNat).mpr hSuite
    unfold validateP2PKCreateWithRotation
    simp [hValue, hSize, hAllow]
    rfl

end CreateSideLiveGateBridge

end RubinFormal
