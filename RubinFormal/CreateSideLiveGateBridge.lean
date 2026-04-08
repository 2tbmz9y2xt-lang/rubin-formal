import RubinFormal.CovenantGenesisV1
import RubinFormal.NativeSpendCreateGate

namespace RubinFormal

namespace CreateSideLiveGateBridge

open CovenantGenesisV1
open NativeSpendCreateGate

/-- Descriptor-aware P2PK create-side branch extracted from the runtime
    rotation create check.
    Scope is intentionally post-rotation only: legacy pre-rotation creation
    remains owned by `validateOutGenesis`.
    Ordering mirrors the live descriptor-aware branch:
    value/length structural guards first, then native create-suite gating. -/
def validateP2PKCreateWithRotation
    (out : TxOut)
    (blockHeight : Nat)
    (d : NativeSuiteRotation.RotationDeploymentDescriptor) :
    Except String Unit := do
  if out.value == 0 then
    throw "TX_ERR_COVENANT_TYPE_INVALID"
  if out.covenantData.size != MAX_P2PK_COVENANT_DATA then
    throw "TX_ERR_COVENANT_TYPE_INVALID"
  let suiteId := (out.covenantData.get! 0).toNat
  if !NativeSpendCreateGate.liveCreateGateAllows (some d) blockHeight suiteId then
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
    validateP2PKCreateWithRotation out blockHeight d =
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
    validateP2PKCreateWithRotation out blockHeight d = .ok () ↔
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

end CreateSideLiveGateBridge

end RubinFormal
