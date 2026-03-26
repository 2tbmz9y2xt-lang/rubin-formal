/-
  FormalGap03.lean — Pre-rotation scoped theorems.

  All theorems in this file carry explicit `w.suiteId = SUITE_ID_ML_DSA_87`
  hypotheses.  They remain valid as-is in the post-rotation world (they simply
  prove properties of the ML-DSA-87 code path).

  Post-rotation (Q-FORMAL-ROTATION-02/04): add per-suite variants that
  generalise bounds and binding proofs to any suite in the registry.
-/
import RubinFormal.Conformance.CVValidationOrderReplay
import RubinFormal.UtxoApplyGenesisV1

namespace RubinFormal

open RubinFormal.Conformance
open RubinFormal.UtxoBasicV1
open RubinFormal.UtxoApplyGenesisV1

def det001ValidationOrderStatement : Prop :=
  ∀ (before suffix : List ValidationCheck) (bad : ValidationCheck),
    (∀ c ∈ before, c.fails = false) →
    bad.fails = true →
    evalOrder (before ++ bad :: suffix) =
      (some bad.err, before.map ValidationCheck.name ++ [bad.name])

def sem001MLDSABoundedLengthStatement : Prop :=
  ∀ (w : WitnessItem) (blockHeight : Nat),
    w.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 →
    (validateWitnessItemLengths w blockHeight = .ok () ↔
        w.pubkey.size = UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES ∧
        0 < w.signature.size ∧
        w.signature.size ≤ UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES + 1)

def p2pkPubkeyKeyIdBound (entry : UtxoEntry) (w : WitnessItem) : Prop :=
  (SHA3.sha3_256 w.pubkey != entry.covenantData.extract 1 33) = false

def sem002MLDSABindingStatement : Prop :=
  ∀ (entry : UtxoEntry) (w : WitnessItem) (blockHeight : Nat),
    validateWitnessItemLengths w blockHeight = .ok () →
    validateP2PKSpendPreSig entry w blockHeight = .ok () →
    w.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 ∧
    w.pubkey.size = UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES ∧
    0 < w.signature.size ∧
    w.signature.size ≤ UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES + 1 ∧
    entry.covenantData.size = CovenantGenesisV1.MAX_P2PK_COVENANT_DATA ∧
    (entry.covenantData.get! 0).toNat = w.suiteId ∧
    p2pkPubkeyKeyIdBound entry w

theorem evalOrderFrom_first_failure
    (evaluated : List String)
    (before suffix : List ValidationCheck)
    (bad : ValidationCheck)
    (hBefore : ∀ c ∈ before, c.fails = false)
    (hBad : bad.fails = true) :
    evalOrderFrom (before ++ bad :: suffix) evaluated =
      (some bad.err, evaluated ++ before.map ValidationCheck.name ++ [bad.name]) := by
  induction before generalizing evaluated with
  | nil =>
      simp [Conformance.evalOrderFrom, hBad]
  | cons c cs ih =>
      have hc : c.fails = false := hBefore c (by simp)
      have hcs : ∀ x ∈ cs, x.fails = false := by
        intro x hx
        exact hBefore x (by simp [hx])
      have ih' := ih (evaluated ++ [c.name]) hcs
      simpa [Conformance.evalOrderFrom, hc, List.map, List.append_assoc] using ih'

theorem det001_validation_order_proved : det001ValidationOrderStatement := by
  intro before suffix bad hBefore hBad
  simpa [det001ValidationOrderStatement, Conformance.evalOrder] using
    evalOrderFrom_first_failure [] before suffix bad hBefore hBad

theorem sem001_mldsa_bounded_lengths_proved : sem001MLDSABoundedLengthStatement := by
  intro w blockHeight hSuite
  have hDistinct : ¬RubinFormal.SUITE_ID_ML_DSA_87 = RubinFormal.SUITE_ID_SENTINEL := by
    native_decide
  by_cases hPub : w.pubkey.size = UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES
  · by_cases hSig0 : w.signature.size = 0
    · simp [sem001MLDSABoundedLengthStatement, validateWitnessItemLengths, hSuite,
        UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87, UtxoApplyGenesisV1.SUITE_ID_SENTINEL,
        hDistinct, hPub, hSig0]
    · by_cases hSigB : w.signature.size > UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES + 1
      · simp [sem001MLDSABoundedLengthStatement, validateWitnessItemLengths, hSuite,
          UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87, UtxoApplyGenesisV1.SUITE_ID_SENTINEL,
          hDistinct, hPub, hSig0, hSigB]
      · have hSigLe : w.signature.size ≤ UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES + 1 := by omega
        have hSigPos : 0 < w.signature.size := by omega
        simp [sem001MLDSABoundedLengthStatement, validateWitnessItemLengths, hSuite,
          UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87, UtxoApplyGenesisV1.SUITE_ID_SENTINEL,
          hDistinct, hPub, hSig0, hSigB, hSigLe, hSigPos, Pure.pure]; rfl
  · simp [sem001MLDSABoundedLengthStatement, validateWitnessItemLengths, hSuite,
      UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87, UtxoApplyGenesisV1.SUITE_ID_SENTINEL,
      hDistinct, hPub]

set_option maxHeartbeats 1000000 in
theorem validateP2PKSpendPreSig_binds_pubkey
    (entry : UtxoEntry)
    (w : WitnessItem)
    (blockHeight : Nat)
    (hOk : validateP2PKSpendPreSig entry w blockHeight = .ok ()) :
    w.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 ∧
    entry.covenantData.size = CovenantGenesisV1.MAX_P2PK_COVENANT_DATA ∧
    (entry.covenantData.get! 0).toNat = w.suiteId ∧
    p2pkPubkeyKeyIdBound entry w := by
  by_cases hSuite : (w.suiteId != UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) = true
  · have hErr : validateP2PKSpendPreSig entry w blockHeight = .error "TX_ERR_SIG_ALG_INVALID" := by
      simp [validateP2PKSpendPreSig, hSuite, Except.bind]
      rfl
    rw [hErr] at hOk
    cases hOk
  · have hSuiteFalse : (w.suiteId != UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87) = false := by
      have hSuiteEq : w.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 := by
        by_contra hNeEq
        exact hSuite (by simp [hNeEq])
      simp [hSuiteEq]
    have hSuiteEq : w.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 := by
      by_contra hNeEq
      exact hSuite (by simp [hNeEq])
    by_cases hSize : (entry.covenantData.size != CovenantGenesisV1.MAX_P2PK_COVENANT_DATA) = true
    · have hErr : validateP2PKSpendPreSig entry w blockHeight = .error "TX_ERR_COVENANT_TYPE_INVALID" := by
        simp [validateP2PKSpendPreSig, hSuiteFalse, hSize, Except.bind]
        rfl
      rw [hErr] at hOk
      cases hOk
    · have hSizeFalse : (entry.covenantData.size != CovenantGenesisV1.MAX_P2PK_COVENANT_DATA) = false := by
        have hSizeEq : entry.covenantData.size = CovenantGenesisV1.MAX_P2PK_COVENANT_DATA := by
          by_contra hNeEq
          exact hSize (by simp [hNeEq])
        simp [hSizeEq]
      have hSizeEq : entry.covenantData.size = CovenantGenesisV1.MAX_P2PK_COVENANT_DATA := by
        by_contra hNeEq
        exact hSize (by simp [hNeEq])
      by_cases hTag : ((entry.covenantData.get! 0).toNat != w.suiteId) = true
      · have hErr : validateP2PKSpendPreSig entry w blockHeight = .error "TX_ERR_COVENANT_TYPE_INVALID" := by
          simp [validateP2PKSpendPreSig, hSuiteFalse, hSizeFalse, hTag, Except.bind]
          rfl
        rw [hErr] at hOk
        cases hOk
      · have hTagFalse : ((entry.covenantData.get! 0).toNat != w.suiteId) = false := by
          have hTagEq : (entry.covenantData.get! 0).toNat = w.suiteId := by
            by_contra hNeEq
            exact hTag (by simp [hNeEq])
          simp [hTagEq]
        have hTagEq : (entry.covenantData.get! 0).toNat = w.suiteId := by
          by_contra hNeEq
          exact hTag (by simp [hNeEq])
        cases hHash : (SHA3.sha3_256 w.pubkey != entry.covenantData.extract 1 33) with
        | true =>
          have hErr : validateP2PKSpendPreSig entry w blockHeight = .error "TX_ERR_SIG_INVALID" := by
            simp [validateP2PKSpendPreSig, hSuiteFalse, hSizeFalse, hTagFalse, hHash, Except.bind]
            rfl
          rw [hErr] at hOk
          cases hOk
        | false =>
          exact ⟨hSuiteEq, hSizeEq, hTagEq, hHash⟩

theorem sem002_mldsa_binding_proved : sem002MLDSABindingStatement := by
  intro entry w blockHeight hLens hPreSig
  have hBinding := validateP2PKSpendPreSig_binds_pubkey entry w blockHeight hPreSig
  rcases hBinding with ⟨hSuite, hCovSize, hSuiteTag, hKeyHash⟩
  have hLengths := (sem001_mldsa_bounded_lengths_proved w blockHeight hSuite).mp hLens
  rcases hLengths with ⟨hPub, hSigPos, hSigLe⟩
  exact ⟨hSuite, hPub, hSigPos, hSigLe, hCovSize, hSuiteTag, hKeyHash⟩

end RubinFormal
