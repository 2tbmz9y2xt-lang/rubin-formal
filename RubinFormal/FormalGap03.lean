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

def sem001MLDSAExactLengthStatement : Prop :=
  ∀ (w : WitnessItem) (blockHeight : Nat),
    w.suiteId = UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87 →
      (validateWitnessItemLengths w blockHeight = .ok () ↔
        w.pubkey.size = UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES ∧
        w.signature.size = UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES)

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

theorem sem001_mldsa_exact_lengths_proved : sem001MLDSAExactLengthStatement := by
  intro w blockHeight hSuite
  have hDistinct : ¬CovenantGenesisV1.SUITE_ID_ML_DSA_87 = CovenantGenesisV1.SUITE_ID_SENTINEL := by
    native_decide
  by_cases hPub : w.pubkey.size = UtxoApplyGenesisV1.ML_DSA_87_PUBKEY_BYTES
  · by_cases hSig : w.signature.size = UtxoApplyGenesisV1.ML_DSA_87_SIG_BYTES
    · simp [sem001MLDSAExactLengthStatement, validateWitnessItemLengths, hSuite,
        UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87, UtxoApplyGenesisV1.SUITE_ID_SENTINEL,
        hDistinct, hPub, hSig]
      change (Except.ok () : Except String Unit) = Except.ok ()
      rfl
    · simp [sem001MLDSAExactLengthStatement, validateWitnessItemLengths, hSuite,
        UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87, UtxoApplyGenesisV1.SUITE_ID_SENTINEL,
        hDistinct, hPub, hSig]
  · simp [sem001MLDSAExactLengthStatement, validateWitnessItemLengths, hSuite,
      UtxoApplyGenesisV1.SUITE_ID_ML_DSA_87, UtxoApplyGenesisV1.SUITE_ID_SENTINEL,
      hDistinct, hPub]

end RubinFormal
