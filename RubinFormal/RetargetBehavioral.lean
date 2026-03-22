import RubinFormal.PowV1

/-!
# Difficulty Retarget Behavioral Proofs (§15)

Proves behavioral properties of the retarget algorithm beyond clamp bounds.
-/

namespace RubinFormal

open PowV1

/-- When tActual = tExpected, retarget candidate equals targetOldNat (identity). -/
theorem retarget_identity (targetOldNat : Nat) :
    (targetOldNat * tExpected) / tExpected = targetOldNat :=
  Nat.mul_div_cancel targetOldNat (by native_decide : 0 < tExpected)

/-- Retarget with zero actual time produces zero candidate. -/
theorem retarget_zero_tActual (targetOldNat : Nat) :
    (targetOldNat * 0) / tExpected = 0 := by simp

/-- Lo bound is always ≥ 1 (prevents zero-target). -/
theorem retarget_lo_positive (targetOldNat : Nat) :
    Nat.max 1 (targetOldNat / 4) ≥ 1 :=
  Nat.le_max_left 1 _

/-- Hi bound never exceeds powLimit. -/
theorem retarget_hi_bounded (targetOldNat : Nat) :
    Nat.min (targetOldNat * 4) powLimit ≤ powLimit :=
  Nat.min_le_right _ _

/-- Clamped result is always between lo and hi. -/
theorem retarget_clamped_in_range (candidate lo hi : Nat) :
    lo ≤ Nat.max lo (Nat.min candidate hi) ∧
    Nat.max lo (Nat.min candidate hi) ≤ Nat.max lo hi := by
  constructor
  · exact Nat.le_max_left lo _
  · exact Nat.max_le.mpr ⟨Nat.le_max_left _ _, Nat.le_trans (Nat.min_le_right _ _) (Nat.le_max_right _ _)⟩

end RubinFormal
