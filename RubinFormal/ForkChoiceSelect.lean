import RubinFormal.ForkChoiceTiebreak

/-!
# Fork-Choice Selector (§23) — End-to-End Determinism

Models the full `fork_choice_select` operation: chainwork comparison first,
tie-break by block hash when chainwork is equal.

Proves:
- `forkSelect_heavier`: unequal chainwork → heavier wins
- `forkSelect_tiebreak_det`: equal chainwork + different hashes → deterministic
- `bytesLT_antisym`: strict ordering (no symmetric pair)

This upgrades the fork_choice_select bridge from `baseline` to
`machine_checked_contract`: the full selector is modeled and its
determinism is machine-checked.
-/

namespace RubinFormal

open ForkChoiceV1

/-! ## bytesLT antisymmetry (required for tie-break determinism) -/

private theorem uint8_eq_helper {x y : UInt8}
    (h1 : ¬ x < y) (h2 : ¬ y < x) : x = y := by
  have h1' : ¬ x.val.val < y.val.val := h1
  have h2' : ¬ y.val.val < x.val.val := h2
  have hEq : x.val.val = y.val.val := by omega
  rcases x with ⟨⟨xn, xh⟩⟩; rcases y with ⟨⟨yn, yh⟩⟩
  simp only at hEq; subst hEq; rfl

/-- bytesLT is antisymmetric: xs < ys → ¬ (ys < xs). -/
theorem bytesLT_antisym : ∀ (xs ys : List UInt8),
    bytesLT xs ys = true → bytesLT ys xs = false
  | [], [], h => by simp [bytesLT] at h
  | [], _ :: _, _ => by simp [bytesLT]
  | _ :: _, [], h => by simp [bytesLT] at h
  | x :: xs, y :: ys, h => by
    unfold bytesLT at h ⊢
    by_cases hLt : x < y
    · simp [show ¬ (y < x) from fun hc => Nat.lt_asymm hLt hc, show y > x from hLt]
    · simp [hLt] at h; by_cases hGt : (x > y : Prop)
      · simp [hGt] at h
      · have := uint8_eq_helper hLt hGt; subst this
        simp [show ¬ (x < x) from Nat.lt_irrefl x.val.val,
              show ¬ (x > x : Prop) from Nat.lt_irrefl x.val.val] at h ⊢
        exact bytesLT_antisym xs ys h

/-! ## Fork-choice selector model -/

/-- Fork-choice outcome. -/
inductive ForkResult where
  | Left   -- lhs chain wins
  | Right  -- rhs chain wins
deriving DecidableEq

/-- Full fork-choice selector: chainwork first, tie-break by block hash.
    Models the runtime fork_choice_select operation from §23. -/
def forkSelect (lhsWork rhsWork : Nat) (lhsHash rhsHash : List UInt8) : ForkResult :=
  if lhsWork > rhsWork then .Left
  else if rhsWork > lhsWork then .Right
  else if bytesLT lhsHash rhsHash then .Right
  else .Left

/-! ## Determinism proofs -/

/-- Heavier chain always wins regardless of hash. -/
theorem forkSelect_heavier (lw rw : Nat) (lh rh : List UInt8) (h : lw > rw) :
    forkSelect lw rw lh rh = .Left := by
  simp [forkSelect, h]

/-- Equal-chainwork tie-break is deterministic: both sides agree on the winner.
    If node A sees (lh, rh) and node B sees (rh, lh), they pick the same chain. -/
theorem forkSelect_tiebreak_det (w : Nat) (lh rh : List UInt8)
    (hL : lh.length = 32) (hR : rh.length = 32) (hNeq : lh ≠ rh) :
    (forkSelect w w lh rh = .Left ∧ forkSelect w w rh lh = .Right) ∨
    (forkSelect w w lh rh = .Right ∧ forkSelect w w rh lh = .Left) := by
  unfold forkSelect; simp [Nat.lt_irrefl]
  cases hLR : bytesLT lh rh
  · have := bytesLT_total_of_ne lh rh (hL ▸ hR ▸ rfl) hNeq
    simp [hLR] at this; simp [this]
  · have := bytesLT_antisym lh rh (by simp [hLR]); simp [this]

/-- Bridge: forkSelect with chainWork composition matches heavierChain
    for the unequal-work case. -/
theorem forkSelect_chainwork_bridge (lhs rhs : List Nat)
    (lhsHash rhsHash : List UInt8)
    (h : ChainWorkV1.chainWork lhs > ChainWorkV1.chainWork rhs) :
    forkSelect (ChainWorkV1.chainWork lhs) (ChainWorkV1.chainWork rhs) lhsHash rhsHash = .Left ∧
    ChainWorkV1.heavierChain lhs rhs = true :=
  ⟨forkSelect_heavier _ _ _ _ h, heavierChain_wins lhs rhs h⟩

/-- Full end-to-end: for ANY two chains with different (work, hash) pairs,
    forkSelect gives a deterministic result — both nodes agree on winner. -/
theorem forkSelect_total_det (lw rw : Nat) (lh rh : List UInt8)
    (hL : lh.length = 32) (hR : rh.length = 32)
    (hDiff : lw ≠ rw ∨ lh ≠ rh) :
    (forkSelect lw rw lh rh = .Left ∧ forkSelect rw lw rh lh = .Right) ∨
    (forkSelect lw rw lh rh = .Right ∧ forkSelect rw lw rh lh = .Left) := by
  by_cases hGt : lw > rw
  · left
    exact ⟨forkSelect_heavier lw rw lh rh hGt,
           by unfold forkSelect; simp [show ¬ (rw > lw) from by omega, hGt]⟩
  · by_cases hLt : rw > lw
    · right
      exact ⟨by unfold forkSelect; simp [show ¬ (lw > rw) from by omega, hLt],
             forkSelect_heavier rw lw rh lh hLt⟩
    · have hEqW : lw = rw := by omega
      subst hEqW
      have hNeq : lh ≠ rh := by
        rcases hDiff with h | h
        · exact absurd rfl h
        · exact h
      exact forkSelect_tiebreak_det lw lh rh hL hR hNeq

end RubinFormal
