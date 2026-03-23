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
deriving DecidableEq, Repr

/-- Full fork-choice selector: chainwork first, tie-break by block hash.
    Models the runtime fork_choice_select operation from §23.
    Precondition: hashes must be 32 bytes (block header hashes).
    The 32-byte requirement is NOT enforced in the function type
    but IS required by the determinism proofs (bytesLT_total_of_ne
    needs equal-length lists, provided by 32 = 32). -/
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

/-- Equal-chainwork symmetric agreement: if node A sees (lh, rh) and node B
    sees (rh, lh), they agree on which chain wins. This is the key fork-choice
    property — two nodes seeing the same chains in different order will converge
    to the same tip. NOT "determinism" in the trivial sense (pure function always
    returns same output for same input), but AGREEMENT across asymmetric views. -/
theorem forkSelect_tiebreak_det (w : Nat) (lh rh : List UInt8)
    (hL : lh.length = 32) (hR : rh.length = 32) (hNeq : lh ≠ rh) :
    (forkSelect w w lh rh = .Left ∧ forkSelect w w rh lh = .Right) ∨
    (forkSelect w w lh rh = .Right ∧ forkSelect w w rh lh = .Left) := by
  unfold forkSelect; simp [Nat.lt_irrefl]
  cases hLR : bytesLT lh rh
  · have := bytesLT_total_of_ne lh rh (hL ▸ hR ▸ rfl) hNeq
    simp [hLR] at this; simp [this]
  · have := bytesLT_antisym lh rh (by simp [hLR]); simp [this]

/-- Full end-to-end symmetric agreement: for ANY two chains with different
    (work, hash) pairs, two nodes seeing them in opposite order agree on
    the winner. Subsumes both the chainwork and tie-break cases. -/
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

/-! ## Convenience: explicit heavier-loses theorem -/

/-- If lhs is heavier, rhs loses when seen from the other side. -/
theorem forkSelect_lighter_loses (lw rw : Nat) (lh rh : List UInt8) (h : lw > rw) :
    forkSelect rw lw rh lh = .Right := by
  unfold forkSelect; simp [show ¬ (rw > lw) from by omega, h]

/-! ## Concrete eval checks (smoke tests) -/

-- Heavier chain: work 100 vs 50 → Left wins
#eval forkSelect 100 50 [1] [2]  -- .Left
-- Lighter chain: work 50 vs 100 → Right wins
#eval forkSelect 50 100 [1] [2]  -- .Right
-- Equal work, lh < rh → Right wins (tie-break)
#eval forkSelect 100 100 [0] [1]  -- .Right
-- Equal work, lh > rh → Left wins (tie-break)
#eval forkSelect 100 100 [1] [0]  -- .Left

/-! ## Go/Rust code reference

Go (chainstate.go):
```
if lhsWork > rhsWork { return lhs }
if rhsWork > lhsWork { return rhs }
if bytes.Compare(lhsHash[:], rhsHash[:]) < 0 { return rhs }
return lhs
```

Rust (sync.rs):
```
match lhs_work.cmp(&rhs_work) {
    Ordering::Greater => lhs,
    Ordering::Less => rhs,
    Ordering::Equal => if lhs_hash < rhs_hash { rhs } else { lhs },
}
```

forkSelect exactly models this: chainwork first, bytesLT tie-break.
-/

end RubinFormal
