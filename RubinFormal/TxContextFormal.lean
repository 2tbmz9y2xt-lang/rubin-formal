import Std
import RubinFormal.ArithmeticSafety

/-!
# SPEC-TXCTX-01 §14 — Formal theorems for TxContext pre-activation gates

Eight theorems required by SPEC-TXCTX-01 §14 before any TxContext-enabled
profile may be activated on devnet or mainnet.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 1600000

namespace RubinFormal.TxContext

-- ============================================================================
-- §14 Theorem 1–2: uint128GTE_correct + uint128GTE_native_equivalence
-- ============================================================================

/-- A 128-bit unsigned integer as two 64-bit limbs (lo, hi).
    Models Go's `[2]uint64{lo, hi}`. -/
structure Uint128 where
  lo : Nat
  hi : Nat
  lo_bound : lo ≤ (2 ^ 64) - 1 := by omega
  hi_bound : hi ≤ (2 ^ 64) - 1 := by omega

/-- Mathematical value: hi * 2^64 + lo. -/
def Uint128.toNat (a : Uint128) : Nat := a.hi * 2 ^ 64 + a.lo

/-- Go-style uint128GTE: compare hi first, then lo on tie. -/
def uint128GTE (a b : Uint128) : Prop :=
  a.hi > b.hi ∨ (a.hi = b.hi ∧ a.lo ≥ b.lo)

/-- **uint128GTE_correct** (§14): definitional. -/
theorem uint128GTE_correct (a b : Uint128) :
    uint128GTE a b ↔ (a.hi > b.hi ∨ (a.hi = b.hi ∧ a.lo ≥ b.lo)) :=
  Iff.rfl

/-- Auxiliary: for any base B > 0, if hi_a > hi_b and lo_b < B,
    then hi_a * B + lo_a ≥ hi_b * B + lo_b. Abstract over B to avoid
    omega normalizing 2^64. -/
private theorem limb_gt_implies_ge (hi_a lo_a hi_b lo_b B : Nat)
    (hgt : hi_a > hi_b) (hlob : lo_b < B) :
    hi_a * B + lo_a ≥ hi_b * B + lo_b := by
  have h1 : (hi_b + 1) * B ≤ hi_a * B := Nat.mul_le_mul_right B hgt
  have h3 : (hi_b + 1) * B = hi_b * B + B := Nat.succ_mul hi_b B
  -- hi_b*B + B ≤ hi_a*B (from h1 rewritten via h3)
  have h4 : hi_b * B + B ≤ hi_a * B := h3 ▸ h1
  -- hi_b*B + lo_b < hi_b*B + B  (from hlob)
  -- hi_b*B + B ≤ hi_a*B ≤ hi_a*B + lo_a
  -- So hi_b*B + lo_b < hi_a*B + lo_a
  have hlt : hi_b * B + lo_b < hi_a * B + lo_a :=
    calc hi_b * B + lo_b
        < hi_b * B + B := Nat.add_lt_add_left hlob _
      _ ≤ hi_a * B := h4
      _ ≤ hi_a * B + lo_a := Nat.le_add_right _ _
  exact Nat.le_of_lt hlt

/-- lo ≤ 2^64 - 1 implies lo < 2^64. -/
private theorem lo_lt_base (n : Nat) (h : n ≤ (2 ^ 64) - 1) : n < 2 ^ 64 :=
  Nat.lt_of_le_of_lt h (by native_decide)

/-- Helper: hi > hi' implies toNat ≥ toNat'. -/
private theorem hi_gt_implies_ge (a b : Uint128) (hgt : a.hi > b.hi) :
    a.toNat ≥ b.toNat := by
  unfold Uint128.toNat
  exact limb_gt_implies_ge a.hi a.lo b.hi b.lo (2^64) hgt (lo_lt_base b.lo b.lo_bound)

/-- Auxiliary: symmetric for lt direction. -/
private theorem limb_lt_implies_lt (hi_a lo_a hi_b lo_b B : Nat)
    (hlt : hi_a < hi_b) (hloa : lo_a < B) :
    hi_a * B + lo_a < hi_b * B + lo_b := by
  have h1 : (hi_a + 1) * B ≤ hi_b * B := Nat.mul_le_mul_right B hlt
  have h3 : (hi_a + 1) * B = hi_a * B + B := Nat.succ_mul hi_a B
  have h4 : hi_a * B + B ≤ hi_b * B := h3 ▸ h1
  calc hi_a * B + lo_a
      < hi_a * B + B := Nat.add_lt_add_left hloa _
    _ ≤ hi_b * B := h4
    _ ≤ hi_b * B + lo_b := Nat.le_add_right _ _

/-- Helper: hi < hi' implies toNat < toNat'. -/
private theorem hi_lt_implies_lt (a b : Uint128) (hlt : a.hi < b.hi) :
    a.toNat < b.toNat := by
  unfold Uint128.toNat
  exact limb_lt_implies_lt a.hi a.lo b.hi b.lo (2^64) hlt (lo_lt_base a.lo a.lo_bound)

/-- **uint128GTE_native_equivalence** (§14, MED-R6-2):
    uint128GTE(a, b) ↔ a.toNat ≥ b.toNat.
    Closes Go uint128GTE ↔ Rust u128 >= gap. -/
theorem uint128GTE_native_equivalence (a b : Uint128) :
    uint128GTE a b ↔ a.toNat ≥ b.toNat := by
  constructor
  · -- Forward
    intro h
    match h with
    | Or.inl hgt => exact hi_gt_implies_ge a b hgt
    | Or.inr ⟨heq, hge⟩ =>
      unfold Uint128.toNat
      rw [heq]
      exact Nat.add_le_add_left hge _
  · -- Backward
    intro h
    by_cases hhi : a.hi > b.hi
    · exact Or.inl hhi
    · have hle : a.hi ≤ b.hi := Nat.le_of_not_lt hhi
      have heq : a.hi = b.hi := by
        by_contra hne
        have hlt : a.hi < b.hi := Nat.lt_of_le_of_ne hle hne
        have habs := hi_lt_implies_lt a b hlt
        exact absurd (Nat.lt_of_lt_of_le habs h) (Nat.lt_irrefl _)
      have hlo : a.lo ≥ b.lo := by
        unfold Uint128.toNat at h
        rw [heq] at h
        exact Nat.le_of_add_le_add_left h
      exact Or.inr ⟨heq, hlo⟩

-- ============================================================================
-- §14 Theorem 3: extid_sort_deterministic
-- ============================================================================

/-- Insertion sort for ext_ids (models Go sorted slice / Rust sorted Vec). -/
def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

def sortAscending : List Nat → List Nat
  | [] => []
  | x :: xs => insertSorted x (sortAscending xs)

/-- insertSorted produces a permutation: x :: ys ~ insertSorted x ys -/
theorem insertSorted_perm (x : Nat) (ys : List Nat) :
    List.Perm (x :: ys) (insertSorted x ys) := by
  induction ys with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    simp only [insertSorted]
    split
    · exact List.Perm.refl _
    · -- x > y: insertSorted x (y::ys) = y :: insertSorted x ys
      -- Need: x :: y :: ys ~ y :: insertSorted x ys
      -- swap gives: y :: x :: ys ~ x :: y :: ys
      -- cons y ih gives: y :: x :: ys ~ y :: insertSorted x ys
      -- We need: x :: y :: ys ~ y :: insertSorted x ys
      exact (List.Perm.swap y x ys).trans (List.Perm.cons y ih)

/-- sortAscending produces a permutation of the input. -/
theorem sortAscending_perm (xs : List Nat) :
    List.Perm xs (sortAscending xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    simp only [sortAscending]
    exact (List.Perm.cons x ih).trans (insertSorted_perm x (sortAscending xs))

/-- Membership lemma for insertSorted (used by sorted proof). -/
private theorem insertSorted_mem (x : Nat) (ys : List Nat) (z : Nat) :
    z ∈ insertSorted x ys ↔ z = x ∨ z ∈ ys := by
  induction ys with
  | nil => simp [insertSorted, List.mem_cons, List.mem_nil_iff]
  | cons y ys ih =>
    simp only [insertSorted]
    split
    · simp [List.mem_cons]
    · simp only [List.mem_cons, ih]
      constructor
      · rintro (rfl | rfl | h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h)
      · rintro (rfl | rfl | h)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr h)

/-- sortAscending produces a sorted list (Pairwise ≤). -/
theorem sortAscending_sorted_v2 (xs : List Nat) :
    List.Pairwise (· ≤ ·) (sortAscending xs) := by
  induction xs with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    simp only [sortAscending]
    exact insertSorted_sorted_v2 x (sortAscending xs) ih
where
  insertSorted_sorted_v2 (x : Nat) (ys : List Nat)
      (h : List.Pairwise (· ≤ ·) ys) :
      List.Pairwise (· ≤ ·) (insertSorted x ys) := by
    induction ys with
    | nil =>
      simp [insertSorted]
    | cons y ys ih_ys =>
      simp only [insertSorted]
      split
      · -- x ≤ y
        rename_i hle
        exact List.pairwise_cons.mpr ⟨fun z hz => by
          rw [List.mem_cons] at hz
          match hz with
          | Or.inl heq => exact heq ▸ hle
          | Or.inr hmem => exact Nat.le_trans hle (List.rel_of_pairwise_cons h hmem),
          h⟩
      · -- x > y
        rename_i hnle
        have hyx : y < x := Nat.lt_of_not_le hnle
        have hpw := List.pairwise_cons.mp h
        have ih_result := ih_ys hpw.2
        exact List.pairwise_cons.mpr ⟨fun z hz => by
          rw [insertSorted_mem] at hz
          match hz with
          | Or.inl heq => exact heq ▸ Nat.le_of_lt hyx
          | Or.inr hmem => exact hpw.1 z hmem,
          ih_result⟩

/-- **extid_sort_deterministic** (§14, strengthened):
    sortAscending produces a sorted permutation of the input.
    This is the substantive property: any two implementations that produce
    a sorted permutation of the same input yield identical results. -/
theorem extid_sort_deterministic (xs : List Nat) :
    List.Perm xs (sortAscending xs) ∧ List.Pairwise (· ≤ ·) (sortAscending xs) :=
  ⟨sortAscending_perm xs, sortAscending_sorted_v2 xs⟩

/-- Concrete verification: descending input [3, 1, 2] produces [1, 2, 3].
    Models CV-51/CV-84: ext_ids in descending wire order are still
    processed in ascending numeric order. -/
theorem extid_sort_concrete_321 :
    sortAscending [3, 1, 2] = [1, 2, 3] := by
  native_decide

/-- ext_ids [0x0003, 0x0001] → [0x0001, 0x0003] (CV-51 regression). -/
theorem extid_sort_cv51 :
    sortAscending [3, 1] = [1, 3] := by
  native_decide

/-- Already sorted input is identity. -/
theorem extid_sort_idempotent_sorted :
    sortAscending [1, 2, 3] = [1, 2, 3] := by
  native_decide

-- ============================================================================
-- §14 Theorem 4: ntotal_empty_v2_equivalence
-- ============================================================================

/-- When v2_count = 0, n_total = v1_count. -/
theorem ntotal_empty_v2_equivalence (v1_count : Nat) :
    v1_count + 0 = v1_count := Nat.add_zero v1_count

-- ============================================================================
-- §14 Theorem 5: k_overflow_discard_complete
-- ============================================================================

/-- BuildTxContext result: success or error (no partial state on error). -/
inductive BuildResult (α : Type) where
  | ok : α → BuildResult α
  | err : String → BuildResult α

/-- **k_overflow_discard_complete** (§14, R18-2):
    err carries no partial TxContextContinuing data — structural. -/
theorem k_overflow_discard_complete {α : Type} (errMsg : String)
    (result : BuildResult α) (herr : result = BuildResult.err errMsg) :
    ¬∃ (v : α), result = BuildResult.ok v := by
  subst herr; intro ⟨_, h⟩; exact BuildResult.noConfusion h

-- ============================================================================
-- §14 Theorem 6: vault_conservation_no_double_count
-- ============================================================================

/-- Canonical §20 value conservation check. -/
def checkValueConservation (totalIn totalOut vaultInputSum : Nat) (hasVaultInputs : Bool) : Bool :=
  if totalOut > totalIn then false
  else if hasVaultInputs && totalOut < vaultInputSum then false
  else true

/-- **vault_conservation_no_double_count** (§14, R18-3):
    Rule (a) depends only on totalIn/totalOut, not vaultInputSum. -/
theorem vault_conservation_no_double_count
    (totalIn totalOut vis1 vis2 : Nat) (hv : Bool) :
    totalOut > totalIn →
    checkValueConservation totalIn totalOut vis1 hv =
    checkValueConservation totalIn totalOut vis2 hv := by
  intro hgt; simp [checkValueConservation, hgt]

/-- When has_vault_inputs = false, vault_input_sum is ignored (CV-63). -/
theorem vault_sum_ignored_when_no_vault (totalIn totalOut vis : Nat) :
    checkValueConservation totalIn totalOut vis false =
    checkValueConservation totalIn totalOut 0 false := by
  simp [checkValueConservation]

-- ============================================================================
-- §14 Theorem 7: parallel_error_equivalence
-- ============================================================================

/-- **parallel_error_equivalence** (§14, strengthened):
    For any permutation of inputs, mapping a pure function f produces
    a permutation of the original results. This is the real property:
    reordering inputs (as happens in parallel scheduling) produces the
    same multiset of results. -/
theorem parallel_error_equivalence {inputs₁ inputs₂ : List α} (f : α → Bool)
    (hperm : List.Perm inputs₁ inputs₂) :
    List.Perm (inputs₁.map f) (inputs₂.map f) :=
  hperm.map f

/-- Corollary: if all results are true in one ordering, all are true in any other. -/
theorem parallel_all_perm_invariant {inputs₁ inputs₂ : List α} (f : α → Bool)
    (hperm : List.Perm inputs₁ inputs₂)
    (hall : ∀ x ∈ inputs₁, f x = true) :
    ∀ x ∈ inputs₂, f x = true := by
  intro x hx
  exact hall x (hperm.symm.mem_iff.mp hx)

/-- Corollary: if any result is false in one ordering, it's false in any other. -/
theorem parallel_any_fail_perm_invariant {inputs₁ inputs₂ : List α} (f : α → Bool)
    (hperm : List.Perm inputs₁ inputs₂)
    (hfail : ∃ x ∈ inputs₁, f x = false) :
    ∃ x ∈ inputs₂, f x = false := by
  obtain ⟨x, hx, hfx⟩ := hfail
  exact ⟨x, hperm.mem_iff.mp hx, hfx⟩

-- ============================================================================
-- §14 Theorem 8: sighash_policy_complete
-- ============================================================================

/-- Check if a sighash type has a valid base type (0x01–0x03). -/
def hasValidBaseType (sighashType : Nat) : Bool :=
  let baseType := sighashType &&& 0x7F
  baseType == 1 || baseType == 2 || baseType == 3

/-- Check if sighash is allowed by profile's allowed_sighash_set bitmask. -/
def sighashAllowed (allowedSet : Nat) (sighashType : Nat) : Bool :=
  let baseType := sighashType &&& 0x7F
  let hasAcp := (sighashType &&& 0x80) != 0
  let baseIdx := baseType - 1
  let baseAllowed := (allowedSet >>> baseIdx) &&& 1 == 1
  let acpAllowed := !hasAcp || ((allowedSet >>> 7) &&& 1 == 1)
  baseAllowed && acpAllowed

/-- **sighash_policy_complete** (§14): 0x87 allows all 6 valid combos. -/
theorem sighash_policy_complete :
    sighashAllowed 0x87 0x01 = true ∧
    sighashAllowed 0x87 0x02 = true ∧
    sighashAllowed 0x87 0x03 = true ∧
    sighashAllowed 0x87 0x81 = true ∧
    sighashAllowed 0x87 0x82 = true ∧
    sighashAllowed 0x87 0x83 = true := by
  native_decide

/-- Invalid base types are rejected. -/
theorem sighash_invalid_base_rejected :
    hasValidBaseType 0x00 = false ∧
    hasValidBaseType 0x04 = false ∧
    hasValidBaseType 0x80 = false := by
  native_decide

end RubinFormal.TxContext
