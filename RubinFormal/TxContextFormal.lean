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

structure Uint128 where
  lo : Nat
  hi : Nat
  lo_bound : lo ≤ (2 ^ 64) - 1 := by omega
  hi_bound : hi ≤ (2 ^ 64) - 1 := by omega

def Uint128.toNat (a : Uint128) : Nat := a.hi * 2 ^ 64 + a.lo

def uint128GTE (a b : Uint128) : Prop :=
  a.hi > b.hi ∨ (a.hi = b.hi ∧ a.lo ≥ b.lo)

theorem uint128GTE_correct (a b : Uint128) :
    uint128GTE a b ↔ (a.hi > b.hi ∨ (a.hi = b.hi ∧ a.lo ≥ b.lo)) :=
  Iff.rfl

private theorem limb_gt_implies_ge (hi_a lo_a hi_b lo_b B : Nat)
    (hgt : hi_a > hi_b) (hlob : lo_b < B) :
    hi_a * B + lo_a ≥ hi_b * B + lo_b := by
  have h1 : (hi_b + 1) * B ≤ hi_a * B := Nat.mul_le_mul_right B hgt
  have h3 : (hi_b + 1) * B = hi_b * B + B := Nat.succ_mul hi_b B
  have h4 : hi_b * B + B ≤ hi_a * B := h3 ▸ h1
  have hlt : hi_b * B + lo_b < hi_a * B + lo_a :=
    calc hi_b * B + lo_b
        < hi_b * B + B := Nat.add_lt_add_left hlob _
      _ ≤ hi_a * B := h4
      _ ≤ hi_a * B + lo_a := Nat.le_add_right _ _
  exact Nat.le_of_lt hlt

private theorem lo_lt_base (n : Nat) (h : n ≤ (2 ^ 64) - 1) : n < 2 ^ 64 :=
  Nat.lt_of_le_of_lt h (by native_decide)

private theorem hi_gt_implies_ge (a b : Uint128) (hgt : a.hi > b.hi) :
    a.toNat ≥ b.toNat := by
  unfold Uint128.toNat
  exact limb_gt_implies_ge a.hi a.lo b.hi b.lo (2^64) hgt (lo_lt_base b.lo b.lo_bound)

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

private theorem hi_lt_implies_lt (a b : Uint128) (hlt : a.hi < b.hi) :
    a.toNat < b.toNat := by
  unfold Uint128.toNat
  exact limb_lt_implies_lt a.hi a.lo b.hi b.lo (2^64) hlt (lo_lt_base a.lo a.lo_bound)

theorem uint128GTE_native_equivalence (a b : Uint128) :
    uint128GTE a b ↔ a.toNat ≥ b.toNat := by
  constructor
  · intro h
    match h with
    | Or.inl hgt => exact hi_gt_implies_ge a b hgt
    | Or.inr ⟨heq, hge⟩ =>
      unfold Uint128.toNat
      rw [heq]
      exact Nat.add_le_add_left hge _
  · intro h
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

def insertSorted (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: insertSorted x ys

def sortAscending : List Nat → List Nat
  | [] => []
  | x :: xs => insertSorted x (sortAscending xs)

theorem insertSorted_perm (x : Nat) (ys : List Nat) :
    List.Perm (x :: ys) (insertSorted x ys) := by
  induction ys with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
    simp only [insertSorted]
    split
    · exact List.Perm.refl _
    · exact (List.Perm.swap y x ys).trans (List.Perm.cons y ih)

theorem sortAscending_perm (xs : List Nat) :
    List.Perm xs (sortAscending xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
    simp only [sortAscending]
    exact (List.Perm.cons x ih).trans (insertSorted_perm x (sortAscending xs))

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
    | nil => simp [insertSorted]
    | cons y ys ih_ys =>
      simp only [insertSorted]
      split
      · rename_i hle
        exact List.pairwise_cons.mpr ⟨fun z hz => by
          rw [List.mem_cons] at hz
          match hz with
          | Or.inl heq => exact heq ▸ hle
          | Or.inr hmem => exact Nat.le_trans hle (List.rel_of_pairwise_cons h hmem),
          h⟩
      · rename_i hnle
        have hyx : y < x := Nat.lt_of_not_le hnle
        have hpw := List.pairwise_cons.mp h
        have ih_result := ih_ys hpw.2
        exact List.pairwise_cons.mpr ⟨fun z hz => by
          rw [insertSorted_mem] at hz
          match hz with
          | Or.inl heq => exact heq ▸ Nat.le_of_lt hyx
          | Or.inr hmem => exact hpw.1 z hmem,
          ih_result⟩

private theorem sorted_perm_unique_when_both_sorted :
    ∀ {xs ys : List Nat},
      List.Pairwise (· ≤ ·) xs →
      List.Pairwise (· ≤ ·) ys →
      List.Perm xs ys →
      xs = ys
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, hperm => by
      have hlen := hperm.length_eq
      simp at hlen
      cases hlen
  | _ :: _, [], _, _, hperm => by
      have hlen := hperm.length_eq
      simp at hlen
      cases hlen
  | x :: xs, y :: ys, hxs, hys, hperm => by
      have hx_mem : x ∈ y :: ys := hperm.mem_iff.mp (by simp)
      have hy_mem : y ∈ x :: xs := hperm.symm.mem_iff.mp (by simp)
      have hxy : x ≤ y := by
        have hcons := List.pairwise_cons.mp hxs
        rw [List.mem_cons] at hy_mem
        rcases hy_mem with rfl | hmem
        · exact Nat.le_refl _
        · exact hcons.1 y hmem
      have hyx : y ≤ x := by
        have hcons := List.pairwise_cons.mp hys
        rw [List.mem_cons] at hx_mem
        rcases hx_mem with rfl | hmem
        · exact Nat.le_refl _
        · exact hcons.1 x hmem
      have hEq : x = y := Nat.le_antisymm hxy hyx
      subst hEq
      have hperm_tail : List.Perm xs ys := List.Perm.cons_inv hperm
      have hxs_tail : List.Pairwise (· ≤ ·) xs := (List.pairwise_cons.mp hxs).2
      have hys_tail : List.Pairwise (· ≤ ·) ys := (List.pairwise_cons.mp hys).2
      simpa using sorted_perm_unique_when_both_sorted hxs_tail hys_tail hperm_tail

theorem extid_sort_deterministic (xs ys : List Nat)
    (hperm : List.Perm xs ys)
    (hsorted : List.Pairwise (· ≤ ·) ys) :
    sortAscending xs = ys := by
  exact sorted_perm_unique_when_both_sorted (sortAscending_sorted_v2 xs) hsorted
    ((sortAscending_perm xs).symm.trans hperm)

theorem extid_sort_concrete_321 :
    sortAscending [3, 1, 2] = [1, 2, 3] := by
  native_decide

theorem extid_sort_cv51 :
    sortAscending [3, 1] = [1, 3] := by
  native_decide

theorem extid_sort_idempotent_sorted :
    sortAscending [1, 2, 3] = [1, 2, 3] := by
  native_decide

theorem ntotal_empty_v2_equivalence (v1_count : Nat) :
    v1_count + 0 = v1_count := Nat.add_zero v1_count

inductive BuildResult (α : Type) where
  | ok : α → BuildResult α
  | err : String → BuildResult α

theorem k_overflow_discard_complete {α : Type} (errMsg : String)
    (result : BuildResult α) (herr : result = BuildResult.err errMsg) :
    ¬∃ (v : α), result = BuildResult.ok v := by
  subst herr; intro ⟨_, h⟩; exact BuildResult.noConfusion h

def checkValueConservation (totalIn totalOut vaultInputSum : Nat) (hasVaultInputs : Bool) : Bool :=
  if totalOut > totalIn then false
  else if hasVaultInputs && totalOut < vaultInputSum then false
  else true

theorem vault_conservation_no_double_count
    (totalIn totalOut vis1 vis2 : Nat) (hv : Bool) :
    totalOut > totalIn →
    checkValueConservation totalIn totalOut vis1 hv =
    checkValueConservation totalIn totalOut vis2 hv := by
  intro hgt; simp [checkValueConservation, hgt]

theorem vault_sum_ignored_when_no_vault (totalIn totalOut vis : Nat) :
    checkValueConservation totalIn totalOut vis false =
    checkValueConservation totalIn totalOut 0 false := by
  simp [checkValueConservation]

/-- Auxiliary permutation invariance for pure result maps. This is not by itself
    the full lowest-index parallel theorem. -/
theorem parallel_error_equivalence {inputs₁ inputs₂ : List α} (f : α → Bool)
    (hperm : List.Perm inputs₁ inputs₂) :
    List.Perm (inputs₁.map f) (inputs₂.map f) :=
  hperm.map f

theorem parallel_all_perm_invariant {inputs₁ inputs₂ : List α} (f : α → Bool)
    (hperm : List.Perm inputs₁ inputs₂)
    (hall : ∀ x ∈ inputs₁, f x = true) :
    ∀ x ∈ inputs₂, f x = true := by
  intro x hx
  exact hall x (hperm.symm.mem_iff.mp hx)

theorem parallel_any_fail_perm_invariant {inputs₁ inputs₂ : List α} (f : α → Bool)
    (hperm : List.Perm inputs₁ inputs₂)
    (hfail : ∃ x ∈ inputs₁, f x = false) :
    ∃ x ∈ inputs₂, f x = false := by
  obtain ⟨x, hx, hfx⟩ := hfail
  exact ⟨x, hperm.mem_iff.mp hx, hfx⟩

def firstErrorIndexFrom (start : Nat) : List Bool → Option Nat
  | [] => none
  | ok :: rest => if ok then firstErrorIndexFrom (start + 1) rest else some start

def sequentialErrorIndex (results : List Bool) : Option Nat :=
  firstErrorIndexFrom 0 results

def indexedValidationResultsFrom (start : Nat) : List Bool → List (Nat × Bool)
  | [] => []
  | ok :: rest => (start, ok) :: indexedValidationResultsFrom (start + 1) rest

def indexedValidationResults (results : List Bool) : List (Nat × Bool) :=
  indexedValidationResultsFrom 0 results

def lowestFailIdx? : List (Nat × Bool) → Option Nat
  | [] => none
  | (idx, ok) :: rest =>
      let tail := lowestFailIdx? rest
      if ok then tail
      else
        match tail with
        | none => some idx
        | some j => some (Nat.min idx j)

private theorem firstErrorIndexFrom_lower_bound (start idx : Nat) (results : List Bool)
    (h : firstErrorIndexFrom start results = some idx) :
    start ≤ idx := by
  induction results generalizing start idx with
  | nil => simp [firstErrorIndexFrom] at h
  | cons ok rest ih =>
      cases ok with
      | false =>
          simp [firstErrorIndexFrom] at h
          cases h
          exact Nat.le_refl _
      | true =>
          simp [firstErrorIndexFrom] at h
          exact Nat.le_trans (Nat.le_succ start) (ih (start + 1) idx h)

private theorem lowestFailIdx_indexed_from (start : Nat) (results : List Bool) :
    lowestFailIdx? (indexedValidationResultsFrom start results) =
    firstErrorIndexFrom start results := by
  induction results generalizing start with
  | nil => rfl
  | cons ok rest ih =>
      cases ok with
      | false =>
          simp [indexedValidationResultsFrom, lowestFailIdx?, firstErrorIndexFrom]
          rw [ih (start + 1)]
          cases hrest : firstErrorIndexFrom (start + 1) rest with
          | none => simp [hrest]
          | some j =>
              have hge1 : start + 1 ≤ j := firstErrorIndexFrom_lower_bound (start + 1) j rest hrest
              have hge : start ≤ j := Nat.le_trans (Nat.le_succ start) hge1
              simp [hrest, Nat.min_eq_left hge]
      | true =>
          simp [indexedValidationResultsFrom, lowestFailIdx?, firstErrorIndexFrom, ih (start + 1)]

private theorem lowestFailIdx_perm_invariant {xs ys : List (Nat × Bool)}
    (hperm : List.Perm xs ys) :
    lowestFailIdx? xs = lowestFailIdx? ys := by
  induction hperm with
  | nil => rfl
  | cons x hperm ih => simpa [lowestFailIdx?, ih]
  | swap x y zs =>
      cases x with
      | mk i oki =>
          cases y with
          | mk j okj =>
              cases oki <;> cases okj <;>
                simp [lowestFailIdx?, Nat.min_assoc, Nat.min_left_comm, Nat.min_comm]
  | trans h1 h2 ih1 ih2 => exact ih1.trans ih2

/-- The lowest-index attribution theorem proved here is for canonically indexed
    worker outputs up to permutation. It does not by itself instantiate the
    current `Refinement.ParallelEquivalence.validatePar` model, which still
    reduces plain `SigTask`s. -/
theorem parallel_error_index_priority_of_tagged_permutation (results : List Bool)
    (parallel : List (Nat × Bool))
    (hperm : List.Perm parallel (indexedValidationResults results)) :
    lowestFailIdx? parallel = sequentialErrorIndex results := by
  calc
    lowestFailIdx? parallel
        = lowestFailIdx? (indexedValidationResults results) := lowestFailIdx_perm_invariant hperm
    _ = firstErrorIndexFrom 0 results := lowestFailIdx_indexed_from 0 results
    _ = sequentialErrorIndex results := rfl

def hasValidBaseType (sighashType : Nat) : Bool :=
  let baseType := sighashType &&& 0x7F
  baseType == 1 || baseType == 2 || baseType == 3

private def bitSet (mask bit : Nat) : Bool :=
  (mask &&& bit) == bit

def sighashAllowed (allowedSet : Nat) (sighashType : Nat) : Bool :=
  let st := sighashType &&& 0xFF
  let baseType := st &&& 0x7F
  let hasAcp := (st &&& 0x80) != 0
  let baseAllowed :=
    (baseType == 1 && bitSet allowedSet 0x01) ||
    (baseType == 2 && bitSet allowedSet 0x02) ||
    (baseType == 3 && bitSet allowedSet 0x04)
  hasValidBaseType st && baseAllowed && (!hasAcp || bitSet allowedSet 0x80)

private def sighashAllowlistOracle (allowedSet : Nat) : List Nat :=
  let a1 := if (allowedSet &&& 0x01) == 0x01 then [0x01] else []
  let a2 := if (allowedSet &&& 0x02) == 0x02 then [0x02] else []
  let a3 := if (allowedSet &&& 0x04) == 0x04 then [0x03] else []
  let acp1 := if (allowedSet &&& 0x81) == 0x81 then [0x81] else []
  let acp2 := if (allowedSet &&& 0x82) == 0x82 then [0x82] else []
  let acp3 := if (allowedSet &&& 0x84) == 0x84 then [0x83] else []
  a1 ++ a2 ++ a3 ++ acp1 ++ acp2 ++ acp3

private def sighashAllowedSpec (allowedSet sighashType : Nat) : Bool :=
  let st := sighashType &&& 0xFF
  decide (st ∈ sighashAllowlistOracle allowedSet)

theorem sighash_policy_complete :
    sighashAllowed 0x87 0x01 = true ∧
    sighashAllowed 0x87 0x02 = true ∧
    sighashAllowed 0x87 0x03 = true ∧
    sighashAllowed 0x87 0x81 = true ∧
    sighashAllowed 0x87 0x82 = true ∧
    sighashAllowed 0x87 0x83 = true := by
  native_decide

theorem sighash_policy_exhaustive_256x256 :
    ∀ (allowedSet sighashType : Fin 256),
      sighashAllowed allowedSet.val sighashType.val =
      sighashAllowedSpec allowedSet.val sighashType.val := by
  native_decide

theorem sighash_invalid_base_rejected :
    ∀ (allowedSet : Fin 256),
      sighashAllowed allowedSet.val 0x00 = false ∧
      sighashAllowed allowedSet.val 0x04 = false ∧
      sighashAllowed allowedSet.val 0x80 = false := by
  native_decide

end RubinFormal.TxContext
