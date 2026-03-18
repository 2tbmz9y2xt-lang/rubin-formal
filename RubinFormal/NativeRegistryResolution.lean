/-
  RubinFormal/NativeRegistryResolution.lean — FI-ROT-03

  Q-FORMAL-ROTATION-02: native registry resolution is deterministic.

  For any suite_id ∈ ActiveNativeSuites(h), registry lookup returns
  exactly one entry with unique PUBKEY_BYTES / SIG_BYTES / VERIFY_COST.

  Formally:
    suite_id ∈ ActiveNativeSuites(h) → ∃! entry, registryLookup(suite_id) = entry

  This closes the descriptor-driven approach and eliminates the need
  for hardcoded suite constants (0x01, 0x02, …).

  Spec: CANONICAL §4.1.1 (suite registry), §4.1.3 (descriptor validity).
  Depends: Q-FORMAL-ROTATION-01 (NativeSuiteRotation.lean).
  Closes #122.
-/

import RubinFormal.RotationPrelude
import RubinFormal.NativeSuiteRotation

namespace RubinFormal

namespace NativeRegistryResolution

open Rotation
open NativeSuiteRotation

/-! ### Registry well-formedness -/

/-- A registry is well-formed if no two entries share the same suiteId. -/
def registryNoDuplicates (reg : SuiteRegistry) : Prop :=
  ∀ (i j : Nat) (hi : i < reg.length) (hj : j < reg.length),
    (reg.get ⟨i, hi⟩).suiteId = (reg.get ⟨j, hj⟩).suiteId → i = j

/-- A suite_id is registered if `registryLookup` returns `some`. -/
def isRegistered (reg : SuiteRegistry) (sid : Nat) : Prop :=
  ∃ entry, registryLookup reg sid = some entry

/-- A rotation descriptor is registry-consistent: both old and new suite
    are present in the registry. -/
def descriptorRegistryConsistent
    (d : RotationDeploymentDescriptor) (reg : SuiteRegistry) : Prop :=
  isRegistered reg d.oldSuiteId ∧ isRegistered reg d.newSuiteId

/-! ### FI-ROT-03: registry resolution deterministic -/

/-- The result of `registryLookup` is deterministic by construction:
    `List.find?` always returns the same element for the same input. -/
theorem fi_rot_03_registry_lookup_deterministic
    (reg : SuiteRegistry) (sid : Nat) :
    ∀ (e1 e2 : SuiteEntry),
      registryLookup reg sid = some e1 →
      registryLookup reg sid = some e2 →
      e1 = e2 := by
  intro e1 e2 h1 h2
  rw [h1] at h2
  injection h2

/-- For a well-formed registry (no duplicates), if a suite is registered,
    lookup returns an entry whose fields are uniquely determined. -/
theorem fi_rot_03_unique_entry
    (reg : SuiteRegistry) (sid : Nat)
    (_hnd : registryNoDuplicates reg)
    (hreg : isRegistered reg sid) :
    ∃ entry, registryLookup reg sid = some entry ∧ ∀ e2, registryLookup reg sid = some e2 → e2 = entry := by
  obtain ⟨entry, hentry⟩ := hreg
  exact ⟨entry, hentry, fun e2 h2 => by rw [hentry] at h2; exact (Option.some.inj h2).symm⟩

/-- The looked-up entry's parameters (pubkeyBytes, sigBytes, verifyCost)
    are uniquely determined by the suite_id and registry. -/
theorem fi_rot_03_params_unique
    (reg : SuiteRegistry) (sid : Nat) (entry : SuiteEntry)
    (hfind : registryLookup reg sid = some entry) :
    ∀ e2, registryLookup reg sid = some e2 →
      e2.pubkeyBytes = entry.pubkeyBytes ∧
      e2.sigBytes = entry.sigBytes ∧
      e2.verifyCost = entry.verifyCost := by
  intro e2 h2
  have : e2 = entry := fi_rot_03_registry_lookup_deterministic reg sid e2 entry h2 hfind
  subst this
  exact ⟨rfl, rfl, rfl⟩

/-! ### Connection to active suites and descriptors -/

/-- NativeCreateSuites only contains oldSuiteId and/or newSuiteId. -/
theorem create_suites_subset
    (d : RotationDeploymentDescriptor) (h : Nat) (sid : Nat)
    (hmem : sid ∈ NativeCreateSuites h d) :
    sid = d.oldSuiteId ∨ sid = d.newSuiteId := by
  unfold NativeCreateSuites at hmem
  split at hmem
  · simp [List.mem_singleton] at hmem; exact Or.inl hmem
  · split at hmem
    · simp [List.mem_cons, List.mem_singleton] at hmem
      rcases hmem with h1 | h2 <;> [exact Or.inl h1; exact Or.inr h2]
    · simp [List.mem_singleton] at hmem; exact Or.inr hmem

/-- NativeSpendSuites only contains oldSuiteId and/or newSuiteId. -/
theorem spend_suites_subset
    (d : RotationDeploymentDescriptor) (h : Nat) (sid : Nat)
    (hmem : sid ∈ NativeSpendSuites h d) :
    sid = d.oldSuiteId ∨ sid = d.newSuiteId := by
  unfold NativeSpendSuites at hmem
  split at hmem
  · simp [List.mem_singleton] at hmem; exact Or.inl hmem
  · cases hh4 : d.h4 with
    | none =>
      simp [hh4] at hmem
      rcases hmem with h1 | h2 <;> [exact Or.inl h1; exact Or.inr h2]
    | some h4val =>
      simp [hh4] at hmem
      split at hmem
      · simp [List.mem_singleton] at hmem; exact Or.inr hmem
      · simp [List.mem_cons, List.mem_singleton] at hmem
        rcases hmem with h1 | h2 <;> [exact Or.inl h1; exact Or.inr h2]

/-- A well-formed descriptor's active suites are all registered.
    PROVED: NativeCreateSuites/NativeSpendSuites only return
    d.oldSuiteId or d.newSuiteId, both registered by hypothesis. -/
theorem descriptor_suites_registered
    (d : RotationDeploymentDescriptor) (reg : SuiteRegistry) (h : Nat)
    (hcons : descriptorRegistryConsistent d reg)
    (_hwf : wellFormedDescriptor d) :
    (∀ sid ∈ NativeCreateSuites h d, isRegistered reg sid) ∧
    (∀ sid ∈ NativeSpendSuites h d, isRegistered reg sid) := by
  obtain ⟨hold, hnew⟩ := hcons
  constructor
  · intro sid hmem
    rcases create_suites_subset d h sid hmem with rfl | rfl
    · exact hold
    · exact hnew
  · intro sid hmem
    rcases spend_suites_subset d h sid hmem with rfl | rfl
    · exact hold
    · exact hnew

/-- Main theorem: for any active native spend suite at height h, registry
    resolution returns exactly one entry with determined parameters.

    This is the formal guarantee that the consensus code can replace
    hardcoded constants with registry lookups without ambiguity. -/
theorem fi_rot_03_active_suite_resolves
    (d : RotationDeploymentDescriptor) (reg : SuiteRegistry) (h : Nat) (sid : Nat)
    (hnd : registryNoDuplicates reg)
    (hcons : descriptorRegistryConsistent d reg)
    (hwf : wellFormedDescriptor d)
    (hactive : sid ∈ NativeSpendSuites h d) :
    ∃ entry, registryLookup reg sid = some entry ∧ ∀ e2, registryLookup reg sid = some e2 → e2 = entry := by
  have ⟨_, hspend⟩ := descriptor_suites_registered d reg h hcons hwf
  exact fi_rot_03_unique_entry reg sid hnd (hspend sid hactive)

/-- Same for create suites. -/
theorem fi_rot_03_active_create_suite_resolves
    (d : RotationDeploymentDescriptor) (reg : SuiteRegistry) (h : Nat) (sid : Nat)
    (hnd : registryNoDuplicates reg)
    (hcons : descriptorRegistryConsistent d reg)
    (hwf : wellFormedDescriptor d)
    (hactive : sid ∈ NativeCreateSuites h d) :
    ∃ entry, registryLookup reg sid = some entry ∧ ∀ e2, registryLookup reg sid = some e2 → e2 = entry := by
  have ⟨hcreate, _⟩ := descriptor_suites_registered d reg h hcons hwf
  exact fi_rot_03_unique_entry reg sid hnd (hcreate sid hactive)

/-! ### Pre-rotation specialisation -/

/-- In the pre-rotation registry, ML-DSA-87 resolves correctly. -/
theorem fi_rot_03_pre_rotation_ml_dsa_resolves :
    registryLookup PRE_ROTATION_REGISTRY 0x01 = some ML_DSA_87_ENTRY := by
  native_decide

/-- The pre-rotation registry has no duplicate suite IDs. -/
theorem fi_rot_03_pre_rotation_no_duplicates :
    registryNoDuplicates PRE_ROTATION_REGISTRY := by
  intro i j hi hj _
  simp [PRE_ROTATION_REGISTRY] at hi hj
  omega

end NativeRegistryResolution

end RubinFormal
