/-
  RubinFormal/RotationPrelude.lean — Suite-Registry Model & Pre-Rotation Audit Inventory

  Q-FORMAL-ROTATION-00: prerequisite for Q-FORMAL-ROTATION-01..05.

  ## Purpose

  This file introduces the abstract suite-registry model that rotation
  proofs (FI-ROT-01 … FI-ROT-07) will use, and documents which existing
  definitions / theorems carry hardcoded SUITE_ID_ML_DSA_87 assumptions.

  ## Pre-Rotation Scoping Convention

  Every definition or theorem that assumes a single-suite world (only
  SENTINEL + ML_DSA_87) is tagged with:

    /-- **Pre-rotation scope**: assumes single native suite ML-DSA-87.
        Must be generalised or re-proved under suite-registry model
        for Q-FORMAL-ROTATION-0N. -/

  ## Suite-Registry Model (abstract)

  After rotation activation, the consensus rule is:
    ∀ h, NATIVE_CREATE_SUITES(h) ⊆ NATIVE_SPEND_SUITES(h) ⊆ Registry
  where Registry maps suite_id → (PUBKEY_BYTES, SIG_BYTES, VERIFY_COST, verifier).

  The single-suite era is the special case where:
    Registry = { 0x01 ↦ (2592, 4627, 8, ml_dsa_87_verify) }
    NATIVE_CREATE_SUITES(h) = NATIVE_SPEND_SUITES(h) = {0x01}  ∀ h
-/

import RubinFormal.Types

namespace RubinFormal

namespace Rotation

/-! ### Abstract suite-registry types -/

/-- A single entry in the native suite registry. -/
structure SuiteEntry where
  suiteId      : Nat
  pubkeyBytes  : Nat
  sigBytes     : Nat
  verifyCost   : Nat
  deriving Repr, DecidableEq

/-- The suite registry: a list of registered native suites.
    In the single-suite era this contains exactly one entry (ML-DSA-87). -/
def SuiteRegistry := List SuiteEntry

/-- Height-dependent active suite sets (post-rotation model). -/
structure RotationDescriptor where
  oldSuite : Nat
  newSuite : Nat
  h1       : Nat   -- NATIVE_CREATE_SUITES cutoff
  h2       : Nat   -- NATIVE_CREATE_SUITES + SPEND transition
  h4       : Option Nat  -- old-suite sunset (None = never)
  deriving Repr, DecidableEq

/-- Lookup a suite entry by ID in the registry. -/
def registryLookup (reg : SuiteRegistry) (sid : Nat) : Option SuiteEntry :=
  reg.find? (fun e => e.suiteId == sid)

/-- A suite_id is registered if `registryLookup` returns `some`. -/
def isRegistered (reg : SuiteRegistry) (sid : Nat) : Prop :=
  ∃ entry, registryLookup reg sid = some entry

/-! ### Single-suite (pre-rotation) era constants -/

/-- The ML-DSA-87 registry entry, used throughout the pre-rotation codebase. -/
def ML_DSA_87_ENTRY : SuiteEntry :=
  { suiteId := 0x01, pubkeyBytes := 2592, sigBytes := 4627, verifyCost := 8 }

/-- Pre-rotation registry: only ML-DSA-87 registered. -/
def PRE_ROTATION_REGISTRY : SuiteRegistry := [ML_DSA_87_ENTRY]

/-- Pre-rotation: NATIVE_CREATE_SUITES(h) = NATIVE_SPEND_SUITES(h) = {0x01} for all h. -/
def preRotationActiveSuites (_h : Nat) : List Nat := [0x01]

/-! ### Inventory of hardcoded assumptions (from Q-FORMAL-ROTATION-00 audit)

  #### TxParseV2.lean
  - `parseWitnessItem`: branches on `suiteID == SUITE_ID_ML_DSA_87`
    with hardcoded `ML_DSA_87_PUBKEY_BYTES` / `ML_DSA_87_SIG_BYTES`.
    **Action for ROT-03**: generalise to registry lookup for pubkey/sig bounds.

  #### TxWeightV2.lean
  - `parseWitnessItemForCounts`: same two-branch suite dispatch.
  - `WitnessSectionResult.mlCount`: named for ML-DSA-87;
    post-rotation becomes per-suite count or generic `knownSuiteCount`.
  - `txWeightAndStats`: `mlCount * VERIFY_COST_ML_DSA_87` —
    must become `Σ (suite, count) → count * registry[suite].verifyCost`.
    **Action for ROT-03**: prove `weight_suite_aware_correct`.

  #### CovenantGenesisV1.lean
  - `validateOutGenesis`: `suiteId != SUITE_ID_ML_DSA_87 → reject`.
    **Action for ROT-04**: generalise to `suiteId ∉ NATIVE_CREATE_SUITES(h) → reject`.

  #### UtxoApplyGenesisV1.lean
  - `validateP2PKSpendPreSig`: `suite != SUITE_ID_ML_DSA_87 → reject`.
    **Action for ROT-04**: generalise to `suite ∉ NATIVE_SPEND_SUITES(h) → reject`.
  - `validateWitnessItemLengths`: ML-DSA-87 branch with hardcoded bounds.
    **Action for ROT-02/ROT-03**: lookup bounds from registry.
  - `validateThresholdSigSpendNoCrypto`: ML-DSA-87 branch.
    **Action for ROT-04**: same generalisation.
  - `sampleOwnerP2PKData`: `SUITE_ID_ML_DSA_87` byte prefix in sample data.
    **Action**: update samples if registry model changes output format.

  #### UtxoBasicV1.lean
  - `scanSingleInputStep`: `suite != SUITE_ID_ML_DSA_87 → reject` in P2PK path.
    **Action for ROT-04**: generalise to `suite ∉ NATIVE_SPEND_SUITES(h)`.

  #### FormalGap03.lean
  - `sem001MLDSABoundedLengthStatement`: hypothesis `w.suiteId = SUITE_ID_ML_DSA_87`.
    **Already scoped** — valid pre-rotation; post-rotation needs per-suite variant.
  - `validateP2PKSpendPreSig_binds_pubkey`: conclusion includes `w.suiteId = SUITE_ID_ML_DSA_87`.
    **Already scoped** — follows from `validateP2PKSpendPreSig` accepting only ML-DSA-87.
  - `sem002_mldsa_binding_proved`: composition of above two.
    **Already scoped** — inherits scope from premises.
-/

end Rotation

end RubinFormal
