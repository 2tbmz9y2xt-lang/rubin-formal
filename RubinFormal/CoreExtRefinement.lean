/-
  CoreExtRefinement.lean — Formal refinement for CORE_EXT deterministic branches.

  Q-FORMAL-CORE-EXT-01: Proves properties about CORE_EXT activation
  transitions, deterministic error-priority mapping, and duplicate
  ACTIVE profile rejection. Maps back to CV-EXT-* fixture families.
-/
import RubinFormal.CoreExtInvariants
import RubinFormal.CriticalInvariants

namespace RubinFormal.CoreExtRefinement

open RubinFormal

-- ============================================================================
-- Section 1: Activation State Machine
-- ============================================================================

/-- CORE_EXT profile activation state at a given height. -/
inductive ActivationState
  | PreActive    -- height < activation_height: permissive path
  | Active       -- height >= activation_height: enforcement path
deriving DecidableEq

/-- Determine activation state from height and activation_height. -/
def activationStateAt (height activationHeight : Nat) : ActivationState :=
  if height < activationHeight then ActivationState.PreActive
  else ActivationState.Active

/-- At activation height, state is Active. -/
theorem active_at_activation (activationHeight : Nat) :
    activationStateAt activationHeight activationHeight = ActivationState.Active := by
  simp only [activationStateAt]
  split
  · rename_i h; omega
  · rfl

/-- Before activation height (h > 0), state is PreActive. -/
theorem pre_active_before (activationHeight : Nat) (hPos : 0 < activationHeight) :
    activationStateAt (activationHeight - 1) activationHeight = ActivationState.PreActive := by
  simp only [activationStateAt]
  split
  · rfl
  · rename_i h; omega

/-- Activation is monotone: once Active, stays Active. -/
theorem activation_monotone (h1 h2 activationHeight : Nat)
    (hLe : h1 ≤ h2)
    (hActive : activationStateAt h1 activationHeight = ActivationState.Active) :
    activationStateAt h2 activationHeight = ActivationState.Active := by
  simp only [activationStateAt] at *
  split at hActive
  · contradiction
  · split
    · rename_i h2lt h1ge; omega
    · rfl

/-- Genesis-active profile (activation_height = 0) is Active at height 0. -/
theorem genesis_active_at_zero :
    activationStateAt 0 0 = ActivationState.Active := by
  simp [activationStateAt]

-- ============================================================================
-- Section 2: Deterministic Error Priority
-- ============================================================================

/-- CORE_EXT error codes in priority order. -/
inductive ExtError
  | ParseError       -- TX_ERR_COVENANT_TYPE_INVALID (envelope malformed)
  | SuiteDisallowed  -- TX_ERR_SIG_ALG_INVALID (suite not in allowed set)
  | SigInvalid       -- TX_ERR_SIG_INVALID (signature verification failed)
deriving DecidableEq

/-- Error priority: ParseError > SuiteDisallowed > SigInvalid.
    Parse errors are detected before suite checks, which are
    detected before signature verification. -/
def errorPriority : ExtError → Nat
  | ExtError.ParseError => 0
  | ExtError.SuiteDisallowed => 1
  | ExtError.SigInvalid => 2

/-- Parse errors always have higher priority than suite errors. -/
theorem parse_before_suite :
    errorPriority ExtError.ParseError < errorPriority ExtError.SuiteDisallowed := by
  native_decide

/-- Suite errors always have higher priority than sig errors. -/
theorem suite_before_sig :
    errorPriority ExtError.SuiteDisallowed < errorPriority ExtError.SigInvalid := by
  native_decide

/-- Given two errors, the deterministic winner is the one with lower priority number. -/
def deterministicError (e1 e2 : ExtError) : ExtError :=
  if errorPriority e1 ≤ errorPriority e2 then e1 else e2

/-- Deterministic error selection is commutative. -/
theorem error_selection_commutative (e1 e2 : ExtError) :
    deterministicError e1 e2 = deterministicError e2 e1 := by
  cases e1 <;> cases e2 <;> simp [deterministicError, errorPriority]

/-- If a parse error is present, it always wins. -/
theorem parse_always_wins (e : ExtError) :
    deterministicError ExtError.ParseError e = ExtError.ParseError := by
  cases e <;> simp [deterministicError, errorPriority]

-- ============================================================================
-- Section 3: Duplicate ACTIVE Profile Rejection
-- ============================================================================

/-- A deployment profile record. -/
structure DeploymentProfile where
  extId : Nat
  activationHeight : Nat

/-- Generic duplicate detection by a projected natural-number key. -/
def hasDuplicateNatKey {α : Type} (key : α → Nat) : List α → Bool
  | [] => false
  | x :: rest =>
    if rest.any (fun y => key y == key x) then true
    else hasDuplicateNatKey key rest

/-- Check for duplicate ext_ids in a list of profiles. -/
def hasDuplicateExtId : List DeploymentProfile → Bool :=
  hasDuplicateNatKey (fun p => p.extId)

/-- Empty profile list has no duplicates (definitional). -/
theorem no_duplicates_empty : hasDuplicateExtId [] = false := rfl

/-- A single profile has no duplicates (definitional). -/
theorem no_duplicates_singleton (p : DeploymentProfile) :
    hasDuplicateExtId [p] = false := by
  simp [hasDuplicateExtId, hasDuplicateNatKey, List.any]

/-- Concrete 3-profile list with distinct ext_ids: no duplicates. -/
theorem no_duplicates_three_distinct :
    hasDuplicateExtId [
      { extId := 1, activationHeight := 10 },
      { extId := 2, activationHeight := 20 },
      { extId := 3, activationHeight := 30 }
    ] = false := by native_decide

/-- Concrete 3-profile list with a duplicate: detected. -/
theorem duplicate_in_three :
    hasDuplicateExtId [
      { extId := 1, activationHeight := 10 },
      { extId := 2, activationHeight := 20 },
      { extId := 1, activationHeight := 30 }
    ] = true := by native_decide

/-- Two profiles with the same ext_id are detected as duplicates. -/
theorem duplicate_detected (p q : DeploymentProfile) (h : p.extId = q.extId) :
    hasDuplicateExtId [p, q] = true := by
  simp [hasDuplicateExtId, hasDuplicateNatKey, h]

/-- Two profiles with different ext_ids are not duplicates. -/
theorem no_duplicate_different_ids (p q : DeploymentProfile) (h : p.extId ≠ q.extId) :
    hasDuplicateExtId [p, q] = false := by
  simp [hasDuplicateExtId, hasDuplicateNatKey, List.any]
  intro hEq
  exact h hEq.symm

-- ============================================================================
-- Section 4: Suite Authorization
-- ============================================================================

/-- Check if a suite ID is in the allowed set and is not the sentinel.
    This matches the active CORE_EXT invariant: post-activation, suite_id = 0
    must be rejected even if it appears in the configured list. -/
def suiteAllowed (suiteId : Nat) (allowedSuites : List Nat) : Bool :=
  allowedSuites.contains suiteId && suiteId != RubinFormal.SUITE_ID_SENTINEL

/-- Post-activation, the sentinel suite_id = 0 is rejected even if listed. -/
theorem sentinel_rejected_even_if_listed :
    suiteAllowed 0 [0, 1, 3] = false := by native_decide

/-- When suite_id is NOT in the allowed list, suiteAllowed returns false. -/
theorem suite_not_allowed_when_absent :
    suiteAllowed 5 [1, 3] = false := by native_decide

/-- Suite authorization is deterministic: same inputs produce same result. -/
theorem suite_auth_deterministic (s : Nat) (allowed : List Nat) :
    suiteAllowed s allowed = suiteAllowed s allowed := rfl

/-- Concrete: suite 1 is allowed in [1, 3]. -/
theorem suite_1_in_1_3 : suiteAllowed 1 [1, 3] = true := by native_decide

/-- Concrete: suite 2 is NOT allowed in [1, 3]. -/
theorem suite_2_not_in_1_3 : suiteAllowed 2 [1, 3] = false := by native_decide

/-- Empty allowed list rejects everything. -/
theorem suite_empty_rejects : suiteAllowed 1 [] = false := by native_decide

-- ============================================================================
-- Section 5: Pre-Activation Permissive Path
-- ============================================================================

/-- Model CORE_EXT spend decision: if profile not active → permissive (true),
    if active → check suite membership. -/
def extSpendDecision (profileActive : Bool) (suiteId : Nat) (allowedSuites : List Nat) : Bool :=
  if !profileActive then true
  else suiteAllowed suiteId allowedSuites

/-- Pre-activation (profileActive = false): unconditionally permissive
    regardless of suite_id or allowed list contents. -/
theorem pre_activation_always_accepts (suiteId : Nat) (allowed : List Nat) :
    extSpendDecision false suiteId allowed = true := by
  simp [extSpendDecision]

/-- Pre-activation result is independent of suite_id: two different
    suites get the same (accept) result when profile is inactive. -/
theorem pre_activation_suite_independent (s1 s2 : Nat) (allowed : List Nat) :
    extSpendDecision false s1 allowed = extSpendDecision false s2 allowed := by
  simp [extSpendDecision]

/-- Post-activation with disallowed suite → reject. This is the
    non-trivial counterpart: enforcement actually rejects. -/
theorem post_activation_disallowed_rejects :
    extSpendDecision true 5 [1, 3] = false := by native_decide

/-- Post-activation with allowed suite → accept. -/
theorem post_activation_allowed_accepts :
    extSpendDecision true 3 [1, 3] = true := by native_decide

-- ============================================================================
-- Section 6: Fixture-Replay Parse/Dispatch Helpers
-- ============================================================================

/-- Minimal deployment-profile view reused by the finite `CV-EXT` replay lane.
    This stays narrower than the live runtime profile surface: it models only
    the fields needed to prove parse/dispatch ordering without claiming
    `verify_sig_ext` correctness or txcontext-enabled behavior. -/
structure ReplayProfile where
  extId : Nat
  activationHeight : Nat
  allowedSuiteIds : List Nat
  binding : String
deriving Repr, DecidableEq

/-- Parsed CORE_EXT envelope: `ext_id` plus the raw payload bytes. -/
structure ParsedEnvelope where
  extId : Nat
  payload : Bytes
deriving Repr, DecidableEq

/-- Parse the finite fixture-envelope shape used by `CV-EXT`.
    Encoding is little-endian `ext_id:u16 || payload_len:u8 || payload`. -/
def parseEnvelope? (raw : Bytes) : Option ParsedEnvelope :=
  if raw.size < 3 then
    none
  else
    let extId := (raw.get! 0).toNat + 256 * (raw.get! 1).toNat
    let payloadLen := (raw.get! 2).toNat
    if raw.size == payloadLen + 3 then
      some { extId := extId, payload := raw.extract 3 raw.size }
    else
      none

/-- Duplicate `ext_id` detection for finite fixture replay profiles. -/
def hasDuplicateReplayProfileExtId : List ReplayProfile → Bool :=
  hasDuplicateNatKey (fun p => p.extId)

/-- Find the first replay profile matching an `ext_id`. Duplicate rejection is
    enforced separately via `hasDuplicateReplayProfileExtId`. -/
def findReplayProfile? (profiles : List ReplayProfile) (extId : Nat) : Option ReplayProfile :=
  profiles.find? (fun p => p.extId == extId)

/-- The current finite replay lane knows only the shipped OpenSSL digest32
    binding name. D2 models reachability to this binding, not verifier
    correctness; D3 remains the theorem lane for `verify_sig_ext`. -/
def bindingRecognized (binding : String) : Bool :=
  binding == "verify_sig_ext_openssl_digest32_v1"

theorem parse_envelope_short_rejects :
    parseEnvelope? (RubinFormal.bytes #[0x01]) = none := by
  native_decide

theorem parse_envelope_len_mismatch_rejects :
    parseEnvelope? (RubinFormal.bytes #[0x00, 0x10, 0x05, 0x01, 0x02]) = none := by
  native_decide

theorem parse_envelope_empty_payload_roundtrip :
    parseEnvelope? (RubinFormal.bytes #[0x00, 0x10, 0x00]) =
      some { extId := 4096, payload := ByteArray.empty } := by
  native_decide

theorem duplicate_replay_profile_detected :
    hasDuplicateReplayProfileExtId
      [ { extId := 7, activationHeight := 10, allowedSuiteIds := [1], binding := "verify_sig_ext_openssl_digest32_v1" }
      , { extId := 7, activationHeight := 20, allowedSuiteIds := [3], binding := "verify_sig_ext_openssl_digest32_v1" }
      ] = true := by
  native_decide

theorem distinct_replay_profiles_accept :
    hasDuplicateReplayProfileExtId
      [ { extId := 7, activationHeight := 10, allowedSuiteIds := [1], binding := "verify_sig_ext_openssl_digest32_v1" }
      , { extId := 8, activationHeight := 20, allowedSuiteIds := [3], binding := "verify_sig_ext_openssl_digest32_v1" }
      ] = false := by
  native_decide

theorem binding_recognized_openssl_digest32 :
    bindingRecognized "verify_sig_ext_openssl_digest32_v1" = true := by
  native_decide

-- ============================================================================
-- Section 7: Post-Parse Verify/Binding Path Ordering (D3)
-- ============================================================================

/-- Model-level post-parse CORE_EXT verification state.
    This D3 model starts after covenant-data parse and digest extraction have
    already succeeded. It captures only suite/native/binding route selection,
    txcontext preconditions, and the final error-class mapping for the
    `verify_sig_ext` callback paths. -/
structure VerifySigExtModelState where
  suiteId : Nat
  allowedSuites : List Nat
  nativeRegistered : Bool
  nativeSpendPermitted : Bool
  nativeWitnessCanonical : Bool
  txContextEnabled : Bool
  verifySigExtSupported : Bool
  txContextPresent : Bool
  txContextContinuingPresent : Bool
deriving Repr, DecidableEq

/-- Route selection after parse/digest success and ACTIVE profile admission. -/
inductive VerifySigExtRoute
  | suiteReject
  | nativeSpendReject
  | nativeRegistryDriftReject
  | nativeWitnessReject
  | nativeVerify
  | txContextUnsupportedReject
  | txContextBundleReject
  | txContextContinuingReject
  | txContextVerify
  | extUnsupportedReject
  | extVerify
deriving Repr, DecidableEq

/-- Final error-class surface for the post-parse verify/binding lane. -/
inductive VerifySigExtVerdict
  | accept
  | sigAlgInvalid
  | sigInvalid
  | sigNoncanonical
deriving Repr, DecidableEq

/-- Select the model-level verification route after parse and digest extraction.
    The ordering mirrors `validateCoreExtWitnessAtHeight`: suite gate first,
    then native-vs-ext dispatch, then txcontext/binding preconditions. -/
def verifySigExtRoute (s : VerifySigExtModelState) : VerifySigExtRoute :=
  if !suiteAllowed s.suiteId s.allowedSuites then
    .suiteReject
  else if s.nativeRegistered then
    if !s.nativeSpendPermitted then
      .nativeSpendReject
    else if !s.nativeWitnessCanonical then
      .nativeWitnessReject
    else
      .nativeVerify
  else if s.nativeSpendPermitted then
    .nativeRegistryDriftReject
  else if s.txContextEnabled then
    if !s.verifySigExtSupported then
      .txContextUnsupportedReject
    else if !s.txContextPresent then
      .txContextBundleReject
    else if !s.txContextContinuingPresent then
      .txContextContinuingReject
    else
      .txContextVerify
  else if !s.verifySigExtSupported then
    .extUnsupportedReject
  else
    .extVerify

/-- Final verdict mapping for the model-level post-parse verify/binding lane.
    `callbackErr` is meaningful only on the `verify_sig_ext` branches; the
    native route models only success vs signature-invalid at this layer. -/
def verifySigExtVerdict (route : VerifySigExtRoute) (callbackErr sigOk : Bool) :
    VerifySigExtVerdict :=
  match route with
  | .suiteReject
  | .nativeSpendReject
  | .nativeRegistryDriftReject
  | .txContextUnsupportedReject
  | .extUnsupportedReject =>
      .sigAlgInvalid
  | .nativeWitnessReject =>
      .sigNoncanonical
  | .txContextBundleReject
  | .txContextContinuingReject =>
      .sigInvalid
  | .nativeVerify =>
      if sigOk then .accept else .sigInvalid
  | .txContextVerify
  | .extVerify =>
      if callbackErr then .sigAlgInvalid else if sigOk then .accept else .sigInvalid

/-- Runtime-facing error-code rendering for D3 route/verdict theorems. -/
def verifySigExtErrCode : VerifySigExtVerdict → Option String
  | .accept => none
  | .sigAlgInvalid => some "TX_ERR_SIG_ALG_INVALID"
  | .sigInvalid => some "TX_ERR_SIG_INVALID"
  | .sigNoncanonical => some "TX_ERR_SIG_NONCANONICAL"

theorem verify_sig_ext_suite_gate_rejects_before_path
    (s : VerifySigExtModelState)
    (hSuite : suiteAllowed s.suiteId s.allowedSuites = false) :
    verifySigExtRoute s = .suiteReject := by
  simp [verifySigExtRoute, hSuite]

theorem verify_sig_ext_registered_native_outside_spend_set_rejects
    (s : VerifySigExtModelState)
    (hSuite : suiteAllowed s.suiteId s.allowedSuites = true)
    (hNative : s.nativeRegistered = true)
    (hSpend : s.nativeSpendPermitted = false) :
    verifySigExtRoute s = .nativeSpendReject := by
  simp [verifySigExtRoute, hSuite, hNative, hSpend]

theorem verify_sig_ext_native_spend_set_without_registry_rejects
    (s : VerifySigExtModelState)
    (hSuite : suiteAllowed s.suiteId s.allowedSuites = true)
    (hNative : s.nativeRegistered = false)
    (hSpend : s.nativeSpendPermitted = true) :
    verifySigExtRoute s = .nativeRegistryDriftReject := by
  simp [verifySigExtRoute, hSuite, hNative, hSpend]

theorem verify_sig_ext_native_noncanonical_rejects_before_verify
    (s : VerifySigExtModelState)
    (hSuite : suiteAllowed s.suiteId s.allowedSuites = true)
    (hNative : s.nativeRegistered = true)
    (hSpend : s.nativeSpendPermitted = true)
    (hCanonical : s.nativeWitnessCanonical = false) :
    verifySigExtRoute s = .nativeWitnessReject := by
  simp [verifySigExtRoute, hSuite, hNative, hSpend, hCanonical]

theorem verify_sig_ext_native_registered_canonical_reaches_native_verify
    (s : VerifySigExtModelState)
    (hSuite : suiteAllowed s.suiteId s.allowedSuites = true)
    (hNative : s.nativeRegistered = true)
    (hSpend : s.nativeSpendPermitted = true)
    (hCanonical : s.nativeWitnessCanonical = true) :
    verifySigExtRoute s = .nativeVerify := by
  simp [verifySigExtRoute, hSuite, hNative, hSpend, hCanonical]

theorem verify_sig_ext_txcontext_unsupported_rejects
    (s : VerifySigExtModelState)
    (hSuite : suiteAllowed s.suiteId s.allowedSuites = true)
    (hNative : s.nativeRegistered = false)
    (hSpend : s.nativeSpendPermitted = false)
    (hTx : s.txContextEnabled = true)
    (hSupport : s.verifySigExtSupported = false) :
    verifySigExtRoute s = .txContextUnsupportedReject := by
  simp [verifySigExtRoute, hSuite, hNative, hSpend, hTx, hSupport]

theorem verify_sig_ext_txcontext_missing_bundle_rejects
    (s : VerifySigExtModelState)
    (hSuite : suiteAllowed s.suiteId s.allowedSuites = true)
    (hNative : s.nativeRegistered = false)
    (hSpend : s.nativeSpendPermitted = false)
    (hTx : s.txContextEnabled = true)
    (hSupport : s.verifySigExtSupported = true)
    (hBundle : s.txContextPresent = false) :
    verifySigExtRoute s = .txContextBundleReject := by
  simp [verifySigExtRoute, hSuite, hNative, hSpend, hTx, hSupport, hBundle]

theorem verify_sig_ext_txcontext_missing_continuing_rejects
    (s : VerifySigExtModelState)
    (hSuite : suiteAllowed s.suiteId s.allowedSuites = true)
    (hNative : s.nativeRegistered = false)
    (hSpend : s.nativeSpendPermitted = false)
    (hTx : s.txContextEnabled = true)
    (hSupport : s.verifySigExtSupported = true)
    (hBundle : s.txContextPresent = true)
    (hContinuing : s.txContextContinuingPresent = false) :
    verifySigExtRoute s = .txContextContinuingReject := by
  simp [verifySigExtRoute, hSuite, hNative, hSpend, hTx, hSupport, hBundle, hContinuing]

theorem verify_sig_ext_txcontext_ready_reaches_verify
    (s : VerifySigExtModelState)
    (hSuite : suiteAllowed s.suiteId s.allowedSuites = true)
    (hNative : s.nativeRegistered = false)
    (hSpend : s.nativeSpendPermitted = false)
    (hTx : s.txContextEnabled = true)
    (hSupport : s.verifySigExtSupported = true)
    (hBundle : s.txContextPresent = true)
    (hContinuing : s.txContextContinuingPresent = true) :
    verifySigExtRoute s = .txContextVerify := by
  simp [verifySigExtRoute, hSuite, hNative, hSpend, hTx, hSupport, hBundle, hContinuing]

theorem verify_sig_ext_ext_binding_unsupported_rejects
    (s : VerifySigExtModelState)
    (hSuite : suiteAllowed s.suiteId s.allowedSuites = true)
    (hNative : s.nativeRegistered = false)
    (hSpend : s.nativeSpendPermitted = false)
    (hTx : s.txContextEnabled = false)
    (hSupport : s.verifySigExtSupported = false) :
    verifySigExtRoute s = .extUnsupportedReject := by
  simp [verifySigExtRoute, hSuite, hNative, hSpend, hTx, hSupport]

theorem verify_sig_ext_ext_binding_ready_reaches_verify
    (s : VerifySigExtModelState)
    (hSuite : suiteAllowed s.suiteId s.allowedSuites = true)
    (hNative : s.nativeRegistered = false)
    (hSpend : s.nativeSpendPermitted = false)
    (hTx : s.txContextEnabled = false)
    (hSupport : s.verifySigExtSupported = true) :
    verifySigExtRoute s = .extVerify := by
  simp [verifySigExtRoute, hSuite, hNative, hSpend, hTx, hSupport]

theorem verify_sig_ext_native_noncanonical_maps_sig_noncanonical :
    verifySigExtErrCode (verifySigExtVerdict .nativeWitnessReject false false) =
      some "TX_ERR_SIG_NONCANONICAL" := by
  native_decide

theorem verify_sig_ext_txcontext_missing_bundle_maps_sig_invalid :
    verifySigExtErrCode (verifySigExtVerdict .txContextBundleReject false false) =
      some "TX_ERR_SIG_INVALID" := by
  native_decide

theorem verify_sig_ext_txcontext_callback_error_maps_alg_invalid :
    verifySigExtErrCode (verifySigExtVerdict .txContextVerify true false) =
      some "TX_ERR_SIG_ALG_INVALID" := by
  native_decide

theorem verify_sig_ext_txcontext_callback_false_maps_sig_invalid :
    verifySigExtErrCode (verifySigExtVerdict .txContextVerify false false) =
      some "TX_ERR_SIG_INVALID" := by
  native_decide

theorem verify_sig_ext_ext_callback_error_maps_alg_invalid :
    verifySigExtErrCode (verifySigExtVerdict .extVerify true false) =
      some "TX_ERR_SIG_ALG_INVALID" := by
  native_decide

theorem verify_sig_ext_ext_callback_false_maps_sig_invalid :
    verifySigExtErrCode (verifySigExtVerdict .extVerify false false) =
      some "TX_ERR_SIG_INVALID" := by
  native_decide

end RubinFormal.CoreExtRefinement
