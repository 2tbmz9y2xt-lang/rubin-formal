-- Finite fixture-anchored CORE_EXT parse/dispatch replay.
-- D2 turns `CV-EXT` into an actual replay lane over the shipped vectors, while
-- staying below D3/D4: this file does not prove `verify_sig_ext` correctness or
-- txcontext-enabled behavior. It proves only the parse/dispatch/order surface
-- exercised by the current pinned fixture set.

import RubinFormal.Conformance.CVExtVectors
import RubinFormal.Hex

namespace RubinFormal.Conformance

open RubinFormal
open RubinFormal.CoreExtRefinement

private def allDistinctIds (vs : List CVExtVector) : Bool :=
  let ids := vs.map (·.id)
  ids.length == ids.eraseDups.length

private def allRejectsHaveErr (vs : List CVExtVector) : Bool :=
  vs.all fun v =>
    if v.expectOk then true
    else match v.expectErr with
      | some e => e.length > 0
      | none => false

private def familyTagMatchesId (v : CVExtVector) : Bool :=
  v.id.startsWith ("CV-EXT-" ++ v.family ++ "-")

private def hasFamilies (vs : List CVExtVector) (families : List String) : Bool :=
  families.all fun fam => vs.any fun v => v.family == fam

private def activationRoutedOp (op : String) : Bool :=
  op == "ext_activation_check" ||
  op == "ext_pre_activation_spend" ||
  op == "ext_enforcement_check" ||
  op == "ext_error_priority"

private def knownReplayOp (op : String) : Bool :=
  activationRoutedOp op ||
  op == "ext_envelope_parse" ||
  op == "ext_duplicate_profile"

def cvExtVectorBundleContract : Bool :=
  cvExtVectors.length == 25 &&
  allDistinctIds cvExtVectors &&
  allRejectsHaveErr cvExtVectors &&
  cvExtVectors.all familyTagMatchesId &&
  cvExtVectors.all (fun v => knownReplayOp v.op) &&
  hasFamilies cvExtVectors ["ENV", "ACT", "PRE", "ENF", "PAY", "ERR", "DUP", "GEN", "PAR"]

def parseEnvelopeHex? (hex : String) : Option ParsedEnvelope := do
  let raw <- RubinFormal.decodeHex? hex
  parseEnvelope? raw

/-- Finite replay outcomes for the current `CV-EXT` lane.
    `verifyReachable` means parse + activation + suite gate + binding selection
    all succeeded; D3 remains responsible for proving the verifier itself. -/
inductive CVExtReplayOutcome
  | parseReject
  | fixtureMetadataReject
  | duplicateProfileReject
  | permissiveAccept
  | suiteReject
  | bindingReject
  | verifyReachable
deriving Repr, DecidableEq

/-- The current shipped fixture lane still treats `suite_id = 0` as an admitted
    enforcement input. This is intentionally fixture-anchored and more
    permissive than the live sentinel rule proved elsewhere; separate
    spend-side theorem files continue to own the live consensus boundary. -/
def fixtureSuiteAdmitted (suiteId : Nat) (allowedSuites : List Nat) : Bool :=
  suiteId == RubinFormal.SUITE_ID_SENTINEL || allowedSuites.contains suiteId

/-- Dispatch result after envelope parse and duplicate-profile screening.
    This is a finite ordering model only: parse/duplicate/profile-state/suite
    gate/binding selection. It stops before `verify_sig_ext` correctness. -/
def dispatchFromProfile (profile : ReplayProfile) (height : Nat)
    (suiteId : Option Nat) : CVExtReplayOutcome :=
  match activationStateAt height profile.activationHeight with
  | ActivationState.PreActive => .permissiveAccept
  | ActivationState.Active =>
      match suiteId with
      | none => .suiteReject
      | some sid =>
          if fixtureSuiteAdmitted sid profile.allowedSuiteIds then
            if bindingRecognized profile.binding then .verifyReachable else .bindingReject
          else
            .suiteReject

/-- Replay the shipped `CV-EXT` vectors through the D2 parse/dispatch model. -/
def replayExtVector (v : CVExtVector) : CVExtReplayOutcome :=
  match parseEnvelopeHex? v.covenantDataHex with
  | none => .parseReject
  | some env =>
      if hasDuplicateReplayProfileExtId v.profiles then
        .duplicateProfileReject
      else
        if knownReplayOp v.op then
          if activationRoutedOp v.op then
            match findReplayProfile? v.profiles env.extId, v.height with
            | none, _ => .permissiveAccept
            | some _, none => .fixtureMetadataReject
            | some profile, some height => dispatchFromProfile profile height v.suiteId
          else match v.op with
          | "ext_envelope_parse" =>
              .permissiveAccept
          | "ext_duplicate_profile" =>
              .permissiveAccept
          | _ =>
              .fixtureMetadataReject
        else
          .fixtureMetadataReject

private def replayOutcomeVerdict (outcome : CVExtReplayOutcome) : Bool × Option String :=
  match outcome with
  | .parseReject | .fixtureMetadataReject | .duplicateProfileReject =>
      (false, some "TX_ERR_COVENANT_TYPE_INVALID")
  | .suiteReject =>
      (false, some "TX_ERR_SIG_ALG_INVALID")
  | .bindingReject =>
      (false, some "TX_ERR_SIG_ALG_INVALID")
  | .permissiveAccept | .verifyReachable =>
      (true, none)

def checkExtVector (v : CVExtVector) : Bool :=
  let (ok, err) := replayOutcomeVerdict (replayExtVector v)
  if v.expectOk then
    ok
  else
    (!ok) && (err == v.expectErr)

def allCVExt : Bool :=
  cvExtVectors.all checkExtVector

def cvExtReplayContract : Bool :=
  cvExtVectorBundleContract && allCVExt

private theorem all_append (xs ys : List CVExtVector) (p : CVExtVector → Bool) :
    (xs ++ ys).all p = (xs.all p && ys.all p) := by
  induction xs with
  | nil =>
      simp [List.all]
  | cons _ _ ih =>
      simp [List.all, ih, Bool.and_assoc]

theorem cv_ext_vector_bundle_contract_holds : cvExtVectorBundleContract = true := by
  native_decide

private theorem all_cv_ext_holds : allCVExt = true := by
  let n : Nat := cvExtVectors.length / 2
  have h1 : (cvExtVectors.take n).all checkExtVector = true := by
    native_decide
  have h2 : (cvExtVectors.drop n).all checkExtVector = true := by
    native_decide
  have h : (cvExtVectors.take n ++ cvExtVectors.drop n).all checkExtVector = true := by
    calc
      (cvExtVectors.take n ++ cvExtVectors.drop n).all checkExtVector
          = ((cvExtVectors.take n).all checkExtVector && (cvExtVectors.drop n).all checkExtVector) := by
              simpa using all_append (cvExtVectors.take n) (cvExtVectors.drop n) checkExtVector
      _ = (true && true) := by simp [h1, h2]
      _ = true := by simp
  simpa [allCVExt, List.take_append_drop] using h

theorem cv_ext_vectors_pass : cvExtReplayContract = true := by
  simp [cvExtReplayContract, cv_ext_vector_bundle_contract_holds, all_cv_ext_holds]

theorem parse_failure_rejects_before_dispatch (v : CVExtVector)
    (hParse : parseEnvelopeHex? v.covenantDataHex = none) :
    replayExtVector v = .parseReject := by
  simp [replayExtVector, hParse]

theorem duplicate_profiles_reject_before_activation (v : CVExtVector) (env : ParsedEnvelope)
    (hParse : parseEnvelopeHex? v.covenantDataHex = some env)
    (hDup : hasDuplicateReplayProfileExtId v.profiles = true) :
    replayExtVector v = .duplicateProfileReject := by
  simp [replayExtVector, hParse, hDup]

theorem matched_profile_without_height_rejects_before_dispatch
    (v : CVExtVector) (env : ParsedEnvelope) (profile : ReplayProfile)
    (hParse : parseEnvelopeHex? v.covenantDataHex = some env)
    (hDup : hasDuplicateReplayProfileExtId v.profiles = false)
    (hOp : activationRoutedOp v.op = true)
    (hProfile : findReplayProfile? v.profiles env.extId = some profile)
    (hHeight : v.height = none) :
    replayExtVector v = .fixtureMetadataReject := by
  simp [replayExtVector, hParse, hDup, hOp, hProfile, hHeight, knownReplayOp]

theorem unknown_op_rejects_as_fixture_metadata
    (v : CVExtVector) (env : ParsedEnvelope)
    (hParse : parseEnvelopeHex? v.covenantDataHex = some env)
    (hDup : hasDuplicateReplayProfileExtId v.profiles = false)
    (hKnown : knownReplayOp v.op = false) :
    replayExtVector v = .fixtureMetadataReject := by
  simp [replayExtVector, hParse, hDup, hKnown]

theorem dispatch_profile_preactive_is_permissive (profile : ReplayProfile) (height : Nat)
    (suiteId : Option Nat)
    (hState : activationStateAt height profile.activationHeight = ActivationState.PreActive) :
    dispatchFromProfile profile height suiteId = .permissiveAccept := by
  simp [dispatchFromProfile, hState]

theorem dispatch_profile_active_disallowed_suite_rejects (profile : ReplayProfile)
    (height suiteId : Nat)
    (hState : activationStateAt height profile.activationHeight = ActivationState.Active)
    (hAllowed : fixtureSuiteAdmitted suiteId profile.allowedSuiteIds = false) :
    dispatchFromProfile profile height (some suiteId) = .suiteReject := by
  simp [dispatchFromProfile, hState, hAllowed]

theorem dispatch_profile_active_missing_suite_rejects (profile : ReplayProfile)
    (height : Nat)
    (hState : activationStateAt height profile.activationHeight = ActivationState.Active) :
    dispatchFromProfile profile height none = .suiteReject := by
  simp [dispatchFromProfile, hState]

theorem dispatch_profile_active_allowed_suite_reaches_verify (profile : ReplayProfile)
    (height suiteId : Nat)
    (hState : activationStateAt height profile.activationHeight = ActivationState.Active)
    (hAllowed : fixtureSuiteAdmitted suiteId profile.allowedSuiteIds = true)
    (hBinding : bindingRecognized profile.binding = true) :
    dispatchFromProfile profile height (some suiteId) = .verifyReachable := by
  simp [dispatchFromProfile, hState, hAllowed, hBinding]

theorem dispatch_profile_active_unknown_binding_rejects (profile : ReplayProfile)
    (height suiteId : Nat)
    (hState : activationStateAt height profile.activationHeight = ActivationState.Active)
    (hAllowed : fixtureSuiteAdmitted suiteId profile.allowedSuiteIds = true)
    (hBinding : bindingRecognized profile.binding = false) :
    dispatchFromProfile profile height (some suiteId) = .bindingReject := by
  simp [dispatchFromProfile, hState, hAllowed, hBinding]

/-- D2 parse surface: malformed envelope and duplicate-profile states are
    explicit theorem obligations, not just comments about fixture structure. -/
def cvExtParsingSurface : Prop :=
  (∀ v : CVExtVector, parseEnvelopeHex? v.covenantDataHex = none →
    replayExtVector v = .parseReject) ∧
  (∀ v : CVExtVector, ∀ env : ParsedEnvelope,
    parseEnvelopeHex? v.covenantDataHex = some env →
    hasDuplicateReplayProfileExtId v.profiles = true →
    replayExtVector v = .duplicateProfileReject) ∧
  (∀ v : CVExtVector, ∀ env : ParsedEnvelope, ∀ profile : ReplayProfile,
    parseEnvelopeHex? v.covenantDataHex = some env →
    hasDuplicateReplayProfileExtId v.profiles = false →
    activationRoutedOp v.op = true →
    findReplayProfile? v.profiles env.extId = some profile →
    v.height = none →
    replayExtVector v = .fixtureMetadataReject) ∧
  (∀ v : CVExtVector, ∀ env : ParsedEnvelope,
    parseEnvelopeHex? v.covenantDataHex = some env →
    hasDuplicateReplayProfileExtId v.profiles = false →
    knownReplayOp v.op = false →
    replayExtVector v = .fixtureMetadataReject)

theorem cv_ext_parsing_surface_proved : cvExtParsingSurface := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v hParse
    exact parse_failure_rejects_before_dispatch v hParse
  · intro v env hParse hDup
    exact duplicate_profiles_reject_before_activation v env hParse hDup
  · intro v env profile hParse hDup hOp hProfile hHeight
    exact matched_profile_without_height_rejects_before_dispatch v env profile hParse hDup hOp hProfile hHeight
  · intro v env hParse hDup hKnown
    exact unknown_op_rejects_as_fixture_metadata v env hParse hDup hKnown

/-- D2 dispatch surface: pre-active permissive path, suite gate ordering, and
    binding reachability are explicit theorem obligations. This remains a
    finite fixture-anchored dispatch model, not a proof of `verify_sig_ext`. -/
def cvExtDispatchSurface : Prop :=
  (∀ profile : ReplayProfile, ∀ height : Nat, ∀ suiteId : Option Nat,
    activationStateAt height profile.activationHeight = ActivationState.PreActive →
    dispatchFromProfile profile height suiteId = .permissiveAccept) ∧
  (∀ profile : ReplayProfile, ∀ height suiteId : Nat,
    activationStateAt height profile.activationHeight = ActivationState.Active →
    fixtureSuiteAdmitted suiteId profile.allowedSuiteIds = false →
    dispatchFromProfile profile height (some suiteId) = .suiteReject) ∧
  (∀ profile : ReplayProfile, ∀ height suiteId : Nat,
    activationStateAt height profile.activationHeight = ActivationState.Active →
    fixtureSuiteAdmitted suiteId profile.allowedSuiteIds = true →
    bindingRecognized profile.binding = true →
    dispatchFromProfile profile height (some suiteId) = .verifyReachable) ∧
  (∀ profile : ReplayProfile, ∀ height : Nat,
    activationStateAt height profile.activationHeight = ActivationState.Active →
    dispatchFromProfile profile height none = .suiteReject) ∧
  (∀ profile : ReplayProfile, ∀ height suiteId : Nat,
    activationStateAt height profile.activationHeight = ActivationState.Active →
    fixtureSuiteAdmitted suiteId profile.allowedSuiteIds = true →
    bindingRecognized profile.binding = false →
    dispatchFromProfile profile height (some suiteId) = .bindingReject)

theorem cv_ext_dispatch_surface_proved : cvExtDispatchSurface := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro profile height suiteId hState
    exact dispatch_profile_preactive_is_permissive profile height suiteId hState
  · intro profile height suiteId hState hAllowed
    exact dispatch_profile_active_disallowed_suite_rejects profile height suiteId hState hAllowed
  · intro profile height suiteId hState hAllowed hBinding
    exact dispatch_profile_active_allowed_suite_reaches_verify profile height suiteId hState hAllowed hBinding
  · intro profile height hState
    exact dispatch_profile_active_missing_suite_rejects profile height hState
  · intro profile height suiteId hState hAllowed hBinding
    exact dispatch_profile_active_unknown_binding_rejects profile height suiteId hState hAllowed hBinding

end RubinFormal.Conformance
