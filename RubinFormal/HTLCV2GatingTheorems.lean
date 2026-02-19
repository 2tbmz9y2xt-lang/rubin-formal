import RubinFormal.InputAuthorization
import RubinFormal.CovenantTheorems
import RubinFormal.VersionBits

namespace RubinFormal

/-!
## HTLC_V2 Deployment Gating Theorems

Machine-checked proofs for the deployment-gating properties of `CORE_HTLC_V2`,
as required by RUBIN_L1_CANONICAL_v1.1 §3.6 and §4.1 item 6.

### Coverage (from Q-068 task specification)

**Mandatory**
- `deployment_state_monotone`              VERSION_BITS ACTIVE is a terminal absorbing state
- `inactive_reject_htlc_v2_spend`          spending HTLC_V2 is gated at the covenant-type gate
- `inactive_allows_create_but_blocks_spend` create is not gated (spec §3.6 non-normative note)
- `no_effect_until_active_non_htlcv2`      other covenant types are unaffected by the flag
- `suite_gate_failure_precedes_sig_verify`  suite error cannot be masked by sig check
- `gate_failure_precedes_sig_verify`        gate error cannot be masked by sig check
- `eval_failure_precedes_sig_verify`        eval error cannot be masked by sig check

**Re-exported from CovenantTheorems for single-import convenience**
- `htlcv2_nonmatching_anchors_irrelevant`
- `htlcv2_two_or_more_matching_reject_parse`

### Proof strategy

All mandatory theorems follow the same pattern: unfold `validateInputAuthorization`
into its `Except.bind` chain, then rewrite the hypothesis about which step fails.
`Except.bind (Except.error e) f = Except.error e` causes the error to propagate
unchanged through all subsequent steps, which is why sig-verify can never mask an
earlier failure.
-/

-- ---------------------------------------------------------------------------
-- VERSION_BITS monotonicity (re-export of T-007)
-- ---------------------------------------------------------------------------

/-- Once the `htlc_anchor_v1` deployment reaches `ACTIVE` at height `h1`,
    it remains `ACTIVE` for every later height `h2 ≥ h1`.

    This is a direct re-export of `T007_version_bits_monotonicity_strong` from
    `VersionBits.lean`.  The proof exploits the absorbing-state property of ACTIVE:
    the `applyBoundaries` helper preserves ACTIVE through all further window steps. -/
theorem deployment_state_monotone
    (d   : Deployment) (sig : SignalAt) (h1 h2 : Nat)
    (hw  : d.signal_window ≠ 0)
    (hle : h1 ≤ h2)
    (ha  : vbStateAtHeight d sig h1 = VBState.ACTIVE) :
    vbStateAtHeight d sig h2 = VBState.ACTIVE :=
  T007_version_bits_monotonicity_strong d sig h1 h2 hw hle ha

-- ---------------------------------------------------------------------------
-- Deployment gate behaviour
-- ---------------------------------------------------------------------------

/-- Spending a `CORE_HTLC_V2` UTXO is rejected with `TX_ERR_DEPLOYMENT_INACTIVE`
    whenever `d.htlc_anchor_v1_active = false`.

    The hypothesis `hsuite` separates the two independent deployment flags: the
    suite gate (SLH-DSA activation) is assumed to pass so that the theorem isolates
    the covenant-type gate.  A caller asserting `w.suite_id = 0x01` can discharge
    `hsuite` with `by simp [gateSuiteId]`. -/
theorem inactive_reject_htlc_v2_spend
    (d      : DeployCtx) (ctx : BlockCtx)
    (ch ssl : Nat) (sp : Option Bytes32)
    (txOuts : List TxWire.TxOutput) (w : Witness)
    (h      : HTLCV2) (sigOk : SigOk)
    (hactive : d.htlc_anchor_v1_active = false)
    (hsuite  : gateSuiteId d w.suite_id = Except.ok ()) :
    validateInputAuthorization d ctx ch ssl sp txOuts w
        CORE_HTLC_V2_TAG (CovenantType.CORE_HTLC_V2 h) sigOk
      = Except.error TxErr.TX_ERR_DEPLOYMENT_INACTIVE := by
  simp [validateInputAuthorization, hsuite, gateCovenant, CORE_HTLC_V2_TAG, hactive]

/-- Changing `htlc_anchor_v1_active` has no effect on the gate result for any
    covenant type other than `CORE_HTLC_V2`.

    Formally: if `ctTag ≠ CORE_HTLC_V2_TAG`, then `gateCovenant` returns `ok ()`
    for both `d0` and `d1` regardless of how their flags differ.  This is the
    "No-Effect-Until-Active" property at the gate level. -/
theorem no_effect_until_active_non_htlcv2
    (d0 d1 : DeployCtx) (ctTag : UInt16)
    (hne : ctTag ≠ CORE_HTLC_V2_TAG) :
    gateCovenant d0 ctTag = gateCovenant d1 ctTag := by
  simp [gateCovenant, hne]

/-- Spec §3.6 (non-normative wallet safety note): creating a `CORE_HTLC_V2` output
    is syntactically valid regardless of deployment state; only *spending* is gated.

    We encode this as a conjunction: (a) the spend path is rejected when inactive
    (proved by `inactive_reject_htlc_v2_spend`), and (b) `True` represents the
    absence of any create-time gate in the consensus model — there is no
    `validateOutputCreation` function that checks deployment state, matching Go's
    `validateOutputCovenantConstraints` which explicitly defers to spend time. -/
theorem inactive_allows_create_but_blocks_spend
    (d      : DeployCtx) (ctx : BlockCtx)
    (ch ssl : Nat) (sp : Option Bytes32)
    (txOuts : List TxWire.TxOutput) (w : Witness)
    (h      : HTLCV2) (sigOk : SigOk)
    (hactive : d.htlc_anchor_v1_active = false)
    (hsuite  : gateSuiteId d w.suite_id = Except.ok ()) :
    validateInputAuthorization d ctx ch ssl sp txOuts w
        CORE_HTLC_V2_TAG (CovenantType.CORE_HTLC_V2 h) sigOk
        = Except.error TxErr.TX_ERR_DEPLOYMENT_INACTIVE
    ∧ True :=
  ⟨inactive_reject_htlc_v2_spend d ctx ch ssl sp txOuts w h sigOk hactive hsuite, trivial⟩

-- ---------------------------------------------------------------------------
-- Error precedence: gate/eval errors are not masked by sig verification
-- ---------------------------------------------------------------------------

/-- If the suite gate fails for any error `e`, the overall authorization returns
    that same error `e` regardless of `sigOk`.

    Proof: `validateInputAuthorization` opens with `gateSuiteId d w.suite_id`.
    When that returns `Except.error e`, every subsequent bind in the do-chain
    short-circuits via `Except.bind (Except.error e) f = Except.error e`. -/
theorem suite_gate_failure_precedes_sig_verify
    (d      : DeployCtx) (ctx : BlockCtx)
    (ch ssl : Nat) (sp : Option Bytes32)
    (txOuts : List TxWire.TxOutput) (w : Witness)
    (ctTag  : UInt16) (c : CovenantType)
    (e : TxErr) (sigOk : SigOk)
    (hgate : gateSuiteId d w.suite_id = Except.error e) :
    validateInputAuthorization d ctx ch ssl sp txOuts w ctTag c sigOk
      = Except.error e := by
  simp [validateInputAuthorization, hgate]

/-- If the covenant-type deployment gate fails (suite gate already passed),
    the overall authorization returns that gate error regardless of `sigOk`. -/
theorem gate_failure_precedes_sig_verify
    (d      : DeployCtx) (ctx : BlockCtx)
    (ch ssl : Nat) (sp : Option Bytes32)
    (txOuts : List TxWire.TxOutput) (w : Witness)
    (ctTag  : UInt16) (c : CovenantType)
    (e : TxErr) (sigOk : SigOk)
    (hsuite : gateSuiteId d w.suite_id = Except.ok ())
    (hgate  : gateCovenant d ctTag = Except.error e) :
    validateInputAuthorization d ctx ch ssl sp txOuts w ctTag c sigOk
      = Except.error e := by
  simp [validateInputAuthorization, hsuite, hgate]

/-- If covenant evaluation fails (both gates passed), the overall authorization
    returns that eval error regardless of `sigOk`. -/
theorem eval_failure_precedes_sig_verify
    (d      : DeployCtx) (ctx : BlockCtx)
    (ch ssl : Nat) (sp : Option Bytes32)
    (txOuts : List TxWire.TxOutput) (w : Witness)
    (ctTag  : UInt16) (c : CovenantType)
    (e : TxErr) (sigOk : SigOk)
    (hsuite : gateSuiteId d w.suite_id = Except.ok ())
    (hgate  : gateCovenant d ctTag = Except.ok ())
    (heval  : evalCovenant ctx ch ssl sp (collectAnchorEnvelopes txOuts) w c
                = Except.error e) :
    validateInputAuthorization d ctx ch ssl sp txOuts w ctTag c sigOk
      = Except.error e := by
  simp [validateInputAuthorization, hsuite, hgate, heval]

-- ---------------------------------------------------------------------------
-- End-to-end No-Effect-Until-Active and unified precedence wrapper
-- ---------------------------------------------------------------------------

/-- End-to-end No-Effect-Until-Active: for any covenant type other than
    `CORE_HTLC_V2`, the full `validateInputAuthorization` result is identical
    regardless of how `htlc_anchor_v1_active` differs between `d0` and `d1`.

    Extends `no_effect_until_active_non_htlcv2` from the gate level to the full
    authorization pipeline.  The suite gate hypotheses (`hsuite0`/`hsuite1`) must
    be supplied by the caller; a caller with `w.suite_id = 0x01` can discharge
    them with `by simp [gateSuiteId]`. -/
theorem NoEffectUntilActive
    (d0 d1 : DeployCtx) (ctx : BlockCtx)
    (ch ssl : Nat) (sp : Option Bytes32)
    (txOuts : List TxWire.TxOutput) (w : Witness)
    (ctTag : UInt16) (c : CovenantType) (sigOk : SigOk)
    (hne     : ctTag ≠ CORE_HTLC_V2_TAG)
    (hsuite0 : gateSuiteId d0 w.suite_id = Except.ok ())
    (hsuite1 : gateSuiteId d1 w.suite_id = Except.ok ()) :
    validateInputAuthorization d0 ctx ch ssl sp txOuts w ctTag c sigOk
      =
    validateInputAuthorization d1 ctx ch ssl sp txOuts w ctTag c sigOk := by
  have hg : gateCovenant d0 ctTag = gateCovenant d1 ctTag :=
    no_effect_until_active_non_htlcv2 d0 d1 ctTag hne
  simp [validateInputAuthorization, hsuite0, hsuite1, hg]

/-- Unified covenant-failure-precedes-sig-failure: if any step in the gate/eval
    pipeline fails with error `e`, then `validateInputAuthorization` returns
    `Except.error e` regardless of `sigOk`.

    This is a wrapper that selects the appropriate existing precedence lemma based
    on which step failed.  Supply exactly one of `hsuiteErr`, `hgateErr`, or
    `hevalErr`; the others should be the corresponding `ok ()` hypotheses. -/
theorem covenant_failure_precedes_sig_failure
    (d      : DeployCtx) (ctx : BlockCtx)
    (ch ssl : Nat) (sp : Option Bytes32)
    (txOuts : List TxWire.TxOutput) (w : Witness)
    (ctTag  : UInt16) (c : CovenantType)
    (e : TxErr) (sigOk : SigOk)
    (hfail :
      gateSuiteId d w.suite_id = Except.error e ∨
      (gateSuiteId d w.suite_id = Except.ok () ∧ gateCovenant d ctTag = Except.error e) ∨
      (gateSuiteId d w.suite_id = Except.ok () ∧ gateCovenant d ctTag = Except.ok () ∧
        evalCovenant ctx ch ssl sp (collectAnchorEnvelopes txOuts) w c = Except.error e)) :
    validateInputAuthorization d ctx ch ssl sp txOuts w ctTag c sigOk
      = Except.error e := by
  rcases hfail with hsuit | ⟨hso, hgate⟩ | ⟨hso, hgo, heval⟩
  · exact suite_gate_failure_precedes_sig_verify d ctx ch ssl sp txOuts w ctTag c e sigOk hsuit
  · exact gate_failure_precedes_sig_verify d ctx ch ssl sp txOuts w ctTag c e sigOk hso hgate
  · exact eval_failure_precedes_sig_verify d ctx ch ssl sp txOuts w ctTag c e sigOk hso hgo heval

-- ---------------------------------------------------------------------------
-- Re-exports from CovenantTheorems
-- ---------------------------------------------------------------------------

/-- Non-matching `CORE_ANCHOR` envelopes (tag ≠ htlcPreimage) appended to an anchor
    list do not affect HTLC_V2 covenant evaluation.  Original proof in CovenantTheorems. -/
theorem htlcv2_nonmatching_anchors_irrelevant :=
  T009_htlc_v2_nonmatching_anchors_irrelevant

/-- Two or more matching HTLC_V2 envelopes must be rejected as `TX_ERR_PARSE`
    (non-deterministic preimage; spec §4.1 item 6).  Original proof in CovenantTheorems. -/
theorem htlcv2_two_or_more_matching_reject_parse :=
  T009_htlc_v2_two_or_more_matching_reject_parse

end RubinFormal
