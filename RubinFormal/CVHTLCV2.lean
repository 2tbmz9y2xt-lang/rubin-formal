import RubinFormal.HTLCV2GatingTheorems

namespace RubinFormal

/-!
## CV-HTLCV2 — Conformance Vectors for HTLC_V2

Eight assertion-level CV cases matching the HTLC_V2 conformance plan.
Each theorem encodes a concrete spec precondition as a Lean hypothesis
and proves the expected outcome through `evalCovenant` or
`validateInputAuthorization`.

### Case index

| ID             | Path            | Trigger                          | Expected              | Status   |
|----------------|-----------------|----------------------------------|-----------------------|----------|
| CV-HTLCV2-01   | validateInputAuth | inactive deployment             | TX_ERR_DEPLOYMENT_INACTIVE | ✅ proved |
| CV-HTLCV2-02   | evalCovenant    | script_sig_len ≠ 0              | TX_ERR_PARSE          | ✅ proved |
| CV-HTLCV2-03   | evalCovenant    | 2 matching envelopes            | TX_ERR_PARSE          | ✅ proved |
| CV-HTLCV2-04   | evalCovenant    | claim path, hash mismatch       | TX_ERR_SIG_INVALID    | ✅ proved |
| CV-HTLCV2-05   | evalCovenant    | claim path, key mismatch        | TX_ERR_SIG_INVALID    | ✅ proved |
| CV-HTLCV2-06   | evalCovenant    | refund path, key mismatch       | TX_ERR_SIG_INVALID    | ✅ proved |
| CV-HTLCV2-07   | evalCovenant    | refund path, timelock not met   | TX_ERR_TIMELOCK_NOT_MET | ✅ proved |
| CV-HTLCV2-08   | evalCovenant    | claim_key_id = refund_key_id    | TX_ERR_PARSE          | ✅ proved |

All 8 cases are proved. CV-02 uses the `script_sig_len != 0` check already present
in `Covenant.evalCovenant`. CV-04/05 use `List.head?` (not `List.get`) which
discharges cleanly via `simp only [..., List.head?]`.
-/

-- Shared test helpers --------------------------------------------------------

-- `zk n` produces a Bytes32 filled with the byte `n`, useful for distinct key IDs.
private def zk (n : UInt8) : Bytes32 := List.replicate 32 n

-- Construct a canonical HTLCV2 with distinct key IDs.
private def mkH
    (hash claim refund : Bytes32)
    (lockMode : LockMode := LockMode.height) (lockVal : Nat := 100) : HTLCV2 :=
  { hash := hash, lock_mode := lockMode, lock_value := lockVal
  , claim_key_id := claim, refund_key_id := refund }

-- A minimal block context (height 200, above any lock_value used in tests).
private def testCtx : BlockCtx := { height := 200, timestamp := 1_700_000_000 }

-- A block context where the height is BELOW the lock value (for timelock-not-met tests).
private def earlyCtx : BlockCtx := { height := 50, timestamp := 1_000_000_000 }

-- A witness using suite_id 0x01 (ML-DSA-87, always permitted).
private def mkW (keyId : Bytes32) : Witness :=
  { suite_id := 0x01, key_id := keyId, isSentinel := false }

-- A deploy context with HTLC_V2 ACTIVE and SLH-DSA ACTIVE.
private def activeCtx : DeployCtx :=
  { htlc_anchor_v1_active := true, slh_dsa_suite_active := true }

-- A deploy context with HTLC_V2 INACTIVE.
private def inactiveCtx : DeployCtx :=
  { htlc_anchor_v1_active := false, slh_dsa_suite_active := true }

-- ---------------------------------------------------------------------------
-- CV-HTLCV2-01 : inactive deployment → TX_ERR_DEPLOYMENT_INACTIVE
-- ---------------------------------------------------------------------------

/-- Spending any `CORE_HTLC_V2` UTXO MUST be rejected when the `htlc_anchor_v1`
    deployment is not ACTIVE, regardless of envelope contents or sig result.

    This tests `validateInputAuthorization` end-to-end, verifying that the gate
    check at step 6b fires before the covenant evaluation at step 7. -/
theorem CV_HTLCV2_01_inactive_spend_rejected (sigOk : SigOk)
    (ssl : Nat) (txOuts : List TxWire.TxOutput) :
    let h := mkH (zk 0xaa) (zk 0x11) (zk 0x22)
    let w := mkW (zk 0x11)
    validateInputAuthorization inactiveCtx testCtx 0 ssl none txOuts w
        CORE_HTLC_V2_TAG (CovenantType.CORE_HTLC_V2 h) sigOk
      = Except.error TxErr.TX_ERR_DEPLOYMENT_INACTIVE := by
  -- suite_id = 0x01 always passes gateSuiteId; then gateCovenant fires
  simp [validateInputAuthorization, gateSuiteId, inactiveCtx,
        gateCovenant, CORE_HTLC_V2_TAG]

-- ---------------------------------------------------------------------------
-- CV-HTLCV2-02 : script_sig_len ≠ 0 → TX_ERR_PARSE
-- ---------------------------------------------------------------------------

/-- When a `CORE_HTLC_V2` input carries a non-empty `script_sig`, it MUST be
    rejected as `TX_ERR_PARSE` (spec §4.1 item 6, §3.1).

    The `script_sig_len != 0` check is the first branch in the `CORE_HTLC_V2`
    match arm of `Covenant.evalCovenant` and fires before any envelope scan. -/
theorem CV_HTLCV2_02_script_sig_len_nonzero_reject (sigOk : SigOk)
    (txOuts : List TxWire.TxOutput) :
    let h := mkH (zk 0xaa) (zk 0x11) (zk 0x22)
    let w := mkW (zk 0x11)
    validateInputAuthorization activeCtx testCtx 0 1 none txOuts w
        CORE_HTLC_V2_TAG (CovenantType.CORE_HTLC_V2 h) sigOk
      = Except.error TxErr.TX_ERR_PARSE := by
  simp [validateInputAuthorization, gateSuiteId, activeCtx,
        gateCovenant, CORE_HTLC_V2_TAG, evalCovenant, mkH, zk]

-- ---------------------------------------------------------------------------
-- CV-HTLCV2-03 : two matching envelopes → TX_ERR_PARSE
-- ---------------------------------------------------------------------------

/-- Two `CORE_ANCHOR` envelopes matching the HTLC_V2 prefix in the same transaction
    create an ambiguous preimage and MUST be rejected as `TX_ERR_PARSE`
    (spec §4.1 item 6: "If |matching| ≥ 2: reject as TX_ERR_PARSE").

    We parameterise over abstract anchors `a1`, `a2` with an htlcPreimage tag,
    matching the assertion-level style of `CovenantExamples.lean`. -/
theorem CV_HTLCV2_03_two_matching_envelopes_reject
    (ctx : BlockCtx) (ch : Nat) (w : Witness)
    (a1 a2 : AnchorEnvelope)
    (ha1 : a1.tag = AnchorTag.htlcPreimage)
    (ha2 : a2.tag = AnchorTag.htlcPreimage) :
    let h := mkH (zk 0xbb) (zk 0x33) (zk 0x44)
    evalCovenant ctx ch 0 none [a1, a2] w (CovenantType.CORE_HTLC_V2 h)
      = Except.error TxErr.TX_ERR_PARSE := by
  simp [evalCovenant, mkH, zk, ha1, ha2]

-- ---------------------------------------------------------------------------
-- CV-HTLCV2-04 : claim path, SHA3-256(preimage) ≠ hash → TX_ERR_SIG_INVALID
-- ---------------------------------------------------------------------------

/-- In the claim path (exactly one matching HTLC_V2 envelope), if the preimage
    hash does not match the committed hash in the covenant, the spend MUST be
    rejected as `TX_ERR_SIG_INVALID` (spec §4.1 item 6, claim path step 2).

    **Pending auxiliary lemma**: the proof requires unfolding the `List.get` proof
    obligation that arises from the single-envelope branch in `evalCovenant`.
    After the auxiliary lemma `evalCovenant_htlcv2_one_matching` is proved, replace
    `sorry` with a call to that lemma followed by `simp [hbad]`. -/
theorem CV_HTLCV2_04_claim_hash_mismatch_reject
    (ctx : BlockCtx) (ch : Nat) (w : Witness) (p32 : Bytes32)
    (anchors : List AnchorEnvelope)
    (hmatch : anchors.filter (fun a => a.tag = AnchorTag.htlcPreimage) =
              [{ tag := AnchorTag.htlcPreimage, preimage32 := p32 }])
    (hbad : SHA3_256 p32 ≠ (zk 0xcc)) :
    let h := mkH (zk 0xcc) (zk 0x55) (zk 0x66)
    evalCovenant ctx ch 0 none anchors w (CovenantType.CORE_HTLC_V2 h)
      = Except.error TxErr.TX_ERR_SIG_INVALID := by
  simp only [evalCovenant, mkH, zk]
  simp only [hmatch, List.length_cons, List.length_nil, List.head?]
  simp [hbad]

-- ---------------------------------------------------------------------------
-- CV-HTLCV2-05 : claim path, key_id ≠ claim_key_id → TX_ERR_SIG_INVALID
-- ---------------------------------------------------------------------------

/-- In the claim path, if the witness key does not match `claim_key_id`,
    the spend MUST be rejected as `TX_ERR_SIG_INVALID`, even when the preimage
    hash is correct (spec §4.1 item 6, claim path step 3).

    **Same auxiliary lemma dependency as CV-04.** -/
theorem CV_HTLCV2_05_claim_key_mismatch_reject
    (ctx : BlockCtx) (ch : Nat) (p32 : Bytes32)
    (anchors : List AnchorEnvelope)
    (hmatch : anchors.filter (fun a => a.tag = AnchorTag.htlcPreimage) =
              [{ tag := AnchorTag.htlcPreimage, preimage32 := p32 }])
    (hhash : SHA3_256 p32 = zk 0xdd)
    (hkey  : (zk 0x77) ≠ (zk 0x55)) :
    -- Witness key_id = 0x77, claim_key_id = 0x55 → mismatch
    let h := mkH (zk 0xdd) (zk 0x55) (zk 0x66)
    let w := mkW (zk 0x77)
    evalCovenant ctx ch 0 none anchors w (CovenantType.CORE_HTLC_V2 h)
      = Except.error TxErr.TX_ERR_SIG_INVALID := by
  simp only [evalCovenant, mkH, mkW, zk]
  simp only [hmatch, List.length_cons, List.length_nil, List.head?]
  simp [hhash, hkey]

-- ---------------------------------------------------------------------------
-- CV-HTLCV2-06 : refund path, key_id ≠ refund_key_id → TX_ERR_SIG_INVALID
-- ---------------------------------------------------------------------------

/-- In the refund path (no matching HTLC_V2 envelopes), if the witness key
    does not match `refund_key_id`, the spend MUST be rejected as
    `TX_ERR_SIG_INVALID` (spec §4.1 item 6, refund path step 1).

    We use an empty anchor list so that `matching = []` trivially. -/
theorem CV_HTLCV2_06_refund_key_mismatch_reject (ctx : BlockCtx) (ch : Nat) :
    let h := mkH (zk 0xee) (zk 0x11) (zk 0x22)
    -- Witness key_id = 0x33 ≠ refund_key_id = 0x22
    let w := mkW (zk 0x33)
    evalCovenant ctx ch 0 none [] w (CovenantType.CORE_HTLC_V2 h)
      = Except.error TxErr.TX_ERR_SIG_INVALID := by
  simp [evalCovenant, mkH, zk]

-- ---------------------------------------------------------------------------
-- CV-HTLCV2-07 : refund path, timelock not met → TX_ERR_TIMELOCK_NOT_MET
-- ---------------------------------------------------------------------------

/-- In the refund path with the correct key, if the height-based timelock has
    not yet been reached, the spend MUST be rejected as `TX_ERR_TIMELOCK_NOT_MET`
    (spec §4.1 item 6, refund path step 3).

    `earlyCtx` has `height = 50`; the covenant's `lock_value = 100`. -/
theorem CV_HTLCV2_07_refund_timelock_not_met :
    let h := mkH (zk 0xff) (zk 0x11) (zk 0x22)
    -- Witness key_id matches refund_key_id (0x22)
    let w := mkW (zk 0x22)
    -- earlyCtx.height = 50 < lock_value = 100
    evalCovenant earlyCtx 0 0 none [] w (CovenantType.CORE_HTLC_V2 h)
      = Except.error TxErr.TX_ERR_TIMELOCK_NOT_MET := by
  simp [evalCovenant, mkH, zk, timelockOk, earlyCtx]

-- ---------------------------------------------------------------------------
-- CV-HTLCV2-08 : claim_key_id = refund_key_id → TX_ERR_PARSE
-- ---------------------------------------------------------------------------

/-- A `CORE_HTLC_V2` covenant with equal `claim_key_id` and `refund_key_id` is
    malformed and MUST be rejected as `TX_ERR_PARSE`
    (spec §3.6: "claim_key_id ≠ refund_key_id MUST be enforced").

    This check fires unconditionally in `evalCovenant` before any envelope scan. -/
theorem CV_HTLCV2_08_equal_key_ids_reject
    (ctx : BlockCtx) (ch : Nat) (w : Witness)
    (anchors : List AnchorEnvelope) (sigOk : SigOk) :
    -- Both key IDs are 0x99 → equal
    let h := mkH (zk 0x00) (zk 0x99) (zk 0x99)
    evalCovenant ctx ch 0 none anchors w (CovenantType.CORE_HTLC_V2 h)
      = Except.error TxErr.TX_ERR_PARSE := by
  simp [evalCovenant, mkH, zk]

end RubinFormal
