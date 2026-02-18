import RubinFormal.Covenant

namespace RubinFormal

def AllOther (xs : List AnchorEnvelope) : Prop :=
  xs.Forall (fun a => a.tag = AnchorTag.other)

theorem filter_htlcPreimage_of_allOther (xs : List AnchorEnvelope) (h : AllOther xs) :
    xs.filter (fun a => a.tag = AnchorTag.htlcPreimage) = [] := by
  induction xs with
  | nil =>
      simp
  | cons a rest ih =>
      have ha : a.tag = AnchorTag.other := by
        simpa [AllOther] using h.1
      have hr : AllOther rest := by
        simpa [AllOther] using h.2
      simp [ha, ih hr]

-- T-009 core: non-matching ANCHOR envelopes do not affect HTLC_V2 evaluation.
theorem T009_htlc_v2_nonmatching_anchors_irrelevant
    (ctx : BlockCtx)
    (creation_height : Nat)
    (script_sig_len : Nat)
    (script_sig_preimage32 : Option Bytes32)
    (w : Witness)
    (h : HTLCV2)
    (anchors extra : List AnchorEnvelope)
    (hextra : AllOther extra)
    (hssl : script_sig_len = 0) :
    evalCovenant ctx creation_height script_sig_len script_sig_preimage32 (anchors ++ extra) w
        (CovenantType.CORE_HTLC_V2 h)
      =
    evalCovenant ctx creation_height script_sig_len script_sig_preimage32 anchors w
        (CovenantType.CORE_HTLC_V2 h) := by
  simp [evalCovenant, hssl, List.filter_append, filter_htlcPreimage_of_allOther _ hextra]

-- T-009 core: two or more matching envelopes MUST reject as TX_ERR_PARSE.
theorem T009_htlc_v2_two_or_more_matching_reject_parse
    (ctx : BlockCtx)
    (creation_height : Nat)
    (w : Witness)
    (h : HTLCV2)
    (anchors : List AnchorEnvelope)
    (hneq : h.claim_key_id ≠ h.refund_key_id)
    (hge : (anchors.filter (fun a => a.tag = AnchorTag.htlcPreimage)).length ≥ 2) :
    evalCovenant ctx creation_height 0 none anchors w (CovenantType.CORE_HTLC_V2 h)
      =
    Except.error TxErr.TX_ERR_PARSE := by
  simp [evalCovenant, hneq, hge]

-- T-011: VAULT owner-path spend_delay monotonicity (if satisfied at a height, it remains satisfied later).
theorem T011_vault_owner_spend_delay_monotone
    (v : VaultV1)
    (w : Witness)
    (creation_height : Nat)
    (h1 h2 ts1 ts2 : Nat)
    (hneq : v.owner_key_id ≠ v.recovery_key_id)
    (hkid : w.key_id = v.owner_key_id)
    (hpos : v.spend_delay > 0)
    (h1ok : h1 ≥ creation_height + v.spend_delay)
    (hle : h1 ≤ h2) :
    evalCovenant { height := h2, timestamp := ts2 } creation_height 0 none [] w
        (CovenantType.CORE_VAULT_V1 v)
      =
    Except.ok () := by
  have h2ok : h2 ≥ creation_height + v.spend_delay := by
    exact Nat.le_trans (show creation_height + v.spend_delay ≤ h1 from h1ok) hle
  -- Force the owner path and discharge the spend_delay branch.
  simp [evalCovenant, hneq, hkid, hpos.ne', h2ok]

end RubinFormal

