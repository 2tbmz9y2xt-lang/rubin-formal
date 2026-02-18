import RubinFormal.Covenant

namespace RubinFormal

-- These examples are designed to align with conformance vectors conceptually.
-- They do not parse YAML; instead, they prove the consensus decision for a semantic case.

def kid (b : UInt8) : Bytes32 := List.replicate 32 b

-- CV-VAULT VAULT-02 style: recovery spends before timelock => TIMELOCK_NOT_MET.
theorem ex_vault_recovery_timelock_not_met :
    let ctx : BlockCtx := { height := 999, timestamp := 1700000999 }
    let v : VaultV1 :=
      { owner_key_id := kid 0x44
        spend_delay := 0
        lock_mode := LockMode.height
        lock_value := 1000
        recovery_key_id := kid 0x55 }
    let w : Witness := { suite_id := 0x01, key_id := kid 0x55, isSentinel := false }
    evalCovenant ctx 0 0 none [] w (CovenantType.CORE_VAULT_V1 v) = Except.error TxErr.TX_ERR_TIMELOCK_NOT_MET := by
  simp [evalCovenant, timelockOk, kid]

-- CV-HTLC HTLC-06 style: 2 matching envelopes => TX_ERR_PARSE.
theorem ex_htlc_v2_two_matching_anchors :
    let ctx : BlockCtx := { height := 600, timestamp := 1700000600 }
    let h : HTLCV2 :=
      { hash := kid 0xaa
        lock_mode := LockMode.height
        lock_value := 500
        claim_key_id := kid 0x22
        refund_key_id := kid 0x33 }
    let a1 : AnchorEnvelope := { tag := AnchorTag.htlcPreimage, preimage32 := kid 0x11 }
    let a2 : AnchorEnvelope := { tag := AnchorTag.htlcPreimage, preimage32 := kid 0x11 }
    let w : Witness := { suite_id := 0x01, key_id := kid 0x22, isSentinel := false }
    evalCovenant ctx 0 0 none [a1, a2] w (CovenantType.CORE_HTLC_V2 h) = Except.error TxErr.TX_ERR_PARSE := by
  simp [evalCovenant, kid]

end RubinFormal

