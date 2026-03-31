import RubinFormal.TxWireDaCoreContract

set_option maxHeartbeats 50000000
set_option maxRecDepth 8192

namespace RubinFormal

open Wire

namespace UtxoBasicV1

private theorem bytes_append_empty (bs : Bytes) : bs = bs ++ ByteArray.empty := by
  cases bs
  rename_i data
  ext; all_goals simp [ByteArray.append, ByteArray.empty, Array.append_assoc]

theorem parseTxFinalize_after_pre
    (pre : Bytes)
    (tx : Tx)
    (h : txStructurallyWellFormed tx) :
    let payloadCountBytes : Bytes := RubinFormal.WireEnc.compactSize tx.daPayloadLen
    parseTxFinalize
        (pre ++ payloadCountBytes ++ tx.daPayload)
        tx.version tx.txKind tx.txNonce tx.inputs tx.outputs tx.locktime tx.daCoreBytes tx.witness
        { bs := pre ++ payloadCountBytes ++ tx.daPayload,
          off := pre.size } =
      Except.ok tx := by
  rcases h with
    ⟨_, _, _, _, _, _, _, _, _, _, _, hDaLenEq, hDaLenBound, hKind0Payload⟩
  let payloadCountBytes : Bytes := RubinFormal.WireEnc.compactSize tx.daPayloadLen
  have hPayloadLenRead :
      Cursor.getCompactSize? { bs := pre ++ payloadCountBytes ++ tx.daPayload, off := pre.size } =
        some
          (tx.daPayloadLen,
            { bs := pre ++ payloadCountBytes ++ tx.daPayload, off := pre.size + payloadCountBytes.size },
            true) := by
    have h_raw := cursor_getCompactSize_after_pre
        (pre := pre)
        (rest := tx.daPayload)
        (n := tx.daPayloadLen)
        hDaLenBound
    simp only [payloadCountBytes, Nat.add_assoc] at h_raw ⊢
    exact h_raw
  have hPayloadRead :
      Cursor.getBytes?
          { bs := pre ++ payloadCountBytes ++ tx.daPayload, off := pre.size + payloadCountBytes.size }
          tx.daPayloadLen =
        some
          (tx.daPayload,
            { bs := pre ++ payloadCountBytes ++ tx.daPayload,
              off := pre.size + payloadCountBytes.size + tx.daPayload.size }) := by
    rw [bytes_append_empty (pre ++ payloadCountBytes ++ tx.daPayload)]
    have h_raw := cursor_getBytes_after_pre_exact
        (pre := pre ++ payloadCountBytes)
        (mid := tx.daPayload)
        (post := ByteArray.empty)
        (n := tx.daPayload.size)
        (by rfl)
    simp only [payloadCountBytes, hDaLenEq, ByteArray.size_append, Nat.add_assoc] at h_raw ⊢
    exact h_raw
  have hKind0PayloadProp : ¬ (tx.txKind = 0x00 ∧ tx.daPayload.size ≠ 0) := by
    rcases hKind0Payload with hNot0 | hZero
    · intro hk
      exact hNot0 hk.1
    · intro hk
      exact hk.2 (by simp only [hDaLenEq] at hZero ⊢; exact hZero)
  have hKind0PayloadPropLen : ¬ (tx.txKind = 0x00 ∧ tx.daPayloadLen ≠ 0) := by
    rcases hKind0Payload with hNot0 | hZero
    · intro hk
      exact hNot0 hk.1
    · intro hk
      exact hk.2 hZero
  have hBodySize' :
      pre.size + payloadCountBytes.size + tx.daPayload.size =
        (pre ++ payloadCountBytes ++ tx.daPayload).size := by
    simp only [ByteArray.size_append, Nat.add_assoc]
  have hPayloadLenRead' := hPayloadLenRead
  have hPayloadRead' := hPayloadRead
  unfold parseTxFinalize
  dsimp [payloadCountBytes] at hPayloadLenRead' hPayloadRead' ⊢
  rw [hPayloadLenRead']
  simp
  rw [hPayloadRead']
  simp
  have hOffEq :
      ByteArray.size pre +
          (ByteArray.size (RubinFormal.WireEnc.compactSize (ByteArray.size tx.daPayload)) + ByteArray.size tx.daPayload) =
        ByteArray.size (pre ++ RubinFormal.WireEnc.compactSize (ByteArray.size tx.daPayload) ++ tx.daPayload) := by
    simp only [payloadCountBytes, hDaLenEq, Nat.add_assoc] at hBodySize' ⊢
    exact hBodySize'
  have hOffEq' :
      ByteArray.size pre + ByteArray.size (RubinFormal.WireEnc.compactSize (ByteArray.size tx.daPayload)) +
          ByteArray.size tx.daPayload =
        ByteArray.size (pre ++ RubinFormal.WireEnc.compactSize (ByteArray.size tx.daPayload) ++ tx.daPayload) := by
    simp only [Nat.add_assoc] at hOffEq ⊢
    exact hOffEq
  have hOffEqLen :
      ByteArray.size pre + ByteArray.size (RubinFormal.WireEnc.compactSize tx.daPayloadLen) + ByteArray.size tx.daPayload =
        ByteArray.size (pre ++ RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload) := by
    simp only [hDaLenEq] at hOffEq' ⊢
    exact hOffEq'
  rw [if_pos hOffEqLen]
  simp [hDaLenEq, hKind0PayloadProp, hKind0PayloadPropLen]
  have hDaLenEq' : ByteArray.size tx.daPayload = tx.daPayloadLen := hDaLenEq.symm
  rw [hDaLenEq']
  rfl

end UtxoBasicV1

end RubinFormal
