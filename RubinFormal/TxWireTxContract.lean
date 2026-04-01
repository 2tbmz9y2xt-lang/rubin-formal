import RubinFormal.TxWireTxBodyContract

set_option maxHeartbeats 50000000
set_option maxRecDepth 8192

namespace RubinFormal

open Wire

namespace UtxoBasicV1

private theorem txKind_lt_256
    (txKind : Nat)
    (hKind : txKind = 0x00 ∨ txKind = 0x01 ∨ txKind = 0x02) :
    txKind < 256 := by
  rcases hKind with rfl | h1 | h2
  · decide
  · rcases h1 with rfl
    decide
  · rcases h2 with rfl
    decide

private theorem txKind_bool_true
    (txKind : Nat)
    (hKind : txKind = 0x00 ∨ txKind = 0x01 ∨ txKind = 0x02) :
    (txKind == 0x00 || txKind == 0x01 || txKind == 0x02) = true := by
  rcases hKind with rfl | h1 | h2
  · simp
  · rcases h1 with rfl
    simp
  · rcases h2 with rfl
    simp

private theorem wire_u32le_size (n : Nat) : (RubinFormal.WireEnc.u32le n).size = 4 := rfl

private theorem wire_u64le_size (n : Nat) : (RubinFormal.WireEnc.u64le n).size = 8 := rfl

private theorem bytes_append_empty_right (bs : Bytes) : bs ++ ByteArray.empty = bs := by
  cases bs; rename_i data
  ext; all_goals simp [ByteArray.append, ByteArray.empty, Array.append_assoc]

private theorem extract_suffix_exact
    (pre mid : Bytes) :
    (pre ++ mid).extract pre.size (pre ++ mid).size = mid := by
  have h := extract_after_pre_exact pre mid ByteArray.empty
  rw [bytes_append_empty_right (pre ++ mid)] at h
  rw [ByteArray.size_append]
  exact h

theorem parseTx_serializeTx_roundtrip
    (tx : Tx)
    (h : txStructurallyWellFormed tx) :
    parseTx (serializeTx tx) = Except.ok tx := by
  have h_wf := h
  rcases h with
    ⟨hVer, hKind, hNonce, _, _, _, _, _, _, _, _, _, _, _⟩
  let kindBytes : Bytes := RubinFormal.bytes #[UInt8.ofNat tx.txKind]
  have hKindBool : (tx.txKind == 0x00 || tx.txKind == 0x01 || tx.txKind == 0x02) = true :=
    txKind_bool_true tx.txKind hKind
  have hKindNat : (UInt8.ofNat tx.txKind).toNat = tx.txKind := by
    have hKindLt : tx.txKind < 256 := txKind_lt_256 tx.txKind hKind
    simp [UInt8.ofNat, UInt8.toNat, Fin.ofNat, Nat.mod_eq_of_lt hKindLt]
  have hNonceLt : tx.txNonce < UInt64.size :=
    Nat.lt_of_le_of_lt hNonce (by decide)
  have hNonceNat : (UInt64.ofNat tx.txNonce).toNat = tx.txNonce := by
    simp [UInt64.ofNat, UInt64.toNat, Fin.ofNat, Nat.mod_eq_of_lt hNonceLt]
  have hHeaderSize :
      (RubinFormal.WireEnc.u32le tx.version ++ kindBytes ++ RubinFormal.WireEnc.u64le tx.txNonce).size = 13 := by
    have hKindSize : kindBytes.size = 1 := by
      simp only [kindBytes, bytes, ByteArray.size, Array.size]
      rfl
    rw [ByteArray.size_append, ByteArray.size_append, wire_u32le_size, hKindSize, wire_u64le_size]
  have hVerRead :
      ({ bs := serializeTx tx, off := 0 } : Cursor).getU32le? =
        some (tx.version, { bs := serializeTx tx, off := 4 }) := by
    have h_raw := cursor_getU32le_prefix tx.version
      (kindBytes ++ RubinFormal.WireEnc.u64le tx.txNonce ++ serializeTxAfterNonce tx) hVer
    simp only [serializeTx, kindBytes, cursor_bytes_left_assoc, Nat.add_assoc] at h_raw ⊢
    exact h_raw
  have hKindRead :
      Cursor.getU8? { bs := serializeTx tx, off := 4 } =
        some (UInt8.ofNat tx.txKind, { bs := serializeTx tx, off := 5 }) := by
    have h_raw := cursor_getU8_after_pre_exact
        (pre := RubinFormal.WireEnc.u32le tx.version)
        (post := RubinFormal.WireEnc.u64le tx.txNonce ++ serializeTxAfterNonce tx)
        (b := UInt8.ofNat tx.txKind)
    simp only [serializeTx, kindBytes, cursor_bytes_left_assoc, Nat.add_assoc] at h_raw ⊢
    exact h_raw
  have hNonceRead :
      Cursor.getU64le? { bs := serializeTx tx, off := 5 } =
        some (UInt64.ofNat tx.txNonce, { bs := serializeTx tx, off := 13 }) := by
    have h_raw := cursor_getU64le_after_pre
        (pre := RubinFormal.WireEnc.u32le tx.version ++ kindBytes)
        (rest := serializeTxAfterNonce tx)
        (n := tx.txNonce)
        hNonce
    simp only [serializeTx, kindBytes, cursor_bytes_left_assoc, Nat.add_assoc] at h_raw ⊢
    exact h_raw
  have hBodyExtract :
      (serializeTx tx).extract 13 (serializeTx tx).size = serializeTxAfterNonce tx := by
    rw [show
        serializeTx tx =
          (RubinFormal.WireEnc.u32le tx.version ++ kindBytes ++ RubinFormal.WireEnc.u64le tx.txNonce) ++
            serializeTxAfterNonce tx by
        simp [serializeTx, kindBytes, Nat.add_assoc]]
    have h_raw := extract_suffix_exact
        (pre := RubinFormal.WireEnc.u32le tx.version ++ kindBytes ++ RubinFormal.WireEnc.u64le tx.txNonce)
        (mid := serializeTxAfterNonce tx)
    simp only [hHeaderSize, ByteArray.size_append, Nat.add_assoc] at h_raw ⊢
    exact h_raw
  have hAfterNonce :
      parseTxAfterNonce (serializeTxAfterNonce tx) tx.version tx.txKind tx.txNonce
          { bs := serializeTxAfterNonce tx, off := 0 } =
        Except.ok tx :=
    parseTxAfterNonce_serializeTx_roundtrip tx h_wf
  unfold parseTx
  dsimp only
  rw [hVerRead]
  simp
  rw [hKindRead]
  simp [hKindNat, hKindBool]
  rw [hNonceRead]
  simp [hNonceNat, hKindNat, hBodyExtract, hAfterNonce]

end UtxoBasicV1

end RubinFormal
