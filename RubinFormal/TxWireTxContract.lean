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

private theorem extract_suffix_exact
    (pre mid : Bytes) :
    (pre ++ mid).extract pre.size (pre ++ mid).size = mid := by
  have h :
      Cursor.getBytes? { bs := pre ++ mid, off := pre.size } mid.size =
        some (mid, { bs := pre ++ mid, off := pre.size + mid.size }) := by
    exact
      cursor_getBytes_after_pre_exact
        (pre := pre)
        (mid := mid)
        (post := ByteArray.empty)
        (n := mid.size)
        (by rfl)
  simp [Cursor.getBytes?, ByteArray.extract, ByteArray.copySlice, ByteArray.size] at h
  rcases h with ⟨_, hEq⟩
  change ({ data := Array.extract (pre.data ++ mid.data) pre.data.size (pre.data.size + (pre.data.size + mid.data.size - pre.data.size)) } : Bytes) = mid
  exact hEq

theorem parseTx_serializeTx_roundtrip
    (tx : Tx)
    (h : txStructurallyWellFormed tx) :
    parseTx (serializeTx tx) = Except.ok tx := by
  rcases h with
    ⟨hVer, hKind, hNonce, _, _, _, _, _, _, _, _, _, _, _⟩
  let kindBytes : Bytes := RubinFormal.bytes #[UInt8.ofNat tx.txKind]
  have hKindBool : (tx.txKind == 0x00 || tx.txKind == 0x01 || tx.txKind == 0x02) = true :=
    txKind_bool_true tx.txKind hKind
  have hNonceLt : tx.txNonce < UInt64.size := by
    omega
  have hNonceNat : (UInt64.ofNat tx.txNonce).toNat = tx.txNonce := by
    simp [UInt64.ofNat, UInt64.toNat, Fin.ofNat, Nat.mod_eq_of_lt hNonceLt]
  have hHeaderSize :
      (RubinFormal.WireEnc.u32le tx.version ++ kindBytes ++ RubinFormal.WireEnc.u64le tx.txNonce).size = 13 := by
    have hKindLt : tx.txKind < 256 := txKind_lt_256 tx.txKind hKind
    have hKindSize : kindBytes.size = 1 := by
      simp [kindBytes]
    rw [show kindBytes.size = 1 by exact hKindSize]
    rw [ByteArray.size_append, ByteArray.size_append, wire_u32le_size, wire_u64le_size]
  have hVerRead :
      ({ bs := serializeTx tx, off := 0 } : Cursor).getU32le? =
        some (tx.version, { bs := serializeTx tx, off := 4 }) := by
    simpa [serializeTx, kindBytes, Nat.add_assoc] using
      (cursor_getU32le_prefix tx.version (kindBytes ++ RubinFormal.WireEnc.u64le tx.txNonce ++ serializeTxAfterNonce tx) hVer)
  have hKindRead :
      Cursor.getU8? { bs := serializeTx tx, off := 4 } =
        some (UInt8.ofNat tx.txKind, { bs := serializeTx tx, off := 5 }) := by
    simpa [serializeTx, kindBytes, cursor_bytes_left_assoc, Nat.add_assoc] using
      (cursor_getU8_after_pre_exact
        (pre := RubinFormal.WireEnc.u32le tx.version)
        (post := RubinFormal.WireEnc.u64le tx.txNonce ++ serializeTxAfterNonce tx)
        (b := UInt8.ofNat tx.txKind))
  have hNonceRead :
      Cursor.getU64le? { bs := serializeTx tx, off := 5 } =
        some (UInt64.ofNat tx.txNonce, { bs := serializeTx tx, off := 13 }) := by
    simpa [serializeTx, kindBytes, cursor_bytes_left_assoc, Nat.add_assoc] using
      (cursor_getU64le_after_pre
        (pre := RubinFormal.WireEnc.u32le tx.version ++ kindBytes)
        (rest := serializeTxAfterNonce tx)
        (n := tx.txNonce)
        hNonce)
  have hBodyExtract :
      (serializeTx tx).extract 13 (serializeTx tx).size = serializeTxAfterNonce tx := by
    rw [show
        serializeTx tx =
          (RubinFormal.WireEnc.u32le tx.version ++ kindBytes ++ RubinFormal.WireEnc.u64le tx.txNonce) ++
            serializeTxAfterNonce tx by
        simp [serializeTx, kindBytes, Nat.add_assoc]]
    simpa [hHeaderSize, ByteArray.size_append, Nat.add_assoc] using
      (extract_suffix_exact
        (pre := RubinFormal.WireEnc.u32le tx.version ++ kindBytes ++ RubinFormal.WireEnc.u64le tx.txNonce)
        (mid := serializeTxAfterNonce tx))
  have hAfterNonce :
      parseTxAfterNonce (serializeTxAfterNonce tx) tx.version tx.txKind tx.txNonce
          { bs := serializeTxAfterNonce tx, off := 0 } =
        Except.ok tx :=
    parseTxAfterNonce_serializeTx_roundtrip tx h
  unfold parseTx
  rw [hVerRead]
  simp
  rw [hKindRead]
  simp [hKindBool]
  rw [hNonceRead]
  simp [hNonceNat, hBodyExtract, hAfterNonce]

end UtxoBasicV1

end RubinFormal
