import RubinFormal.TxWireTxFinalizeContract

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace RubinFormal

open Wire

namespace UtxoBasicV1

private theorem parseTxAfterOutputs_after_pre
    (pre : Bytes)
    (tx : Tx)
    (h : txStructurallyWellFormed tx) :
    parseTxAfterOutputs
        (pre ++ RubinFormal.WireEnc.u32le tx.locktime ++ tx.daCoreBytes ++
          serializeWitness tx.witness ++ RubinFormal.WireEnc.compactSize tx.daPayloadLen ++
          tx.daPayload)
        tx.version tx.txKind tx.txNonce tx.inputs tx.outputs
        { bs := pre ++ RubinFormal.WireEnc.u32le tx.locktime ++ tx.daCoreBytes ++
            serializeWitness tx.witness ++ RubinFormal.WireEnc.compactSize tx.daPayloadLen ++
            tx.daPayload,
          off := pre.size } =
      Except.ok tx := by
  have hLock := h.2.2.2.2.2.2.2.1
  let postLock : Bytes :=
    tx.daCoreBytes ++ serializeWitness tx.witness ++ RubinFormal.WireEnc.compactSize tx.daPayloadLen ++
      tx.daPayload
  have hLockRead :
      Cursor.getU32le?
          { bs := pre ++ RubinFormal.WireEnc.u32le tx.locktime ++ postLock, off := pre.size } =
        some
          (tx.locktime,
            { bs := pre ++ RubinFormal.WireEnc.u32le tx.locktime ++ postLock, off := pre.size + 4 }) := by
    simpa [postLock, Nat.add_assoc] using
      (cursor_getU32le_after_pre
        (pre := pre)
        (rest := postLock)
        (n := tx.locktime)
        hLock)
  have hAfterLock :
      parseTxAfterLock
          ((pre ++ RubinFormal.WireEnc.u32le tx.locktime) ++ tx.daCoreBytes ++
            serializeWitness tx.witness ++ RubinFormal.WireEnc.compactSize tx.daPayloadLen ++
            tx.daPayload)
          tx.version tx.txKind tx.txNonce tx.inputs tx.outputs tx.locktime
          { bs := (pre ++ RubinFormal.WireEnc.u32le tx.locktime) ++ tx.daCoreBytes ++
              serializeWitness tx.witness ++ RubinFormal.WireEnc.compactSize tx.daPayloadLen ++
              tx.daPayload,
            off := (pre ++ RubinFormal.WireEnc.u32le tx.locktime).size } =
        Except.ok tx := by
    have h_raw := parseTxAfterLock_after_pre (pre := pre ++ RubinFormal.WireEnc.u32le tx.locktime) tx h
    simp only [← cursor_bytes_left_assoc] at h_raw
    exact h_raw
  unfold parseTxAfterOutputs
  simp only [postLock, ← cursor_bytes_left_assoc] at hLockRead
  rw [hLockRead]
  simpa [postLock, ByteArray.size_append, Nat.add_assoc] using hAfterLock

private theorem parseTxAfterInputs_after_pre
    (pre : Bytes)
    (tx : Tx)
    (h : txStructurallyWellFormed tx) :
    parseTxAfterInputs
        (pre ++ RubinFormal.WireEnc.compactSize tx.outputs.length ++ serializeOutputs tx.outputs ++
          RubinFormal.WireEnc.u32le tx.locktime ++ tx.daCoreBytes ++ serializeWitness tx.witness ++
          RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload)
        tx.version tx.txKind tx.txNonce tx.inputs
        { bs := pre ++ RubinFormal.WireEnc.compactSize tx.outputs.length ++ serializeOutputs tx.outputs ++
            RubinFormal.WireEnc.u32le tx.locktime ++ tx.daCoreBytes ++ serializeWitness tx.witness ++
            RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload,
          off := pre.size } =
      Except.ok tx := by
  have hOutputsWF := h.2.2.2.2.2.1
  have hOutputsLen := h.2.2.2.2.2.2.1
  let outCountBytes : Bytes := RubinFormal.WireEnc.compactSize tx.outputs.length
  let postOutCount : Bytes :=
    serializeOutputs tx.outputs ++ RubinFormal.WireEnc.u32le tx.locktime ++ tx.daCoreBytes ++
      serializeWitness tx.witness ++ RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload
  have hOutCountRead :
      Cursor.getCompactSize?
          { bs := pre ++ outCountBytes ++ postOutCount, off := pre.size } =
        some
          (tx.outputs.length,
            { bs := pre ++ outCountBytes ++ postOutCount, off := pre.size + outCountBytes.size },
            true) := by
    simpa [outCountBytes, postOutCount, Nat.add_assoc] using
      (cursor_getCompactSize_after_pre
        (pre := pre)
        (rest := postOutCount)
        (n := tx.outputs.length)
        hOutputsLen)
  have hOutputsRead :
      parseOutputs
          { bs := pre ++ outCountBytes ++ postOutCount, off := pre.size + outCountBytes.size }
          tx.outputs.length =
        some
          (tx.outputs,
            { bs := pre ++ outCountBytes ++ postOutCount,
              off := pre.size + outCountBytes.size + (serializeOutputs tx.outputs).size }) := by
    have h_raw := (parseOutputs_serializeOutputs_between
        (pre := pre ++ outCountBytes)
        (outs := tx.outputs)
        (post := RubinFormal.WireEnc.u32le tx.locktime ++ tx.daCoreBytes ++ serializeWitness tx.witness ++
          RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload)
        hOutputsWF)
    simp only [outCountBytes, postOutCount, ← cursor_bytes_left_assoc, ByteArray.size_append, Nat.add_assoc] at h_raw ⊢
    exact h_raw
  have hAfterOutputs :
      parseTxAfterOutputs
          ((pre ++ outCountBytes) ++ serializeOutputs tx.outputs ++ RubinFormal.WireEnc.u32le tx.locktime ++
            tx.daCoreBytes ++ serializeWitness tx.witness ++ RubinFormal.WireEnc.compactSize tx.daPayloadLen ++
            tx.daPayload)
          tx.version tx.txKind tx.txNonce tx.inputs tx.outputs
          { bs := (pre ++ outCountBytes) ++ serializeOutputs tx.outputs ++ RubinFormal.WireEnc.u32le tx.locktime ++
              tx.daCoreBytes ++ serializeWitness tx.witness ++ RubinFormal.WireEnc.compactSize tx.daPayloadLen ++
              tx.daPayload,
            off := (pre ++ outCountBytes).size + (serializeOutputs tx.outputs).size } =
        Except.ok tx := by
    have h_raw := parseTxAfterOutputs_after_pre (pre := pre ++ outCountBytes ++ serializeOutputs tx.outputs) tx h
    simp only [outCountBytes, ← cursor_bytes_left_assoc, ByteArray.size_append, Nat.add_assoc] at h_raw ⊢
    exact h_raw
  unfold parseTxAfterInputs
  simp only [outCountBytes, postOutCount, ← cursor_bytes_left_assoc] at hOutCountRead
  rw [hOutCountRead]
  simp
  simp only [outCountBytes, postOutCount, ← cursor_bytes_left_assoc, ByteArray.size_append, Nat.add_assoc] at hOutputsRead
  rw [hOutputsRead]
  simpa [outCountBytes, postOutCount, ByteArray.size_append, Nat.add_assoc] using hAfterOutputs

private theorem parseTxAfterNonce_after_pre
    (pre : Bytes)
    (tx : Tx)
    (h : txStructurallyWellFormed tx) :
    parseTxAfterNonce
        (pre ++ serializeTxAfterNonce tx)
        tx.version tx.txKind tx.txNonce
        { bs := pre ++ serializeTxAfterNonce tx, off := pre.size } =
      Except.ok tx := by
  have hInputsWF := h.2.2.2.1
  have hInputsLen := h.2.2.2.2.1
  let inCountBytes : Bytes := RubinFormal.WireEnc.compactSize tx.inputs.length
  let postInCount : Bytes :=
    serializeInputs tx.inputs ++ RubinFormal.WireEnc.compactSize tx.outputs.length ++
      serializeOutputs tx.outputs ++ RubinFormal.WireEnc.u32le tx.locktime ++ tx.daCoreBytes ++
      serializeWitness tx.witness ++ RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload
  have hInCountRead :
      Cursor.getCompactSize?
          { bs := pre ++ inCountBytes ++ postInCount, off := pre.size } =
        some
          (tx.inputs.length,
            { bs := pre ++ inCountBytes ++ postInCount, off := pre.size + inCountBytes.size },
            true) := by
    simpa [inCountBytes, postInCount, serializeTxAfterNonce, Nat.add_assoc] using
      (cursor_getCompactSize_after_pre
        (pre := pre)
        (rest := postInCount)
        (n := tx.inputs.length)
        hInputsLen)
  have hInputsRead :
      parseInputs
          { bs := pre ++ inCountBytes ++ postInCount, off := pre.size + inCountBytes.size }
          tx.inputs.length =
        some
          (tx.inputs,
            { bs := pre ++ inCountBytes ++ postInCount,
              off := pre.size + inCountBytes.size + (serializeInputs tx.inputs).size }) := by
    have h_raw := (parseInputs_serializeInputs_between
        (pre := pre ++ inCountBytes)
        (ins := tx.inputs)
        (post := RubinFormal.WireEnc.compactSize tx.outputs.length ++ serializeOutputs tx.outputs ++
          RubinFormal.WireEnc.u32le tx.locktime ++ tx.daCoreBytes ++ serializeWitness tx.witness ++
          RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload)
        hInputsWF)
    simp only [inCountBytes, postInCount, serializeTxAfterNonce, ← cursor_bytes_left_assoc, ByteArray.size_append, Nat.add_assoc] at h_raw ⊢
    exact h_raw
  have hAfterInputs :
      parseTxAfterInputs
          ((pre ++ inCountBytes) ++ serializeInputs tx.inputs ++ RubinFormal.WireEnc.compactSize tx.outputs.length ++
            serializeOutputs tx.outputs ++ RubinFormal.WireEnc.u32le tx.locktime ++ tx.daCoreBytes ++
            serializeWitness tx.witness ++ RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload)
          tx.version tx.txKind tx.txNonce tx.inputs
          { bs := (pre ++ inCountBytes) ++ serializeInputs tx.inputs ++ RubinFormal.WireEnc.compactSize tx.outputs.length ++
              serializeOutputs tx.outputs ++ RubinFormal.WireEnc.u32le tx.locktime ++ tx.daCoreBytes ++
              serializeWitness tx.witness ++ RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload,
            off := (pre ++ inCountBytes).size + (serializeInputs tx.inputs).size } =
        Except.ok tx := by
    have h_raw := parseTxAfterInputs_after_pre (pre := pre ++ inCountBytes ++ serializeInputs tx.inputs) tx h
    simp only [inCountBytes, ← cursor_bytes_left_assoc, ByteArray.size_append, Nat.add_assoc] at h_raw ⊢
    exact h_raw
  unfold parseTxAfterNonce serializeTxAfterNonce
  simp only [← cursor_bytes_left_assoc]
  simp only [inCountBytes, postInCount, ← cursor_bytes_left_assoc] at hInCountRead
  rw [hInCountRead]
  simp
  simp only [inCountBytes, postInCount, ← cursor_bytes_left_assoc, ByteArray.size_append, Nat.add_assoc] at hInputsRead
  rw [hInputsRead]
  simp only [inCountBytes, postInCount, ← cursor_bytes_left_assoc, ByteArray.size_append, Nat.add_assoc] at hAfterInputs ⊢
  exact hAfterInputs

private theorem bytes_empty_append (bs : Bytes) : ByteArray.empty ++ bs = bs := by
  apply ByteArray.ext
  simp [ByteArray.append_data, ByteArray.empty_data, Array.nil_append]

private theorem bytes_empty_size : ByteArray.empty.size = 0 := rfl

theorem parseTxAfterNonce_serializeTx_roundtrip
    (tx : Tx)
    (h : txStructurallyWellFormed tx) :
    parseTxAfterNonce (serializeTxAfterNonce tx) tx.version tx.txKind tx.txNonce
        { bs := serializeTxAfterNonce tx, off := 0 } =
      Except.ok tx := by
  have h_raw := parseTxAfterNonce_after_pre (pre := ByteArray.empty) tx h
  simp only [bytes_empty_append, bytes_empty_size] at h_raw
  exact h_raw

end UtxoBasicV1

end RubinFormal
