import RubinFormal.TxWireTxAfterLockStep
import RubinFormal.TxWirePrefixLemmas
import RubinFormal.TxWireTxAfterDaCoreContract

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

namespace RubinFormal

open Wire

namespace UtxoBasicV1

theorem parseTxAfterLock_of_afterDaCore_ok
    (txBytes : Bytes)
    (ver tk nonce : Nat)
    (ins : List TxIn)
    (outs : List TxOut)
    (lock : Nat)
    (daCoreBytes : Bytes)
    (c8 c9 : Cursor)
    (txVal : Tx)
    (hStep :
      parseTxAfterLock txBytes ver tk nonce ins outs lock c8 =
        parseTxAfterDaCore txBytes ver tk nonce ins outs lock daCoreBytes c9)
    (hOk :
      parseTxAfterDaCore txBytes ver tk nonce ins outs lock daCoreBytes c9 =
        Except.ok txVal) :
    parseTxAfterLock txBytes ver tk nonce ins outs lock c8 = Except.ok txVal := by
  rw [hStep, hOk]

theorem parseTxAfterLock_after_pre
    (pre : Bytes)
    (tx : Tx)
    (h : txStructurallyWellFormed tx) :
    let pre' : Bytes := pre ++ tx.daCoreBytes
    let payloadCountBytes : Bytes := RubinFormal.WireEnc.compactSize tx.daPayloadLen
    let post : Bytes := serializeWitness tx.witness ++ payloadCountBytes ++ tx.daPayload
    let txBytes : Bytes := pre' ++ post
    parseTxAfterLock
        txBytes
        tx.version tx.txKind tx.txNonce tx.inputs tx.outputs tx.locktime
        { bs := txBytes,
          off := pre.size } =
      Except.ok tx := by
  let pre' : Bytes := pre ++ tx.daCoreBytes
  let payloadCountBytes : Bytes := RubinFormal.WireEnc.compactSize tx.daPayloadLen
  let post : Bytes := serializeWitness tx.witness ++ payloadCountBytes ++ tx.daPayload
  let txBytes : Bytes := pre' ++ post
  have hStep :
      parseTxAfterLock
          txBytes
          tx.version tx.txKind tx.txNonce tx.inputs tx.outputs tx.locktime
          { bs := txBytes, off := pre.size } =
        parseTxAfterDaCore
          txBytes
          tx.version tx.txKind tx.txNonce tx.inputs tx.outputs tx.locktime tx.daCoreBytes
          { bs := txBytes, off := pre'.size } := by
    exact parseTxAfterLock_after_pre_step (pre := pre) (tx := tx) h
  have hBytes :
      txBytes =
        pre' ++ serializeWitness tx.witness ++
          (RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload) := by
    simp only [txBytes, post, cursor_bytes_left_assoc]
  have hAfterDaCore :
      parseTxAfterDaCore
          txBytes
          tx.version tx.txKind tx.txNonce tx.inputs tx.outputs tx.locktime tx.daCoreBytes
          { bs := txBytes,
            off := pre'.size } =
        Except.ok tx := by
    rw [hBytes]
    exact parseTxAfterDaCore_after_pre (pre := pre') (tx := tx) h
  exact
    parseTxAfterLock_of_afterDaCore_ok
      (txBytes := txBytes)
      (ver := tx.version)
      (tk := tx.txKind)
      (nonce := tx.txNonce)
      (ins := tx.inputs)
      (outs := tx.outputs)
      (lock := tx.locktime)
      (daCoreBytes := tx.daCoreBytes)
      (c8 := { bs := txBytes, off := pre.size })
      (c9 := { bs := txBytes, off := pre'.size })
      (txVal := tx)
      hStep
      hAfterDaCore

end UtxoBasicV1

end RubinFormal
