import RubinFormal.TxWireTxAfterLockStep
import RubinFormal.TxWirePrefixLemmas
import RubinFormal.TxWireTxAfterDaCoreContract

set_option maxHeartbeats 50000000
set_option maxRecDepth 8192

namespace RubinFormal

open Wire

namespace UtxoBasicV1

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
    simpa [post, txBytes] using
      (cursor_bytes_left_assoc
        (a := pre')
        (b := serializeWitness tx.witness)
        (c := RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload)).symm
  have hAfterDaCore :
      parseTxAfterDaCore
          txBytes
          tx.version tx.txKind tx.txNonce tx.inputs tx.outputs tx.locktime tx.daCoreBytes
          { bs := txBytes,
            off := pre'.size } =
        Except.ok tx := by
    rw [hBytes]
    exact parseTxAfterDaCore_after_pre (pre := pre') (tx := tx) h
  rw [hStep, hAfterDaCore]

end UtxoBasicV1

end RubinFormal
