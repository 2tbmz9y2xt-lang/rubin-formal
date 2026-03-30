import RubinFormal.TxWireTxAfterDaCoreStep
import RubinFormal.TxWirePrefixLemmas
import RubinFormal.TxWireTxWithWitnessContract

set_option maxHeartbeats 50000000
set_option maxRecDepth 8192

namespace RubinFormal

open Wire

namespace UtxoBasicV1

theorem parseTxAfterDaCore_after_pre
    (pre : Bytes)
    (tx : Tx)
    (h : txStructurallyWellFormed tx) :
    let post : Bytes := RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload
    let txBytes : Bytes := pre ++ serializeWitness tx.witness ++ post
    parseTxAfterDaCore
        txBytes
        tx.version tx.txKind tx.txNonce tx.inputs tx.outputs tx.locktime tx.daCoreBytes
        { bs := txBytes, off := pre.size } =
      Except.ok tx := by
  let post : Bytes := RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload
  let txBytes : Bytes := pre ++ serializeWitness tx.witness ++ post
  calc
    parseTxAfterDaCore
        txBytes
        tx.version tx.txKind tx.txNonce tx.inputs tx.outputs tx.locktime tx.daCoreBytes
        { bs := txBytes, off := pre.size }
      =
        parseTxAfterDaCoreWithWitness
          txBytes
          tx.version tx.txKind tx.txNonce tx.inputs tx.outputs tx.locktime tx.daCoreBytes tx.witness
          { bs := txBytes,
            off := pre.size + (serializeWitness tx.witness).size } :=
      parseTxAfterDaCore_after_pre_step (pre := pre) (tx := tx) h
    _ = Except.ok tx := by
      have hBytes :
          txBytes =
            (pre ++ serializeWitness tx.witness) ++
              RubinFormal.WireEnc.compactSize tx.daPayloadLen ++ tx.daPayload := by
        simpa [post, txBytes] using
          (cursor_bytes_left_assoc
            (a := pre ++ serializeWitness tx.witness)
            (b := RubinFormal.WireEnc.compactSize tx.daPayloadLen)
            (c := tx.daPayload)).symm
      have hOff :
          pre.size + (serializeWitness tx.witness).size =
            (pre ++ serializeWitness tx.witness).size := by
        rw [ByteArray.size_append]
      rw [hBytes, hOff]
      exact parseTxAfterDaCoreWithWitness_after_pre (pre := pre) (tx := tx) h

end UtxoBasicV1

end RubinFormal
