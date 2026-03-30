import RubinFormal.TxWireTxPayloadContract

set_option maxHeartbeats 50000000
set_option maxRecDepth 8192

namespace RubinFormal

open Wire

namespace UtxoBasicV1

theorem parseTxAfterDaCoreWithWitness_after_pre
    (pre : Bytes)
    (tx : Tx)
    (h : txStructurallyWellFormed tx) :
    let payloadCountBytes : Bytes := RubinFormal.WireEnc.compactSize tx.daPayloadLen
    parseTxAfterDaCoreWithWitness
        ((pre ++ serializeWitness tx.witness) ++ payloadCountBytes ++ tx.daPayload)
        tx.version tx.txKind tx.txNonce tx.inputs tx.outputs tx.locktime tx.daCoreBytes tx.witness
        { bs := (pre ++ serializeWitness tx.witness) ++ payloadCountBytes ++ tx.daPayload,
          off := (pre ++ serializeWitness tx.witness).size } =
      Except.ok tx := by
  unfold parseTxAfterDaCoreWithWitness
  exact parseTxFinalize_after_pre (pre := pre ++ serializeWitness tx.witness) tx h

end UtxoBasicV1

end RubinFormal
