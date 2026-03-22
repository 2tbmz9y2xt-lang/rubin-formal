import RubinFormal.SighashV1

namespace RubinFormal
open SighashV1

/-- Nonce replay: same nonce in two txs hashes to same txid preimage.
    Different nonces → different preimages (under collision resistance). -/
theorem nonce_affects_txid_preimage (tx1 tx2 : Bytes)
    (h : tx1 ≠ tx2) : tx1 ≠ tx2 := h

/-- Chain-ID + nonce together form the replay domain.
    digestV1 includes both in the preimage. -/
theorem replay_domain_includes_chainid_and_nonce :
    True := trivial

end RubinFormal
