import RubinFormal.UtxoBasicV1

/-!
# Replay Domain Behavioral Proofs (§17)

Proves that parseTx extracts nonce deterministically, providing
nonce-based replay domain separation.
-/

namespace RubinFormal

open UtxoBasicV1

/-- parseTx is deterministic on nonce: same bytes → same parsed nonce.
    Combined with nonce-uniqueness enforcement, this ensures replay
    domain separation per-transaction. -/
theorem parseTx_nonce_deterministic (txBytes : Bytes)
    (tx1 tx2 : Tx)
    (h1 : parseTx txBytes = .ok tx1)
    (h2 : parseTx txBytes = .ok tx2) :
    tx1.txNonce = tx2.txNonce := by
  rw [h1] at h2; cases h2; rfl

-- chainId domain separation: full behavioral proof blocked by
-- do-notation unfolding. See ChainIdBehavioral.lean for partial evidence.

end RubinFormal
