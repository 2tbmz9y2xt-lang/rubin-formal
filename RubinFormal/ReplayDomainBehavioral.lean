import RubinFormal.UtxoBasicV1
import RubinFormal.PrimitiveEncodingRoundtrip

namespace RubinFormal
open UtxoBasicV1

/-- parseTx deterministic on nonce. -/
theorem parseTx_nonce_deterministic (txBytes : Bytes)
    (tx1 tx2 : Tx) (h1 : parseTx txBytes = .ok tx1) (h2 : parseTx txBytes = .ok tx2) :
    tx1.txNonce = tx2.txNonce := by rw [h1] at h2; cases h2; rfl

/-- u64le encoding of 0 differs from 1 — nonce encoding is non-constant. -/
theorem u64le_zero_ne_one : encodeU64le 0 ≠ encodeU64le 1 := by native_decide

/-- u64le encoding of 0 differs from max — covers full range. -/
theorem u64le_zero_ne_max : encodeU64le 0 ≠ encodeU64le 18446744073709551615 := by native_decide

end RubinFormal
