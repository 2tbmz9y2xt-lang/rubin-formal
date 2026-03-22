import RubinFormal.BlockBasicCheckV1
namespace RubinFormal
open BlockBasicCheckV1

/-- Timestamp at MTP boundary is accepted (not too old). -/
theorem timestamp_at_mtp_accepted (mtp : Nat) :
    timestampBounds mtp (mtp + 1) = .ok () := by rfl

/-- Timestamp equal to MTP is rejected as too old. -/
theorem timestamp_at_mtp_rejected (mtp : Nat) :
    timestampBounds mtp mtp = .error "BLOCK_ERR_TIMESTAMP_OLD" := by rfl

/-- Timestamp in far future is rejected. -/
theorem timestamp_far_future_rejected :
    timestampBounds 0 (MAX_FUTURE_DRIFT + 1) = .error "BLOCK_ERR_TIMESTAMP_FUTURE" := by rfl

end RubinFormal
