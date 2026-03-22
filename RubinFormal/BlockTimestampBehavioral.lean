import RubinFormal.BlockBasicCheckV1
namespace RubinFormal
open BlockBasicCheckV1

/-- Concrete: timestamp 101 with MTP 100 is accepted. -/
theorem timestamp_after_mtp_accepted :
    timestampBounds 100 101 = .ok () := by rfl

/-- Concrete: timestamp equal to MTP is rejected. -/
theorem timestamp_at_mtp_rejected :
    timestampBounds 100 100 = .error "BLOCK_ERR_TIMESTAMP_OLD" := by rfl

/-- Concrete: timestamp below MTP is rejected. -/
theorem timestamp_before_mtp_rejected :
    timestampBounds 100 50 = .error "BLOCK_ERR_TIMESTAMP_OLD" := by rfl

end RubinFormal
