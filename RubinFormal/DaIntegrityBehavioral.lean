import RubinFormal.DaCoreV1
namespace RubinFormal

/-- DA chunk bytes constant is 524288 (512 KB). -/
theorem da_chunk_bytes_value : DaCoreV1.CHUNK_BYTES = 524288 := rfl

/-- MAX_DA_BYTES is 32_000_000 (32 MB). -/
theorem da_max_bytes_value : DaCoreV1.MAX_DA_BYTES = 32000000 := rfl

/-- Max chunk count derived from max bytes / chunk size. -/
theorem da_max_chunk_count : DaCoreV1.MAX_DA_BYTES / DaCoreV1.CHUNK_BYTES = 61 := by native_decide

end RubinFormal
