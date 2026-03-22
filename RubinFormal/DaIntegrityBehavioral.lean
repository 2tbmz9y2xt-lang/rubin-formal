import RubinFormal.DaCoreV1
namespace RubinFormal
/-- DA chunk index 0 is valid for any non-zero chunk count. -/
theorem da_chunk_index_zero_valid (chunkCount : Nat) (h : chunkCount > 0) :
    0 < chunkCount := h
/-- DA chunk bytes constant is 524288 (512 KB). -/
theorem da_chunk_bytes_value : DaCoreV1.CHUNK_BYTES = 524288 := rfl
end RubinFormal
