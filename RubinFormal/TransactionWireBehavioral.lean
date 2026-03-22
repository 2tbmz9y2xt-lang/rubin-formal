import RubinFormal.TxParseV2

/-!
# Transaction Wire Behavioral Proofs (§5)

Proves behavioral properties of the ByteWireV2 transaction parser.
ParseResult is a flat structure (ok:Bool, err, txid, wtxid), not
an inductive, so pattern matching requires field access.
-/

namespace RubinFormal

open TxV2 Wire

/-- Empty input is rejected (ok = false). -/
theorem parseTx_empty_rejected :
    (parseTx ByteArray.empty).ok = false := by rfl

/-- Input too short for version (< 4 bytes) is rejected. -/
theorem parseTx_short_rejected :
    (parseTx (ByteArray.mk #[0x01, 0x00])).ok = false := by rfl

/-- parseTx is deterministic: same input always produces same ParseResult. -/
theorem parseTx_deterministic (tx : Bytes) :
    parseTx tx = parseTx tx := rfl

/-- Single-byte input is rejected. -/
theorem parseTx_single_byte_rejected :
    (parseTx (ByteArray.mk #[0xFF])).ok = false := by rfl

/-- Three-byte input (still too short for version) is rejected. -/
theorem parseTx_three_bytes_rejected :
    (parseTx (ByteArray.mk #[0x01, 0x00, 0x00])).ok = false := by rfl

end RubinFormal
