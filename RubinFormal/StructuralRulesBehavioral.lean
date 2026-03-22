import RubinFormal.UtxoApplyGenesisV1

/-!
# Transaction Structural Rules Behavioral Proofs (§16)

Proves behavioral properties of structural transaction validators.
-/

namespace RubinFormal

open UtxoApplyGenesisV1
open UtxoBasicV1

/-- Concrete: unknown suite ID 0x05 is rejected with TX_ERR_SIG_ALG_INVALID. -/
theorem unknown_suite_0x05_rejected :
    validateWitnessItemLengths ⟨0x05, ByteArray.empty, ByteArray.empty⟩ 0 =
    .error "TX_ERR_SIG_ALG_INVALID" := by rfl

/-- Concrete: sentinel with non-empty pubkey is rejected. -/
theorem sentinel_nonempty_pubkey_rejected :
    validateWitnessItemLengths ⟨SUITE_ID_SENTINEL, ⟨#[0x01]⟩, ByteArray.empty⟩ 0 =
    .error "TX_ERR_PARSE" := by rfl

/-- Concrete: sentinel with empty pubkey+sig is accepted. -/
theorem sentinel_empty_accepted :
    validateWitnessItemLengths ⟨SUITE_ID_SENTINEL, ByteArray.empty, ByteArray.empty⟩ 0 =
    .ok () := by rfl

end RubinFormal
