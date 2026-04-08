import RubinFormal.UtxoApplyGenesisV1

namespace RubinFormal

namespace HtlcSpendCryptoAssumptionBridge

open RubinFormal
open RubinFormal.UtxoApplyGenesisV1
open RubinFormal.CovenantGenesisV1

/-- Executable claim-path preimage length parser from the live HTLC spend path. -/
def claimPathPreLen (pathItem : UtxoBasicV1.WitnessItem) : Nat :=
  UtxoApplyGenesisV1.parseU16le (pathItem.signature.get! 1) (pathItem.signature.get! 2)

/-- Executable claim-path preimage slicer from the live HTLC spend path. -/
def claimPathPreimage (pathItem : UtxoBasicV1.WitnessItem) : Bytes :=
  let preLen := claimPathPreLen pathItem
  pathItem.signature.extract 3 (3 + preLen)

/-- Honest assumption-boundary reduction for HTLC claim-path crypto:
    if two distinct executable claim preimages both satisfy the same hashlock
    target, then SHA3-256 would have to collide on distinct inputs.
    This is a reduction theorem, not a cryptographic impossibility proof. -/
theorem claim_hash_collision_reduces_to_sha3_collision
    (c : CovenantGenesisV1.HtlcCovenant)
    (pathItem₁ pathItem₂ : UtxoBasicV1.WitnessItem)
    (hHash₁ : SHA3.sha3_256 (claimPathPreimage pathItem₁) = c.hash)
    (hHash₂ : SHA3.sha3_256 (claimPathPreimage pathItem₂) = c.hash)
    (hDistinct : claimPathPreimage pathItem₁ ≠ claimPathPreimage pathItem₂) :
    SHA3.sha3_256 (claimPathPreimage pathItem₁) =
      SHA3.sha3_256 (claimPathPreimage pathItem₂) ∧
    claimPathPreimage pathItem₁ ≠ claimPathPreimage pathItem₂ := by
  constructor
  · calc
      SHA3.sha3_256 (claimPathPreimage pathItem₁) = c.hash := hHash₁
      _ = SHA3.sha3_256 (claimPathPreimage pathItem₂) := hHash₂.symm
  · exact hDistinct

end HtlcSpendCryptoAssumptionBridge

end RubinFormal
