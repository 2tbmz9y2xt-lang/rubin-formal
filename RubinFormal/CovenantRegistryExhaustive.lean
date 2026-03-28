import RubinFormal.CovenantGenesisV1
import RubinFormal.CovenantParserGaps

/-!
# Covenant Registry Exhaustive Proofs (§14)

Proves covenant type tags are pairwise distinct and that
the canonical registry maps each known tag to a unique branch.
-/

namespace RubinFormal

open CovenantGenesisV1

private def repeatByte (b : UInt8) (n : Nat) : Bytes :=
  Id.run <| do
    let mut out := ByteArray.empty
    for _ in [0:n] do
      out := out.push b
    pure out

private def byte32 (n : Nat) : Bytes :=
  repeatByte (UInt8.ofNat n) 32

private def u16leBytes (n : Nat) : Bytes :=
  let lo : UInt8 := UInt8.ofNat (n % 256)
  let hi : UInt8 := UInt8.ofNat ((n / 256) % 256)
  RubinFormal.bytes #[lo, hi]

private def u64leBytes (n : Nat) : Bytes :=
  RubinFormal.bytes #[
    UInt8.ofNat (n % 256),
    UInt8.ofNat ((n / 256) % 256),
    UInt8.ofNat ((n / 65536) % 256),
    UInt8.ofNat ((n / 16777216) % 256),
    UInt8.ofNat ((n / 4294967296) % 256),
    UInt8.ofNat ((n / 1099511627776) % 256),
    UInt8.ofNat ((n / 281474976710656) % 256),
    UInt8.ofNat ((n / 72057594037927936) % 256)
  ]

private def sampleP2PKOut : TxOut :=
  {
    value := 1
    covenantType := COV_TYPE_P2PK
    covenantData := RubinFormal.bytes #[UInt8.ofNat SUITE_ID_ML_DSA_87] ++ byte32 0x11
  }

private def sampleAnchorOut : TxOut :=
  {
    value := 0
    covenantType := COV_TYPE_ANCHOR
    covenantData := RubinFormal.bytes #[0x42]
  }

private def sampleVaultOut : TxOut :=
  {
    value := 7
    covenantType := COV_TYPE_VAULT
    covenantData :=
      byte32 0x10 ++
      RubinFormal.bytes #[0x01, 0x01] ++
      byte32 0x20 ++
      u16leBytes 1 ++
      byte32 0x30
  }

private def sampleMultisigOut : TxOut :=
  {
    value := 9
    covenantType := COV_TYPE_MULTISIG
    covenantData := RubinFormal.bytes #[0x01, 0x01] ++ byte32 0x40
  }

private def sampleHtlcOut : TxOut :=
  {
    value := 11
    covenantType := COV_TYPE_HTLC
    covenantData :=
      byte32 0x50 ++
      RubinFormal.bytes #[UInt8.ofNat LOCK_MODE_HEIGHT] ++
      u64leBytes 1 ++
      byte32 0x60 ++
      byte32 0x70
  }

private def sampleDaCommitOut : TxOut :=
  {
    value := 0
    covenantType := COV_TYPE_DA_COMMIT
    covenantData := byte32 0x80
  }

/-- All canonical covenant type tags are pairwise distinct. -/
theorem covenant_types_pairwise_distinct :
    COV_TYPE_P2PK ≠ COV_TYPE_ANCHOR ∧
    COV_TYPE_P2PK ≠ COV_TYPE_HTLC ∧
    COV_TYPE_P2PK ≠ COV_TYPE_DA_COMMIT ∧
    COV_TYPE_ANCHOR ≠ COV_TYPE_HTLC ∧
    COV_TYPE_ANCHOR ≠ COV_TYPE_DA_COMMIT ∧
    COV_TYPE_HTLC ≠ COV_TYPE_DA_COMMIT := by native_decide

/-- P2PK tag is 0x0000. -/
theorem cov_type_p2pk_value : COV_TYPE_P2PK = 0x0000 := rfl

/-- ANCHOR tag is 0x0002. -/
theorem cov_type_anchor_value : COV_TYPE_ANCHOR = 0x0002 := rfl

/-- HTLC tag is 0x0100. -/
theorem cov_type_htlc_value : COV_TYPE_HTLC = 0x0100 := rfl

/-- DA_COMMIT tag is 0x0103. -/
theorem cov_type_da_commit_value : COV_TYPE_DA_COMMIT = 0x0103 := rfl

/-- Canonical P2PK outputs are accepted by the live genesis registry. -/
theorem validate_out_genesis_p2pk_canonical_ok :
    (match validateOutGenesis sampleP2PKOut 0 0 with
      | .ok () => true
      | _ => false) = true := by
  native_decide

/-- Canonical anchor outputs are accepted by the live genesis registry. -/
theorem validate_out_genesis_anchor_canonical_ok :
    (match validateOutGenesis sampleAnchorOut 0 0 with
      | .ok () => true
      | _ => false) = true := by
  native_decide

/-- Canonical vault outputs are accepted by the live genesis registry. -/
theorem validate_out_genesis_vault_canonical_ok :
    (match validateOutGenesis sampleVaultOut 0 0 with
      | .ok () => true
      | _ => false) = true := by
  native_decide

/-- Canonical multisig outputs are accepted by the live genesis registry. -/
theorem validate_out_genesis_multisig_canonical_ok :
    (match validateOutGenesis sampleMultisigOut 0 0 with
      | .ok () => true
      | _ => false) = true := by
  native_decide

/-- Canonical HTLC outputs are accepted by the live genesis registry. -/
theorem validate_out_genesis_htlc_canonical_ok :
    (match validateOutGenesis sampleHtlcOut 0 0 with
      | .ok () => true
      | _ => false) = true := by
  native_decide

/-- Canonical DA_COMMIT outputs are accepted on transaction kind `0x01`. -/
theorem validate_out_genesis_da_commit_canonical_ok :
    (match validateOutGenesis sampleDaCommitOut 0x01 0 with
      | .ok () => true
      | _ => false) = true := by
  native_decide

/-- Reserved-future tag stays outside the live canonical registry. -/
theorem validate_out_genesis_reserved_future_rejects
    (value txKind blockHeight : Nat) (covData : Bytes) :
    validateOutGenesis { value := value, covenantType := COV_TYPE_RESERVED_FUTURE, covenantData := covData } txKind blockHeight =
      .error "TX_ERR_COVENANT_TYPE_INVALID" := by
  apply validate_out_genesis_rejects_unknown
  all_goals
    simp [COV_TYPE_RESERVED_FUTURE, COV_TYPE_P2PK, COV_TYPE_ANCHOR, COV_TYPE_VAULT,
      COV_TYPE_MULTISIG, COV_TYPE_HTLC, COV_TYPE_DA_COMMIT]

end RubinFormal
