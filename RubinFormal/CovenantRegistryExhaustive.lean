import RubinFormal.CovenantGenesisV1
import RubinFormal.CovenantParserGaps

/-!
# Covenant Registry Exhaustive + Bounded Proofs (§14)

`covenantDispositionComplete` classifies every u16 tag by its static
Section 14 disposition. It does not define output acceptance, deployment or
activation behavior, descriptors, spend rules, cryptography, or client parity.

`validateOutGenesis_ok_constrained` remains a six-accept legacy genesis-model
theorem for P2PK/ANCHOR/VAULT/MULTISIG/HTLC/DA_COMMIT. Its constrained output
surface does not cover CORE_STEALTH or CORE_SIMPLICITY.
-/

namespace RubinFormal

open CovenantGenesisV1

/-- Static Section 14 tag disposition. The total function is intentionally
    separate from the legacy six-branch genesis model. -/
def covenantDisposition (tag : Nat) : CovenantDisposition :=
  if tag = 0x0000 then CovenantDisposition.accepted CovenantKind.coreP2PK
  else if tag = 0x0001 then CovenantDisposition.invalidCovenantType
  else if tag = 0x0002 then CovenantDisposition.accepted CovenantKind.coreAnchor
  else if tag = 0x00FF then CovenantDisposition.reserved
  else if tag = 0x0100 then CovenantDisposition.accepted CovenantKind.coreHTLC
  else if tag = 0x0101 then CovenantDisposition.accepted CovenantKind.coreVault
  else if tag = 0x0102 then CovenantDisposition.invalidCovenantType
  else if tag = 0x0103 then CovenantDisposition.accepted CovenantKind.coreDACommit
  else if tag = 0x0104 then CovenantDisposition.accepted CovenantKind.coreMultisig
  else if tag = 0x0105 then CovenantDisposition.accepted CovenantKind.coreStealth
  else if tag = 0x0106 then CovenantDisposition.deploymentGated CovenantKind.coreSimplicity
  else CovenantDisposition.invalidCovenantType

/-- Exact bounded Section 14 classification for one tag and one disposition. -/
def section14DispositionCase (tag : Nat) (disposition : CovenantDisposition) : Prop :=
  tag < 0x10000 ∧
    ((tag = 0x0000 ∧ disposition = CovenantDisposition.accepted CovenantKind.coreP2PK) ∨
    (tag = 0x0001 ∧ disposition = CovenantDisposition.invalidCovenantType) ∨
    (tag = 0x0002 ∧ disposition = CovenantDisposition.accepted CovenantKind.coreAnchor) ∨
    (tag = 0x00FF ∧ disposition = CovenantDisposition.reserved) ∨
    (tag = 0x0100 ∧ disposition = CovenantDisposition.accepted CovenantKind.coreHTLC) ∨
    (tag = 0x0101 ∧ disposition = CovenantDisposition.accepted CovenantKind.coreVault) ∨
    (tag = 0x0102 ∧ disposition = CovenantDisposition.invalidCovenantType) ∨
    (tag = 0x0103 ∧ disposition = CovenantDisposition.accepted CovenantKind.coreDACommit) ∨
    (tag = 0x0104 ∧ disposition = CovenantDisposition.accepted CovenantKind.coreMultisig) ∨
    (tag = 0x0105 ∧ disposition = CovenantDisposition.accepted CovenantKind.coreStealth) ∨
    (tag = 0x0106 ∧ disposition = CovenantDisposition.deploymentGated CovenantKind.coreSimplicity) ∨
    (tag ≠ 0x0000 ∧ tag ≠ 0x0001 ∧ tag ≠ 0x0002 ∧ tag ≠ 0x00FF ∧
      tag ≠ 0x0100 ∧ tag ≠ 0x0101 ∧ tag ≠ 0x0102 ∧ tag ≠ 0x0103 ∧
      tag ≠ 0x0104 ∧ tag ≠ 0x0105 ∧ tag ≠ 0x0106 ∧
      disposition = CovenantDisposition.invalidCovenantType))

/-- Every u16 tag has exactly the static Section 14 disposition in the matrix.
    This theorem makes no activation, descriptor, spend, cryptographic, or client claim. -/
theorem covenantDispositionComplete (tag : Nat) (hU16 : tag < 0x10000) :
    section14DispositionCase tag (covenantDisposition tag) := by
  unfold section14DispositionCase
  refine ⟨hU16, ?_⟩
  by_cases hP2PK : tag = 0x0000
  · simp [covenantDisposition, hP2PK]
  by_cases hInvalidOne : tag = 0x0001
  · simp [covenantDisposition, hP2PK, hInvalidOne]
  by_cases hAnchor : tag = 0x0002
  · simp [covenantDisposition, hP2PK, hInvalidOne, hAnchor]
  by_cases hReserved : tag = 0x00FF
  · simp [covenantDisposition, hP2PK, hInvalidOne, hAnchor, hReserved]
  by_cases hHtlc : tag = 0x0100
  · simp [covenantDisposition, hP2PK, hInvalidOne, hAnchor, hReserved, hHtlc]
  by_cases hVault : tag = 0x0101
  · simp [covenantDisposition, hP2PK, hInvalidOne, hAnchor, hReserved, hHtlc, hVault]
  by_cases hInvalidTwo : tag = 0x0102
  · simp [covenantDisposition, hP2PK, hInvalidOne, hAnchor, hReserved, hHtlc, hVault,
      hInvalidTwo]
  by_cases hDaCommit : tag = 0x0103
  · simp [covenantDisposition, hP2PK, hInvalidOne, hAnchor, hReserved, hHtlc, hVault,
      hInvalidTwo, hDaCommit]
  by_cases hMultisig : tag = 0x0104
  · simp [covenantDisposition, hP2PK, hInvalidOne, hAnchor, hReserved, hHtlc, hVault,
      hInvalidTwo, hDaCommit, hMultisig]
  by_cases hStealth : tag = 0x0105
  · simp [covenantDisposition, hP2PK, hInvalidOne, hAnchor, hReserved, hHtlc, hVault,
      hInvalidTwo, hDaCommit, hMultisig, hStealth]
  by_cases hSimplicity : tag = 0x0106
  · simp [covenantDisposition, hP2PK, hInvalidOne, hAnchor, hReserved, hHtlc, hVault,
      hInvalidTwo, hDaCommit, hMultisig, hStealth, hSimplicity]
  · simp [covenantDisposition, hP2PK, hInvalidOne, hAnchor, hReserved, hHtlc, hVault,
      hInvalidTwo, hDaCommit, hMultisig, hStealth, hSimplicity]

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

/-- The explicitly enumerated P2PK/ANCHOR/HTLC/DA_COMMIT tag pairs are distinct. -/
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

/-- Canonical P2PK outputs are accepted by the legacy genesis model. -/
theorem validate_out_genesis_p2pk_canonical_ok :
    (match validateOutGenesis sampleP2PKOut 0 0 with
      | .ok () => true
      | _ => false) = true := by
  native_decide

/-- Canonical anchor outputs are accepted by the legacy genesis model. -/
theorem validate_out_genesis_anchor_canonical_ok :
    (match validateOutGenesis sampleAnchorOut 0 0 with
      | .ok () => true
      | _ => false) = true := by
  native_decide

/-- Canonical vault outputs are accepted by the legacy genesis model. -/
theorem validate_out_genesis_vault_canonical_ok :
    (match validateOutGenesis sampleVaultOut 0 0 with
      | .ok () => true
      | _ => false) = true := by
  native_decide

/-- Canonical multisig outputs are accepted by the legacy genesis model. -/
theorem validate_out_genesis_multisig_canonical_ok :
    (match validateOutGenesis sampleMultisigOut 0 0 with
      | .ok () => true
      | _ => false) = true := by
  native_decide

/-- Canonical HTLC outputs are accepted by the legacy genesis model. -/
theorem validate_out_genesis_htlc_canonical_ok :
    (match validateOutGenesis sampleHtlcOut 0 0 with
      | .ok () => true
      | _ => false) = true := by
  native_decide

/-- Canonical DA_COMMIT outputs are accepted by the legacy genesis model on transaction kind `0x01`. -/
theorem validate_out_genesis_da_commit_canonical_ok :
    (match validateOutGenesis sampleDaCommitOut 0x01 0 with
      | .ok () => true
      | _ => false) = true := by
  native_decide

/-- The legacy genesis model rejects the reserved-future tag. -/
theorem validate_out_genesis_reserved_future_rejects
    (value txKind blockHeight : Nat) (covData : Bytes) :
    validateOutGenesis { value := value, covenantType := COV_TYPE_RESERVED_FUTURE, covenantData := covData } txKind blockHeight =
      .error "TX_ERR_COVENANT_TYPE_INVALID" := by
  apply validate_out_genesis_rejects_unknown
  all_goals
    simp [COV_TYPE_RESERVED_FUTURE, COV_TYPE_P2PK, COV_TYPE_ANCHOR, COV_TYPE_VAULT,
      COV_TYPE_MULTISIG, COV_TYPE_HTLC, COV_TYPE_DA_COMMIT]

-- ═══════════════════════════════════════════════════════════════════
-- §  Constrained universal theorem (§14 covenant registry)
-- ═══════════════════════════════════════════════════════════════════

private theorem not_not_iff_self {P : Prop} [Decidable P] : ¬¬P ↔ P :=
  ⟨Decidable.byContradiction, fun h hn => hn h⟩

/-- Non-do form of validateOutGenesis for proof tractability. -/
private def validateOutGenesisExplicit (out : TxOut) (txKind : Nat) (_blockHeight : Nat) : Except String Unit :=
  if out.covenantType == COV_TYPE_P2PK then
    if out.value == 0 then Except.error "TX_ERR_COVENANT_TYPE_INVALID"
    else if out.covenantData.size != MAX_P2PK_COVENANT_DATA then Except.error "TX_ERR_COVENANT_TYPE_INVALID"
    else if (out.covenantData.get! 0).toNat != SUITE_ID_ML_DSA_87 then Except.error "TX_ERR_COVENANT_TYPE_INVALID"
    else Except.ok ()
  else if out.covenantType == COV_TYPE_ANCHOR then
    if out.value != 0 then Except.error "TX_ERR_COVENANT_TYPE_INVALID"
    else if out.covenantData.size == 0 || out.covenantData.size > MAX_ANCHOR_PAYLOAD_SIZE then Except.error "TX_ERR_COVENANT_TYPE_INVALID"
    else Except.ok ()
  else if out.covenantType == COV_TYPE_VAULT then
    if out.value == 0 then Except.error "TX_ERR_VAULT_PARAMS_INVALID"
    else match parseVaultCovenantData out.covenantData with
      | .error e => Except.error e
      | .ok _ => Except.ok ()
  else if out.covenantType == COV_TYPE_MULTISIG then
    if out.value == 0 then Except.error "TX_ERR_COVENANT_TYPE_INVALID"
    else match parseMultisigCovenantData out.covenantData with
      | .error e => Except.error e
      | .ok _ => Except.ok ()
  else if out.covenantType == COV_TYPE_HTLC then
    if out.value == 0 then Except.error "TX_ERR_COVENANT_TYPE_INVALID"
    else match parseHtlcCovenantData out.covenantData with
      | .error e => Except.error e
      | .ok _ => Except.ok ()
  else if out.covenantType == COV_TYPE_DA_COMMIT then
    if txKind != 0x01 then Except.error "TX_ERR_COVENANT_TYPE_INVALID"
    else if out.value != 0 then Except.error "TX_ERR_COVENANT_TYPE_INVALID"
    else if out.covenantData.size != 32 then Except.error "TX_ERR_COVENANT_TYPE_INVALID"
    else Except.ok ()
  else Except.error "TX_ERR_COVENANT_TYPE_INVALID"

-- 8M heartbeats needed: unfold + 6-branch do-notation normalization
set_option maxHeartbeats 8000000 in
/-- BRIDGE: validateOutGenesis (do-notation) = validateOutGenesisExplicit (if-else).
    Needed because do-notation creates `__do_jp` join points that block `split at h`. -/
private theorem validateOutGenesis_eq_explicit (out : TxOut) (txKind bh : Nat) :
    validateOutGenesis out txKind bh = validateOutGenesisExplicit out txKind bh := by
  unfold validateOutGenesis validateOutGenesisExplicit
  simp only [Bind.bind, Except.bind, Pure.pure, Except.pure,
             throwThe, MonadExcept.throw, MonadExceptOf.throw]
  -- Each branch: split on guard condition, close by rfl/contradiction/simp_all
  repeat (first | split | rfl | contradiction | (exfalso; contradiction) | simp_all)

-- 8M heartbeats needed: 6 by_cases + nested split at h per branch
set_option maxHeartbeats 8000000 in
/-- **Legacy `validateOutGenesis` constrained theorem**: when the six-accept
    genesis model accepts an output, at least one of six disjuncts holds —
    each constraining covenantType, value, and payload conditions. This is
    not a theorem for CORE_STEALTH or CORE_SIMPLICITY, and makes no claim about
    activation, deployment, descriptors, HTLC spend-side preimages, or crypto semantics. -/
theorem validateOutGenesis_ok_constrained (out : TxOut) (txKind bh : Nat)
    (h : validateOutGenesis out txKind bh = .ok ()) :
    (out.covenantType = COV_TYPE_P2PK ∧ out.value ≠ 0 ∧
     out.covenantData.size = MAX_P2PK_COVENANT_DATA ∧
     (out.covenantData.get! 0).toNat = SUITE_ID_ML_DSA_87) ∨
    (out.covenantType = COV_TYPE_ANCHOR ∧ out.value = 0 ∧
     out.covenantData.size > 0 ∧ out.covenantData.size ≤ MAX_ANCHOR_PAYLOAD_SIZE) ∨
    (out.covenantType = COV_TYPE_VAULT ∧ out.value ≠ 0 ∧
     ∃ v, parseVaultCovenantData out.covenantData = .ok v) ∨
    (out.covenantType = COV_TYPE_MULTISIG ∧ out.value ≠ 0 ∧
     ∃ v, parseMultisigCovenantData out.covenantData = .ok v) ∨
    (out.covenantType = COV_TYPE_HTLC ∧ out.value ≠ 0 ∧
     ∃ v, parseHtlcCovenantData out.covenantData = .ok v) ∨
    (out.covenantType = COV_TYPE_DA_COMMIT ∧ txKind = 1 ∧
     out.value = 0 ∧ out.covenantData.size = 32) := by
  rw [validateOutGenesis_eq_explicit] at h
  unfold validateOutGenesisExplicit at h
  -- Normalize all Bool/Prop comparisons and split exhaustively
  simp only [beq_iff_eq, bne_iff_ne, ne_eq, Bool.or_eq_true, decide_eq_true_eq] at h
  -- Case split on covenantType
  by_cases hP2PK : out.covenantType = COV_TYPE_P2PK
  · -- P2PK
    simp only [hP2PK, ite_true] at h
    split at h <;> [simp at h; skip]
    split at h <;> [simp at h; skip]
    split at h <;> [simp at h; skip]
    -- After 3 splits, hypotheses in reverse order: hVal hSize hSuite
    rename_i hVal hSize hSuite
    have hSize' := Decidable.byContradiction hSize
    have hSuite' := Decidable.byContradiction hSuite
    left; exact ⟨hP2PK, hVal, hSize', hSuite'⟩
  · simp only [hP2PK, ite_false] at h
    by_cases hAnch : out.covenantType = COV_TYPE_ANCHOR
    · -- ANCHOR
      simp only [hAnch, ite_true] at h
      split at h <;> [simp at h; skip]
      split at h <;> [simp at h; skip]
      rename_i hVal hBounds
      simp only [not_or] at hBounds
      have hVal' := Decidable.byContradiction hVal
      right; left; exact ⟨hAnch, hVal', by omega, by omega⟩
    · simp only [hAnch, ite_false] at h
      by_cases hVault : out.covenantType = COV_TYPE_VAULT
      · -- VAULT
        simp only [hVault, ite_true] at h
        split at h <;> [simp at h; skip]
        cases hParse : parseVaultCovenantData out.covenantData with
        | error e => simp [hParse] at h
        | ok v =>
          rename_i hValNZ
          right; right; left; exact ⟨hVault, hValNZ, ⟨v, rfl⟩⟩
      · simp only [hVault, ite_false] at h
        by_cases hMulti : out.covenantType = COV_TYPE_MULTISIG
        · -- MULTISIG
          simp only [hMulti, ite_true] at h
          split at h <;> [simp at h; skip]
          cases hParse : parseMultisigCovenantData out.covenantData with
          | error e => simp [hParse] at h
          | ok v =>
            rename_i hValNZ
            right; right; right; left; exact ⟨hMulti, hValNZ, ⟨v, rfl⟩⟩
        · simp only [hMulti, ite_false] at h
          by_cases hHtlc : out.covenantType = COV_TYPE_HTLC
          · -- HTLC
            simp only [hHtlc, ite_true] at h
            split at h <;> [simp at h; skip]
            cases hParse : parseHtlcCovenantData out.covenantData with
            | error e => simp [hParse] at h
            | ok v =>
              rename_i hValNZ
              right; right; right; right; left; exact ⟨hHtlc, hValNZ, ⟨v, rfl⟩⟩
          · simp only [hHtlc, ite_false] at h
            by_cases hDaCom : out.covenantType = COV_TYPE_DA_COMMIT
            · -- DA_COMMIT
              simp only [hDaCom, ite_true] at h
              split at h <;> [simp at h; skip]
              split at h <;> [simp at h; skip]
              split at h <;> [simp at h; skip]
              simp only [ne_eq, not_not_iff_self, bne_iff_ne] at *
              right; right; right; right; right; exact ⟨hDaCom, ‹_›, ‹_›, ‹_›⟩
            · -- ELSE
              simp only [hDaCom, ite_false] at h

end RubinFormal
