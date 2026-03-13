import RubinFormal.CriticalInvariants
import RubinFormal.ByteWireLegacy
import RubinFormal.ArithmeticSafety
import RubinFormal.CoreExtInvariants
import RubinFormal.SighashV1
import RubinFormal.CovenantGenesisV1
import RubinFormal.WitnessCommitmentV1

namespace RubinFormal

/-- Bootstrap-only transaction-wire statement.
    The `CompactSize` and `TxMini` conjuncts intentionally use the legacy toy model in
    `ByteWireLegacy`; byte-accurate wire claims come from `ByteWireV2` and conformance replay,
    as tracked in `proof_coverage.json`. -/
def transactionWireStatement : Prop :=
  parseTransactionWire [] = none ∧
  (∀ n : Nat, n < 253 →
    ByteWireLegacy.parseCompactSizeToy (ByteWireLegacy.encodeCompactSizeToy n) = some (n, [])) ∧
  (∀ tx : ByteWireLegacy.TxMini, ByteWireLegacy.txMiniByteValid tx →
    ByteWireLegacy.parseTxMini (ByteWireLegacy.serializeTxMini tx) = some tx)
/-- v2 (F-01 fix): ByteArray preimage distinctness for txid ≠ wtxid.
    When witness is non-empty (coreEnd < tx.size), the txid preimage
    (tx.extract 0 coreEnd) differs from the wtxid preimage (full tx). -/
def transactionIdentifiersStatement : Prop :=
  ∀ (tx : ByteArray) (coreEnd : Nat),
    coreEnd < tx.size → tx.extract 0 coreEnd ≠ tx
def weightAccountingStatement : Prop :=
  ∀ base witness1 witness2 sigCost : Nat, witness1 ≤ witness2 → weight base witness1 sigCost ≤ weight base witness2 sigCost
/-- v3 (D08-F02 fix): standalone witness-commitment semantics.
    (1) Witness merkle construction zeroes the coinbase slot.
    (2) The isolated witness-commitment step accepts iff the coinbase anchor
        matches the prefixed witness-merkle commitment.
    (3) Once parse/pow/target/linkage/merkle gates pass, `validateBlockBasic`
        reduces exactly to this witness-commitment step. -/
def witnessCommitmentStatement : Prop :=
  (∀ (coinbaseWtxid : Bytes) (rest : List Bytes),
    BlockBasicV1.witnessMerkleRootWtxids (coinbaseWtxid :: rest) =
      BlockBasicV1.merkleRootTagged
        (BlockBasicV1.coinbaseWitnessReservedValue :: rest) 0x02 0x03) ∧
  (∀ (pb : BlockBasicV1.ParsedBlock) (witnessRoot gotCommit : Bytes),
    BlockBasicV1.witnessMerkleRootWtxids pb.wtxids = .ok witnessRoot →
    BlockBasicV1.findCoinbaseAnchorCommitment pb.coinbaseTx = .ok gotCommit →
    (BlockBasicV1.checkWitnessCommitment pb = .ok () ↔
      gotCommit = BlockBasicV1.witnessCommitmentHash witnessRoot)) ∧
  (∀ (blockBytes : Bytes)
      (expectedPrevHash expectedTarget : Option Bytes)
      (pb : BlockBasicV1.ParsedBlock),
    BlockBasicV1.parseBlock blockBytes = .ok pb →
    BlockBasicV1.powCheck pb.header = .ok () →
    (match expectedTarget with
    | none => True
    | some exp => pb.header.target = exp) →
    (match expectedPrevHash with
    | none => True
    | some exp => pb.header.prevHash = exp) →
    BlockBasicV1.merkleRootTxids pb.txids = .ok pb.header.merkleRoot →
    BlockBasicV1.validateBlockBasic blockBytes expectedPrevHash expectedTarget =
      BlockBasicV1.checkWitnessCommitment pb)
/-- v2 (F-02 fix): sighash encoding size invariants over real `SighashV1.u64le`/`u32le`.
    Fixed encoding sizes (8 and 4 bytes) are essential for preimage domain separation
    in the sighash construction (`digestV1`). -/
def sighashV1Statement : Prop :=
  (∀ n : Nat, (SighashV1.u64le n).size = 8) ∧
  (∀ n : Nat, (SighashV1.u32le n).size = 4)
def consensusErrorCodesStatement : Prop := ErrorCode.TxErrParse ≠ ErrorCode.TxErrSigInvalid
def covenantRegistryStatement : Prop := CovenantType.P2PK ≠ CovenantType.HTLC
def difficultyUpdateStatement : Prop :=
  (∀ prevTs newTs maxStep : Nat, clampTimestampStep prevTs newTs maxStep ≤ prevTs + maxStep) ∧
  (∀ a b : Nat, 0 < b → floorDiv a b * b ≤ a)
/-- v2 (F-13 fix): strengthened from zero-slot only to general case + advance property.
    (1) General validity: any cursor + slots ≤ witnessCount is valid.
    (2) Advance: consuming one slot preserves validity (operational loop invariant). -/
def transactionStructuralRulesStatement : Prop :=
  (∀ cursor slots witnessCount : Nat,
    cursor + slots ≤ witnessCount → witnessCursorValid cursor slots witnessCount) ∧
  (∀ cursor slots witnessCount : Nat,
    witnessCursorValid cursor (slots + 1) witnessCount →
      witnessCursorValid (cursor + 1) slots witnessCount)
def replayDomainChecksStatement : Prop :=
  ∀ n : Nat, ∀ xs : List Nat, n ∈ xs → ¬ nonceReplayFree (n :: xs)
def utxoStateModelStatement : Prop := ∀ v : Nat, ¬ canSpend { spendable := false, value := v }
def valueConservationStatement : Prop :=
  (∀ sumIn sumOut fee : Nat, valueConserved sumIn sumOut → valueConserved (sumIn + fee) sumOut) ∧
  (∀ sumIn sumOut fee : Nat, inU128 sumIn → valueConserved sumIn sumOut → valueConserved (satAddU128 sumIn fee) sumOut)
def daSetIntegrityStatement : Prop := ¬ daChunkSetValid []
/-- v2 (F-04 fix): soft-fork tightening WITH substantive sentinel rejection.
    (1) active → legacy (trivially true, anyone-can-spend).
    (2) active rejects SENTINEL suite_id = 0x00.
    (3) legacy accepts SENTINEL.
    Together (2)+(3) prove the rule is a STRICT tightening. -/
def coreExtTighteningStatement : Prop :=
  (∀ allowedSuiteIds : List Nat,
    ∀ w : WitnessItemMini, coreExtActiveAllowed allowedSuiteIds w → coreExtLegacyAllowed w) ∧
  (∀ allowedSuiteIds : List Nat,
    ¬ coreExtActiveAllowed allowedSuiteIds { suiteId := SUITE_ID_SENTINEL }) ∧
  (coreExtLegacyAllowed { suiteId := SUITE_ID_SENTINEL })
def coreExtPreActivationStrictSupersetStatement : Prop :=
  ∀ allowedSuiteIds : List Nat,
    ∃ w : WitnessItemMini, coreExtLegacyAllowed w ∧ ¬ coreExtActiveAllowed allowedSuiteIds w
def coreExtCursorNoAmbiguityStatement : Prop :=
  ∀ inputCount witnessCount : Nat,
    witnessCount = inputCount →
      (∀ i j : Nat,
        i < inputCount →
        j < inputCount →
        coreExtAssignedWitnessIndex i = coreExtAssignedWitnessIndex j →
          i = j) ∧
      (∀ i : Nat, i < inputCount → coreExtAssignedWitnessIndex i < witnessCount)
-- §19.1: subsidy arithmetic fits in machine integer types (PR #420).
def subsidyU128SafetyStatement : Prop :=
  (∀ h ag : Nat, SubsidyV1.blockSubsidy h ag ≤ SubsidyV1.MINEABLE_CAP) ∧
  (∀ h ag : Nat, SubsidyV1.blockSubsidy h ag ≤ maxU64) ∧
  (∀ h ag fees : Nat, ag ≤ SubsidyV1.MINEABLE_CAP → fees ≤ maxU64 →
    ag + SubsidyV1.blockSubsidy h ag + fees ≤ maxU128)
/-- F-05 fix: ByteWireV2 cursor advancement + TxErr distinctness.
    (1) getU8? advances offset by 1.
    (2) getBytes? advances offset by n.
    (3) All TxErr constructors are pairwise distinct. -/
def byteWireV2CursorStatement : Prop :=
  (∀ c : Wire.Cursor, ∀ b : UInt8, ∀ c' : Wire.Cursor,
    c.getU8? = some (b, c') → c'.off = c.off + 1) ∧
  (∀ c : Wire.Cursor, ∀ n : Nat, ∀ bs : Bytes, ∀ c' : Wire.Cursor,
    c.getBytes? n = some (bs, c') → c'.off = c.off + n) ∧
  (Wire.TxErr.parse ≠ Wire.TxErr.witnessOverflow ∧
   Wire.TxErr.parse ≠ Wire.TxErr.sigAlgInvalid ∧
   Wire.TxErr.parse ≠ Wire.TxErr.sigNoncanonical ∧
   Wire.TxErr.witnessOverflow ≠ Wire.TxErr.sigAlgInvalid ∧
   Wire.TxErr.witnessOverflow ≠ Wire.TxErr.sigNoncanonical ∧
   Wire.TxErr.sigAlgInvalid ≠ Wire.TxErr.sigNoncanonical)
/-- F-17 fix: HTLC timelock enforcement — refund path blocked before expiry.
    (1) Height-lock: blockHeight < lockValue → timelock NOT met.
    (2) Timestamp-lock: blockMtp < lockValue → timelock NOT met.
    (3) Lock modes are distinct (height ≠ timestamp). -/
def htlcTimelockStatement : Prop :=
  (∀ lockValue blockHeight blockMtp : Nat, blockHeight < lockValue →
    CovenantGenesisV1.htlcTimelockMet CovenantGenesisV1.LOCK_MODE_HEIGHT lockValue blockHeight blockMtp = false) ∧
  (∀ lockValue blockHeight blockMtp : Nat, blockMtp < lockValue →
    CovenantGenesisV1.htlcTimelockMet CovenantGenesisV1.LOCK_MODE_TIMESTAMP lockValue blockHeight blockMtp = false) ∧
  (CovenantGenesisV1.LOCK_MODE_HEIGHT ≠ CovenantGenesisV1.LOCK_MODE_TIMESTAMP)

theorem transaction_wire_proved : transactionWireStatement := by
  refine ⟨?_, ?_, ?_⟩
  · simpa using parse_empty_none
  · intro n hn
    exact ByteWireLegacy.parse_encodeCompactSizeToy_roundtrip n hn
  · intro tx htx
    exact ByteWireLegacy.parse_serializeTxMini_roundtrip tx htx

theorem transaction_identifiers_proved : transactionIdentifiersStatement := by
  intro tx coreEnd h
  exact txid_wtxid_preimage_bytes_distinct tx coreEnd h

theorem weight_accounting_proved : weightAccountingStatement := by
  intro base witness1 witness2 sigCost hw
  exact weight_monotone_witness base witness1 witness2 sigCost hw

theorem witness_commitment_proved : witnessCommitmentStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro coinbaseWtxid rest
    exact WitnessCommitmentV1.witnessMerkleRootWtxids_rewrites_coinbase_slot coinbaseWtxid rest
  · intro pb witnessRoot gotCommit hRoot hCommit
    exact WitnessCommitmentV1.checkWitnessCommitment_ok_iff
      pb witnessRoot gotCommit hRoot hCommit
  · intro blockBytes expectedPrevHash expectedTarget pb hParse hPow hTarget hPrev hMerkle
    exact WitnessCommitmentV1.validateBlockBasic_witness_stage
      blockBytes expectedPrevHash expectedTarget pb hParse hPow hTarget hPrev hMerkle

theorem sighash_v1_proved : sighashV1Statement := by
  exact ⟨fun _ => rfl, fun _ => rfl⟩

theorem consensus_error_codes_proved : consensusErrorCodesStatement := by
  simpa [consensusErrorCodesStatement] using error_codes_distinct

theorem covenant_registry_proved : covenantRegistryStatement := by
  simpa [covenantRegistryStatement] using covenant_types_distinct

theorem difficulty_update_proved : difficultyUpdateStatement := by
  refine ⟨?_, ?_⟩
  · intro prevTs newTs maxStep
    exact clamp_respects_upper_bound prevTs newTs maxStep
  · intro a b hb
    exact floorDiv_mul_le a b hb

theorem transaction_structural_rules_proved : transactionStructuralRulesStatement := by
  refine ⟨?_, ?_⟩
  · intro cursor slots witnessCount h
    exact witness_cursor_valid_general cursor slots witnessCount h
  · intro cursor slots witnessCount h
    exact witness_cursor_advance cursor slots witnessCount h

theorem replay_domain_checks_proved : replayDomainChecksStatement := by
  intro n xs h
  exact duplicate_nonce_not_replay_free n xs h

theorem utxo_state_model_proved : utxoStateModelStatement := by
  intro v
  exact non_spendable_cannot_spend v

theorem value_conservation_proved : valueConservationStatement := by
  refine ⟨?_, ?_⟩
  · intro sumIn sumOut fee h
    exact value_conservation_with_extra_input sumIn sumOut fee h
  · intro sumIn sumOut fee hU128 hCons
    unfold valueConserved at *
    exact Nat.le_trans hCons (satAddU128_preserves_lower_bound sumIn fee hU128)

theorem da_set_integrity_proved : daSetIntegrityStatement := by
  simpa [daSetIntegrityStatement] using da_chunk_set_requires_nonempty

theorem core_ext_tightening_proved : coreExtTighteningStatement := by
  refine ⟨?_, ?_, ?_⟩
  · intro allowedSuiteIds w h
    exact core_ext_softfork_tightening allowedSuiteIds w h
  · intro allowedSuiteIds
    exact core_ext_active_rejects_sentinel allowedSuiteIds
  · exact core_ext_legacy_accepts_sentinel

theorem core_ext_preactivation_strict_superset_proved : coreExtPreActivationStrictSupersetStatement := by
  intro allowedSuiteIds
  refine ⟨{ suiteId := SUITE_ID_SENTINEL }, ?_, ?_⟩
  · exact core_ext_legacy_accepts_sentinel
  · exact core_ext_active_rejects_sentinel allowedSuiteIds

theorem core_ext_cursor_no_ambiguity_proved : coreExtCursorNoAmbiguityStatement := by
  intro inputCount witnessCount h
  exact core_ext_no_cursor_ambiguity inputCount witnessCount h

theorem subsidy_u128_safety_proved : subsidyU128SafetyStatement := by
  refine ⟨?_, ?_, ?_⟩
  · exact blockSubsidy_bounded
  · exact blockSubsidy_in_u64
  · intro h ag fees hAg hFees
    exact subsidy_accumulation_in_u128 h ag fees hAg hFees

theorem byte_wire_v2_cursor_proved : byteWireV2CursorStatement := by
  refine ⟨?_, ?_, ?_⟩
  · exact Wire.Cursor.getU8_advances
  · exact Wire.Cursor.getBytes_advances
  · exact Wire.txerr_all_distinct

theorem htlc_timelock_proved : htlcTimelockStatement := by
  refine ⟨?_, ?_, ?_⟩
  · exact CovenantGenesisV1.htlc_height_lock_enforcement
  · exact CovenantGenesisV1.htlc_timestamp_lock_enforcement
  · exact CovenantGenesisV1.htlc_lock_modes_distinct

end RubinFormal
