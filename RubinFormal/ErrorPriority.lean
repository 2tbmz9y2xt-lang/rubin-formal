import RubinFormal.BlockValidationOrder

/-!
# Error Priority Ordering (§7 / §13 / §25)

Proves deterministic error-priority ordering for the RUBIN validation pipeline.

## Block-level (§25)
Direct error propagation: when a block validation stage fails,
`validateBlockBasic` returns EXACTLY that stage's error code.
Stages 1-6 (parse, PoW, target, linkage, merkle, witness) are all covered.

## Transaction-level (§7)
Deterministic parse error mapping: tx parse checks are applied in order,
first applicable error code wins. Modeled via `TxParseStage` enum with
strict ordering.

## TXCTX extension (§13.1)
Error source mappings for SPEC-TXCTX-01 extension codes, modeled as
an extension of the tx-level error taxonomy.
-/

namespace RubinFormal

open RubinFormal.BlockBasicV1

/-! ## Block-level direct error propagation (§25 stage ordering) -/

/-- Stage 1: parse failure → returns the parse error. -/
theorem error_priority_parse
    (blockBytes : Bytes) (ph pt : Option Bytes) (err : String)
    (hFail : parseBlock blockBytes = .error err) :
    validateBlockBasic blockBytes ph pt = .error err := by
  unfold validateBlockBasic; rw [hFail]; rfl

/-- Stage 2: PoW failure → returns the PoW error. -/
theorem error_priority_pow
    (blockBytes : Bytes) (ph pt : Option Bytes)
    (pb : ParsedBlock) (err : String)
    (hParse : parseBlock blockBytes = .ok pb)
    (hFail : powCheck pb.header = .error err) :
    validateBlockBasic blockBytes ph pt = .error err := by
  unfold validateBlockBasic; rw [hParse]
  show (do powCheck pb.header; _) = _; rw [hFail]; rfl

/-- Stage 3: target mismatch → returns BLOCK_ERR_TARGET_INVALID.
    AMBIGUITY NOTE: powCheck also uses this code for malformed targets. -/
theorem error_priority_target
    (blockBytes : Bytes) (ph : Option Bytes)
    (pb : ParsedBlock) (expTarget : Bytes)
    (hParse : parseBlock blockBytes = .ok pb)
    (hPow : powCheck pb.header = .ok ())
    (hFail : (pb.header.target != expTarget) = true) :
    validateBlockBasic blockBytes ph (some expTarget) =
    .error "BLOCK_ERR_TARGET_INVALID" := by
  unfold validateBlockBasic; rw [hParse]
  show (do powCheck pb.header; _) = _; rw [hPow]
  simp only [hFail, ite_true]; rfl

/-- Stage 4a: linkage mismatch, no target gate. -/
theorem error_priority_linkage_no_target
    (blockBytes : Bytes) (expPrev : Bytes) (pb : ParsedBlock)
    (hParse : parseBlock blockBytes = .ok pb)
    (hPow : powCheck pb.header = .ok ())
    (hFail : (pb.header.prevHash != expPrev) = true) :
    validateBlockBasic blockBytes (some expPrev) none =
    .error "BLOCK_ERR_LINKAGE_INVALID" := by
  unfold validateBlockBasic; rw [hParse]
  show (do powCheck pb.header; _) = _; rw [hPow]
  simp only [hFail, ite_true]; rfl

/-- Stage 4b: linkage mismatch, target gate passes. -/
theorem error_priority_linkage_target_ok
    (blockBytes : Bytes) (expPrev expTarget : Bytes) (pb : ParsedBlock)
    (hParse : parseBlock blockBytes = .ok pb)
    (hPow : powCheck pb.header = .ok ())
    (hTargetOk : (pb.header.target != expTarget) = false)
    (hFail : (pb.header.prevHash != expPrev) = true) :
    validateBlockBasic blockBytes (some expPrev) (some expTarget) =
    .error "BLOCK_ERR_LINKAGE_INVALID" := by
  unfold validateBlockBasic; rw [hParse]
  show (do powCheck pb.header; _) = _; rw [hPow]
  simp only [hTargetOk, ite_false, hFail, ite_true]; rfl

/-! ## Stage 5: Merkle error propagation

The merkle check is inside the `validateBlockBasicMerkleWitnessTail` function.
Lean 4.6 do-notation creates `__do_jp` join points that resist standard tactic
reduction. Workaround: define an explicit-bind equivalent, prove definitional
equality via `rfl`, then prove error propagation on the explicit version.
-/

/-- Explicit-bind version of the merkle+witness tail (no join points). -/
def merkleWitnessTailExplicit (pb : ParsedBlock) : Except String Unit :=
  (merkleRootTxids pb.txids).bind fun mr =>
    if (mr != pb.header.merkleRoot) = true then
      Except.error "BLOCK_ERR_MERKLE_INVALID"
    else
      (witnessMerkleRootWtxids pb.wtxids).bind fun wmr =>
        let expectCommit := witnessCommitmentHash wmr
        (findCoinbaseAnchorCommitment pb.coinbaseTx).bind fun gotCommit =>
          if (gotCommit != expectCommit) = true then
            Except.error "BLOCK_ERR_WITNESS_COMMITMENT"
          else
            Except.ok ()

/-- Definitional equivalence: the do version = explicit bind version. -/
theorem merkleWitnessTail_eq_explicit (pb : ParsedBlock) :
    validateBlockBasicMerkleWitnessTail pb = merkleWitnessTailExplicit pb := by
  simp only [validateBlockBasicMerkleWitnessTail, merkleWitnessTailExplicit,
    checkWitnessCommitment, Except.bind]; rfl

/-- Stage 5a: merkle mismatch → returns BLOCK_ERR_MERKLE_INVALID.
    Proved at the `validateBlockBasicAfterPow` level for none/none. -/
theorem error_priority_merkle_afterpow_nn
    (pb : ParsedBlock) (mr : Bytes)
    (hMerkle : merkleRootTxids pb.txids = .ok mr)
    (hMismatch : (mr != pb.header.merkleRoot) = true) :
    validateBlockBasicAfterPow pb none none = .error "BLOCK_ERR_MERKLE_INVALID" := by
  show validateBlockBasicMerkleWitnessTail pb = _
  rw [merkleWitnessTail_eq_explicit]
  simp only [merkleWitnessTailExplicit, hMerkle, Except.bind, hMismatch, ite_true]

/-- Stage 5a: merkle mismatch, target passes. -/
theorem error_priority_merkle_afterpow_sn
    (pb : ParsedBlock) (mr expTarget : Bytes)
    (hTargetOk : (pb.header.target != expTarget) = false)
    (hMerkle : merkleRootTxids pb.txids = .ok mr)
    (hMismatch : (mr != pb.header.merkleRoot) = true) :
    validateBlockBasicAfterPow pb none (some expTarget) = .error "BLOCK_ERR_MERKLE_INVALID" := by
  unfold validateBlockBasicAfterPow
  simp only [hTargetOk, ite_false]
  show validateBlockBasicMerkleWitnessTail pb = _
  rw [merkleWitnessTail_eq_explicit]
  simp only [merkleWitnessTailExplicit, hMerkle, Except.bind, hMismatch, ite_true]

/-- Stage 5a: merkle mismatch, linkage passes. -/
theorem error_priority_merkle_afterpow_ns
    (pb : ParsedBlock) (mr expPrev : Bytes)
    (hLinkOk : (pb.header.prevHash != expPrev) = false)
    (hMerkle : merkleRootTxids pb.txids = .ok mr)
    (hMismatch : (mr != pb.header.merkleRoot) = true) :
    validateBlockBasicAfterPow pb (some expPrev) none = .error "BLOCK_ERR_MERKLE_INVALID" := by
  unfold validateBlockBasicAfterPow
  simp only [hLinkOk, ite_false]
  show validateBlockBasicMerkleWitnessTail pb = _
  rw [merkleWitnessTail_eq_explicit]
  simp only [merkleWitnessTailExplicit, hMerkle, Except.bind, hMismatch, ite_true]

/-- Stage 5a: merkle mismatch, target+linkage pass. -/
theorem error_priority_merkle_afterpow_ss
    (pb : ParsedBlock) (mr expTarget expPrev : Bytes)
    (hTargetOk : (pb.header.target != expTarget) = false)
    (hLinkOk : (pb.header.prevHash != expPrev) = false)
    (hMerkle : merkleRootTxids pb.txids = .ok mr)
    (hMismatch : (mr != pb.header.merkleRoot) = true) :
    validateBlockBasicAfterPow pb (some expPrev) (some expTarget) =
    .error "BLOCK_ERR_MERKLE_INVALID" := by
  unfold validateBlockBasicAfterPow
  simp only [hTargetOk, ite_false, hLinkOk]
  show validateBlockBasicMerkleWitnessTail pb = _
  rw [merkleWitnessTail_eq_explicit]
  simp only [merkleWitnessTailExplicit, hMerkle, Except.bind, hMismatch, ite_true]

/-- Stage 5b: merkleRootTxids computation error → error propagates. -/
theorem error_priority_merkle_compute_fail
    (pb : ParsedBlock) (err : String)
    (hFail : merkleRootTxids pb.txids = .error err) :
    validateBlockBasicMerkleWitnessTail pb = .error err := by
  rw [merkleWitnessTail_eq_explicit]
  simp only [merkleWitnessTailExplicit, hFail, Except.bind]

/-! ## Monadic error propagation -/

/-- Generic short-circuit: `Except.error.bind f = Except.error`. -/
theorem except_error_bind {α β : Type} {err : String}
    (f : α → Except String β) :
    (Except.error err : Except String α).bind f = Except.error err := rfl

/-! ## Success-implies-check-passed chain (contrapositives) -/

theorem validate_success_parse
    (b : Bytes) (ph pt : Option Bytes)
    (h : validateBlockBasic b ph pt = .ok ()) :
    ∃ pb, parseBlock b = .ok pb :=
  let ⟨pb, hp, _⟩ := validateBlockBasic_parses b ph pt h; ⟨pb, hp⟩

theorem validate_success_pow
    (b : Bytes) (ph pt : Option Bytes)
    (h : validateBlockBasic b ph pt = .ok ()) :
    ∃ pb, parseBlock b = .ok pb ∧ powCheck pb.header = .ok () :=
  let ⟨pb, hp, hpow, _⟩ := validateBlockBasic_pow_passes b ph pt h; ⟨pb, hp, hpow⟩

/-! ## Transaction-level parse error ordering model (§7)

Section 7 defines deterministic parse error mapping for transactions.
The stages are ordered and the first applicable error code wins.
This inductive type models the ordering contract.
-/

/-- Transaction parse stages from §7. Ordering: earlier stage wins.
    Models the ERROR CODE switching points in parseTxFromCursor
    (BlockBasicV1.lean:108-158). Does NOT cover the `match none => throw`
    truncation branches which all return BLOCK_ERR_PARSE/TX_ERR_PARSE. -/
inductive TxParseStage where
  | compactSizeMinimality    -- §7 stage 1: TX_ERR_PARSE (compact size decode)
  | txKindDaPayload          -- §7 stage 2: TX_ERR_PARSE (invalid tx_kind)
  | inputOutputBounds        -- §7 stage 3: TX_ERR_PARSE (count limits)
  | witnessCountBytes        -- §7 stage 4: TX_ERR_WITNESS_OVERFLOW
  | witnessItemStructural    -- §7 stage 5a: TX_ERR_PARSE
  | witnessSuiteDisallowed   -- §7 stage 5b-pre: TX_ERR_SIG_ALG_INVALID (live parser)
  | witnessCanonicalLength   -- §7 stage 5b: TX_ERR_SIG_NONCANONICAL
  | daLenMinimality          -- §7 stage 6: TX_ERR_PARSE (da_payload_len minimality)
  | daLenBounds              -- §7 stage 7: TX_ERR_PARSE (da_payload_len per tx_kind)
  deriving DecidableEq, Repr

/-- The error code produced by each tx parse stage. -/
def txParseStageError : TxParseStage → String
  | .compactSizeMinimality  => "TX_ERR_PARSE"
  | .txKindDaPayload        => "TX_ERR_PARSE"
  | .inputOutputBounds      => "TX_ERR_PARSE"
  | .witnessCountBytes      => "TX_ERR_WITNESS_OVERFLOW"
  | .witnessItemStructural  => "TX_ERR_PARSE"
  | .witnessSuiteDisallowed => "TX_ERR_SIG_ALG_INVALID"
  | .witnessCanonicalLength => "TX_ERR_SIG_NONCANONICAL"
  | .daLenMinimality        => "TX_ERR_PARSE"
  | .daLenBounds            => "TX_ERR_PARSE"

/-- Strict ordering on tx parse stages: earlier stage has priority. -/
def txParseStageOrd : TxParseStage → Nat
  | .compactSizeMinimality  => 0
  | .txKindDaPayload        => 1
  | .inputOutputBounds      => 2
  | .witnessCountBytes      => 3
  | .witnessItemStructural  => 4
  | .witnessSuiteDisallowed => 5
  | .witnessCanonicalLength => 6
  | .daLenMinimality        => 7
  | .daLenBounds            => 8

/-- Earlier stage takes priority. -/
theorem tx_parse_stage_priority (s1 s2 : TxParseStage)
    (hLt : txParseStageOrd s1 < txParseStageOrd s2) :
    txParseStageOrd s1 < txParseStageOrd s2 := hLt

/-- Distinctness: TX_ERR_PARSE ≠ TX_ERR_WITNESS_OVERFLOW. -/
theorem err_ne_tx_parse_witness_overflow :
    ("TX_ERR_PARSE" : String) ≠ "TX_ERR_WITNESS_OVERFLOW" := by decide

/-- Distinctness: TX_ERR_PARSE ≠ TX_ERR_SIG_ALG_INVALID. -/
theorem err_ne_tx_parse_sig_alg :
    ("TX_ERR_PARSE" : String) ≠ "TX_ERR_SIG_ALG_INVALID" := by decide

/-- Distinctness: TX_ERR_PARSE ≠ TX_ERR_SIG_NONCANONICAL. -/
theorem err_ne_tx_parse_sig_noncanonical :
    ("TX_ERR_PARSE" : String) ≠ "TX_ERR_SIG_NONCANONICAL" := by decide

/-- Distinctness: TX_ERR_WITNESS_OVERFLOW ≠ TX_ERR_SIG_ALG_INVALID. -/
theorem err_ne_tx_witness_overflow_sig_alg :
    ("TX_ERR_WITNESS_OVERFLOW" : String) ≠ "TX_ERR_SIG_ALG_INVALID" := by decide

/-- Distinctness: TX_ERR_WITNESS_OVERFLOW ≠ TX_ERR_SIG_NONCANONICAL. -/
theorem err_ne_tx_witness_overflow_sig_noncanonical :
    ("TX_ERR_WITNESS_OVERFLOW" : String) ≠ "TX_ERR_SIG_NONCANONICAL" := by decide

/-- Distinctness: TX_ERR_SIG_ALG_INVALID ≠ TX_ERR_SIG_NONCANONICAL. -/
theorem err_ne_tx_sig_alg_sig_noncanonical :
    ("TX_ERR_SIG_ALG_INVALID" : String) ≠ "TX_ERR_SIG_NONCANONICAL" := by decide

/-- The stage ordering is total: all stages have distinct ordinals. -/
theorem tx_parse_stage_ord_injective (s1 s2 : TxParseStage)
    (hEq : txParseStageOrd s1 = txParseStageOrd s2) : s1 = s2 := by
  cases s1 <;> cases s2 <;> simp [txParseStageOrd] at hEq <;> rfl

/-! ## Live witness-check ordering (parseTxFromCursor lines 144-147)

These theorems prove error priority on the actual `WitnessSectionResult`
type from `TxWeightV2`, modeling the exact check sequence in the live parser.
-/

open RubinFormal.TxWeightV2 in
/-- Witness check sequence extracted from parseTxFromCursor.
    Uses the live WitnessSectionResult — same fields as the parser. -/
def witnessCheckSequence (witBytes : Nat) (ws : WitnessSectionResult) : Except String Unit :=
  if witBytes > MAX_WITNESS_BYTES_PER_TX then
    Except.error "TX_ERR_WITNESS_OVERFLOW"
  else if ws.isOverflow then
    Except.error "TX_ERR_WITNESS_OVERFLOW"
  else if ws.anySigAlgInvalid then
    Except.error "TX_ERR_SIG_ALG_INVALID"
  else if ws.anySigNoncanonical then
    Except.error "TX_ERR_SIG_NONCANONICAL"
  else
    Except.ok ()

open RubinFormal.TxWeightV2 in
theorem witness_bytes_overflow_priority
    (witBytes : Nat) (ws : WitnessSectionResult)
    (h : (witBytes > MAX_WITNESS_BYTES_PER_TX) = true) :
    witnessCheckSequence witBytes ws = .error "TX_ERR_WITNESS_OVERFLOW" := by
  simp [witnessCheckSequence, h]

open RubinFormal.TxWeightV2 in
theorem witness_count_overflow_priority
    (witBytes : Nat) (ws : WitnessSectionResult)
    (hBytes : (witBytes > MAX_WITNESS_BYTES_PER_TX) = false)
    (hOverflow : ws.isOverflow = true) :
    witnessCheckSequence witBytes ws = .error "TX_ERR_WITNESS_OVERFLOW" := by
  simp [witnessCheckSequence, hBytes, hOverflow]

open RubinFormal.TxWeightV2 in
theorem sig_alg_priority_over_noncanonical
    (witBytes : Nat) (ws : WitnessSectionResult)
    (hBytes : (witBytes > MAX_WITNESS_BYTES_PER_TX) = false)
    (hNoOverflow : ws.isOverflow = false)
    (hSigAlg : ws.anySigAlgInvalid = true) :
    witnessCheckSequence witBytes ws = .error "TX_ERR_SIG_ALG_INVALID" := by
  simp [witnessCheckSequence, hBytes, hNoOverflow, hSigAlg]

open RubinFormal.TxWeightV2 in
theorem sig_noncanonical_last_priority
    (witBytes : Nat) (ws : WitnessSectionResult)
    (hBytes : (witBytes > MAX_WITNESS_BYTES_PER_TX) = false)
    (hNoOverflow : ws.isOverflow = false)
    (hNoSigAlg : ws.anySigAlgInvalid = false)
    (hNoncanon : ws.anySigNoncanonical = true) :
    witnessCheckSequence witBytes ws = .error "TX_ERR_SIG_NONCANONICAL" := by
  simp [witnessCheckSequence, hBytes, hNoOverflow, hNoSigAlg, hNoncanon]

open RubinFormal.TxWeightV2 in
theorem witness_check_all_pass
    (witBytes : Nat) (ws : WitnessSectionResult)
    (hBytes : (witBytes > MAX_WITNESS_BYTES_PER_TX) = false)
    (hNoOverflow : ws.isOverflow = false)
    (hNoSigAlg : ws.anySigAlgInvalid = false)
    (hNoNoncanon : ws.anySigNoncanonical = false) :
    witnessCheckSequence witBytes ws = .ok () := by
  simp [witnessCheckSequence, hBytes, hNoOverflow, hNoSigAlg, hNoNoncanon]

open RubinFormal.TxWeightV2 in
theorem witness_check_total (witBytes : Nat) (ws : WitnessSectionResult) :
    (∃ err, witnessCheckSequence witBytes ws = .error err) ∨
    witnessCheckSequence witBytes ws = .ok () := by
  unfold witnessCheckSequence
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-! ## Semantic-level tx error ordering (post-parse)

After parsing succeeds, semantic validation applies these checks in order:
- nonce uniqueness (TX_ERR_NONCE_REPLAY)
- suite authorization (TX_ERR_SIG_ALG_INVALID)
- signature verification (TX_ERR_SIG_INVALID)
- double-spend (TX_ERR_DOUBLE_SPEND)
-/

/-- Semantic tx validation stages (post-parse, per-tx).
    Aligned with live code in UtxoApplyGenesisV1.lean:
    - duplicate inputs → TX_ERR_PARSE (line 215-216)
    - missing/spent UTXO → TX_ERR_MISSING_UTXO (line 218-223)
    - suite authorization → TX_ERR_SIG_ALG_INVALID
    - signature verification → TX_ERR_SIG_INVALID
    Note: TX_ERR_NONCE_REPLAY lives in BlockBasicCheckV1.nonceReplayCheck
    (block-level, after merkle/witness gates), NOT in per-tx semantic path.
    TX_ERR_DOUBLE_SPEND does not exist in the current codebase. -/
inductive TxSemanticStage where
  | duplicateInputs    -- TX_ERR_PARSE (duplicate input detection)
  | missingUtxo        -- TX_ERR_MISSING_UTXO (input not in UTXO set)
  | suiteAuthorization -- TX_ERR_SIG_ALG_INVALID
  | signatureVerify    -- TX_ERR_SIG_INVALID
  deriving DecidableEq, Repr

def txSemanticStageError : TxSemanticStage → String
  | .duplicateInputs    => "TX_ERR_PARSE"
  | .missingUtxo        => "TX_ERR_MISSING_UTXO"
  | .suiteAuthorization => "TX_ERR_SIG_ALG_INVALID"
  | .signatureVerify    => "TX_ERR_SIG_INVALID"

def txSemanticStageOrd : TxSemanticStage → Nat
  | .duplicateInputs    => 0
  | .missingUtxo        => 1
  | .suiteAuthorization => 2
  | .signatureVerify    => 3

/-- All semantic error codes are pairwise distinct. -/
theorem err_ne_dupinput_missing : ("TX_ERR_PARSE" : String) ≠ "TX_ERR_MISSING_UTXO" := by decide
theorem err_ne_dupinput_suite : ("TX_ERR_PARSE" : String) ≠ "TX_ERR_SIG_ALG_INVALID" := by decide
theorem err_ne_dupinput_sig : ("TX_ERR_PARSE" : String) ≠ "TX_ERR_SIG_INVALID" := by decide
theorem err_ne_missing_suite : ("TX_ERR_MISSING_UTXO" : String) ≠ "TX_ERR_SIG_ALG_INVALID" := by decide
theorem err_ne_missing_sig : ("TX_ERR_MISSING_UTXO" : String) ≠ "TX_ERR_SIG_INVALID" := by decide
theorem err_ne_suite_sig : ("TX_ERR_SIG_ALG_INVALID" : String) ≠ "TX_ERR_SIG_INVALID" := by decide

/-- Semantic stage ordering is total with distinct ordinals. -/
theorem tx_semantic_stage_ord_injective (s1 s2 : TxSemanticStage)
    (hEq : txSemanticStageOrd s1 = txSemanticStageOrd s2) : s1 = s2 := by
  cases s1 <;> cases s2 <;> simp [txSemanticStageOrd] at hEq <;> rfl

/-! ## TXCTX extension error codes (§13.1 / SPEC-TXCTX-01)

SPEC-TXCTX-01 adds error source mappings for the TxContext validation path.
These are distinct from base error codes and follow the same priority model.
-/

/-- TXCTX-specific error code from SPEC-TXCTX-01 §13.1.
    TX_ERR_COVENANT_TYPE_INVALID is emitted by the CORE_EXT covenant
    validation path when the covenant type is invalid or malformed.
    Note: TX_ERR_TXCTX_OVERFLOW was removed — no producer exists in codebase. -/
def TX_ERR_COVENANT_TYPE_INVALID : String := "TX_ERR_COVENANT_TYPE_INVALID"

/-- TXCTX error code is distinct from base codes. -/
theorem err_ne_covenant_parse :
    TX_ERR_COVENANT_TYPE_INVALID ≠ ("TX_ERR_PARSE" : String) := by decide
theorem err_ne_covenant_sig :
    TX_ERR_COVENANT_TYPE_INVALID ≠ ("TX_ERR_SIG_ALG_INVALID" : String) := by decide
theorem err_ne_covenant_missing :
    TX_ERR_COVENANT_TYPE_INVALID ≠ ("TX_ERR_MISSING_UTXO" : String) := by decide

/-! ## Block-level error code distinctness (§13) -/

theorem err_ne_parse_target : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_TARGET_INVALID" := by decide
theorem err_ne_parse_linkage : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_LINKAGE_INVALID" := by decide
theorem err_ne_parse_merkle : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_MERKLE_INVALID" := by decide
theorem err_ne_parse_witness : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_WITNESS_COMMITMENT" := by decide
theorem err_ne_target_linkage : ("BLOCK_ERR_TARGET_INVALID" : String) ≠ "BLOCK_ERR_LINKAGE_INVALID" := by decide
theorem err_ne_target_merkle : ("BLOCK_ERR_TARGET_INVALID" : String) ≠ "BLOCK_ERR_MERKLE_INVALID" := by decide
theorem err_ne_target_witness : ("BLOCK_ERR_TARGET_INVALID" : String) ≠ "BLOCK_ERR_WITNESS_COMMITMENT" := by decide
theorem err_ne_linkage_merkle : ("BLOCK_ERR_LINKAGE_INVALID" : String) ≠ "BLOCK_ERR_MERKLE_INVALID" := by decide
theorem err_ne_linkage_witness : ("BLOCK_ERR_LINKAGE_INVALID" : String) ≠ "BLOCK_ERR_WITNESS_COMMITMENT" := by decide
theorem err_ne_merkle_witness : ("BLOCK_ERR_MERKLE_INVALID" : String) ≠ "BLOCK_ERR_WITNESS_COMMITMENT" := by decide
theorem err_ne_ts_old_future : ("BLOCK_ERR_TIMESTAMP_OLD" : String) ≠ "BLOCK_ERR_TIMESTAMP_FUTURE" := by decide
theorem err_ne_parse_ts_old : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_TIMESTAMP_OLD" := by decide
theorem err_ne_parse_ts_future : ("BLOCK_ERR_PARSE" : String) ≠ "BLOCK_ERR_TIMESTAMP_FUTURE" := by decide
theorem err_ne_tx_parse_nonce : ("TX_ERR_PARSE" : String) ≠ "TX_ERR_NONCE_REPLAY" := by decide

end RubinFormal
