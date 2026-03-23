import RubinFormal.BlockValidationOrder
import RubinFormal.UtxoApplyGenesisV1

/-!
# Error Priority Ordering (§13 / §25)

## Block-level (§25) — on live `validateBlockBasic`
Direct error propagation for all 6 stages: parse → PoW → target →
linkage → merkle (via explicit-bind equivalence) → witness (existing).

## Tx-level — live sub-function decomposition
- `applyWitnessChecks` (LIVE, called from `parseTxFromCursor`):
  OVERFLOW → SIG_ALG_INVALID → SIG_NONCANONICAL ordering via rfl equivalence.
- `applyDaLenChecks` (LIVE, called from `parseTxFromCursor`):
  4 DA-length checks, all TX_ERR_PARSE.
- `applyTxPreInputChecks` (LIVE, called from `applyNonCoinbaseTxBasicNoCrypto`):
  empty inputs → nonce invalid → output covenant loop.
- `validateInputStructural` (LIVE, per-input loop):
  scriptSig → sequence → coinbase prevout.

## Not covered
- `parseTxFromCursor` header/bounds (lines 108-139): all TX_ERR_PARSE.
- Per-input UTXO lookup/duplicate/covenant-type: mutable state in for-loop.
- Error code distinctness: all block + tx codes via `by decide`.
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
    DISAMBIGUATION: when powCheck passes, this error is unambiguously from
    target mismatch (stage 3), not from malformed target (stage 2).
    powCheck validates target well-formedness; stage 3 checks expected match. -/
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

/-- TARGET DISAMBIGUATION: after powCheck succeeds, BLOCK_ERR_TARGET_INVALID
    is unambiguously from stage 3 (mismatch), not stage 2 (malformed).
    powCheck validates target well-formedness; stage 3 validates expected match. -/
theorem target_error_disambiguated
    (blockBytes : Bytes) (ph : Option Bytes)
    (pb : ParsedBlock) (expTarget : Bytes)
    (hParse : parseBlock blockBytes = .ok pb)
    (hPow : powCheck pb.header = .ok ())
    (hMismatch : (pb.header.target != expTarget) = true) :
    validateBlockBasic blockBytes ph (some expTarget) =
    .error "BLOCK_ERR_TARGET_INVALID" ∧ powCheck pb.header = .ok () := by
  constructor
  · unfold validateBlockBasic; rw [hParse]
    show (do powCheck pb.header; _) = _; rw [hPow]
    simp only [hMismatch, ite_true]; rfl
  · exact hPow

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

/-! ## Tx-level error code distinctness (§7/§13)

Pairwise inequality for all tx error codes used in the validation pipeline.
Ordering is proved via live sub-function decomposition (see sections below),
not via enum models.
-/

theorem err_ne_tx_parse_witness_overflow :
    ("TX_ERR_PARSE" : String) ≠ "TX_ERR_WITNESS_OVERFLOW" := by decide
theorem err_ne_tx_parse_sig_alg :
    ("TX_ERR_PARSE" : String) ≠ "TX_ERR_SIG_ALG_INVALID" := by decide
theorem err_ne_tx_parse_sig_noncanonical :
    ("TX_ERR_PARSE" : String) ≠ "TX_ERR_SIG_NONCANONICAL" := by decide
theorem err_ne_tx_witness_overflow_sig_alg :
    ("TX_ERR_WITNESS_OVERFLOW" : String) ≠ "TX_ERR_SIG_ALG_INVALID" := by decide
theorem err_ne_tx_witness_overflow_sig_noncanonical :
    ("TX_ERR_WITNESS_OVERFLOW" : String) ≠ "TX_ERR_SIG_NONCANONICAL" := by decide
theorem err_ne_tx_sig_alg_sig_noncanonical :
    ("TX_ERR_SIG_ALG_INVALID" : String) ≠ "TX_ERR_SIG_NONCANONICAL" := by decide
theorem err_ne_tx_parse_missing_utxo :
    ("TX_ERR_PARSE" : String) ≠ "TX_ERR_MISSING_UTXO" := by decide
theorem err_ne_tx_missing_utxo_sig_alg :
    ("TX_ERR_MISSING_UTXO" : String) ≠ "TX_ERR_SIG_ALG_INVALID" := by decide
theorem err_ne_tx_missing_utxo_sig_invalid :
    ("TX_ERR_MISSING_UTXO" : String) ≠ "TX_ERR_SIG_INVALID" := by decide
theorem err_ne_tx_sig_alg_sig_invalid :
    ("TX_ERR_SIG_ALG_INVALID" : String) ≠ "TX_ERR_SIG_INVALID" := by decide
theorem err_ne_tx_covenant_parse :
    ("TX_ERR_COVENANT_TYPE_INVALID" : String) ≠ "TX_ERR_PARSE" := by decide
theorem err_ne_tx_covenant_sig_alg :
    ("TX_ERR_COVENANT_TYPE_INVALID" : String) ≠ "TX_ERR_SIG_ALG_INVALID" := by decide
theorem err_ne_tx_covenant_missing :
    ("TX_ERR_COVENANT_TYPE_INVALID" : String) ≠ "TX_ERR_MISSING_UTXO" := by decide

/-! ## Live witness-check ordering (applyWitnessChecks — called from parseTxFromCursor)

`applyWitnessChecks` is a LIVE sub-function extracted from parseTxFromCursor.
It is called directly by parseTxFromCursor (BlockBasicV1.lean) — not a proof-only
decomposition. Error ordering is proved via explicit-bind equivalence.
-/

open RubinFormal.TxWeightV2 in
/-- Explicit-bind version of applyWitnessChecks (no join points). -/
def applyWitnessChecksExplicit (ws : WitnessSectionResult) : Except String Unit :=
  let witBytes := ws.endOff - ws.startOff
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
/-- Definitional equivalence: live do-version = explicit bind version. -/
theorem applyWitnessChecks_eq_explicit (ws : WitnessSectionResult) :
    applyWitnessChecks ws = applyWitnessChecksExplicit ws := by
  simp only [applyWitnessChecks, applyWitnessChecksExplicit, Except.bind]; rfl

-- Ordering theorems on the LIVE applyWitnessChecks function

open RubinFormal.TxWeightV2 in
theorem witness_bytes_overflow_priority (ws : WitnessSectionResult)
    (h : (ws.endOff - ws.startOff > MAX_WITNESS_BYTES_PER_TX) = true) :
    applyWitnessChecks ws = .error "TX_ERR_WITNESS_OVERFLOW" := by
  rw [applyWitnessChecks_eq_explicit]; simp [applyWitnessChecksExplicit, h]

open RubinFormal.TxWeightV2 in
theorem witness_count_overflow_priority (ws : WitnessSectionResult)
    (hBytes : (ws.endOff - ws.startOff > MAX_WITNESS_BYTES_PER_TX) = false)
    (hOverflow : ws.isOverflow = true) :
    applyWitnessChecks ws = .error "TX_ERR_WITNESS_OVERFLOW" := by
  rw [applyWitnessChecks_eq_explicit]; simp [applyWitnessChecksExplicit, hBytes, hOverflow]

open RubinFormal.TxWeightV2 in
theorem sig_alg_priority_over_noncanonical (ws : WitnessSectionResult)
    (hBytes : (ws.endOff - ws.startOff > MAX_WITNESS_BYTES_PER_TX) = false)
    (hNoOverflow : ws.isOverflow = false)
    (hSigAlg : ws.anySigAlgInvalid = true) :
    applyWitnessChecks ws = .error "TX_ERR_SIG_ALG_INVALID" := by
  rw [applyWitnessChecks_eq_explicit]; simp [applyWitnessChecksExplicit, hBytes, hNoOverflow, hSigAlg]

open RubinFormal.TxWeightV2 in
theorem sig_noncanonical_last_priority (ws : WitnessSectionResult)
    (hBytes : (ws.endOff - ws.startOff > MAX_WITNESS_BYTES_PER_TX) = false)
    (hNoOverflow : ws.isOverflow = false)
    (hNoSigAlg : ws.anySigAlgInvalid = false)
    (hNoncanon : ws.anySigNoncanonical = true) :
    applyWitnessChecks ws = .error "TX_ERR_SIG_NONCANONICAL" := by
  rw [applyWitnessChecks_eq_explicit]; simp [applyWitnessChecksExplicit, hBytes, hNoOverflow, hNoSigAlg, hNoncanon]

open RubinFormal.TxWeightV2 in
theorem witness_check_all_pass (ws : WitnessSectionResult)
    (hBytes : (ws.endOff - ws.startOff > MAX_WITNESS_BYTES_PER_TX) = false)
    (hNoOverflow : ws.isOverflow = false)
    (hNoSigAlg : ws.anySigAlgInvalid = false)
    (hNoNoncanon : ws.anySigNoncanonical = false) :
    applyWitnessChecks ws = .ok () := by
  rw [applyWitnessChecks_eq_explicit]; simp [applyWitnessChecksExplicit, hBytes, hNoOverflow, hNoSigAlg, hNoNoncanon]

open RubinFormal.TxWeightV2 in
theorem witness_check_total (ws : WitnessSectionResult) :
    (∃ err, applyWitnessChecks ws = .error err) ∨
    applyWitnessChecks ws = .ok () := by
  rw [applyWitnessChecks_eq_explicit]
  unfold applyWitnessChecksExplicit
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all
  split <;> simp_all

/-! ## Top-level merkle error propagation on validateBlockBasic -/

theorem error_priority_merkle_top_nn
    (blockBytes : Bytes) (pb : ParsedBlock) (mr : Bytes)
    (hParse : parseBlock blockBytes = .ok pb)
    (hPow : powCheck pb.header = .ok ())
    (hMerkle : merkleRootTxids pb.txids = .ok mr)
    (hMismatch : (mr != pb.header.merkleRoot) = true) :
    validateBlockBasic blockBytes none none = .error "BLOCK_ERR_MERKLE_INVALID" := by
  unfold validateBlockBasic; rw [hParse]
  show (do powCheck pb.header; _) = _; rw [hPow]
  exact error_priority_merkle_afterpow_nn pb mr hMerkle hMismatch

theorem error_priority_merkle_top_sn
    (blockBytes : Bytes) (pb : ParsedBlock) (mr expTarget : Bytes)
    (hParse : parseBlock blockBytes = .ok pb)
    (hPow : powCheck pb.header = .ok ())
    (hTargetOk : (pb.header.target != expTarget) = false)
    (hMerkle : merkleRootTxids pb.txids = .ok mr)
    (hMismatch : (mr != pb.header.merkleRoot) = true) :
    validateBlockBasic blockBytes none (some expTarget) = .error "BLOCK_ERR_MERKLE_INVALID" := by
  unfold validateBlockBasic; rw [hParse]
  show (do powCheck pb.header; _) = _; rw [hPow]
  simp only [hTargetOk, ite_false]
  exact error_priority_merkle_afterpow_nn pb mr hMerkle hMismatch

theorem error_priority_merkle_top_ns
    (blockBytes : Bytes) (pb : ParsedBlock) (mr expPrev : Bytes)
    (hParse : parseBlock blockBytes = .ok pb)
    (hPow : powCheck pb.header = .ok ())
    (hLinkOk : (pb.header.prevHash != expPrev) = false)
    (hMerkle : merkleRootTxids pb.txids = .ok mr)
    (hMismatch : (mr != pb.header.merkleRoot) = true) :
    validateBlockBasic blockBytes (some expPrev) none = .error "BLOCK_ERR_MERKLE_INVALID" := by
  unfold validateBlockBasic; rw [hParse]
  show (do powCheck pb.header; _) = _; rw [hPow]
  simp only [hLinkOk, ite_false]
  exact error_priority_merkle_afterpow_nn pb mr hMerkle hMismatch

theorem error_priority_merkle_top_ss
    (blockBytes : Bytes) (pb : ParsedBlock) (mr expTarget expPrev : Bytes)
    (hParse : parseBlock blockBytes = .ok pb)
    (hPow : powCheck pb.header = .ok ())
    (hTargetOk : (pb.header.target != expTarget) = false)
    (hLinkOk : (pb.header.prevHash != expPrev) = false)
    (hMerkle : merkleRootTxids pb.txids = .ok mr)
    (hMismatch : (mr != pb.header.merkleRoot) = true) :
    validateBlockBasic blockBytes (some expPrev) (some expTarget) = .error "BLOCK_ERR_MERKLE_INVALID" := by
  unfold validateBlockBasic; rw [hParse]
  show (do powCheck pb.header; _) = _; rw [hPow]
  simp only [hTargetOk, ite_false, hLinkOk]
  exact error_priority_merkle_afterpow_nn pb mr hMerkle hMismatch

/-! ## Live semantic tx pre-input ordering (applyTxPreInputChecks)

`applyTxPreInputChecks` is a LIVE sub-function called from
`applyNonCoinbaseTxBasicNoCrypto`. Ordering proved by unfold+rw
on the top checks of the do-block.
-/

open UtxoApplyGenesisV1 in
theorem preinput_empty_inputs_priority
    (tx : UtxoBasicV1.Tx) (height : Nat)
    (h : (tx.inputs.length == 0) = true) :
    applyTxPreInputChecks tx height = .error "TX_ERR_PARSE" := by
  unfold applyTxPreInputChecks; rw [h]; rfl

open UtxoApplyGenesisV1 in
theorem preinput_nonce_zero_priority
    (tx : UtxoBasicV1.Tx) (height : Nat)
    (hInputs : (tx.inputs.length == 0) = false)
    (hNonce : (tx.txNonce == 0) = true) :
    applyTxPreInputChecks tx height = .error "TX_ERR_TX_NONCE_INVALID" := by
  unfold applyTxPreInputChecks
  rw [show (tx.inputs.length == 0) = false from hInputs]
  simp only [hNonce, ite_true]; rfl

/-! ## Live DA-len checks ordering (applyDaLenChecks)

`applyDaLenChecks` is a LIVE sub-function called from `parseTxFromCursor`.
All checks produce TX_ERR_PARSE.
-/

open BlockBasicV1 in
theorem dalen_minimality_priority
    (tk daLen : Nat) (minDa : Bool)
    (h : minDa = false) :
    applyDaLenChecks tk daLen minDa = .error "TX_ERR_PARSE" := by
  unfold applyDaLenChecks; rw [h]; rfl

open BlockBasicV1 in
theorem dalen_kind0_nonzero
    (daLen : Nat)
    (h : (daLen != 0) = true) :
    applyDaLenChecks 0x00 daLen true = .error "TX_ERR_PARSE" := by
  unfold applyDaLenChecks; simp [h]; rfl

open BlockBasicV1 in
theorem dalen_kind1_overflow
    (daLen : Nat)
    (h : (daLen > DaCoreV1.MAX_DA_MANIFEST_BYTES_PER_TX) = true) :
    applyDaLenChecks 0x01 daLen true = .error "TX_ERR_PARSE" := by
  unfold applyDaLenChecks; simp [h]; rfl

open BlockBasicV1 in
theorem dalen_kind2_bounds
    (tk daLen : Nat)
    (hNotZero : (tk == 0x00) = false)
    (hNotOne : (tk == 0x01) = false)
    (h : (daLen < 1 || daLen > DaCoreV1.CHUNK_BYTES) = true) :
    applyDaLenChecks tk daLen true = .error "TX_ERR_PARSE" := by
  unfold applyDaLenChecks; simp [hNotZero, hNotOne, h]; rfl

/-! ## Per-input structural ordering (validateInputStructural)

LIVE sub-function called from applyNonCoinbaseTxBasicNoCrypto per-input loop.
Ordering: scriptSig → sequence → coinbase prevout.
-/

open UtxoApplyGenesisV1 in
theorem input_scriptsig_priority
    (i : UtxoBasicV1.TxIn)
    (h : (i.scriptSig.size != 0) = true) :
    validateInputStructural i = .error "TX_ERR_PARSE" := by
  unfold validateInputStructural; rw [h]; rfl

open UtxoApplyGenesisV1 in
theorem input_sequence_priority
    (i : UtxoBasicV1.TxIn)
    (hSS : (i.scriptSig.size != 0) = false)
    (h : (i.sequence > 0x7fffffff) = true) :
    validateInputStructural i = .error "TX_ERR_SEQUENCE_INVALID" := by
  simp [validateInputStructural, hSS, h]; rfl

open UtxoApplyGenesisV1 in
theorem input_coinbase_prevout_priority
    (i : UtxoBasicV1.TxIn)
    (hSS : (i.scriptSig.size != 0) = false)
    (hSeq : (i.sequence > 0x7fffffff) = false)
    (h : UtxoBasicV1.isCoinbasePrevout i = true) :
    validateInputStructural i = .error "TX_ERR_PARSE" := by
  simp [validateInputStructural, hSS, hSeq, h]; rfl

/-! ## Header/bounds parse checks (validateTxKind, validateInputCountMin, validateOutputCountMin)

LIVE sub-functions called from parseTxFromCursor. All throw TX_ERR_PARSE.
-/

open BlockBasicV1 in
theorem txkind_invalid (tk : Nat)
    (h : (!(tk == 0x00 || tk == 0x01 || tk == 0x02)) = true) :
    validateTxKind tk = .error "TX_ERR_PARSE" := by
  unfold validateTxKind; rw [h]; rfl

open BlockBasicV1 in
theorem input_count_min_fail (minIn : Bool) (h : minIn = false) :
    validateInputCountMin minIn = .error "TX_ERR_PARSE" := by
  unfold validateInputCountMin; rw [h]; rfl

open BlockBasicV1 in
theorem output_count_min_fail (minOut : Bool) (h : minOut = false) :
    validateOutputCountMin minOut = .error "TX_ERR_PARSE" := by
  unfold validateOutputCountMin; rw [h]; rfl

/-! ## Per-input UTXO lookup ordering (validateInputUtxoLookup)

LIVE sub-function called from per-input loop. Written without do-notation
to enable formal ordering proofs. Ordering: duplicate → missing → anchor/DA → coinbase.
-/

open UtxoApplyGenesisV1 in
theorem utxo_duplicate_priority (utxoEntry : Option UtxoBasicV1.UtxoEntry) (height : Nat) :
    validateInputUtxoLookup true utxoEntry height = .error "TX_ERR_PARSE" := by
  simp [validateInputUtxoLookup]

open UtxoApplyGenesisV1 in
theorem utxo_missing_priority (height : Nat) :
    validateInputUtxoLookup false none height = .error "TX_ERR_MISSING_UTXO" := by
  simp [validateInputUtxoLookup]

open UtxoApplyGenesisV1 in
theorem utxo_anchor_rejected (e : UtxoBasicV1.UtxoEntry) (height : Nat)
    (h : (e.covenantType == CovenantGenesisV1.COV_TYPE_ANCHOR || e.covenantType == CovenantGenesisV1.COV_TYPE_DA_COMMIT) = true) :
    validateInputUtxoLookup false (some e) height = .error "TX_ERR_MISSING_UTXO" := by
  simp [validateInputUtxoLookup, h]

open UtxoApplyGenesisV1 in
theorem utxo_coinbase_immature (e : UtxoBasicV1.UtxoEntry) (height : Nat)
    (hNotAnchor : (e.covenantType == CovenantGenesisV1.COV_TYPE_ANCHOR || e.covenantType == CovenantGenesisV1.COV_TYPE_DA_COMMIT) = false)
    (hCoinbase : e.createdByCoinbase = true)
    (hImmature : (height < e.creationHeight + UtxoBasicV1.COINBASE_MATURITY) = true) :
    validateInputUtxoLookup false (some e) height = .error "TX_ERR_COINBASE_IMMATURE" := by
  simp [validateInputUtxoLookup, hNotAnchor, hCoinbase, hImmature]

/-! ## Post-loop witness cursor (validateWitnessCursorComplete)

LIVE sub-function: validates all witness items consumed after per-input loop.
-/

open UtxoApplyGenesisV1 in
theorem witness_cursor_incomplete (cursor witnessLen : Nat)
    (h : (cursor != witnessLen) = true) :
    validateWitnessCursorComplete cursor witnessLen = .error "TX_ERR_PARSE" := by
  simp [validateWitnessCursorComplete, h]

/-! ## Full covenant dispatch ordering (dispatchCovenantValidation — LIVE)

`dispatchCovenantValidation` is a LIVE sub-function extracted from the per-input
for-loop body of `applyNonCoinbaseTxBasicNoCrypto` (lines 260-301).
Written without do-notation (explicit if/match) to enable formal proofs.

FULL DISPATCH PROOF: unknown covenant type → TX_ERR_COVENANT_TYPE_INVALID.
This is direct error propagation on the live function, not a model.
-/

open UtxoApplyGenesisV1 in
/-- FULL DISPATCH: unknown covenant type → exactly TX_ERR_COVENANT_TYPE_INVALID.
    All 4 known-type checks fail → else branch fires. Direct on live function. -/
theorem dispatch_unknown_covenant_error
    (e : UtxoBasicV1.UtxoEntry) (tx : UtxoBasicV1.Tx) (wc height mtp : Nat)
    (hNotP2PK : (e.covenantType == CovenantGenesisV1.COV_TYPE_P2PK) = false)
    (hNotMulti : (e.covenantType == CovenantGenesisV1.COV_TYPE_MULTISIG) = false)
    (hNotVault : (e.covenantType == CovenantGenesisV1.COV_TYPE_VAULT) = false)
    (hNotHtlc : (e.covenantType == CovenantGenesisV1.COV_TYPE_HTLC) = false) :
    dispatchCovenantValidation e tx wc height mtp = .error "TX_ERR_COVENANT_TYPE_INVALID" := by
  simp [dispatchCovenantValidation, hNotP2PK, hNotMulti, hNotVault, hNotHtlc]

/-! ## Value conservation (validateValueConservation — LIVE)

LIVE sub-function: post-loop check in applyNonCoinbaseTxBasicNoCrypto.
Written without do-notation.
-/

open UtxoApplyGenesisV1 in
theorem value_conservation_overspend (sumOut sumIn vic siv : Nat)
    (h : (sumOut > sumIn) = true) :
    validateValueConservation sumOut sumIn vic siv = .error "TX_ERR_VALUE_CONSERVATION" := by
  simp [validateValueConservation, h]

open UtxoApplyGenesisV1 in
theorem value_conservation_vault_drain (sumOut sumIn sumInVault : Nat)
    (_hNotOver : ¬ sumOut > sumIn)
    (hDrain : sumOut < sumInVault) :
    validateValueConservation sumOut sumIn 1 sumInVault = .error "TX_ERR_VALUE_CONSERVATION" := by
  simp [validateValueConservation]
  intro _ hGe
  omega

theorem err_ne_tx_value_parse : ("TX_ERR_VALUE_CONSERVATION" : String) ≠ "TX_ERR_PARSE" := by decide
theorem err_ne_tx_value_missing : ("TX_ERR_VALUE_CONSERVATION" : String) ≠ "TX_ERR_MISSING_UTXO" := by decide
theorem err_ne_tx_value_covenant : ("TX_ERR_VALUE_CONSERVATION" : String) ≠ "TX_ERR_COVENANT_TYPE_INVALID" := by decide

/-! ## Error code distinctness (§13) -/

theorem err_ne_block_tx_parse : ("BLOCK_ERR_PARSE" : String) ≠ "TX_ERR_PARSE" := by decide
theorem err_ne_tx_parse_seq : ("TX_ERR_PARSE" : String) ≠ "TX_ERR_SEQUENCE_INVALID" := by decide
theorem err_ne_tx_parse_coinbase : ("TX_ERR_PARSE" : String) ≠ "TX_ERR_COINBASE_IMMATURE" := by decide
theorem err_ne_tx_missing_coinbase : ("TX_ERR_MISSING_UTXO" : String) ≠ "TX_ERR_COINBASE_IMMATURE" := by decide
theorem err_ne_tx_parse_nonce_invalid : ("TX_ERR_PARSE" : String) ≠ "TX_ERR_TX_NONCE_INVALID" := by decide

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
