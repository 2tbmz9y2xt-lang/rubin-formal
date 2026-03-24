import RubinFormal.DaIntegrityV1
import RubinFormal.Conformance.CVDaIntegrityReplay

/-!
# DA Set Integrity Behavioral + Refinement Proofs (§21)

LIVE behavioral proofs on `validateDASetIntegrity` and `validateDaIntegrityGate`
(DaIntegrityV1.lean). Upgrades evidence_level from `baseline` to
`machine_checked_contract` by combining:

1. Conformance replay: `cv_da_integrity_vectors_pass` (native_decide on real vectors)
2. Gate error propagation: each gate step's error flows to the output deterministically
3. Empty-set acceptance: validateDASetIntegrity on [] = .ok ()
4. Constants: canonical DA parameters

Go equivalent: validateDASetIntegrity (consensus/da_integrity.go)
Rust equivalent: validate_da_set_integrity (rubin-consensus/src/da_integrity.rs)
-/

namespace RubinFormal
open DaIntegrityV1

/-! ## DA constants (canonical values from §21) -/

/-- DA chunk bytes constant is 524288 (512 KB). -/
theorem da_chunk_bytes_value : DaCoreV1.CHUNK_BYTES = 524288 := rfl

/-- Max DA chunk count is 61. -/
theorem da_max_chunk_count_value : DaCoreV1.MAX_DA_CHUNK_COUNT = 61 := rfl

/-- Total DA capacity: 61 chunks × 512 KB = 31_981_568 bytes. -/
theorem da_total_capacity : DaCoreV1.MAX_DA_CHUNK_COUNT * DaCoreV1.CHUNK_BYTES = 31981568 := by
  native_decide

/-- Max DA batches per block = 128. -/
theorem da_max_batches_value : MAX_DA_BATCHES_PER_BLOCK = 128 := rfl

/-- DA commit covenant type = 0x0103. -/
theorem da_cov_type_value : COV_TYPE_DA_COMMIT = 0x0103 := rfl

/-! ## Empty set acceptance (LIVE) -/

/-- validateDASetIntegrity on empty tx list = accepted.
    No DA txs = valid empty DA set. -/
theorem da_empty_txs_accepted :
    validateDASetIntegrity [] = .ok () := by
  unfold validateDASetIntegrity
  simp only [List.forIn, Std.RBMap.empty, Std.RBMap.size]
  rfl

/-! ## Batch count rejection (LIVE on validateDaBatchCount) -/

/-- Exceeds batch limit → BLOCK_ERR_DA_BATCH_EXCEEDED. -/
theorem da_batch_exceeded (n : Nat) (h : n > MAX_DA_BATCHES_PER_BLOCK) :
    validateDaBatchCount n = .error "BLOCK_ERR_DA_BATCH_EXCEEDED" := by
  simp only [validateDaBatchCount, h, ite_true]

/-- Within batch limit → accepted. -/
theorem da_batch_ok (n : Nat) (h : ¬(n > MAX_DA_BATCHES_PER_BLOCK)) :
    validateDaBatchCount n = .ok () := by
  simp only [validateDaBatchCount, h, ite_false]

/-- Boundary: MAX (128) is ok. -/
theorem da_batch_at_limit : validateDaBatchCount 128 = .ok () := by
  simp only [validateDaBatchCount, MAX_DA_BATCHES_PER_BLOCK, show ¬(128 > 128) from by omega, ite_false]

/-- Boundary: MAX+1 (129) is rejected. -/
theorem da_batch_over_limit : validateDaBatchCount 129 = .error "BLOCK_ERR_DA_BATCH_EXCEEDED" := by
  simp only [validateDaBatchCount, MAX_DA_BATCHES_PER_BLOCK, show 129 > 128 from by omega, ite_true]

/-! ## Chunk hash verification (LIVE on validateChunkHash) -/

/-- Hash mismatch → BLOCK_ERR_DA_CHUNK_HASH_INVALID. -/
theorem da_chunk_hash_mismatch (payload hash : Bytes) (h : (SHA3.sha3_256 payload != hash) = true) :
    validateChunkHash payload hash = .error "BLOCK_ERR_DA_CHUNK_HASH_INVALID" := by
  simp only [validateChunkHash, h, ite_true]

/-- Hash match → accepted. -/
theorem da_chunk_hash_ok (payload hash : Bytes) (h : (SHA3.sha3_256 payload != hash) = false) :
    validateChunkHash payload hash = .ok () := by
  simp only [validateChunkHash, h, ite_false]

/-! ## Gate error propagation (LIVE)

validateDaIntegrityGate = validateBlockBasic >> parseBlock >> validateDASetIntegrity.
Each step's error flows deterministically to the gate output.
-/

/-- Block validation failure → gate returns same error. -/
theorem da_gate_block_error (blockBytes : Bytes) (ph pt : Option Bytes) (err : String)
    (hB : BlockBasicV1.validateBlockBasic blockBytes ph pt = .error err) :
    validateDaIntegrityGate blockBytes ph pt = .error err := by
  unfold validateDaIntegrityGate; rw [hB]; rfl

/-- Block ok + parse failure → gate returns parse error. -/
theorem da_gate_parse_error (blockBytes : Bytes) (ph pt : Option Bytes) (err : String)
    (hB : BlockBasicV1.validateBlockBasic blockBytes ph pt = .ok ())
    (hP : BlockBasicV1.parseBlock blockBytes = .error err) :
    validateDaIntegrityGate blockBytes ph pt = .error err := by
  unfold validateDaIntegrityGate; rw [hB]
  show (do let pb ← BlockBasicV1.parseBlock blockBytes; validateDASetIntegrity pb.txs) = _
  rw [hP]; rfl

/-- Block ok + parse ok + DA integrity failure → gate returns DA error. -/
theorem da_gate_integrity_error (blockBytes : Bytes) (ph pt : Option Bytes)
    (pb : BlockBasicV1.ParsedBlock) (err : String)
    (hB : BlockBasicV1.validateBlockBasic blockBytes ph pt = .ok ())
    (hP : BlockBasicV1.parseBlock blockBytes = .ok pb)
    (hD : validateDASetIntegrity pb.txs = .error err) :
    validateDaIntegrityGate blockBytes ph pt = .error err := by
  unfold validateDaIntegrityGate; rw [hB]
  show (do let pb' ← BlockBasicV1.parseBlock blockBytes; validateDASetIntegrity pb'.txs) = _
  rw [hP]; exact hD

/-- All steps ok → gate ok. -/
theorem da_gate_all_ok (blockBytes : Bytes) (ph pt : Option Bytes)
    (pb : BlockBasicV1.ParsedBlock)
    (hB : BlockBasicV1.validateBlockBasic blockBytes ph pt = .ok ())
    (hP : BlockBasicV1.parseBlock blockBytes = .ok pb)
    (hD : validateDASetIntegrity pb.txs = .ok ()) :
    validateDaIntegrityGate blockBytes ph pt = .ok () := by
  unfold validateDaIntegrityGate; rw [hB]
  show (do let pb' ← BlockBasicV1.parseBlock blockBytes; validateDASetIntegrity pb'.txs) = _
  rw [hP]; exact hD

/-! ## Gate success invariants (LIVE)

Non-trivial: gate success implies ALL sub-steps passed.
Proved by contradiction (if any sub-step failed, gate would fail). -/

/-- Gate success → block validation passed. -/
theorem da_gate_ok_implies_block_ok (blockBytes : Bytes) (ph pt : Option Bytes)
    (hOk : validateDaIntegrityGate blockBytes ph pt = .ok ()) :
    BlockBasicV1.validateBlockBasic blockBytes ph pt = .ok () := by
  cases hBB : BlockBasicV1.validateBlockBasic blockBytes ph pt with
  | ok _ => rfl
  | error e =>
    exfalso; have : validateDaIntegrityGate blockBytes ph pt = .error e := by
      unfold validateDaIntegrityGate; rw [hBB]; rfl
    simp only [this] at hOk

/-- Gate success → parse ok AND DA integrity ok. -/
theorem da_gate_ok_implies_das_ok (blockBytes : Bytes) (ph pt : Option Bytes)
    (hOk : validateDaIntegrityGate blockBytes ph pt = .ok ()) :
    ∃ pb, BlockBasicV1.parseBlock blockBytes = .ok pb ∧
          validateDASetIntegrity pb.txs = .ok () := by
  have hB := da_gate_ok_implies_block_ok blockBytes ph pt hOk
  cases hP : BlockBasicV1.parseBlock blockBytes with
  | error e =>
    exfalso; have : validateDaIntegrityGate blockBytes ph pt = .error e := by
      unfold validateDaIntegrityGate; rw [hB]
      show (do let pb ← BlockBasicV1.parseBlock blockBytes; validateDASetIntegrity pb.txs) = _
      rw [hP]; rfl
    simp only [this] at hOk
  | ok pb =>
    refine ⟨pb, rfl, ?_⟩
    unfold validateDaIntegrityGate at hOk; rw [hB] at hOk
    have hDo : (do let pb' ← BlockBasicV1.parseBlock blockBytes; validateDASetIntegrity pb'.txs) =
               validateDASetIntegrity pb.txs := by rw [hP]; rfl
    rw [hDo] at hOk; exact hOk

/-- Gate success full decomposition: block ok ∧ DA integrity ok. -/
theorem da_gate_ok_full (blockBytes : Bytes) (ph pt : Option Bytes)
    (hOk : validateDaIntegrityGate blockBytes ph pt = .ok ()) :
    BlockBasicV1.validateBlockBasic blockBytes ph pt = .ok () ∧
    ∃ pb, BlockBasicV1.parseBlock blockBytes = .ok pb ∧
          validateDASetIntegrity pb.txs = .ok () :=
  ⟨da_gate_ok_implies_block_ok blockBytes ph pt hOk,
   da_gate_ok_implies_das_ok blockBytes ph pt hOk⟩

/-! ## Conformance replay (existing — referenced, not duplicated)

cv_da_integrity_vectors_pass (CVDaIntegrityReplay.lean):
Proves that ALL conformance vectors from CV-DA pass through
validateDaIntegrityGate via native_decide. Combined with error
propagation theorems, this provides refined_model evidence.
Does NOT cover BLOCK_ERR_DA_BATCH_EXCEEDED (no CV vector with >128 batches).
-/

end RubinFormal
