import RubinFormal.ConnectBlockStrong
import RubinFormal.CoinbaseBehavioral
import RubinFormal.TxContextBehavioral

/-!
# Full Block Connection with Coinbase + TxContext (§18/§19/§14)

Models the complete block connection path including:
1. Non-coinbase transaction validation (via connectBlockTxs)
2. Coinbase value bound + vault check
3. Coinbase UTXO creation
4. TxContext bundle construction (LIVE — wired, not parallel model)

Written with explicit match (no do) for formal proof access.
-/

namespace RubinFormal

open UtxoBasicV1 SubsidyV1

/-- Full block connection result with TxContext bundle. -/
structure ConnectBlockResult where
  utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint
  sumFees : Nat
  txContext : Option TxContextBundle

/-- Full block connection pipeline with TxContext construction.
    Models connect_block_inmem.go:138-186 + per-tx BuildTxContext.
    TxContext is constructed from activeExtIds/totalIn/totalOut when ext_ids active. -/
def connectBlockFull
    (nonCoinbaseTxs : List Bytes)
    (coinbaseOutputs : List CovenantGenesisV1.TxOut)
    (coinbaseTxid : Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat) (chainId : Bytes) (subsidy : Nat)
    (activeExtIds : List Nat) (totalIn totalOut : Nat)
    (continuingData : List (Nat × TxContextContinuing))
    : Except String ConnectBlockResult :=
  match connectBlockTxs nonCoinbaseTxs utxoMap height blockTimestamp chainId with
  | .error e => .error e
  | .ok (sumFees, postTxUtxos) =>
    match validateCoinbaseValueBound coinbaseOutputs subsidy sumFees with
    | .error e => .error e
    | .ok () =>
      match validateCoinbaseApplyOutputs coinbaseOutputs with
      | .error e => .error e
      | .ok () =>
        .ok { utxoMap := addCoinbaseOutputs coinbaseOutputs coinbaseTxid height postTxUtxos
            , sumFees := sumFees
            , txContext := buildTxContext activeExtIds totalIn totalOut height continuingData }

/-! ## Helper: extract connectBlockTxs success -/

private theorem connectBlockFull_txs_ok
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (result : ConnectBlockResult)
    (hOk : connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd = .ok result) :
    ∃ postTxUtxos,
      connectBlockTxs nctxs utxos h bt cid = .ok (result.sumFees, postTxUtxos) := by
  simp only [connectBlockFull] at hOk
  match hTxs : connectBlockTxs nctxs utxos h bt cid with
  | .error _ => simp [hTxs] at hOk
  | .ok (sf, ptx) =>
    simp [hTxs] at hOk
    match hBound : validateCoinbaseValueBound couts sub sf with
    | .error _ => simp [hBound] at hOk
    | .ok () =>
      simp [hBound] at hOk
      match hVault : validateCoinbaseApplyOutputs couts with
      | .error _ => simp [hVault] at hOk
      | .ok () =>
        simp [hVault] at hOk; obtain ⟨_, rfl, _⟩ := hOk; exact ⟨ptx, rfl⟩

/-! ## Non-coinbase behavioral proofs -/

/-- Full connection success → non-coinbase conservation + no-double-spend. -/
theorem connectBlockFull_preserves_noncoinbase_invariants
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (result : ConnectBlockResult)
    (hOk : connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd = .ok result) :
    utxo_conserved nctxs utxos h bt cid ∧
    no_double_spend nctxs utxos h bt cid := by
  obtain ⟨ptx, hTxs⟩ := connectBlockFull_txs_ok _ _ _ _ _ _ _ _ _ _ _ _ _ hOk
  exact ⟨utxo_conservation_theorem _ _ _ _ _ _ _ hTxs,
         no_double_spend_theorem _ _ _ _ _ _ _ hTxs⟩

/-- Full connection success → coinbase value ≤ subsidy + fees. -/
theorem connectBlockFull_coinbase_bound
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (result : ConnectBlockResult)
    (hOk : connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd = .ok result) :
    ¬(sumCoinbaseOutputs couts > sub + result.sumFees) := by
  simp only [connectBlockFull] at hOk
  match hTxs : connectBlockTxs nctxs utxos h bt cid with
  | .error _ => simp [hTxs] at hOk
  | .ok (sf, ptx) =>
    simp [hTxs] at hOk
    match hBound : validateCoinbaseValueBound couts sub sf with
    | .error _ => simp [hBound] at hOk
    | .ok () =>
      simp [hBound] at hOk
      match hVault : validateCoinbaseApplyOutputs couts with
      | .error _ => simp [hVault] at hOk
      | .ok () =>
        simp [hVault] at hOk; obtain ⟨_, rfl, _⟩ := hOk
        simp only [validateCoinbaseValueBound] at hBound
        by_cases hGt : sumCoinbaseOutputs couts > sub + sf
        · simp [hGt] at hBound
        · exact hGt

/-- Full connection success → no CORE_VAULT in coinbase. -/
theorem connectBlockFull_no_vault
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (result : ConnectBlockResult)
    (hOk : connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd = .ok result) :
    couts.any (·.covenantType == CovenantGenesisV1.COV_TYPE_VAULT) = false := by
  simp only [connectBlockFull] at hOk
  match hTxs : connectBlockTxs nctxs utxos h bt cid with
  | .error _ => simp [hTxs] at hOk
  | .ok (sf, ptx) =>
    simp [hTxs] at hOk
    match hBound : validateCoinbaseValueBound couts sub sf with
    | .error _ => simp [hBound] at hOk
    | .ok () =>
      simp [hBound] at hOk
      match hVault : validateCoinbaseApplyOutputs couts with
      | .error _ => simp [hVault] at hOk
      | .ok () =>
        by_cases hAny : couts.any (·.covenantType == CovenantGenesisV1.COV_TYPE_VAULT) = true
        · have : validateCoinbaseApplyOutputs couts = .error "BLOCK_ERR_COINBASE_INVALID" :=
            coinbase_no_vault_rejects couts hAny
          rw [this] at hVault; simp at hVault
        · exact Bool.eq_false_iff.mpr (fun hh => hAny hh)

/-! ## Error branch proofs -/

/-- Non-coinbase tx failure → full connect rejected with same error. -/
theorem connectBlockFull_rejects_bad_txs
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (err : String)
    (hFail : connectBlockTxs nctxs utxos h bt cid = .error err) :
    connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd = .error err := by
  simp [connectBlockFull, hFail]

/-- Coinbase exceeds subsidy+fees → full connect rejected. -/
theorem connectBlockFull_rejects_oversized_coinbase
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (sumFees : Nat) (postTxUtxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (hTxs : connectBlockTxs nctxs utxos h bt cid = .ok (sumFees, postTxUtxos))
    (hOver : sumCoinbaseOutputs couts > sub + sumFees) :
    connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd =
    .error "BLOCK_ERR_SUBSIDY_EXCEEDED" := by
  simp [connectBlockFull, hTxs, validateCoinbaseValueBound, hOver]

/-- CORE_VAULT in coinbase → full connect rejected. -/
theorem connectBlockFull_rejects_vault_coinbase
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (sumFees : Nat) (postTxUtxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (hTxs : connectBlockTxs nctxs utxos h bt cid = .ok (sumFees, postTxUtxos))
    (hBound : ¬(sumCoinbaseOutputs couts > sub + sumFees))
    (hVault : couts.any (·.covenantType == CovenantGenesisV1.COV_TYPE_VAULT) = true) :
    connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd =
    .error "BLOCK_ERR_COINBASE_INVALID" := by
  simp [connectBlockFull, hTxs, validateCoinbaseValueBound, hBound,
        validateCoinbaseApplyOutputs, hVault]

/-! ## Structural ordering -/

/-- Coinbase processed strictly AFTER all non-coinbase txs. -/
theorem coinbase_processed_after_noncoinbase
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (result : ConnectBlockResult)
    (hOk : connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd = .ok result) :
    ∃ sf ptx, connectBlockTxs nctxs utxos h bt cid = .ok (sf, ptx) := by
  simp only [connectBlockFull] at hOk
  match hT : connectBlockTxs nctxs utxos h bt cid with
  | .error _ => simp [hT] at hOk
  | .ok (sf, ptx) => exact ⟨sf, ptx, rfl⟩

/-! ## Error taxonomy (replaces former axiom) -/

/-- Structural correspondence: connectBlockFull returns ONLY canonical
    error codes. Machine-checked exhaustive proof, zero axioms. -/
theorem connectBlockFull_error_taxonomy
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (err : String)
    (hFail : connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd = .error err) :
    err = "BLOCK_ERR_SUBSIDY_EXCEEDED" ∨
    err = "BLOCK_ERR_COINBASE_INVALID" ∨
    (∃ txErr, connectBlockTxs nctxs utxos h bt cid = .error txErr ∧ err = txErr) := by
  simp only [connectBlockFull] at hFail
  match hT : connectBlockTxs nctxs utxos h bt cid with
  | .error e =>
    simp [hT] at hFail; exact Or.inr (Or.inr ⟨e, rfl, hFail.symm⟩)
  | .ok (sf, ptx) =>
    simp [hT] at hFail
    by_cases hOver : sumCoinbaseOutputs couts > sub + sf
    · have hB : validateCoinbaseValueBound couts sub sf = .error "BLOCK_ERR_SUBSIDY_EXCEEDED" :=
        coinbase_value_bound_rejects couts sub sf hOver
      simp [hB] at hFail; exact Or.inl hFail.symm
    · have hB : validateCoinbaseValueBound couts sub sf = .ok () :=
        coinbase_value_bound_accepts couts sub sf hOver
      simp [hB] at hFail
      by_cases hVault : couts.any (·.covenantType == CovenantGenesisV1.COV_TYPE_VAULT) = true
      · have hV : validateCoinbaseApplyOutputs couts = .error "BLOCK_ERR_COINBASE_INVALID" :=
          coinbase_no_vault_rejects couts hVault
        simp [hV] at hFail; exact Or.inr (Or.inl hFail.symm)
      · have hNotV := Bool.eq_false_iff.mpr (fun hh => hVault hh)
        have hV : validateCoinbaseApplyOutputs couts = .ok () :=
          coinbase_no_vault_accepts couts hNotV
        simp [hV] at hFail

/-! ## TxContext wiring proofs (LIVE — not parallel model) -/

/-- If block connects with active ext_ids, TxContext bundle is produced. -/
theorem connectBlockFull_produces_txcontext
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (hIds : ids.length > 0)
    (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (result : ConnectBlockResult)
    (hOk : connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd = .ok result) :
    result.txContext.isSome = true := by
  simp only [connectBlockFull] at hOk
  match hT : connectBlockTxs nctxs utxos h bt cid with
  | .error _ => simp [hT] at hOk
  | .ok (sf, ptx) =>
    simp [hT] at hOk
    match hB : validateCoinbaseValueBound couts sub sf with
    | .error _ => simp [hB] at hOk
    | .ok () =>
      simp [hB] at hOk
      match hV : validateCoinbaseApplyOutputs couts with
      | .error _ => simp [hV] at hOk
      | .ok () =>
        simp [hV] at hOk; obtain ⟨_, _, rfl⟩ := hOk
        exact buildTxContext_some ids hIds tin tout h cd

/-- If block connects with no active ext_ids, no TxContext bundle. -/
theorem connectBlockFull_no_txcontext_when_empty
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (result : ConnectBlockResult)
    (hOk : connectBlockFull nctxs couts ctxid utxos h bt cid sub [] tin tout cd = .ok result) :
    result.txContext = none := by
  simp only [connectBlockFull] at hOk
  match hT : connectBlockTxs nctxs utxos h bt cid with
  | .error _ => simp [hT] at hOk
  | .ok (sf, ptx) =>
    simp [hT] at hOk
    match hB : validateCoinbaseValueBound couts sub sf with
    | .error _ => simp [hB] at hOk
    | .ok () =>
      simp [hB] at hOk
      match hV : validateCoinbaseApplyOutputs couts with
      | .error _ => simp [hV] at hOk
      | .ok () =>
        simp [hV] at hOk; obtain ⟨_, _, rfl⟩ := hOk
        rfl

/-- TxContext bundle in result has correct ext_ids. -/
theorem connectBlockFull_txcontext_ext_ids
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (hIds : ids.length > 0)
    (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (result : ConnectBlockResult) (bundle : TxContextBundle)
    (hOk : connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd = .ok result)
    (hBundle : result.txContext = some bundle) :
    bundle.continuingExtIds = ids := by
  simp only [connectBlockFull] at hOk
  match hT : connectBlockTxs nctxs utxos h bt cid with
  | .error _ => simp [hT] at hOk
  | .ok (sf, ptx) =>
    simp [hT] at hOk
    match hB : validateCoinbaseValueBound couts sub sf with
    | .error _ => simp [hB] at hOk
    | .ok () =>
      simp [hB] at hOk
      match hV : validateCoinbaseApplyOutputs couts with
      | .error _ => simp [hV] at hOk
      | .ok () =>
        simp [hV] at hOk; obtain ⟨_, _, rfl⟩ := hOk
        exact buildTxContext_ext_ids ids hIds tin tout h cd bundle hBundle

/-- TxContext bundle has correct base values (totalIn, totalOut, height). -/
theorem connectBlockFull_txcontext_base_values
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (hIds : ids.length > 0)
    (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (result : ConnectBlockResult) (bundle : TxContextBundle)
    (hOk : connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd = .ok result)
    (hBundle : result.txContext = some bundle) :
    bundle.base.totalIn = tin ∧ bundle.base.totalOut = tout ∧ bundle.base.height = h := by
  simp only [connectBlockFull] at hOk
  match hT : connectBlockTxs nctxs utxos h bt cid with
  | .error _ => simp [hT] at hOk
  | .ok (sf, ptx) =>
    simp [hT] at hOk
    match hB : validateCoinbaseValueBound couts sub sf with
    | .error _ => simp [hB] at hOk
    | .ok () =>
      simp [hB] at hOk
      match hV : validateCoinbaseApplyOutputs couts with
      | .error _ => simp [hV] at hOk
      | .ok () =>
        simp [hV] at hOk; obtain ⟨_, _, rfl⟩ := hOk
        exact buildTxContext_base_values ids hIds tin tout h cd bundle hBundle

/-! ## End-to-end scenario -/

/-- Valid block end-to-end: ALL invariants hold simultaneously.
    Conservation + no-double-spend + coinbase bound + no-vault + TxContext presence. -/
theorem valid_block_end_to_end
    (nctxs : List Bytes) (couts : List CovenantGenesisV1.TxOut)
    (ctxid : Bytes) (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) (sub : Nat)
    (ids : List Nat) (hIds : ids.length > 0)
    (tin tout : Nat) (cd : List (Nat × TxContextContinuing))
    (result : ConnectBlockResult)
    (hOk : connectBlockFull nctxs couts ctxid utxos h bt cid sub ids tin tout cd = .ok result) :
    utxo_conserved nctxs utxos h bt cid ∧
    no_double_spend nctxs utxos h bt cid ∧
    ¬(sumCoinbaseOutputs couts > sub + result.sumFees) ∧
    couts.any (·.covenantType == CovenantGenesisV1.COV_TYPE_VAULT) = false ∧
    result.txContext.isSome = true :=
  ⟨(connectBlockFull_preserves_noncoinbase_invariants _ _ _ _ _ _ _ _ _ _ _ _ _ hOk).1,
   (connectBlockFull_preserves_noncoinbase_invariants _ _ _ _ _ _ _ _ _ _ _ _ _ hOk).2,
   connectBlockFull_coinbase_bound _ _ _ _ _ _ _ _ _ _ _ _ _ hOk,
   connectBlockFull_no_vault _ _ _ _ _ _ _ _ _ _ _ _ _ hOk,
   connectBlockFull_produces_txcontext _ _ _ _ _ _ _ _ _ hIds _ _ _ _ hOk⟩

/-! ## Guard lemma

connectBlockFull has exactly 4 match arms + TxContext construction:
1. connectBlockTxs error → propagate
2. validateCoinbaseValueBound error → BLOCK_ERR_SUBSIDY_EXCEEDED
3. validateCoinbaseApplyOutputs error → BLOCK_ERR_COINBASE_INVALID
4. ok → construct result with coinbase UTXOs + TxContext bundle

Adding a 5th validation step requires updating every theorem above.
Lean's exhaustiveness checker enforces this: missing arm → compile error. -/

end RubinFormal
