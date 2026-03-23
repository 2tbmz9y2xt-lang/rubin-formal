import RubinFormal.ConnectBlockStrong
import RubinFormal.CoinbaseBehavioral

/-!
# Full Block Connection with Coinbase (§18/§19)

Models the complete block connection path including coinbase.
Written with explicit match (no do) for formal proof access.
Equivalence with Go/Rust connect_block_inmem.go is structural.
-/

namespace RubinFormal

open UtxoBasicV1 SubsidyV1

/-- Full block connection result. -/
structure ConnectBlockResult where
  utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint
  sumFees : Nat

/-- Full block connection pipeline.
    Models connect_block_inmem.go lines 138-186. -/
def connectBlockFull
    (nonCoinbaseTxs : List Bytes)
    (coinbaseOutputs : List CovenantGenesisV1.TxOut)
    (coinbaseTxid : Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat)
    (chainId : Bytes)
    (subsidy : Nat) : Except String ConnectBlockResult :=
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
            , sumFees := sumFees }

/-! ## Helper: extract connectBlockTxs success from connectBlockFull success -/

private theorem connectBlockFull_txs_ok
    (nonCoinbaseTxs : List Bytes) (coinbaseOutputs : List CovenantGenesisV1.TxOut)
    (coinbaseTxid : Bytes) (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat) (chainId : Bytes) (subsidy : Nat)
    (result : ConnectBlockResult)
    (hOk : connectBlockFull nonCoinbaseTxs coinbaseOutputs coinbaseTxid
           utxoMap height blockTimestamp chainId subsidy = .ok result) :
    ∃ postTxUtxos,
      connectBlockTxs nonCoinbaseTxs utxoMap height blockTimestamp chainId =
        .ok (result.sumFees, postTxUtxos) := by
  simp only [connectBlockFull] at hOk
  match hTxs : connectBlockTxs nonCoinbaseTxs utxoMap height blockTimestamp chainId with
  | .error _ => simp [hTxs] at hOk
  | .ok (sf, ptx) =>
    simp [hTxs] at hOk
    match hBound : validateCoinbaseValueBound coinbaseOutputs subsidy sf with
    | .error _ => simp [hBound] at hOk
    | .ok () =>
      simp [hBound] at hOk
      match hVault : validateCoinbaseApplyOutputs coinbaseOutputs with
      | .error _ => simp [hVault] at hOk
      | .ok () =>
        simp [hVault] at hOk
        obtain ⟨_, rfl⟩ := hOk
        exact ⟨ptx, rfl⟩

/-! ## Behavioral proofs -/

/-- Full connection success → non-coinbase conservation + no-double-spend. -/
theorem connectBlockFull_preserves_noncoinbase_invariants
    (nonCoinbaseTxs : List Bytes) (coinbaseOutputs : List CovenantGenesisV1.TxOut)
    (coinbaseTxid : Bytes) (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat) (chainId : Bytes) (subsidy : Nat)
    (result : ConnectBlockResult)
    (hOk : connectBlockFull nonCoinbaseTxs coinbaseOutputs coinbaseTxid
           utxoMap height blockTimestamp chainId subsidy = .ok result) :
    utxo_conserved nonCoinbaseTxs utxoMap height blockTimestamp chainId ∧
    no_double_spend nonCoinbaseTxs utxoMap height blockTimestamp chainId := by
  obtain ⟨ptx, hTxs⟩ := connectBlockFull_txs_ok _ _ _ _ _ _ _ _ _ hOk
  exact ⟨utxo_conservation_theorem _ _ _ _ _ _ _ hTxs,
         no_double_spend_theorem _ _ _ _ _ _ _ hTxs⟩

/-- Full connection success → coinbase value ≤ subsidy + fees. -/
theorem connectBlockFull_coinbase_bound
    (nonCoinbaseTxs : List Bytes) (coinbaseOutputs : List CovenantGenesisV1.TxOut)
    (coinbaseTxid : Bytes) (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat) (chainId : Bytes) (subsidy : Nat)
    (result : ConnectBlockResult)
    (hOk : connectBlockFull nonCoinbaseTxs coinbaseOutputs coinbaseTxid
           utxoMap height blockTimestamp chainId subsidy = .ok result) :
    ¬(sumCoinbaseOutputs coinbaseOutputs > subsidy + result.sumFees) := by
  simp only [connectBlockFull] at hOk
  match hTxs : connectBlockTxs nonCoinbaseTxs utxoMap height blockTimestamp chainId with
  | .error _ => simp [hTxs] at hOk
  | .ok (sf, ptx) =>
    simp [hTxs] at hOk
    match hBound : validateCoinbaseValueBound coinbaseOutputs subsidy sf with
    | .error _ => simp [hBound] at hOk
    | .ok () =>
      simp [hBound] at hOk
      match hVault : validateCoinbaseApplyOutputs coinbaseOutputs with
      | .error _ => simp [hVault] at hOk
      | .ok () =>
        simp [hVault] at hOk
        obtain ⟨_, rfl⟩ := hOk
        -- hBound : validateCoinbaseValueBound ... = .ok ()
        simp only [validateCoinbaseValueBound] at hBound
        by_cases hGt : sumCoinbaseOutputs coinbaseOutputs > subsidy + sf
        · simp [hGt] at hBound
        · exact hGt

/-- Full connection success → no CORE_VAULT in coinbase. -/
theorem connectBlockFull_no_vault
    (nonCoinbaseTxs : List Bytes) (coinbaseOutputs : List CovenantGenesisV1.TxOut)
    (coinbaseTxid : Bytes) (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat) (chainId : Bytes) (subsidy : Nat)
    (result : ConnectBlockResult)
    (hOk : connectBlockFull nonCoinbaseTxs coinbaseOutputs coinbaseTxid
           utxoMap height blockTimestamp chainId subsidy = .ok result) :
    coinbaseOutputs.any (·.covenantType == CovenantGenesisV1.COV_TYPE_VAULT) = false := by
  simp only [connectBlockFull] at hOk
  match hTxs : connectBlockTxs nonCoinbaseTxs utxoMap height blockTimestamp chainId with
  | .error _ => simp [hTxs] at hOk
  | .ok (sf, ptx) =>
    simp [hTxs] at hOk
    match hBound : validateCoinbaseValueBound coinbaseOutputs subsidy sf with
    | .error _ => simp [hBound] at hOk
    | .ok () =>
      simp [hBound] at hOk
      match hVault : validateCoinbaseApplyOutputs coinbaseOutputs with
      | .error _ => simp [hVault] at hOk
      | .ok () =>
        -- hVault : validateCoinbaseApplyOutputs coinbaseOutputs = .ok ()
        -- validateCoinbaseApplyOutputs is: if any vault then error else ok
        -- ok means not-any-vault
        by_cases hAny : coinbaseOutputs.any (·.covenantType == CovenantGenesisV1.COV_TYPE_VAULT) = true
        · -- If any vault = true, then validateCoinbaseApplyOutputs = error
          -- But hVault says ok → contradiction
          have : validateCoinbaseApplyOutputs coinbaseOutputs = .error "BLOCK_ERR_COINBASE_INVALID" :=
            coinbase_no_vault_rejects coinbaseOutputs hAny
          rw [this] at hVault; simp at hVault
        · -- any vault ≠ true → any vault = false (Bool)
          exact Bool.eq_false_iff.mpr (fun h => hAny h)

end RubinFormal
