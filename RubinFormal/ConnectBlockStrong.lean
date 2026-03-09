import RubinFormal.SubsidyV1

namespace RubinFormal

open RubinFormal
open RubinFormal.UtxoBasicV1
open RubinFormal.SubsidyV1

def inputs_available
    (tx : Tx)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height : Nat) : Prop :=
  ∃ inputState, scanInputs tx.inputs utxoMap height = .ok inputState

/-- Check that each element in a list is distinct from all predecessors.
    Mirrors the `consumedOutpoints.contains` check in `scanSingleInputStep`. -/
def prefixNoDupAux [BEq α] (seen : List α) : List α → Bool
  | [] => true
  | x :: rest => !seen.contains x && prefixNoDupAux (seen ++ [x]) rest

def prefixNoDup [BEq α] (xs : List α) : Bool :=
  prefixNoDupAux [] xs

/-- A transaction has no intra-tx double spend iff all input outpoints are distinct. -/
def no_intra_tx_double_spend (tx : Tx) : Prop :=
  prefixNoDup (tx.inputs.map txInOutpoint) = true

def utxo_conserved_tx
    (tx : Tx)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height : Nat)
    (fee : Nat) : Prop :=
  ∃ inputState,
    scanInputs tx.inputs utxoMap height = .ok inputState ∧
    inputState.sumIn = sumOutputs tx.outputs + fee

def utxo_conserved
    (txs : List Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat)
    (chainId : Bytes) : Prop :=
  match txs with
  | [] => True
  | txBytes :: rest =>
      ∃ prepared,
        prepareNonCoinbaseTxBasic txBytes utxoMap height blockTimestamp chainId = .ok prepared ∧
        utxo_conserved_tx prepared.tx utxoMap height prepared.fee ∧
        utxo_conserved rest prepared.nextUtxoMap height blockTimestamp chainId

def no_double_spend
    (txs : List Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat)
    (chainId : Bytes) : Prop :=
  match txs with
  | [] => True
  | txBytes :: rest =>
      ∃ prepared,
        prepareNonCoinbaseTxBasic txBytes utxoMap height blockTimestamp chainId = .ok prepared ∧
        inputs_available prepared.tx utxoMap height ∧
        no_intra_tx_double_spend prepared.tx ∧
        no_double_spend rest prepared.nextUtxoMap height blockTimestamp chainId

theorem applyNonCoinbaseTxBasicState_success_prepared
    (txBytes : Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat)
    (chainId : Bytes)
    (fee : Nat)
    (next : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (hApply :
      applyNonCoinbaseTxBasicState txBytes utxoMap height blockTimestamp chainId = .ok (fee, next)) :
    ∃ prepared,
      prepareNonCoinbaseTxBasic txBytes utxoMap height blockTimestamp chainId = .ok prepared ∧
      prepared.fee = fee ∧
      prepared.nextUtxoMap = next := by
  unfold applyNonCoinbaseTxBasicState at hApply
  cases hPrep : prepareNonCoinbaseTxBasic txBytes utxoMap height blockTimestamp chainId with
  | error e =>
      simp [hPrep] at hApply
      cases hApply
  | ok prepared =>
      simp [hPrep] at hApply
      cases hApply
      exact ⟨prepared, rfl, rfl, rfl⟩

theorem except_bind_eq_ok
    {ε α β : Type}
    {x : Except ε α}
    {f : α → Except ε β}
    {y : β}
    (h : x >>= f = .ok y) :
    ∃ a, x = .ok a ∧ f a = .ok y := by
  cases x with
  | error e =>
      cases h
  | ok a =>
      exact ⟨a, rfl, h⟩

theorem computeBasicFee_success
    (tx : Tx)
    (inputState : InputScanState)
    (fee : Nat)
    (hFee : computeBasicFee tx inputState = .ok fee) :
    inputState.sumIn = sumOutputs tx.outputs + fee := by
  unfold computeBasicFee at hFee
  by_cases hTooBig : sumOutputs tx.outputs > inputState.sumIn
  · simp [hTooBig] at hFee
    cases hFee
  · simp [hTooBig] at hFee
    cases hFee
    omega

theorem prepareNonCoinbaseTxBasic_success_core
    (txBytes : Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat)
    (chainId : Bytes)
    (prepared : PreparedNonCoinbaseTx)
    (hPrep : prepareNonCoinbaseTxBasic txBytes utxoMap height blockTimestamp chainId = .ok prepared) :
    ∃ core,
      prepareNonCoinbaseTxCore txBytes utxoMap height blockTimestamp chainId = .ok core ∧
      prepared =
        {
          tx := core.tx
          inputState := core.inputState
          fee := core.fee
          nextUtxoMap :=
            insertOutputs (eraseInputs utxoMap core.tx.inputs)
              (match (TxV2.parseTx txBytes).txid with
              | some t => t
              | none => SHA3.sha3_256 ByteArray.empty)
              core.tx.outputs height
        } := by
  unfold prepareNonCoinbaseTxBasic at hPrep
  rcases except_bind_eq_ok hPrep with ⟨core, hCore, hPure⟩
  simp at hPure
  cases hPure
  exact ⟨core, hCore, rfl⟩

theorem prepareNonCoinbaseTxCore_success_components
    (txBytes : Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat)
    (chainId : Bytes)
    (core : PreparedNonCoinbaseTxCore)
    (hCore : prepareNonCoinbaseTxCore txBytes utxoMap height blockTimestamp chainId = .ok core) :
    ∃ tx inputState,
      core.tx = tx ∧
      core.inputState = inputState ∧
      parseTx txBytes = .ok tx ∧
      scanInputs tx.inputs utxoMap height = .ok inputState ∧
      computeBasicFee tx inputState = .ok core.fee := by
  unfold prepareNonCoinbaseTxCore at hCore
  rcases except_bind_eq_ok hCore with ⟨tx, hParse, hRest1⟩
  rcases except_bind_eq_ok hRest1 with ⟨_u1, _hEnv, hRest2⟩
  rcases except_bind_eq_ok hRest2 with ⟨_u2, _hStruct, hRest3⟩
  rcases except_bind_eq_ok hRest3 with ⟨inputState, hScan, hRest4⟩
  rcases except_bind_eq_ok hRest4 with ⟨_u3, _hWitness, hRest5⟩
  rcases except_bind_eq_ok hRest5 with ⟨_u4, _hVault, hRest6⟩
  rcases except_bind_eq_ok hRest6 with ⟨fee, hFee, hPure⟩
  cases hPure
  exact ⟨tx, inputState, rfl, rfl, hParse, hScan, hFee⟩

theorem prepareNonCoinbaseTxBasic_utxo_conserved
    (txBytes : Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat)
    (chainId : Bytes)
    (prepared : PreparedNonCoinbaseTx)
    (hPrep : prepareNonCoinbaseTxBasic txBytes utxoMap height blockTimestamp chainId = .ok prepared) :
    utxo_conserved_tx prepared.tx utxoMap height prepared.fee := by
  rcases prepareNonCoinbaseTxBasic_success_core
      txBytes utxoMap height blockTimestamp chainId prepared hPrep with
    ⟨core, hCore, hPreparedEq⟩
  cases hPreparedEq
  rcases prepareNonCoinbaseTxCore_success_components
      txBytes utxoMap height blockTimestamp chainId core hCore with
    ⟨tx, inputState, hTxEq, hInputEq, hParse, hScan, hFeeCore⟩
  cases hTxEq
  cases hInputEq
  refine ⟨core.inputState, hScan, ?_⟩
  exact computeBasicFee_success core.tx core.inputState core.fee hFeeCore

theorem prepareNonCoinbaseTxBasic_inputs_available
    (txBytes : Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat)
    (chainId : Bytes)
    (prepared : PreparedNonCoinbaseTx)
    (hPrep : prepareNonCoinbaseTxBasic txBytes utxoMap height blockTimestamp chainId = .ok prepared) :
    inputs_available prepared.tx utxoMap height := by
  rcases prepareNonCoinbaseTxBasic_success_core
      txBytes utxoMap height blockTimestamp chainId prepared hPrep with
    ⟨core, hCore, hPreparedEq⟩
  cases hPreparedEq
  rcases prepareNonCoinbaseTxCore_success_components
      txBytes utxoMap height blockTimestamp chainId core hCore with
    ⟨tx, inputState, hTxEq, hInputEq, hParse, hScan, hFeeCore⟩
  cases hTxEq
  cases hInputEq
  exact ⟨core.inputState, hScan⟩

/-! ## Intra-transaction anti-double-spend -/

theorem scanSingleInputStep_not_contains
    (input : TxIn)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height : Nat)
    (acc result : InputScanState)
    (hStep : scanSingleInputStep input utxoMap height acc = .ok result) :
    acc.consumedOutpoints.contains (txInOutpoint input) = false := by
  cases hDup : acc.consumedOutpoints.contains (txInOutpoint input) with
  | false => rfl
  | true =>
    exfalso
    have herr : scanSingleInputStep input utxoMap height acc = Except.error "TX_ERR_PARSE" := by
      unfold scanSingleInputStep
      simp only [hDup, ite_true, Bind.bind, Except.bind]
    rw [herr] at hStep
    exact absurd hStep (by intro h; cases h)

set_option maxRecDepth 4096 in
theorem scanSingleInputStep_consumed_ext
    (input : TxIn)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height : Nat)
    (acc result : InputScanState)
    (hStep : scanSingleInputStep input utxoMap height acc = .ok result) :
    result.consumedOutpoints = acc.consumedOutpoints ++ [txInOutpoint input] := by
  have hNoDup := scanSingleInputStep_not_contains input utxoMap height acc result hStep
  unfold scanSingleInputStep at hStep
  simp only [hNoDup, ite_false, ite_true, Bind.bind, Except.bind,
             Pure.pure, Except.pure] at hStep
  -- hStep is now a nested if/match tree where every .ok leaf has
  -- consumedOutpoints := List.concat acc.consumedOutpoints (txInOutpoint input).
  -- Strategy: repeatedly split all if/match in hStep, close error-leaves.
  -- After all splits, remaining goals have either:
  --   hStep : Except.ok {...} = Except.ok result (→ subst + simp)
  --   or no hStep (already subst'd by cases → direct simp)
  split at hStep <;> try cases hStep  -- find?
  split at hStep <;> try cases hStep  -- anchor
  all_goals try (split at hStep <;> try cases hStep)  -- coinbase
  all_goals try (split at hStep <;> try cases hStep)  -- maturity
  all_goals try (split at hStep <;> try cases hStep)  -- p2pk
  all_goals try (split at hStep <;> try cases hStep)  -- p2pk size
  all_goals try (split at hStep <;> try cases hStep)  -- p2pk suite
  all_goals try (split at hStep <;> try cases hStep)  -- vault
  all_goals try (split at hStep <;> try cases hStep)  -- parseVault result
  all_goals try (split at hStep <;> try cases hStep)  -- multi-input
  all_goals (first
    | (simp only [Except.ok.injEq] at hStep; subst hStep; simp [List.concat_eq_append])
    | simp [List.concat_eq_append])

theorem scanInputsGo_prefixNoDup
    (inputs : List TxIn)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height : Nat)
    (acc result : InputScanState)
    (hScan : scanInputsGo inputs utxoMap height acc = .ok result) :
    prefixNoDupAux acc.consumedOutpoints (inputs.map txInOutpoint) = true := by
  induction inputs generalizing acc with
  | nil =>
      simp [List.map, prefixNoDupAux]
  | cons i rest ih =>
      unfold scanInputsGo at hScan
      rcases except_bind_eq_ok hScan with ⟨nextAcc, hStep, hRest⟩
      have hNotDup := scanSingleInputStep_not_contains i utxoMap height acc nextAcc hStep
      have hExt := scanSingleInputStep_consumed_ext i utxoMap height acc nextAcc hStep
      have hIH := ih nextAcc hRest
      simp only [List.map, prefixNoDupAux, hNotDup, Bool.not_false, Bool.true_and]
      rw [← hExt]
      exact hIH

theorem scanInputs_no_intra_tx_double_spend
    (tx : Tx)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height : Nat)
    (inputState : InputScanState)
    (hScan : scanInputs tx.inputs utxoMap height = .ok inputState) :
    no_intra_tx_double_spend tx := by
  unfold no_intra_tx_double_spend prefixNoDup
  unfold scanInputs at hScan
  exact scanInputsGo_prefixNoDup tx.inputs utxoMap height InputScanState.empty inputState hScan

theorem prepareNonCoinbaseTxBasic_no_intra_double_spend
    (txBytes : Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat)
    (chainId : Bytes)
    (prepared : PreparedNonCoinbaseTx)
    (hPrep : prepareNonCoinbaseTxBasic txBytes utxoMap height blockTimestamp chainId = .ok prepared) :
    no_intra_tx_double_spend prepared.tx := by
  rcases prepareNonCoinbaseTxBasic_success_core
      txBytes utxoMap height blockTimestamp chainId prepared hPrep with
    ⟨core, hCore, hPreparedEq⟩
  cases hPreparedEq
  rcases prepareNonCoinbaseTxCore_success_components
      txBytes utxoMap height blockTimestamp chainId core hCore with
    ⟨tx, inputState, hTxEq, hInputEq, hParse, hScan, hFeeCore⟩
  cases hTxEq
  cases hInputEq
  exact scanInputs_no_intra_tx_double_spend core.tx utxoMap height core.inputState hScan

/-! ## Main theorems -/

theorem utxo_conservation_theorem
    (txs : List Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat)
    (chainId : Bytes)
    (sumFees : Nat)
    (finalMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (hConnect :
      connectBlockTxs txs utxoMap height blockTimestamp chainId = .ok (sumFees, finalMap)) :
    utxo_conserved txs utxoMap height blockTimestamp chainId := by
  induction txs generalizing utxoMap sumFees finalMap with
  | nil =>
      simp [utxo_conserved]
  | cons tx rest ih =>
      cases hStep : applyNonCoinbaseTxBasicState tx utxoMap height blockTimestamp chainId with
      | error e =>
          simp [connectBlockTxs, hStep] at hConnect
      | ok step =>
          cases step with
          | mk fee next =>
              cases hTail : connectBlockTxs rest next height blockTimestamp chainId with
              | error e =>
                  simp [connectBlockTxs, hStep, hTail] at hConnect
              | ok tail =>
                  cases tail with
                  | mk feesTail finalTail =>
                      simp [connectBlockTxs, hStep, hTail] at hConnect
                      cases hConnect
                      rcases applyNonCoinbaseTxBasicState_success_prepared
                          tx utxoMap height blockTimestamp chainId fee next hStep with
                        ⟨prepared, hPrep, hFeeEq, hNextEq⟩
                      cases hFeeEq
                      cases hNextEq
                      refine ⟨prepared, hPrep, ?_, ?_⟩
                      · exact prepareNonCoinbaseTxBasic_utxo_conserved
                          tx utxoMap height blockTimestamp chainId prepared hPrep
                      · exact ih prepared.nextUtxoMap feesTail finalTail hTail

theorem no_double_spend_theorem
    (txs : List Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat)
    (chainId : Bytes)
    (sumFees : Nat)
    (finalMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (hConnect :
      connectBlockTxs txs utxoMap height blockTimestamp chainId = .ok (sumFees, finalMap)) :
    no_double_spend txs utxoMap height blockTimestamp chainId := by
  induction txs generalizing utxoMap sumFees finalMap with
  | nil =>
      simp [no_double_spend]
  | cons tx rest ih =>
      cases hStep : applyNonCoinbaseTxBasicState tx utxoMap height blockTimestamp chainId with
      | error e =>
          simp [connectBlockTxs, hStep] at hConnect
      | ok step =>
          cases step with
          | mk fee next =>
              cases hTail : connectBlockTxs rest next height blockTimestamp chainId with
              | error e =>
                  simp [connectBlockTxs, hStep, hTail] at hConnect
              | ok tail =>
                  cases tail with
                  | mk feesTail finalTail =>
                      simp [connectBlockTxs, hStep, hTail] at hConnect
                      cases hConnect
                      rcases applyNonCoinbaseTxBasicState_success_prepared
                          tx utxoMap height blockTimestamp chainId fee next hStep with
                        ⟨prepared, hPrep, hFeeEq, hNextEq⟩
                      cases hFeeEq
                      cases hNextEq
                      refine ⟨prepared, hPrep, ?_, ?_, ?_⟩
                      · exact prepareNonCoinbaseTxBasic_inputs_available
                          tx utxoMap height blockTimestamp chainId prepared hPrep
                      · exact prepareNonCoinbaseTxBasic_no_intra_double_spend
                          tx utxoMap height blockTimestamp chainId prepared hPrep
                      · exact ih prepared.nextUtxoMap feesTail finalTail hTail

end RubinFormal
