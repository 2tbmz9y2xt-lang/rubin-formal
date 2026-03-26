import RubinFormal.Refinement.GoTraceV1Check
import RubinFormal.ConnectBlockStrong

namespace RubinFormal

/-- Narrow machine-checked bridge for the retarget executable path.
    Every `retarget_v1` row in the generated Go trace v1 corpus is rechecked against
    Lean's executable `PowV1.retargetV1` on the matching `CV-POW` fixture id. -/
theorem retarget_v1_go_trace_contract_proved :
    RubinFormal.Refinement.retargetGoTraceV1Pass = true := by
  native_decide

/-- Narrow machine-checked bridge for the live UTXO apply executable path.
    Every included `CV-UTXO-BASIC` row in the generated Go trace v1 corpus is
    rechecked against Lean's executable `applyNonCoinbaseTxBasic` on the matching
    fixture id. `CV-U-16` is intentionally excluded from this theorem because it is
    a post-activation SLH row while the current formal `applyNonCoinbaseTxBasic`
    model on `main` remains pre-rotation. -/
theorem utxo_apply_basic_go_trace_contract_proved :
    RubinFormal.Refinement.utxoApplyBasicGoTraceV1Pass = true := by
  native_decide
/-! ## Universal UTXO refinement theorems

  The narrow trace-backed contract (`utxo_apply_basic_go_trace_contract_proved`)
  covers a fixed subset of CV vectors via `native_decide`.  The theorems below
  are strictly stronger: they hold for **any** transaction list and UTXO state
  where `connectBlockTxs` succeeds, proved by induction over the transaction
  list — no axioms, no fixture dependence.

  These are re-exported from `ConnectBlockStrong` into the refinement bridge
  namespace so that the evidence registry can reference a single Lean file. -/

open UtxoBasicV1
open SubsidyV1

/-- Universal UTXO apply refinement: for any transactions and any UTXO state,
    if `connectBlockTxs` succeeds then both UTXO conservation and
    anti-double-spend hold simultaneously.  Proved by combining two independent
    inductive proofs from `ConnectBlockStrong`. -/
theorem utxo_apply_basic_universal_refinement
    (txs : List Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (height blockTimestamp : Nat)
    (chainId : Bytes)
    (sumFees : Nat)
    (finalMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (hConnect :
      connectBlockTxs txs utxoMap height blockTimestamp chainId = .ok (sumFees, finalMap)) :
    utxo_conserved txs utxoMap height blockTimestamp chainId ∧
    no_double_spend txs utxoMap height blockTimestamp chainId :=
  ⟨utxo_conservation_theorem txs utxoMap height blockTimestamp chainId sumFees finalMap hConnect,
   no_double_spend_theorem txs utxoMap height blockTimestamp chainId sumFees finalMap hConnect⟩

/-- Chain-level universal UTXO refinement: for any sequence of blocks,
    if `connectBlockSequence` succeeds over the entire chain, then every
    individual block preserves UTXO conservation and anti-double-spend.
    This is the strongest available UTXO refinement theorem — it composes
    block-level guarantees into a chain-wide invariant by induction. -/
theorem utxo_apply_basic_chain_refinement
    (steps : List ChainConnectStep)
    (utxoMap finalMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (hSequence : connectBlockSequence steps utxoMap = .ok finalMap) :
    chainConsistency steps utxoMap :=
  chainConsistency_inductive steps utxoMap finalMap hSequence

end RubinFormal