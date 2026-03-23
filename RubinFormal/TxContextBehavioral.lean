import RubinFormal.TxContextFormal

/-!
# TxContext Behavioral Proof (§14 / §18)

Models behavioral properties of the TxContext bundle construction path
with REAL parameters (totalIn, totalOut, height, continuing data).
WIRED into connectBlockFull (ConnectBlockFull.lean) — buildTxContext is
called as part of the live block connection pipeline.

Ext_id sorting properties are in TxContextFormal.lean (separate surface).
-/

namespace RubinFormal

/-! ## TxContext bundle types (modeling Go/Rust structs) -/

/-- Maximum continuing outputs per ext_id (CANONICAL). -/
def TXCONTEXT_MAX_CONTINUING_OUTPUTS : Nat := 2

/-- TxContext output view. -/
structure TxOutputView where
  value : Nat
  extPayload : List UInt8

/-- Per-ext_id continuing output bundle with bounded count. -/
structure TxContextContinuing where
  count : Nat
  outputs : List TxOutputView
  hBound : count ≤ TXCONTEXT_MAX_CONTINUING_OUTPUTS

/-- TxContext base — immutable transaction-level context. -/
structure TxContextBase where
  totalIn : Nat
  totalOut : Nat
  height : Nat

/-- Full TxContext bundle. -/
structure TxContextBundle where
  base : TxContextBase
  continuingByExt : List (Nat × TxContextContinuing)
  continuingExtIds : List Nat

/-! ## BuildTxContext with real parameters -/

/-- Build TxContext bundle from real parameters.
    Models Go BuildTxContext / Rust build_tx_context.
    Takes actual totalIn, totalOut, height, and continuing data.
    Called from connectBlockFull (block-level) with block aggregates,
    AND from buildPerTxContext (ConnectBlockFull.lean) with per-tx params.
    Both paths use the same buildTxContext — per-tx properties proved
    via perTx_context_base_values and perTx_context_ext_ids. -/
def buildTxContext
    (activeExtIds : List Nat)
    (totalIn totalOut height : Nat)
    (continuingData : List (Nat × TxContextContinuing))
    : Option TxContextBundle :=
  if activeExtIds.length = 0 then none
  else some {
    base := { totalIn := totalIn, totalOut := totalOut, height := height }
    continuingByExt := continuingData
    continuingExtIds := activeExtIds
  }

/-! ## Nil/Some behavioral properties -/

/-- No active ext_ids → no bundle produced. -/
theorem buildTxContext_nil (tin tout h : Nat) (cd : List (Nat × TxContextContinuing)) :
    buildTxContext [] tin tout h cd = none := rfl

/-- Active ext_ids → bundle produced. -/
theorem buildTxContext_some (ids : List Nat) (hLen : ids.length > 0)
    (tin tout ht : Nat) (cd : List (Nat × TxContextContinuing)) :
    (buildTxContext ids tin tout ht cd).isSome = true := by
  simp only [buildTxContext]; split
  · rename_i heq; omega
  · rfl

/-! ## Structural correctness — bundle fields match inputs -/

/-- Bundle ext_ids = input ext_ids (no reordering, no drops, no additions). -/
theorem buildTxContext_ext_ids (ids : List Nat) (hLen : ids.length > 0)
    (tin tout ht : Nat) (cd : List (Nat × TxContextContinuing))
    (bundle : TxContextBundle)
    (hEq : buildTxContext ids tin tout ht cd = some bundle) :
    bundle.continuingExtIds = ids := by
  simp only [buildTxContext] at hEq; split at hEq
  · rename_i heq; omega
  · cases hEq; rfl

/-- Bundle base fields reflect real parameters. -/
theorem buildTxContext_base_values (ids : List Nat) (hLen : ids.length > 0)
    (tin tout ht : Nat) (cd : List (Nat × TxContextContinuing))
    (bundle : TxContextBundle)
    (hEq : buildTxContext ids tin tout ht cd = some bundle) :
    bundle.base.totalIn = tin ∧ bundle.base.totalOut = tout ∧ bundle.base.height = ht := by
  simp only [buildTxContext] at hEq; split at hEq
  · rename_i heq; omega
  · cases hEq; exact ⟨rfl, rfl, rfl⟩

/-- Bundle continuing data = input continuing data. -/
theorem buildTxContext_continuing_data (ids : List Nat) (hLen : ids.length > 0)
    (tin tout ht : Nat) (cd : List (Nat × TxContextContinuing))
    (bundle : TxContextBundle)
    (hEq : buildTxContext ids tin tout ht cd = some bundle) :
    bundle.continuingByExt = cd := by
  simp only [buildTxContext] at hEq; split at hEq
  · rename_i heq; omega
  · cases hEq; rfl

/-! ## Derived properties -/

/-- No-dup preservation: if input ids are unique, bundle ids are unique. -/
theorem buildTxContext_preserves_nodup (ids : List Nat) (hLen : ids.length > 0)
    (hNodup : ids.Nodup)
    (tin tout ht : Nat) (cd : List (Nat × TxContextContinuing))
    (bundle : TxContextBundle)
    (hEq : buildTxContext ids tin tout ht cd = some bundle) :
    bundle.continuingExtIds.Nodup := by
  rw [buildTxContext_ext_ids ids hLen tin tout ht cd bundle hEq]; exact hNodup

/-- Value conservation: totalIn in bundle = sum of input values. -/
theorem buildTxContext_totalIn_is_sum (ids : List Nat) (hLen : ids.length > 0)
    (inputValues : List Nat) (tout ht : Nat)
    (cd : List (Nat × TxContextContinuing))
    (bundle : TxContextBundle)
    (hEq : buildTxContext ids (inputValues.foldl (· + ·) 0) tout ht cd = some bundle) :
    bundle.base.totalIn = inputValues.foldl (· + ·) 0 :=
  (buildTxContext_base_values ids hLen _ _ _ cd bundle hEq).1

/-- Value conservation: totalOut in bundle = sum of output values. -/
theorem buildTxContext_totalOut_is_sum (ids : List Nat) (hLen : ids.length > 0)
    (tin : Nat) (outputValues : List Nat) (ht : Nat)
    (cd : List (Nat × TxContextContinuing))
    (bundle : TxContextBundle)
    (hEq : buildTxContext ids tin (outputValues.foldl (· + ·) 0) ht cd = some bundle) :
    bundle.base.totalOut = outputValues.foldl (· + ·) 0 :=
  (buildTxContext_base_values ids hLen _ _ _ cd bundle hEq).2.1

/-- Height correctness: bundle height = block height. -/
theorem buildTxContext_height (ids : List Nat) (hLen : ids.length > 0)
    (tin tout blockHeight : Nat)
    (cd : List (Nat × TxContextContinuing))
    (bundle : TxContextBundle)
    (hEq : buildTxContext ids tin tout blockHeight cd = some bundle) :
    bundle.base.height = blockHeight :=
  (buildTxContext_base_values ids hLen _ _ _ cd bundle hEq).2.2

/-- Continuing output count bounded by MAX for every entry in bundle. -/
theorem buildTxContext_continuing_bounded
    (cont : TxContextContinuing) :
    cont.count ≤ TXCONTEXT_MAX_CONTINUING_OUTPUTS :=
  cont.hBound

/-- MAX_CONTINUING_OUTPUTS = 2 (canonical constant). -/
theorem max_continuing_outputs_value : TXCONTEXT_MAX_CONTINUING_OUTPUTS = 2 := rfl

/-! ## Ext_id ordering

Ext_id sort properties are already proved in TxContextFormal.lean:
- extid_sort_sorted_perm: sortAscending produces Perm ∧ Sorted
- extid_sort_deterministic: sortAscending is deterministic (pure function)
- Multiple concrete CV vector replays

These are reused by reference, not duplicated here. -/

end RubinFormal
