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

/-! ## Real value computation (models Go sumTxContextInputValues) -/

/-- Sum input values by folding over resolved inputs. -/
def sumInputValues (values : List Nat) : Nat := values.foldl (· + ·) 0

/-- Sum output values by folding over tx outputs. -/
def sumOutputValues (values : List Nat) : Nat := values.foldl (· + ·) 0

/-- BuildTxContext with COMPUTED totalIn/totalOut from real value lists.
    This is the REAL path: totalIn/totalOut are not free parameters
    but computed from actual input/output values via fold. -/
def buildTxContextFromValues
    (activeExtIds : List Nat)
    (inputValues outputValues : List Nat)
    (height : Nat)
    (continuingData : List (Nat × TxContextContinuing))
    : Option TxContextBundle :=
  buildTxContext activeExtIds (sumInputValues inputValues) (sumOutputValues outputValues) height continuingData

/-! ## Value conservation with REAL sums (not free parameters) -/

/-- bundle.totalIn = fold sum of actual input values. -/
theorem buildTxContextFromValues_totalIn_real
    (ids : List Nat) (hLen : ids.length > 0)
    (inVals outVals : List Nat) (ht : Nat)
    (cd : List (Nat × TxContextContinuing))
    (bundle : TxContextBundle)
    (hEq : buildTxContextFromValues ids inVals outVals ht cd = some bundle) :
    bundle.base.totalIn = sumInputValues inVals :=
  (buildTxContext_base_values ids hLen _ _ _ cd bundle hEq).1

/-- bundle.totalOut = fold sum of actual output values. -/
theorem buildTxContextFromValues_totalOut_real
    (ids : List Nat) (hLen : ids.length > 0)
    (inVals outVals : List Nat) (ht : Nat)
    (cd : List (Nat × TxContextContinuing))
    (bundle : TxContextBundle)
    (hEq : buildTxContextFromValues ids inVals outVals ht cd = some bundle) :
    bundle.base.totalOut = sumOutputValues outVals :=
  (buildTxContext_base_values ids hLen _ _ _ cd bundle hEq).2.1

/-- bundle.height = block height (wired through buildTxContextFromValues). -/
theorem buildTxContextFromValues_height_real
    (ids : List Nat) (hLen : ids.length > 0)
    (inVals outVals : List Nat) (blockHeight : Nat)
    (cd : List (Nat × TxContextContinuing))
    (bundle : TxContextBundle)
    (hEq : buildTxContextFromValues ids inVals outVals blockHeight cd = some bundle) :
    bundle.base.height = blockHeight :=
  (buildTxContext_base_values ids hLen _ _ _ cd bundle hEq).2.2

/-! ## Continuing output bounds (type invariant, not precondition) -/

/-- Every TxContextContinuing carries count ≤ MAX as TYPE INVARIANT. -/
theorem continuing_bound_is_invariant (cont : TxContextContinuing) :
    cont.count ≤ TXCONTEXT_MAX_CONTINUING_OUTPUTS := cont.hBound

/-- MAX = 2 (canonical constant from §14). -/
theorem max_continuing_is_two : TXCONTEXT_MAX_CONTINUING_OUTPUTS = 2 := rfl

/-- ALL continuings in a built bundle have count ≤ 2 (fold-level). -/
theorem buildTxContext_all_continuings_bounded
    (ids : List Nat) (hLen : ids.length > 0)
    (tin tout ht : Nat) (cd : List (Nat × TxContextContinuing))
    (bundle : TxContextBundle)
    (hEq : buildTxContext ids tin tout ht cd = some bundle)
    (pair : Nat × TxContextContinuing)
    (hMem : pair ∈ bundle.continuingByExt) :
    pair.2.count ≤ 2 := by
  have hCd := buildTxContext_continuing_data ids hLen tin tout ht cd bundle hEq
  rw [hCd] at hMem; exact pair.2.hBound

/-! ## Cross-property: value conservation (fee ≥ 0) -/

/-- If inputs ≥ outputs, bundle preserves totalIn ≥ totalOut. -/
theorem buildTxContextFromValues_value_conservation
    (ids : List Nat) (hLen : ids.length > 0)
    (inVals outVals : List Nat) (ht : Nat)
    (cd : List (Nat × TxContextContinuing))
    (bundle : TxContextBundle)
    (hEq : buildTxContextFromValues ids inVals outVals ht cd = some bundle)
    (hFee : sumInputValues inVals ≥ sumOutputValues outVals) :
    bundle.base.totalIn ≥ bundle.base.totalOut := by
  have hIn := buildTxContextFromValues_totalIn_real ids hLen inVals outVals ht cd bundle hEq
  have hOut := buildTxContextFromValues_totalOut_real ids hLen inVals outVals ht cd bundle hEq
  omega

/-! ## Ext_id ordering

Ext_id sort properties are already proved in TxContextFormal.lean:
- extid_sort_sorted_perm: sortAscending produces Perm ∧ Sorted
- extid_sort_deterministic: sortAscending is deterministic (pure function)
- Multiple concrete CV vector replays

These are reused by reference, not duplicated here. -/

end RubinFormal
