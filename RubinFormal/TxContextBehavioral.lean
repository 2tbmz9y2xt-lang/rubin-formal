import RubinFormal.TxContextFormal

/-!
# TxContext Behavioral Proof (§14 / §18)

Models behavioral properties of the TxContext bundle construction path:
1. No active profiles → nil bundle (no TxContext processing)
2. Continuing output count bounded by MAX_CONTINUING_OUTPUTS (type-enforced)
3. Empty value sum = 0

These are property-level models, NOT wired into the live BuildTxContext
function. Equivalence with Go/Rust is structural, not rfl-proved.
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

/-- Per-ext_id continuing output bundle. -/
structure TxContextContinuing where
  count : Nat
  outputs : List TxOutputView
  hBound : count ≤ TXCONTEXT_MAX_CONTINUING_OUTPUTS

/-- TxContext base (immutable tx-level context). -/
structure TxContextBase where
  totalIn : Nat
  totalOut : Nat
  height : Nat

/-- Full TxContext bundle. -/
structure TxContextBundle where
  base : TxContextBase
  continuingByExt : List (Nat × TxContextContinuing)
  continuingExtIds : List Nat

/-! ## BuildTxContext behavioral properties -/

/-- No active ext_ids → no bundle produced. -/
def buildTxContextResult (activeExtIds : List Nat) : Option TxContextBundle :=
  if activeExtIds.length = 0 then none
  else some {
    base := { totalIn := 0, totalOut := 0, height := 0 }
    continuingByExt := []
    continuingExtIds := activeExtIds
  }

/-- No active profiles → BuildTxContext returns nil.
    Direct model of Go BuildTxContext lines 241-243. -/
theorem buildTxContext_nil_when_no_active :
    buildTxContextResult [] = none := rfl

/-- Active profiles → BuildTxContext returns some bundle. -/
theorem buildTxContext_some_when_active (ids : List Nat) (h : ids.length > 0) :
    (buildTxContextResult ids).isSome = true := by
  simp only [buildTxContextResult]
  split
  · rename_i heq; omega
  · rfl

/-- Structural correctness: returned bundle contains EXACTLY the active ext_ids,
    in the same order, with no duplicates introduced and no ids dropped.
    This is stronger than just `isSome` — it constrains the bundle FIELDS. -/
theorem buildTxContext_bundle_ext_ids (ids : List Nat) (h : ids.length > 0)
    (bundle : TxContextBundle)
    (hEq : buildTxContextResult ids = some bundle) :
    bundle.continuingExtIds = ids := by
  simp only [buildTxContextResult] at hEq
  split at hEq
  · rename_i heq; omega
  · cases hEq; rfl

/-- If input ids have no duplicates, bundle ext_ids have no duplicates. -/
theorem buildTxContext_preserves_nodup (ids : List Nat) (h : ids.length > 0)
    (hNodup : ids.Nodup)
    (bundle : TxContextBundle)
    (hEq : buildTxContextResult ids = some bundle) :
    bundle.continuingExtIds.Nodup := by
  have := buildTxContext_bundle_ext_ids ids h bundle hEq
  rw [this]; exact hNodup

/-- Bundle ext_ids are a permutation of input ids (trivially equal). -/
theorem buildTxContext_ext_ids_perm (ids : List Nat) (h : ids.length > 0)
    (bundle : TxContextBundle)
    (hEq : buildTxContextResult ids = some bundle) :
    bundle.continuingExtIds.Perm ids := by
  have := buildTxContext_bundle_ext_ids ids h bundle hEq
  rw [this]

/-- Continuing output count is bounded by MAX. -/
theorem continuing_count_bounded (c : TxContextContinuing) :
    c.count ≤ TXCONTEXT_MAX_CONTINUING_OUTPUTS :=
  c.hBound

/-- MAX_CONTINUING_OUTPUTS = 2. -/
theorem max_continuing_outputs_value :
    TXCONTEXT_MAX_CONTINUING_OUTPUTS = 2 := rfl

/-! ## Sum correctness -/

/-- Sum of input values. Models `sumTxContextInputValues`. -/
def sumInputValues (values : List Nat) : Nat :=
  values.foldl (· + ·) 0

/-- Sum of output values. Models `sumTxContextOutputValues`. -/
def sumOutputValues (values : List Nat) : Nat :=
  values.foldl (· + ·) 0

/-- Sum over empty list is zero. -/
theorem sum_empty : sumInputValues [] = 0 := rfl

/-! ## Ext_id ordering

Ext_id sort properties are already proved in TxContextFormal.lean:
- extid_sort_sorted_perm: sortAscending produces Perm ∧ Sorted
- extid_sort_deterministic: sortAscending is deterministic (pure function)
- Multiple concrete CV vector replays

These are reused by reference, not duplicated here. -/

end RubinFormal
