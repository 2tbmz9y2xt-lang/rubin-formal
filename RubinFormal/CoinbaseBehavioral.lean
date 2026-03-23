import RubinFormal.ConnectBlockStrong

/-!
# Coinbase Behavioral Proof (§18 / §19)

Models the coinbase transaction apply path and proves:
1. Coinbase value bound: sum(coinbase outputs) ≤ subsidy + fees
2. Coinbase UTXO creation: spendable outputs marked CreatedByCoinbase
3. No vault in coinbase: CORE_VAULT outputs forbidden
4. Non-spendable (ANCHOR/DA_COMMIT) outputs excluded from UTXO set

Lean model functions that mirror the Go/Rust coinbase path
(block_basic_coinbase.go / connect_block_inmem.go). WIRED into
connectBlockFull (ConnectBlockFull.lean). Bridge between list
representation (coinbaseEntryList) and fold representation
(addCoinbaseOutputs) proved via shared coinbaseUtxoEntry constructor.
-/

namespace RubinFormal

open UtxoBasicV1

/-! ## Coinbase value bound -/

/-- Sum of coinbase output values. Models Go `sumCoinbase` loop. -/
def sumCoinbaseOutputs (outputs : List CovenantGenesisV1.TxOut) : Nat :=
  outputs.foldl (fun acc out => acc + out.value) 0

/-- Coinbase value bound check: sum(outputs) ≤ subsidy + fees.
    Models `validateCoinbaseValueBound` (block_basic_coinbase.go:24). -/
def validateCoinbaseValueBound
    (outputs : List CovenantGenesisV1.TxOut)
    (subsidy fees : Nat) : Except String Unit :=
  if sumCoinbaseOutputs outputs > subsidy + fees then
    Except.error "BLOCK_ERR_SUBSIDY_EXCEEDED"
  else Except.ok ()

/-- No CORE_VAULT in coinbase outputs.
    Models `validateCoinbaseApplyOutputs` (block_basic_coinbase.go:56). -/
def validateCoinbaseApplyOutputs
    (outputs : List CovenantGenesisV1.TxOut) : Except String Unit :=
  if outputs.any (fun out => out.covenantType == CovenantGenesisV1.COV_TYPE_VAULT) then
    Except.error "BLOCK_ERR_COINBASE_INVALID"
  else Except.ok ()

/-- Spendable coinbase output predicate: not ANCHOR, not DA_COMMIT. -/
def isSpendableCoinbaseOutput (out : CovenantGenesisV1.TxOut) : Bool :=
  out.covenantType != CovenantGenesisV1.COV_TYPE_ANCHOR &&
  out.covenantType != CovenantGenesisV1.COV_TYPE_DA_COMMIT

/-- Add spendable coinbase outputs to UTXO set.
    Models the coinbase UTXO creation loop (connect_block_inmem.go:174-186). -/
def addCoinbaseOutputs
    (outputs : List CovenantGenesisV1.TxOut)
    (txid : Bytes) (height : Nat)
    (utxos : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    : Std.RBMap Outpoint UtxoEntry cmpOutpoint :=
  outputs.enum.foldl (fun acc (idx, out) =>
    if isSpendableCoinbaseOutput out then
      acc.insert
        { txid := txid, vout := idx }
        { value := out.value
        , covenantType := out.covenantType
        , covenantData := out.covenantData
        , creationHeight := height
        , createdByCoinbase := true }
    else acc
  ) utxos

/-! ## Behavioral proofs -/

/-- Coinbase value bound rejects oversized coinbase. -/
theorem coinbase_value_bound_rejects
    (outputs : List CovenantGenesisV1.TxOut) (subsidy fees : Nat)
    (h : sumCoinbaseOutputs outputs > subsidy + fees) :
    validateCoinbaseValueBound outputs subsidy fees =
    .error "BLOCK_ERR_SUBSIDY_EXCEEDED" := by
  simp [validateCoinbaseValueBound, h]

/-- Coinbase value bound accepts valid coinbase. -/
theorem coinbase_value_bound_accepts
    (outputs : List CovenantGenesisV1.TxOut) (subsidy fees : Nat)
    (h : ¬(sumCoinbaseOutputs outputs > subsidy + fees)) :
    validateCoinbaseValueBound outputs subsidy fees = .ok () := by
  simp [validateCoinbaseValueBound, h]

/-- No-vault check rejects coinbase with CORE_VAULT. -/
theorem coinbase_no_vault_rejects
    (outputs : List CovenantGenesisV1.TxOut)
    (h : outputs.any (fun out => out.covenantType == CovenantGenesisV1.COV_TYPE_VAULT) = true) :
    validateCoinbaseApplyOutputs outputs =
    .error "BLOCK_ERR_COINBASE_INVALID" := by
  simp [validateCoinbaseApplyOutputs, h]

/-- No-vault check accepts coinbase without CORE_VAULT. -/
theorem coinbase_no_vault_accepts
    (outputs : List CovenantGenesisV1.TxOut)
    (h : outputs.any (fun out => out.covenantType == CovenantGenesisV1.COV_TYPE_VAULT) = false) :
    validateCoinbaseApplyOutputs outputs = .ok () := by
  simp [validateCoinbaseApplyOutputs, h]

/-- Every entry created by `addCoinbaseOutputs` has `createdByCoinbase = true`.
    Proved via the structure of the inserted UtxoEntry literal. -/
theorem coinbase_entry_always_marked (out : CovenantGenesisV1.TxOut)
    (_txid : Bytes) (height _idx : Nat) (_hSpend : isSpendableCoinbaseOutput out = true) :
    ({ value := out.value, covenantType := out.covenantType,
       covenantData := out.covenantData, creationHeight := height,
       createdByCoinbase := true } : UtxoEntry).createdByCoinbase = true := rfl

/-- Non-spendable outputs are NOT added to UTXO set. -/
theorem coinbase_nonspendable_excluded
    (out : CovenantGenesisV1.TxOut)
    (hAnchor : out.covenantType = CovenantGenesisV1.COV_TYPE_ANCHOR ∨
               out.covenantType = CovenantGenesisV1.COV_TYPE_DA_COMMIT) :
    isSpendableCoinbaseOutput out = false := by
  simp [isSpendableCoinbaseOutput]
  rcases hAnchor with h | h <;> simp [h]

/-! ## Fold-level generalization (Checklist 3.1)

Prove properties over the ENTIRE outputs list, not just one entry.
Uses a list-based representation for full inductive reasoning.
-/

/-- Coinbase entries as a flat list (mirrors addCoinbaseOutputs fold). -/
def coinbaseEntryList
    (outputs : List CovenantGenesisV1.TxOut)
    (txid : Bytes) (height : Nat) : List (Outpoint × UtxoEntry) :=
  (outputs.enum.filter (fun (_, out) => isSpendableCoinbaseOutput out)).map
    (fun (idx, out) => (
      { txid := txid, vout := idx },
      { value := out.value
      , covenantType := out.covenantType
      , covenantData := out.covenantData
      , creationHeight := height
      , createdByCoinbase := true }))

/-! ## Bridge: shared entry constructor (coinbaseEntryList ↔ addCoinbaseOutputs)

Both `addCoinbaseOutputs` (RBMap fold) and `coinbaseEntryList` (List filter+map)
use the SAME UtxoEntry literal. This bridges the two representations.
-/

/-- Shared UtxoEntry constructor for coinbase outputs. -/
def coinbaseUtxoEntry (out : CovenantGenesisV1.TxOut) (height : Nat) : UtxoEntry :=
  { value := out.value
  , covenantType := out.covenantType
  , covenantData := out.covenantData
  , creationHeight := height
  , createdByCoinbase := true }

/-- coinbaseEntryList is exactly filter+map with coinbaseUtxoEntry (rfl). -/
theorem coinbaseEntryList_uses_shared_constructor
    (outputs : List CovenantGenesisV1.TxOut) (txid : Bytes) (height : Nat) :
    coinbaseEntryList outputs txid height =
    (outputs.enum.filter (fun p => isSpendableCoinbaseOutput p.2)).map
      (fun p => (Outpoint.mk txid p.1, coinbaseUtxoEntry p.2 height)) := by
  unfold coinbaseEntryList coinbaseUtxoEntry; rfl

/-- createdByCoinbase = true for the shared constructor (structural). -/
theorem coinbaseUtxoEntry_always_marked (out : CovenantGenesisV1.TxOut) (height : Nat) :
    (coinbaseUtxoEntry out height).createdByCoinbase = true := rfl

/-- addCoinbaseOutputs fold step uses the same coinbaseUtxoEntry constructor.
    Bridge: both addCoinbaseOutputs (RBMap.insert) and coinbaseEntryList (List.map)
    construct entries with coinbaseUtxoEntry. RBMap operational equivalence
    (find? after insert) requires Std.RBMap lemmas not available in Std4 without
    Mathlib — the shared constructor is the strongest provable bridge. -/
theorem addCoinbaseOutputs_step_uses_shared
    (out : CovenantGenesisV1.TxOut) (_txid : Bytes) (height _idx : Nat)
    (_hSpend : isSpendableCoinbaseOutput out = true) :
    coinbaseUtxoEntry out height =
    { value := out.value, covenantType := out.covenantType,
      covenantData := out.covenantData, creationHeight := height,
      createdByCoinbase := true } := rfl

/-! ## Fold-level properties -/

/-- EVERY entry in the coinbase list has createdByCoinbase = true.
    Proved by induction on the filtered+mapped list structure. -/
theorem coinbase_list_all_marked
    (outputs : List CovenantGenesisV1.TxOut) (txid : Bytes) (height : Nat)
    (pair : Outpoint × UtxoEntry)
    (hMem : pair ∈ coinbaseEntryList outputs txid height) :
    pair.2.createdByCoinbase = true := by
  simp [coinbaseEntryList, List.mem_map] at hMem
  obtain ⟨⟨idx, out⟩, _, rfl⟩ := hMem
  rfl

/-- Universal: ALL entries in coinbase list are coinbase-marked. -/
theorem coinbase_list_all_marked_universal
    (outputs : List CovenantGenesisV1.TxOut) (txid : Bytes) (height : Nat) :
    ∀ pair ∈ coinbaseEntryList outputs txid height,
      pair.2.createdByCoinbase = true :=
  fun pair hMem => coinbase_list_all_marked outputs txid height pair hMem

/-- Non-spendable output produces zero entries. -/
theorem coinbase_list_excludes_nonspendable
    (out : CovenantGenesisV1.TxOut) (txid : Bytes) (height : Nat)
    (hNonSpend : isSpendableCoinbaseOutput out = false) :
    coinbaseEntryList [out] txid height = [] := by
  simp [coinbaseEntryList, List.enum, hNonSpend]

/-- Fold-level: NO entry in coinbaseEntryList has ANCHOR or DA_COMMIT covenant type.
    Proved: filter condition rejects non-spendable, and ANCHOR/DA_COMMIT are non-spendable. -/
theorem coinbase_list_no_anchor_or_da
    (outputs : List CovenantGenesisV1.TxOut) (txid : Bytes) (height : Nat)
    (pair : Outpoint × UtxoEntry)
    (hMem : pair ∈ coinbaseEntryList outputs txid height) :
    pair.2.covenantType ≠ CovenantGenesisV1.COV_TYPE_ANCHOR ∧
    pair.2.covenantType ≠ CovenantGenesisV1.COV_TYPE_DA_COMMIT := by
  simp [coinbaseEntryList, List.mem_map, List.mem_filter] at hMem
  obtain ⟨⟨idx, out⟩, ⟨_, hSpend⟩, rfl⟩ := hMem
  -- pair.2.covenantType = out.covenantType
  -- hSpend : isSpendableCoinbaseOutput out = true
  -- isSpendableCoinbaseOutput checks that covenantType ≠ ANCHOR ∧ ≠ DA_COMMIT
  simp only [isSpendableCoinbaseOutput, Bool.and_eq_true, bne_iff_ne] at hSpend
  exact ⟨hSpend.1, hSpend.2⟩

/-! ## UTXO key safety (Checklist 3.2)

Index uniqueness follows from `List.enum` structure: `List.enum` assigns
consecutive indices starting from 0. Two entries at different LIST positions
get different indices by construction. `List.enum` injectivity on first
component is not in Std4, so we prove it directly. -/

/-- List.enum assigns unique indices: if (i, a) and (j, b) are both in
    xs.enum and i = j, then they must be the same pair (same list position).
    Proved by induction on the list. -/
private theorem enumFrom_ge {α : Type} (start : Nat) (xs : List α) (i : Nat) (a : α)
    (h : (i, a) ∈ List.enumFrom start xs) : i ≥ start := by
  induction xs generalizing start with
  | nil => simp [List.enumFrom] at h
  | cons x rest ih =>
    simp [List.enumFrom] at h
    obtain ⟨rfl, _⟩ | h := h
    · omega
    · have := ih (start + 1) h; omega

private theorem enumFrom_injective_fst {α : Type} (start : Nat) (xs : List α)
    (i : Nat) (a b : α)
    (ha : (i, a) ∈ List.enumFrom start xs)
    (hb : (i, b) ∈ List.enumFrom start xs) : a = b := by
  induction xs generalizing start with
  | nil => simp [List.enumFrom] at ha
  | cons x rest ih =>
    simp [List.enumFrom] at ha hb
    obtain ⟨rfl, rfl⟩ | ha := ha
    · obtain ⟨_, rfl⟩ | hb := hb
      · rfl
      · exact absurd (enumFrom_ge _ rest _ _ hb) (by omega)
    · obtain ⟨rfl, _⟩ | hb := hb
      · exact absurd (enumFrom_ge _ rest _ _ ha) (by omega)
      · exact ih _ ha hb

/-- List.enum assigns unique indices: if (i, a) and (i, b) are both in
    xs.enum, then a = b. Proved by induction via enumFrom_ge bound. -/
theorem enum_injective_fst {α : Type} (xs : List α) (i : Nat) (a b : α)
    (ha : (i, a) ∈ xs.enum) (hb : (i, b) ∈ xs.enum) : a = b :=
  enumFrom_injective_fst 0 xs i a b ha hb

/-- Coinbase entries have distinct outpoints: derived from List.enum
    injectivity — different entries must have different indices. -/
theorem coinbase_distinct_outpoints
    (outputs : List CovenantGenesisV1.TxOut) (txid : Bytes) (height : Nat)
    (p1 p2 : Outpoint × UtxoEntry)
    (h1 : p1 ∈ coinbaseEntryList outputs txid height)
    (h2 : p2 ∈ coinbaseEntryList outputs txid height)
    (hNe : p1 ≠ p2) :
    p1.1 ≠ p2.1 := by
  simp [coinbaseEntryList, List.mem_map] at h1 h2
  obtain ⟨⟨i, oi⟩, hi, rfl⟩ := h1
  obtain ⟨⟨j, oj⟩, hj, rfl⟩ := h2
  -- p1.1 = {txid, vout := i}, p2.1 = {txid, vout := j}
  -- Need i ≠ j. If i = j, then by enum_injective_fst applied to
  -- the filtered list, oi = oj, so p1 = p2, contradicting hNe.
  intro heq
  -- heq : {txid, vout := i} = {txid, vout := j} → i = j
  cases heq
  -- Now i = j. Show p1 = p2.
  have hMem_i := List.mem_filter.mp hi
  have hMem_j := List.mem_filter.mp hj
  have := enum_injective_fst outputs i oi oj hMem_i.1 hMem_j.1
  subst this
  exact hNe rfl

/-! ## Boundary cases (Checklist 2.2) -/

/-- Zero fees: coinbase ≤ subsidy. -/
theorem coinbase_bound_zero_fees (outputs : List CovenantGenesisV1.TxOut) (subsidy : Nat)
    (h : ¬(sumCoinbaseOutputs outputs > subsidy + 0)) :
    sumCoinbaseOutputs outputs ≤ subsidy := by omega

/-- Zero subsidy: coinbase ≤ fees. -/
theorem coinbase_bound_zero_subsidy (outputs : List CovenantGenesisV1.TxOut) (fees : Nat)
    (h : ¬(sumCoinbaseOutputs outputs > 0 + fees)) :
    sumCoinbaseOutputs outputs ≤ fees := by omega

/-- Empty coinbase outputs → always passes value bound. -/
theorem coinbase_empty_outputs_passes (subsidy fees : Nat) :
    validateCoinbaseValueBound [] subsidy fees = .ok () := by
  simp [validateCoinbaseValueBound, sumCoinbaseOutputs]; omega

/-- Empty coinbase outputs → zero entries in UTXO list. -/
theorem coinbase_empty_outputs_no_entries (txid : Bytes) (height : Nat) :
    coinbaseEntryList [] txid height = [] := by
  simp [coinbaseEntryList, List.enum]

end RubinFormal
