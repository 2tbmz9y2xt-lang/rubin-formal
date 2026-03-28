/-
  TxWireContractGap.lean — closes #299 (Q-FORMAL-VERIFY-TX-WIRE-CONTRACT-01)
  Proves:
  - parseTx result coherence (no-panic contract)

  Gap origin: TZ-VERIFY-01 matrix claimed parse_tx no-panic +L and marshal→parse +L
  but the original work plan failed to schedule these explicitly.
  The no-panic contract is fully closed here.
  marshal→parse primitive roundtrips (u32le, u64le, CompactSize) are already proved
  in ByteWireV2.lean and TxWireRoundtrip.lean.
-/
import RubinFormal.TxParseV2

set_option maxHeartbeats 8000000

namespace RubinFormal

open Wire TxV2

-- ═══════════════════════════════════════════════════════════════════
-- §1  parseTx result coherence (no-panic contract)
-- ═══════════════════════════════════════════════════════════════════

/-- `fail` always produces a coherent negative result. -/
theorem fail_coherent (e : TxErr) :
    (fail e).ok = false ∧ (fail e).err = some e ∧
    (fail e).txid = none ∧ (fail e).wtxid = none :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- parseTx is total (Lean type system) and always produces a coherent result:
    either (ok=true, err=none, txid present, wtxid present)
    or     (ok=false, err present, txid=none, wtxid=none).
    This is the "no-panic" contract: parseTx never produces an inconsistent
    ParseResult (e.g., ok=true with txid=none, or ok=false with err=none). -/
theorem parseTx_coherent (tx : Bytes) :
    let r := parseTx tx
    (r.ok = true ∧ r.err = none ∧ r.txid.isSome = true ∧ r.wtxid.isSome = true) ∨
    (r.ok = false ∧ r.err.isSome = true ∧ r.txid = none ∧ r.wtxid = none) := by
  simp only [parseTx, fail]
  -- Every branch of parseTx is either `fail e` (right disjunct) or the
  -- single success record at the bottom (left disjunct).
  -- Strategy: split each match/if, close fail branches with right+rfl,
  -- close the success branch with left+rfl.
  repeat (first
    | exact Or.inl ⟨rfl, rfl, rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl, rfl, rfl⟩
    | split)

/-- If parseTx returns ok=true, then err=none and both txid/wtxid are present. -/
theorem parseTx_ok_implies_complete (tx : Bytes) (h : (parseTx tx).ok = true) :
    (parseTx tx).err = none ∧ (parseTx tx).txid.isSome = true ∧
    (parseTx tx).wtxid.isSome = true := by
  rcases parseTx_coherent tx with ⟨_, he, ht, hw⟩ | ⟨hf, _, _, _⟩
  · exact ⟨he, ht, hw⟩
  · exact absurd h (by rw [hf]; decide)

/-- If parseTx returns ok=false, then err is present and txid/wtxid are none. -/
theorem parseTx_fail_implies_complete (tx : Bytes) (h : (parseTx tx).ok = false) :
    (parseTx tx).err.isSome = true ∧ (parseTx tx).txid = none ∧
    (parseTx tx).wtxid = none := by
  rcases parseTx_coherent tx with ⟨ht, _, _, _⟩ | ⟨_, he, hti, hwi⟩
  · exact absurd h (by rw [ht]; decide)
  · exact ⟨he, hti, hwi⟩

/-- parseTx ok result always has txid. -/
theorem parseTx_ok_has_txid (tx : Bytes) (h : (parseTx tx).ok = true) :
    ∃ t, (parseTx tx).txid = some t := by
  have ⟨_, ht, _⟩ := parseTx_ok_implies_complete tx h
  exact Option.isSome_iff_exists.mp ht

/-- parseTx ok result always has wtxid. -/
theorem parseTx_ok_has_wtxid (tx : Bytes) (h : (parseTx tx).ok = true) :
    ∃ w, (parseTx tx).wtxid = some w := by
  have ⟨_, _, hw⟩ := parseTx_ok_implies_complete tx h
  exact Option.isSome_iff_exists.mp hw

/-- parseTx fail result always has a specific error. -/
theorem parseTx_fail_has_err (tx : Bytes) (h : (parseTx tx).ok = false) :
    ∃ e, (parseTx tx).err = some e := by
  have ⟨he, _, _⟩ := parseTx_fail_implies_complete tx h
  exact Option.isSome_iff_exists.mp he

-- ═══════════════════════════════════════════════════════════════════
-- §2  Coverage notes (explicit gap narrowing)
-- ═══════════════════════════════════════════════════════════════════

/-!
## Coverage vs TZ-VERIFY-01 matrix

### parse_tx no-panic (+L) — CLOSED
`parseTx_coherent` proves that every parseTx result is either a well-formed
success (ok=true, err=none, txid/wtxid present) or a well-formed failure
(ok=false, err present, txid/wtxid=none). Combined with Lean 4's type system
guaranteeing totality, this closes the no-panic claim.

Derived theorems provide direct accessors:
- `parseTx_ok_implies_complete` / `parseTx_fail_implies_complete`
- `parseTx_ok_has_txid` / `parseTx_ok_has_wtxid` / `parseTx_fail_has_err`

### marshal→parse (+L) — NARROWED (not in scope for this issue)
Full V2 transaction marshal→parse roundtrip (`marshalTx ∘ parseTx = id`)
requires a `marshalTx : Tx → Bytes` serializer that does not yet exist in the
codebase. The gap is narrowed to primitive roundtrips already proved elsewhere:
- **Value-level**: `u32le_ofNat_roundtrip`, `u64le_ofNat_roundtrip` (ByteWireV2.lean)
- **Cursor-level**: `compactSize_encode_roundtrip` (ByteWireV2.lean)
- **Cursor advancement**: `getU32le_advances`, `getU64le_advances` (TxWireRoundtrip.lean)
- **Encode sizes**: `u32le_size`, `u64le_size`, `compactSize_size_*` (TxWireRoundtrip.lean)
- **Legacy roundtrip**: `parse_serializeTxMini_roundtrip` (ByteWireLegacy.lean)
- **Remaining**: Define V2 `marshalTx` and prove full roundtrip. Tracked separately
  as it requires consensus on the V2 serialization format.
-/

end RubinFormal
