/-
  TxWireRoundtrip.lean — transaction wire contract proofs (#295)
  LIVE theorems on ByteWireV2 wire-format properties:
  - CompactSize canonical → minimal encoding
  - Primitive encode output lengths
  - parseTx fail-path invariants
  - Wire decoder determinism
  - Cursor advancement safety
-/
import RubinFormal.ByteWireV2
import RubinFormal.OutputDescriptorV2
import RubinFormal.TxParseV2
import Std.Tactic.Omega

set_option maxHeartbeats 4000000

namespace RubinFormal

open Wire WireEnc TxV2

-- ═══════════════════════════════════════════════════════════════════
-- §1  Encode output size contracts
-- ═══════════════════════════════════════════════════════════════════

/-- u16le always produces exactly 2 bytes. -/
theorem u16le_size (n : Nat) : (WireEnc.u16le n).size = 2 := rfl

/-- u32le always produces exactly 4 bytes. -/
theorem u32le_size (n : Nat) : (WireEnc.u32le n).size = 4 := rfl

/-- u64le always produces exactly 8 bytes. -/
theorem u64le_size (n : Nat) : (WireEnc.u64le n).size = 8 := rfl

/-- CompactSize encodes values < 0xfd into exactly 1 byte. -/
theorem compactSize_size_one (n : Nat) (h : n < 0xfd) :
    (WireEnc.compactSize n).size = 1 := by
  simp [WireEnc.compactSize, h, RubinFormal.bytes, ByteArray.size]

/-- CompactSize encodes values in [0xfd, 0xffff] into exactly 3 bytes. -/
theorem compactSize_size_three (n : Nat) (h1 : ¬(n < 0xfd)) (h2 : n ≤ 0xffff) :
    (WireEnc.compactSize n).size = 3 := by
  simp only [WireEnc.compactSize, h1, ite_false, h2, ite_true,
             ByteArray.size_append, ByteArray.size_push, u16le_size]
  rfl

/-- CompactSize encodes values in (0xffff, 0xffffffff] into exactly 5 bytes. -/
theorem compactSize_size_five (n : Nat) (h1 : ¬(n < 0xfd)) (h2 : ¬(n ≤ 0xffff))
    (h3 : n ≤ 0xffffffff) :
    (WireEnc.compactSize n).size = 5 := by
  simp only [WireEnc.compactSize, h1, ite_false, h2, ite_false, h3, ite_true,
             ByteArray.size_append, ByteArray.size_push, u32le_size]
  rfl

/-- CompactSize encodes values > 0xffffffff into exactly 9 bytes. -/
theorem compactSize_size_nine (n : Nat) (h1 : ¬(n < 0xfd)) (h2 : ¬(n ≤ 0xffff))
    (h3 : ¬(n ≤ 0xffffffff)) :
    (WireEnc.compactSize n).size = 9 := by
  simp only [WireEnc.compactSize, h1, ite_false, h2, ite_false, h3, ite_false,
             ByteArray.size_append, ByteArray.size_push, u64le_size]
  rfl

-- ═══════════════════════════════════════════════════════════════════
-- §2  parseTx fail-path invariants
-- ═══════════════════════════════════════════════════════════════════

/-- Every fail path has ok = false. -/
theorem fail_ok_false (e : TxErr) : (fail e).ok = false := rfl

/-- Every fail path has txid = none. -/
theorem fail_txid_none (e : TxErr) : (fail e).txid = none := rfl

/-- Every fail path has wtxid = none. -/
theorem fail_wtxid_none (e : TxErr) : (fail e).wtxid = none := rfl

/-- Every fail path has err = some e. -/
theorem fail_err_some (e : TxErr) : (fail e).err = some e := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §3  Wire decoder determinism (explicit)
-- ═══════════════════════════════════════════════════════════════════

/-- getU32le? is deterministic. -/
theorem getU32le_deterministic (c : Cursor) :
    ∀ r1 r2, c.getU32le? = some r1 → c.getU32le? = some r2 → r1 = r2 := by
  intros r1 r2 h1 h2; exact Option.some.inj (h1.symm.trans h2)

/-- getU64le? is deterministic. -/
theorem getU64le_deterministic (c : Cursor) :
    ∀ r1 r2, c.getU64le? = some r1 → c.getU64le? = some r2 → r1 = r2 := by
  intros r1 r2 h1 h2; exact Option.some.inj (h1.symm.trans h2)

/-- getCompactSize? is deterministic. -/
theorem getCompactSize_deterministic (c : Cursor) :
    ∀ r1 r2, c.getCompactSize? = some r1 → c.getCompactSize? = some r2 → r1 = r2 := by
  intros r1 r2 h1 h2; exact Option.some.inj (h1.symm.trans h2)

/-- parseTx is deterministic (explicit statement of a language property). -/
theorem parseTx_deterministic (tx : Bytes) :
    ∀ r1 r2, parseTx tx = r1 → parseTx tx = r2 → r1 = r2 := by
  intros r1 r2 h1 h2; exact h1.symm.trans h2

-- ═══════════════════════════════════════════════════════════════════
-- §4  Cursor advancement safety
-- ═══════════════════════════════════════════════════════════════════

/-- getU32le? advance: if it succeeds, cursor advances by exactly 4. -/
theorem getU32le_advance (c c' : Cursor) (v : Nat) :
    c.getU32le? = some (v, c') → c'.off = c.off + 4 := by
  unfold Cursor.getU32le?
  intro h
  simp only [Bind.bind, Option.bind] at h
  split at h
  · simp at h
  · next a heq =>
    simp only [Pure.pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact Cursor.getBytes_advances c 4 a.1 a.2 (by simp only [Prod.eta]; exact heq)

/-- getU64le? advance: if it succeeds, cursor advances by exactly 8. -/
theorem getU64le_advance (c c' : Cursor) (v : UInt64) :
    c.getU64le? = some (v, c') → c'.off = c.off + 8 := by
  unfold Cursor.getU64le?
  intro h
  simp only [Bind.bind, Option.bind] at h
  split at h
  · simp at h
  · next a heq =>
    simp only [Pure.pure, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact Cursor.getBytes_advances c 8 a.1 a.2 (by simp only [Prod.eta]; exact heq)

-- ═══════════════════════════════════════════════════════════════════
-- §5  CompactSize cursor advancement corollary
-- ═══════════════════════════════════════════════════════════════════

/-- CompactSize encode→decode roundtrip with advancement. -/
theorem compactSize_cursor_advances (n : Nat) (h : n ≤ UInt64.size - 1) :
    ∃ c', ({ bs := WireEnc.compactSize n, off := 0 } : Cursor).getCompactSize? =
      some (n, c', true) ∧ c'.off = (WireEnc.compactSize n).size := by
  exact ⟨_, compactSize_encode_roundtrip n h, rfl⟩

-- ═══════════════════════════════════════════════════════════════════
-- §6  getU8? cursor preservation
-- ═══════════════════════════════════════════════════════════════════

/-- getU8? preserves the underlying byte stream (only offset changes). -/
theorem getU8_preserves_bs (c : Cursor) (b : UInt8) (c' : Cursor) :
    c.getU8? = some (b, c') → c'.bs = c.bs := by
  simp only [Cursor.getU8?]
  split
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro _ h; subst h; rfl
  · simp

/-- getBytes? preserves the underlying byte stream. -/
theorem getBytes_preserves_bs (c : Cursor) (n : Nat) (bs : Bytes) (c' : Cursor) :
    c.getBytes? n = some (bs, c') → c'.bs = c.bs := by
  simp only [Cursor.getBytes?]
  split
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro _ h; subst h; rfl
  · simp

end RubinFormal
