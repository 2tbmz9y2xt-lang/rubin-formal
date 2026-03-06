import RubinFormal.Types

namespace RubinFormal

namespace Wire

structure Cursor where
  bs : Bytes
  off : Nat

def Cursor.remaining (c : Cursor) : Nat :=
  c.bs.size - c.off

def Cursor.getU8? (c : Cursor) : Option (UInt8 × Cursor) :=
  if h : c.off < c.bs.size then
    let b := c.bs.get! c.off
    some (b, { c with off := c.off + 1 })
  else
    none

def Cursor.getBytes? (c : Cursor) (n : Nat) : Option (Bytes × Cursor) :=
  if c.off + n <= c.bs.size then
    let out := c.bs.extract c.off (c.off + n)
    some (out, { c with off := c.off + n })
  else
    none

def u16le? (b0 b1 : UInt8) : Nat :=
  (b0.toNat) + (b1.toNat <<< 8)

def u32le? (b0 b1 b2 b3 : UInt8) : Nat :=
  (b0.toNat) + (b1.toNat <<< 8) + (b2.toNat <<< 16) + (b3.toNat <<< 24)

def u64le? (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) : UInt64 :=
  (UInt64.ofNat b0.toNat) |||
  ((UInt64.ofNat b1.toNat) <<< 8) |||
  ((UInt64.ofNat b2.toNat) <<< 16) |||
  ((UInt64.ofNat b3.toNat) <<< 24) |||
  ((UInt64.ofNat b4.toNat) <<< 32) |||
  ((UInt64.ofNat b5.toNat) <<< 40) |||
  ((UInt64.ofNat b6.toNat) <<< 48) |||
  ((UInt64.ofNat b7.toNat) <<< 56)

def Cursor.getU32le? (c : Cursor) : Option (Nat × Cursor) := do
  let (bs, c') ← c.getBytes? 4
  let b0 := bs.get! 0
  let b1 := bs.get! 1
  let b2 := bs.get! 2
  let b3 := bs.get! 3
  pure (u32le? b0 b1 b2 b3, c')

def Cursor.getU64le? (c : Cursor) : Option (UInt64 × Cursor) := do
  let (bs, c') ← c.getBytes? 8
  let b0 := bs.get! 0
  let b1 := bs.get! 1
  let b2 := bs.get! 2
  let b3 := bs.get! 3
  let b4 := bs.get! 4
  let b5 := bs.get! 5
  let b6 := bs.get! 6
  let b7 := bs.get! 7
  pure (u64le? b0 b1 b2 b3 b4 b5 b6 b7, c')

inductive TxErr where
  | parse
  | witnessOverflow
  | sigAlgInvalid
  | sigNoncanonical
deriving DecidableEq

def TxErr.toString : TxErr -> String
  | .parse => "TX_ERR_PARSE"
  | .witnessOverflow => "TX_ERR_WITNESS_OVERFLOW"
  | .sigAlgInvalid => "TX_ERR_SIG_ALG_INVALID"
  | .sigNoncanonical => "TX_ERR_SIG_NONCANONICAL"

structure ParseResult where
  ok : Bool
  err : Option TxErr
  txid : Option Bytes
  wtxid : Option Bytes

-- CompactSize (Varint) with minimality constraints (FIPS 202 spec section 3).
def Cursor.getCompactSize? (c : Cursor) : Option (Nat × Cursor × Bool) := do
  let (b, c1) ← c.getU8?
  let tag := b.toNat
  if tag < 0xfd then
    pure (tag, c1, true)
  else if tag == 0xfd then
    let (raw, c2) ← c1.getBytes? 2
    let n := u16le? (raw.get! 0) (raw.get! 1)
    let minimal := n >= 0xfd
    pure (n, c2, minimal)
  else if tag == 0xfe then
    let (raw, c2) ← c1.getBytes? 4
    let n := u32le? (raw.get! 0) (raw.get! 1) (raw.get! 2) (raw.get! 3)
    let minimal := n > 0xffff
    pure (n, c2, minimal)
  else
    let (raw, c2) ← c1.getBytes? 8
    let n64 := u64le? (raw.get! 0) (raw.get! 1) (raw.get! 2) (raw.get! 3) (raw.get! 4) (raw.get! 5) (raw.get! 6) (raw.get! 7)
    let n := n64.toNat
    let minimal := n > 0xffffffff
    pure (n, c2, minimal)

-- ═══════════════════════════════════════════════════════════════════
-- ByteWireV2 structural theorems (F-05 fix, Q-FORMAL-GAP-04)
-- ═══════════════════════════════════════════════════════════════════

/-- getU8? advances the cursor by exactly 1 byte when it succeeds. -/
theorem Cursor.getU8_advances (c : Cursor) (b : UInt8) (c' : Cursor) :
    c.getU8? = some (b, c') → c'.off = c.off + 1 := by
  simp only [Cursor.getU8?]
  split
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro _ h; subst h; rfl
  · simp

/-- getBytes? advances the cursor by exactly n bytes when it succeeds. -/
theorem Cursor.getBytes_advances (c : Cursor) (n : Nat) (bs : Bytes) (c' : Cursor) :
    c.getBytes? n = some (bs, c') → c'.off = c.off + n := by
  simp only [Cursor.getBytes?]
  split
  · simp only [Option.some.injEq, Prod.mk.injEq, and_imp]
    intro _ h; subst h; rfl
  · simp

/-- getU8? only succeeds when there is remaining data (off < size). -/
theorem Cursor.getU8_requires_data (c : Cursor) :
    (∃ b c', c.getU8? = some (b, c')) → c.off < c.bs.size := by
  intro ⟨b, c', h⟩
  simp only [Cursor.getU8?] at h
  split at h <;> [assumption; simp at h]

/-- All four TxErr constructors are pairwise distinct. -/
theorem txerr_all_distinct :
    TxErr.parse ≠ TxErr.witnessOverflow ∧
    TxErr.parse ≠ TxErr.sigAlgInvalid ∧
    TxErr.parse ≠ TxErr.sigNoncanonical ∧
    TxErr.witnessOverflow ≠ TxErr.sigAlgInvalid ∧
    TxErr.witnessOverflow ≠ TxErr.sigNoncanonical ∧
    TxErr.sigAlgInvalid ≠ TxErr.sigNoncanonical := by
  exact ⟨by simp, by simp, by simp, by simp, by simp, by simp⟩

/-- TxErr.toString maps different error codes to different strings. -/
theorem txerr_toString_injective :
    ∀ e1 e2 : TxErr, e1.toString = e2.toString → e1 = e2 := by
  intro e1 e2
  cases e1 <;> cases e2 <;> simp [TxErr.toString] <;> decide

end Wire
end RubinFormal
