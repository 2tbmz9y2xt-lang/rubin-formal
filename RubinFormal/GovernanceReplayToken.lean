/-
  GovernanceReplayToken.lean — governance replay-token contract proofs (#297)
  Models the live GovernanceReplayToken from core_ext.rs and proves:
  - Validation semantics (5 outcomes, canonical check order)
  - Size invariant (always 26 bytes)
  - Overflow saturation (expiry_height never wraps)
  - Field bounds match Rust u16/u64 wire types
-/
import RubinFormal.Types
import RubinFormal.OutputDescriptorV2
import Std.Tactic.Omega
import Std.Data.UInt

namespace RubinFormal

open WireEnc

set_option maxHeartbeats 4000000

-- ═══════════════════════════════════════════════════════════════════
-- §1  Structure and wire format (bounded fields)
-- ═══════════════════════════════════════════════════════════════════

/-- GovernanceReplayToken binds a profile authorization to a specific
    height window, preventing replay of governance actions across
    activation/deactivation cycles.
    Fields carry intrinsic bounds matching Rust's u16/u64 wire types,
    so the model cannot represent states unreachable in the live impl. -/
structure GovernanceReplayToken where
  ext_id : Nat
  nonce : Nat
  issued_at_height : Nat
  validity_window : Nat
  h_ext_id : ext_id < 65536
  h_nonce : nonce < UInt64.size
  h_iat : issued_at_height < UInt64.size
  h_vw : validity_window < UInt64.size

def GOVERNANCE_REPLAY_TOKEN_BYTES : Nat := 26

/-- Saturating add for u64 range.  Mirrors Rust's `u64::saturating_add`. -/
def saturatingAdd64 (a b : Nat) : Nat :=
  min (a + b) (UInt64.size - 1)

/-- Expiry height with saturation (never wraps past u64::MAX). -/
def GovernanceReplayToken.expiryHeight (t : GovernanceReplayToken) : Nat :=
  saturatingAdd64 t.issued_at_height t.validity_window

/-- Serialize token to 26 deterministic bytes:
    u16le(ext_id) ++ u64le(nonce) ++ u64le(issued_at_height) ++ u64le(validity_window).
    Defined as List literal inside Array.mk (not #[] push-chain) so that
    ByteArray.size/get! reduce in O(n) kernel steps, not O(n²). -/
def GovernanceReplayToken.toBytes (t : GovernanceReplayToken) : Bytes :=
  ⟨⟨[UInt8.ofNat t.ext_id, UInt8.ofNat (t.ext_id / 256),
     UInt8.ofNat t.nonce, UInt8.ofNat (t.nonce / 256),
     UInt8.ofNat (t.nonce / 65536), UInt8.ofNat (t.nonce / 16777216),
     UInt8.ofNat (t.nonce / 4294967296), UInt8.ofNat (t.nonce / 1099511627776),
     UInt8.ofNat (t.nonce / 281474976710656), UInt8.ofNat (t.nonce / 72057594037927936),
     UInt8.ofNat t.issued_at_height, UInt8.ofNat (t.issued_at_height / 256),
     UInt8.ofNat (t.issued_at_height / 65536), UInt8.ofNat (t.issued_at_height / 16777216),
     UInt8.ofNat (t.issued_at_height / 4294967296), UInt8.ofNat (t.issued_at_height / 1099511627776),
     UInt8.ofNat (t.issued_at_height / 281474976710656), UInt8.ofNat (t.issued_at_height / 72057594037927936),
     UInt8.ofNat t.validity_window, UInt8.ofNat (t.validity_window / 256),
     UInt8.ofNat (t.validity_window / 65536), UInt8.ofNat (t.validity_window / 16777216),
     UInt8.ofNat (t.validity_window / 4294967296), UInt8.ofNat (t.validity_window / 1099511627776),
     UInt8.ofNat (t.validity_window / 281474976710656), UInt8.ofNat (t.validity_window / 72057594037927936)]⟩⟩

-- Helper: every UInt8 has toNat ≤ 255.
-- Use b.val.isLt with explicit type ascription to avoid opaque UInt8.size.
private theorem byte_le (b : UInt8) : b.toNat ≤ 255 := by
  have h : b.toNat < 256 := b.val.isLt
  omega

-- Helper: u32-range LE value from 4 bytes is bounded
private theorem u32_from_bytes_bound (b0 b1 b2 b3 : UInt8) :
    b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 < 4294967296 := by
  have h0 := byte_le b0
  have h1 : b1.toNat * 256 ≤ 255 * 256 := Nat.mul_le_mul_right 256 (byte_le b1)
  have h2 : b2.toNat * 65536 ≤ 255 * 65536 := Nat.mul_le_mul_right 65536 (byte_le b2)
  have h3 : b3.toNat * 16777216 ≤ 255 * 16777216 := Nat.mul_le_mul_right 16777216 (byte_le b3)
  omega

-- Helper: lo < 2^32 ∧ hi < 2^32 → lo + hi * 2^32 < 2^64
private theorem combine_u32_to_u64 (lo hi : Nat) (hlo : lo < 4294967296) (hhi : hi < 4294967296) :
    lo + hi * 4294967296 < 18446744073709551616 := by
  have : hi * 4294967296 ≤ 4294967295 * 4294967296 := Nat.mul_le_mul_right 4294967296 (by omega)
  omega

-- Helper: reconstruction of u64 from 8 bytes is bounded.
-- Strategy: split into lo(4 bytes) + hi(4 bytes) * 2^32, bound each half < 2^32.
private theorem u64_from_bytes_bound (b0 b1 b2 b3 b4 b5 b6 b7 : UInt8) :
    b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 +
    b4.toNat * 4294967296 + b5.toNat * 1099511627776 +
    b6.toNat * 281474976710656 + b7.toNat * 72057594037927936 < UInt64.size := by
  -- Algebraic identity: the flat sum equals lo + hi * 2^32
  have key : b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216 +
      b4.toNat * 4294967296 + b5.toNat * 1099511627776 +
      b6.toNat * 281474976710656 + b7.toNat * 72057594037927936 =
      (b0.toNat + b1.toNat * 256 + b2.toNat * 65536 + b3.toNat * 16777216) +
      (b4.toNat + b5.toNat * 256 + b6.toNat * 65536 + b7.toNat * 16777216) * 4294967296 := by
    omega
  rw [key]; simp only [UInt64.size]
  exact combine_u32_to_u64 _ _ (u32_from_bytes_bound b0 b1 b2 b3) (u32_from_bytes_bound b4 b5 b6 b7)

-- Helper: reconstruction of u16 from 2 bytes is bounded
private theorem u16_from_bytes_bound (b0 b1 : UInt8) :
    b0.toNat + b1.toNat * 256 < 65536 := by
  have h0 := byte_le b0
  have h1 : b1.toNat * 256 ≤ 255 * 256 := Nat.mul_le_mul_right 256 (byte_le b1)
  omega

/-- Deserialize a token from 26 bytes. Returns none on wrong length.
    Reconstructed fields are intrinsically bounded by UInt8 range. -/
def GovernanceReplayToken.fromBytes (data : Bytes) : Option GovernanceReplayToken :=
  if data.size ≠ GOVERNANCE_REPLAY_TOKEN_BYTES then none
  else
    some {
      ext_id := (data.get! 0).toNat + (data.get! 1).toNat * 256
      nonce :=
        (data.get! 2).toNat + (data.get! 3).toNat * 256 +
        (data.get! 4).toNat * 65536 + (data.get! 5).toNat * 16777216 +
        (data.get! 6).toNat * 4294967296 + (data.get! 7).toNat * 1099511627776 +
        (data.get! 8).toNat * 281474976710656 + (data.get! 9).toNat * 72057594037927936
      issued_at_height :=
        (data.get! 10).toNat + (data.get! 11).toNat * 256 +
        (data.get! 12).toNat * 65536 + (data.get! 13).toNat * 16777216 +
        (data.get! 14).toNat * 4294967296 + (data.get! 15).toNat * 1099511627776 +
        (data.get! 16).toNat * 281474976710656 + (data.get! 17).toNat * 72057594037927936
      validity_window :=
        (data.get! 18).toNat + (data.get! 19).toNat * 256 +
        (data.get! 20).toNat * 65536 + (data.get! 21).toNat * 16777216 +
        (data.get! 22).toNat * 4294967296 + (data.get! 23).toNat * 1099511627776 +
        (data.get! 24).toNat * 281474976710656 + (data.get! 25).toNat * 72057594037927936
      h_ext_id := u16_from_bytes_bound (data.get! 0) (data.get! 1)
      h_nonce := u64_from_bytes_bound (data.get! 2) (data.get! 3) (data.get! 4) (data.get! 5)
                                       (data.get! 6) (data.get! 7) (data.get! 8) (data.get! 9)
      h_iat := u64_from_bytes_bound (data.get! 10) (data.get! 11) (data.get! 12) (data.get! 13)
                                     (data.get! 14) (data.get! 15) (data.get! 16) (data.get! 17)
      h_vw := u64_from_bytes_bound (data.get! 18) (data.get! 19) (data.get! 20) (data.get! 21)
                                    (data.get! 22) (data.get! 23) (data.get! 24) (data.get! 25)
    }

-- ═══════════════════════════════════════════════════════════════════
-- §2  Validation semantics (canonical check order from Rust)
-- ═══════════════════════════════════════════════════════════════════

inductive GovernanceValidation where
  | valid
  | extIdMismatch
  | nonceMismatch
  | notYetValid
  | expired
  deriving DecidableEq, Repr

/-- Canonical validation check order: ext_id → nonce → issued_at → expiry.
    Matches Rust impl `validation_outcome` exactly. -/
def GovernanceReplayToken.validate
    (t : GovernanceReplayToken)
    (expected_ext_id : Nat) (current_height : Nat) (expected_nonce : Nat)
    : GovernanceValidation :=
  if t.ext_id ≠ expected_ext_id then .extIdMismatch
  else if t.nonce ≠ expected_nonce then .nonceMismatch
  else if current_height < t.issued_at_height then .notYetValid
  else if current_height ≥ t.expiryHeight then .expired
  else .valid

-- ═══════════════════════════════════════════════════════════════════
-- §3  ByteArray ↔ Array bridge lemmas
-- ═══════════════════════════════════════════════════════════════════

/-- Bridge: ByteArray.mk size = Array size.  Sidesteps @[extern] on ByteArray.size. -/
@[simp] private theorem ba_size_eq (a : Array UInt8) :
    (ByteArray.mk a).size = a.size := rfl

/-- Bridge: ByteArray.mk get! = Array get!.  Sidesteps @[extern] on ByteArray.get!. -/
@[simp] private theorem ba_get!_eq (a : Array UInt8) (i : Nat) :
    (ByteArray.mk a).get! i = a.get! i := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §4  Wire size invariant
-- ═══════════════════════════════════════════════════════════════════

/-- toBytes always produces exactly 26 bytes. -/
theorem GovernanceReplayToken.toBytes_size (t : GovernanceReplayToken) :
    t.toBytes.size = GOVERNANCE_REPLAY_TOKEN_BYTES := by
  cases t; rfl

-- ═══════════════════════════════════════════════════════════════════
-- §5  Validation semantics — each outcome
-- ═══════════════════════════════════════════════════════════════════

/-- ext_id mismatch is the first check. -/
theorem validate_ext_id_mismatch (t : GovernanceReplayToken)
    (eid : Nat) (h : Nat) (n : Nat) (hne : t.ext_id ≠ eid) :
    t.validate eid h n = .extIdMismatch := by
  simp [GovernanceReplayToken.validate, hne]

/-- nonce mismatch is the second check (ext_id matches). -/
theorem validate_nonce_mismatch (t : GovernanceReplayToken)
    (eid : Nat) (h : Nat) (n : Nat)
    (he : t.ext_id = eid) (hn : t.nonce ≠ n) :
    t.validate eid h n = .nonceMismatch := by
  simp [GovernanceReplayToken.validate, he, hn]

/-- not yet valid when height < issued_at (ext_id and nonce match). -/
theorem validate_not_yet_valid (t : GovernanceReplayToken)
    (eid : Nat) (h : Nat) (n : Nat)
    (he : t.ext_id = eid) (hn : t.nonce = n) (hlt : h < t.issued_at_height) :
    t.validate eid h n = .notYetValid := by
  simp [GovernanceReplayToken.validate, he, hn, hlt]

/-- expired when height ≥ expiryHeight (all prior checks pass). -/
theorem validate_expired (t : GovernanceReplayToken)
    (eid : Nat) (h : Nat) (n : Nat)
    (he : t.ext_id = eid) (hn : t.nonce = n)
    (hge : h ≥ t.issued_at_height) (hexp : h ≥ t.expiryHeight) :
    t.validate eid h n = .expired := by
  have hNotLt : ¬(h < t.issued_at_height) := by omega
  simp [GovernanceReplayToken.validate, he, hn, hNotLt, hexp]

/-- valid when height is in [issued_at, expiry). -/
theorem validate_valid (t : GovernanceReplayToken)
    (eid : Nat) (h : Nat) (n : Nat)
    (he : t.ext_id = eid) (hn : t.nonce = n)
    (hge : h ≥ t.issued_at_height) (hlt : h < t.expiryHeight) :
    t.validate eid h n = .valid := by
  have hNotLt : ¬(h < t.issued_at_height) := by omega
  have hNotExp : ¬(h ≥ t.expiryHeight) := by omega
  simp [GovernanceReplayToken.validate, he, hn, hNotLt, hNotExp]

-- ═══════════════════════════════════════════════════════════════════
-- §6  Saturation safety
-- ═══════════════════════════════════════════════════════════════════

/-- saturatingAdd64 never exceeds u64::MAX. -/
theorem saturatingAdd64_le_max (a b : Nat) :
    saturatingAdd64 a b ≤ UInt64.size - 1 := by
  simp [saturatingAdd64]
  omega

/-- expiryHeight never exceeds u64::MAX. -/
theorem GovernanceReplayToken.expiryHeight_le_max (t : GovernanceReplayToken) :
    t.expiryHeight ≤ UInt64.size - 1 :=
  saturatingAdd64_le_max t.issued_at_height t.validity_window

-- ═══════════════════════════════════════════════════════════════════
-- §7  fromBytes rejects wrong length
-- ═══════════════════════════════════════════════════════════════════

/-- fromBytes returns none on any input not exactly 26 bytes. -/
theorem GovernanceReplayToken.fromBytes_wrong_len (data : Bytes)
    (h : data.size ≠ GOVERNANCE_REPLAY_TOKEN_BYTES) :
    GovernanceReplayToken.fromBytes data = none := by
  simp [GovernanceReplayToken.fromBytes, h]

-- ═══════════════════════════════════════════════════════════════════
-- §8  Validation completeness + helpers
-- ═══════════════════════════════════════════════════════════════════

/-- validate always returns one of the five outcomes (exhaustiveness). -/
theorem validate_exhaustive (t : GovernanceReplayToken)
    (eid : Nat) (h : Nat) (n : Nat) :
    t.validate eid h n = .valid ∨
    t.validate eid h n = .extIdMismatch ∨
    t.validate eid h n = .nonceMismatch ∨
    t.validate eid h n = .notYetValid ∨
    t.validate eid h n = .expired := by
  simp only [GovernanceReplayToken.validate]
  split
  · right; left; rfl
  · split
    · right; right; left; rfl
    · split
      · right; right; right; left; rfl
      · split
        · right; right; right; right; rfl
        · left; rfl

/-- u16 LE byte-level reconstruction roundtrip. -/
theorem u16_le_byte_roundtrip (n : Nat) (h : n < 65536) :
    n % 256 + (n / 256 % 256) * 256 = n := by omega

/-- UInt8.ofNat roundtrip: (UInt8.ofNat x).toNat = x % 256. -/
theorem uint8_ofNat_toNat (x : Nat) : (UInt8.ofNat x).toNat = x % 256 := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §9  Wire roundtrip: toBytes → fromBytes = identity
-- ═══════════════════════════════════════════════════════════════════

/-- (a % 256) % 256 = a % 256 — collapses the double mod from UInt8.ofNat/toNat. -/
private theorem mod_mod_256 (a : Nat) : a % 256 % 256 = a % 256 :=
  Nat.mod_eq_of_lt (Nat.mod_lt a (by omega))

/-- u32 LE byte-level reconstruction roundtrip.
    Proof via iterated Nat.div_add_mod — omega can't handle raw div/mod at this scale. -/
private theorem u32_le_byte_roundtrip (n : Nat) (h : n < 4294967296) :
    (n % 256) + (n / 256 % 256) * 256 + (n / 65536 % 256) * 65536 +
    (n / 16777216 % 256) * 16777216 = n := by
  have h1 := Nat.div_add_mod n 256
  have h2 := Nat.div_add_mod (n / 256) 256
  have h3 := Nat.div_add_mod (n / 65536) 256
  have hd1 : n / 256 / 256 = n / 65536 := Nat.div_div_eq_div_mul n 256 256
  have hd2 : n / 65536 / 256 = n / 16777216 := Nat.div_div_eq_div_mul n 65536 256
  have h4 : n / 16777216 < 256 := by omega
  have h5 : n / 16777216 % 256 = n / 16777216 := Nat.mod_eq_of_lt h4
  omega

/-- u64 LE byte-level reconstruction roundtrip. -/
private theorem u64_le_byte_roundtrip (n : Nat) (h : n < UInt64.size) :
    (n % 256) + (n / 256 % 256) * 256 + (n / 65536 % 256) * 65536 +
    (n / 16777216 % 256) * 16777216 + (n / 4294967296 % 256) * 4294967296 +
    (n / 1099511627776 % 256) * 1099511627776 +
    (n / 281474976710656 % 256) * 281474976710656 +
    (n / 72057594037927936 % 256) * 72057594037927936 = n := by
  simp only [UInt64.size] at h
  have h1 := Nat.div_add_mod n 256
  have h2 := Nat.div_add_mod (n / 256) 256
  have h3 := Nat.div_add_mod (n / 65536) 256
  have h4 := Nat.div_add_mod (n / 16777216) 256
  have h5 := Nat.div_add_mod (n / 4294967296) 256
  have h6 := Nat.div_add_mod (n / 1099511627776) 256
  have h7 := Nat.div_add_mod (n / 281474976710656) 256
  have hd1 : n / 256 / 256 = n / 65536 := Nat.div_div_eq_div_mul n 256 256
  have hd2 : n / 65536 / 256 = n / 16777216 := Nat.div_div_eq_div_mul n 65536 256
  have hd3 : n / 16777216 / 256 = n / 4294967296 := Nat.div_div_eq_div_mul n 16777216 256
  have hd4 : n / 4294967296 / 256 = n / 1099511627776 := Nat.div_div_eq_div_mul n 4294967296 256
  have hd5 : n / 1099511627776 / 256 = n / 281474976710656 := Nat.div_div_eq_div_mul n 1099511627776 256
  have hd6 : n / 281474976710656 / 256 = n / 72057594037927936 := Nat.div_div_eq_div_mul n 281474976710656 256
  have h8 : n / 72057594037927936 < 256 := by omega
  have h9 : n / 72057594037927936 % 256 = n / 72057594037927936 := Nat.mod_eq_of_lt h8
  omega

/-- Wire roundtrip: fromBytes (toBytes t) = some t. -/
theorem GovernanceReplayToken.wire_roundtrip (t : GovernanceReplayToken) :
    GovernanceReplayToken.fromBytes (GovernanceReplayToken.toBytes t) = some t := by
  cases t with
  | mk eid n iat vw he hn hi hv =>
    -- Phase 1: eliminate the if-branch via toBytes_size
    have hsz : ¬((GovernanceReplayToken.toBytes ⟨eid, n, iat, vw, he, hn, hi, hv⟩).size ≠
                  GOVERNANCE_REPLAY_TOKEN_BYTES) := by
      simp [GovernanceReplayToken.toBytes_size]
    unfold GovernanceReplayToken.fromBytes
    rw [if_neg hsz]
    -- Phase 2: reduce each get! to concrete UInt8, then apply byte roundtrips
    simp only [GovernanceReplayToken.toBytes,
               ba_get!_eq,
               Array.get!_eq_get?, Array.get?_eq_data_get?,
               List.get?_cons_zero, List.get?_cons_succ,
               Option.getD_some,
               uint8_ofNat_toNat, mod_mod_256,
               u16_le_byte_roundtrip eid he,
               u64_le_byte_roundtrip n hn,
               u64_le_byte_roundtrip iat hi,
               u64_le_byte_roundtrip vw hv]

end RubinFormal
