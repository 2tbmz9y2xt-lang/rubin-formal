import Std

namespace RubinFormal

-- CompactSize encoding/decoding (Bitcoin-style) used by the RUBIN wire format.
-- Spec intent: non-minimal encodings MUST be rejected (consensus error TX_ERR_PARSE).

abbrev Byte := UInt8
abbrev Bytes := List Byte

def pow256 (k : Nat) : Nat :=
  256 ^ k

def leBytes (n : Nat) : Nat → Bytes
  | 0 => []
  | (k + 1) => UInt8.ofNat (n % 256) :: leBytes (n / 256) k

def fromLEBytes : Bytes → Nat
  | [] => 0
  | b :: rest => b.toNat + 256 * fromLEBytes rest

theorem fromLEBytes_leBytes (n k : Nat) (h : n < pow256 k) :
    fromLEBytes (leBytes n k) = n := by
  induction k generalizing n with
  | zero =>
      -- pow256 0 = 1, so n < 1 => n = 0
      have hn : n = 0 := by
        have : n < 1 := by simpa [pow256] using h
        exact Nat.eq_zero_of_lt_one this
      simp [leBytes, fromLEBytes, hn]
  | succ k ih =>
      -- n < 256^(k+1) = 256 * 256^k
      have hdiv : n / 256 < pow256 k := by
        -- from n < 256 * pow256 k, conclude n/256 < pow256 k
        have : n < 256 * pow256 k := by
          simpa [pow256, Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
        -- standard division lemma
        exact Nat.div_lt_of_lt_mul this
      -- expand one byte
      simp [leBytes, fromLEBytes]
      -- apply IH to the tail
      have ht : fromLEBytes (leBytes (n / 256) k) = (n / 256) := ih (n := n / 256) hdiv
      -- show reconstruction identity: n = (n % 256) + 256*(n/256)
      have hrecon : n = (n % 256) + 256 * (n / 256) := by
        exact (Nat.mod_add_div n 256).symm
      -- finish
      -- UInt8.ofNat (n % 256) .toNat = n % 256
      have hb : (UInt8.ofNat (n % 256)).toNat = (n % 256) := by
        -- toNat (ofNat x) = x % 256, but here x is already (n % 256)
        simp
      -- combine
      simp [ht, hb, hrecon, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

structure DecodeResult where
  value : Nat
  rest  : Bytes
  deriving Repr

-- Decode CompactSize with canonical (minimal) encoding enforcement.
def decodeCompactSize : Bytes → Option DecodeResult
  | [] => none
  | b0 :: bs =>
      let x0 := b0.toNat
      if x0 < 253 then
        some { value := x0, rest := bs }
      else if x0 = 253 then
        match bs with
        | b1 :: b2 :: rest =>
            let v := fromLEBytes [b1, b2]
            if v < 253 then none else some { value := v, rest := rest }
        | _ => none
      else if x0 = 254 then
        match bs with
        | b1 :: b2 :: b3 :: b4 :: rest =>
            let v := fromLEBytes [b1, b2, b3, b4]
            if v < 65536 then none else some { value := v, rest := rest }
        | _ => none
      else
        -- x0 = 255
        match bs with
        | b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: b8 :: rest =>
            let v := fromLEBytes [b1, b2, b3, b4, b5, b6, b7, b8]
            if v < 4294967296 then none else some { value := v, rest := rest }
        | _ => none

-- Encode CompactSize canonically (minimal form).
def encodeCompactSize (n : Nat) : Option Bytes :=
  if h1 : n < 253 then
    some [UInt8.ofNat n]
  else if h2 : n < 65536 then
    some (UInt8.ofNat 253 :: leBytes n 2)
  else if h3 : n < 4294967296 then
    some (UInt8.ofNat 254 :: leBytes n 4)
  else if h4 : n < (2 ^ 64) then
    some (UInt8.ofNat 255 :: leBytes n 8)
  else
    none

-- T-012 core: decode(encode(n)) round-trip for n < 2^64.
theorem T012_compactsize_roundtrip (n : Nat) (h : n < (2 ^ 64)) :
    ∃ enc : Bytes, encodeCompactSize n = some enc ∧
      decodeCompactSize enc = some { value := n, rest := [] } := by
  unfold encodeCompactSize
  by_cases h1 : n < 253
  · refine ⟨[UInt8.ofNat n], ?_, ?_⟩
    · simp [h1]
    · simp [decodeCompactSize, h1]
  · simp [h1]
    by_cases h2 : n < 65536
    · refine ⟨UInt8.ofNat 253 :: leBytes n 2, ?_, ?_⟩
      · simp [h1, h2]
      · -- decode 0xFD + 2 bytes
        have hn : n < pow256 2 := by
          -- 256^2 = 65536
          simpa [pow256] using h2
        have hle : fromLEBytes (leBytes n 2) = n := fromLEBytes_leBytes n 2 hn
        -- enforce minimality: n >= 253 since not (n<253)
        have hmin : ¬ (n < 253) := h1
        have : 253 ≤ n := Nat.le_of_not_gt hmin
        simp [decodeCompactSize, h1, Nat.lt_of_lt_of_eq (Nat.lt_succ_self _) rfl] at *
        -- We need to open the matching branch explicitly
        simp [decodeCompactSize, h1, hle, this, Nat.lt_of_lt_of_eq]  -- best-effort simp
    · simp [h2]
      by_cases h3 : n < 4294967296
      · refine ⟨UInt8.ofNat 254 :: leBytes n 4, ?_, ?_⟩
        · simp [h1, h2, h3]
        · have hn : n < pow256 4 := by
            -- 256^4 = 2^32 = 4294967296
            simpa [pow256] using h3
          have hle : fromLEBytes (leBytes n 4) = n := fromLEBytes_leBytes n 4 hn
          have : 65536 ≤ n := by exact Nat.le_of_not_gt h2
          -- decode 0xFE + 4 bytes
          simp [decodeCompactSize, h1, h2, hle, this]
      · simp [h3]
        -- final branch requires n < 2^64 (given)
        refine ⟨UInt8.ofNat 255 :: leBytes n 8, ?_, ?_⟩
        · simp [h1, h2, h3, h]
        · have hn : n < pow256 8 := by
            -- 256^8 = 2^64
            simpa [pow256] using h
          have hle : fromLEBytes (leBytes n 8) = n := fromLEBytes_leBytes n 8 hn
          have : 4294967296 ≤ n := by exact Nat.le_of_not_gt h3
          simp [decodeCompactSize, h1, h2, h3, hle, this]

end RubinFormal

