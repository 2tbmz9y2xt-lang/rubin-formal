import Std

namespace RubinFormal

abbrev Byte := UInt8
abbrev Bytes := List Byte

-- Cryptographic primitives are modeled axiomatically.
-- We only need determinism and fixed output length for consensus-level reasoning.

axiom SHA3_256 : Bytes → Bytes
axiom SHA3_256_len32 : ∀ bs : Bytes, (SHA3_256 bs).length = 32

-- Strong form used for key_id uniqueness statements in the spec:
-- collision resistance / injectivity (modeled as an axiom).
axiom SHA3_256_injective : ∀ x y : Bytes, SHA3_256 x = SHA3_256 y → x = y

end RubinFormal
