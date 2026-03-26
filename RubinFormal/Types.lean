import Std

namespace RubinFormal

abbrev Bytes := ByteArray

def bytes (xs : Array UInt8) : Bytes := ⟨xs⟩

instance : BEq Bytes where
  beq a b := a.data == b.data

instance : DecidableEq Bytes :=
  fun a b =>
    match (inferInstance : DecidableEq (Array UInt8)) a.data b.data with
    | isTrue h =>
        isTrue (by
          cases a
          cases b
          cases h
          rfl)
    | isFalse h =>
        isFalse (by
          intro hab
          apply h
          cases a
          cases b
          cases hab
          rfl)

instance : Repr Bytes where
  reprPrec _ _ := "<bytes>"

instance : Inhabited Bytes where
  default := ByteArray.empty

/-- Canonical suite ID constants (CANONICAL §2.3 / §5.4).
    Rotation/covenant/validator modules must reuse these definitions instead
    of carrying local copies, so theorem users share one sentinel source. -/
def SUITE_ID_SENTINEL : Nat := 0x00
def SUITE_ID_ML_DSA_87 : Nat := 0x01

end RubinFormal
