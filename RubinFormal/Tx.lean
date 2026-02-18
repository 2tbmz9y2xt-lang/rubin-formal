-- Spec-structured transaction value model for §4.5 Value conservation.
-- The spec requires exact checked arithmetic (overflow => TX_ERR_PARSE).
-- Here we model outputs/inputs as u64 values with explicit overflow checking.

import RubinFormal.U64

namespace RubinFormal

structure Tx where
  inputValues : List U64
  outputValues : List U64
  isCoinbase : Bool := false
  deriving DecidableEq, Repr

def sumU64? (xs : List U64) : Option U64 :=
  U64.sum? xs

def inValue? (tx : Tx) : Option U64 := sumU64? tx.inputValues
def outValue? (tx : Tx) : Option U64 := sumU64? tx.outputValues

-- Consensus-oriented error surface (subset).
inductive TxErr where
  | TX_ERR_PARSE
  | TX_ERR_VALUE_CONSERVATION
  deriving DecidableEq, Repr

def validateValueConservation (tx : Tx) : Option TxErr :=
  if tx.isCoinbase then
    none
  else
    match inValue? tx, outValue? tx with
    | none, _ => some TxErr.TX_ERR_PARSE
    | _, none => some TxErr.TX_ERR_PARSE
    | some sumIn, some sumOut =>
        if sumOut.val > sumIn.val then
          some TxErr.TX_ERR_VALUE_CONSERVATION
        else
          none

-- T-005 (spec-structured): If validation returns OK (no error),
-- then sum_out <= sum_in and no overflow occurred in summations.
theorem T005_value_conservation_noncoinbase
    (tx : Tx) (hcb : tx.isCoinbase = false)
    (hok : validateValueConservation tx = none) :
    ∃ sumIn sumOut : U64,
      inValue? tx = some sumIn ∧
      outValue? tx = some sumOut ∧
      sumOut.val ≤ sumIn.val := by
  -- unfold and case split on the validator
  simp [validateValueConservation, hcb] at hok
  -- hok now implies the match branches produced `none`
  -- so both sums exist and sumOut.n <= sumIn.n
  cases hin : inValue? tx <;> cases hout : outValue? tx <;> simp [inValue?, outValue?, sumU64?, hin, hout] at hok
  · -- in none
    contradiction
  · -- in none, out some
    contradiction
  · -- in some, out none
    contradiction
  · -- in some, out some
    rename_i sumIn sumOut
    refine ⟨sumIn, sumOut, hin, hout, ?_⟩
    -- from hok: not (sumOut.n > sumIn.n)
    have hnot : ¬ (sumOut.val > sumIn.val) := by
      -- hok is the result of `if sumOut.n > sumIn.n then ... else ...`
      simpa using hok
    exact Nat.le_of_not_gt hnot

end RubinFormal
