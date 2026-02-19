import RubinFormal.Tx

namespace RubinFormal

/-!
## HTLC_V2 Value Preservation Corollaries

Thin corollaries over `Tx.T005_value_conservation_noncoinbase` confirming that
value conservation holds on any valid non-coinbase transaction, independent of
whether the spend path is claim or refund.  Both theorems share the same proof
because value conservation is a transaction-level invariant that does not depend
on which covenant path was taken.
-/

/-- On a successful non-coinbase transaction taking the HTLC_V2 **claim** path,
    the sum of spendable output values does not exceed the sum of input values. -/
theorem value_preservation_claim
    (tx : Tx.Tx)
    (hcb : tx.isCoinbase = false)
    (hok : Tx.validateValueConservation tx = none) :
    ∃ sumIn sumOut : U64,
      Tx.inValue? tx = some sumIn ∧
      Tx.outValue? tx = some sumOut ∧
      sumOut.val ≤ sumIn.val :=
  Tx.T005_value_conservation_noncoinbase tx hcb hok

/-- On a successful non-coinbase transaction taking the HTLC_V2 **refund** path,
    the sum of spendable output values does not exceed the sum of input values. -/
theorem value_preservation_refund
    (tx : Tx.Tx)
    (hcb : tx.isCoinbase = false)
    (hok : Tx.validateValueConservation tx = none) :
    ∃ sumIn sumOut : U64,
      Tx.inValue? tx = some sumIn ∧
      Tx.outValue? tx = some sumOut ∧
      sumOut.val ≤ sumIn.val :=
  Tx.T005_value_conservation_noncoinbase tx hcb hok

end RubinFormal
