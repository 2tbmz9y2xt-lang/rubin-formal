import RubinFormal.Conformance.CVTxctxVectors

namespace RubinFormal.Conformance

private def allDistinctIds (vs : List CVTxctxVector) : Bool :=
  let ids := vs.map (·.id)
  ids.length == ids.eraseDups.length

private def allRejectsHaveErr (vs : List CVTxctxVector) : Bool :=
  vs.all fun v =>
    if v.governanceScope then true
    else if v.expectOk then true
    else match v.expectErr with
      | some e => e.length > 0
      | none => false

private def governanceScopedCount (vs : List CVTxctxVector) : Nat :=
  vs.foldl (fun acc v => if v.governanceScope then acc + 1 else acc) 0

def cvTxctxVectorBundleContract : Bool :=
  cvTxctxVectors.length == 92 &&
  allDistinctIds cvTxctxVectors &&
  allRejectsHaveErr cvTxctxVectors &&
  governanceScopedCount cvTxctxVectors == 2

theorem cv_txctx_vectors_pass : cvTxctxVectorBundleContract = true := by
  native_decide

end RubinFormal.Conformance
