-- CV-EXT conformance replay: verify vector expectations are self-consistent.
-- Full mechanized replay (parse + verify) requires CV-EXT ops in Lean model.
-- These theorems verify structural properties of the vector set.

import RubinFormal.Conformance.CVExtVectors

namespace RubinFormal.Conformance

private def allDistinctIds (vs : List CVExtVector) : Bool :=
  let ids := vs.map (·.id)
  ids.length == ids.eraseDups.length

private def allRejectsHaveErr (vs : List CVExtVector) : Bool :=
  vs.all fun v =>
    if v.expectOk then true
    else match v.expectErr with
      | some e => e.length > 0
      | none => false

private def hasFamilies (vs : List CVExtVector) (families : List String) : Bool :=
  families.all fun fam => vs.any fun v => v.id.startsWith ("CV-EXT-" ++ fam)

def cvExtVectorBundleContract : Bool :=
  cvExtVectors.length == 25 &&
  allDistinctIds cvExtVectors &&
  allRejectsHaveErr cvExtVectors &&
  hasFamilies cvExtVectors ["ENV", "ACT", "PRE", "ENF", "PAY", "ERR", "DUP", "GEN", "PAR"]

theorem cv_ext_vectors_pass : cvExtVectorBundleContract = true := by
  native_decide

end RubinFormal.Conformance
