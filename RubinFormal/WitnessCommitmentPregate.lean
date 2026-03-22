import RubinFormal.BlockValidationOrder
namespace RubinFormal
open BlockBasicV1

/-- Witness commitment check is reached only after parse+PoW+target+linkage+merkle
    all pass. This is the pre-gate chain. -/
theorem witness_commitment_requires_parse_pow
    (blockBytes : Bytes) (ph pt : Option Bytes)
    (hOk : validateBlockBasic blockBytes ph pt = .ok ()) :
    ∃ pb, parseBlock blockBytes = .ok pb ∧ powCheck pb.header = .ok () :=
  validate_success_pow blockBytes ph pt hOk

end RubinFormal
