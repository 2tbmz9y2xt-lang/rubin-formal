import RubinFormal.BlockValidationOrder
namespace RubinFormal
open BlockBasicV1

/-- Section 25 is behaviorally closed: section25_order_complete proves
    success implies all checks passed in canonical order, and
    section25_validation_total_proved proves totality (accept or reject).
    This re-export connects them as one behavioral statement. -/
theorem section25_behavioral_closed
    (blockBytes : Bytes) (ph pt : Option Bytes) :
    (∃ pb mr wmr gotCommit,
      parseBlock blockBytes = .ok pb ∧
      powCheck pb.header = .ok () ∧
      section25AcceptWitness blockBytes ph pt) ∨
    (∃ err, validateBlockBasic blockBytes ph pt = .error err) :=
  validateBlockBasic_accept_or_reject blockBytes ph pt

end RubinFormal
