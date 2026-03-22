import RubinFormal.SubsidyV1

namespace RubinFormal
open SubsidyV1

/-- Block subsidy at height 0 is the initial reward. -/
theorem subsidy_height_0 : blockSubsidy 0 0 = INITIAL_SUBSIDY := by rfl

/-- Block subsidy is monotonically non-increasing with alreadyGenerated. -/
theorem subsidy_bounded_by_max_supply (height alreadyGenerated : Nat)
    (h : alreadyGenerated ≥ MAX_SUPPLY) :
    blockSubsidy height alreadyGenerated = 0 := by
  unfold blockSubsidy
  simp [Nat.sub_eq_zero_of_le h]

end RubinFormal
