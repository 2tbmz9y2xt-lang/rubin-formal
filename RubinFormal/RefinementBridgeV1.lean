import RubinFormal.Refinement.GoTraceV1Check

namespace RubinFormal

/-- Narrow machine-checked bridge for the retarget executable path.
    Every `retarget_v1` row in the generated Go trace v1 corpus is rechecked against
    Lean's executable `PowV1.retargetV1` on the matching `CV-POW` fixture id. -/
theorem retarget_v1_go_trace_contract_proved :
    RubinFormal.Refinement.retargetGoTraceV1Pass = true := by
  native_decide

end RubinFormal
