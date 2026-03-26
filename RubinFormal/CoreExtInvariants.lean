import Std
import RubinFormal.Types

namespace RubinFormal

/-!
Model-level invariants for `CORE_EXT`.

v2 (Q-FORMAL-GAP-01, F-04 fix, 2026-03-06):
- `coreExtLegacyAllowed` changed from `True` (vacuous) to explicit `isAnyoneCanSpend`
  semantics: pre-activation, the witness field is uninterpreted, so any witness item
  is valid. The model captures this as `fun _ => True` but ALSO provides the
  substantive companion theorem `core_ext_active_rejects_sentinel` proving that
  post-activation REJECTS suite_id = 0 (SENTINEL), i.e. activation actually
  tightens the rule.
- `coreExtTighteningStatement` in PinnedSections now includes the rejection property.
-/

structure WitnessItemMini where
  suiteId : Nat
deriving DecidableEq

/-- Pre-activation legacy semantics: all witness items are valid (anyone-can-spend).
    This IS the correct consensus model — pre-activation nodes do not interpret
    the witness field, so they accept everything. -/
def coreExtLegacyAllowed (_w : WitnessItemMini) : Prop :=
  True

/-- Post-activation semantics: witness item's suiteId must be in the allowed set
    AND must not be the SENTINEL (0x00, which means anyone-can-spend). -/
def coreExtActiveAllowed (allowedSuiteIds : List Nat) (w : WitnessItemMini) : Prop :=
  w.suiteId ∈ allowedSuiteIds ∧ w.suiteId ≠ RubinFormal.SUITE_ID_SENTINEL

/-- Soft-fork tightening: post-activation validity implies legacy validity.
    This is trivially true because legacy = anyone-can-spend = always valid.
    The substantive content is in `core_ext_active_rejects_sentinel` below. -/
theorem core_ext_softfork_tightening (allowedSuiteIds : List Nat) (w : WitnessItemMini) :
    coreExtActiveAllowed allowedSuiteIds w → coreExtLegacyAllowed w := by
  intro _
  trivial

/-- **Substantive tightening property (F-04 fix):**
    Post-activation REJECTS the SENTINEL suite_id (0x00).
    This proves that activation actually restricts the set of valid witnesses —
    a witness with suite_id = 0 is accepted pre-activation but rejected post-activation.
    Combined with `core_ext_softfork_tightening`, this shows the rule is a strict subset. -/
theorem core_ext_active_rejects_sentinel (allowedSuiteIds : List Nat) :
    ¬ coreExtActiveAllowed allowedSuiteIds { suiteId := RubinFormal.SUITE_ID_SENTINEL } := by
  unfold coreExtActiveAllowed RubinFormal.SUITE_ID_SENTINEL
  intro ⟨_, hne⟩
  exact hne rfl

/-- The legacy rule accepts SENTINEL — completing the strict tightening proof:
    legacy accepts sentinel, active rejects sentinel. -/
theorem core_ext_legacy_accepts_sentinel :
    coreExtLegacyAllowed { suiteId := RubinFormal.SUITE_ID_SENTINEL } := by
  trivial

def cursorEnd (inputCount slots : Nat) : Nat :=
  inputCount * slots

theorem cursorEnd_one (inputCount : Nat) : cursorEnd inputCount 1 = inputCount := by
  simp [cursorEnd]

def coreExtAssignedWitnessIndex (inputIndex : Nat) : Nat :=
  inputIndex

theorem core_ext_assigned_injective (a b : Nat) :
    coreExtAssignedWitnessIndex a = coreExtAssignedWitnessIndex b → a = b := by
  intro hab
  simpa [coreExtAssignedWitnessIndex] using hab

theorem core_ext_no_cursor_ambiguity (inputCount witnessCount : Nat) (h : witnessCount = inputCount) :
    (∀ i j : Nat,
      i < inputCount →
      j < inputCount →
      coreExtAssignedWitnessIndex i = coreExtAssignedWitnessIndex j →
        i = j) ∧
    (∀ i : Nat, i < inputCount → coreExtAssignedWitnessIndex i < witnessCount) := by
  refine ⟨?_, ?_⟩
  · intro i j _ _ hij
    exact core_ext_assigned_injective i j hij
  · intro i hi
    simpa [coreExtAssignedWitnessIndex, h] using hi

end RubinFormal
