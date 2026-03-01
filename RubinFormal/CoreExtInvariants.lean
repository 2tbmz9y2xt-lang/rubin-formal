import Std

namespace RubinFormal

/-!
Model-level invariants for `CORE_EXT`.

These are not full mechanized proofs of CANONICAL semantics. They capture the two
consensus-safety properties required by `Q-SF-EXT-06`:

1) Soft-fork tightening shape: post-activation validity implies legacy validity
   under an "anyone-can-spend" legacy interpretation.
2) No cursor ambiguity when `witness_slots` is fixed (for `CORE_EXT`, slots = 1):
   witness assignment is deterministic and non-overlapping.
-/

structure WitnessItemMini where
  suiteId : Nat
deriving DecidableEq

def coreExtLegacyAllowed (_w : WitnessItemMini) : Prop :=
  True

def coreExtActiveAllowed (allowedSuiteIds : List Nat) (w : WitnessItemMini) : Prop :=
  w.suiteId ∈ allowedSuiteIds ∧ w.suiteId ≠ 0

theorem core_ext_softfork_tightening (allowedSuiteIds : List Nat) (w : WitnessItemMini) :
    coreExtActiveAllowed allowedSuiteIds w → coreExtLegacyAllowed w := by
  intro _
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
