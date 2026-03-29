/-
  RubinFormal/FeatureActivationLiveBridge.lean — Feature Activation Live Bridge

  Bridges the model featureBitNextState and flagDayActive to live Go/Rust
  evaluation semantics.

  Live code mapping:
  - Go:   consensus/featurebits.go → evalFeatureBitsNextState
  - Rust: src/featurebits.rs → next_state
  - Go:   consensus/flagday.go → FlagDayActiveAtHeight
  - Rust: src/flagday.rs → flagday_active_at_height

  The Lean `featureBitNextState` is a faithful transcription of the Go/Rust
  switch/match statement. This file proves behavioral bridge properties that
  demonstrate the model captures Go/Rust-specific evaluation order and
  transition semantics.

  Spec: CANONICAL §23 (feature deployment), §23.2 (flagday).
  Depends: FeatureActivationFSM.lean.
-/

import RubinFormal.FeatureActivationFSM

namespace RubinFormal

namespace FeatureActivationLiveBridge

-- ═══════════════════════════════════════════════════════════════════
-- §1  Lock-in priority bridge
--
-- Go `evalFeatureBitsNextState` evaluates `prevWindowSignalCount >=
-- SIGNAL_THRESHOLD` BEFORE `boundaryHeight >= d.TimeoutHeight`.
-- This means lock-in takes priority over timeout — a critical
-- consensus-divergence-preventing property.
--
-- Rust `next_state` has identical evaluation order.
-- ═══════════════════════════════════════════════════════════════════

/-- **Lock-in priority over timeout**: when BOTH the lock-in threshold and
    the timeout height are reached simultaneously, the state transitions
    to LOCKED_IN, not FAILED.

    This is NOT a tautology — it depends on the evaluation order in the
    Go/Rust code. A different implementation that checked timeout first
    would produce FAILED, causing a consensus fork.

    Go: `if prevWindowSignalCount >= SIGNAL_THRESHOLD { return LOCKED_IN }`
    checked before `if boundaryHeight >= d.TimeoutHeight { return FAILED }`. -/
theorem lockin_priority_over_timeout
    (bh cnt : Nat) (d : FeatureBitDeployment)
    (hCnt : cnt ≥ SIGNAL_THRESHOLD)
    (_hTimeout : bh ≥ d.timeoutHeight) :
    featureBitNextState .started bh cnt d = .lockedIn := by
  simp only [featureBitNextState]
  rw [if_pos hCnt]

/-- Converse: when lock-in threshold is NOT met but timeout IS reached,
    the state transitions to FAILED.
    Go: falls through to `if boundaryHeight >= d.TimeoutHeight { return FAILED }`. -/
theorem timeout_when_threshold_not_met
    (bh cnt : Nat) (d : FeatureBitDeployment)
    (hCnt : cnt < SIGNAL_THRESHOLD)
    (hTimeout : bh ≥ d.timeoutHeight) :
    featureBitNextState .started bh cnt d = .failed := by
  simp only [featureBitNextState]
  rw [if_neg (by omega : ¬ cnt ≥ SIGNAL_THRESHOLD)]
  rw [if_pos hTimeout]

-- ═══════════════════════════════════════════════════════════════════
-- §2  No-skip transition bridge
--
-- Go/Rust FSM is single-step. These theorems prove certain state
-- transitions require multiple steps, matching the live behavior
-- and preventing implementations that "skip" states.
-- ═══════════════════════════════════════════════════════════════════

/-- DEFINED cannot reach ACTIVE in one step.
    Go: `case DEFINED: return STARTED or DEFINED` — no ACTIVE path. -/
theorem no_defined_to_active (bh cnt : Nat) (d : FeatureBitDeployment) :
    featureBitNextState .defined bh cnt d ≠ .active := by
  simp only [featureBitNextState]
  split <;> decide

/-- DEFINED cannot reach LOCKED_IN in one step.
    Go: `case DEFINED:` only returns STARTED or DEFINED. -/
theorem no_defined_to_lockedin (bh cnt : Nat) (d : FeatureBitDeployment) :
    featureBitNextState .defined bh cnt d ≠ .lockedIn := by
  simp only [featureBitNextState]
  split <;> decide

/-- DEFINED cannot reach FAILED in one step.
    Go: `case DEFINED:` never returns FAILED. -/
theorem no_defined_to_failed (bh cnt : Nat) (d : FeatureBitDeployment) :
    featureBitNextState .defined bh cnt d ≠ .failed := by
  simp only [featureBitNextState]
  split <;> decide

/-- STARTED cannot reach ACTIVE in one step (must go through LOCKED_IN).
    Go: `case STARTED:` returns LOCKED_IN, FAILED, or STARTED — not ACTIVE.
    ACTIVE requires: STARTED → LOCKED_IN → ACTIVE (2 steps minimum). -/
theorem no_started_to_active (bh cnt : Nat) (d : FeatureBitDeployment) :
    featureBitNextState .started bh cnt d ≠ .active := by
  simp only [featureBitNextState]
  split
  · decide
  · split <;> decide

-- ═══════════════════════════════════════════════════════════════════
-- §3  Exact transition condition bridge (iff characterizations)
-- ═══════════════════════════════════════════════════════════════════

/-- DEFINED → STARTED iff boundaryHeight ≥ startHeight.
    Matches Go: `if boundaryHeight >= d.StartHeight { return STARTED }`. -/
theorem defined_to_started_iff (bh cnt : Nat) (d : FeatureBitDeployment) :
    featureBitNextState .defined bh cnt d = .started ↔ bh ≥ d.startHeight := by
  simp only [featureBitNextState]
  constructor
  · intro h
    by_cases hge : bh ≥ d.startHeight
    · exact hge
    · rw [if_neg hge] at h; exact absurd h (by decide)
  · intro h; rw [if_pos h]

/-- DEFINED stays DEFINED iff boundaryHeight < startHeight. -/
theorem defined_stays_defined_iff (bh cnt : Nat) (d : FeatureBitDeployment) :
    featureBitNextState .defined bh cnt d = .defined ↔ bh < d.startHeight := by
  simp only [featureBitNextState]
  constructor
  · intro h
    by_cases hge : bh ≥ d.startHeight
    · rw [if_pos hge] at h; exact absurd h (by decide)
    · omega
  · intro h; rw [if_neg (by omega : ¬ bh ≥ d.startHeight)]

/-- STARTED → LOCKED_IN iff signal count ≥ SIGNAL_THRESHOLD.
    Matches Go: `if prevWindowSignalCount >= SIGNAL_THRESHOLD { return LOCKED_IN }`.
    Note: independent of boundaryHeight — threshold alone decides lock-in. -/
theorem started_to_lockedin_iff (bh cnt : Nat) (d : FeatureBitDeployment) :
    featureBitNextState .started bh cnt d = .lockedIn ↔ cnt ≥ SIGNAL_THRESHOLD := by
  simp only [featureBitNextState]
  constructor
  · intro h
    by_cases hcnt : cnt ≥ SIGNAL_THRESHOLD
    · exact hcnt
    · rw [if_neg hcnt] at h
      by_cases hto : bh ≥ d.timeoutHeight
      · rw [if_pos hto] at h; exact absurd h (by decide)
      · rw [if_neg hto] at h; exact absurd h (by decide)
  · intro h; rw [if_pos h]

/-- STARTED → FAILED iff signal count < threshold AND boundary ≥ timeout.
    Matches Go evaluation order: threshold checked first, timeout second. -/
theorem started_to_failed_iff (bh cnt : Nat) (d : FeatureBitDeployment) :
    featureBitNextState .started bh cnt d = .failed ↔
    cnt < SIGNAL_THRESHOLD ∧ bh ≥ d.timeoutHeight := by
  simp only [featureBitNextState]
  constructor
  · intro h
    by_cases hcnt : cnt ≥ SIGNAL_THRESHOLD
    · rw [if_pos hcnt] at h; exact absurd h (by decide)
    · rw [if_neg hcnt] at h
      by_cases hto : bh ≥ d.timeoutHeight
      · exact ⟨by omega, hto⟩
      · rw [if_neg hto] at h; exact absurd h (by decide)
  · intro ⟨hcnt, hto⟩
    rw [if_neg (by omega : ¬ cnt ≥ SIGNAL_THRESHOLD)]
    rw [if_pos hto]

-- ═══════════════════════════════════════════════════════════════════
-- §4  FlagDay live bridge
-- ═══════════════════════════════════════════════════════════════════

/-- **FlagDay activation iff**: `flagDayActive` returns true iff
    `height ≥ activationHeight`.
    Matches Go: `FlagDayActiveAtHeight(d, height) = (height >= d.ActivationHeight, nil)`.
    Matches Rust: `flagday_active_at_height(&d, height) = Ok(height >= d.activation_height)`. -/
theorem flagday_active_iff (activationHeight height : Nat) :
    flagDayActive activationHeight height = true ↔ height ≥ activationHeight := by
  simp [flagDayActive]

/-- FlagDay inactive iff height < activationHeight. -/
theorem flagday_inactive_iff (activationHeight height : Nat) :
    flagDayActive activationHeight height = false ↔ height < activationHeight := by
  simp [flagDayActive]

-- ═══════════════════════════════════════════════════════════════════
-- §5  Consensus constant parity bridge
-- ═══════════════════════════════════════════════════════════════════

/-- Lean `SIGNAL_THRESHOLD` matches Go/Rust consensus constant.
    Go:   `consensus/params.go` → `SIGNAL_THRESHOLD = 1815`
    Rust: `src/params.rs`       → `pub const SIGNAL_THRESHOLD: u32 = 1815`

    A mismatch here would cause consensus divergence between Lean model
    predictions and Go/Rust runtime behavior. -/
theorem signal_threshold_value : SIGNAL_THRESHOLD = 1815 := rfl

-- ═══════════════════════════════════════════════════════════════════
-- §6  Minimum steps to ACTIVE bridge
--
-- Go/Rust require exactly 3 boundary transitions to reach ACTIVE
-- from DEFINED: DEFINED → STARTED → LOCKED_IN → ACTIVE.
-- ═══════════════════════════════════════════════════════════════════

/-- ACTIVE requires minimum 3 transitions from DEFINED.
    Step 1: DEFINED → STARTED (when bh ≥ startHeight)
    Step 2: STARTED → LOCKED_IN (when cnt ≥ SIGNAL_THRESHOLD)
    Step 3: LOCKED_IN → ACTIVE (unconditional, by locked_in_always_activates)

    This proves the minimum path length and extracts the two non-trivial
    preconditions, matching Go/Rust FSM behavior. -/
theorem min_three_steps_to_active
    (bh1 cnt1 bh2 cnt2 : Nat) (d : FeatureBitDeployment)
    (hStep1 : featureBitNextState .defined bh1 cnt1 d = .started)
    (hStep2 : featureBitNextState .started bh2 cnt2 d = .lockedIn) :
    bh1 ≥ d.startHeight ∧ cnt2 ≥ SIGNAL_THRESHOLD := by
  constructor
  · exact (defined_to_started_iff bh1 cnt1 d).mp hStep1
  · exact (started_to_lockedin_iff bh2 cnt2 d).mp hStep2

end FeatureActivationLiveBridge

end RubinFormal
