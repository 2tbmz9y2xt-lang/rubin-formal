namespace RubinFormal

inductive VBState where
  | DEFINED
  | STARTED
  | LOCKED_IN
  | ACTIVE
  | FAILED
  deriving DecidableEq, Repr

structure Deployment where
  bit : Nat
  start_height : Nat
  timeout_height : Nat
  signal_window : Nat
  threshold : Nat
  deriving Repr

def VERSION_BITS_START_HEIGHT : Nat := 0

def boundaryOrigin (d : Deployment) : Nat :=
  max VERSION_BITS_START_HEIGHT d.start_height

def isWindowBoundary (d : Deployment) (h : Nat) : Prop :=
  (h - boundaryOrigin d) % d.signal_window = 0

-- A chain history is modeled as a signaling predicate over heights.
abbrev SignalAt := Nat → Bool

def countSignalsInWindow (sig : SignalAt) (start : Nat) (win : Nat) : Nat :=
  (List.range win).foldl (fun acc i => if sig (start + i) then acc + 1 else acc) 0

-- Spec-aligned step function evaluated at a window boundary height `h`.
-- Inputs:
-- - `enteredLockedIn` is true iff the previous boundary transitioned into LOCKED_IN,
--   so that the "next boundary after entering LOCKED_IN" rule can be enforced.
structure VBWorkState where
  state : VBState
  enteredLockedInPrev : Bool := false
  deriving DecidableEq, Repr

def vbStepAtBoundary (d : Deployment) (sig : SignalAt) (h : Nat) (ws : VBWorkState) : VBWorkState :=
  match ws.state with
  | VBState.ACTIVE => { ws with state := VBState.ACTIVE, enteredLockedInPrev := false }
  | VBState.FAILED => { ws with state := VBState.FAILED, enteredLockedInPrev := false }
  | VBState.LOCKED_IN =>
      -- Rule 4: LOCKED_IN -> ACTIVE at the next boundary after entering LOCKED_IN.
      { state := VBState.ACTIVE, enteredLockedInPrev := false }
  | VBState.DEFINED =>
      if h >= d.start_height then
        { state := VBState.STARTED, enteredLockedInPrev := false }
      else
        { ws with state := VBState.DEFINED, enteredLockedInPrev := false }
  | VBState.STARTED =>
      -- Rule ordering from spec §8.0.1:
      -- 2) STARTED -> LOCKED_IN if preceding completed window meets threshold
      -- 3) STARTED -> FAILED if timeout reached and not LOCKED_IN
      let windowStart :=
        -- completed window immediately preceding boundary `h` is [h - window, h)
        if h >= d.signal_window then h - d.signal_window else 0
      let signalCount := countSignalsInWindow sig windowStart d.signal_window
      if signalCount >= d.threshold then
        { state := VBState.LOCKED_IN, enteredLockedInPrev := true }
      else if h >= d.timeout_height then
        { state := VBState.FAILED, enteredLockedInPrev := false }
      else
        { state := VBState.STARTED, enteredLockedInPrev := false }

def boundaryHeight (d : Deployment) (idx : Nat) : Nat :=
  boundaryOrigin d + idx * d.signal_window

-- Apply boundary transitions from index 0 up to (count-1) in order.
def applyBoundaries (d : Deployment) (sig : SignalAt) : Nat → VBWorkState → VBWorkState
  | 0, ws => ws
  | (n + 1), ws => applyBoundaries d sig n (vbStepAtBoundary d sig (boundaryHeight d n) ws)

def vbStateAtHeight (d : Deployment) (sig : SignalAt) (h : Nat) : VBState :=
  if d.signal_window = 0 then
    -- guard against degenerate params (non-spec)
    VBState.FAILED
  else
    let origin := boundaryOrigin d
    if h < origin then
      VBState.DEFINED
    else
      let idx := (h - origin) / d.signal_window
      -- for any height in window idx, the effective state includes evaluation at boundary 0..idx.
      (applyBoundaries d sig (idx + 1) { state := VBState.DEFINED, enteredLockedInPrev := false }).state

theorem vbStepAtBoundary_active_absorbing (d : Deployment) (sig : SignalAt) (h : Nat) :
    (vbStepAtBoundary d sig h { state := VBState.ACTIVE, enteredLockedInPrev := false }).state = VBState.ACTIVE := by
  simp [vbStepAtBoundary]

theorem applyBoundaries_active_absorbing (d : Deployment) (sig : SignalAt) (n : Nat) :
    (applyBoundaries d sig n { state := VBState.ACTIVE, enteredLockedInPrev := false }).state = VBState.ACTIVE := by
  induction n with
  | zero =>
      simp [applyBoundaries]
  | succ n ih =>
      -- applyBoundaries (n+1) = applyBoundaries n (vbStepAtBoundary ... at boundaryHeight n)
      simp [applyBoundaries, ih, vbStepAtBoundary_active_absorbing]

-- T-007 (spec-structured core): terminal states at window boundaries (spec §8.0.1 rule 5).
theorem T007_version_bits_terminal_at_boundary
    (d : Deployment) (sig : SignalAt) (h : Nat) :
    (vbStepAtBoundary d sig h { state := VBState.ACTIVE, enteredLockedInPrev := false }).state = VBState.ACTIVE ∧
    (vbStepAtBoundary d sig h { state := VBState.FAILED, enteredLockedInPrev := false }).state = VBState.FAILED := by
  constructor <;> simp [vbStepAtBoundary]

end RubinFormal
