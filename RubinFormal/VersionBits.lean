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

theorem applyBoundaries_append (d : Deployment) (sig : SignalAt) (n m : Nat) (ws : VBWorkState) :
    applyBoundaries d sig (n + m) ws = applyBoundaries d sig m (applyBoundaries d sig n ws) := by
  induction m generalizing ws with
  | zero =>
      simp [applyBoundaries]
  | succ m ih =>
      -- (n + (m+1)) = (n+m) + 1; unfold one step of applyBoundaries
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, applyBoundaries, ih]

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

theorem applyBoundaries_from_active (d : Deployment) (sig : SignalAt) (n : Nat) (ws : VBWorkState)
    (hws : ws.state = VBState.ACTIVE) :
    (applyBoundaries d sig n ws).state = VBState.ACTIVE := by
  induction n generalizing ws with
  | zero =>
      simpa [applyBoundaries, hws]
  | succ n ih =>
      -- one step: applyBoundaries (n+1) ws = applyBoundaries n (vbStepAtBoundary ... ws)
      -- and vbStepAtBoundary preserves ACTIVE regardless of enteredLockedInPrev
      have : (vbStepAtBoundary d sig (boundaryHeight d n) ws).state = VBState.ACTIVE := by
        -- rewrite ws.state = ACTIVE then simplify vbStepAtBoundary
        cases ws with
        | mk st ent =>
          simp [VBWorkState.state] at hws
          cases hws
          simp [vbStepAtBoundary, boundaryHeight]
      -- apply IH on the new ws
      exact ih (ws := vbStepAtBoundary d sig (boundaryHeight d n) ws) this

-- T-007 (strong): if state is ACTIVE at some height, it stays ACTIVE for all later heights.
theorem T007_version_bits_monotonicity_strong
    (d : Deployment) (sig : SignalAt) (h1 h2 : Nat)
    (hw : d.signal_window ≠ 0)
    (hle : h1 ≤ h2)
    (ha : vbStateAtHeight d sig h1 = VBState.ACTIVE) :
    vbStateAtHeight d sig h2 = VBState.ACTIVE := by
  unfold vbStateAtHeight at ha ⊢
  simp [hw] at ha ⊢
  let origin := boundaryOrigin d
  by_cases h1lt : h1 < origin
  · -- before origin => DEFINED, cannot be ACTIVE
    simp [origin, h1lt] at ha
  · have h1ge : origin ≤ h1 := Nat.le_of_not_gt h1lt
    have h2ge : origin ≤ h2 := Nat.le_trans h1ge hle
    have h1nlt : ¬ (h1 < origin) := Nat.not_lt_of_ge h1ge
    have h2nlt : ¬ (h2 < origin) := Nat.not_lt_of_ge h2ge
    simp [origin, h1nlt] at ha
    simp [origin, h2nlt]
    let idx1 := (h1 - origin) / d.signal_window
    let idx2 := (h2 - origin) / d.signal_window
    have hidx : idx1 ≤ idx2 := by
      exact Nat.div_le_div_right (Nat.sub_le_sub_right hle origin)
    -- At h1, applyBoundaries (idx1+1) yields ACTIVE.
    -- For h2, applyBoundaries (idx2+1) = applyBoundaries (idx1+1 + (idx2-idx1)) ...; ACTIVE absorbs.
    have : (applyBoundaries d sig (idx2 + 1) { state := VBState.DEFINED, enteredLockedInPrev := false }).state = VBState.ACTIVE := by
      have hsplit : idx2 + 1 = (idx1 + 1) + (idx2 - idx1) := by
        simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.add_sub_of_le hidx]
      -- rewrite and use append lemma + from_active absorption
      -- applyBoundaries (a+b) ws = applyBoundaries b (applyBoundaries a ws)
      -- and applyBoundaries a ws has state ACTIVE by ha
      have happ : applyBoundaries d sig ((idx1 + 1) + (idx2 - idx1)) { state := VBState.DEFINED, enteredLockedInPrev := false }
                  =
                applyBoundaries d sig (idx2 - idx1)
                  (applyBoundaries d sig (idx1 + 1) { state := VBState.DEFINED, enteredLockedInPrev := false }) := by
        simpa using (applyBoundaries_append d sig (idx1 + 1) (idx2 - idx1) { state := VBState.DEFINED, enteredLockedInPrev := false })
      -- now use ha and absorption
      -- set wsA := applyBoundaries ... (idx1+1) ...
      let wsA := applyBoundaries d sig (idx1 + 1) { state := VBState.DEFINED, enteredLockedInPrev := false }
      have wsAActive : wsA.state = VBState.ACTIVE := by
        simpa [wsA] using ha
      have tailActive : (applyBoundaries d sig (idx2 - idx1) wsA).state = VBState.ACTIVE :=
        applyBoundaries_from_active d sig (idx2 - idx1) wsA wsAActive
      -- finish
      simpa [hsplit, happ, wsA] using tailActive
    exact this

-- T-007 (spec-structured core): terminal states at window boundaries (spec §8.0.1 rule 5).
theorem T007_version_bits_terminal_at_boundary
    (d : Deployment) (sig : SignalAt) (h : Nat) :
    (vbStepAtBoundary d sig h { state := VBState.ACTIVE, enteredLockedInPrev := false }).state = VBState.ACTIVE ∧
    (vbStepAtBoundary d sig h { state := VBState.FAILED, enteredLockedInPrev := false }).state = VBState.FAILED := by
  constructor <;> simp [vbStepAtBoundary]

-- T-003 (ordering): if LOCKED_IN triggers, FAILED MUST NOT be evaluated at the same boundary.
-- In the spec this is captured by evaluating transition #2 before #3.
theorem T003_started_boundary_ordering_lockedin_over_failed
    (d : Deployment) (sig : SignalAt) (h : Nat) (ws : VBWorkState)
    (hws : ws.state = VBState.STARTED)
    (windowStart : Nat)
    (hs : windowStart = (if h >= d.signal_window then h - d.signal_window else 0))
    (hcnt : countSignalsInWindow sig windowStart d.signal_window ≥ d.threshold)
    (htimeout : h ≥ d.timeout_height) :
    (vbStepAtBoundary d sig h ws).state = VBState.LOCKED_IN := by
  -- rewrite to STARTED branch and simplify: threshold branch is taken before timeout check.
  cases ws with
  | mk st ent =>
    simp at hws
    cases hws
    -- unfold and rewrite windowStart
    simp [vbStepAtBoundary, hs, hcnt, htimeout, countSignalsInWindow]

end RubinFormal
