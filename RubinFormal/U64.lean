namespace RubinFormal

-- Spec-aligned (consensus intent): u64 arithmetic must be exact; any overflow is a parse error.
-- In Lean, we model "exact u64" as a bounded Nat to make overflow explicit and provable.

def U64_MAX : Nat := (2 ^ 64) - 1
def U64_MOD : Nat := 2 ^ 64

abbrev U64 := Fin U64_MOD

def U64.ofNat? (x : Nat) : Option U64 :=
  if hx : x < U64_MOD then
    some ⟨x, hx⟩
  else
    none

def U64.add? (a b : U64) : Option U64 :=
  U64.ofNat? (a.val + b.val)

def U64.sum? (xs : List U64) : Option U64 :=
  xs.foldl
    (fun acc x =>
      match acc with
      | none => none
      | some s => U64.add? s x)
    (some ⟨0, by simp [U64_MOD]⟩)

theorem U64.sum?_some_implies_bounded (xs : List U64) (s : U64)
    (h : U64.sum? xs = some s) : s.val < U64_MOD := by
  -- Trivial: stored invariant in Fin.
  exact s.isLt

end RubinFormal
