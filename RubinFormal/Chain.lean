import RubinFormal.Core

namespace RubinFormal

/-!
Chain-level "phase 1" invariants (model-level):

* A node applies blocks sequentially at increasing heights.
* If any block is invalid, evaluation stops at the first error.
* Prefix/suffix decomposition holds: applying (xs ++ ys) equals
  applying xs then (if OK) applying ys starting at the shifted height.

This is the minimal formal surface needed to reason about reorg safety as
"rewind to common ancestor state, then apply the chosen suffix".
-/

def ApplyBlocks (u0 : UTXOSet) (bs : List Block) (h0 : Height) : UTXOSet × Outcome :=
  let rec go (u : UTXOSet) (bs : List Block) (h : Height) : UTXOSet × Outcome :=
    match bs with
    | [] => (u, Outcome.ok)
    | b :: rest =>
        match ApplyBlock u b h with
        | (u', Outcome.ok) => go u' rest (h + 1)
        | (u', Outcome.err e) => (u', Outcome.err e)
  go u0 bs h0

theorem ApplyBlocks_nil (u0 : UTXOSet) (h0 : Height) :
    ApplyBlocks u0 [] h0 = (u0, Outcome.ok) := by
  unfold ApplyBlocks
  rfl

theorem ApplyBlocks_append (u0 : UTXOSet) (xs ys : List Block) (h0 : Height) :
    ApplyBlocks u0 (xs ++ ys) h0 =
      match ApplyBlocks u0 xs h0 with
      | (u1, Outcome.ok) => ApplyBlocks u1 ys (h0 + xs.length)
      | (u1, Outcome.err e) => (u1, Outcome.err e) := by
  -- Proof by induction on xs; the height shift is xs.length.
  induction xs generalizing u0 h0 with
  | nil =>
      simp [ApplyBlocks, ApplyBlocks_nil]
  | cons x xs ih =>
      -- Expand one step and reduce to the induction hypothesis.
      unfold ApplyBlocks
      -- `simp` turns (x :: xs) ++ ys into x :: (xs ++ ys), and (h0 + (Nat.succ ...))
      -- bookkeeping is handled by simp/arithmetic.
      simp
      -- After simp, we have a `match ApplyBlock u0 x h0 with ...` on both sides.
      -- Split on the result of ApplyBlock.
      cases hstep : ApplyBlock u0 x h0 with
      | mk u1 out1 =>
          cases out1 with
          | ok =>
              -- Continue with the remaining blocks at height h0+1.
              -- Also note: (h0 + (List.length (x :: xs))) = (h0 + 1 + xs.length).
              simpa [hstep, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
                (ih (u0 := u1) (h0 := h0 + 1) (ys := ys))
          | err e =>
              -- First error stops; both sides return the same (u1, err e).
              simp [hstep]

end RubinFormal

