import RubinFormal.UTXO

namespace RubinFormal

inductive Outcome where
  | ok
  | err (code : TxErr)
  deriving DecidableEq, Repr

structure Block where
  txs : List Tx
  deriving DecidableEq, Repr

-- Spec-structured ApplyBlock per `spec/RUBIN_L1_CANONICAL_v1.1.md §2`:
-- sequential over transactions in block order; invalid block => state does not advance.
def ApplyBlock (u0 : UTXOSet) (b : Block) (h : Height) : UTXOSet × Outcome :=
  let rec go (u : UTXOSet) (txs : List Tx) : UTXOSet × Outcome :=
    match txs with
    | [] => (u, Outcome.ok)
    | t :: rest =>
        match SpendTx u t h with
        | Except.ok u' => go u' rest
        | Except.error e => (u0, Outcome.err e)
  go u0 b.txs

-- T-004 (spec-structured): ApplyBlock determinism (no implementation choice permitted).
theorem T004_ApplyBlock_determinism
    (u0 : UTXOSet) (b : Block) (h : Height) (x y : UTXOSet × Outcome)
    (hx : ApplyBlock u0 b h = x) (hy : ApplyBlock u0 b h = y) : x = y := by
  exact Eq.trans (Eq.symm hx) hy

end RubinFormal
