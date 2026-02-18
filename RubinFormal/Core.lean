namespace RubinFormal

-- Minimal "bytes" model sufficient for determinism statements.
abbrev Byte := UInt8
abbrev Bytes := List Byte

inductive Outcome where
  | ok
  | err (code : UInt32)
  deriving DecidableEq, Repr

structure State where
  utxoTag : UInt64 := 0
  deriving DecidableEq, Repr

structure BlockBytes where
  raw : Bytes
  deriving DecidableEq, Repr

-- Spec-structured model: ApplyBlock is a sequential fold over transactions in block order.
-- We keep parsing abstract for now, but we make the structure match §2 and §4:
-- - parse block bytes -> list of tx "events" (abstract)
-- - fold SpendTx over the working UTXO state

abbrev Height := Nat

structure TxEvent where
  tag : UInt64
  deriving DecidableEq, Repr

def parseBlock (b : BlockBytes) : Option (List TxEvent) :=
  -- Placeholder parser: treat empty as parse error, otherwise one tx.
  match b.raw with
  | [] => none
  | _  => some [{ tag := 1 }]

def SpendTx (s : State) (_t : TxEvent) (_h : Height) : State :=
  -- Placeholder state transition: bump tag deterministically.
  { utxoTag := s.utxoTag + 1 }

def ApplyBlock (s : State) (b : BlockBytes) (h : Height) : State × Outcome :=
  match parseBlock b with
  | none => (s, Outcome.err 1)
  | some txs =>
      let s' := txs.foldl (fun acc t => SpendTx acc t h) s
      (s', Outcome.ok)

-- T-004 (model-level): ApplyBlock determinism.
theorem T004_ApplyBlock_determinism
    (s : State) (b : BlockBytes) (h : Height) (x y : State × Outcome)
    (hx : ApplyBlock s b h = x) (hy : ApplyBlock s b h = y) : x = y := by
  exact Eq.trans (Eq.symm hx) hy

end RubinFormal

