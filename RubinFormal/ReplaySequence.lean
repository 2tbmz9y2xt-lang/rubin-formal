import Std

namespace RubinFormal

-- Replay-domain and sequence checks (spec §3.4).

inductive TxErr where
  | TX_ERR_TX_NONCE_INVALID
  | TX_ERR_NONCE_REPLAY
  | TX_ERR_SEQUENCE_INVALID
  deriving DecidableEq, Repr

structure TxMinimal where
  tx_nonce : UInt64
  sequences : List UInt32
  isCoinbase : Bool := false
  deriving DecidableEq, Repr

def nonceOk (n : UInt64) : Bool :=
  n != 0

def sequenceOk (s : UInt32) : Bool :=
  (s != 0xffffffff) && (s.toNat ≤ 0x7fffffff)

def validateReplayAndSequence (seen : Std.RBSet UInt64 compare) (t : TxMinimal) :
    Except TxErr (Std.RBSet UInt64 compare) :=
  if t.isCoinbase then
    -- coinbase tx_nonce=0 is allowed (spec coinbase rules), and no sequence rules enforced here.
    Except.ok seen
  else
    if !nonceOk t.tx_nonce then
      Except.error TxErr.TX_ERR_TX_NONCE_INVALID
    else if seen.contains t.tx_nonce then
      Except.error TxErr.TX_ERR_NONCE_REPLAY
    else if t.sequences.all sequenceOk then
      Except.ok (seen.insert t.tx_nonce)
    else
      Except.error TxErr.TX_ERR_SEQUENCE_INVALID

-- Validate all non-coinbase txs in block order, as per spec.
def validateBlockReplayAndSequence (txs : List TxMinimal) : Except TxErr Unit :=
  let rec go (seen : Std.RBSet UInt64 compare) (rest : List TxMinimal) : Except TxErr Unit :=
    match rest with
    | [] => Except.ok ()
    | t :: rs =>
        match validateReplayAndSequence seen t with
        | Except.error e => Except.error e
        | Except.ok seen' => go seen' rs
  go (Std.RBSet.empty) txs

end RubinFormal

