import Std
import RubinFormal.U64

namespace RubinFormal

abbrev Height := Nat
abbrev Txid := Nat

structure OutPoint where
  txid : Txid
  vout : Nat
  deriving DecidableEq, Ord, Repr

inductive CovenantType where
  | CORE_P2PK
  | CORE_TIMELOCK_V1
  | CORE_HTLC_V1
  | CORE_VAULT_V1
  | CORE_HTLC_V2
  | CORE_ANCHOR
  | CORE_RESERVED_FUTURE
  deriving DecidableEq, Repr

structure TxOutput where
  value : U64
  covenant_type : CovenantType
  deriving DecidableEq, Repr

structure UtxoEntry where
  out : TxOutput
  creation_height : Height
  deriving DecidableEq, Repr

abbrev UTXOSet := Std.RBMap OutPoint UtxoEntry compare

def spendable (o : TxOutput) : Bool :=
  o.covenant_type != CovenantType.CORE_ANCHOR

structure Tx where
  txid : Txid
  inputs : List OutPoint
  outputs : List TxOutput
  isCoinbase : Bool := false
  deriving DecidableEq, Repr

inductive TxErr where
  | TX_ERR_MISSING_UTXO
  | TX_ERR_PARSE
  deriving DecidableEq, Repr

def removeInputs (u : UTXOSet) : List OutPoint → Option UTXOSet
  | [] => some u
  | op :: rest =>
      match u.find? op with
      | none => none
      | some _ =>
          removeInputs (u.erase op) rest

def addOutputs (u : UTXOSet) (txid : Txid) (outs : List TxOutput) (h : Height) : UTXOSet :=
  (outs.enum).foldl
    (fun acc (p : Nat × TxOutput) =>
      let (idx, out) := p
      if spendable out then
        let key : OutPoint := { txid := txid, vout := idx }
        acc.insert key { out := out, creation_height := h }
      else
        acc)
    u

def SpendTx (u : UTXOSet) (t : Tx) (h : Height) : Except TxErr UTXOSet :=
  if t.isCoinbase then
    -- coinbase has no inputs in this model; only creates spendable outputs
    Except.ok (addOutputs u t.txid t.outputs h)
  else
    match removeInputs u t.inputs with
    | none => Except.error TxErr.TX_ERR_MISSING_UTXO
    | some u' => Except.ok (addOutputs u' t.txid t.outputs h)

end RubinFormal

