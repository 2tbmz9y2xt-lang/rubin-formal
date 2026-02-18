import Std
import RubinFormal.U64

namespace RubinFormal

abbrev Height := Nat
abbrev Txid := Nat

-- v1.1 protocol limits (consensus constants in the spec).
def MAX_TX_INPUTS : Nat := 1024
def MAX_TX_OUTPUTS : Nat := 1024
def MAX_WITNESS_ITEMS : Nat := 1024

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
  witness_count : Nat
  isCoinbase : Bool := false
  deriving DecidableEq, Repr

inductive TxErr where
  | TX_ERR_MISSING_UTXO
  | TX_ERR_PARSE
  | TX_ERR_VALUE_CONSERVATION
  | TX_ERR_WITNESS_OVERFLOW
  deriving DecidableEq, Repr

def hasDuplicateOutpoints (xs : List OutPoint) : Bool :=
  let rec go (seen : Std.RBSet OutPoint compare) : List OutPoint → Bool
    | [] => false
    | x :: rest =>
        if seen.contains x then
          true
        else
          go (seen.insert x) rest
  go (Std.RBSet.empty) xs

def valuesOfOutputs (outs : List TxOutput) : List U64 :=
  outs.map (fun o => o.value)

def lookupInputValues (u : UTXOSet) (ins : List OutPoint) : Option (List U64) :=
  ins.mapM (fun op => do
    let e ← u.find? op
    some e.out.value)

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

def validateTx (u : UTXOSet) (t : Tx) : Except TxErr Unit :=
  -- Basic structural limits first (cheap rejects).
  if t.inputs.length > MAX_TX_INPUTS then
    Except.error TxErr.TX_ERR_PARSE
  else if t.outputs.length > MAX_TX_OUTPUTS then
    Except.error TxErr.TX_ERR_PARSE
  else if t.witness_count > MAX_WITNESS_ITEMS then
    Except.error TxErr.TX_ERR_WITNESS_OVERFLOW
  else if t.isCoinbase then
    -- Spec: coinbase witness_count MUST be 0.
    if t.witness_count = 0 then
      Except.ok ()
    else
      Except.error TxErr.TX_ERR_PARSE
  else if t.witness_count != t.inputs.length then
    -- Spec: witness_count MUST equal input_count.
    Except.error TxErr.TX_ERR_PARSE
  else if (t.isCoinbase = false) && hasDuplicateOutpoints t.inputs then
    -- Spec: duplicate input outpoints MUST reject as TX_ERR_PARSE.
    Except.error TxErr.TX_ERR_PARSE
  else
    -- Value conservation per spec §4.5 with checked arithmetic.
    match lookupInputValues u t.inputs with
    | none => Except.error TxErr.TX_ERR_MISSING_UTXO
    | some ins =>
        match U64.sum? ins, U64.sum? (valuesOfOutputs t.outputs) with
        | none, _ => Except.error TxErr.TX_ERR_PARSE
        | _, none => Except.error TxErr.TX_ERR_PARSE
        | some sumIn, some sumOut =>
            if sumOut.val > sumIn.val then
              Except.error TxErr.TX_ERR_VALUE_CONSERVATION
            else
              Except.ok ()

def SpendTx (u : UTXOSet) (t : Tx) (h : Height) : Except TxErr UTXOSet := do
  validateTx u t
  if t.isCoinbase then
    -- Coinbase creates outputs; inputs are ignored in this simplified model.
    Except.ok (addOutputs u t.txid t.outputs h)
  else
    match removeInputs u t.inputs with
    | none => Except.error TxErr.TX_ERR_MISSING_UTXO
    | some u' => Except.ok (addOutputs u' t.txid t.outputs h)

end RubinFormal
