import Std
import RubinFormal.Hash

namespace RubinFormal

abbrev Byte := UInt8
abbrev Bytes := List Byte

-- For v1.1 formalization we represent 32-byte values abstractly as bytes, but keep
-- parsing out of scope. Conformance binds these to real vectors in the runner.
abbrev Bytes32 := Bytes

structure BlockCtx where
  height : Nat
  timestamp : Nat
  deriving DecidableEq, Repr

inductive TxErr where
  | TX_ERR_PARSE
  | TX_ERR_SIG_INVALID
  | TX_ERR_SIG_ALG_INVALID
  | TX_ERR_TIMELOCK_NOT_MET
  | TX_ERR_DEPLOYMENT_INACTIVE
  | TX_ERR_COVENANT_TYPE_INVALID
  deriving DecidableEq, Repr

-- Covenant payloads (semantic, already-parsed).
inductive LockMode where
  | height
  | unixTime
  deriving DecidableEq, Repr

structure P2PK where
  suite_id : UInt8
  key_id : Bytes32
  deriving DecidableEq, Repr

structure TimelockV1 where
  lock_mode : LockMode
  lock_value : Nat
  deriving DecidableEq, Repr

structure HTLCV1 where
  hash : Bytes32
  lock_mode : LockMode
  lock_value : Nat
  claim_key_id : Bytes32
  refund_key_id : Bytes32
  deriving DecidableEq, Repr

structure VaultV1 where
  owner_key_id : Bytes32
  spend_delay : Nat
  lock_mode : LockMode
  lock_value : Nat
  recovery_key_id : Bytes32
  deriving DecidableEq, Repr

-- Anchor envelopes for HTLC_V2 (semantic).
inductive AnchorTag where
  | htlcPreimage
  | other
  deriving DecidableEq, Repr

structure AnchorEnvelope where
  tag : AnchorTag
  preimage32 : Bytes32
  deriving DecidableEq, Repr

structure HTLCV2 where
  hash : Bytes32
  lock_mode : LockMode
  lock_value : Nat
  claim_key_id : Bytes32
  refund_key_id : Bytes32
  deriving DecidableEq, Repr

inductive CovenantType where
  | CORE_P2PK (p : P2PK)
  | CORE_TIMELOCK_V1 (t : TimelockV1)
  | CORE_HTLC_V1 (h : HTLCV1)
  | CORE_VAULT_V1 (v : VaultV1)
  | CORE_HTLC_V2 (h : HTLCV2)
  | CORE_ANCHOR
  | CORE_RESERVED_FUTURE
  deriving DecidableEq, Repr

structure Witness where
  suite_id : UInt8
  key_id : Bytes32
  isSentinel : Bool := false
  deriving DecidableEq, Repr

-- Deterministic lock check (spec §4.1 lock rules).
def timelockOk (ctx : BlockCtx) (m : LockMode) (v : Nat) : Bool :=
  match m with
  | LockMode.height => ctx.height ≥ v
  | LockMode.unixTime => ctx.timestamp ≥ v

def evalCovenant
    (ctx : BlockCtx)
    (creation_height : Nat) -- for VAULT spend_delay rule
    (script_sig_len : Nat)  -- for HTLC_V1 claim/refund branching
    (script_sig_preimage32 : Option Bytes32) -- claim path only (semantic)
    (anchors : List AnchorEnvelope) -- for HTLC_V2
    (w : Witness)
    (c : CovenantType) : Except TxErr Unit :=
  match c with
  | CovenantType.CORE_P2PK p =>
      if w.key_id = p.key_id ∧ w.suite_id = p.suite_id then
        Except.ok ()
      else
        Except.error TxErr.TX_ERR_SIG_INVALID

  | CovenantType.CORE_TIMELOCK_V1 t =>
      -- Spec: TIMELOCK spends require sentinel witness; any non-sentinel => SIG_ALG_INVALID.
      if w.isSentinel = false then
        Except.error TxErr.TX_ERR_SIG_ALG_INVALID
      else if timelockOk ctx t.lock_mode t.lock_value then
        Except.ok ()
      else
        Except.error TxErr.TX_ERR_TIMELOCK_NOT_MET

  | CovenantType.CORE_HTLC_V1 h =>
        if script_sig_len = 32 then
          -- claim path
          match script_sig_preimage32 with
          | none => Except.error TxErr.TX_ERR_PARSE
          | some preimage32 =>
              if SHA3_256 preimage32 = h.hash ∧ w.key_id = h.claim_key_id then
                Except.ok ()
              else
                Except.error TxErr.TX_ERR_SIG_INVALID
        else if script_sig_len = 0 then
          -- refund path
          if w.key_id != h.refund_key_id then
            Except.error TxErr.TX_ERR_SIG_INVALID
          else if timelockOk ctx h.lock_mode h.lock_value then
            Except.ok ()
          else
            Except.error TxErr.TX_ERR_TIMELOCK_NOT_MET
        else
          Except.error TxErr.TX_ERR_PARSE

  | CovenantType.CORE_VAULT_V1 v =>
      if w.key_id = v.owner_key_id then
        if v.spend_delay = 0 then
          Except.ok ()
        else if ctx.height ≥ creation_height + v.spend_delay then
          Except.ok ()
        else
          Except.error TxErr.TX_ERR_TIMELOCK_NOT_MET
      else if w.key_id = v.recovery_key_id then
        if timelockOk ctx v.lock_mode v.lock_value then
          Except.ok ()
        else
          Except.error TxErr.TX_ERR_TIMELOCK_NOT_MET
      else
        Except.error TxErr.TX_ERR_SIG_INVALID

  | CovenantType.CORE_HTLC_V2 h =>
      -- Spec §4.1 item 6 / §3.1 line 241: script_sig MUST be empty for HTLC_V2 spends.
      if script_sig_len != 0 then
        Except.error TxErr.TX_ERR_PARSE
      else if h.claim_key_id = h.refund_key_id then
        Except.error TxErr.TX_ERR_PARSE
      else
        let matching :=
          anchors.filter (fun a => a.tag = AnchorTag.htlcPreimage)
        if matching.length ≥ 2 then
          Except.error TxErr.TX_ERR_PARSE
        else
          -- Use head? to avoid List.get proof obligations in external proofs.
          -- When matching = [env]: head? = some env  (claim path)
          -- When matching = []:    head? = none       (refund path)
          match matching.head? with
          | some env =>
              -- Claim path: exactly one matching HTLC_V2 envelope.
              let preimage32 := env.preimage32
              if SHA3_256 preimage32 = h.hash ∧ w.key_id = h.claim_key_id then
                Except.ok ()
              else
                Except.error TxErr.TX_ERR_SIG_INVALID
          | none =>
              -- Refund path: no matching envelopes.
              if w.key_id != h.refund_key_id then
                Except.error TxErr.TX_ERR_SIG_INVALID
              else if timelockOk ctx h.lock_mode h.lock_value then
                Except.ok ()
              else
                Except.error TxErr.TX_ERR_TIMELOCK_NOT_MET

  | CovenantType.CORE_ANCHOR =>
      -- Non-spendable; if it appears as an input, consensus returns missing UTXO earlier.
      Except.error TxErr.TX_ERR_COVENANT_TYPE_INVALID

  | CovenantType.CORE_RESERVED_FUTURE =>
      Except.error TxErr.TX_ERR_COVENANT_TYPE_INVALID

-- Determinism hook for covenant evaluation.
theorem evalCovenant_deterministic
    (ctx : BlockCtx) (ch : Nat) (ssl : Nat) (sp : Option Bytes32) (as : List AnchorEnvelope)
    (w : Witness) (c : CovenantType) :
    evalCovenant ctx ch ssl sp as w c = evalCovenant ctx ch ssl sp as w c := by
  rfl

end RubinFormal
