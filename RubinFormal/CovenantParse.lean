import Std
import RubinFormal.Covenant
import RubinFormal.CompactSize

namespace RubinFormal

abbrev Byte := UInt8
abbrev Bytes := List Byte
abbrev Bytes32 := Bytes

-- covenant_type tags per spec §3.6
def CORE_P2PK_TAG : UInt16 := 0x0000
def CORE_TIMELOCK_V1_TAG : UInt16 := 0x0001
def CORE_ANCHOR_TAG : UInt16 := 0x0002
def CORE_HTLC_V1_TAG : UInt16 := 0x0100
def CORE_VAULT_V1_TAG : UInt16 := 0x0101
def CORE_HTLC_V2_TAG : UInt16 := 0x0102
def CORE_RESERVED_FUTURE_TAG : UInt16 := 0x00ff

def takeExact (n : Nat) (bs : Bytes) : Option (Bytes × Bytes) :=
  if h : n ≤ bs.length then
    some (bs.take n, bs.drop n)
  else
    none

def parseBytes32 (bs : Bytes) : Except TxErr Bytes32 :=
  if bs.length = 32 then
    Except.ok bs
  else
    Except.error TxErr.TX_ERR_PARSE

def parseLockMode (b : UInt8) : Except TxErr LockMode :=
  if b = 0x00 then
    Except.ok LockMode.height
  else if b = 0x01 then
    Except.ok LockMode.unixTime
  else
    Except.error TxErr.TX_ERR_PARSE

def parseU64le (bs : Bytes) : Except TxErr Nat :=
  if bs.length = 8 then
    -- `fromLEBytes` is a total function.
    Except.ok (fromLEBytes bs)
  else
    Except.error TxErr.TX_ERR_PARSE

def parseP2PK (cd : Bytes) : Except TxErr P2PK := do
  -- 1 + 32
  match takeExact 1 cd with
  | none => Except.error TxErr.TX_ERR_PARSE
  | some (s0, rest) =>
      let suite_id := s0.getD 0 0x00
      let kid ← parseBytes32 rest
      if cd.length = 33 then
        Except.ok { suite_id := suite_id, key_id := kid }
      else
        Except.error TxErr.TX_ERR_PARSE

def parseTimelockV1 (cd : Bytes) : Except TxErr TimelockV1 := do
  if cd.length != 9 then
    Except.error TxErr.TX_ERR_PARSE
  else
    match takeExact 1 cd with
    | none => Except.error TxErr.TX_ERR_PARSE
    | some (m0, rest) =>
        let modeB := m0.getD 0 0x00
        let m ← parseLockMode modeB
        let v ← parseU64le rest
        Except.ok { lock_mode := m, lock_value := v }

def parseHTLCCommon (cd : Bytes) : Except TxErr (Bytes32 × LockMode × Nat × Bytes32 × Bytes32) := do
  if cd.length != 105 then
    Except.error TxErr.TX_ERR_PARSE
  else
    match takeExact 32 cd with
    | none => Except.error TxErr.TX_ERR_PARSE
    | some (hsh, rest1) =>
        let hash ← parseBytes32 hsh
        match takeExact 1 rest1 with
        | none => Except.error TxErr.TX_ERR_PARSE
        | some (m0, rest2) =>
            let modeB := m0.getD 0 0x00
            let m ← parseLockMode modeB
            match takeExact 8 rest2 with
            | none => Except.error TxErr.TX_ERR_PARSE
            | some (lvB, rest3) =>
                let lv ← parseU64le lvB
                match takeExact 32 rest3 with
                | none => Except.error TxErr.TX_ERR_PARSE
                | some (ck, rest4) =>
                    let claim ← parseBytes32 ck
                    match takeExact 32 rest4 with
                    | none => Except.error TxErr.TX_ERR_PARSE
                    | some (rk, rest5) =>
                        if rest5.length != 0 then
                          Except.error TxErr.TX_ERR_PARSE
                        else
                          let refund ← parseBytes32 rk
                          Except.ok (hash, m, lv, claim, refund)

def parseHTLCV1 (cd : Bytes) : Except TxErr HTLCV1 := do
  let (hash, m, lv, claim, refund) ← parseHTLCCommon cd
  Except.ok { hash := hash, lock_mode := m, lock_value := lv, claim_key_id := claim, refund_key_id := refund }

def parseHTLCV2 (cd : Bytes) : Except TxErr HTLCV2 := do
  let (hash, m, lv, claim, refund) ← parseHTLCCommon cd
  -- Spec: claim_key_id != refund_key_id MUST be enforced for HTLC_V2.
  if claim = refund then
    Except.error TxErr.TX_ERR_PARSE
  else
    Except.ok { hash := hash, lock_mode := m, lock_value := lv, claim_key_id := claim, refund_key_id := refund }

def parseVaultV1 (cd : Bytes) : Except TxErr VaultV1 := do
  if cd.length = 73 then
    -- legacy: owner32 || lock_mode || lock_value || recovery32
    match takeExact 32 cd with
    | none => Except.error TxErr.TX_ERR_PARSE
    | some (ok, rest1) =>
        let owner ← parseBytes32 ok
        match takeExact 1 rest1 with
        | none => Except.error TxErr.TX_ERR_PARSE
        | some (m0, rest2) =>
            let modeB := m0.getD 0 0x00
            let m ← parseLockMode modeB
            match takeExact 8 rest2 with
            | none => Except.error TxErr.TX_ERR_PARSE
            | some (lvB, rest3) =>
                let lv ← parseU64le lvB
                let recov ← parseBytes32 rest3
                Except.ok
                  { owner_key_id := owner
                    spend_delay := 0
                    lock_mode := m
                    lock_value := lv
                    recovery_key_id := recov }
  else if cd.length = 81 then
    -- extended: owner32 || spend_delay8 || lock_mode || lock_value || recovery32
    match takeExact 32 cd with
    | none => Except.error TxErr.TX_ERR_PARSE
    | some (ok, rest1) =>
        let owner ← parseBytes32 ok
        match takeExact 8 rest1 with
        | none => Except.error TxErr.TX_ERR_PARSE
        | some (sdB, rest2) =>
            let sd ← parseU64le sdB
            match takeExact 1 rest2 with
            | none => Except.error TxErr.TX_ERR_PARSE
            | some (m0, rest3) =>
                let modeB := m0.getD 0 0x00
                let m ← parseLockMode modeB
                match takeExact 8 rest3 with
                | none => Except.error TxErr.TX_ERR_PARSE
                | some (lvB, rest4) =>
                    let lv ← parseU64le lvB
                    let recov ← parseBytes32 rest4
                    Except.ok
                      { owner_key_id := owner
                        spend_delay := sd
                        lock_mode := m
                        lock_value := lv
                        recovery_key_id := recov }
  else
    Except.error TxErr.TX_ERR_PARSE

def parseCovenantType (ct : UInt16) (cd : Bytes) : Except TxErr CovenantType :=
  if ct = CORE_P2PK_TAG then
    return CovenantType.CORE_P2PK (← parseP2PK cd)
  else if ct = CORE_TIMELOCK_V1_TAG then
    return CovenantType.CORE_TIMELOCK_V1 (← parseTimelockV1 cd)
  else if ct = CORE_ANCHOR_TAG then
    return CovenantType.CORE_ANCHOR
  else if ct = CORE_HTLC_V1_TAG then
    return CovenantType.CORE_HTLC_V1 (← parseHTLCV1 cd)
  else if ct = CORE_VAULT_V1_TAG then
    return CovenantType.CORE_VAULT_V1 (← parseVaultV1 cd)
  else if ct = CORE_HTLC_V2_TAG then
    return CovenantType.CORE_HTLC_V2 (← parseHTLCV2 cd)
  else if ct = CORE_RESERVED_FUTURE_TAG then
    return CovenantType.CORE_RESERVED_FUTURE
  else
    Except.error TxErr.TX_ERR_COVENANT_TYPE_INVALID

end RubinFormal

