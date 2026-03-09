import RubinFormal.Types
import RubinFormal.ByteWireV2
import RubinFormal.TxParseV2
import RubinFormal.DaCoreV1

namespace RubinFormal

open Wire

namespace TxWeightV2

-- Constants from CANONICAL §§2/4/5/9 (subset required for weight accounting).
def WITNESS_DISCOUNT_DIVISOR : Nat := 4

def VERIFY_COST_ML_DSA_87 : Nat := 8
def VERIFY_COST_UNKNOWN_SUITE : Nat := 64

def MAX_WITNESS_ITEMS : Nat := 1024
def MAX_WITNESS_BYTES_PER_TX : Nat := 100000

def SUITE_ID_SENTINEL : Nat := 0x00
def SUITE_ID_ML_DSA_87 : Nat := 0x01

def ML_DSA_87_PUBKEY_BYTES : Nat := 2592
def ML_DSA_87_SIG_BYTES : Nat := 4627

def COV_TYPE_ANCHOR : Nat := 0x0002
def COV_TYPE_DA_COMMIT : Nat := 0x0103

def compactSizeLen (n : Nat) : Nat :=
  if n < 0xfd then 1
  else if n ≤ 0xffff then 3
  else if n ≤ 0xffffffff then 5
  else 9

structure WeightStats where
  weight : Nat
  daBytes : Nat
  anchorBytes : Nat
deriving Repr, DecidableEq

def requireMinimal (minimal : Bool) : Option Unit :=
  if minimal then some () else none

def parseInputsSkip (c : Cursor) (n : Nat) : Option Cursor := do
  let mut cur := c
  for _ in [0:n] do
    let (_, cur1) ← cur.getBytes? 32
    let (_, cur2) ← cur1.getBytes? 4
    let (ssLen, cur3, minimal) ← cur2.getCompactSize?
    let _ ← requireMinimal minimal
    let (_, cur4) ← cur3.getBytes? ssLen
    let (_, cur5) ← cur4.getBytes? 4
    cur := cur5
  pure cur

def parseOutputsForAnchor (c : Cursor) (n : Nat) : Option (Cursor × Nat) := do
  let mut cur := c
  let mut anchor : Nat := 0
  for _ in [0:n] do
    let (_, cur1) ← cur.getBytes? 8
    let (ctRaw, cur2) ← cur1.getBytes? 2
    let covenantType := Wire.u16le? (ctRaw.get! 0) (ctRaw.get! 1)
    let (cdLen, cur3, minimal) ← cur2.getCompactSize?
    let _ ← requireMinimal minimal
    let (_, cur4) ← cur3.getBytes? cdLen
    if covenantType == COV_TYPE_ANCHOR || covenantType == COV_TYPE_DA_COMMIT then
      anchor := anchor + cdLen
    cur := cur4
  pure (cur, anchor)

-- Parse a single witness item for weight accounting.
-- Returns (cursor, isML, isSigAlgInvalid, isSigNoncanonical).
-- isML: true iff suite=ML_DSA_87 with canonical pubkey/sig lengths.
-- isSigAlgInvalid: true for unknown suites (not sentinel, not ML_DSA_87).
-- isSigNoncanonical: true for ML_DSA_87 with wrong pubkey/sig lengths.
def parseWitnessItemForCounts (c : Cursor) : Option (Cursor × Bool × Bool × Bool) := do
  let (suite, c1) ← c.getU8?
  let suiteID := suite.toNat
  let (pubLen, c2, minimal1) ← c1.getCompactSize?
  let _ ← requireMinimal minimal1
  let (_pub, c3) ← c2.getBytes? pubLen
  let (sigLen, c4, minimal2) ← c3.getCompactSize?
  let _ ← requireMinimal minimal2
  let (sig, c5) ← c4.getBytes? sigLen

  if suiteID == SUITE_ID_SENTINEL then
    -- canonical sentinel encodings (see CANONICAL §5.4); only needed to preserve parse parity
    if pubLen == 0 && sigLen == 0 then
      pure (c5, false, false, false)
    else if pubLen == 32 then
      if sigLen == 1 then
        if sig.size == 1 && sig.get! 0 == 0x01 then
          pure (c5, false, false, false)
        else
          none
      else if sigLen >= 3 then
        if sig.size >= 3 && sig.get! 0 == 0x00 then
          let preLen := Wire.u16le? (sig.get! 1) (sig.get! 2)
          if preLen >= 1 && preLen <= TxV2.MAX_HTLC_PREIMAGE_BYTES && sigLen == 3 + preLen then
            pure (c5, false, false, false)
          else
            none
        else
          none
      else
        none
    else
      none
  else if suiteID == SUITE_ID_ML_DSA_87 then
    if pubLen == ML_DSA_87_PUBKEY_BYTES && sigLen == ML_DSA_87_SIG_BYTES + 1 then
      pure (c5, true, false, false)
    else
      -- Non-canonical ML-DSA-87 (wrong pubkey/sig lengths)
      pure (c5, false, false, true)
  else
    -- Unknown suite ID
    pure (c5, false, true, false)

-- Witness section results.  Callers choose which fields to consume:
--   weight function: uses mlCount + unknownSuiteCount, ignores error flags
--   block/tx validation: uses error flags, ignores unknownSuiteCount
structure WitnessSectionResult where
  cursor         : Cursor
  isOverflow     : Bool
  startOff       : Nat
  endOff         : Nat
  mlCount        : Nat
  unknownSuiteCount : Nat
  anySigAlgInvalid  : Bool
  anySigNoncanonical : Bool

def parseWitnessSectionForWeight (c : Cursor) : Option WitnessSectionResult := do
  let startOff := c.off
  let (wCount, c1, minimal) ← c.getCompactSize?
  let _ ← requireMinimal minimal
  if wCount > MAX_WITNESS_ITEMS then
    pure { cursor := c1, isOverflow := true, startOff := startOff, endOff := c1.off,
           mlCount := 0, unknownSuiteCount := 0, anySigAlgInvalid := false, anySigNoncanonical := false }
  else
    let mut cur := c1
    let mut mlCount : Nat := 0
    let mut unknownSuiteCount : Nat := 0
    let mut anySigAlgInvalid : Bool := false
    let mut anySigNoncanonical : Bool := false

    for _ in [0:wCount] do
      let (cur', isML, isSigAlg, isSigNoncan) ← parseWitnessItemForCounts cur
      cur := cur'
      if isML then mlCount := mlCount + 1
      if isSigAlg then
        unknownSuiteCount := unknownSuiteCount + 1
        anySigAlgInvalid := true
      if isSigNoncan then anySigNoncanonical := true

    let endOff := cur.off
    pure { cursor := cur, isOverflow := false, startOff := startOff, endOff := endOff,
           mlCount := mlCount, unknownSuiteCount := unknownSuiteCount,
           anySigAlgInvalid := anySigAlgInvalid, anySigNoncanonical := anySigNoncanonical }

def txWeightAndStats (tx : Bytes) : Except String WeightStats := do
  let c0 : Cursor := { bs := tx, off := 0 }
  let (_, c1) ←
    match c0.getU32le? with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  let (txKindB, c2) ←
    match c1.getU8? with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  let txKind := txKindB.toNat
  if !(txKind == 0x00 || txKind == 0x01 || txKind == 0x02) then
    throw "TX_ERR_PARSE"
  let (_, c3) ←
    match c2.getU64le? with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x

  let (inCount, c4, minIn) ←
    match c3.getCompactSize? with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  if !minIn then throw "TX_ERR_PARSE"
  match parseInputsSkip c4 inCount with
  | none => throw "TX_ERR_PARSE"
  | some c5 =>
    let (outCount, c6, minOut) ←
      match c5.getCompactSize? with
      | none => throw "TX_ERR_PARSE"
      | some x => pure x
    if !minOut then throw "TX_ERR_PARSE"
    let (c7, anchorBytes) ←
      match parseOutputsForAnchor c6 outCount with
      | none => throw "TX_ERR_PARSE"
      | some x => pure x
    let (_, c8) ←
      match c7.getU32le? with
      | none => throw "TX_ERR_PARSE"
      | some x => pure x
    let (c9, _daCoreLen) ←
      match DaCoreV1.parseDaCoreFieldsWithBytes txKind c8 with
      | none => throw "TX_ERR_PARSE"
      | some x => pure x
    let baseSize := c9.off

    let ws ←
      match parseWitnessSectionForWeight c9 with
      | none => throw "TX_ERR_PARSE"
      | some x => pure x
    let witnessSize := ws.endOff - ws.startOff
    if witnessSize > MAX_WITNESS_BYTES_PER_TX then
      throw "TX_ERR_WITNESS_OVERFLOW"
    if ws.isOverflow then throw "TX_ERR_WITNESS_OVERFLOW"
    -- Weight function does NOT throw sig errors (Go parity: CalcTxWeight §9).
    -- Sig errors are caught by ParseTx/validation, not weight calculation.

    let (daLen, c10, minDa) ←
      match ws.cursor.getCompactSize? with
      | none => throw "TX_ERR_PARSE"
      | some x => pure x
    if !minDa then throw "TX_ERR_PARSE"
    if txKind == 0x00 then
      if daLen != 0 then throw "TX_ERR_PARSE"
    else if txKind == 0x01 then
      if daLen > DaCoreV1.MAX_DA_MANIFEST_BYTES_PER_TX then throw "TX_ERR_PARSE"
    else
      if daLen < 1 || daLen > DaCoreV1.CHUNK_BYTES then throw "TX_ERR_PARSE"
    let (_, c11) ←
      match c10.getBytes? daLen with
      | none => throw "TX_ERR_PARSE"
      | some x => pure x
    if c11.off != tx.size then
      throw "TX_ERR_PARSE"

    let daSize := compactSizeLen daLen + daLen
    let daBytes := if txKind == 0x00 then 0 else daLen
    let mlCost := ws.mlCount * VERIFY_COST_ML_DSA_87
    let unknownCost := ws.unknownSuiteCount * VERIFY_COST_UNKNOWN_SUITE
    let sigCost := mlCost + unknownCost

    let weight := (WITNESS_DISCOUNT_DIVISOR * baseSize) + witnessSize + daSize + sigCost
    pure { weight := weight, daBytes := daBytes, anchorBytes := anchorBytes }

end TxWeightV2

end RubinFormal
