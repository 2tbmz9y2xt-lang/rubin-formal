import RubinFormal.Covenant
import RubinFormal.CovenantParse
import RubinFormal.TxWire

namespace RubinFormal

/-!
## Anchor Envelope Parsing for HTLC_V2

Spec §4.1 item 6 defines the matching set as:

  matching = { output a in tx.outputs :
    a.covenant_type = CORE_ANCHOR  AND
    |a.covenant_data| = 54         AND
    a.covenant_data[0:22] = ASCII("RUBINv1-htlc-preimage/") }

This module provides a deterministic, total parser that converts a
`List TxWire.TxOutput` into the `List AnchorEnvelope` consumed by
`evalCovenant`.  The translation is:

  CORE_ANCHOR output + valid 54-byte envelope → AnchorTag.htlcPreimage
  CORE_ANCHOR output + any other payload       → AnchorTag.other
  non-CORE_ANCHOR output                       → dropped (filterMap → none)

This mirrors the Go reference implementation in `clients/go/consensus/tx.go`
(const htlcV2Prefix = "RUBINv1-htlc-preimage/", htlcV2EnvelopeLen = 54).
-/

-- ASCII("RUBINv1-htlc-preimage/") — exactly 22 bytes.
-- Byte values verified by HTLCV2_PREFIX_length below.
def HTLCV2_PREFIX : Bytes :=
  ([0x52, 0x55, 0x42, 0x49, 0x4e, 0x76, 0x31, 0x2d,
    0x68, 0x74, 0x6c, 0x63, 0x2d, 0x70, 0x72, 0x65,
    0x69, 0x6d, 0x61, 0x67, 0x65, 0x2f] : List Nat).map UInt8.ofNat

def HTLCV2_PREFIX_LEN   : Nat := 22
def HTLCV2_ENVELOPE_LEN : Nat := 54  -- 22 (prefix) + 32 (preimage32)

-- Sanity check compiled at build time.
theorem HTLCV2_PREFIX_length : HTLCV2_PREFIX.length = HTLCV2_PREFIX_LEN := by
  native_decide

-- ---------------------------------------------------------------------------
-- Prefix matching
-- ---------------------------------------------------------------------------

/-- `startsWith bs pref` is `true` iff the first `pref.length` bytes of `bs` equal `pref`.
    Using `List.take` keeps the definition extractable and easy to reason about. -/
def startsWith (bs pref : Bytes) : Bool :=
  bs.take pref.length = pref

theorem startsWith_def (bs pref : Bytes) :
    startsWith bs pref = (bs.take pref.length = pref) := rfl

-- An empty prefix is trivially matched by any byte string.
theorem startsWith_nil (bs : Bytes) : startsWith bs [] = true := by
  simp [startsWith]

-- ---------------------------------------------------------------------------
-- Envelope extraction
-- ---------------------------------------------------------------------------

/-- Parse a CORE_ANCHOR output's `covenant_data` as an HTLC_V2 envelope.
    Returns `some preimage32` (the 32-byte suffix) iff the data is exactly 54 bytes
    and begins with the HTLC_V2 prefix.  Returns `none` otherwise. -/
def parseHtlcV2Envelope (anchorData : Bytes) : Option Bytes32 :=
  if anchorData.length = HTLCV2_ENVELOPE_LEN ∧ startsWith anchorData HTLCV2_PREFIX then
    some (anchorData.drop HTLCV2_PREFIX_LEN)
  else
    none

/-- Convert a single transaction output into an `AnchorEnvelope`, or `none` if
    the output is not a CORE_ANCHOR.

    - Non-CORE_ANCHOR → `none`  (will be dropped by `filterMap`)
    - CORE_ANCHOR + valid 54-byte HTLC_V2 envelope → `some { htlcPreimage, p32 }`
    - CORE_ANCHOR + any other payload               → `some { other, [] }` -/
def envelopeOfOutput (o : TxWire.TxOutput) : Option AnchorEnvelope :=
  if o.covenant_type = CORE_ANCHOR_TAG then
    match parseHtlcV2Envelope o.covenant_data with
    | some p32 => some { tag := AnchorTag.htlcPreimage, preimage32 := p32 }
    | none     => some { tag := AnchorTag.other,        preimage32 := [] }
  else
    none

/-- Collect all `AnchorEnvelope`s from a transaction's output list.
    This is the bridge between the wire representation (`TxWire.TxOutput`) and
    the semantic `AnchorEnvelope` list consumed by `evalCovenant`. -/
def collectAnchorEnvelopes (outs : List TxWire.TxOutput) : List AnchorEnvelope :=
  outs.filterMap envelopeOfOutput

-- ---------------------------------------------------------------------------
-- Key properties
-- ---------------------------------------------------------------------------

-- The parser is a pure total function; determinism is reflexivity.
theorem collectAnchorEnvelopes_deterministic (outs : List TxWire.TxOutput) :
    collectAnchorEnvelopes outs = collectAnchorEnvelopes outs := rfl

-- Non-CORE_ANCHOR outputs contribute nothing.
theorem envelopeOfOutput_non_anchor (o : TxWire.TxOutput)
    (h : o.covenant_type ≠ CORE_ANCHOR_TAG) :
    envelopeOfOutput o = none := by
  simp [envelopeOfOutput, h]

-- A CORE_ANCHOR output with a valid HTLC_V2 envelope yields an htlcPreimage envelope.
theorem envelopeOfOutput_htlc_match (o : TxWire.TxOutput) (p32 : Bytes32)
    (hct  : o.covenant_type = CORE_ANCHOR_TAG)
    (henv : parseHtlcV2Envelope o.covenant_data = some p32) :
    envelopeOfOutput o = some { tag := AnchorTag.htlcPreimage, preimage32 := p32 } := by
  simp [envelopeOfOutput, hct, henv]

-- A CORE_ANCHOR output whose data does not match the HTLC_V2 envelope format
-- is still collected, but tagged as `other`.
theorem envelopeOfOutput_other (o : TxWire.TxOutput)
    (hct  : o.covenant_type = CORE_ANCHOR_TAG)
    (henv : parseHtlcV2Envelope o.covenant_data = none) :
    envelopeOfOutput o = some { tag := AnchorTag.other, preimage32 := [] } := by
  simp [envelopeOfOutput, hct, henv]

end RubinFormal
