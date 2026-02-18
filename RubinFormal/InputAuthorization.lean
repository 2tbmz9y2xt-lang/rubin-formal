import RubinFormal.Covenant
import RubinFormal.DeploymentGate
import RubinFormal.AnchorEnvelopeParse

namespace RubinFormal

/-!
## Input Authorization

Models the strictly-ordered validation pipeline for each non-coinbase input,
as specified in §4 of RUBIN_L1_CANONICAL_v1.1 and implemented in
`ValidateInputAuthorization` in `clients/go/consensus/tx.go`.

### Step ordering (spec §4, steps 6–8)

```
6a. Suite gate     : reject unknown or inactive witness suite_ids
6b. Covenant gate  : reject CORE_HTLC_V2 spends when htlc_anchor_v1 is inactive
7.  Covenant eval  : type-specific deterministic rules (locks, hash checks, envelope scan)
8.  Signature verify: abstracted as an opaque Bool (SigOk)
```

The ordering is the key invariant: because each step is bound via `Except.bind`,
any error produced in steps 6–7 propagates unchanged through step 8.
This means covenant and gate failures can never be masked by a signature failure,
which the `gate_failure_precedes_sig_verify` family of theorems formalise.

### Abstraction of cryptography

`SigOk` is an opaque `Bool` representing the result of the post-quantum
signature check (ML-DSA-87 or SLH-DSA-SHAKE-256f).  Keeping it opaque
lets us prove ordering properties — and thus the full conformance suite —
without modelling the actual elliptic-curve / lattice arithmetic.
-/

/-- Abstract result of a post-quantum signature verification. -/
abbrev SigOk := Bool

/-- Validates a single non-coinbase input.

Parameters mirror the Go `ValidateInputAuthorization` signature:
- `d`                       deployment activation flags (VERSION_BITS state)
- `ctx`                     block height and timestamp at validation time
- `creation_height`         block height at which the UTXO being spent was created
- `script_sig_len`          byte-length of the input's `script_sig` field
- `script_sig_preimage32`   parsed 32-byte preimage if present (HTLC_V1 claim path)
- `txOuts`                  outputs of the spending transaction (HTLC_V2 envelope scan)
- `w`                       parsed witness: suite_id, key_id, sentinel flag
- `ctTag`                   raw `covenant_type` UInt16 from wire format
- `c`                       fully parsed covenant payload (semantic)
- `sigOk`                   abstract result of the PQ signature check
-/
def validateInputAuthorization
    (d                     : DeployCtx)
    (ctx                   : BlockCtx)
    (creation_height       : Nat)
    (script_sig_len        : Nat)
    (script_sig_preimage32 : Option Bytes32)
    (txOuts                : List TxWire.TxOutput)
    (w                     : Witness)
    (ctTag                 : UInt16)
    (c                     : CovenantType)
    (sigOk                 : SigOk) : Except TxErr Unit := do
  -- Step 6a: reject unknown suite_id or inactive SLH-DSA suite.
  gateSuiteId d w.suite_id
  -- Step 6b: reject CORE_HTLC_V2 spends when htlc_anchor_v1 is not ACTIVE.
  gateCovenant d ctTag
  -- Step 7: deterministic covenant evaluation — locks, hash checks, envelope scan.
  let anchors := collectAnchorEnvelopes txOuts
  evalCovenant ctx creation_height script_sig_len script_sig_preimage32 anchors w c
  -- Step 8: signature verification (last step; cannot mask earlier failures).
  if w.isSentinel then
    -- Sentinel witness (suite_id = 0x00): no signature required.
    pure ()
  else if sigOk then
    pure ()
  else
    throw TxErr.TX_ERR_SIG_INVALID

end RubinFormal
