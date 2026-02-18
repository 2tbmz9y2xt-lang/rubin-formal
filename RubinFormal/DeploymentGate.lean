import RubinFormal.CovenantParse
import RubinFormal.Covenant

namespace RubinFormal

-- Deployment gate (spec §4 step 6): reject certain covenant types unless ACTIVE.

structure DeployCtx where
  htlc_anchor_v1_active : Bool := false
  slh_dsa_suite_active : Bool := false
  deriving DecidableEq, Repr

def gateCovenant (d : DeployCtx) (ct : UInt16) : Except TxErr Unit :=
  if ct = CORE_HTLC_V2_TAG then
    if d.htlc_anchor_v1_active then
      Except.ok ()
    else
      Except.error TxErr.TX_ERR_DEPLOYMENT_INACTIVE
  else
    Except.ok ()

-- Suite activation gate (spec §4 deployment/suite activation rules; exercised by CV-DEP).
-- - suite_id 0x01 (ML-DSA-87) is always allowed in v1.1.
-- - suite_id 0x02 (SLH-DSA-SHAKE-256f) is allowed only when the corresponding deployment is ACTIVE.
-- - suite_id 0x00 is the sentinel witness and is syntactically valid here (semantic gating is covenant-specific).
-- - any other suite_id MUST reject as TX_ERR_SIG_ALG_INVALID.
def gateSuiteId (d : DeployCtx) (suite_id : UInt8) : Except TxErr Unit :=
  if suite_id = 0x00 then
    Except.ok ()
  else if suite_id = 0x01 then
    Except.ok ()
  else if suite_id = 0x02 then
    if d.slh_dsa_suite_active then
      Except.ok ()
    else
      Except.error TxErr.TX_ERR_DEPLOYMENT_INACTIVE
  else
    Except.error TxErr.TX_ERR_SIG_ALG_INVALID

end RubinFormal
