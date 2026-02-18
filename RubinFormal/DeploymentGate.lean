import RubinFormal.CovenantParse
import RubinFormal.Covenant

namespace RubinFormal

-- Deployment gate (spec §4 step 6): reject certain covenant types unless ACTIVE.

structure DeployCtx where
  htlc_anchor_v1_active : Bool := false
  deriving DecidableEq, Repr

def gateCovenant (d : DeployCtx) (ct : UInt16) : Except TxErr Unit :=
  if ct = CORE_HTLC_V2_TAG then
    if d.htlc_anchor_v1_active then
      Except.ok ()
    else
      Except.error TxErr.TX_ERR_DEPLOYMENT_INACTIVE
  else
    Except.ok ()

end RubinFormal

