import RubinFormal.CovenantGenesisV1
namespace RubinFormal
open CovenantGenesisV1

/-- P2PK covenant type is 0x0000 (genesis rule anchor). -/
theorem genesis_p2pk_covenant : COV_TYPE_P2PK = 0 := rfl

/-- ANCHOR covenant type is 0x0002. -/
theorem genesis_anchor_covenant : COV_TYPE_ANCHOR = 2 := rfl

/-- HTLC covenant type is 0x0100 (256). -/
theorem genesis_htlc_covenant : COV_TYPE_HTLC = 256 := rfl

end RubinFormal
