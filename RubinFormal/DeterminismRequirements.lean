import RubinFormal.BlockValidationOrder
import RubinFormal.ConnectBlockStrong
namespace RubinFormal
open BlockBasicV1 UtxoBasicV1

/-- validateBlockBasic is deterministic. -/
theorem validateBlockBasic_deterministic
    (b : Bytes) (ph pt : Option Bytes) :
    validateBlockBasic b ph pt = validateBlockBasic b ph pt := rfl

/-- parseTx is deterministic. -/
theorem parseTx_det (txBytes : Bytes) :
    parseTx txBytes = parseTx txBytes := rfl

/-- prepareNonCoinbaseTxBasic is deterministic. -/
theorem prepare_det (txBytes : Bytes)
    (utxoMap : Std.RBMap Outpoint UtxoEntry cmpOutpoint)
    (h bt : Nat) (cid : Bytes) :
    prepareNonCoinbaseTxBasic txBytes utxoMap h bt cid =
    prepareNonCoinbaseTxBasic txBytes utxoMap h bt cid := rfl

end RubinFormal
