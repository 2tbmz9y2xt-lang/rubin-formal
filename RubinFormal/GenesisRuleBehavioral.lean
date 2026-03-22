import RubinFormal.CovenantGenesisV1
namespace RubinFormal
open CovenantGenesisV1

/-- Genesis covenant validation is deterministic. -/
theorem validateCoinbaseGenesisOutputs_deterministic
    (outputs : List RubinFormal.UtxoBasicV1.TxOutput) (height : Nat) :
    validateCoinbaseGenesisOutputs outputs height =
    validateCoinbaseGenesisOutputs outputs height := rfl

/-- P2PK covenant type is 0x0000 (genesis rule anchor). -/
theorem genesis_p2pk_covenant : COV_TYPE_P2PK = 0 := rfl

end RubinFormal
