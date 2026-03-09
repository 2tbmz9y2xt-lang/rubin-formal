import RubinFormal.VaultStateMachine
import RubinFormal.Conformance.CVVaultReplay

namespace RubinFormal.Conformance

open RubinFormal

/-- Prefix-free fallback for existing vectors that still encode the lifecycle in
    transaction structure instead of the ID. -/
private def vaultLifecyclePhaseFromStructure (v : VaultVector) : Option VaultState :=
  let spendsVault :=
    v.utxos.any (fun u => u.covenantType == CovenantGenesisV1.COV_TYPE_VAULT)
  let createsVault :=
    match RubinFormal.decodeHex? v.txHex with
    | some txBytes =>
        match UtxoBasicV1.parseTx txBytes with
        | .ok tx => tx.outputs.any (fun o => o.covenantType == CovenantGenesisV1.COV_TYPE_VAULT)
        | .error _ => false
    | none => false
  if createsVault && !spendsVault then some .created
  else if spendsVault then some .triggered
  else none

/-- Classify a CV-VAULT conformance vector by vault lifecycle phase.
    CREATE vectors → `.created` (vault output produced).
    SPEND vectors  → `.triggered` (vault input being consumed).
    Non-prefixed vectors must still classify from concrete tx/UTXO structure;
    otherwise the combined gate fails closed. -/
def vaultLifecyclePhase (v : VaultVector) : Option VaultState :=
  if "VAULT-CREATE".isPrefixOf v.id then some .created
  else if "VAULT-SPEND".isPrefixOf v.id then some .triggered
  else vaultLifecyclePhaseFromStructure v

/-- Combined gate: each CV-VAULT conformance vector must pass both
    (1) transaction-level replay and
    (2) state-machine reachability for its lifecycle phase.

    CREATE + expectOk: SM `.created` admits `trigger` (vault is live).
    SPEND:             SM `.triggered` admits `wait` (state is reachable). -/
def vaultVectorWithLifecycle (v : VaultVector) : Bool :=
  let txPass := vaultVectorPass v
  let smOk :=
    match vaultLifecyclePhase v with
    | some .created =>
        if v.expectOk then
          (vaultTransition .created .trigger).isSome
        else true
    | some .triggered =>
        (vaultTransition .triggered .wait).isSome
    | _ => false
  txPass && smOk

def cvVaultWithLifecyclePass : Bool :=
  cvUtxoApplyVectors_CV_VAULT.all vaultVectorWithLifecycle

/-- Machine-checked gate: all CV-VAULT vectors pass the combined
    transaction-level + state-machine lifecycle check. -/
theorem cv_vault_with_lifecycle_pass : cvVaultWithLifecyclePass = true := by
  native_decide

/-- Full happy-path lifecycle: created → triggered → swept.
    Valid whenever the HTLC timelock condition is satisfied. -/
theorem vault_full_lifecycle_valid
    (lockMode lockValue blockHeight blockMtp : Nat)
    (hTimelock : CovenantGenesisV1.htlcTimelockMet lockMode lockValue blockHeight blockMtp = true) :
    vaultTransition .created .trigger = some .triggered ∧
    vaultTransition .triggered (.sweep lockMode lockValue blockHeight blockMtp) = some .swept := by
  constructor
  · rfl
  · simp [vaultTransition, hTimelock]

/-- Cancel lifecycle: created → cancelled, and cancelled blocks sweep. -/
theorem vault_cancel_lifecycle_valid :
    vaultTransition .created .cancel = some .cancelled ∧
    ∀ lm lv bh bm : Nat, vaultTransition .cancelled (.sweep lm lv bh bm) = none := by
  constructor
  · rfl
  · intros; rfl

end RubinFormal.Conformance
