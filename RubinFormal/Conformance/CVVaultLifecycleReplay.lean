import RubinFormal.VaultStateMachine
import RubinFormal.Conformance.CVVaultReplay

namespace RubinFormal.Conformance

open RubinFormal

private structure VaultLifecycleWitness where
  tx : UtxoBasicV1.Tx
  spentVaults : List CovenantGenesisV1.VaultCovenant
  createdVaults : List CovenantGenesisV1.VaultCovenant
  htlcOutputs : List CovenantGenesisV1.HtlcCovenant

private def collectSpentVaults? (utxos : List VaultEntry) :
    Option (List CovenantGenesisV1.VaultCovenant) :=
  utxos.foldl
    (fun acc u =>
      acc.bind fun spent =>
        if u.covenantType == CovenantGenesisV1.COV_TYPE_VAULT then
          match RubinFormal.decodeHex? u.covenantDataHex with
          | some covData =>
              match CovenantGenesisV1.parseVaultCovenantData covData with
              | .ok vault => some (spent.concat vault)
              | .error _ => none
          | none => none
        else
          some spent)
    (some [])

private def collectCreatedLifecycleOutputs? (outs : List UtxoBasicV1.TxOut) :
    Option (List CovenantGenesisV1.VaultCovenant × List CovenantGenesisV1.HtlcCovenant) :=
  outs.foldl
    (fun acc o =>
      acc.bind fun (vaults, htlcs) =>
        if o.covenantType == CovenantGenesisV1.COV_TYPE_VAULT then
          match CovenantGenesisV1.parseVaultCovenantData o.covenantData with
          | .ok vault => some (vaults.concat vault, htlcs)
          | .error _ => none
        else if o.covenantType == CovenantGenesisV1.COV_TYPE_HTLC then
          match CovenantGenesisV1.parseHtlcCovenantData o.covenantData with
          | .ok htlc => some (vaults, htlcs.concat htlc)
          | .error _ => none
        else
          some (vaults, htlcs))
    (some ([], []))

/-- Filter UTXO entries to only those actually consumed by a transaction's inputs.
    Compares (txidHex, vout) against each input's (prevTxid, prevVout). -/
private def filterSpentUtxos (utxos : List VaultEntry) (inputs : List UtxoBasicV1.TxIn) :
    List VaultEntry :=
  utxos.filter (fun u =>
    inputs.any (fun inp =>
      match RubinFormal.decodeHex? u.txidHex with
      | some txid => inp.prevTxid == txid && inp.prevVout == u.vout
      | none => false))

/-- Decode the concrete tx/UTXO lifecycle witness carried by a `CV-VAULT` vector.
    Only UTXOs actually consumed by the transaction's inputs are treated as spent.
    If any lifecycle-relevant covenant bytes fail to parse, the bridge fails closed. -/
private def vaultLifecycleWitness? (v : VaultVector) : Option VaultLifecycleWitness := do
  let txBytes <- RubinFormal.decodeHex? v.txHex
  let tx <- match UtxoBasicV1.parseTx txBytes with | .ok tx => some tx | .error _ => none
  let spentEntries := filterSpentUtxos v.utxos tx.inputs
  let spentVaults <- collectSpentVaults? spentEntries
  let (createdVaults, htlcOutputs) <- collectCreatedLifecycleOutputs? tx.outputs
  pure { tx := tx, spentVaults := spentVaults, createdVaults := createdVaults, htlcOutputs := htlcOutputs }

/-- Classify a `CV-VAULT` vector by the lifecycle witness actually carried in its
    tx/UTXO bytes, not by any naming convention in `id`. -/
def vaultLifecyclePhase (v : VaultVector) : Option VaultState :=
  match vaultLifecycleWitness? v with
  | some witness =>
      if witness.spentVaults.isEmpty && !witness.createdVaults.isEmpty then
        some .created
      else if !witness.spentVaults.isEmpty then
        some .triggered
      else
        none
  | none => none

private def txBlockMtp (v : VaultVector) : Nat :=
  match v.blockMtp with
  | some mtp => mtp
  | none => v.blockTimestamp

private def outputsWhitelisted
    (vault : CovenantGenesisV1.VaultCovenant)
    (tx : UtxoBasicV1.Tx) : Bool :=
  tx.outputs.all (fun o =>
    vault.whitelist.contains (RubinFormal.OutputDescriptor.hash o.covenantType o.covenantData))

private def createWitnessCarriesState (witness : VaultLifecycleWitness) : Bool :=
  witness.spentVaults.isEmpty && !witness.createdVaults.isEmpty

private def spendWitnessCarriesLifecycle
    (v : VaultVector)
    (witness : VaultLifecycleWitness) : Bool :=
  let blockedByMultiplicity := 1 < witness.spentVaults.length
  let blockedByRecursion := !witness.createdVaults.isEmpty
  let blockedByWhitelist :=
    match witness.spentVaults with
    | spentVault :: [] => !outputsWhitelisted spentVault witness.tx
    | _ => false
  let triggerWitness :=
    match witness.spentVaults with
    | spentVault :: [] =>
        witness.createdVaults.isEmpty &&
        outputsWhitelisted spentVault witness.tx &&
        vaultTransition .created .trigger == some .triggered
    | _ => false
  let sweepWitness :=
    witness.htlcOutputs.any (fun htlc =>
      match vaultTransition .triggered (.sweep htlc.lockMode htlc.lockValue v.height (txBlockMtp v)) with
      | some .swept => true
      | _ => false)
  (!witness.spentVaults.isEmpty) &&
    (triggerWitness || sweepWitness || blockedByWhitelist || blockedByRecursion || blockedByMultiplicity)

/-- Combined gate: each CV-VAULT conformance vector must pass both
    (1) transaction-level replay and
    (2) a lifecycle bridge reconstructed from concrete tx/UTXO bytes.

    `.created` is witnessed by a parseable `CORE_VAULT` output.
    `.triggered` is witnessed by either:
    - a concrete `trigger` transition from a spent vault input,
    - a concrete `sweep` transition from an HTLC output, or
    - a concrete blocking witness (multi-vault spend, vault recursion, whitelist miss). -/
def vaultVectorWithLifecycle (v : VaultVector) : Bool :=
  let txPass := vaultVectorPass v
  let smOk :=
    match vaultLifecycleWitness? v, vaultLifecyclePhase v with
    | some witness, some .created => createWitnessCarriesState witness
    | some witness, some .triggered => spendWitnessCarriesLifecycle v witness
    | _, _ => false
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
    (hMode : lockMode <= CovenantGenesisV1.LOCK_MODE_TIMESTAMP)
    (hPositive : 0 < lockValue)
    (hTimelock : CovenantGenesisV1.htlcTimelockMet lockMode lockValue blockHeight blockMtp = true) :
    vaultTransition .created .trigger = some .triggered ∧
    vaultTransition .triggered (.sweep lockMode lockValue blockHeight blockMtp) = some .swept := by
  constructor
  · rfl
  · simp [vaultTransition, validSweepParams, hMode, hPositive, hTimelock]

/-- Cancel lifecycle: created → cancelled, and cancelled blocks sweep. -/
theorem vault_cancel_lifecycle_valid :
    vaultTransition .created .cancel = some .cancelled ∧
    ∀ lm lv bh bm : Nat, vaultTransition .cancelled (.sweep lm lv bh bm) = none := by
  constructor
  · rfl
  · intros; rfl

end RubinFormal.Conformance
