import RubinFormal.CovenantGenesisV1
import RubinFormal.Conformance.CVVaultPolicyReplay

namespace RubinFormal

/-- Policy-level lifecycle for a `CORE_VAULT` output. -/
inductive VaultState where
  | created
  | triggered
  | swept
  | cancelled
  deriving DecidableEq, Repr

/-- Lifecycle actions. `wait` is an explicit stutter step so every state
    admits at least one valid transition in the model. -/
inductive VaultAction where
  | trigger
  | sweep (lockMode lockValue blockHeight blockMtp : Nat)
  | cancel
  | wait
  deriving DecidableEq, Repr

/-- Sweep parameters must satisfy the same wire-level bounds as the HTLC parser:
    only modes `0`/`1` are valid and `lockValue` must be positive. -/
def validSweepParams (lockMode lockValue : Nat) : Bool :=
  (lockMode <= CovenantGenesisV1.LOCK_MODE_TIMESTAMP) && (0 < lockValue)

def vaultTransition : VaultState -> VaultAction -> Option VaultState
  | .created, .trigger => some .triggered
  | .created, .cancel => some .cancelled
  | .created, .wait => some .created
  | .triggered, .sweep lockMode lockValue blockHeight blockMtp =>
      if validSweepParams lockMode lockValue then
        if CovenantGenesisV1.htlcTimelockMet lockMode lockValue blockHeight blockMtp then
          some .swept
        else
          none
      else
        none
  | .triggered, .wait => some .triggered
  | .swept, .wait => some .swept
  | .cancelled, .wait => some .cancelled
  | _, _ => none

theorem triggered_implies_sweepable
    (lockMode lockValue blockHeight blockMtp : Nat)
    (hMode : lockMode <= CovenantGenesisV1.LOCK_MODE_TIMESTAMP)
    (hValue : 0 < lockValue)
    (h : CovenantGenesisV1.htlcTimelockMet lockMode lockValue blockHeight blockMtp = true) :
    vaultTransition .triggered (.sweep lockMode lockValue blockHeight blockMtp) = some .swept := by
  simp [vaultTransition, validSweepParams, hMode, hValue, h]

theorem cancelled_implies_not_sweepable
    (lockMode lockValue blockHeight blockMtp : Nat) :
    vaultTransition .cancelled (.sweep lockMode lockValue blockHeight blockMtp) = none := by
  rfl

theorem no_dead_states : ∀ s : VaultState, ∃ a next, vaultTransition s a = some next := by
  intro s
  cases s with
  | created =>
      exact ⟨VaultAction.trigger, VaultState.triggered, rfl⟩
  | triggered =>
      exact ⟨VaultAction.wait, VaultState.triggered, rfl⟩
  | swept =>
      exact ⟨VaultAction.wait, VaultState.swept, rfl⟩
  | cancelled =>
      exact ⟨VaultAction.wait, VaultState.cancelled, rfl⟩

theorem timelock_enforced
    (lockMode lockValue blockHeight blockMtp : Nat)
    (h : CovenantGenesisV1.htlcTimelockMet lockMode lockValue blockHeight blockMtp = false) :
    vaultTransition .triggered (.sweep lockMode lockValue blockHeight blockMtp) = none := by
  simp [vaultTransition, validSweepParams, h]

/-- Convenience bundle: the state-machine sweep check and the vault-policy replay
    theorem are both available under their respective independent hypotheses. -/
theorem vault_sweep_and_policy_independent_checks
    (v : Conformance.CVVaultPolicyVector)
    (lockMode lockValue blockHeight blockMtp : Nat)
    (hOrder : v.validationOrder = none)
    (hMulti : v.vaultInputCount <= 1)
    (hOwner : v.hasOwnerAuth = true)
    (hSponsor : (v.nonVaultLockIds.all (fun x => x == v.ownerLockId)) = true)
    (hSlots : (v.slots == v.keyCount) = true)
    (hSentinel :
      (v.sentinelSuiteId == 0 &&
        v.sentinelPubkeyLen == 0 &&
        v.sentinelSigLen == 0 &&
        (!v.sentinelVerifyCalled)) = true)
    (hSig : v.sigThresholdOk = true)
    (hWhitelist : Conformance.strictlySortedUnique v.whitelist = true)
    (hValue : v.sumOut >= v.sumInVault)
    (hMode : lockMode <= CovenantGenesisV1.LOCK_MODE_TIMESTAMP)
    (hPositive : 0 < lockValue)
    (hTimelock : CovenantGenesisV1.htlcTimelockMet lockMode lockValue blockHeight blockMtp = true) :
    vaultTransition .triggered (.sweep lockMode lockValue blockHeight blockMtp) = some .swept ∧
      Conformance.vaultPolicyEval v = (true, none) := by
  constructor
  · exact triggered_implies_sweepable lockMode lockValue blockHeight blockMtp hMode hPositive hTimelock
  · exact Conformance.vault_policy_default_order_safe_proved
      v hOrder hMulti hOwner hSponsor hSlots hSentinel hSig hWhitelist hValue

end RubinFormal
