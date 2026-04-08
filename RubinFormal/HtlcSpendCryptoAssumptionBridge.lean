import RubinFormal.UtxoApplyGenesisV1

namespace RubinFormal

namespace HtlcSpendCryptoAssumptionBridge

open RubinFormal
open RubinFormal.UtxoApplyGenesisV1
open RubinFormal.CovenantGenesisV1

private theorem uint8_beq_eq_decide (x y : UInt8) :
    BEq.beq x y = decide (x = y) := by
  cases x with
  | mk xv =>
    cases y with
    | mk yv =>
      simp [BEq.beq]

private theorem bytes_beq_refl (a : Bytes) : (a == a) = true := by
  cases a with
  | mk ad =>
      show Array.isEqv ad ad BEq.beq = true
      have h :
          (fun (x y : UInt8) => @BEq.beq UInt8 _ x y) =
          (fun x y => decide (x = y)) := by
        funext x y
        exact uint8_beq_eq_decide x y
      have hrw :
          Array.isEqv ad ad BEq.beq =
          Array.isEqv ad ad (fun x y => decide (x = y)) := by
        congr 1
      rw [hrw]
      exact Array.isEqv_self ad

private theorem bytes_bne_self_false (a : Bytes) : (a != a) = false := by
  show (!(a == a)) = false
  rw [bytes_beq_refl]
  rfl

private theorem bytes_beq_true_eq
    (a b : Bytes)
    (h : (a == b) = true) :
    a = b := by
  cases a with
  | mk ad =>
      cases b with
      | mk bd =>
          change Array.isEqv ad bd BEq.beq = true at h
          have hData : ad = bd := by
            apply Array.eq_of_isEqv
            simpa using h
          cases hData
          rfl

private theorem bytes_bne_false_eq
    (a b : Bytes)
    (h : (a != b) = false) :
    a = b := by
  change (!(a == b)) = false at h
  cases hEq : (a == b) with
  | false =>
      simp [hEq] at h
  | true =>
      exact bytes_beq_true_eq a b hEq

private theorem bytes_bne_true_of_ne
    (a b : Bytes)
    (h : a ≠ b) :
    (a != b) = true := by
  cases hCmp : (a != b) with
  | true => rfl
  | false =>
      exact False.elim (h (bytes_bne_false_eq a b hCmp))

/-- Executable claim-path preimage length parser from the live HTLC spend path. -/
def claimPathPreLen (pathItem : UtxoBasicV1.WitnessItem) : Nat :=
  UtxoApplyGenesisV1.parseU16le (pathItem.signature.get! 1) (pathItem.signature.get! 2)

/-- Executable claim-path preimage slicer from the live HTLC spend path. -/
def claimPathPreimage (pathItem : UtxoBasicV1.WitnessItem) : Bytes :=
  let preLen := claimPathPreLen pathItem
  pathItem.signature.extract 3 (3 + preLen)

/-- Extracted live claim-path hashlock helper:
    this is exactly the HTLC claim sub-branch between path dispatch and the
    later shared `sigItem` checks. -/
def validateHTLCClaimHashlock
    (c : CovenantGenesisV1.HtlcCovenant)
    (pathItem : UtxoBasicV1.WitnessItem) : Except String Bytes := do
  if pathItem.signature.size < 3 then
    throw "TX_ERR_PARSE"
  let preLen := claimPathPreLen pathItem
  if preLen == 0 then
    throw "TX_ERR_PARSE"
  if preLen > 256 then
    throw "TX_ERR_PARSE"
  if pathItem.signature.size != 3 + preLen then
    throw "TX_ERR_PARSE"
  if pathItem.pubkey != c.claimKeyId then
    throw "TX_ERR_SIG_INVALID"
  let preimage := claimPathPreimage pathItem
  if SHA3.sha3_256 preimage != c.hash then
    throw "TX_ERR_SIG_INVALID"
  pure c.claimKeyId

set_option maxHeartbeats 10000000

theorem validateHTLCClaimHashlock_hash_mismatch_rejects_sig_invalid
    (c : CovenantGenesisV1.HtlcCovenant)
    (pathItem : UtxoBasicV1.WitnessItem)
    (hPrePos : 0 < claimPathPreLen pathItem)
    (hPreBound : claimPathPreLen pathItem ≤ 256)
    (hSigSize : pathItem.signature.size = 3 + claimPathPreLen pathItem)
    (hClaimKey : pathItem.pubkey = c.claimKeyId)
    (hHashNe : SHA3.sha3_256 (claimPathPreimage pathItem) ≠ c.hash) :
    validateHTLCClaimHashlock c pathItem =
      .error "TX_ERR_SIG_INVALID" := by
  have hNotShort : ¬ pathItem.signature.size < 3 := by
    rw [hSigSize]
    omega
  have hPreNeZero : (claimPathPreLen pathItem == 0) = false := by
    simp [beq_iff_eq, Nat.ne_of_gt hPrePos]
  have hPreNotGt : ¬ claimPathPreLen pathItem > 256 := by
    omega
  have hSigSizeOk : (pathItem.signature.size != 3 + claimPathPreLen pathItem) = false := by
    simp [bne_iff_ne, hSigSize]
  have hClaimKeyFalse : (pathItem.pubkey != c.claimKeyId) = false := by
    rw [hClaimKey]
    exact bytes_bne_self_false c.claimKeyId
  have hHashTrue : (SHA3.sha3_256 (claimPathPreimage pathItem) != c.hash) = true := by
    exact bytes_bne_true_of_ne _ _ hHashNe
  unfold validateHTLCClaimHashlock
  simp only [Except.bind, hNotShort, hPreNeZero, hPreNotGt, hSigSizeOk, hClaimKeyFalse, hHashTrue, ite_false, ite_true]
  rfl

theorem validateHTLCClaimHashlock_ok_implies_hash_match
    (c : CovenantGenesisV1.HtlcCovenant)
    (pathItem : UtxoBasicV1.WitnessItem)
    (hPrePos : 0 < claimPathPreLen pathItem)
    (hPreBound : claimPathPreLen pathItem ≤ 256)
    (hSigSize : pathItem.signature.size = 3 + claimPathPreLen pathItem)
    (hClaimKey : pathItem.pubkey = c.claimKeyId)
    (hOk : validateHTLCClaimHashlock c pathItem = .ok c.claimKeyId) :
    SHA3.sha3_256 (claimPathPreimage pathItem) = c.hash := by
  by_contra hHashNe
  have hErr :=
    validateHTLCClaimHashlock_hash_mismatch_rejects_sig_invalid c pathItem
      hPrePos hPreBound hSigSize hClaimKey hHashNe
  rw [hErr] at hOk
  cases hOk

set_option maxHeartbeats 200000

/-- Honest assumption-boundary reduction for HTLC claim-path crypto:
    two distinct executable claim-path preimages cannot both satisfy the same
    extracted hashlock helper unless SHA3-256 collides on distinct inputs.
    This is a reduction theorem, not a cryptographic impossibility proof. -/
theorem claim_hash_collision_reduces_to_sha3_collision
    (c : CovenantGenesisV1.HtlcCovenant)
    (pathItem₁ pathItem₂ : UtxoBasicV1.WitnessItem)
    (hPrePos₁ : 0 < claimPathPreLen pathItem₁)
    (hPreBound₁ : claimPathPreLen pathItem₁ ≤ 256)
    (hSigSize₁ : pathItem₁.signature.size = 3 + claimPathPreLen pathItem₁)
    (hClaimKey₁ : pathItem₁.pubkey = c.claimKeyId)
    (hOk₁ : validateHTLCClaimHashlock c pathItem₁ = .ok c.claimKeyId)
    (hPrePos₂ : 0 < claimPathPreLen pathItem₂)
    (hPreBound₂ : claimPathPreLen pathItem₂ ≤ 256)
    (hSigSize₂ : pathItem₂.signature.size = 3 + claimPathPreLen pathItem₂)
    (hClaimKey₂ : pathItem₂.pubkey = c.claimKeyId)
    (hOk₂ : validateHTLCClaimHashlock c pathItem₂ = .ok c.claimKeyId)
    (hDistinct : claimPathPreimage pathItem₁ ≠ claimPathPreimage pathItem₂) :
    SHA3.sha3_256 (claimPathPreimage pathItem₁) =
      SHA3.sha3_256 (claimPathPreimage pathItem₂) ∧
    claimPathPreimage pathItem₁ ≠ claimPathPreimage pathItem₂ := by
  have hHash₁ :
      SHA3.sha3_256 (claimPathPreimage pathItem₁) = c.hash :=
    validateHTLCClaimHashlock_ok_implies_hash_match c pathItem₁
      hPrePos₁ hPreBound₁ hSigSize₁ hClaimKey₁ hOk₁
  have hHash₂ :
      SHA3.sha3_256 (claimPathPreimage pathItem₂) = c.hash :=
    validateHTLCClaimHashlock_ok_implies_hash_match c pathItem₂
      hPrePos₂ hPreBound₂ hSigSize₂ hClaimKey₂ hOk₂
  constructor
  · calc
      SHA3.sha3_256 (claimPathPreimage pathItem₁) = c.hash := hHash₁
      _ = SHA3.sha3_256 (claimPathPreimage pathItem₂) := hHash₂.symm
  · exact hDistinct

end HtlcSpendCryptoAssumptionBridge

end RubinFormal
