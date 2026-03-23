import RubinFormal.Types
import RubinFormal.SHA3_256
import RubinFormal.OutputDescriptorV2
import RubinFormal.UtxoBasicV1
import RubinFormal.CovenantGenesisV1

namespace RubinFormal

namespace UtxoApplyGenesisV1

open RubinFormal
open RubinFormal.UtxoBasicV1
open RubinFormal.CovenantGenesisV1

/- Pre-rotation suite constants (re-exported from CovenantGenesisV1).
   Post-rotation (Q-FORMAL-ROTATION-02/04): use `Rotation.registryLookup`. -/
def SUITE_ID_SENTINEL : Nat := CovenantGenesisV1.SUITE_ID_SENTINEL
def SUITE_ID_ML_DSA_87 : Nat := CovenantGenesisV1.SUITE_ID_ML_DSA_87

def ML_DSA_87_PUBKEY_BYTES : Nat := 2592
def ML_DSA_87_SIG_BYTES : Nat := 4627

def WITNESS_SLOTS (covType : Nat) (covData : Bytes) : Except String Nat := do
  if covType == CovenantGenesisV1.COV_TYPE_HTLC then
    pure 2
  else if covType == CovenantGenesisV1.COV_TYPE_MULTISIG then
    if covData.size < 2 then throw "TX_ERR_PARSE"
    pure (covData.get! 1).toNat
  else if covType == CovenantGenesisV1.COV_TYPE_VAULT then
    if covData.size < 34 then throw "TX_ERR_VAULT_MALFORMED"
    pure (covData.get! 33).toNat
  else
    pure 1

def lockIdOfEntry (e : UtxoEntry) : Bytes :=
  RubinFormal.OutputDescriptor.hash e.covenantType e.covenantData

def parseU16le (b0 b1 : UInt8) : Nat :=
  Wire.u16le? b0 b1

/-- **Pre-rotation scope**: rejects any `suite ≠ ML_DSA_87`.
    Post-rotation (Q-FORMAL-ROTATION-04): `suite ∉ NATIVE_SPEND_SUITES(h) → reject`. -/
def validateP2PKSpendPreSig (entry : UtxoEntry) (w : WitnessItem) (_blockHeight : Nat) : Except String Unit := do
  let suite := w.suiteId
  if suite != SUITE_ID_ML_DSA_87 then
    throw "TX_ERR_SIG_ALG_INVALID"
  if entry.covenantData.size != CovenantGenesisV1.MAX_P2PK_COVENANT_DATA then
    throw "TX_ERR_COVENANT_TYPE_INVALID"
  if (entry.covenantData.get! 0).toNat != suite then
    throw "TX_ERR_COVENANT_TYPE_INVALID"
  let keyId := entry.covenantData.extract 1 33
  if SHA3.sha3_256 w.pubkey != keyId then
    throw "TX_ERR_SIG_INVALID"
  -- crypto verify omitted (out-of-scope for formal replay)
  pure ()

/-- **Pre-rotation scope**: hardcoded ML-DSA-87 pubkey/sig bounds.
    Post-rotation (Q-FORMAL-ROTATION-02): bounds from `Rotation.registryLookup`. -/
def validateWitnessItemLengths (w : WitnessItem) (_blockHeight : Nat) : Except String Unit := do
  if w.suiteId == SUITE_ID_SENTINEL then
    if w.pubkey.size != 0 || w.signature.size != 0 then
      throw "TX_ERR_PARSE"
    pure ()
  else if w.suiteId == SUITE_ID_ML_DSA_87 then
    if w.pubkey.size != ML_DSA_87_PUBKEY_BYTES || w.signature.size = 0 || w.signature.size > ML_DSA_87_SIG_BYTES + 1 then
      throw "TX_ERR_SIG_NONCANONICAL"
    pure ()
  else
    throw "TX_ERR_SIG_ALG_INVALID"

/-- **Pre-rotation scope**: ML-DSA-87 is the only signing suite in threshold dispatch.
    Post-rotation (Q-FORMAL-ROTATION-04): `suite ∉ NATIVE_SPEND_SUITES(h) → reject`. -/
def validateThresholdSigSpendNoCrypto
    (keys : List Bytes)
    (threshold : Nat)
    (ws : List WitnessItem)
    (_blockHeight : Nat)
    (_context : String) : Except String Unit := do
  if ws.length != keys.length then
    throw "TX_ERR_PARSE"
  let mut valid : Nat := 0
  for (w, key) in List.zip ws keys do
    if w.suiteId == SUITE_ID_SENTINEL then
      pure ()
    else if w.suiteId == SUITE_ID_ML_DSA_87 then
      if SHA3.sha3_256 w.pubkey != key then
        throw "TX_ERR_SIG_INVALID"
      valid := valid + 1
    else
      throw "TX_ERR_SIG_ALG_INVALID"
  if valid < threshold then
    throw "TX_ERR_SIG_INVALID"
  pure ()

def validateHTLCSpendNoCrypto
    (entry : UtxoEntry)
    (pathItem : WitnessItem)
    (sigItem : WitnessItem)
    (blockHeight : Nat)
    (blockMtp : Nat) : Except String Unit := do
  let c ← CovenantGenesisV1.parseHtlcCovenantData entry.covenantData

  if pathItem.suiteId != SUITE_ID_SENTINEL then
    throw "TX_ERR_PARSE"
  if pathItem.pubkey.size != 32 then
    throw "TX_ERR_PARSE"
  if pathItem.signature.size < 1 then
    throw "TX_ERR_PARSE"
  let pathId := (pathItem.signature.get! 0).toNat
  let mut expectedKeyId : Bytes := ByteArray.empty
  if pathId == 0x00 then
    if pathItem.signature.size < 3 then
      throw "TX_ERR_PARSE"
    let preLen := parseU16le (pathItem.signature.get! 1) (pathItem.signature.get! 2)
    if preLen == 0 then
      throw "TX_ERR_PARSE"
    if preLen > 256 then
      throw "TX_ERR_PARSE"
    if pathItem.signature.size != 3 + preLen then
      throw "TX_ERR_PARSE"
    let pathKeyId := pathItem.pubkey
    if pathKeyId != c.claimKeyId then
      throw "TX_ERR_SIG_INVALID"
    let preimage := pathItem.signature.extract 3 (3 + preLen)
    if SHA3.sha3_256 preimage != c.hash then
      throw "TX_ERR_SIG_INVALID"
    expectedKeyId := c.claimKeyId
  else if pathId == 0x01 then
    if pathItem.signature.size != 1 then
      throw "TX_ERR_PARSE"
    let pathKeyId := pathItem.pubkey
    if pathKeyId != c.refundKeyId then
      throw "TX_ERR_SIG_INVALID"
    if c.lockMode == CovenantGenesisV1.LOCK_MODE_HEIGHT then
      if blockHeight < c.lockValue then
        throw "TX_ERR_TIMELOCK_NOT_MET"
    else
      if blockMtp < c.lockValue then
        throw "TX_ERR_TIMELOCK_NOT_MET"
    expectedKeyId := c.refundKeyId
  else
    throw "TX_ERR_PARSE"

  -- sig item structural checks + activation
  validateWitnessItemLengths sigItem blockHeight
  if SHA3.sha3_256 sigItem.pubkey != expectedKeyId then
    throw "TX_ERR_SIG_INVALID"
  -- crypto verify omitted
  pure ()

def vaultCreationOwnerAuthorized
    (owner : Bytes)
    (inputLockIds : List Bytes)
    (inputCovTypes : List Nat) : Bool :=
  (List.zip inputLockIds inputCovTypes).any (fun (lockId, covType) =>
    lockId == owner &&
      (covType == CovenantGenesisV1.COV_TYPE_P2PK ||
        covType == CovenantGenesisV1.COV_TYPE_MULTISIG))

def vaultSpendOutputAllowed
    (whitelist : List Bytes)
    (o : UtxoBasicV1.TxOut) : Bool :=
  (o.covenantType != CovenantGenesisV1.COV_TYPE_VAULT) &&
    whitelist.contains (RubinFormal.OutputDescriptor.hash o.covenantType o.covenantData)

def vaultSpendOutputsAllowed
    (whitelist : List Bytes)
    (outs : List UtxoBasicV1.TxOut) : Bool :=
  outs.all (vaultSpendOutputAllowed whitelist)

/-- Per-input structural checks from the for-loop (lines 218-220).
    LIVE sub-function: called from applyNonCoinbaseTxBasicNoCrypto per-input loop.
    Ordering: scriptSig non-empty → sequence invalid → coinbase prevout. -/
def validateInputStructural (i : UtxoBasicV1.TxIn) : Except String Unit := do
  if i.scriptSig.size != 0 then throw "TX_ERR_PARSE"
  if i.sequence > 0x7fffffff then throw "TX_ERR_SEQUENCE_INVALID"
  if UtxoBasicV1.isCoinbasePrevout i then throw "TX_ERR_PARSE"
  pure ()

/-- Post-loop witness cursor check.
    LIVE sub-function: called after per-input loop in applyNonCoinbaseTxBasicNoCrypto. -/
def validateWitnessCursorComplete (cursor witnessLen : Nat) : Except String Unit :=
  if cursor != witnessLen then Except.error "TX_ERR_PARSE" else Except.ok ()

/-- Per-input UTXO lookup and pre-covenant checks.
    LIVE sub-function: called from applyNonCoinbaseTxBasicNoCrypto per-input loop.
    Ordering: duplicate → missing UTXO → anchor/DA → coinbase maturity.
    Written without do-notation to avoid join points for formal proofs. -/
def validateInputUtxoLookup
    (isDuplicate : Bool)
    (utxoEntry : Option UtxoBasicV1.UtxoEntry)
    (height : Nat) : Except String UtxoBasicV1.UtxoEntry :=
  if isDuplicate then Except.error "TX_ERR_PARSE"
  else match utxoEntry with
    | none => Except.error "TX_ERR_MISSING_UTXO"
    | some e =>
      if e.covenantType == CovenantGenesisV1.COV_TYPE_ANCHOR ||
         e.covenantType == CovenantGenesisV1.COV_TYPE_DA_COMMIT then
        Except.error "TX_ERR_MISSING_UTXO"
      else if e.createdByCoinbase then
        if height < e.creationHeight + UtxoBasicV1.COINBASE_MATURITY then
          Except.error "TX_ERR_COINBASE_IMMATURE"
        else Except.ok e
      else Except.ok e

/-- Pre-input semantic checks: parse, nonce, output covenants.
    LIVE sub-function: applyNonCoinbaseTxBasicNoCrypto calls it directly.
    Ordering: TX_ERR_PARSE (empty inputs) → TX_ERR_TX_NONCE_INVALID →
    TX_ERR_COVENANT_TYPE_INVALID (output validation) → per-input checks. -/
def applyTxPreInputChecks
    (tx : UtxoBasicV1.Tx)
    (height : Nat) : Except String Unit := do
  if tx.inputs.length == 0 then throw "TX_ERR_PARSE"
  if tx.txNonce == 0 then throw "TX_ERR_TX_NONCE_INVALID"
  for o in tx.outputs do
    CovenantGenesisV1.validateOutGenesis
      { value := o.value, covenantType := o.covenantType, covenantData := o.covenantData }
      tx.txKind height

/-- Value conservation check. LIVE sub-function: called from
    applyNonCoinbaseTxBasicNoCrypto after output summation.
    Written without do-notation. -/
def validateValueConservation
    (sumOut sumIn : Nat)
    (vaultInputCount sumInVault : Nat) : Except String Unit :=
  if sumOut > sumIn then Except.error "TX_ERR_VALUE_CONSERVATION"
  else if vaultInputCount == 1 && sumOut < sumInVault then
    Except.error "TX_ERR_VALUE_CONSERVATION"
  else Except.ok ()

/-- Per-input covenant dispatch — parallel model of the inline if/else chain
    in `applyNonCoinbaseTxBasicNoCrypto` for-loop body (lines 308-349).
    NOT directly called from the for-loop (inline code has mutable state updates
    that this function doesn't model). Written without do-notation to enable
    formal dispatch ordering proofs. The inline code's covenant-type checks
    are structurally identical to this function's if/else chain.
    Ordering: P2PK → Multisig → Vault → HTLC → TX_ERR_COVENANT_TYPE_INVALID. -/
def dispatchCovenantValidation
    (e : UtxoBasicV1.UtxoEntry)
    (tx : UtxoBasicV1.Tx)
    (witnessCursor : Nat)
    (height blockMtp : Nat) : Except String Nat :=
  if e.covenantType == CovenantGenesisV1.COV_TYPE_P2PK then
    match WITNESS_SLOTS e.covenantType e.covenantData with
    | .error err => Except.error err
    | .ok slots =>
      if slots != 1 then Except.error "TX_ERR_PARSE"
      else if witnessCursor + slots > tx.witness.length then Except.error "TX_ERR_PARSE"
      else Except.ok (witnessCursor + 1)
  else if e.covenantType == CovenantGenesisV1.COV_TYPE_MULTISIG then
    match CovenantGenesisV1.parseMultisigCovenantData e.covenantData with
    | .error err => Except.error err
    | .ok _ =>
      match WITNESS_SLOTS e.covenantType e.covenantData with
      | .error err => Except.error err
      | .ok slots =>
        if witnessCursor + slots > tx.witness.length then Except.error "TX_ERR_PARSE"
        else Except.ok (witnessCursor + slots)
  else if e.covenantType == CovenantGenesisV1.COV_TYPE_VAULT then
    match CovenantGenesisV1.parseVaultCovenantData e.covenantData with
    | .error err => Except.error err
    | .ok _ =>
      match WITNESS_SLOTS e.covenantType e.covenantData with
      | .error err => Except.error err
      | .ok slots =>
        if witnessCursor + slots > tx.witness.length then Except.error "TX_ERR_PARSE"
        else Except.ok (witnessCursor + slots)
  else if e.covenantType == CovenantGenesisV1.COV_TYPE_HTLC then
    match CovenantGenesisV1.parseHtlcCovenantData e.covenantData with
    | .error err => Except.error err
    | .ok _ =>
      match WITNESS_SLOTS e.covenantType e.covenantData with
      | .error err => Except.error err
      | .ok slots =>
        if slots != 2 then Except.error "TX_ERR_PARSE"
        else if witnessCursor + slots > tx.witness.length then Except.error "TX_ERR_PARSE"
        else Except.ok (witnessCursor + 2)
  else
    Except.error "TX_ERR_COVENANT_TYPE_INVALID"

def applyNonCoinbaseTxBasicNoCrypto
    (txBytes : Bytes)
    (utxos : List (Outpoint × UtxoEntry))
    (height : Nat)
    (blockTimestamp : Nat)
    (blockMtp : Nat)
    (chainId : Bytes) : Except String (Nat × Nat) := do
  let _ := chainId
  let tx ← UtxoBasicV1.parseTx txBytes

  applyTxPreInputChecks tx height

  -- build lookup
  let utxoMap := UtxoBasicV1.buildUtxoMap utxos
  let mut next := utxoMap

  let mut sumIn : Nat := 0
  let mut sumInVault : Nat := 0
  let mut vaultInputCount : Nat := 0
  let mut vaultWhitelist : List Bytes := []
  let mut vaultOwnerLockId : Bytes := ByteArray.empty
  let mut vaultKeys : List Bytes := []
  let mut vaultThreshold : Nat := 0
  let mut vaultWitness : List WitnessItem := []

  let mut witnessCursor : Nat := 0
  let mut inputLockIds : List Bytes := []
  let mut inputCovTypes : List Nat := []

  let mut seen : Std.RBSet Outpoint UtxoBasicV1.cmpOutpoint := Std.RBSet.empty

  for inputIndex in [0:tx.inputs.length] do
    let i := tx.inputs.get! inputIndex
    validateInputStructural i
    let op : Outpoint := { txid := i.prevTxid, vout := i.prevVout }
    let isDup := seen.contains op
    seen := seen.insert op
    let e ← validateInputUtxoLookup isDup (next.find? op) height

    -- spend covenant structural validity (parsers)
    if e.covenantType == CovenantGenesisV1.COV_TYPE_P2PK then
      let slots ← WITNESS_SLOTS e.covenantType e.covenantData
      if slots != 1 then throw "TX_ERR_PARSE"
      if witnessCursor + slots > tx.witness.length then throw "TX_ERR_PARSE"
      let w := tx.witness.get! witnessCursor
      -- pre-signature checks only
      validateP2PKSpendPreSig e w height
      witnessCursor := witnessCursor + 1
    else if e.covenantType == CovenantGenesisV1.COV_TYPE_MULTISIG then
      let m ← CovenantGenesisV1.parseMultisigCovenantData e.covenantData
      let slots ← WITNESS_SLOTS e.covenantType e.covenantData
      if witnessCursor + slots > tx.witness.length then throw "TX_ERR_PARSE"
      let assigned := (tx.witness.drop witnessCursor).take slots
      witnessCursor := witnessCursor + slots
      validateThresholdSigSpendNoCrypto m.keys m.threshold assigned height "CORE_MULTISIG"
    else if e.covenantType == CovenantGenesisV1.COV_TYPE_VAULT then
      let v ← CovenantGenesisV1.parseVaultCovenantData e.covenantData
      let slots ← WITNESS_SLOTS e.covenantType e.covenantData
      if witnessCursor + slots > tx.witness.length then throw "TX_ERR_PARSE"
      let assigned := (tx.witness.drop witnessCursor).take slots
      witnessCursor := witnessCursor + slots
      vaultInputCount := vaultInputCount + 1
      if vaultInputCount > 1 then
        throw "TX_ERR_VAULT_MULTI_INPUT_FORBIDDEN"
      sumInVault := sumInVault + e.value
      vaultWhitelist := v.whitelist
      vaultOwnerLockId := v.ownerLockId
      vaultKeys := v.keys
      vaultThreshold := v.threshold
      vaultWitness := assigned
    else if e.covenantType == CovenantGenesisV1.COV_TYPE_HTLC then
      let _ ← CovenantGenesisV1.parseHtlcCovenantData e.covenantData
      let slots ← WITNESS_SLOTS e.covenantType e.covenantData
      if slots != 2 then throw "TX_ERR_PARSE"
      if witnessCursor + slots > tx.witness.length then throw "TX_ERR_PARSE"
      let pathItem := tx.witness.get! witnessCursor
      let sigItem := tx.witness.get! (witnessCursor + 1)
      witnessCursor := witnessCursor + 2
      validateHTLCSpendNoCrypto e pathItem sigItem height blockMtp
    else
      -- unsupported covenant in basic apply path
      throw "TX_ERR_COVENANT_TYPE_INVALID"

    let lid := lockIdOfEntry e
    inputLockIds := inputLockIds.concat lid
    inputCovTypes := inputCovTypes.concat e.covenantType
    sumIn := sumIn + e.value
    next := next.erase op

  validateWitnessCursorComplete witnessCursor tx.witness.length

  -- outputs: add to UTXO (excluding non-spendable)
  let mut sumOut : Nat := 0
  let mut createsVault : Bool := false
  for o in tx.outputs do
    sumOut := sumOut + o.value
    if o.covenantType == CovenantGenesisV1.COV_TYPE_VAULT then
      createsVault := true
  let txid := SHA3.sha3_256 txBytes
  for outIndex in [0:tx.outputs.length] do
    let oo := tx.outputs.get! outIndex
    if oo.covenantType == CovenantGenesisV1.COV_TYPE_ANCHOR || oo.covenantType == CovenantGenesisV1.COV_TYPE_DA_COMMIT then
      continue
    let op2 : Outpoint := { txid := txid, vout := outIndex }
    next := next.insert op2 { value := oo.value, covenantType := oo.covenantType, covenantData := oo.covenantData, creationHeight := height, createdByCoinbase := false }

  -- CORE_VAULT creation requires owner-authorized input (lock_id match + type P2PK/MULTISIG).
  if createsVault then
    for o in tx.outputs do
      if o.covenantType != CovenantGenesisV1.COV_TYPE_VAULT then
        continue
      let v ← CovenantGenesisV1.parseVaultCovenantData o.covenantData
      let owner := v.ownerLockId
      if !vaultCreationOwnerAuthorized owner inputLockIds inputCovTypes then
        throw "TX_ERR_VAULT_OWNER_AUTH_REQUIRED"

  -- CORE_VAULT spend rules (safe-only model).
  if vaultInputCount == 1 then
    let mut ownerAuthPresent : Bool := false
    for lid in inputLockIds do
      if lid == vaultOwnerLockId then ownerAuthPresent := true
    if !ownerAuthPresent then
      throw "TX_ERR_VAULT_OWNER_AUTH_REQUIRED"
    for idx in [0:inputCovTypes.length] do
      let cov := inputCovTypes.get! idx
      if cov == CovenantGenesisV1.COV_TYPE_VAULT then
        continue
      if inputLockIds.get! idx != vaultOwnerLockId then
        throw "TX_ERR_VAULT_FEE_SPONSOR_FORBIDDEN"
    validateThresholdSigSpendNoCrypto vaultKeys vaultThreshold vaultWitness height "CORE_VAULT"
    if !vaultSpendOutputsAllowed vaultWhitelist tx.outputs then
      throw "TX_ERR_VAULT_OUTPUT_NOT_WHITELISTED"

  validateValueConservation sumOut sumIn vaultInputCount sumInVault

  let fee := sumIn - sumOut
  pure (fee, next.size)

private def repeatByte (b : UInt8) (n : Nat) : Bytes :=
  Id.run <| do
    let mut out := ByteArray.empty
    for _ in [0:n] do
      out := out.push b
    pure out

private def byte32 (n : Nat) : Bytes :=
  repeatByte (UInt8.ofNat n) 32

private def sampleOwnerP2PKKeyId : Bytes :=
  byte32 0x41

private def sampleOwnerP2PKData : Bytes :=
  RubinFormal.bytes #[UInt8.ofNat SUITE_ID_ML_DSA_87] ++ sampleOwnerP2PKKeyId

private def sampleOwnerP2PKLockId : Bytes :=
  RubinFormal.OutputDescriptor.hash CovenantGenesisV1.COV_TYPE_P2PK sampleOwnerP2PKData

private def sampleOwnerMultisigKey : Bytes :=
  byte32 0x52

private def sampleOwnerMultisigData : Bytes :=
  RubinFormal.bytes #[UInt8.ofNat 0x01, UInt8.ofNat 0x01] ++ sampleOwnerMultisigKey

private def sampleOwnerMultisigLockId : Bytes :=
  RubinFormal.OutputDescriptor.hash CovenantGenesisV1.COV_TYPE_MULTISIG sampleOwnerMultisigData

private def sampleSpendOutput1 : UtxoBasicV1.TxOut :=
  { value := 10, covenantType := CovenantGenesisV1.COV_TYPE_P2PK, covenantData := sampleOwnerP2PKData }

private def sampleSpendOutput2 : UtxoBasicV1.TxOut :=
  { value := 20, covenantType := CovenantGenesisV1.COV_TYPE_MULTISIG, covenantData := sampleOwnerMultisigData }

private def sampleSpendWhitelist : List Bytes :=
  [
    RubinFormal.OutputDescriptor.hash sampleSpendOutput1.covenantType sampleSpendOutput1.covenantData,
    RubinFormal.OutputDescriptor.hash sampleSpendOutput2.covenantType sampleSpendOutput2.covenantData
  ]

private def sampleRecursiveVaultOutput : UtxoBasicV1.TxOut :=
  { value := 30, covenantType := CovenantGenesisV1.COV_TYPE_VAULT, covenantData := byte32 0x63 }

theorem creation_owner_auth_p2pk_or_multisig :
    vaultCreationOwnerAuthorized sampleOwnerP2PKLockId [sampleOwnerP2PKLockId] [CovenantGenesisV1.COV_TYPE_P2PK] = true ∧
      vaultCreationOwnerAuthorized sampleOwnerMultisigLockId [sampleOwnerMultisigLockId] [CovenantGenesisV1.COV_TYPE_MULTISIG] = true := by
  native_decide

theorem output_whitelist_closure :
    vaultSpendOutputsAllowed sampleSpendWhitelist [sampleSpendOutput1, sampleSpendOutput2] = true := by
  native_decide

theorem vault_recursion_ban :
    vaultSpendOutputsAllowed sampleSpendWhitelist [sampleSpendOutput1, sampleRecursiveVaultOutput] = false := by
  native_decide

end UtxoApplyGenesisV1

end RubinFormal
