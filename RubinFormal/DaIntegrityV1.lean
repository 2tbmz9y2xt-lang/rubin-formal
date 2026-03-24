import RubinFormal.Types
import RubinFormal.SHA3_256
import RubinFormal.ByteWireV2
import RubinFormal.TxWeightV2
import RubinFormal.DaCoreV1
import RubinFormal.BlockBasicV1

namespace RubinFormal

open Wire

namespace DaIntegrityV1

def MAX_DA_MANIFEST_BYTES_PER_TX : Nat := RubinFormal.DaCoreV1.MAX_DA_MANIFEST_BYTES_PER_TX
def CHUNK_BYTES : Nat := RubinFormal.DaCoreV1.CHUNK_BYTES
def MAX_DA_CHUNK_COUNT : Nat := RubinFormal.DaCoreV1.MAX_DA_CHUNK_COUNT
def MAX_DA_BATCHES_PER_BLOCK : Nat := 128

def COV_TYPE_DA_COMMIT : Nat := 0x0103

def cmpBytes (a b : Bytes) : Ordering :=
  let rec go (xs ys : List UInt8) : Ordering :=
    match xs, ys with
    | [], [] => .eq
    | [], _ => .lt
    | _, [] => .gt
    | x :: xs', y :: ys' =>
        if x < y then .lt else if x > y then .gt else go xs' ys'
  go a.data.toList b.data.toList

structure TxOut where
  covenantType : Nat
  covenantData : Bytes
deriving Repr, DecidableEq

structure DaCommitInfo where
  chunkCount : Nat
  outputs : List TxOut
deriving Repr, DecidableEq

structure DaChunkInfo where
  chunkIndex : Nat
  chunkHash : Bytes
  payload : Bytes
deriving Repr, DecidableEq

structure ParsedDATx where
  txKind : Nat
  commitDaId : Option Bytes
  commitChunkCount : Option Nat
  chunkDaId : Option Bytes
  chunkIndex : Option Nat
  chunkHash : Option Bytes
  outputs : List TxOut
  payload : Bytes
deriving Repr, DecidableEq

def requireMinimal (minimal : Bool) : Option Unit :=
  if minimal then some () else none

def parseOutputsLite (c : Cursor) (n : Nat) : Option (List TxOut × Cursor) := do
  let mut cur := c
  let mut outs : List TxOut := []
  for _ in [0:n] do
    let (_, cur1) ← cur.getBytes? 8
    let (ctRaw, cur2) ← cur1.getBytes? 2
    let covenantType := Wire.u16le? (ctRaw.get! 0) (ctRaw.get! 1)
    let (cdLen, cur3, minimal) ← cur2.getCompactSize?
    let _ ← requireMinimal minimal
    let (cd, cur4) ← cur3.getBytes? cdLen
    outs := outs.concat { covenantType := covenantType, covenantData := cd }
    cur := cur4
  pure (outs, cur)

def parseDaCommitCore (c : Cursor) : Option (Bytes × Nat × Cursor) := do
  let (daId, c1) ← c.getBytes? 32
  let (ccRaw, c2) ← c1.getBytes? 2
  let chunkCount := Wire.u16le? (ccRaw.get! 0) (ccRaw.get! 1)
  if chunkCount < 1 || chunkCount > MAX_DA_CHUNK_COUNT then
    none
  let (_, c3) ← c2.getBytes? 32
  let (_, c4) ← c3.getBytes? 8
  let (_, c5) ← c4.getBytes? 32
  let (_, c6) ← c5.getBytes? 32
  let (_, c7) ← c6.getBytes? 32
  let (_, c8) ← c7.getBytes? 1
  let (sigLen, c9, minimal) ← c8.getCompactSize?
  let _ ← requireMinimal minimal
  if sigLen > MAX_DA_MANIFEST_BYTES_PER_TX then
    none
  let (_, c10) ← c9.getBytes? sigLen
  pure (daId, chunkCount, c10)

def parseDaChunkCore (c : Cursor) : Option (Bytes × Nat × Bytes × Cursor) := do
  let (daId, c1) ← c.getBytes? 32
  let (idxRaw, c2) ← c1.getBytes? 2
  let idx := Wire.u16le? (idxRaw.get! 0) (idxRaw.get! 1)
  let (h, c3) ← c2.getBytes? 32
  pure (daId, idx, h, c3)

def parseDATx (tx : Bytes) : Except String ParsedDATx := do
  let c0 : Cursor := { bs := tx, off := 0 }
  let (_, c1) ←
    match c0.getU32le? with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  let (tkB, c2) ←
    match c1.getU8? with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  let tk := tkB.toNat
  if !(tk == 0x00 || tk == 0x01 || tk == 0x02) then throw "TX_ERR_PARSE"
  let (_, c3) ←
    match c2.getU64le? with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  let (inCount, c4, minIn) ←
    match c3.getCompactSize? with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  if !minIn then throw "TX_ERR_PARSE"
  let c5 ←
    match RubinFormal.TxWeightV2.parseInputsSkip c4 inCount with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  let (outCount, c6, minOut) ←
    match c5.getCompactSize? with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  if !minOut then throw "TX_ERR_PARSE"
  let (outs, c7) ←
    match parseOutputsLite c6 outCount with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  let (_, c8) ←
    match c7.getU32le? with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x

  let mut commitDaId : Option Bytes := none
  let mut commitChunkCount : Option Nat := none
  let mut chunkDaId : Option Bytes := none
  let mut chunkIndex : Option Nat := none
  let mut chunkHash : Option Bytes := none
  let c9 ←
    if tk == 0x00 then
      pure c8
    else if tk == 0x01 then
      match parseDaCommitCore c8 with
      | none => throw "TX_ERR_PARSE"
      | some (daId, cc, c') =>
          commitDaId := some daId
          commitChunkCount := some cc
          pure c'
    else
      match parseDaChunkCore c8 with
      | none => throw "TX_ERR_PARSE"
      | some (daId, idx, h, c') =>
          chunkDaId := some daId
          chunkIndex := some idx
          chunkHash := some h
          pure c'

  let ws ←
    match RubinFormal.TxWeightV2.parseWitnessSectionForWeight c9 with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  let witBytes := ws.endOff - ws.startOff
  if witBytes > RubinFormal.TxWeightV2.MAX_WITNESS_BYTES_PER_TX then throw "TX_ERR_WITNESS_OVERFLOW"
  if ws.isOverflow then throw "TX_ERR_WITNESS_OVERFLOW"
  if ws.anySigAlgInvalid then throw "TX_ERR_SIG_ALG_INVALID"
  if ws.anySigNoncanonical then throw "TX_ERR_SIG_NONCANONICAL"

  let (daLen, c10, minDa) ←
    match ws.cursor.getCompactSize? with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  if !minDa then throw "TX_ERR_PARSE"
  if tk == 0x00 then
    if daLen != 0 then throw "TX_ERR_PARSE"
  else if tk == 0x01 then
    if daLen > MAX_DA_MANIFEST_BYTES_PER_TX then throw "TX_ERR_PARSE"
  else
    if daLen < 1 || daLen > CHUNK_BYTES then throw "TX_ERR_PARSE"
  let (payload, c11) ←
    match c10.getBytes? daLen with
    | none => throw "TX_ERR_PARSE"
    | some x => pure x
  if c11.off != tx.size then
    throw "TX_ERR_PARSE"

  pure {
    txKind := tk
    commitDaId := commitDaId
    commitChunkCount := commitChunkCount
    chunkDaId := chunkDaId
    chunkIndex := chunkIndex
    chunkHash := chunkHash
    outputs := outs
    payload := payload
  }

/-- Batch count limit check. LIVE sub-function (line 226-227). -/
def validateDaBatchCount (commitCount : Nat) : Except String Unit :=
  if commitCount > MAX_DA_BATCHES_PER_BLOCK then
    Except.error "BLOCK_ERR_DA_BATCH_EXCEEDED"
  else Except.ok ()

/-- Orphan chunk check: every chunk daId must have a commit. LIVE sub-function (line 229-231).
    Recursive version for formal proof access. -/
def validateNoOrphanChunks
    (chunkList : List (Bytes × Std.RBMap Nat DaChunkInfo compare))
    (commits : Std.RBMap Bytes DaCommitInfo cmpBytes) : Except String Unit :=
  match chunkList with
  | [] => .ok ()
  | (daId, _) :: rest =>
    if !(commits.contains daId) then .error "BLOCK_ERR_DA_SET_INVALID"
    else validateNoOrphanChunks rest commits

/-- Chunk hash verification: sha3(payload) must match embedded hash. LIVE sub-function (line 219-220). -/
def validateChunkHash (payload hash : Bytes) : Except String Unit :=
  if SHA3.sha3_256 payload != hash then
    Except.error "BLOCK_ERR_DA_CHUNK_HASH_INVALID"
  else Except.ok ()

/-- Duplicate commit check: daId already in commits map → BLOCK_ERR_DA_SET_INVALID.
    LIVE sub-function (line 233). Written without do for formal proof access. -/
def validateNoDuplicateCommit
    (commits : Std.RBMap Bytes DaCommitInfo cmpBytes) (daId : Bytes) : Except String Unit :=
  if commits.contains daId then Except.error "BLOCK_ERR_DA_SET_INVALID"
  else Except.ok ()

/-- Duplicate chunk index check: idx already in set → BLOCK_ERR_DA_SET_INVALID.
    LIVE sub-function (line 242). Written without do for formal proof access. -/
def validateNoDuplicateChunk
    (set : Std.RBMap Nat DaChunkInfo compare) (idx : Nat) : Except String Unit :=
  if set.contains idx then Except.error "BLOCK_ERR_DA_SET_INVALID"
  else Except.ok ()

/-- Count DA_COMMIT outputs and extract the single commit hash.
    Returns (count, hash_or_empty). Pure function for proof access. -/
def countDaCommitOutputs (outputs : List TxOut) : Nat × Bytes :=
  outputs.foldl (fun (acc : Nat × Bytes) o =>
    if o.covenantType == COV_TYPE_DA_COMMIT then
      let count := acc.1 + 1
      let got := if o.covenantData.size == 32 then o.covenantData else acc.2
      (count, got)
    else acc
  ) (0, ByteArray.empty)

/-- Validate commit output: exactly 1 DA_COMMIT output with matching hash.
    LIVE sub-function (lines 293-303). Written without do for formal proof access. -/
def validateCommitOutput (outputs : List TxOut) (payloadCommit : Bytes)
    : Except String Unit :=
  let (count, got) := countDaCommitOutputs outputs
  if count != 1 then Except.error "BLOCK_ERR_DA_PAYLOAD_COMMIT_INVALID"
  else if got != payloadCommit then Except.error "BLOCK_ERR_DA_PAYLOAD_COMMIT_INVALID"
  else Except.ok ()

/-- Validate chunk count matches commit declaration.
    LIVE sub-function (lines 284-285). Written without do for formal proof access. -/
def validateChunkCountMatch (setSize chunkCount : Nat) : Except String Unit :=
  if setSize != chunkCount then Except.error "BLOCK_ERR_DA_INCOMPLETE"
  else Except.ok ()

/-- Collect and concatenate chunk payloads in index order [start..start+count).
    Returns error if any index missing. LIVE sub-function (lines 287-295).
    Recursive version (no foldlM/List.range) for full formal proof access. -/
def collectChunkPayloads
    (set : Std.RBMap Nat DaChunkInfo compare) (count : Nat)
    (acc : Bytes := ByteArray.empty) (start : Nat := 0)
    : Except String Bytes :=
  match count with
  | 0 => .ok acc
  | n + 1 =>
    match set.find? start with
    | none => .error "BLOCK_ERR_DA_INCOMPLETE"
    | some ch => collectChunkPayloads set n (acc ++ ch.payload) (start + 1)

/-- Process one commit tx: extract daId, chunkCount, check duplicate.
    LIVE sub-function of accumulateDATxs commit branch. -/
def processCommitTx
    (t : ParsedDATx)
    (commits : Std.RBMap Bytes DaCommitInfo cmpBytes)
    : Except String (Std.RBMap Bytes DaCommitInfo cmpBytes) :=
  match t.commitDaId with
  | none => .error "TX_ERR_PARSE"
  | some daId =>
    match t.commitChunkCount with
    | none => .error "TX_ERR_PARSE"
    | some cc =>
      match validateNoDuplicateCommit commits daId with
      | .error e => .error e
      | .ok () => .ok (commits.insert daId { chunkCount := cc, outputs := t.outputs })

/-- Process one chunk tx: extract daId, index, hash, verify, check duplicate.
    LIVE sub-function of accumulateDATxs chunk branch. -/
def processChunkTx
    (t : ParsedDATx)
    (chunks : Std.RBMap Bytes (Std.RBMap Nat DaChunkInfo compare) cmpBytes)
    : Except String (Std.RBMap Bytes (Std.RBMap Nat DaChunkInfo compare) cmpBytes) :=
  match t.chunkDaId with
  | none => .error "TX_ERR_PARSE"
  | some daId =>
    match t.chunkIndex with
    | none => .error "TX_ERR_PARSE"
    | some idx =>
      match t.chunkHash with
      | none => .error "TX_ERR_PARSE"
      | some h =>
        match validateChunkHash t.payload h with
        | .error e => .error e
        | .ok () =>
          let set := match chunks.find? daId with | none => Std.RBMap.empty | some m => m
          match validateNoDuplicateChunk set idx with
          | .error e => .error e
          | .ok () => .ok (chunks.insert daId (set.insert idx { chunkIndex := idx, chunkHash := h, payload := t.payload }))

/-- Accumulate DA txs using decomposed processCommitTx / processChunkTx.
    Each branch delegates to the corresponding sub-function, enabling
    formal error propagation proofs at the sub-function level. -/
def accumulateDATxs
    (txs : List Bytes)
    (commits : Std.RBMap Bytes DaCommitInfo cmpBytes)
    (chunks : Std.RBMap Bytes (Std.RBMap Nat DaChunkInfo compare) cmpBytes)
    : Except String (Std.RBMap Bytes DaCommitInfo cmpBytes ×
                      Std.RBMap Bytes (Std.RBMap Nat DaChunkInfo compare) cmpBytes) :=
  match txs with
  | [] => .ok (commits, chunks)
  | txBytes :: rest =>
    match parseDATx txBytes with
    | .error e => .error e
    | .ok t =>
      if t.txKind == 0x01 then
        match processCommitTx t commits with
        | .error e => .error e
        | .ok newCommits => accumulateDATxs rest newCommits chunks
      else if t.txKind == 0x02 then
        match processChunkTx t chunks with
        | .error e => .error e
        | .ok newChunks => accumulateDATxs rest commits newChunks
      else
        accumulateDATxs rest commits chunks

/-- Verify loop: check per-commit integrity for each commit.
    Recursive version for formal proof access. -/
def verifyCommitIntegrity
    (commitList : List (Bytes × DaCommitInfo))
    (chunks : Std.RBMap Bytes (Std.RBMap Nat DaChunkInfo compare) cmpBytes)
    : Except String Unit :=
  match commitList with
  | [] => .ok ()
  | (daId, cinfo) :: rest =>
    match chunks.find? daId with
    | none => .error "BLOCK_ERR_DA_INCOMPLETE"
    | some set =>
      match validateChunkCountMatch set.size cinfo.chunkCount with
      | .error e => .error e
      | .ok () =>
        match collectChunkPayloads set cinfo.chunkCount with
        | .error e => .error e
        | .ok concat =>
          let payloadCommit := SHA3.sha3_256 concat
          match validateCommitOutput cinfo.outputs payloadCommit with
          | .error e => .error e
          | .ok () => verifyCommitIntegrity rest chunks

/-- Full DA set integrity validation. Composed from recursive sub-functions.
    No do-notation for full formal proof access. -/
def validateDASetIntegrity (txs : List Bytes) : Except String Unit :=
  match accumulateDATxs txs Std.RBMap.empty Std.RBMap.empty with
  | .error e => .error e
  | .ok (commits, chunks) =>
    match validateDaBatchCount commits.size with
    | .error e => .error e
    | .ok () =>
      match validateNoOrphanChunks chunks.toList commits with
      | .error e => .error e
      | .ok () => verifyCommitIntegrity commits.toList chunks

def validateDaIntegrityGate
    (blockBytes : Bytes)
    (expectedPrevHash : Option Bytes)
    (expectedTarget : Option Bytes) : Except String Unit := do
  BlockBasicV1.validateBlockBasic blockBytes expectedPrevHash expectedTarget
  let pb ← BlockBasicV1.parseBlock blockBytes
  validateDASetIntegrity pb.txs

end DaIntegrityV1

end RubinFormal
