import Examples.BytesStoreLite.FullSetChunkOldLongReturn
import Examples.BytesStoreLite.StorageReadbackFacts
import Examples.BytesStoreLite.StorageLoopFacts

/-!
# BytesStoreLite — `setMapped(uint256,bytes)` runtime slice

This module starts the full-contract `setMapped(uint256,bytes)` selector arm.  The ABI
shape matches `setChunk(uint256,bytes)`, while the storage target is the mapping value at
`keccak256(key, 4)`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace BytesStoreLite

def bytesStoreLiteSetMappedKeyWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def bytesStoreLiteSetMappedValueBytes (I : ExecutionEnv) : ByteArray :=
  bytesStoreLiteSetChunkValueBytes I

def bytesStoreLiteSetMappedLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "key"
    (.int (Int.ofNat (bytesStoreLiteSetMappedKeyWord I).toNat))).insert "value"
    (.bytes (bytesStoreLiteSetMappedValueBytes I)))

def bytesStoreLiteSetMappedLocalsOf (key : UInt256) (value : ByteArray) : Store :=
  ((∅ : Store).insert "key" (.int (Int.ofNat key.toNat))).insert "value" (.bytes value)

def bytesStoreLiteSetMappedFrameOf (key : UInt256) (value : ByteArray) : Frame :=
  { contract := bytesStoreLiteContract,
    locals := bytesStoreLiteSetMappedLocalsOf key value }

def bytesStoreLiteSetMappedRefOf (key : UInt256) : EvaledStorageRef :=
  { base := "mapped", steps := [.mindex (.int (Int.ofNat key.toNat))] }

def bytesStoreLiteSetMappedRef (I : ExecutionEnv) : EvaledStorageRef :=
  bytesStoreLiteSetMappedRefOf (bytesStoreLiteSetMappedKeyWord I)

def bytesStoreLiteSetMappedSlotOf (key : UInt256) : UInt256 :=
  mappedValueSlot (.int (Int.ofNat key.toNat))

def bytesStoreLiteSetMappedSlot (I : ExecutionEnv) : UInt256 :=
  bytesStoreLiteSetMappedSlotOf (bytesStoreLiteSetMappedKeyWord I)

theorem accountMapEquiv_setMappedHeaderStore {σ : AccountMap} {evm : EVM.State}
    (I : ExecutionEnv) (owner : AccountAddress) (header : UInt256)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
  accountMapEquiv
      (sstoreAccountMap owner σ (bytesStoreLiteSetMappedSlot I) header)
      (Solm.EVM.storageStore evm owner (bytesStoreLiteSetMappedSlot I) header).accountMap := by
  exact accountMapEquiv_bytesHeaderStore owner (bytesStoreLiteSetMappedSlot I) header hAccounts

theorem bytesStoreLiteSetMappedRefOf_length_slot (evm : EVM.State) (key : UInt256) :
    ∃ loc, bytesStoreLiteLayout
        { bytesStoreLiteSetMappedRefOf key with
          steps := (bytesStoreLiteSetMappedRefOf key).steps ++ [.length] } evm =
          some loc ∧
        loc.slot = bytesStoreLiteSetMappedSlotOf key := by
  refine ⟨bytesLikeLengthLoc (bytesStoreLiteSetMappedSlotOf key) evm, ?_, ?_⟩
  · simp [bytesStoreLiteLayout, bytesStoreLiteSetMappedRefOf, bytesStoreLiteSetMappedSlotOf]
  · simp [bytesLikeLengthLoc]

theorem bytesStoreLiteSetMappedRef_length_slot (evm : EVM.State) (I : ExecutionEnv) :
    ∃ loc, bytesStoreLiteLayout
        { bytesStoreLiteSetMappedRef I with
          steps := (bytesStoreLiteSetMappedRef I).steps ++ [.length] } evm =
          some loc ∧
        loc.slot = bytesStoreLiteSetMappedSlot I := by
  exact bytesStoreLiteSetMappedRefOf_length_slot evm (bytesStoreLiteSetMappedKeyWord I)

def bytesStoreLiteSetMappedHeaderWordOf (σ : AccountMap) (I : ExecutionEnv)
    (key : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreLiteSetMappedSlotOf key) ⟨0⟩)

def bytesStoreLiteSetMappedHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  bytesStoreLiteSetMappedHeaderWordOf σ I (bytesStoreLiteSetMappedKeyWord I)

theorem bytesStoreLiteSetMappedHeaderWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreLiteSetMappedHeaderWord σ_evm I =
      bytesStoreLiteSetMappedHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner
    (bytesStoreLiteSetMappedSlot I) ⟨0⟩

theorem bytesStoreLiteStorageLoadSetMappedHeader_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreLiteSetMappedSlot I) =
      bytesStoreLiteSetMappedHeaderWord σ_evm I := by
  simpa [bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf] using
    bytesStoreLiteStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreLiteSetMappedSlot I) hAccounts

def bytesStoreLiteSetMappedShortStoredWord (I : ExecutionEnv)
    (len payloadStart : UInt256) : UInt256 :=
  bytesStoreLiteSetChunkShortStoredWord I len payloadStart

theorem bytesStoreLiteSetMappedSlotHash (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          ((twoWordHashMem (bytesStoreLiteSetMappedKeyWord I) ⟨4⟩ solcFreePtrMem).readWithPadding 0 64))) =
      bytesStoreLiteSetMappedSlot I := by
  rw [twoWordHashMem_read0_64 (bytesStoreLiteSetMappedKeyWord I) ⟨4⟩ solcFreePtrMem_size]
  unfold bytesStoreLiteSetMappedSlot bytesStoreLiteSetMappedSlotOf mappedValueSlot
  rw [keyValueToWord_uint256]
  exact mappingSlot_single (bytesStoreLiteSetMappedKeyWord I) ⟨4⟩

theorem bytesStoreLiteSetMappedValueBytes_toList {I : ExecutionEnv} :
    (bytesStoreLiteSetMappedValueBytes I).toList =
      (((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat) := by
  simpa [bytesStoreLiteSetMappedValueBytes] using
    (bytesStoreLiteSetChunkValueBytes_toList (I := I))

theorem bytesStoreLiteSetMappedValueBytes_size {I : ExecutionEnv}
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    (bytesStoreLiteSetMappedValueBytes I).size =
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat := by
  simpa [bytesStoreLiteSetMappedValueBytes] using
    (bytesStoreLiteSetChunkValueBytes_size (I := I) hpayload)

theorem bytesStoreLiteSetMappedResolve {evm : EVM.State}
    {key : UInt256} {value : ByteArray} :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetMappedFrameOf key value) evm (mappedRef (.var "key")) =
        .ok (bytesStoreLiteSetMappedRefOf key, .bytes) := by
  have hgetKey :
      (bytesStoreLiteSetMappedLocalsOf key value)["key"]? =
        some (.int (Int.ofNat key.toNat)) := by
    have h :
        (bytesStoreLiteSetMappedLocalsOf key value).get? "key" =
          some (.int (Int.ofNat key.toNat)) := by
      unfold bytesStoreLiteSetMappedLocalsOf
      rw [store_get_ne]
      · exact store_get_self (∅ : Store) "key" (.int (Int.ofNat key.toNat))
      · native_decide
    simpa [Std.HashMap.get?_eq_getElem?] using h
  have hgetMapped :
      (bytesStoreLiteSetMappedLocalsOf key value)["mapped"]? = none := by
    have h :
        (bytesStoreLiteSetMappedLocalsOf key value).get? "mapped" = none := by
      unfold bytesStoreLiteSetMappedLocalsOf
      rw [store_get_ne]
      · rw [store_get_ne]
        · simp
        · native_decide
      · native_decide
    simpa [Std.HashMap.get?_eq_getElem?] using h
  have hgetMappedRaw :
      (bytesStoreLiteSetMappedLocalsOf key value).get? "mapped" = none := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetMapped
  have her :
      evalStorageRef bytesStoreLiteConfig
        (bytesStoreLiteSetMappedFrameOf key value) evm (mappedRef (.var "key")) =
          .ok (bytesStoreLiteSetMappedRefOf key) := by
    exact evalStorageRef_mindex_var_of_get?
      (base := "mapped")
      (hget := by simpa [Std.HashMap.get?_eq_getElem?] using hgetKey)
      (hkey := by simp [valueToKey?])
  exact resolveStorageRef?_ok hgetMappedRaw her (by
    simp [bytesStoreLiteSetMappedFrameOf, bytesStoreLiteSetMappedRefOf, storageTypeAt?,
      bytesStoreLiteContract, storageDecls, bytesSt, uint256Int, storageTypeStep?])

theorem bytesStoreLiteSetMappedAssign {evm evm' : EVM.State}
    {key : UInt256} {value : ByteArray}
    (hwrite :
      writeStorage? bytesStoreLiteConfig evm
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evm') :
    assignStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetMappedFrameOf key value)
      evm .storage (mappedRef (.var "key")) (.bytes value) =
        .ok (bytesStoreLiteSetMappedFrameOf key value, evm') := by
  have hresolve :=
    bytesStoreLiteSetMappedResolve (evm := evm) (key := key) (value := value)
  exact assignStorageRef_storage_bytes_ok_of_write hresolve hwrite

theorem bytesStoreLiteSetMappedLengthAfterWrite {evm : EVM.State}
    {key : UInt256} {value : ByteArray} {n : Nat}
    (hlen :
      readStorageBytesLength? bytesStoreLiteConfig evm
        (bytesStoreLiteSetMappedRefOf key) = .ok n) :
    evalExpr? bytesStoreLiteConfig
      (bytesStoreLiteSetMappedFrameOf key value)
      evm (.arrayLength .storage (mappedRef (.var "key"))) =
        .ok (.int n) := by
  have hresolve :=
    bytesStoreLiteSetMappedResolve (evm := evm) (key := key) (value := value)
  rw [evalExpr?]
  rw [hresolve]
  simp [readStorageArrayLength?, hlen, EvalResult.bind, bind, pure]

theorem bytesStoreLiteSetMappedBodyReturnsOfWrite {evm evm' : EVM.State}
    {key : UInt256} {value : ByteArray} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite :
      writeStorage? bytesStoreLiteConfig evm
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evm')
    (hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evm'
        (bytesStoreLiteSetMappedRefOf key) = .ok n) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetMappedLocalsOf key value)
      setMappedTransition.body
      (.returned (bytesStoreLiteSetMappedFrameOf key value)
        evm' (some (.int n))) := by
  let solm0 := bytesStoreLiteSetMappedFrameOf key value
  have hvalue : evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreLiteSetMappedLocalsOf key value).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreLiteSetMappedLocalsOf
      exact store_get_self ((∅ : Store).insert "key"
        (.int (Int.ofNat key.toNat))) "value" (.bytes value)
    exact evalExpr_var_of_get? (by simpa [solm0, bytesStoreLiteSetMappedFrameOf] using hlookup)
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm0 evm .storage
        (mappedRef (.var "key")) (.bytes value) =
          .ok (solm0, evm') := by
    simpa [solm0] using
      bytesStoreLiteSetMappedAssign
        (evm := evm) (evm' := evm') (key := key) (value := value) hwrite
  have hret :
      evalExpr? bytesStoreLiteConfig solm0 evm'
        (.arrayLength .storage (mappedRef (.var "key"))) =
          .ok (.int n) := by
    simpa [solm0] using
      bytesStoreLiteSetMappedLengthAfterWrite
        (evm := evm') (key := key) (value := value) hlenMapped
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreLiteSetMappedBodyRevertsOfWrite {evm : EVM.State}
    {key : UInt256} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite :
      writeStorage? bytesStoreLiteConfig evm
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetMappedLocalsOf key value)
      setMappedTransition.body .reverted := by
  let solm0 := bytesStoreLiteSetMappedFrameOf key value
  have hvalue : evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreLiteSetMappedLocalsOf key value).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreLiteSetMappedLocalsOf
      exact store_get_self ((∅ : Store).insert "key"
        (.int (Int.ofNat key.toNat))) "value" (.bytes value)
    exact evalExpr_var_of_get? (by simpa [solm0, bytesStoreLiteSetMappedFrameOf] using hlookup)
  have hresolve :=
    bytesStoreLiteSetMappedResolve (evm := evm) (key := key) (value := value)
  have hresolve0 :
      resolveStorageRef? bytesStoreLiteConfig solm0 evm
        (mappedRef (.var "key")) =
          .ok (bytesStoreLiteSetMappedRefOf key, .bytes) := by
    simpa [solm0] using hresolve
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm0 evm .storage
        (mappedRef (.var "key")) (.bytes value) = .revert := by
    exact assignStorageRef_storage_bytes_revert_of_write hresolve0 hwrite
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteSetMappedWriteEmptyOldShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreLiteSetMappedSlot I) ⟨0⟩
    writeStorage? bytesStoreLiteConfig evmSolm0
      (bytesStoreLiteSetMappedRef I) .bytes
      (.bytes (bytesStoreLiteSetMappedValueBytes I)) = .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize0 : (bytesStoreLiteSetMappedValueBytes I).size = 0 := by
    rw [bytesStoreLiteSetMappedValueBytes_size hpayload, hlenZero]
    rfl
  have hvalueEmpty : bytesStoreLiteSetMappedValueBytes I = ByteArray.empty :=
    byteArray_eq_empty_of_size_eq_zero (bytesStoreLiteSetMappedValueBytes I) hvalueSize0
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlot I) =
        bytesStoreLiteSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked (bytesStoreLiteSetMappedSlot I) evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite := writeSolidityBytesShortPacked
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evmSolm0)
    (er := bytesStoreLiteSetMappedRef I)
    (baseSlot := bytesStoreLiteSetMappedSlot I)
    (header := bytesStoreLiteSetMappedHeaderWord σ_evm I) (len := oldLen)
    (value := ByteArray.empty)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreLiteSetMappedSlot I) evmSolm0, ?_, by simp⟩
      simp [bytesStoreLiteLayout, bytesStoreLiteSetMappedRef,
        bytesStoreLiteSetMappedRefOf, bytesStoreLiteSetMappedSlot,
        bytesStoreLiteSetMappedSlotOf])
    (by decide) hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, bytesStoreLiteSetMappedRef, bytesStoreLiteSetMappedRefOf,
    bytesStoreLiteSetMappedSlot, hvalueEmpty, hshortEmpty] using hwrite

theorem bytesStoreLiteSetMappedWriteShortOldShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g len : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hshort : len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreLiteSetMappedSlot I)
      (solidityShortBytesWord (bytesStoreLiteSetMappedValueBytes I))
    writeStorage? bytesStoreLiteConfig evmSolm0
      (bytesStoreLiteSetMappedRef I) .bytes
      (.bytes (bytesStoreLiteSetMappedValueBytes I)) = .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize : (bytesStoreLiteSetMappedValueBytes I).size < 32 := by
    rw [bytesStoreLiteSetMappedValueBytes_size hpayload, ← hlenAbi]
    exact hshort
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlot I) =
        bytesStoreLiteSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked (bytesStoreLiteSetMappedSlot I) evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite := writeSolidityBytesShortPacked
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evmSolm0)
    (er := bytesStoreLiteSetMappedRef I)
    (baseSlot := bytesStoreLiteSetMappedSlot I)
    (header := bytesStoreLiteSetMappedHeaderWord σ_evm I) (len := oldLen)
    (value := bytesStoreLiteSetMappedValueBytes I)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreLiteSetMappedSlot I) evmSolm0, ?_, by simp⟩
      simp [bytesStoreLiteLayout, bytesStoreLiteSetMappedRef,
        bytesStoreLiteSetMappedRefOf, bytesStoreLiteSetMappedSlot,
        bytesStoreLiteSetMappedSlotOf])
    hvalueSize hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, bytesStoreLiteSetMappedRef, bytesStoreLiteSetMappedRefOf,
    bytesStoreLiteSetMappedSlot] using hwrite

theorem bytesStoreLiteSetMappedWriteLongOldShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g len : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlong : ¬ len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let value := bytesStoreLiteSetMappedValueBytes I
    writeStorage? bytesStoreLiteConfig evmSolm0
      (bytesStoreLiteSetMappedRef I) .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetMappedSlot I) value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetMappedSlot I) value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlot I) (solidityBytesHeaderWord value.size)) := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let value := bytesStoreLiteSetMappedValueBytes I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize : ¬ value.size < 32 := by
    rw [show value.size = len.toNat by
      dsimp [value]
      rw [bytesStoreLiteSetMappedValueBytes_size hpayload, ← hlenAbi]]
    exact hlong
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlot I) =
        bytesStoreLiteSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked (bytesStoreLiteSetMappedSlot I) evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite := writeSolidityBytesLongPacked
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evmSolm0)
    (er := bytesStoreLiteSetMappedRef I)
    (baseSlot := bytesStoreLiteSetMappedSlot I)
    (header := bytesStoreLiteSetMappedHeaderWord σ_evm I) (len := oldLen)
    (value := value)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreLiteSetMappedSlot I) evmSolm0, ?_, by simp⟩
      simp [bytesStoreLiteLayout, bytesStoreLiteSetMappedRef,
        bytesStoreLiteSetMappedRefOf, bytesStoreLiteSetMappedSlot,
        bytesStoreLiteSetMappedSlotOf])
    hvalueSize hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, value, bytesStoreLiteSetMappedRef,
    bytesStoreLiteSetMappedRefOf, bytesStoreLiteSetMappedSlot] using hwrite

theorem bytesStoreLiteSetMappedWriteLongOldLongPrepared
    {cA gh bl σ_evm σ_solm σ₀ A I} {g len oldStoredLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlong : ¬ len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let value := bytesStoreLiteSetMappedValueBytes I
    writeStorage? bytesStoreLiteConfig evmSolm0
      (bytesStoreLiteSetMappedRef I) .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom
            (clearSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetMappedSlot I)
              (solidityBytesDataWordCount value.size)
              (solidityBytesDataWordCount oldStoredLen.toNat -
                solidityBytesDataWordCount value.size))
            (bytesStoreLiteSetMappedSlot I) value 0 (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom
            (clearSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetMappedSlot I)
              (solidityBytesDataWordCount value.size)
              (solidityBytesDataWordCount oldStoredLen.toNat -
                solidityBytesDataWordCount value.size))
            (bytesStoreLiteSetMappedSlot I) value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlot I) (solidityBytesHeaderWord value.size)) := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let value := bytesStoreLiteSetMappedValueBytes I
  have hvalueSize : ¬ value.size < 32 := by
    rw [show value.size = len.toNat by
      dsimp [value]
      rw [bytesStoreLiteSetMappedValueBytes_size hpayload, ← hlenAbi]]
    exact hlong
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlot I) =
        bytesStoreLiteSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite := writeSolidityBytesLongFromLongPrepared
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evmSolm0)
    (er := bytesStoreLiteSetMappedRef I)
    (baseSlot := bytesStoreLiteSetMappedSlot I)
    (header := bytesStoreLiteSetMappedHeaderWord σ_evm I)
    (len := oldStoredLen)
    (value := value)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreLiteSetMappedSlot I) evmSolm0, ?_, by simp⟩
      simp [bytesStoreLiteLayout, bytesStoreLiteSetMappedRef,
        bytesStoreLiteSetMappedRefOf, bytesStoreLiteSetMappedSlot,
        bytesStoreLiteSetMappedSlotOf])
    hvalueSize
    hload
    hflag holdStoredLen hvalid
  simpa [evmSolm0, value, bytesStoreLiteSetMappedRef,
    bytesStoreLiteSetMappedRefOf, bytesStoreLiteSetMappedSlot,
    clearSolidityBytesDataWordsFrom_executionEnv]
    using hwrite

theorem bytesStoreLiteSetMappedWriteShortOldLongPrepared
    {cA gh bl σ_evm σ_solm σ₀ A I} {g len oldStoredLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hshort : len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩) :
    let value := bytesStoreLiteSetMappedValueBytes I
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
      (bytesStoreLiteSetMappedSlot I) 0 ((oldStoredLen.toNat + 31) / 32)
    let evmData := Solm.EVM.storageStore evmClear I.codeOwner
      (bytesStoreLiteSetMappedSlot I) (solidityShortBytesWord value)
    writeStorage? bytesStoreLiteConfig evmSolm0
      (bytesStoreLiteSetMappedRef I) .bytes
      (.bytes value) = .ok evmData := by
  dsimp only
  let value := bytesStoreLiteSetMappedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreLiteSetMappedSlot I) 0 ((oldStoredLen.toNat + 31) / 32)
  let evmData := Solm.EVM.storageStore evmClear I.codeOwner
    (bytesStoreLiteSetMappedSlot I) (solidityShortBytesWord value)
  have hvalueSize : value.size < 32 := by
    dsimp [value]
    rw [bytesStoreLiteSetMappedValueBytes_size hpayload, ← hlenAbi]
    exact hshort
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlot I) =
        bytesStoreLiteSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite := writeSolidityBytesShortFromLongPrepared
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evmSolm0)
    (er := bytesStoreLiteSetMappedRef I)
    (baseSlot := bytesStoreLiteSetMappedSlot I)
    (header := bytesStoreLiteSetMappedHeaderWord σ_evm I)
    (len := oldStoredLen)
    (value := value)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreLiteSetMappedSlot I) evmSolm0, ?_, by simp⟩
      simp [bytesStoreLiteLayout, bytesStoreLiteSetMappedRef,
        bytesStoreLiteSetMappedRefOf, bytesStoreLiteSetMappedSlot,
        bytesStoreLiteSetMappedSlotOf])
    hvalueSize
    hload
    hflag holdStoredLen hvalid
  simpa [evmSolm0, evmClear, evmData, value, bytesStoreLiteSetMappedRef,
    bytesStoreLiteSetMappedRefOf, bytesStoreLiteSetMappedSlot,
    clearSolidityBytesDataWordsFrom_executionEnv]
    using hwrite

theorem bytesStoreLiteSetMappedShortFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {oldLen storedWord : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hstored : storedWord = solidityShortBytesWord value)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        (bytesStoreLiteSetMappedSlot I) storedWord)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (bytesStoreLiteSetMappedSlot I) 0 ((oldLen.toNat + 31) / 32))
        I.codeOwner (bytesStoreLiteSetMappedSlot I)
          (solidityShortBytesWord value)).accountMap := by
  exact accountMapEquiv_setBytesShortFromLongPostAccountMapEquiv
    (baseSlot := bytesStoreLiteSetMappedSlot I)
    (oldLen := oldLen) (storedWord := storedWord) (value := value)
    hAccounts hstored holdLenLt

theorem bytesStoreLiteSetMappedEmptyFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {oldLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        (bytesStoreLiteSetMappedSlot I) ⟨0⟩)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (bytesStoreLiteSetMappedSlot I) 0 ((oldLen.toNat + 31) / 32))
        I.codeOwner (bytesStoreLiteSetMappedSlot I) ⟨0⟩).accountMap := by
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hstored : (⟨0⟩ : UInt256) = solidityShortBytesWord ByteArray.empty := hshortEmpty.symm
  simpa [initState, hshortEmpty] using
    bytesStoreLiteSetMappedShortFromLongPostAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (oldLen := oldLen) (storedWord := (⟨0⟩ : UInt256))
      (value := ByteArray.empty) hAccounts hstored holdLenLt

theorem bytesStoreLiteSetMappedWriteLongOldShortPackedAbsent
    {cA gh bl σ_evm σ_solm σ₀ A I} {g len : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlong : ¬ len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hmissing :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap.find?
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
          none) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let value := bytesStoreLiteSetMappedValueBytes I
    writeStorage? bytesStoreLiteConfig evmSolm0
      (bytesStoreLiteSetMappedRef I) .bytes (.bytes value) = .ok evmSolm0 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let value := bytesStoreLiteSetMappedValueBytes I
  have hwrite₀ := bytesStoreLiteSetMappedWriteLongOldShortPacked
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
    hAccounts hlenAbi hpayload hlong hflag hvalid
  have hdata :
      writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetMappedSlot I) value 0
          (solidityBytesDataWordCount value.size) = evmSolm0 := by
    exact writeSolidityBytesDataWordsFrom_absent_same
      (evm := evmSolm0) (baseSlot := bytesStoreLiteSetMappedSlot I)
      (value := value) (idx := 0) (fuel := solidityBytesDataWordCount value.size)
      (by simpa [evmSolm0] using hmissing)
  have hstore :
      Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetMappedSlot I) value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetMappedSlot I) value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlot I) (solidityBytesHeaderWord value.size) =
        evmSolm0 := by
    rw [hdata]
    exact storageStore_absent evmSolm0 evmSolm0.executionEnv.codeOwner
      (by simpa [evmSolm0] using hmissing)
      (bytesStoreLiteSetMappedSlot I) (solidityBytesHeaderWord value.size)
  simpa [evmSolm0, value, hstore] using hwrite₀

theorem bytesStoreLiteSetMappedWriteMalformedLong {evm : EVM.State}
    (I : ExecutionEnv) (header : UInt256) (value : ByteArray)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetMappedSlot I) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm
      (bytesStoreLiteSetMappedRef I) .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedLong
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm)
    (er := bytesStoreLiteSetMappedRef I)
    (baseSlot := bytesStoreLiteSetMappedSlot I) (header := header) (value := value)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreLiteSetMappedSlot I) evm, ?_, by simp⟩
      simp [bytesStoreLiteLayout, bytesStoreLiteSetMappedRef,
        bytesStoreLiteSetMappedRefOf, bytesStoreLiteSetMappedSlot,
        bytesStoreLiteSetMappedSlotOf])
    hload hflag hbad

theorem bytesStoreLiteSetMappedWriteMalformedShort {evm : EVM.State}
    (I : ExecutionEnv) (header : UInt256) (value : ByteArray)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreLiteSetMappedSlot I) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm
      (bytesStoreLiteSetMappedRef I) .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedShort
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm)
    (er := bytesStoreLiteSetMappedRef I)
    (baseSlot := bytesStoreLiteSetMappedSlot I) (header := header) (value := value)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreLiteSetMappedSlot I) evm, ?_, by simp⟩
      simp [bytesStoreLiteLayout, bytesStoreLiteSetMappedRef,
        bytesStoreLiteSetMappedRefOf, bytesStoreLiteSetMappedSlot,
        bytesStoreLiteSetMappedSlotOf])
    hload hflag hbad

theorem bytesStoreLiteSetMappedLengthAfterEmptyWrite
    {cA gh bl σ_solm σ₀ A I} {g : UInt256} :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreLiteSetMappedSlot I) ⟨0⟩
    readStorageBytesLength? bytesStoreLiteConfig evmSolm1
      (bytesStoreLiteSetMappedRef I) = .ok 0 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetMappedSlot I) ⟨0⟩
  exact bytesStoreLiteReadLengthAfterHeaderStoreZero
    (er := bytesStoreLiteSetMappedRef I) (evm := evmSolm0) (evmData := evmSolm1)
    (baseSlot := bytesStoreLiteSetMappedSlot I) (by rfl)
    (bytesStoreLiteSetMappedRef_length_slot evmSolm1 I)

theorem bytesStoreLiteSetMappedLengthAfterShortWrite
    {cA gh bl σ_solm σ₀ A I} {g len payloadStart : UInt256} {acc : Account}
    (hacc : σ_solm.find? I.codeOwner = some acc)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let storedWord := bytesStoreLiteSetMappedShortStoredWord I len payloadStart
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreLiteSetMappedSlot I) storedWord
    readStorageBytesLength? bytesStoreLiteConfig evmSolm1
      (bytesStoreLiteSetMappedRef I) = .ok len.toNat := by
  dsimp only
  let storedWord := bytesStoreLiteSetMappedShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetMappedSlot I) storedWord
  have hdecode :
      solidityDecodeBytesLengthHeader storedWord = .ok len.toNat := by
    exact solidityDecodeBytesLengthHeader_short_valid
      (header := storedWord) (len := len)
      (by
        simpa [storedWord, bytesStoreLiteSetMappedShortStoredWord] using
          bytesStoreLiteSetChunkShortStoredWord_flag_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        symm
        simpa [storedWord, bytesStoreLiteSetMappedShortStoredWord] using
          bytesStoreLiteSetChunkShortStoredWord_shortLen_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        rw [show UInt256.lt len ⟨32⟩ = ⟨1⟩ by
          exact ult_one (by
            rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
            exact hshort)]
        have hflag :
            UInt256.land storedWord ⟨1⟩ = ⟨0⟩ := by
          simpa [storedWord, bytesStoreLiteSetMappedShortStoredWord] using
            bytesStoreLiteSetChunkShortStoredWord_flag_eq
              (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
        rw [hflag]
        native_decide)
  have hacc0 : evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner = some acc := by
    simpa [evmSolm0, initState] using hacc
  exact bytesStoreLiteReadLengthAfterHeaderStorePresent
    (er := bytesStoreLiteSetMappedRef I) (evm := evmSolm0) (evmData := evmSolm1)
    (baseSlot := bytesStoreLiteSetMappedSlot I) (header := storedWord) (len := len.toNat)
    (by rfl)
    (bytesStoreLiteSetMappedRef_length_slot evmSolm1 I)
    hacc0
    hdecode

theorem bytesStoreLiteSetMappedLengthAfterLongStoreOfState
    {evm : EVM.State} {I : ExecutionEnv} {len header : UInt256} {acc : Account}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hacc : evm.accountMap.find? I.codeOwner = some acc)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
      (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreLiteSetMappedSlot I) header
    readStorageBytesLength? bytesStoreLiteConfig evmData
      (bytesStoreLiteSetMappedRef I) = .ok len.toNat := by
  dsimp only
  let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreLiteSetMappedSlot I) header
  have hdecode :
      solidityDecodeBytesLengthHeader header = .ok len.toNat := by
    exact solidityDecodeBytesLengthHeader_long_valid
      (header := header) (len := len) hflag hlen (by simpa [← hlen] using hvalid)
  simpa [evmData, storageStore_executionEnv, howner] using
    bytesStoreLiteReadLengthAfterHeaderStorePresent
      (er := bytesStoreLiteSetMappedRef I) (evm := evm) (evmData := evmData)
      (baseSlot := bytesStoreLiteSetMappedSlot I) (header := header) (len := len.toNat)
      (by simp [evmData, howner])
      (by simpa [evmData, howner] using bytesStoreLiteSetMappedRef_length_slot evmData I)
      (by simpa [howner] using hacc)
      hdecode

theorem bytesStoreLiteSetMappedLengthAfterShortStoreOfState
    {evm : EVM.State} {I : ExecutionEnv} {len payloadStart : UInt256} {acc : Account}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hacc : evm.accountMap.find? I.codeOwner = some acc)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let storedWord := bytesStoreLiteSetMappedShortStoredWord I len payloadStart
    let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreLiteSetMappedSlot I) storedWord
    readStorageBytesLength? bytesStoreLiteConfig evmData
      (bytesStoreLiteSetMappedRef I) = .ok len.toNat := by
  dsimp only
  let storedWord := bytesStoreLiteSetMappedShortStoredWord I len payloadStart
  let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreLiteSetMappedSlot I) storedWord
  have hdecode :
      solidityDecodeBytesLengthHeader storedWord = .ok len.toNat := by
    exact solidityDecodeBytesLengthHeader_short_valid
      (header := storedWord) (len := len)
      (by
        simpa [storedWord, bytesStoreLiteSetMappedShortStoredWord] using
          bytesStoreLiteSetChunkShortStoredWord_flag_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        symm
        simpa [storedWord, bytesStoreLiteSetMappedShortStoredWord] using
          bytesStoreLiteSetChunkShortStoredWord_shortLen_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        rw [show UInt256.lt len ⟨32⟩ = ⟨1⟩ by
          exact ult_one (by
            rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
            exact hshort)]
        have hflag :
            UInt256.land storedWord ⟨1⟩ = ⟨0⟩ := by
          simpa [storedWord, bytesStoreLiteSetMappedShortStoredWord] using
            bytesStoreLiteSetChunkShortStoredWord_flag_eq
              (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
        rw [hflag]
        native_decide)
  simpa [evmData, storageStore_executionEnv, howner] using
    bytesStoreLiteReadLengthAfterHeaderStorePresent
      (er := bytesStoreLiteSetMappedRef I) (evm := evm) (evmData := evmData)
      (baseSlot := bytesStoreLiteSetMappedSlot I) (header := storedWord) (len := len.toNat)
      (by simp [evmData, howner])
      (by simpa [evmData, howner] using bytesStoreLiteSetMappedRef_length_slot evmData I)
      (by simpa [howner] using hacc)
      hdecode

theorem bytesStoreLiteSetMappedLengthAfterEmptyStoreOfState
    {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreLiteSetMappedSlot I) ⟨0⟩
    readStorageBytesLength? bytesStoreLiteConfig evmData
      (bytesStoreLiteSetMappedRef I) = .ok 0 := by
  dsimp only
  let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreLiteSetMappedSlot I) ⟨0⟩
  simpa [evmData, storageStore_executionEnv, howner] using
    bytesStoreLiteReadLengthAfterHeaderStoreZero
      (er := bytesStoreLiteSetMappedRef I) (evm := evm) (evmData := evmData)
      (baseSlot := bytesStoreLiteSetMappedSlot I)
      (by simp [evmData, howner])
      (by simpa [evmData, howner] using bytesStoreLiteSetMappedRef_length_slot evmData I)

theorem bytesStoreLiteSetMappedSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xe1, 0x91, 0x9b, 0x17]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLiteReachSetMappedDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2154⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨498⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hreach⟩ := bytesStoreLiteReachSetMapped
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  exact ⟨_, _, by
    simpa [bytesStoreLiteSetMappedEntryPc] using
      (evm_run hreach with [
        jumpdest, push2 ⟨263⟩, push2 ⟨498⟩, calldatasize, push1 ⟨4⟩,
        push2 ⟨2154⟩, jump (by native_decide)])⟩

theorem bytesStoreLiteX_setMappedDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetMappedDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setMappedDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetMappedDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setMappedDecodeOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetMappedDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 36) ⟨18446744073709551615⟩ = ⟨1⟩ := by
    exact ugt_one (by simpa [ABI.solcMaxU64] using hoff)
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hgt
  have rd2172 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload]
  have rd2189 := RD.pushConst rd2172 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  exact evm_run rd2189 with [
    dup2, gt, iszero, push2 ⟨2201⟩,
    jumpiNT (by rw [hgt']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setMappedDecodeLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetMappedDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 36) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    simpa [calldataWord] using hstart
  have rd2172 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload]
  have rd2189 := RD.pushConst rd2172 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2201 := evm_run rd2189 with [
    dup2, gt, iszero, push2 ⟨2201⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2201 with [
    jumpdest, push2 ⟨2213⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  exact evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiNT (by simpa [calldataWord] using hstart'),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setMappedDecodeLengthHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨1⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetMappedDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 36) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hlenMax
  have rd2172 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload]
  have rd2189 := RD.pushConst rd2172 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2201 := evm_run rd2189 with [
    dup2, gt, iszero, push2 ⟨2201⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2201 with [
    jumpdest, push2 ⟨2213⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  have rd1830 := evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiT (by rw [hstart']; decide) (by native_decide)]
  have rd1834 := evm_run rd1830 with [jumpdest, pop, dup2, calldataload]
  have rd1843 := RD.pushConst rd1834 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  exact evm_run rd1843 with [
    dup2, gt, iszero, push2 ⟨1853⟩,
    jumpiNT (by rw [hlenMax']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setMappedDecodePayloadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetMappedDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 36) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hlenMax
  have hpayload' :
      UInt256.gt
        (((((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
          uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
              32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hpayload
  have rd2172 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload]
  have rd2189 := RD.pushConst rd2172 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2201 := evm_run rd2189 with [
    dup2, gt, iszero, push2 ⟨2201⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2201 with [
    jumpdest, push2 ⟨2213⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  have rd1830 := evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiT (by rw [hstart']; decide) (by native_decide)]
  have rd1834 := evm_run rd1830 with [jumpdest, pop, dup2, calldataload]
  have rd1843 := RD.pushConst rd1834 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1853 := evm_run rd1843 with [
    dup2, gt, iszero, push2 ⟨1853⟩,
    jumpiT (by rw [hlenMax']; decide) (by native_decide)]
  exact evm_run rd1853 with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop,
    dup4, push1 ⟨32⟩, dup3, dup6, add, add, gt, iszero, push2 ⟨1876⟩,
    jumpiNT (by rw [hpayload']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem bytesStoreLiteX_setMappedDecodeValidRaw {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [ uInt256OfByteArray
          (I.calldata.readBytes
            (((⟨4⟩ : UInt256) +
              uInt256OfByteArray
                (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
            32),
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
          ⟨32⟩),
        uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32),
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetMappedDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 36) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hlenMax
  have hpayload' :
      UInt256.gt
        (((((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
          uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
              32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    simpa [calldataWord] using hpayload
  have rd2172 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload, swap3, pop, push1 ⟨32⟩, dup5, add, calldataload]
  have rd2189 := RD.pushConst rd2172 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2201 := evm_run rd2189 with [
    dup2, gt, iszero, push2 ⟨2201⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2201 with [
    jumpdest, push2 ⟨2213⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  have rd1830 := evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiT (by rw [hstart']; decide) (by native_decide)]
  have rd1834 := evm_run rd1830 with [jumpdest, pop, dup2, calldataload]
  have rd1843 := RD.pushConst rd1834 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd1853 := evm_run rd1843 with [
    dup2, gt, iszero, push2 ⟨1853⟩,
    jumpiT (by rw [hlenMax']; decide) (by native_decide)]
  have rd1876 := evm_run rd1853 with [
    jumpdest, push1 ⟨32⟩, dup4, add, swap2, pop,
    dup4, push1 ⟨32⟩, dup3, dup6, add, add, gt, iszero, push2 ⟨1876⟩,
    jumpiT (by rw [hpayload']; decide) (by native_decide)]
  have rd2213 := evm_run rd1876 with [
    jumpdest, swap3, pop, swap3, swap1, pop, jump (by native_decide)]
  have rd498 := evm_run rd2213 with [
    jumpdest, swap5, swap8, swap1, swap7, pop, swap4, swap5, pop, pop, pop, pop,
    jump (by native_decide)]
  exact ⟨_, _, evm_run rd498 with [jumpdest, push2 ⟨1644⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setMappedReachWriteHelper {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart key : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2599⟩
      [bytesStoreLiteSetMappedSlotOf key, payloadStart, len, ⟨1668⟩,
        bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1644⟩ := hreach
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨4⟩ solcFreePtrMem).readWithPadding 0 64))) =
        bytesStoreLiteSetMappedSlotOf key := by
    rw [twoWordHashMem_read0_64 key ⟨4⟩ solcFreePtrMem_size]
    unfold bytesStoreLiteSetMappedSlotOf mappedValueSlot
    rw [keyValueToWord_uint256]
    exact mappingSlot_single key ⟨4⟩
  have rd1658 := evm_run rd1644 with [
    jumpdest, push0, dup4, dup2,
    raw mstore 0 (wordAt0Mem key solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0 (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, dup2,
    raw keccak256 0 (bytesStoreLiteSetMappedSlotOf key) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd1658 with [
    push2 ⟨1668⟩, dup4, dup6, dup4, push2 ⟨2599⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setMappedReachWriteHeaderDecoder {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart key : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      ((bytesStoreLiteSetMappedHeaderWordOf σ I key) ::
        ⟨2637⟩ :: len :: ⟨2643⟩ :: bytesStoreLiteSetMappedSlotOf key ::
        payloadStart :: len :: ⟨1668⟩ :: bytesStoreLiteSetMappedSlotOf key ::
        ⟨0⟩ :: len :: payloadStart :: key :: ⟨263⟩ ::
        bytesStoreLiteSelWord I :: [])
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  have hhelper := bytesStoreLiteX_setMappedReachWriteHelper
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key) hreach
  simpa [bytesStoreLiteSetMappedHeaderWordOf] using
    bytesStoreLiteX_writeBytesHelperReachHeaderDecoder
      (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (slot := bytesStoreLiteSetMappedSlotOf key)
      (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
      (tail := [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreLiteSelWord I])
      (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
      (rdata := ByteArray.empty) hhelper hlenMax
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedLongMalformedHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart key : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreLiteX_setMappedReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key) hreach hlenMax
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (header := bytesStoreLiteSetMappedHeaderWordOf σ I key) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, bytesStoreLiteSetMappedSlotOf key, payloadStart, len,
      ⟨1668⟩, bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem)
    hdecoder hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedShortMalformedHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart key : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreLiteX_setMappedReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key) hreach hlenMax
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (header := bytesStoreLiteSetMappedHeaderWordOf σ I key) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, bytesStoreLiteSetMappedSlotOf key, payloadStart, len,
      ⟨1668⟩, bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem)
    hdecoder hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedShortHeaderReachWriteBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart key : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [bytesStoreLiteSetMappedSlotOf key, payloadStart, len, ⟨1668⟩,
        bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  have hhelper := bytesStoreLiteX_setMappedReachWriteHelper
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key) hreach
  exact bytesStoreLiteX_writeBytesHelperShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreLiteSetMappedSlotOf key)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hhelper hlenMax hflag hvalid
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedLongHeaderNoClearReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let header : UInt256 := bytesStoreLiteSetMappedHeaderWordOf σ I key
  have hdecoder := bytesStoreLiteX_setMappedReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax
  have hstoredEq : UInt256.div header ⟨2⟩ = oldStoredLen := by
    simpa [header] using holdStoredLen.symm
  have hvalidHeader :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [header, hstoredEq] using hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩,
      len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header, slot] using hdecoder)
    (by simpa [header] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩,
          slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [slot, oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩,
        slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2637 with [
      jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldStoredLen ≠ ⟨0⟩ :=
    BytesStoreLiteCore.clearCurrentLongValid_gt31
      (header := header) (len := oldStoredLen)
      (by simpa [header] using hflag)
      (by simpa [header] using hvalid)
  have holdLong : UInt256.gt oldStoredLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldStoredLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldStoredLen from rfl]
    exact BytesStoreLiteCore.clearCurrent_ult_eq_one_of_ne_zero hgt31
  simpa [slot] using
    bytesStoreLiteX_writeBytesCleanupOldLongNoClear
      (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
      (len := len) (ret := ⟨2643⟩)
      (tail := [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
        key, ⟨263⟩, bytesStoreLiteSelWord I])
      (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem)
      (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
      hcleanupReach holdLong hgtOldNew (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedLongNoTailOldLongNoClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  have hbranch := bytesStoreLiteX_setMappedLongHeaderNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (key := key) (oldStoredLen := oldStoredLen)
    hreach hlenMax hflag holdStoredLen hvalid hgtOldNew
  exact bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm (by simpa [slot] using hbranch) hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedLongTailOldLongNoClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot
            (bytesLikeDataBase slot) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride
                (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  have hbranch := bytesStoreLiteX_setMappedLongHeaderNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (key := key) (oldStoredLen := oldStoredLen)
    hreach hlenMax hflag holdStoredLen hvalid hgtOldNew
  exact bytesStoreLiteX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm (by simpa [slot] using hbranch) hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedLongHeaderClearReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩))) =
        ⟨0⟩)
    (hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)) =
        ⟨0⟩) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩ fuel
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σClear) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let header : UInt256 := bytesStoreLiteSetMappedHeaderWordOf σ I key
  have hdecoder := bytesStoreLiteX_setMappedReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax
  have hstoredEq : UInt256.div header ⟨2⟩ = oldStoredLen := by
    simpa [header] using holdStoredLen.symm
  have hvalidHeader :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [header, hstoredEq] using hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩,
      len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header, slot] using hdecoder)
    (by simpa [header] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩, slot,
          ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [slot, oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩,
        slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2637 with [
      jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldStoredLen ≠ ⟨0⟩ :=
    BytesStoreLiteCore.clearCurrentLongValid_gt31
      (header := header) (len := oldStoredLen)
      (by simpa [header] using hflag)
      (by simpa [header] using hvalid)
  have holdLong : UInt256.gt oldStoredLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldStoredLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldStoredLen from rfl]
    exact BytesStoreLiteCore.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have hlongWord : UInt256.lt len ⟨32⟩ = ⟨0⟩ :=
    ult_zero (by
      have hle : 32 ≤ len.toNat := Nat.le_of_not_gt hlong
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hle)
  have hloopEntry := bytesStoreLiteX_writeBytesCleanupOldLongLongToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
    (len := len) (ret := ⟨2643⟩)
    (tail := [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
      key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hcleanupReach holdLong hgtOldNew hlongWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hloop := bytesStoreLiteX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩))
    (base := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot)
    (dead₀ := slot) (dead₁ := oldStoredLen) (dead₂ := len)
    (ret := (⟨2643⟩ : UInt256))
    (rest := [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
      key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [slot] using hloop

theorem bytesStoreLiteX_setMappedLongHeaderClearReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
          bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat) k C := by
  let count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
    (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreLiteX_setMappedLongHeaderClearReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (len := len) (payloadStart := payloadStart)
      (key := key) (oldStoredLen := oldStoredLen) (fuel := count.toNat)
      hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
      hcontinue hdone

theorem bytesStoreLiteX_setMappedLongNoTailOldLongClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
      (BytesStoreLiteCore.clearCurrentHashAw
        (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  have hbranch := bytesStoreLiteX_setMappedLongHeaderClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (key := key) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
  exact bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σClear) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    hperm (by simpa [slot, σClear] using hbranch) hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedLongTailOldLongClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot
            (bytesLikeDataBase slot) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride
                (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
      (BytesStoreLiteCore.clearCurrentHashAw
        (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  have hbranch := bytesStoreLiteX_setMappedLongHeaderClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (key := key) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
  exact bytesStoreLiteX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σClear) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    hperm (by simpa [slot, σClear] using hbranch) hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedReachReturnLengthDecoderFromMemEarly
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart key : UInt256} {mem : ByteArray}
    (hmem : mem.size = 96)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      mem (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteSetMappedHeaderWordOf σ I key, ⟨1002⟩, bytesStoreLiteSetMappedSlotOf key,
        ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem key ⟨4⟩ mem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1668⟩ := hreach
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨4⟩ mem).readWithPadding 0 64))) =
        bytesStoreLiteSetMappedSlotOf key := by
    rw [twoWordHashMem_read0_64 key ⟨4⟩ hmem]
    unfold bytesStoreLiteSetMappedSlotOf mappedValueSlot
    rw [keyValueToWord_uint256]
    exact mappingSlot_single key ⟨4⟩
  have rd1683 := evm_run rd1668 with [
    jumpdest, pop, push0, dup5, dup2,
    raw mstore 0 (wordAt0Mem key mem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0
      (twoWordHashMem key ⟨4⟩ mem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (bytesStoreLiteSetMappedSlotOf key)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1684₀⟩ := rd1683.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1684⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1685⟩
        [bytesStoreLiteSetMappedHeaderWordOf σ I key, bytesStoreLiteSetMappedSlotOf key,
          ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem key ⟨4⟩ mem)
        (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreLiteSetMappedHeaderWordOf, initState] using rd1684₀⟩
  exact ⟨_, _, evm_run rd1684 with [
    push2 ⟨1002⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setMappedLongNoTailOldLongClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (haccData :
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
            bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat)
        (bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) payloadStart
        (⟨0⟩ : UInt256) I (len.toNat / 32)).find? I.codeOwner = some acc) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let start : UInt256 := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩
  let count : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ (start + bytesLikeDataBase slot) ⟨0⟩ count.toNat
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap := sstoreAccountMap I.codeOwner σLoop slot header
  let loadedHeader : UInt256 := bytesStoreLiteSetMappedHeaderWordOf σData I key
  let writeMem : ByteArray :=
    wordAt0Mem slot (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hbody := bytesStoreLiteX_setMappedLongNoTailOldLongClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong hnoTailMod
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoderFromMemEarly
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)))
    (by
      simpa [σClear, σLoop, σData, slot, header, start, count, writeMem,
        BytesStoreLiteCore.clearCurrentHashAw] using hbody)
  have hdata : bytesStoreLiteSetMappedHeaderWordOf σData I key = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σLoop, σClear, slot, header, start, count,
      bytesStoreLiteSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some σLoop I.codeOwner acc
        slot header
        (by simpa [σLoop, σClear, slot, start, count] using haccData) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, retMem] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (chunkIndex := key)
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := retMem)
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_size_96 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (wordAt0Mem_size_96 slot
              (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))))
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_read64 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (wordAt0Mem_size_96 slot
              (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)))
          (bytesStoreLiteWordAt0Mem_read64 slot
            (wordAt0Mem_size_96 slot
              (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
            (bytesStoreLiteWordAt0Mem_read64 slot
              (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
              (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64))))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setMappedLongTailOldLongClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner σ
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
              bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) ⟨0⟩
            (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
              (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat)
          (bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) payloadStart
          (⟨0⟩ : UInt256) I (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot
          (bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let tailSlot : UInt256 :=
      BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
    let tailWord : UInt256 :=
      BytesStoreLiteCore.longDataTailMaskedWord
        (bytesStoreLiteCalldataLongDataWord I payloadStart
          (BytesStoreLiteCore.longDataWordsLoopStride
            (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
    let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let start : UInt256 := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩
  let count : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ (start + bytesLikeDataBase slot) ⟨0⟩ count.toNat
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap := sstoreAccountMap I.codeOwner σTail slot header
  let loadedHeader : UInt256 := bytesStoreLiteSetMappedHeaderWordOf σData I key
  let writeMem : ByteArray :=
    wordAt0Mem slot (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hbody := bytesStoreLiteX_setMappedLongTailOldLongClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong htailMod
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoderFromMemEarly
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)))
    (by
      simpa [σClear, σLoop, tailSlot, tailWord, σTail, σData, slot, header,
        start, count, writeMem, BytesStoreLiteCore.clearCurrentHashAw] using hbody)
  have hdata : bytesStoreLiteSetMappedHeaderWordOf σData I key = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σTail, σLoop, σClear, tailSlot, tailWord, slot, header,
      start, count, bytesStoreLiteSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some σTail I.codeOwner acc
        slot header
        (by simpa [σTail, σLoop, σClear, tailSlot, tailWord, slot, start, count]
          using haccTail)
        hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, retMem] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (chunkIndex := key)
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := retMem)
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_size_96 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (wordAt0Mem_size_96 slot
              (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))))
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_read64 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (wordAt0Mem_size_96 slot
              (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)))
          (bytesStoreLiteWordAt0Mem_read64 slot
            (wordAt0Mem_size_96 slot
              (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
            (bytesStoreLiteWordAt0Mem_read64 slot
              (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
              (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64))))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setMappedLongNoTailOldShortWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  have hbranch := bytesStoreLiteX_setMappedShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax hflag hvalid
  exact bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm (by simpa [slot] using hbranch) hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedLongTailOldShortWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot
            (bytesLikeDataBase slot) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride
                (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  have hbranch := bytesStoreLiteX_setMappedShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax hflag hvalid
  exact bytesStoreLiteX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm (by simpa [slot] using hbranch) hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedEmptyWriteReturnsToBody {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedSlotOf key) ⟨0⟩)
      k C := by
  have hbranch := bytesStoreLiteX_setMappedShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax hflag hvalid
  have hpacked := bytesStoreLiteX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreLiteSetMappedSlotOf key)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hbranch hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hwrite := bytesStoreLiteX_writeBytesNewEmptyWriteHeaderGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreLiteSetMappedSlotOf key)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm hpacked hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedSlotOf key) ⟨0⟩)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := bytesStoreLiteSetMappedSlotOf key) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1668⟩)
    (tail := [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hwrite (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedShortNonemptyWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreLiteSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedSlotOf key)
        (bytesStoreLiteSetMappedShortStoredWord I len payloadStart)) k C := by
  have hbranch := bytesStoreLiteX_setMappedShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax hflag hvalid
  have hwrite := bytesStoreLiteX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreLiteSetMappedSlotOf key)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm hbranch hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedSlotOf key)
      (bytesStoreLiteSetMappedShortStoredWord I len payloadStart))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := bytesStoreLiteSetMappedSlotOf key) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1668⟩)
    (tail := [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    (by simpa [bytesStoreLiteSetMappedShortStoredWord] using hwrite)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedReachReturnLengthDecoder
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart key : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteSetMappedHeaderWordOf σ I key, ⟨1002⟩, bytesStoreLiteSetMappedSlotOf key,
        ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1668⟩ := hreach
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          ((twoWordHashMem key ⟨4⟩
            (twoWordHashMem key ⟨4⟩ solcFreePtrMem)).readWithPadding 0 64))) =
        bytesStoreLiteSetMappedSlotOf key := by
    rw [twoWordHashMem_read0_64 key ⟨4⟩
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)]
    unfold bytesStoreLiteSetMappedSlotOf mappedValueSlot
    rw [keyValueToWord_uint256]
    exact mappingSlot_single key ⟨4⟩
  have rd1683 := evm_run rd1668 with [
    jumpdest, pop, push0, dup5, dup2,
    raw mstore 0 (wordAt0Mem key (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0
      (twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (bytesStoreLiteSetMappedSlotOf key) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1684₀⟩ := rd1683.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1684⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1685⟩
        [bytesStoreLiteSetMappedHeaderWordOf σ I key, bytesStoreLiteSetMappedSlotOf key,
          ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreLiteSetMappedHeaderWordOf, initState] using rd1684₀⟩
  exact ⟨_, _, evm_run rd1684 with [
    push2 ⟨1002⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setMappedReachReturnLengthDecoderFromMem
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart key : UInt256} {mem : ByteArray}
    (hmem : mem.size = 96)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      mem (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [bytesStoreLiteSetMappedHeaderWordOf σ I key, ⟨1002⟩, bytesStoreLiteSetMappedSlotOf key,
        ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem key ⟨4⟩ mem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1668⟩ := hreach
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨4⟩ mem).readWithPadding 0 64))) =
        bytesStoreLiteSetMappedSlotOf key := by
    rw [twoWordHashMem_read0_64 key ⟨4⟩ hmem]
    unfold bytesStoreLiteSetMappedSlotOf mappedValueSlot
    rw [keyValueToWord_uint256]
    exact mappingSlot_single key ⟨4⟩
  have rd1683 := evm_run rd1668 with [
    jumpdest, pop, push0, dup5, dup2,
    raw mstore 0 (wordAt0Mem key mem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0
      (twoWordHashMem key ⟨4⟩ mem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (bytesStoreLiteSetMappedSlotOf key)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1684₀⟩ := rd1683.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1684⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1685⟩
        [bytesStoreLiteSetMappedHeaderWordOf σ I key, bytesStoreLiteSetMappedSlotOf key,
          ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem key ⟨4⟩ mem)
        (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreLiteSetMappedHeaderWordOf, initState] using rd1684₀⟩
  exact ⟨_, _, evm_run rd1684 with [
    push2 ⟨1002⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setMappedReturnFromDecodedLength
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {mappedLen slot len payloadStart key : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1002⟩
      [mappedLen, slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreLiteSelWord I]
      mem aw rdata (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨263⟩
      [mappedLen, bytesStoreLiteSelWord I]
      mem aw rdata (cA, σ) k C := by
  exact bytesStoreLiteX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := mappedLen) (slot := slot)
    (len := len) (payloadStart := payloadStart) (chunkIndex := key)
    (mem := mem) (rdata := rdata) (aw := aw) hreach

theorem bytesStoreLiteX_setMappedLongNoTailReturnsOfBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    {acc : Account}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hlong : ¬ len.toNat < 32)
    (hbody :
      let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
      let σLoop : AccountMap :=
        bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32)
      let σData : AccountMap :=
        sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
        [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
        (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
        (cA, σData) k C)
    (haccData :
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) payloadStart
        (⟨0⟩ : UInt256) I (len.toNat / 32)).find? I.codeOwner = some acc) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only at hbody ⊢
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap := sstoreAccountMap I.codeOwner σLoop slot header
  let loadedHeader : UInt256 := bytesStoreLiteSetMappedHeaderWordOf σData I key
  let writeMem : ByteArray := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
    (by simpa [σLoop, σData, slot, header, writeMem] using hbody)
  have hdata : bytesStoreLiteSetMappedHeaderWordOf σData I key = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σLoop, slot, header, bytesStoreLiteSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some σLoop I.codeOwner acc
        slot header (by simpa [σLoop, slot] using haccData) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, retMem] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := retMem)
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_size_96 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)))
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_read64 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
          (bytesStoreLiteWordAt0Mem_read64 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
            (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setMappedLongTailReturnsOfBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    {acc : Account}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hlong : ¬ len.toNat < 32)
    (hbody :
      let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
      let σLoop : AccountMap :=
        bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32)
      let tailSlot : UInt256 :=
        BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
      let tailWord : UInt256 :=
        BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
      let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
      let σData : AccountMap :=
        sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
        [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
        (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
        (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
        (cA, σData) k C)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) payloadStart
          (⟨0⟩ : UInt256) I (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot
          (bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let tailSlot : UInt256 :=
      BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
    let tailWord : UInt256 :=
      BytesStoreLiteCore.longDataTailMaskedWord
        (bytesStoreLiteCalldataLongDataWord I payloadStart
          (BytesStoreLiteCore.longDataWordsLoopStride
            (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
    let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only at hbody ⊢
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap := sstoreAccountMap I.codeOwner σTail slot header
  let loadedHeader : UInt256 := bytesStoreLiteSetMappedHeaderWordOf σData I key
  let writeMem : ByteArray := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
    (by simpa [σLoop, tailSlot, tailWord, σTail, σData, slot, header, writeMem]
      using hbody)
  have hdata : bytesStoreLiteSetMappedHeaderWordOf σData I key = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σTail, σLoop, tailSlot, tailWord, slot, header,
      bytesStoreLiteSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some σTail I.codeOwner acc
        slot header
        (by simpa [σTail, σLoop, tailSlot, tailWord, slot] using haccTail) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, retMem] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := retMem)
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_size_96 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)))
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_read64 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
          (bytesStoreLiteWordAt0Mem_read64 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
            (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setMappedLongNoTailOldLongNoClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (haccData :
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) payloadStart
        (⟨0⟩ : UInt256) I (len.toNat / 32)).find? I.codeOwner = some acc) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap :=
    sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hbody := bytesStoreLiteX_setMappedLongNoTailOldLongNoClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong hnoTailMod
  exact bytesStoreLiteX_setMappedLongNoTailReturnsOfBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key) (acc := acc)
    hlenMax hlong
    (by simpa [slot, σLoop, σData] using hbody)
    (by simpa [slot] using haccData)

theorem bytesStoreLiteX_setMappedLongTailOldLongNoClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) payloadStart
          (⟨0⟩ : UInt256) I (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot
          (bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let tailSlot : UInt256 :=
      BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
    let tailWord : UInt256 :=
      BytesStoreLiteCore.longDataTailMaskedWord
        (bytesStoreLiteCalldataLongDataWord I payloadStart
          (BytesStoreLiteCore.longDataWordsLoopStride
            (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
    let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap :=
    sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hbody := bytesStoreLiteX_setMappedLongTailOldLongNoClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong htailMod
  exact bytesStoreLiteX_setMappedLongTailReturnsOfBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key) (acc := acc)
    hlenMax hlong
    (by simpa [slot, σLoop, tailSlot, tailWord, σTail, σData] using hbody)
    (by simpa [slot, σLoop, tailSlot, tailWord, σTail] using haccTail)

theorem bytesStoreLiteX_setMappedShortOldLongReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hshort : len.toNat < 32)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)) =
        ⟨0⟩)
    (hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩) =
        ⟨0⟩) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩ fuel
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
        key, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σClear) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let header : UInt256 := bytesStoreLiteSetMappedHeaderWordOf σ I key
  have hdecoder := bytesStoreLiteX_setMappedReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax
  have hstoredEq : UInt256.div header ⟨2⟩ = oldStoredLen := by
    simpa [header] using holdStoredLen.symm
  have hvalidHeader :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [header, hstoredEq] using hvalid
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩,
      len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header, slot] using hdecoder)
    (by simpa [header] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩,
          slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [slot, oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩,
        slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2637 with [
      jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldStoredLen ≠ ⟨0⟩ :=
    BytesStoreLiteCore.clearCurrentLongValid_gt31
      (header := header) (len := oldStoredLen)
      (by simpa [header] using hflag)
      (by simpa [header] using hvalid)
  have holdLong : UInt256.gt oldStoredLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldStoredLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldStoredLen from rfl]
    exact BytesStoreLiteCore.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have holdGtNat : 31 < oldStoredLen.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩ :=
    ugt_one (by omega)
  have hshortWord : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
    ult_one (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
  have hloopEntry := bytesStoreLiteX_writeBytesCleanupOldLongShortToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
    (len := len) (ret := ⟨2643⟩)
    (tail := [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
      key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hcleanupReach holdLong hgtOldNew hshortWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hloop := bytesStoreLiteX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)
    (base := (⟨0⟩ : UInt256) + bytesLikeDataBase slot)
    (dead₀ := slot) (dead₁ := oldStoredLen) (dead₂ := len)
    (ret := (⟨2643⟩ : UInt256))
    (rest := [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
      key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [slot] using hloop

theorem bytesStoreLiteX_setMappedShortOldLongReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hshort : len.toNat < 32) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
        key, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat) k C := by
  let count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [BytesStoreLiteCore.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreLiteX_setMappedShortOldLongReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (len := len) (payloadStart := payloadStart)
      (key := key) (oldStoredLen := oldStoredLen) (fuel := count.toNat)
      hperm hreach hlenMax hflag holdStoredLen hvalid hshort hcontinue hdone

theorem bytesStoreLiteX_setMappedShortNonemptyOldLongWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σClear slot
        (bytesStoreLiteSetMappedShortStoredWord I len payloadStart)) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hbranch := bytesStoreLiteX_setMappedShortOldLongReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (key := key) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hshort
  have hwrite := bytesStoreLiteX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm
    (by simpa [slot, σClear] using hbranch) hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σClear slot
      (bytesStoreLiteSetMappedShortStoredWord I len payloadStart))
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [bytesStoreLiteSetMappedShortStoredWord] using hwrite)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setMappedEmptyOldLongWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σClear slot ⟨0⟩) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hshort : len.toNat < 32 := by
    rw [hlenZero]
    native_decide
  have hbranch := bytesStoreLiteX_setMappedShortOldLongReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (key := key) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hshort
  have hpacked := bytesStoreLiteX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [slot, σClear] using hbranch) hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hwrite := bytesStoreLiteX_writeBytesNewEmptyWriteHeaderGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm hpacked hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σClear slot ⟨0⟩)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hwrite (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteSetMappedEmptyHeaderAfterWrite
    (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) :
    bytesStoreLiteSetMappedHeaderWordOf
        (sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedSlotOf key) ⟨0⟩) I key =
      ⟨0⟩ := by
  unfold bytesStoreLiteSetMappedHeaderWordOf
  change (((sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedSlotOf key) ⟨0⟩).find?
      I.codeOwner).option (default : UInt256)
      (fun acc => acc.storage.findD (bytesStoreLiteSetMappedSlotOf key) (default : UInt256))) =
    ⟨0⟩
  have h := sstoreAccountMap_storage_findD_eq_if σ I.codeOwner
    (bytesStoreLiteSetMappedSlotOf key) (bytesStoreLiteSetMappedSlotOf key) (⟨0⟩ : UInt256)
  rw [h]
  cases σ.find? I.codeOwner with
  | none =>
      simp [Option.option]
      rfl
  | some _ =>
      simp [Option.option]

theorem bytesStoreLiteX_setMappedShortNonemptyOldLongReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (haccClear :
      (clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat).find?
          I.codeOwner = some acc) :
    let storedWord := bytesStoreLiteSetMappedShortStoredWord I len payloadStart
    let σClear :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σClear (bytesStoreLiteSetMappedSlotOf key) storedWord
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray len) := by
  dsimp only
  let storedWord := bytesStoreLiteSetMappedShortStoredWord I len payloadStart
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σClear (bytesStoreLiteSetMappedSlotOf key) storedWord
  let header : UInt256 := bytesStoreLiteSetMappedHeaderWordOf σ' I key
  have hbody := bytesStoreLiteX_setMappedShortNonemptyOldLongWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hnz hshort
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreLiteSetMappedSlotOf key)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := wordAt0Mem (bytesStoreLiteSetMappedSlotOf key)
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (by
      exact wordAt0Mem_size_96 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    (by simpa [σ', σClear, storedWord] using hbody)
  have hdata : bytesStoreLiteSetMappedHeaderWordOf σ' I key = storedWord := by
    have hnzStored := bytesStoreLiteSetChunkShortStoredWord_beq_zero_false
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
    simpa [σ', σClear, storedWord, bytesStoreLiteSetMappedHeaderWordOf,
      bytesStoreLiteSetMappedShortStoredWord] using
      sstoreAccountMap_storage_findD_self_of_find_some σClear I.codeOwner acc
        (bytesStoreLiteSetMappedSlotOf key) storedWord
        (by simpa [σClear] using haccClear) hnzStored
  have hheader : header = storedWord := by
    simpa [header] using hdata
  have hflag' : UInt256.land header ⟨1⟩ = ⟨0⟩ := by
    rw [hheader]
    simpa [storedWord, bytesStoreLiteSetMappedShortStoredWord] using
      bytesStoreLiteSetChunkShortStoredWord_flag_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have hvalid' :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    rw [hheader]
    simp only [storedWord, bytesStoreLiteSetMappedShortStoredWord]
    rw [
      bytesStoreLiteSetChunkShortStoredWord_flag_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort,
      bytesStoreLiteSetChunkShortStoredWord_shortLen_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort]
    have hlt : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    rw [hlt]
    native_decide
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨1002⟩)
    (rest := [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩
      (wordAt0Mem (bytesStoreLiteSetMappedSlotOf key)
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [header] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded :
      UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ = len := by
    rw [hheader]
    simpa [storedWord, bytesStoreLiteSetMappedShortStoredWord] using
      bytesStoreLiteSetChunkShortStoredWord_shortLen_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have h263 := bytesStoreLiteX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := len)
    (slot := bytesStoreLiteSetMappedSlotOf key) (len := len) (payloadStart := payloadStart)
    (key := key)
    (mem := twoWordHashMem key ⟨4⟩
      (wordAt0Mem (bytesStoreLiteSetMappedSlotOf key)
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := twoWordHashMem key ⟨4⟩
      (wordAt0Mem (bytesStoreLiteSetMappedSlotOf key)
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
    (by
      exact twoWordHashMem_size_96 _ _
        (wordAt0Mem_size_96 _
          (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)))
    (by
      exact twoWordHashMem_read64 _ _
        (wordAt0Mem_size_96 _
          (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
        (bytesStoreLiteWordAt0Mem_read64 _
          (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
          (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)))
    h263

theorem bytesStoreLiteX_setMappedEmptyOldLongReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    let σClear :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σClear (bytesStoreLiteSetMappedSlotOf key) ⟨0⟩
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  dsimp only
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σClear (bytesStoreLiteSetMappedSlotOf key) ⟨0⟩
  have hbody := bytesStoreLiteX_setMappedEmptyOldLongWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hlenZero
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreLiteSetMappedSlotOf key)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := wordAt0Mem (bytesStoreLiteSetMappedSlotOf key)
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (by
      exact wordAt0Mem_size_96 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    (by simpa [σ', σClear] using hbody)
  have hheader : bytesStoreLiteSetMappedHeaderWordOf σ' I key = ⟨0⟩ := by
    simpa [σ'] using bytesStoreLiteSetMappedEmptyHeaderAfterWrite σClear I key
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := (⟨0⟩ : UInt256)) (ret := ⟨1002⟩)
    (rest := [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩
      (wordAt0Mem (bytesStoreLiteSetMappedSlotOf key)
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [hheader] using hdecoder)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h263 := bytesStoreLiteX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := (⟨0⟩ : UInt256))
    (slot := bytesStoreLiteSetMappedSlotOf key) (len := len) (payloadStart := payloadStart)
    (key := key)
    (mem := twoWordHashMem key ⟨4⟩
      (wordAt0Mem (bytesStoreLiteSetMappedSlotOf key)
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := twoWordHashMem key ⟨4⟩
      (wordAt0Mem (bytesStoreLiteSetMappedSlotOf key)
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
    (by
      exact twoWordHashMem_size_96 _ _
        (wordAt0Mem_size_96 _
          (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)))
    (by
      exact twoWordHashMem_read64 _ _
        (wordAt0Mem_size_96 _
          (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
        (bytesStoreLiteWordAt0Mem_read64 _
          (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
          (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)))
    h263

theorem bytesStoreLiteX_setMappedEmptyOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedSlotOf key) ⟨0⟩
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  dsimp only
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedSlotOf key) ⟨0⟩
  have hbody := bytesStoreLiteX_setMappedEmptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMax hflag hvalid hlenZero
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreLiteSetMappedSlotOf key)
    (len := len) (payloadStart := payloadStart) (key := key)
    (by simpa [σ'] using hbody)
  have hheader : bytesStoreLiteSetMappedHeaderWordOf σ' I key = ⟨0⟩ := by
    simpa [σ'] using bytesStoreLiteSetMappedEmptyHeaderAfterWrite σ I key
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := (⟨0⟩ : UInt256)) (ret := ⟨1002⟩)
    (rest := [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [hheader] using hdecoder)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h263 := bytesStoreLiteX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := (⟨0⟩ : UInt256))
    (slot := bytesStoreLiteSetMappedSlotOf key) (len := len) (payloadStart := payloadStart)
    (key := key)
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    (twoWordHashMem_read64 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
      (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
    h263

theorem bytesStoreLiteX_setMappedShortNonemptyOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hacc : σ.find? I.codeOwner = some acc) :
    let storedWord := bytesStoreLiteSetMappedShortStoredWord I len payloadStart
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedSlotOf key) storedWord
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray len) := by
  dsimp only
  let storedWord := bytesStoreLiteSetMappedShortStoredWord I len payloadStart
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedSlotOf key) storedWord
  let header : UInt256 := bytesStoreLiteSetMappedHeaderWordOf σ' I key
  have hbody := bytesStoreLiteX_setMappedShortNonemptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMax hflag hvalid hnz hshort
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreLiteSetMappedSlotOf key)
    (len := len) (payloadStart := payloadStart) (key := key)
    (by
      simpa [σ', storedWord, bytesStoreLiteSetMappedShortStoredWord] using hbody)
  have hdata : bytesStoreLiteSetMappedHeaderWordOf σ' I key = storedWord := by
    simpa [σ', storedWord, bytesStoreLiteSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreLiteSetMappedSlotOf key) storedWord hacc
  have hheader : header = storedWord := by
    simpa [header] using hdata
  have hflag' : UInt256.land header ⟨1⟩ = ⟨0⟩ := by
    rw [hheader]
    simpa [storedWord, bytesStoreLiteSetMappedShortStoredWord] using
      bytesStoreLiteSetChunkShortStoredWord_flag_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have hvalid' :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    rw [hheader]
    simp only [storedWord, bytesStoreLiteSetMappedShortStoredWord]
    rw [
      bytesStoreLiteSetChunkShortStoredWord_flag_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort,
      bytesStoreLiteSetChunkShortStoredWord_shortLen_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort]
    have hlt : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    rw [hlt]
    native_decide
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨1002⟩)
    (rest := [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded :
      UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ = len := by
    rw [hheader]
    simpa [storedWord, bytesStoreLiteSetMappedShortStoredWord] using
      bytesStoreLiteSetChunkShortStoredWord_shortLen_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have h263 := bytesStoreLiteX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := len)
    (slot := bytesStoreLiteSetMappedSlotOf key) (len := len) (payloadStart := payloadStart)
    (key := key)
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    (twoWordHashMem_read64 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
      (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
    h263

theorem bytesStoreLiteX_setMappedShortNonemptyOldShortAbsentReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hmissing : σ.find? I.codeOwner = none) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  let storedWord := bytesStoreLiteSetMappedShortStoredWord I len payloadStart
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σ (bytesStoreLiteSetMappedSlotOf key) storedWord
  have hbody := bytesStoreLiteX_setMappedShortNonemptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMax hflag hvalid hnz hshort
  have hsame : σ' = σ := by
    simpa [σ', storedWord] using
      sstoreAccountMap_absent_same (owner := I.codeOwner) (τ := σ)
        (slot := bytesStoreLiteSetMappedSlotOf key) (val := storedWord) hmissing
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreLiteSetMappedSlotOf key)
    (len := len) (payloadStart := payloadStart) (key := key)
    (by simpa [σ', storedWord, bytesStoreLiteSetMappedShortStoredWord] using hbody)
  have hheader : bytesStoreLiteSetMappedHeaderWordOf σ' I key = ⟨0⟩ := by
    dsimp [bytesStoreLiteSetMappedHeaderWordOf]
    rw [hsame, hmissing]
    rfl
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := (⟨0⟩ : UInt256)) (ret := ⟨1002⟩)
    (rest := [bytesStoreLiteSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [hheader] using hdecoder)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h263 := bytesStoreLiteX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := (⟨0⟩ : UInt256))
    (slot := bytesStoreLiteSetMappedSlotOf key) (len := len) (payloadStart := payloadStart)
    (key := key)
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa using hdecoded)
  have hret := bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := (⟨0⟩ : UInt256))
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    (twoWordHashMem_read64 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
      (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
    h263
  simpa [hsame] using hret

theorem bytesStoreLiteX_setMappedLongNoTailOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (haccData :
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) payloadStart
        (⟨0⟩ : UInt256) I (len.toNat / 32)).find? I.codeOwner = some acc) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap := sstoreAccountMap I.codeOwner σLoop slot header
  let loadedHeader : UInt256 := bytesStoreLiteSetMappedHeaderWordOf σData I key
  let writeMem : ByteArray := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hbody := bytesStoreLiteX_setMappedLongNoTailOldShortWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMaxWord hflag hvalid hlong hnoTailMod
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
    (by simpa [σLoop, σData, slot, header, writeMem] using hbody)
  have hdata : bytesStoreLiteSetMappedHeaderWordOf σData I key = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σLoop, slot, header, bytesStoreLiteSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some σLoop I.codeOwner acc
        slot header (by simpa [σLoop, slot] using haccData) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, retMem] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := retMem)
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_size_96 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)))
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_read64 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
          (bytesStoreLiteWordAt0Mem_read64 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
            (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setMappedLongTailOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) payloadStart
          (⟨0⟩ : UInt256) I (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot
          (bytesLikeDataBase (bytesStoreLiteSetMappedSlotOf key)) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
    let σLoop : AccountMap :=
      bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let tailSlot : UInt256 :=
      BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
    let tailWord : UInt256 :=
      BytesStoreLiteCore.longDataTailMaskedWord
        (bytesStoreLiteCalldataLongDataWord I payloadStart
          (BytesStoreLiteCore.longDataWordsLoopStride
            (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
    let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap := sstoreAccountMap I.codeOwner σTail slot header
  let loadedHeader : UInt256 := bytesStoreLiteSetMappedHeaderWordOf σData I key
  let writeMem : ByteArray := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hbody := bytesStoreLiteX_setMappedLongTailOldShortWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMaxWord hflag hvalid hlong htailMod
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
    (by simpa [σLoop, tailSlot, tailWord, σTail, σData, slot, header, writeMem]
      using hbody)
  have hdata : bytesStoreLiteSetMappedHeaderWordOf σData I key = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σTail, σLoop, tailSlot, tailWord, slot, header,
      bytesStoreLiteSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some σTail I.codeOwner acc
        slot header
        (by simpa [σTail, σLoop, tailSlot, tailWord, slot] using haccTail) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, retMem] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := retMem)
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_size_96 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)))
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_read64 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
          (bytesStoreLiteWordAt0Mem_read64 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
            (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setMappedLongNoTailOldShortAbsentReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (hmissing : σ.find? I.codeOwner = none) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap := sstoreAccountMap I.codeOwner σLoop slot header
  let writeMem : ByteArray := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hbody := bytesStoreLiteX_setMappedLongNoTailOldShortWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMaxWord hflag hvalid hlong hnoTailMod
  have hloopSame : σLoop = σ := by
    simpa [σLoop, slot] using
      bytesStoreLiteCalldataLongDataForwardFrom_absent_same
        (σ := σ) (owner := I.codeOwner) (slot := bytesLikeDataBase slot)
        (payloadStart := payloadStart) (stride := (⟨0⟩ : UInt256)) (I := I)
        hmissing (len.toNat / 32)
  have hdataSame : σData = σ := by
    dsimp [σData]
    rw [hloopSame]
    exact sstoreAccountMap_absent_same (owner := I.codeOwner) (τ := σ)
      (slot := slot) (val := header) hmissing
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
    (by simpa [σLoop, σData, slot, header, writeMem] using hbody)
  have hloaded : bytesStoreLiteSetMappedHeaderWordOf σData I key = ⟨0⟩ := by
    dsimp [bytesStoreLiteSetMappedHeaderWordOf]
    rw [hdataSame, hmissing]
    rfl
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreLiteSetMappedHeaderWordOf σData I key) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [retMem] using hdecoder)
    (by rw [hloaded]; native_decide)
    (by rw [hloaded]; native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h263 := bytesStoreLiteX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := (⟨0⟩ : UInt256)) (slot := slot)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hloaded] using hdecoded)
  have hret := bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := (⟨0⟩ : UInt256))
    (mem := retMem)
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_size_96 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)))
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_read64 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
          (bytesStoreLiteWordAt0Mem_read64 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
            (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)
  simpa [hdataSame] using hret

theorem bytesStoreLiteX_setMappedLongTailOldShortAbsentReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (hmissing : σ.find? I.codeOwner = none) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  let slot : UInt256 := bytesStoreLiteSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap := sstoreAccountMap I.codeOwner σTail slot header
  let writeMem : ByteArray := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hbody := bytesStoreLiteX_setMappedLongTailOldShortWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMaxWord hflag hvalid hlong htailMod
  have hloopSame : σLoop = σ := by
    simpa [σLoop, slot] using
      bytesStoreLiteCalldataLongDataForwardFrom_absent_same
        (σ := σ) (owner := I.codeOwner) (slot := bytesLikeDataBase slot)
        (payloadStart := payloadStart) (stride := (⟨0⟩ : UInt256)) (I := I)
        hmissing (len.toNat / 32)
  have htailSame : σTail = σ := by
    dsimp [σTail]
    rw [hloopSame]
    exact sstoreAccountMap_absent_same (owner := I.codeOwner) (τ := σ)
      (slot := tailSlot) (val := tailWord) hmissing
  have hdataSame : σData = σ := by
    dsimp [σData]
    rw [htailSame]
    exact sstoreAccountMap_absent_same (owner := I.codeOwner) (τ := σ)
      (slot := slot) (val := header) hmissing
  have hdecoder := bytesStoreLiteX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
    (by simpa [σLoop, tailSlot, tailWord, σTail, σData, slot, header, writeMem]
      using hbody)
  have hloaded : bytesStoreLiteSetMappedHeaderWordOf σData I key = ⟨0⟩ := by
    dsimp [bytesStoreLiteSetMappedHeaderWordOf]
    rw [hdataSame, hmissing]
    rfl
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreLiteSetMappedHeaderWordOf σData I key) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [retMem] using hdecoder)
    (by rw [hloaded]; native_decide)
    (by rw [hloaded]; native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h263 := bytesStoreLiteX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := (⟨0⟩ : UInt256)) (slot := slot)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := retMem) (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hloaded] using hdecoded)
  have hret := bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := (⟨0⟩ : UInt256))
    (mem := retMem)
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_size_96 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)))
    (by
      simpa [retMem, writeMem] using
        twoWordHashMem_read64 key ⟨4⟩
          (wordAt0Mem_size_96 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
          (bytesStoreLiteWordAt0Mem_read64 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
            (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)
  simpa [hdataSame] using hret

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedLongOldShortAbsentRuntimeOfReturn
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len key : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmissingEvm : σ_evm.find? I.codeOwner = none)
    (hkey : key = bytesStoreLiteSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlong : ¬ len.toNat < 32)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σ_evm) (UInt256.toByteArray (⟨0⟩ : UInt256))) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetMappedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hmissingSolm : σ_solm.find? I.codeOwner = none :=
    accountMapEquiv_find?_none hAccounts hmissingEvm
  have hmissingSolm0 :
      evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner = none := by
    simpa [evmSolm0, initState] using hmissingSolm
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evmSolm0 := by
    simpa [evmSolm0, value, bytesStoreLiteSetMappedRef, hkey] using
      bytesStoreLiteSetMappedWriteLongOldShortPackedAbsent
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        hAccounts hlenAbi hpayloadList hlong hflag hvalid hmissingSolm0
  have hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) = .ok 0 := by
    have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlotOf key) = (⟨0⟩ : UInt256) := by
      simp [Solm.EVM.storageLoad, State.lookupAccount, hmissingSolm0, Option.option]
    exact bytesStoreLiteReadLengthZeroOfHeaderLoad
      (er := bytesStoreLiteSetMappedRefOf key) (evm := evmSolm0)
      (baseSlot := bytesStoreLiteSetMappedSlotOf key)
      (bytesStoreLiteSetMappedRefOf_length_slot evmSolm0 key) hload
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreLiteSetMappedFrameOf key value) evmSolm0
          (some (.int 0))) := by
    have hlocals :
        bytesStoreLiteSetMappedLocals I = bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyReturnsOfWrite
      (evm := evmSolm0) (evm' := evmSolm0)
      (key := key) (value := value) (n := 0)
      (by simp [evmSolm0, initState]; exact hwv)
      hwrite hlenMapped
  have hCreated : (cA, σ_evm).1 = evmSolm0.createdAccounts := by
    simp [evmSolm0, initState]
  have henc :
      returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccounts henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedLongNoTailOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreLiteSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetMappedValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let σFinal := sstoreAccountMap I.codeOwner σLoop
    (bytesStoreLiteSetMappedSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetMappedSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreLiteSetMappedSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (bytesStoreLiteSetMappedSlot I))
      (payloadStart := payloadStart) (stride := (⟨0⟩ : UInt256)) (I := I)
      haccEvm (len.toNat / 32)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σLoop, bytesStoreLiteSetMappedSlot, hkey,
      bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf] using
      bytesStoreLiteX_setMappedLongNoTailOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key) (acc := accLoop)
        hperm hreach hlenMaxWord hlenMax
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
        hlong hnoTailMod
        (by simpa [σLoop, bytesStoreLiteSetMappedSlot, hkey] using haccLoop)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreLiteSetMappedWriteLongOldShortPacked
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts hlenAbi hpayloadList hlong hflag hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header,
      bytesStoreLiteSetMappedRef, hkey] using hwrite₀
  have hdataFuelEq : dataFuel = len.toNat / 32 := by
    dsimp [dataFuel]
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_eq_div_of_mod_zero hnoTailMod
  have hAccountsLoop : accountMapEquiv σLoop evmLoop.accountMap := by
    have hbridge :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (bytesStoreLiteSetMappedSlot I)
            value 0 (len.toNat / 32))
          σLoop := by
      simpa [σLoop, value, bytesStoreLiteSetMappedSlot] using
        accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          (baseSlot := bytesStoreLiteSetMappedSlot I) hsrc haddrBound hsizeDecoded hlenAbi
          hpayloadStart hoffMax (τ := σ_evm) (fuel := len.toNat / 32) (by rfl)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (bytesStoreLiteSetMappedSlot I)
            value 0 (len.toNat / 32))
          (solidityDataWordsForwardFrom I.codeOwner σ_solm (bytesStoreLiteSetMappedSlot I)
            value 0 (len.toNat / 32)) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
        (baseSlot := bytesStoreLiteSetMappedSlot I) (bytes := value)
        (idx := 0) (len.toNat / 32) hAccounts
    simpa [evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_accountMap, initState,
      hdataFuelEq] using accountMapEquiv.trans (accountMapEquiv.symm hbridge) hcong
  obtain ⟨accSolmLoop, haccSolmLoop⟩ :=
    accountMapEquiv_find?_some_exists hAccountsLoop haccLoop
  have hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreLiteSetMappedLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmLoop)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmLoop
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState,
      bytesStoreLiteSetMappedRef, hkey] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    have hAccountsData :
        accountMapEquiv
          (sstoreAccountMap I.codeOwner σLoop (bytesStoreLiteSetMappedSlot I)
            (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          evmData.accountMap := by
      simpa [evmData, evmLoop, hheaderEq,
        writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using
        accountMapEquiv_setMappedHeaderStore I evmLoop.executionEnv.codeOwner header
          hAccountsLoop
    simpa [σFinal] using hAccountsData
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreLiteSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreLiteSetMappedLocals I = bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyReturnsOfWrite
      (evm := evmSolm0) (evm' := evmData)
      (key := key) (value := value) (n := value.size)
      (by simp [evmSolm0, initState]; exact hwv)
      hwrite hlenMapped
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedLongNoTailOldLongNoClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreLiteSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetMappedValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let σFinal := sstoreAccountMap I.codeOwner σLoop
    (bytesStoreLiteSetMappedSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetMappedSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreLiteSetMappedSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (bytesStoreLiteSetMappedSlot I))
      (payloadStart := payloadStart) (stride := (⟨0⟩ : UInt256)) (I := I)
      haccEvm (len.toNat / 32)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σLoop, bytesStoreLiteSetMappedSlot, hkey,
      bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf] using
      bytesStoreLiteX_setMappedLongNoTailOldLongNoClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen) (acc := accLoop)
        hperm hreach hlenMaxWord hlenMax
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using holdStoredLen)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
        hgtOldNew hlong hnoTailMod
        (by simpa [σLoop, bytesStoreLiteSetMappedSlot, hkey] using haccLoop)
  have hOldLeLen : oldStoredLen.toNat ≤ len.toNat := by
    by_contra hle
    have hone : UInt256.gt oldStoredLen len = ⟨1⟩ :=
      ugt_one (Nat.lt_of_not_ge hle)
    rw [hone] at hgtOldNew
    have hbad : (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by native_decide
    exact hbad hgtOldNew
  have hdataFuelEq : dataFuel = len.toNat / 32 := by
    dsimp [dataFuel]
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_eq_div_of_mod_zero hnoTailMod
  have hclearCountZero :
      solidityBytesDataWordCount oldStoredLen.toNat -
          solidityBytesDataWordCount value.size = 0 := by
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_sub_eq_zero_of_le hOldLeLen
  have hdataCountEq : solidityBytesDataWordCount value.size = len.toNat / 32 := by
    simpa [dataFuel] using hdataFuelEq
  have hclearCountZeroLen :
      solidityBytesDataWordCount oldStoredLen.toNat - len.toNat / 32 = 0 := by
    simpa [hdataCountEq] using hclearCountZero
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreLiteSetMappedWriteLongOldLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      (oldStoredLen := oldStoredLen)
      hAccounts hlenAbi hpayloadList hlong hflag holdStoredLen hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header, hclearCountZero,
      hclearCountZeroLen, clearSolidityBytesDataWordsFrom, hdataFuelEq,
      bytesStoreLiteSetMappedRef, hkey] using hwrite₀
  have hAccountsLoop : accountMapEquiv σLoop evmLoop.accountMap := by
    have hbridge :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (bytesStoreLiteSetMappedSlot I)
            value 0 (len.toNat / 32))
          σLoop := by
      simpa [σLoop, value, bytesStoreLiteSetMappedSlot] using
        accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          (baseSlot := bytesStoreLiteSetMappedSlot I) hsrc haddrBound hsizeDecoded hlenAbi
          hpayloadStart hoffMax (τ := σ_evm) (fuel := len.toNat / 32) (by rfl)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (bytesStoreLiteSetMappedSlot I)
            value 0 (len.toNat / 32))
          (solidityDataWordsForwardFrom I.codeOwner σ_solm (bytesStoreLiteSetMappedSlot I)
            value 0 (len.toNat / 32)) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
        (baseSlot := bytesStoreLiteSetMappedSlot I) (bytes := value)
        (idx := 0) (len.toNat / 32) hAccounts
    simpa [evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_accountMap, initState,
      hdataFuelEq] using accountMapEquiv.trans (accountMapEquiv.symm hbridge) hcong
  obtain ⟨accSolmLoop, haccSolmLoop⟩ :=
    accountMapEquiv_find?_some_exists hAccountsLoop haccLoop
  have hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreLiteSetMappedLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmLoop)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmLoop
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState,
      bytesStoreLiteSetMappedRef, hkey] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    have hAccountsData :
        accountMapEquiv
          (sstoreAccountMap I.codeOwner σLoop (bytesStoreLiteSetMappedSlot I)
            (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          evmData.accountMap := by
      simpa [evmData, evmLoop, hheaderEq,
        writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using
        accountMapEquiv_setMappedHeaderStore I evmLoop.executionEnv.codeOwner header
          hAccountsLoop
    simpa [σFinal] using hAccountsData
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreLiteSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreLiteSetMappedLocals I = bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyReturnsOfWrite
      (evm := evmSolm0) (evm' := evmData)
      (key := key) (value := value) (n := value.size)
      (by simp [evmSolm0, initState]; exact hwv)
      hwrite hlenMapped
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedLongNoTailOldLongClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreLiteSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetMappedValueBytes I
  let oldFuel : Nat := (oldStoredLen.toNat + 31) / 32
  let clearFuel : Nat := (value.size + 31) / 32
  let tailFuel : Nat := oldFuel - clearFuel
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let clearCount : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) ⟨0⟩ clearCount.toNat
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let σFinal := sstoreAccountMap I.codeOwner σLoop
    (bytesStoreLiteSetMappedSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreLiteSetMappedSlot I) clearFuel tailFuel
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmClear (bytesStoreLiteSetMappedSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreLiteSetMappedSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  have holdGtNat : len.toNat < oldStoredLen.toNat :=
    BytesStoreLiteCore.ugt_eq_one_toNat_lt hgtOldNew
  have hclearFuelCeil : clearFuel = (len.toNat + 31) / 32 := by
    dsimp [clearFuel]
    rw [hsizeDecoded]
  have hdataFuelEq : dataFuel = len.toNat / 32 := by
    dsimp [dataFuel]
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_eq_div_of_mod_zero hnoTailMod
  have hclearFuelEq : clearFuel = len.toNat / 32 := by
    rw [hclearFuelCeil]
    exact solidityBytesDataWordCount_eq_div_of_mod_zero hnoTailMod
  have hclearLeOld : clearFuel ≤ oldFuel := by
    dsimp [oldFuel]
    rw [hclearFuelCeil]
    exact solidityBytesDataWordCount_mono (Nat.le_of_lt holdGtNat)
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 :=
    BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLiteSetMappedHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hnewShiftClear :
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩).toNat = clearFuel := by
    rw [hclearFuelCeil]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_u64 (x := len) hlenMax
  have hnewShiftEq :
      UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ = UInt256.ofNat clearFuel := by
    apply u256_inj
    rw [hnewShiftClear]
    exact (ulit_toNat' clearFuel (by
      have hlt : clearFuel < 2 ^ 251 := by
        rw [hclearFuelCeil]
        apply Nat.div_lt_of_lt_mul
        have hmax : ABI.solcMaxU64 + 31 < 2 ^ 251 * 32 := by
          norm_num [ABI.solcMaxU64]
        omega
      have hsize' : (2 : Nat) ^ 251 < UInt256.size := by
        norm_num [UInt256.size]
      omega)).symm
  have holdShiftNat :
      (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩).toNat = oldFuel := by
    dsimp [oldFuel]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_lt_sign (x := oldStoredLen) holdLenLt
  have hcountNat : clearCount.toNat = tailFuel := by
    dsimp [clearCount, tailFuel]
    rw [usub_toNat]
    · rw [holdShiftNat, hnewShiftClear]
    · rw [holdShiftNat, hnewShiftClear]
      exact hclearLeOld
  have hcountNatShift :
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.ofNat clearFuel)).toNat = tailFuel := by
    rw [← hnewShiftEq]
    simpa [clearCount] using hcountNat
  obtain ⟨accClear, haccClear⟩ :=
    clearDataWordsForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (base := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        bytesLikeDataBase (bytesStoreLiteSetMappedSlot I))
      (idx := (⟨0⟩ : UInt256)) haccEvm clearCount.toNat
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σClear) (owner := I.codeOwner) (acc := accClear)
      (slot := bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I)
      (by simpa [σClear, clearCount] using haccClear) (len.toNat / 32)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σLoop, σClear, clearCount, bytesStoreLiteSetMappedSlot, hkey,
      bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf] using
      bytesStoreLiteX_setMappedLongNoTailOldLongClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen) (acc := accLoop)
        hperm hreach hlenMaxWord hlenMax
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using holdStoredLen)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
        hgtOldNew hlong hnoTailMod
        (by simpa [σLoop, σClear, clearCount, bytesStoreLiteSetMappedSlot, hkey]
          using haccLoop)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreLiteSetMappedWriteLongOldLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      (oldStoredLen := oldStoredLen)
      hAccounts hlenAbi hpayloadList hlong hflag holdStoredLen hvalid
    simpa [evmSolm0, evmClear, evmLoop, evmData, value, dataFuel, header,
      oldFuel, clearFuel, tailFuel, solidityBytesDataWordCount,
      bytesStoreLiteSetMappedRef, hkey] using hwrite₀
  have hAccountsClear : accountMapEquiv σClear evmClear.accountMap := by
    have hshift := accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
      (owner := I.codeOwner) (σ := σ_evm) (τ := σ_solm)
      (baseSlot := bytesStoreLiteSetMappedSlot I) clearFuel (⟨0⟩ : UInt256) tailFuel
      hAccounts
    dsimp [σClear, evmClear, evmSolm0, clearCount]
    rw [hnewShiftEq, hcountNatShift]
    have hidxZero :
        UInt256.ofNat clearFuel + (⟨0⟩ : UInt256) = UInt256.ofNat clearFuel := by
      simpa using BytesStoreLiteCore.uint256_add_zero_right (UInt256.ofNat clearFuel)
    simpa [clearSolidityBytesDataWordsFrom_accountMap, initState, hidxZero,
      u256_add_comm (UInt256.ofNat clearFuel)
        (bytesLikeDataBase (bytesStoreLiteSetMappedSlot I))]
      using hshift
  have hAccountsLoop : accountMapEquiv σLoop evmLoop.accountMap := by
    have hbridge :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σClear (bytesStoreLiteSetMappedSlot I)
            value 0 (len.toNat / 32))
          σLoop := by
      simpa [σLoop, value, bytesStoreLiteSetMappedSlot] using
        accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          (baseSlot := bytesStoreLiteSetMappedSlot I) hsrc haddrBound hsizeDecoded hlenAbi
          hpayloadStart hoffMax (τ := σClear) (fuel := len.toNat / 32) (by rfl)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σClear (bytesStoreLiteSetMappedSlot I)
            value 0 (len.toNat / 32))
          (solidityDataWordsForwardFrom I.codeOwner evmClear.accountMap
            (bytesStoreLiteSetMappedSlot I) value 0 (len.toNat / 32)) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σClear) (σ := evmClear.accountMap)
        (baseSlot := bytesStoreLiteSetMappedSlot I) (bytes := value)
        (idx := 0) (len.toNat / 32) hAccountsClear
    simpa [evmLoop, evmClear, evmSolm0, writeSolidityBytesDataWordsFrom_accountMap,
      clearSolidityBytesDataWordsFrom_executionEnv, initState, hdataFuelEq] using
      accountMapEquiv.trans (accountMapEquiv.symm hbridge) hcong
  obtain ⟨accSolmLoop, haccSolmLoop⟩ :=
    accountMapEquiv_find?_some_exists hAccountsLoop haccLoop
  have hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreLiteSetMappedLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmLoop)
      (by simp [evmLoop, evmClear, evmSolm0, initState,
        writeSolidityBytesDataWordsFrom_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv])
      haccSolmLoop
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState,
      bytesStoreLiteSetMappedRef, hkey] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState, header] using
      accountMapEquiv_setMappedHeaderStore I evmLoop.executionEnv.codeOwner header
        hAccountsLoop
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreLiteSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreLiteSetMappedLocals I = bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyReturnsOfWrite
      (evm := evmSolm0) (evm' := evmData)
      (key := key) (value := value) (n := value.size)
      (by simp [evmSolm0, initState]; exact hwv)
      hwrite hlenMapped
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmLoop, evmClear, evmSolm0,
      writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedLongTailOldLongClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreLiteSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetMappedValueBytes I
  let oldFuel : Nat := (oldStoredLen.toNat + 31) / 32
  let clearFuel : Nat := (value.size + 31) / 32
  let tailFuel : Nat := oldFuel - clearFuel
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let clearCount : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) ⟨0⟩ clearCount.toNat
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
        0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σFinal := sstoreAccountMap I.codeOwner σTail
    (bytesStoreLiteSetMappedSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreLiteSetMappedSlot I) clearFuel tailFuel
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmClear (bytesStoreLiteSetMappedSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreLiteSetMappedSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  have holdGtNat : len.toNat < oldStoredLen.toNat :=
    BytesStoreLiteCore.ugt_eq_one_toNat_lt hgtOldNew
  have hclearFuelCeil : clearFuel = (len.toNat + 31) / 32 := by
    dsimp [clearFuel]
    rw [hsizeDecoded]
  have hdataFuelEq : dataFuel = len.toNat / 32 + 1 := by
    dsimp [dataFuel]
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_eq_div_succ_of_mod_ne htailMod
  have hdataCountEq :
      solidityBytesDataWordCount (bytesStoreLiteSetMappedValueBytes I).size =
        len.toNat / 32 + 1 := by
    simpa [dataFuel, value] using hdataFuelEq
  have hclearLeOld : clearFuel ≤ oldFuel := by
    dsimp [oldFuel]
    rw [hclearFuelCeil]
    exact solidityBytesDataWordCount_mono (Nat.le_of_lt holdGtNat)
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 :=
    BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLiteSetMappedHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hnewShiftClear :
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩).toNat = clearFuel := by
    rw [hclearFuelCeil]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_u64 (x := len) hlenMax
  have hnewShiftEq :
      UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ = UInt256.ofNat clearFuel := by
    apply u256_inj
    rw [hnewShiftClear]
    exact (ulit_toNat' clearFuel (by
      have hlt : clearFuel < 2 ^ 251 := by
        rw [hclearFuelCeil]
        apply Nat.div_lt_of_lt_mul
        have hmax : ABI.solcMaxU64 + 31 < 2 ^ 251 * 32 := by
          norm_num [ABI.solcMaxU64]
        omega
      have hsize' : (2 : Nat) ^ 251 < UInt256.size := by
        norm_num [UInt256.size]
      omega)).symm
  have holdShiftNat :
      (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩).toNat = oldFuel := by
    dsimp [oldFuel]
    exact bytesStoreLite_shiftRight_add31_five_toNat_of_lt_sign (x := oldStoredLen) holdLenLt
  have hcountNat : clearCount.toNat = tailFuel := by
    dsimp [clearCount, tailFuel]
    rw [usub_toNat]
    · rw [holdShiftNat, hnewShiftClear]
    · rw [holdShiftNat, hnewShiftClear]
      exact hclearLeOld
  have hcountNatShift :
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.ofNat clearFuel)).toNat = tailFuel := by
    rw [← hnewShiftEq]
    simpa [clearCount] using hcountNat
  obtain ⟨accClear, haccClear⟩ :=
    clearDataWordsForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (base := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        bytesLikeDataBase (bytesStoreLiteSetMappedSlot I))
      (idx := (⟨0⟩ : UInt256)) haccEvm clearCount.toNat
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σClear) (owner := I.codeOwner) (acc := accClear)
      (slot := bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I)
      (by simpa [σClear, clearCount] using haccClear) (len.toNat / 32)
  obtain ⟨accTail, haccTail⟩ :=
    sstoreAccountMap_find?_some_exists_of_find_some
      (σ := σLoop) (a := I.codeOwner) (acc := accLoop)
      (slot := tailSlot) (val := tailWord)
      (by simpa [σLoop, σClear, clearCount] using haccLoop)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σTail, σLoop, σClear, clearCount, tailSlot, tailWord,
      bytesStoreLiteSetMappedSlot, hkey,
      bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf] using
      bytesStoreLiteX_setMappedLongTailOldLongClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen) (acc := accTail)
        hperm hreach hlenMaxWord hlenMax
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using holdStoredLen)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
        hgtOldNew hlong htailMod
        (by simpa [σTail, σLoop, σClear, clearCount, tailSlot, tailWord,
          bytesStoreLiteSetMappedSlot, hkey] using haccTail)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreLiteSetMappedWriteLongOldLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      (oldStoredLen := oldStoredLen)
      hAccounts hlenAbi hpayloadList hlong hflag holdStoredLen hvalid
    simpa [evmSolm0, evmClear, evmLoop, evmData, value, dataFuel, header,
      oldFuel, clearFuel, tailFuel, solidityBytesDataWordCount,
      bytesStoreLiteSetMappedRef, hkey] using hwrite₀
  have hAccountsClear : accountMapEquiv σClear evmClear.accountMap := by
    have hshift := accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
      (owner := I.codeOwner) (σ := σ_evm) (τ := σ_solm)
      (baseSlot := bytesStoreLiteSetMappedSlot I) clearFuel (⟨0⟩ : UInt256) tailFuel
      hAccounts
    dsimp [σClear, evmClear, evmSolm0, clearCount]
    rw [hnewShiftEq, hcountNatShift]
    have hidxZero :
        UInt256.ofNat clearFuel + (⟨0⟩ : UInt256) = UInt256.ofNat clearFuel := by
      simpa using BytesStoreLiteCore.uint256_add_zero_right (UInt256.ofNat clearFuel)
    simpa [clearSolidityBytesDataWordsFrom_accountMap, initState, hidxZero,
      u256_add_comm (UInt256.ofNat clearFuel)
        (bytesLikeDataBase (bytesStoreLiteSetMappedSlot I))]
      using hshift
  have hAccountsTail : accountMapEquiv σTail evmLoop.accountMap := by
    let baseSlot : UInt256 := bytesStoreLiteSetMappedSlot I
    let fullFuel : Nat := len.toNat / 32
    have hbridgeEvm :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σClear baseSlot value 0 fullFuel)
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel) := by
      exact accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
        (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
        (baseSlot := baseSlot) hsrc haddrBound hsizeDecoded hlenAbi hpayloadStart hoffMax
        (τ := σClear) (fuel := fullFuel) (by dsimp [fullFuel]; omega)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σClear baseSlot value 0 fullFuel)
          (solidityDataWordsForwardFrom I.codeOwner evmClear.accountMap baseSlot value 0
            fullFuel) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σClear) (σ := evmClear.accountMap)
        (baseSlot := baseSlot) (bytes := value) (idx := 0) fullFuel hAccountsClear
    have hdataFull :
        accountMapEquiv
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
          (solidityDataWordsForwardFrom I.codeOwner evmClear.accountMap baseSlot value 0
            fullFuel) :=
      accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
    have htailWord :
        BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (UInt256.ofNat (32 * fullFuel)) 0) len =
          uInt256OfByteArray (value.readWithPadding (fullFuel * 32) 32) := by
      simpa [value, bytesStoreLiteSetMappedValueBytes, fullFuel, Nat.mul_comm] using
        bytesStoreLiteSetChunkCalldataLongDataTailMaskedWord_eq_decoded_tail
          (I := I) (len := len) (payloadStart := payloadStart)
          htailAddr hsrc hsizeDecoded hlenAbi hpayloadStart hoffMax hlong htailMod
    have hslotEq :
        BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel =
          solidityBytesDataSlot baseSlot fullFuel := by
      exact bytesStoreLiteLongDataWordsLoopSlot_bytesLikeDataBase baseSlot fullFuel
    have htailStore :=
      accountMapEquiv_sstore_solidityDataWordsForwardFrom_succ_last
        (owner := I.codeOwner) (σ := bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
          σClear (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
        (τ := evmClear.accountMap) (baseSlot := baseSlot)
        (slot := BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
        (word := BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len)
        (bytes := value) (idx := 0) (fuel := fullFuel)
        hdataFull (by simpa using hslotEq) (by simpa using htailWord)
    simpa [σTail, σLoop, σClear, clearCount, tailSlot, tailWord, evmLoop, evmClear,
      evmSolm0, initState, value, baseSlot, fullFuel, hdataFuelEq,
      writeSolidityBytesDataWordsFrom_accountMap,
      clearSolidityBytesDataWordsFrom_executionEnv,
      bytesStoreLiteLongDataWordsLoopStride_zero_ofNat] using htailStore
  obtain ⟨accSolmTail, haccSolmTail⟩ :=
    accountMapEquiv_find?_some_exists hAccountsTail haccTail
  have hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreLiteSetMappedLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmTail)
      (by simp [evmLoop, evmClear, evmSolm0, initState,
        writeSolidityBytesDataWordsFrom_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv])
      haccSolmTail
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState,
      bytesStoreLiteSetMappedRef, hkey] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState, header] using
      accountMapEquiv_setMappedHeaderStore I evmLoop.executionEnv.codeOwner header
        hAccountsTail
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreLiteSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreLiteSetMappedLocals I = bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyReturnsOfWrite
      (evm := evmSolm0) (evm' := evmData)
      (key := key) (value := value) (n := value.size)
      (by simp [evmSolm0, initState]; exact hwv)
      hwrite hlenMapped
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmLoop, evmClear, evmSolm0,
      writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedLongTailOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreLiteSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetMappedValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
        0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σFinal := sstoreAccountMap I.codeOwner σTail
    (bytesStoreLiteSetMappedSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetMappedSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreLiteSetMappedSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (bytesStoreLiteSetMappedSlot I))
      (payloadStart := payloadStart) (stride := (⟨0⟩ : UInt256)) (I := I)
      haccEvm (len.toNat / 32)
  obtain ⟨accTail, haccTail⟩ :=
    sstoreAccountMap_find?_some_exists_of_find_some
      (σ := σLoop) (a := I.codeOwner) (acc := accLoop)
      (slot := tailSlot) (val := tailWord) (by simpa [σLoop] using haccLoop)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σTail, σLoop, tailSlot, tailWord, bytesStoreLiteSetMappedSlot, hkey,
      bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf] using
      bytesStoreLiteX_setMappedLongTailOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key) (acc := accTail)
        hperm hreach hlenMaxWord hlenMax
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
        hlong htailMod
        (by simpa [σTail, σLoop, tailSlot, tailWord, bytesStoreLiteSetMappedSlot, hkey]
          using haccTail)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreLiteSetMappedWriteLongOldShortPacked
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts hlenAbi hpayloadList hlong hflag hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header,
      bytesStoreLiteSetMappedRef, hkey] using hwrite₀
  have hdataFuelEq : dataFuel = len.toNat / 32 + 1 := by
    dsimp [dataFuel]
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_eq_div_succ_of_mod_ne htailMod
  have hAccountsTail : accountMapEquiv σTail evmLoop.accountMap := by
    let baseSlot : UInt256 := bytesStoreLiteSetMappedSlot I
    let fullFuel : Nat := len.toNat / 32
    have hbridgeEvm :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm baseSlot value 0 fullFuel)
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel) := by
      exact accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
        (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
        (baseSlot := baseSlot) hsrc haddrBound hsizeDecoded hlenAbi hpayloadStart hoffMax
        (τ := σ_evm) (fuel := fullFuel) (by dsimp [fullFuel]; omega)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm baseSlot value 0 fullFuel)
          (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot value 0 fullFuel) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
        (baseSlot := baseSlot) (bytes := value) (idx := 0) fullFuel hAccounts
    have hdataFull :
        accountMapEquiv
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
          (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot value 0 fullFuel) :=
      accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
    have htailWord :
        BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (UInt256.ofNat (32 * fullFuel)) 0) len =
          uInt256OfByteArray (value.readWithPadding (fullFuel * 32) 32) := by
      simpa [value, bytesStoreLiteSetMappedValueBytes, fullFuel, Nat.mul_comm] using
        bytesStoreLiteSetChunkCalldataLongDataTailMaskedWord_eq_decoded_tail
          (I := I) (len := len) (payloadStart := payloadStart)
          htailAddr hsrc hsizeDecoded hlenAbi hpayloadStart hoffMax hlong htailMod
    have hslotEq :
        BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel =
          solidityBytesDataSlot baseSlot fullFuel := by
      exact bytesStoreLiteLongDataWordsLoopSlot_bytesLikeDataBase baseSlot fullFuel
    have htailStore :=
      accountMapEquiv_sstore_solidityDataWordsForwardFrom_succ_last
        (owner := I.codeOwner) (σ := bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
          σ_evm (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
        (τ := σ_solm) (baseSlot := baseSlot)
        (slot := BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
        (word := BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len)
        (bytes := value) (idx := 0) (fuel := fullFuel)
        hdataFull (by simpa using hslotEq) (by simpa using htailWord)
    simpa [σTail, σLoop, tailSlot, tailWord, evmLoop, evmSolm0, initState, value,
      baseSlot, fullFuel, hdataFuelEq, writeSolidityBytesDataWordsFrom_accountMap,
      bytesStoreLiteLongDataWordsLoopStride_zero_ofNat] using htailStore
  obtain ⟨accSolmTail, haccSolmTail⟩ :=
    accountMapEquiv_find?_some_exists hAccountsTail haccTail
  have hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreLiteSetMappedLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmTail)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmTail
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState,
      bytesStoreLiteSetMappedRef, hkey] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState, header] using
      accountMapEquiv_setMappedHeaderStore I evmLoop.executionEnv.codeOwner header
        hAccountsTail
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreLiteSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreLiteSetMappedLocals I = bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyReturnsOfWrite
      (evm := evmSolm0) (evm' := evmData)
      (key := key) (value := value) (n := value.size)
      (by simp [evmSolm0, initState]; exact hwv)
      hwrite hlenMapped
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedLongTailOldLongNoClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreLiteSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetMappedValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
        0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σFinal := sstoreAccountMap I.codeOwner σTail
    (bytesStoreLiteSetMappedSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreLiteSetMappedSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreLiteSetMappedSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (bytesStoreLiteSetMappedSlot I))
      (payloadStart := payloadStart) (stride := (⟨0⟩ : UInt256)) (I := I)
      haccEvm (len.toNat / 32)
  obtain ⟨accTail, haccTail⟩ :=
    sstoreAccountMap_find?_some_exists_of_find_some
      (σ := σLoop) (a := I.codeOwner) (acc := accLoop)
      (slot := tailSlot) (val := tailWord) (by simpa [σLoop] using haccLoop)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σTail, σLoop, tailSlot, tailWord, bytesStoreLiteSetMappedSlot, hkey,
      bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf] using
      bytesStoreLiteX_setMappedLongTailOldLongNoClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen) (acc := accTail)
        hperm hreach hlenMaxWord hlenMax
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using holdStoredLen)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
        hgtOldNew hlong htailMod
        (by simpa [σTail, σLoop, tailSlot, tailWord, bytesStoreLiteSetMappedSlot, hkey]
          using haccTail)
  have hOldLeLen : oldStoredLen.toNat ≤ len.toNat := by
    by_contra hle
    have hone : UInt256.gt oldStoredLen len = ⟨1⟩ :=
      ugt_one (Nat.lt_of_not_ge hle)
    rw [hone] at hgtOldNew
    have hbad : (⟨1⟩ : UInt256) ≠ ⟨0⟩ := by native_decide
    exact hbad hgtOldNew
  have hdataFuelEq : dataFuel = len.toNat / 32 + 1 := by
    dsimp [dataFuel]
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_eq_div_succ_of_mod_ne htailMod
  have hclearCountZero :
      solidityBytesDataWordCount oldStoredLen.toNat -
          solidityBytesDataWordCount value.size = 0 := by
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_sub_eq_zero_of_le hOldLeLen
  have hdataCountEq : solidityBytesDataWordCount value.size = len.toNat / 32 + 1 := by
    simpa [dataFuel] using hdataFuelEq
  have hclearCountZeroLen :
      solidityBytesDataWordCount oldStoredLen.toNat - (len.toNat / 32 + 1) = 0 := by
    simpa [hdataCountEq] using hclearCountZero
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreLiteSetMappedWriteLongOldLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      (oldStoredLen := oldStoredLen)
      hAccounts hlenAbi hpayloadList hlong hflag holdStoredLen hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header, hclearCountZero,
      hclearCountZeroLen, clearSolidityBytesDataWordsFrom, hdataFuelEq,
      bytesStoreLiteSetMappedRef, hkey] using hwrite₀
  have hAccountsTail : accountMapEquiv σTail evmLoop.accountMap := by
    let baseSlot : UInt256 := bytesStoreLiteSetMappedSlot I
    let fullFuel : Nat := len.toNat / 32
    have hbridgeEvm :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm baseSlot value 0 fullFuel)
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel) := by
      exact accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
        (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
        (baseSlot := baseSlot) hsrc haddrBound hsizeDecoded hlenAbi hpayloadStart hoffMax
        (τ := σ_evm) (fuel := fullFuel) (by dsimp [fullFuel]; omega)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm baseSlot value 0 fullFuel)
          (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot value 0 fullFuel) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
        (baseSlot := baseSlot) (bytes := value) (idx := 0) fullFuel hAccounts
    have hdataFull :
        accountMapEquiv
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
          (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot value 0 fullFuel) :=
      accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
    have htailWord :
        BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (UInt256.ofNat (32 * fullFuel)) 0) len =
          uInt256OfByteArray (value.readWithPadding (fullFuel * 32) 32) := by
      simpa [value, bytesStoreLiteSetMappedValueBytes, fullFuel, Nat.mul_comm] using
        bytesStoreLiteSetChunkCalldataLongDataTailMaskedWord_eq_decoded_tail
          (I := I) (len := len) (payloadStart := payloadStart)
          htailAddr hsrc hsizeDecoded hlenAbi hpayloadStart hoffMax hlong htailMod
    have hslotEq :
        BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel =
          solidityBytesDataSlot baseSlot fullFuel := by
      exact bytesStoreLiteLongDataWordsLoopSlot_bytesLikeDataBase baseSlot fullFuel
    have htailStore :=
      accountMapEquiv_sstore_solidityDataWordsForwardFrom_succ_last
        (owner := I.codeOwner) (σ := bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
          σ_evm (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
        (τ := σ_solm) (baseSlot := baseSlot)
        (slot := BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
        (word := BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len)
        (bytes := value) (idx := 0) (fuel := fullFuel)
        hdataFull (by simpa using hslotEq) (by simpa using htailWord)
    simpa [σTail, σLoop, tailSlot, tailWord, evmLoop, evmSolm0, initState, value,
      baseSlot, fullFuel, hdataFuelEq, writeSolidityBytesDataWordsFrom_accountMap,
      bytesStoreLiteLongDataWordsLoopStride_zero_ofNat] using htailStore
  obtain ⟨accSolmTail, haccSolmTail⟩ :=
    accountMapEquiv_find?_some_exists hAccountsTail haccTail
  have hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreLiteSetMappedLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmTail)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmTail
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState,
      bytesStoreLiteSetMappedRef, hkey] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState, header] using
      accountMapEquiv_setMappedHeaderStore I evmLoop.executionEnv.codeOwner header
        hAccountsTail
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreLiteSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreLiteSetMappedLocals I = bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyReturnsOfWrite
      (evm := evmSolm0) (evm' := evmData)
      (key := key) (value := value) (n := value.size)
      (by simp [evmSolm0, initState]; exact hwv)
      hwrite hlenMapped
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedShortNonemptyOldLongRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreLiteSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetMappedValueBytes I
  let storedWord := bytesStoreLiteSetMappedShortStoredWord I len payloadStart
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σFinal := sstoreAccountMap I.codeOwner σClear
    (bytesStoreLiteSetMappedSlot I) storedWord
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreLiteSetMappedSlot I) 0 ((oldStoredLen.toNat + 31) / 32)
  let evmData := Solm.EVM.storageStore evmClear I.codeOwner
    (bytesStoreLiteSetMappedSlot I) (solidityShortBytesWord value)
  obtain ⟨accClear, haccClear⟩ :=
    clearDataWordsForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (base := ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)))
      (idx := ⟨0⟩) haccEvm
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σClear, storedWord, bytesStoreLiteSetMappedSlot, hkey,
      bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf] using
      bytesStoreLiteX_setMappedShortNonemptyOldLongReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen) (acc := accClear)
        hperm hreach hlenMax
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using holdStoredLen)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
        hnz hshort
        (by simpa [σClear, bytesStoreLiteSetMappedSlot, hkey] using haccClear)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    simpa [evmSolm0, evmClear, evmData, value, bytesStoreLiteSetMappedRef, hkey] using
      bytesStoreLiteSetMappedWriteShortOldLongPrepared
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        (oldStoredLen := oldStoredLen)
        hAccounts hpayloadList hlenAbi hshort hflag holdStoredLen hvalid
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value, bytesStoreLiteSetMappedShortStoredWord,
      bytesStoreLiteSetMappedValueBytes] using
      bytesStoreLiteSetChunkShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayloadList
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  obtain ⟨accSolmClear, haccSolmClear⟩ :=
    clearDataWordsForwardFrom_find?_some_exists_of_find_some
      (σ := σ_solm) (owner := I.codeOwner) (acc := accSolm)
      (base := solidityBytesDataBaseSlot (bytesStoreLiteSetMappedSlot I))
      (idx := UInt256.ofNat 0) haccSolm ((oldStoredLen.toNat + 31) / 32)
  have haccEvmClear :
      evmClear.accountMap.find? I.codeOwner = some accSolmClear := by
    simpa [evmClear, evmSolm0, initState, clearSolidityBytesDataWordsFrom_accountMap]
      using haccSolmClear
  have hvalueSize : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreLiteSetMappedLengthAfterShortStoreOfState
      (evm := evmClear) (I := I) (len := len) (payloadStart := payloadStart)
      (acc := accSolmClear)
      (by simp [evmClear, evmSolm0, initState, clearSolidityBytesDataWordsFrom_executionEnv])
      haccEvmClear hnz hshort
    simpa [evmClear, evmData, storedWord, hstored, hvalueSize,
      bytesStoreLiteSetMappedRef, hkey] using hlen₀
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 := by
    exact BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLiteSetMappedHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, σClear, evmData, evmClear, evmSolm0, value, storedWord, initState,
      clearSolidityBytesDataWordsFrom_executionEnv] using
      bytesStoreLiteSetMappedShortFromLongPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (oldLen := oldStoredLen) (storedWord := storedWord) (value := value)
        hAccounts hstored holdLenLt
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreLiteSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreLiteSetMappedLocals I = bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyReturnsOfWrite
      (evm := evmSolm0) (evm' := evmData)
      (key := key) (value := value) (n := value.size)
      (by simp [evmSolm0, initState]; exact hwv)
      hwrite hlenMapped
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmClear, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hvalueSize]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedEmptyOldLongRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key oldStoredLen : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreLiteSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩)
    (hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetMappedValueBytes I
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreLiteSetMappedSlot I)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σFinal := sstoreAccountMap I.codeOwner σClear (bytesStoreLiteSetMappedSlot I) ⟨0⟩
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreLiteSetMappedSlot I) 0 ((oldStoredLen.toNat + 31) / 32)
  let evmData := Solm.EVM.storageStore evmClear I.codeOwner (bytesStoreLiteSetMappedSlot I) ⟨0⟩
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    simpa [σFinal, σClear, bytesStoreLiteSetMappedSlot, hkey,
      bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf] using
      bytesStoreLiteX_setMappedEmptyOldLongReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen)
        hperm hreach hlenMax
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using holdStoredLen)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
        hlenZero
  have hvalueSize0 : value.size = 0 := by
    dsimp [value]
    rw [bytesStoreLiteSetMappedValueBytes_size hpayloadList, hlenZeroAbi]
    rfl
  have hvalueEmpty : value = ByteArray.empty :=
    byteArray_eq_empty_of_size_eq_zero value hvalueSize0
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hshort : len.toNat < 32 := by
      rw [hlenZero]
      native_decide
    have hwrite₀ := bytesStoreLiteSetMappedWriteShortOldLongPrepared
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        (oldStoredLen := oldStoredLen)
        hAccounts hpayloadList (by rw [hlenZero, hlenZeroAbi]) hshort
        hflag holdStoredLen hvalid
    simpa [evmSolm0, evmClear, evmData, value, hvalueEmpty, hshortEmpty,
      bytesStoreLiteSetMappedRef, hkey] using hwrite₀
  have hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evmData
        (bytesStoreLiteSetMappedRefOf key) = .ok 0 := by
    have hlen₀ := bytesStoreLiteSetMappedLengthAfterEmptyStoreOfState
      (evm := evmClear) (I := I)
      (by simp [evmClear, evmSolm0, initState, clearSolidityBytesDataWordsFrom_executionEnv])
    simpa [evmClear, evmData, bytesStoreLiteSetMappedRef, hkey] using hlen₀
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 := by
    exact BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLiteSetMappedHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, σClear, evmData, evmClear, evmSolm0, initState,
      clearSolidityBytesDataWordsFrom_executionEnv] using
      bytesStoreLiteSetMappedEmptyFromLongPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (oldLen := oldStoredLen) hAccounts holdLenLt
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreLiteSetMappedFrameOf key value) evmData
          (some (.int 0))) := by
    have hlocals :
        bytesStoreLiteSetMappedLocals I = bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyReturnsOfWrite
      (evm := evmSolm0) (evm' := evmData)
      (key := key) (value := value) (n := 0)
      (by simp [evmSolm0, initState]; exact hwv)
      hwrite hlenMapped
  have hCreated : (cA, σFinal).1 = evmData.createdAccounts := by
    simp [evmData, evmClear, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have henc :
      returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

theorem bytesStoreLiteSetMappedEmptyOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreLiteSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩)
    (hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetMappedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetMappedSlot I) ⟨0⟩
  let σFinal := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetMappedSlot I) ⟨0⟩
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    simpa [σFinal, bytesStoreLiteSetMappedSlot, hkey,
      bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf] using
      bytesStoreLiteX_setMappedEmptyOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        hperm hreach hlenMax
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
        hlenZero
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, value, bytesStoreLiteSetMappedRef, hkey] using
      bytesStoreLiteSetMappedWriteEmptyOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hAccounts hpayloadList hlenZeroAbi hflag hvalid
  have hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evmSolm1
        (bytesStoreLiteSetMappedRefOf key) = .ok 0 := by
    simpa [evmSolm0, evmSolm1, bytesStoreLiteSetMappedRef, hkey] using
      bytesStoreLiteSetMappedLengthAfterEmptyWrite
        (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreLiteSetMappedFrameOf key value) evmSolm1
          (some (.int 0))) := by
    have hlocals :
        bytesStoreLiteSetMappedLocals I = bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyReturnsOfWrite
      (evm := evmSolm0) (evm' := evmSolm1)
      (key := key) (value := value) (n := 0)
      (by simp [evmSolm0, initState]; exact hwv)
      hwrite hlenMapped
  have hCreated : (cA, σFinal).1 = evmSolm1.createdAccounts := by
    simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts]
  have hAccountsPost : accountMapEquiv σFinal evmSolm1.accountMap := by
    simpa [σFinal, evmSolm1, evmSolm0, initState] using
      accountMapEquiv_storageStore_initState_codeOwner
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetMappedSlot I) ⟨0⟩
  have henc :
      returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedShortNonemptyOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreLiteSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetMappedValueBytes I
  let storedWord := bytesStoreLiteSetMappedShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreLiteSetMappedSlot I) (solidityShortBytesWord value)
  let σFinal := sstoreAccountMap I.codeOwner σ_evm (bytesStoreLiteSetMappedSlot I) storedWord
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, storedWord, bytesStoreLiteSetMappedSlot, hkey,
      bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf] using
      bytesStoreLiteX_setMappedShortNonemptyOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key) (acc := accEvm)
        hperm hreach hlenMax
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreLiteSetMappedHeaderWord,
          bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
        hnz hshort haccEvm
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, value, bytesStoreLiteSetMappedRef, hkey] using
      bytesStoreLiteSetMappedWriteShortOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        hAccounts hpayloadList hlenAbi hshort hflag hvalid
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value, bytesStoreLiteSetMappedShortStoredWord,
      bytesStoreLiteSetMappedValueBytes] using
      bytesStoreLiteSetChunkShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayloadList
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hvalueSize : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreLiteSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evmSolm1
        (bytesStoreLiteSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreLiteSetMappedLengthAfterShortWrite
      (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (len := len) (payloadStart := payloadStart) (acc := accSolm)
      haccSolm hnz hshort
    simpa [evmSolm0, evmSolm1, value, storedWord, hstored, hvalueSize,
      bytesStoreLiteSetMappedRef, hkey] using hlen₀
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreLiteSetMappedFrameOf key value) evmSolm1
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreLiteSetMappedLocals I = bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyReturnsOfWrite
      (evm := evmSolm0) (evm' := evmSolm1)
      (key := key) (value := value) (n := value.size)
      (by simp [evmSolm0, initState]; exact hwv)
      hwrite hlenMapped
  have hCreated : (cA, σFinal).1 = evmSolm1.createdAccounts := by
    simp [evmSolm1, evmSolm0, initState, storageStore_createdAccounts]
  have hAccountsPost : accountMapEquiv σFinal evmSolm1.accountMap := by
    simpa [σFinal, evmSolm1, evmSolm0, initState, hstored] using
      accountMapEquiv_storageStore_initState_codeOwner
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (bytesStoreLiteSetMappedSlot I) (solidityShortBytesWord value)
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hvalueSize]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedShortNonemptyOldShortAbsentRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmissingEvm : σ_evm.find? I.codeOwner = none)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreLiteSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreLiteSetMappedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σ_evm)
        (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    exact bytesStoreLiteX_setMappedShortNonemptyOldShortAbsentReturns
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (key := key)
      hperm hreach hlenMax
      (by simpa [bytesStoreLiteSetMappedHeaderWord,
        bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
      (by simpa [bytesStoreLiteSetMappedHeaderWord,
        bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
      hnz hshort hmissingEvm
  have hmissingSolm : σ_solm.find? I.codeOwner = none :=
    accountMapEquiv_find?_none hAccounts hmissingEvm
  have hmissingSolm0 :
      evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner = none := by
    simpa [evmSolm0, initState] using hmissingSolm
  have hwrite₀ :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlot I) (solidityShortBytesWord value)) := by
    simpa [evmSolm0, value, bytesStoreLiteSetMappedRef, hkey] using
      bytesStoreLiteSetMappedWriteShortOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        hAccounts hpayloadList hlenAbi hshort hflag hvalid
  have hstoreAbsent :
      Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlot I) (solidityShortBytesWord value) =
        evmSolm0 := by
    exact storageStore_absent evmSolm0 evmSolm0.executionEnv.codeOwner hmissingSolm0
      (bytesStoreLiteSetMappedSlot I) (solidityShortBytesWord value)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes (.bytes value) = .ok evmSolm0 := by
    simpa [hstoreAbsent] using hwrite₀
  have hlenMapped :
      readStorageBytesLength? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) = .ok 0 := by
    have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlotOf key) = (⟨0⟩ : UInt256) := by
      simp [Solm.EVM.storageLoad, State.lookupAccount, hmissingSolm0, Option.option]
    exact bytesStoreLiteReadLengthZeroOfHeaderLoad
      (er := bytesStoreLiteSetMappedRefOf key) (evm := evmSolm0)
      (baseSlot := bytesStoreLiteSetMappedSlotOf key)
      (bytesStoreLiteSetMappedRefOf_length_slot evmSolm0 key) hload
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreLiteSetMappedFrameOf key value) evmSolm0
          (some (.int 0))) := by
    have hlocals :
        bytesStoreLiteSetMappedLocals I = bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyReturnsOfWrite
      (evm := evmSolm0) (evm' := evmSolm0)
      (key := key) (value := value) (n := 0)
      (by simp [evmSolm0, initState]; exact hwv)
      hwrite hlenMapped
  have hCreated : (cA, σ_evm).1 = evmSolm0.createdAccounts := by
    simp [evmSolm0, initState]
  have hAccountsPost : accountMapEquiv σ_evm evmSolm0.accountMap := by
    simpa [evmSolm0, initState] using hAccounts
  have henc :
      returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

theorem bytesStoreLiteDecode_setMapped_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 68) :
    decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_short (cd := I.calldata) (x := "key")
      (y := "value") hshort

theorem bytesStoreLiteDecode_setMapped_none_totalHuge {I : ExecutionEnv}
    (hbig : 2 ^ 255 ≤ I.calldata.size) :
    decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_total_huge (cd := I.calldata)
      (x := "key") (y := "value") hbig

theorem bytesStoreLiteDecode_setMapped_none_offsetHuge {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_offset_huge (cd := I.calldata)
      (x := "key") (y := "value") hsz68 hsizeSign hoff

theorem bytesStoreLiteDecode_setMapped_none_lengthShort {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 36).toNat + 32) :
    decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_length_short (cd := I.calldata)
      (x := "key") (y := "value") hsz68 hsizeSign hoffMax hshort

theorem bytesStoreLiteDecode_setMapped_none_lengthHuge {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat) :
    decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_length_huge (cd := I.calldata)
      (x := "key") (y := "value") hsz68 hsizeSign hoffMax hlenWord hlenHuge

theorem bytesStoreLiteDecode_setMapped_none_payloadShort {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length ≠
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_payload_short (cd := I.calldata)
      (x := "key") (y := "value") hsz68 hsizeSign hoffMax hlenWord hlenMax
      hpayload

theorem bytesStoreLiteDecode_setMapped {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (_hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetMappedLocals I) := by
  show decodeCalldata ["key", "value"] [uint256, .bytes] I.calldata =
    some (bytesStoreLiteSetMappedLocals I)
  simpa [uint256, abiUInt256, bytesStoreLiteSetMappedLocals,
    bytesStoreLiteSetMappedKeyWord, bytesStoreLiteSetMappedValueBytes,
    bytesStoreLiteSetChunkValueBytes] using
    decodeCalldata_uint256_bytes_some (cd := I.calldata) (x := "key")
      (y := "value") hsz68 hsizeSign hoffMax hlenWord hlenMax hpayload

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedShortNonemptyOldLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let key : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreLiteX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreLiteCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hkey : key = bytesStoreLiteSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreLiteSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hnzLen : len.toNat ≠ 0 := by
    rw [hlenAbi]
    exact hnz
  have hshortLen : len.toNat < 32 := by
    rw [hlenAbi]
    exact hshort
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreLiteSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  exact bytesStoreLiteSetMappedShortNonemptyOldLongRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen) (accEvm := accEvm)
    hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec
    hlenAbi hpayloadStart hoffMax hsrc hpayloadList hlenMaxLen
    hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
    hnzLen hshortLen

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedEmptyOldLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let key : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreLiteX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_gt_max I hoffMax hlenMaxAbiWord
  have hlenZeroLen : len = ⟨0⟩ := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_zero I hoffMax hlenZero
  have hkey : key = bytesStoreLiteSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreLiteSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  exact bytesStoreLiteSetMappedEmptyOldLongRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hcode hperm hwv hAccounts hreach hkey hd hdec hpayloadList hlenMaxLen
    hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
    hlenZeroLen hlenZero

theorem bytesStoreLiteSetMappedShortOldLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hzero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩
  · exact bytesStoreLiteSetMappedEmptyOldLongRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hzero
  · have hnz :
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0 := by
      intro hnat
      apply hzero
      apply u256_inj
      rw [hnat]
      native_decide
    cases hacc : σ_evm.find? I.codeOwner with
    | none =>
        have hheader0 : bytesStoreLiteSetMappedHeaderWord σ_evm I = ⟨0⟩ := by
          rw [bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf, hacc]
          rfl
        have hland0 :
            UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
          rw [hheader0]
          native_decide
        exact False.elim (hflag hland0)
    | some accEvm =>
        exact bytesStoreLiteSetMappedShortNonemptyOldLongRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
          hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax
          hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid
          hnz hshort

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedLongOldLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let key : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreLiteX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreLiteCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hlenMaxNat : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenAbi]
    exact Nat.le_of_not_gt hlenMax
  have hkey : key = bytesStoreLiteSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreLiteSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hnzLen : len.toNat ≠ 0 := by
    intro hz
    exact hlongLen (by omega)
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreLiteSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  have haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size := by
    intro i hi
    have hfull : 32 * i < len.toNat := by
      have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
        Nat.mul_le_mul_left 32 hsucc
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      have hle := le_trans hmul hdiv
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  by_cases hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩
  · by_cases hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0
    · exact bytesStoreLiteSetMappedLongNoTailOldLongClearRuntimeOfReach
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen)
        hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec hlenAbi
        hpayloadStart hoffMax hsrc haddrBound hpayloadList hlenMaxLen hlenMaxNat
        hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
        hgtOldNew hlongLen (by simpa [hlenAbi] using hnoTailMod)
    · have htailAddrBound :
        payloadStart.toNat + 32 * (len.toNat / 32) < UInt256.size := by
        have htailModLen : len.toNat % 32 ≠ 0 := by
          simpa [hlenAbi] using hnoTailMod
        have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero htailModLen
        have hdiv := Nat.div_add_mod len.toNat 32
        have hltLen : 32 * (len.toNat / 32) < len.toNat := by
          omega
        exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
      have htailAddr :
          (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
            payloadStart.toNat + 32 * (len.toNat / 32) :=
        bytesStoreLiteCalldataLongDataAddr_toNat_of_bound
          (payloadStart := payloadStart) (i := len.toNat / 32) htailAddrBound
      exact bytesStoreLiteSetMappedLongTailOldLongClearRuntimeOfReach
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen)
        hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec hlenAbi
        hpayloadStart hoffMax hsrc haddrBound htailAddr hpayloadList hlenMaxLen hlenMaxNat
        hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
        hgtOldNew hlongLen (by simpa [hlenAbi] using hnoTailMod)
  · have hgtOldNew0 : UInt256.gt oldStoredLen len = ⟨0⟩ := by
      by_cases hle : oldStoredLen.toNat ≤ len.toNat
      · exact ugt_zero hle
      · exact False.elim (hgtOldNew (ugt_one (Nat.lt_of_not_ge hle)))
    by_cases hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0
    · exact bytesStoreLiteSetMappedLongNoTailOldLongNoClearRuntimeOfReach
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen)
        hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec hlenAbi
        hpayloadStart hoffMax hsrc haddrBound hpayloadList hlenMaxLen hlenMaxNat
        hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
        hgtOldNew0 hlongLen (by simpa [hlenAbi] using hnoTailMod)
    · have htailAddrBound :
        payloadStart.toNat + 32 * (len.toNat / 32) < UInt256.size := by
        have htailModLen : len.toNat % 32 ≠ 0 := by
          simpa [hlenAbi] using hnoTailMod
        have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero htailModLen
        have hdiv := Nat.div_add_mod len.toNat 32
        have hltLen : 32 * (len.toNat / 32) < len.toNat := by
          omega
        exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
      have htailAddr :
          (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
            payloadStart.toNat + 32 * (len.toNat / 32) :=
        bytesStoreLiteCalldataLongDataAddr_toNat_of_bound
          (payloadStart := payloadStart) (i := len.toNat / 32) htailAddrBound
      exact bytesStoreLiteSetMappedLongTailOldLongNoClearRuntimeOfReach
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen)
        hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec hlenAbi
        hpayloadStart hoffMax hsrc haddrBound htailAddr hpayloadList hlenMaxLen hlenMaxNat
        hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
        hgtOldNew0 hlongLen (by simpa [hlenAbi] using hnoTailMod)

theorem bytesStoreLiteSetMappedEmptyOldShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let key : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreLiteX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_gt_max I hoffMax hlenMaxAbiWord
  have hlenZeroLen : len = ⟨0⟩ := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_zero I hoffMax hlenZero
  have hkey : key = bytesStoreLiteSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreLiteSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  exact bytesStoreLiteSetMappedEmptyOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (key := key)
    hcode hperm hwv hAccounts hreach hkey hd hdec hpayloadList hlenMaxLen
    hflag hvalid hlenZeroLen hlenZero

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedShortNonemptyOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let key : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreLiteX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreLiteCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hkey : key = bytesStoreLiteSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreLiteSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hnzLen : len.toNat ≠ 0 := by
    rw [hlenAbi]
    exact hnz
  have hshortLen : len.toNat < 32 := by
    rw [hlenAbi]
    exact hshort
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreLiteSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  exact bytesStoreLiteSetMappedShortNonemptyOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (key := key)
    (accEvm := accEvm)
    hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec
    hlenAbi hpayloadStart hoffMax hsrc hpayloadList hlenMaxLen
    hflag hvalid hnzLen hshortLen

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedShortNonemptyOldShortAbsentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmissingEvm : σ_evm.find? I.codeOwner = none)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let key : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreLiteX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hkey : key = bytesStoreLiteSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreLiteSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hnzLen : len.toNat ≠ 0 := by
    rw [hlenAbi]
    exact hnz
  have hshortLen : len.toNat < 32 := by
    rw [hlenAbi]
    exact hshort
  exact bytesStoreLiteSetMappedShortNonemptyOldShortAbsentRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (key := key)
    hcode hperm hwv hAccounts hmissingEvm hreach hkey hd hdec hlenAbi hpayloadList
    hlenMaxLen hflag hvalid hnzLen hshortLen

theorem bytesStoreLiteSetMappedShortOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hzero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩
  · exact bytesStoreLiteSetMappedEmptyOldShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hzero
  · have hnz :
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0 := by
      intro hnat
      apply hzero
      apply u256_inj
      rw [hnat]
      native_decide
    cases hacc : σ_evm.find? I.codeOwner with
    | none =>
        exact bytesStoreLiteSetMappedShortNonemptyOldShortAbsentRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hnz hshort
    | some accEvm =>
        exact bytesStoreLiteSetMappedShortNonemptyOldShortRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
          hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hnz hshort

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedLongNoTailOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let key : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreLiteX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreLiteCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hlenMaxNat : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenAbi]
    exact Nat.le_of_not_gt hlenMax
  have hkey : key = bytesStoreLiteSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreLiteSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hnzLen : len.toNat ≠ 0 := by
    intro hz
    exact hlongLen (by omega)
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreLiteSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  have haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size := by
    intro i hi
    have hfull : 32 * i < len.toNat := by
      have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
        Nat.mul_le_mul_left 32 hsucc
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      have hle := le_trans hmul hdiv
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  exact bytesStoreLiteSetMappedLongNoTailOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (len := len) (payloadStart := payloadStart) (key := key)
    hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec hlenAbi
    hpayloadStart hoffMax hsrc haddrBound hpayloadList hlenMaxLen hlenMaxNat
    hflag hvalid hlongLen (by simpa [hlenAbi] using hnoTailMod)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedLongTailOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let key : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreLiteX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreLiteCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hlenMaxNat : len.toNat ≤ ABI.solcMaxU64 := by
    rw [hlenAbi]
    exact Nat.le_of_not_gt hlenMax
  have hkey : key = bytesStoreLiteSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreLiteSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hnzLen : len.toNat ≠ 0 := by
    intro hz
    exact hlongLen (by omega)
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreLiteSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  have haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size := by
    intro i hi
    have hfull : 32 * i < len.toNat := by
      have hsucc : i + 1 ≤ len.toNat / 32 := Nat.succ_le_of_lt hi
      have hmul : 32 * (i + 1) ≤ 32 * (len.toNat / 32) :=
        Nat.mul_le_mul_left 32 hsucc
      have hdiv : 32 * (len.toNat / 32) ≤ len.toNat := by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self len.toNat 32
      have hle := le_trans hmul hdiv
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  have htailAddrBound :
      payloadStart.toNat + 32 * (len.toNat / 32) < UInt256.size := by
    have htailModLen : len.toNat % 32 ≠ 0 := by
      simpa [hlenAbi] using htailMod
    have hremPos : 0 < len.toNat % 32 := Nat.pos_of_ne_zero htailModLen
    have hdiv := Nat.div_add_mod len.toNat 32
    have hltLen : 32 * (len.toNat / 32) < len.toNat := by
      omega
    exact lt_of_lt_of_le (by omega) (lt_of_le_of_lt hsrc hsize)
  have htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32) :=
    bytesStoreLiteCalldataLongDataAddr_toNat_of_bound
      (payloadStart := payloadStart) (i := len.toNat / 32) htailAddrBound
  exact bytesStoreLiteSetMappedLongTailOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (len := len) (payloadStart := payloadStart) (key := key)
    hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec hlenAbi
    hpayloadStart hoffMax hsrc haddrBound htailAddr hpayloadList hlenMaxLen hlenMaxNat
    hflag hvalid hlongLen (by simpa [hlenAbi] using htailMod)

theorem bytesStoreLiteSetMappedLongOldShortPresentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0
  · exact bytesStoreLiteSetMappedLongNoTailOldShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
      hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
      hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid
      hnewLong hnoTailMod
  · exact bytesStoreLiteSetMappedLongTailOldShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
      hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
      hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid
      hnewLong hnoTailMod

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedLongNoTailOldShortAbsentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmissingEvm : σ_evm.find? I.codeOwner = none)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let key : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreLiteX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hkey : key = bytesStoreLiteSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreLiteSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σ_evm) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    exact bytesStoreLiteX_setMappedLongNoTailOldShortAbsentReturns
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (key := key)
      hperm hreach hlenMaxLen
      (by simpa [bytesStoreLiteSetMappedHeaderWord,
        bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
      (by simpa [bytesStoreLiteSetMappedHeaderWord,
        bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
      hlongLen (by simpa [hlenAbi] using hnoTailMod) hmissingEvm
  exact bytesStoreLiteSetMappedLongOldShortAbsentRuntimeOfReturn
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len) (key := key)
    hcode hwv hAccounts hmissingEvm hkey hd hdec hlenAbi hpayloadList
    hlongLen hflag hvalid hret

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedLongTailOldShortAbsentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmissingEvm : σ_evm.find? I.codeOwner = none)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let key : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreLiteX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hkey : key = bytesStoreLiteSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreLiteSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σ_evm) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    exact bytesStoreLiteX_setMappedLongTailOldShortAbsentReturns
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (key := key)
      hperm hreach hlenMaxLen
      (by simpa [bytesStoreLiteSetMappedHeaderWord,
        bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
      (by simpa [bytesStoreLiteSetMappedHeaderWord,
        bytesStoreLiteSetMappedHeaderWordOf, hkey] using hvalid)
      hlongLen (by simpa [hlenAbi] using htailMod) hmissingEvm
  exact bytesStoreLiteSetMappedLongOldShortAbsentRuntimeOfReturn
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len) (key := key)
    hcode hwv hAccounts hmissingEvm hkey hd hdec hlenAbi hpayloadList
    hlongLen hflag hvalid hret

theorem bytesStoreLiteSetMappedLongOldShortAbsentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmissingEvm : σ_evm.find? I.codeOwner = none)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0
  · exact bytesStoreLiteSetMappedLongNoTailOldShortAbsentRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hmissingEvm hsz68 hhi hsizeSign hoffMax
      hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid
      hnewLong hnoTailMod
  · exact bytesStoreLiteSetMappedLongTailOldShortAbsentRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hmissingEvm hsz68 hhi hsizeSign hoffMax
      hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid
      hnewLong hnoTailMod

theorem bytesStoreLiteSetMappedLongOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  cases hacc : σ_evm.find? I.codeOwner with
  | none =>
      exact bytesStoreLiteSetMappedLongOldShortAbsentRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hnewLong
  | some accEvm =>
      exact bytesStoreLiteSetMappedLongOldShortPresentRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hnewLong

theorem bytesStoreLiteSetMappedOldShortValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32
  · exact bytesStoreLiteSetMappedShortOldShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hshort
  · exact bytesStoreLiteSetMappedLongOldShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hshort

theorem bytesStoreLiteSetMappedOldLongValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32
  · exact bytesStoreLiteSetMappedShortOldLongRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hshort
  · cases hacc : σ_evm.find? I.codeOwner with
    | none =>
        have hheader0 : bytesStoreLiteSetMappedHeaderWord σ_evm I = ⟨0⟩ := by
          rw [bytesStoreLiteSetMappedHeaderWord, bytesStoreLiteSetMappedHeaderWordOf, hacc]
          rfl
        have hland0 :
            UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
          rw [hheader0]
          native_decide
        exact False.elim (hflag hland0)
    | some accEvm =>
        exact bytesStoreLiteSetMappedLongOldLongRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
          hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hshort

theorem bytesStoreLiteSetMappedLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let key : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreLiteX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hkey : key = bytesStoreLiteSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreLiteSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hrev : RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    exact bytesStoreLiteX_setMappedLongMalformedHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (key := key)
      hreach hlenMaxWord
      (by simpa [bytesStoreLiteSetMappedHeaderWord,
        bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
      (by simpa [bytesStoreLiteSetMappedHeaderWord,
        bytesStoreLiteSetMappedHeaderWordOf, hkey] using hbad)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlot I) =
        bytesStoreLiteSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes
        (.bytes (bytesStoreLiteSetMappedValueBytes I)) = .revert := by
    simpa [evmSolm0, bytesStoreLiteSetMappedRef, hkey] using
      bytesStoreLiteSetMappedWriteMalformedLong
        (evm := evmSolm0) I (bytesStoreLiteSetMappedHeaderWord σ_evm I)
        (bytesStoreLiteSetMappedValueBytes I)
        hloadHeader hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body .reverted := by
    let value := bytesStoreLiteSetMappedValueBytes I
    have hlocals :
        bytesStoreLiteSetMappedLocals I =
          bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyRevertsOfWrite
      (evm := evmSolm0) (key := key) (value := value)
      (by simp [evmSolm0, initState]; exact hwv)
      (by simpa [value] using hwrite)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetMappedShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let len : UInt256 :=
    uInt256OfByteArray
      (I.calldata.readBytes
        (((⟨4⟩ : UInt256) +
          uInt256OfByteArray
            (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)).toNat)
        32)
  let payloadStart : UInt256 :=
    (((⟨4⟩ : UInt256) +
      uInt256OfByteArray
        (I.calldata.readBytes (((⟨4⟩ : UInt256) + ⟨32⟩).toNat) 32)) +
      ⟨32⟩)
  let key : UInt256 :=
    uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)
  have hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreLiteX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hkey : key = bytesStoreLiteSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreLiteSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hrev : RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    exact bytesStoreLiteX_setMappedShortMalformedHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (key := key)
      hreach hlenMaxWord
      (by simpa [bytesStoreLiteSetMappedHeaderWord,
        bytesStoreLiteSetMappedHeaderWordOf, hkey] using hflag)
      (by simpa [bytesStoreLiteSetMappedHeaderWord,
        bytesStoreLiteSetMappedHeaderWordOf, hkey] using hbad)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreLiteSetMappedSlot I) =
        bytesStoreLiteSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        (bytesStoreLiteSetMappedRefOf key) .bytes
        (.bytes (bytesStoreLiteSetMappedValueBytes I)) = .revert := by
    simpa [evmSolm0, bytesStoreLiteSetMappedRef, hkey] using
      bytesStoreLiteSetMappedWriteMalformedShort
        (evm := evmSolm0) I (bytesStoreLiteSetMappedHeaderWord σ_evm I)
        (bytesStoreLiteSetMappedValueBytes I)
        hloadHeader hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evmSolm0
        (bytesStoreLiteSetMappedLocals I) setMappedTransition.body .reverted := by
    let value := bytesStoreLiteSetMappedValueBytes I
    have hlocals :
        bytesStoreLiteSetMappedLocals I =
          bytesStoreLiteSetMappedLocalsOf key value := by
      simp [value, bytesStoreLiteSetMappedLocals, bytesStoreLiteSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreLiteSetMappedBodyRevertsOfWrite
      (evm := evmSolm0) (key := key) (value := value)
      (by simp [evmSolm0, initState]; exact hwv)
      (by simpa [value] using hwrite)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLiteSetMappedShortHeaderRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
  · exact bytesStoreLiteSetMappedShortOldShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hshort
  · exact bytesStoreLiteSetMappedShortMalformedRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag
      (not_ne_iff.mp hvalid)

theorem bytesStoreLiteSetMappedDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 68) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetMappedSelector_size hsel
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped_none_short (I := I) hshort
  exact (bytesStoreLiteX_setMappedDecodeShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz hshort hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetMappedDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetMappedSelector_size hsel
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped_none_totalHuge (I := I) (by omega)
  exact (bytesStoreLiteX_setMappedDecodeHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz hbig hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetMappedDecodeOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setMappedTransition.params.map Param.name)
        (transitionSignature setMappedTransition).paramTypes I.calldata = none := by
    by_cases hsizeSign' : I.calldata.size < 2 ^ 255
    · exact bytesStoreLiteDecode_setMapped_none_offsetHuge (I := I)
        hsz68 hsizeSign' hoff
    · exact bytesStoreLiteDecode_setMapped_none_totalHuge (I := I)
        (Nat.le_of_not_gt hsizeSign')
  exact (bytesStoreLiteX_setMappedDecodeOffsetHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz68 hhi hsize hsel hoff)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetMappedDecodeLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 36).toNat + 32)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped_none_lengthShort (I := I)
    hsz68 hsizeSign hoffMax hlenShort
  exact (bytesStoreLiteX_setMappedDecodeLengthShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetMappedDecodeLengthHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped_none_lengthHuge (I := I)
    hsz68 hsizeSign hoffMax hlenWord hlenHuge
  exact (bytesStoreLiteX_setMappedDecodeLengthHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetMappedDecodePayloadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadListNe :
      ((((I.calldata.toList.drop 4).drop
        ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata
          (4 + (calldataWord I.calldata 36).toNat)).toNat).length ≠
        (calldataWord I.calldata
          (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped_none_payloadShort (I := I)
    hsz68 hsizeSign hoffMax hlenWord hlenMax hpayloadListNe
  exact (bytesStoreLiteX_setMappedDecodePayloadShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetMappedDecodeTotalHighRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsizeHigh : ¬ I.calldata.size < 2 ^ 255) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setMapped_none_totalHuge (I := I)
    (Nat.le_of_not_gt hsizeHigh)
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    bytesStoreLiteSetChunkStart_slt_zero_of_size_high I.calldata hoffMax hsize hsizeHigh
  exact (bytesStoreLiteX_setMappedDecodeLengthShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart)
    |>.reEquivDecodingFailed hcode hd hdec

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedDecodedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflagShort : UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalidShort :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteSetMappedOldShortValidRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflagShort hvalidShort
    · exact bytesStoreLiteSetMappedShortMalformedRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflagShort
        (not_ne_iff.mp hvalidShort)
  · have hflagLong :
      UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := hflagShort
    by_cases hvalidLong :
      UInt256.sub (UInt256.land (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLiteSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreLiteSetMappedOldLongValidRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflagLong hvalidLong
    · exact bytesStoreLiteSetMappedLongMalformedRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflagLong
        (not_ne_iff.mp hvalidLong)

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetMappedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort : I.calldata.size < 68
  · exact bytesStoreLiteSetMappedDecodeShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hshort
  · have hsz68 : 68 ≤ I.calldata.size := Nat.le_of_not_gt hshort
    by_cases hbig : 2 ^ 255 + 4 ≤ I.calldata.size
    · exact bytesStoreLiteSetMappedDecodeHugeRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hbig
    · have hhi : I.calldata.size < 2 ^ 255 + 4 := Nat.lt_of_not_ge hbig
      by_cases hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat
      · exact bytesStoreLiteSetMappedDecodeOffsetHugeRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hsz68 hhi hoff
      · have hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat := hoff
        by_cases hsizeSign : I.calldata.size < 2 ^ 255
        · by_cases hlenShort :
            I.calldata.size < 4 + (calldataWord I.calldata 36).toNat + 32
          · have hstart :
                UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
                    (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
              bytesStoreLiteSetChunkStart_slt_zero_of_length_short
                I.calldata hoffMax hsizeSign hlenShort
            exact bytesStoreLiteSetMappedDecodeLengthShortRuntime
              (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
              (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax
              hlenShort hstart
          · have hlenWord :
              4 + (calldataWord I.calldata 36).toNat + 32 ≤ I.calldata.size :=
              Nat.le_of_not_gt hlenShort
            have hstart :
                UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
                    (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
              bytesStoreLiteSetChunkStart_slt_one I.calldata hoffMax hlenWord hsizeSign
            by_cases hlenHuge :
                ABI.solcMaxU64 <
                  (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat
            · have hlenMaxWord :
                  UInt256.gt
                      (uInt256OfByteArray
                        (I.calldata.readBytes
                          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
                      ⟨18446744073709551615⟩ = ⟨1⟩ := by
                rw [← bytesStoreLiteCalldataWord36_add32 I]
                rw [bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax]
                apply ugt_one
                rw [show (⟨18446744073709551615⟩ : UInt256).toNat =
                    ABI.solcMaxU64 by native_decide]
                exact hlenHuge
              exact bytesStoreLiteSetMappedDecodeLengthHugeRuntime
                (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax
                hlenWord hlenHuge hstart hlenMaxWord
            · by_cases hpayloadList :
                ((((I.calldata.toList.drop 4).drop
                  ((calldataWord I.calldata 36).toNat + 32)).take
                  (calldataWord I.calldata
                    (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
                  (calldataWord I.calldata
                    (4 + (calldataWord I.calldata 36).toNat)).toNat)
              · have hlenMaxWord :
                    UInt256.gt
                        (uInt256OfByteArray
                          (I.calldata.readBytes
                            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
                        ⟨18446744073709551615⟩ = ⟨0⟩ := by
                  rw [← bytesStoreLiteCalldataWord36_add32 I]
                  rw [bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax]
                  apply ugt_zero
                  rw [show (⟨18446744073709551615⟩ : UInt256).toNat =
                      ABI.solcMaxU64 by native_decide]
                  exact Nat.le_of_not_gt hlenHuge
                have hpayloadWord :
                    UInt256.gt
                      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
                        uInt256OfByteArray
                          (I.calldata.readBytes
                            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
                        ⟨32⟩))
                      (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
                  bytesStoreLiteSetChunkPayloadWord_zero_of_payload
                    I hsize hoffMax hlenWord hlenHuge hpayloadList
                exact bytesStoreLiteSetMappedDecodedRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign
                  hoffMax hlenWord hlenHuge hpayloadList hstart hlenMaxWord hpayloadWord
              · have hpayloadListNe :
                  ((((I.calldata.toList.drop 4).drop
                    ((calldataWord I.calldata 36).toNat + 32)).take
                    (calldataWord I.calldata
                      (4 + (calldataWord I.calldata 36).toNat)).toNat).length ≠
                    (calldataWord I.calldata
                      (4 + (calldataWord I.calldata 36).toNat)).toNat) := hpayloadList
                have hlenMaxWord :
                    UInt256.gt
                        (uInt256OfByteArray
                          (I.calldata.readBytes
                            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
                        ⟨18446744073709551615⟩ = ⟨0⟩ := by
                  rw [← bytesStoreLiteCalldataWord36_add32 I]
                  rw [bytesStoreLiteSetChunkRawLengthWord_eq I hoffMax]
                  apply ugt_zero
                  rw [show (⟨18446744073709551615⟩ : UInt256).toNat =
                      ABI.solcMaxU64 by native_decide]
                  exact Nat.le_of_not_gt hlenHuge
                have hpayloadWord :
                    UInt256.gt
                      (((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) +
                        uInt256OfByteArray
                          (I.calldata.readBytes
                            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32)) +
                        ⟨32⟩))
                      (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
                  bytesStoreLiteSetChunkPayloadWord_one_of_payload_short
                    I hsize hoffMax hlenWord hlenHuge hpayloadListNe
                exact bytesStoreLiteSetMappedDecodePayloadShortRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax
                  hlenWord hlenHuge hpayloadListNe hstart hlenMaxWord hpayloadWord
        · exact bytesStoreLiteSetMappedDecodeTotalHighRuntime
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hcode hsize hperm hwv hsel hAccounts hsz68 hhi hoffMax hsizeSign

end BytesStoreLite
