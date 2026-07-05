import Examples.BytesStore.FullSetChunkOldLongReturn
import Examples.BytesStore.StorageReadbackFacts
import Examples.BytesStore.StorageLoopFacts

/-!
# BytesStore — `setMapped(uint256,bytes)` runtime slice

This module starts the full-contract `setMapped(uint256,bytes)` selector arm.  The ABI
shape matches `setChunk(uint256,bytes)`, while the storage target is the mapping value at
`keccak256(key, 4)`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 4000000

namespace BytesStore

def bytesStoreSetMappedKeyWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

def bytesStoreSetMappedValueBytes (I : ExecutionEnv) : ByteArray :=
  bytesStoreSetChunkValueBytes I

def bytesStoreSetMappedLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "key"
    (.int (Int.ofNat (bytesStoreSetMappedKeyWord I).toNat))).insert "value"
    (.bytes (bytesStoreSetMappedValueBytes I)))

def bytesStoreSetMappedLocalsOf (key : UInt256) (value : ByteArray) : Store :=
  ((∅ : Store).insert "key" (.int (Int.ofNat key.toNat))).insert "value" (.bytes value)

def bytesStoreSetMappedFrameOf (key : UInt256) (value : ByteArray) : Frame :=
  { contract := bytesStoreContract,
    locals := bytesStoreSetMappedLocalsOf key value }

def bytesStoreSetMappedRefOf (key : UInt256) : EvaledStorageRef :=
  { base := "mapped", steps := [.mindex (.int (Int.ofNat key.toNat))] }

def bytesStoreSetMappedRef (I : ExecutionEnv) : EvaledStorageRef :=
  bytesStoreSetMappedRefOf (bytesStoreSetMappedKeyWord I)

def bytesStoreSetMappedSlotOf (key : UInt256) : UInt256 :=
  mappedValueSlot (.int (Int.ofNat key.toNat))

def bytesStoreSetMappedSlot (I : ExecutionEnv) : UInt256 :=
  bytesStoreSetMappedSlotOf (bytesStoreSetMappedKeyWord I)

theorem accountMapEquiv_setMappedHeaderStore {σ : AccountMap} {evm : EVM.State}
    (I : ExecutionEnv) (owner : AccountAddress) (header : UInt256)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
  accountMapEquiv
      (sstoreAccountMap owner σ (bytesStoreSetMappedSlot I) header)
      (Solm.EVM.storageStore evm owner (bytesStoreSetMappedSlot I) header).accountMap := by
  exact accountMapEquiv_bytesHeaderStore owner (bytesStoreSetMappedSlot I) header hAccounts

theorem bytesStoreSetMappedRefOf_length_slot (evm : EVM.State) (key : UInt256) :
    ∃ loc, bytesStoreLayout
        { bytesStoreSetMappedRefOf key with
          steps := (bytesStoreSetMappedRefOf key).steps ++ [.length] } evm =
          some loc ∧
        loc.slot = bytesStoreSetMappedSlotOf key := by
  refine ⟨bytesLikeLengthLoc (bytesStoreSetMappedSlotOf key) evm, ?_, ?_⟩
  · simp [bytesStoreLayout, bytesStoreSetMappedRefOf, bytesStoreSetMappedSlotOf]
  · simp [bytesLikeLengthLoc]

theorem bytesStoreSetMappedRef_length_slot (evm : EVM.State) (I : ExecutionEnv) :
    ∃ loc, bytesStoreLayout
        { bytesStoreSetMappedRef I with
          steps := (bytesStoreSetMappedRef I).steps ++ [.length] } evm =
          some loc ∧
        loc.slot = bytesStoreSetMappedSlot I := by
  exact bytesStoreSetMappedRefOf_length_slot evm (bytesStoreSetMappedKeyWord I)

def bytesStoreSetMappedHeaderWordOf (σ : AccountMap) (I : ExecutionEnv)
    (key : UInt256) : UInt256 :=
  σ.find? I.codeOwner |>.option ⟨0⟩
    (fun acc => acc.storage.findD (bytesStoreSetMappedSlotOf key) ⟨0⟩)

def bytesStoreSetMappedHeaderWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  bytesStoreSetMappedHeaderWordOf σ I (bytesStoreSetMappedKeyWord I)

theorem bytesStoreSetMappedHeaderWord_eq_of_accountMapEquiv
    {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    bytesStoreSetMappedHeaderWord σ_evm I =
      bytesStoreSetMappedHeaderWord σ_solm I :=
  accountMapEquiv_storage_findD hAccounts I.codeOwner
    (bytesStoreSetMappedSlot I) ⟨0⟩

theorem bytesStoreStorageLoadSetMappedHeader_initState_of_accountMapEquiv
    {cA : Batteries.RBSet AccountAddress compare} {gh : BlockHeader} {bl : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    Solm.EVM.storageLoad (initState cA gh bl σ_solm σ₀ g A I)
        (initState cA gh bl σ_solm σ₀ g A I).executionEnv.codeOwner
        (bytesStoreSetMappedSlot I) =
      bytesStoreSetMappedHeaderWord σ_evm I := by
  simpa [bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf] using
    bytesStoreStorageLoad_initState_of_accountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (bytesStoreSetMappedSlot I) hAccounts

def bytesStoreSetMappedShortStoredWord (I : ExecutionEnv)
    (len payloadStart : UInt256) : UInt256 :=
  bytesStoreSetChunkShortStoredWord I len payloadStart

theorem bytesStoreSetMappedSlotHash (I : ExecutionEnv) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          ((twoWordHashMem (bytesStoreSetMappedKeyWord I) ⟨4⟩ solcFreePtrMem).readWithPadding 0 64))) =
      bytesStoreSetMappedSlot I := by
  rw [twoWordHashMem_read0_64 (bytesStoreSetMappedKeyWord I) ⟨4⟩ solcFreePtrMem_size]
  unfold bytesStoreSetMappedSlot bytesStoreSetMappedSlotOf mappedValueSlot
  rw [keyValueToWord_uint256]
  exact mappingSlot_single (bytesStoreSetMappedKeyWord I) ⟨4⟩

theorem bytesStoreSetMappedValueBytes_toList {I : ExecutionEnv} :
    (bytesStoreSetMappedValueBytes I).toList =
      (((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat) := by
  simpa [bytesStoreSetMappedValueBytes] using
    (bytesStoreSetChunkValueBytes_toList (I := I))

theorem bytesStoreSetMappedValueBytes_size {I : ExecutionEnv}
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat)) :
    (bytesStoreSetMappedValueBytes I).size =
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat := by
  simpa [bytesStoreSetMappedValueBytes] using
    (bytesStoreSetChunkValueBytes_size (I := I) hpayload)

theorem bytesStoreSetMappedResolve {evm : EVM.State}
    {key : UInt256} {value : ByteArray} :
    resolveStorageRef? bytesStoreConfig
      (bytesStoreSetMappedFrameOf key value) evm (mappedRef (.var "key")) =
        .ok (bytesStoreSetMappedRefOf key, .bytes) := by
  have hgetKey :
      (bytesStoreSetMappedLocalsOf key value)["key"]? =
        some (.int (Int.ofNat key.toNat)) := by
    have h :
        (bytesStoreSetMappedLocalsOf key value).get? "key" =
          some (.int (Int.ofNat key.toNat)) := by
      unfold bytesStoreSetMappedLocalsOf
      rw [store_get_ne]
      · exact store_get_self (∅ : Store) "key" (.int (Int.ofNat key.toNat))
      · native_decide
    simpa [Std.HashMap.get?_eq_getElem?] using h
  have hgetMapped :
      (bytesStoreSetMappedLocalsOf key value)["mapped"]? = none := by
    have h :
        (bytesStoreSetMappedLocalsOf key value).get? "mapped" = none := by
      unfold bytesStoreSetMappedLocalsOf
      rw [store_get_ne]
      · rw [store_get_ne]
        · simp
        · native_decide
      · native_decide
    simpa [Std.HashMap.get?_eq_getElem?] using h
  have hgetMappedRaw :
      (bytesStoreSetMappedLocalsOf key value).get? "mapped" = none := by
    simpa [Std.HashMap.get?_eq_getElem?] using hgetMapped
  have her :
      evalStorageRef bytesStoreConfig
        (bytesStoreSetMappedFrameOf key value) evm (mappedRef (.var "key")) =
          .ok (bytesStoreSetMappedRefOf key) := by
    exact evalStorageRef_mindex_var_of_get?
      (base := "mapped")
      (hget := by simpa [Std.HashMap.get?_eq_getElem?] using hgetKey)
      (hkey := by simp [valueToKey?])
  exact resolveStorageRef?_ok hgetMappedRaw her (by
    simp [bytesStoreSetMappedFrameOf, bytesStoreSetMappedRefOf, storageTypeAt?,
      bytesStoreContract, storageDecls, bytesSt, uint256Int, storageTypeStep?])

theorem bytesStoreSetMappedAssign {evm evm' : EVM.State}
    {key : UInt256} {value : ByteArray}
    (hwrite :
      writeStorage? bytesStoreConfig evm
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evm') :
    assignStorageRef? bytesStoreConfig
      (bytesStoreSetMappedFrameOf key value)
      evm .storage (mappedRef (.var "key")) (.bytes value) =
        .ok (bytesStoreSetMappedFrameOf key value, evm') := by
  have hresolve :=
    bytesStoreSetMappedResolve (evm := evm) (key := key) (value := value)
  exact assignStorageRef_storage_bytes_ok_of_write hresolve hwrite

theorem bytesStoreSetMappedLengthAfterWrite {evm : EVM.State}
    {key : UInt256} {value : ByteArray} {n : Nat}
    (hlen :
      readStorageBytesLength? bytesStoreConfig evm
        (bytesStoreSetMappedRefOf key) = .ok n) :
    evalExpr? bytesStoreConfig
      (bytesStoreSetMappedFrameOf key value)
      evm (.arrayLength .storage (mappedRef (.var "key"))) =
        .ok (.int n) := by
  have hresolve :=
    bytesStoreSetMappedResolve (evm := evm) (key := key) (value := value)
  rw [evalExpr?]
  rw [hresolve]
  simp [readStorageArrayLength?, hlen, EvalResult.bind, bind, pure]

theorem bytesStoreSetMappedBodyReturnsOfWrite {evm evm' : EVM.State}
    {key : UInt256} {value : ByteArray} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite :
      writeStorage? bytesStoreConfig evm
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evm')
    (hlenMapped :
      readStorageBytesLength? bytesStoreConfig evm'
        (bytesStoreSetMappedRefOf key) = .ok n) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedLocalsOf key value)
      setMappedTransition.body
      (.returned (bytesStoreSetMappedFrameOf key value)
        evm' (some (.int n))) := by
  let solm0 := bytesStoreSetMappedFrameOf key value
  have hvalue : evalExpr? bytesStoreConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreSetMappedLocalsOf key value).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreSetMappedLocalsOf
      exact store_get_self ((∅ : Store).insert "key"
        (.int (Int.ofNat key.toNat))) "value" (.bytes value)
    exact evalExpr_var_of_get? (by simpa [solm0, bytesStoreSetMappedFrameOf] using hlookup)
  have hassign :
      assignStorageRef? bytesStoreConfig solm0 evm .storage
        (mappedRef (.var "key")) (.bytes value) =
          .ok (solm0, evm') := by
    simpa [solm0] using
      bytesStoreSetMappedAssign
        (evm := evm) (evm' := evm') (key := key) (value := value) hwrite
  have hret :
      evalExpr? bytesStoreConfig solm0 evm'
        (.arrayLength .storage (mappedRef (.var "key"))) =
          .ok (.int n) := by
    simpa [solm0] using
      bytesStoreSetMappedLengthAfterWrite
        (evm := evm') (key := key) (value := value) hlenMapped
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal (ExecStmt.assign hvalue hassign) <|
        ExecBlock.consReturn (ExecStmt.return hret)

theorem bytesStoreSetMappedBodyRevertsOfWrite {evm : EVM.State}
    {key : UInt256} {value : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite :
      writeStorage? bytesStoreConfig evm
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .revert) :
    ExecTransitionBody bytesStoreConfig bytesStoreContract evm
      (bytesStoreSetMappedLocalsOf key value)
      setMappedTransition.body .reverted := by
  let solm0 := bytesStoreSetMappedFrameOf key value
  have hvalue : evalExpr? bytesStoreConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreSetMappedLocalsOf key value).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreSetMappedLocalsOf
      exact store_get_self ((∅ : Store).insert "key"
        (.int (Int.ofNat key.toNat))) "value" (.bytes value)
    exact evalExpr_var_of_get? (by simpa [solm0, bytesStoreSetMappedFrameOf] using hlookup)
  have hresolve :=
    bytesStoreSetMappedResolve (evm := evm) (key := key) (value := value)
  have hresolve0 :
      resolveStorageRef? bytesStoreConfig solm0 evm
        (mappedRef (.var "key")) =
          .ok (bytesStoreSetMappedRefOf key, .bytes) := by
    simpa [solm0] using hresolve
  have hassign :
      assignStorageRef? bytesStoreConfig solm0 evm .storage
        (mappedRef (.var "key")) (.bytes value) = .revert := by
    exact assignStorageRef_storage_bytes_revert_of_write hresolve0 hwrite
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreSetMappedWriteEmptyOldShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreSetMappedSlot I) ⟨0⟩
    writeStorage? bytesStoreConfig evmSolm0
      (bytesStoreSetMappedRef I) .bytes
      (.bytes (bytesStoreSetMappedValueBytes I)) = .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize0 : (bytesStoreSetMappedValueBytes I).size = 0 := by
    rw [bytesStoreSetMappedValueBytes_size hpayload, hlenZero]
    rfl
  have hvalueEmpty : bytesStoreSetMappedValueBytes I = ByteArray.empty :=
    byteArray_eq_empty_of_size_eq_zero (bytesStoreSetMappedValueBytes I) hvalueSize0
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedSlot I) =
        bytesStoreSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked (bytesStoreSetMappedSlot I) evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite := writeSolidityBytesShortPacked
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evmSolm0)
    (er := bytesStoreSetMappedRef I)
    (baseSlot := bytesStoreSetMappedSlot I)
    (header := bytesStoreSetMappedHeaderWord σ_evm I) (len := oldLen)
    (value := ByteArray.empty)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreSetMappedSlot I) evmSolm0, ?_, by simp⟩
      simp [bytesStoreLayout, bytesStoreSetMappedRef,
        bytesStoreSetMappedRefOf, bytesStoreSetMappedSlot,
        bytesStoreSetMappedSlotOf])
    (by decide) hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, bytesStoreSetMappedRef, bytesStoreSetMappedRefOf,
    bytesStoreSetMappedSlot, hvalueEmpty, hshortEmpty] using hwrite

theorem bytesStoreSetMappedWriteShortOldShortPacked
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
      UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreSetMappedSlot I)
      (solidityShortBytesWord (bytesStoreSetMappedValueBytes I))
    writeStorage? bytesStoreConfig evmSolm0
      (bytesStoreSetMappedRef I) .bytes
      (.bytes (bytesStoreSetMappedValueBytes I)) = .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize : (bytesStoreSetMappedValueBytes I).size < 32 := by
    rw [bytesStoreSetMappedValueBytes_size hpayload, ← hlenAbi]
    exact hshort
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedSlot I) =
        bytesStoreSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked (bytesStoreSetMappedSlot I) evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite := writeSolidityBytesShortPacked
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evmSolm0)
    (er := bytesStoreSetMappedRef I)
    (baseSlot := bytesStoreSetMappedSlot I)
    (header := bytesStoreSetMappedHeaderWord σ_evm I) (len := oldLen)
    (value := bytesStoreSetMappedValueBytes I)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreSetMappedSlot I) evmSolm0, ?_, by simp⟩
      simp [bytesStoreLayout, bytesStoreSetMappedRef,
        bytesStoreSetMappedRefOf, bytesStoreSetMappedSlot,
        bytesStoreSetMappedSlotOf])
    hvalueSize hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, bytesStoreSetMappedRef, bytesStoreSetMappedRefOf,
    bytesStoreSetMappedSlot] using hwrite

theorem bytesStoreSetMappedWriteLongOldShortPacked
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
      UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let value := bytesStoreSetMappedValueBytes I
    writeStorage? bytesStoreConfig evmSolm0
      (bytesStoreSetMappedRef I) .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreSetMappedSlot I) value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreSetMappedSlot I) value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          (bytesStoreSetMappedSlot I) (solidityBytesHeaderWord value.size)) := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let value := bytesStoreSetMappedValueBytes I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize : ¬ value.size < 32 := by
    rw [show value.size = len.toNat by
      dsimp [value]
      rw [bytesStoreSetMappedValueBytes_size hpayload, ← hlenAbi]]
    exact hlong
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedSlot I) =
        bytesStoreSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked (bytesStoreSetMappedSlot I) evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite := writeSolidityBytesLongPacked
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evmSolm0)
    (er := bytesStoreSetMappedRef I)
    (baseSlot := bytesStoreSetMappedSlot I)
    (header := bytesStoreSetMappedHeaderWord σ_evm I) (len := oldLen)
    (value := value)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreSetMappedSlot I) evmSolm0, ?_, by simp⟩
      simp [bytesStoreLayout, bytesStoreSetMappedRef,
        bytesStoreSetMappedRefOf, bytesStoreSetMappedSlot,
        bytesStoreSetMappedSlotOf])
    hvalueSize hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, value, bytesStoreSetMappedRef,
    bytesStoreSetMappedRefOf, bytesStoreSetMappedSlot] using hwrite

theorem bytesStoreSetMappedWriteLongOldLongPrepared
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
      UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let value := bytesStoreSetMappedValueBytes I
    writeStorage? bytesStoreConfig evmSolm0
      (bytesStoreSetMappedRef I) .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom
            (clearSolidityBytesDataWordsFrom evmSolm0 (bytesStoreSetMappedSlot I)
              (solidityBytesDataWordCount value.size)
              (solidityBytesDataWordCount oldStoredLen.toNat -
                solidityBytesDataWordCount value.size))
            (bytesStoreSetMappedSlot I) value 0 (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom
            (clearSolidityBytesDataWordsFrom evmSolm0 (bytesStoreSetMappedSlot I)
              (solidityBytesDataWordCount value.size)
              (solidityBytesDataWordCount oldStoredLen.toNat -
                solidityBytesDataWordCount value.size))
            (bytesStoreSetMappedSlot I) value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          (bytesStoreSetMappedSlot I) (solidityBytesHeaderWord value.size)) := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let value := bytesStoreSetMappedValueBytes I
  have hvalueSize : ¬ value.size < 32 := by
    rw [show value.size = len.toNat by
      dsimp [value]
      rw [bytesStoreSetMappedValueBytes_size hpayload, ← hlenAbi]]
    exact hlong
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedSlot I) =
        bytesStoreSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite := writeSolidityBytesLongFromLongPrepared
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evmSolm0)
    (er := bytesStoreSetMappedRef I)
    (baseSlot := bytesStoreSetMappedSlot I)
    (header := bytesStoreSetMappedHeaderWord σ_evm I)
    (len := oldStoredLen)
    (value := value)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreSetMappedSlot I) evmSolm0, ?_, by simp⟩
      simp [bytesStoreLayout, bytesStoreSetMappedRef,
        bytesStoreSetMappedRefOf, bytesStoreSetMappedSlot,
        bytesStoreSetMappedSlotOf])
    hvalueSize
    hload
    hflag holdStoredLen hvalid
  simpa [evmSolm0, value, bytesStoreSetMappedRef,
    bytesStoreSetMappedRefOf, bytesStoreSetMappedSlot,
    clearSolidityBytesDataWordsFrom_executionEnv]
    using hwrite

theorem bytesStoreSetMappedWriteShortOldLongPrepared
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
      UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩) :
    let value := bytesStoreSetMappedValueBytes I
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
      (bytesStoreSetMappedSlot I) 0 ((oldStoredLen.toNat + 31) / 32)
    let evmData := Solm.EVM.storageStore evmClear I.codeOwner
      (bytesStoreSetMappedSlot I) (solidityShortBytesWord value)
    writeStorage? bytesStoreConfig evmSolm0
      (bytesStoreSetMappedRef I) .bytes
      (.bytes value) = .ok evmData := by
  dsimp only
  let value := bytesStoreSetMappedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreSetMappedSlot I) 0 ((oldStoredLen.toNat + 31) / 32)
  let evmData := Solm.EVM.storageStore evmClear I.codeOwner
    (bytesStoreSetMappedSlot I) (solidityShortBytesWord value)
  have hvalueSize : value.size < 32 := by
    dsimp [value]
    rw [bytesStoreSetMappedValueBytes_size hpayload, ← hlenAbi]
    exact hshort
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedSlot I) =
        bytesStoreSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite := writeSolidityBytesShortFromLongPrepared
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evmSolm0)
    (er := bytesStoreSetMappedRef I)
    (baseSlot := bytesStoreSetMappedSlot I)
    (header := bytesStoreSetMappedHeaderWord σ_evm I)
    (len := oldStoredLen)
    (value := value)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreSetMappedSlot I) evmSolm0, ?_, by simp⟩
      simp [bytesStoreLayout, bytesStoreSetMappedRef,
        bytesStoreSetMappedRefOf, bytesStoreSetMappedSlot,
        bytesStoreSetMappedSlotOf])
    hvalueSize
    hload
    hflag holdStoredLen hvalid
  simpa [evmSolm0, evmClear, evmData, value, bytesStoreSetMappedRef,
    bytesStoreSetMappedRefOf, bytesStoreSetMappedSlot,
    clearSolidityBytesDataWordsFrom_executionEnv]
    using hwrite

theorem bytesStoreSetMappedShortFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {oldLen storedWord : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hstored : storedWord = solidityShortBytesWord value)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreSetMappedSlot I)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        (bytesStoreSetMappedSlot I) storedWord)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (bytesStoreSetMappedSlot I) 0 ((oldLen.toNat + 31) / 32))
        I.codeOwner (bytesStoreSetMappedSlot I)
          (solidityShortBytesWord value)).accountMap := by
  exact accountMapEquiv_setBytesShortFromLongPostAccountMapEquiv
    (baseSlot := bytesStoreSetMappedSlot I)
    (oldLen := oldLen) (storedWord := storedWord) (value := value)
    hAccounts hstored holdLenLt

theorem bytesStoreSetMappedEmptyFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {oldLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreSetMappedSlot I)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        (bytesStoreSetMappedSlot I) ⟨0⟩)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (bytesStoreSetMappedSlot I) 0 ((oldLen.toNat + 31) / 32))
        I.codeOwner (bytesStoreSetMappedSlot I) ⟨0⟩).accountMap := by
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hstored : (⟨0⟩ : UInt256) = solidityShortBytesWord ByteArray.empty := hshortEmpty.symm
  simpa [initState, hshortEmpty] using
    bytesStoreSetMappedShortFromLongPostAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (oldLen := oldLen) (storedWord := (⟨0⟩ : UInt256))
      (value := ByteArray.empty) hAccounts hstored holdLenLt

theorem bytesStoreSetMappedWriteLongOldShortPackedAbsent
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
      UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hmissing :
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).accountMap.find?
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner =
          none) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let value := bytesStoreSetMappedValueBytes I
    writeStorage? bytesStoreConfig evmSolm0
      (bytesStoreSetMappedRef I) .bytes (.bytes value) = .ok evmSolm0 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let value := bytesStoreSetMappedValueBytes I
  have hwrite₀ := bytesStoreSetMappedWriteLongOldShortPacked
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
    hAccounts hlenAbi hpayload hlong hflag hvalid
  have hdata :
      writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreSetMappedSlot I) value 0
          (solidityBytesDataWordCount value.size) = evmSolm0 := by
    exact writeSolidityBytesDataWordsFrom_absent_same
      (evm := evmSolm0) (baseSlot := bytesStoreSetMappedSlot I)
      (value := value) (idx := 0) (fuel := solidityBytesDataWordCount value.size)
      (by simpa [evmSolm0] using hmissing)
  have hstore :
      Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreSetMappedSlot I) value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreSetMappedSlot I) value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          (bytesStoreSetMappedSlot I) (solidityBytesHeaderWord value.size) =
        evmSolm0 := by
    rw [hdata]
    exact storageStore_absent evmSolm0 evmSolm0.executionEnv.codeOwner
      (by simpa [evmSolm0] using hmissing)
      (bytesStoreSetMappedSlot I) (solidityBytesHeaderWord value.size)
  simpa [evmSolm0, value, hstore] using hwrite₀

theorem bytesStoreSetMappedWriteMalformedLong {evm : EVM.State}
    (I : ExecutionEnv) (header : UInt256) (value : ByteArray)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedSlot I) = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreConfig evm
      (bytesStoreSetMappedRef I) .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedLong
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm)
    (er := bytesStoreSetMappedRef I)
    (baseSlot := bytesStoreSetMappedSlot I) (header := header) (value := value)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreSetMappedSlot I) evm, ?_, by simp⟩
      simp [bytesStoreLayout, bytesStoreSetMappedRef,
        bytesStoreSetMappedRefOf, bytesStoreSetMappedSlot,
        bytesStoreSetMappedSlotOf])
    hload hflag hbad

theorem bytesStoreSetMappedWriteMalformedShort {evm : EVM.State}
    (I : ExecutionEnv) (header : UInt256) (value : ByteArray)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
        (bytesStoreSetMappedSlot I) = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreConfig evm
      (bytesStoreSetMappedRef I) .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedShort
    (cfg := bytesStoreConfig) (layout := bytesStoreLayout)
    (evm := evm)
    (er := bytesStoreSetMappedRef I)
    (baseSlot := bytesStoreSetMappedSlot I) (header := header) (value := value)
    rfl
    (by
      refine ⟨bytesLikeLengthLoc (bytesStoreSetMappedSlot I) evm, ?_, by simp⟩
      simp [bytesStoreLayout, bytesStoreSetMappedRef,
        bytesStoreSetMappedRefOf, bytesStoreSetMappedSlot,
        bytesStoreSetMappedSlotOf])
    hload hflag hbad

theorem bytesStoreSetMappedLengthAfterEmptyWrite
    {cA gh bl σ_solm σ₀ A I} {g : UInt256} :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreSetMappedSlot I) ⟨0⟩
    readStorageBytesLength? bytesStoreConfig evmSolm1
      (bytesStoreSetMappedRef I) = .ok 0 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetMappedSlot I) ⟨0⟩
  exact bytesStoreReadLengthAfterHeaderStoreZero
    (er := bytesStoreSetMappedRef I) (evm := evmSolm0) (evmData := evmSolm1)
    (baseSlot := bytesStoreSetMappedSlot I) (by rfl)
    (bytesStoreSetMappedRef_length_slot evmSolm1 I)

theorem bytesStoreSetMappedLengthAfterShortWrite
    {cA gh bl σ_solm σ₀ A I} {g len payloadStart : UInt256} {acc : Account}
    (hacc : σ_solm.find? I.codeOwner = some acc)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let storedWord := bytesStoreSetMappedShortStoredWord I len payloadStart
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
      (bytesStoreSetMappedSlot I) storedWord
    readStorageBytesLength? bytesStoreConfig evmSolm1
      (bytesStoreSetMappedRef I) = .ok len.toNat := by
  dsimp only
  let storedWord := bytesStoreSetMappedShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetMappedSlot I) storedWord
  have hdecode :
      solidityDecodeBytesLengthHeader storedWord = .ok len.toNat := by
    exact solidityDecodeBytesLengthHeader_short_valid
      (header := storedWord) (len := len)
      (by
        simpa [storedWord, bytesStoreSetMappedShortStoredWord] using
          bytesStoreSetChunkShortStoredWord_flag_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        symm
        simpa [storedWord, bytesStoreSetMappedShortStoredWord] using
          bytesStoreSetChunkShortStoredWord_shortLen_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        rw [show UInt256.lt len ⟨32⟩ = ⟨1⟩ by
          exact ult_one (by
            rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
            exact hshort)]
        have hflag :
            UInt256.land storedWord ⟨1⟩ = ⟨0⟩ := by
          simpa [storedWord, bytesStoreSetMappedShortStoredWord] using
            bytesStoreSetChunkShortStoredWord_flag_eq
              (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
        rw [hflag]
        native_decide)
  have hacc0 : evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner = some acc := by
    simpa [evmSolm0, initState] using hacc
  exact bytesStoreReadLengthAfterHeaderStorePresent
    (er := bytesStoreSetMappedRef I) (evm := evmSolm0) (evmData := evmSolm1)
    (baseSlot := bytesStoreSetMappedSlot I) (header := storedWord) (len := len.toNat)
    (by rfl)
    (bytesStoreSetMappedRef_length_slot evmSolm1 I)
    hacc0
    hdecode

theorem bytesStoreSetMappedLengthAfterLongStoreOfState
    {evm : EVM.State} {I : ExecutionEnv} {len header : UInt256} {acc : Account}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hacc : evm.accountMap.find? I.codeOwner = some acc)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
      (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreSetMappedSlot I) header
    readStorageBytesLength? bytesStoreConfig evmData
      (bytesStoreSetMappedRef I) = .ok len.toNat := by
  dsimp only
  let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreSetMappedSlot I) header
  have hdecode :
      solidityDecodeBytesLengthHeader header = .ok len.toNat := by
    exact solidityDecodeBytesLengthHeader_long_valid
      (header := header) (len := len) hflag hlen (by simpa [← hlen] using hvalid)
  simpa [evmData, storageStore_executionEnv, howner] using
    bytesStoreReadLengthAfterHeaderStorePresent
      (er := bytesStoreSetMappedRef I) (evm := evm) (evmData := evmData)
      (baseSlot := bytesStoreSetMappedSlot I) (header := header) (len := len.toNat)
      (by simp [evmData, howner])
      (by simpa [evmData, howner] using bytesStoreSetMappedRef_length_slot evmData I)
      (by simpa [howner] using hacc)
      hdecode

theorem bytesStoreSetMappedLengthAfterShortStoreOfState
    {evm : EVM.State} {I : ExecutionEnv} {len payloadStart : UInt256} {acc : Account}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hacc : evm.accountMap.find? I.codeOwner = some acc)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let storedWord := bytesStoreSetMappedShortStoredWord I len payloadStart
    let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreSetMappedSlot I) storedWord
    readStorageBytesLength? bytesStoreConfig evmData
      (bytesStoreSetMappedRef I) = .ok len.toNat := by
  dsimp only
  let storedWord := bytesStoreSetMappedShortStoredWord I len payloadStart
  let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreSetMappedSlot I) storedWord
  have hdecode :
      solidityDecodeBytesLengthHeader storedWord = .ok len.toNat := by
    exact solidityDecodeBytesLengthHeader_short_valid
      (header := storedWord) (len := len)
      (by
        simpa [storedWord, bytesStoreSetMappedShortStoredWord] using
          bytesStoreSetChunkShortStoredWord_flag_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        symm
        simpa [storedWord, bytesStoreSetMappedShortStoredWord] using
          bytesStoreSetChunkShortStoredWord_shortLen_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        rw [show UInt256.lt len ⟨32⟩ = ⟨1⟩ by
          exact ult_one (by
            rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
            exact hshort)]
        have hflag :
            UInt256.land storedWord ⟨1⟩ = ⟨0⟩ := by
          simpa [storedWord, bytesStoreSetMappedShortStoredWord] using
            bytesStoreSetChunkShortStoredWord_flag_eq
              (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
        rw [hflag]
        native_decide)
  simpa [evmData, storageStore_executionEnv, howner] using
    bytesStoreReadLengthAfterHeaderStorePresent
      (er := bytesStoreSetMappedRef I) (evm := evm) (evmData := evmData)
      (baseSlot := bytesStoreSetMappedSlot I) (header := storedWord) (len := len.toNat)
      (by simp [evmData, howner])
      (by simpa [evmData, howner] using bytesStoreSetMappedRef_length_slot evmData I)
      (by simpa [howner] using hacc)
      hdecode

theorem bytesStoreSetMappedLengthAfterEmptyStoreOfState
    {evm : EVM.State} {I : ExecutionEnv}
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreSetMappedSlot I) ⟨0⟩
    readStorageBytesLength? bytesStoreConfig evmData
      (bytesStoreSetMappedRef I) = .ok 0 := by
  dsimp only
  let evmData := Solm.EVM.storageStore evm I.codeOwner (bytesStoreSetMappedSlot I) ⟨0⟩
  simpa [evmData, storageStore_executionEnv, howner] using
    bytesStoreReadLengthAfterHeaderStoreZero
      (er := bytesStoreSetMappedRef I) (evm := evm) (evmData := evmData)
      (baseSlot := bytesStoreSetMappedSlot I)
      (by simp [evmData, howner])
      (by simpa [evmData, howner] using bytesStoreSetMappedRef_length_slot evmData I)

theorem bytesStoreSetMappedSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0xe1, 0x91, 0x9b, 0x17]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreReachSetMappedDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2154⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨498⟩, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hreach⟩ := bytesStoreReachSetMapped
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  exact ⟨_, _, by
    simpa [bytesStoreSetMappedEntryPc] using
      (evm_run hreach with [
        jumpdest, push2 ⟨263⟩, push2 ⟨498⟩, calldatasize, push1 ⟨4⟩,
        push2 ⟨2154⟩, jump (by native_decide)])⟩

theorem bytesStoreX_setMappedDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetMappedDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setMappedDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetMappedDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2172⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreX_setMappedDecodeOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetMappedDecoder
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

theorem bytesStoreX_setMappedDecodeLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetMappedDecoder
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

theorem bytesStoreX_setMappedDecodeLengthHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
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
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetMappedDecoder
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

theorem bytesStoreX_setMappedDecodePayloadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
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
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetMappedDecoder
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
theorem bytesStoreX_setMappedDecodeValidRaw {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreBytecode) (hwv : I.weiValue = ⟨0⟩)
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
    ∃ k C, RD bytesStoreBytecode I g
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
        ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdec⟩ := bytesStoreReachSetMappedDecoder
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

theorem bytesStoreX_setMappedReachWriteHelper {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart key : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2599⟩
      [bytesStoreSetMappedSlotOf key, payloadStart, len, ⟨1668⟩,
        bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1644⟩ := hreach
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨4⟩ solcFreePtrMem).readWithPadding 0 64))) =
        bytesStoreSetMappedSlotOf key := by
    rw [twoWordHashMem_read0_64 key ⟨4⟩ solcFreePtrMem_size]
    unfold bytesStoreSetMappedSlotOf mappedValueSlot
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
    raw keccak256 0 (bytesStoreSetMappedSlotOf key) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)]
  exact ⟨_, _, evm_run rd1658 with [
    push2 ⟨1668⟩, dup4, dup6, dup4, push2 ⟨2599⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setMappedReachWriteHeaderDecoder {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart key : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      ((bytesStoreSetMappedHeaderWordOf σ I key) ::
        ⟨2637⟩ :: len :: ⟨2643⟩ :: bytesStoreSetMappedSlotOf key ::
        payloadStart :: len :: ⟨1668⟩ :: bytesStoreSetMappedSlotOf key ::
        ⟨0⟩ :: len :: payloadStart :: key :: ⟨263⟩ ::
        bytesStoreSelWord I :: [])
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  have hhelper := bytesStoreX_setMappedReachWriteHelper
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key) hreach
  simpa [bytesStoreSetMappedHeaderWordOf] using
    bytesStoreX_writeBytesHelperReachHeaderDecoder
      (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (slot := bytesStoreSetMappedSlotOf key)
      (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
      (tail := [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreSelWord I])
      (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
      (rdata := ByteArray.empty) hhelper hlenMax
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedLongMalformedHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart key : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreX_setMappedReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key) hreach hlenMax
  exact bytesStoreX_bytesLengthDecoderLongMalformedMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (header := bytesStoreSetMappedHeaderWordOf σ I key) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, bytesStoreSetMappedSlotOf key, payloadStart, len,
      ⟨1668⟩, bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem)
    hdecoder hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedShortMalformedHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart key : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreX_setMappedReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key) hreach hlenMax
  exact bytesStoreX_bytesLengthDecoderShortMalformedMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (header := bytesStoreSetMappedHeaderWordOf σ I key) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, bytesStoreSetMappedSlotOf key, payloadStart, len,
      ⟨1668⟩, bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem)
    hdecoder hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedShortHeaderReachWriteBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart key : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [bytesStoreSetMappedSlotOf key, payloadStart, len, ⟨1668⟩,
        bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  have hhelper := bytesStoreX_setMappedReachWriteHelper
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key) hreach
  exact bytesStoreX_writeBytesHelperShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreSetMappedSlotOf key)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hhelper hlenMax hflag hvalid
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedLongHeaderNoClearReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let header : UInt256 := bytesStoreSetMappedHeaderWordOf σ I key
  have hdecoder := bytesStoreX_setMappedReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax
  have hstoredEq : UInt256.div header ⟨2⟩ = oldStoredLen := by
    simpa [header] using holdStoredLen.symm
  have hvalidHeader :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [header, hstoredEq] using hvalid
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩,
      len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header, slot] using hdecoder)
    (by simpa [header] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩,
          slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [slot, oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩,
        slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2637 with [
      jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldStoredLen ≠ ⟨0⟩ :=
    StringStoreLite.clearCurrentLongValid_gt31
      (header := header) (len := oldStoredLen)
      (by simpa [header] using hflag)
      (by simpa [header] using hvalid)
  have holdLong : UInt256.gt oldStoredLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldStoredLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldStoredLen from rfl]
    exact StringStoreLite.clearCurrent_ult_eq_one_of_ne_zero hgt31
  simpa [slot] using
    bytesStoreX_writeBytesCleanupOldLongNoClear
      (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
      (len := len) (ret := ⟨2643⟩)
      (tail := [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
        key, ⟨263⟩, bytesStoreSelWord I])
      (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem)
      (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
      hcleanupReach holdLong hgtOldNew (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedLongNoTailOldLongNoClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  have hbranch := bytesStoreX_setMappedLongHeaderNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (key := key) (oldStoredLen := oldStoredLen)
    hreach hlenMax hflag holdStoredLen hvalid hgtOldNew
  exact bytesStoreX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm (by simpa [slot] using hbranch) hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedLongTailOldLongNoClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (StringStoreLite.longDataWordsLoopSlot
            (bytesLikeDataBase slot) (len.toNat / 32))
          (StringStoreLite.longDataTailMaskedWord
            (bytesStoreCalldataLongDataWord I payloadStart
              (StringStoreLite.longDataWordsLoopStride
                (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  have hbranch := bytesStoreX_setMappedLongHeaderNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (key := key) (oldStoredLen := oldStoredLen)
    hreach hlenMax hflag holdStoredLen hvalid hgtOldNew
  exact bytesStoreX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm (by simpa [slot] using hbranch) hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedLongHeaderClearReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩))) =
        ⟨0⟩)
    (hdone :
      UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)) =
        ⟨0⟩) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩ fuel
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σClear) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let header : UInt256 := bytesStoreSetMappedHeaderWordOf σ I key
  have hdecoder := bytesStoreX_setMappedReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax
  have hstoredEq : UInt256.div header ⟨2⟩ = oldStoredLen := by
    simpa [header] using holdStoredLen.symm
  have hvalidHeader :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [header, hstoredEq] using hvalid
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩,
      len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header, slot] using hdecoder)
    (by simpa [header] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩, slot,
          ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [slot, oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩,
        slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2637 with [
      jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldStoredLen ≠ ⟨0⟩ :=
    StringStoreLite.clearCurrentLongValid_gt31
      (header := header) (len := oldStoredLen)
      (by simpa [header] using hflag)
      (by simpa [header] using hvalid)
  have holdLong : UInt256.gt oldStoredLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldStoredLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldStoredLen from rfl]
    exact StringStoreLite.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have hlongWord : UInt256.lt len ⟨32⟩ = ⟨0⟩ :=
    ult_zero (by
      have hle : 32 ≤ len.toNat := Nat.le_of_not_gt hlong
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hle)
  have hloopEntry := bytesStoreX_writeBytesCleanupOldLongLongToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
    (len := len) (ret := ⟨2643⟩)
    (tail := [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
      key, ⟨263⟩, bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hcleanupReach holdLong hgtOldNew hlongWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hloop := bytesStoreX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩))
    (base := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot)
    (dead₀ := slot) (dead₁ := oldStoredLen) (dead₂ := len)
    (ret := (⟨2643⟩ : UInt256))
    (rest := [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
      key, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [slot] using hloop

theorem bytesStoreX_setMappedLongHeaderClearReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
          bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat) k C := by
  let count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
    (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreX_setMappedLongHeaderClearReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (len := len) (payloadStart := payloadStart)
      (key := key) (oldStoredLen := oldStoredLen) (fuel := count.toNat)
      hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
      hcontinue hdone

theorem bytesStoreX_setMappedLongNoTailOldLongClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreCalldataLongDataForwardFrom I.codeOwner σClear
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
      (StringStoreLite.clearCurrentHashAw
        (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  have hbranch := bytesStoreX_setMappedLongHeaderClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (key := key) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
  exact bytesStoreX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σClear) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    hperm (by simpa [slot, σClear] using hbranch) hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedLongTailOldLongClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreCalldataLongDataForwardFrom I.codeOwner σClear
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (StringStoreLite.longDataWordsLoopSlot
            (bytesLikeDataBase slot) (len.toNat / 32))
          (StringStoreLite.longDataTailMaskedWord
            (bytesStoreCalldataLongDataWord I payloadStart
              (StringStoreLite.longDataWordsLoopStride
                (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
      (StringStoreLite.clearCurrentHashAw
        (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  have hbranch := bytesStoreX_setMappedLongHeaderClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (key := key) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
  exact bytesStoreX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σClear) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    hperm (by simpa [slot, σClear] using hbranch) hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedReachReturnLengthDecoderFromMemEarly
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart key : UInt256} {mem : ByteArray}
    (hmem : mem.size = 96)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      mem (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [bytesStoreSetMappedHeaderWordOf σ I key, ⟨1002⟩, bytesStoreSetMappedSlotOf key,
        ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (twoWordHashMem key ⟨4⟩ mem)
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1668⟩ := hreach
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨4⟩ mem).readWithPadding 0 64))) =
        bytesStoreSetMappedSlotOf key := by
    rw [twoWordHashMem_read0_64 key ⟨4⟩ hmem]
    unfold bytesStoreSetMappedSlotOf mappedValueSlot
    rw [keyValueToWord_uint256]
    exact mappingSlot_single key ⟨4⟩
  have rd1683 := evm_run rd1668 with [
    jumpdest, pop, push0, dup5, dup2,
    raw mstore 0 (wordAt0Mem key mem)
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0
      (twoWordHashMem key ⟨4⟩ mem)
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (bytesStoreSetMappedSlotOf key)
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1684₀⟩ := rd1683.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1684⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1685⟩
        [bytesStoreSetMappedHeaderWordOf σ I key, bytesStoreSetMappedSlotOf key,
          ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
        (twoWordHashMem key ⟨4⟩ mem)
        (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreSetMappedHeaderWordOf, initState] using rd1684₀⟩
  exact ⟨_, _, evm_run rd1684 with [
    push2 ⟨1002⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setMappedLongNoTailOldLongClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (haccData :
      (bytesStoreCalldataLongDataForwardFrom I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
            bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat)
        (bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) payloadStart
        (⟨0⟩ : UInt256) I (len.toNat / 32)).find? I.codeOwner = some acc) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σLoop : AccountMap :=
      bytesStoreCalldataLongDataForwardFrom I.codeOwner σClear
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let start : UInt256 := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩
  let count : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ (start + bytesLikeDataBase slot) ⟨0⟩ count.toNat
  let σLoop : AccountMap :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap := sstoreAccountMap I.codeOwner σLoop slot header
  let loadedHeader : UInt256 := bytesStoreSetMappedHeaderWordOf σData I key
  let writeMem : ByteArray :=
    wordAt0Mem slot (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hbody := bytesStoreX_setMappedLongNoTailOldLongClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong hnoTailMod
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoderFromMemEarly
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
        StringStoreLite.clearCurrentHashAw] using hbody)
  have hdata : bytesStoreSetMappedHeaderWordOf σData I key = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σLoop, σClear, slot, header, start, count,
      bytesStoreSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some σLoop I.codeOwner acc
        slot header
        (by simpa [σLoop, σClear, slot, start, count] using haccData) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, retMem] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (chunkIndex := key)
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreX_returnWord263OfMemState
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
          (bytesStoreWordAt0Mem_read64 slot
            (wordAt0Mem_size_96 slot
              (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
            (bytesStoreWordAt0Mem_read64 slot
              (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
              (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64))))
    (by simpa [StringStoreLite.clearCurrentHashAw] using h263)

theorem bytesStoreX_setMappedLongTailOldLongClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreCalldataLongDataForwardFrom I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner σ
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
              bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) ⟨0⟩
            (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
              (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat)
          (bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) payloadStart
          (⟨0⟩ : UInt256) I (len.toNat / 32))
        (StringStoreLite.longDataWordsLoopSlot
          (bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) (len.toNat / 32))
        (StringStoreLite.longDataTailMaskedWord
          (bytesStoreCalldataLongDataWord I payloadStart
            (StringStoreLite.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σLoop : AccountMap :=
      bytesStoreCalldataLongDataForwardFrom I.codeOwner σClear
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let tailSlot : UInt256 :=
      StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
    let tailWord : UInt256 :=
      StringStoreLite.longDataTailMaskedWord
        (bytesStoreCalldataLongDataWord I payloadStart
          (StringStoreLite.longDataWordsLoopStride
            (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
    let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let start : UInt256 := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩
  let count : UInt256 :=
    UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ (start + bytesLikeDataBase slot) ⟨0⟩ count.toNat
  let σLoop : AccountMap :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    StringStoreLite.longDataTailMaskedWord
      (bytesStoreCalldataLongDataWord I payloadStart
        (StringStoreLite.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap := sstoreAccountMap I.codeOwner σTail slot header
  let loadedHeader : UInt256 := bytesStoreSetMappedHeaderWordOf σData I key
  let writeMem : ByteArray :=
    wordAt0Mem slot (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hbody := bytesStoreX_setMappedLongTailOldLongClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong htailMod
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoderFromMemEarly
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
        start, count, writeMem, StringStoreLite.clearCurrentHashAw] using hbody)
  have hdata : bytesStoreSetMappedHeaderWordOf σData I key = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σTail, σLoop, σClear, tailSlot, tailWord, slot, header,
      start, count, bytesStoreSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some σTail I.codeOwner acc
        slot header
        (by simpa [σTail, σLoop, σClear, tailSlot, tailWord, slot, start, count]
          using haccTail)
        hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, retMem] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (chunkIndex := key)
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreX_returnWord263OfMemState
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
          (bytesStoreWordAt0Mem_read64 slot
            (wordAt0Mem_size_96 slot
              (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
            (bytesStoreWordAt0Mem_read64 slot
              (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
              (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64))))
    (by simpa [StringStoreLite.clearCurrentHashAw] using h263)

theorem bytesStoreX_setMappedLongNoTailOldShortWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  have hbranch := bytesStoreX_setMappedShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax hflag hvalid
  exact bytesStoreX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm (by simpa [slot] using hbranch) hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedLongTailOldShortWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
            (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (StringStoreLite.longDataWordsLoopSlot
            (bytesLikeDataBase slot) (len.toNat / 32))
          (StringStoreLite.longDataTailMaskedWord
            (bytesStoreCalldataLongDataWord I payloadStart
              (StringStoreLite.longDataWordsLoopStride
                (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
        slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  have hbranch := bytesStoreX_setMappedShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax hflag hvalid
  exact bytesStoreX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    hperm (by simpa [slot] using hbranch) hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedEmptyWriteReturnsToBody {cA gh bl σ σ₀ A I}
    {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedSlotOf key) ⟨0⟩)
      k C := by
  have hbranch := bytesStoreX_setMappedShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax hflag hvalid
  have hpacked := bytesStoreX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreSetMappedSlotOf key)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hbranch hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hwrite := bytesStoreX_writeBytesNewEmptyWriteHeaderGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreSetMappedSlotOf key)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm hpacked hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedSlotOf key) ⟨0⟩)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := bytesStoreSetMappedSlotOf key) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1668⟩)
    (tail := [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hwrite (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedShortNonemptyWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedSlotOf key)
        (bytesStoreSetMappedShortStoredWord I len payloadStart)) k C := by
  have hbranch := bytesStoreX_setMappedShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax hflag hvalid
  have hwrite := bytesStoreX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreSetMappedSlotOf key)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm hbranch hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedSlotOf key)
      (bytesStoreSetMappedShortStoredWord I len payloadStart))
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (slot := bytesStoreSetMappedSlotOf key) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1668⟩)
    (tail := [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty)
    (by simpa [bytesStoreSetMappedShortStoredWord] using hwrite)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedReachReturnLengthDecoder
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart key : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [bytesStoreSetMappedHeaderWordOf σ I key, ⟨1002⟩, bytesStoreSetMappedSlotOf key,
        ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd1668⟩ := hreach
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC
          ((twoWordHashMem key ⟨4⟩
            (twoWordHashMem key ⟨4⟩ solcFreePtrMem)).readWithPadding 0 64))) =
        bytesStoreSetMappedSlotOf key := by
    rw [twoWordHashMem_read0_64 key ⟨4⟩
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)]
    unfold bytesStoreSetMappedSlotOf mappedValueSlot
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
    raw keccak256 0 (bytesStoreSetMappedSlotOf key) (UInt256.ofNat 3)
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1684₀⟩ := rd1683.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1684⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1685⟩
        [bytesStoreSetMappedHeaderWordOf σ I key, bytesStoreSetMappedSlotOf key,
          ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
        (twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
        (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreSetMappedHeaderWordOf, initState] using rd1684₀⟩
  exact ⟨_, _, evm_run rd1684 with [
    push2 ⟨1002⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setMappedReachReturnLengthDecoderFromMem
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {slot len payloadStart key : UInt256} {mem : ByteArray}
    (hmem : mem.size = 96)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      mem (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
      ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [bytesStoreSetMappedHeaderWordOf σ I key, ⟨1002⟩, bytesStoreSetMappedSlotOf key,
        ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (twoWordHashMem key ⟨4⟩ mem)
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd1668⟩ := hreach
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key ⟨4⟩ mem).readWithPadding 0 64))) =
        bytesStoreSetMappedSlotOf key := by
    rw [twoWordHashMem_read0_64 key ⟨4⟩ hmem]
    unfold bytesStoreSetMappedSlotOf mappedValueSlot
    rw [keyValueToWord_uint256]
    exact mappingSlot_single key ⟨4⟩
  have rd1683 := evm_run rd1668 with [
    jumpdest, pop, push0, dup5, dup2,
    raw mstore 0 (wordAt0Mem key mem)
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨4⟩, push1 ⟨32⟩,
    raw mstore 0
      (twoWordHashMem key ⟨4⟩ mem)
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) (by native_decide)
      mem_cost
      (by rfl)
      (by native_decide) (by evm_ov),
    push1 ⟨64⟩, swap1,
    raw keccak256 0 (bytesStoreSetMappedSlotOf key)
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
      (by native_decide) mem_cost hslot (by native_decide) (by evm_ov),
    dup1]
  obtain ⟨_, _, rd1684₀⟩ := rd1683.sload (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1684⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨1685⟩
        [bytesStoreSetMappedHeaderWordOf σ I key, bytesStoreSetMappedSlotOf key,
          ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
        (twoWordHashMem key ⟨4⟩ mem)
        (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
        (cA, σ) k C := by
    exact ⟨_, _, by simpa [bytesStoreSetMappedHeaderWordOf, initState] using rd1684₀⟩
  exact ⟨_, _, evm_run rd1684 with [
    push2 ⟨1002⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreX_setMappedReturnFromDecodedLength
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {mappedLen slot len payloadStart key : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1002⟩
      [mappedLen, slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
        bytesStoreSelWord I]
      mem aw rdata (cA, σ) k C) :
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨263⟩
      [mappedLen, bytesStoreSelWord I]
      mem aw rdata (cA, σ) k C := by
  exact bytesStoreX_setChunkReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σinit) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (chunkLen := mappedLen) (slot := slot)
    (len := len) (payloadStart := payloadStart) (chunkIndex := key)
    (mem := mem) (rdata := rdata) (aw := aw) hreach

theorem bytesStoreX_setMappedLongNoTailReturnsOfBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    {acc : Account}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hlong : ¬ len.toNat < 32)
    (hbody :
      let slot : UInt256 := bytesStoreSetMappedSlotOf key
      let σLoop : AccountMap :=
        bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32)
      let σData : AccountMap :=
        sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
        [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
        (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
        (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
        (cA, σData) k C)
    (haccData :
      (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) payloadStart
        (⟨0⟩ : UInt256) I (len.toNat / 32)).find? I.codeOwner = some acc) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σLoop : AccountMap :=
      bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only at hbody ⊢
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap := sstoreAccountMap I.codeOwner σLoop slot header
  let loadedHeader : UInt256 := bytesStoreSetMappedHeaderWordOf σData I key
  let writeMem : ByteArray := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
    (by simpa [σLoop, σData, slot, header, writeMem] using hbody)
  have hdata : bytesStoreSetMappedHeaderWordOf σData I key = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σLoop, slot, header, bytesStoreSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some σLoop I.codeOwner acc
        slot header (by simpa [σLoop, slot] using haccData) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, retMem] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreX_returnWord263OfMemState
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
          (bytesStoreWordAt0Mem_read64 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
            (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [StringStoreLite.clearCurrentHashAw] using h263)

theorem bytesStoreX_setMappedLongTailReturnsOfBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    {acc : Account}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hlong : ¬ len.toNat < 32)
    (hbody :
      let slot : UInt256 := bytesStoreSetMappedSlotOf key
      let σLoop : AccountMap :=
        bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32)
      let tailSlot : UInt256 :=
        StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
      let tailWord : UInt256 :=
        StringStoreLite.longDataTailMaskedWord
          (bytesStoreCalldataLongDataWord I payloadStart
            (StringStoreLite.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
      let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
      let σData : AccountMap :=
        sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
        [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
        (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
        (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
        (cA, σData) k C)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) payloadStart
          (⟨0⟩ : UInt256) I (len.toNat / 32))
        (StringStoreLite.longDataWordsLoopSlot
          (bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) (len.toNat / 32))
        (StringStoreLite.longDataTailMaskedWord
          (bytesStoreCalldataLongDataWord I payloadStart
            (StringStoreLite.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σLoop : AccountMap :=
      bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let tailSlot : UInt256 :=
      StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
    let tailWord : UInt256 :=
      StringStoreLite.longDataTailMaskedWord
        (bytesStoreCalldataLongDataWord I payloadStart
          (StringStoreLite.longDataWordsLoopStride
            (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
    let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only at hbody ⊢
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    StringStoreLite.longDataTailMaskedWord
      (bytesStoreCalldataLongDataWord I payloadStart
        (StringStoreLite.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap := sstoreAccountMap I.codeOwner σTail slot header
  let loadedHeader : UInt256 := bytesStoreSetMappedHeaderWordOf σData I key
  let writeMem : ByteArray := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
    (by simpa [σLoop, tailSlot, tailWord, σTail, σData, slot, header, writeMem]
      using hbody)
  have hdata : bytesStoreSetMappedHeaderWordOf σData I key = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σTail, σLoop, tailSlot, tailWord, slot, header,
      bytesStoreSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some σTail I.codeOwner acc
        slot header
        (by simpa [σTail, σLoop, tailSlot, tailWord, slot] using haccTail) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, retMem] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreX_returnWord263OfMemState
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
          (bytesStoreWordAt0Mem_read64 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
            (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [StringStoreLite.clearCurrentHashAw] using h263)

theorem bytesStoreX_setMappedLongNoTailOldLongNoClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (haccData :
      (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) payloadStart
        (⟨0⟩ : UInt256) I (len.toNat / 32)).find? I.codeOwner = some acc) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σLoop : AccountMap :=
      bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let σLoop : AccountMap :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap :=
    sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hbody := bytesStoreX_setMappedLongNoTailOldLongNoClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong hnoTailMod
  exact bytesStoreX_setMappedLongNoTailReturnsOfBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key) (acc := acc)
    hlenMax hlong
    (by simpa [slot, σLoop, σData] using hbody)
    (by simpa [slot] using haccData)

theorem bytesStoreX_setMappedLongTailOldLongNoClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) payloadStart
          (⟨0⟩ : UInt256) I (len.toNat / 32))
        (StringStoreLite.longDataWordsLoopSlot
          (bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) (len.toNat / 32))
        (StringStoreLite.longDataTailMaskedWord
          (bytesStoreCalldataLongDataWord I payloadStart
            (StringStoreLite.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σLoop : AccountMap :=
      bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let tailSlot : UInt256 :=
      StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
    let tailWord : UInt256 :=
      StringStoreLite.longDataTailMaskedWord
        (bytesStoreCalldataLongDataWord I payloadStart
          (StringStoreLite.longDataWordsLoopStride
            (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
    let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let σLoop : AccountMap :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    StringStoreLite.longDataTailMaskedWord
      (bytesStoreCalldataLongDataWord I payloadStart
        (StringStoreLite.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap :=
    sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  have hbody := bytesStoreX_setMappedLongTailOldLongNoClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong htailMod
  exact bytesStoreX_setMappedLongTailReturnsOfBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key) (acc := acc)
    hlenMax hlong
    (by simpa [slot, σLoop, tailSlot, tailWord, σTail, σData] using hbody)
    (by simpa [slot, σLoop, tailSlot, tailWord, σTail] using haccTail)

theorem bytesStoreX_setMappedShortOldLongReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hshort : len.toNat < 32)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)) =
        ⟨0⟩)
    (hdone :
      UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩) =
        ⟨0⟩) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩ fuel
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
        key, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σClear) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let header : UInt256 := bytesStoreSetMappedHeaderWordOf σ I key
  have hdecoder := bytesStoreX_setMappedReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hreach hlenMax
  have hstoredEq : UInt256.div header ⟨2⟩ = oldStoredLen := by
    simpa [header] using holdStoredLen.symm
  have hvalidHeader :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    simpa [header, hstoredEq] using hvalid
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩,
      len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header, slot] using hdecoder)
    (by simpa [header] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩,
          slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [slot, oldStoredLen, len, ⟨2643⟩, slot, payloadStart, len, ⟨1668⟩,
        slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, evm_run rd2637 with [
      jumpdest, dup4, push2 ⟨2302⟩, jump (by native_decide)]⟩
  have hgt31 : UInt256.lt ⟨31⟩ oldStoredLen ≠ ⟨0⟩ :=
    StringStoreLite.clearCurrentLongValid_gt31
      (header := header) (len := oldStoredLen)
      (by simpa [header] using hflag)
      (by simpa [header] using hvalid)
  have holdLong : UInt256.gt oldStoredLen ⟨31⟩ = ⟨1⟩ := by
    rw [show UInt256.gt oldStoredLen ⟨31⟩ = UInt256.lt ⟨31⟩ oldStoredLen from rfl]
    exact StringStoreLite.clearCurrent_ult_eq_one_of_ne_zero hgt31
  have holdGtNat : 31 < oldStoredLen.toNat := by
    simpa [show (⟨31⟩ : UInt256).toNat = 31 from by decide] using
      ult_ne_zero_toNat_lt hgt31
  have hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩ :=
    ugt_one (by omega)
  have hshortWord : UInt256.lt len ⟨32⟩ = ⟨1⟩ :=
    ult_one (by
      simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
  have hloopEntry := bytesStoreX_writeBytesCleanupOldLongShortToLoop
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (oldLen := oldStoredLen)
    (len := len) (ret := ⟨2643⟩)
    (tail := [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
      key, ⟨263⟩, bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hcleanupReach holdLong hgtOldNew hshortWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hloop := bytesStoreX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)
    (base := (⟨0⟩ : UInt256) + bytesLikeDataBase slot)
    (dead₀ := slot) (dead₁ := oldStoredLen) (dead₂ := len)
    (ret := (⟨2643⟩ : UInt256))
    (rest := [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
      key, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa [slot] using hloop

theorem bytesStoreX_setMappedShortOldLongReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hshort : len.toNat < 32) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [slot, payloadStart, len, ⟨1668⟩, slot, ⟨0⟩, len, payloadStart,
        key, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat) k C := by
  let count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩
  have hcontinue : ∀ i, i < count.toNat →
      UInt256.isZero
        (UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) count) =
          ⟨0⟩ := by
    intro i hi
    have hidx : (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i).toNat = i := by
      rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat]
      exact ulit_toNat' i (lt_trans hi count.val.isLt)
    have hlt : UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ i) count = ⟨1⟩ :=
      ult_one (by simpa [hidx] using hi)
    rw [hlt]
    decide
  have hdone :
      UInt256.lt (StringStoreLite.clearDataWordsLoopIndex ⟨0⟩ count.toNat) count =
        ⟨0⟩ := by
    rw [StringStoreLite.clearDataWordsLoopIndex_zero_ofNat, u256_ofNat_toNat count]
    exact ult_zero (a := count) (b := count) (Nat.le_refl _)
  simpa [count] using
    bytesStoreX_setMappedShortOldLongReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (len := len) (payloadStart := payloadStart)
      (key := key) (oldStoredLen := oldStoredLen) (fuel := count.toNat)
      hperm hreach hlenMax hflag holdStoredLen hvalid hshort hcontinue hdone

theorem bytesStoreX_setMappedShortNonemptyOldLongWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σClear slot
        (bytesStoreSetMappedShortStoredWord I len payloadStart)) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hbranch := bytesStoreX_setMappedShortOldLongReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (key := key) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hshort
  have hwrite := bytesStoreX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (payloadStart := payloadStart)
    (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm
    (by simpa [slot, σClear] using hbranch) hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σClear slot
      (bytesStoreSetMappedShortStoredWord I len payloadStart))
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [bytesStoreSetMappedShortStoredWord] using hwrite)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreX_setMappedEmptyOldLongWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1668⟩
      [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      (wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
      (StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σClear slot ⟨0⟩) k C := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase slot) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hshort : len.toNat < 32 := by
    rw [hlenZero]
    native_decide
  have hbranch := bytesStoreX_setMappedShortOldLongReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (len := len) (payloadStart := payloadStart)
    (key := key) (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hshort
  have hpacked := bytesStoreX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [slot, σClear] using hbranch) hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hwrite := bytesStoreX_writeBytesNewEmptyWriteHeaderGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm hpacked hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σClear slot ⟨0⟩)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := slot)
    (payloadStart := payloadStart) (len := len) (ret := ⟨1668⟩)
    (tail := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hwrite (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreSetMappedEmptyHeaderAfterWrite
    (σ : AccountMap) (I : ExecutionEnv) (key : UInt256) :
    bytesStoreSetMappedHeaderWordOf
        (sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedSlotOf key) ⟨0⟩) I key =
      ⟨0⟩ := by
  unfold bytesStoreSetMappedHeaderWordOf
  change (((sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedSlotOf key) ⟨0⟩).find?
      I.codeOwner).option (default : UInt256)
      (fun acc => acc.storage.findD (bytesStoreSetMappedSlotOf key) (default : UInt256))) =
    ⟨0⟩
  have h := sstoreAccountMap_storage_findD_eq_if σ I.codeOwner
    (bytesStoreSetMappedSlotOf key) (bytesStoreSetMappedSlotOf key) (⟨0⟩ : UInt256)
  rw [h]
  cases σ.find? I.codeOwner with
  | none =>
      simp [Option.option]
      rfl
  | some _ =>
      simp [Option.option]

theorem bytesStoreX_setMappedShortNonemptyOldLongReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (haccClear :
      (clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat).find?
          I.codeOwner = some acc) :
    let storedWord := bytesStoreSetMappedShortStoredWord I len payloadStart
    let σClear :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σClear (bytesStoreSetMappedSlotOf key) storedWord
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray len) := by
  dsimp only
  let storedWord := bytesStoreSetMappedShortStoredWord I len payloadStart
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σClear (bytesStoreSetMappedSlotOf key) storedWord
  let header : UInt256 := bytesStoreSetMappedHeaderWordOf σ' I key
  have hbody := bytesStoreX_setMappedShortNonemptyOldLongWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hnz hshort
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreSetMappedSlotOf key)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := wordAt0Mem (bytesStoreSetMappedSlotOf key)
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (by
      exact wordAt0Mem_size_96 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    (by simpa [σ', σClear, storedWord] using hbody)
  have hdata : bytesStoreSetMappedHeaderWordOf σ' I key = storedWord := by
    have hnzStored := bytesStoreSetChunkShortStoredWord_beq_zero_false
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
    simpa [σ', σClear, storedWord, bytesStoreSetMappedHeaderWordOf,
      bytesStoreSetMappedShortStoredWord] using
      sstoreAccountMap_storage_findD_self_of_find_some σClear I.codeOwner acc
        (bytesStoreSetMappedSlotOf key) storedWord
        (by simpa [σClear] using haccClear) hnzStored
  have hheader : header = storedWord := by
    simpa [header] using hdata
  have hflag' : UInt256.land header ⟨1⟩ = ⟨0⟩ := by
    rw [hheader]
    simpa [storedWord, bytesStoreSetMappedShortStoredWord] using
      bytesStoreSetChunkShortStoredWord_flag_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have hvalid' :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    rw [hheader]
    simp only [storedWord, bytesStoreSetMappedShortStoredWord]
    rw [
      bytesStoreSetChunkShortStoredWord_flag_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort,
      bytesStoreSetChunkShortStoredWord_shortLen_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort]
    have hlt : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    rw [hlt]
    native_decide
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨1002⟩)
    (rest := [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedSlotOf key)
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [header] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded :
      UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ = len := by
    rw [hheader]
    simpa [storedWord, bytesStoreSetMappedShortStoredWord] using
      bytesStoreSetChunkShortStoredWord_shortLen_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have h263 := bytesStoreX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := len)
    (slot := bytesStoreSetMappedSlotOf key) (len := len) (payloadStart := payloadStart)
    (key := key)
    (mem := twoWordHashMem key ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedSlotOf key)
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreX_returnWord263OfMemState
    (mem := twoWordHashMem key ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedSlotOf key)
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
    (by
      exact twoWordHashMem_size_96 _ _
        (wordAt0Mem_size_96 _
          (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)))
    (by
      exact twoWordHashMem_read64 _ _
        (wordAt0Mem_size_96 _
          (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
        (bytesStoreWordAt0Mem_read64 _
          (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
          (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)))
    h263

theorem bytesStoreX_setMappedEmptyOldLongReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    let σClear :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σClear (bytesStoreSetMappedSlotOf key) ⟨0⟩
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  dsimp only
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σClear (bytesStoreSetMappedSlotOf key) ⟨0⟩
  have hbody := bytesStoreX_setMappedEmptyOldLongWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hlenZero
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreSetMappedSlotOf key)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := wordAt0Mem (bytesStoreSetMappedSlotOf key)
      (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (by
      exact wordAt0Mem_size_96 _
        (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    (by simpa [σ', σClear] using hbody)
  have hheader : bytesStoreSetMappedHeaderWordOf σ' I key = ⟨0⟩ := by
    simpa [σ'] using bytesStoreSetMappedEmptyHeaderAfterWrite σClear I key
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := (⟨0⟩ : UInt256)) (ret := ⟨1002⟩)
    (rest := [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedSlotOf key)
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [hheader] using hdecoder)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h263 := bytesStoreX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := (⟨0⟩ : UInt256))
    (slot := bytesStoreSetMappedSlotOf key) (len := len) (payloadStart := payloadStart)
    (key := key)
    (mem := twoWordHashMem key ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedSlotOf key)
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
    (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa using hdecoded)
  exact bytesStoreX_returnWord263OfMemState
    (mem := twoWordHashMem key ⟨4⟩
      (wordAt0Mem (bytesStoreSetMappedSlotOf key)
        (twoWordHashMem key ⟨4⟩ solcFreePtrMem)))
    (by
      exact twoWordHashMem_size_96 _ _
        (wordAt0Mem_size_96 _
          (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)))
    (by
      exact twoWordHashMem_read64 _ _
        (wordAt0Mem_size_96 _
          (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
        (bytesStoreWordAt0Mem_read64 _
          (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
          (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64)))
    h263

theorem bytesStoreX_setMappedEmptyOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedSlotOf key) ⟨0⟩
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  dsimp only
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedSlotOf key) ⟨0⟩
  have hbody := bytesStoreX_setMappedEmptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMax hflag hvalid hlenZero
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreSetMappedSlotOf key)
    (len := len) (payloadStart := payloadStart) (key := key)
    (by simpa [σ'] using hbody)
  have hheader : bytesStoreSetMappedHeaderWordOf σ' I key = ⟨0⟩ := by
    simpa [σ'] using bytesStoreSetMappedEmptyHeaderAfterWrite σ I key
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := (⟨0⟩ : UInt256)) (ret := ⟨1002⟩)
    (rest := [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [hheader] using hdecoder)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h263 := bytesStoreX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := (⟨0⟩ : UInt256))
    (slot := bytesStoreSetMappedSlotOf key) (len := len) (payloadStart := payloadStart)
    (key := key)
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa using hdecoded)
  exact bytesStoreX_returnWord263OfMemState
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    (twoWordHashMem_read64 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
      (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
    h263

theorem bytesStoreX_setMappedShortNonemptyOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hacc : σ.find? I.codeOwner = some acc) :
    let storedWord := bytesStoreSetMappedShortStoredWord I len payloadStart
    let σ' : AccountMap :=
      sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedSlotOf key) storedWord
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ') (UInt256.toByteArray len) := by
  dsimp only
  let storedWord := bytesStoreSetMappedShortStoredWord I len payloadStart
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedSlotOf key) storedWord
  let header : UInt256 := bytesStoreSetMappedHeaderWordOf σ' I key
  have hbody := bytesStoreX_setMappedShortNonemptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMax hflag hvalid hnz hshort
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreSetMappedSlotOf key)
    (len := len) (payloadStart := payloadStart) (key := key)
    (by
      simpa [σ', storedWord, bytesStoreSetMappedShortStoredWord] using hbody)
  have hdata : bytesStoreSetMappedHeaderWordOf σ' I key = storedWord := by
    simpa [σ', storedWord, bytesStoreSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some_any σ I.codeOwner acc
        (bytesStoreSetMappedSlotOf key) storedWord hacc
  have hheader : header = storedWord := by
    simpa [header] using hdata
  have hflag' : UInt256.land header ⟨1⟩ = ⟨0⟩ := by
    rw [hheader]
    simpa [storedWord, bytesStoreSetMappedShortStoredWord] using
      bytesStoreSetChunkShortStoredWord_flag_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have hvalid' :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    rw [hheader]
    simp only [storedWord, bytesStoreSetMappedShortStoredWord]
    rw [
      bytesStoreSetChunkShortStoredWord_flag_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort,
      bytesStoreSetChunkShortStoredWord_shortLen_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort]
    have hlt : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    rw [hlt]
    native_decide
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨1002⟩)
    (rest := [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded :
      UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ = len := by
    rw [hheader]
    simpa [storedWord, bytesStoreSetMappedShortStoredWord] using
      bytesStoreSetChunkShortStoredWord_shortLen_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have h263 := bytesStoreX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := len)
    (slot := bytesStoreSetMappedSlotOf key) (len := len) (payloadStart := payloadStart)
    (key := key)
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (twoWordHashMem_size_96 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size))
    (twoWordHashMem_read64 _ _
      (twoWordHashMem_size_96 _ _ solcFreePtrMem_size)
      (twoWordHashMem_read64 _ _ solcFreePtrMem_size solcFreePtrMem_read64))
    h263

theorem bytesStoreX_setMappedShortNonemptyOldShortAbsentReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hmissing : σ.find? I.codeOwner = none) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  let storedWord := bytesStoreSetMappedShortStoredWord I len payloadStart
  let σ' : AccountMap :=
    sstoreAccountMap I.codeOwner σ (bytesStoreSetMappedSlotOf key) storedWord
  have hbody := bytesStoreX_setMappedShortNonemptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMax hflag hvalid hnz hshort
  have hsame : σ' = σ := by
    simpa [σ', storedWord] using
      sstoreAccountMap_absent_same (owner := I.codeOwner) (τ := σ)
        (slot := bytesStoreSetMappedSlotOf key) (val := storedWord) hmissing
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := bytesStoreSetMappedSlotOf key)
    (len := len) (payloadStart := payloadStart) (key := key)
    (by simpa [σ', storedWord, bytesStoreSetMappedShortStoredWord] using hbody)
  have hheader : bytesStoreSetMappedHeaderWordOf σ' I key = ⟨0⟩ := by
    dsimp [bytesStoreSetMappedHeaderWordOf]
    rw [hsame, hmissing]
    rfl
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := (⟨0⟩ : UInt256)) (ret := ⟨1002⟩)
    (rest := [bytesStoreSetMappedSlotOf key, ⟨0⟩, len, payloadStart, key, ⟨263⟩,
      bytesStoreSelWord I])
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [hheader] using hdecoder)
    (by native_decide)
    (by native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h263 := bytesStoreX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ') (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := (⟨0⟩ : UInt256))
    (slot := bytesStoreSetMappedSlotOf key) (len := len) (payloadStart := payloadStart)
    (key := key)
    (mem := twoWordHashMem key ⟨4⟩ (twoWordHashMem key ⟨4⟩ solcFreePtrMem))
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa using hdecoded)
  have hret := bytesStoreX_returnWord263OfMemState
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

theorem bytesStoreX_setMappedLongNoTailOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (haccData :
      (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) payloadStart
        (⟨0⟩ : UInt256) I (len.toNat / 32)).find? I.codeOwner = some acc) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σLoop : AccountMap :=
      bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σLoop slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap := sstoreAccountMap I.codeOwner σLoop slot header
  let loadedHeader : UInt256 := bytesStoreSetMappedHeaderWordOf σData I key
  let writeMem : ByteArray := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hbody := bytesStoreX_setMappedLongNoTailOldShortWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMaxWord hflag hvalid hlong hnoTailMod
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
    (by simpa [σLoop, σData, slot, header, writeMem] using hbody)
  have hdata : bytesStoreSetMappedHeaderWordOf σData I key = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σLoop, slot, header, bytesStoreSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some σLoop I.codeOwner acc
        slot header (by simpa [σLoop, slot] using haccData) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, retMem] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreX_returnWord263OfMemState
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
          (bytesStoreWordAt0Mem_read64 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
            (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [StringStoreLite.clearCurrentHashAw] using h263)

theorem bytesStoreX_setMappedLongTailOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) payloadStart
          (⟨0⟩ : UInt256) I (len.toNat / 32))
        (StringStoreLite.longDataWordsLoopSlot
          (bytesLikeDataBase (bytesStoreSetMappedSlotOf key)) (len.toNat / 32))
        (StringStoreLite.longDataTailMaskedWord
          (bytesStoreCalldataLongDataWord I payloadStart
            (StringStoreLite.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    let slot : UInt256 := bytesStoreSetMappedSlotOf key
    let σLoop : AccountMap :=
      bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)
    let tailSlot : UInt256 :=
      StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
    let tailWord : UInt256 :=
      StringStoreLite.longDataTailMaskedWord
        (bytesStoreCalldataLongDataWord I payloadStart
          (StringStoreLite.longDataWordsLoopStride
            (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
    let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner σTail slot (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σData) (UInt256.toByteArray len) := by
  dsimp only
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    StringStoreLite.longDataTailMaskedWord
      (bytesStoreCalldataLongDataWord I payloadStart
        (StringStoreLite.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap := sstoreAccountMap I.codeOwner σTail slot header
  let loadedHeader : UInt256 := bytesStoreSetMappedHeaderWordOf σData I key
  let writeMem : ByteArray := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hbody := bytesStoreX_setMappedLongTailOldShortWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMaxWord hflag hvalid hlong htailMod
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
    (by simpa [σLoop, tailSlot, tailWord, σTail, σData, slot, header, writeMem]
      using hbody)
  have hdata : bytesStoreSetMappedHeaderWordOf σData I key = header := by
    have hnzHeader : (header == (default : UInt256)) = false := by
      apply beq_false_of_ne
      intro hzero
      have hflagHeader : UInt256.land header ⟨1⟩ = ⟨1⟩ := by
        simpa [header] using
          bytesStoreSetPacketLongHeader_flag_eq_one (len := len) hlenMax
      rw [hzero] at hflagHeader
      have hbad : UInt256.land (default : UInt256) ⟨1⟩ ≠ ⟨1⟩ := by
        native_decide
      exact hbad hflagHeader
    simpa [σData, σTail, σLoop, tailSlot, tailWord, slot, header,
      bytesStoreSetMappedHeaderWordOf] using
      sstoreAccountMap_storage_findD_self_of_find_some σTail I.codeOwner acc
        slot header
        (by simpa [σTail, σLoop, tailSlot, tailWord, slot] using haccTail) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader] using hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, retMem] using hdecoder)
    hflag' hvalid' (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := len) (slot := slot)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreX_returnWord263OfMemState
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
          (bytesStoreWordAt0Mem_read64 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
            (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [StringStoreLite.clearCurrentHashAw] using h263)

theorem bytesStoreX_setMappedLongNoTailOldShortAbsentReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (hmissing : σ.find? I.codeOwner = none) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData : AccountMap := sstoreAccountMap I.codeOwner σLoop slot header
  let writeMem : ByteArray := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hbody := bytesStoreX_setMappedLongNoTailOldShortWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMaxWord hflag hvalid hlong hnoTailMod
  have hloopSame : σLoop = σ := by
    simpa [σLoop, slot] using
      bytesStoreCalldataLongDataForwardFrom_absent_same
        (σ := σ) (owner := I.codeOwner) (slot := bytesLikeDataBase slot)
        (payloadStart := payloadStart) (stride := (⟨0⟩ : UInt256)) (I := I)
        hmissing (len.toNat / 32)
  have hdataSame : σData = σ := by
    dsimp [σData]
    rw [hloopSame]
    exact sstoreAccountMap_absent_same (owner := I.codeOwner) (τ := σ)
      (slot := slot) (val := header) hmissing
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
    (by simpa [σLoop, σData, slot, header, writeMem] using hbody)
  have hloaded : bytesStoreSetMappedHeaderWordOf σData I key = ⟨0⟩ := by
    dsimp [bytesStoreSetMappedHeaderWordOf]
    rw [hdataSame, hmissing]
    rfl
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetMappedHeaderWordOf σData I key) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [retMem] using hdecoder)
    (by rw [hloaded]; native_decide)
    (by rw [hloaded]; native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h263 := bytesStoreX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := (⟨0⟩ : UInt256)) (slot := slot)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hloaded] using hdecoded)
  have hret := bytesStoreX_returnWord263OfMemState
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
          (bytesStoreWordAt0Mem_read64 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
            (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [StringStoreLite.clearCurrentHashAw] using h263)
  simpa [hdataSame] using hret

theorem bytesStoreX_setMappedLongTailOldShortAbsentReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {len payloadStart key : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWordOf σ I key) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWordOf σ I key) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (hmissing : σ.find? I.codeOwner = none) :
    RDret bytesStoreBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
  let slot : UInt256 := bytesStoreSetMappedSlotOf key
  let header : UInt256 := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop : AccountMap :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase slot) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot : UInt256 :=
    StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase slot) (len.toNat / 32)
  let tailWord : UInt256 :=
    StringStoreLite.longDataTailMaskedWord
      (bytesStoreCalldataLongDataWord I payloadStart
        (StringStoreLite.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail : AccountMap := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData : AccountMap := sstoreAccountMap I.codeOwner σTail slot header
  let writeMem : ByteArray := wordAt0Mem slot (twoWordHashMem key ⟨4⟩ solcFreePtrMem)
  let retMem : ByteArray := twoWordHashMem key ⟨4⟩ writeMem
  have hbody := bytesStoreX_setMappedLongTailOldShortWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (len := len) (payloadStart := payloadStart) (key := key)
    hperm hreach hlenMaxWord hflag hvalid hlong htailMod
  have hloopSame : σLoop = σ := by
    simpa [σLoop, slot] using
      bytesStoreCalldataLongDataForwardFrom_absent_same
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
  have hdecoder := bytesStoreX_setMappedReachReturnLengthDecoderFromMem
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := slot) (len := len)
    (payloadStart := payloadStart) (key := key) (mem := writeMem)
    (by
      simpa [writeMem] using
        wordAt0Mem_size_96 slot (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size))
    (by simpa [σLoop, tailSlot, tailWord, σTail, σData, slot, header, writeMem]
      using hbody)
  have hloaded : bytesStoreSetMappedHeaderWordOf σData I key = ⟨0⟩ := by
    dsimp [bytesStoreSetMappedHeaderWordOf]
    rw [hdataSame, hmissing]
    rfl
  have hdecoded := bytesStoreX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
    (header := bytesStoreSetMappedHeaderWordOf σData I key) (ret := ⟨1002⟩)
    (rest := [slot, ⟨0⟩, len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I])
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [retMem] using hdecoder)
    (by rw [hloaded]; native_decide)
    (by rw [hloaded]; native_decide)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have h263 := bytesStoreX_setMappedReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (mappedLen := (⟨0⟩ : UInt256)) (slot := slot)
    (len := len) (payloadStart := payloadStart) (key := key)
    (mem := retMem) (aw := StringStoreLite.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hloaded] using hdecoded)
  have hret := bytesStoreX_returnWord263OfMemState
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
          (bytesStoreWordAt0Mem_read64 slot
            (twoWordHashMem_size_96 key ⟨4⟩ solcFreePtrMem_size)
            (twoWordHashMem_read64 key ⟨4⟩ solcFreePtrMem_size solcFreePtrMem_read64)))
    (by simpa [StringStoreLite.clearCurrentHashAw] using h263)
  simpa [hdataSame] using hret

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedLongOldShortAbsentRuntimeOfReturn
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len key : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmissingEvm : σ_evm.find? I.codeOwner = none)
    (hkey : key = bytesStoreSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlong : ¬ len.toNat < 32)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σ_evm) (UInt256.toByteArray (⟨0⟩ : UInt256))) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetMappedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hmissingSolm : σ_solm.find? I.codeOwner = none :=
    accountMapEquiv_find?_none hAccounts hmissingEvm
  have hmissingSolm0 :
      evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner = none := by
    simpa [evmSolm0, initState] using hmissingSolm
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evmSolm0 := by
    simpa [evmSolm0, value, bytesStoreSetMappedRef, hkey] using
      bytesStoreSetMappedWriteLongOldShortPackedAbsent
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        hAccounts hlenAbi hpayloadList hlong hflag hvalid hmissingSolm0
  have hlenMapped :
      readStorageBytesLength? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) = .ok 0 := by
    have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedSlotOf key) = (⟨0⟩ : UInt256) := by
      simp [Solm.EVM.storageLoad, State.lookupAccount, hmissingSolm0, Option.option]
    exact bytesStoreReadLengthZeroOfHeaderLoad
      (er := bytesStoreSetMappedRefOf key) (evm := evmSolm0)
      (baseSlot := bytesStoreSetMappedSlotOf key)
      (bytesStoreSetMappedRefOf_length_slot evmSolm0 key) hload
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreSetMappedFrameOf key value) evmSolm0
          (some (.int 0))) := by
    have hlocals :
        bytesStoreSetMappedLocals I = bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyReturnsOfWrite
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
theorem bytesStoreSetMappedLongNoTailOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedLocals I))
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetMappedValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (bytesStoreSetMappedSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let σFinal := sstoreAccountMap I.codeOwner σLoop
    (bytesStoreSetMappedSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreSetMappedSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreSetMappedSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact StringStoreLite.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (bytesStoreSetMappedSlot I))
      (payloadStart := payloadStart) (stride := (⟨0⟩ : UInt256)) (I := I)
      haccEvm (len.toNat / 32)
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σLoop, bytesStoreSetMappedSlot, hkey,
      bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf] using
      bytesStoreX_setMappedLongNoTailOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key) (acc := accLoop)
        hperm hreach hlenMaxWord hlenMax
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
        hlong hnoTailMod
        (by simpa [σLoop, bytesStoreSetMappedSlot, hkey] using haccLoop)
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreSetMappedWriteLongOldShortPacked
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts hlenAbi hpayloadList hlong hflag hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header,
      bytesStoreSetMappedRef, hkey] using hwrite₀
  have hdataFuelEq : dataFuel = len.toNat / 32 := by
    dsimp [dataFuel]
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_eq_div_of_mod_zero hnoTailMod
  have hAccountsLoop : accountMapEquiv σLoop evmLoop.accountMap := by
    have hbridge :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (bytesStoreSetMappedSlot I)
            value 0 (len.toNat / 32))
          σLoop := by
      simpa [σLoop, value, bytesStoreSetMappedSlot] using
        accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          (baseSlot := bytesStoreSetMappedSlot I) hsrc haddrBound hsizeDecoded hlenAbi
          hpayloadStart hoffMax (τ := σ_evm) (fuel := len.toNat / 32) (by rfl)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (bytesStoreSetMappedSlot I)
            value 0 (len.toNat / 32))
          (solidityDataWordsForwardFrom I.codeOwner σ_solm (bytesStoreSetMappedSlot I)
            value 0 (len.toNat / 32)) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
        (baseSlot := bytesStoreSetMappedSlot I) (bytes := value)
        (idx := 0) (len.toNat / 32) hAccounts
    simpa [evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_accountMap, initState,
      hdataFuelEq] using accountMapEquiv.trans (accountMapEquiv.symm hbridge) hcong
  obtain ⟨accSolmLoop, haccSolmLoop⟩ :=
    accountMapEquiv_find?_some_exists hAccountsLoop haccLoop
  have hlenMapped :
      readStorageBytesLength? bytesStoreConfig evmData
        (bytesStoreSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreSetMappedLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmLoop)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmLoop
      (by
        rw [hheaderEq]
        exact bytesStoreSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState,
      bytesStoreSetMappedRef, hkey] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    have hAccountsData :
        accountMapEquiv
          (sstoreAccountMap I.codeOwner σLoop (bytesStoreSetMappedSlot I)
            (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          evmData.accountMap := by
      simpa [evmData, evmLoop, hheaderEq,
        writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using
        accountMapEquiv_setMappedHeaderStore I evmLoop.executionEnv.codeOwner header
          hAccountsLoop
    simpa [σFinal] using hAccountsData
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreSetMappedLocals I = bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyReturnsOfWrite
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
theorem bytesStoreSetMappedLongNoTailOldLongNoClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedLocals I))
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetMappedValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (bytesStoreSetMappedSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let σFinal := sstoreAccountMap I.codeOwner σLoop
    (bytesStoreSetMappedSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreSetMappedSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreSetMappedSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact StringStoreLite.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (bytesStoreSetMappedSlot I))
      (payloadStart := payloadStart) (stride := (⟨0⟩ : UInt256)) (I := I)
      haccEvm (len.toNat / 32)
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σLoop, bytesStoreSetMappedSlot, hkey,
      bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf] using
      bytesStoreX_setMappedLongNoTailOldLongNoClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen) (acc := accLoop)
        hperm hreach hlenMaxWord hlenMax
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using holdStoredLen)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
        hgtOldNew hlong hnoTailMod
        (by simpa [σLoop, bytesStoreSetMappedSlot, hkey] using haccLoop)
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
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreSetMappedWriteLongOldLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      (oldStoredLen := oldStoredLen)
      hAccounts hlenAbi hpayloadList hlong hflag holdStoredLen hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header, hclearCountZero,
      hclearCountZeroLen, clearSolidityBytesDataWordsFrom, hdataFuelEq,
      bytesStoreSetMappedRef, hkey] using hwrite₀
  have hAccountsLoop : accountMapEquiv σLoop evmLoop.accountMap := by
    have hbridge :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (bytesStoreSetMappedSlot I)
            value 0 (len.toNat / 32))
          σLoop := by
      simpa [σLoop, value, bytesStoreSetMappedSlot] using
        accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          (baseSlot := bytesStoreSetMappedSlot I) hsrc haddrBound hsizeDecoded hlenAbi
          hpayloadStart hoffMax (τ := σ_evm) (fuel := len.toNat / 32) (by rfl)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (bytesStoreSetMappedSlot I)
            value 0 (len.toNat / 32))
          (solidityDataWordsForwardFrom I.codeOwner σ_solm (bytesStoreSetMappedSlot I)
            value 0 (len.toNat / 32)) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
        (baseSlot := bytesStoreSetMappedSlot I) (bytes := value)
        (idx := 0) (len.toNat / 32) hAccounts
    simpa [evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_accountMap, initState,
      hdataFuelEq] using accountMapEquiv.trans (accountMapEquiv.symm hbridge) hcong
  obtain ⟨accSolmLoop, haccSolmLoop⟩ :=
    accountMapEquiv_find?_some_exists hAccountsLoop haccLoop
  have hlenMapped :
      readStorageBytesLength? bytesStoreConfig evmData
        (bytesStoreSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreSetMappedLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmLoop)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmLoop
      (by
        rw [hheaderEq]
        exact bytesStoreSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState,
      bytesStoreSetMappedRef, hkey] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    have hAccountsData :
        accountMapEquiv
          (sstoreAccountMap I.codeOwner σLoop (bytesStoreSetMappedSlot I)
            (len * (⟨2⟩ : UInt256) + ⟨1⟩))
          evmData.accountMap := by
      simpa [evmData, evmLoop, hheaderEq,
        writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using
        accountMapEquiv_setMappedHeaderStore I evmLoop.executionEnv.codeOwner header
          hAccountsLoop
    simpa [σFinal] using hAccountsData
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreSetMappedLocals I = bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyReturnsOfWrite
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
theorem bytesStoreSetMappedLongNoTailOldLongClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedLocals I))
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetMappedValueBytes I
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
        bytesLikeDataBase (bytesStoreSetMappedSlot I)) ⟨0⟩ clearCount.toNat
  let σLoop :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase (bytesStoreSetMappedSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let σFinal := sstoreAccountMap I.codeOwner σLoop
    (bytesStoreSetMappedSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreSetMappedSlot I) clearFuel tailFuel
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmClear (bytesStoreSetMappedSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreSetMappedSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact StringStoreLite.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  have holdGtNat : len.toNat < oldStoredLen.toNat :=
    StringStoreLite.ugt_eq_one_toNat_lt hgtOldNew
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
    StringStoreLite.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreSetMappedHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hnewShiftClear :
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩).toNat = clearFuel := by
    rw [hclearFuelCeil]
    exact bytesStore_shiftRight_add31_five_toNat_of_u64 (x := len) hlenMax
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
    exact bytesStore_shiftRight_add31_five_toNat_of_lt_sign (x := oldStoredLen) holdLenLt
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
        bytesLikeDataBase (bytesStoreSetMappedSlot I))
      (idx := (⟨0⟩ : UInt256)) haccEvm clearCount.toNat
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σClear) (owner := I.codeOwner) (acc := accClear)
      (slot := bytesLikeDataBase (bytesStoreSetMappedSlot I)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I)
      (by simpa [σClear, clearCount] using haccClear) (len.toNat / 32)
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σLoop, σClear, clearCount, bytesStoreSetMappedSlot, hkey,
      bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf] using
      bytesStoreX_setMappedLongNoTailOldLongClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen) (acc := accLoop)
        hperm hreach hlenMaxWord hlenMax
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using holdStoredLen)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
        hgtOldNew hlong hnoTailMod
        (by simpa [σLoop, σClear, clearCount, bytesStoreSetMappedSlot, hkey]
          using haccLoop)
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreSetMappedWriteLongOldLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      (oldStoredLen := oldStoredLen)
      hAccounts hlenAbi hpayloadList hlong hflag holdStoredLen hvalid
    simpa [evmSolm0, evmClear, evmLoop, evmData, value, dataFuel, header,
      oldFuel, clearFuel, tailFuel, solidityBytesDataWordCount,
      bytesStoreSetMappedRef, hkey] using hwrite₀
  have hAccountsClear : accountMapEquiv σClear evmClear.accountMap := by
    have hshift := accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
      (owner := I.codeOwner) (σ := σ_evm) (τ := σ_solm)
      (baseSlot := bytesStoreSetMappedSlot I) clearFuel (⟨0⟩ : UInt256) tailFuel
      hAccounts
    dsimp [σClear, evmClear, evmSolm0, clearCount]
    rw [hnewShiftEq, hcountNatShift]
    have hidxZero :
        UInt256.ofNat clearFuel + (⟨0⟩ : UInt256) = UInt256.ofNat clearFuel := by
      simpa using StringStoreLite.uint256_add_zero_right (UInt256.ofNat clearFuel)
    simpa [clearSolidityBytesDataWordsFrom_accountMap, initState, hidxZero,
      u256_add_comm (UInt256.ofNat clearFuel)
        (bytesLikeDataBase (bytesStoreSetMappedSlot I))]
      using hshift
  have hAccountsLoop : accountMapEquiv σLoop evmLoop.accountMap := by
    have hbridge :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σClear (bytesStoreSetMappedSlot I)
            value 0 (len.toNat / 32))
          σLoop := by
      simpa [σLoop, value, bytesStoreSetMappedSlot] using
        accountMapEquiv_setChunkDataWordsFrom_calldataLongDataForwardFrom_full_zero
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          (baseSlot := bytesStoreSetMappedSlot I) hsrc haddrBound hsizeDecoded hlenAbi
          hpayloadStart hoffMax (τ := σClear) (fuel := len.toNat / 32) (by rfl)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σClear (bytesStoreSetMappedSlot I)
            value 0 (len.toNat / 32))
          (solidityDataWordsForwardFrom I.codeOwner evmClear.accountMap
            (bytesStoreSetMappedSlot I) value 0 (len.toNat / 32)) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σClear) (σ := evmClear.accountMap)
        (baseSlot := bytesStoreSetMappedSlot I) (bytes := value)
        (idx := 0) (len.toNat / 32) hAccountsClear
    simpa [evmLoop, evmClear, evmSolm0, writeSolidityBytesDataWordsFrom_accountMap,
      clearSolidityBytesDataWordsFrom_executionEnv, initState, hdataFuelEq] using
      accountMapEquiv.trans (accountMapEquiv.symm hbridge) hcong
  obtain ⟨accSolmLoop, haccSolmLoop⟩ :=
    accountMapEquiv_find?_some_exists hAccountsLoop haccLoop
  have hlenMapped :
      readStorageBytesLength? bytesStoreConfig evmData
        (bytesStoreSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreSetMappedLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmLoop)
      (by simp [evmLoop, evmClear, evmSolm0, initState,
        writeSolidityBytesDataWordsFrom_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv])
      haccSolmLoop
      (by
        rw [hheaderEq]
        exact bytesStoreSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState,
      bytesStoreSetMappedRef, hkey] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState, header] using
      accountMapEquiv_setMappedHeaderStore I evmLoop.executionEnv.codeOwner header
        hAccountsLoop
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreSetMappedLocals I = bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyReturnsOfWrite
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
theorem bytesStoreSetMappedLongTailOldLongClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedLocals I))
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetMappedValueBytes I
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
        bytesLikeDataBase (bytesStoreSetMappedSlot I)) ⟨0⟩ clearCount.toNat
  let σLoop :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase (bytesStoreSetMappedSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let tailSlot :=
    StringStoreLite.longDataWordsLoopSlot
      (bytesLikeDataBase (bytesStoreSetMappedSlot I)) (len.toNat / 32)
  let tailWord :=
    StringStoreLite.longDataTailMaskedWord
      (bytesStoreCalldataLongDataWord I payloadStart
        (StringStoreLite.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
        0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σFinal := sstoreAccountMap I.codeOwner σTail
    (bytesStoreSetMappedSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreSetMappedSlot I) clearFuel tailFuel
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmClear (bytesStoreSetMappedSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreSetMappedSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact StringStoreLite.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  have holdGtNat : len.toNat < oldStoredLen.toNat :=
    StringStoreLite.ugt_eq_one_toNat_lt hgtOldNew
  have hclearFuelCeil : clearFuel = (len.toNat + 31) / 32 := by
    dsimp [clearFuel]
    rw [hsizeDecoded]
  have hdataFuelEq : dataFuel = len.toNat / 32 + 1 := by
    dsimp [dataFuel]
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_eq_div_succ_of_mod_ne htailMod
  have hdataCountEq :
      solidityBytesDataWordCount (bytesStoreSetMappedValueBytes I).size =
        len.toNat / 32 + 1 := by
    simpa [dataFuel, value] using hdataFuelEq
  have hclearLeOld : clearFuel ≤ oldFuel := by
    dsimp [oldFuel]
    rw [hclearFuelCeil]
    exact solidityBytesDataWordCount_mono (Nat.le_of_lt holdGtNat)
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 :=
    StringStoreLite.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreSetMappedHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hnewShiftClear :
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩).toNat = clearFuel := by
    rw [hclearFuelCeil]
    exact bytesStore_shiftRight_add31_five_toNat_of_u64 (x := len) hlenMax
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
    exact bytesStore_shiftRight_add31_five_toNat_of_lt_sign (x := oldStoredLen) holdLenLt
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
        bytesLikeDataBase (bytesStoreSetMappedSlot I))
      (idx := (⟨0⟩ : UInt256)) haccEvm clearCount.toNat
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σClear) (owner := I.codeOwner) (acc := accClear)
      (slot := bytesLikeDataBase (bytesStoreSetMappedSlot I)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I)
      (by simpa [σClear, clearCount] using haccClear) (len.toNat / 32)
  obtain ⟨accTail, haccTail⟩ :=
    sstoreAccountMap_find?_some_exists_of_find_some
      (σ := σLoop) (a := I.codeOwner) (acc := accLoop)
      (slot := tailSlot) (val := tailWord)
      (by simpa [σLoop, σClear, clearCount] using haccLoop)
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σTail, σLoop, σClear, clearCount, tailSlot, tailWord,
      bytesStoreSetMappedSlot, hkey,
      bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf] using
      bytesStoreX_setMappedLongTailOldLongClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen) (acc := accTail)
        hperm hreach hlenMaxWord hlenMax
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using holdStoredLen)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
        hgtOldNew hlong htailMod
        (by simpa [σTail, σLoop, σClear, clearCount, tailSlot, tailWord,
          bytesStoreSetMappedSlot, hkey] using haccTail)
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreSetMappedWriteLongOldLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      (oldStoredLen := oldStoredLen)
      hAccounts hlenAbi hpayloadList hlong hflag holdStoredLen hvalid
    simpa [evmSolm0, evmClear, evmLoop, evmData, value, dataFuel, header,
      oldFuel, clearFuel, tailFuel, solidityBytesDataWordCount,
      bytesStoreSetMappedRef, hkey] using hwrite₀
  have hAccountsClear : accountMapEquiv σClear evmClear.accountMap := by
    have hshift := accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
      (owner := I.codeOwner) (σ := σ_evm) (τ := σ_solm)
      (baseSlot := bytesStoreSetMappedSlot I) clearFuel (⟨0⟩ : UInt256) tailFuel
      hAccounts
    dsimp [σClear, evmClear, evmSolm0, clearCount]
    rw [hnewShiftEq, hcountNatShift]
    have hidxZero :
        UInt256.ofNat clearFuel + (⟨0⟩ : UInt256) = UInt256.ofNat clearFuel := by
      simpa using StringStoreLite.uint256_add_zero_right (UInt256.ofNat clearFuel)
    simpa [clearSolidityBytesDataWordsFrom_accountMap, initState, hidxZero,
      u256_add_comm (UInt256.ofNat clearFuel)
        (bytesLikeDataBase (bytesStoreSetMappedSlot I))]
      using hshift
  have hAccountsTail : accountMapEquiv σTail evmLoop.accountMap := by
    let baseSlot : UInt256 := bytesStoreSetMappedSlot I
    let fullFuel : Nat := len.toNat / 32
    have hbridgeEvm :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σClear baseSlot value 0 fullFuel)
          (bytesStoreCalldataLongDataForwardFrom I.codeOwner σClear
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
          (bytesStoreCalldataLongDataForwardFrom I.codeOwner σClear
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
          (solidityDataWordsForwardFrom I.codeOwner evmClear.accountMap baseSlot value 0
            fullFuel) :=
      accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
    have htailWord :
        StringStoreLite.longDataTailMaskedWord
            (bytesStoreCalldataLongDataWord I payloadStart
              (UInt256.ofNat (32 * fullFuel)) 0) len =
          uInt256OfByteArray (value.readWithPadding (fullFuel * 32) 32) := by
      simpa [value, bytesStoreSetMappedValueBytes, fullFuel, Nat.mul_comm] using
        bytesStoreSetChunkCalldataLongDataTailMaskedWord_eq_decoded_tail
          (I := I) (len := len) (payloadStart := payloadStart)
          htailAddr hsrc hsizeDecoded hlenAbi hpayloadStart hoffMax hlong htailMod
    have hslotEq :
        StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel =
          solidityBytesDataSlot baseSlot fullFuel := by
      exact bytesStoreLongDataWordsLoopSlot_bytesLikeDataBase baseSlot fullFuel
    have htailStore :=
      accountMapEquiv_sstore_solidityDataWordsForwardFrom_succ_last
        (owner := I.codeOwner) (σ := bytesStoreCalldataLongDataForwardFrom I.codeOwner
          σClear (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
        (τ := evmClear.accountMap) (baseSlot := baseSlot)
        (slot := StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
        (word := StringStoreLite.longDataTailMaskedWord
          (bytesStoreCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len)
        (bytes := value) (idx := 0) (fuel := fullFuel)
        hdataFull (by simpa using hslotEq) (by simpa using htailWord)
    simpa [σTail, σLoop, σClear, clearCount, tailSlot, tailWord, evmLoop, evmClear,
      evmSolm0, initState, value, baseSlot, fullFuel, hdataFuelEq,
      writeSolidityBytesDataWordsFrom_accountMap,
      clearSolidityBytesDataWordsFrom_executionEnv,
      bytesStoreLongDataWordsLoopStride_zero_ofNat] using htailStore
  obtain ⟨accSolmTail, haccSolmTail⟩ :=
    accountMapEquiv_find?_some_exists hAccountsTail haccTail
  have hlenMapped :
      readStorageBytesLength? bytesStoreConfig evmData
        (bytesStoreSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreSetMappedLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmTail)
      (by simp [evmLoop, evmClear, evmSolm0, initState,
        writeSolidityBytesDataWordsFrom_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv])
      haccSolmTail
      (by
        rw [hheaderEq]
        exact bytesStoreSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState,
      bytesStoreSetMappedRef, hkey] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState, header] using
      accountMapEquiv_setMappedHeaderStore I evmLoop.executionEnv.codeOwner header
        hAccountsTail
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreSetMappedLocals I = bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyReturnsOfWrite
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
theorem bytesStoreSetMappedLongTailOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedLocals I))
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetMappedValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (bytesStoreSetMappedSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let tailSlot :=
    StringStoreLite.longDataWordsLoopSlot
      (bytesLikeDataBase (bytesStoreSetMappedSlot I)) (len.toNat / 32)
  let tailWord :=
    StringStoreLite.longDataTailMaskedWord
      (bytesStoreCalldataLongDataWord I payloadStart
        (StringStoreLite.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
        0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σFinal := sstoreAccountMap I.codeOwner σTail
    (bytesStoreSetMappedSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreSetMappedSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreSetMappedSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact StringStoreLite.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (bytesStoreSetMappedSlot I))
      (payloadStart := payloadStart) (stride := (⟨0⟩ : UInt256)) (I := I)
      haccEvm (len.toNat / 32)
  obtain ⟨accTail, haccTail⟩ :=
    sstoreAccountMap_find?_some_exists_of_find_some
      (σ := σLoop) (a := I.codeOwner) (acc := accLoop)
      (slot := tailSlot) (val := tailWord) (by simpa [σLoop] using haccLoop)
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σTail, σLoop, tailSlot, tailWord, bytesStoreSetMappedSlot, hkey,
      bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf] using
      bytesStoreX_setMappedLongTailOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key) (acc := accTail)
        hperm hreach hlenMaxWord hlenMax
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
        hlong htailMod
        (by simpa [σTail, σLoop, tailSlot, tailWord, bytesStoreSetMappedSlot, hkey]
          using haccTail)
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreSetMappedWriteLongOldShortPacked
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts hlenAbi hpayloadList hlong hflag hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header,
      bytesStoreSetMappedRef, hkey] using hwrite₀
  have hdataFuelEq : dataFuel = len.toNat / 32 + 1 := by
    dsimp [dataFuel]
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_eq_div_succ_of_mod_ne htailMod
  have hAccountsTail : accountMapEquiv σTail evmLoop.accountMap := by
    let baseSlot : UInt256 := bytesStoreSetMappedSlot I
    let fullFuel : Nat := len.toNat / 32
    have hbridgeEvm :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm baseSlot value 0 fullFuel)
          (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ_evm
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
          (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ_evm
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
          (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot value 0 fullFuel) :=
      accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
    have htailWord :
        StringStoreLite.longDataTailMaskedWord
            (bytesStoreCalldataLongDataWord I payloadStart
              (UInt256.ofNat (32 * fullFuel)) 0) len =
          uInt256OfByteArray (value.readWithPadding (fullFuel * 32) 32) := by
      simpa [value, bytesStoreSetMappedValueBytes, fullFuel, Nat.mul_comm] using
        bytesStoreSetChunkCalldataLongDataTailMaskedWord_eq_decoded_tail
          (I := I) (len := len) (payloadStart := payloadStart)
          htailAddr hsrc hsizeDecoded hlenAbi hpayloadStart hoffMax hlong htailMod
    have hslotEq :
        StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel =
          solidityBytesDataSlot baseSlot fullFuel := by
      exact bytesStoreLongDataWordsLoopSlot_bytesLikeDataBase baseSlot fullFuel
    have htailStore :=
      accountMapEquiv_sstore_solidityDataWordsForwardFrom_succ_last
        (owner := I.codeOwner) (σ := bytesStoreCalldataLongDataForwardFrom I.codeOwner
          σ_evm (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
        (τ := σ_solm) (baseSlot := baseSlot)
        (slot := StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
        (word := StringStoreLite.longDataTailMaskedWord
          (bytesStoreCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len)
        (bytes := value) (idx := 0) (fuel := fullFuel)
        hdataFull (by simpa using hslotEq) (by simpa using htailWord)
    simpa [σTail, σLoop, tailSlot, tailWord, evmLoop, evmSolm0, initState, value,
      baseSlot, fullFuel, hdataFuelEq, writeSolidityBytesDataWordsFrom_accountMap,
      bytesStoreLongDataWordsLoopStride_zero_ofNat] using htailStore
  obtain ⟨accSolmTail, haccSolmTail⟩ :=
    accountMapEquiv_find?_some_exists hAccountsTail haccTail
  have hlenMapped :
      readStorageBytesLength? bytesStoreConfig evmData
        (bytesStoreSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreSetMappedLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmTail)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmTail
      (by
        rw [hheaderEq]
        exact bytesStoreSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState,
      bytesStoreSetMappedRef, hkey] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState, header] using
      accountMapEquiv_setMappedHeaderStore I evmLoop.executionEnv.codeOwner header
        hAccountsTail
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreSetMappedLocals I = bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyReturnsOfWrite
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
theorem bytesStoreSetMappedLongTailOldLongNoClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedLocals I))
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetMappedValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (bytesStoreSetMappedSlot I)) payloadStart
      (⟨0⟩ : UInt256) I (len.toNat / 32)
  let tailSlot :=
    StringStoreLite.longDataWordsLoopSlot
      (bytesLikeDataBase (bytesStoreSetMappedSlot I)) (len.toNat / 32)
  let tailWord :=
    StringStoreLite.longDataTailMaskedWord
      (bytesStoreCalldataLongDataWord I payloadStart
        (StringStoreLite.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
        0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σFinal := sstoreAccountMap I.codeOwner σTail
    (bytesStoreSetMappedSlot I) (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop :=
    writeSolidityBytesDataWordsFrom evmSolm0 (bytesStoreSetMappedSlot I) value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner
    (bytesStoreSetMappedSlot I) header
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact StringStoreLite.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (bytesStoreSetMappedSlot I))
      (payloadStart := payloadStart) (stride := (⟨0⟩ : UInt256)) (I := I)
      haccEvm (len.toNat / 32)
  obtain ⟨accTail, haccTail⟩ :=
    sstoreAccountMap_find?_some_exists_of_find_some
      (σ := σLoop) (a := I.codeOwner) (acc := accLoop)
      (slot := tailSlot) (val := tailWord) (by simpa [σLoop] using haccLoop)
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σTail, σLoop, tailSlot, tailWord, bytesStoreSetMappedSlot, hkey,
      bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf] using
      bytesStoreX_setMappedLongTailOldLongNoClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen) (acc := accTail)
        hperm hreach hlenMaxWord hlenMax
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using holdStoredLen)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
        hgtOldNew hlong htailMod
        (by simpa [σTail, σLoop, tailSlot, tailWord, bytesStoreSetMappedSlot, hkey]
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
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hwrite₀ := bytesStoreSetMappedWriteLongOldLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      (oldStoredLen := oldStoredLen)
      hAccounts hlenAbi hpayloadList hlong hflag holdStoredLen hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header, hclearCountZero,
      hclearCountZeroLen, clearSolidityBytesDataWordsFrom, hdataFuelEq,
      bytesStoreSetMappedRef, hkey] using hwrite₀
  have hAccountsTail : accountMapEquiv σTail evmLoop.accountMap := by
    let baseSlot : UInt256 := bytesStoreSetMappedSlot I
    let fullFuel : Nat := len.toNat / 32
    have hbridgeEvm :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm baseSlot value 0 fullFuel)
          (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ_evm
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
          (bytesStoreCalldataLongDataForwardFrom I.codeOwner σ_evm
            (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
          (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot value 0 fullFuel) :=
      accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
    have htailWord :
        StringStoreLite.longDataTailMaskedWord
            (bytesStoreCalldataLongDataWord I payloadStart
              (UInt256.ofNat (32 * fullFuel)) 0) len =
          uInt256OfByteArray (value.readWithPadding (fullFuel * 32) 32) := by
      simpa [value, bytesStoreSetMappedValueBytes, fullFuel, Nat.mul_comm] using
        bytesStoreSetChunkCalldataLongDataTailMaskedWord_eq_decoded_tail
          (I := I) (len := len) (payloadStart := payloadStart)
          htailAddr hsrc hsizeDecoded hlenAbi hpayloadStart hoffMax hlong htailMod
    have hslotEq :
        StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel =
          solidityBytesDataSlot baseSlot fullFuel := by
      exact bytesStoreLongDataWordsLoopSlot_bytesLikeDataBase baseSlot fullFuel
    have htailStore :=
      accountMapEquiv_sstore_solidityDataWordsForwardFrom_succ_last
        (owner := I.codeOwner) (σ := bytesStoreCalldataLongDataForwardFrom I.codeOwner
          σ_evm (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
        (τ := σ_solm) (baseSlot := baseSlot)
        (slot := StringStoreLite.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
        (word := StringStoreLite.longDataTailMaskedWord
          (bytesStoreCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len)
        (bytes := value) (idx := 0) (fuel := fullFuel)
        hdataFull (by simpa using hslotEq) (by simpa using htailWord)
    simpa [σTail, σLoop, tailSlot, tailWord, evmLoop, evmSolm0, initState, value,
      baseSlot, fullFuel, hdataFuelEq, writeSolidityBytesDataWordsFrom_accountMap,
      bytesStoreLongDataWordsLoopStride_zero_ofNat] using htailStore
  obtain ⟨accSolmTail, haccSolmTail⟩ :=
    accountMapEquiv_find?_some_exists hAccountsTail haccTail
  have hlenMapped :
      readStorageBytesLength? bytesStoreConfig evmData
        (bytesStoreSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreSetMappedLengthAfterLongStoreOfState
      (evm := evmLoop) (I := I) (len := len) (header := header)
      (acc := accSolmTail)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmTail
      (by
        rw [hheaderEq]
        exact bytesStoreSetPacketLongHeader_flag_ne_zero (len := len) hlenMax)
      (by
        rw [hheaderEq]
        symm
        exact bytesStoreSetPacketLongHeader_div_two (len := len) hlenMax)
      (by
        rw [hheaderEq]
        exact bytesStoreSetPacketLongHeader_valid (len := len) hlenMax hlong)
    simpa [evmLoop, evmData, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState,
      bytesStoreSetMappedRef, hkey] using hlen₀
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState, header] using
      accountMapEquiv_setMappedHeaderStore I evmLoop.executionEnv.codeOwner header
        hAccountsTail
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreSetMappedLocals I = bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyReturnsOfWrite
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
theorem bytesStoreSetMappedShortNonemptyOldLongRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedLocals I))
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetMappedValueBytes I
  let storedWord := bytesStoreSetMappedShortStoredWord I len payloadStart
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreSetMappedSlot I)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σFinal := sstoreAccountMap I.codeOwner σClear
    (bytesStoreSetMappedSlot I) storedWord
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreSetMappedSlot I) 0 ((oldStoredLen.toNat + 31) / 32)
  let evmData := Solm.EVM.storageStore evmClear I.codeOwner
    (bytesStoreSetMappedSlot I) (solidityShortBytesWord value)
  obtain ⟨accClear, haccClear⟩ :=
    clearDataWordsForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (base := ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreSetMappedSlot I)))
      (idx := ⟨0⟩) haccEvm
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σClear, storedWord, bytesStoreSetMappedSlot, hkey,
      bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf] using
      bytesStoreX_setMappedShortNonemptyOldLongReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen) (acc := accClear)
        hperm hreach hlenMax
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using holdStoredLen)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
        hnz hshort
        (by simpa [σClear, bytesStoreSetMappedSlot, hkey] using haccClear)
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    simpa [evmSolm0, evmClear, evmData, value, bytesStoreSetMappedRef, hkey] using
      bytesStoreSetMappedWriteShortOldLongPrepared
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        (oldStoredLen := oldStoredLen)
        hAccounts hpayloadList hlenAbi hshort hflag holdStoredLen hvalid
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value, bytesStoreSetMappedShortStoredWord,
      bytesStoreSetMappedValueBytes] using
      bytesStoreSetChunkShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayloadList
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  obtain ⟨accSolmClear, haccSolmClear⟩ :=
    clearDataWordsForwardFrom_find?_some_exists_of_find_some
      (σ := σ_solm) (owner := I.codeOwner) (acc := accSolm)
      (base := solidityBytesDataBaseSlot (bytesStoreSetMappedSlot I))
      (idx := UInt256.ofNat 0) haccSolm ((oldStoredLen.toNat + 31) / 32)
  have haccEvmClear :
      evmClear.accountMap.find? I.codeOwner = some accSolmClear := by
    simpa [evmClear, evmSolm0, initState, clearSolidityBytesDataWordsFrom_accountMap]
      using haccSolmClear
  have hvalueSize : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hlenMapped :
      readStorageBytesLength? bytesStoreConfig evmData
        (bytesStoreSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreSetMappedLengthAfterShortStoreOfState
      (evm := evmClear) (I := I) (len := len) (payloadStart := payloadStart)
      (acc := accSolmClear)
      (by simp [evmClear, evmSolm0, initState, clearSolidityBytesDataWordsFrom_executionEnv])
      haccEvmClear hnz hshort
    simpa [evmClear, evmData, storedWord, hstored, hvalueSize,
      bytesStoreSetMappedRef, hkey] using hlen₀
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 := by
    exact StringStoreLite.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreSetMappedHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, σClear, evmData, evmClear, evmSolm0, value, storedWord, initState,
      clearSolidityBytesDataWordsFrom_executionEnv] using
      bytesStoreSetMappedShortFromLongPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (oldLen := oldStoredLen) (storedWord := storedWord) (value := value)
        hAccounts hstored holdLenLt
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreSetMappedFrameOf key value) evmData
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreSetMappedLocals I = bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyReturnsOfWrite
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
theorem bytesStoreSetMappedEmptyOldLongRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key oldStoredLen : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedLocals I))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩)
    (hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetMappedValueBytes I
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (bytesStoreSetMappedSlot I)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σFinal := sstoreAccountMap I.codeOwner σClear (bytesStoreSetMappedSlot I) ⟨0⟩
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0
    (bytesStoreSetMappedSlot I) 0 ((oldStoredLen.toNat + 31) / 32)
  let evmData := Solm.EVM.storageStore evmClear I.codeOwner (bytesStoreSetMappedSlot I) ⟨0⟩
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    simpa [σFinal, σClear, bytesStoreSetMappedSlot, hkey,
      bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf] using
      bytesStoreX_setMappedEmptyOldLongReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen)
        hperm hreach hlenMax
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using holdStoredLen)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
        hlenZero
  have hvalueSize0 : value.size = 0 := by
    dsimp [value]
    rw [bytesStoreSetMappedValueBytes_size hpayloadList, hlenZeroAbi]
    rfl
  have hvalueEmpty : value = ByteArray.empty :=
    byteArray_eq_empty_of_size_eq_zero value hvalueSize0
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evmData := by
    have hshort : len.toNat < 32 := by
      rw [hlenZero]
      native_decide
    have hwrite₀ := bytesStoreSetMappedWriteShortOldLongPrepared
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        (oldStoredLen := oldStoredLen)
        hAccounts hpayloadList (by rw [hlenZero, hlenZeroAbi]) hshort
        hflag holdStoredLen hvalid
    simpa [evmSolm0, evmClear, evmData, value, hvalueEmpty, hshortEmpty,
      bytesStoreSetMappedRef, hkey] using hwrite₀
  have hlenMapped :
      readStorageBytesLength? bytesStoreConfig evmData
        (bytesStoreSetMappedRefOf key) = .ok 0 := by
    have hlen₀ := bytesStoreSetMappedLengthAfterEmptyStoreOfState
      (evm := evmClear) (I := I)
      (by simp [evmClear, evmSolm0, initState, clearSolidityBytesDataWordsFrom_executionEnv])
    simpa [evmClear, evmData, bytesStoreSetMappedRef, hkey] using hlen₀
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 := by
    exact StringStoreLite.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreSetMappedHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hAccountsPost : accountMapEquiv σFinal evmData.accountMap := by
    simpa [σFinal, σClear, evmData, evmClear, evmSolm0, initState,
      clearSolidityBytesDataWordsFrom_executionEnv] using
      bytesStoreSetMappedEmptyFromLongPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (oldLen := oldStoredLen) hAccounts holdLenLt
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreSetMappedFrameOf key value) evmData
          (some (.int 0))) := by
    have hlocals :
        bytesStoreSetMappedLocals I = bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyReturnsOfWrite
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

theorem bytesStoreSetMappedEmptyOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedLocals I))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩)
    (hlenZeroAbi :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetMappedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetMappedSlot I) ⟨0⟩
  let σFinal := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedSlot I) ⟨0⟩
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    simpa [σFinal, bytesStoreSetMappedSlot, hkey,
      bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf] using
      bytesStoreX_setMappedEmptyOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key)
        hperm hreach hlenMax
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
        hlenZero
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, value, bytesStoreSetMappedRef, hkey] using
      bytesStoreSetMappedWriteEmptyOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hAccounts hpayloadList hlenZeroAbi hflag hvalid
  have hlenMapped :
      readStorageBytesLength? bytesStoreConfig evmSolm1
        (bytesStoreSetMappedRefOf key) = .ok 0 := by
    simpa [evmSolm0, evmSolm1, bytesStoreSetMappedRef, hkey] using
      bytesStoreSetMappedLengthAfterEmptyWrite
        (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreSetMappedFrameOf key value) evmSolm1
          (some (.int 0))) := by
    have hlocals :
        bytesStoreSetMappedLocals I = bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyReturnsOfWrite
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
        (bytesStoreSetMappedSlot I) ⟨0⟩
  have henc :
      returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
        setMappedTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedShortNonemptyOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedLocals I))
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetMappedValueBytes I
  let storedWord := bytesStoreSetMappedShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
    (bytesStoreSetMappedSlot I) (solidityShortBytesWord value)
  let σFinal := sstoreAccountMap I.codeOwner σ_evm (bytesStoreSetMappedSlot I) storedWord
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, storedWord, bytesStoreSetMappedSlot, hkey,
      bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf] using
      bytesStoreX_setMappedShortNonemptyOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g)
        (len := len) (payloadStart := payloadStart) (key := key) (acc := accEvm)
        hperm hreach hlenMax
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
        (by simpa [bytesStoreSetMappedHeaderWord,
          bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
        hnz hshort haccEvm
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evmSolm1 := by
    simpa [evmSolm0, evmSolm1, value, bytesStoreSetMappedRef, hkey] using
      bytesStoreSetMappedWriteShortOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        hAccounts hpayloadList hlenAbi hshort hflag hvalid
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value, bytesStoreSetMappedShortStoredWord,
      bytesStoreSetMappedValueBytes] using
      bytesStoreSetChunkShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayloadList
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hvalueSize : value.size = len.toNat := by
    dsimp [value]
    rw [bytesStoreSetMappedValueBytes_size hpayloadList, ← hlenAbi]
  have hlenMapped :
      readStorageBytesLength? bytesStoreConfig evmSolm1
        (bytesStoreSetMappedRefOf key) = .ok value.size := by
    have hlen₀ := bytesStoreSetMappedLengthAfterShortWrite
      (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (len := len) (payloadStart := payloadStart) (acc := accSolm)
      haccSolm hnz hshort
    simpa [evmSolm0, evmSolm1, value, storedWord, hstored, hvalueSize,
      bytesStoreSetMappedRef, hkey] using hlen₀
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreSetMappedFrameOf key value) evmSolm1
          (some (.int value.size))) := by
    have hlocals :
        bytesStoreSetMappedLocals I = bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyReturnsOfWrite
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
        (bytesStoreSetMappedSlot I) (solidityShortBytesWord value)
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
theorem bytesStoreSetMappedShortNonemptyOldShortAbsentRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {len payloadStart key : UInt256}
    (hcode : I.code = bytesStoreBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hmissingEvm : σ_evm.find? I.codeOwner = none)
    (hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hkey : key = bytesStoreSetMappedKeyWord I)
    (hd : dispatchMsg bytesStoreContract I.calldata = some setMappedTransition)
    (hdec : decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata =
        some (bytesStoreSetMappedLocals I))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 36).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat))
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := bytesStoreSetMappedValueBytes I
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σ_evm)
        (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    exact bytesStoreX_setMappedShortNonemptyOldShortAbsentReturns
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (key := key)
      hperm hreach hlenMax
      (by simpa [bytesStoreSetMappedHeaderWord,
        bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
      (by simpa [bytesStoreSetMappedHeaderWord,
        bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
      hnz hshort hmissingEvm
  have hmissingSolm : σ_solm.find? I.codeOwner = none :=
    accountMapEquiv_find?_none hAccounts hmissingEvm
  have hmissingSolm0 :
      evmSolm0.accountMap.find? evmSolm0.executionEnv.codeOwner = none := by
    simpa [evmSolm0, initState] using hmissingSolm
  have hwrite₀ :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedSlot I) (solidityShortBytesWord value)) := by
    simpa [evmSolm0, value, bytesStoreSetMappedRef, hkey] using
      bytesStoreSetMappedWriteShortOldShortPacked
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
        hAccounts hpayloadList hlenAbi hshort hflag hvalid
  have hstoreAbsent :
      Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedSlot I) (solidityShortBytesWord value) =
        evmSolm0 := by
    exact storageStore_absent evmSolm0 evmSolm0.executionEnv.codeOwner hmissingSolm0
      (bytesStoreSetMappedSlot I) (solidityShortBytesWord value)
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes (.bytes value) = .ok evmSolm0 := by
    simpa [hstoreAbsent] using hwrite₀
  have hlenMapped :
      readStorageBytesLength? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) = .ok 0 := by
    have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedSlotOf key) = (⟨0⟩ : UInt256) := by
      simp [Solm.EVM.storageLoad, State.lookupAccount, hmissingSolm0, Option.option]
    exact bytesStoreReadLengthZeroOfHeaderLoad
      (er := bytesStoreSetMappedRefOf key) (evm := evmSolm0)
      (baseSlot := bytesStoreSetMappedSlotOf key)
      (bytesStoreSetMappedRefOf_length_slot evmSolm0 key) hload
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body
        (.returned (bytesStoreSetMappedFrameOf key value) evmSolm0
          (some (.int 0))) := by
    have hlocals :
        bytesStoreSetMappedLocals I = bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyReturnsOfWrite
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

theorem bytesStoreDecode_setMapped_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 68) :
    decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_short (cd := I.calldata) (x := "key")
      (y := "value") hshort

theorem bytesStoreDecode_setMapped_none_totalHuge {I : ExecutionEnv}
    (hbig : 2 ^ 255 ≤ I.calldata.size) :
    decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_total_huge (cd := I.calldata)
      (x := "key") (y := "value") hbig

theorem bytesStoreDecode_setMapped_none_offsetHuge {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_offset_huge (cd := I.calldata)
      (x := "key") (y := "value") hsz68 hsizeSign hoff

theorem bytesStoreDecode_setMapped_none_lengthShort {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 36).toNat + 32) :
    decodeCalldata (setMappedTransition.params.map Param.name)
      (transitionSignature setMappedTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["key", "value"] [uint256, .bytes] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_uint256_bytes_none_length_short (cd := I.calldata)
      (x := "key") (y := "value") hsz68 hsizeSign hoffMax hshort

theorem bytesStoreDecode_setMapped_none_lengthHuge {I : ExecutionEnv}
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

theorem bytesStoreDecode_setMapped_none_payloadShort {I : ExecutionEnv}
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

theorem bytesStoreDecode_setMapped {I : ExecutionEnv}
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
        some (bytesStoreSetMappedLocals I) := by
  show decodeCalldata ["key", "value"] [uint256, .bytes] I.calldata =
    some (bytesStoreSetMappedLocals I)
  simpa [uint256, abiUInt256, bytesStoreSetMappedLocals,
    bytesStoreSetMappedKeyWord, bytesStoreSetMappedValueBytes,
    bytesStoreSetChunkValueBytes] using
    decodeCalldata_uint256_bytes_some (cd := I.calldata) (x := "key")
      (y := "value") hsz68 hsizeSign hoffMax hlenWord hlenMax hpayload

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedShortNonemptyOldLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hkey : key = bytesStoreSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hnzLen : len.toNat ≠ 0 := by
    rw [hlenAbi]
    exact hnz
  have hshortLen : len.toNat < 32 := by
    rw [hlenAbi]
    exact hshort
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  exact bytesStoreSetMappedShortNonemptyOldLongRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen) (accEvm := accEvm)
    hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec
    hlenAbi hpayloadStart hoffMax hsrc hpayloadList hlenMaxLen
    hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
    hnzLen hshortLen

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedEmptyOldLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_gt_max I hoffMax hlenMaxAbiWord
  have hlenZeroLen : len = ⟨0⟩ := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_zero I hoffMax hlenZero
  have hkey : key = bytesStoreSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  exact bytesStoreSetMappedEmptyOldLongRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (key := key)
    (oldStoredLen := oldStoredLen)
    hcode hperm hwv hAccounts hreach hkey hd hdec hpayloadList hlenMaxLen
    hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
    hlenZeroLen hlenZero

theorem bytesStoreSetMappedShortOldLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hzero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩
  · exact bytesStoreSetMappedEmptyOldLongRuntime
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
        have hheader0 : bytesStoreSetMappedHeaderWord σ_evm I = ⟨0⟩ := by
          rw [bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf, hacc]
          rfl
        have hland0 :
            UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
          rw [hheader0]
          native_decide
        exact False.elim (hflag hland0)
    | some accEvm =>
        exact bytesStoreSetMappedShortNonemptyOldLongRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
          hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax
          hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid
          hnz hshort

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedLongOldLongRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  let oldStoredLen : UInt256 := UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreCalldataWord36_add32]
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
  have hkey : key = bytesStoreSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hnzLen : len.toNat ≠ 0 := by
    intro hz
    exact hlongLen (by omega)
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreSetChunkPayloadStartLen_le_of_payload
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
    · exact bytesStoreSetMappedLongNoTailOldLongClearRuntimeOfReach
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
        bytesStoreCalldataLongDataAddr_toNat_of_bound
          (payloadStart := payloadStart) (i := len.toNat / 32) htailAddrBound
      exact bytesStoreSetMappedLongTailOldLongClearRuntimeOfReach
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
    · exact bytesStoreSetMappedLongNoTailOldLongNoClearRuntimeOfReach
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
        bytesStoreCalldataLongDataAddr_toNat_of_bound
          (payloadStart := payloadStart) (i := len.toNat / 32) htailAddrBound
      exact bytesStoreSetMappedLongTailOldLongNoClearRuntimeOfReach
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        (len := len) (payloadStart := payloadStart) (key := key)
        (oldStoredLen := oldStoredLen)
        hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec hlenAbi
        hpayloadStart hoffMax hsrc haddrBound htailAddr hpayloadList hlenMaxLen hlenMaxNat
        hflag (by dsimp [oldStoredLen]) (by simpa [oldStoredLen] using hvalid)
        hgtOldNew0 hlongLen (by simpa [hlenAbi] using hnoTailMod)

theorem bytesStoreSetMappedEmptyOldShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_gt_max I hoffMax hlenMaxAbiWord
  have hlenZeroLen : len = ⟨0⟩ := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_zero I hoffMax hlenZero
  have hkey : key = bytesStoreSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  exact bytesStoreSetMappedEmptyOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (key := key)
    hcode hperm hwv hAccounts hreach hkey hd hdec hpayloadList hlenMaxLen
    hflag hvalid hlenZeroLen hlenZero

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedShortNonemptyOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreCalldataWord36_add32]
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hkey : key = bytesStoreSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hnzLen : len.toNat ≠ 0 := by
    rw [hlenAbi]
    exact hnz
  have hshortLen : len.toNat < 32 := by
    rw [hlenAbi]
    exact hshort
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreSetChunkPayloadStartLen_le_of_payload
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnzLen hpayloadList
  exact bytesStoreSetMappedShortNonemptyOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (key := key)
    (accEvm := accEvm)
    hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec
    hlenAbi hpayloadStart hoffMax hsrc hpayloadList hlenMaxLen
    hflag hvalid hnzLen hshortLen

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedShortNonemptyOldShortAbsentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hnz :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat ≠ 0)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_eq I hoffMax
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hkey : key = bytesStoreSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hnzLen : len.toNat ≠ 0 := by
    rw [hlenAbi]
    exact hnz
  have hshortLen : len.toNat < 32 := by
    rw [hlenAbi]
    exact hshort
  exact bytesStoreSetMappedShortNonemptyOldShortAbsentRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (len := len) (payloadStart := payloadStart) (key := key)
    hcode hperm hwv hAccounts hmissingEvm hreach hkey hd hdec hlenAbi hpayloadList
    hlenMaxLen hflag hvalid hnzLen hshortLen

theorem bytesStoreSetMappedShortOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hzero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) = ⟨0⟩
  · exact bytesStoreSetMappedEmptyOldShortRuntime
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
        exact bytesStoreSetMappedShortNonemptyOldShortAbsentRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hnz hshort
    | some accEvm =>
        exact bytesStoreSetMappedShortNonemptyOldShortRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
          hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hnz hshort

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedLongNoTailOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreCalldataWord36_add32]
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
  have hkey : key = bytesStoreSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hnzLen : len.toNat ≠ 0 := by
    intro hz
    exact hlongLen (by omega)
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreSetChunkPayloadStartLen_le_of_payload
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
  exact bytesStoreSetMappedLongNoTailOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (len := len) (payloadStart := payloadStart) (key := key)
    hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec hlenAbi
    hpayloadStart hoffMax hsrc haddrBound hpayloadList hlenMaxLen hlenMaxNat
    hflag hvalid hlongLen (by simpa [hlenAbi] using hnoTailMod)

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedLongTailOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_eq I hoffMax
  have hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨32⟩) := by
    dsimp [payloadStart]
    rw [bytesStoreCalldataWord36_add32]
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
  have hkey : key = bytesStoreSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hnzLen : len.toNat ≠ 0 := by
    intro hz
    exact hlongLen (by omega)
  have hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size :=
    bytesStoreSetChunkPayloadStartLen_le_of_payload
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
    bytesStoreCalldataLongDataAddr_toNat_of_bound
      (payloadStart := payloadStart) (i := len.toNat / 32) htailAddrBound
  exact bytesStoreSetMappedLongTailOldShortRuntimeOfReach
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
    (len := len) (payloadStart := payloadStart) (key := key)
    hcode hperm hwv hAccounts haccEvm hreach hkey hd hdec hlenAbi
    hpayloadStart hoffMax hsrc haddrBound htailAddr hpayloadList hlenMaxLen hlenMaxNat
    hflag hvalid hlongLen (by simpa [hlenAbi] using htailMod)

theorem bytesStoreSetMappedLongOldShortPresentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0
  · exact bytesStoreSetMappedLongNoTailOldShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
      hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
      hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid
      hnewLong hnoTailMod
  · exact bytesStoreSetMappedLongTailOldShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
      hcode hsize hperm hwv hsel hAccounts haccEvm hsz68 hhi hsizeSign hoffMax
      hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid
      hnewLong hnoTailMod

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedLongNoTailOldShortAbsentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32)
    (hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_eq I hoffMax
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hkey : key = bytesStoreSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σ_evm) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    exact bytesStoreX_setMappedLongNoTailOldShortAbsentReturns
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (key := key)
      hperm hreach hlenMaxLen
      (by simpa [bytesStoreSetMappedHeaderWord,
        bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
      (by simpa [bytesStoreSetMappedHeaderWord,
        bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
      hlongLen (by simpa [hlenAbi] using hnoTailMod) hmissingEvm
  exact bytesStoreSetMappedLongOldShortAbsentRuntimeOfReturn
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len) (key := key)
    hcode hwv hAccounts hmissingEvm hkey hd hdec hlenAbi hpayloadList
    hlongLen hflag hvalid hret

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedLongTailOldShortAbsentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32)
    (htailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat) := by
    dsimp [len]
    exact bytesStoreSetChunkRawLengthWord_eq I hoffMax
  have hlenMaxAbiWord :
      UInt256.gt (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hlenMax
  have hlenMaxLen : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩ := by
    rw [hlenAbi]
    exact hlenMaxAbiWord
  have hkey : key = bytesStoreSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hlongLen : ¬ len.toNat < 32 := by
    rw [hlenAbi]
    exact hnewLong
  have hret :
      RDret bytesStoreBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σ_evm) (UInt256.toByteArray (⟨0⟩ : UInt256)) := by
    exact bytesStoreX_setMappedLongTailOldShortAbsentReturns
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
      (A := A) (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (key := key)
      hperm hreach hlenMaxLen
      (by simpa [bytesStoreSetMappedHeaderWord,
        bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
      (by simpa [bytesStoreSetMappedHeaderWord,
        bytesStoreSetMappedHeaderWordOf, hkey] using hvalid)
      hlongLen (by simpa [hlenAbi] using htailMod) hmissingEvm
  exact bytesStoreSetMappedLongOldShortAbsentRuntimeOfReturn
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len) (key := key)
    hcode hwv hAccounts hmissingEvm hkey hd hdec hlenAbi hpayloadList
    hlongLen hflag hvalid hret

theorem bytesStoreSetMappedLongOldShortAbsentRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hnoTailMod :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat % 32 = 0
  · exact bytesStoreSetMappedLongNoTailOldShortAbsentRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hmissingEvm hsz68 hhi hsizeSign hoffMax
      hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid
      hnewLong hnoTailMod
  · exact bytesStoreSetMappedLongTailOldShortAbsentRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hmissingEvm hsz68 hhi hsizeSign hoffMax
      hlenWord hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid
      hnewLong hnoTailMod

theorem bytesStoreSetMappedLongOldShortRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnewLong :
      ¬ (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  cases hacc : σ_evm.find? I.codeOwner with
  | none =>
      exact bytesStoreSetMappedLongOldShortAbsentRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hnewLong
  | some accEvm =>
      exact bytesStoreSetMappedLongOldShortPresentRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
        hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hnewLong

theorem bytesStoreSetMappedOldShortValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32
  · exact bytesStoreSetMappedShortOldShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hshort
  · exact bytesStoreSetMappedLongOldShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hshort

theorem bytesStoreSetMappedOldLongValidRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32
  · exact bytesStoreSetMappedShortOldLongRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hshort
  · cases hacc : σ_evm.find? I.codeOwner with
    | none =>
        have hheader0 : bytesStoreSetMappedHeaderWord σ_evm I = ⟨0⟩ := by
          rw [bytesStoreSetMappedHeaderWord, bytesStoreSetMappedHeaderWordOf, hacc]
          rfl
        have hland0 :
            UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩ := by
          rw [hheader0]
          native_decide
        exact False.elim (hflag hland0)
    | some accEvm =>
        exact bytesStoreSetMappedLongOldLongRuntime
          (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
          (σ₀ := σ₀) (A := A) (I := I) (g := g) (accEvm := accEvm)
          hcode hsize hperm hwv hsel hAccounts hacc hsz68 hhi hsizeSign hoffMax hlenWord
          hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hshort

theorem bytesStoreSetMappedLongMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hkey : key = bytesStoreSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hrev : RDrev bytesStoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    exact bytesStoreX_setMappedLongMalformedHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (key := key)
      hreach hlenMaxWord
      (by simpa [bytesStoreSetMappedHeaderWord,
        bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
      (by simpa [bytesStoreSetMappedHeaderWord,
        bytesStoreSetMappedHeaderWordOf, hkey] using hbad)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedSlot I) =
        bytesStoreSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes
        (.bytes (bytesStoreSetMappedValueBytes I)) = .revert := by
    simpa [evmSolm0, bytesStoreSetMappedRef, hkey] using
      bytesStoreSetMappedWriteMalformedLong
        (evm := evmSolm0) I (bytesStoreSetMappedHeaderWord σ_evm I)
        (bytesStoreSetMappedValueBytes I)
        hloadHeader hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body .reverted := by
    let value := bytesStoreSetMappedValueBytes I
    have hlocals :
        bytesStoreSetMappedLocals I =
          bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyRevertsOfWrite
      (evm := evmSolm0) (key := key) (value := value)
      (by simp [evmSolm0, initState]; exact hwv)
      (by simpa [value] using hwrite)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetMappedShortMalformedRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
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
  have hreach : ∃ k C, RD bytesStoreBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1644⟩
      [len, payloadStart, key, ⟨263⟩, bytesStoreSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C := by
    dsimp [len, payloadStart, key]
    exact bytesStoreX_setMappedDecodeValidRaw
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayloadList
  have hkey : key = bytesStoreSetMappedKeyWord I := by
    dsimp [key]
    rw [bytesStoreSetMappedKeyWord, calldataWord]
    have h4 : (⟨4⟩ : UInt256).toNat = 4 := by native_decide
    rw [h4]
  have hrev : RDrev bytesStoreBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) := by
    exact bytesStoreX_setMappedShortMalformedHeader
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      (len := len) (payloadStart := payloadStart) (key := key)
      hreach hlenMaxWord
      (by simpa [bytesStoreSetMappedHeaderWord,
        bytesStoreSetMappedHeaderWordOf, hkey] using hflag)
      (by simpa [bytesStoreSetMappedHeaderWord,
        bytesStoreSetMappedHeaderWordOf, hkey] using hbad)
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hloadHeader :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner
          (bytesStoreSetMappedSlot I) =
        bytesStoreSetMappedHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreStorageLoadSetMappedHeader_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreConfig evmSolm0
        (bytesStoreSetMappedRefOf key) .bytes
        (.bytes (bytesStoreSetMappedValueBytes I)) = .revert := by
    simpa [evmSolm0, bytesStoreSetMappedRef, hkey] using
      bytesStoreSetMappedWriteMalformedShort
        (evm := evmSolm0) I (bytesStoreSetMappedHeaderWord σ_evm I)
        (bytesStoreSetMappedValueBytes I)
        hloadHeader hflag hbad
  have hbody :
      ExecTransitionBody bytesStoreConfig bytesStoreContract evmSolm0
        (bytesStoreSetMappedLocals I) setMappedTransition.body .reverted := by
    let value := bytesStoreSetMappedValueBytes I
    have hlocals :
        bytesStoreSetMappedLocals I =
          bytesStoreSetMappedLocalsOf key value := by
      simp [value, bytesStoreSetMappedLocals, bytesStoreSetMappedLocalsOf, hkey]
    rw [hlocals]
    exact bytesStoreSetMappedBodyRevertsOfWrite
      (evm := evmSolm0) (key := key) (value := value)
      (by simp [evmSolm0, initState]; exact hwv)
      (by simpa [value] using hwrite)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreSetMappedShortHeaderRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    (hflag : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hshort :
      (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat < 32) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hvalid :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
  · exact bytesStoreSetMappedShortOldShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag hvalid hshort
  · exact bytesStoreSetMappedShortMalformedRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
      hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflag
      (not_ne_iff.mp hvalid)

theorem bytesStoreSetMappedDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 68) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedSelector_size hsel
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped_none_short (I := I) hshort
  exact (bytesStoreX_setMappedDecodeShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz hshort hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetMappedDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreSetMappedSelector_size hsel
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped_none_totalHuge (I := I) (by omega)
  exact (bytesStoreX_setMappedDecodeHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz hbig hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetMappedDecodeOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setMappedTransition.params.map Param.name)
        (transitionSignature setMappedTransition).paramTypes I.calldata = none := by
    by_cases hsizeSign' : I.calldata.size < 2 ^ 255
    · exact bytesStoreDecode_setMapped_none_offsetHuge (I := I)
        hsz68 hsizeSign' hoff
    · exact bytesStoreDecode_setMapped_none_totalHuge (I := I)
        (Nat.le_of_not_gt hsizeSign')
  exact (bytesStoreX_setMappedDecodeOffsetHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hcode hwv hsz68 hhi hsize hsel hoff)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetMappedDecodeLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped_none_lengthShort (I := I)
    hsz68 hsizeSign hoffMax hlenShort
  exact (bytesStoreX_setMappedDecodeLengthShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetMappedDecodeLengthHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped_none_lengthHuge (I := I)
    hsz68 hsizeSign hoffMax hlenWord hlenHuge
  exact (bytesStoreX_setMappedDecodeLengthHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetMappedDecodePayloadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped_none_payloadShort (I := I)
    hsz68 hsizeSign hoffMax hlenWord hlenMax hpayloadListNe
  exact (bytesStoreX_setMappedDecodePayloadShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreSetMappedDecodeTotalHighRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat)
    (hsizeHigh : ¬ I.calldata.size < 2 ^ 255) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreDispatch_setMapped (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreDecode_setMapped_none_totalHuge (I := I)
    (Nat.le_of_not_gt hsizeHigh)
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ :=
    bytesStoreSetChunkStart_slt_zero_of_size_high I.calldata hoffMax hsize hsizeHigh
  exact (bytesStoreX_setMappedDecodeLengthShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hstart)
    |>.reEquivDecodingFailed hcode hd hdec

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedDecodedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
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
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hflagShort : UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩
  · by_cases hvalidShort :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreSetMappedOldShortValidRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflagShort hvalidShort
    · exact bytesStoreSetMappedShortMalformedRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflagShort
        (not_ne_iff.mp hvalidShort)
  · have hflagLong :
      UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩ := hflagShort
    by_cases hvalidLong :
      UInt256.sub (UInt256.land (bytesStoreSetMappedHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreSetMappedHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩
    · exact bytesStoreSetMappedOldLongValidRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflagLong hvalidLong
    · exact bytesStoreSetMappedLongMalformedRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax hlenWord
        hlenMax hpayloadList hstart hlenMaxWord hpayloadWord hflagLong
        (not_ne_iff.mp hvalidLong)

set_option maxHeartbeats 1200000 in
theorem bytesStoreSetMappedRuntime
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xe1, 0x91, 0x9b, 0x17]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor bytesStoreConfig bytesStoreContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  by_cases hshort : I.calldata.size < 68
  · exact bytesStoreSetMappedDecodeShortRuntime
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      hcode hsize hperm hwv hsel hAccounts hshort
  · have hsz68 : 68 ≤ I.calldata.size := Nat.le_of_not_gt hshort
    by_cases hbig : 2 ^ 255 + 4 ≤ I.calldata.size
    · exact bytesStoreSetMappedDecodeHugeRuntime
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hcode hsize hperm hwv hsel hAccounts hbig
    · have hhi : I.calldata.size < 2 ^ 255 + 4 := Nat.lt_of_not_ge hbig
      by_cases hoff : ABI.solcMaxU64 < (calldataWord I.calldata 36).toNat
      · exact bytesStoreSetMappedDecodeOffsetHugeRuntime
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
              bytesStoreSetChunkStart_slt_zero_of_length_short
                I.calldata hoffMax hsizeSign hlenShort
            exact bytesStoreSetMappedDecodeLengthShortRuntime
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
              bytesStoreSetChunkStart_slt_one I.calldata hoffMax hlenWord hsizeSign
            by_cases hlenHuge :
                ABI.solcMaxU64 <
                  (calldataWord I.calldata (4 + (calldataWord I.calldata 36).toNat)).toNat
            · have hlenMaxWord :
                  UInt256.gt
                      (uInt256OfByteArray
                        (I.calldata.readBytes
                          ((((⟨4⟩ : UInt256) + calldataWord I.calldata 36)).toNat) 32))
                      ⟨18446744073709551615⟩ = ⟨1⟩ := by
                rw [← bytesStoreCalldataWord36_add32 I]
                rw [bytesStoreSetChunkRawLengthWord_eq I hoffMax]
                apply ugt_one
                rw [show (⟨18446744073709551615⟩ : UInt256).toNat =
                    ABI.solcMaxU64 by native_decide]
                exact hlenHuge
              exact bytesStoreSetMappedDecodeLengthHugeRuntime
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
                  rw [← bytesStoreCalldataWord36_add32 I]
                  rw [bytesStoreSetChunkRawLengthWord_eq I hoffMax]
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
                  bytesStoreSetChunkPayloadWord_zero_of_payload
                    I hsize hoffMax hlenWord hlenHuge hpayloadList
                exact bytesStoreSetMappedDecodedRuntime
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
                  rw [← bytesStoreCalldataWord36_add32 I]
                  rw [bytesStoreSetChunkRawLengthWord_eq I hoffMax]
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
                  bytesStoreSetChunkPayloadWord_one_of_payload_short
                    I hsize hoffMax hlenWord hlenHuge hpayloadListNe
                exact bytesStoreSetMappedDecodePayloadShortRuntime
                  (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm)
                  (σ_solm := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hcode hsize hperm hwv hsel hAccounts hsz68 hhi hsizeSign hoffMax
                  hlenWord hlenHuge hpayloadListNe hstart hlenMaxWord hpayloadWord
        · exact bytesStoreSetMappedDecodeTotalHighRuntime
            (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hcode hsize hperm hwv hsel hAccounts hsz68 hhi hoffMax hsizeSign

end BytesStore
