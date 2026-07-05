import Examples.BytesStoreLite.FullSetByte
import Examples.BytesStoreLite.FullSetLongOldLongRuntime
import Examples.BytesStoreLite.FullPushChunkLongTail
import Examples.BytesStoreLite.FullPushChunkLongStorage
import Examples.BytesStoreLite.FullSetPacketStorage
import Examples.BytesStoreLite.StorageLoopFacts

/-!
# BytesStoreLite — `setPacket(bytes,uint256)` runtime slice

This module isolates the full-contract `setPacket(bytes,uint256)` selector arm.  The first layer
pins the mixed dynamic/static ABI decoding facts; the bytecode body proof reuses the shared
calldata-bytes storage-write helper from the `set(bytes)` proof, with base slot `2`, followed by
the scalar tag write at slot `3`.
-/

namespace BytesStoreLite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

def bytesStoreLiteSetPacketTagWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

def bytesStoreLiteSetPacketLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "value" (.bytes (BytesStoreLiteCore.setDecodedValueBytes I))).insert
    "tag" (.int (Int.ofNat (bytesStoreLiteSetPacketTagWord I).toNat)))

def bytesStoreLiteSetPacketLocalsOf (value : ByteArray) (tag : UInt256) : Store :=
  ((∅ : Store).insert "value" (.bytes value)).insert "tag"
    (.int (Int.ofNat tag.toNat))

def bytesStoreLiteSetPacketFrameOf (value : ByteArray) (tag : UInt256) : Frame :=
  { contract := bytesStoreLiteContract,
    locals := bytesStoreLiteSetPacketLocalsOf value tag }

theorem accountMapEquiv_setPacketTagStore {σ : AccountMap} {evm : EVM.State}
    (owner : AccountAddress) (tag : UInt256)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
  accountMapEquiv
      (sstoreAccountMap owner σ ⟨3⟩ tag)
      (Solm.EVM.storageStore evm owner ⟨3⟩ tag).accountMap := by
  exact accountMapEquiv_bytesHeaderStore owner ⟨3⟩ tag hAccounts

theorem accountMapEquiv_setPacketDataHeaderAndTagStore {σ : AccountMap} {evm : EVM.State}
    (owner : AccountAddress) (header tag : UInt256)
    (hAccounts : accountMapEquiv σ evm.accountMap) :
    accountMapEquiv
      (sstoreAccountMap owner
        (sstoreAccountMap owner σ ⟨2⟩ header) ⟨3⟩ tag)
      (Solm.EVM.storageStore
        (Solm.EVM.storageStore evm owner ⟨2⟩ header)
        owner ⟨3⟩ tag).accountMap := by
  exact accountMapEquiv_bytesHeaderAndTagStore owner ⟨2⟩ header ⟨3⟩ tag hAccounts

theorem bytesStoreLiteSetPacketBodyReturnsOfAssigns
    {evm evmData evmTag : EVM.State} {value : ByteArray} {tag : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassignData :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetPacketFrameOf value tag)
        evm .storage packetDataRef (.bytes value) =
        .ok (bytesStoreLiteSetPacketFrameOf value tag, evmData))
    (hassignTag :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetPacketFrameOf value tag)
        evmData .storage packetTagRef (.int (Int.ofNat tag.toNat)) =
        .ok (bytesStoreLiteSetPacketFrameOf value tag, evmTag))
    (hlen :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetPacketFrameOf value tag)
        evmTag (.arrayLength .storage packetDataRef) =
        .ok (.int value.size)) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetPacketLocalsOf value tag)
      setPacketTransition.body
      (.returned
        (bytesStoreLiteSetPacketFrameOf value tag)
        evmTag (some (.int value.size))) := by
  let locals0 : Store := bytesStoreLiteSetPacketLocalsOf value tag
  let solm0 : Frame := bytesStoreLiteSetPacketFrameOf value tag
  have hvalue : evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreLiteSetPacketLocalsOf value tag).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreLiteSetPacketLocalsOf
      rw [store_get_ne]
      · exact store_get_self (∅ : Store) "value" (.bytes value)
      · native_decide
    rw [Std.HashMap.get?_eq_getElem?] at hlookup
    rw [evalExpr?]
    simp [solm0, bytesStoreLiteSetPacketFrameOf, hlookup, EvalResult.ofOption]
  have htag : evalExpr? bytesStoreLiteConfig solm0 evmData (.var "tag") =
      .ok (.int (Int.ofNat tag.toNat)) := by
    have hlookup :
        (bytesStoreLiteSetPacketLocalsOf value tag).get? "tag" =
          some (.int (Int.ofNat tag.toNat)) := by
      unfold bytesStoreLiteSetPacketLocalsOf
      exact store_get_self ((∅ : Store).insert "value" (.bytes value)) "tag"
        (.int (Int.ofNat tag.toNat))
    rw [Std.HashMap.get?_eq_getElem?] at hlookup
    rw [evalExpr?]
    simp [solm0, bytesStoreLiteSetPacketFrameOf, hlookup, EvalResult.ofOption]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.assign hvalue (by simpa [solm0, locals0] using hassignData)) <|
        ExecBlock.consNormal
          (ExecStmt.assign htag (by simpa [solm0, locals0] using hassignTag)) <|
          ExecBlock.consReturn
            (ExecStmt.return (by simpa [solm0, locals0] using hlen))

theorem bytesStoreLiteSetPacketBodyReturnsOfAssignsLength
    {evm evmData evmTag : EVM.State} {value : ByteArray} {tag : UInt256} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hassignData :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetPacketFrameOf value tag)
        evm .storage packetDataRef (.bytes value) =
        .ok (bytesStoreLiteSetPacketFrameOf value tag, evmData))
    (hassignTag :
      assignStorageRef? bytesStoreLiteConfig
        (bytesStoreLiteSetPacketFrameOf value tag)
        evmData .storage packetTagRef (.int (Int.ofNat tag.toNat)) =
        .ok (bytesStoreLiteSetPacketFrameOf value tag, evmTag))
    (hlen :
      evalExpr? bytesStoreLiteConfig
        (bytesStoreLiteSetPacketFrameOf value tag)
        evmTag (.arrayLength .storage packetDataRef) =
        .ok (.int n)) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetPacketLocalsOf value tag)
      setPacketTransition.body
      (.returned
        (bytesStoreLiteSetPacketFrameOf value tag)
        evmTag (some (.int n))) := by
  let locals0 : Store := bytesStoreLiteSetPacketLocalsOf value tag
  let solm0 : Frame := bytesStoreLiteSetPacketFrameOf value tag
  have hvalue : evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreLiteSetPacketLocalsOf value tag).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreLiteSetPacketLocalsOf
      rw [store_get_ne]
      · exact store_get_self (∅ : Store) "value" (.bytes value)
      · native_decide
    rw [Std.HashMap.get?_eq_getElem?] at hlookup
    rw [evalExpr?]
    simp [solm0, bytesStoreLiteSetPacketFrameOf, hlookup, EvalResult.ofOption]
  have htag : evalExpr? bytesStoreLiteConfig solm0 evmData (.var "tag") =
      .ok (.int (Int.ofNat tag.toNat)) := by
    have hlookup :
        (bytesStoreLiteSetPacketLocalsOf value tag).get? "tag" =
          some (.int (Int.ofNat tag.toNat)) := by
      unfold bytesStoreLiteSetPacketLocalsOf
      exact store_get_self ((∅ : Store).insert "value" (.bytes value)) "tag"
        (.int (Int.ofNat tag.toNat))
    rw [Std.HashMap.get?_eq_getElem?] at hlookup
    rw [evalExpr?]
    simp [solm0, bytesStoreLiteSetPacketFrameOf, hlookup, EvalResult.ofOption]
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consNormal
        (ExecStmt.assign hvalue (by simpa [solm0, locals0] using hassignData)) <|
        ExecBlock.consNormal
          (ExecStmt.assign htag (by simpa [solm0, locals0] using hassignTag)) <|
          ExecBlock.consReturn
            (ExecStmt.return (by simpa [solm0, locals0] using hlen))

theorem bytesStoreLiteSetPacketResolveData (evm : EVM.State) (value : ByteArray)
    (tag : UInt256) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetPacketFrameOf value tag) evm packetDataRef =
        .ok ({ base := "packet", steps := [.field "data"] }, .bytes) := by
  have hbase :
      (bytesStoreLiteSetPacketFrameOf value tag).locals.get? packetDataRef.base = none := by
    simp [bytesStoreLiteSetPacketFrameOf, bytesStoreLiteSetPacketLocalsOf, packetDataRef,
      Std.HashMap.get?_eq_getElem?]
  have her :
      evalStorageRef bytesStoreLiteConfig (bytesStoreLiteSetPacketFrameOf value tag)
        evm packetDataRef =
          .ok ({ base := "packet", steps := [.field "data"] } : EvaledStorageRef) := by
    simpa [packetDataRef] using
      (evalStorageRef_field
        (cfg := bytesStoreLiteConfig) (solm := bytesStoreLiteSetPacketFrameOf value tag)
        (evm := evm) (base := "packet") (field := "data"))
  exact resolveStorageRef?_ok hbase her (by
    simp [bytesStoreLiteSetPacketFrameOf, storageTypeAt?, bytesStoreLiteContract,
      storageDecls, packetStructDecl, packetStructTy, bytesSt, storageTypeStep?])

theorem bytesStoreLiteSetPacketResolveTag (evm : EVM.State) (value : ByteArray)
    (tag : UInt256) :
    resolveStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetPacketFrameOf value tag) evm packetTagRef =
        .ok ({ base := "packet", steps := [.field "tag"] },
          uint256St) := by
  have hbase :
      (bytesStoreLiteSetPacketFrameOf value tag).locals.get? packetTagRef.base = none := by
    simp [bytesStoreLiteSetPacketFrameOf, bytesStoreLiteSetPacketLocalsOf, packetTagRef,
      Std.HashMap.get?_eq_getElem?]
  have her :
      evalStorageRef bytesStoreLiteConfig (bytesStoreLiteSetPacketFrameOf value tag)
        evm packetTagRef =
          .ok ({ base := "packet", steps := [.field "tag"] } : EvaledStorageRef) := by
    simpa [packetTagRef] using
      (evalStorageRef_field
        (cfg := bytesStoreLiteConfig) (solm := bytesStoreLiteSetPacketFrameOf value tag)
        (evm := evm) (base := "packet") (field := "tag"))
  exact resolveStorageRef?_ok hbase her (by
    simp [bytesStoreLiteSetPacketFrameOf, storageTypeAt?, bytesStoreLiteContract,
      storageDecls, packetStructDecl, packetStructTy, uint256St, uint256Int, storageTypeStep?])

theorem bytesStoreLiteAssignPacketDataOfWrite
    {evm evmData : EVM.State} {value : ByteArray} {tag : UInt256}
    (hwrite : writeStorage? bytesStoreLiteConfig evm
      { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
        .ok evmData) :
    assignStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetPacketFrameOf value tag)
      evm .storage packetDataRef (.bytes value) =
        .ok (bytesStoreLiteSetPacketFrameOf value tag, evmData) := by
  have hresolve := bytesStoreLiteSetPacketResolveData evm value tag
  exact assignStorageRef_storage_bytes_ok_of_write hresolve hwrite

theorem bytesStoreLiteAssignPacketTagOfStore
    {evmData evmTag : EVM.State} {value : ByteArray} {tag : UInt256}
    (hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag) :
    assignStorageRef? bytesStoreLiteConfig
      (bytesStoreLiteSetPacketFrameOf value tag)
      evmData .storage packetTagRef (.int (Int.ofNat tag.toNat)) =
        .ok (bytesStoreLiteSetPacketFrameOf value tag, evmTag) := by
  have hbase :
      (bytesStoreLiteSetPacketFrameOf value tag).locals.get? packetTagRef.base = none := by
    simp [bytesStoreLiteSetPacketFrameOf, bytesStoreLiteSetPacketLocalsOf, packetTagRef,
      Std.HashMap.get?_eq_getElem?]
  have her :
      evalStorageRef bytesStoreLiteConfig (bytesStoreLiteSetPacketFrameOf value tag)
        evmData packetTagRef =
          .ok { base := "packet", steps := [.field "tag"] } := by
    simpa [packetTagRef] using
      (evalStorageRef_field
        (cfg := bytesStoreLiteConfig) (solm := bytesStoreLiteSetPacketFrameOf value tag)
        (evm := evmData) (base := "packet") (field := "tag"))
  have hty :
      storageTypeAt? (bytesStoreLiteSetPacketFrameOf value tag).contract.storage
          ({ base := "packet", steps := [.field "tag"] } : EvaledStorageRef) =
        some uint256St := by
    simp [bytesStoreLiteSetPacketFrameOf, storageTypeAt?, bytesStoreLiteContract,
      storageDecls, packetStructDecl, packetStructTy, uint256St, uint256Int,
      storageTypeStep?]
  have hloc :
      bytesStoreLiteConfig.storage.layout
          ({ base := "packet", steps := [.field "tag"] } : EvaledStorageRef) =
        fun _ => some (uint256Loc ⟨3⟩) := by
    funext evm'
    rfl
  exact assignStorageRef_storage_scalar (cfg := bytesStoreLiteConfig)
    (solm := bytesStoreLiteSetPacketFrameOf value tag) (evm := evmData)
    (evm' := evmTag) (slot := packetTagRef)
    (er := { base := "packet", steps := [.field "tag"] }) (loc := uint256Loc ⟨3⟩)
    (n := Int.ofNat tag.toNat)
    hbase her hty hloc hstore

theorem bytesStoreLiteSetPacketLengthAfterWrite
    {evmTag : EVM.State} {value : ByteArray} {tag : UInt256}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evmTag
      { base := "packet", steps := [.field "data"] } = .ok value.size) :
    evalExpr? bytesStoreLiteConfig
      (bytesStoreLiteSetPacketFrameOf value tag)
      evmTag (.arrayLength .storage packetDataRef) =
        .ok (.int value.size) := by
  have hresolve := bytesStoreLiteSetPacketResolveData evmTag value tag
  simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure]

theorem bytesStoreLiteSetPacketLengthAfterWriteOfLength
    {evmTag : EVM.State} {value : ByteArray} {tag : UInt256} {n : Nat}
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evmTag
      { base := "packet", steps := [.field "data"] } = .ok n) :
    evalExpr? bytesStoreLiteConfig
      (bytesStoreLiteSetPacketFrameOf value tag)
      evmTag (.arrayLength .storage packetDataRef) =
        .ok (.int n) := by
  have hresolve := bytesStoreLiteSetPacketResolveData evmTag value tag
  simp only [evalExpr?, hresolve, readStorageArrayLength?, EvalResult.bind, bind, hlen, pure]

theorem bytesStoreLiteSetPacketBodyReturnsOfWriteAndTagStore
    {evm evmData evmTag : EVM.State} {value : ByteArray} {tag : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite : writeStorage? bytesStoreLiteConfig evm
      { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
        .ok evmData)
    (hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evmTag
      { base := "packet", steps := [.field "data"] } = .ok value.size) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetPacketLocalsOf value tag)
      setPacketTransition.body
      (.returned
        (bytesStoreLiteSetPacketFrameOf value tag)
        evmTag (some (.int value.size))) := by
  exact bytesStoreLiteSetPacketBodyReturnsOfAssigns (evm := evm) (evmData := evmData)
    (evmTag := evmTag) (value := value) (tag := tag) hwv
    (bytesStoreLiteAssignPacketDataOfWrite hwrite)
    (bytesStoreLiteAssignPacketTagOfStore hstore)
    (bytesStoreLiteSetPacketLengthAfterWrite hlen)

theorem bytesStoreLiteSetPacketBodyReturnsOfWriteAndTagStoreLength
    {evm evmData evmTag : EVM.State} {value : ByteArray} {tag : UInt256} {n : Nat}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite : writeStorage? bytesStoreLiteConfig evm
      { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
        .ok evmData)
    (hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evmTag
      { base := "packet", steps := [.field "data"] } = .ok n) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetPacketLocalsOf value tag)
      setPacketTransition.body
      (.returned
        (bytesStoreLiteSetPacketFrameOf value tag)
        evmTag (some (.int n))) := by
  exact bytesStoreLiteSetPacketBodyReturnsOfAssignsLength (evm := evm) (evmData := evmData)
    (evmTag := evmTag) (value := value) (tag := tag) hwv
    (bytesStoreLiteAssignPacketDataOfWrite hwrite)
    (bytesStoreLiteAssignPacketTagOfStore hstore)
    (bytesStoreLiteSetPacketLengthAfterWriteOfLength hlen)

theorem bytesStoreLiteSetPacketBodyRevertsOfWrite
    {evm : EVM.State} {value : ByteArray} {tag : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwrite : writeStorage? bytesStoreLiteConfig evm
      { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
        .revert) :
    ExecTransitionBody bytesStoreLiteConfig bytesStoreLiteContract evm
      (bytesStoreLiteSetPacketLocalsOf value tag)
      setPacketTransition.body .reverted := by
  let solm0 : Frame := bytesStoreLiteSetPacketFrameOf value tag
  have hvalue : evalExpr? bytesStoreLiteConfig solm0 evm (.var "value") =
      .ok (.bytes value) := by
    have hlookup :
        (bytesStoreLiteSetPacketLocalsOf value tag).get? "value" =
          some (.bytes value) := by
      unfold bytesStoreLiteSetPacketLocalsOf
      rw [store_get_ne]
      · exact store_get_self (∅ : Store) "value" (.bytes value)
      · native_decide
    rw [Std.HashMap.get?_eq_getElem?] at hlookup
    rw [evalExpr?]
    simp [solm0, bytesStoreLiteSetPacketFrameOf, hlookup, EvalResult.ofOption]
  have hresolve := bytesStoreLiteSetPacketResolveData evm value tag
  have hassign :
      assignStorageRef? bytesStoreLiteConfig solm0 evm .storage packetDataRef (.bytes value) =
        .revert := by
    exact assignStorageRef_storage_bytes_revert_of_write
      (by simpa [solm0] using hresolve) hwrite
  exact ExecFuncBody.execBlockRevert <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) <|
      ExecBlock.consRevert (ExecStmt.assignStoreRevert hvalue hassign)

theorem bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {value o : ByteArray} {tag : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmData evmTag : EVM.State}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hret : RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc o)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf value tag))
    (hwrite : writeStorage? bytesStoreLiteConfig
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { base := "packet", steps := [.field "data"] } .bytes (.bytes value) = .ok evmData)
    (hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evmTag
      { base := "packet", steps := [.field "data"] } = .ok value.size)
    (hCreated : acc.1 = evmTag.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evmTag.accountMap)
    (henc : returnEquiv o (some (.int value.size)) setPacketTransition.returnType) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody := bytesStoreLiteSetPacketBodyReturnsOfWriteAndTagStore
    (evm := evmSolm0) (evmData := evmData) (evmTag := evmTag)
    (value := value) (tag := tag)
    (by simp [evmSolm0, initState]; exact hwv)
    (by simpa [evmSolm0] using hwrite)
    hstore hlen
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccounts henc

theorem bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquivLength
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {value o : ByteArray} {tag : UInt256} {n : Nat}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {evmData evmTag : EVM.State}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hret : RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) acc o)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf value tag))
    (hwrite : writeStorage? bytesStoreLiteConfig
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { base := "packet", steps := [.field "data"] } .bytes (.bytes value) = .ok evmData)
    (hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag)
    (hlen : readStorageBytesLength? bytesStoreLiteConfig evmTag
      { base := "packet", steps := [.field "data"] } = .ok n)
    (hCreated : acc.1 = evmTag.createdAccounts)
    (hAccounts : accountMapEquiv acc.2 evmTag.accountMap)
    (henc : returnEquiv o (some (.int n)) setPacketTransition.returnType) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody := bytesStoreLiteSetPacketBodyReturnsOfWriteAndTagStoreLength
    (evm := evmSolm0) (evmData := evmData) (evmTag := evmTag)
    (value := value) (tag := tag) (n := n)
    (by simp [evmSolm0, initState]; exact hwv)
    (by simpa [evmSolm0] using hwrite)
    hstore hlen
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hd hdec hbody
    hCreated hAccounts henc

theorem bytesStoreLiteSetPacketRuntimeOfWriteRevert
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {value : ByteArray} {tag : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hrev : RDrev bytesStoreLiteBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf value tag))
    (hwrite : writeStorage? bytesStoreLiteConfig
      (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
      { base := "packet", steps := [.field "data"] } .bytes (.bytes value) = .revert) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody := bytesStoreLiteSetPacketBodyRevertsOfWrite
    (evm := evmSolm0) (value := value) (tag := tag)
    (by simp [evmSolm0, initState]; exact hwv)
    (by simpa [evmSolm0] using hwrite)
  exact hrev.reEquivExecutionRevert hcode hd hdec hbody

theorem bytesStoreLitePacketDataLengthBaseSlot {evm : EVM.State} :
    ∃ loc,
      bytesStoreLiteLayout { base := "packet", steps := [.field "data", .length] } evm =
        some loc ∧ loc.slot = ⟨2⟩ := by
  refine ⟨bytesLikeLengthLoc ⟨2⟩ evm, ?_, by simp⟩
  simp [bytesStoreLiteLayout]

theorem bytesStoreLiteWritePacketDataShortPacked {evm : EVM.State}
    {header len : UInt256} {value : ByteArray}
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = header)
    (hpacked : checkBytesPacked ⟨2⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm { base := "packet", steps := [.field "data"] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
          (solidityShortBytesWord value)) := by
  exact writeSolidityBytesShortPacked
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "packet", steps := [.field "data"] })
    (baseSlot := ⟨2⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreLitePacketDataLengthBaseSlot hvalueSize hload hpacked hflag hlen hvalid

theorem bytesStoreLiteWritePacketDataShortFromLongPrepared {evm : EVM.State}
    {header len : UInt256} {value : ByteArray}
    (hvalueSize : value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm { base := "packet", steps := [.field "data"] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (clearSolidityBytesDataWordsFrom evm ⟨2⟩ 0 ((len.toNat + 31) / 32))
          (clearSolidityBytesDataWordsFrom evm ⟨2⟩ 0
            ((len.toNat + 31) / 32)).executionEnv.codeOwner
          ⟨2⟩ (solidityShortBytesWord value)) := by
  exact writeSolidityBytesShortFromLongPrepared
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "packet", steps := [.field "data"] })
    (baseSlot := ⟨2⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreLitePacketDataLengthBaseSlot hvalueSize hload hflag hlen hvalid

theorem bytesStoreLiteWritePacketDataLongPacked {evm : EVM.State}
    {header len : UInt256} {value : ByteArray}
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = header)
    (hpacked : checkBytesPacked ⟨2⟩ evm = true)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hlen : len = UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm { base := "packet", steps := [.field "data"] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evm ⟨2⟩ value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evm ⟨2⟩ value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          ⟨2⟩ (solidityBytesHeaderWord value.size)) := by
  exact writeSolidityBytesLongPacked
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "packet", steps := [.field "data"] })
    (baseSlot := ⟨2⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreLitePacketDataLengthBaseSlot hvalueSize hload hpacked hflag hlen hvalid

theorem bytesStoreLiteWritePacketDataLongFromLongPrepared {evm : EVM.State}
    {header len : UInt256} {value : ByteArray}
    (hvalueSize : ¬ value.size < 32)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩) (UInt256.lt len ⟨32⟩) ≠ ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm { base := "packet", steps := [.field "data"] }
      .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom
            (clearSolidityBytesDataWordsFrom evm ⟨2⟩
              (solidityBytesDataWordCount value.size)
              (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
            ⟨2⟩ value 0 (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom
              (clearSolidityBytesDataWordsFrom evm ⟨2⟩
                (solidityBytesDataWordCount value.size)
                (solidityBytesDataWordCount len.toNat - solidityBytesDataWordCount value.size))
              ⟨2⟩ value 0 (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          ⟨2⟩ (solidityBytesHeaderWord value.size)) := by
  exact writeSolidityBytesLongFromLongPrepared
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "packet", steps := [.field "data"] })
    (baseSlot := ⟨2⟩) (header := header) (len := len) (value := value)
    rfl bytesStoreLitePacketDataLengthBaseSlot hvalueSize hload hflag hlen hvalid

theorem bytesStoreLiteWritePacketDataMalformedLong {evm : EVM.State}
    {header : UInt256} {value : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm { base := "packet", steps := [.field "data"] }
      .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedLong
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "packet", steps := [.field "data"] })
    (baseSlot := ⟨2⟩) (header := header) (value := value)
    rfl bytesStoreLitePacketDataLengthBaseSlot hload hflag hbad

theorem bytesStoreLiteWritePacketDataMalformedShort {evm : EVM.State}
    {header : UInt256} {value : ByteArray}
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩ = header)
    (hflag : UInt256.land header ⟨1⟩ = ⟨0⟩)
    (hbad : UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    writeStorage? bytesStoreLiteConfig evm { base := "packet", steps := [.field "data"] }
      .bytes (.bytes value) = .revert := by
  exact writeSolidityBytesMalformedShort
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (evm := evm) (er := { base := "packet", steps := [.field "data"] })
    (baseSlot := ⟨2⟩) (header := header) (value := value)
    rfl bytesStoreLitePacketDataLengthBaseSlot hload hflag hbad

theorem bytesStoreLiteWritePacketDataMalformedLongOfAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    writeStorage? bytesStoreLiteConfig evmSolm0
      { base := "packet", steps := [.field "data"] } .bytes (.bytes value) = .revert := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite := bytesStoreLiteWritePacketDataMalformedLong
    (evm := evmSolm0) (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
    (value := value) hload hflag hbad
  simpa [evmSolm0] using hwrite

theorem bytesStoreLiteWritePacketDataMalformedShortOfAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    writeStorage? bytesStoreLiteConfig evmSolm0
      { base := "packet", steps := [.field "data"] } .bytes (.bytes value) = .revert := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite := bytesStoreLiteWritePacketDataMalformedShort
    (evm := evmSolm0) (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
    (value := value) hload hflag hbad
  simpa [evmSolm0] using hwrite

theorem bytesStoreLiteWritePacketDataEmptyShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hflag : UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ ⟨0⟩
    writeStorage? bytesStoreLiteConfig evmSolm0
      { base := "packet", steps := [.field "data"] } .bytes (.bytes ByteArray.empty) =
        .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked ⟨2⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite := bytesStoreLiteWritePacketDataShortPacked (evm := evmSolm0)
    (header := bytesStoreLitePacketLengthHeaderWord σ_evm I) (len := oldLen)
    (value := ByteArray.empty)
    (by decide) hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, hshortEmpty] using hwrite

theorem bytesStoreLiteWritePacketDataDecodedShortPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g len : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hshort : len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let value := BytesStoreLiteCore.setDecodedValueBytes I
    let evmSolm1 :=
      Solm.EVM.storageStore evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩
        (solidityShortBytesWord value)
    writeStorage? bytesStoreLiteConfig evmSolm0
      { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
        .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let value := BytesStoreLiteCore.setDecodedValueBytes I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize : value.size < 32 := by
    dsimp [value]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayload]
    rw [← hlenAbi]
    exact hshort
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked ⟨2⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite := bytesStoreLiteWritePacketDataShortPacked (evm := evmSolm0)
    (header := bytesStoreLitePacketLengthHeaderWord σ_evm I) (len := oldLen)
    (value := value)
    hvalueSize hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, value] using hwrite

theorem bytesStoreLiteWritePacketDataDecodedShortFromLongPrepared
    {cA gh bl σ_evm σ_solm σ₀ A I} {g len : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hshort : len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let oldLen : UInt256 := UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩
    let value := BytesStoreLiteCore.setDecodedValueBytes I
    writeStorage? bytesStoreLiteConfig evmSolm0
      { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (clearSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ 0 ((oldLen.toNat + 31) / 32))
          (clearSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ 0
            ((oldLen.toNat + 31) / 32)).executionEnv.codeOwner
          ⟨2⟩ (solidityShortBytesWord value)) := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let oldLen : UInt256 := UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩
  let value := BytesStoreLiteCore.setDecodedValueBytes I
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hvalueSize : value.size < 32 := by
    dsimp [value]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayload]
    rw [← hlenAbi]
    exact hshort
  have hwrite := bytesStoreLiteWritePacketDataShortFromLongPrepared (evm := evmSolm0)
    (header := bytesStoreLitePacketLengthHeaderWord σ_evm I) (len := oldLen)
    (value := value)
    hvalueSize hload hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, oldLen, value] using hwrite

theorem bytesStoreLiteWritePacketDataDecodedLongPacked
    {cA gh bl σ_evm σ_solm σ₀ A I} {g len : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hlong : ¬ len.toNat < 32)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let value := BytesStoreLiteCore.setDecodedValueBytes I
    writeStorage? bytesStoreLiteConfig evmSolm0
      { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
        .ok (Solm.EVM.storageStore
          (writeSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ value 0
            (solidityBytesDataWordCount value.size))
          (writeSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ value 0
            (solidityBytesDataWordCount value.size)).executionEnv.codeOwner
          ⟨2⟩ (solidityBytesHeaderWord value.size)) := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let value := BytesStoreLiteCore.setDecodedValueBytes I
  let oldLen : UInt256 :=
    UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩) ⟨127⟩
  have hvalueSize : ¬ value.size < 32 := by
    rw [show value.size = len.toNat by
      dsimp [value]
      rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayload]
      rw [← hlenAbi]]
    exact hlong
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hpacked : checkBytesPacked ⟨2⟩ evmSolm0 = true :=
    checkBytesPacked_of_storageLoad_land_one_zero hload hflag
  have hwrite := bytesStoreLiteWritePacketDataLongPacked (evm := evmSolm0)
    (header := bytesStoreLitePacketLengthHeaderWord σ_evm I) (len := oldLen)
    (value := value)
    hvalueSize hload hpacked hflag rfl (by simpa [oldLen] using hvalid)
  simpa [evmSolm0, value] using hwrite

theorem bytesStoreLiteWritePacketDataEmptyFromLongPrepared
    {cA gh bl σ_evm σ_solm σ₀ A I} {g oldStoredLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩) :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmSolm1 := Solm.EVM.storageStore
      (clearSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ 0 ((oldStoredLen.toNat + 31) / 32))
      I.codeOwner ⟨2⟩ ⟨0⟩
    writeStorage? bytesStoreLiteConfig evmSolm0
      { base := "packet", steps := [.field "data"] } .bytes (.bytes ByteArray.empty) =
        .ok evmSolm1 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm1 := Solm.EVM.storageStore
    (clearSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ 0 ((oldStoredLen.toNat + 31) / 32))
    I.codeOwner ⟨2⟩ ⟨0⟩
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hwrite := bytesStoreLiteWritePacketDataShortFromLongPrepared (evm := evmSolm0)
    (header := bytesStoreLitePacketLengthHeaderWord σ_evm I) (len := oldStoredLen)
    (value := ByteArray.empty)
    (by decide) hload hflag holdStoredLen hvalid
  simpa [evmSolm0, evmSolm1, hshortEmpty,
    clearSolidityBytesDataWordsFrom_executionEnv] using hwrite

theorem bytesStoreLitePacketDataLengthAfterEmptyTagStore
    {cA gh bl σ_solm σ₀ A I} {g tag : UInt256} :
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmData := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨2⟩ ⟨0⟩
    let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
    readStorageBytesLength? bytesStoreLiteConfig evmTag
      { base := "packet", steps := [.field "data"] } = .ok 0 := by
  dsimp only
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmData := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨2⟩ ⟨0⟩
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  exact readStorageBytesLength?_ok_of_layout_after_storageStore_ne_zero
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (er := bytesStoreLitePacketDataRef) (evm := evmSolm0) (owner := I.codeOwner)
    (baseSlot := (⟨2⟩ : UInt256)) (tagSlot := (⟨3⟩ : UInt256)) (tag := tag)
    (by rfl) (by simp [evmSolm0, initState])
    (by simpa [evmTag, evmData] using bytesStoreLitePacketDataRef_length_slot evmTag)
    (by native_decide)

def bytesStoreLiteSetPacketShortStoredWord (I : ExecutionEnv)
    (len payloadStart : UInt256) : UInt256 :=
  UInt256.lor (UInt256.shiftLeft len ⟨1⟩)
    (UInt256.land
      (UInt256.lnot
        (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
      (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32)))

theorem bytesStoreLiteSetPacketShortStoredWord_eq_solidityShortBytesWord
    {I : ExecutionEnv} {len payloadStart : UInt256}
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    bytesStoreLiteSetPacketShortStoredWord I len payloadStart =
      solidityShortBytesWord (BytesStoreLiteCore.setDecodedValueBytes I) := by
  simpa [bytesStoreLiteSetPacketShortStoredWord] using
    bytesStoreLiteOptimizedShortStoredWord_eq_solidityShortBytesWord
      (I := I) (len := len) (payloadStart := payloadStart)
      hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayload

theorem nat_lor_mod_256_of_right_zero {a b : Nat}
    (hb : b % 256 = 0) :
    Nat.lor a b % 256 = a % 256 := by
  rw [nat_lor_comm]
  exact nat_lor_mod_256_of_left_zero hb

theorem nat_land_mod_256_of_left_zero {mask n : Nat}
    (hmask : mask % 256 = 0) :
    Nat.land mask n % 256 = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [show 256 = 2 ^ 8 by norm_num, Nat.testBit_mod_two_pow]
  by_cases hi : i < 8
  · have hbit := congrArg (fun m => m.testBit i) hmask
    change (mask % 2 ^ 8).testBit i = (0 : Nat).testBit i at hbit
    rw [Nat.testBit_mod_two_pow] at hbit
    simp [hi] at hbit
    simp [hi]
    change (mask &&& n).testBit i = false
    rw [Nat.testBit_land, hbit]
    simp
  · simp [hi]

theorem bytesStoreLiteSetPacketShortStoredMask_mod256_zero {len : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    (UInt256.lnot
      (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩))).toNat %
        256 = 0 := by
  interval_cases hnat : len.toNat
  all_goals
    have hword : len = UInt256.ofNat len.toNat := (u256_ofNat_toNat len).symm
    rw [hword, hnat]
    native_decide

theorem bytesStoreLiteSetPacketShortStoredWord_mod256 {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    (bytesStoreLiteSetPacketShortStoredWord I len payloadStart).toNat % 256 =
      (2 * len.toNat) % 256 := by
  have hmask := bytesStoreLiteSetPacketShortStoredMask_mod256_zero
    (len := len) hnz hshort
  have hright :
      (UInt256.land
        (UInt256.lnot
          (UInt256.shiftRight (UInt256.lnot ⟨0⟩) (UInt256.shiftLeft len ⟨3⟩)))
        (uInt256OfByteArray (I.calldata.readBytes payloadStart.toNat 32))).toNat %
          256 = 0 := by
    rw [u256_land_toNat, nat_mod_u256_mod_256]
    exact nat_land_mod_256_of_left_zero hmask
  have hleft :
      (UInt256.shiftLeft len ⟨1⟩).toNat % 256 = (2 * len.toNat) % 256 := by
    rw [bytesStoreLite_shiftLeft_one_eq_mul_two_of_short hshort, u256_mul_toNat,
      nat_mod_u256_mod_256]
    rw [show (⟨2⟩ : UInt256).toNat = 2 by decide]
    ring_nf
  rw [bytesStoreLiteSetPacketShortStoredWord, u256_lor_toNat, nat_mod_u256_mod_256]
  rw [nat_lor_mod_256_of_right_zero hright, hleft]

theorem bytesStoreLiteSetPacketShortStoredWord_flag_eq {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    UInt256.land (bytesStoreLiteSetPacketShortStoredWord I len payloadStart) ⟨1⟩ =
      ⟨0⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat]
  have hmod := bytesStoreLiteSetPacketShortStoredWord_mod256
    (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have hleft :
      (bytesStoreLiteSetPacketShortStoredWord I len payloadStart).toNat % 2 =
        ((bytesStoreLiteSetPacketShortStoredWord I len payloadStart).toNat % 256) % 2 := by
    rw [Nat.mod_mod_of_dvd]
    norm_num
  rw [hleft, hmod]
  have hlt : 2 * len.toNat < 256 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  rw [show (⟨0⟩ : UInt256).toNat = 0 by decide]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_right 2 len.toNat)

theorem bytesStoreLiteSetPacketShortStoredWord_shortLen_eq {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    UInt256.land
        (UInt256.div (bytesStoreLiteSetPacketShortStoredWord I len payloadStart) ⟨2⟩)
        ⟨127⟩ = len := by
  apply u256_inj
  rw [bytesStoreLiteShortLenBits_toNat]
  have hmod := bytesStoreLiteSetPacketShortStoredWord_mod256
    (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  rw [hmod]
  have hlt : 2 * len.toNat < 256 := by omega
  rw [Nat.mod_eq_of_lt hlt]
  rw [Nat.mul_div_right _ (by decide : 0 < 2)]

theorem bytesStoreLiteSetPacketShortStoredWord_beq_zero_false {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hnz : len.toNat ≠ 0) (hshort : len.toNat < 32) :
    (bytesStoreLiteSetPacketShortStoredWord I len payloadStart == (default : UInt256)) =
      false := by
  apply beq_false_of_ne
  intro hzero
  have hlen := bytesStoreLiteSetPacketShortStoredWord_shortLen_eq
    (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  rw [hzero] at hlen
  have hlenZero : len.toNat = 0 := by
    rw [← hlen]
    native_decide
  exact hnz hlenZero

theorem bytesStoreLiteSetPacketDataShortPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {storedWord : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hstored : storedWord = solidityShortBytesWord value) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner σ_evm ⟨2⟩ storedWord)
      (Solm.EVM.storageStore
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        I.codeOwner ⟨2⟩ (solidityShortBytesWord value)).accountMap := by
  simpa [initState, hstored] using
    accountMapEquiv_storageStore_initState_codeOwner
      (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hAccounts ⟨2⟩
      (solidityShortBytesWord value)

theorem bytesStoreLiteSetPacketDataShortFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {oldLen storedWord : UInt256} {value : ByteArray}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hstored : storedWord = solidityShortBytesWord value)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        ⟨2⟩ storedWord)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ⟨2⟩ 0 ((oldLen.toNat + 31) / 32))
        I.codeOwner ⟨2⟩ (solidityShortBytesWord value)).accountMap := by
  exact accountMapEquiv_setBytesShortFromLongPostAccountMapEquiv
    (baseSlot := (⟨2⟩ : UInt256))
    (oldLen := oldLen) (storedWord := storedWord) (value := value)
    hAccounts hstored holdLenLt

theorem bytesStoreLiteSetPacketDataEmptyFromLongPostAccountMapEquiv
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {oldLen : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (holdLenLt : oldLen.toNat < 2 ^ 255) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ_evm
          ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
        ⟨2⟩ ⟨0⟩)
      (Solm.EVM.storageStore
        (clearSolidityBytesDataWordsFrom
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          ⟨2⟩ 0 ((oldLen.toNat + 31) / 32))
        I.codeOwner ⟨2⟩ ⟨0⟩).accountMap := by
  have hshortEmpty : solidityShortBytesWord ByteArray.empty = ⟨0⟩ := by
    rw [solidityShortBytesWord, empty_readWithPadding_word_zero]
    rfl
  have hstored : (⟨0⟩ : UInt256) = solidityShortBytesWord ByteArray.empty := hshortEmpty.symm
  simpa [initState, hshortEmpty] using
    bytesStoreLiteSetPacketDataShortFromLongPostAccountMapEquiv
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (oldLen := oldLen) (storedWord := (⟨0⟩ : UInt256))
      (value := ByteArray.empty) hAccounts hstored holdLenLt

theorem bytesStoreLitePacketDataLengthAfterShortTagStoreOfState
    {evm : EVM.State} {I : ExecutionEnv} {tag len payloadStart : UInt256}
    {acc : Account}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hacc : evm.accountMap.find? I.codeOwner = some acc)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let storedWord := bytesStoreLiteSetPacketShortStoredWord I len payloadStart
    let evmData := Solm.EVM.storageStore evm I.codeOwner ⟨2⟩ storedWord
    let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
    readStorageBytesLength? bytesStoreLiteConfig evmTag
      { base := "packet", steps := [.field "data"] } = .ok len.toNat := by
  dsimp only
  let storedWord := bytesStoreLiteSetPacketShortStoredWord I len payloadStart
  let evmData := Solm.EVM.storageStore evm I.codeOwner ⟨2⟩ storedWord
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  have hdecode :
      solidityDecodeBytesLengthHeader storedWord = .ok len.toNat := by
    exact solidityDecodeBytesLengthHeader_short_valid
      (header := storedWord) (len := len)
      (by
        simpa [storedWord] using
          bytesStoreLiteSetPacketShortStoredWord_flag_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        symm
        simpa [storedWord] using
          bytesStoreLiteSetPacketShortStoredWord_shortLen_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        rw [show UInt256.lt len ⟨32⟩ = ⟨1⟩ by
          exact ult_one (by
            rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
            exact hshort)]
        have hflag :
            UInt256.land storedWord ⟨1⟩ = ⟨0⟩ := by
          simpa [storedWord] using
            bytesStoreLiteSetPacketShortStoredWord_flag_eq
              (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
        rw [hflag]
        native_decide)
  exact readStorageBytesLength?_ok_of_layout_after_storageStore_ne_present
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (er := bytesStoreLitePacketDataRef) (evm := evm) (owner := I.codeOwner)
    (baseSlot := (⟨2⟩ : UInt256)) (header := storedWord)
    (tagSlot := (⟨3⟩ : UInt256)) (tag := tag) (len := len.toNat)
    (by rfl) howner
    (by simpa [evmTag, evmData] using bytesStoreLitePacketDataRef_length_slot evmTag)
    hacc (by native_decide) hdecode

theorem bytesStoreLitePacketDataLengthAfterEmptyTagStoreOfState
    {evm : EVM.State} {I : ExecutionEnv} {tag : UInt256}
    (howner : evm.executionEnv.codeOwner = I.codeOwner) :
    let evmData := Solm.EVM.storageStore evm I.codeOwner ⟨2⟩ ⟨0⟩
    let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
    readStorageBytesLength? bytesStoreLiteConfig evmTag
      { base := "packet", steps := [.field "data"] } = .ok 0 := by
  dsimp only
  let evmData := Solm.EVM.storageStore evm I.codeOwner ⟨2⟩ ⟨0⟩
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  exact readStorageBytesLength?_ok_of_layout_after_storageStore_ne_zero
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (er := bytesStoreLitePacketDataRef) (evm := evm) (owner := I.codeOwner)
    (baseSlot := (⟨2⟩ : UInt256)) (tagSlot := (⟨3⟩ : UInt256)) (tag := tag)
    (by rfl) howner
    (by simpa [evmTag, evmData] using bytesStoreLitePacketDataRef_length_slot evmTag)
    (by native_decide)

theorem bytesStoreLitePacketDataLengthAfterLongTagStoreOfState
    {evm : EVM.State} {I : ExecutionEnv} {tag len header : UInt256} {acc : Account}
    (howner : evm.executionEnv.codeOwner = I.codeOwner)
    (hacc : evm.accountMap.find? I.codeOwner = some acc)
    (hflag : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (hlen : len = UInt256.div header ⟨2⟩)
    (hvalid : UInt256.sub (UInt256.land header ⟨1⟩)
      (UInt256.lt (UInt256.div header ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩) :
    let evmData := Solm.EVM.storageStore evm I.codeOwner ⟨2⟩ header
    let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
    readStorageBytesLength? bytesStoreLiteConfig evmTag
      { base := "packet", steps := [.field "data"] } = .ok len.toNat := by
  dsimp only
  let evmData := Solm.EVM.storageStore evm I.codeOwner ⟨2⟩ header
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  have hdecode :
      solidityDecodeBytesLengthHeader header = .ok len.toNat := by
    exact solidityDecodeBytesLengthHeader_long_valid
      (header := header) (len := len) hflag hlen (by simpa [← hlen] using hvalid)
  exact readStorageBytesLength?_ok_of_layout_after_storageStore_ne_present
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (er := bytesStoreLitePacketDataRef) (evm := evm) (owner := I.codeOwner)
    (baseSlot := (⟨2⟩ : UInt256)) (header := header)
    (tagSlot := (⟨3⟩ : UInt256)) (tag := tag) (len := len.toNat)
    (by rfl) howner
    (by simpa [evmTag, evmData] using bytesStoreLitePacketDataRef_length_slot evmTag)
    hacc (by native_decide) hdecode

theorem bytesStoreLitePacketDataLengthAfterShortTagStore
    {cA gh bl σ_solm σ₀ A I} {g tag len payloadStart : UInt256}
    {acc : Account}
    (hacc : σ_solm.find? I.codeOwner = some acc)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let storedWord := bytesStoreLiteSetPacketShortStoredWord I len payloadStart
    let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    let evmData := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨2⟩ storedWord
    let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
    readStorageBytesLength? bytesStoreLiteConfig evmTag
      { base := "packet", steps := [.field "data"] } = .ok len.toNat := by
  dsimp only
  let storedWord := bytesStoreLiteSetPacketShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmData := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨2⟩ storedWord
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  have hdecode :
      solidityDecodeBytesLengthHeader storedWord = .ok len.toNat := by
    exact solidityDecodeBytesLengthHeader_short_valid
      (header := storedWord) (len := len)
      (by
        simpa [storedWord] using
          bytesStoreLiteSetPacketShortStoredWord_flag_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        symm
        simpa [storedWord] using
          bytesStoreLiteSetPacketShortStoredWord_shortLen_eq
            (I := I) (len := len) (payloadStart := payloadStart) hnz hshort)
      (by
        rw [show UInt256.lt len ⟨32⟩ = ⟨1⟩ by
          exact ult_one (by
            rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
            exact hshort)]
        have hflag :
            UInt256.land storedWord ⟨1⟩ = ⟨0⟩ := by
          simpa [storedWord] using
            bytesStoreLiteSetPacketShortStoredWord_flag_eq
              (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
        rw [hflag]
        native_decide)
  have hacc0 : evmSolm0.accountMap.find? I.codeOwner = some acc := by
    simpa [evmSolm0, initState] using hacc
  exact readStorageBytesLength?_ok_of_layout_after_storageStore_ne_present
    (cfg := bytesStoreLiteConfig) (layout := bytesStoreLiteLayout)
    (er := bytesStoreLitePacketDataRef) (evm := evmSolm0) (owner := I.codeOwner)
    (baseSlot := (⟨2⟩ : UInt256)) (header := storedWord)
    (tagSlot := (⟨3⟩ : UInt256)) (tag := tag) (len := len.toNat)
    (by rfl) (by simp [evmSolm0, initState])
    (by simpa [evmTag, evmData] using bytesStoreLitePacketDataRef_length_slot evmTag)
    hacc0 (by native_decide) hdecode

theorem bytesStoreLiteSetPacketLongHeader_toNat {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    (len * (⟨2⟩ : UInt256) + ⟨1⟩).toNat = len.toNat * 2 + 1 := by
  rw [uadd_toNat]
  rw [umul_toNat (a := len) (b := (⟨2⟩ : UInt256)) (by
    have hmax : ABI.solcMaxU64 * 2 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    rw [show (⟨2⟩ : UInt256).toNat = 2 from by decide]
    omega)]
  rw [show (⟨2⟩ : UInt256).toNat = 2 from by decide,
    show (⟨1⟩ : UInt256).toNat = 1 from by decide]
  have hwordLt : len.toNat * 2 + 1 < UInt256.size := by
    have hmax : ABI.solcMaxU64 * 2 + 1 < UInt256.size := by
      norm_num [ABI.solcMaxU64, UInt256.size]
    omega
  rw [Nat.mod_eq_of_lt hwordLt]

theorem bytesStoreLiteSetPacketLongHeader_flag_eq_one {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    UInt256.land (len * (⟨2⟩ : UInt256) + ⟨1⟩) ⟨1⟩ = ⟨1⟩ := by
  apply u256_inj
  rw [uInt256_land_one_toNat,
    bytesStoreLiteSetPacketLongHeader_toNat (len := len) hlenMax]
  rw [show (⟨1⟩ : UInt256).toNat = 1 from by decide]
  omega

theorem bytesStoreLiteSetPacketLongHeader_flag_ne_zero {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    UInt256.land (len * (⟨2⟩ : UInt256) + ⟨1⟩) ⟨1⟩ ≠ ⟨0⟩ := by
  rw [bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax]
  native_decide

theorem bytesStoreLiteSetPacketLongHeader_div_two {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) :
    UInt256.div (len * (⟨2⟩ : UInt256) + ⟨1⟩) ⟨2⟩ = len := by
  apply u256_inj
  rw [udiv_toNat, bytesStoreLiteSetPacketLongHeader_toNat (len := len) hlenMax]
  rw [show (⟨2⟩ : UInt256).toNat = 2 from by decide]
  omega

theorem bytesStoreLiteSetPacketLongHeader_valid {len : UInt256}
    (hlenMax : len.toNat ≤ ABI.solcMaxU64) (hlong : ¬ len.toNat < 32) :
    UInt256.sub (UInt256.land (len * (⟨2⟩ : UInt256) + ⟨1⟩) ⟨1⟩)
      (UInt256.lt (UInt256.div (len * (⟨2⟩ : UInt256) + ⟨1⟩) ⟨2⟩) ⟨32⟩) ≠
        ⟨0⟩ := by
  rw [bytesStoreLiteSetPacketLongHeader_flag_eq_one (len := len) hlenMax,
    bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax]
  have hlt : UInt256.lt len ⟨32⟩ = ⟨0⟩ := by
    exact ult_zero (by
      rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
      exact Nat.le_of_not_gt hlong)
  rw [hlt]
  native_decide

theorem bytesStoreLiteReachSetPacketDecoder {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2059⟩
      [⟨4⟩, UInt256.ofNat I.calldata.size, ⟨352⟩, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hreach⟩ := bytesStoreLiteReachSetPacket
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz hsize hsel
  exact ⟨_, _, by
    simpa [bytesStoreLiteSetPacketEntryPc] using
      (evm_run hreach with [
        jumpdest, push2 ⟨263⟩, push2 ⟨352⟩, calldatasize, push1 ⟨4⟩,
        push2 ⟨2059⟩, jump (by native_decide)])⟩

theorem bytesStoreLiteX_setPacketDecodeShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetPacketDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckShort_4_64 hsz4 hshort hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2077⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setPacketDecodeHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hbig : 2 ^ 255 + 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetPacketDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv hsz4 hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ :=
    solcDecodeLenCheckHuge_4_64 hbig hsize
  exact evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2077⟩, jumpiNT (by rw [hslt]; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setPacketDecodeOffsetHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetPacketDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨1⟩ := by
    exact ugt_one (by simpa [ABI.solcMaxU64] using hoff)
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hgt
  have rd2077 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2077⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload]
  have rd2089 := RD.pushConst rd2077 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  exact evm_run rd2089 with [
    dup2, gt, iszero, push2 ⟨2099⟩,
    jumpiNT (by rw [hgt']; decide),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setPacketDecodeLengthShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetPacketDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    by_cases hsizeSign : I.calldata.size < 2 ^ 255
    · apply slt_lit_zero hsizeSign
      · rw [BytesStoreLiteCore.setStartPlus31_toNat I.calldata hoffMax]
        omega
      · rw [BytesStoreLiteCore.setStartPlus31_toNat I.calldata hoffMax]
        have hle : (calldataWord I.calldata 4).toNat ≤ 18446744073709551615 := by
          simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
        omega
    · apply BytesStoreLiteCore.slt_zero_of_left_low_right_high
      · rw [BytesStoreLiteCore.setStartPlus31_toNat I.calldata hoffMax]
        have hle : (calldataWord I.calldata 4).toNat ≤ 18446744073709551615 := by
          simpa [ABI.solcMaxU64] using Nat.le_of_not_gt hoffMax
        omega
      · rw [ulit_toNat' I.calldata.size hsize]
        omega
  have rd2077 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2077⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload]
  have rd2089 := RD.pushConst rd2077 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2099 := evm_run rd2089 with [
    dup2, gt, iszero, push2 ⟨2099⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2099 with [
    jumpdest, push2 ⟨2111⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  exact evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiNT (by simpa [calldataWord] using hstart),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setPacketDecodeTotalHigh {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsizeHigh : ¬ I.calldata.size < 2 ^ 255) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetPacketDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstartPlus31Small :
      4 + (calldataWord I.calldata 4).toNat + 31 < 2 ^ 255 := by
    have hmax : ABI.solcMaxU64 + 35 < 2 ^ 255 := by
      norm_num [ABI.solcMaxU64]
    have hle : (calldataWord I.calldata 4).toNat ≤ ABI.solcMaxU64 :=
      Nat.le_of_not_gt hoffMax
    omega
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    apply BytesStoreLiteCore.slt_zero_of_left_low_right_high
    · rw [BytesStoreLiteCore.setStartPlus31_toNat I.calldata hoffMax]
      exact hstartPlus31Small
    · rw [ulit_toNat' I.calldata.size hsize]
      omega
  have rd2077 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2077⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload]
  have rd2089 := RD.pushConst rd2077 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2099 := evm_run rd2089 with [
    dup2, gt, iszero, push2 ⟨2099⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2099 with [
    jumpdest, push2 ⟨2111⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
    jump (by native_decide)]
  exact evm_run rd1814 with [
    jumpdest, push0, push0, dup4, push1 ⟨31⟩, dup5, add, slt, push2 ⟨1830⟩,
    jumpiNT (by simpa [calldataWord] using hstart),
    raw revertStub (by native_decide) (by native_decide) (by native_decide) (by evm_ov)]

theorem bytesStoreLiteX_setPacketDecodeLengthHuge {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨1⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetPacketDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨1⟩ := by
    simpa [calldataWord] using hlenMax
  have rd2077 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2077⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload]
  have rd2089 := RD.pushConst rd2077 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2099 := evm_run rd2089 with [
    dup2, gt, iszero, push2 ⟨2099⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2099 with [
    jumpdest, push2 ⟨2111⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
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

theorem bytesStoreLiteX_setPacketDecodePayloadShort {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetPacketDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hlenMax
  have hpayload' :
      UInt256.gt
        (((((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)) +
          uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hpayload
  have rd2077 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2077⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload]
  have rd2089 := RD.pushConst rd2077 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2099 := evm_run rd2089 with [
    dup2, gt, iszero, push2 ⟨2099⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2099 with [
    jumpdest, push2 ⟨2111⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
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

theorem bytesStoreLiteX_setPacketDecodeValid {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = bytesStoreLiteBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩)
    (hlenMax :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩)
    (hpayload :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [bytesStoreLiteSetPacketTagWord I,
        uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32),
        (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩),
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdec⟩ := bytesStoreLiteReachSetPacketDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hcode hwv (by omega) hsize hsel
  have hslt :
      UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨0⟩ :=
    solcDecodeLenCheckOk_4_64 hsz68 hhi hsize
  have hgt :
      UInt256.gt (calldataWord I.calldata 4) ⟨18446744073709551615⟩ = ⟨0⟩ := by
    apply ugt_zero
    rw [show (⟨18446744073709551615⟩ : UInt256).toNat = ABI.solcMaxU64 by native_decide]
    exact Nat.le_of_not_gt hoffMax
  have hgt' :
      UInt256.gt
          (uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hgt
  have hstart' :
      UInt256.slt
          (((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32) +
            ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ := by
    simpa [calldataWord] using hstart
  have hlenMax' :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32))
          ⟨18446744073709551615⟩ = ⟨0⟩ := by
    simpa [calldataWord] using hlenMax
  have hpayload' :
      UInt256.gt
        (((((⟨4⟩ : UInt256) +
              uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)) +
          uInt256OfByteArray
            (I.calldata.readBytes
              (((⟨4⟩ : UInt256) +
                uInt256OfByteArray (I.calldata.readBytes (⟨4⟩ : UInt256).toNat 32)).toNat)
              32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩ := by
    simpa [calldataWord] using hpayload
  have rd2077 := evm_run hdec with [
    jumpdest, push0, push0, push0, push1 ⟨64⟩, dup5, dup7, sub, slt, iszero,
    push2 ⟨2077⟩, jumpiT (by rw [hslt]; decide) (by native_decide),
    jumpdest, dup4, calldataload]
  have rd2089 := RD.pushConst rd2077 ⟨18446744073709551615⟩
    (width := 8) (op := .PUSH8) (by native_decide) (by native_decide) (by evm_ov)
  have rd2099 := evm_run rd2089 with [
    dup2, gt, iszero, push2 ⟨2099⟩,
    jumpiT (by rw [hgt']; decide) (by native_decide)]
  have rd1814 := evm_run rd2099 with [
    jumpdest, push2 ⟨2111⟩, dup7, dup3, dup8, add, push2 ⟨1814⟩,
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
  have rd2111 := evm_run rd1876 with [
    jumpdest, swap3, pop, swap3, swap1, pop, jump (by native_decide)]
  exact ⟨_, _, by
    simpa [calldataWord, bytesStoreLiteSetPacketTagWord] using
      (evm_run rd2111 with [
        jumpdest, swap1, swap8, swap1, swap7, pop, push1 ⟨32⟩, swap6, swap1,
        swap6, add, calldataload, swap5, swap4, pop, pop, pop, pop,
        jump (by native_decide),
        jumpdest, push2 ⟨969⟩, jump (by native_decide)])⟩

theorem bytesStoreLiteX_setPacketReachWriteHelper {cA gh bl σ σ₀ A I} {g : Sat256}
    {tag len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2599⟩
      [⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩, tag, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, rd969⟩ := hreach
  exact ⟨_, _, evm_run rd969 with [
    jumpdest, push0, push1 ⟨2⟩, push2 ⟨983⟩, dup5, dup7, dup4,
    push2 ⟨2599⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setPacketReachWriteHeaderDecoder {cA gh bl σ σ₀ A I}
    {g : Sat256} {tag len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2246⟩
      ((σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ::
        ⟨2637⟩ :: len :: ⟨2643⟩ :: ⟨2⟩ :: payloadStart :: len :: ⟨983⟩ ::
        ⟨2⟩ :: ⟨0⟩ :: tag :: len :: payloadStart :: ⟨263⟩ ::
        bytesStoreLiteSelWord I :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hhelper := bytesStoreLiteX_setPacketReachWriteHelper
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart) hreach
  exact bytesStoreLiteX_writeBytesHelperReachHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨2⟩) (payloadStart := payloadStart)
    (len := len) (ret := ⟨983⟩) (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I]) (mem := solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty) hhelper hlenMax
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketLongMalformedHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {tag len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ ≠ ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩)
          ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreLiteX_setPacketReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hreach hlenMax
  exact bytesStoreLiteX_bytesLengthDecoderLongMalformedMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (header := bytesStoreLitePacketLengthHeaderWord σ I) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, ⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩,
      tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem)
    hdecoder hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketShortMalformedHeader {cA gh bl σ σ₀ A I}
    {g : Sat256} {tag len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩ = ⟨0⟩)
    (hbad :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ I) ⟨2⟩)
            ⟨127⟩) ⟨32⟩) = ⟨0⟩) :
    RDrev bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hdecoder := bytesStoreLiteX_setPacketReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hreach hlenMax
  exact bytesStoreLiteX_bytesLengthDecoderShortMalformedMem
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)
    (header := bytesStoreLitePacketLengthHeaderWord σ I) (ret := ⟨2637⟩)
    (rest := [len, ⟨2643⟩, ⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩,
      tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem)
    hdecoder hflag hbad
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketShortHeaderReachWriteBranch {cA gh bl σ σ₀ A I}
    {g : Sat256} {tag len payloadStart : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                (σ.find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩, tag, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hhelper := bytesStoreLiteX_setPacketReachWriteHelper
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart) hreach
  exact bytesStoreLiteX_writeBytesHelperShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨2⟩) (payloadStart := payloadStart)
    (len := len) (ret := ⟨983⟩) (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I]) (mem := solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hhelper hlenMax hflag hvalid
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_writeBytesNewEmptyWriteHeaderGeneric {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2669⟩
      ((⟨0⟩ : UInt256) :: UInt256.gt len ⟨31⟩ :: ⟨0⟩ :: slot :: payloadStart ::
        len :: ret :: tail)
      mem aw rdata (cA, σ) k C)
    (hlenZero : len = ⟨0⟩)
    (hov : tail.length + 12 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2688⟩
      (UInt256.gt len ⟨31⟩ :: ⟨0⟩ :: slot :: payloadStart :: len :: ret :: tail)
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ slot ⟨0⟩) k C := by
  obtain ⟨_, _, rd2669⟩ := hreach
  have rd2687pre := evm_run rd2669 with [
    jumpdest, push0, not, push1 ⟨3⟩, dup8, swap1, shl, shr, not, and,
    push1 ⟨1⟩, dup7, swap1, shl, lor, dup4]
  obtain ⟨_, _, rd2688₀⟩ := rd2687pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact ⟨_, _, by simpa [initState, hlenZero] using rd2688₀⟩

theorem bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric {cA gh bl σinit σ σ₀ A I}
    {g : Sat256} {slot payloadStart len ret : UInt256} {tail : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2688⟩
      (UInt256.gt len ⟨31⟩ :: ⟨0⟩ :: slot :: payloadStart :: len :: ret :: tail)
      mem aw rdata (cA, σ) k C)
    (hret : (D_J bytesStoreLiteBytecode 0).contains ret = true)
    (hov : tail.length + 7 ≤ 1024) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ret tail mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd2688⟩ := hreach
  have rd2572 := evm_run rd2688 with [push2 ⟨2572⟩, jump (by native_decide)]
  exact ⟨_, _, evm_run rd2572 with [
    jumpdest, pop, pop, pop, pop, pop,
    raw jump (by native_decide) hret (by omega)]⟩

theorem bytesStoreLiteX_setPacketEmptyWriteReturnsToBody {cA gh bl σ σ₀ A I}
    {g : Sat256} {tag len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                (σ.find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨983⟩
      [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩ ⟨0⟩) k C := by
  have hbranch := bytesStoreLiteX_setPacketShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hreach hlenMax hflag hvalid
  have hpacked := bytesStoreLiteX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨2⟩) (payloadStart := payloadStart)
    (len := len) (ret := ⟨983⟩) (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I]) (mem := solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty) hbranch hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hwrite := bytesStoreLiteX_writeBytesNewEmptyWriteHeaderGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨2⟩) (payloadStart := payloadStart)
    (len := len) (ret := ⟨983⟩) (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I]) (mem := solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty) hperm hpacked hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨2⟩ ⟨0⟩) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨2⟩) (payloadStart := payloadStart)
    (len := len) (ret := ⟨983⟩) (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I]) (mem := solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty) hwrite
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketShortNonemptyWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                (σ.find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨983⟩
      [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (bytesStoreLiteSetPacketShortStoredWord I len payloadStart)) k C := by
  have hbranch := bytesStoreLiteX_setPacketShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hreach hlenMax hflag hvalid
  have hwrite := bytesStoreLiteX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨2⟩) (payloadStart := payloadStart)
    (len := len) (ret := ⟨983⟩) (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I]) (mem := solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty) hperm hbranch hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σ ⟨2⟩
      (bytesStoreLiteSetPacketShortStoredWord I len payloadStart))
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := ⟨2⟩)
    (payloadStart := payloadStart) (len := len) (ret := ⟨983⟩)
    (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I]) (mem := solcFreePtrMem)
    (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [bytesStoreLiteSetPacketShortStoredWord] using hwrite)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketLongNoTailWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                (σ.find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨983⟩
      [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  have hbranch := bytesStoreLiteX_setPacketShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hreach hlenMaxWord hflag hvalid
  exact bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := ⟨2⟩)
    (payloadStart := payloadStart) (len := len) (ret := ⟨983⟩)
    (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hperm hbranch hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketLongTailWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt
            (UInt256.land
              (UInt256.div
                (σ.find? I.codeOwner |>.option ⟨0⟩
                  (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
                ⟨2⟩)
              ⟨127⟩)
            ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
            (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot
            (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride
                (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
        ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨983⟩
      [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  have hbranch := bytesStoreLiteX_setPacketShortHeaderReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hreach hlenMaxWord hflag hvalid
  exact bytesStoreLiteX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := ⟨2⟩)
    (payloadStart := payloadStart) (len := len) (ret := ⟨983⟩)
    (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hperm hbranch hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketShortOldLongReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
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
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩ fuel
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩, tag, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σClear) k C := by
  dsimp only
  let header : UInt256 :=
    (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hdecoder := bytesStoreLiteX_setPacketReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
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
    (rest := [len, ⟨2643⟩, ⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩,
      ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header] using hdecoder)
    (by simpa [header] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, ⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩,
          ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨2⟩, oldStoredLen, len, ⟨2643⟩, ⟨2⟩, payloadStart, len, ⟨983⟩,
        ⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
    (A := A) (I := I) (g := g) (slot := ⟨2⟩) (oldLen := oldStoredLen)
    (len := len) (ret := ⟨2643⟩)
    (tail := [⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩, tag, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hcleanupReach holdLong hgtOldNew hshortWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hloop := bytesStoreLiteX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩)
    (base := (⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256))
    (dead₀ := (⟨2⟩ : UInt256)) (dead₁ := oldStoredLen) (dead₂ := len)
    (ret := (⟨2643⟩ : UInt256))
    (rest := [⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩, tag, len,
      payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa using hloop

theorem bytesStoreLiteX_setPacketShortOldLongReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hshort : len.toNat < 32) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩, tag, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
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
    bytesStoreLiteX_setPacketShortOldLongReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
      (oldStoredLen := oldStoredLen) (fuel := count.toNat)
      hperm hreach hlenMax hflag holdStoredLen hvalid hshort hcontinue hdone

theorem bytesStoreLiteX_setPacketLongHeaderClearReachWriteBranchWithLoopSchedule
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    {fuel : Nat}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hcontinue : ∀ i, i < fuel →
      UInt256.isZero
        (UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ i)
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩))) = ⟨0⟩)
    (hdone :
      UInt256.lt (BytesStoreLiteCore.clearDataWordsLoopIndex ⟨0⟩ fuel)
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)) = ⟨0⟩) :
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
          bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩ fuel
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩, tag, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σClear) k C := by
  dsimp only
  let header : UInt256 :=
    (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hdecoder := bytesStoreLiteX_setPacketReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
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
    (rest := [len, ⟨2643⟩, ⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩,
      ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header] using hdecoder)
    (by simpa [header] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, ⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩,
          ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨2⟩, oldStoredLen, len, ⟨2643⟩, ⟨2⟩, payloadStart, len, ⟨983⟩,
        ⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
    (A := A) (I := I) (g := g) (slot := ⟨2⟩) (oldLen := oldStoredLen)
    (len := len) (ret := ⟨2643⟩)
    (tail := [⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩, tag, len,
      payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hcleanupReach holdLong hgtOldNew hlongWord
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hloop := bytesStoreLiteX_setClearDataWordsLoopGenerated
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (idx := (⟨0⟩ : UInt256))
    (count := UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩))
    (base := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
      bytesLikeDataBase (⟨2⟩ : UInt256))
    (dead₀ := (⟨2⟩ : UInt256)) (dead₁ := oldStoredLen) (dead₂ := len)
    (ret := (⟨2643⟩ : UInt256))
    (rest := [⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩, tag, len,
      payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (fuel := fuel)
    hperm hloopEntry hcontinue hdone (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  simpa using hloop

theorem bytesStoreLiteX_setPacketLongHeaderClearReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩, tag, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
          bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
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
    bytesStoreLiteX_setPacketLongHeaderClearReachWriteBranchWithLoopSchedule
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
      (oldStoredLen := oldStoredLen) (fuel := count.toNat)
      hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
      hcontinue hdone

theorem bytesStoreLiteX_setPacketLongNoTailOldLongClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
          bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
          (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨983⟩
      [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256)
        (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw
        (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  have hbranch := bytesStoreLiteX_setPacketLongHeaderClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
  exact bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σClear) (slot := ⟨2⟩)
    (payloadStart := payloadStart) (len := len) (ret := ⟨983⟩)
    (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    hperm (by simpa [σClear] using hbranch) hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketLongTailOldLongClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
          bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
            (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot
            (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride
                (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
        ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨983⟩
      [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256)
        (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
      (BytesStoreLiteCore.clearCurrentHashAw
        (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  have hbranch := bytesStoreLiteX_setPacketLongHeaderClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
  exact bytesStoreLiteX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σClear) (slot := ⟨2⟩)
    (payloadStart := payloadStart) (len := len) (ret := ⟨983⟩)
    (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    hperm (by simpa [σClear] using hbranch) hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketLongHeaderNoClearReachWriteBranch
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2643⟩
      [⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩, tag, len, payloadStart,
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have _hperm := hperm
  let header : UInt256 :=
    (σ.find? I.codeOwner |>.option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hdecoder := bytesStoreLiteX_setPacketReachWriteHeaderDecoder
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
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
    (rest := [len, ⟨2643⟩, ⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩,
      ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header] using hdecoder)
    (by simpa [header] using hflag)
    hvalidHeader
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd2637₀⟩ := hdecoded
  obtain ⟨_, _, rd2637⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨2637⟩
        [oldStoredLen, len, ⟨2643⟩, ⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩,
          ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa [hstoredEq] using rd2637₀⟩
  have hcleanupReach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨2302⟩
      [⟨2⟩, oldStoredLen, len, ⟨2643⟩, ⟨2⟩, payloadStart, len, ⟨983⟩,
        ⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
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
  simpa using
    bytesStoreLiteX_writeBytesCleanupOldLongNoClear
      (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) (slot := ⟨2⟩) (oldLen := oldStoredLen)
      (len := len) (ret := ⟨2643⟩)
      (tail := [⟨2⟩, payloadStart, len, ⟨983⟩, ⟨2⟩, ⟨0⟩, tag, len,
        payloadStart, ⟨263⟩, bytesStoreLiteSelWord I])
      (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
      hcleanupReach holdLong hgtOldNew (by native_decide)
      (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketLongNoTailOldLongNoClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨983⟩
      [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  have hbranch := bytesStoreLiteX_setPacketLongHeaderNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew
  exact bytesStoreLiteX_writeBytesNewLongNoTailFromWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := ⟨2⟩)
    (payloadStart := payloadStart) (len := len) (ret := ⟨983⟩)
    (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hperm hbranch hlong hnoTailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketLongTailOldLongNoClearWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    let σData : AccountMap :=
      sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
            (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot
            (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride
                (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
        ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨983⟩
      [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, σData) k C := by
  dsimp only
  have hbranch := bytesStoreLiteX_setPacketLongHeaderNoClearReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hgtOldNew
  exact bytesStoreLiteX_writeBytesNewLongTailFromWriteBranchSplit
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (τ := σ) (slot := ⟨2⟩)
    (payloadStart := payloadStart) (len := len) (ret := ⟨983⟩)
    (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    hperm hbranch hlong htailMod (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketShortNonemptyOldLongWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨983⟩
      [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σClear ⟨2⟩
        (bytesStoreLiteSetPacketShortStoredWord I len payloadStart)) k C := by
  dsimp only
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hbranch := bytesStoreLiteX_setPacketShortOldLongReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hshort
  have hwrite := bytesStoreLiteX_writeBytesNewShortNonemptyWriteHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨2⟩) (payloadStart := payloadStart)
    (len := len) (ret := ⟨983⟩) (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm
    (by simpa [σClear] using hbranch) hnz hshort
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σClear ⟨2⟩
      (bytesStoreLiteSetPacketShortStoredWord I len payloadStart))
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := ⟨2⟩)
    (payloadStart := payloadStart) (len := len) (ret := ⟨983⟩)
    (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [bytesStoreLiteSetPacketShortStoredWord] using hwrite)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketEmptyOldLongWriteReturnsToBody
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
        ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen =
        UInt256.div
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
          ⟨2⟩)
    (hvalid :
      UInt256.sub
          (UInt256.land
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
            ⟨1⟩)
          (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    let σClear : AccountMap :=
      clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨983⟩
      [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σClear ⟨2⟩ ⟨0⟩) k C := by
  dsimp only
  let σClear : AccountMap :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hshort : len.toNat < 32 := by
    rw [hlenZero]
    decide
  have hbranch := bytesStoreLiteX_setPacketShortOldLongReachWriteBranch
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hshort
  have hpacked := bytesStoreLiteX_writeBytesNewEmptyReachPackedHeader
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨2⟩) (payloadStart := payloadStart)
    (len := len) (ret := ⟨983⟩) (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [σClear] using hbranch) hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hwrite := bytesStoreLiteX_writeBytesNewEmptyWriteHeaderGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σClear) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (slot := ⟨2⟩) (payloadStart := payloadStart)
    (len := len) (ret := ⟨983⟩) (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart,
      ⟨263⟩, bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm hpacked hlenZero
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact bytesStoreLiteX_writeBytesReturnFromEmptyWriteGeneric
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ)
    (σ := sstoreAccountMap I.codeOwner σClear ⟨2⟩ ⟨0⟩)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (slot := ⟨2⟩)
    (payloadStart := payloadStart) (len := len) (ret := ⟨983⟩)
    (tail := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hwrite
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    {cA gh bl σinit σ σ₀ A I} {g : Sat256} {tag len payloadStart : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨983⟩
      [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      mem aw rdata (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨2246⟩
      [((sstoreAccountMap I.codeOwner σ ⟨3⟩ tag).find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)),
        ⟨1002⟩, ⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I]
      mem aw rdata (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩ tag) k C := by
  obtain ⟨_, _, rd983⟩ := hreach
  have rd989pre := evm_run rd983 with [jumpdest, pop, push1 ⟨3⟩, dup3, swap1]
  obtain ⟨_, _, rd990₀⟩ := rd989pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd990⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨990⟩
        [⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem aw rdata (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩ tag) k C := by
    exact ⟨_, _, by simpa [initState] using rd990₀⟩
  have rd993pre := evm_run rd990 with [push1 ⟨2⟩, dup1]
  obtain ⟨_, _, rd994₀⟩ := rd993pre.sload (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rd994⟩ :
      ∃ k C, RD bytesStoreLiteBytecode I g
        (initState cA gh bl σinit σ₀ g A I) ⟨994⟩
        [((sstoreAccountMap I.codeOwner σ ⟨3⟩ tag).find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)),
          ⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
        mem aw rdata (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩ tag) k C := by
    exact ⟨_, _, by simpa [initState] using rd994₀⟩
  exact ⟨_, _, evm_run rd994 with [
    push2 ⟨1002⟩, swap1, push2 ⟨2246⟩, jump (by native_decide)]⟩

theorem bytesStoreLiteX_setPacketReturnFromDecodedLength
    {cA gh bl σinit σ σ₀ A I} {g : Sat256}
    {packetLen tag len payloadStart : UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨1002⟩
      [packetLen, ⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
        bytesStoreLiteSelWord I]
      mem aw rdata (cA, σ) k C) :
    ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σinit σ₀ g A I) ⟨263⟩
      [packetLen, bytesStoreLiteSelWord I]
      mem aw rdata (cA, σ) k C := by
  obtain ⟨_, _, rd1002⟩ := hreach
  exact ⟨_, _, evm_run rd1002 with [
    jumpdest, swap6, swap5, pop, pop, pop, pop, pop, jump (by native_decide)]⟩

theorem bytesStoreLiteSetPacketEmptyHeaderAfterTag (σ : AccountMap) (I : ExecutionEnv)
    (tag : UInt256) :
    (((sstoreAccountMap I.codeOwner (sstoreAccountMap I.codeOwner σ ⟨2⟩ ⟨0⟩)
        ⟨3⟩ tag).find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256))) = ⟨0⟩ := by
  exact bytesStoreLitePacketDataWordAfterDataTagSstore_zero σ I tag

theorem bytesStoreLiteX_setPacketEmptyOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div
              ((σ.find? I.codeOwner).option ⟨0⟩
                (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨2⟩ ⟨0⟩) ⟨3⟩ tag)
      (UInt256.toByteArray ⟨0⟩) := by
  let σData := sstoreAccountMap I.codeOwner σ ⟨2⟩ ⟨0⟩
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let header : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketEmptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid hlenZero
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart) (mem := solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm (by simpa [σData] using hbody)
  have hheader : header = ⟨0⟩ := by
    simpa [header, σFinal, σData] using bytesStoreLiteSetPacketEmptyHeaderAfterTag σ I tag
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header, σFinal, σData] using hdecoder)
    (by rw [hheader]; native_decide)
    (by rw [hheader]; native_decide)
    (by native_decide)
    (by simp)
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := ⟨0⟩) (tag := tag) (len := len)
    (payloadStart := payloadStart) (mem := solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) (by simpa [header, hheader] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := ⟨0⟩) (mem := solcFreePtrMem)
    solcFreePtrMem_size solcFreePtrMem_read64 h263

theorem bytesStoreLiteX_setPacketEmptyOldLongReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen : oldStoredLen =
        UInt256.div
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner σ
            ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
            (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
          ⟨2⟩ ⟨0⟩) ⟨3⟩ tag)
      (UInt256.toByteArray ⟨0⟩) := by
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σData := sstoreAccountMap I.codeOwner σClear ⟨2⟩ ⟨0⟩
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let header : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketEmptyOldLongWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hlenZero
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm (by simpa [σClear, σData] using hbody)
  have hheader : header = ⟨0⟩ := by
    simpa [header, σFinal, σData, σClear] using
      bytesStoreLiteSetPacketEmptyHeaderAfterTag σClear I tag
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [header, σFinal, σData, σClear] using hdecoder)
    (by rw [hheader]; native_decide)
    (by rw [hheader]; native_decide)
    (by native_decide)
    (by simp)
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := ⟨0⟩) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [header, hheader] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := ⟨0⟩)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setPacketShortNonemptyOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div
              ((σ.find? I.codeOwner).option ⟨0⟩
                (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hacc : σ.find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σ ⟨2⟩
          (bytesStoreLiteSetPacketShortStoredWord I len payloadStart)) ⟨3⟩ tag)
      (UInt256.toByteArray len) := by
  let storedWord := bytesStoreLiteSetPacketShortStoredWord I len payloadStart
  let σData := sstoreAccountMap I.codeOwner σ ⟨2⟩ storedWord
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let header : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketShortNonemptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid hnz hshort
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart) (mem := solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm (by simpa [σData, storedWord] using hbody)
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256)))) = storedWord := by
    have hnzStored := bytesStoreLiteSetPacketShortStoredWord_beq_zero_false
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
    simpa [σData, storedWord] using
      sstoreAccountMap_storage_findD_self_of_find_some σ I.codeOwner acc ⟨2⟩
        storedWord hacc hnzStored
  have hheader : header = storedWord := by
    simpa [header, σFinal] using
      bytesStoreLitePacketDataWordAfterTagSstore_eq_of_before
        (σ := σData) (I := I) (tag := tag) hdata
  have hflag' : UInt256.land header ⟨1⟩ = ⟨0⟩ := by
    rw [hheader]
    exact bytesStoreLiteSetPacketShortStoredWord_flag_eq
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have hvalid' :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    rw [hheader,
      bytesStoreLiteSetPacketShortStoredWord_flag_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort,
      bytesStoreLiteSetPacketShortStoredWord_shortLen_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort]
    have hlt : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    rw [hlt]
    native_decide
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header, σFinal, σData, storedWord] using hdecoder)
    hflag' hvalid' (by native_decide) (by simp)
  have hlenDecoded :
      UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ = len := by
    rw [hheader]
    exact bytesStoreLiteSetPacketShortStoredWord_shortLen_eq
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := len) (tag := tag) (len := len)
    (payloadStart := payloadStart) (mem := solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len) (mem := solcFreePtrMem)
    solcFreePtrMem_size solcFreePtrMem_read64 h263

theorem bytesStoreLiteX_setPacketShortNonemptyOldShortAbsentReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div
              ((σ.find? I.codeOwner).option ⟨0⟩
                (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (hmissing : σ.find? I.codeOwner = none) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (UInt256.toByteArray ⟨0⟩) := by
  let storedWord := bytesStoreLiteSetPacketShortStoredWord I len payloadStart
  let σData := sstoreAccountMap I.codeOwner σ ⟨2⟩ storedWord
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let header : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketShortNonemptyWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMax hflag hvalid hnz hshort
  have hdataSame : σData = σ := by
    simpa [σData, storedWord] using
      sstoreAccountMap_absent_same (owner := I.codeOwner) (τ := σ)
        (slot := ⟨2⟩) (val := storedWord) hmissing
  have hfinalSame : σFinal = σ := by
    dsimp [σFinal]
    rw [hdataSame]
    exact sstoreAccountMap_absent_same (owner := I.codeOwner) (τ := σ)
      (slot := ⟨3⟩) (val := tag) hmissing
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart) (mem := solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) hperm (by simpa [σData, storedWord] using hbody)
  have hheader : header = ⟨0⟩ := by
    dsimp [header]
    rw [hfinalSame, hmissing]
    rfl
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := solcFreePtrMem) (aw := UInt256.ofNat 3) (rdata := ByteArray.empty)
    (by simpa [header, σFinal, σData, storedWord] using hdecoder)
    (by rw [hheader]; native_decide)
    (by rw [hheader]; native_decide)
    (by native_decide)
    (by simp)
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := ⟨0⟩) (tag := tag) (len := len)
    (payloadStart := payloadStart) (mem := solcFreePtrMem) (aw := UInt256.ofNat 3)
    (rdata := ByteArray.empty) (by simpa [header, hheader] using hdecoded)
  have hret := bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := ⟨0⟩) (mem := solcFreePtrMem)
    solcFreePtrMem_size solcFreePtrMem_read64 h263
  simpa [hfinalSame] using hret

theorem bytesStoreLiteX_setPacketShortNonemptyOldLongReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMax : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen : oldStoredLen =
        UInt256.div
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32)
    (haccClear :
      (clearDataWordsForwardFrom I.codeOwner σ
        ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
        (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat).find?
          I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner σ
            ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
            (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat)
          ⟨2⟩ (bytesStoreLiteSetPacketShortStoredWord I len payloadStart)) ⟨3⟩ tag)
      (UInt256.toByteArray len) := by
  let storedWord := bytesStoreLiteSetPacketShortStoredWord I len payloadStart
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σData := sstoreAccountMap I.codeOwner σClear ⟨2⟩ storedWord
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let header : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketShortNonemptyOldLongWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMax hflag holdStoredLen hvalid hnz hshort
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm
    (by simpa [σClear, σData, storedWord] using hbody)
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256)))) = storedWord := by
    have hnzStored := bytesStoreLiteSetPacketShortStoredWord_beq_zero_false
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
    simpa [σData, σClear, storedWord] using
      sstoreAccountMap_storage_findD_self_of_find_some σClear I.codeOwner acc ⟨2⟩
        storedWord (by simpa [σClear] using haccClear) hnzStored
  have hheader : header = storedWord := by
    simpa [header, σFinal] using
      bytesStoreLitePacketDataWordAfterTagSstore_eq_of_before
        (σ := σData) (I := I) (tag := tag) hdata
  have hflag' : UInt256.land header ⟨1⟩ = ⟨0⟩ := by
    rw [hheader]
    exact bytesStoreLiteSetPacketShortStoredWord_flag_eq
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have hvalid' :
      UInt256.sub (UInt256.land header ⟨1⟩)
        (UInt256.lt (UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩) ⟨32⟩) ≠
          ⟨0⟩ := by
    rw [hheader,
      bytesStoreLiteSetPacketShortStoredWord_flag_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort,
      bytesStoreLiteSetPacketShortStoredWord_shortLen_eq
        (I := I) (len := len) (payloadStart := payloadStart) hnz hshort]
    have hlt : UInt256.lt len ⟨32⟩ = ⟨1⟩ := by
      exact ult_one (by simpa [show (⟨32⟩ : UInt256).toNat = 32 from by decide] using hshort)
    rw [hlt]
    native_decide
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := header) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [header, σFinal, σData, σClear, storedWord] using hdecoder)
    hflag' hvalid' (by native_decide) (by simp)
  have hlenDecoded :
      UInt256.land (UInt256.div header ⟨2⟩) ⟨127⟩ = len := by
    rw [hheader]
    exact bytesStoreLiteSetPacketShortStoredWord_shortLen_eq
      (I := I) (len := len) (payloadStart := payloadStart) hnz hshort
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := len) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setPacketLongNoTailOldLongClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen : oldStoredLen =
        UInt256.div
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (haccData :
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
        (clearDataWordsForwardFrom I.codeOwner σ
          (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
            bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
          (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat)
        (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)).find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
            (clearDataWordsForwardFrom I.codeOwner σ
              (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
                bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
              (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
                (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat)
            (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) ⟨3⟩ tag)
      (UInt256.toByteArray len) := by
  let header := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData := sstoreAccountMap I.codeOwner σLoop ⟨2⟩ header
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let loadedHeader : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketLongNoTailOldLongClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong hnoTailMod
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256)
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)))
    (rdata := ByteArray.empty) hperm
    (by simpa [σClear, σLoop, σData, header] using hbody)
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256)))) = header := by
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
    simpa [σData, σLoop, σClear, header] using
      sstoreAccountMap_storage_findD_self_of_find_some σLoop I.codeOwner acc ⟨2⟩
        header (by simpa [σLoop, σClear] using haccData) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader, σFinal] using
      bytesStoreLitePacketDataWordAfterTagSstore_eq_of_before
        (σ := σData) (I := I) (tag := tag) hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256)
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, σFinal, σData, σLoop, σClear, header] using hdecoder)
    hflag' hvalid' (by native_decide) (by simp)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := len) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256)
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨2⟩ : UInt256)
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 _
      (wordAt0Mem_size_96 _ solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _ solcFreePtrMem_size)
      (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setPacketLongTailOldLongClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen : oldStoredLen =
        UInt256.div
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
          (clearDataWordsForwardFrom I.codeOwner σ
            (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
              bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
            (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
              (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat)
          (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot
          (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
              (clearDataWordsForwardFrom I.codeOwner σ
                (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
                  bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
                (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
                  (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat)
              (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
              (len.toNat / 32))
            (BytesStoreLiteCore.longDataWordsLoopSlot
              (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32))
            (BytesStoreLiteCore.longDataTailMaskedWord
              (bytesStoreLiteCalldataLongDataWord I payloadStart
                (BytesStoreLiteCore.longDataWordsLoopStride
                  (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
          ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) ⟨3⟩ tag)
      (UInt256.toByteArray len) := by
  let header := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ +
        bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩)
        (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩)).toNat
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData := sstoreAccountMap I.codeOwner σTail ⟨2⟩ header
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let loadedHeader : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketLongTailOldLongClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong htailMod
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256)
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)))
    (rdata := ByteArray.empty) hperm
    (by simpa [σClear, σLoop, tailSlot, tailWord, σTail, σData, header] using hbody)
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256)))) = header := by
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
    simpa [σData, σTail, σLoop, σClear, tailSlot, tailWord, header] using
      sstoreAccountMap_storage_findD_self_of_find_some σTail I.codeOwner acc ⟨2⟩
        header (by simpa [σTail, σLoop, σClear, tailSlot, tailWord] using haccTail)
        hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader, σFinal] using
      bytesStoreLitePacketDataWordAfterTagSstore_eq_of_before
        (σ := σData) (I := I) (tag := tag) hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256)
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, σFinal, σData, σTail, σLoop, σClear, tailSlot,
      tailWord, header] using hdecoder)
    hflag' hvalid' (by native_decide) (by simp)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := len) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256)
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
    (aw := BytesStoreLiteCore.clearCurrentHashAw
      (BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3)))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨2⟩ : UInt256)
      (wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem))
    (wordAt0Mem_size_96 _
      (wordAt0Mem_size_96 _ solcFreePtrMem_size))
    (bytesStoreLiteWordAt0Mem_read64 _
      (wordAt0Mem_size_96 _ solcFreePtrMem_size)
      (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64))
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setPacketLongNoTailOldLongNoClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen : oldStoredLen =
        UInt256.div
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (haccData :
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)).find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
            (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) ⟨3⟩ tag)
      (UInt256.toByteArray len) := by
  let header := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData := sstoreAccountMap I.codeOwner σLoop ⟨2⟩ header
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let loadedHeader : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketLongNoTailOldLongNoClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong hnoTailMod
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm
    (by simpa [σLoop, σData, header] using hbody)
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256)))) = header := by
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
    simpa [σData, σLoop, header] using
      sstoreAccountMap_storage_findD_self_of_find_some σLoop I.codeOwner acc ⟨2⟩
        header haccData hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader, σFinal] using
      bytesStoreLitePacketDataWordAfterTagSstore_eq_of_before
        (σ := σData) (I := I) (tag := tag) hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, σFinal, σData, σLoop, header] using hdecoder)
    hflag' hvalid' (by native_decide) (by simp)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := len) (tag := tag) (len := len)
    (payloadStart := payloadStart) (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setPacketLongTailOldLongNoClearReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart oldStoredLen : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen : oldStoredLen =
        UInt256.div
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot
          (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
              (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
              (len.toNat / 32))
            (BytesStoreLiteCore.longDataWordsLoopSlot
              (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32))
            (BytesStoreLiteCore.longDataTailMaskedWord
              (bytesStoreLiteCalldataLongDataWord I payloadStart
                (BytesStoreLiteCore.longDataWordsLoopStride
                  (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
          ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) ⟨3⟩ tag)
      (UInt256.toByteArray len) := by
  let header := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData := sstoreAccountMap I.codeOwner σTail ⟨2⟩ header
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let loadedHeader : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketLongTailOldLongNoClearWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    (oldStoredLen := oldStoredLen)
    hperm hreach hlenMaxWord hflag holdStoredLen hvalid hgtOldNew hlong htailMod
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm
    (by simpa [σLoop, tailSlot, tailWord, σTail, σData, header] using hbody)
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256)))) = header := by
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
    simpa [σData, σTail, σLoop, tailSlot, tailWord, header] using
      sstoreAccountMap_storage_findD_self_of_find_some σTail I.codeOwner acc ⟨2⟩
        header (by simpa [σTail, σLoop, tailSlot, tailWord] using haccTail) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader, σFinal] using
      bytesStoreLitePacketDataWordAfterTagSstore_eq_of_before
        (σ := σData) (I := I) (tag := tag) hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, σFinal, σData, σTail, σLoop, tailSlot, tailWord, header]
      using hdecoder)
    hflag' hvalid' (by native_decide) (by simp)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := len) (tag := tag) (len := len)
    (payloadStart := payloadStart) (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setPacketLongNoTailOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div
              ((σ.find? I.codeOwner).option ⟨0⟩
                (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (haccData :
      (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
        (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
        (len.toNat / 32)).find? I.codeOwner = some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
            (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) ⟨3⟩ tag)
      (UInt256.toByteArray len) := by
  let header := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData := sstoreAccountMap I.codeOwner σLoop ⟨2⟩ header
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let loadedHeader : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketLongNoTailWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMaxWord hflag hvalid hlong hnoTailMod
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm (by simpa [σLoop, σData, header] using hbody)
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256)))) = header := by
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
    simpa [σData, σLoop, header] using
      sstoreAccountMap_storage_findD_self_of_find_some σLoop I.codeOwner acc ⟨2⟩
        header haccData hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader, σFinal] using
      bytesStoreLitePacketDataWordAfterTagSstore_eq_of_before
        (σ := σData) (I := I) (tag := tag) hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, σFinal, σData, σLoop, header] using hdecoder)
    hflag' hvalid' (by native_decide) (by simp)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := len) (tag := tag) (len := len)
    (payloadStart := payloadStart) (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setPacketLongNoTailOldShortAbsentReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div
              ((σ.find? I.codeOwner).option ⟨0⟩
                (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0)
    (hmissing : σ.find? I.codeOwner = none) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (UInt256.toByteArray ⟨0⟩) := by
  let header := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σData := sstoreAccountMap I.codeOwner σLoop ⟨2⟩ header
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let loadedHeader : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketLongNoTailWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMaxWord hflag hvalid hlong hnoTailMod
  have hloopSame : σLoop = σ := by
    simpa [σLoop] using
      bytesStoreLiteCalldataLongDataForwardFrom_absent_same
        (σ := σ) (owner := I.codeOwner) (slot := bytesLikeDataBase (⟨2⟩ : UInt256))
        (payloadStart := payloadStart) (stride := (⟨0⟩ : UInt256)) (I := I)
        hmissing (len.toNat / 32)
  have hdataSame : σData = σ := by
    dsimp [σData]
    rw [hloopSame]
    exact sstoreAccountMap_absent_same (owner := I.codeOwner) (τ := σ)
      (slot := ⟨2⟩) (val := header) hmissing
  have hfinalSame : σFinal = σ := by
    dsimp [σFinal]
    rw [hdataSame]
    exact sstoreAccountMap_absent_same (owner := I.codeOwner) (τ := σ)
      (slot := ⟨3⟩) (val := tag) hmissing
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm (by simpa [σLoop, σData, header] using hbody)
  have hloaded : loadedHeader = ⟨0⟩ := by
    dsimp [loadedHeader]
    rw [hfinalSame, hmissing]
    rfl
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, σFinal, σData, σLoop, header] using hdecoder)
    (by rw [hloaded]; native_decide)
    (by rw [hloaded]; native_decide)
    (by native_decide)
    (by simp)
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := ⟨0⟩) (tag := tag) (len := len)
    (payloadStart := payloadStart) (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [loadedHeader, hloaded] using hdecoded)
  have hret := bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := ⟨0⟩)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)
  simpa [hfinalSame] using hret

theorem bytesStoreLiteX_setPacketLongTailOldShortReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart : UInt256}
    {acc : Account}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div
              ((σ.find? I.codeOwner).option ⟨0⟩
                (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (haccTail :
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
          (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot
          (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride
              (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len)).find? I.codeOwner =
        some acc) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
              (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
              (len.toNat / 32))
            (BytesStoreLiteCore.longDataWordsLoopSlot
              (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32))
            (BytesStoreLiteCore.longDataTailMaskedWord
              (bytesStoreLiteCalldataLongDataWord I payloadStart
                (BytesStoreLiteCore.longDataWordsLoopStride
                  (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len))
          ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩)) ⟨3⟩ tag)
      (UInt256.toByteArray len) := by
  let header := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData := sstoreAccountMap I.codeOwner σTail ⟨2⟩ header
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let loadedHeader : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketLongTailWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMaxWord hflag hvalid hlong htailMod
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm
    (by simpa [σLoop, tailSlot, tailWord, σTail, σData, header] using hbody)
  have hdata :
      (((σData.find? I.codeOwner).option (default : UInt256)
        (fun acc => acc.storage.findD ⟨2⟩ (default : UInt256)))) = header := by
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
    simpa [σData, σTail, σLoop, tailSlot, tailWord, header] using
      sstoreAccountMap_storage_findD_self_of_find_some σTail I.codeOwner acc ⟨2⟩
        header (by simpa [σTail, σLoop, tailSlot, tailWord] using haccTail) hnzHeader
  have hloaded : loadedHeader = header := by
    simpa [loadedHeader, σFinal] using
      bytesStoreLitePacketDataWordAfterTagSstore_eq_of_before
        (σ := σData) (I := I) (tag := tag) hdata
  have hflag' : UInt256.land loadedHeader ⟨1⟩ ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax
  have hvalid' :
      UInt256.sub (UInt256.land loadedHeader ⟨1⟩)
        (UInt256.lt (UInt256.div loadedHeader ⟨2⟩) ⟨32⟩) ≠ ⟨0⟩ := by
    rw [hloaded]
    exact bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderLongValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, σFinal, σData, σTail, σLoop, tailSlot, tailWord, header]
      using hdecoder)
    hflag' hvalid' (by native_decide) (by simp)
  have hlenDecoded : UInt256.div loadedHeader ⟨2⟩ = len := by
    rw [hloaded]
    simpa [header] using bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := len) (tag := tag) (len := len)
    (payloadStart := payloadStart) (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [hlenDecoded] using hdecoded)
  exact bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := len)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)

theorem bytesStoreLiteX_setPacketLongTailOldShortAbsentReturns
    {cA gh bl σ σ₀ A I} {g : Sat256} {tag len payloadStart : UInt256}
    (hperm : I.perm = true)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag : UInt256.land
        ((σ.find? I.codeOwner).option ⟨0⟩
          (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩ = ⟨0⟩)
    (hvalid : UInt256.sub
        (UInt256.land
          ((σ.find? I.codeOwner).option ⟨0⟩
            (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div
              ((σ.find? I.codeOwner).option ⟨0⟩
                (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩)) ⟨2⟩) ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0)
    (hmissing : σ.find? I.codeOwner = none) :
    RDret bytesStoreLiteBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, σ) (UInt256.toByteArray ⟨0⟩) := by
  let header := len * (⟨2⟩ : UInt256) + ⟨1⟩
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride
          (⟨0⟩ : UInt256) (len.toNat / 32)) 0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData := sstoreAccountMap I.codeOwner σTail ⟨2⟩ header
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let loadedHeader : UInt256 :=
    ((σFinal.find? I.codeOwner).option ⟨0⟩
      (fun acc => acc.storage.findD ⟨2⟩ ⟨0⟩))
  have hbody := bytesStoreLiteX_setPacketLongTailWriteReturnsToBody
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) (tag := tag) (len := len) (payloadStart := payloadStart)
    hperm hreach hlenMaxWord hflag hvalid hlong htailMod
  have hloopSame : σLoop = σ := by
    simpa [σLoop] using
      bytesStoreLiteCalldataLongDataForwardFrom_absent_same
        (σ := σ) (owner := I.codeOwner) (slot := bytesLikeDataBase (⟨2⟩ : UInt256))
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
      (slot := ⟨2⟩) (val := header) hmissing
  have hfinalSame : σFinal = σ := by
    dsimp [σFinal]
    rw [hdataSame]
    exact sstoreAccountMap_absent_same (owner := I.codeOwner) (τ := σ)
      (slot := ⟨3⟩) (val := tag) hmissing
  have hdecoder := bytesStoreLiteX_setPacketAfterBytesWriteReachLengthDecoder
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σData) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (tag := tag) (len := len)
    (payloadStart := payloadStart)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) hperm
    (by simpa [σLoop, tailSlot, tailWord, σTail, σData, header] using hbody)
  have hloaded : loadedHeader = ⟨0⟩ := by
    dsimp [loadedHeader]
    rw [hfinalSame, hmissing]
    rfl
  have hdecoded := bytesStoreLiteX_bytesLengthDecoderShortValidMemCarried
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (τ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (header := loadedHeader) (ret := ⟨1002⟩)
    (rest := [⟨2⟩, ⟨0⟩, tag, len, payloadStart, ⟨263⟩,
      bytesStoreLiteSelWord I])
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty)
    (by simpa [loadedHeader, σFinal, σData, σTail, σLoop, tailSlot, tailWord, header]
      using hdecoder)
    (by rw [hloaded]; native_decide)
    (by rw [hloaded]; native_decide)
    (by native_decide)
    (by simp)
  have h263 := bytesStoreLiteX_setPacketReturnFromDecodedLength
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (packetLen := ⟨0⟩) (tag := tag) (len := len)
    (payloadStart := payloadStart) (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (aw := BytesStoreLiteCore.clearCurrentHashAw (UInt256.ofNat 3))
    (rdata := ByteArray.empty) (by simpa [loadedHeader, hloaded] using hdecoded)
  have hret := bytesStoreLiteX_returnWord263OfMemState
    (cA := cA) (gh := gh) (bl := bl) (σinit := σ) (σ := σFinal) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) (val := ⟨0⟩)
    (mem := wordAt0Mem (⟨2⟩ : UInt256) solcFreePtrMem)
    (wordAt0Mem_size_96 _ solcFreePtrMem_size)
    (bytesStoreLiteWordAt0Mem_read64 _ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simpa [BytesStoreLiteCore.clearCurrentHashAw] using h263)
  simpa [hfinalSame] using hret

theorem bytesStoreLiteSetPacketSelector_size {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩) :
    4 ≤ I.calldata.size := by
  have hs := byteArray_size_eq_of_beq hsel
  have hleft : (⟨#[0x14, 0xf1, 0x7c, 0x69]⟩ : ByteArray).size = 4 := rfl
  rw [hleft, ByteArray.size_extract] at hs
  omega

theorem bytesStoreLiteDecode_setPacket_none_short {I : ExecutionEnv}
    (hshort : I.calldata.size < 68) :
    decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "tag"] [.bytes, uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_bytes_uint256_none_short (cd := I.calldata) (x := "value")
      (y := "tag") hshort

theorem bytesStoreLiteDecode_setPacket_none_totalHuge {I : ExecutionEnv}
    (hbig : 2 ^ 255 ≤ I.calldata.size) :
    decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "tag"] [.bytes, uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_bytes_uint256_none_total_huge (cd := I.calldata) (x := "value")
      (y := "tag") hbig

theorem bytesStoreLiteDecode_setPacket_none_offsetHuge {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "tag"] [.bytes, uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_bytes_uint256_none_offset_huge (cd := I.calldata) (x := "value")
      (y := "tag") hsz68 hsizeSign hoff

theorem bytesStoreLiteDecode_setPacket_none_lengthShort {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hshort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "tag"] [.bytes, uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_bytes_uint256_none_length_short (cd := I.calldata) (x := "value")
      (y := "tag") hsz68 hsizeSign hoffMax hshort

theorem bytesStoreLiteDecode_setPacket_none_lengthHuge {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "tag"] [.bytes, uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_bytes_uint256_none_length_huge (cd := I.calldata) (x := "value")
      (y := "tag") hsz68 hsizeSign hoffMax hlenWord hlenHuge

theorem bytesStoreLiteDecode_setPacket_none_payloadShort {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata = none := by
  show decodeCalldata ["value", "tag"] [.bytes, uint256] I.calldata = none
  simpa [uint256, abiUInt256]
    using decodeCalldata_bytes_uint256_none_payload_short (cd := I.calldata) (x := "value")
      (y := "tag") hsz68 hsizeSign hoffMax hlenWord hlenMax hpayload

theorem bytesStoreLiteDecode_setPacket {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (_hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)) :
    decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocals I) := by
  show decodeCalldata ["value", "tag"] [.bytes, uint256] I.calldata =
    some (bytesStoreLiteSetPacketLocals I)
  simpa [uint256, abiUInt256, bytesStoreLiteSetPacketLocals,
    bytesStoreLiteSetPacketTagWord, BytesStoreLiteCore.setDecodedValueBytes] using
    decodeCalldata_bytes_uint256_some (cd := I.calldata) (x := "value") (y := "tag")
      hsz68 hsizeSign hoffMax hlenWord hlenMax hpayload

theorem bytesStoreLiteSetPacketDecodedValueEmpty {I : ExecutionEnv}
    {len payloadStart : UInt256}
    (hlenAbi : len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart : payloadStart = ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenZero : len = ⟨0⟩) :
    BytesStoreLiteCore.setDecodedValueBytes I = ByteArray.empty := by
  have hvalueExtract := BytesStoreLiteCore.setDecodedValueBytes_eq_extract
    (I := I) (len := len) (payloadStart := payloadStart)
    hlenAbi hpayloadStart hoffMax
  rw [hvalueExtract, hlenZero]
  simp [hpayloadStart]

theorem bytesStoreLiteDecode_setPacket_empty {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayload :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hlenZero :
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) = ⟨0⟩) :
    decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf ByteArray.empty
          (bytesStoreLiteSetPacketTagWord I)) := by
  have hdec := bytesStoreLiteDecode_setPacket (I := I)
    hsz68 hhi hsizeSign hoffMax hlenWord hlenMax hpayload
  have hempty : BytesStoreLiteCore.setDecodedValueBytes I = ByteArray.empty :=
    bytesStoreLiteSetPacketDecodedValueEmpty
      (I := I)
      (len := calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
      (payloadStart := ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩)
      (by rfl) (by rfl) hoffMax (by simpa using hlenZero)
  simpa [bytesStoreLiteSetPacketLocals, bytesStoreLiteSetPacketLocalsOf,
    hempty] using hdec

theorem bytesStoreLiteSetPacketDecodeValidReachToBody
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hwv : I.weiValue = ⟨0⟩)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨0⟩) :
    ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨969⟩
      [bytesStoreLiteSetPacketTagWord I,
        calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat),
        ((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩,
        ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hstart :
      UInt256.slt ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨31⟩))
          (UInt256.ofNat I.calldata.size) = ⟨1⟩ :=
    BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign
  have hlenMaxWord :
      UInt256.gt
          (uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32))
          ⟨18446744073709551615⟩ = ⟨0⟩ :=
    BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax
  have hdecodedReach := bytesStoreLiteX_setPacketDecodeValid
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz68 hhi hsize hsel hoffMax hstart hlenMaxWord hpayloadWord
  have hlenEvm :
      uInt256OfByteArray
          (I.calldata.readBytes
            ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32) =
        calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) := by
    simpa using BytesStoreLiteCore.setLengthWord_eq_abi I.calldata hoffMax
  simpa [bytesStoreLiteSetPacketTagWord, hlenEvm] using hdecodedReach

theorem bytesStoreLiteSetPacketDecodeShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hshort : I.calldata.size < 68) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetPacketSelector_size hsel
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacket_none_short (I := I) hshort
  exact (bytesStoreLiteX_setPacketDecodeShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hshort hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetPacketDecodeHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hbig : 2 ^ 255 + 4 ≤ I.calldata.size) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hsz := bytesStoreLiteSetPacketSelector_size hsel
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacket_none_totalHuge (I := I) (by omega)
  exact (bytesStoreLiteX_setPacketDecodeHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz hbig hsize hsel)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetPacketDecodeTotalHighRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsizeHigh : ¬ I.calldata.size < 2 ^ 255) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacket_none_totalHuge (I := I)
    (Nat.le_of_not_gt hsizeHigh)
  exact (bytesStoreLiteX_setPacketDecodeTotalHigh
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hsizeHigh)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetPacketDecodeOffsetHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hoff : ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec :
      decodeCalldata (setPacketTransition.params.map Param.name)
        (transitionSignature setPacketTransition).paramTypes I.calldata = none := by
    by_cases hsizeSign : I.calldata.size < 2 ^ 255
    · exact bytesStoreLiteDecode_setPacket_none_offsetHuge (I := I)
        hsz68 hsizeSign hoff
    · exact bytesStoreLiteDecode_setPacket_none_totalHuge (I := I)
        (Nat.le_of_not_gt hsizeSign)
  exact (bytesStoreLiteX_setPacketDecodeOffsetHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoff)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetPacketDecodeLengthShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenShort : I.calldata.size < 4 + (calldataWord I.calldata 4).toNat + 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacket_none_lengthShort (I := I)
    hsz68 hsizeSign hoffMax hlenShort
  exact (bytesStoreLiteX_setPacketDecodeLengthShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax hlenShort)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetPacketDecodeLengthHugeRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenHuge :
      ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacket_none_lengthHuge (I := I)
    hsz68 hsizeSign hoffMax hlenWord hlenHuge
  exact (bytesStoreLiteX_setPacketDecodeLengthHuge
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax
      (BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
      (BytesStoreLiteCore.setLengthMaxWord_one_of_abi I.calldata hoffMax hlenHuge))
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetPacketDecodePayloadShortRuntime {cA gh bl σ_evm σ_solm σ₀ A I}
    {g : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x14, 0xf1, 0x7c, 0x69]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsz68 : 68 ≤ I.calldata.size) (hhi : I.calldata.size < 2 ^ 255 + 4)
    (hsizeSign : I.calldata.size < 2 ^ 255)
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlenWord : 4 + (calldataWord I.calldata 4).toNat + 32 ≤ I.calldata.size)
    (hlenMax :
      ¬ ABI.solcMaxU64 <
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length ≠
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hpayloadWord :
      UInt256.gt
        (((((⟨4⟩ : UInt256) + calldataWord I.calldata 4) +
          uInt256OfByteArray
            (I.calldata.readBytes
              ((((⟨4⟩ : UInt256) + calldataWord I.calldata 4)).toNat) 32)) +
          ⟨32⟩))
        (UInt256.ofNat I.calldata.size) = ⟨1⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  have hd := bytesStoreLiteDispatch_setPacket (cd := I.calldata) (by simpa [selIs] using hsel)
  have hdec := bytesStoreLiteDecode_setPacket_none_payloadShort (I := I)
    hsz68 hsizeSign hoffMax hlenWord hlenMax hpayloadList
  exact (bytesStoreLiteX_setPacketDecodePayloadShort
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz68 hhi hsize hsel hoffMax
      (BytesStoreLiteCore.setStart_slt_one I.calldata hoffMax hlenWord hsizeSign)
      (BytesStoreLiteCore.setLengthMaxWord_of_abi I.calldata hoffMax hlenMax)
      hpayloadWord)
    |>.reEquivDecodingFailed hcode hd hdec

theorem bytesStoreLiteSetPacketEmptyOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {tag len payloadStart : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf ByteArray.empty tag))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmData := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨2⟩ ⟨0⟩
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  let σFinal :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ_evm ⟨2⟩ ⟨0⟩) ⟨3⟩ tag
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray ⟨0⟩) := by
    simpa [σFinal] using
      bytesStoreLiteX_setPacketEmptyOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (tag := tag)
        (len := len) (payloadStart := payloadStart)
        hperm hreach hlenMaxWord hflag hvalid hlenZero
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } .bytes (.bytes ByteArray.empty) =
          .ok evmData := by
    have hwrite₀ := bytesStoreLiteWritePacketDataEmptyShortPacked
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hAccounts hflag hvalid
    simpa [evmSolm0, evmData] using hwrite₀
  have hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag := by
    simpa [evmTag, evmData, evmSolm0, storageStore_executionEnv, initState] using
      storageLocStore_uint256 evmData ⟨3⟩ tag
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig evmTag
        { base := "packet", steps := [.field "data"] } = .ok ByteArray.empty.size := by
    simpa [evmSolm0, evmData, evmTag] using
      bytesStoreLitePacketDataLengthAfterEmptyTagStore
        (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) (tag := tag)
  have hCreated : (cA, σFinal).1 = evmTag.createdAccounts := by
    simp [evmTag, evmData, evmSolm0, storageStore_createdAccounts, initState]
  have hAccountsPost : accountMapEquiv σFinal evmTag.accountMap := by
    simpa [σFinal, evmTag, evmData, evmSolm0] using
      accountMapEquiv_storageStore_initState_codeOwner_two
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (⟨2⟩ : UInt256) (⟨0⟩ : UInt256) (⟨3⟩ : UInt256) tag
  have henc :
      returnEquiv (UInt256.toByteArray ⟨0⟩) (some (.int ByteArray.empty.size))
        setPacketTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty) (tag := tag)
    (o := UInt256.toByteArray ⟨0⟩) (acc := (cA, σFinal))
    (evmData := evmData) (evmTag := evmTag)
    hcode hwv hret hd hdec hwrite hstore hlen hCreated hAccountsPost henc

theorem bytesStoreLiteSetPacketShortNonemptyOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {tag len payloadStart : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf
          (BytesStoreLiteCore.setDecodedValueBytes I) tag))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := BytesStoreLiteCore.setDecodedValueBytes I
  let storedWord := bytesStoreLiteSetPacketShortStoredWord I len payloadStart
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmData := Solm.EVM.storageStore evmSolm0 I.codeOwner ⟨2⟩
    (solidityShortBytesWord value)
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  let σFinal :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σ_evm ⟨2⟩ storedWord) ⟨3⟩ tag
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, storedWord] using
      bytesStoreLiteX_setPacketShortNonemptyOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (tag := tag)
        (len := len) (payloadStart := payloadStart) (acc := accEvm)
        hperm hreach hlenMaxWord hflag hvalid hnz hshort haccEvm
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
          .ok evmData := by
    have hwrite₀ := bytesStoreLiteWritePacketDataDecodedShortPacked
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts hlenAbi hpayloadList hshort hflag hvalid
    simpa [evmSolm0, evmData, value] using hwrite₀
  have hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag := by
    simpa [evmTag, evmData, evmSolm0, storageStore_executionEnv, initState] using
      storageLocStore_uint256 evmData ⟨3⟩ tag
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value] using
      bytesStoreLiteSetPacketShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayloadList
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig evmTag
        { base := "packet", steps := [.field "data"] } = .ok value.size := by
    have hlen₀ := bytesStoreLitePacketDataLengthAfterShortTagStore
      (cA := cA) (gh := gh) (bl := bl) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (tag := tag)
      (len := len) (payloadStart := payloadStart) (acc := accSolm)
      haccSolm hnz hshort
    have hvalueSize : value.size = len.toNat := by
      dsimp [value]
      rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
      rw [← hlenAbi]
    simpa [evmSolm0, evmData, evmTag, storedWord, hstored, hvalueSize] using hlen₀
  have hCreated : (cA, σFinal).1 = evmTag.createdAccounts := by
    simp [evmTag, evmData, evmSolm0, storageStore_createdAccounts, initState]
  have hAccountsPost : accountMapEquiv σFinal evmTag.accountMap := by
    simpa [σFinal, evmTag, evmData, evmSolm0, hstored] using
      accountMapEquiv_storageStore_initState_codeOwner_two
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
        (⟨2⟩ : UInt256) (solidityShortBytesWord value) (⟨3⟩ : UInt256) tag
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setPacketTransition.returnType := by
    have hvalueSize : value.size = len.toNat := by
      dsimp [value]
      rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
      rw [← hlenAbi]
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hvalueSize]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value) (tag := tag)
    (o := UInt256.toByteArray len) (acc := (cA, σFinal))
    (evmData := evmData) (evmTag := evmTag)
    hcode hwv hret hd hdec hwrite hstore hlen hCreated hAccountsPost henc

theorem bytesStoreLiteSetPacketShortNonemptyOldLongRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {tag len payloadStart oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf
          (BytesStoreLiteCore.setDecodedValueBytes I) tag))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hnz : len.toNat ≠ 0)
    (hshort : len.toNat < 32) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := BytesStoreLiteCore.setDecodedValueBytes I
  let storedWord := bytesStoreLiteSetPacketShortStoredWord I len payloadStart
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σFinal :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σClear ⟨2⟩ storedWord) ⟨3⟩ tag
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear :=
    clearSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ 0 ((oldStoredLen.toNat + 31) / 32)
  let evmData := Solm.EVM.storageStore evmClear I.codeOwner ⟨2⟩
    (solidityShortBytesWord value)
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  obtain ⟨accClear, haccClear⟩ :=
    clearDataWordsForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (base := ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)))
      (idx := ⟨0⟩) haccEvm
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σClear, storedWord] using
      bytesStoreLiteX_setPacketShortNonemptyOldLongReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (tag := tag)
        (len := len) (payloadStart := payloadStart) (oldStoredLen := oldStoredLen)
        (acc := accClear)
        hperm hreach hlenMaxWord hflag holdStoredLen hvalid hnz hshort
        (by simpa [σClear] using haccClear)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
          .ok evmData := by
    have hvalidWrite :
        UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
          (UInt256.lt (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨32⟩) ≠ ⟨0⟩ := by
      simpa [holdStoredLen] using hvalid
    have hwrite₀ := bytesStoreLiteWritePacketDataDecodedShortFromLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts hlenAbi hpayloadList hshort hflag hvalidWrite
    simpa [evmSolm0, evmClear, evmData, value, holdStoredLen,
      clearSolidityBytesDataWordsFrom_executionEnv] using hwrite₀
  have hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag := by
    simpa [evmTag, evmData, evmClear, evmSolm0, storageStore_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, initState] using
      storageLocStore_uint256 evmData ⟨3⟩ tag
  have hstored : storedWord = solidityShortBytesWord value := by
    simpa [storedWord, value] using
      bytesStoreLiteSetPacketShortStoredWord_eq_solidityShortBytesWord
        (I := I) (len := len) (payloadStart := payloadStart)
        hlenAbi hpayloadStart hoffMax hnz hshort hsrc hpayloadList
  obtain ⟨accSolm, haccSolm⟩ :=
    accountMapEquiv_find?_some_exists hAccounts haccEvm
  obtain ⟨accSolmClear, haccSolmClear⟩ :=
    clearDataWordsForwardFrom_find?_some_exists_of_find_some
      (σ := σ_solm) (owner := I.codeOwner) (acc := accSolm)
      (base := solidityBytesDataBaseSlot (⟨2⟩ : UInt256)) (idx := UInt256.ofNat 0)
      haccSolm ((oldStoredLen.toNat + 31) / 32)
  have haccEvmClear :
      evmClear.accountMap.find? I.codeOwner = some accSolmClear := by
    simpa [evmClear, evmSolm0, initState, clearSolidityBytesDataWordsFrom_accountMap]
      using haccSolmClear
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig evmTag
        { base := "packet", steps := [.field "data"] } = .ok value.size := by
    have hlen₀ := bytesStoreLitePacketDataLengthAfterShortTagStoreOfState
      (evm := evmClear) (I := I) (tag := tag) (len := len)
      (payloadStart := payloadStart) (acc := accSolmClear)
      (by simp [evmClear, evmSolm0, initState, clearSolidityBytesDataWordsFrom_executionEnv])
      haccEvmClear hnz hshort
    have hvalueSize : value.size = len.toNat := by
      dsimp [value]
      rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
      rw [← hlenAbi]
    simpa [evmClear, evmData, evmTag, storedWord, hstored, hvalueSize] using hlen₀
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 := by
    exact BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hCreated : (cA, σFinal).1 = evmTag.createdAccounts := by
    simp [evmTag, evmData, evmClear, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have hAccountsData :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σClear ⟨2⟩ storedWord)
        evmData.accountMap := by
    simpa [σClear, evmData, evmClear, evmSolm0, value, storedWord, initState,
      clearSolidityBytesDataWordsFrom_executionEnv] using
      bytesStoreLiteSetPacketDataShortFromLongPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (oldLen := oldStoredLen) (storedWord := storedWord) (value := value)
        hAccounts hstored holdLenLt
  have hAccountsPost : accountMapEquiv σFinal evmTag.accountMap := by
    simpa [σFinal, evmTag, evmData] using
      accountMapEquiv_setPacketTagStore I.codeOwner tag hAccountsData
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setPacketTransition.returnType := by
    have hvalueSize : value.size = len.toNat := by
      dsimp [value]
      rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
      rw [← hlenAbi]
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hvalueSize]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value) (tag := tag)
    (o := UInt256.toByteArray len) (acc := (cA, σFinal))
    (evmData := evmData) (evmTag := evmTag)
    hcode hwv hret hd hdec hwrite hstore hlen hCreated hAccountsPost henc

theorem bytesStoreLiteSetPacketEmptyOldLongRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {tag len payloadStart oldStoredLen : UInt256}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf ByteArray.empty tag))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hlenZero : len = ⟨0⟩) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let σClear :=
    clearDataWordsForwardFrom I.codeOwner σ_evm
      ((⟨0⟩ : UInt256) + bytesLikeDataBase (⟨2⟩ : UInt256)) ⟨0⟩
      (UInt256.sub (UInt256.shiftRight (oldStoredLen + ⟨31⟩) ⟨5⟩) ⟨0⟩).toNat
  let σFinal :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σClear ⟨2⟩ ⟨0⟩) ⟨3⟩ tag
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear :=
    clearSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ 0 ((oldStoredLen.toNat + 31) / 32)
  let evmData := Solm.EVM.storageStore evmClear I.codeOwner ⟨2⟩ ⟨0⟩
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray ⟨0⟩) := by
    simpa [σFinal, σClear] using
      bytesStoreLiteX_setPacketEmptyOldLongReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (tag := tag)
        (len := len) (payloadStart := payloadStart) (oldStoredLen := oldStoredLen)
        hperm hreach hlenMaxWord hflag holdStoredLen hvalid hlenZero
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } .bytes (.bytes ByteArray.empty) =
          .ok evmData := by
    have hwrite₀ := bytesStoreLiteWritePacketDataEmptyFromLongPrepared
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (oldStoredLen := oldStoredLen)
      hAccounts holdStoredLen hflag hvalid
    simpa [evmSolm0, evmClear, evmData,
      clearSolidityBytesDataWordsFrom_executionEnv] using hwrite₀
  have hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag := by
    simpa [evmTag, evmData, evmClear, evmSolm0, storageStore_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, initState] using
      storageLocStore_uint256 evmData ⟨3⟩ tag
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig evmTag
        { base := "packet", steps := [.field "data"] } = .ok ByteArray.empty.size := by
    have hlen₀ := bytesStoreLitePacketDataLengthAfterEmptyTagStoreOfState
      (evm := evmClear) (I := I) (tag := tag)
      (by simp [evmClear, evmSolm0, initState, clearSolidityBytesDataWordsFrom_executionEnv])
    simpa [evmClear, evmData, evmTag] using hlen₀
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 := by
    exact BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
      (len := oldStoredLen) holdStoredLen
  have hCreated : (cA, σFinal).1 = evmTag.createdAccounts := by
    simp [evmTag, evmData, evmClear, evmSolm0, clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have hAccountsData :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σClear ⟨2⟩ ⟨0⟩)
        evmData.accountMap := by
    simpa [σClear, evmData, evmClear, evmSolm0, initState,
      clearSolidityBytesDataWordsFrom_executionEnv] using
      bytesStoreLiteSetPacketDataEmptyFromLongPostAccountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (oldLen := oldStoredLen) hAccounts holdLenLt
  have hAccountsPost : accountMapEquiv σFinal evmTag.accountMap := by
    simpa [σFinal, evmTag, evmData] using
      accountMapEquiv_setPacketTagStore I.codeOwner tag hAccountsData
  have henc :
      returnEquiv (UInt256.toByteArray ⟨0⟩) (some (.int ByteArray.empty.size))
        setPacketTransition.returnType := by
    change returnEquiv (UInt256.toByteArray (⟨0⟩ : UInt256)) (some (.int 0))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    exact returnEquiv_of_encode (uint256ReturnEncoding (⟨0⟩ : UInt256))
  exact bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := ByteArray.empty) (tag := tag)
    (o := UInt256.toByteArray ⟨0⟩) (acc := (cA, σFinal))
    (evmData := evmData) (evmTag := evmTag)
    hcode hwv hret hd hdec hwrite hstore hlen hCreated hAccountsPost henc

theorem bytesStoreLiteSetPacketLongNoTailOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {tag len payloadStart : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf
          (BytesStoreLiteCore.setDecodedValueBytes I) tag))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := BytesStoreLiteCore.setDecodedValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σFinal :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σLoop ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      ⟨3⟩ tag
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop := writeSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner ⟨2⟩ header
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
    rw [← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (⟨2⟩ : UInt256)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I) haccEvm (len.toNat / 32)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σLoop] using
      bytesStoreLiteX_setPacketLongNoTailOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (tag := tag)
        (len := len) (payloadStart := payloadStart) (acc := accLoop)
        hperm hreach hlenMaxWord hlenMax hflag hvalid hlong hnoTailMod
        (by simpa [σLoop] using haccLoop)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
          .ok evmData := by
    have hwrite₀ := bytesStoreLiteWritePacketDataDecodedLongPacked
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts hlenAbi hpayloadList hlong hflag hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header] using hwrite₀
  have hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag := by
    simpa [evmTag, evmData, evmLoop, evmSolm0, storageStore_executionEnv,
      writeSolidityBytesDataWordsFrom_executionEnv, initState] using
      storageLocStore_uint256 evmData ⟨3⟩ tag
  have hdataFuelEq : dataFuel = len.toNat / 32 := by
    dsimp [dataFuel]
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_eq_div_of_mod_zero hnoTailMod
  have hAccountsLoop : accountMapEquiv σLoop evmLoop.accountMap := by
    have hbridge :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (⟨2⟩ : UInt256)
            value 0 (len.toNat / 32))
          σLoop := by
      simpa [σLoop, value] using
        accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_zero
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          (baseSlot := (⟨2⟩ : UInt256)) hsrc haddrBound hsizeDecoded hlenAbi
          hpayloadStart hoffMax (τ := σ_evm) (fuel := len.toNat / 32) (by rfl)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (⟨2⟩ : UInt256)
            value 0 (len.toNat / 32))
          (solidityDataWordsForwardFrom I.codeOwner σ_solm (⟨2⟩ : UInt256)
            value 0 (len.toNat / 32)) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
        (baseSlot := (⟨2⟩ : UInt256)) (bytes := value)
        (idx := 0) (len.toNat / 32) hAccounts
    simpa [evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_accountMap, initState,
      hdataFuelEq] using accountMapEquiv.trans (accountMapEquiv.symm hbridge) hcong
  obtain ⟨accSolmLoop, haccSolmLoop⟩ :=
    accountMapEquiv_find?_some_exists hAccountsLoop haccLoop
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig evmTag
        { base := "packet", steps := [.field "data"] } = .ok value.size := by
    have hlen₀ := bytesStoreLitePacketDataLengthAfterLongTagStoreOfState
      (evm := evmLoop) (I := I) (tag := tag) (len := len) (header := header)
      (acc := accSolmLoop)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmLoop
      (by
        rw [hheaderEq]
        exact (bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax))
      (by
        rw [hheaderEq]
        symm
        exact (bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax))
      (by
        rw [hheaderEq]
        exact (bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong))
    simpa [evmLoop, evmData, evmTag, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using hlen₀
  have hCreated : (cA, σFinal).1 = evmTag.createdAccounts := by
    simp [evmTag, evmData, evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have hAccountsPost : accountMapEquiv σFinal evmTag.accountMap := by
    simpa [σFinal, evmTag, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using
      accountMapEquiv_setPacketDataHeaderAndTagStore I.codeOwner header tag hAccountsLoop
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setPacketTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value) (tag := tag)
    (o := UInt256.toByteArray len) (acc := (cA, σFinal))
    (evmData := evmData) (evmTag := evmTag)
    hcode hwv hret hd hdec hwrite hstore hlen hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongNoTailOldLongNoClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {tag len payloadStart oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf
          (BytesStoreLiteCore.setDecodedValueBytes I) tag))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := BytesStoreLiteCore.setDecodedValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σFinal :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σLoop ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      ⟨3⟩ tag
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop := writeSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner ⟨2⟩ header
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
    rw [← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (⟨2⟩ : UInt256)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I) haccEvm (len.toNat / 32)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σLoop] using
      bytesStoreLiteX_setPacketLongNoTailOldLongNoClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (tag := tag)
        (len := len) (payloadStart := payloadStart) (oldStoredLen := oldStoredLen)
        (acc := accLoop)
        hperm hreach hlenMaxWord hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
        hnoTailMod (by simpa [σLoop] using haccLoop)
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
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
          .ok evmData := by
    have hwrite₀ := bytesStoreLiteWritePacketDataLongFromLongPrepared
      (evm := evmSolm0) (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
      (len := oldStoredLen) (value := value)
      (by rw [hsizeDecoded]; exact hlong)
      hload hflag holdStoredLen hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header, hclearCountZero,
      hclearCountZeroLen, clearSolidityBytesDataWordsFrom, hdataFuelEq] using hwrite₀
  have hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag := by
    simpa [evmTag, evmData, evmLoop, evmSolm0, storageStore_executionEnv,
      writeSolidityBytesDataWordsFrom_executionEnv, initState] using
      storageLocStore_uint256 evmData ⟨3⟩ tag
  have hAccountsLoop : accountMapEquiv σLoop evmLoop.accountMap := by
    have hbridge :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (⟨2⟩ : UInt256)
            value 0 (len.toNat / 32))
          σLoop := by
      simpa [σLoop, value] using
        accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_zero
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          (baseSlot := (⟨2⟩ : UInt256)) hsrc haddrBound hsizeDecoded hlenAbi
          hpayloadStart hoffMax (τ := σ_evm) (fuel := len.toNat / 32) (by rfl)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σ_evm (⟨2⟩ : UInt256)
            value 0 (len.toNat / 32))
          (solidityDataWordsForwardFrom I.codeOwner σ_solm (⟨2⟩ : UInt256)
            value 0 (len.toNat / 32)) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
        (baseSlot := (⟨2⟩ : UInt256)) (bytes := value)
        (idx := 0) (len.toNat / 32) hAccounts
    simpa [evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_accountMap, initState,
      hdataFuelEq] using accountMapEquiv.trans (accountMapEquiv.symm hbridge) hcong
  obtain ⟨accSolmLoop, haccSolmLoop⟩ :=
    accountMapEquiv_find?_some_exists hAccountsLoop haccLoop
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig evmTag
        { base := "packet", steps := [.field "data"] } = .ok value.size := by
    have hlen₀ := bytesStoreLitePacketDataLengthAfterLongTagStoreOfState
      (evm := evmLoop) (I := I) (tag := tag) (len := len) (header := header)
      (acc := accSolmLoop)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmLoop
      (by
        rw [hheaderEq]
        exact (bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax))
      (by
        rw [hheaderEq]
        symm
        exact (bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax))
      (by
        rw [hheaderEq]
        exact (bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong))
    simpa [evmLoop, evmData, evmTag, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using hlen₀
  have hCreated : (cA, σFinal).1 = evmTag.createdAccounts := by
    simp [evmTag, evmData, evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have hAccountsPost : accountMapEquiv σFinal evmTag.accountMap := by
    simpa [σFinal, evmTag, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState] using
      accountMapEquiv_setPacketDataHeaderAndTagStore I.codeOwner header tag hAccountsLoop
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setPacketTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value) (tag := tag)
    (o := UInt256.toByteArray len) (acc := (cA, σFinal))
    (evmData := evmData) (evmTag := evmTag)
    hcode hwv hret hd hdec hwrite hstore hlen hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongNoTailOldLongClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {tag len payloadStart oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf
          (BytesStoreLiteCore.setDecodedValueBytes I) tag))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (hnoTailMod : len.toNat % 32 = 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := BytesStoreLiteCore.setDecodedValueBytes I
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
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase (⟨2⟩ : UInt256))
      ⟨0⟩ clearCount.toNat
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let σFinal :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σLoop ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      ⟨3⟩ tag
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ clearFuel tailFuel
  let evmLoop := writeSolidityBytesDataWordsFrom evmClear ⟨2⟩ value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner ⟨2⟩ header
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
    rw [← hlenAbi]
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
      (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
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
      (base := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase (⟨2⟩ : UInt256))
      (idx := (⟨0⟩ : UInt256)) haccEvm clearCount.toNat
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σClear) (owner := I.codeOwner) (acc := accClear)
      (slot := bytesLikeDataBase (⟨2⟩ : UInt256)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I)
      (by simpa [σClear, clearCount] using haccClear) (len.toNat / 32)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σLoop, σClear, clearCount] using
      bytesStoreLiteX_setPacketLongNoTailOldLongClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (tag := tag)
        (len := len) (payloadStart := payloadStart) (oldStoredLen := oldStoredLen)
        (acc := accLoop)
        hperm hreach hlenMaxWord hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
        hnoTailMod (by simpa [σLoop, σClear, clearCount] using haccLoop)
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
          .ok evmData := by
    have hwrite₀ := bytesStoreLiteWritePacketDataLongFromLongPrepared
      (evm := evmSolm0) (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
      (len := oldStoredLen) (value := value)
      (by rw [hsizeDecoded]; exact hlong)
      hload hflag holdStoredLen hvalid
    simpa [evmSolm0, evmClear, evmLoop, evmData, value, dataFuel, header,
      oldFuel, clearFuel, tailFuel, solidityBytesDataWordCount] using hwrite₀
  have hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag := by
    simpa [evmTag, evmData, evmLoop, evmClear, evmSolm0, storageStore_executionEnv,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, initState] using
      storageLocStore_uint256 evmData ⟨3⟩ tag
  have hAccountsClear : accountMapEquiv σClear evmClear.accountMap := by
    have hshift := accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
      (owner := I.codeOwner) (σ := σ_evm) (τ := σ_solm)
      (baseSlot := (⟨2⟩ : UInt256)) clearFuel (⟨0⟩ : UInt256) tailFuel hAccounts
    dsimp [σClear, evmClear, evmSolm0, clearCount]
    rw [hnewShiftEq, hcountNatShift]
    have hidxZero :
        UInt256.ofNat clearFuel + (⟨0⟩ : UInt256) = UInt256.ofNat clearFuel := by
      simpa using BytesStoreLiteCore.uint256_add_zero_right (UInt256.ofNat clearFuel)
    simpa [clearSolidityBytesDataWordsFrom_accountMap, initState, hidxZero,
      u256_add_comm (UInt256.ofNat clearFuel) (bytesLikeDataBase (⟨2⟩ : UInt256))]
      using hshift
  have hAccountsLoop : accountMapEquiv σLoop evmLoop.accountMap := by
    have hbridge :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σClear (⟨2⟩ : UInt256)
            value 0 (len.toNat / 32))
          σLoop := by
      simpa [σLoop, value] using
        accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_zero
          (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
          (baseSlot := (⟨2⟩ : UInt256)) hsrc haddrBound hsizeDecoded hlenAbi
          hpayloadStart hoffMax (τ := σClear) (fuel := len.toNat / 32) (by rfl)
    have hcong :
        accountMapEquiv
          (solidityDataWordsForwardFrom I.codeOwner σClear (⟨2⟩ : UInt256)
            value 0 (len.toNat / 32))
          (solidityDataWordsForwardFrom I.codeOwner evmClear.accountMap (⟨2⟩ : UInt256)
            value 0 (len.toNat / 32)) := by
      exact accountMapEquiv_solidityDataWordsForwardFrom
        (owner := I.codeOwner) (τ := σClear) (σ := evmClear.accountMap)
        (baseSlot := (⟨2⟩ : UInt256)) (bytes := value)
        (idx := 0) (len.toNat / 32) hAccountsClear
    simpa [evmLoop, evmClear, evmSolm0, writeSolidityBytesDataWordsFrom_accountMap,
      clearSolidityBytesDataWordsFrom_executionEnv, initState, hdataFuelEq] using
      accountMapEquiv.trans (accountMapEquiv.symm hbridge) hcong
  obtain ⟨accSolmLoop, haccSolmLoop⟩ :=
    accountMapEquiv_find?_some_exists hAccountsLoop haccLoop
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig evmTag
        { base := "packet", steps := [.field "data"] } = .ok value.size := by
    have hlen₀ := bytesStoreLitePacketDataLengthAfterLongTagStoreOfState
      (evm := evmLoop) (I := I) (tag := tag) (len := len) (header := header)
      (acc := accSolmLoop)
      (by simp [evmLoop, evmClear, evmSolm0, initState,
        writeSolidityBytesDataWordsFrom_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv])
      haccSolmLoop
      (by
        rw [hheaderEq]
        exact (bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax))
      (by
        rw [hheaderEq]
        symm
        exact (bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax))
      (by
        rw [hheaderEq]
        exact (bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong))
    simpa [evmLoop, evmData, evmTag, header, hsizeDecoded,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState] using hlen₀
  have hCreated : (cA, σFinal).1 = evmTag.createdAccounts := by
    simp [evmTag, evmData, evmLoop, evmClear, evmSolm0,
      writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have hAccountsPost : accountMapEquiv σFinal evmTag.accountMap := by
    simpa [σFinal, evmTag, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState] using
      accountMapEquiv_setPacketDataHeaderAndTagStore I.codeOwner header tag hAccountsLoop
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setPacketTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value) (tag := tag)
    (o := UInt256.toByteArray len) (acc := (cA, σFinal))
    (evmData := evmData) (evmTag := evmTag)
    hcode hwv hret hd hdec hwrite hstore hlen hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem accountMapEquiv_setPacketLongTailStorage
    {I : ExecutionEnv} {len payloadStart : UInt256}
    {σ_evm σ_solm : AccountMap}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlong : ¬ len.toNat < 32)
    (hmod : len.toNat % 32 ≠ 0)
    (hheader :
      solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size =
        len * (⟨2⟩ : UInt256) + ⟨1⟩) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
            (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
            (len.toNat / 32))
          (BytesStoreLiteCore.longDataWordsLoopSlot
            (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32))
          (BytesStoreLiteCore.longDataTailMaskedWord
            (bytesStoreLiteCalldataLongDataWord I payloadStart
              (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
              0) len))
        ⟨2⟩ (len * (⟨2⟩ : UInt256) + ⟨1⟩))
      (sstoreAccountMap I.codeOwner
        (solidityDataWordsForwardFrom I.codeOwner σ_solm (⟨2⟩ : UInt256)
          (BytesStoreLiteCore.setDecodedValueBytes I) 0
          (solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size))
        ⟨2⟩
        (solidityBytesHeaderWord (BytesStoreLiteCore.setDecodedValueBytes I).size)) := by
  let baseSlot : UInt256 := ⟨2⟩
  let fullFuel : Nat := len.toNat / 32
  have hdataFuelEq :
      solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size =
        fullFuel + 1 := by
    rw [hsize]
    dsimp [fullFuel]
    exact solidityBytesDataWordCount_eq_div_succ_of_mod_ne hmod
  have hbridgeEvm :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel)
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_zero
      (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
      (baseSlot := baseSlot) hsrc haddrBound hsize hlenAbi hpayloadStart hoffMax
      (τ := σ_evm) (fuel := fullFuel) (by dsimp [fullFuel]; omega)
  have hcong :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel)
        (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom
      (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
      (baseSlot := baseSlot) (bytes := BytesStoreLiteCore.setDecodedValueBytes I)
      (idx := 0) fullFuel hAccounts
  have hdataFull :
      accountMapEquiv
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
        (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel) :=
    accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
  have htailWord :
      BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len =
        uInt256OfByteArray
          ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding (fullFuel * 32) 32) := by
    simpa [fullFuel, Nat.mul_comm] using
      bytesStoreLiteCalldataLongDataTailMaskedWord_eq_decoded_tail
        (I := I) (len := len) (payloadStart := payloadStart)
        htailAddr hsrc hsize hlenAbi hpayloadStart hoffMax hlong hmod
  have hslotEq :
      BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel =
        solidityBytesDataSlot baseSlot fullFuel := by
    exact bytesStoreLiteLongDataWordsLoopSlot_bytesLikeDataBase baseSlot fullFuel
  have hstored :=
    accountMapEquiv_sstore_header_after_solidityDataWordsForwardFrom_succ_last
      (owner := I.codeOwner) (σ := bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner
        σ_evm (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
      (τ := σ_solm) (baseSlot := baseSlot)
      (slot := BytesStoreLiteCore.longDataWordsLoopSlot (bytesLikeDataBase baseSlot) fullFuel)
      (word := BytesStoreLiteCore.longDataTailMaskedWord
        (bytesStoreLiteCalldataLongDataWord I payloadStart
          (UInt256.ofNat (32 * fullFuel)) 0) len)
      (headerSlot := baseSlot) (header := len * (⟨2⟩ : UInt256) + ⟨1⟩)
      (bytes := BytesStoreLiteCore.setDecodedValueBytes I) (idx := 0) (fuel := fullFuel)
      hdataFull (by simpa using hslotEq) (by simpa using htailWord)
  simpa [baseSlot, fullFuel, hdataFuelEq, hheader,
    bytesStoreLiteLongDataWordsLoopStride_zero_ofNat] using hstored

set_option maxHeartbeats 1200000 in
theorem accountMapEquiv_setPacketLongTailDataStorage
    {I : ExecutionEnv} {len payloadStart : UInt256}
    {σ_evm σ_solm : AccountMap}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hsize : (BytesStoreLiteCore.setDecodedValueBytes I).size = len.toNat)
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hlong : ¬ len.toNat < 32)
    (hmod : len.toNat % 32 ≠ 0) :
    accountMapEquiv
      (sstoreAccountMap I.codeOwner
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
          (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
          (len.toNat / 32))
        (BytesStoreLiteCore.longDataWordsLoopSlot
          (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32))
        (BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
            0) len))
      (solidityDataWordsForwardFrom I.codeOwner σ_solm (⟨2⟩ : UInt256)
        (BytesStoreLiteCore.setDecodedValueBytes I) 0
        (solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size)) := by
  let baseSlot : UInt256 := ⟨2⟩
  let fullFuel : Nat := len.toNat / 32
  have hdataFuelEq :
      solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size =
        fullFuel + 1 := by
    rw [hsize]
    dsimp [fullFuel]
    exact solidityBytesDataWordCount_eq_div_succ_of_mod_ne hmod
  have hbridgeEvm :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel)
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom_calldataLongDataForwardFrom_full_zero
      (I := I) (len := len) (payloadStart := payloadStart) (owner := I.codeOwner)
      (baseSlot := baseSlot) hsrc haddrBound hsize hlenAbi hpayloadStart hoffMax
      (τ := σ_evm) (fuel := fullFuel) (by dsimp [fullFuel]; omega)
  have hcong :
      accountMapEquiv
        (solidityDataWordsForwardFrom I.codeOwner σ_evm baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel)
        (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel) := by
    exact accountMapEquiv_solidityDataWordsForwardFrom
      (owner := I.codeOwner) (τ := σ_evm) (σ := σ_solm)
      (baseSlot := baseSlot) (bytes := BytesStoreLiteCore.setDecodedValueBytes I)
      (idx := 0) fullFuel hAccounts
  have hdataFull :
      accountMapEquiv
        (bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
          (bytesLikeDataBase baseSlot) payloadStart (⟨0⟩ : UInt256) I fullFuel)
        (solidityDataWordsForwardFrom I.codeOwner σ_solm baseSlot
          (BytesStoreLiteCore.setDecodedValueBytes I) 0 fullFuel) :=
    accountMapEquiv.trans (accountMapEquiv.symm hbridgeEvm) hcong
  have htailWord :
      BytesStoreLiteCore.longDataTailMaskedWord
          (bytesStoreLiteCalldataLongDataWord I payloadStart
            (UInt256.ofNat (32 * fullFuel)) 0) len =
        uInt256OfByteArray
          ((BytesStoreLiteCore.setDecodedValueBytes I).readWithPadding (fullFuel * 32) 32) := by
    simpa [fullFuel, Nat.mul_comm] using
      bytesStoreLiteCalldataLongDataTailMaskedWord_eq_decoded_tail
        (I := I) (len := len) (payloadStart := payloadStart)
        htailAddr hsrc hsize hlenAbi hpayloadStart hoffMax hlong hmod
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
      (bytes := BytesStoreLiteCore.setDecodedValueBytes I) (idx := 0) (fuel := fullFuel)
      hdataFull (by simpa using hslotEq) (by simpa using htailWord)
  simpa [baseSlot, fullFuel, hdataFuelEq,
    bytesStoreLiteLongDataWordsLoopStride_zero_ofNat] using htailStore

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongTailOldShortRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {tag len payloadStart : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf
          (BytesStoreLiteCore.setDecodedValueBytes I) tag))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ = ⟨0⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt
          (UInt256.land
            (UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
            ⟨127⟩)
          ⟨32⟩) ≠ ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := BytesStoreLiteCore.setDecodedValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
        0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData := sstoreAccountMap I.codeOwner σTail ⟨2⟩
    (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop := writeSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner ⟨2⟩ header
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
    rw [← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (⟨2⟩ : UInt256)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I) haccEvm (len.toNat / 32)
  obtain ⟨accTail, haccTail⟩ :=
    sstoreAccountMap_find?_some_exists_of_find_some
      (σ := σLoop) (a := I.codeOwner) (acc := accLoop)
      (slot := tailSlot) (val := tailWord) (by simpa [σLoop] using haccLoop)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σData, σTail, σLoop, tailSlot, tailWord] using
      bytesStoreLiteX_setPacketLongTailOldShortReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (tag := tag)
        (len := len) (payloadStart := payloadStart) (acc := accTail)
        hperm hreach hlenMaxWord hlenMax hflag hvalid hlong htailMod
        (by simpa [σTail, σLoop, tailSlot, tailWord] using haccTail)
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
          .ok evmData := by
    have hwrite₀ := bytesStoreLiteWritePacketDataDecodedLongPacked
      (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) (len := len)
      hAccounts hlenAbi hpayloadList hlong hflag hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header] using hwrite₀
  have hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag := by
    simpa [evmTag, evmData, evmLoop, evmSolm0, storageStore_executionEnv,
      writeSolidityBytesDataWordsFrom_executionEnv, initState] using
      storageLocStore_uint256 evmData ⟨3⟩ tag
  have hdataFuelEq : dataFuel = len.toNat / 32 + 1 := by
    dsimp [dataFuel]
    rw [hsizeDecoded]
    exact solidityBytesDataWordCount_eq_div_succ_of_mod_ne htailMod
  have hdataFuelCount :
      solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size =
        len.toNat / 32 + 1 := by
    simpa [dataFuel, value] using hdataFuelEq
  have hAccountsTail : accountMapEquiv σTail evmLoop.accountMap := by
    have hbridge := accountMapEquiv_setPacketLongTailDataStorage
      (I := I) (len := len) (payloadStart := payloadStart)
      (σ_evm := σ_evm) (σ_solm := σ_solm)
      hAccounts hsrc haddrBound htailAddr hsizeDecoded hlenAbi hpayloadStart
      hoffMax hlong htailMod
    simpa [σTail, σLoop, tailSlot, tailWord, evmLoop, evmSolm0, initState, value,
      hdataFuelEq, hdataFuelCount, writeSolidityBytesDataWordsFrom_accountMap] using hbridge
  obtain ⟨accSolmTail, haccSolmTail⟩ :=
    accountMapEquiv_find?_some_exists hAccountsTail haccTail
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig evmTag
        { base := "packet", steps := [.field "data"] } = .ok value.size := by
    have hlen₀ := bytesStoreLitePacketDataLengthAfterLongTagStoreOfState
      (evm := evmLoop) (I := I) (tag := tag) (len := len) (header := header)
      (acc := accSolmTail)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmTail
      (by
        rw [hheaderEq]
        exact (bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax))
      (by
        rw [hheaderEq]
        symm
        exact (bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax))
      (by
        rw [hheaderEq]
        exact (bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong))
    simpa [evmLoop, evmData, evmTag, evmSolm0, initState, header, hsizeDecoded,
      storageStore_executionEnv, writeSolidityBytesDataWordsFrom_executionEnv] using hlen₀
  have hCreated : (cA, σFinal).1 = evmTag.createdAccounts := by
    simp [evmTag, evmData, evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have hAccountsPost : accountMapEquiv σFinal evmTag.accountMap := by
    simpa [σFinal, σData, evmTag, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState, header] using
      accountMapEquiv_setPacketDataHeaderAndTagStore I.codeOwner header tag hAccountsTail
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setPacketTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value) (tag := tag)
    (o := UInt256.toByteArray len) (acc := (cA, σFinal))
    (evmData := evmData) (evmTag := evmTag)
    hcode hwv hret hd hdec hwrite hstore hlen hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongTailOldLongNoClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {tag len payloadStart oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf
          (BytesStoreLiteCore.setDecodedValueBytes I) tag))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨0⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := BytesStoreLiteCore.setDecodedValueBytes I
  let dataFuel : Nat := solidityBytesDataWordCount value.size
  let header : UInt256 := solidityBytesHeaderWord value.size
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σ_evm
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
        0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData := sstoreAccountMap I.codeOwner σTail ⟨2⟩
    (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmLoop := writeSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner ⟨2⟩ header
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
    rw [← hlenAbi]
  have hheaderEq : header = len * (⟨2⟩ : UInt256) + ⟨1⟩ := by
    dsimp [header]
    exact BytesStoreLiteCore.solidityBytesHeaderWord_eq_len_mul_two_add_one
      (len := len) (n := value.size) hsizeDecoded hlong hlenMax
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σ_evm) (owner := I.codeOwner) (acc := accEvm)
      (slot := bytesLikeDataBase (⟨2⟩ : UInt256)) (payloadStart := payloadStart)
      (stride := (⟨0⟩ : UInt256)) (I := I) haccEvm (len.toNat / 32)
  obtain ⟨accTail, haccTail⟩ :=
    sstoreAccountMap_find?_some_exists_of_find_some
      (σ := σLoop) (a := I.codeOwner) (acc := accLoop)
      (slot := tailSlot) (val := tailWord) (by simpa [σLoop] using haccLoop)
  have hret :
      RDret bytesStoreLiteBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, σFinal)
        (UInt256.toByteArray len) := by
    simpa [σFinal, σData, σTail, σLoop, tailSlot, tailWord] using
      bytesStoreLiteX_setPacketLongTailOldLongNoClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (tag := tag)
        (len := len) (payloadStart := payloadStart) (oldStoredLen := oldStoredLen)
        (acc := accTail)
        hperm hreach hlenMaxWord hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
        htailMod (by simpa [σTail, σLoop, tailSlot, tailWord] using haccTail)
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
  have hdataCountEq :
      solidityBytesDataWordCount value.size = len.toNat / 32 + 1 := by
    simpa [dataFuel] using hdataFuelEq
  have hclearCountZeroLen :
      solidityBytesDataWordCount oldStoredLen.toNat - (len.toNat / 32 + 1) = 0 := by
    simpa [hdataCountEq] using hclearCountZero
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
          .ok evmData := by
    have hwrite₀ := bytesStoreLiteWritePacketDataLongFromLongPrepared
      (evm := evmSolm0) (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
      (len := oldStoredLen) (value := value)
      (by rw [hsizeDecoded]; exact hlong)
      hload hflag holdStoredLen hvalid
    simpa [evmSolm0, evmLoop, evmData, value, dataFuel, header, hclearCountZero,
      hclearCountZeroLen, clearSolidityBytesDataWordsFrom, hdataFuelEq] using hwrite₀
  have hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag := by
    simpa [evmTag, evmData, evmLoop, evmSolm0, storageStore_executionEnv,
      writeSolidityBytesDataWordsFrom_executionEnv, initState] using
      storageLocStore_uint256 evmData ⟨3⟩ tag
  have hAccountsTail : accountMapEquiv σTail evmLoop.accountMap := by
    have hbridge := accountMapEquiv_setPacketLongTailDataStorage
      (I := I) (len := len) (payloadStart := payloadStart)
      (σ_evm := σ_evm) (σ_solm := σ_solm)
      hAccounts hsrc haddrBound htailAddr hsizeDecoded hlenAbi hpayloadStart
      hoffMax hlong htailMod
    simpa [σTail, σLoop, tailSlot, tailWord, evmLoop, evmSolm0, initState, value,
      hdataFuelEq, hdataCountEq, writeSolidityBytesDataWordsFrom_accountMap] using hbridge
  obtain ⟨accSolmTail, haccSolmTail⟩ :=
    accountMapEquiv_find?_some_exists hAccountsTail haccTail
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig evmTag
        { base := "packet", steps := [.field "data"] } = .ok value.size := by
    have hlen₀ := bytesStoreLitePacketDataLengthAfterLongTagStoreOfState
      (evm := evmLoop) (I := I) (tag := tag) (len := len) (header := header)
      (acc := accSolmTail)
      (by simp [evmLoop, evmSolm0, initState, writeSolidityBytesDataWordsFrom_executionEnv])
      haccSolmTail
      (by
        rw [hheaderEq]
        exact (bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax))
      (by
        rw [hheaderEq]
        symm
        exact (bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax))
      (by
        rw [hheaderEq]
        exact (bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong))
    simpa [evmLoop, evmData, evmTag, evmSolm0, initState, header, hsizeDecoded,
      storageStore_executionEnv, writeSolidityBytesDataWordsFrom_executionEnv] using hlen₀
  have hCreated : (cA, σFinal).1 = evmTag.createdAccounts := by
    simp [evmTag, evmData, evmLoop, evmSolm0, writeSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have hAccountsPost : accountMapEquiv σFinal evmTag.accountMap := by
    simpa [σFinal, σData, evmTag, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv, evmSolm0, initState, header] using
      accountMapEquiv_setPacketDataHeaderAndTagStore I.codeOwner header tag hAccountsTail
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setPacketTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value) (tag := tag)
    (o := UInt256.toByteArray len) (acc := (cA, σFinal))
    (evmData := evmData) (evmTag := evmTag)
    hcode hwv hret hd hdec hwrite hstore hlen hCreated hAccountsPost henc

set_option maxHeartbeats 1200000 in
theorem bytesStoreLiteSetPacketLongTailOldLongClearRuntimeOfReach
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {tag len payloadStart oldStoredLen : UInt256} {accEvm : Account}
    (hcode : I.code = bytesStoreLiteBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (haccEvm : σ_evm.find? I.codeOwner = some accEvm)
    (hreach : ∃ k C, RD bytesStoreLiteBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨969⟩
      [tag, len, payloadStart, ⟨263⟩, bytesStoreLiteSelWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hd : dispatchMsg bytesStoreLiteContract I.calldata = some setPacketTransition)
    (hdec : decodeCalldata (setPacketTransition.params.map Param.name)
      (transitionSignature setPacketTransition).paramTypes I.calldata =
        some (bytesStoreLiteSetPacketLocalsOf
          (BytesStoreLiteCore.setDecodedValueBytes I) tag))
    (hlenAbi :
      len = calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat))
    (hpayloadStart :
      payloadStart = (((⟨4⟩ : UInt256) + calldataWord I.calldata 4) + ⟨32⟩))
    (hoffMax : ¬ ABI.solcMaxU64 < (calldataWord I.calldata 4).toNat)
    (hsrc : payloadStart.toNat + len.toNat ≤ I.calldata.size)
    (haddrBound :
      ∀ i, i < len.toNat / 32 →
        payloadStart.toNat + 32 * i < UInt256.size)
    (htailAddr :
      (payloadStart + UInt256.ofNat (32 * (len.toNat / 32))).toNat =
        payloadStart.toNat + 32 * (len.toNat / 32))
    (hpayloadList :
      ((((I.calldata.toList.drop 4).drop ((calldataWord I.calldata 4).toNat + 32)).take
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat).length =
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat))
    (hlenMaxWord : UInt256.gt len ⟨18446744073709551615⟩ = ⟨0⟩)
    (hlenMax : len.toNat ≤ ABI.solcMaxU64)
    (hflag :
      UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩ ≠ ⟨0⟩)
    (holdStoredLen :
      oldStoredLen = UInt256.div (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨2⟩)
    (hvalid :
      UInt256.sub (UInt256.land (bytesStoreLitePacketLengthHeaderWord σ_evm I) ⟨1⟩)
        (UInt256.lt oldStoredLen ⟨32⟩) ≠ ⟨0⟩)
    (hgtOldNew : UInt256.gt oldStoredLen len = ⟨1⟩)
    (hlong : ¬ len.toNat < 32)
    (htailMod : len.toNat % 32 ≠ 0) :
    runtimeEquivalenceFor bytesStoreLiteConfig bytesStoreLiteContract cA gh bl
      σ_evm σ_solm σ₀ g A I := by
  let value := BytesStoreLiteCore.setDecodedValueBytes I
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
      (UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase (⟨2⟩ : UInt256))
      ⟨0⟩ clearCount.toNat
  let σLoop :=
    bytesStoreLiteCalldataLongDataForwardFrom I.codeOwner σClear
      (bytesLikeDataBase (⟨2⟩ : UInt256)) payloadStart (⟨0⟩ : UInt256) I
      (len.toNat / 32)
  let tailSlot :=
    BytesStoreLiteCore.longDataWordsLoopSlot
      (bytesLikeDataBase (⟨2⟩ : UInt256)) (len.toNat / 32)
  let tailWord :=
    BytesStoreLiteCore.longDataTailMaskedWord
      (bytesStoreLiteCalldataLongDataWord I payloadStart
        (BytesStoreLiteCore.longDataWordsLoopStride (⟨0⟩ : UInt256) (len.toNat / 32))
        0) len
  let σTail := sstoreAccountMap I.codeOwner σLoop tailSlot tailWord
  let σData := sstoreAccountMap I.codeOwner σTail ⟨2⟩
    (len * (⟨2⟩ : UInt256) + ⟨1⟩)
  let σFinal := sstoreAccountMap I.codeOwner σData ⟨3⟩ tag
  let evmSolm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmClear := clearSolidityBytesDataWordsFrom evmSolm0 ⟨2⟩ clearFuel tailFuel
  let evmLoop := writeSolidityBytesDataWordsFrom evmClear ⟨2⟩ value 0 dataFuel
  let evmData := Solm.EVM.storageStore evmLoop evmLoop.executionEnv.codeOwner ⟨2⟩ header
  let evmTag := Solm.EVM.storageStore evmData I.codeOwner ⟨3⟩ tag
  have hsizeDecoded : value.size = len.toNat := by
    dsimp [value]
    rw [BytesStoreLiteCore.setDecodedValueBytes_size hpayloadList]
    rw [← hlenAbi]
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
      solidityBytesDataWordCount (BytesStoreLiteCore.setDecodedValueBytes I).size =
        len.toNat / 32 + 1 := by
    simpa [dataFuel, value] using hdataFuelEq
  have hclearLeOld : clearFuel ≤ oldFuel := by
    dsimp [oldFuel]
    rw [hclearFuelCeil]
    exact solidityBytesDataWordCount_mono (Nat.le_of_lt holdGtNat)
  have holdLenLt : oldStoredLen.toNat < 2 ^ 255 :=
    BytesStoreLiteCore.clearCurrent_len_toNat_lt_sign_of_div2
      (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
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
      (base := UInt256.shiftRight (len + ⟨31⟩) ⟨5⟩ + bytesLikeDataBase (⟨2⟩ : UInt256))
      (idx := (⟨0⟩ : UInt256)) haccEvm clearCount.toNat
  obtain ⟨accLoop, haccLoop⟩ :=
    bytesStoreLiteCalldataLongDataForwardFrom_find?_some_exists_of_find_some
      (σ := σClear) (owner := I.codeOwner) (acc := accClear)
      (slot := bytesLikeDataBase (⟨2⟩ : UInt256)) (payloadStart := payloadStart)
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
    simpa [σFinal, σData, σTail, σLoop, σClear, clearCount, tailSlot, tailWord] using
      bytesStoreLiteX_setPacketLongTailOldLongClearReturns
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (A := A) (I := I) (g := Sat256.ofUInt256 g) (tag := tag)
        (len := len) (payloadStart := payloadStart) (oldStoredLen := oldStoredLen)
        (acc := accTail)
        hperm hreach hlenMaxWord hlenMax hflag holdStoredLen hvalid hgtOldNew hlong
        htailMod (by simpa [σTail, σLoop, σClear, clearCount, tailSlot, tailWord] using haccTail)
  have hload :
      Solm.EVM.storageLoad evmSolm0 evmSolm0.executionEnv.codeOwner ⟨2⟩ =
        bytesStoreLitePacketLengthHeaderWord σ_evm I := by
    simpa [evmSolm0] using
      bytesStoreLiteStorageLoadPacketLength_initState_of_accountMapEquiv
        (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
        (I := I) (g := Sat256.ofUInt256 g) hAccounts
  have hwrite :
      writeStorage? bytesStoreLiteConfig evmSolm0
        { base := "packet", steps := [.field "data"] } .bytes (.bytes value) =
          .ok evmData := by
    have hwrite₀ := bytesStoreLiteWritePacketDataLongFromLongPrepared
      (evm := evmSolm0) (header := bytesStoreLitePacketLengthHeaderWord σ_evm I)
      (len := oldStoredLen) (value := value)
      (by rw [hsizeDecoded]; exact hlong)
      hload hflag holdStoredLen hvalid
    simpa [evmSolm0, evmClear, evmLoop, evmData, value, dataFuel, header,
      oldFuel, clearFuel, tailFuel, solidityBytesDataWordCount] using hwrite₀
  have hstore :
      storageLocStore evmData (uint256Loc ⟨3⟩) (.int (Int.ofNat tag.toNat)) =
        some evmTag := by
    simpa [evmTag, evmData, evmLoop, evmClear, evmSolm0, storageStore_executionEnv,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, initState] using
      storageLocStore_uint256 evmData ⟨3⟩ tag
  have hAccountsClear : accountMapEquiv σClear evmClear.accountMap := by
    have hshift := accountMapEquiv_clearDataWordsForwardFrom_shift_bytesLikeBase
      (owner := I.codeOwner) (σ := σ_evm) (τ := σ_solm)
      (baseSlot := (⟨2⟩ : UInt256)) clearFuel (⟨0⟩ : UInt256) tailFuel hAccounts
    dsimp [σClear, evmClear, evmSolm0, clearCount]
    rw [hnewShiftEq, hcountNatShift]
    have hidxZero :
        UInt256.ofNat clearFuel + (⟨0⟩ : UInt256) = UInt256.ofNat clearFuel := by
      simpa using BytesStoreLiteCore.uint256_add_zero_right (UInt256.ofNat clearFuel)
    simpa [clearSolidityBytesDataWordsFrom_accountMap, initState, hidxZero,
      u256_add_comm (UInt256.ofNat clearFuel) (bytesLikeDataBase (⟨2⟩ : UInt256))]
      using hshift
  have hAccountsTail : accountMapEquiv σTail evmLoop.accountMap := by
    have hbridge := accountMapEquiv_setPacketLongTailDataStorage
      (I := I) (len := len) (payloadStart := payloadStart)
      (σ_evm := σClear) (σ_solm := evmClear.accountMap)
      hAccountsClear hsrc haddrBound htailAddr hsizeDecoded hlenAbi hpayloadStart
      hoffMax hlong htailMod
    simpa [σTail, σLoop, σClear, clearCount, tailSlot, tailWord, evmLoop, evmClear,
      evmSolm0, initState, value, hdataFuelEq, hdataCountEq,
      writeSolidityBytesDataWordsFrom_accountMap,
      clearSolidityBytesDataWordsFrom_executionEnv] using hbridge
  obtain ⟨accSolmTail, haccSolmTail⟩ :=
    accountMapEquiv_find?_some_exists hAccountsTail haccTail
  have hlen :
      readStorageBytesLength? bytesStoreLiteConfig evmTag
        { base := "packet", steps := [.field "data"] } = .ok value.size := by
    have hlen₀ := bytesStoreLitePacketDataLengthAfterLongTagStoreOfState
      (evm := evmLoop) (I := I) (tag := tag) (len := len) (header := header)
      (acc := accSolmTail)
      (by simp [evmLoop, evmClear, evmSolm0, initState,
        writeSolidityBytesDataWordsFrom_executionEnv,
        clearSolidityBytesDataWordsFrom_executionEnv])
      haccSolmTail
      (by
        rw [hheaderEq]
        exact (bytesStoreLiteSetPacketLongHeader_flag_ne_zero (len := len) hlenMax))
      (by
        rw [hheaderEq]
        symm
        exact (bytesStoreLiteSetPacketLongHeader_div_two (len := len) hlenMax))
      (by
        rw [hheaderEq]
        exact (bytesStoreLiteSetPacketLongHeader_valid (len := len) hlenMax hlong))
    simpa [evmLoop, evmData, evmTag, evmSolm0, initState, header, hsizeDecoded,
      storageStore_executionEnv, writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear] using hlen₀
  have hCreated : (cA, σFinal).1 = evmTag.createdAccounts := by
    simp [evmTag, evmData, evmLoop, evmClear, evmSolm0,
      writeSolidityBytesDataWordsFrom_createdAccounts,
      clearSolidityBytesDataWordsFrom_createdAccounts,
      storageStore_createdAccounts, initState]
  have hAccountsPost : accountMapEquiv σFinal evmTag.accountMap := by
    simpa [σFinal, σData, evmTag, evmData, evmLoop, hheaderEq,
      writeSolidityBytesDataWordsFrom_executionEnv,
      clearSolidityBytesDataWordsFrom_executionEnv, evmClear, evmSolm0, initState, header] using
      accountMapEquiv_setPacketDataHeaderAndTagStore I.codeOwner header tag hAccountsTail
  have henc :
      returnEquiv (UInt256.toByteArray len) (some (.int value.size))
        setPacketTransition.returnType := by
    change returnEquiv (UInt256.toByteArray len) (some (.int value.size))
      (some (.elem (.int (.uint ⟨256, by decide⟩))))
    rw [hsizeDecoded]
    exact returnEquiv_of_encode (uint256ReturnEncoding len)
  exact bytesStoreLiteSetPacketRuntimeOfWriteAccountMapEquiv
    (cA := cA) (gh := gh) (bl := bl) (σ_evm := σ_evm) (σ_solm := σ_solm)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) (value := value) (tag := tag)
    (o := UInt256.toByteArray len) (acc := (cA, σFinal))
    (evmData := evmData) (evmTag := evmTag)
    hcode hwv hret hd hdec hwrite hstore hlen hCreated hAccountsPost henc

end BytesStoreLite
