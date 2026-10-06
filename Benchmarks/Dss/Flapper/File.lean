import Reasoning.PackedStorage
import Reasoning.ABILegacy
import Benchmarks.Dss.Flapper.Deny

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Flapper

/-! ## `file(bytes32,uint256)` -/

abbrev fileWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileBegBytes : List UInt8 :=
  [98, 101, 103] ++ zeroPad29

abbrev fileLidBytes : List UInt8 :=
  [108, 105, 100] ++ zeroPad29

abbrev fileTtlBytes : List UInt8 :=
  [116, 116, 108] ++ zeroPad29

abbrev fileTauBytes : List UInt8 :=
  [116, 97, 117] ++ zeroPad29

abbrev fileLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileWhat I))).insert
    "data" (.int (Int.ofNat (fileData I).toNat))


theorem flapperDecode_file_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
      (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I) := by
  simpa [config, fileTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileLocals, fileWhat, fileData, abiBytes32, abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem flapperDecode_file_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
      (transitionSignature fileTransition).paramTypes I.calldata = none := by
  simpa [config, fileTransition, bytes32, bytes32Width, uint256, uint256Int, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem fileWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileWhat I).length = 32 := by
  simp [fileWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (fileWhat I) = calldataWord I.calldata 4 := by
  simpa [fileWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem fileWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hbs : fileWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileWhatWord_eq (I := I) hsz36).symm

theorem fileWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileWhat I)
    (fileWhat_length (I := I) hsz36)
  rw [fileWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : fileWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileWhat_eq_of_word_eq hsz36 hword hbsLen)

theorem fileLocals_get_what (I : ExecutionEnv) :
    (fileLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileWhat I)) := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileLocals_get_data (I : ExecutionEnv) :
    (fileLocals I).get? "data" =
      some (.int (Int.ofNat (fileData I).toNat)) := by
  rw [fileLocals, store_get_self]

theorem fileLocals_get_wards (I : ExecutionEnv) :
    (fileLocals I).get? "wards" = none := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileLocals_get_beg (I : ExecutionEnv) :
    (fileLocals I).get? "beg" = none := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileLocals_get_lid (I : ExecutionEnv) :
    (fileLocals I).get? "lid" = none := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileLocals_get_ttl (I : ExecutionEnv) :
    (fileLocals I).get? "ttl" = none := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileLocals_get_tau (I : ExecutionEnv) :
    (fileLocals I).get? "tau" = none := by
  rw [fileLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileData I).toNat))
  rw [h]
  rfl

theorem evalExpr_wrap48FileData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (wrap48 (.var "data")) =
      .ok (.int (Int.ofNat (fileData I).toNat % uint48Modulus)) := by
  unfold wrap48
  rw [evalExpr?]
  simp only [evalExpr?, h, EvalResult.bind, pure, bind]
  change evalBinaryOp? BinaryOp.mod (Value.int (Int.ofNat (fileData I).toNat))
      (Value.int uint48Modulus) =
    .ok (.int (Int.ofNat (fileData I).toNat % uint48Modulus))
  simp [evalBinaryOp?, uint48Modulus]
  all_goals decide

theorem evalExpr_fileWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileWhat I)))
    (hwhat : fileWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileWhat I)))
    (hwhat : fileWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide


def fileBegPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ (fileData I)

def fileLidPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ (fileData I)

def fileTtlStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  setUint48Offset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
    (fileData I)

def fileTtlPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ (fileTtlStoredWord evm I)

def fileTtlStoredWordMap (I : ExecutionEnv) (σ : AccountMap) : UInt256 :=
  setUint48Offset0Word (solcSlotWord σ I ⟨5⟩) (fileData I)

def fileTtlPostAccountMap (I : ExecutionEnv) (σ : AccountMap) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨5⟩ (fileTtlStoredWordMap I σ)

def fileTauStoredWord (evm : EVM.State) (I : ExecutionEnv) : UInt256 :=
  setUint48Offset6Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
    (fileData I)

def fileTauPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ (fileTauStoredWord evm I)

def fileTauStoredWordMap (I : ExecutionEnv) (σ : AccountMap) : UInt256 :=
  setUint48Offset6Word (solcSlotWord σ I ⟨5⟩) (fileData I)

def fileTauPostAccountMap (I : ExecutionEnv) (σ : AccountMap) : AccountMap :=
  sstoreAccountMap I.codeOwner σ ⟨5⟩ (fileTauStoredWordMap I σ)

theorem assign_fileBegStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := fileLocals I } evm
      .storage begRef (.int (Int.ofNat (fileData I).toNat)) =
        .ok ({ contract := contract, locals := fileLocals I }, fileBegPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "beg", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨4⟩)
      (hbase := fileLocals_get_beg I)
      (her := by simp [begRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [fileBegPostState, wordLoc, uint256Loc] using
    storageLocStore_uint256 evm ⟨4⟩ (fileData I)

theorem assign_fileLidStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := fileLocals I } evm
      .storage lidRef (.int (Int.ofNat (fileData I).toNat)) =
        .ok ({ contract := contract, locals := fileLocals I }, fileLidPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "lid", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨8⟩)
      (hbase := fileLocals_get_lid I)
      (her := by simp [lidRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [fileLidPostState, wordLoc, uint256Loc] using
    storageLocStore_uint256 evm ⟨8⟩ (fileData I)

theorem assign_fileTtlStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := fileLocals I } evm
      .storage ttlRef (.int (Int.ofNat (fileData I).toNat % uint48Modulus)) =
        .ok ({ contract := contract, locals := fileLocals I }, fileTtlPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint48St)
      (er := ({ base := "ttl", steps := [] } : EvaledStorageRef))
      (loc := uint48Loc ⟨5⟩ ⟨0, by decide⟩ (by decide))
      (hbase := fileLocals_get_ttl I)
      (her := by simp [ttlRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint48St])
      (hloc := by rfl)
  simpa [fileTtlPostState, fileTtlStoredWord, uint48Loc] using
    storageLocStore_uint48_offset0_word evm ⟨5⟩ (fileData I)

theorem assign_fileTauStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := fileLocals I } evm
      .storage tauRef (.int (Int.ofNat (fileData I).toNat % uint48Modulus)) =
        .ok ({ contract := contract, locals := fileLocals I }, fileTauPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint48St)
      (er := ({ base := "tau", steps := [] } : EvaledStorageRef))
      (loc := uint48Loc ⟨5⟩ ⟨6, by decide⟩ (by decide))
      (hbase := fileLocals_get_tau I)
      (her := by simp [tauRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint48St])
      (hloc := by rfl)
  simpa [fileTauPostState, fileTauStoredWord, uint48Loc] using
    storageLocStore_uint48_offset6_word evm ⟨5⟩ (fileData I)

theorem flapperFileBegSourceBody {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileWhat I = fileBegBytes) :
    let locals := fileLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileBegPostState evm0 I
    ExecTransitionBody config contract evm0 locals fileTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simp [locals])
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") begParamLit) = .ok (.bool true) := by
    simpa [begParamLit, fileBegBytes] using
      (evalExpr_fileWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileBegBytes) (by simpa [locals] using fileLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileData I).toNat)) := by
    exact evalExpr_fileData (evm := evm0) (I := I) (locals := locals)
      (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage begRef (.int (Int.ofNat (fileData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileBegStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage begRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem flapperFileTtlSourceBody {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hbeg : fileWhat I ≠ fileBegBytes)
    (httl : fileWhat I = fileTtlBytes) :
    let locals := fileLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileTtlPostState evm0 I
    ExecTransitionBody config contract evm0 locals fileTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simp [locals])
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hbegCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") begParamLit) = .ok (.bool false) := by
    simpa [begParamLit, fileBegBytes] using
      (evalExpr_fileWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileBegBytes) (by simpa [locals] using fileLocals_get_what I) hbeg)
  have httlCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") ttlParamLit) = .ok (.bool true) := by
    simpa [ttlParamLit, fileTtlBytes] using
      (evalExpr_fileWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileTtlBytes) (by simpa [locals] using fileLocals_get_what I) httl)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (wrap48 (.var "data")) =
        .ok (.int (Int.ofNat (fileData I).toNat % uint48Modulus)) := by
    exact evalExpr_wrap48FileData (evm := evm0) (I := I) (locals := locals)
      (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage ttlRef (.int (Int.ofNat (fileData I).toNat % uint48Modulus)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileTtlStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage ttlRef (wrap48 (.var "data"))]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have httlBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite
          (.binary .eq (.var "what") ttlParamLit)
          [.assign .storage ttlRef (wrap48 (.var "data"))]
          [.ite
            (.binary .eq (.var "what") tauParamLit)
            [.assign .storage tauRef (wrap48 (.var "data"))]
            [.ite
              (.binary .eq (.var "what") lidParamLit)
              [.assign .storage lidRef (.var "data")]
              [.require (.boolLit false)]]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue httlCond hthen) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbegCond httlBlock) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 1000000 in
theorem flapperFileTauSourceBody {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hbeg : fileWhat I ≠ fileBegBytes)
    (httl : fileWhat I ≠ fileTtlBytes)
    (htau : fileWhat I = fileTauBytes) :
    let locals := fileLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileTauPostState evm0 I
    ExecTransitionBody config contract evm0 locals fileTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simp [locals])
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hbegCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") begParamLit) = .ok (.bool false) := by
    simpa [begParamLit, fileBegBytes] using
      (evalExpr_fileWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileBegBytes) (by simpa [locals] using fileLocals_get_what I) hbeg)
  have httlCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") ttlParamLit) = .ok (.bool false) := by
    simpa [ttlParamLit, fileTtlBytes] using
      (evalExpr_fileWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileTtlBytes) (by simpa [locals] using fileLocals_get_what I) httl)
  have htauCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") tauParamLit) = .ok (.bool true) := by
    simpa [tauParamLit, fileTauBytes] using
      (evalExpr_fileWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileTauBytes) (by simpa [locals] using fileLocals_get_what I) htau)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (wrap48 (.var "data")) =
        .ok (.int (Int.ofNat (fileData I).toNat % uint48Modulus)) := by
    exact evalExpr_wrap48FileData (evm := evm0) (I := I) (locals := locals)
      (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage tauRef (.int (Int.ofNat (fileData I).toNat % uint48Modulus)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileTauStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage tauRef (wrap48 (.var "data"))]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have htauBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite
          (.binary .eq (.var "what") tauParamLit)
          [.assign .storage tauRef (wrap48 (.var "data"))]
          [.ite
            (.binary .eq (.var "what") lidParamLit)
            [.assign .storage lidRef (.var "data")]
            [.require (.boolLit false)]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue htauCond hthen) ExecBlock.nil
  have httlBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite
          (.binary .eq (.var "what") ttlParamLit)
          [.assign .storage ttlRef (wrap48 (.var "data"))]
          [.ite
            (.binary .eq (.var "what") tauParamLit)
            [.assign .storage tauRef (wrap48 (.var "data"))]
            [.ite
              (.binary .eq (.var "what") lidParamLit)
              [.assign .storage lidRef (.var "data")]
              [.require (.boolLit false)]]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse httlCond htauBlock) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbegCond httlBlock) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 1000000 in
theorem flapperFileLidSourceBody {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hbeg : fileWhat I ≠ fileBegBytes)
    (httl : fileWhat I ≠ fileTtlBytes)
    (htau : fileWhat I ≠ fileTauBytes)
    (hlid : fileWhat I = fileLidBytes) :
    let locals := fileLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileLidPostState evm0 I
    ExecTransitionBody config contract evm0 locals fileTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simp [locals])
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hbegCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") begParamLit) = .ok (.bool false) := by
    simpa [begParamLit, fileBegBytes] using
      (evalExpr_fileWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileBegBytes) (by simpa [locals] using fileLocals_get_what I) hbeg)
  have httlCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") ttlParamLit) = .ok (.bool false) := by
    simpa [ttlParamLit, fileTtlBytes] using
      (evalExpr_fileWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileTtlBytes) (by simpa [locals] using fileLocals_get_what I) httl)
  have htauCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") tauParamLit) = .ok (.bool false) := by
    simpa [tauParamLit, fileTauBytes] using
      (evalExpr_fileWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileTauBytes) (by simpa [locals] using fileLocals_get_what I) htau)
  have hlidCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") lidParamLit) = .ok (.bool true) := by
    simpa [lidParamLit, fileLidBytes] using
      (evalExpr_fileWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileLidBytes) (by simpa [locals] using fileLocals_get_what I) hlid)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileData I).toNat)) := by
    exact evalExpr_fileData (evm := evm0) (I := I) (locals := locals)
      (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage lidRef (.int (Int.ofNat (fileData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileLidStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage lidRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hlidBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite
          (.binary .eq (.var "what") lidParamLit)
          [.assign .storage lidRef (.var "data")]
          [.require (.boolLit false)]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hlidCond hthen) ExecBlock.nil
  have htauBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite
          (.binary .eq (.var "what") tauParamLit)
          [.assign .storage tauRef (wrap48 (.var "data"))]
          [.ite
            (.binary .eq (.var "what") lidParamLit)
            [.assign .storage lidRef (.var "data")]
            [.require (.boolLit false)]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse htauCond hlidBlock) ExecBlock.nil
  have httlBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite
          (.binary .eq (.var "what") ttlParamLit)
          [.assign .storage ttlRef (wrap48 (.var "data"))]
          [.ite
            (.binary .eq (.var "what") tauParamLit)
            [.assign .storage tauRef (wrap48 (.var "data"))]
            [.ite
              (.binary .eq (.var "what") lidParamLit)
              [.assign .storage lidRef (.var "data")]
              [.require (.boolLit false)]]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse httlCond htauBlock) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbegCond httlBlock) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem flapperFileSourceBodyAuthReverts {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := fileLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    exact evalExpr_auth_false_of_wards_none evm0 I locals
      (by simp [locals])
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.ite
        (.binary .eq (.var "what") begParamLit)
        [.assign .storage begRef (.var "data")]
        [.ite
          (.binary .eq (.var "what") ttlParamLit)
          [.assign .storage ttlRef (wrap48 (.var "data"))]
          [.ite
            (.binary .eq (.var "what") tauParamLit)
            [.assign .storage tauRef (wrap48 (.var "data"))]
            [.ite
              (.binary .eq (.var "what") lidParamLit)
              [.assign .storage lidRef (.var "data")]
              [.require (.boolLit false)]]]]])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem flapperFileSourceBodyUnrecognized {σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hbeg : fileWhat I ≠ fileBegBytes)
    (httl : fileWhat I ≠ fileTtlBytes)
    (htau : fileWhat I ≠ fileTauBytes)
    (hlid : fileWhat I ≠ fileLidBytes) :
    let locals := fileLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simp [locals])
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, solcSlotWordAt, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hbegCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") begParamLit) = .ok (.bool false) := by
    simpa [begParamLit, fileBegBytes] using
      (evalExpr_fileWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileBegBytes) (by simpa [locals] using fileLocals_get_what I) hbeg)
  have httlCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") ttlParamLit) = .ok (.bool false) := by
    simpa [ttlParamLit, fileTtlBytes] using
      (evalExpr_fileWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileTtlBytes) (by simpa [locals] using fileLocals_get_what I) httl)
  have htauCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") tauParamLit) = .ok (.bool false) := by
    simpa [tauParamLit, fileTauBytes] using
      (evalExpr_fileWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileTauBytes) (by simpa [locals] using fileLocals_get_what I) htau)
  have hlidCond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") lidParamLit) = .ok (.bool false) := by
    simpa [lidParamLit, fileLidBytes] using
      (evalExpr_fileWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileLidBytes) (by simpa [locals] using fileLocals_get_what I) hlid)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hrequireFalse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hlidBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite
          (.binary .eq (.var "what") lidParamLit)
          [.assign .storage lidRef (.var "data")]
          [.require (.boolLit false)]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hlidCond hrequireFalse)
  have htauBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite
          (.binary .eq (.var "what") tauParamLit)
          [.assign .storage tauRef (wrap48 (.var "data"))]
          [.ite
            (.binary .eq (.var "what") lidParamLit)
            [.assign .storage lidRef (.var "data")]
            [.require (.boolLit false)]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse htauCond hlidBlock)
  have httlBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite
          (.binary .eq (.var "what") ttlParamLit)
          [.assign .storage ttlRef (wrap48 (.var "data"))]
          [.ite
            (.binary .eq (.var "what") tauParamLit)
            [.assign .storage tauRef (wrap48 (.var "data"))]
            [.ite
              (.binary .eq (.var "what") lidParamLit)
              [.assign .storage lidRef (.var "data")]
              [.require (.boolLit false)]]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse httlCond htauBlock)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hbegCond httlBlock)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flapperReachFileBody {σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flapperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flapperSelBytes 5)) :
    ∃ k C, RD flapperBytecode I g (initState σ σ₀ g A I)
        ⟨362⟩ [flapperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        σ k C := by
  have hword : flapperSelWord I = ⟨0x29ae8114⟩ := by
    simpa [flapperSelWord, solcSelectorWord] using
      solcSelectorWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨0x29ae8114⟩
        (by native_decide) (by simpa [flapperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flapperBytecode flapperRootSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flapperBytecode flapperLowSplitPc)
      (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  obtain ⟨_, _, hfirst⟩ :=
    flapperReachLowLowFirstArm (σ := σ)
      (σ₀ := σ₀) (A := A) (I := I) (g := g) hcode hwv hsz hsize hroot hlow
  have heq0 : ∀ j, j < 2 →
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowLowFirstArmPc j))
        (flapperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat flapperBytecode (nthArmPc flapperBytecode flapperLowLowFirstArmPc 2))
        (flapperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo ⟨362⟩ 2 hfirst
    (fun j hj => flapperLowLowArmsWellFormed j (le_trans hj (by omega)))
    heq0 htake (by jump_dest) (by native_decide) (by simp)

theorem RD.flapperFileDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
    (h : RD code ee g s0 ⟨384⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = flapperBytecode)
    (hroutine : (D_J code 0).contains ⟨1225⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1225⟩
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd359 := h.jumpdest (by native_decide) (by evm_ov)
  have rd360 := rd359.pop (by native_decide) (by evm_ov)
  have rd361 := rd360.dup1 (by native_decide) (by evm_ov)
  have rd362 := rd361.calldataload (by native_decide) (by evm_ov)
  have rd363 := rd362.swap1 (by native_decide) (by evm_ov)
  have rd365 := rd363.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd366 := rd365.add (by native_decide) (by evm_ov)
  have rd367 := rd366.calldataload (by native_decide) (by evm_ov)
  have rd370 := rd367.push2 ⟨1225⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd370.jump (by native_decide) hroutine (by evm_ov)⟩

theorem flapperFileX_decoded {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState σ σ₀ g A I) ⟨362⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k C, RD flapperBytecode I g (initState σ σ₀ g A I) ⟨1225⟩
        [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flapperBytecode) (sel := sel) (entry := ⟨362⟩) (ret := ⟨360⟩)
    (decoded := ⟨384⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.flapperFileDecodeToRoutine
    (code := flapperBytecode) (ret := ⟨360⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileData] using hroutine⟩

set_option maxHeartbeats 1000000 in
theorem flapperFileX_authorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD flapperBytecode I g s0 ⟨1225⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨1318⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1221pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1222 := rd1221pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1226pre := evm_run rd1222 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1227 := rd1226pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1230pre := evm_run rd1227 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1231 := rd1230pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1232, C1232, rd1232raw⟩ := rd1231.sload (by native_decide) (by evm_ov)
  have rd1232 : RD flapperBytecode I g s0 ⟨1242⟩
      (relyAuthWord σ I :: fileData I :: calldataWord I.calldata 4 :: ⟨360⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k1232 C1232 := by
    simpa [relyAuthWord, solcSlotWordAt, relyAuthStorageSlot_eq_mapSlot_source I] using
      rd1232raw
  have rd1235pre := evm_run rd1232 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1235pre
  have rd1238 := rd1235pre.pushConst (⟨1318⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1238.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem flapperFileX_unauthorized {σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD flapperBytecode I g s0 ⟨1225⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev flapperBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1221pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1222 := rd1221pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1226pre := evm_run rd1222 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1227 := rd1226pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1230pre := evm_run rd1227 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1231 := rd1230pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1232, C1232, rd1232raw⟩ := rd1231.sload (by native_decide) (by evm_ov)
  have rd1232 : RD flapperBytecode I g s0 ⟨1242⟩
      (relyAuthWord σ I :: fileData I :: calldataWord I.calldata 4 :: ⟨360⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k1232 C1232 := by
    simpa [relyAuthWord, solcSlotWordAt, relyAuthStorageSlot_eq_mapSlot_source I] using
      rd1232raw
  have rd1235pre := evm_run rd1232 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1235pre
  have rd1238 := rd1235pre.pushConst (⟨1318⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1239 := rd1238.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1249⟩)
    (len := ⟨22⟩)
    (rawWord := ⟨0x119b185c1c195c8bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨82⟩)
    (word := ⟨0x466c61707065722f6e6f742d617574686f72697a656400000000000000000000⟩)
    (op := .PUSH22)
    (width := 22)
    rd1239
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem flapperFileX_shortarg {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD flapperBytecode I g
      (initState σ σ₀ g A I) ⟨362⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev flapperBytecode g (initState σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flapperBytecode) (sel := sel) (entry := ⟨362⟩) (ret := ⟨360⟩)
    (decoded := ⟨384⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

abbrev flapperFileUnrecognizedRawWord : UInt256 :=
  ⟨0x466c61707065722f66696c652d756e7265636f676e697a65642d706172616d00⟩

theorem RD.flapperFileUnrecognizedRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (h : RD flapperBytecode ee g s0 ⟨1466⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev flapperBytecode g s0 := by
  have rdMload := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨31⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨31⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst flapperFileUnrecognizedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨31⟩ flapperFileUnrecognizedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨31⟩ flapperFileUnrecognizedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem flapperFileX_storeBegAuthorized {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (hperm : I.perm = true)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileBegBytes)
    (h : RD flapperBytecode I g s0 ⟨1318⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret flapperBytecode g s0
      (sstoreAccountMap I.codeOwner σ ⟨4⟩ (fileData I))
      ByteArray.empty := by
  have rd1309 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1310 := rd1309.dup2 (by native_decide) (by evm_ov)
  have rd1314 := rd1310.pushConst (⟨0x626567⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1316 := rd1314.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd1317 := rd1316.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨0x626567⟩ : UInt256) ⟨232⟩ =
      ABI.bytesToWord fileBegBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd1317
  have rd1318 := rd1317.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd1318
  have rd1319 := rd1318.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1319
  have rd1322 := rd1319.pushConst (⟨1342⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1323 := rd1322.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1325 := rd1323.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd1326 := rd1325.dup2 (by native_decide) (by evm_ov)
  have rd1327 := rd1326.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1328raw⟩ := rd1327.sstore hperm (by native_decide) (by evm_ov)
  have rd1331 := rd1328raw.push2 ⟨1543⟩ (by native_decide) (by evm_ov)
  have rd1533 := rd1331.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1534 := rd1533.jumpdest (by native_decide) (by evm_ov)
  have rd1535 := rd1534.pop (by native_decide) (by evm_ov)
  have rd1536 := rd1535.pop (by native_decide) (by evm_ov)
  have rd334 := rd1536.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd335 := rd334.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd335 (by native_decide) (by evm_ov)

theorem flapperFileX_skipBeg {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hbeg : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes)
    (h : RD flapperBytecode I g s0 ⟨1318⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨1342⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have rd1309 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1310 := rd1309.dup2 (by native_decide) (by evm_ov)
  have rd1314 := rd1310.pushConst (⟨0x626567⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1316 := rd1314.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd1317 := rd1316.shl (by native_decide) (by evm_ov)
  have hbegConst : UInt256.shiftLeft (⟨0x626567⟩ : UInt256) ⟨232⟩ =
      ABI.bytesToWord fileBegBytes := by
    native_decide
  rw [hbegConst] at rd1317
  have rd1318 := rd1317.eq (by native_decide) (by evm_ov)
  have hbegEq0 : UInt256.eq (ABI.bytesToWord fileBegBytes)
      (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hbeg h.symm)
  rw [hbegEq0] at rd1318
  have rd1319 := rd1318.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1319
  have rd1322 := rd1319.pushConst (⟨1342⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1332 := rd1322.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact ⟨_, _, rd1332⟩

set_option maxHeartbeats 1000000 in
theorem flapperFileX_takeTtl {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileTtlBytes)
    (h : RD flapperBytecode I g s0 ⟨1342⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨1357⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have rd1333 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1334 := rd1333.dup2 (by native_decide) (by evm_ov)
  have rd1338 := rd1334.pushConst (⟨0x1d1d1b⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1340 := rd1338.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd1341 := rd1340.shl (by native_decide) (by evm_ov)
  have httlConst : UInt256.shiftLeft (⟨0x1d1d1b⟩ : UInt256) ⟨234⟩ =
      ABI.bytesToWord fileTtlBytes := by
    native_decide
  rw [httlConst] at rd1341
  have rd1342 := rd1341.eq (by native_decide) (by evm_ov)
  have httlEq1 : UInt256.eq (ABI.bytesToWord fileTtlBytes)
      (calldataWord I.calldata 4) = ⟨1⟩ := by
    rw [hmatch]
    exact u256_eq_refl (ABI.bytesToWord fileTtlBytes)
  rw [httlEq1] at rd1342
  have rd1343 := rd1342.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1343
  have rd1346 := rd1343.pushConst (⟨1386⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1347 := rd1346.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact ⟨_, _, rd1347⟩

theorem flapperFileX_skipTtl {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (httl : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTtlBytes)
    (h : RD flapperBytecode I g s0 ⟨1342⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨1386⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have rd1333 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1334 := rd1333.dup2 (by native_decide) (by evm_ov)
  have rd1338 := rd1334.pushConst (⟨0x1d1d1b⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1340 := rd1338.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd1341 := rd1340.shl (by native_decide) (by evm_ov)
  have httlConst : UInt256.shiftLeft (⟨0x1d1d1b⟩ : UInt256) ⟨234⟩ =
      ABI.bytesToWord fileTtlBytes := by
    native_decide
  rw [httlConst] at rd1341
  have rd1342 := rd1341.eq (by native_decide) (by evm_ov)
  have httlEq0 : UInt256.eq (ABI.bytesToWord fileTtlBytes)
      (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => httl h.symm)
  rw [httlEq0] at rd1342
  have rd1343 := rd1342.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1343
  have rd1346 := rd1343.pushConst (⟨1386⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1356 := rd1346.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact ⟨_, _, rd1356⟩

set_option maxHeartbeats 1000000 in
theorem flapperFileX_takeTau {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileTauBytes)
    (h : RD flapperBytecode I g s0 ⟨1386⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨1401⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have rd1401 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1402 := rd1401.dup2 (by native_decide) (by evm_ov)
  have rd1406 := rd1402.pushConst (⟨0x746175⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1408 := rd1406.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd1409 := rd1408.shl (by native_decide) (by evm_ov)
  have htauConst : UInt256.shiftLeft (⟨0x746175⟩ : UInt256) ⟨232⟩ =
      ABI.bytesToWord fileTauBytes := by
    native_decide
  rw [htauConst] at rd1409
  have rd1410 := rd1409.eq (by native_decide) (by evm_ov)
  have htauEq1 : UInt256.eq (ABI.bytesToWord fileTauBytes)
      (calldataWord I.calldata 4) = ⟨1⟩ := by
    rw [hmatch]
    exact u256_eq_refl (ABI.bytesToWord fileTauBytes)
  rw [htauEq1] at rd1410
  have rd1411 := rd1410.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1411
  have rd1414 := rd1411.pushConst (⟨1442⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1415 := rd1414.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact ⟨_, _, rd1415⟩

theorem flapperFileX_skipTau {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (htau : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTauBytes)
    (h : RD flapperBytecode I g s0 ⟨1386⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨1442⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have rd1401 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1402 := rd1401.dup2 (by native_decide) (by evm_ov)
  have rd1406 := rd1402.pushConst (⟨0x746175⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1408 := rd1406.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd1409 := rd1408.shl (by native_decide) (by evm_ov)
  have htauConst : UInt256.shiftLeft (⟨0x746175⟩ : UInt256) ⟨232⟩ =
      ABI.bytesToWord fileTauBytes := by
    native_decide
  rw [htauConst] at rd1409
  have rd1410 := rd1409.eq (by native_decide) (by evm_ov)
  have htauEq0 : UInt256.eq (ABI.bytesToWord fileTauBytes)
      (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => htau h.symm)
  rw [htauEq0] at rd1410
  have rd1411 := rd1410.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1411
  have rd1414 := rd1411.pushConst (⟨1442⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1456 := rd1414.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact ⟨_, _, rd1456⟩

set_option maxHeartbeats 1000000 in
theorem flapperFileX_takeLid {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileLidBytes)
    (h : RD flapperBytecode I g s0 ⟨1442⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨1457⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have rd1457 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1458 := rd1457.dup2 (by native_decide) (by evm_ov)
  have rd1462 := rd1458.pushConst (⟨0x1b1a59⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1464 := rd1462.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd1465 := rd1464.shl (by native_decide) (by evm_ov)
  have hlidConst : UInt256.shiftLeft (⟨0x1b1a59⟩ : UInt256) ⟨234⟩ =
      ABI.bytesToWord fileLidBytes := by
    native_decide
  rw [hlidConst] at rd1465
  have rd1466 := rd1465.eq (by native_decide) (by evm_ov)
  have hlidEq1 : UInt256.eq (ABI.bytesToWord fileLidBytes)
      (calldataWord I.calldata 4) = ⟨1⟩ := by
    rw [hmatch]
    exact u256_eq_refl (ABI.bytesToWord fileLidBytes)
  rw [hlidEq1] at rd1466
  have rd1467 := rd1466.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1467
  have rd1470 := rd1467.pushConst (⟨1466⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1471 := rd1470.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact ⟨_, _, rd1471⟩

theorem flapperFileX_skipLid {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hlid : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileLidBytes)
    (h : RD flapperBytecode I g s0 ⟨1442⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    ∃ k' C', RD flapperBytecode I g s0 ⟨1466⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k' C' := by
  have rd1457 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1458 := rd1457.dup2 (by native_decide) (by evm_ov)
  have rd1462 := rd1458.pushConst (⟨0x1b1a59⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1464 := rd1462.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd1465 := rd1464.shl (by native_decide) (by evm_ov)
  have hlidConst : UInt256.shiftLeft (⟨0x1b1a59⟩ : UInt256) ⟨234⟩ =
      ABI.bytesToWord fileLidBytes := by
    native_decide
  rw [hlidConst] at rd1465
  have rd1466 := rd1465.eq (by native_decide) (by evm_ov)
  have hlidEq0 : UInt256.eq (ABI.bytesToWord fileLidBytes)
      (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hlid h.symm)
  rw [hlidEq0] at rd1466
  have rd1467 := rd1466.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1467
  have rd1470 := rd1467.pushConst (⟨1466⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1471 := rd1470.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact ⟨_, _, rd1471⟩

set_option maxHeartbeats 1000000 in
theorem RD.flapperFileStoreTtlTail {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {what sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (h : RD flapperBytecode I g s0 ⟨1357⟩ [fileData I, what, ⟨360⟩, sel]
      mem aw rdata σ k C) :
    RDret flapperBytecode g s0
      (fileTtlPostAccountMap I σ)
      ByteArray.empty := by
  have rd1373 := h.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  have rd1374 := rd1373.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k1375, C1375, rd1375raw⟩ := rd1374.sload (by native_decide) (by evm_ov)
  have rd1375 : RD flapperBytecode I g s0 ⟨1361⟩
      ((σ.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD ⟨5⟩ ⟨0⟩)) ::
        ⟨5⟩ :: fileData I :: what :: ⟨360⟩ :: [sel])
      mem aw rdata σ k1375 C1375 := by
    exact rd1375raw
  have rd1382 := rd1375.pushConst uint48Mask
    (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have rd1384pre := evm_run rd1382 with [
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have rd1391 := rd1384pre.pushConst uint48Mask
    (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
  have rd1393pre := evm_run rd1391 with [
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have rd1394 := rd1393pre.or (by native_decide) (by evm_ov)
  have rd1395 := rd1394.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1396raw⟩ := rd1395.sstore hperm (by native_decide) (by evm_ov)
  have hword :
      UInt256.lor (UInt256.land (fileData I) uint48Mask)
          (UInt256.land
            (UInt256.lnot uint48Mask)
            (σ.get? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.getD ⟨5⟩ ⟨0⟩))) =
        fileTtlStoredWordMap I σ := by
    rw [u256_land_comm (UInt256.lnot uint48Mask)]
    simp [fileTtlStoredWordMap, setUint48Offset0Word, solcSlotWord, u256_lor_comm]
  have rd1399 := rd1396raw.push2 ⟨1543⟩ (by native_decide) (by evm_ov)
  have rd1533 := rd1399.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1534 := rd1533.jumpdest (by native_decide) (by evm_ov)
  have rd1535 := rd1534.pop (by native_decide) (by evm_ov)
  have rd1536 := rd1535.pop (by native_decide) (by evm_ov)
  have rd334 := rd1536.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd335 := rd334.jumpdest (by native_decide) (by evm_ov)
  simpa [-Std.ExtTreeMap.get?_eq_getElem?, fileTtlPostAccountMap, hword] using RD.stop rd335 (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem RD.flapperFileStoreTauTail {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {what sel : UInt256} {mem rdata : ByteArray} {aw : UInt256}
    (hperm : I.perm = true)
    (h : RD flapperBytecode I g s0 ⟨1401⟩ [fileData I, what, ⟨360⟩, sel]
      mem aw rdata σ k C) :
    RDret flapperBytecode g s0
      (fileTauPostAccountMap I σ)
      ByteArray.empty := by
  have rd1417 := h.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  have rd1418 := rd1417.dup1 (by native_decide) (by evm_ov)
  obtain ⟨k1419, C1419, rd1419raw⟩ := rd1418.sload (by native_decide) (by evm_ov)
  have rd1419 : RD flapperBytecode I g s0 ⟨1405⟩
      ((σ.get? I.codeOwner |>.option ⟨0⟩ (fun acc => acc.storage.getD ⟨5⟩ ⟨0⟩)) ::
        ⟨5⟩ :: fileData I :: what :: ⟨360⟩ :: [sel])
      mem aw rdata σ k1419 C1419 := by
    exact rd1419raw
  have rd1433pre := evm_run
    (rd1419.pushConst uint48Offset6Mask
      (width := 12) (op := .PUSH12) (by decide) (by native_decide) (by evm_ov)) with [
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have rd1436 := rd1433pre.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1438 := rd1436.push1 ⟨48⟩ (by native_decide) (by evm_ov)
  have rd1439 := rd1438.shl (by native_decide) (by evm_ov)
  have hfactor : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨48⟩ =
      UInt256.ofNat (2 ^ 48) := by
    native_decide
  rw [hfactor] at rd1439
  have rd1446pre := evm_run
    (rd1439.pushConst uint48Mask
      (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)) with [
    raw dup5 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw mul (by native_decide) (by evm_ov)]
  have rd1449 := rd1446pre.or (by native_decide) (by evm_ov)
  have rd1450 := rd1449.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1451raw⟩ := rd1450.sstore hperm (by native_decide) (by evm_ov)
  have hword :
      UInt256.lor
          (UInt256.mul (UInt256.land (fileData I) uint48Mask)
            (UInt256.ofNat (2 ^ 48)))
          (UInt256.land
            (UInt256.lnot uint48Offset6Mask)
            (σ.get? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.getD ⟨5⟩ ⟨0⟩))) =
        fileTauStoredWordMap I σ := by
    rw [u256_land_comm (UInt256.lnot uint48Offset6Mask)]
    simp [fileTauStoredWordMap, setUint48Offset6Word, solcSlotWord, u256_lor_comm]
  have rd1455 := rd1451raw.push2 ⟨1543⟩ (by native_decide) (by evm_ov)
  have rd1533 := rd1455.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1534 := rd1533.jumpdest (by native_decide) (by evm_ov)
  have rd1535 := rd1534.pop (by native_decide) (by evm_ov)
  have rd1536 := rd1535.pop (by native_decide) (by evm_ov)
  have rd334 := rd1536.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd335 := rd334.jumpdest (by native_decide) (by evm_ov)
  rw [hword] at rd335
  simpa [fileTauPostAccountMap] using RD.stop rd335 (by native_decide) (by evm_ov)

set_option maxHeartbeats 1000000 in
theorem flapperFileX_storeTtlAuthorized {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (hperm : I.perm = true)
    (hbeg : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileTtlBytes)
    (h : RD flapperBytecode I g s0 ⟨1318⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret flapperBytecode g s0
      (fileTtlPostAccountMap I σ)
      ByteArray.empty := by
  obtain ⟨_, _, h1342⟩ := flapperFileX_skipBeg hbeg h
  obtain ⟨_, _, h1357⟩ := flapperFileX_takeTtl hmatch h1342
  exact RD.flapperFileStoreTtlTail hperm h1357

set_option maxHeartbeats 1000000 in
theorem flapperFileX_storeTauAuthorized {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (hperm : I.perm = true)
    (hbeg : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes)
    (httl : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTtlBytes)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileTauBytes)
    (h : RD flapperBytecode I g s0 ⟨1318⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret flapperBytecode g s0
      (fileTauPostAccountMap I σ)
      ByteArray.empty := by
  obtain ⟨_, _, h1342⟩ := flapperFileX_skipBeg hbeg h
  obtain ⟨_, _, h1386⟩ := flapperFileX_skipTtl httl h1342
  obtain ⟨_, _, h1401⟩ := flapperFileX_takeTau hmatch h1386
  exact RD.flapperFileStoreTauTail hperm h1401

theorem flapperFileX_storeLidAuthorized {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (hperm : I.perm = true)
    (hbeg : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes)
    (httl : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTtlBytes)
    (htau : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTauBytes)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileLidBytes)
    (h : RD flapperBytecode I g s0 ⟨1318⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDret flapperBytecode g s0
      (sstoreAccountMap I.codeOwner σ ⟨8⟩ (fileData I))
      ByteArray.empty := by
  obtain ⟨_, _, h1342⟩ := flapperFileX_skipBeg hbeg h
  obtain ⟨_, _, h1386⟩ := flapperFileX_skipTtl httl h1342
  obtain ⟨_, _, h1442⟩ := flapperFileX_skipTau htau h1386
  obtain ⟨_, _, h1457⟩ := flapperFileX_takeLid hmatch h1442
  have rd1459 := h1457.push1 ⟨8⟩ (by native_decide) (by evm_ov)
  have rd1460 := rd1459.dup2 (by native_decide) (by evm_ov)
  have rd1461 := rd1460.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1462raw⟩ := rd1461.sstore hperm (by native_decide) (by evm_ov)
  have rd1465 := rd1462raw.push2 ⟨1543⟩ (by native_decide) (by evm_ov)
  have rd1543 := rd1465.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1544 := rd1543.jumpdest (by native_decide) (by evm_ov)
  have rd1545 := rd1544.pop (by native_decide) (by evm_ov)
  have rd1546 := rd1545.pop (by native_decide) (by evm_ov)
  have rd360 := rd1546.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd361 := rd360.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd361 (by native_decide) (by evm_ov)


theorem flapperFileX_unrecognized {σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hbeg : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes)
    (httl : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTtlBytes)
    (htau : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTauBytes)
    (hlid : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileLidBytes)
    (h : RD flapperBytecode I g s0 ⟨1318⟩
      [fileData I, calldataWord I.calldata 4, ⟨360⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty σ k C) :
    RDrev flapperBytecode g s0 := by
  obtain ⟨_, _, h1342⟩ := flapperFileX_skipBeg hbeg h
  obtain ⟨_, _, h1386⟩ := flapperFileX_skipTtl httl h1342
  obtain ⟨_, _, h1442⟩ := flapperFileX_skipTau htau h1386
  obtain ⟨_, _, h1466⟩ := flapperFileX_skipLid hlid h1442
  exact RD.flapperFileUnrecognizedRevert h1466
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem flapperFileBodyCoreBeg
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hwhat : fileWhat I = fileBegBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
        (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨362⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let data := fileData I
  let locals := fileLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := fileBegPostState evm0 I
  have hauthSolm : relyAuthWord σ I = ⟨1⟩ := by
    have hword : relyAuthWord σ I = relyAuthWord σ I :=
      rfl
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, data] using
      (flapperFileBegSourceBody (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := flapperFileX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flapperFileX_authorized (I := I) hauth hdecoded
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileBegBytes :=
    fileWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := flapperFileX_storeBegAuthorized hperm hmatch hswitch
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by
      simp [evm1, evm0, initState, fileBegPostState, storageStore_accountMap, data])
    (by
      simpa [fileTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flapperFileBodyCoreLid
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hbeg : fileWhat I ≠ fileBegBytes)
    (httl : fileWhat I ≠ fileTtlBytes)
    (htau : fileWhat I ≠ fileTauBytes)
    (hwhat : fileWhat I = fileLidBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
        (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨362⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let data := fileData I
  let locals := fileLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := fileLidPostState evm0 I
  have hauthSolm : relyAuthWord σ I = ⟨1⟩ := by
    have hword : relyAuthWord σ I = relyAuthWord σ I :=
      rfl
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, data] using
      (flapperFileLidSourceBody (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hbeg httl htau hwhat)
  obtain ⟨_, _, hdecoded⟩ := flapperFileX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flapperFileX_authorized (I := I) hauth hdecoded
  have hbegWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) hbeg (by native_decide)
  have httlWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTtlBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) httl (by native_decide)
  have htauWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTauBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) htau (by native_decide)
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileLidBytes :=
    fileWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := flapperFileX_storeLidAuthorized hperm hbegWord httlWord htauWord hmatch
    hswitch
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by
      simp [evm1, evm0, initState, fileLidPostState, storageStore_accountMap, data])
    (by
      simpa [fileTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flapperFileBodyCoreTtl
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hbeg : fileWhat I ≠ fileBegBytes)
    (hwhat : fileWhat I = fileTtlBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
        (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨362⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := fileLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := fileTtlPostState evm0 I
  have hauthSolm : relyAuthWord σ I = ⟨1⟩ := by
    have hword : relyAuthWord σ I = relyAuthWord σ I :=
      rfl
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals] using
      (flapperFileTtlSourceBody (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hbeg hwhat)
  obtain ⟨_, _, hdecoded⟩ := flapperFileX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flapperFileX_authorized (I := I) hauth hdecoded
  have hbegWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) hbeg (by native_decide)
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileTtlBytes :=
    fileWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := flapperFileX_storeTtlAuthorized hperm hbegWord hmatch hswitch
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by
      simpa [evm1, evm0, initState, fileTtlPostState, fileTtlStoredWord,
        fileTtlPostAccountMap, fileTtlStoredWordMap, storageStore_accountMap,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord])
    (by
      simpa [fileTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flapperFileBodyCoreTau
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hbeg : fileWhat I ≠ fileBegBytes)
    (httl : fileWhat I ≠ fileTtlBytes)
    (hwhat : fileWhat I = fileTauBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
        (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨362⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := fileLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := fileTauPostState evm0 I
  have hauthSolm : relyAuthWord σ I = ⟨1⟩ := by
    have hword : relyAuthWord σ I = relyAuthWord σ I :=
      rfl
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals] using
      (flapperFileTauSourceBody (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hbeg httl hwhat)
  obtain ⟨_, _, hdecoded⟩ := flapperFileX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flapperFileX_authorized (I := I) hauth hdecoded
  have hbegWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) hbeg (by native_decide)
  have httlWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTtlBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) httl (by native_decide)
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileTauBytes :=
    fileWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := flapperFileX_storeTauAuthorized hperm hbegWord httlWord hmatch hswitch
  exact hret.reEquivExecutionGen hcode hdispatch hdecode hbody
    (by
      simpa [evm1, evm0, initState, fileTauPostState, fileTauStoredWord,
        fileTauPostAccountMap, fileTauStoredWordMap, storageStore_accountMap,
        Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        solcSlotWord])
    (by
      simpa [fileTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem flapperFileBodyCoreUnauthorized
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
        (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨362⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := fileLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ I = relyAuthWord σ I :=
      rfl
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
    simpa [evm0, locals] using
      (flapperFileSourceBodyAuthReverts (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := flapperFileX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  exact (flapperFileX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperFileBodyCoreUnrecognized
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hbeg : fileWhat I ≠ fileBegBytes)
    (httl : fileWhat I ≠ fileTtlBytes)
    (htau : fileWhat I ≠ fileTauBytes)
    (hlid : fileWhat I ≠ fileLidBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileTransition.params.map Param.name)
        (transitionSignature fileTransition).paramTypes I.calldata = some (fileLocals I))
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨362⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  let locals := fileLocals I
  let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ I = ⟨1⟩ := by
    have hword : relyAuthWord σ I = relyAuthWord σ I :=
      rfl
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileTransition.body .reverted := by
    simpa [evm0, locals] using
      (flapperFileSourceBodyUnrecognized (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hbeg httl htau hlid)
  obtain ⟨_, _, hdecoded⟩ := flapperFileX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flapperFileX_authorized (I := I) hauth hdecoded
  have hbegWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileBegBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) hbeg (by native_decide)
  have httlWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTtlBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) httl (by native_decide)
  have htauWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileTauBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) htau (by native_decide)
  have hlidWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileLidBytes :=
    fileWhatWord_ne_of_bytes_ne (by omega) hlid (by native_decide)
  exact (flapperFileX_unrecognized hbegWord httlWord htauWord hlidWord hswitch)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flapperFileBodyCoreDecodeFailed_short
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flapperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some fileTransition)
    (hreach : ∃ k C, RD flapperBytecode I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨362⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  exact (flapperFileX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (flapperDecode_file_none_short hsz4 hshort)

theorem flapperFileBodyCore {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = flapperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flapperSelBytes 5)) :
    runtimeEquivalenceFor config contract σ σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flapperSelBytes 5) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileTransition :=
    flapperDispatchFile hsel
  have hreach := flapperReachFileBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ I = ⟨1⟩
    · by_cases hbeg : fileWhat I = fileBegBytes
      · exact flapperFileBodyCoreBeg hcode hsize hperm hwv hsz68 hauth hbeg
          hdispatch (flapperDecode_file_ok hsz68) hreach
      · by_cases httl : fileWhat I = fileTtlBytes
        · exact flapperFileBodyCoreTtl hcode hsize hperm hwv hsz68 hauth hbeg httl
            hdispatch (flapperDecode_file_ok hsz68) hreach
        · by_cases htau : fileWhat I = fileTauBytes
          · exact flapperFileBodyCoreTau hcode hsize hperm hwv hsz68 hauth hbeg httl htau
              hdispatch (flapperDecode_file_ok hsz68) hreach
          · by_cases hlid : fileWhat I = fileLidBytes
            · exact flapperFileBodyCoreLid hcode hsize hperm hwv hsz68 hauth hbeg httl htau
                hlid hdispatch (flapperDecode_file_ok hsz68) hreach
            · exact flapperFileBodyCoreUnrecognized hcode hsize hwv hsz68 hauth hbeg httl
                htau hlid hdispatch (flapperDecode_file_ok hsz68) hreach
    · exact flapperFileBodyCoreUnauthorized hcode hsize hwv hsz68 hauth hdispatch
        (flapperDecode_file_ok hsz68) hreach
  · exact flapperFileBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach


end Benchmarks.Dss.Flapper
