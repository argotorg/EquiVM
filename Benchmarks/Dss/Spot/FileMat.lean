import Benchmarks.Dss.Spot.FilePar
import Benchmarks.Dss.Spot.Ilks
import Benchmarks.Dss.Jug.FileDuty

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Spot

/-! ## `file(bytes32,bytes32,uint256)` -/

abbrev fileMatIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileMatWhatBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 36).take 32

abbrev fileMatIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev fileMatWhatWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileMatData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev fileMatIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (fileMatIlkBytes I)

abbrev fileMatPipSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (fileMatIlkKey I)

abbrev fileMatSlotFor (I : ExecutionEnv) : UInt256 :=
  fileMatPipSlotFor I + ⟨1⟩

abbrev fileMatEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (fileMatIlkKey I), .field "mat"] }

abbrev fileMatBytes : List UInt8 :=
  [109, 97, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileMatLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (fileMatIlkBytes I))).insert
    "what" (.fixedBytes bytes32Width (fileMatWhatBytes I))).insert
    "data" (.int (Int.ofNat (fileMatData I).toNat))

noncomputable abbrev fileMatIlkHashMem (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (fileMatIlkWord I) ⟨1⟩ (relyAuthHashMem I)

theorem fileMatIlkBytes_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileMatIlkBytes I).length = 32 := by
  simp [fileMatIlkBytes, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileMatWhatBytes_length {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    (fileMatWhatBytes I).length = 32 := by
  simp [fileMatWhatBytes, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileMatWhatWord_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    ABI.bytesToWord (fileMatWhatBytes I) = fileMatWhatWord I := by
  simpa [fileMatWhatBytes, fileMatWhatWord] using
    decode_word_at_eq I.calldata 36 (by omega) (by norm_num)

theorem fileMatWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hbs : fileMatWhatBytes I = bs) :
    fileMatWhatWord I = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileMatWhatWord_eq (I := I) hsz68).symm

theorem fileMatWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hword : fileMatWhatWord I = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileMatWhatBytes I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileMatWhatBytes I)
    (fileMatWhatBytes_length (I := I) hsz68)
  rw [fileMatWhatWord_eq (I := I) hsz68, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileMatWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hneq : fileMatWhatBytes I ≠ bs)
    (hbsLen : bs.length = 32) :
    fileMatWhatWord I ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileMatWhat_eq_of_word_eq hsz68 hword hbsLen)

theorem keyValueToWord_fileMatIlkKey {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    keyValueToWord (fileMatIlkKey I) = fileMatIlkWord I := by
  have hlen32 : (fileMatIlkBytes I).length = 32 := fileMatIlkBytes_length hsz36
  have hword : ABI.bytesToWord (fileMatIlkBytes I) = fileMatIlkWord I := by
    simpa [fileMatIlkBytes, fileMatIlkWord] using
      decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  have hbytes : fileMatIlkBytes I = EVM.Word.toBytesBE (fileMatIlkWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := fileMatIlkBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [fileMatIlkKey, bytes32Width, hbytes] using
    keyValueToWord_fixedBytes32 (fileMatIlkWord I)

theorem fileMatPipSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    fileMatPipSlotFor I = solcMappingSlot ⟨1⟩ (fileMatIlkWord I) := by
  unfold fileMatPipSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_fileMatIlkKey hsz36]

theorem fileMatSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    fileMatSlotFor I = solcMappingSlot ⟨1⟩ (fileMatIlkWord I) + ⟨1⟩ := by
  simp [fileMatSlotFor, fileMatPipSlotFor_eq hsz36]

theorem fileMatIlkHashMem_size (I : ExecutionEnv) :
    (fileMatIlkHashMem I).size = 96 := by
  exact twoWordHashMem_size_96 (fileMatIlkWord I) ⟨1⟩ (relyAuthHashMem_size I)

theorem fileMatIlkHashMem_read64 (I : ExecutionEnv) :
    (fileMatIlkHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  exact twoWordHashMem_read64 (fileMatIlkWord I) ⟨1⟩
    (relyAuthHashMem_size I) (relyAuthHashMem_read64 I)

set_option maxHeartbeats 1000000 in
theorem spotDecode_fileMat_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileMatTransition.params.map Param.name)
      (transitionSignature fileMatTransition).paramTypes I.calldata =
        some (fileMatLocals I) := by
  simpa [config, fileMatTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileMatLocals, fileMatIlkBytes, fileMatWhatBytes, fileMatData, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (Benchmarks.Dss.Jug.decodeCalldata_legacyBytes32_bytes32_uint256_ok
      (cd := I.calldata) (x := "ilk") (y := "what") (z := "data") hsz100)

theorem spotDecode_fileMat_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (fileMatTransition.params.map Param.name)
      (transitionSignature fileMatTransition).paramTypes I.calldata = none := by
  simpa [config, fileMatTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256] using
    (Benchmarks.Dss.Jug.decodeCalldata_legacyBytes32_bytes32_uint256_none_short
      (cd := I.calldata) (x := "ilk") (y := "what") (z := "data") hsz4 hshort)

theorem fileMatLocals_get_ilk (I : ExecutionEnv) :
    (fileMatLocals I).get? "ilk" =
      some (.fixedBytes bytes32Width (fileMatIlkBytes I)) := by
  rw [fileMatLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem fileMatLocals_get_what (I : ExecutionEnv) :
    (fileMatLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileMatWhatBytes I)) := by
  rw [fileMatLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileMatLocals_get_data (I : ExecutionEnv) :
    (fileMatLocals I).get? "data" =
      some (.int (Int.ofNat (fileMatData I).toNat)) := by
  rw [fileMatLocals, store_get_self]

theorem fileMatLocals_get_wards (I : ExecutionEnv) :
    (fileMatLocals I).get? "wards" = none := by
  rw [fileMatLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem fileMatLocals_get_live (I : ExecutionEnv) :
    (fileMatLocals I).get? "live" = none := by
  rw [fileMatLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem fileMatLocals_get_ilks (I : ExecutionEnv) :
    (fileMatLocals I).get? "ilks" = none := by
  rw [fileMatLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileMatData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileMatData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileMatData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileMatData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileMatWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileMatWhatBytes I)))
    (hwhat : fileMatWhatBytes I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileMatWhatBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileMatWhatBytes I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileMatWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileMatWhatBytes I)))
    (hwhat : fileMatWhatBytes I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileMatWhatBytes I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileMatWhatBytes I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

set_option maxHeartbeats 1000000 in
theorem assign_fileMatStorage (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (fileMatSlotFor I)
      (fileMatData I)
    assignStorageRef? config { contract := contract, locals := fileMatLocals I } evm
      .storage (ilksF (.var "ilk") "mat") (.int (Int.ofNat (fileMatData I).toNat)) =
        .ok ({ contract := contract, locals := fileMatLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := fileMatEvaledRef I)
      (loc := wordLoc (fileMatSlotFor I))
      (hbase := fileMatLocals_get_ilks I)
      (her := by
        have hkeyLen : (fileMatIlkBytes I).length = ↑bytes32Width + 1 := by
          simpa [bytes32Width] using fileMatIlkBytes_length (I := I) hsz36
        simp [fileMatEvaledRef, fileMatIlkKey, evalStorageRef, evalStorageRefSteps,
          evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
          ← Std.HashMap.get?_eq_getElem?, fileMatLocals_get_ilk I, EvalResult.ofOption,
          EvalResult.bind, pure, bind, hkeyLen])
      (hty := by
        simp [fileMatIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
          IlkStructTy, uint256St])
      (hloc := by rfl)
  simpa [evm'] using storageLocStore_uint256 evm (fileMatSlotFor I) (fileMatData I)

set_option maxHeartbeats 1000000 in
theorem spotFileMatSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : spotLiveWord σ I = ⟨1⟩)
    (hwhat : fileMatWhatBytes I = fileMatBytes) :
    let locals := fileMatLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (fileMatSlotFor I) (fileMatData I)
    ExecTransitionBody config contract evm0 locals fileMatTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileMatLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_live_true_of_none evm0 locals
      (by simpa [locals] using fileMatLocals_get_live I)
      (by
        simpa [evm0, spotLiveWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hlive)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") matParamLit) = .ok (.bool true) := by
    simpa [matParamLit, fileMatBytes] using
      (evalExpr_fileMatWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileMatBytes) (by simpa [locals] using fileMatLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileMatData I).toNat)) := by
    exact evalExpr_fileMatData (evm := evm0) (I := I) (locals := locals)
      (by simpa [locals] using fileMatLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (ilksF (.var "ilk") "mat") (.int (Int.ofNat (fileMatData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileMatStorage evm0 I hsz36
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage (ilksF (.var "ilk") "mat") (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileMatTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem spotFileMatSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := fileMatLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileMatTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    exact evalExpr_auth_false_of_wards_none evm0 I locals
      (by simpa [locals] using fileMatLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileMatTransition, nonpayable, auth, requireLive] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.require (.binary .eq (.storage liveRef) (.intLit 1)),
        .ite (.binary .eq (.var "what") matParamLit)
          [.assign .storage (ilksF (.var "ilk") "mat") (.var "data")]
          [.require (.boolLit false)]])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem spotFileMatSourceBodyNotLive {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : spotLiveWord σ I ≠ ⟨1⟩) :
    let locals := fileMatLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileMatTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileMatLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
    exact evalExpr_live_false_of_none evm0 locals
      (by simpa [locals] using fileMatLocals_get_live I)
      (by
        simpa [evm0, spotLiveWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hlive)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileMatTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hliveGuard)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem spotFileMatSourceBodyUnrecognized {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : spotLiveWord σ I = ⟨1⟩)
    (hwhat : fileMatWhatBytes I ≠ fileMatBytes) :
    let locals := fileMatLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileMatTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileMatLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_live_true_of_none evm0 locals
      (by simpa [locals] using fileMatLocals_get_live I)
      (by
        simpa [evm0, spotLiveWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hlive)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") matParamLit) = .ok (.bool false) := by
    simpa [matParamLit, fileMatBytes] using
      (evalExpr_fileMatWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileMatBytes) (by simpa [locals] using fileMatLocals_get_what I) hwhat)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileMatTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem spotReachFileMatBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (spotSelBytes 2)) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨216⟩ [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : spotSelWord I = ⟨0x1a0b287e⟩ :=
    spotSelWord_eq_of_beq I hsz 0x1a 0x0b 0x28 0x7e ⟨0x1a0b287e⟩
      (by native_decide) (by simpa [spotSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc j))
        (spotSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc 1))
        (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact spotReachLowBody 1 (by omega) ⟨216⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem RD.spotFileMatDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨238⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = spotBytecode)
    (hroutine : (D_J code 0).contains ⟨993⟩ = true)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨993⟩
      (calldataWord ee.calldata 68 :: calldataWord ee.calldata 36 ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd239 := h.jumpdest (by native_decide) (by evm_ov)
  have rd240 := rd239.pop (by native_decide) (by evm_ov)
  have rd241 := rd240.dup1 (by native_decide) (by evm_ov)
  have rd242 := rd241.calldataload (by native_decide) (by evm_ov)
  have rd243 := rd242.swap1 (by native_decide) (by evm_ov)
  have rd245 := rd243.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd246 := rd245.dup2 (by native_decide) (by evm_ov)
  have rd247 := rd246.add (by native_decide) (by evm_ov)
  have rd248 := rd247.calldataload (by native_decide) (by evm_ov)
  have rd249 := rd248.swap1 (by native_decide) (by evm_ov)
  have rd251 := rd249.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd252 := rd251.add (by native_decide) (by evm_ov)
  have rd253 := rd252.calldataload (by native_decide) (by evm_ov)
  have rd256 := rd253.push2 ⟨993⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨68⟩ : UInt256).toNat = 68 from by decide]
      using rd256.jump (by native_decide) hroutine (by evm_ov)⟩

theorem spotFileMatX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨216⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨993⟩
        [fileMatData I, fileMatWhatWord I, fileMatIlkWord I, ⟨214⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := spotBytecode) (sel := sel) (entry := ⟨216⟩) (ret := ⟨214⟩)
    (decoded := ⟨238⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.spotFileMatDecodeToRoutine
    (code := spotBytecode) (ret := ⟨214⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileMatData, fileMatWhatWord, fileMatIlkWord] using hroutine⟩

theorem spotFileMatX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨993⟩
      [fileMatData I, fileMatWhatWord I, fileMatIlkWord I, ⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD spotBytecode I g s0 ⟨1075⟩
      [fileMatData I, fileMatWhatWord I, fileMatIlkWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd999pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1000 := rd999pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1004pre := evm_run rd1000 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1005 := rd1004pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1008pre := evm_run rd1005 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1009 := rd1008pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1010, C1010, rd1010raw⟩ := rd1009.sload (by native_decide) (by evm_ov)
  have rd1010 : RD spotBytecode I g s0 ⟨1010⟩
      (relyAuthWord σ I :: fileMatData I :: fileMatWhatWord I :: fileMatIlkWord I ::
        ⟨214⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1010 C1010 := by
    simpa [relyAuthWord, spotSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1010raw
  have rd1013pre := evm_run rd1010 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1013pre
  have rd1016 := rd1013pre.pushConst (⟨1075⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1016.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem spotFileMatX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨993⟩
      [fileMatData I, fileMatWhatWord I, fileMatIlkWord I, ⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd999pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1000 := rd999pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1004pre := evm_run rd1000 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1005 := rd1004pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1008pre := evm_run rd1005 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1009 := rd1008pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1010, C1010, rd1010raw⟩ := rd1009.sload (by native_decide) (by evm_ov)
  have rd1010 : RD spotBytecode I g s0 ⟨1010⟩
      (relyAuthWord σ I :: fileMatData I :: fileMatWhatWord I :: fileMatIlkWord I ::
        ⟨214⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1010 C1010 := by
    simpa [relyAuthWord, spotSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1010raw
  have rd1013pre := evm_run rd1010 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1013pre
  have rd1016 := rd1013pre.pushConst (⟨1075⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1017 := rd1016.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.spotCodecopyAuthRevertTail ⟨2134⟩ ⟨22⟩ rd1017
    (by
      unfold spotCodecopyAuthRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem spotFileMatX_liveOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : spotLiveWord σ I = ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1075⟩
      [fileMatData I, fileMatWhatWord I, fileMatIlkWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD spotBytecode I g s0 ⟨1149⟩
      [fileMatData I, fileMatWhatWord I, fileMatIlkWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1078 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1079raw⟩ := rd1078.sload (by native_decide) (by evm_ov)
  have hliveRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨4⟩ ⟨0⟩)) = ⟨1⟩ := by
    simpa [spotLiveWord, spotSlotWord, solcSlotWord] using hlive
  rw [hliveRaw] at rd1079raw
  have rd1082pre := evm_run rd1079raw with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [uInt256_eq_self] at rd1082pre
  have rd1085 := rd1082pre.pushConst (⟨1149⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1085.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem spotFileMatX_notLive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : spotLiveWord σ I ≠ ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1075⟩
      [fileMatData I, fileMatWhatWord I, fileMatIlkWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g s0 := by
  have rd1078 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1079raw⟩ := rd1078.sload (by native_decide) (by evm_ov)
  have rd1082pre := evm_run rd1079raw with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have hliveRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨4⟩ ⟨0⟩)) ≠ ⟨1⟩ := by
    simpa [spotLiveWord, spotSlotWord, solcSlotWord] using hlive
  have heq0 :
      UInt256.eq ⟨1⟩
        (σ.find? I.codeOwner |>.option ⟨0⟩
          (fun acc => acc.storage.findD ⟨4⟩ ⟨0⟩)) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h1 => hliveRaw h1.symm)
  rw [heq0] at rd1082pre
  have rd1085 := rd1082pre.pushConst (⟨1149⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1086 := rd1085.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1086⟩)
    (len := ⟨16⟩)
    (rawWord := spotNotLiveRawWord)
    (shift := ⟨128⟩)
    (word := UInt256.shiftLeft spotNotLiveRawWord ⟨128⟩)
    (op := .PUSH16)
    (width := 16)
    rd1086
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    rfl
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem spotFileMatX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hsz36 : 36 ≤ I.calldata.size) (hperm : I.perm = true)
    (hmatch : fileMatWhatWord I = ABI.bytesToWord fileMatBytes)
    (h : RD spotBytecode I g s0 ⟨1149⟩
      [fileMatData I, fileMatWhatWord I, fileMatIlkWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret spotBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (fileMatSlotFor I) (fileMatData I))
      ByteArray.empty := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((fileMatIlkHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (fileMatIlkWord I) := by
    simpa [fileMatIlkHashMem] using
      twoWordHashMem_solcMappingSlot (⟨1⟩ : UInt256) (fileMatIlkWord I)
        (relyAuthHashMem_size I)
  have rd1150 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1151 := rd1150.dup2 (by native_decide) (by evm_ov)
  have rd1155 := rd1151.pushConst (⟨1792093⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1157 := rd1155.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd1158 := rd1157.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨1792093⟩ : UInt256) ⟨234⟩ =
      ABI.bytesToWord fileMatBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd1158
  have rd1159 := rd1158.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd1159
  have rd1160 := rd1159.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1160
  have rd1163 := rd1160.pushConst (⟨1189⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1164 := rd1163.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1166 := rd1164.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd1167 := rd1166.dup4 (by native_decide) (by evm_ov)
  have rd1168pre := rd1167.dup2 (by native_decide) (by evm_ov)
  have rd1169 := rd1168pre.mstore 0 (wordAt0Mem (fileMatIlkWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1175pre := evm_run rd1169 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1176 := rd1175pre.mstore 0 (fileMatIlkHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1179pre := evm_run rd1176 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd1180 := rd1179pre.keccak256 0 (solcMappingSlot ⟨1⟩ (fileMatIlkWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd1181 := rd1180.add (by native_decide) (by evm_ov)
  have rd1182 := rd1181.dup2 (by native_decide) (by evm_ov)
  have rd1183 := rd1182.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1184⟩ := rd1183.sstore hperm (by native_decide) (by evm_ov)
  have rd1188 := rd1184.push2 ⟨1266⟩ (by native_decide) (by evm_ov)
  have rd1266 := rd1188.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1267 := rd1266.jumpdest (by native_decide) (by evm_ov)
  have rd1268 := rd1267.pop (by native_decide) (by evm_ov)
  have rd1269 := rd1268.pop (by native_decide) (by evm_ov)
  have rd1270 := rd1269.pop (by native_decide) (by evm_ov)
  have rd214 := rd1270.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd215 := rd214.jumpdest (by native_decide) (by evm_ov)
  simpa [fileMatSlotFor_eq hsz36] using RD.stop rd215 (by native_decide) (by evm_ov)

theorem spotFileMatX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hneq : fileMatWhatWord I ≠ ABI.bytesToWord fileMatBytes)
    (h : RD spotBytecode I g s0 ⟨1149⟩
      [fileMatData I, fileMatWhatWord I, fileMatIlkWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g s0 := by
  have rd1150 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1151 := rd1150.dup2 (by native_decide) (by evm_ov)
  have rd1155 := rd1151.pushConst (⟨1792093⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1157 := rd1155.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd1158 := rd1157.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨1792093⟩ : UInt256) ⟨234⟩ =
      ABI.bytesToWord fileMatBytes := by
    native_decide
  rw [hconst] at rd1158
  have rd1159 := rd1158.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileMatBytes) (fileMatWhatWord I) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd1159
  have rd1160 := rd1159.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1160
  have rd1163 := rd1160.pushConst (⟨1189⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1189 := rd1163.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact RD.spotFileUnrecognizedRevert rd1189
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem spotFileMatX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨216⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := spotBytecode) (sel := sel) (entry := ⟨216⟩) (ret := ⟨214⟩)
    (decoded := ⟨238⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem spotFileMatBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : spotLiveWord σ_evm I = ⟨1⟩)
    (hwhat : fileMatWhatBytes I = fileMatBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileMatTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileMatTransition.params.map Param.name)
        (transitionSignature fileMatTransition).paramTypes I.calldata = some (fileMatLocals I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨216⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let data := fileMatData I
  let matSlot := fileMatSlotFor I
  let locals := fileMatLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner matSlot data
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hliveSolm : spotLiveWord σ_solm I = ⟨1⟩ := by
    have hword : spotLiveWord σ_evm I = spotLiveWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
    rw [← hword]
    exact hlive
  have hbody :
      ExecTransitionBody config contract evm0 locals fileMatTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, matSlot, data] using
      (spotFileMatSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv (by omega) hauthSolm
        hliveSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := spotFileMatX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  obtain ⟨_, _, hauthz⟩ := spotFileMatX_authorized (I := I) hauth hdecoded
  obtain ⟨_, _, hlivez⟩ := spotFileMatX_liveOk (I := I) hlive hauthz
  have hmatch : fileMatWhatWord I = ABI.bytesToWord fileMatBytes :=
    fileMatWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := spotFileMatX_storeAuthorized (I := I) (by omega) hperm hmatch hlivez
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    (by
      simpa [evm1, evm0, initState, storageStore_accountMap, matSlot, data] using
        accountMapEquiv_sstoreAccountMap I.codeOwner matSlot data hAccounts)
    (by
      simpa [fileMatTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem spotFileMatBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileMatTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileMatTransition.params.map Param.name)
        (transitionSignature fileMatTransition).paramTypes I.calldata = some (fileMatLocals I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨216⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileMatLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileMatTransition.body .reverted := by
    simpa [evm0, locals] using
      (spotFileMatSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := spotFileMatX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  exact (spotFileMatX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem spotFileMatBodyCoreNotLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : spotLiveWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileMatTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileMatTransition.params.map Param.name)
        (transitionSignature fileMatTransition).paramTypes I.calldata = some (fileMatLocals I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨216⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileMatLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hliveSolm : spotLiveWord σ_solm I ≠ ⟨1⟩ := by
    have hword : spotLiveWord σ_evm I = spotLiveWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
    intro hbad
    exact hlive (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileMatTransition.body .reverted := by
    simpa [evm0, locals] using
      (spotFileMatSourceBodyNotLive (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm)
  obtain ⟨_, _, hdecoded⟩ := spotFileMatX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  obtain ⟨_, _, hauthz⟩ := spotFileMatX_authorized (I := I) hauth hdecoded
  exact (spotFileMatX_notLive (I := I) hlive hauthz)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem spotFileMatBodyCoreUnrecognized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : spotLiveWord σ_evm I = ⟨1⟩)
    (hwhat : fileMatWhatBytes I ≠ fileMatBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileMatTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileMatTransition.params.map Param.name)
        (transitionSignature fileMatTransition).paramTypes I.calldata = some (fileMatLocals I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨216⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileMatLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hliveSolm : spotLiveWord σ_solm I = ⟨1⟩ := by
    have hword : spotLiveWord σ_evm I = spotLiveWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
    rw [← hword]
    exact hlive
  have hbody :
      ExecTransitionBody config contract evm0 locals fileMatTransition.body .reverted := by
    simpa [evm0, locals] using
      (spotFileMatSourceBodyUnrecognized (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := spotFileMatX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  obtain ⟨_, _, hauthz⟩ := spotFileMatX_authorized (I := I) hauth hdecoded
  obtain ⟨_, _, hlivez⟩ := spotFileMatX_liveOk (I := I) hlive hauthz
  have hneq : fileMatWhatWord I ≠ ABI.bytesToWord fileMatBytes :=
    fileMatWhatWord_ne_of_bytes_ne (by omega) hwhat (by native_decide)
  exact (spotFileMatX_unrecognized hneq hlivez)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem spotFileMatBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some fileMatTransition)
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨216⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (spotFileMatX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (spotDecode_fileMat_none_short hsz4 hshort)

theorem spotFileMatBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = spotBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (spotSelBytes 2))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (spotSelBytes 2) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileMatTransition :=
    spotDispatchFileMat hsel
  have hreach := spotReachFileMatBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · by_cases hlive : spotLiveWord σ_evm I = ⟨1⟩
      · by_cases hwhat : fileMatWhatBytes I = fileMatBytes
        · exact spotFileMatBodyCoreOk hcode hsize _hperm hwv hsz100 hauth hlive hwhat
            hdispatch (spotDecode_fileMat_ok hsz100) hreach hAccounts
        · exact spotFileMatBodyCoreUnrecognized hcode hsize hwv hsz100 hauth hlive hwhat
            hdispatch (spotDecode_fileMat_ok hsz100) hreach hAccounts
      · exact spotFileMatBodyCoreNotLive hcode hsize hwv hsz100 hauth hlive
          hdispatch (spotDecode_fileMat_ok hsz100) hreach hAccounts
    · exact spotFileMatBodyCoreUnauthorized hcode hsize hwv hsz100 hauth hdispatch
        (spotDecode_fileMat_ok hsz100) hreach hAccounts
  · exact spotFileMatBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Spot
