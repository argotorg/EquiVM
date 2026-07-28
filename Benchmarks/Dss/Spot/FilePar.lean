import Benchmarks.Dss.Spot.Rely
import Benchmarks.Dss.Jug.FileBase

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Spot

/-! ## Shared `file(...)` helpers -/

theorem evalStorageRef_live_of_none (evm : EVM.State) (locals : Store)
    (hlive : locals.get? "live" = none) :
    evalStorageRef config { contract := contract, locals := locals } evm liveRef =
      .ok ({ base := "live", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind, hlive]

theorem evalExpr_live_true_of_none (evm : EVM.State) (locals : Store)
    (hlive : locals.get? "live" = none)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage liveRef) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (slot := liveRef)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨4⟩)
      (value := .int 1)
      (hbase := by simpa [liveRef] using hlive)
      (her := evalStorageRef_live_of_none evm locals hlive)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using spotStorageLocLoad_uint256 evm ⟨4⟩)]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_live_false_of_none (evm : EVM.State) (locals : Store)
    (hlive : locals.get? "live" = none)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (slot := liveRef)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨4⟩)
      (hbase := by simpa [liveRef] using hlive)
      (her := evalStorageRef_live_of_none evm locals hlive)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact spotStorageLocLoad_uint256 evm ⟨4⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩).toNat) ≠
        Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact hload (uint256_toNat_eq_one (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩).toNat) ==
        Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

abbrev spotNotLiveRawWord : UInt256 :=
  ⟨0x53706f747465722f6e6f742d6c697665⟩

abbrev spotFileUnrecognizedRawWord : UInt256 :=
  ⟨0x53706f747465722f66696c652d756e7265636f676e697a65642d706172616d00⟩

theorem RD.spotFileUnrecognizedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD spotBytecode ee g s0 ⟨1189⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev spotBytecode g s0 := by
  have rdMload := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
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
  have rdRaw := rdPrefix.pushConst spotFileUnrecognizedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨31⟩ spotFileUnrecognizedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨31⟩ spotFileUnrecognizedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

/-! ## `file(bytes32,uint256)` -/

abbrev fileParWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileParData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileParBytes : List UInt8 :=
  [112, 97, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileParLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileParWhat I))).insert
    "data" (.int (Int.ofNat (fileParData I).toNat))

theorem spotDecode_filePar_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileParTransition.params.map Param.name)
      (transitionSignature fileParTransition).paramTypes I.calldata =
        some (fileParLocals I) := by
  simpa [config, fileParTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileParLocals, fileParWhat, fileParData, abiBytes32, abiBytes32Width, abiUInt256] using
    (Benchmarks.Dss.Jug.decodeCalldata_legacyBytes32_uint256_ok (cd := I.calldata)
      (x := "what") (y := "data") hsz68)

theorem spotDecode_filePar_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileParTransition.params.map Param.name)
      (transitionSignature fileParTransition).paramTypes I.calldata = none := by
  simpa [config, fileParTransition, bytes32, bytes32Width, uint256, uint256Int, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (Benchmarks.Dss.Jug.decodeCalldata_legacyBytes32_uint256_none_short
      (cd := I.calldata) (x := "what") (y := "data") hsz4 hshort)

theorem fileParWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileParWhat I).length = 32 := by
  simp [fileParWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileParWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (fileParWhat I) = calldataWord I.calldata 4 := by
  simpa [fileParWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem fileParWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hbs : fileParWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileParWhatWord_eq (I := I) hsz36).symm

theorem fileParWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileParWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileParWhat I)
    (fileParWhat_length (I := I) hsz36)
  rw [fileParWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileParWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : fileParWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileParWhat_eq_of_word_eq hsz36 hword hbsLen)

theorem fileParLocals_get_what (I : ExecutionEnv) :
    (fileParLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileParWhat I)) := by
  rw [fileParLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileParLocals_get_data (I : ExecutionEnv) :
    (fileParLocals I).get? "data" =
      some (.int (Int.ofNat (fileParData I).toNat)) := by
  rw [fileParLocals, store_get_self]

theorem fileParLocals_get_wards (I : ExecutionEnv) :
    (fileParLocals I).get? "wards" = none := by
  rw [fileParLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileParLocals_get_live (I : ExecutionEnv) :
    (fileParLocals I).get? "live" = none := by
  rw [fileParLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileParLocals_get_par (I : ExecutionEnv) :
    (fileParLocals I).get? "par" = none := by
  rw [fileParLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileParData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileParData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileParData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileParData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileParWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileParWhat I)))
    (hwhat : fileParWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileParWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileParWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileParWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileParWhat I)))
    (hwhat : fileParWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileParWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileParWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem assign_fileParStorage (evm : EVM.State) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ (fileParData I)
    assignStorageRef? config { contract := contract, locals := fileParLocals I } evm
      .storage parRef (.int (Int.ofNat (fileParData I).toNat)) =
        .ok ({ contract := contract, locals := fileParLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "par", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨3⟩)
      (hbase := fileParLocals_get_par I)
      (her := by simp [parRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [evm'] using storageLocStore_uint256 evm ⟨3⟩ (fileParData I)

theorem spotFileParSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : spotLiveWord σ I = ⟨1⟩)
    (hwhat : fileParWhat I = fileParBytes) :
    let locals := fileParLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨3⟩ (fileParData I)
    ExecTransitionBody config contract evm0 locals fileParTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileParLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_live_true_of_none evm0 locals
      (by simpa [locals] using fileParLocals_get_live I)
      (by
        simpa [evm0, spotLiveWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hlive)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") parParamLit) = .ok (.bool true) := by
    simpa [parParamLit, fileParBytes] using
      (evalExpr_fileParWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileParBytes) (by simpa [locals] using fileParLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileParData I).toNat)) := by
    exact evalExpr_fileParData (evm := evm0) (I := I) (locals := locals)
      (by simpa [locals] using fileParLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage parRef (.int (Int.ofNat (fileParData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileParStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage parRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileParTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem spotFileParSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := fileParLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileParTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    exact evalExpr_auth_false_of_wards_none evm0 I locals
      (by simpa [locals] using fileParLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileParTransition, nonpayable, auth, requireLive] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.require (.binary .eq (.storage liveRef) (.intLit 1)),
        .ite (.binary .eq (.var "what") parParamLit)
          [.assign .storage parRef (.var "data")] [.require (.boolLit false)]])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem spotFileParSourceBodyNotLive {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : spotLiveWord σ I ≠ ⟨1⟩) :
    let locals := fileParLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileParTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileParLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
    exact evalExpr_live_false_of_none evm0 locals
      (by simpa [locals] using fileParLocals_get_live I)
      (by
        simpa [evm0, spotLiveWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hlive)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileParTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hliveGuard)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem spotFileParSourceBodyUnrecognized {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : spotLiveWord σ I = ⟨1⟩)
    (hwhat : fileParWhat I ≠ fileParBytes) :
    let locals := fileParLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileParTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using fileParLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_live_true_of_none evm0 locals
      (by simpa [locals] using fileParLocals_get_live I)
      (by
        simpa [evm0, spotLiveWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hlive)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") parParamLit) = .ok (.bool false) := by
    simpa [parParamLit, fileParBytes] using
      (evalExpr_fileParWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileParBytes) (by simpa [locals] using fileParLocals_get_what I) hwhat)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileParTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem spotReachFileParBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (spotSelBytes 3)) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨257⟩ [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : spotSelWord I = ⟨0x29ae8114⟩ :=
    spotSelWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨0x29ae8114⟩
      (by native_decide) (by simpa [spotSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc j))
        (spotSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotLowFirstArmPc 2))
        (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact spotReachLowBody 2 (by omega) ⟨257⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem RD.spotFileParDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨279⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = spotBytecode)
    (hroutine : (D_J code 0).contains ⟨1271⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1271⟩
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd280 := h.jumpdest (by native_decide) (by evm_ov)
  have rd281 := rd280.pop (by native_decide) (by evm_ov)
  have rd282 := rd281.dup1 (by native_decide) (by evm_ov)
  have rd283 := rd282.calldataload (by native_decide) (by evm_ov)
  have rd284 := rd283.swap1 (by native_decide) (by evm_ov)
  have rd286 := rd284.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd287 := rd286.add (by native_decide) (by evm_ov)
  have rd288 := rd287.calldataload (by native_decide) (by evm_ov)
  have rd291 := rd288.push2 ⟨1271⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd291.jump (by native_decide) hroutine (by evm_ov)⟩

theorem spotFileParX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨257⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1271⟩
        [fileParData I, calldataWord I.calldata 4, ⟨214⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := spotBytecode) (sel := sel) (entry := ⟨257⟩) (ret := ⟨214⟩)
    (decoded := ⟨279⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.spotFileParDecodeToRoutine
    (code := spotBytecode) (ret := ⟨214⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileParData] using hroutine⟩

theorem spotFileParX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1271⟩
      [fileParData I, calldataWord I.calldata 4, ⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD spotBytecode I g s0 ⟨1353⟩
      [fileParData I, calldataWord I.calldata 4, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1277pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1278 := rd1277pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1282pre := evm_run rd1278 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1283 := rd1282pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1286pre := evm_run rd1283 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1287 := rd1286pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1288, C1288, rd1288raw⟩ := rd1287.sload (by native_decide) (by evm_ov)
  have rd1288 : RD spotBytecode I g s0 ⟨1288⟩
      (relyAuthWord σ I :: fileParData I :: calldataWord I.calldata 4 :: ⟨214⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1288 C1288 := by
    simpa [relyAuthWord, spotSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1288raw
  have rd1291pre := evm_run rd1288 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1291pre
  have rd1294 := rd1291pre.pushConst (⟨1353⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1294.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem spotFileParX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1271⟩
      [fileParData I, calldataWord I.calldata 4, ⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1277pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1278 := rd1277pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1282pre := evm_run rd1278 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1283 := rd1282pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1286pre := evm_run rd1283 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1287 := rd1286pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1288, C1288, rd1288raw⟩ := rd1287.sload (by native_decide) (by evm_ov)
  have rd1288 : RD spotBytecode I g s0 ⟨1288⟩
      (relyAuthWord σ I :: fileParData I :: calldataWord I.calldata 4 :: ⟨214⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1288 C1288 := by
    simpa [relyAuthWord, spotSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1288raw
  have rd1291pre := evm_run rd1288 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1291pre
  have rd1294 := rd1291pre.pushConst (⟨1353⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1295 := rd1294.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.spotCodecopyAuthRevertTail ⟨2134⟩ ⟨22⟩ rd1295
    (by
      unfold spotCodecopyAuthRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem spotFileParX_liveOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : spotLiveWord σ I = ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1353⟩
      [fileParData I, calldataWord I.calldata 4, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD spotBytecode I g s0 ⟨1427⟩
      [fileParData I, calldataWord I.calldata 4, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1356 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1357raw⟩ := rd1356.sload (by native_decide) (by evm_ov)
  have hliveRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨4⟩ ⟨0⟩)) = ⟨1⟩ := by
    simpa [spotLiveWord, spotSlotWord, solcSlotWord] using hlive
  rw [hliveRaw] at rd1357raw
  have rd1360pre := evm_run rd1357raw with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [uInt256_eq_self] at rd1360pre
  have rd1363 := rd1360pre.pushConst (⟨1427⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1363.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem spotFileParX_notLive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : spotLiveWord σ I ≠ ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1353⟩
      [fileParData I, calldataWord I.calldata 4, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g s0 := by
  have rd1356 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1357raw⟩ := rd1356.sload (by native_decide) (by evm_ov)
  have rd1360pre := evm_run rd1357raw with [
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
  rw [heq0] at rd1360pre
  have rd1363 := rd1360pre.pushConst (⟨1427⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1364 := rd1363.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1364⟩)
    (len := ⟨16⟩)
    (rawWord := spotNotLiveRawWord)
    (shift := ⟨128⟩)
    (word := UInt256.shiftLeft spotNotLiveRawWord ⟨128⟩)
    (op := .PUSH16)
    (width := 16)
    rd1364
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    rfl
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem spotFileParX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileParBytes)
    (h : RD spotBytecode I g s0 ⟨1427⟩
      [fileParData I, calldataWord I.calldata 4, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret spotBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩ (fileParData I))
      ByteArray.empty := by
  have rd1428 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1429 := rd1428.dup2 (by native_decide) (by evm_ov)
  have rd1433 := rd1429.pushConst (⟨3682489⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1435 := rd1433.push1 ⟨233⟩ (by native_decide) (by evm_ov)
  have rd1436 := rd1435.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨3682489⟩ : UInt256) ⟨233⟩ =
      ABI.bytesToWord fileParBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd1436
  have rd1437 := rd1436.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd1437
  have rd1438 := rd1437.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1438
  have rd1441 := rd1438.pushConst (⟨1189⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1442 := rd1441.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1444 := rd1442.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1445raw⟩ := rd1444.sstore hperm (by native_decide) (by evm_ov)
  have rd1446 := rd1445raw.pop (by native_decide) (by evm_ov)
  have rd214 := rd1446.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd215 := rd214.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop rd215 (by native_decide) (by evm_ov)

theorem spotFileParX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileParBytes)
    (h : RD spotBytecode I g s0 ⟨1427⟩
      [fileParData I, calldataWord I.calldata 4, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g s0 := by
  have rd1428 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1429 := rd1428.dup2 (by native_decide) (by evm_ov)
  have rd1433 := rd1429.pushConst (⟨3682489⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1435 := rd1433.push1 ⟨233⟩ (by native_decide) (by evm_ov)
  have rd1436 := rd1435.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨3682489⟩ : UInt256) ⟨233⟩ =
      ABI.bytesToWord fileParBytes := by
    native_decide
  rw [hconst] at rd1436
  have rd1437 := rd1436.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileParBytes) (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd1437
  have rd1438 := rd1437.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1438
  have rd1441 := rd1438.pushConst (⟨1189⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1189 := rd1441.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact RD.spotFileUnrecognizedRevert rd1189
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem spotFileParX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨257⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := spotBytecode) (sel := sel) (entry := ⟨257⟩) (ret := ⟨214⟩)
    (decoded := ⟨279⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem spotFileParBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : spotLiveWord σ_evm I = ⟨1⟩)
    (hwhat : fileParWhat I = fileParBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileParTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileParTransition.params.map Param.name)
        (transitionSignature fileParTransition).paramTypes I.calldata = some (fileParLocals I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨257⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let data := fileParData I
  let locals := fileParLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨3⟩ data
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
      ExecTransitionBody config contract evm0 locals fileParTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, data] using
      (spotFileParSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := spotFileParX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hauthz⟩ := spotFileParX_authorized (I := I) hauth hdecoded
  obtain ⟨_, _, hlivez⟩ := spotFileParX_liveOk (I := I) hlive hauthz
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileParBytes :=
    fileParWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := spotFileParX_storeAuthorized hperm hmatch hlivez
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    (by
      simpa [evm1, evm0, initState, storageStore_accountMap, data] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩ data hAccounts)
    (by
      simpa [fileParTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem spotFileParBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileParTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileParTransition.params.map Param.name)
        (transitionSignature fileParTransition).paramTypes I.calldata = some (fileParLocals I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨257⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileParLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileParTransition.body .reverted := by
    simpa [evm0, locals] using
      (spotFileParSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := spotFileParX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  exact (spotFileParX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem spotFileParBodyCoreNotLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : spotLiveWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileParTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileParTransition.params.map Param.name)
        (transitionSignature fileParTransition).paramTypes I.calldata = some (fileParLocals I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨257⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileParLocals I
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
      ExecTransitionBody config contract evm0 locals fileParTransition.body .reverted := by
    simpa [evm0, locals] using
      (spotFileParSourceBodyNotLive (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm)
  obtain ⟨_, _, hdecoded⟩ := spotFileParX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hauthz⟩ := spotFileParX_authorized (I := I) hauth hdecoded
  exact (spotFileParX_notLive (I := I) hlive hauthz)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem spotFileParBodyCoreUnrecognized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : spotLiveWord σ_evm I = ⟨1⟩)
    (hwhat : fileParWhat I ≠ fileParBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileParTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileParTransition.params.map Param.name)
        (transitionSignature fileParTransition).paramTypes I.calldata = some (fileParLocals I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨257⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileParLocals I
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
      ExecTransitionBody config contract evm0 locals fileParTransition.body .reverted := by
    simpa [evm0, locals] using
      (spotFileParSourceBodyUnrecognized (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := spotFileParX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hauthz⟩ := spotFileParX_authorized (I := I) hauth hdecoded
  obtain ⟨_, _, hlivez⟩ := spotFileParX_liveOk (I := I) hlive hauthz
  have hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileParBytes :=
    fileParWhatWord_ne_of_bytes_ne (by omega) hwhat (by native_decide)
  exact (spotFileParX_unrecognized hneq hlivez)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem spotFileParBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some fileParTransition)
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨257⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (spotFileParX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (spotDecode_filePar_none_short hsz4 hshort)

theorem spotFileParBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = spotBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (spotSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (spotSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileParTransition :=
    spotDispatchFilePar hsel
  have hreach := spotReachFileParBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · by_cases hlive : spotLiveWord σ_evm I = ⟨1⟩
      · by_cases hwhat : fileParWhat I = fileParBytes
        · exact spotFileParBodyCoreOk hcode hsize _hperm hwv hsz68 hauth hlive hwhat
            hdispatch (spotDecode_filePar_ok hsz68) hreach hAccounts
        · exact spotFileParBodyCoreUnrecognized hcode hsize hwv hsz68 hauth hlive hwhat
            hdispatch (spotDecode_filePar_ok hsz68) hreach hAccounts
      · exact spotFileParBodyCoreNotLive hcode hsize hwv hsz68 hauth hlive
          hdispatch (spotDecode_filePar_ok hsz68) hreach hAccounts
    · exact spotFileParBodyCoreUnauthorized hcode hsize hwv hsz68 hauth hdispatch
        (spotDecode_filePar_ok hsz68) hreach hAccounts
  · exact spotFileParBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Spot
