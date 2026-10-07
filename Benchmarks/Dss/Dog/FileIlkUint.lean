import Benchmarks.Dss.Dog.Dispatch
import Reasoning.MemCascade
import Reasoning.ABIComposite

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Dog

/-! ## `file(bytes32,bytes32,uint256)` -/

abbrev fileIlkUintIlkBytes (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileIlkUintWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 36).take 32

abbrev fileIlkUintIlkWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev fileIlkUintWhatWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileIlkUintData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 68

abbrev fileIlkUintIlkValue (I : ExecutionEnv) : Value :=
  .fixedBytes bytes32Width (fileIlkUintIlkBytes I)

abbrev fileIlkUintIlkKey (I : ExecutionEnv) : KeyValue :=
  .fixedBytes bytes32Width (fileIlkUintIlkBytes I)

abbrev fileIlkUintLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "ilk" (fileIlkUintIlkValue I)).insert "what"
    (.fixedBytes bytes32Width (fileIlkUintWhat I))).insert "data"
    (.int (Int.ofNat (fileIlkUintData I).toNat))

abbrev fileIlkUintChopBytes : List UInt8 :=
  [99, 104, 111, 112] ++ zeroPad28

abbrev fileIlkUintHoleBytes : List UInt8 :=
  [104, 111, 108, 101] ++ zeroPad28

abbrev fileIlkUintChopEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (fileIlkUintIlkKey I), .field "chop"] }

abbrev fileIlkUintHoleEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (fileIlkUintIlkKey I), .field "hole"] }

abbrev fileIlkUintChopSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (fileIlkUintIlkKey I) + ⟨1⟩

abbrev fileIlkUintHoleSlotFor (I : ExecutionEnv) : UInt256 :=
  ilksBase (fileIlkUintIlkKey I) + ⟨2⟩

abbrev dogFileIlkUintLogTopic : UInt256 :=
  ⟨60204663538082082015795290635914298705294497855896068000583932457933612039377⟩

abbrev dogFileChopLtWadRawWord : UInt256 :=
  ⟨97673935956977212165653204999239571013255942225⟩

theorem fileIlkUintChopBytes_length : fileIlkUintChopBytes.length = 32 := by
  native_decide

theorem fileIlkUintHoleBytes_length : fileIlkUintHoleBytes.length = 32 := by
  native_decide

theorem fileIlkUintIlkBytes_len {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    (fileIlkUintIlkBytes I).length = bytes32Width.val + 1 := by
  unfold fileIlkUintIlkBytes
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  simp [bytes32Width]
  omega

theorem fileIlkUintIlkBytes_len32 {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    (fileIlkUintIlkBytes I).length = 32 := by
  have hlen := fileIlkUintIlkBytes_len (I := I) hsz100
  simpa [bytes32Width] using hlen

theorem fileIlkUintWhat_length {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    (fileIlkUintWhat I).length = 32 := by
  simp [fileIlkUintWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem keyValueToWord_fileIlkUintIlkKey {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    keyValueToWord (fileIlkUintIlkKey I) = fileIlkUintIlkWord I := by
  have hlen32 : (fileIlkUintIlkBytes I).length = 32 :=
    fileIlkUintIlkBytes_len32 (I := I) hsz100
  have hword : ABI.bytesToWord (fileIlkUintIlkBytes I) = fileIlkUintIlkWord I := by
    simpa [fileIlkUintIlkBytes, fileIlkUintIlkWord] using
      (decode_word_at_eq_any I.calldata 4 (by omega))
  have hbytes : fileIlkUintIlkBytes I = EVM.Word.toBytesBE (fileIlkUintIlkWord I) := by
    have hto := toBytesBE_bytesToWord_of_length (bs := fileIlkUintIlkBytes I) hlen32
    rw [hword] at hto
    exact hto.symm
  simpa [fileIlkUintIlkKey, bytes32Width, hbytes] using
    keyValueToWord_fixedBytes32 (fileIlkUintIlkWord I)

theorem fileIlkUintChopSlotFor_eq {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    fileIlkUintChopSlotFor I = solcMappingSlot ⟨1⟩ (fileIlkUintIlkWord I) + ⟨1⟩ := by
  unfold fileIlkUintChopSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_fileIlkUintIlkKey hsz100]

theorem fileIlkUintHoleSlotFor_eq {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    fileIlkUintHoleSlotFor I = solcMappingSlot ⟨1⟩ (fileIlkUintIlkWord I) + ⟨2⟩ := by
  unfold fileIlkUintHoleSlotFor ilksBase mapSlot solcMappingSlot
  rw [keyValueToWord_fileIlkUintIlkKey hsz100]

theorem fileIlkUintWhatWord_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    ABI.bytesToWord (fileIlkUintWhat I) = fileIlkUintWhatWord I := by
  simpa [fileIlkUintWhat, fileIlkUintWhatWord] using
    decode_word_at_eq I.calldata 36 (by omega) (by norm_num)

theorem fileIlkUintWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hbs : fileIlkUintWhat I = bs) :
    fileIlkUintWhatWord I = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileIlkUintWhatWord_eq (I := I) hsz68).symm

theorem fileIlkUintWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hword : fileIlkUintWhatWord I = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileIlkUintWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileIlkUintWhat I)
    (fileIlkUintWhat_length (I := I) hsz68)
  rw [fileIlkUintWhatWord_eq (I := I) hsz68, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileIlkUintWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hneq : fileIlkUintWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    fileIlkUintWhatWord I ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileIlkUintWhat_eq_of_word_eq hsz68 hword hbsLen)


theorem dogDecode_fileIlkUint_ok {I : ExecutionEnv}
    (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode
      (fileIlkUintTransition.params.map Param.name)
      (transitionSignature fileIlkUintTransition).paramTypes I.calldata =
        some (fileIlkUintLocals I) := by
  simpa [config, fileIlkUintTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256, fileIlkUintLocals, fileIlkUintIlkValue,
    fileIlkUintIlkBytes, fileIlkUintWhat, fileIlkUintData] using
    decodeCalldata_legacyBytes32_bytes32_uint256_ok (cd := I.calldata)
      (x := "ilk") (y := "what") (z := "data") hsz100

theorem dogDecode_fileIlkUint_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode
      (fileIlkUintTransition.params.map Param.name)
      (transitionSignature fileIlkUintTransition).paramTypes I.calldata = none := by
  simpa [config, fileIlkUintTransition, bytes32, bytes32Width, uint256, uint256Int,
    abiBytes32, abiBytes32Width, abiUInt256] using
    decodeCalldata_legacyBytes32_bytes32_uint256_none_short
      (cd := I.calldata) (x := "ilk") (y := "what") (z := "data") hsz4 hshort

theorem fileIlkUintLocals_get_ilk (I : ExecutionEnv) :
    (fileIlkUintLocals I).get? "ilk" = some (fileIlkUintIlkValue I) := by
  rw [fileIlkUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem fileIlkUintLocals_get_what (I : ExecutionEnv) :
    (fileIlkUintLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileIlkUintWhat I)) := by
  rw [fileIlkUintLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileIlkUintLocals_get_data (I : ExecutionEnv) :
    (fileIlkUintLocals I).get? "data" =
      some (.int (Int.ofNat (fileIlkUintData I).toNat)) := by
  rw [fileIlkUintLocals, store_get_self]

theorem fileIlkUintLocals_get_ilks (I : ExecutionEnv) :
    (fileIlkUintLocals I).get? "ilks" = none := by
  rw [fileIlkUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileIlkUintData {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileIlkUintData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "data") =
      .ok (.int (Int.ofNat (fileIlkUintData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileIlkUintData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileIlkUintWhatEq_true {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileIlkUintWhat I)))
    (hwhat : fileIlkUintWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileIlkUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileIlkUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileIlkUintWhatEq_false {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileIlkUintWhat I)))
    (hwhat : fileIlkUintWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileIlkUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileIlkUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileIlkUintDataGeWad_true {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (hget : locals.get? "data" = some (.int (Int.ofNat (fileIlkUintData I).toNat)))
    (hge : (1000000000000000000 : Nat) ≤ (fileIlkUintData I).toNat) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .ge (.var "data") (.intLit WAD)) = .ok (.bool true) := by
  have hdata := evalExpr_fileIlkUintData (v := v) (evm := evm) (I := I)
    (locals := locals) hget
  rw [evalExpr?]
  simp only [hdata, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, WAD]
  all_goals first | omega | decide

theorem evalExpr_fileIlkUintDataGeWad_false {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (hget : locals.get? "data" = some (.int (Int.ofNat (fileIlkUintData I).toNat)))
    (hlt : (fileIlkUintData I).toNat < (1000000000000000000 : Nat)) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm
      (.binary .ge (.var "data") (.intLit WAD)) = .ok (.bool false) := by
  have hdata := evalExpr_fileIlkUintData (v := v) (evm := evm) (I := I)
    (locals := locals) hget
  rw [evalExpr?]
  simp only [hdata, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, WAD]
  all_goals first | omega | decide

theorem assign_fileIlkUintChopStorage {v : DogImmutables} (evm : EVM.State)
    {I : ExecutionEnv} {locals : Store} (hsz100 : 100 ≤ I.calldata.size)
    (data : UInt256)
    (hbase : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (fileIlkUintIlkValue I)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (fileIlkUintChopSlotFor I) data
    assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm
      .storage (ilksF (.var "ilk") "chop") (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm') := by
  intro evm'
  have hkeyLen : (fileIlkUintIlkBytes I).length = bytes32Width.val + 1 :=
    fileIlkUintIlkBytes_len hsz100
  have hvar :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "ilk") =
        .ok (fileIlkUintIlkValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") =
      .ok (fileIlkUintIlkValue I)
    rw [hilk]
    rfl
  have hstore :
      storageLocStore evm (wordLoc (fileIlkUintChopSlotFor I))
          (.int (Int.ofNat data.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm (fileIlkUintChopSlotFor I) data
  exact assignStorageRef_storage_scalar (hbackend := rfl)
    (er := fileIlkUintChopEvaledRef I)
    (ty := .elem (.int uint256Int)) (loc := wordLoc (fileIlkUintChopSlotFor I)) (hleaf := by first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩)
    (hbase := hbase)
    (her := by
      simp [fileIlkUintChopEvaledRef, fileIlkUintIlkKey, fileIlkUintIlkValue,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ilksF, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen, hvar])
    (hty := by simp [fileIlkUintIlkKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, IlkStructTy, uint256St])
    (hloc := by rfl)
    (hstore := hstore)

theorem assign_fileIlkUintHoleStorage {v : DogImmutables} (evm : EVM.State)
    {I : ExecutionEnv} {locals : Store} (hsz100 : 100 ≤ I.calldata.size)
    (data : UInt256)
    (hbase : locals.get? "ilks" = none)
    (hilk : locals.get? "ilk" = some (fileIlkUintIlkValue I)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner
      (fileIlkUintHoleSlotFor I) data
    assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm
      .storage (ilksF (.var "ilk") "hole") (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm') := by
  intro evm'
  have hkeyLen : (fileIlkUintIlkBytes I).length = bytes32Width.val + 1 :=
    fileIlkUintIlkBytes_len hsz100
  have hvar :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm (.var "ilk") =
        .ok (fileIlkUintIlkValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "ilk") =
      .ok (fileIlkUintIlkValue I)
    rw [hilk]
    rfl
  have hstore :
      storageLocStore evm (wordLoc (fileIlkUintHoleSlotFor I))
          (.int (Int.ofNat data.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm (fileIlkUintHoleSlotFor I) data
  exact assignStorageRef_storage_scalar (hbackend := rfl)
    (er := fileIlkUintHoleEvaledRef I)
    (ty := .elem (.int uint256Int)) (loc := wordLoc (fileIlkUintHoleSlotFor I)) (hleaf := by first | exact Or.inl ⟨_, rfl⟩ | exact Or.inr ⟨_, rfl⟩)
    (hbase := hbase)
    (her := by
      simp [fileIlkUintHoleEvaledRef, fileIlkUintIlkKey, fileIlkUintIlkValue,
        evalStorageRef, evalStorageRefSteps, evalStorageRefStep, ilksF, valueToKey?,
        EvalResult.ofOption, EvalResult.bind, pure, bind, hkeyLen, hvar])
    (hty := by simp [fileIlkUintIlkKey, storageTypeAt?, storageTypeStep?, contract,
      storageDecls, IlkStructTy, uint256St])
    (hloc := by rfl)
    (hstore := hstore)

theorem fileIlkUintChopSourceBodySplit {v : DogImmutables} {σ σ₀ A I}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : solcSlotWordAt (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkUintWhat I = fileIlkUintChopBytes)
    (hge : (1000000000000000000 : Nat) ≤ (fileIlkUintData I).toNat) :
    let locals := fileIlkUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner
      (fileIlkUintChopSlotFor I) (fileIlkUintData I)
    (ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm1 none) (immStore v)) ∧
      (I.perm = false → ExecTransitionBody config contract
        evm0 locals fileIlkUintTransition.body .staticViolation (immStore v)) := by
  intro locals evm0 evm1
  have hguard := dogAuthGuardEval_true (v := v)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkUintLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.var "what") chopParamLit) = .ok (.bool true) := by
    simpa [chopParamLit, fileIlkUintChopBytes] using
      (evalExpr_fileIlkUintWhatEq_true (v := v) (evm := evm0) (I := I)
        (locals := locals) (bs := fileIlkUintChopBytes)
        (by simpa [locals] using fileIlkUintLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileIlkUintData I).toNat)) := by
    simpa [locals] using
      (evalExpr_fileIlkUintData (v := v) (evm := evm0) (I := I)
        (by simp [locals, fileIlkUintLocals]))
  have hgeExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .ge (.var "data") (.intLit WAD)) = .ok (.bool true) := by
    exact evalExpr_fileIlkUintDataGeWad_true (v := v) (evm := evm0) (I := I)
      (locals := locals) (by simpa [locals] using fileIlkUintLocals_get_data I) hge
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm0
        .storage (ilksF (.var "ilk") "chop")
        (.int (Int.ofNat (fileIlkUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm1) := by
    simpa [evm1] using
      (assign_fileIlkUintChopStorage (v := v) evm0 (I := I) (locals := locals)
        hsz100 (fileIlkUintData I)
        (by simpa [locals] using fileIlkUintLocals_get_ilks I)
        (by simpa [locals] using fileIlkUintLocals_get_ilk I))
  have hprefix {result : ExecResult}
      (hwrite : ExecBlock config { contract := contract, locals := locals, immutables := immStore v }
        evm0 [.assign .storage (ilksF (.var "ilk") "chop") (.var "data")] result) :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileIlkUintTransition.body result := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact execBlock_singleton (ExecStmt.iteTrue hcond
      (ExecBlock.consNormal (ExecStmt.requireTrue hgeExpr) hwrite))
  constructor
  · exact ExecFuncBody.execBlockOK
      (hprefix (ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil))
  · intro hperm
    exact ExecFuncBody.execBlockStatic
      (hprefix (ExecBlock.consStatic (ExecStmt.assignStatic hdata hassign
        (by simp only [evm0, initState]; exact hperm))))

theorem fileIlkUintChopSourceBody {v : DogImmutables} {σ σ₀ A I}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : solcSlotWordAt (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkUintWhat I = fileIlkUintChopBytes)
    (hge : (1000000000000000000 : Nat) ≤ (fileIlkUintData I).toNat) :
    let locals := fileIlkUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner
      (fileIlkUintChopSlotFor I) (fileIlkUintData I)
    ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm1 none) (immStore v) :=
  (fileIlkUintChopSourceBodySplit hwv hsz100 hauth hwhat hge).1

theorem fileIlkUintChopLtWadSourceBody {v : DogImmutables} {σ σ₀ A I}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : solcSlotWordAt (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileIlkUintWhat I = fileIlkUintChopBytes)
    (hlt : (fileIlkUintData I).toNat < (1000000000000000000 : Nat)) :
    let locals := fileIlkUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hguard := dogAuthGuardEval_true (v := v)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkUintLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.var "what") chopParamLit) = .ok (.bool true) := by
    simpa [chopParamLit, fileIlkUintChopBytes] using
      (evalExpr_fileIlkUintWhatEq_true (v := v) (evm := evm0) (I := I)
        (locals := locals) (bs := fileIlkUintChopBytes)
        (by simpa [locals] using fileIlkUintLocals_get_what I) hwhat)
  have hgeExpr :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .ge (.var "data") (.intLit WAD)) = .ok (.bool false) := by
    exact evalExpr_fileIlkUintDataGeWad_false (v := v) (evm := evm0) (I := I)
      (locals := locals) (by simpa [locals] using fileIlkUintLocals_get_data I) hlt
  have hthen :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        [.require (.binary .ge (.var "data") (.intLit WAD)),
          .assign .storage (ilksF (.var "ilk") "chop") (.var "data")]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hgeExpr)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileIlkUintTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteTrue hcond hthen)
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

theorem fileIlkUintHoleSourceBodySplit {v : DogImmutables} {σ σ₀ A I}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : solcSlotWordAt (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotChop : fileIlkUintWhat I ≠ fileIlkUintChopBytes)
    (hwhat : fileIlkUintWhat I = fileIlkUintHoleBytes) :
    let locals := fileIlkUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner
      (fileIlkUintHoleSlotFor I) (fileIlkUintData I)
    (ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body
      (.returned { contract := contract, locals := locals, immutables := immStore v } evm1 none) (immStore v)) ∧
      (I.perm = false → ExecTransitionBody config contract
        evm0 locals fileIlkUintTransition.body .staticViolation (immStore v)) := by
  intro locals evm0 evm1
  have hguard := dogAuthGuardEval_true (v := v)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkUintLocals]) hauth
  have hcondChop :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.var "what") chopParamLit) = .ok (.bool false) := by
    simpa [chopParamLit, fileIlkUintChopBytes] using
      (evalExpr_fileIlkUintWhatEq_false (v := v) (evm := evm0) (I := I)
        (locals := locals) (bs := fileIlkUintChopBytes)
        (by simpa [locals] using fileIlkUintLocals_get_what I) hnotChop)
  have hcondHole :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.var "what") holeParamLit) = .ok (.bool true) := by
    simpa [holeParamLit, fileIlkUintHoleBytes] using
      (evalExpr_fileIlkUintWhatEq_true (v := v) (evm := evm0) (I := I)
        (locals := locals) (bs := fileIlkUintHoleBytes)
        (by simpa [locals] using fileIlkUintLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileIlkUintData I).toNat)) := by
    simpa [locals] using
      (evalExpr_fileIlkUintData (v := v) (evm := evm0) (I := I)
        (by simp [locals, fileIlkUintLocals]))
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals, immutables := immStore v } evm0
        .storage (ilksF (.var "ilk") "hole")
        (.int (Int.ofNat (fileIlkUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals, immutables := immStore v }, evm1) := by
    simpa [evm1] using
      (assign_fileIlkUintHoleStorage (v := v) evm0 (I := I) (locals := locals)
        hsz100 (fileIlkUintData I)
        (by simpa [locals] using fileIlkUintLocals_get_ilks I)
        (by simpa [locals] using fileIlkUintLocals_get_ilk I))
  have hprefix {result : ExecResult}
      (hwrite : ExecBlock config { contract := contract, locals := locals, immutables := immStore v }
        evm0 [.assign .storage (ilksF (.var "ilk") "hole") (.var "data")] result) :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileIlkUintTransition.body result := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact execBlock_singleton (ExecStmt.iteFalse hcondChop
      (execBlock_singleton (ExecStmt.iteTrue hcondHole hwrite)))
  constructor
  · exact ExecFuncBody.execBlockOK
      (hprefix (ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil))
  · intro hperm
    exact ExecFuncBody.execBlockStatic
      (hprefix (ExecBlock.consStatic (ExecStmt.assignStatic hdata hassign
        (by simp only [evm0, initState]; exact hperm))))

theorem fileIlkUintUnrecognizedSourceBody {v : DogImmutables} {σ σ₀ A I}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : solcSlotWordAt (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotChop : fileIlkUintWhat I ≠ fileIlkUintChopBytes)
    (hnotHole : fileIlkUintWhat I ≠ fileIlkUintHoleBytes) :
    let locals := fileIlkUintLocals I
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body
      .reverted (immStore v) := by
  intro locals evm0
  have hguard := dogAuthGuardEval_true (v := v)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileIlkUintLocals]) hauth
  have hcondChop :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.var "what") chopParamLit) = .ok (.bool false) := by
    simpa [chopParamLit, fileIlkUintChopBytes] using
      (evalExpr_fileIlkUintWhatEq_false (v := v) (evm := evm0) (I := I)
        (locals := locals) (bs := fileIlkUintChopBytes)
        (by simpa [locals] using fileIlkUintLocals_get_what I) hnotChop)
  have hcondHole :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.binary .eq (.var "what") holeParamLit) = .ok (.bool false) := by
    simpa [holeParamLit, fileIlkUintHoleBytes] using
      (evalExpr_fileIlkUintWhatEq_false (v := v) (evm := evm0) (I := I)
        (locals := locals) (bs := fileIlkUintHoleBytes)
        (by simpa [locals] using fileIlkUintLocals_get_what I) hnotHole)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals, immutables := immStore v } evm0
        (.boolLit false) = .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hholeElse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have helse :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        [.ite
          (.binary .eq (.var "what") holeParamLit)
          [ .assign .storage (ilksF (.var "ilk") "hole") (.var "data") ]
          [ .require (.boolLit false) ]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcondHole hholeElse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals, immutables := immStore v } evm0
        fileIlkUintTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcondChop helse)
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

theorem dogReachFileIlkUintBody {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 7)) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) ⟨272⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C := by
  have hword : solcSelectorWord I = ⟨0x1a0b287e⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0x1a 0x0b 0x28 0x7e ⟨0x1a0b287e⟩
      (by native_decide) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootTgt : armTgt code (⟨32⟩ : UInt256) = ⟨162⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hlowTgt : armTgt code (⟨163⟩ : UInt256) = ⟨222⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨163⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h162 : RD code I g (initState σ σ₀ g A I) ⟨162⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ (k32 + 5) (C32 + 22) := by
    simpa [hrootTgt] using
      RD.selectorSplitTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot
        (by
          rw [hrootTgt]
          exact dogPatchedDJumpPrefix1405 ⟨162⟩ hpatch (by native_decide))
        (by simp)
  have h163 : RD code I g (initState σ σ₀ g A I) ⟨163⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ (k32 + 5 + 1) (C32 + 22 + 1) := by
    simpa using
      h162.jumpdest
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by simp only [List.length_singleton]; omega)
  have hlow :
      UInt256.gt (armSelNat code (⟨163⟩ : UInt256)) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨163⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h222 : RD code I g (initState σ σ₀ g A I) ⟨222⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      σ (k32 + 5 + 1 + 5) (C32 + 22 + 1 + 22) := by
    simpa [hlowTgt] using
      RD.selectorSplitTakenAuto h163 (dogLowSplitWellFormed hpatch) hlow
        (by
          rw [hlowTgt]
          exact dogPatchedDJumpPrefix1405 ⟨222⟩ hpatch (by native_decide))
        (by simp)
  have h223 := h222.jumpdest
    (by
      rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length_singleton]; omega)
  have hfileIlkUint : UInt256.eq (dogSelectorWord 7) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h272 := by
    simpa using
      h223.selectorArmTaken (selNat := dogSelectorWord 7) (tgt := (⟨272⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hfileIlkUint
        (dogPatchedDJumpPrefix1405 ⟨272⟩ hpatch (by native_decide))
        (by simp)
  exact ⟨_, _, h272⟩

theorem RD.dogFileIlkUintDecodeToRoutine {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {ret de sel : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨294⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hroutine : (D_J code 0).contains ⟨845⟩ = true)
    (hov : R.length + 11 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨845⟩
      (fileIlkUintData ee :: fileIlkUintWhatWord ee :: fileIlkUintIlkWord ee :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  have rd295 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd296 := rd295.pop
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd297 := rd296.dup1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd298 := rd297.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd299 := rd298.swap1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd301 := rd299.push1 ⟨32⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd302 := rd301.dup2
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd303 := rd302.add
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd304 := rd303.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd305 := rd304.swap1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd307 := rd305.push1 ⟨64⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd308 := rd307.add
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd309 := rd308.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd312 := rd309.push2 ⟨845⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  exact ⟨_, _, by
    simpa [fileIlkUintData, fileIlkUintWhatWord, fileIlkUintIlkWord, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (UInt256.add (⟨32⟩ : UInt256) ⟨4⟩).toNat = 36 from by decide,
      show (UInt256.add (⟨64⟩ : UInt256) ⟨4⟩).toNat = 68 from by decide]
      using rd312.jump
        (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
        hroutine (by evm_ov)⟩

theorem RD.dogFileIlkUintToSwitch {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState σ σ₀ g A I)
      ⟨272⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩) :
    ∃ k C, RD code I g (initState σ σ₀ g A I) ⟨934⟩
      (fileIlkUintData I :: fileIlkUintWhatWord I :: fileIlkUintIlkWord I :: ⟨313⟩ :: sel :: [])
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty σ k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := code) (sel := sel) (entry := ⟨272⟩) (ret := ⟨313⟩)
    (decoded := ⟨294⟩) (need := ⟨96⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedDJumpPrefix1405 ⟨294⟩ hpatch (by native_decide))
    (by
      exact solcDecodeLenCheckOkUnsigned
        (sz := I.calldata.size) (head := ⟨4⟩) (need := ⟨96⟩)
        (by change 100 ≤ I.calldata.size; exact hsz100) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.dogFileIlkUintDecodeToRoutine
    (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hdecoded (dogPatchedJumpDest hpatch (by native_decide)) (by simp)
  obtain ⟨_, _, hafterAuth⟩ := RD.solcAuthCheckOk
    (code := code) (pc := ⟨845⟩) (okPc := ⟨934⟩)
    (key := fileIlkUintData I) (ret := fileIlkUintWhatWord I)
    (R := [fileIlkUintIlkWord I, ⟨313⟩, sel])
    (by simpa [fileIlkUintData, fileIlkUintWhatWord, fileIlkUintIlkWord] using hroutine)
    (by
      unfold solcAuthCheckWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
    hauth (dogPatchedDJumpPrefix1405 ⟨934⟩ hpatch (by native_decide)) (by simp)
  exact ⟨_, _, hafterAuth⟩

theorem RD.dogFileIlkUintAuthRevert {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState σ σ₀ g A I)
      ⟨272⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩) :
    RDrev code g (initState σ σ₀ g A I) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := code) (sel := sel) (entry := ⟨272⟩) (ret := ⟨313⟩)
    (decoded := ⟨294⟩) (need := ⟨96⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedDJumpPrefix1405 ⟨294⟩ hpatch (by native_decide))
    (by
      exact solcDecodeLenCheckOkUnsigned
        (sz := I.calldata.size) (head := ⟨4⟩) (need := ⟨96⟩)
        (by change 100 ≤ I.calldata.size; exact hsz100) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.dogFileIlkUintDecodeToRoutine
    (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hdecoded (dogPatchedJumpDest hpatch (by native_decide)) (by simp)
  exact RD.dogAuthCheckRevert
    (code := code) (pc := ⟨845⟩) (okPc := ⟨934⟩)
    (key := fileIlkUintData I) (ret := fileIlkUintWhatWord I)
    (R := [fileIlkUintIlkWord I, ⟨313⟩, sel])
    (by simpa [fileIlkUintData, fileIlkUintWhatWord, fileIlkUintIlkWord] using hroutine)
    (by
      unfold solcAuthCheckWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
    (by
      unfold solcErrorStringRevertTailWf solcAuthTailPc dogNotAuthorizedRawWord
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
    hauth (by simp)

theorem RD.dogFileIlkUintLogTail {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ilk ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨1176⟩ (data :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (sel :: R) (writeWord mem 128 data)
      (UInt256.ofNat 5) rdata acc k' C' := by
  have rd1177 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rdMload := evm_run rd1177 with [
    raw push1 ⟨64⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3)
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) hread64)
      (by native_decide) (by evm_ov)]
  have rdMstorePrefix := evm_run rdMload with [
    raw dup3
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdMstore := rdMstorePrefix.mstore 6 (writeWord mem 128 data) (UInt256.ofNat 5)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hread64' :
      (writeWord mem 128 data).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [writeWord_read_preserved mem 128 64 data
      (by rw [hmem]; native_decide)
      (Or.inl ⟨by norm_num, by rw [hmem]⟩)]
    exact hread64
  have rdMload2Prefix := rdMstore.swap1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rdMload2 := rdMload2Prefix.mload 0 ⟨128⟩ (UInt256.ofNat 5)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    mem_cost
    (mloadFreePtrValue
      (by
        have hsz := writeWord_size mem 128 data (by rw [hmem]; native_decide)
        rw [hsz, hmem]
        decide) hread64')
    (by native_decide) (by evm_ov)
  have rdTopicStack := evm_run rdMload2 with [
    raw dup4
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup6
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdTopic := rdTopicStack.pushConst dogFileIlkUintLogTopic
    (width := 32) (op := .PUSH32) (by decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLogStack := evm_run rdTopic with [
    raw swap2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdLog := RD.log3 0 (UInt256.ofNat 5) rdLogStack
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    hperm mem_cost (by native_decide) (by simp only [List.length_cons]; omega)
  have rdPop := evm_run rdLog with [
    raw pop
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, rdPop.jump
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    hret (by evm_ov)⟩

theorem RD.dogFileIlkUintStoreChopLogSplit {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ilk ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨934⟩ (data :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata σ k C)
    (hmatch : what = ABI.bytesToWord fileIlkUintChopBytes)
    (hge : (1000000000000000000 : Nat) ≤ data.toNat)
    (hret : (D_J code 0).contains ret = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 12 ≤ 1024) :
    (ee.perm = true ∧
      ∃ k' C', RD code ee g s0 ret (sel :: R)
        (writeWord (twoWordHashMem ilk ⟨1⟩ mem) 128 data) (UInt256.ofNat 5) rdata
        (sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨1⟩ ilk + ⟨1⟩) data) k' C') ∨
      (ee.perm = false ∧ RDstatic code g s0) := by
  have rd935 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd943 := evm_run rd935 with [
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push4 ⟨104236791⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨228⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have hconst : UInt256.shiftLeft ⟨104236791⟩ ⟨228⟩ =
      ABI.bytesToWord fileIlkUintChopBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd943
  have rd944 := rd943.eq
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  rw [uInt256_eq_self] at rd944
  have rd945 := rd944.iszero
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd945
  have rd946 := rd945.push2 ⟨1059⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd950 := rd946.jumpiNT
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd959 := rd950.pushConst (⟨1000000000000000000⟩ : UInt256)
    (width := 8) (op := .PUSH8) (by decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by simp only [List.length_cons]; omega)
  have rd960 := rd959.dup2
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd961 := rd960.lt
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have hlt0 : UInt256.lt data (⟨1000000000000000000⟩ : UInt256) = ⟨0⟩ := by
    apply ult_zero
    simpa using hge
  rw [hlt0] at rd961
  have rd962 := rd961.iszero
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd962
  have rd965 := rd962.push2 ⟨1033⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd1033 := rd965.jumpiT
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    one_ne_zero_uint (dogPatchedDJumpPrefix1405 ⟨1033⟩ hpatch (by native_decide))
    (by evm_ov)
  have rd1034 := rd1033.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rdMstore0Prefix := evm_run rd1034 with [
    raw push1 ⟨0⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup4
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem ilk mem)
    (UInt256.ofNat 3)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem ilk ⟨1⟩ mem)
    (UInt256.ofNat 3)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hhashSize : (twoWordHashMem ilk ⟨1⟩ mem).size = 96 :=
    twoWordHashMem_size_96 ilk ⟨1⟩ hmem
  have hhashRead64 :
      (twoWordHashMem ilk ⟨1⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 ilk ⟨1⟩ hmem hread64
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((twoWordHashMem ilk ⟨1⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ ilk :=
    twoWordHashMem_solcMappingSlot ⟨1⟩ ilk hmem
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨1⟩ ilk)
    (UInt256.ofNat 3)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    mem_cost hslot (by native_decide) (by evm_ov)
  have rdSlotPlus := rdSlot.add
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rdBeforeStore := evm_run rdSlotPlus with [
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have hstoreDec : decode code ⟨1054⟩ = some (.SSTORE, none) := by
    rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
    native_decide
  by_cases hperm : ee.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rdBeforeStore.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rdAfterStore⟩ := rdBeforeStore.sstore hperm
    hstoreDec
    (by evm_ov)
  have rdPushTail := rdAfterStore.push2 ⟨1176⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rdTail := rdPushTail.jump
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedDJumpPrefix1405 ⟨1176⟩ hpatch (by native_decide)) (by evm_ov)
  exact RD.dogFileIlkUintLogTail
    (v := v) (code := code) (data := data) (what := what) (ilk := ilk)
    (ret := ret) (sel := sel) (R := R) hpatch
    (by simpa [hmatch, hconst] using rdTail) hret hperm hhashSize hhashRead64 hov

theorem RD.dogFileIlkUintStoreHoleLogSplit {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ilk ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨934⟩ (data :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata σ k C)
    (hnotChop : what ≠ ABI.bytesToWord fileIlkUintChopBytes)
    (hmatch : what = ABI.bytesToWord fileIlkUintHoleBytes)
    (hret : (D_J code 0).contains ret = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 12 ≤ 1024) :
    (ee.perm = true ∧
      ∃ k' C', RD code ee g s0 ret (sel :: R)
        (writeWord (twoWordHashMem ilk ⟨1⟩ mem) 128 data) (UInt256.ofNat 5) rdata
        (sstoreAccountMap ee.codeOwner σ (solcMappingSlot ⟨1⟩ ilk + ⟨2⟩) data) k' C') ∨
      (ee.perm = false ∧ RDstatic code g s0) := by
  have rd935 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd943 := evm_run rd935 with [
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push4 ⟨104236791⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨228⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have hconstChop : UInt256.shiftLeft ⟨104236791⟩ ⟨228⟩ =
      ABI.bytesToWord fileIlkUintChopBytes := by
    native_decide
  rw [hconstChop] at rd943
  have rd944 := rd943.eq
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileIlkUintChopBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hnotChop h.symm)
  rw [heq0] at rd944
  have rd945 := rd944.iszero
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd945
  have rd946 := rd945.push2 ⟨1059⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd1059 := rd946.jumpiT
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    one_ne_zero_uint (dogPatchedDJumpPrefix1405 ⟨1059⟩ hpatch (by native_decide))
    (by evm_ov)
  have rd1060 := rd1059.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd1068 := evm_run rd1060 with [
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push4 ⟨1752132709⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨224⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have hconstHole : UInt256.shiftLeft ⟨1752132709⟩ ⟨224⟩ =
      ABI.bytesToWord fileIlkUintHoleBytes := by
    native_decide
  rw [hmatch, ← hconstHole] at rd1068
  have rd1069 := rd1068.eq
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  rw [uInt256_eq_self] at rd1069
  have rd1070 := rd1069.iszero
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1070
  have rd1071 := rd1070.push2 ⟨1099⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd1075 := rd1071.jumpiNT
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rdMstore0Prefix := evm_run rd1075 with [
    raw push1 ⟨0⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup4
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdAfterKey := rdMstore0Prefix.mstore 0 (wordAt0Mem ilk mem)
    (UInt256.ofNat 3)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rdMstoreSlotPrefix := evm_run rdAfterKey with [
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdHashMem := rdMstoreSlotPrefix.mstore 0 (twoWordHashMem ilk ⟨1⟩ mem)
    (UInt256.ofNat 3)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hhashSize : (twoWordHashMem ilk ⟨1⟩ mem).size = 96 :=
    twoWordHashMem_size_96 ilk ⟨1⟩ hmem
  have hhashRead64 :
      (twoWordHashMem ilk ⟨1⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 ilk ⟨1⟩ hmem hread64
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (KEC ((twoWordHashMem ilk ⟨1⟩ mem).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ ilk :=
    twoWordHashMem_solcMappingSlot ⟨1⟩ ilk hmem
  have rdKeccakPrefix := evm_run rdHashMem with [
    raw push1 ⟨64⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdSlot := rdKeccakPrefix.keccak256 0 (solcMappingSlot ⟨1⟩ ilk)
    (UInt256.ofNat 3)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    mem_cost hslot (by native_decide) (by evm_ov)
  have rdSlotPlusRaw := evm_run rdSlot with [
    raw push1 ⟨2⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdSlotPlus := by
    simpa [u256_add_comm (⟨2⟩ : UInt256) (solcMappingSlot ⟨1⟩ ilk)] using rdSlotPlusRaw
  have rdBeforeStore := evm_run rdSlotPlus with [
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have hstoreDec : decode code ⟨1094⟩ = some (.SSTORE, none) := by
    rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
    native_decide
  by_cases hperm : ee.perm = true
  swap
  · exact Or.inr ⟨by simpa using hperm,
      rdBeforeStore.sstoreStatic (by simpa using hperm) hstoreDec (by evm_ov)⟩
  refine Or.inl ⟨hperm, ?_⟩
  obtain ⟨_, _, rdAfterStore⟩ := rdBeforeStore.sstore hperm
    hstoreDec
    (by evm_ov)
  have rdPushTail := rdAfterStore.push2 ⟨1176⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rdTail := rdPushTail.jump
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedDJumpPrefix1405 ⟨1176⟩ hpatch (by native_decide)) (by evm_ov)
  exact RD.dogFileIlkUintLogTail
    (v := v) (code := code) (data := data) (what := what) (ilk := ilk)
    (ret := ret) (sel := sel) (R := R) hpatch
    (by simpa [hmatch, hconstHole] using rdTail) hret hperm hhashSize hhashRead64 hov

theorem RD.dogFileIlkUintChopLtWadRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ilk ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨934⟩ (data :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hmatch : what = ABI.bytesToWord fileIlkUintChopBytes)
    (hlt : data.toNat < (1000000000000000000 : Nat))
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev code g s0 := by
  have rd935 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd943 := evm_run rd935 with [
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push4 ⟨104236791⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨228⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have hconst : UInt256.shiftLeft ⟨104236791⟩ ⟨228⟩ =
      ABI.bytesToWord fileIlkUintChopBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd943
  have rd944 := rd943.eq
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  rw [uInt256_eq_self] at rd944
  have rd945 := rd944.iszero
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd945
  have rd946 := rd945.push2 ⟨1059⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd950 := rd946.jumpiNT
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd959 := rd950.pushConst (⟨1000000000000000000⟩ : UInt256)
    (width := 8) (op := .PUSH8) (by decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by simp only [List.length_cons]; omega)
  have rd960 := rd959.dup2
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd961 := rd960.lt
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have hlt1 : UInt256.lt data (⟨1000000000000000000⟩ : UInt256) = ⟨1⟩ := by
    apply ult_one
    simpa using hlt
  rw [hlt1] at rd961
  have rd962 := rd961.iszero
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd962
  have rd965 := rd962.push2 ⟨1033⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd966 := rd965.jumpiNT
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨966⟩) (len := ⟨20⟩) (rawWord := dogFileChopLtWadRawWord)
    (shift := ⟨98⟩) (word := UInt256.shiftLeft dogFileChopLtWadRawWord ⟨98⟩)
    (op := .PUSH20) (width := 20) rd966
    (by
      unfold solcErrorStringRevertTailWf dogFileChopLtWadRawWord
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
    (by decide) (by rfl) hmem hread64 (by simp only [List.length_cons]; omega)

theorem RD.dogFileIlkUintUnrecognizedRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ilk ret sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {acc : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨934⟩ (data :: what :: ilk :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hnotChop : what ≠ ABI.bytesToWord fileIlkUintChopBytes)
    (hnotHole : what ≠ ABI.bytesToWord fileIlkUintHoleBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 12 ≤ 1024) :
    RDrev code g s0 := by
  have rd935 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd943 := evm_run rd935 with [
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push4 ⟨104236791⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨228⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have hconstChop : UInt256.shiftLeft ⟨104236791⟩ ⟨228⟩ =
      ABI.bytesToWord fileIlkUintChopBytes := by
    native_decide
  rw [hconstChop] at rd943
  have rd944 := rd943.eq
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have heqChop0 : UInt256.eq (ABI.bytesToWord fileIlkUintChopBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hnotChop h.symm)
  rw [heqChop0] at rd944
  have rd945 := rd944.iszero
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd945
  have rd946 := rd945.push2 ⟨1059⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd1059 := rd946.jumpiT
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    one_ne_zero_uint (dogPatchedDJumpPrefix1405 ⟨1059⟩ hpatch (by native_decide))
    (by evm_ov)
  have rd1060 := rd1059.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd1068 := evm_run rd1060 with [
    raw dup2
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push4 ⟨1752132709⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨224⟩
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
      (by evm_ov)]
  have hconstHole : UInt256.shiftLeft ⟨1752132709⟩ ⟨224⟩ =
      ABI.bytesToWord fileIlkUintHoleBytes := by
    native_decide
  rw [hconstHole] at rd1068
  have rd1069 := rd1068.eq
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have heqHole0 : UInt256.eq (ABI.bytesToWord fileIlkUintHoleBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hnotHole h.symm)
  rw [heqHole0] at rd1069
  have rd1070 := rd1069.iszero
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1070
  have rd1071 := rd1070.push2 ⟨1099⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd1099 := rd1071.jumpiT
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    one_ne_zero_uint (dogPatchedDJumpPrefix1405 ⟨1099⟩ hpatch (by native_decide))
    (by evm_ov)
  have rd1100 := rd1099.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  exact RD.solcErrorStringRevertTailDirect
    (pc := ⟨1100⟩) (len := ⟨27⟩) (word := dogFileUnrecognizedRawWord)
    (op := .PUSH32) (width := 32) rd1100
    (by
      unfold solcErrorStringRevertTailDirectWf dogFileUnrecognizedRawWord
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
    (by decide) hmem hread64 (by simp only [List.length_cons]; omega)

theorem dogFileIlkUintBodyCoreOk
    {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileIlkUintTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode
        (fileIlkUintTransition.params.map Param.name)
        (transitionSignature fileIlkUintTransition).paramTypes I.calldata =
          some (fileIlkUintLocals I))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨272⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  let data := fileIlkUintData I
  let callerSlot := dogCallerWardsSlot I
  let locals := fileIlkUintLocals I
  have henc : returnEquiv ByteArray.empty none fileIlkUintTransition.returnType := by
    rw [show fileIlkUintTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  by_cases hauthEvm : solcSlotWordAt callerSlot σ I = ⟨1⟩
  · have hauthSolm : solcSlotWordAt callerSlot σ I = ⟨1⟩ := hauthEvm
    have hauthSolc :
        solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, dogCallerWardsSlot, solcSlotWordAt] using hauthEvm
    have hmemAuth :
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
      twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
    have hread64Auth :
        (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
          UInt256.toByteArray ⟨128⟩ :=
      twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
        solcFreePtrMem_read64
    obtain ⟨_, _, hswitch⟩ := RD.dogFileIlkUintToSwitch hpatch hreach hsz100 hsize
      hauthSolc
    by_cases hwhatChop : fileIlkUintWhat I = fileIlkUintChopBytes
    · have hwordChop :
          fileIlkUintWhatWord I = ABI.bytesToWord fileIlkUintChopBytes :=
        fileIlkUintWhatWord_eq_of_bytes_eq (by omega) hwhatChop
      by_cases hltWad : data.toNat < (1000000000000000000 : Nat)
      · let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody config contract evm0 locals
              fileIlkUintTransition.body .reverted (immStore v) := by
          simpa [evm0, locals, data] using
            (fileIlkUintChopLtWadSourceBody (v := v)
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthSolm hwhatChop (by simpa [data] using hltWad))
        have hrev := RD.dogFileIlkUintChopLtWadRevert
          (v := v) (code := code) (data := data) (what := fileIlkUintWhatWord I)
          (ilk := fileIlkUintIlkWord I) (ret := ⟨313⟩) (sel := sel) (R := [])
          hpatch hswitch hwordChop hltWad hmemAuth hread64Auth (by simp)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hgeWad : (1000000000000000000 : Nat) ≤ data.toNat := by
          exact Nat.le_of_not_gt hltWad
        let actualSlot := solcMappingSlot ⟨1⟩ (fileIlkUintIlkWord I) + ⟨1⟩
        let sourceSlot := fileIlkUintChopSlotFor I
        let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
        let evm1 := Solm.EVM.storageStore evm0 I.codeOwner sourceSlot data
        have hslotEq : actualSlot = sourceSlot := by
          simpa [actualSlot, sourceSlot] using
            (fileIlkUintChopSlotFor_eq (I := I) hsz100).symm
        have hbodySplit :
            (ExecTransitionBody config contract evm0 locals
              fileIlkUintTransition.body
              (.returned { contract := contract, locals := locals, immutables := immStore v } evm1 none) (immStore v)) ∧
            (I.perm = false → ExecTransitionBody config contract
              evm0 locals fileIlkUintTransition.body .staticViolation (immStore v)) := by
          simpa [evm0, evm1, locals, data, sourceSlot] using
            (fileIlkUintChopSourceBodySplit (v := v)
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hsz100 hauthSolm hwhatChop (by simpa [data] using hgeWad))
        rcases RD.dogFileIlkUintStoreChopLogSplit
          (v := v) (code := code) (data := data) (what := fileIlkUintWhatWord I)
          (ilk := fileIlkUintIlkWord I) (ret := ⟨313⟩) (sel := sel) (R := [])
          hpatch hswitch hwordChop hgeWad
          (dogPatchedDJumpPrefix1405 ⟨313⟩ hpatch (by native_decide))
          hmemAuth hread64Auth (by simp) with
            ⟨_hperm, _, _, hretPc⟩ | ⟨hperm, hstatic⟩
        swap
        · exact hstatic.reEquivStaticHalt hcode hdispatch hdecode (hbodySplit.2 hperm)
        have hretPc' := hretPc.jumpdest
          (by
            rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
            native_decide)
          (by evm_ov)
        have hret :
            RDret code (Sat256.ofUInt256 g)
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (sstoreAccountMap I.codeOwner σ actualSlot data) ByteArray.empty := by
          simpa [actualSlot] using RD.stop hretPc'
            (by
              change decode code (⟨314⟩ : UInt256) = some (.STOP, .none)
              rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
              native_decide)
            (by simp only [List.length_singleton]; omega)
        have haccounts :
            Eq (sstoreAccountMap I.codeOwner σ actualSlot data)
              evm1.accountMap := by
          simpa [evm1, evm0, initState, storageStore_accountMap, actualSlot, sourceSlot,
            hslotEq]
        exact hret.reEquivExecutionGen hcode hdispatch hdecode hbodySplit.1
          haccounts henc
    · have hnotChopWord :
          fileIlkUintWhatWord I ≠ ABI.bytesToWord fileIlkUintChopBytes :=
        fileIlkUintWhatWord_ne_of_bytes_ne (by omega) hwhatChop
          fileIlkUintChopBytes_length
      by_cases hwhatHole : fileIlkUintWhat I = fileIlkUintHoleBytes
      · have hwordHole :
            fileIlkUintWhatWord I = ABI.bytesToWord fileIlkUintHoleBytes :=
          fileIlkUintWhatWord_eq_of_bytes_eq (by omega) hwhatHole
        let actualSlot := solcMappingSlot ⟨1⟩ (fileIlkUintIlkWord I) + ⟨2⟩
        let sourceSlot := fileIlkUintHoleSlotFor I
        let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
        let evm1 := Solm.EVM.storageStore evm0 I.codeOwner sourceSlot data
        have hslotEq : actualSlot = sourceSlot := by
          simpa [actualSlot, sourceSlot] using
            (fileIlkUintHoleSlotFor_eq (I := I) hsz100).symm
        have hbodySplit :
            (ExecTransitionBody config contract evm0 locals
              fileIlkUintTransition.body
              (.returned { contract := contract, locals := locals, immutables := immStore v } evm1 none) (immStore v)) ∧
            (I.perm = false → ExecTransitionBody config contract
              evm0 locals fileIlkUintTransition.body .staticViolation (immStore v)) := by
          simpa [evm0, evm1, locals, data, sourceSlot] using
            (fileIlkUintHoleSourceBodySplit (v := v)
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hsz100 hauthSolm hwhatChop hwhatHole)
        rcases RD.dogFileIlkUintStoreHoleLogSplit
          (v := v) (code := code) (data := data) (what := fileIlkUintWhatWord I)
          (ilk := fileIlkUintIlkWord I) (ret := ⟨313⟩) (sel := sel) (R := [])
          hpatch hswitch hnotChopWord hwordHole
          (dogPatchedDJumpPrefix1405 ⟨313⟩ hpatch (by native_decide))
          hmemAuth hread64Auth (by simp) with
            ⟨_hperm, _, _, hretPc⟩ | ⟨hperm, hstatic⟩
        swap
        · exact hstatic.reEquivStaticHalt hcode hdispatch hdecode (hbodySplit.2 hperm)
        have hretPc' := hretPc.jumpdest
          (by
            rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
            native_decide)
          (by evm_ov)
        have hret :
            RDret code (Sat256.ofUInt256 g)
              (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (sstoreAccountMap I.codeOwner σ actualSlot data) ByteArray.empty := by
          simpa [actualSlot] using RD.stop hretPc'
            (by
              change decode code (⟨314⟩ : UInt256) = some (.STOP, .none)
              rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
              native_decide)
            (by simp only [List.length_singleton]; omega)
        have haccounts :
            Eq (sstoreAccountMap I.codeOwner σ actualSlot data)
              evm1.accountMap := by
          simpa [evm1, evm0, initState, storageStore_accountMap, actualSlot, sourceSlot,
            hslotEq]
        exact hret.reEquivExecutionGen hcode hdispatch hdecode hbodySplit.1
          haccounts henc
      · have hnotHoleWord :
            fileIlkUintWhatWord I ≠ ABI.bytesToWord fileIlkUintHoleBytes :=
          fileIlkUintWhatWord_ne_of_bytes_ne (by omega) hwhatHole
            fileIlkUintHoleBytes_length
        let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
        have hbody :
            ExecTransitionBody config contract evm0 locals
              fileIlkUintTransition.body .reverted (immStore v) := by
          simpa [evm0, locals] using
            (fileIlkUintUnrecognizedSourceBody (v := v)
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              hwv hauthSolm hwhatChop hwhatHole)
        have hrev := RD.dogFileIlkUintUnrecognizedRevert
          (v := v) (code := code) (data := data) (what := fileIlkUintWhatWord I)
          (ilk := fileIlkUintIlkWord I) (ret := ⟨313⟩) (sel := sel) (R := [])
          hpatch hswitch hnotChopWord hnotHoleWord hmemAuth hread64Auth (by simp)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : solcSlotWordAt callerSlot σ I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm hsolm
    let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
    have hbody :
        ExecTransitionBody config contract evm0 locals fileIlkUintTransition.body
          .reverted (immStore v) := by
      have hguard := dogAuthGuardEval_false (v := v)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals, fileIlkUintLocals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals, immutables := immStore v })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [
          .ite
            (.binary .eq (.var "what") chopParamLit)
            [ .require (.binary .ge (.var "data") (.intLit WAD)),
              .assign .storage (ilksF (.var "ilk") "chop") (.var "data") ]
            [ .ite
                (.binary .eq (.var "what") holeParamLit)
                [ .assign .storage (ilksF (.var "ilk") "hole") (.var "data") ]
                [ .require (.boolLit false) ] ] ])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, fileIlkUintTransition, nonpayable, auth, evm0, locals] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc :
        solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, dogCallerWardsSlot, solcSlotWordAt] using hauthEvm
    have hrev := RD.dogFileIlkUintAuthRevert hpatch hreach hsz100 hsize hauthSolc
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem dogFileIlkUintBodyCoreDecodeFailed_short
    {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some fileIlkUintTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState σ σ₀ (Sat256.ofUInt256 g) A I) ⟨272⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty σ k C) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := ⟨272⟩) (ret := ⟨313⟩)
    (decoded := ⟨294⟩) (need := ⟨96⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (dogDecode_fileIlkUint_none_short hsz4 hshort)

theorem dogFileIlkUintBodyCore {v : DogImmutables} {code : ByteArray}
    {σ σ₀ A I} {g : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (dogSelBytes 7)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 7) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileIlkUintTransition :=
    dogDispatchFileIlkUint hsel
  have hreach := dogReachFileIlkUintBody
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · exact dogFileIlkUintBodyCoreOk hpatch hcode hwv hsz100 hsize hdispatch
      (dogDecode_fileIlkUint_ok hsz100) hreach
  · exact dogFileIlkUintBodyCoreDecodeFailed_short hpatch hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dog
