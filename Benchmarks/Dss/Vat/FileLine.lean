import Benchmarks.Dss.Vat.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 50000000
set_option maxHeartbeats 1000000

namespace Benchmarks.Dss.Vat

/-! ## `file(bytes32,uint256)` -/

abbrev fileLineWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileLineWhatWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev fileLineData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileLineBytes : List UInt8 :=
  [76, 105, 110, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileLineWord : UInt256 :=
  UInt256.shiftLeft (⟨0x4c696e65⟩ : UInt256) ⟨224⟩

abbrev fileLineLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileLineWhat I))).insert
    "data" (.int (Int.ofNat (fileLineData I).toNat))

theorem fileLineWhat_length {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    (fileLineWhat I).length = 32 := by
  unfold fileLineWhat
  rw [List.length_take, List.length_drop]
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [htlen]
  omega

theorem fileLineWhatWord_eq {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    ABI.bytesToWord (fileLineWhat I) = fileLineWhatWord I := by
  simpa [fileLineWhat, fileLineWhatWord] using
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem fileLineBytes_length : fileLineBytes.length = 32 := by
  rfl

theorem fileLineBytes_word : ABI.bytesToWord fileLineBytes = fileLineWord := by
  native_decide

theorem fileLineWhat_eq_of_word_eq {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hword : fileLineWhatWord I = fileLineWord) :
    fileLineWhat I = fileLineBytes := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileLineWhat I)
    (fileLineWhat_length (I := I) hsz68)
  rw [fileLineWhatWord_eq (I := I) hsz68, hword, ← fileLineBytes_word] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := fileLineBytes)
    fileLineBytes_length)

theorem fileLineWhatWord_eq_of_bytes_eq {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hwhat : fileLineWhat I = fileLineBytes) :
    fileLineWhatWord I = fileLineWord := by
  rw [← fileLineBytes_word, ← hwhat]
  exact (fileLineWhatWord_eq (I := I) hsz68).symm

theorem fileLineWhatWord_ne_of_bytes_ne {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) (hwhat : fileLineWhat I ≠ fileLineBytes) :
    fileLineWhatWord I ≠ fileLineWord := by
  intro hword
  exact hwhat (fileLineWhat_eq_of_word_eq hsz68 hword)

theorem fileLineLocals_get_what (I : ExecutionEnv) :
    (fileLineLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileLineWhat I)) := by
  rw [fileLineLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileLineLocals_get_data (I : ExecutionEnv) :
    (fileLineLocals I).get? "data" =
      some (.int (Int.ofNat (fileLineData I).toNat)) := by
  rw [fileLineLocals, store_get_self]

theorem fileLineLocals_get_wards (I : ExecutionEnv) :
    (fileLineLocals I).get? "wards" = none := by
  rw [fileLineLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileLineLocals_get_live (I : ExecutionEnv) :
    (fileLineLocals I).get? "live" = none := by
  rw [fileLineLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileLineLocals_get_Line (I : ExecutionEnv) :
    (fileLineLocals I).get? "Line" = none := by
  rw [fileLineLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileLineData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileLineData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileLineData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileLineData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileLineWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileLineWhat I)))
    (hwhat : fileLineWhat I = fileLineBytes) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") lineParamLit) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileLineWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileLineWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [lineParamLit, evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileLineWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileLineWhat I)))
    (hwhat : fileLineWhat I ≠ fileLineBytes) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") lineParamLit) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileLineWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileLineWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [lineParamLit, evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem assign_fileLineStorage (evm : EVM.State) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩ (fileLineData I)
    assignStorageRef? config { contract := contract, locals := fileLineLocals I } evm
      .storage LineRef (.int (Int.ofNat (fileLineData I).toNat)) =
        .ok ({ contract := contract, locals := fileLineLocals I }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "Line", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨9⟩)
      (hbase := fileLineLocals_get_Line I)
      (her := by simp [LineRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
        pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [evm'] using vatStorageLocStore_uint256 evm ⟨9⟩ (fileLineData I)

theorem vatFileLineSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ I = ⟨1⟩)
    (hwhat : fileLineWhat I = fileLineBytes) :
    let locals := fileLineLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨9⟩ (fileLineData I)
    ExecTransitionBody config contract evm0 locals fileLineTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileLineLocals I).get? "wards" = none; exact fileLineLocals_get_wards I)
    hauth
  have hguardLive := vatLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileLineLocals I).get? "live" = none; exact fileLineLocals_get_live I)
    hlive
  have hcond := evalExpr_fileLineWhatEq_true (evm := evm0) (I := I) (locals := locals)
    (by change (fileLineLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileLineWhat I)); exact fileLineLocals_get_what I)
    hwhat
  have hdata := evalExpr_fileLineData (evm := evm0) (I := I) (locals := locals)
    (by change (fileLineLocals I).get? "data" =
      some (.int (Int.ofNat (fileLineData I).toNat)); exact fileLineLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage LineRef (.int (Int.ofNat (fileLineData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileLineStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage LineRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileLineTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, fileLineTransition, nonpayable, auth, requireLive, locals,
    evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem vatFileLineSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    let locals := fileLineLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileLineTransition.body .reverted := by
  intro locals evm0
  have hguard := vatAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileLineLocals I).get? "wards" = none; exact fileLineLocals_get_wards I)
    hauth
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileLineTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [
        .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .ite (.binary .eq (.var "what") lineParamLit)
          [.assign .storage LineRef (.var "data")] [.require (.boolLit false)]])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem vatFileLineSourceBodyNotLive {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ I ≠ ⟨1⟩) :
    let locals := fileLineLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileLineTransition.body .reverted := by
  intro locals evm0
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileLineLocals I).get? "wards" = none; exact fileLineLocals_get_wards I)
    hauth
  have hguardLive := vatLiveGuardEval_false (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileLineLocals I).get? "live" = none; exact fileLineLocals_get_live I)
    hlive
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileLineTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
  simpa [ExecTransitionBody, fileLineTransition, nonpayable, auth, requireLive, evm0,
    locals] using ExecFuncBody.execBlockRevert hblock

theorem vatFileLineSourceBodyUnrecognized {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ I = ⟨1⟩)
    (hwhat : fileLineWhat I ≠ fileLineBytes) :
    let locals := fileLineLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileLineTransition.body .reverted := by
  intro locals evm0
  have hguardAuth := vatAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileLineLocals I).get? "wards" = none; exact fileLineLocals_get_wards I)
    hauth
  have hguardLive := vatLiveGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := Sat256.ofUInt256 g) (locals := locals)
    (by change (fileLineLocals I).get? "live" = none; exact fileLineLocals_get_live I)
    hlive
  have hcond := evalExpr_fileLineWhatEq_false (evm := evm0) (I := I) (locals := locals)
    (by change (fileLineLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileLineWhat I)); exact fileLineLocals_get_what I)
    hwhat
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileLineTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, fileLineTransition, nonpayable, auth, requireLive, evm0,
    locals] using ExecFuncBody.execBlockRevert hblock

theorem decodeABIValues_bytes32_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [bytes32, uint256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes bytes32Width (bytes.take 32),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, bytes32, uint256, bytes32Width, uint256Int, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32]
  rw [Int.emod_eq_of_lt]
  · simp [UInt256.toNat]
  · exact Int.natCast_nonneg _
  · exact_mod_cast (ABI.bytesToWord ((bytes.drop 32).take 32)).val.isLt

theorem decodeABIValues_bytes32_uint256_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [bytes32, uint256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, bytes32, uint256, bytes32Width, uint256Int, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have htake0n : ¬ (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
      rw [List.length_take, List.length_drop]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    have hnot : ¬ 32 ≤ bytes.length - 32 := by
      rw [List.length_take, List.length_drop] at htake32n
      omega
    simp [readWord?, readBytes?, hnot]

theorem decodeCalldata_legacyBytes32_uint256_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [bytes32, uint256] cd =
      some (((∅ : Store).insert x
        (.fixedBytes bytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword36 : ABI.bytesToWord ((cd.toList.drop 36).take 32) = calldataWord cd 36 :=
    decode_word_at_eq cd 36 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [bytes32, uint256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, uint256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem decodeCalldata_legacyBytes32_uint256_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [bytes32, uint256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [bytes32, uint256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [bytes32, uint256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_uint256_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

theorem vatDecode_fileLine_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileLineTransition.params.map Param.name)
      (transitionSignature fileLineTransition).paramTypes I.calldata =
        some (fileLineLocals I) := by
  simpa [config, fileLineTransition, fileLineLocals, fileLineWhat, fileLineData, bytes32,
    uint256, bytes32Width, uint256Int] using
    (decodeCalldata_legacyBytes32_uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem vatDecode_fileLine_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileLineTransition.params.map Param.name)
      (transitionSignature fileLineTransition).paramTypes I.calldata = none := by
  simpa [config, fileLineTransition, bytes32, uint256, bytes32Width, uint256Int] using
    (decodeCalldata_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem vatDispatchFileLine {I : ExecutionEnv}
    (hsel : selIs I (vatSelBytes 7)) :
    dispatchMsg contract I.calldata = some fileLineTransition := by
  have hcd : I.calldata.extract 0 4 = vatSelBytes 7 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileLineTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, LineSelectorBytes, cageSelectorBytes,
    canSelectorBytes, daiSelectorBytes, debtSelectorBytes, denySelectorBytes,
    fileIlkSelectorBytes, fileLineSelectorBytes]
  native_decide

theorem vatReachFileLineBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vatBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (vatSelBytes 7)) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨639⟩ [vatSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vatSelWord I = ⟨0x29ae8114⟩ :=
    vatSelWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨0x29ae8114⟩
      (by native_decide) (by simpa [vatSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat vatBytecode vatRootSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vatBytecode vatLowSplitPc) (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlowlow :
      UInt256.gt (armSelNat vatBytecode vatLowLowSplitPc) (vatSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc j))
        (vatSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq (armSelNat vatBytecode (nthArmPc vatBytecode vatArms370FirstPc 1))
        (vatSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vatReachArms370Body 1 (by omega) ⟨639⟩ hcode hwv hsz hsize
    hroot hlow hlowlow heq0 htake (by jump_dest) (by native_decide)

@[reducible] def solcTwoWordExternalLoadAndJumpWf
    (code : ByteArray) (pc routine : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p3 := p2 + ⟨1⟩
  let p4 := p3 + ⟨1⟩
  let p5 := p4 + ⟨1⟩
  let p7 := p5 + UInt256.ofNat 2
  let p8 := p7 + ⟨1⟩
  let p9 := p8 + ⟨1⟩
  let p12 := p9 + UInt256.ofNat 3
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.POP, .none)
  ∧ decode code p2 = some (.DUP1, .none)
  ∧ decode code p3 = some (.CALLDATALOAD, .none)
  ∧ decode code p4 = some (.SWAP1, .none)
  ∧ decode code p5 = some (.Push .PUSH1, some (⟨32⟩, 1))
  ∧ decode code p7 = some (.ADD, .none)
  ∧ decode code p8 = some (.CALLDATALOAD, .none)
  ∧ decode code p9 = some (.Push .PUSH2, some (routine, 2))
  ∧ decode code p12 = some (.JUMP, .none)

theorem RD.solcTwoWordExternalLoadAndJump {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {decoded ret routine de : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 decoded (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hwf : solcTwoWordExternalLoadAndJumpWf code decoded routine)
    (hroutine : (D_J code 0).contains routine = true)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD code ee g s0 routine
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: R)
      mem aw rdata acc k' C' := by
  rcases hwf with ⟨hd0, hd1, hd2, hd3, hd4, hd5, hd7, hd8, hd9, hd12⟩
  have rd1 := h.jumpdest hd0 (by evm_ov)
  have rd2 := rd1.pop hd1 (by evm_ov)
  have rd3 := rd2.dup1 hd2 (by evm_ov)
  have rd4 := rd3.calldataload hd3 (by evm_ov)
  have rd5 := rd4.swap1 hd4 (by evm_ov)
  have rd7 := rd5.push1 ⟨32⟩ hd5 (by evm_ov)
  have rd8 := rd7.add hd7 (by evm_ov)
  have rd9 := rd8.calldataload hd8 (by evm_ov)
  have rd12 := rd9.push2 routine hd9 (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd12.jump hd12 hroutine (by evm_ov)⟩

theorem vatFileLineX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨639⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD vatBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2052⟩
        [fileLineData I, fileLineWhatWord I, ⟨524⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := vatBytecode) (sel := sel) (entry := ⟨639⟩) (ret := ⟨524⟩)
    (decoded := ⟨661⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.solcTwoWordExternalLoadAndJump
    (code := vatBytecode) (decoded := ⟨661⟩) (ret := ⟨524⟩) (routine := ⟨2052⟩)
    (R := [sel]) hdecoded
    (by
      unfold solcTwoWordExternalLoadAndJumpWf
      repeat' first | apply And.intro | native_decide)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileLineData, fileLineWhatWord] using hroutine⟩

@[reducible] def vatFileLineStoreWf (code : ByteArray) (pc badPc : UInt256) : Prop :=
  let p1 := pc + ⟨1⟩
  let p2 := p1 + ⟨1⟩
  let p6 := p2 + UInt256.ofNat 5
  let p8 := p6 + UInt256.ofNat 2
  let p9 := p8 + ⟨1⟩
  let p10 := p9 + ⟨1⟩
  let p11 := p10 + ⟨1⟩
  let p14 := p11 + UInt256.ofNat 3
  let p15 := p14 + ⟨1⟩
  let p17 := p15 + UInt256.ofNat 2
  let p18 := p17 + ⟨1⟩
  let p19 := p18 + ⟨1⟩
  decode code pc = some (.JUMPDEST, .none)
  ∧ decode code p1 = some (.DUP2, .none)
  ∧ decode code p2 = some (.Push .PUSH4, some (⟨0x4c696e65⟩, 4))
  ∧ decode code p6 = some (.Push .PUSH1, some (⟨224⟩, 1))
  ∧ decode code p8 = some (.SHL, .none)
  ∧ decode code p9 = some (.EQ, .none)
  ∧ decode code p10 = some (.ISZERO, .none)
  ∧ decode code p11 = some (.Push .PUSH2, some (badPc, 2))
  ∧ decode code p14 = some (.JUMPI, .none)
  ∧ decode code p15 = some (.Push .PUSH1, some (⟨9⟩, 1))
  ∧ decode code p17 = some (.SSTORE, .none)
  ∧ decode code p18 = some (.POP, .none)
  ∧ decode code p19 = some (.JUMP, .none)

theorem RD.vatFileLineStoreOk {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc badPc data what ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (data :: what :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (hwf : vatFileLineStoreWf code pc badPc)
    (hwhat : what = fileLineWord)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret R mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨9⟩ data) k' C' := by
  rcases hwf with
    ⟨hd0, hd1, hd2, hd6, hd8, hd9, hd10, hd11, hd14, hd15, hd17, hd18, hd19⟩
  have rd2 := h.jumpdest hd0 (by evm_ov) |>.dup2 hd1 (by evm_ov)
  have rd6 := rd2.push4 ⟨0x4c696e65⟩ hd2 (by evm_ov)
  have rd8 := rd6.push1 ⟨224⟩ hd6 (by evm_ov)
  have rd9₀ := rd8.shl hd8 (by evm_ov)
  have hline : UInt256.shiftLeft (⟨0x4c696e65⟩ : UInt256) ⟨224⟩ = fileLineWord := by
    rfl
  have rd9 := rd9₀
  rw [hline] at rd9
  have rd10₀ := rd9.eq hd9 (by evm_ov)
  have rd10 := rd10₀
  rw [hwhat, uInt256_eq_self] at rd10
  have rd11₀ := rd10.iszero hd10 (by evm_ov)
  have rd11 := rd11₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd11
  have rd13 := rd11.push2 badPc hd11 (by evm_ov)
  have rd14 := rd13.jumpiNT hd14 (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd16 := rd14.push1 ⟨9⟩ hd15 (by evm_ov)
  obtain ⟨_, _, rd17⟩ := rd16.sstore hperm hd17 (by evm_ov)
  have rd18 := rd17.pop hd18 (by evm_ov)
  exact ⟨_, _, rd18.jump hd19 hret (by evm_ov)⟩

abbrev vatFileUnrecognizedRawWord : UInt256 :=
  ⟨0x5661742f66696c652d756e7265636f676e697a65642d706172616d0000000000⟩

theorem RD.vatFileUnrecognizedRevert {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {data what ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vatBytecode ee g s0 ⟨1905⟩ (data :: what :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDrev vatBytecode g s0 := by
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
    raw push1 ⟨27⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨27⟩ mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst vatFileUnrecognizedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ vatFileUnrecognizedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ vatFileUnrecognizedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem RD.vatFileLineStoreBad {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {pc data what ret : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD code ee g s0 pc (data :: what :: ret :: R) mem (UInt256.ofNat 3) rdata
      (cA, σ) k C)
    (hwf : vatFileLineStoreWf code pc ⟨1905⟩)
    (hwhat : what ≠ fileLineWord)
    (hcode : code = vatBytecode)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 8 ≤ 1024) :
    RDrev code g s0 := by
  subst code
  rcases hwf with
    ⟨hd0, hd1, hd2, hd6, hd8, hd9, hd10, hd11, hd14, _hd15, _hd17, _hd18, _hd19⟩
  have rd2 := h.jumpdest hd0 (by evm_ov) |>.dup2 hd1 (by evm_ov)
  have rd6 := rd2.push4 ⟨0x4c696e65⟩ hd2 (by evm_ov)
  have rd8 := rd6.push1 ⟨224⟩ hd6 (by evm_ov)
  have rd9₀ := rd8.shl hd8 (by evm_ov)
  have hline : UInt256.shiftLeft (⟨0x4c696e65⟩ : UInt256) ⟨224⟩ = fileLineWord := by
    rfl
  have rd9 := rd9₀
  rw [hline] at rd9
  have rd10₀ := rd9.eq hd9 (by evm_ov)
  have heq0 : UInt256.eq fileLineWord what = ⟨0⟩ :=
    u256_eq_of_ne (fun hbad => hwhat hbad.symm)
  have rd10 := rd10₀
  rw [heq0] at rd10
  have rd11₀ := rd10.iszero hd10 (by evm_ov)
  have rd11 := rd11₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd11
  have rd13 := rd11.push2 ⟨1905⟩ hd11 (by evm_ov)
  have rdBad := rd13.jumpiT hd14 one_ne_zero_uint (by
    jump_dest) (by evm_ov)
  exact RD.vatFileUnrecognizedRevert
    (data := data) (what := what) (ret := ret) (R := R)
    rdBad hmem hread64 hov

theorem vatFileLineX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD vatBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨639⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev vatBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := vatBytecode) (sel := sel) (entry := ⟨639⟩) (ret := ⟨524⟩)
    (decoded := ⟨661⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem vatFileLineBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hwhat : fileLineWhat I = fileLineBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileLineTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileLineTransition.params.map Param.name)
        (transitionSignature fileLineTransition).paramTypes I.calldata =
          some (fileLineLocals I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨639⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileLineLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨9⟩ (fileLineData I)
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauth
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
    rw [← hliveWord]
    exact hlive
  have hbody :
      ExecTransitionBody config contract evm0 locals fileLineTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals] using
      (vatFileLineSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := vatFileLineX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
    (code := vatBytecode) (pc := ⟨2052⟩) (okPc := ⟨2134⟩)
    (key := fileLineData I) (ret := fileLineWhatWord I) (R := [⟨524⟩, sel])
    hdecoded
    (by
      unfold vatAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by jump_dest) (by simp)
  have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ = ⟨1⟩ := by
    simpa [vatSlotWord] using hlive
  obtain ⟨_, _, hstorePc⟩ := RD.vatLiveGuardOk
    (code := vatBytecode) (pc := ⟨2134⟩) (okPc := ⟨2204⟩)
    (key := fileLineData I) (ret := fileLineWhatWord I) (R := [⟨524⟩, sel])
    hafterAuth
    (by
      unfold vatLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    hliveSolc (by jump_dest) (by simp)
  have hwhatWord : fileLineWhatWord I = fileLineWord :=
    fileLineWhatWord_eq_of_bytes_eq hsz68 hwhat
  have hmemAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  obtain ⟨_, _, hretPc⟩ := RD.vatFileLineStoreOk
    (code := vatBytecode) (pc := ⟨2204⟩) (badPc := ⟨1905⟩)
    (data := fileLineData I) (what := fileLineWhatWord I) (ret := ⟨524⟩) (R := [sel])
    hstorePc
    (by
      unfold vatFileLineStoreWf
      repeat' first | apply And.intro | native_decide)
    hwhatWord (by jump_dest) hperm (by simp)
  have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
  have hret :
      RDret vatBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨9⟩ (fileLineData I)) ByteArray.empty := by
    simpa using RD.stop hretPc' (by native_decide) (by simp)
  have haccounts :
      accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨9⟩ (fileLineData I))
        evm1.accountMap := by
    simpa [evm1, evm0, initState, storageStore_accountMap] using
      accountMapEquiv_sstoreAccountMap I.codeOwner ⟨9⟩ (fileLineData I) hAccounts
  have henc : returnEquiv ByteArray.empty none fileLineTransition.returnType := by
    rw [show fileLineTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    haccounts henc

theorem vatFileLineBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileLineTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileLineTransition.params.map Param.name)
        (transitionSignature fileLineTransition).paramTypes I.calldata =
          some (fileLineLocals I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨639⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileLineLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I ≠ ⟨1⟩ := by
    intro hbad
    exact hauth (by rw [hcallerWord, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileLineTransition.body .reverted := by
    simpa [evm0, locals] using
      (vatFileLineSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := vatFileLineX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) ≠ ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  have hrev := RD.vatAuthCheckRevert
    (pc := ⟨2052⟩) (okPc := ⟨2134⟩)
    (key := fileLineData I) (ret := fileLineWhatWord I) (R := [⟨524⟩, sel])
    hdecoded
    (by
      unfold vatAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold vatAuthRevertTailWf vatAuthTailPc
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by simp)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vatFileLineBodyCoreNotLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileLineTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileLineTransition.params.map Param.name)
        (transitionSignature fileLineTransition).paramTypes I.calldata =
          some (fileLineLocals I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨639⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileLineLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauth
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I ≠ ⟨1⟩ := by
    intro hbad
    exact hlive (by rw [hliveWord, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileLineTransition.body .reverted := by
    simpa [evm0, locals] using
      (vatFileLineSourceBodyNotLive (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm
        hliveSolm)
  obtain ⟨_, _, hdecoded⟩ := vatFileLineX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
    (code := vatBytecode) (pc := ⟨2052⟩) (okPc := ⟨2134⟩)
    (key := fileLineData I) (ret := fileLineWhatWord I) (R := [⟨524⟩, sel])
    hdecoded
    (by
      unfold vatAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by jump_dest) (by simp)
  have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ ≠ ⟨1⟩ := by
    simpa [vatSlotWord] using hlive
  have hmemAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hreadAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  have hrev := RD.vatLiveGuardRevert
    (code := vatBytecode) (pc := ⟨2134⟩) (okPc := ⟨2204⟩)
    (key := fileLineData I) (ret := fileLineWhatWord I) (R := [⟨524⟩, sel])
    hafterAuth
    (by
      unfold vatLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf vatLiveGuardTailPc vatNotLiveRawWord
      repeat' first | apply And.intro | native_decide)
    hliveSolc hmemAuth hreadAuth (by simp)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vatFileLineBodyCoreUnrecognized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩)
    (hwhat : fileLineWhat I ≠ fileLineBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileLineTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileLineTransition.params.map Param.name)
        (transitionSignature fileLineTransition).paramTypes I.calldata =
          some (fileLineLocals I))
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨639⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileLineLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hcallerWord : vatSlotWord (vatCallerWardsSlot I) σ_evm I =
      vatSlotWord (vatCallerWardsSlot I) σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner (vatCallerWardsSlot I) ⟨0⟩
  have hauthSolm : vatSlotWord (vatCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauth
  have hliveWord : vatSlotWord ⟨10⟩ σ_evm I = vatSlotWord ⟨10⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨10⟩ ⟨0⟩
  have hliveSolm : vatSlotWord ⟨10⟩ σ_solm I = ⟨1⟩ := by
    rw [← hliveWord]
    exact hlive
  have hbody :
      ExecTransitionBody config contract evm0 locals fileLineTransition.body .reverted := by
    simpa [evm0, locals] using
      (vatFileLineSourceBodyUnrecognized (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm
        hliveSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := vatFileLineX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (hopeSourceWord I)) = ⟨1⟩ := by
    simpa [vatCallerWardsSlot, vatSlotWord] using hauth
  obtain ⟨_, _, hafterAuth⟩ := RD.vatAuthCheckOk
    (code := vatBytecode) (pc := ⟨2052⟩) (okPc := ⟨2134⟩)
    (key := fileLineData I) (ret := fileLineWhatWord I) (R := [⟨524⟩, sel])
    hdecoded
    (by
      unfold vatAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by jump_dest) (by simp)
  have hliveSolc : solcSlotWord σ_evm I ⟨10⟩ = ⟨1⟩ := by
    simpa [vatSlotWord] using hlive
  obtain ⟨_, _, hstorePc⟩ := RD.vatLiveGuardOk
    (code := vatBytecode) (pc := ⟨2134⟩) (okPc := ⟨2204⟩)
    (key := fileLineData I) (ret := fileLineWhatWord I) (R := [⟨524⟩, sel])
    hafterAuth
    (by
      unfold vatLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    hliveSolc (by jump_dest) (by simp)
  have hmemAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hreadAuth :
      (twoWordHashMem (hopeSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (hopeSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  have hwhatWord : fileLineWhatWord I ≠ fileLineWord :=
    fileLineWhatWord_ne_of_bytes_ne hsz68 hwhat
  have hrev := RD.vatFileLineStoreBad
    (code := vatBytecode) (pc := ⟨2204⟩)
    (data := fileLineData I) (what := fileLineWhatWord I) (ret := ⟨524⟩) (R := [sel])
    hstorePc
    (by
      unfold vatFileLineStoreWf
      repeat' first | apply And.intro | native_decide)
    hwhatWord rfl hmemAuth hreadAuth (by simp)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vatFileLineBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vatBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some fileLineTransition)
    (hreach : ∃ k C, RD vatBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨639⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (vatFileLineX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (vatDecode_fileLine_none_short hsz4 hshort)

theorem vatFileLineBodyCore : VatBodyTheorem 7 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (vatSelBytes 7) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileLineTransition :=
    vatDispatchFileLine hsel
  have hreach := vatReachFileLineBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hauth : vatSlotWord (vatCallerWardsSlot I) σ_evm I = ⟨1⟩
    · by_cases hlive : vatSlotWord ⟨10⟩ σ_evm I = ⟨1⟩
      · by_cases hwhat : fileLineWhat I = fileLineBytes
        · exact vatFileLineBodyCoreOk hcode hsize hperm hwv hsz68 hauth hlive hwhat
            hdispatch (vatDecode_fileLine_ok hsz68) hreach hAccounts
        · exact vatFileLineBodyCoreUnrecognized hcode hsize hwv hsz68 hauth hlive hwhat
            hdispatch (vatDecode_fileLine_ok hsz68) hreach hAccounts
      · exact vatFileLineBodyCoreNotLive hcode hsize hwv hsz68 hauth hlive hdispatch
          (vatDecode_fileLine_ok hsz68) hreach hAccounts
    · exact vatFileLineBodyCoreUnauthorized hcode hsize hwv hsz68 hauth hdispatch
        (vatDecode_fileLine_ok hsz68) hreach hAccounts
  · exact vatFileLineBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega) hdispatch hreach

end Benchmarks.Dss.Vat
