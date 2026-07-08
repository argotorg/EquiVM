import Benchmarks.Dss.End.Rely

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.End

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

attribute [local simp]
  wardsSelectorBytes vatSelectorBytes catSelectorBytes dogSelectorBytes vowSelectorBytes
  potSelectorBytes spotSelectorBytes cureSelectorBytes liveSelectorBytes whenSelectorBytes
  waitSelectorBytes debtSelectorBytes tagSelectorBytes gapSelectorBytes ArtSelectorBytes
  fixSelectorBytes bagSelectorBytes outSelectorBytes relySelectorBytes denySelectorBytes
  fileAddressSelectorBytes fileUintSelectorBytes cageSelectorBytes cageIlkSelectorBytes
  snipSelectorBytes skipSelectorBytes skimSelectorBytes freeSelectorBytes thawSelectorBytes
  flowSelectorBytes packSelectorBytes cashSelectorBytes

/-! ## `file(bytes32,uint256)` -/

abbrev fileUintWhat (I : ExecutionEnv) : List UInt8 :=
  EVM.Word.toBytesBE (calldataWord I.calldata 4)

abbrev fileUintData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileUintWaitBytes : List UInt8 :=
  [119, 97, 105, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileUintLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileUintWhat I))).insert
    "data" (.int (Int.ofNat (fileUintData I).toNat))

def fileUintLiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨8⟩ σ I

def fileUintPostState (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨10⟩ (fileUintData I)

theorem fileUintWhat_length (I : ExecutionEnv) :
    (fileUintWhat I).length = 32 := by
  simpa [fileUintWhat] using word_toBytesBE_toByteArray_size (calldataWord I.calldata 4)

theorem fileUintWaitBytes_length : fileUintWaitBytes.length = 32 := by
  native_decide

theorem fileUintWaitBytes_word :
    ABI.bytesToWord fileUintWaitBytes =
      UInt256.shiftLeft (⟨0x1dd85a5d⟩ : UInt256) ⟨226⟩ := by
  native_decide

theorem fileUintWhatWord_eq (I : ExecutionEnv) :
    ABI.bytesToWord (fileUintWhat I) = calldataWord I.calldata 4 := by
  simp [fileUintWhat, bytesToWord_toBytesBE]

theorem fileUintWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hbs : fileUintWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileUintWhatWord_eq I).symm

theorem fileUintWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hneq : fileUintWhat I ≠ bs) (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  apply hneq
  rw [fileUintWhat, hword]
  exact toBytesBE_bytesToWord_of_length hbsLen

theorem endDecode_fileUint_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata =
        some (fileUintLocals I) := by
  simpa [config, fileUintTransition, fileUintLocals, fileUintWhat, fileUintData, bytes32,
    bytes32Width, uint256, uint256Int, abiBytes32, abiBytes32Width, abiUInt256] using
    (endDecodeCalldata_legacyBytes32Uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem endDecode_fileUint_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata = none := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (endDecodeCalldata_legacyBytes32Uint256_none_short (cd := I.calldata)
      (x := "what") (y := "data") hsz4 hshort)

theorem endDispatchFileUintLocal {I : ExecutionEnv} (hsel : selIs I (endSelBytes 21)) :
    dispatchMsg contract I.calldata = some fileUintTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 21 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileUintTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, fileUintSelectorBytes]
  native_decide

theorem fileUintLocals_get_what (I : ExecutionEnv) :
    (fileUintLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileUintWhat I)) := by
  rw [fileUintLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileUintLocals_get_data (I : ExecutionEnv) :
    (fileUintLocals I).get? "data" =
      some (.int (Int.ofNat (fileUintData I).toNat)) := by
  rw [fileUintLocals, store_get_self]

theorem fileUintLocals_get_wards (I : ExecutionEnv) :
    (fileUintLocals I).get? "wards" = none := by
  rw [fileUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileUintLocals_get_live (I : ExecutionEnv) :
    (fileUintLocals I).get? "live" = none := by
  rw [fileUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileUintLocals_get_wait (I : ExecutionEnv) :
    (fileUintLocals I).get? "wait" = none := by
  rw [fileUintLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileUintData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileUintData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileUintData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileUintWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileUintWhat I)))
    (hwhat : fileUintWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileUintWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileUintWhat I)))
    (hwhat : fileUintWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalStorageRef_fileUint_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := fileUintLocals I } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_fileUint_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileUintLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileUintLocals I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileUintLocals I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simp [fileUintLocals, wardsRef])
      (her := evalStorageRef_fileUint_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using endStorageLocLoad_uint256 evm (relyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_fileUint_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileUintLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileUintLocals I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (relyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileUintLocals I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (hbase := by simp [fileUintLocals, wardsRef])
      (her := evalStorageRef_fileUint_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm (relyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (relyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalStorageRef_fileUint_live (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := fileUintLocals I } evm liveRef =
      .ok ({ base := "live", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind]

theorem evalExpr_fileUint_live_true (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileUintLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileUintLocals I } evm
        (.storage liveRef) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileUintLocals I })
      (slot := liveRef)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (value := .int 1)
      (hbase := by simp [fileUintLocals, liveRef])
      (her := evalStorageRef_fileUint_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using endStorageLocLoad_uint256 evm ⟨8⟩)]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_fileUint_live_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileUintLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileUintLocals I } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileUintLocals I })
      (slot := liveRef)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (hbase := by simp [fileUintLocals, liveRef])
      (her := evalStorageRef_fileUint_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm ⟨8⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ≠
        Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact uint256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat) ==
        Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem assign_fileUintWaitStorage (evm : EVM.State) (I : ExecutionEnv) :
    assignStorageRef? config { contract := contract, locals := fileUintLocals I } evm
      .storage waitRef (.int (Int.ofNat (fileUintData I).toNat)) =
        .ok ({ contract := contract, locals := fileUintLocals I }, fileUintPostState evm I) := by
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := ({ base := "wait", steps := [] } : EvaledStorageRef))
      (loc := wordLoc ⟨10⟩)
      (hbase := fileUintLocals_get_wait I)
      (her := by simp [waitRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
  simpa [fileUintPostState, wordLoc, uint256Loc, uint256Int] using
    storageLocStore_uint256 evm ⟨10⟩ (fileUintData I)

theorem endFileUintSourceBodyWaitOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : fileUintLiveWord σ I = ⟨1⟩)
    (hwhat : fileUintWhat I = fileUintWaitBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileUintPostState evm0 I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileUint_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, fileUintLiveWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileUint_live_true evm0 I hlive
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") waitLit) = .ok (.bool true) := by
    simpa [waitLit, fileUintWaitBytes, strLit4, locals] using
      (evalExpr_fileUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintWaitBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
    simpa [locals] using
      evalExpr_fileUintData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage waitRef (.int (Int.ofNat (fileUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_fileUintWaitStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage waitRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileUintTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem endFileUintSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileUint_auth_false evm0 I (by simp [evm0, initState]) hauth
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileUintTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := ([
        Stmt.require (.binary .eq (.storage liveRef) (.intLit 1)),
        Stmt.ite (.binary .eq (.var "what") waitLit)
          [Stmt.assign .storage waitRef (.var "data")]
          [Stmt.require (.boolLit false)]
      ] : List Stmt))
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem endFileUintSourceBodyNotLiveReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : fileUintLiveWord σ I ≠ ⟨1⟩) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileUint_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0, fileUintLiveWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileUint_live_false evm0 I hlive
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hliveGuard)

theorem endFileUintSourceBodyUnrecognizedReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : fileUintLiveWord σ I = ⟨1⟩)
    (hnotWait : fileUintWhat I ≠ fileUintWaitBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileUint_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, fileUintLiveWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileUint_live_true evm0 I hlive
  have hwait :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") waitLit) = .ok (.bool false) := by
    simpa [waitLit, fileUintWaitBytes, strLit4, locals] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintWaitBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotWait)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hunrec :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  refine ExecFuncBody.execBlockRevert ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
  exact ExecBlock.consRevert (ExecStmt.iteFalse hwait hunrec)

/-! ## EVM/refinement assembly -/

noncomputable def fileUintLogDataMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (fileUintData I)).write 0 (relyAuthHashMem I) 128 32

theorem fileUintLogDataMem_size (I : ExecutionEnv) :
    (fileUintLogDataMem I).size = 160 := by
  unfold fileUintLogDataMem
  exact toByteArray_write32_size_of_ge (relyAuthHashMem I) (fileUintData I) 128 96 160
    (relyAuthHashMem_size I) (by omega)
    (by simpa using lt_usize 32 (by norm_num))
    (by omega)

theorem fileUintLogDataMem_read64 (I : ExecutionEnv) :
    (fileUintLogDataMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold fileUintLogDataMem
  rw [toByteArray_write_read_below_of_gap (fileUintData I) (relyAuthHashMem I) 128 64
    (by rw [relyAuthHashMem_size I]) (by omega)
    (by rw [relyAuthHashMem_size I]; exact lt_usize _ (by norm_num))]
  exact relyAuthHashMem_read64 I

theorem fileUintNotLiveWord :
    UInt256.shiftLeft (⟨0x456e642f6e6f742d6c697665⟩ : UInt256) ⟨160⟩ =
      ⟨0x456e642f6e6f742d6c6976650000000000000000000000000000000000000000⟩ := by
  native_decide

abbrev fileUintUnrecognizedRawWord : UInt256 :=
  ⟨0x456e642f66696c652d756e7265636f676e697a65642d706172616d0000000000⟩

theorem endReachFileUintBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 21)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨527⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0x29ae8114⟩ :=
    endSelWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨0x29ae8114⟩
      (by native_decide) (by simpa [endSelBytes] using hsel)
  obtain ⟨_, _, h32⟩ :=
    endReachRootSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have hroot : UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h271 := RD.selectorSplitTakenAuto h32
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    hroot (by jump_dest) (by simp)
  have h272 := h271.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h272gt : UInt256.gt (armSelNat endBytecode (⟨272⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h391 := RD.selectorSplitTakenAuto h272
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h272gt (by jump_dest) (by simp)
  have h392 := h391.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have h392gt : UInt256.gt (armSelNat endBytecode (⟨392⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h451 := RD.selectorSplitTakenAuto h392
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h392gt (by jump_dest) (by simp)
  have h452 := h451.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have hdebt0 : UInt256.eq (armSelNat endBytecode (⟨452⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]; native_decide
  have hfileUint :
      UInt256.eq (armSelNat endBytecode (⟨463⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]; native_decide
  have h527 := h452
    |>.selectorArmNotTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hdebt0 (by simp)
    |>.selectorArmTakenAuto
      (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
      hfileUint (by jump_dest) (by simp)
  exact ⟨_, _, h527⟩

theorem RD.endFileUintDecodeToRoutine {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel de : UInt256}
    (h : RD endBytecode I g s0 ⟨549⟩
      (de :: ⟨4⟩ :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨1315⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1315 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw calldataload (by native_decide) (by evm_ov),
    raw push2 ⟨1315⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact ⟨_, _, by simpa [fileUintData, calldataWord] using rd1315⟩

theorem endFileUintX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨527⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1315⟩
        [fileUintData I, calldataWord I.calldata 4, ⟨562⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := ⟨527⟩) (ret := ⟨562⟩)
    (decoded := ⟨549⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  exact RD.endFileUintDecodeToRoutine hdecoded

theorem endFileUintX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨527⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := endBytecode) (sel := sel)
    (entry := ⟨527⟩) (ret := ⟨562⟩) (decoded := ⟨549⟩)
    (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem endFileUintX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD endBytecode I g s0 ⟨1315⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨1404⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1321pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1322 := rd1321pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1326pre := evm_run rd1322 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1327 := rd1326pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1330pre := evm_run rd1327 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1331 := rd1330pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1332, C1332, rd1332raw⟩ := rd1331.sload (by native_decide) (by evm_ov)
  have rd1332 : RD endBytecode I g s0 ⟨1332⟩
      (relyAuthWord σ I :: fileUintData I :: calldataWord I.calldata 4 :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1332 C1332 := by
    simpa [relyAuthWord, endSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1332raw
  have rd1335pre := evm_run rd1332 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1335pre
  have rd1338 := rd1335pre.pushConst (⟨1404⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1338.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem endFileUintX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD endBytecode I g s0 ⟨1315⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1321pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1322 := rd1321pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1326pre := evm_run rd1322 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1327 := rd1326pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1330pre := evm_run rd1327 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1331 := rd1330pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1332, C1332, rd1332raw⟩ := rd1331.sload (by native_decide) (by evm_ov)
  have rd1332 : RD endBytecode I g s0 ⟨1332⟩
      (relyAuthWord σ I :: fileUintData I :: calldataWord I.calldata 4 :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1332 C1332 := by
    simpa [relyAuthWord, endSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1332raw
  have rd1335pre := evm_run rd1332 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1335pre
  have rd1338 := rd1335pre.pushConst (⟨1404⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1339 := rd1338.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1339⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x115b990bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x456e642f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd1339
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem endFileUintX_live {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : fileUintLiveWord σ I = ⟨1⟩)
    (h : RD endBytecode I g s0 ⟨1404⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨1474⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1408pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k1408, C1408, rd1408raw⟩ := rd1408pre.sload (by native_decide) (by evm_ov)
  have rd1408 : RD endBytecode I g s0 ⟨1408⟩
      (fileUintLiveWord σ I :: fileUintData I :: calldataWord I.calldata 4 :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1408 C1408 := by
    simpa [fileUintLiveWord, endSlotWord] using rd1408raw
  have rd1411pre := evm_run rd1408 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hlive, u256_eq_refl] at rd1411pre
  have rd1414 := rd1411pre.pushConst (⟨1474⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1414.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem endFileUintX_notLive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : fileUintLiveWord σ I ≠ ⟨1⟩)
    (h : RD endBytecode I g s0 ⟨1404⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd1408pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k1408, C1408, rd1408raw⟩ := rd1408pre.sload (by native_decide) (by evm_ov)
  have rd1408 : RD endBytecode I g s0 ⟨1408⟩
      (fileUintLiveWord σ I :: fileUintData I :: calldataWord I.calldata 4 :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1408 C1408 := by
    simpa [fileUintLiveWord, endSlotWord] using rd1408raw
  have rd1411pre := evm_run rd1408 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (fileUintLiveWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hlive hbad.symm)
  rw [heq] at rd1411pre
  have rd1414 := rd1411pre.pushConst (⟨1474⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1415 := rd1414.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1415⟩)
    (len := ⟨12⟩)
    (rawWord := ⟨0x456e642f6e6f742d6c697665⟩)
    (shift := ⟨160⟩)
    (word := ⟨0x456e642f6e6f742d6c6976650000000000000000000000000000000000000000⟩)
    (op := .PUSH12)
    (width := 12)
    rd1415
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    fileUintNotLiveWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFileUintX_logReturn {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {what sel : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (h : RD endBytecode I g s0 ⟨1576⟩
      [fileUintData I, what, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDret endBytecode g s0 acc ByteArray.empty := by
  have rd1583pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [relyAuthHashMem_size I]; decide) (by decide)
        (relyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1584 := rd1583pre.mstore 6 (fileUintLogDataMem I)
    (UInt256.ofNat 5) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd1588pre := evm_run rd1584 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [fileUintLogDataMem_size I]; decide) (by decide)
        (fileUintLogDataMem_read64 I))
      (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd1621 := rd1588pre.pushConst
    (⟨0xe986e40cc8c151830d4f61050f4fb2e4add8567caad2d5f5496f9158e91fe4c7⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd1629pre := evm_run rd1621 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1631 := RD.log2
    (a := ⟨128⟩) (b := ⟨32⟩)
    (c := ⟨0xe986e40cc8c151830d4f61050f4fb2e4add8567caad2d5f5496f9158e91fe4c7⟩)
    (d := what)
    (t := [fileUintData I, what, ⟨562⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 5).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    rd1629pre (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1631 := RD.pop (a := fileUintData I) (t := [what, ⟨562⟩, sel])
    rd1631 (by native_decide) (by evm_ov)
  have rd1632 := RD.pop (a := what) (t := [⟨562⟩, sel])
    rd1631 (by native_decide) (by evm_ov)
  have rd562 := RD.jump (a := ⟨562⟩) (t := [sel]) rd1632
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := ⟨562⟩) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

theorem RD.endFileUintUnrecognizedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨1499⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev endBytecode g s0 := by
  have rd1503pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd1507 := rd1503pre.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rd1507 with [
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
  have rd1560 := rdPrefix.pushConst fileUintUnrecognizedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rd1560 with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ fileUintUnrecognizedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ fileUintUnrecognizedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

set_option maxHeartbeats 3000000 in
theorem endFileUintX_wait_ok {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hwhatWord : calldataWord I.calldata 4 = ABI.bytesToWord fileUintWaitBytes)
    (h : RD endBytecode I g s0 ⟨1474⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨10⟩ (fileUintData I)) ByteArray.empty := by
  have rd1476pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1481 := rd1476pre.pushConst (⟨0x1dd85a5d⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd1486pre := evm_run rd1481 with [
    raw push1 ⟨226⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  rw [hwhatWord, fileUintWaitBytes_word, u256_eq_refl] at rd1486pre
  have rd1490pre := evm_run rd1486pre with [
    raw push2 ⟨1499⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  have rd1494pre := evm_run rd1490pre with [
    raw push1 ⟨10⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  obtain ⟨k1495, C1495, rd1495raw⟩ := rd1494pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1495 : RD endBytecode I g s0 ⟨1495⟩
      [fileUintData I, UInt256.shiftLeft (⟨0x1dd85a5d⟩ : UInt256) ⟨226⟩, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨10⟩ (fileUintData I)) k1495 C1495 := by
    simpa using rd1495raw
  have rd1576 := evm_run rd1495 with [
    raw push2 ⟨1576⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact endFileUintX_logReturn hperm rd1576

set_option maxHeartbeats 3000000 in
theorem endFileUintX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hnotWaitWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintWaitBytes)
    (h : RD endBytecode I g s0 ⟨1474⟩
      [fileUintData I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd1476pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1481 := rd1476pre.pushConst (⟨0x1dd85a5d⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide) (by evm_ov)
  have rd1485pre := evm_run rd1481 with [
    raw push1 ⟨226⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have hwaitEq :
      UInt256.eq
          (UInt256.shiftLeft (⟨0x1dd85a5d⟩ : UInt256) ⟨226⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← fileUintWaitBytes_word]
    exact u256_eq_of_ne (by intro hbad; exact hnotWaitWord hbad.symm)
  rw [hwaitEq] at rd1485pre
  have rd1499 := evm_run rd1485pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨1499⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact RD.endFileUintUnrecognizedRevert rd1499
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem endFileUintBodyCore : endBodyObligation 21 := by
  intro cA gh bl σ_evm σ_solm σ₀ A I g hcode hsize hperm hwv hsel hAccounts
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (endSelBytes 21) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileUintTransition :=
    endDispatchFileUintLocal hsel
  have hreach := endReachFileUintBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := endDecode_fileUint_ok (I := I) hsz68
    obtain ⟨_, _, rd1315⟩ :=
      endFileUintX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hauthCouple : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    have hliveCouple : fileUintLiveWord σ_evm I = fileUintLiveWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · have hauthSolm : relyAuthWord σ_solm I = ⟨1⟩ := by
        rw [← hauthCouple]
        exact hauth
      obtain ⟨_, _, rd1404⟩ := endFileUintX_authorized (I := I) hauth rd1315
      by_cases hlive : fileUintLiveWord σ_evm I = ⟨1⟩
      · have hliveSolm : fileUintLiveWord σ_solm I = ⟨1⟩ := by
          rw [← hliveCouple]
          exact hlive
        obtain ⟨_, _, rd1474⟩ := endFileUintX_live (I := I) hlive rd1404
        by_cases hwait : fileUintWhat I = fileUintWaitBytes
        · have hwaitWord : calldataWord I.calldata 4 = ABI.bytesToWord fileUintWaitBytes :=
            fileUintWhatWord_eq_of_bytes_eq hwait
          have hbody :
              ExecTransitionBody config contract evmSolm (fileUintLocals I)
                fileUintTransition.body
                (.returned { contract := contract, locals := fileUintLocals I }
                  (fileUintPostState evmSolm I) none) := by
            simpa [evmSolm] using
              endFileUintSourceBodyWaitOk (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hliveSolm hwait
          exact (endFileUintX_wait_ok hperm hwaitWord rd1474)
            |>.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
              (by simp [fileUintPostState, evmSolm, initState, storageStore_createdAccounts])
              (by
                simpa [fileUintPostState, evmSolm, initState, storageStore_accountMap] using
                  accountMapEquiv_sstoreAccountMap I.codeOwner ⟨10⟩ (fileUintData I)
                    hAccounts)
              (by
                simpa [fileUintTransition] using
                  (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
                    (dvs := []) rfl (by native_decide) (by native_decide)))
        · have hnotWaitWord :
              calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintWaitBytes :=
            fileUintWhatWord_ne_of_bytes_ne hwait fileUintWaitBytes_length
          have hbody :
              ExecTransitionBody config contract evmSolm (fileUintLocals I)
                fileUintTransition.body .reverted := by
            simpa [evmSolm] using
              endFileUintSourceBodyUnrecognizedReverts
                (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
                (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm hwait
          exact (endFileUintX_unrecognized hnotWaitWord rd1474)
            |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hliveSolm : fileUintLiveWord σ_solm I ≠ ⟨1⟩ := by
          intro hbad
          exact hlive (by rw [hliveCouple, hbad])
        have hbody :
            ExecTransitionBody config contract evmSolm (fileUintLocals I)
              fileUintTransition.body .reverted := by
          simpa [evmSolm] using
            endFileUintSourceBodyNotLiveReverts
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm
        exact (endFileUintX_notLive (I := I) hlive rd1404)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
        intro hbad
        exact hauth (by rw [hauthCouple, hbad])
      have hbody :
          ExecTransitionBody config contract evmSolm (fileUintLocals I)
            fileUintTransition.body .reverted := by
        simpa [evmSolm] using
          endFileUintSourceBodyAuthReverts
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hauthSolm
      exact (endFileUintX_unauthorized (I := I) hauth rd1315)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact (endFileUintX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize (by omega) hreach)
      |>.reEquivDecodingFailed hcode hdispatch
        (endDecode_fileUint_none_short hsz4 (by omega))

end Benchmarks.Dss.End
