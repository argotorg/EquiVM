import Benchmarks.Dss.DaiJoin.Exit

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.DaiJoin

theorem daiJoinExitNotLiveReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hnotLive : exitLiveWord evm.accountMap evm.executionEnv ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  have hlive :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage liveRef) =
        .ok (.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat)) :=
    evalExpr_daiJoinLiveStorage (evm := evm) (locals := exitStore I)
      (exitStore_get_live I)
  have hguard :
      evalExpr? config { contract := contract, locals := exitStore I } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
          .ok (.bool false) :=
    evalExpr_daiJoinLiveGuard_false hlive hnotLive
  have hblock :
      ExecBlock config { contract := contract, locals := exitStore I } evm
        exitTransition.body .reverted := by
    simp only [exitTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem daiJoinExitBodyMulReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hliveOne : exitLiveWord evm.accountMap evm.executionEnv = ⟨1⟩)
    (hwad : exitWadWord I ≠ ⟨0⟩)
    (hguard :
      UInt256.div (daiJoinRadWord (exitWadWord I)) (exitWadWord I) ≠ daiJoinONEWord) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  have hlive :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage liveRef) =
        .ok (.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat)) :=
    evalExpr_daiJoinLiveStorage (evm := evm) (locals := exitStore I)
      (exitStore_get_live I)
  have hliveGuard :
      evalExpr? config { contract := contract, locals := exitStore I } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
          .ok (.bool true) :=
    evalExpr_daiJoinLiveGuard_true hlive hliveOne
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    rfl
  have hbindMul :
      bindParams? mulFunction.params
          [.int (Int.ofNat daiJoinONEWord.toNat), exitWadValue I] =
        some (daiJoinUintBinaryLocals daiJoinONEWord (exitWadWord I)) := by
    simp [mulFunction, uint256, bindParams?, daiJoinUintBinaryLocals, exitWadValue]
  have hover :
      UInt256.size ≤ daiJoinONEWord.toNat * (exitWadWord I).toNat :=
    daiJoinMulOverflow_of_guard_fail (x := daiJoinONEWord) (y := exitWadWord I) hwad hguard
  have hmulStmt :
      ExecStmt config { contract := contract, locals := exitStore I } evm
        (.internalCall "mul" [.intLit ONE, .var "wad"] "rad") .reverted :=
    internalCallFunctionRevert
      (cfg := config)
      (caller := Frame.mk contract (exitStore I))
      (evm := evm) (name := "mul") (retVar := "rad")
      (args := [.intLit ONE, .var "wad"])
      (argVals := [.int (Int.ofNat daiJoinONEWord.toNat), exitWadValue I])
      (callee := mulFunction)
      (locals := daiJoinUintBinaryLocals daiJoinONEWord (exitWadWord I))
      (evalExprs_daiJoinExitMulArgs evm I) hlookupMul hbindMul
      (execDaiJoinMulFunctionRevert evm (x := daiJoinONEWord) (y := exitWadWord I) hover)
  have hblock :
      ExecBlock config { contract := contract, locals := exitStore I } evm
        exitTransition.body .reverted := by
    simp only [exitTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consRevert hmulStmt
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem daiJoinExitVatNoCodeReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hliveOne : exitLiveWord evm.accountMap evm.executionEnv = ⟨1⟩)
    (hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  have hlive :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage liveRef) =
        .ok (.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat)) :=
    evalExpr_daiJoinLiveStorage (evm := evm) (locals := exitStore I)
      (exitStore_get_live I)
  have hliveGuard :
      evalExpr? config { contract := contract, locals := exitStore I } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
          .ok (.bool true) :=
    evalExpr_daiJoinLiveGuard_true hlive hliveOne
  have hmulStmt :=
    daiJoinExitInternalMulReturns evm I hfit
  have hvat :
      evalExpr? config { contract := contract, locals := exitRadStore I } evm (.storage vatRef) =
        .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) :=
    evalExpr_daiJoinVatStorage (evm := evm) (locals := exitRadStore I)
      (exitRadStore_get_vat I)
  have hnoCodeNat :
      (UInt256.ofNat
        ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0 :=
    daiJoinVatCode_zero_of_codeSize_zero hnoCode
  have hguard :
      evalExpr? config { contract := contract, locals := exitRadStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_daiJoinVatCodeGuard_false hvat hnoCodeNat
  have hblock :
      ExecBlock config { contract := contract, locals := exitStore I } evm
        exitTransition.body .reverted := by
    simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem daiJoinExitVatMoveCallFailedReverts (evm evmVat : EVM.State)
    (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hliveOne : exitLiveWord evm.accountMap evm.executionEnv = ⟨1⟩)
    (hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size)
    (hcode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) "move" 0
        [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
          .int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)]
        (false, evmVat, out) true) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  have hlive :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage liveRef) =
        .ok (.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat)) :=
    evalExpr_daiJoinLiveStorage (evm := evm) (locals := exitStore I)
      (exitStore_get_live I)
  have hliveGuard :
      evalExpr? config { contract := contract, locals := exitStore I } evm
        (.binary .eq (.storage liveRef) (.intLit 1)) =
          .ok (.bool true) :=
    evalExpr_daiJoinLiveGuard_true hlive hliveOne
  have hmulStmt :=
    daiJoinExitInternalMulReturns evm I hfit
  have hvat :
      evalExpr? config { contract := contract, locals := exitRadStore I } evm (.storage vatRef) =
        .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) :=
    evalExpr_daiJoinVatStorage (evm := evm) (locals := exitRadStore I)
      (exitRadStore_get_vat I)
  have hcodeNat :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat :=
    daiJoinVatCode_pos_of_codeSize_ne_zero hcode
  have hguard :
      evalExpr? config { contract := contract, locals := exitRadStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_daiJoinVatCodeGuard_true hvat hcodeNat
  have hargs :=
    evalExprs_daiJoinExitVatMoveArgs evm I
  have hblock :
      ExecBlock config { contract := contract, locals := exitStore I } evm
        exitTransition.body .reverted := by
    simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert
      (ExecStmt.externalCallFailure (sendVal := 0) (perm := true)
        hvat (by simp [evalExpr?, pure]) hargs hcall)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem daiJoinExitDaiMintNoCodeAfterVatReverts (evm evmVat : EVM.State)
    (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hliveOne : exitLiveWord evm.accountMap evm.executionEnv = ⟨1⟩)
    (hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcallMove :
      typedCallViaEVM config evm
        (EVM.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) "move" 0
        [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
          .int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)]
        (true, evmVat, out) true)
    (hdaiNoCode :
      Reasoning.Theory.extCodeSizeWord evmVat.accountMap
        (daiJoinDaiTargetWord evmVat.accountMap evmVat.executionEnv) = ⟨0⟩) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  have hlive :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage liveRef) =
        .ok (.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat)) :=
    evalExpr_daiJoinLiveStorage (evm := evm) (locals := exitStore I)
      (exitStore_get_live I)
  have hliveGuard :=
    evalExpr_daiJoinLiveGuard_true hlive hliveOne
  have hmulStmt :=
    daiJoinExitInternalMulReturns evm I hfit
  have hvat :
      evalExpr? config { contract := contract, locals := exitRadStore I } evm (.storage vatRef) =
        .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) :=
    evalExpr_daiJoinVatStorage (evm := evm) (locals := exitRadStore I)
      (exitRadStore_get_vat I)
  have hvatCodeNat :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat :=
    daiJoinVatCode_pos_of_codeSize_ne_zero hvatCode
  have hvatGuard :=
    evalExpr_daiJoinVatCodeGuard_true hvat hvatCodeNat
  have hmoveArgs :=
    evalExprs_daiJoinExitVatMoveArgs evm I
  have hmoveDecode : config.externalABI.decode? "move" out = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hdai :
      evalExpr? config { contract := contract, locals := exitAfterMoveStore I } evmVat
        (.storage daiRef) =
        .ok (.address (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)) :=
    evalExpr_daiJoinDaiStorage (evm := evmVat) (locals := exitAfterMoveStore I)
      (exitAfterMoveStore_get_dai I)
  have hdaiNoCodeNat :
      (UInt256.ofNat
        ((evmVat.lookupAccount (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0 :=
    daiJoinDaiCode_zero_of_codeSize_zero hdaiNoCode
  have hdaiGuard :=
    evalExpr_daiJoinDaiCodeGuard_false hdai hdaiNoCodeNat
  have hblock :
      ExecBlock config { contract := contract, locals := exitStore I } evm
        exitTransition.body .reverted := by
    simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) (perm := true)
        hvat (by simp [evalExpr?, pure]) hmoveArgs hcallMove hmoveDecode) ?_
    exact checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evmVat)
      (locals := exitAfterMoveStore I) (receiver := .storage daiRef)
      (retVar := "mintRet") (name := "mint") (sendVal := 0)
      (args := [.var "usr", .var "wad"]) (perm := true) hdaiGuard
  simpa [ExecTransitionBody, exitAfterMoveStore] using ExecFuncBody.execBlockRevert hblock

theorem daiJoinExitDaiMintCallFailedAfterVatReverts (evm evmVat evmMint : EVM.State)
    (I : ExecutionEnv) (outMove outMint : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hliveOne : exitLiveWord evm.accountMap evm.executionEnv = ⟨1⟩)
    (hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcallMove :
      typedCallViaEVM config evm
        (EVM.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) "move" 0
        [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
          .int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)]
        (true, evmVat, outMove) true)
    (hdaiCode :
      Reasoning.Theory.extCodeSizeWord evmVat.accountMap
        (daiJoinDaiTargetWord evmVat.accountMap evmVat.executionEnv) ≠ ⟨0⟩)
    (hcallMint :
      typedCallViaEVM config evmVat
        (EVM.address (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)) "mint" 0
        [.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)), exitWadValue I]
        (false, evmMint, outMint) true) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body .reverted := by
  have hlive :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage liveRef) =
        .ok (.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat)) :=
    evalExpr_daiJoinLiveStorage (evm := evm) (locals := exitStore I)
      (exitStore_get_live I)
  have hliveGuard :=
    evalExpr_daiJoinLiveGuard_true hlive hliveOne
  have hmulStmt :=
    daiJoinExitInternalMulReturns evm I hfit
  have hvat :
      evalExpr? config { contract := contract, locals := exitRadStore I } evm (.storage vatRef) =
        .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) :=
    evalExpr_daiJoinVatStorage (evm := evm) (locals := exitRadStore I)
      (exitRadStore_get_vat I)
  have hvatCodeNat :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat :=
    daiJoinVatCode_pos_of_codeSize_ne_zero hvatCode
  have hvatGuard :=
    evalExpr_daiJoinVatCodeGuard_true hvat hvatCodeNat
  have hmoveArgs :=
    evalExprs_daiJoinExitVatMoveArgs evm I
  have hmoveDecode : config.externalABI.decode? "move" outMove = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hdai :
      evalExpr? config { contract := contract, locals := exitAfterMoveStore I } evmVat
        (.storage daiRef) =
        .ok (.address (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)) :=
    evalExpr_daiJoinDaiStorage (evm := evmVat) (locals := exitAfterMoveStore I)
      (exitAfterMoveStore_get_dai I)
  have hdaiCodeNat :
      0 <
        (UInt256.ofNat
          ((evmVat.lookupAccount (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat :=
    daiJoinDaiCode_pos_of_codeSize_ne_zero hdaiCode
  have hdaiGuard :=
    evalExpr_daiJoinDaiCodeGuard_true hdai hdaiCodeNat
  have hmintArgs :=
    evalExprs_daiJoinExitDaiMintArgs evmVat I
  have hblock :
      ExecBlock config { contract := contract, locals := exitStore I } evm
        exitTransition.body .reverted := by
    simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) (perm := true)
        hvat (by simp [evalExpr?, pure]) hmoveArgs hcallMove hmoveDecode) ?_
    exact checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evmVat) (evm' := evmMint)
      (locals := exitAfterMoveStore I) (receiver := .storage daiRef)
      (retVar := "mintRet") (name := "mint")
      (target := daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)
      (sendVal := 0) (args := [.var "usr", .var "wad"])
      (argVals := [.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)), exitWadValue I])
      (out := outMint) (perm := true) hdaiGuard hdai hmintArgs hcallMint
  simpa [ExecTransitionBody, exitAfterMoveStore] using ExecFuncBody.execBlockRevert hblock

theorem daiJoinExitDaiMintSuccessAfterVatReturns (evm evmVat evmMint : EVM.State)
    (I : ExecutionEnv) (outMove outMint : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hliveOne : exitLiveWord evm.accountMap evm.executionEnv = ⟨1⟩)
    (hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcallMove :
      typedCallViaEVM config evm
        (EVM.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) "move" 0
        [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
          .int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)]
        (true, evmVat, outMove) true)
    (hdaiCode :
      Reasoning.Theory.extCodeSizeWord evmVat.accountMap
        (daiJoinDaiTargetWord evmVat.accountMap evmVat.executionEnv) ≠ ⟨0⟩)
    (hcallMint :
      typedCallViaEVM config evmVat
        (EVM.address (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)) "mint" 0
        [.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)), exitWadValue I]
        (true, evmMint, outMint) true) :
    ExecTransitionBody config contract evm (exitStore I) exitTransition.body
      (.returned
        { contract := contract,
          locals := (exitAfterMoveStore I).insert "mintRet" (collapseReturns []) }
        evmMint none) := by
  have hlive :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.storage liveRef) =
        .ok (.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat)) :=
    evalExpr_daiJoinLiveStorage (evm := evm) (locals := exitStore I)
      (exitStore_get_live I)
  have hliveGuard :=
    evalExpr_daiJoinLiveGuard_true hlive hliveOne
  have hmulStmt :=
    daiJoinExitInternalMulReturns evm I hfit
  have hvat :
      evalExpr? config { contract := contract, locals := exitRadStore I } evm (.storage vatRef) =
        .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) :=
    evalExpr_daiJoinVatStorage (evm := evm) (locals := exitRadStore I)
      (exitRadStore_get_vat I)
  have hvatCodeNat :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat :=
    daiJoinVatCode_pos_of_codeSize_ne_zero hvatCode
  have hvatGuard :=
    evalExpr_daiJoinVatCodeGuard_true hvat hvatCodeNat
  have hmoveArgs :=
    evalExprs_daiJoinExitVatMoveArgs evm I
  have hmoveDecode : config.externalABI.decode? "move" outMove = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hdai :
      evalExpr? config { contract := contract, locals := exitAfterMoveStore I } evmVat
        (.storage daiRef) =
        .ok (.address (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)) :=
    evalExpr_daiJoinDaiStorage (evm := evmVat) (locals := exitAfterMoveStore I)
      (exitAfterMoveStore_get_dai I)
  have hdaiCodeNat :
      0 <
        (UInt256.ofNat
          ((evmVat.lookupAccount (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat :=
    daiJoinDaiCode_pos_of_codeSize_ne_zero hdaiCode
  have hdaiGuard :=
    evalExpr_daiJoinDaiCodeGuard_true hdai hdaiCodeNat
  have hmintArgs :=
    evalExprs_daiJoinExitDaiMintArgs evmVat I
  have hmintDecode : config.externalABI.decode? "mint" outMint = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock :
      ExecBlock config { contract := contract, locals := exitStore I } evm
        exitTransition.body
        (.ok
          { contract := contract,
            locals := (exitAfterMoveStore I).insert "mintRet" (collapseReturns []) }
          evmMint) := by
    simp only [exitTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) (perm := true)
        hvat (by simp [evalExpr?, pure]) hmoveArgs hcallMove hmoveDecode) ?_
    exact checkedExternalCallSuccess
      (cfg := config) (C := contract) (evm := evmVat) (evm' := evmMint)
      (locals := exitAfterMoveStore I) (receiver := .storage daiRef)
      (retVar := "mintRet") (name := "mint")
      (target := daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)
      (sendVal := 0) (args := [.var "usr", .var "wad"])
      (argVals := [.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)), exitWadValue I])
      (out := outMint) (perm := true) (value := [])
      hdaiGuard hdai hmintArgs hcallMint hmintDecode
  simpa [ExecTransitionBody, exitAfterMoveStore] using ExecFuncBody.execBlockOK hblock

theorem daiJoinExitVatMoveCallFailedCore
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A I} {g sel gasWord : UInt256}
    {Ain : Substate} {out : ByteArray} {k C : ℕ}
    (hcode : I.code = daiJoinBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hliveOne : exitLiveWord σ_solm I = ⟨1⟩)
    (hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm (daiJoinVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd1467 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1467⟩
      (⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ_evm I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem)
      (UInt256.ofNat 8) out (cA', σ') k C)
    (hΘ :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', false, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ_evm σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I))
          (toExecute σ_evm (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (I.depth + 1) I.header I.perm)
    (hout : out.size < UInt256.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g) evmE := by
    simpa [evmE] using daiJoinExitVatMoveCallFailed rd1467 hout
  have hcodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (daiJoinVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
    daiJoinVatCodeSize_ne_zero_accountMapEquiv hAccounts hcodeSize
  rcases hΘ with ⟨g'', A', hΘ⟩
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hbad
    simp [evmE, initState] at hbad
    rw [hbad] at hdepth
    omega
  have htgt :
      EVM.address (daiJoinVatAddress σ_solm I) =
        AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I) :=
    daiJoinVatEvmAddress_eq_target_of_accountMapEquiv hAccounts
  have hΘE :
      (cA', σ', g'', A', false, out) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
          evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I))
          (toExecute evmE.accountMap (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true := by
    simpa [evmE, initState, hperm] using hΘ
  obtain ⟨σ'_solm, A'_solm, hcallSolm, _hAccounts'⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (daiJoinVatAddress σ_solm I))
      (targetWord := daiJoinVatTargetWord σ_evm I)
      (name := "move")
      (args := [.address I.source, .address I.codeOwner,
        .int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)])
      (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain) (z := false)
      (out := out) (g'' := g'') (callGas := gasWord)
      (mem := exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := true)
      hdepthNe htgt
      (exitMoveEncode_eq I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem_size) hΘE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  have hbody :
      ExecTransitionBody config contract evmS (exitStore I) exitTransition.body .reverted := by
    simpa [evmS, initState] using
      (daiJoinExitVatMoveCallFailedReverts
        (evm := evmS)
        (evmVat := { evmS with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
        (I := I) (out := out)
        (by simpa [evmS, initState] using hwv)
        (by simpa [evmS, initState] using hliveOne)
        hfit hcodeSizeSolm
        (by simpa [evmS, initState] using hcallSolm))
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem daiJoinExitDaiMintNoCodeCore
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A I} {g sel gasWord : UInt256}
    {Ain : Substate} {out : ByteArray} {k C : ℕ}
    (hcode : I.code = daiJoinBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hliveOne : exitLiveWord σ_solm I = ⟨1⟩)
    (hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size)
    (hvatCodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm (daiJoinVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdaiCodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (daiJoinDaiTargetWord σ' I) = ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd1485 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1485⟩
      (⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ_evm I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem)
      (UInt256.ofNat 8) out (cA', σ') k C)
    (hΘ :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', true, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ_evm σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I))
          (toExecute σ_evm (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (I.depth + 1) I.header I.perm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g) evmE := by
    simpa [evmE] using daiJoinExitDaiMintNoCode rd1485 hdaiCodeSize
  have hvatCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (daiJoinVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
    daiJoinVatCodeSize_ne_zero_accountMapEquiv hAccounts hvatCodeSize
  rcases hΘ with ⟨g'', A', hΘ⟩
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hbad
    simp [evmE, initState] at hbad
    rw [hbad] at hdepth
    omega
  have htgt :
      EVM.address (daiJoinVatAddress σ_solm I) =
        AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I) :=
    daiJoinVatEvmAddress_eq_target_of_accountMapEquiv hAccounts
  have hΘE :
      (cA', σ', g'', A', true, out) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
          evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I))
          (toExecute evmE.accountMap (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true := by
    simpa [evmE, initState, hperm] using hΘ
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hAccounts'⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (daiJoinVatAddress σ_solm I))
      (targetWord := daiJoinVatTargetWord σ_evm I)
      (name := "move")
      (args := [.address I.source, .address I.codeOwner,
        .int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)])
      (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain) (z := true)
      (out := out) (g'' := g'') (callGas := gasWord)
      (mem := exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := true)
      hdepthNe htgt
      (exitMoveEncode_eq I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem_size) hΘE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  have hdaiCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ'_solm (daiJoinDaiTargetWord σ'_solm I) = ⟨0⟩ :=
    daiJoinDaiCodeSize_zero_accountMapEquiv hAccounts' hdaiCodeSize
  have hbody :
      ExecTransitionBody config contract evmS (exitStore I) exitTransition.body .reverted := by
    simpa [evmS, initState] using
      (daiJoinExitDaiMintNoCodeAfterVatReverts
        (evm := evmS)
        (evmVat := { evmS with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
        (I := I) (out := out)
        (by simpa [evmS, initState] using hwv)
        (by simpa [evmS, initState] using hliveOne)
        hfit hvatCodeSizeSolm
        (by simpa [evmS, initState] using hcallSolm)
        (by simpa [evmS, initState] using hdaiCodeSizeSolm))
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem daiJoinExitDaiMintCallFailedCore
    {cA cA' cA'' gh bl σ_evm σ_solm σ' σ'' σ₀ A I} {g sel gasWord mintGas : UInt256}
    {Ain mintAin : Substate} {out outMint : ByteArray} {k C : ℕ}
    (hcode : I.code = daiJoinBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hliveOne : exitLiveWord σ_solm I = ⟨1⟩)
    (hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size)
    (hvatCodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm (daiJoinVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdaiCodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (daiJoinDaiTargetWord σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd1576 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1576⟩
      (⟨0⟩ :: ⟨196⟩ :: exitMintSelectorPlainWord :: daiJoinDaiTargetWord σ' I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (exitMintCalldataMem I
        (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem))
      (UInt256.ofNat 8) outMint (cA'', σ'') k C)
    (hΘMove :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', true, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ_evm σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I))
          (toExecute σ_evm (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (I.depth + 1) I.header I.perm)
    (hΘMint :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', false, outMint) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl
          σ' σ₀ mintAin
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I))
          (toExecute σ' (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I)))
          mintGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMintCalldataMem I
            (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem)).readWithPadding
              128 68)
          (I.depth + 1) I.header I.perm)
    (houtMint : outMint.size < UInt256.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g) evmE := by
    simpa [evmE] using daiJoinExitDaiMintCallFailed rd1576 houtMint
  have hvatCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (daiJoinVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
    daiJoinVatCodeSize_ne_zero_accountMapEquiv hAccounts hvatCodeSize
  rcases hΘMove with ⟨gMove'', AMove', hΘMove⟩
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hbad
    simp [evmE, initState] at hbad
    rw [hbad] at hdepth
    omega
  have htgtMove :
      EVM.address (daiJoinVatAddress σ_solm I) =
        AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I) :=
    daiJoinVatEvmAddress_eq_target_of_accountMapEquiv hAccounts
  have hΘMoveE :
      (cA', σ', gMove'', AMove', true, out) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
          evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I))
          (toExecute evmE.accountMap (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true := by
    simpa [evmE, initState, hperm] using hΘMove
  obtain ⟨σ'_solm, AMove'_solm, hcallMoveSolm, hAccounts'⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (daiJoinVatAddress σ_solm I))
      (targetWord := daiJoinVatTargetWord σ_evm I)
      (name := "move")
      (args := [.address I.source, .address I.codeOwner,
        .int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)])
      (cA' := cA') (σ' := σ') (A' := AMove') (A_in := Ain) (z := true)
      (out := out) (g'' := gMove'') (callGas := gasWord)
      (mem := exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := true)
      hdepthNe htgtMove
      (exitMoveEncode_eq I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem_size) hΘMoveE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  have hdaiCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ'_solm (daiJoinDaiTargetWord σ'_solm I) ≠ ⟨0⟩ :=
    daiJoinDaiCodeSize_ne_zero_accountMapEquiv hAccounts' hdaiCodeSize
  rcases hΘMint with ⟨gMint'', AMint', hΘMint⟩
  let evmVatE : EVM.State :=
    { evmE with accountMap := σ', substate := AMove', createdAccounts := cA' }
  let evmVatS : EVM.State :=
    { evmS with accountMap := σ'_solm, substate := AMove'_solm, createdAccounts := cA' }
  let evmVatSAligned : EVM.State := { evmVatS with substate := AMove' }
  have htgtMint :
      EVM.address (daiJoinDaiAddress σ'_solm I) =
        AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I) :=
    daiJoinDaiEvmAddress_eq_target_of_accountMapEquiv hAccounts'
  have hΘMintE :
      (cA'', σ'', gMint'', AMint', false, outMint) =
        Ethereum.EVM.Θ evmVatE.executionEnv.blobVersionedHashes evmVatE.createdAccounts
          evmVatE.genesisBlockHeader evmVatE.blocks evmVatE.accountMap evmVatE.σ₀ mintAin
          (AccountAddress.ofUInt256 (UInt256.ofNat evmVatE.executionEnv.codeOwner))
          evmVatE.executionEnv.sender (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I))
          (toExecute evmVatE.accountMap (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I)))
          mintGas (UInt256.ofNat evmVatE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMintCalldataMem I
            (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem)).readWithPadding
              128 68)
          (evmVatE.executionEnv.depth + 1) evmVatE.executionEnv.header true := by
    simpa [evmVatE, evmE, initState, hperm] using hΘMint
  have hmoveMemSize :
      (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem).size = 228 :=
    exitMoveCalldataMem_size I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem_size
  obtain ⟨σ''_solm, AMint'_solm, hcallMintAligned, _hAccounts''⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmVatE) (evm_solm := evmVatSAligned)
      (tgt := EVM.address (daiJoinDaiAddress σ'_solm I))
      (targetWord := daiJoinDaiTargetWord σ' I)
      (name := "mint")
      (args := [.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)), exitWadValue I])
      (cA' := cA'') (σ' := σ'') (A' := AMint') (A_in := mintAin) (z := false)
      (out := outMint) (g'' := gMint'') (callGas := mintGas)
      (mem := exitMintCalldataMem I
        (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem))
      (inOff := ⟨128⟩) (inSize := ⟨68⟩) (callPerm := true)
      (by simpa [evmVatE, evmE, initState] using hdepthNe) htgtMint
      (exitMintEncode_eq I hmoveMemSize) hΘMintE
      (by simpa [evmVatE, evmVatSAligned, evmVatS] using hAccounts')
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  have hcallMintSolm :
      typedCallViaEVM config evmVatS
        (EVM.address (daiJoinDaiAddress σ'_solm I)) "mint" 0
        [.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)), exitWadValue I]
        (false,
          { evmVatS with
              accountMap := σ''_solm
              substate := AMint'_solm
              createdAccounts := cA'' },
          outMint) true := by
    simpa [evmVatSAligned] using
      (daiJoin_typedCallViaEVM_zero_substate_irrel
        (cfg := config) (evm := evmVatS) (A0 := AMove')
        (tgt := EVM.address (daiJoinDaiAddress σ'_solm I)) (name := "mint")
        (args := [.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)), exitWadValue I])
        (z := false) (out := outMint) (callPerm := true)
        hcallMintAligned
        (by simpa [evmVatS, evmS, initState] using hdepthNe))
  have hbody :
      ExecTransitionBody config contract evmS (exitStore I) exitTransition.body .reverted := by
    simpa [evmS, evmVatS, initState] using
      (daiJoinExitDaiMintCallFailedAfterVatReverts
        (evm := evmS) (evmVat := evmVatS)
        (evmMint := { evmVatS with
          accountMap := σ''_solm
          substate := AMint'_solm
          createdAccounts := cA'' })
        (I := I) (outMove := out) (outMint := outMint)
        (by simpa [evmS, initState] using hwv)
        (by simpa [evmS, initState] using hliveOne)
        hfit hvatCodeSizeSolm
        (by simpa [evmS, evmVatS, initState] using hcallMoveSolm)
        (by simpa [evmVatS, evmS, initState] using hdaiCodeSizeSolm)
        hcallMintSolm)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem daiJoinExitDaiMintSuccessCore
    {cA cA' cA'' gh bl σ_evm σ_solm σ' σ'' σ₀ A I} {g sel gasWord mintGas : UInt256}
    {Ain mintAin : Substate} {out outMint : ByteArray} {k C : ℕ}
    (hcode : I.code = daiJoinBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some exitTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
        (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hliveOne : exitLiveWord σ_solm I = ⟨1⟩)
    (hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size)
    (hvatCodeSize :
      Reasoning.Theory.extCodeSizeWord σ_evm (daiJoinVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdaiCodeSize :
      Reasoning.Theory.extCodeSizeWord σ' (daiJoinDaiTargetWord σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd1576 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1576⟩
      (⟨1⟩ :: ⟨196⟩ :: exitMintSelectorPlainWord :: daiJoinDaiTargetWord σ' I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (exitMintCalldataMem I
        (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem))
      (UInt256.ofNat 8) outMint (cA'', σ'') k C)
    (hΘMove :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', true, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ_evm σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I))
          (toExecute σ_evm (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (I.depth + 1) I.header I.perm)
    (hΘMint :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', true, outMint) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl
          σ' σ₀ mintAin
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I))
          (toExecute σ' (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I)))
          mintGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMintCalldataMem I
            (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem)).readWithPadding
              128 68)
          (I.depth + 1) I.header I.perm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨_, _, rd1594⟩ := daiJoinExitDaiMintCallSucceeded rd1576
  have hmoveMemSize :
      (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem).size = 228 :=
    exitMoveCalldataMem_size I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem_size
  have hmoveRead64 :
      (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    exitMoveCalldataMem_read64 I (daiJoinRadWord (exitWadWord I))
      solcFreePtrMem_size solcFreePtrMem_read64
  have hmintMemSize :
      (exitMintCalldataMem I
        (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem)).size = 228 :=
    exitMintCalldataMem_size I hmoveMemSize
  have hmintRead64 :
      (exitMintCalldataMem I
        (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem)).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    exitMintCalldataMem_read64 I hmoveMemSize hmoveRead64
  have hret : RDret daiJoinBytecode (Sat256.ofUInt256 g) evmE (cA'', σ'') ByteArray.empty := by
    simpa [evmE] using
      daiJoinExitDaiMintSuccessTail
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (σd := σ') (A := A) (I := I) (g := g) (sel := sel)
        (mem := exitMintCalldataMem I
          (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem))
        (rdata := outMint) (acc := (cA'', σ'')) hperm hmintMemSize hmintRead64
        (by simpa using rd1594)
  have hvatCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (daiJoinVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
    daiJoinVatCodeSize_ne_zero_accountMapEquiv hAccounts hvatCodeSize
  rcases hΘMove with ⟨gMove'', AMove', hΘMove⟩
  have hdepthNe : evmE.executionEnv.depth ≠ 1024 := by
    intro hbad
    simp [evmE, initState] at hbad
    rw [hbad] at hdepth
    omega
  have htgtMove :
      EVM.address (daiJoinVatAddress σ_solm I) =
        AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I) :=
    daiJoinVatEvmAddress_eq_target_of_accountMapEquiv hAccounts
  have hΘMoveE :
      (cA', σ', gMove'', AMove', true, out) =
        Ethereum.EVM.Θ evmE.executionEnv.blobVersionedHashes evmE.createdAccounts
          evmE.genesisBlockHeader evmE.blocks evmE.accountMap evmE.σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat evmE.executionEnv.codeOwner))
          evmE.executionEnv.sender (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I))
          (toExecute evmE.accountMap (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat evmE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true := by
    simpa [evmE, initState, hperm] using hΘMove
  obtain ⟨σ'_solm, AMove'_solm, hcallMoveSolm, hAccounts'⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (daiJoinVatAddress σ_solm I))
      (targetWord := daiJoinVatTargetWord σ_evm I)
      (name := "move")
      (args := [.address I.source, .address I.codeOwner,
        .int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)])
      (cA' := cA') (σ' := σ') (A' := AMove') (A_in := Ain) (z := true)
      (out := out) (g'' := gMove'') (callGas := gasWord)
      (mem := exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := true)
      hdepthNe htgtMove
      (exitMoveEncode_eq I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem_size) hΘMoveE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  have hdaiCodeSizeSolm :
      Reasoning.Theory.extCodeSizeWord σ'_solm (daiJoinDaiTargetWord σ'_solm I) ≠ ⟨0⟩ :=
    daiJoinDaiCodeSize_ne_zero_accountMapEquiv hAccounts' hdaiCodeSize
  rcases hΘMint with ⟨gMint'', AMint', hΘMint⟩
  let evmVatE : EVM.State :=
    { evmE with accountMap := σ', substate := AMove', createdAccounts := cA' }
  let evmVatS : EVM.State :=
    { evmS with accountMap := σ'_solm, substate := AMove'_solm, createdAccounts := cA' }
  let evmVatSAligned : EVM.State := { evmVatS with substate := AMove' }
  have htgtMint :
      EVM.address (daiJoinDaiAddress σ'_solm I) =
        AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I) :=
    daiJoinDaiEvmAddress_eq_target_of_accountMapEquiv hAccounts'
  have hΘMintE :
      (cA'', σ'', gMint'', AMint', true, outMint) =
        Ethereum.EVM.Θ evmVatE.executionEnv.blobVersionedHashes evmVatE.createdAccounts
          evmVatE.genesisBlockHeader evmVatE.blocks evmVatE.accountMap evmVatE.σ₀ mintAin
          (AccountAddress.ofUInt256 (UInt256.ofNat evmVatE.executionEnv.codeOwner))
          evmVatE.executionEnv.sender (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I))
          (toExecute evmVatE.accountMap (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I)))
          mintGas (UInt256.ofNat evmVatE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMintCalldataMem I
            (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem)).readWithPadding
              128 68)
          (evmVatE.executionEnv.depth + 1) evmVatE.executionEnv.header true := by
    simpa [evmVatE, evmE, initState, hperm] using hΘMint
  obtain ⟨σ''_solm, AMint'_solm, hcallMintAligned, hAccounts''⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmVatE) (evm_solm := evmVatSAligned)
      (tgt := EVM.address (daiJoinDaiAddress σ'_solm I))
      (targetWord := daiJoinDaiTargetWord σ' I)
      (name := "mint")
      (args := [.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)), exitWadValue I])
      (cA' := cA'') (σ' := σ'') (A' := AMint') (A_in := mintAin) (z := true)
      (out := outMint) (g'' := gMint'') (callGas := mintGas)
      (mem := exitMintCalldataMem I
        (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem))
      (inOff := ⟨128⟩) (inSize := ⟨68⟩) (callPerm := true)
      (by simpa [evmVatE, evmE, initState] using hdepthNe) htgtMint
      (exitMintEncode_eq I hmoveMemSize) hΘMintE
      (by simpa [evmVatE, evmVatSAligned, evmVatS] using hAccounts')
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  have hcallMintSolm :
      typedCallViaEVM config evmVatS
        (EVM.address (daiJoinDaiAddress σ'_solm I)) "mint" 0
        [.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)), exitWadValue I]
        (true,
          { evmVatS with
              accountMap := σ''_solm
              substate := AMint'_solm
              createdAccounts := cA'' },
          outMint) true := by
    simpa [evmVatSAligned] using
      (daiJoin_typedCallViaEVM_zero_substate_irrel
        (cfg := config) (evm := evmVatS) (A0 := AMove')
        (tgt := EVM.address (daiJoinDaiAddress σ'_solm I)) (name := "mint")
        (args := [.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)), exitWadValue I])
        (z := true) (out := outMint) (callPerm := true)
        hcallMintAligned
        (by simpa [evmVatS, evmS, initState] using hdepthNe))
  let evmMintS : EVM.State :=
    { evmVatS with accountMap := σ''_solm, substate := AMint'_solm, createdAccounts := cA'' }
  have hbody :
      ExecTransitionBody config contract evmS (exitStore I) exitTransition.body
        (.returned
          { contract := contract,
            locals := (exitAfterMoveStore I).insert "mintRet" (collapseReturns []) }
          evmMintS none) := by
    simpa [evmS, evmVatS, evmMintS, initState] using
      (daiJoinExitDaiMintSuccessAfterVatReturns
        (evm := evmS) (evmVat := evmVatS) (evmMint := evmMintS)
        (I := I) (outMove := out) (outMint := outMint)
        (by simpa [evmS, initState] using hwv)
        (by simpa [evmS, initState] using hliveOne)
        hfit hvatCodeSizeSolm
        (by simpa [evmS, evmVatS, initState] using hcallMoveSolm)
        (by simpa [evmVatS, evmS, initState] using hdaiCodeSizeSolm)
        hcallMintSolm)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by rfl)
    (by simpa [evmMintS] using hAccounts'')
    (by
      simpa [exitTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem daiJoinExitBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiJoinSelBytes 3))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiJoinSelBytes 3) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some exitTransition :=
    daiJoinDispatchExit hsel
  have hreach := daiJoinReachExitBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := daiJoinDecode_exit_ok hsz68
    obtain ⟨_, _, rd1262⟩ := daiJoinExitX_decoded
      (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    by_cases hlive : exitLiveWord σ_evm I = ⟨1⟩
    · obtain ⟨_, _, rd1336⟩ := daiJoinExitLiveOk hlive rd1262
      have hliveSolm : exitLiveWord σ_solm I = ⟨1⟩ := by
        have hslot : exitLiveWord σ_evm I = exitLiveWord σ_solm I := by
          simpa [exitLiveWord, daiJoinSlotWord] using
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
        exact hslot ▸ hlive
      have finishMul
          (hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size)
          {k C : ℕ}
          (rd1377 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1377⟩
            [daiJoinRadWord (exitWadWord I), UInt256.ofNat I.codeOwner, solcSourceWord I,
              joinMoveSelectorPlainWord, daiJoinVatTargetWord σ_evm I, exitWadWord I,
              exitUsrMaskedWord I, ⟨232⟩, daiJoinSelWord I]
            solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
          runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
        by_cases hvatCode :
            Reasoning.Theory.extCodeSizeWord σ_evm
              (daiJoinVatTargetWord σ_evm I) = ⟨0⟩
        · have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
            daiJoinExitVatMoveNoCode rd1377 hvatCode
          have hvatCodeSolm :
              Reasoning.Theory.extCodeSizeWord σ_solm
                (daiJoinVatTargetWord σ_solm I) = ⟨0⟩ :=
            daiJoinVatCodeSize_zero_accountMapEquiv hAccounts hvatCode
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (exitStore I)
                exitTransition.body .reverted :=
            daiJoinExitVatNoCodeReverts
              (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simpa [initState] using hwv)
              (by simpa [initState] using hliveSolm) hfit
              (by simpa [initState] using hvatCodeSolm)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · obtain ⟨_, _, _, rd1466⟩ :=
            daiJoinExitVatMoveCallReady rd1377 hvatCode
          by_cases hdepthLt : I.depth.val < 1024
          · obtain ⟨cA', σ', z, out, Ain, gasWord, k', C', hΘ, rd1467, hout⟩ :=
              daiJoinExitVatMovePostCall rd1466 hdepthLt
            cases z
            · exact daiJoinExitVatMoveCallFailedCore
                (cA := cA) (cA' := cA') (gh := gh) (bl := bl)
                (σ_evm := σ_evm) (σ_solm := σ_solm) (σ' := σ')
                (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := daiJoinSelWord I)
                (gasWord := gasWord) (Ain := Ain) (out := out) (k := k') (C := C')
                hcode hperm hwv hdispatch hdecode hAccounts hliveSolm hfit hvatCode hdepthLt
                (by simpa using rd1467) hΘ hout
            · obtain ⟨_, _, rd1485⟩ :=
                daiJoinExitVatMoveCallSucceeded (by simpa using rd1467)
              by_cases hdaiCode :
                  Reasoning.Theory.extCodeSizeWord σ'
                    (daiJoinDaiTargetWord σ' I) = ⟨0⟩
              · exact daiJoinExitDaiMintNoCodeCore
                  (cA := cA) (cA' := cA') (gh := gh) (bl := bl)
                  (σ_evm := σ_evm) (σ_solm := σ_solm) (σ' := σ')
                  (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := daiJoinSelWord I)
                  (gasWord := gasWord) (Ain := Ain) (out := out)
                  hcode hperm hwv hdispatch hdecode hAccounts hliveSolm hfit hvatCode
                  hdaiCode hdepthLt (by simpa using rd1485) hΘ
              · obtain ⟨_mintGasWord, _, _, rd1575⟩ :=
                  daiJoinExitDaiMintCallReady (by simpa using rd1485) hdaiCode
                obtain ⟨cA'', σ'', zMint, outMint, mintAin, mintCallGas, kMint, CMint,
                    hΘMint, rd1576, houtMint⟩ :=
                  daiJoinExitDaiMintPostCall rd1575 hdepthLt
                cases zMint
                · exact daiJoinExitDaiMintCallFailedCore
                    (cA := cA) (cA' := cA') (cA'' := cA'') (gh := gh) (bl := bl)
                    (σ_evm := σ_evm) (σ_solm := σ_solm) (σ' := σ') (σ'' := σ'')
                    (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := daiJoinSelWord I)
                    (gasWord := gasWord) (mintGas := mintCallGas)
                    (Ain := Ain) (mintAin := mintAin) (out := out) (outMint := outMint)
                    (k := kMint) (C := CMint)
                    hcode hperm hwv hdispatch hdecode hAccounts hliveSolm hfit hvatCode hdaiCode
                    hdepthLt (by simpa using rd1576) hΘ hΘMint houtMint
                · exact daiJoinExitDaiMintSuccessCore
                    (cA := cA) (cA' := cA') (cA'' := cA'') (gh := gh) (bl := bl)
                    (σ_evm := σ_evm) (σ_solm := σ_solm) (σ' := σ') (σ'' := σ'')
                    (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := daiJoinSelWord I)
                    (gasWord := gasWord) (mintGas := mintCallGas)
                    (Ain := Ain) (mintAin := mintAin) (out := out) (outMint := outMint)
                    (k := kMint) (C := CMint)
                    hcode hperm hwv hdispatch hdecode hAccounts hliveSolm hfit hvatCode hdaiCode
                    hdepthLt (by simpa using rd1576) hΘ hΘMint
          · have hdepthEq : I.depth = 1024 := by
              apply Fin.ext
              have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
              have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepthLt
              omega
            obtain ⟨_, _, rd1467⟩ := daiJoinExitVatMoveCallDepthLimit rd1466 hdepthEq
            have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
              daiJoinExitVatMoveCallFailed rd1467 (by simp [UInt256.size])
            let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            have hvatCodeSolm :
                Reasoning.Theory.extCodeSizeWord σ_solm
                  (daiJoinVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
              daiJoinVatCodeSize_ne_zero_accountMapEquiv hAccounts hvatCode
            have hcallSolm :
                typedCallViaEVM config evmS
                  (EVM.address (daiJoinVatAddress σ_solm I)) "move" 0
                  [.address I.source, .address I.codeOwner,
                    .int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)]
                  (false,
                    { evmS with
                      substate :=
                        (evmS.addAccessedAccount (EVM.address (daiJoinVatAddress σ_solm I))).substate },
                    ByteArray.empty) true := by
              exact callNotMade_depthLimit
                (cfg := config) (evm := evmS)
                (tgt := EVM.address (daiJoinVatAddress σ_solm I))
                (name := "move")
                (args := [.address I.source, .address I.codeOwner,
                  .int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)])
                (calldata :=
                  (exitMoveCalldataMem I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem).readWithPadding
                    128 100)
                (callPerm := true)
                (exitMoveEncode_eq I (daiJoinRadWord (exitWadWord I)) solcFreePtrMem_size)
                (by simpa [evmS, initState] using hdepthEq)
            have hbody :
                ExecTransitionBody config contract evmS (exitStore I) exitTransition.body .reverted :=
              daiJoinExitVatMoveCallFailedReverts
                (evm := evmS)
                (evmVat :=
                  { evmS with
                    substate :=
                      (evmS.addAccessedAccount (EVM.address (daiJoinVatAddress σ_solm I))).substate })
                (I := I) (out := ByteArray.empty)
                (by simpa [evmS, initState] using hwv)
                (by simpa [evmS, initState] using hliveSolm)
                hfit hvatCodeSolm
                (by simpa [evmS, initState] using hcallSolm)
            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      by_cases hwad : exitWadWord I = ⟨0⟩
      · have hmulOk :
            exitWadWord I = ⟨0⟩ ∨
              UInt256.div (daiJoinRadWord (exitWadWord I)) (exitWadWord I) =
                daiJoinONEWord :=
          Or.inl hwad
        obtain ⟨_, _, rd1377⟩ := daiJoinExitMulSuccess hmulOk rd1336
        have hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size := by
          rw [hwad]
          native_decide
        exact finishMul hfit (by simpa using rd1377)
      · by_cases hguard :
          UInt256.div (daiJoinRadWord (exitWadWord I)) (exitWadWord I) = daiJoinONEWord
        · have hmulOk :
              exitWadWord I = ⟨0⟩ ∨
                UInt256.div (daiJoinRadWord (exitWadWord I)) (exitWadWord I) =
                  daiJoinONEWord :=
            Or.inr hguard
          obtain ⟨_, _, rd1377⟩ := daiJoinExitMulSuccess hmulOk rd1336
          have hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size :=
            daiJoinMulFit_of_guard hguard
          exact finishMul hfit (by simpa using rd1377)
        · have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
            daiJoinExitMulReverts hwad hguard rd1336
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (exitStore I)
                exitTransition.body .reverted :=
            daiJoinExitBodyMulReverts
              (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simpa [initState] using hwv)
              (by simpa [initState] using hliveSolm) hwad hguard
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
        daiJoinExitLiveReverts hlive rd1262
      have hliveSolm : exitLiveWord σ_solm I ≠ ⟨1⟩ := by
        intro hbad
        apply hlive
        have hslot : exitLiveWord σ_evm I = exitLiveWord σ_solm I := by
          simpa [exitLiveWord, daiJoinSlotWord] using
            accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
        exact hslot.trans hbad
      have hbody :
          ExecTransitionBody config contract
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (exitStore I)
            exitTransition.body .reverted :=
        daiJoinExitNotLiveReverts
          (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
          (by simpa [initState] using hwv)
          (by simpa [initState] using hliveSolm)
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hdecode := daiJoinDecode_exit_none_short hsz4 (by omega)
    exact (daiJoinExitX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize (by omega) hreach)
      |>.reEquivDecodingFailed hcode hdispatch hdecode

end Benchmarks.Dss.DaiJoin
