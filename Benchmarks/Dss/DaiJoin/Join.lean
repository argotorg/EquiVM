import Benchmarks.Dss.DaiJoin.JoinTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.DaiJoin

/-! ## `join(address,uint256)` -/

theorem daiJoinDecode_join_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
      (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I) := by
  simpa [config, joinTransition, joinStore, joinUsrValue, joinWadValue, joinUsrWord,
    joinWadWord, calldataWord] using
    decodeCalldata_legacyAddress_uint256_ok (cd := I.calldata) (x := "usr") (y := "wad")
      hsz68

theorem daiJoinDecode_join_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
      (transitionSignature joinTransition).paramTypes I.calldata = none := by
  simpa [config, joinTransition] using
    decodeCalldata_legacyAddress_uint256_none_short (cd := I.calldata)
      (x := "usr") (y := "wad") hsz4 hshort

theorem daiJoinReachJoinBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiJoinSelBytes 4)) :
    ∃ k C, RD daiJoinBytecode I g
        (initState cA gh bl σ σ₀ g A I)
        ⟨188⟩ [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : daiJoinSelWord I = ⟨0x3b4da69f⟩ :=
    daiJoinSelWord_eq_of_beq I hsz 0x3b 0x4d 0xa6 0x9f ⟨0x3b4da69f⟩
      (by native_decide) (by simpa [daiJoinSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat daiJoinBytecode daiJoinRootSplitPc) (daiJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq
        (armSelNat daiJoinBytecode
          (nthArmPc daiJoinBytecode daiJoinLowFirstArmPc j))
        (daiJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    native_decide
  have htake :
      UInt256.eq
        (armSelNat daiJoinBytecode
          (nthArmPc daiJoinBytecode daiJoinLowFirstArmPc 1))
        (daiJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact daiJoinReachLowBody 1 (by omega) ⟨188⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem daiJoinJoinX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨188⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiJoinBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨449⟩
        [joinWadWord I, joinUsrMaskedWord I, ⟨232⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := daiJoinBytecode) (sel := sel)
    (entry := ⟨188⟩) (ret := ⟨232⟩) (decoded := ⟨210⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcAddressUint256ExternalMaskAndJumpMasked
    (code := daiJoinBytecode) (decoded := ⟨210⟩) (ret := ⟨232⟩)
    (routine := ⟨449⟩) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [joinWadWord, joinUsrMaskedWord, joinUsrWord, calldataWord] using hroutine⟩

theorem daiJoinJoinX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD daiJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨188⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := daiJoinBytecode) (sel := sel)
    (entry := ⟨188⟩) (ret := ⟨232⟩) (decoded := ⟨210⟩)
    (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem joinStore_get_wad (I : ExecutionEnv) :
    (joinStore I).get? "wad" = some (joinWadValue I) := by
  rw [joinStore, store_get_self]

theorem evalExprs_daiJoinJoinMulArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := joinStore I } evm
      [.intLit ONE, .var "wad"] =
        .ok [.int (Int.ofNat daiJoinONEWord.toNat), joinWadValue I] := by
  have hOne :
      evalExpr? config { contract := contract, locals := joinStore I } evm (.intLit ONE) =
        .ok (.int (Int.ofNat daiJoinONEWord.toNat)) := by
    simp [evalExpr?, pure, daiJoinONE_eq_ONEWord_toNat]
  have hWad :
      evalExpr? config { contract := contract, locals := joinStore I } evm (.var "wad") =
        .ok (joinWadValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((joinStore I).get? "wad") =
      .ok (joinWadValue I)
    rw [joinStore_get_wad]
    rfl
  simp [evalExprs?, hOne, hWad, EvalResult.bind, bind, pure]

theorem daiJoinJoinBodyMulReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hwad : joinWadWord I ≠ ⟨0⟩)
    (hguard :
      UInt256.div (daiJoinRadWord (joinWadWord I)) (joinWadWord I) ≠ daiJoinONEWord) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    rfl
  have hbindMul :
      bindParams? mulFunction.params
          [.int (Int.ofNat daiJoinONEWord.toNat), joinWadValue I] =
        some (daiJoinUintBinaryLocals daiJoinONEWord (joinWadWord I)) := by
    simp [mulFunction, uint256, bindParams?, daiJoinUintBinaryLocals, joinWadValue]
  have hover :
      UInt256.size ≤ daiJoinONEWord.toNat * (joinWadWord I).toNat :=
    daiJoinMulOverflow_of_guard_fail (x := daiJoinONEWord) (y := joinWadWord I) hwad hguard
  have hmulStmt :
      ExecStmt config { contract := contract, locals := joinStore I } evm
        (.internalCall "mul" [.intLit ONE, .var "wad"] "rad") .reverted :=
    internalCallFunctionRevert
      (cfg := config)
      (caller := Frame.mk contract (joinStore I))
      (evm := evm) (name := "mul") (retVar := "rad")
      (args := [.intLit ONE, .var "wad"])
      (argVals := [.int (Int.ofNat daiJoinONEWord.toNat), joinWadValue I])
      (callee := mulFunction)
      (locals := daiJoinUintBinaryLocals daiJoinONEWord (joinWadWord I))
      (evalExprs_daiJoinJoinMulArgs evm I) hlookupMul hbindMul
      (execDaiJoinMulFunctionRevert evm (x := daiJoinONEWord) (y := joinWadWord I) hover)
  have hblock :
      ExecBlock config { contract := contract, locals := joinStore I } evm
        joinTransition.body .reverted := by
    simp only [joinTransition, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    exact ExecBlock.consRevert hmulStmt
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

abbrev joinRadStore (I : ExecutionEnv) : Store :=
  (joinStore I).insert "rad" (.int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat))

theorem daiJoinJoinInternalMulReturns (evm : EVM.State) (I : ExecutionEnv)
    (hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := joinStore I } evm
      (.internalCall "mul" [.intLit ONE, .var "wad"] "rad")
      (.ok { contract := contract, locals := joinRadStore I } evm) := by
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    rfl
  have hbindMul :
      bindParams? mulFunction.params
          [.int (Int.ofNat daiJoinONEWord.toNat), joinWadValue I] =
        some (daiJoinUintBinaryLocals daiJoinONEWord (joinWadWord I)) := by
    simp [mulFunction, uint256, bindParams?, daiJoinUintBinaryLocals, joinWadValue]
  have hbody :=
    execDaiJoinMulFunctionReturn evm
      (x := daiJoinONEWord) (y := joinWadWord I)
      (prod := daiJoinRadWord (joinWadWord I)) rfl hfit
  have hstmt :=
    internalCallFunctionReturn
      (cfg := config)
      (caller := Frame.mk contract (joinStore I))
      (evm := evm) (calleeEvm := evm)
      (name := "mul") (retVar := "rad")
      (args := [.intLit ONE, .var "wad"])
      (argVals := [.int (Int.ofNat daiJoinONEWord.toNat), joinWadValue I])
      (callee := mulFunction)
      (locals := daiJoinUintBinaryLocals daiJoinONEWord (joinWadWord I))
      (calleeSolm :=
        { contract := contract,
          locals := daiJoinUintBinaryLocalsZ daiJoinONEWord (joinWadWord I)
            (daiJoinRadWord (joinWadWord I)) })
      (value := some [.int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)])
      (evalExprs_daiJoinJoinMulArgs evm I) hlookupMul hbindMul hbody
  simpa [joinRadStore, resumeAfterInternalCall, collapseReturns] using hstmt

theorem daiJoinJoinMulPrefixReturns (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size) :
    ExecBlock config { contract := contract, locals := joinStore I } evm
      (nonpayable ++ [.internalCall "mul" [.intLit ONE, .var "wad"] "rad"])
      (.ok { contract := contract, locals := joinRadStore I } evm) := by
  simp only [nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  exact ExecBlock.consNormal (daiJoinJoinInternalMulReturns evm I hfit) ExecBlock.nil

theorem joinRadStore_get_vat (I : ExecutionEnv) :
    (joinRadStore I).get? "vat" = none := by
  rw [joinRadStore, store_get_ne _ _ (by decide), joinStore,
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem joinRadStore_get_usr (I : ExecutionEnv) :
    (joinRadStore I).get? "usr" = some (joinUsrValue I) := by
  rw [joinRadStore, store_get_ne _ _ (by decide), joinStore,
    store_get_ne _ _ (by decide), store_get_self]

theorem joinRadStore_get_rad (I : ExecutionEnv) :
    (joinRadStore I).get? "rad" =
      some (.int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)) := by
  rw [joinRadStore, store_get_self]

theorem joinUsrValue_eq_masked (I : ExecutionEnv) :
    joinUsrValue I = .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)) := by
  rw [joinUsrValue, accountAddress_ofUInt256_eq_ofNat_toNat]
  simpa [joinUsrMaskedWord] using solcAddressValue_masked (joinUsrWord I)

theorem evalExprs_daiJoinJoinVatMoveArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := joinRadStore I } evm
      [thisAddr, .var "usr", .var "rad"] =
        .ok [.address evm.executionEnv.codeOwner,
          .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
          .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)] := by
  have hThis :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm thisAddr =
        .ok (.address evm.executionEnv.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, pure]
  have hUsr :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm (.var "usr") =
        .ok (.address (AccountAddress.ofUInt256 (joinUsrMaskedWord I))) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((joinRadStore I).get? "usr") =
      .ok (.address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)))
    rw [joinRadStore_get_usr, joinUsrValue_eq_masked]
    rfl
  have hRad :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm (.var "rad") =
        .ok (.int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((joinRadStore I).get? "rad") =
      .ok (.int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat))
    rw [joinRadStore_get_rad]
    rfl
  simp [evalExprs?, hThis, hUsr, hRad, EvalResult.bind, bind, pure]

theorem evalExpr_daiJoinVatStorage {evm : EVM.State} {locals : Store}
    (hvat : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := vatRef) (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨1⟩)
    (value := .address (daiJoinVatAddress evm.accountMap evm.executionEnv))
    hvat
    (by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [daiJoinVatAddress, daiJoinVatTargetWord, daiJoinAddressReturnWord,
        daiJoinSlotWord] using
        daiJoinStorageLocLoad_address_offset0 evm ⟨1⟩)

theorem evalExpr_daiJoinVatCodeGuard_false {evm : EVM.State} {locals : Store}
    (hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)))
    (hnoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hnoCode]

theorem evalExpr_daiJoinVatCodeGuard_true {evm : EVM.State} {locals : Store}
    (hvat :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)))
    (hcode :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hvat, evalBinaryOp?, EVM.Word.ofNat, hcode]

abbrev joinAfterMoveStore (I : ExecutionEnv) : Store :=
  (joinRadStore I).insert "moveRet" (collapseReturns [])

theorem joinAfterMoveStore_get_wad (I : ExecutionEnv) :
    (joinAfterMoveStore I).get? "wad" = some (joinWadValue I) := by
  rw [joinAfterMoveStore, store_get_ne _ _ (by decide), joinRadStore,
    store_get_ne _ _ (by decide), joinStore, store_get_self]

theorem joinAfterMoveStore_get_dai (I : ExecutionEnv) :
    (joinAfterMoveStore I).get? "dai" = none := by
  rw [joinAfterMoveStore, store_get_ne _ _ (by decide), joinRadStore,
    store_get_ne _ _ (by decide), joinStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem evalExprs_daiJoinJoinDaiBurnArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := joinAfterMoveStore I } evm
      [sender, .var "wad"] =
        .ok [.address evm.executionEnv.source, joinWadValue I] := by
  have hSender :
      evalExpr? config { contract := contract, locals := joinAfterMoveStore I } evm sender =
        .ok (.address evm.executionEnv.source) := by
    simp [sender, evalExpr?, envValue, pure]
  have hWad :
      evalExpr? config { contract := contract, locals := joinAfterMoveStore I } evm (.var "wad") =
        .ok (joinWadValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((joinAfterMoveStore I).get? "wad") =
      .ok (joinWadValue I)
    rw [joinAfterMoveStore_get_wad]
    rfl
  simp [evalExprs?, hSender, hWad, EvalResult.bind, bind, pure]

theorem evalExpr_daiJoinDaiStorage {evm : EVM.State} {locals : Store}
    (hdai : locals.get? "dai" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage daiRef) =
      .ok (.address (daiJoinDaiAddress evm.accountMap evm.executionEnv)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := daiRef) (er := ({ base := "dai", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨2⟩)
    (value := .address (daiJoinDaiAddress evm.accountMap evm.executionEnv))
    hdai
    (by simp [evalStorageRef, evalStorageRefSteps, daiRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by rfl)
    (by
      simpa [daiJoinDaiAddress, daiJoinDaiTargetWord, daiJoinAddressReturnWord,
        daiJoinSlotWord] using
        daiJoinStorageLocLoad_address_offset0 evm ⟨2⟩)

theorem evalExpr_daiJoinDaiCodeGuard_false {evm : EVM.State} {locals : Store}
    (hdai :
      evalExpr? config { contract := contract, locals := locals } evm (.storage daiRef) =
        .ok (.address (daiJoinDaiAddress evm.accountMap evm.executionEnv)))
    (hnoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (daiJoinDaiAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage daiRef)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hdai, evalBinaryOp?, EVM.Word.ofNat, hnoCode]

theorem evalExpr_daiJoinDaiCodeGuard_true {evm : EVM.State} {locals : Store}
    (hdai :
      evalExpr? config { contract := contract, locals := locals } evm (.storage daiRef) =
        .ok (.address (daiJoinDaiAddress evm.accountMap evm.executionEnv)))
    (hcode :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (daiJoinDaiAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage daiRef)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hdai, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem daiJoinJoinVatNoCodeReverts (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size)
    (hnoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) = ⟨0⟩) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  have hmulStmt :=
    daiJoinJoinInternalMulReturns evm I hfit
  have hvat :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm (.storage vatRef) =
        .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) :=
    evalExpr_daiJoinVatStorage (evm := evm) (locals := joinRadStore I)
      (joinRadStore_get_vat I)
  have hnoCodeNat :
      (UInt256.ofNat
        ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0 :=
    daiJoinVatCode_zero_of_codeSize_zero hnoCode
  have hguard :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_daiJoinVatCodeGuard_false hvat hnoCodeNat
  have hblock :
      ExecBlock config { contract := contract, locals := joinStore I } evm
        joinTransition.body .reverted := by
    simp only [joinTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem daiJoinJoinVatMoveCallFailedReverts (evm evmVat : EVM.State)
    (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size)
    (hcode :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcall :
      typedCallViaEVM config evm
        (EVM.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) "move" 0
        [.address evm.executionEnv.codeOwner,
          .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
          .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)]
        (false, evmVat, out) true) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  have hmulStmt :=
    daiJoinJoinInternalMulReturns evm I hfit
  have hvat :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm (.storage vatRef) =
        .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) :=
    evalExpr_daiJoinVatStorage (evm := evm) (locals := joinRadStore I)
      (joinRadStore_get_vat I)
  have hcodeNat :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat :=
    daiJoinVatCode_pos_of_codeSize_ne_zero hcode
  have hguard :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_daiJoinVatCodeGuard_true hvat hcodeNat
  have hargs :=
    evalExprs_daiJoinJoinVatMoveArgs evm I
  have hblock :
      ExecBlock config { contract := contract, locals := joinStore I } evm
        joinTransition.body .reverted := by
    simp only [joinTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert
      (ExecStmt.externalCallFailure (sendVal := 0) (perm := true)
        hvat (by simp [evalExpr?, pure]) hargs hcall)
  simpa [ExecTransitionBody] using ExecFuncBody.execBlockRevert hblock

theorem daiJoinJoinDaiBurnNoCodeAfterVatReverts (evm evmVat : EVM.State)
    (I : ExecutionEnv) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size)
    (hvatCode :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcallMove :
      typedCallViaEVM config evm
        (EVM.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) "move" 0
        [.address evm.executionEnv.codeOwner,
          .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
          .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)]
        (true, evmVat, out) true)
    (hdaiNoCode :
      Reasoning.Theory.uniswapExtCodeSizeWord evmVat.accountMap
        (daiJoinDaiTargetWord evmVat.accountMap evmVat.executionEnv) = ⟨0⟩) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  have hmulStmt :=
    daiJoinJoinInternalMulReturns evm I hfit
  have hvat :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm (.storage vatRef) =
        .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) :=
    evalExpr_daiJoinVatStorage (evm := evm) (locals := joinRadStore I)
      (joinRadStore_get_vat I)
  have hvatCodeNat :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat :=
    daiJoinVatCode_pos_of_codeSize_ne_zero hvatCode
  have hvatGuard :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_daiJoinVatCodeGuard_true hvat hvatCodeNat
  have hmoveArgs :=
    evalExprs_daiJoinJoinVatMoveArgs evm I
  have hmoveDecode : config.externalABI.decode? "move" out = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hdai :
      evalExpr? config { contract := contract, locals := joinAfterMoveStore I } evmVat
        (.storage daiRef) =
        .ok (.address (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)) :=
    evalExpr_daiJoinDaiStorage (evm := evmVat) (locals := joinAfterMoveStore I)
      (joinAfterMoveStore_get_dai I)
  have hdaiNoCodeNat :
      (UInt256.ofNat
        ((evmVat.lookupAccount (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)).option 0
          (fun acc => acc.code.size))).toNat = 0 :=
    daiJoinDaiCode_zero_of_codeSize_zero hdaiNoCode
  have hdaiGuard :
      evalExpr? config { contract := contract, locals := joinAfterMoveStore I } evmVat
        (.binary .gt (.extCodeSize (.storage daiRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_daiJoinDaiCodeGuard_false hdai hdaiNoCodeNat
  have hblock :
      ExecBlock config { contract := contract, locals := joinStore I } evm
        joinTransition.body .reverted := by
    simp only [joinTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) (perm := true)
        hvat (by simp [evalExpr?, pure]) hmoveArgs hcallMove hmoveDecode) ?_
    exact checkedExternalCallNoCode
      (cfg := config) (C := contract) (evm := evmVat)
      (locals := joinAfterMoveStore I) (receiver := .storage daiRef)
      (retVar := "burnRet") (name := "burn") (sendVal := 0)
      (args := [sender, .var "wad"]) (perm := true) hdaiGuard
  simpa [ExecTransitionBody, joinAfterMoveStore] using ExecFuncBody.execBlockRevert hblock

theorem daiJoinJoinDaiBurnCallFailedAfterVatReverts (evm evmVat evmBurn : EVM.State)
    (I : ExecutionEnv) (outMove outBurn : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size)
    (hvatCode :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcallMove :
      typedCallViaEVM config evm
        (EVM.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) "move" 0
        [.address evm.executionEnv.codeOwner,
          .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
          .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)]
        (true, evmVat, outMove) true)
    (hdaiCode :
      Reasoning.Theory.uniswapExtCodeSizeWord evmVat.accountMap
        (daiJoinDaiTargetWord evmVat.accountMap evmVat.executionEnv) ≠ ⟨0⟩)
    (hcallBurn :
      typedCallViaEVM config evmVat
        (EVM.address (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)) "burn" 0
        [.address evmVat.executionEnv.source, joinWadValue I]
        (false, evmBurn, outBurn) true) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  have hmulStmt :=
    daiJoinJoinInternalMulReturns evm I hfit
  have hvat :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm (.storage vatRef) =
        .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) :=
    evalExpr_daiJoinVatStorage (evm := evm) (locals := joinRadStore I)
      (joinRadStore_get_vat I)
  have hvatCodeNat :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat :=
    daiJoinVatCode_pos_of_codeSize_ne_zero hvatCode
  have hvatGuard :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_daiJoinVatCodeGuard_true hvat hvatCodeNat
  have hmoveArgs :=
    evalExprs_daiJoinJoinVatMoveArgs evm I
  have hmoveDecode : config.externalABI.decode? "move" outMove = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hdai :
      evalExpr? config { contract := contract, locals := joinAfterMoveStore I } evmVat
        (.storage daiRef) =
        .ok (.address (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)) :=
    evalExpr_daiJoinDaiStorage (evm := evmVat) (locals := joinAfterMoveStore I)
      (joinAfterMoveStore_get_dai I)
  have hdaiCodeNat :
      0 <
        (UInt256.ofNat
          ((evmVat.lookupAccount (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat :=
    daiJoinDaiCode_pos_of_codeSize_ne_zero hdaiCode
  have hdaiGuard :
      evalExpr? config { contract := contract, locals := joinAfterMoveStore I } evmVat
        (.binary .gt (.extCodeSize (.storage daiRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_daiJoinDaiCodeGuard_true hdai hdaiCodeNat
  have hburnArgs :=
    evalExprs_daiJoinJoinDaiBurnArgs evmVat I
  have hblock :
      ExecBlock config { contract := contract, locals := joinStore I } evm
        joinTransition.body .reverted := by
    simp only [joinTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) (perm := true)
        hvat (by simp [evalExpr?, pure]) hmoveArgs hcallMove hmoveDecode) ?_
    exact checkedExternalCallFailure
      (cfg := config) (C := contract) (evm := evmVat) (evm' := evmBurn)
      (locals := joinAfterMoveStore I) (receiver := .storage daiRef)
      (retVar := "burnRet") (name := "burn")
      (target := daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)
      (sendVal := 0) (args := [sender, .var "wad"])
      (argVals := [.address evmVat.executionEnv.source, joinWadValue I])
      (out := outBurn) (perm := true) hdaiGuard hdai hburnArgs hcallBurn
  simpa [ExecTransitionBody, joinAfterMoveStore] using ExecFuncBody.execBlockRevert hblock

theorem daiJoinJoinDaiBurnSuccessAfterVatReturns (evm evmVat evmBurn : EVM.State)
    (I : ExecutionEnv) (outMove outBurn : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size)
    (hvatCode :
      Reasoning.Theory.uniswapExtCodeSizeWord evm.accountMap
        (daiJoinVatTargetWord evm.accountMap evm.executionEnv) ≠ ⟨0⟩)
    (hcallMove :
      typedCallViaEVM config evm
        (EVM.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) "move" 0
        [.address evm.executionEnv.codeOwner,
          .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
          .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)]
        (true, evmVat, outMove) true)
    (hdaiCode :
      Reasoning.Theory.uniswapExtCodeSizeWord evmVat.accountMap
        (daiJoinDaiTargetWord evmVat.accountMap evmVat.executionEnv) ≠ ⟨0⟩)
    (hcallBurn :
      typedCallViaEVM config evmVat
        (EVM.address (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)) "burn" 0
        [.address evmVat.executionEnv.source, joinWadValue I]
        (true, evmBurn, outBurn) true) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body
      (.returned
        { contract := contract,
          locals := (joinAfterMoveStore I).insert "burnRet" (collapseReturns []) }
        evmBurn none) := by
  have hmulStmt :=
    daiJoinJoinInternalMulReturns evm I hfit
  have hvat :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm (.storage vatRef) =
        .ok (.address (daiJoinVatAddress evm.accountMap evm.executionEnv)) :=
    evalExpr_daiJoinVatStorage (evm := evm) (locals := joinRadStore I)
      (joinRadStore_get_vat I)
  have hvatCodeNat :
      0 <
        (UInt256.ofNat
          ((evm.lookupAccount (daiJoinVatAddress evm.accountMap evm.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat :=
    daiJoinVatCode_pos_of_codeSize_ne_zero hvatCode
  have hvatGuard :
      evalExpr? config { contract := contract, locals := joinRadStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_daiJoinVatCodeGuard_true hvat hvatCodeNat
  have hmoveArgs :=
    evalExprs_daiJoinJoinVatMoveArgs evm I
  have hmoveDecode : config.externalABI.decode? "move" outMove = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hdai :
      evalExpr? config { contract := contract, locals := joinAfterMoveStore I } evmVat
        (.storage daiRef) =
        .ok (.address (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)) :=
    evalExpr_daiJoinDaiStorage (evm := evmVat) (locals := joinAfterMoveStore I)
      (joinAfterMoveStore_get_dai I)
  have hdaiCodeNat :
      0 <
        (UInt256.ofNat
          ((evmVat.lookupAccount (daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)).option 0
            (fun acc => acc.code.size))).toNat :=
    daiJoinDaiCode_pos_of_codeSize_ne_zero hdaiCode
  have hdaiGuard :
      evalExpr? config { contract := contract, locals := joinAfterMoveStore I } evmVat
        (.binary .gt (.extCodeSize (.storage daiRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_daiJoinDaiCodeGuard_true hdai hdaiCodeNat
  have hburnArgs :=
    evalExprs_daiJoinJoinDaiBurnArgs evmVat I
  have hburnDecode : config.externalABI.decode? "burn" outBurn = some [] := by
    simp [config, externalABI, decodeVoid?]
  have hblock :
      ExecBlock config { contract := contract, locals := joinStore I } evm
        joinTransition.body
        (.ok
          { contract := contract,
            locals := (joinAfterMoveStore I).insert "burnRet" (collapseReturns []) }
          evmBurn) := by
    simp only [joinTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
      List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
    refine ExecBlock.consNormal hmulStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
    refine ExecBlock.consNormal
      (ExecStmt.externalCallSuccess (sendVal := 0) (perm := true)
        hvat (by simp [evalExpr?, pure]) hmoveArgs hcallMove hmoveDecode) ?_
    exact checkedExternalCallSuccess
      (cfg := config) (C := contract) (evm := evmVat) (evm' := evmBurn)
      (locals := joinAfterMoveStore I) (receiver := .storage daiRef)
      (retVar := "burnRet") (name := "burn")
      (target := daiJoinDaiAddress evmVat.accountMap evmVat.executionEnv)
      (sendVal := 0) (args := [sender, .var "wad"])
      (argVals := [.address evmVat.executionEnv.source, joinWadValue I])
      (out := outBurn) (perm := true) (value := [])
      hdaiGuard hdai hburnArgs hcallBurn hburnDecode
  simpa [ExecTransitionBody, joinAfterMoveStore] using ExecFuncBody.execBlockOK hblock

theorem daiJoinJoinVatMoveCallFailedCore
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A I} {g sel gasWord : UInt256}
    {Ain : Substate} {out : ByteArray} {k C : ℕ}
    (hcode : I.code = daiJoinBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (daiJoinVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd580 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨580⟩
      (⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ_evm I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem)
      (UInt256.ofNat 8) out (cA', σ') k C)
    (hΘ :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', false, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ_evm σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I))
          (toExecute σ_evm (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (I.depth + 1) I.header I.perm)
    (hout : out.size < UInt256.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g) evmE := by
    simpa [evmE] using daiJoinJoinVatMoveCallFailed rd580 hout
  have hcodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (daiJoinVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
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
          ((joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true := by
    simpa [evmE, initState, hperm] using hΘ
  obtain ⟨σ'_solm, A'_solm, hcallSolm, _hAccounts'⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (daiJoinVatAddress σ_solm I))
      (targetWord := daiJoinVatTargetWord σ_evm I)
      (name := "move")
      (args := [.address I.codeOwner, .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
        .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)])
      (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain) (z := false)
      (out := out) (g'' := g'') (callGas := gasWord)
      (mem := joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := true)
      hdepthNe htgt
      (joinMoveEncode_eq I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem_size) hΘE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  have hbody :
      ExecTransitionBody config contract evmS (joinStore I) joinTransition.body .reverted := by
    simpa [evmS, initState] using
      (daiJoinJoinVatMoveCallFailedReverts
        (evm := evmS)
        (evmVat := { evmS with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
        (I := I) (out := out)
        (by simpa [evmS, initState] using hwv) hfit hcodeSizeSolm
        (by simpa [evmS, initState] using hcallSolm))
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem daiJoinJoinDaiBurnNoCodeCore
    {cA cA' gh bl σ_evm σ_solm σ' σ₀ A I} {g sel gasWord : UInt256}
    {Ain : Substate} {out : ByteArray} {k C : ℕ}
    (hcode : I.code = daiJoinBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size)
    (hvatCodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (daiJoinVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdaiCodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ' (daiJoinDaiTargetWord σ' I) = ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd598 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨598⟩
      (⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ_evm I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem)
      (UInt256.ofNat 8) out (cA', σ') k C)
    (hΘ :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', true, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ_evm σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I))
          (toExecute σ_evm (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (I.depth + 1) I.header I.perm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g) evmE := by
    simpa [evmE] using daiJoinJoinDaiBurnNoCode rd598 hdaiCodeSize
  have hvatCodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (daiJoinVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
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
          ((joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true := by
    simpa [evmE, initState, hperm] using hΘ
  obtain ⟨σ'_solm, A'_solm, hcallSolm, hAccounts'⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (daiJoinVatAddress σ_solm I))
      (targetWord := daiJoinVatTargetWord σ_evm I)
      (name := "move")
      (args := [.address I.codeOwner, .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
        .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)])
      (cA' := cA') (σ' := σ') (A' := A') (A_in := Ain) (z := true)
      (out := out) (g'' := g'') (callGas := gasWord)
      (mem := joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := true)
      hdepthNe htgt
      (joinMoveEncode_eq I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem_size) hΘE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  have hdaiCodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'_solm (daiJoinDaiTargetWord σ'_solm I) = ⟨0⟩ :=
    daiJoinDaiCodeSize_zero_accountMapEquiv hAccounts' hdaiCodeSize
  have hbody :
      ExecTransitionBody config contract evmS (joinStore I) joinTransition.body .reverted := by
    simpa [evmS, initState] using
      (daiJoinJoinDaiBurnNoCodeAfterVatReverts
        (evm := evmS)
        (evmVat := { evmS with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
        (I := I) (out := out)
        (by simpa [evmS, initState] using hwv) hfit hvatCodeSizeSolm
        (by simpa [evmS, initState] using hcallSolm)
        (by simpa [evmS, initState] using hdaiCodeSizeSolm))
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem daiJoinJoinDaiBurnCallFailedCore
    {cA cA' cA'' gh bl σ_evm σ_solm σ' σ'' σ₀ A I} {g sel gasWord burnGas : UInt256}
    {Ain burnAin : Substate} {out outBurn : ByteArray} {k C : ℕ}
    (hcode : I.code = daiJoinBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size)
    (hvatCodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (daiJoinVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdaiCodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ' (daiJoinDaiTargetWord σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd687 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨687⟩
      (⟨0⟩ :: ⟨196⟩ :: joinBurnSelectorPlainWord :: daiJoinDaiTargetWord σ' I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (joinBurnCalldataMem I
        (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem))
      (UInt256.ofNat 8) outBurn (cA'', σ'') k C)
    (hΘMove :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', true, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ_evm σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I))
          (toExecute σ_evm (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (I.depth + 1) I.header I.perm)
    (hΘBurn :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', false, outBurn) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl
          σ' σ₀ burnAin
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I))
          (toExecute σ' (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I)))
          burnGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((joinBurnCalldataMem I
            (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem)).readWithPadding
              128 68)
          (I.depth + 1) I.header I.perm)
    (houtBurn : outBurn.size < UInt256.size) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g) evmE := by
    simpa [evmE] using daiJoinJoinDaiBurnCallFailed rd687 houtBurn
  have hvatCodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (daiJoinVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
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
          ((joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true := by
    simpa [evmE, initState, hperm] using hΘMove
  obtain ⟨σ'_solm, AMove'_solm, hcallMoveSolm, hAccounts'⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (daiJoinVatAddress σ_solm I))
      (targetWord := daiJoinVatTargetWord σ_evm I)
      (name := "move")
      (args := [.address I.codeOwner, .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
        .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)])
      (cA' := cA') (σ' := σ') (A' := AMove') (A_in := Ain) (z := true)
      (out := out) (g'' := gMove'') (callGas := gasWord)
      (mem := joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := true)
      hdepthNe htgtMove
      (joinMoveEncode_eq I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem_size) hΘMoveE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  have hdaiCodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'_solm (daiJoinDaiTargetWord σ'_solm I) ≠ ⟨0⟩ :=
    daiJoinDaiCodeSize_ne_zero_accountMapEquiv hAccounts' hdaiCodeSize
  rcases hΘBurn with ⟨gBurn'', ABurn', hΘBurn⟩
  let evmVatE : EVM.State :=
    { evmE with accountMap := σ', substate := AMove', createdAccounts := cA' }
  let evmVatS : EVM.State :=
    { evmS with accountMap := σ'_solm, substate := AMove'_solm, createdAccounts := cA' }
  let evmVatSAligned : EVM.State := { evmVatS with substate := AMove' }
  have htgtBurn :
      EVM.address (daiJoinDaiAddress σ'_solm I) =
        AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I) :=
    daiJoinDaiEvmAddress_eq_target_of_accountMapEquiv hAccounts'
  have hΘBurnE :
      (cA'', σ'', gBurn'', ABurn', false, outBurn) =
        Ethereum.EVM.Θ evmVatE.executionEnv.blobVersionedHashes evmVatE.createdAccounts
          evmVatE.genesisBlockHeader evmVatE.blocks evmVatE.accountMap evmVatE.σ₀ burnAin
          (AccountAddress.ofUInt256 (UInt256.ofNat evmVatE.executionEnv.codeOwner))
          evmVatE.executionEnv.sender (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I))
          (toExecute evmVatE.accountMap (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I)))
          burnGas (UInt256.ofNat evmVatE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((joinBurnCalldataMem I
            (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem)).readWithPadding
              128 68)
          (evmVatE.executionEnv.depth + 1) evmVatE.executionEnv.header true := by
    simpa [evmVatE, evmE, initState, hperm] using hΘBurn
  have hburnMemSize :
      (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).size = 228 :=
    joinMoveCalldataMem_size I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem_size
  obtain ⟨σ''_solm, ABurn'_solm, hcallBurnAligned, _hAccounts''⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmVatE) (evm_solm := evmVatSAligned)
      (tgt := EVM.address (daiJoinDaiAddress σ'_solm I))
      (targetWord := daiJoinDaiTargetWord σ' I)
      (name := "burn")
      (args := [.address I.source, joinWadValue I])
      (cA' := cA'') (σ' := σ'') (A' := ABurn') (A_in := burnAin) (z := false)
      (out := outBurn) (g'' := gBurn'') (callGas := burnGas)
      (mem := joinBurnCalldataMem I
        (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem))
      (inOff := ⟨128⟩) (inSize := ⟨68⟩) (callPerm := true)
      (by simpa [evmVatE, evmE, initState] using hdepthNe) htgtBurn
      (joinBurnEncode_eq I hburnMemSize) hΘBurnE
      (by simpa [evmVatE, evmVatSAligned, evmVatS] using hAccounts')
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  have hcallBurnSolm :
      typedCallViaEVM config evmVatS
        (EVM.address (daiJoinDaiAddress σ'_solm I)) "burn" 0
        [.address evmVatS.executionEnv.source, joinWadValue I]
        (false,
          { evmVatS with
              accountMap := σ''_solm
              substate := ABurn'_solm
              createdAccounts := cA'' },
          outBurn) true := by
    simpa [evmVatSAligned] using
      (daiJoin_typedCallViaEVM_zero_substate_irrel
        (cfg := config) (evm := evmVatS) (A0 := AMove')
        (tgt := EVM.address (daiJoinDaiAddress σ'_solm I)) (name := "burn")
        (args := [.address evmVatS.executionEnv.source, joinWadValue I])
        (z := false) (out := outBurn) (callPerm := true)
        hcallBurnAligned
        (by simpa [evmVatS, evmS, initState] using hdepthNe))
  have hbody :
      ExecTransitionBody config contract evmS (joinStore I) joinTransition.body .reverted := by
    simpa [evmS, evmVatS, initState] using
      (daiJoinJoinDaiBurnCallFailedAfterVatReverts
        (evm := evmS) (evmVat := evmVatS)
        (evmBurn := { evmVatS with
          accountMap := σ''_solm
          substate := ABurn'_solm
          createdAccounts := cA'' })
        (I := I) (outMove := out) (outBurn := outBurn)
        (by simpa [evmS, initState] using hwv) hfit hvatCodeSizeSolm
        (by simpa [evmS, evmVatS, initState] using hcallMoveSolm)
        (by simpa [evmVatS, evmS, initState] using hdaiCodeSizeSolm)
        hcallBurnSolm)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem daiJoinJoinDaiBurnSuccessCore
    {cA cA' cA'' gh bl σ_evm σ_solm σ' σ'' σ₀ A I} {g sel gasWord burnGas : UInt256}
    {Ain burnAin : Substate} {out outBurn : ByteArray} {k C : ℕ}
    (hcode : I.code = daiJoinBytecode)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size)
    (hvatCodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_evm (daiJoinVatTargetWord σ_evm I) ≠ ⟨0⟩)
    (hdaiCodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ' (daiJoinDaiTargetWord σ' I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (rd687 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨687⟩
      (⟨1⟩ :: ⟨196⟩ :: joinBurnSelectorPlainWord :: daiJoinDaiTargetWord σ' I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (joinBurnCalldataMem I
        (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem))
      (UInt256.ofNat 8) outBurn (cA'', σ'') k C)
    (hΘMove :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA', σ', g'', A', true, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA gh bl
          σ_evm σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I))
          (toExecute σ_evm (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ_evm I)))
          gasWord (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (I.depth + 1) I.header I.perm)
    (hΘBurn :
      ∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', true, outBurn) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl
          σ' σ₀ burnAin
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I))
          (toExecute σ' (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I)))
          burnGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((joinBurnCalldataMem I
            (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem)).readWithPadding
              128 68)
          (I.depth + 1) I.header I.perm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmE := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  obtain ⟨_, _, rd705⟩ := daiJoinJoinDaiBurnCallSucceeded rd687
  have hmoveMemSize :
      (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).size = 228 :=
    joinMoveCalldataMem_size I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem_size
  have hmoveRead64 :
      (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    joinMoveCalldataMem_read64 I (daiJoinRadWord (joinWadWord I))
      solcFreePtrMem_size solcFreePtrMem_read64
  have hburnMemSize :
      (joinBurnCalldataMem I
        (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem)).size = 228 :=
    joinBurnCalldataMem_size I hmoveMemSize
  have hburnRead64 :
      (joinBurnCalldataMem I
        (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem)).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    joinBurnCalldataMem_read64 I hmoveMemSize hmoveRead64
  have hret : RDret daiJoinBytecode (Sat256.ofUInt256 g) evmE (cA'', σ'') ByteArray.empty := by
    simpa [evmE] using
      daiJoinJoinDaiBurnSuccessTail
        (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀)
        (σd := σ') (A := A) (I := I) (g := g) (sel := sel)
        (mem := joinBurnCalldataMem I
          (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem))
        (rdata := outBurn) (acc := (cA'', σ'')) hperm hburnMemSize hburnRead64
        (by simpa using rd705)
  have hvatCodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord σ_solm (daiJoinVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
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
          ((joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).readWithPadding
            128 100)
          (evmE.executionEnv.depth + 1) evmE.executionEnv.header true := by
    simpa [evmE, initState, hperm] using hΘMove
  obtain ⟨σ'_solm, AMove'_solm, hcallMoveSolm, hAccounts'⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmE) (evm_solm := evmS)
      (tgt := EVM.address (daiJoinVatAddress σ_solm I))
      (targetWord := daiJoinVatTargetWord σ_evm I)
      (name := "move")
      (args := [.address I.codeOwner, .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
        .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)])
      (cA' := cA') (σ' := σ') (A' := AMove') (A_in := Ain) (z := true)
      (out := out) (g'' := gMove'') (callGas := gasWord)
      (mem := joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem)
      (inOff := ⟨128⟩) (inSize := ⟨100⟩) (callPerm := true)
      hdepthNe htgtMove
      (joinMoveEncode_eq I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem_size) hΘMoveE
      (by simpa [evmE, evmS, initState] using hAccounts)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  have hdaiCodeSizeSolm :
      Reasoning.Theory.uniswapExtCodeSizeWord σ'_solm (daiJoinDaiTargetWord σ'_solm I) ≠ ⟨0⟩ :=
    daiJoinDaiCodeSize_ne_zero_accountMapEquiv hAccounts' hdaiCodeSize
  rcases hΘBurn with ⟨gBurn'', ABurn', hΘBurn⟩
  let evmVatE : EVM.State :=
    { evmE with accountMap := σ', substate := AMove', createdAccounts := cA' }
  let evmVatS : EVM.State :=
    { evmS with accountMap := σ'_solm, substate := AMove'_solm, createdAccounts := cA' }
  let evmVatSAligned : EVM.State := { evmVatS with substate := AMove' }
  have htgtBurn :
      EVM.address (daiJoinDaiAddress σ'_solm I) =
        AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I) :=
    daiJoinDaiEvmAddress_eq_target_of_accountMapEquiv hAccounts'
  have hΘBurnE :
      (cA'', σ'', gBurn'', ABurn', true, outBurn) =
        Ethereum.EVM.Θ evmVatE.executionEnv.blobVersionedHashes evmVatE.createdAccounts
          evmVatE.genesisBlockHeader evmVatE.blocks evmVatE.accountMap evmVatE.σ₀ burnAin
          (AccountAddress.ofUInt256 (UInt256.ofNat evmVatE.executionEnv.codeOwner))
          evmVatE.executionEnv.sender (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I))
          (toExecute evmVatE.accountMap (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I)))
          burnGas (UInt256.ofNat evmVatE.executionEnv.gasPrice) ⟨0⟩ ⟨0⟩
          ((joinBurnCalldataMem I
            (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem)).readWithPadding
              128 68)
          (evmVatE.executionEnv.depth + 1) evmVatE.executionEnv.header true := by
    simpa [evmVatE, evmE, initState, hperm] using hΘBurn
  obtain ⟨σ''_solm, ABurn'_solm, hcallBurnAligned, hAccounts''⟩ :=
    typedCallViaEVM_callMade_accountMapEquiv
      (cfg := config) (evm_evm := evmVatE) (evm_solm := evmVatSAligned)
      (tgt := EVM.address (daiJoinDaiAddress σ'_solm I))
      (targetWord := daiJoinDaiTargetWord σ' I)
      (name := "burn")
      (args := [.address I.source, joinWadValue I])
      (cA' := cA'') (σ' := σ'') (A' := ABurn') (A_in := burnAin) (z := true)
      (out := outBurn) (g'' := gBurn'') (callGas := burnGas)
      (mem := joinBurnCalldataMem I
        (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem))
      (inOff := ⟨128⟩) (inSize := ⟨68⟩) (callPerm := true)
      (by simpa [evmVatE, evmE, initState] using hdepthNe) htgtBurn
      (joinBurnEncode_eq I hmoveMemSize) hΘBurnE
      (by simpa [evmVatE, evmVatSAligned, evmVatS] using hAccounts')
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
      (by rfl)
  have hcallBurnSolm :
      typedCallViaEVM config evmVatS
        (EVM.address (daiJoinDaiAddress σ'_solm I)) "burn" 0
        [.address evmVatS.executionEnv.source, joinWadValue I]
        (true,
          { evmVatS with
              accountMap := σ''_solm
              substate := ABurn'_solm
              createdAccounts := cA'' },
          outBurn) true := by
    simpa [evmVatSAligned] using
      (daiJoin_typedCallViaEVM_zero_substate_irrel
        (cfg := config) (evm := evmVatS) (A0 := AMove')
        (tgt := EVM.address (daiJoinDaiAddress σ'_solm I)) (name := "burn")
        (args := [.address evmVatS.executionEnv.source, joinWadValue I])
        (z := true) (out := outBurn) (callPerm := true)
        hcallBurnAligned
        (by simpa [evmVatS, evmS, initState] using hdepthNe))
  let evmBurnS : EVM.State :=
    { evmVatS with accountMap := σ''_solm, substate := ABurn'_solm, createdAccounts := cA'' }
  have hbody :
      ExecTransitionBody config contract evmS (joinStore I) joinTransition.body
        (.returned
          { contract := contract,
            locals := (joinAfterMoveStore I).insert "burnRet" (collapseReturns []) }
          evmBurnS none) := by
    simpa [evmS, evmVatS, evmBurnS, initState] using
      (daiJoinJoinDaiBurnSuccessAfterVatReturns
        (evm := evmS) (evmVat := evmVatS) (evmBurn := evmBurnS)
        (I := I) (outMove := out) (outBurn := outBurn)
        (by simpa [evmS, initState] using hwv) hfit hvatCodeSizeSolm
        (by simpa [evmS, evmVatS, initState] using hcallMoveSolm)
        (by simpa [evmVatS, evmS, initState] using hdaiCodeSizeSolm)
        hcallBurnSolm)
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by rfl)
    (by simpa [evmBurnS] using hAccounts'')
    (by
      simpa [joinTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem daiJoinJoinBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = daiJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (daiJoinSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (daiJoinSelBytes 4) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some joinTransition :=
    daiJoinDispatchJoin hsel
  have hreach := daiJoinReachJoinBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := daiJoinDecode_join_ok hsz68
    obtain ⟨_, _, rd449⟩ := daiJoinJoinX_decoded
      (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    by_cases hwad : joinWadWord I = ⟨0⟩
    · have hmulOk :
          joinWadWord I = ⟨0⟩ ∨
            UInt256.div (daiJoinRadWord (joinWadWord I)) (joinWadWord I) =
              daiJoinONEWord :=
        Or.inl hwad
      obtain ⟨_, _, rd490⟩ := daiJoinJoinMulSuccess hmulOk rd449
      have hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size := by
        rw [hwad]
        native_decide
      by_cases hvatCode :
          Reasoning.Theory.uniswapExtCodeSizeWord σ_evm
            (daiJoinVatTargetWord σ_evm I) = ⟨0⟩
      · have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
          daiJoinJoinVatMoveNoCode rd490 hvatCode
        have hvatCodeSolm :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
              (daiJoinVatTargetWord σ_solm I) = ⟨0⟩ :=
          daiJoinVatCodeSize_zero_accountMapEquiv hAccounts hvatCode
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (joinStore I)
              joinTransition.body .reverted :=
          daiJoinJoinVatNoCodeReverts
            (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simpa [initState] using hwv) hfit
            (by simpa [initState] using hvatCodeSolm)
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · obtain ⟨_, _, _, rd579⟩ :=
          daiJoinJoinVatMoveCallReady rd490 hvatCode
        by_cases hdepthLt : I.depth.val < 1024
        · obtain ⟨cA', σ', z, out, Ain, gasWord, k', C', hΘ, rd580, hout⟩ :=
            daiJoinJoinVatMovePostCall rd579 hdepthLt
          cases z
          · exact daiJoinJoinVatMoveCallFailedCore
              (cA := cA) (cA' := cA') (gh := gh) (bl := bl)
              (σ_evm := σ_evm) (σ_solm := σ_solm) (σ' := σ')
              (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := daiJoinSelWord I)
              (gasWord := gasWord) (Ain := Ain) (out := out) (k := k') (C := C')
              hcode hperm hwv hdispatch hdecode hAccounts hfit hvatCode hdepthLt
              (by simpa using rd580) hΘ hout
          · obtain ⟨_, _, rd598⟩ :=
              daiJoinJoinVatMoveCallSucceeded (by simpa using rd580)
            by_cases hdaiCode :
                Reasoning.Theory.uniswapExtCodeSizeWord σ'
                  (daiJoinDaiTargetWord σ' I) = ⟨0⟩
            · exact daiJoinJoinDaiBurnNoCodeCore
                (cA := cA) (cA' := cA') (gh := gh) (bl := bl)
                (σ_evm := σ_evm) (σ_solm := σ_solm) (σ' := σ')
                (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := daiJoinSelWord I)
                (gasWord := gasWord) (Ain := Ain) (out := out)
                hcode hperm hwv hdispatch hdecode hAccounts hfit hvatCode hdaiCode hdepthLt
                (by simpa using rd598) hΘ
            · obtain ⟨_burnGasWord, _, _, rd686⟩ :=
                daiJoinJoinDaiBurnCallReady (by simpa using rd598) hdaiCode
              obtain ⟨cA'', σ'', zBurn, outBurn, burnAin, burnCallGas, kBurn, CBurn,
                  hΘBurn, rd687, houtBurn⟩ :=
                daiJoinJoinDaiBurnPostCall rd686 hdepthLt
              cases zBurn
              · exact daiJoinJoinDaiBurnCallFailedCore
                  (cA := cA) (cA' := cA') (cA'' := cA'') (gh := gh) (bl := bl)
                  (σ_evm := σ_evm) (σ_solm := σ_solm) (σ' := σ') (σ'' := σ'')
                  (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := daiJoinSelWord I)
                  (gasWord := gasWord) (burnGas := burnCallGas)
                  (Ain := Ain) (burnAin := burnAin) (out := out) (outBurn := outBurn)
                  (k := kBurn) (C := CBurn)
                  hcode hperm hwv hdispatch hdecode hAccounts hfit hvatCode hdaiCode
                  hdepthLt (by simpa using rd687) hΘ hΘBurn houtBurn
              · exact daiJoinJoinDaiBurnSuccessCore
                  (cA := cA) (cA' := cA') (cA'' := cA'') (gh := gh) (bl := bl)
                  (σ_evm := σ_evm) (σ_solm := σ_solm) (σ' := σ') (σ'' := σ'')
                  (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := daiJoinSelWord I)
                  (gasWord := gasWord) (burnGas := burnCallGas)
                  (Ain := Ain) (burnAin := burnAin) (out := out) (outBurn := outBurn)
                  (k := kBurn) (C := CBurn)
                  hcode hperm hwv hdispatch hdecode hAccounts hfit hvatCode hdaiCode
                  hdepthLt (by simpa using rd687) hΘ hΘBurn
        · have hdepthEq : I.depth = 1024 := by
            apply Fin.ext
            have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
            have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepthLt
            omega
          obtain ⟨_, _, rd580⟩ := daiJoinJoinVatMoveCallDepthLimit rd579 hdepthEq
          have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
            daiJoinJoinVatMoveCallFailed rd580 (by simp [UInt256.size])
          let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          have hvatCodeSolm :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                (daiJoinVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
            daiJoinVatCodeSize_ne_zero_accountMapEquiv hAccounts hvatCode
          have hcallSolm :
              typedCallViaEVM config evmS
                (EVM.address (daiJoinVatAddress σ_solm I)) "move" 0
                [.address I.codeOwner,
                  .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
                  .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)]
                (false,
                  { evmS with
                    substate :=
                      (evmS.addAccessedAccount (EVM.address (daiJoinVatAddress σ_solm I))).substate },
                  ByteArray.empty) true := by
            exact callNotMade_depthLimit
              (cfg := config) (evm := evmS)
              (tgt := EVM.address (daiJoinVatAddress σ_solm I))
              (name := "move")
              (args := [.address I.codeOwner,
                .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
                .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)])
              (calldata :=
                (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).readWithPadding
                  128 100)
              (callPerm := true)
              (joinMoveEncode_eq I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem_size)
              (by simpa [evmS, initState] using hdepthEq)
          have hbody :
              ExecTransitionBody config contract evmS (joinStore I) joinTransition.body .reverted :=
            daiJoinJoinVatMoveCallFailedReverts
              (evm := evmS)
              (evmVat :=
                { evmS with
                  substate :=
                    (evmS.addAccessedAccount (EVM.address (daiJoinVatAddress σ_solm I))).substate })
              (I := I) (out := ByteArray.empty)
              (by simpa [evmS, initState] using hwv) hfit hvatCodeSolm
              (by simpa [evmS, initState] using hcallSolm)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · by_cases hguard :
        UInt256.div (daiJoinRadWord (joinWadWord I)) (joinWadWord I) = daiJoinONEWord
      · have hmulOk :
            joinWadWord I = ⟨0⟩ ∨
              UInt256.div (daiJoinRadWord (joinWadWord I)) (joinWadWord I) =
                daiJoinONEWord :=
          Or.inr hguard
        obtain ⟨_, _, rd490⟩ := daiJoinJoinMulSuccess hmulOk rd449
        have hfit : daiJoinONEWord.toNat * (joinWadWord I).toNat < UInt256.size :=
          daiJoinMulFit_of_guard hguard
        by_cases hvatCode :
            Reasoning.Theory.uniswapExtCodeSizeWord σ_evm
              (daiJoinVatTargetWord σ_evm I) = ⟨0⟩
        · have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g)
              (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
            daiJoinJoinVatMoveNoCode rd490 hvatCode
          have hvatCodeSolm :
              Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                (daiJoinVatTargetWord σ_solm I) = ⟨0⟩ :=
            daiJoinVatCodeSize_zero_accountMapEquiv hAccounts hvatCode
          have hbody :
              ExecTransitionBody config contract
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (joinStore I)
                joinTransition.body .reverted :=
            daiJoinJoinVatNoCodeReverts
              (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
              (by simpa [initState] using hwv) hfit
              (by simpa [initState] using hvatCodeSolm)
          exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
        · obtain ⟨_, _, _, rd579⟩ :=
            daiJoinJoinVatMoveCallReady rd490 hvatCode
          by_cases hdepthLt : I.depth.val < 1024
          · obtain ⟨cA', σ', z, out, Ain, gasWord, k', C', hΘ, rd580, hout⟩ :=
              daiJoinJoinVatMovePostCall rd579 hdepthLt
            cases z
            · exact daiJoinJoinVatMoveCallFailedCore
                (cA := cA) (cA' := cA') (gh := gh) (bl := bl)
                (σ_evm := σ_evm) (σ_solm := σ_solm) (σ' := σ')
                (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := daiJoinSelWord I)
                (gasWord := gasWord) (Ain := Ain) (out := out) (k := k') (C := C')
                hcode hperm hwv hdispatch hdecode hAccounts hfit hvatCode hdepthLt
                (by simpa using rd580) hΘ hout
            · obtain ⟨_, _, rd598⟩ :=
                daiJoinJoinVatMoveCallSucceeded (by simpa using rd580)
              by_cases hdaiCode :
                  Reasoning.Theory.uniswapExtCodeSizeWord σ'
                    (daiJoinDaiTargetWord σ' I) = ⟨0⟩
              · exact daiJoinJoinDaiBurnNoCodeCore
                  (cA := cA) (cA' := cA') (gh := gh) (bl := bl)
                  (σ_evm := σ_evm) (σ_solm := σ_solm) (σ' := σ')
                  (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := daiJoinSelWord I)
                  (gasWord := gasWord) (Ain := Ain) (out := out)
                  hcode hperm hwv hdispatch hdecode hAccounts hfit hvatCode hdaiCode hdepthLt
                  (by simpa using rd598) hΘ
              · obtain ⟨_burnGasWord, _, _, rd686⟩ :=
                  daiJoinJoinDaiBurnCallReady (by simpa using rd598) hdaiCode
                obtain ⟨cA'', σ'', zBurn, outBurn, burnAin, burnCallGas, kBurn, CBurn,
                    hΘBurn, rd687, houtBurn⟩ :=
                  daiJoinJoinDaiBurnPostCall rd686 hdepthLt
                cases zBurn
                · exact daiJoinJoinDaiBurnCallFailedCore
                    (cA := cA) (cA' := cA') (cA'' := cA'') (gh := gh) (bl := bl)
                    (σ_evm := σ_evm) (σ_solm := σ_solm) (σ' := σ') (σ'' := σ'')
                    (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := daiJoinSelWord I)
                    (gasWord := gasWord) (burnGas := burnCallGas)
                    (Ain := Ain) (burnAin := burnAin) (out := out) (outBurn := outBurn)
                    (k := kBurn) (C := CBurn)
                    hcode hperm hwv hdispatch hdecode hAccounts hfit hvatCode hdaiCode
                    hdepthLt (by simpa using rd687) hΘ hΘBurn houtBurn
                · exact daiJoinJoinDaiBurnSuccessCore
                    (cA := cA) (cA' := cA') (cA'' := cA'') (gh := gh) (bl := bl)
                    (σ_evm := σ_evm) (σ_solm := σ_solm) (σ' := σ') (σ'' := σ'')
                    (σ₀ := σ₀) (A := A) (I := I) (g := g) (sel := daiJoinSelWord I)
                    (gasWord := gasWord) (burnGas := burnCallGas)
                    (Ain := Ain) (burnAin := burnAin) (out := out) (outBurn := outBurn)
                    (k := kBurn) (C := CBurn)
                    hcode hperm hwv hdispatch hdecode hAccounts hfit hvatCode hdaiCode
                    hdepthLt (by simpa using rd687) hΘ hΘBurn
          · have hdepthEq : I.depth = 1024 := by
              apply Fin.ext
              have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
              have hge : 1024 ≤ I.depth.val := Nat.le_of_not_gt hdepthLt
              omega
            obtain ⟨_, _, rd580⟩ := daiJoinJoinVatMoveCallDepthLimit rd579 hdepthEq
            have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g)
                (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
              daiJoinJoinVatMoveCallFailed rd580 (by simp [UInt256.size])
            let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            have hvatCodeSolm :
                Reasoning.Theory.uniswapExtCodeSizeWord σ_solm
                  (daiJoinVatTargetWord σ_solm I) ≠ ⟨0⟩ :=
              daiJoinVatCodeSize_ne_zero_accountMapEquiv hAccounts hvatCode
            have hcallSolm :
                typedCallViaEVM config evmS
                  (EVM.address (daiJoinVatAddress σ_solm I)) "move" 0
                  [.address I.codeOwner,
                    .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
                    .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)]
                  (false,
                    { evmS with
                      substate :=
                        (evmS.addAccessedAccount (EVM.address (daiJoinVatAddress σ_solm I))).substate },
                    ByteArray.empty) true := by
              exact callNotMade_depthLimit
                (cfg := config) (evm := evmS)
                (tgt := EVM.address (daiJoinVatAddress σ_solm I))
                (name := "move")
                (args := [.address I.codeOwner,
                  .address (AccountAddress.ofUInt256 (joinUsrMaskedWord I)),
                  .int (Int.ofNat (daiJoinRadWord (joinWadWord I)).toNat)])
                (calldata :=
                  (joinMoveCalldataMem I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem).readWithPadding
                    128 100)
                (callPerm := true)
                (joinMoveEncode_eq I (daiJoinRadWord (joinWadWord I)) solcFreePtrMem_size)
                (by simpa [evmS, initState] using hdepthEq)
            have hbody :
                ExecTransitionBody config contract evmS (joinStore I) joinTransition.body .reverted :=
              daiJoinJoinVatMoveCallFailedReverts
                (evm := evmS)
                (evmVat :=
                  { evmS with
                    substate :=
                      (evmS.addAccessedAccount (EVM.address (daiJoinVatAddress σ_solm I))).substate })
                (I := I) (out := ByteArray.empty)
                (by simpa [evmS, initState] using hwv) hfit hvatCodeSolm
                (by simpa [evmS, initState] using hcallSolm)
            exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hrev : RDrev daiJoinBytecode (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
          daiJoinJoinMulReverts hwad hguard rd449
        have hbody :
            ExecTransitionBody config contract
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) (joinStore I)
              joinTransition.body .reverted :=
          daiJoinJoinBodyMulReverts
            (evm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I
            (by simpa [initState] using hwv) hwad hguard
        exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hdecode := daiJoinDecode_join_none_short hsz4 (by omega)
    exact (daiJoinJoinX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize (by omega) hreach)
      |>.reEquivDecodingFailed hcode hdispatch hdecode

end Benchmarks.Dss.DaiJoin
