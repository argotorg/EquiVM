import Benchmarks.Dss.DaiJoin.Join

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.DaiJoin

/-! ## `exit(address,uint256)` -/

abbrev exitUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev exitUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (exitUsrWord I)

abbrev exitWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev exitUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (exitUsrWord I).toNat)

abbrev exitWadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (exitWadWord I).toNat)

abbrev exitStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "usr" (exitUsrValue I)).insert "wad" (exitWadValue I)

def exitLiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  daiJoinSlotWord ⟨3⟩ σ I

abbrev exitRadStore (I : ExecutionEnv) : Store :=
  (exitStore I).insert "rad" (.int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat))

abbrev exitAfterMoveStore (I : ExecutionEnv) : Store :=
  (exitRadStore I).insert "moveRet" (collapseReturns [])

theorem exitStore_get_wad (I : ExecutionEnv) :
    (exitStore I).get? "wad" = some (exitWadValue I) := by
  rw [exitStore, store_get_self]

theorem exitStore_get_live (I : ExecutionEnv) :
    (exitStore I).get? "live" = none := by
  rw [exitStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem exitRadStore_get_vat (I : ExecutionEnv) :
    (exitRadStore I).get? "vat" = none := by
  rw [exitRadStore, store_get_ne _ _ (by decide), exitStore,
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem exitRadStore_get_rad (I : ExecutionEnv) :
    (exitRadStore I).get? "rad" =
      some (.int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)) := by
  rw [exitRadStore, store_get_self]

theorem exitRadStore_get_usr (I : ExecutionEnv) :
    (exitRadStore I).get? "usr" = some (exitUsrValue I) := by
  rw [exitRadStore, store_get_ne _ _ (by decide), exitStore,
    store_get_ne _ _ (by decide), store_get_self]

theorem exitAfterMoveStore_get_dai (I : ExecutionEnv) :
    (exitAfterMoveStore I).get? "dai" = none := by
  rw [exitAfterMoveStore, store_get_ne _ _ (by decide), exitRadStore,
    store_get_ne _ _ (by decide), exitStore, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem exitAfterMoveStore_get_wad (I : ExecutionEnv) :
    (exitAfterMoveStore I).get? "wad" = some (exitWadValue I) := by
  rw [exitAfterMoveStore, store_get_ne _ _ (by decide), exitRadStore,
    store_get_ne _ _ (by decide), exitStore, store_get_self]

theorem exitAfterMoveStore_get_usr (I : ExecutionEnv) :
    (exitAfterMoveStore I).get? "usr" = some (exitUsrValue I) := by
  rw [exitAfterMoveStore, store_get_ne _ _ (by decide), exitRadStore,
    store_get_ne _ _ (by decide), exitStore, store_get_ne _ _ (by decide),
    store_get_self]

theorem exitUsrValue_eq_masked (I : ExecutionEnv) :
    exitUsrValue I = .address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)) := by
  rw [exitUsrValue, accountAddress_ofUInt256_eq_ofNat_toNat]
  simpa [exitUsrMaskedWord] using solcAddressValue_masked (exitUsrWord I)

theorem evalExpr_daiJoinLiveStorage {evm : EVM.State} {locals : Store}
    (hlive : locals.get? "live" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage liveRef) =
      .ok (.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat)) := by
  exact evalExpr_storage_scalar_value
    (cfg := config) (solm := { contract := contract, locals := locals }) (evm := evm)
    (slot := liveRef) (er := ({ base := "live", steps := [] } : EvaledStorageRef))
    (t := .int uint256Int) (loc := wordLoc ⟨3⟩)
    (value := .int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat))
    hlive
    (by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (by rfl)
    (by
      simpa [exitLiveWord, daiJoinSlotWord] using
        daiJoinStorageLocLoad_uint256 evm ⟨3⟩)

theorem evalExpr_daiJoinLiveGuard_false {evm : EVM.State} {locals : Store}
    (hlive :
      evalExpr? config { contract := contract, locals := locals } evm (.storage liveRef) =
        .ok (.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat)))
    (hnotLive : exitLiveWord evm.accountMap evm.executionEnv ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) =
        .ok (.bool false) := by
  have hne :
      Value.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat) ≠
        Value.int 1 := by
    intro h
    rw [Value.int.injEq] at h
    apply hnotLive
    apply u256_inj
    simpa using Int.ofNat.inj h
  have hbeq :
      (Value.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat) ==
        Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hlive, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_daiJoinLiveGuard_true {evm : EVM.State} {locals : Store}
    (hlive :
      evalExpr? config { contract := contract, locals := locals } evm (.storage liveRef) =
        .ok (.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat)))
    (hliveOne : exitLiveWord evm.accountMap evm.executionEnv = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) =
        .ok (.bool true) := by
  have hbeq :
      (Value.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat) ==
        Value.int 1) = true := by
    rw [hliveOne]
    rfl
  simp only [evalExpr?, hlive, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat (exitLiveWord evm.accountMap evm.executionEnv).toNat))
      (Value.int 1) = .ok (.bool true)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExprs_daiJoinExitMulArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := exitStore I } evm
      [.intLit ONE, .var "wad"] =
        .ok [.int (Int.ofNat daiJoinONEWord.toNat), exitWadValue I] := by
  have hOne :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.intLit ONE) =
        .ok (.int (Int.ofNat daiJoinONEWord.toNat)) := by
    simp [evalExpr?, pure, daiJoinONE_eq_ONEWord_toNat]
  have hWad :
      evalExpr? config { contract := contract, locals := exitStore I } evm (.var "wad") =
        .ok (exitWadValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((exitStore I).get? "wad") =
      .ok (exitWadValue I)
    rw [exitStore_get_wad]
    rfl
  simp [evalExprs?, hOne, hWad, EvalResult.bind, bind, pure]

theorem daiJoinExitInternalMulReturns (evm : EVM.State) (I : ExecutionEnv)
    (hfit : daiJoinONEWord.toNat * (exitWadWord I).toNat < UInt256.size) :
    ExecStmt config { contract := contract, locals := exitStore I } evm
      (.internalCall "mul" [.intLit ONE, .var "wad"] "rad")
      (.ok { contract := contract, locals := exitRadStore I } evm) := by
  have hlookupMul : lookupCallable? contract "mul" = some mulFunction.toCallable := by
    rfl
  have hbindMul :
      bindParams? mulFunction.params
          [.int (Int.ofNat daiJoinONEWord.toNat), exitWadValue I] =
        some (daiJoinUintBinaryLocals daiJoinONEWord (exitWadWord I)) := by
    simp [mulFunction, uint256, bindParams?, daiJoinUintBinaryLocals, exitWadValue]
  have hbody :=
    execDaiJoinMulFunctionReturn evm
      (x := daiJoinONEWord) (y := exitWadWord I)
      (prod := daiJoinRadWord (exitWadWord I)) rfl hfit
  have hstmt :=
    internalCallFunctionReturn
      (cfg := config)
      (caller := Frame.mk contract (exitStore I))
      (evm := evm) (calleeEvm := evm)
      (name := "mul") (retVar := "rad")
      (args := [.intLit ONE, .var "wad"])
      (argVals := [.int (Int.ofNat daiJoinONEWord.toNat), exitWadValue I])
      (callee := mulFunction)
      (locals := daiJoinUintBinaryLocals daiJoinONEWord (exitWadWord I))
      (calleeSolm :=
        { contract := contract,
          locals := daiJoinUintBinaryLocalsZ daiJoinONEWord (exitWadWord I)
            (daiJoinRadWord (exitWadWord I)) })
      (value := some [.int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)])
      (evalExprs_daiJoinExitMulArgs evm I) hlookupMul hbindMul hbody
  simpa [exitRadStore, resumeAfterInternalCall, collapseReturns] using hstmt

theorem evalExprs_daiJoinExitVatMoveArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := exitRadStore I } evm
      [sender, thisAddr, .var "rad"] =
        .ok [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
          .int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)] := by
  have hSender :
      evalExpr? config { contract := contract, locals := exitRadStore I } evm sender =
        .ok (.address evm.executionEnv.source) := by
    simp [sender, evalExpr?, envValue, pure]
  have hThis :
      evalExpr? config { contract := contract, locals := exitRadStore I } evm thisAddr =
        .ok (.address evm.executionEnv.codeOwner) := by
    simp [thisAddr, evalExpr?, envValue, pure]
  have hRad :
      evalExpr? config { contract := contract, locals := exitRadStore I } evm (.var "rad") =
        .ok (.int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((exitRadStore I).get? "rad") =
      .ok (.int (Int.ofNat (daiJoinRadWord (exitWadWord I)).toNat))
    rw [exitRadStore_get_rad]
    rfl
  simp [evalExprs?, hSender, hThis, hRad, EvalResult.bind, bind, pure]

theorem evalExprs_daiJoinExitDaiMintArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := exitAfterMoveStore I } evm
      [.var "usr", .var "wad"] =
        .ok [.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)), exitWadValue I] := by
  have hUsr :
      evalExpr? config { contract := contract, locals := exitAfterMoveStore I } evm (.var "usr") =
        .ok (.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I))) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((exitAfterMoveStore I).get? "usr") =
      .ok (.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)))
    rw [exitAfterMoveStore_get_usr, exitUsrValue_eq_masked]
    rfl
  have hWad :
      evalExpr? config { contract := contract, locals := exitAfterMoveStore I } evm (.var "wad") =
        .ok (exitWadValue I) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable ((exitAfterMoveStore I).get? "wad") =
      .ok (exitWadValue I)
    rw [exitAfterMoveStore_get_wad]
    rfl
  simp [evalExprs?, hUsr, hWad, EvalResult.bind, bind, pure]

noncomputable def exitMoveSenderMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (solcSourceWord I).toByteArray.write 0 (joinMoveSelectorMem mem) 132 32

noncomputable def exitMoveThisMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0 (exitMoveSenderMem I mem) 164 32

noncomputable def exitMoveCalldataMem (I : ExecutionEnv) (rad : UInt256)
    (mem : ByteArray) : ByteArray :=
  rad.toByteArray.write 0 (exitMoveThisMem I mem) 196 32

theorem exitMoveSenderMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96) :
    (exitMoveSenderMem I mem).size = 164 := by
  unfold exitMoveSenderMem
  exact toByteArray_write32_size_of_le (joinMoveSelectorMem mem) (solcSourceWord I)
    132 160 164 (joinMoveSelectorMem_size hmem)
    (by rw [joinMoveSelectorMem_size hmem]; omega) (by omega)

theorem exitMoveThisMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 96) :
    (exitMoveThisMem I mem).size = 196 := by
  unfold exitMoveThisMem
  exact toByteArray_write32_size_of_le (exitMoveSenderMem I mem)
    (UInt256.ofNat I.codeOwner.val) 164 164 196 (exitMoveSenderMem_size I hmem)
    (by rw [exitMoveSenderMem_size I hmem]) (by omega)

theorem exitMoveCalldataMem_size (I : ExecutionEnv) (rad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (exitMoveCalldataMem I rad mem).size = 228 := by
  unfold exitMoveCalldataMem
  exact toByteArray_write32_size_of_le (exitMoveThisMem I mem) rad
    196 196 228 (exitMoveThisMem_size I hmem)
    (by rw [exitMoveThisMem_size I hmem]) (by omega)

theorem exitMoveSenderMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (exitMoveSenderMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold exitMoveSenderMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [joinMoveSelectorMem_size hmem]; omega) (by omega)]
  exact joinMoveSelectorMem_read64 hmem hread64

theorem exitMoveThisMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (exitMoveThisMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold exitMoveThisMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [exitMoveSenderMem_size I hmem]) (by norm_num)]
  exact exitMoveSenderMem_read64 I hmem hread64

theorem exitMoveCalldataMem_read64 (I : ExecutionEnv) (rad : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (exitMoveCalldataMem I rad mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold exitMoveCalldataMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [exitMoveThisMem_size I hmem]) (by omega)]
  exact exitMoveThisMem_read64 I hmem hread64

theorem exitMoveCalldataMem_read128_100 (I : ExecutionEnv) (rad : UInt256)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (exitMoveCalldataMem I rad mem).readWithPadding 128 100 =
      vatMoveSelector ++ (solcSourceWord I).toByteArray ++
        (UInt256.ofNat I.codeOwner.val).toByteArray ++ rad.toByteArray := by
  let final := exitMoveCalldataMem I rad mem
  have hfinalSize : final.size = 228 := by
    dsimp [final]
    exact exitMoveCalldataMem_size I rad hmem
  have hselectorRead : final.readWithPadding 128 4 = vatMoveSelector := by
    dsimp [final]
    unfold exitMoveCalldataMem
    rw [write32_read_below_len _ _ 196 128 4 (by rw [toByteArray_size])
      (by rw [exitMoveThisMem_size I hmem]) (by omega)
      (by rw [exitMoveThisMem_size I hmem]; omega) (by omega) (by norm_num)]
    unfold exitMoveThisMem
    rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
      (by rw [exitMoveSenderMem_size I hmem]) (by omega)
      (by rw [exitMoveSenderMem_size I hmem]; omega) (by omega) (by norm_num)]
    unfold exitMoveSenderMem
    rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by rw [joinMoveSelectorMem_size hmem]; omega) (by omega)
      (by rw [joinMoveSelectorMem_size hmem]; omega) (by omega) (by norm_num)]
    unfold joinMoveSelectorMem
    rw [toByteArray_write_read_window_of_gap joinMoveSelectorShiftedWord mem 128 0 4
      (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
    unfold joinMoveSelectorShiftedWord joinMoveSelectorPlainWord vatMoveSelector selectorBytes
    native_decide
  have hsenderRead :
      final.readWithPadding 132 32 = (solcSourceWord I).toByteArray := by
    dsimp [final]
    unfold exitMoveCalldataMem
    rw [write32_read_below_len _ _ 196 132 32 (by rw [toByteArray_size])
      (by rw [exitMoveThisMem_size I hmem]) (by omega)
      (by rw [exitMoveThisMem_size I hmem]; omega) (by omega) (by norm_num)]
    unfold exitMoveThisMem
    rw [write32_read_below_len _ _ 164 132 32 (by rw [toByteArray_size])
      (by rw [exitMoveSenderMem_size I hmem]) (by omega)
      (by rw [exitMoveSenderMem_size I hmem]) (by omega) (by norm_num)]
    unfold exitMoveSenderMem
    rw [write32_read_prefix_len _ _ 132 32 (by rw [toByteArray_size])
      (by rw [joinMoveSelectorMem_size hmem]; omega) (by omega) (by omega)
      (by norm_num)]
    rw [toByteArray_extract_all]
  have hthisRead :
      final.readWithPadding 164 32 = (UInt256.ofNat I.codeOwner.val).toByteArray := by
    dsimp [final]
    unfold exitMoveCalldataMem
    rw [write32_read_below_len _ _ 196 164 32 (by rw [toByteArray_size])
      (by rw [exitMoveThisMem_size I hmem]) (by omega)
      (by rw [exitMoveThisMem_size I hmem]) (by omega) (by norm_num)]
    unfold exitMoveThisMem
    rw [write32_read_prefix_len _ _ 164 32 (by rw [toByteArray_size])
      (by rw [exitMoveSenderMem_size I hmem]) (by omega) (by omega)
      (by norm_num)]
    rw [toByteArray_extract_all]
  have hradRead : final.readWithPadding 196 32 = rad.toByteArray := by
    dsimp [final]
    unfold exitMoveCalldataMem
    rw [write32_read_back _ _ 196 (by rw [toByteArray_size])
      (by rw [exitMoveThisMem_size I hmem])]
    rw [toByteArray_extract_all]
  rw [readWithPadding_eq_extract' final 128 100 (by norm_num) (by norm_num)
    (by rw [hfinalSize])]
  have hselectorExt : final.extract 128 132 = vatMoveSelector := by
    rw [← readWithPadding_eq_extract' final 128 4 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hselectorRead
  have hsenderExt : final.extract 132 164 = (solcSourceWord I).toByteArray := by
    rw [← readWithPadding_eq_extract' final 132 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hsenderRead
  have hthisExt : final.extract 164 196 = (UInt256.ofNat I.codeOwner.val).toByteArray := by
    rw [← readWithPadding_eq_extract' final 164 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hthisRead
  have hradExt : final.extract 196 228 = rad.toByteArray := by
    rw [← readWithPadding_eq_extract' final 196 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize])]
    exact hradRead
  have hsplit : final.extract 128 228 =
      final.extract 128 132 ++ final.extract 132 164 ++ final.extract 164 196 ++
        final.extract 196 228 := by
    rw [show final.extract 128 228 = final.extract 128 132 ++ final.extract 132 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 132 228 = final.extract 132 164 ++ final.extract 164 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 164 228 = final.extract 164 196 ++ final.extract 196 228 by
      rw [ByteArray.extract_append_extract]; norm_num]
    simp
  rw [hsplit, hselectorExt, hsenderExt, hthisExt, hradExt]

theorem exitMoveEncode_eq (I : ExecutionEnv) (rad : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    config.externalABI.encode? "move"
        [.address I.source, .address I.codeOwner, .int (Int.ofNat rad.toNat)] =
      some ((exitMoveCalldataMem I rad mem).readWithPadding 128 100) := by
  rw [exitMoveCalldataMem_read128_100 I rad hmem]
  have hsenderWord : EVM.word I.source.val = solcSourceWord I := by
    rfl
  have hthisWord : EVM.word I.codeOwner.val = UInt256.ofNat I.codeOwner.val := by
    rfl
  have hradLt : rad.toNat < EVM.twoPow 256 := by
    simp [UInt256.toNat, UInt256.size, EVM.twoPow]
  have hradWord : EVM.word rad.toNat = rad := by
    simpa [UInt256.ofNat] using u256_ofNat_toNat rad
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, uint256, uint256Int,
    vatMoveSelector, selectorBytes, hsenderWord, hthisWord, hradLt, hradWord,
    word_toBytesBE_toByteArray_eq_toByteArray, ByteArray.append_assoc]

abbrev exitMintSelectorPlainWord : UInt256 := ⟨0x40c10f19⟩

abbrev exitMintSelectorShiftedWord : UInt256 :=
  UInt256.shiftLeft exitMintSelectorPlainWord ⟨224⟩

noncomputable def exitMintSelectorMem (mem : ByteArray) : ByteArray :=
  exitMintSelectorShiftedWord.toByteArray.write 0 mem 128 32

noncomputable def exitMintUsrMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (exitUsrMaskedWord I).toByteArray.write 0 (exitMintSelectorMem mem) 132 32

noncomputable def exitMintCalldataMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (exitWadWord I).toByteArray.write 0 (exitMintUsrMem I mem) 164 32

theorem exitMintSelectorMem_size {mem : ByteArray} (hmem : mem.size = 228) :
    (exitMintSelectorMem mem).size = 228 := by
  unfold exitMintSelectorMem
  exact toByteArray_write32_size_of_le mem exitMintSelectorShiftedWord 128 228 228 hmem
    (by rw [hmem]; omega) (by omega)

theorem exitMintUsrMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 228) :
    (exitMintUsrMem I mem).size = 228 := by
  unfold exitMintUsrMem
  exact toByteArray_write32_size_of_le (exitMintSelectorMem mem) (exitUsrMaskedWord I)
    132 228 228 (exitMintSelectorMem_size hmem)
    (by rw [exitMintSelectorMem_size hmem]; omega) (by omega)

theorem exitMintCalldataMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 228) :
    (exitMintCalldataMem I mem).size = 228 := by
  unfold exitMintCalldataMem
  exact toByteArray_write32_size_of_le (exitMintUsrMem I mem) (exitWadWord I)
    164 228 228 (exitMintUsrMem_size I hmem)
    (by rw [exitMintUsrMem_size I hmem]; omega) (by omega)

theorem exitMintSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (exitMintSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold exitMintSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by norm_num)]
  exact hread64

theorem exitMintUsrMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (exitMintUsrMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold exitMintUsrMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [exitMintSelectorMem_size hmem]; omega) (by omega)]
  exact exitMintSelectorMem_read64 hmem hread64

theorem exitMintCalldataMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (exitMintCalldataMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold exitMintCalldataMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [exitMintUsrMem_size I hmem]; omega) (by omega)]
  exact exitMintUsrMem_read64 I hmem hread64

theorem exitMintCalldataMem_read128_68 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (exitMintCalldataMem I mem).readWithPadding 128 68 =
      daiMintSelector ++ (exitUsrMaskedWord I).toByteArray ++ (exitWadWord I).toByteArray := by
  let final := exitMintCalldataMem I mem
  have hfinalSize : final.size = 228 := by
    dsimp [final]
    exact exitMintCalldataMem_size I hmem
  have hselectorRead : final.readWithPadding 128 4 = daiMintSelector := by
    dsimp [final]
    unfold exitMintCalldataMem
    rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
      (by rw [exitMintUsrMem_size I hmem]; omega) (by omega)
      (by rw [exitMintUsrMem_size I hmem]; omega) (by omega) (by omega)]
    unfold exitMintUsrMem
    rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by rw [exitMintSelectorMem_size hmem]; omega) (by omega)
      (by rw [exitMintSelectorMem_size hmem]; omega) (by omega) (by omega)]
    unfold exitMintSelectorMem
    rw [toByteArray_write_read_window_of_gap exitMintSelectorShiftedWord mem 128 0 4
      (by norm_num) (by norm_num) (by norm_num) (by rw [hmem]; native_decide)]
    unfold exitMintSelectorShiftedWord exitMintSelectorPlainWord daiMintSelector selectorBytes
    native_decide
  have husrRead : final.readWithPadding 132 32 = (exitUsrMaskedWord I).toByteArray := by
    dsimp [final]
    unfold exitMintCalldataMem
    rw [write32_read_below_len _ _ 164 132 32 (by rw [toByteArray_size])
      (by rw [exitMintUsrMem_size I hmem]; omega) (by omega)
      (by rw [exitMintUsrMem_size I hmem]; omega) (by omega) (by omega)]
    unfold exitMintUsrMem
    rw [write32_read_prefix_len _ _ 132 32 (by rw [toByteArray_size])
      (by rw [exitMintSelectorMem_size hmem]; omega) (by omega) (by omega)
      (by omega)]
    rw [toByteArray_extract_all]
  have hwadRead : final.readWithPadding 164 32 = (exitWadWord I).toByteArray := by
    dsimp [final]
    unfold exitMintCalldataMem
    rw [write32_read_prefix_len _ _ 164 32 (by rw [toByteArray_size])
      (by rw [exitMintUsrMem_size I hmem]; omega) (by omega) (by omega)
      (by omega)]
    rw [toByteArray_extract_all]
  rw [readWithPadding_eq_extract' final 128 68 (by norm_num) (by norm_num)
    (by rw [hfinalSize]; omega)]
  have hselectorExt : final.extract 128 132 = daiMintSelector := by
    rw [← readWithPadding_eq_extract' final 128 4 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hselectorRead
  have husrExt : final.extract 132 164 = (exitUsrMaskedWord I).toByteArray := by
    rw [← readWithPadding_eq_extract' final 132 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact husrRead
  have hwadExt : final.extract 164 196 = (exitWadWord I).toByteArray := by
    rw [← readWithPadding_eq_extract' final 164 32 (by norm_num) (by norm_num)
      (by rw [hfinalSize]; omega)]
    exact hwadRead
  have hsplit : final.extract 128 196 =
      final.extract 128 132 ++ final.extract 132 164 ++ final.extract 164 196 := by
    rw [show final.extract 128 196 = final.extract 128 132 ++ final.extract 132 196 by
      rw [ByteArray.extract_append_extract]; norm_num]
    rw [show final.extract 132 196 = final.extract 132 164 ++ final.extract 164 196 by
      rw [ByteArray.extract_append_extract]; norm_num]
    simp
  rw [hsplit, hselectorExt, husrExt, hwadExt]

theorem exitMintEncode_eq (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    config.externalABI.encode? "mint"
        [.address (AccountAddress.ofUInt256 (exitUsrMaskedWord I)), exitWadValue I] =
      some ((exitMintCalldataMem I mem).readWithPadding 128 68) := by
  rw [exitMintCalldataMem_read128_68 I hmem]
  have husrCanon : (exitUsrMaskedWord I).toNat < EVM.addressModulus := by
    rw [exitUsrMaskedWord, u256_land_comm]
    exact solcAddrMask_result_canonical (exitUsrWord I)
  have husrWord :
      EVM.word (AccountAddress.ofNat (exitUsrMaskedWord I).toNat).val =
        exitUsrMaskedWord I := by
    exact Option.some.inj (valueToWord_address_ofNat_canonical (exitUsrMaskedWord I) husrCanon)
  have hwadLt : (exitWadWord I).toNat < EVM.twoPow 256 := by
    simp [UInt256.toNat, UInt256.size, EVM.twoPow]
  have hwadWord : EVM.word (exitWadWord I).toNat = exitWadWord I := by
    simpa [UInt256.ofNat] using u256_ofNat_toNat (exitWadWord I)
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, uint256, uint256Int,
    daiMintSelector, selectorBytes, exitWadValue, hwadLt, hwadWord, husrWord,
    accountAddress_ofUInt256_eq_ofNat_toNat, word_toBytesBE_toByteArray_eq_toByteArray,
    ByteArray.append_assoc]

abbrev exitEventSignatureWord : UInt256 :=
  ⟨0x22d324652c93739755cf4581508b60875ebdd78c20c0cff5cf8e23452b299631⟩

noncomputable def exitExitEventMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (exitWadWord I).toByteArray.write 0 mem 128 32

theorem exitExitEventMem_size (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 228) :
    (exitExitEventMem I mem).size = 228 := by
  unfold exitExitEventMem
  exact toByteArray_write32_size_of_le mem (exitWadWord I) 128 228 228 hmem
    (by rw [hmem]; omega) (by omega)

theorem exitExitEventMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (exitExitEventMem I mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold exitExitEventMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega)]
  exact hread64

theorem daiJoinExitLiveReverts {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hnotLive : exitLiveWord σ I ≠ ⟨1⟩)
    (h : RD daiJoinBytecode I g s0 ⟨1262⟩
      [exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiJoinBytecode g s0 := by
  have heq0 : UInt256.eq (exitLiveWord σ I) ⟨1⟩ = ⟨0⟩ :=
    u256_eq_of_ne hnotLive
  have heq0rev : UInt256.eq ⟨1⟩ (exitLiveWord σ I) = ⟨0⟩ := by
    apply u256_eq_of_ne
    intro hbad
    exact hnotLive hbad.symm
  have rd1272 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k1266, C1266, rd1266raw⟩ := rd1272.sload (by native_decide) (by evm_ov)
  have rd1266 : RD daiJoinBytecode I g s0 ⟨1266⟩
      (exitLiveWord σ I :: exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1266 C1266 := by
    simpa [exitLiveWord, daiJoinSlotWord, solcSlotWord] using rd1266raw
  have rd1272' := evm_run rd1266 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨1336⟩ (by native_decide) (by evm_ov)]
  rw [heq0rev] at rd1272'
  have rd1273 := rd1272'.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1273⟩) (len := ⟨16⟩)
    (rawWord := ⟨0x4461694a6f696e2f6e6f742d6c697665⟩) (shift := ⟨128⟩)
    (word := UInt256.shiftLeft ⟨0x4461694a6f696e2f6e6f742d6c697665⟩ ⟨128⟩)
    (op := .PUSH16) (width := 16) rd1273
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide) rfl solcFreePtrMem_size solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem daiJoinExitLiveOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hlive : exitLiveWord σ I = ⟨1⟩)
    (h : RD daiJoinBytecode I g s0 ⟨1262⟩
      [exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiJoinBytecode I g s0 ⟨1336⟩
      [exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have heq1 : UInt256.eq (exitLiveWord σ I) ⟨1⟩ = ⟨1⟩ := by
    rw [hlive]
    native_decide
  have heq1rev : UInt256.eq ⟨1⟩ (exitLiveWord σ I) = ⟨1⟩ := by
    rw [hlive]
    native_decide
  have rd1272 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k1266, C1266, rd1266raw⟩ := rd1272.sload (by native_decide) (by evm_ov)
  have rd1266 : RD daiJoinBytecode I g s0 ⟨1266⟩
      (exitLiveWord σ I :: exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1266 C1266 := by
    simpa [exitLiveWord, daiJoinSlotWord, solcSlotWord] using rd1266raw
  have rd1272' := evm_run rd1266 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw push2 ⟨1336⟩ (by native_decide) (by evm_ov)]
  rw [heq1rev] at rd1272'
  exact ⟨_, _, rd1272'.jumpiT (by native_decide) (by decide) (by jump_dest) (by evm_ov)⟩

theorem daiJoinExitMulSuccess {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hguard :
      exitWadWord I = ⟨0⟩ ∨
        UInt256.div (daiJoinRadWord (exitWadWord I)) (exitWadWord I) = daiJoinONEWord)
    (h : RD daiJoinBytecode I g s0 ⟨1336⟩
      [exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiJoinBytecode I g s0 ⟨1377⟩
      [daiJoinRadWord (exitWadWord I), UInt256.ofNat I.codeOwner, solcSourceWord I,
        joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I, exitWadWord I,
        exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd1356p := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k1340, C1340, rd1340raw⟩ := rd1356p.sload (by native_decide) (by evm_ov)
  have rd1340 : RD daiJoinBytecode I g s0 ⟨1340⟩
      (daiJoinSlotWord ⟨1⟩ σ I :: exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1340 C1340 := by
    simpa [daiJoinSlotWord, solcSlotWord] using rd1340raw
  have rd1359 := evm_run rd1340 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push4 joinMoveSelectorPlainWord (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    uniswapAddress,
    raw push2 ⟨1377⟩ (by native_decide) (by evm_ov)]
  have rd1359Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨1359⟩
      [⟨1377⟩, UInt256.ofNat I.codeOwner, solcSourceWord I, joinMoveSelectorPlainWord,
        daiJoinVatTargetWord σ I, exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [daiJoinVatTargetWord, daiJoinAddressReturnWord, hmaskConst, u256_land_comm]
        using rd1359⟩
  obtain ⟨_, _, rd1359'⟩ := rd1359Norm
  have rd1372 := rd1359'.pushConst daiJoinONEWord
    (width := 12) (op := .PUSH12) (by native_decide) (by native_decide) (by evm_ov)
  have rd1372Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨1372⟩
      [daiJoinONEWord, ⟨1377⟩, UInt256.ofNat I.codeOwner, solcSourceWord I,
        joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I, exitWadWord I,
        exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd1372⟩
  obtain ⟨_, _, rd1372'⟩ := rd1372Norm
  have rd1376 := evm_run rd1372' with [
    raw dup7 (by native_decide) (by evm_ov),
    raw push2 ⟨1678⟩ (by native_decide) (by evm_ov)]
  have rd1678Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨1678⟩
      [exitWadWord I, daiJoinONEWord, ⟨1377⟩, UInt256.ofNat I.codeOwner,
        solcSourceWord I, joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I,
        exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    have hpc :
        ((⟨1372⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3) =
          (⟨1376⟩ : UInt256) := by
      native_decide
    have rd1376Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨1376⟩
        [⟨1678⟩, exitWadWord I, daiJoinONEWord, ⟨1377⟩, UInt256.ofNat I.codeOwner,
          solcSourceWord I, joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I,
          exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      exact ⟨_, _, by simpa [hpc] using rd1376⟩
    obtain ⟨_, _, rd1376'⟩ := rd1376Norm
    exact ⟨_, _, RD.jump (a := ⟨1678⟩) rd1376'
      (by native_decide) (by jump_dest) (by evm_ov)⟩
  obtain ⟨_, _, rd1678⟩ := rd1678Norm
  obtain ⟨_, _, rd1377⟩ := daiJoinMulRoutine_success
    (code := daiJoinBytecode) (ee := I) (g := g) (s0 := s0)
    (x := daiJoinONEWord) (y := exitWadWord I) (ret := ⟨1377⟩)
    (R := [UInt256.ofNat I.codeOwner, solcSourceWord I, joinMoveSelectorPlainWord,
      daiJoinVatTargetWord σ I, exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel])
    rd1678 hguard (by jump_dest) daiJoinMulRoutine_shape (by simp)
  exact ⟨_, _, by simpa [daiJoinRadWord] using rd1377⟩

theorem daiJoinExitMulReverts {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hwad : exitWadWord I ≠ ⟨0⟩)
    (hguard : UInt256.div (daiJoinRadWord (exitWadWord I)) (exitWadWord I) ≠ daiJoinONEWord)
    (h : RD daiJoinBytecode I g s0 ⟨1336⟩
      [exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev daiJoinBytecode g s0 := by
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have rd1356p := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k1340, C1340, rd1340raw⟩ := rd1356p.sload (by native_decide) (by evm_ov)
  have rd1340 : RD daiJoinBytecode I g s0 ⟨1340⟩
      (daiJoinSlotWord ⟨1⟩ σ I :: exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1340 C1340 := by
    simpa [daiJoinSlotWord, solcSlotWord] using rd1340raw
  have rd1359 := evm_run rd1340 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push4 joinMoveSelectorPlainWord (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    uniswapAddress,
    raw push2 ⟨1377⟩ (by native_decide) (by evm_ov)]
  have rd1359Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨1359⟩
      [⟨1377⟩, UInt256.ofNat I.codeOwner, solcSourceWord I, joinMoveSelectorPlainWord,
        daiJoinVatTargetWord σ I, exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [daiJoinVatTargetWord, daiJoinAddressReturnWord, hmaskConst, u256_land_comm]
        using rd1359⟩
  obtain ⟨_, _, rd1359'⟩ := rd1359Norm
  have rd1372 := rd1359'.pushConst daiJoinONEWord
    (width := 12) (op := .PUSH12) (by native_decide) (by native_decide) (by evm_ov)
  have rd1372Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨1372⟩
      [daiJoinONEWord, ⟨1377⟩, UInt256.ofNat I.codeOwner, solcSourceWord I,
        joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I, exitWadWord I,
        exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    exact ⟨_, _, by simpa using rd1372⟩
  obtain ⟨_, _, rd1372'⟩ := rd1372Norm
  have rd1376 := evm_run rd1372' with [
    raw dup7 (by native_decide) (by evm_ov),
    raw push2 ⟨1678⟩ (by native_decide) (by evm_ov)]
  have rd1678Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨1678⟩
      [exitWadWord I, daiJoinONEWord, ⟨1377⟩, UInt256.ofNat I.codeOwner,
        solcSourceWord I, joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I,
        exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
    have hpc :
        ((⟨1372⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 3) =
          (⟨1376⟩ : UInt256) := by
      native_decide
    have rd1376Norm : ∃ k C, RD daiJoinBytecode I g s0 ⟨1376⟩
        [⟨1678⟩, exitWadWord I, daiJoinONEWord, ⟨1377⟩, UInt256.ofNat I.codeOwner,
          solcSourceWord I, joinMoveSelectorPlainWord, daiJoinVatTargetWord σ I,
          exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
      exact ⟨_, _, by simpa [hpc] using rd1376⟩
    obtain ⟨_, _, rd1376'⟩ := rd1376Norm
    exact ⟨_, _, RD.jump (a := ⟨1678⟩) rd1376'
      (by native_decide) (by jump_dest) (by evm_ov)⟩
  obtain ⟨_, _, rd1678⟩ := rd1678Norm
  exact daiJoinMulRoutine_revert
    (code := daiJoinBytecode) (ee := I) (g := g) (s0 := s0)
    (x := daiJoinONEWord) (y := exitWadWord I) (ret := ⟨1377⟩)
    (R := [UInt256.ofNat I.codeOwner, solcSourceWord I, joinMoveSelectorPlainWord,
      daiJoinVatTargetWord σ I, exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel])
    rd1678 hwad hguard daiJoinMulRoutine_revert_shape (by simp)

theorem daiJoinExitToVatMoveExtcodesizeGuard {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel rad : UInt256}
    (h : RD daiJoinBytecode I g s0 ⟨1377⟩
      [rad, UInt256.ofNat I.codeOwner, solcSourceWord I, joinMoveSelectorPlainWord,
        daiJoinVatTargetWord σ I, exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD daiJoinBytecode I g s0 ⟨1451⟩
      (daiJoinVatTargetWord σ I :: daiJoinVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ ::
        ⟨100⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord ::
        daiJoinVatTargetWord σ I :: exitWadWord I :: exitUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (exitMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have hselectorMask :
      UInt256.land (⟨4294967295⟩ : UInt256) joinMoveSelectorPlainWord =
        joinMoveSelectorPlainWord := by
    native_decide
  have hsourceCanon : (solcSourceWord I).toNat < EVM.addressModulus := by
    unfold solcSourceWord
    rw [UInt256.toNat_ofNat_of_lt]
    · rw [show EVM.addressModulus = AccountAddress.size from by decide]
      exact I.source.isLt
    · exact lt_trans I.source.isLt (by native_decide)
  have hsourceMask :
      UInt256.land solcAddrMask (solcSourceWord I) = solcSourceWord I :=
    solcAddrMask_clean_left hsourceCanon
  have hownerCanon : (UInt256.ofNat I.codeOwner.val).toNat < EVM.addressModulus := by
    rw [UInt256.toNat_ofNat_of_lt]
    · rw [show EVM.addressModulus = AccountAddress.size from by decide]
      exact I.codeOwner.isLt
    · exact lt_trans I.codeOwner.isLt (by native_decide)
  have hownerMask :
      UInt256.land solcAddrMask (UInt256.ofNat I.codeOwner.val) =
        UInt256.ofNat I.codeOwner.val :=
    solcAddrMask_clean_left hownerCanon
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide)
      solcFreePtrMem_read64
  have hcallMem : (exitMoveCalldataMem I rad solcFreePtrMem).size = 228 :=
    exitMoveCalldataMem_size I rad solcFreePtrMem_size
  have hcallRead64 :
      (exitMoveCalldataMem I rad solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    exitMoveCalldataMem_read64 I rad solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Call :
      (if (⟨64⟩ : UInt256).toNat ≥ (exitMoveCalldataMem I rad solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((exitMoveCalldataMem I rad solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hcallMem]; decide) (by decide) hcallRead64
  have rd1451 := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 6 (joinMoveSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (exitMoveSenderMem I solcFreePtrMem) (UInt256.ofNat 6)
      (by native_decide) mem_cost
      (by
        simpa [exitMoveSenderMem, hmaskConst]
          using congrArg
            (fun w => w.toByteArray.write 0 (joinMoveSelectorMem solcFreePtrMem) 132 32)
            hsourceMask)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (exitMoveThisMem I solcFreePtrMem) (UInt256.ofNat 7)
      (by native_decide) mem_cost
      (by
        simpa [exitMoveThisMem, hmaskConst]
          using congrArg
            (fun w => w.toByteArray.write 0 (exitMoveSenderMem I solcFreePtrMem) 164 32)
            hownerMask)
      (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 3 (exitMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Call (by decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc :
      ((⟨1377⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 5 + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨1451⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by
    simpa [daiJoinVatTargetWord, daiJoinAddressReturnWord, hmaskConst, hselectorMask,
      exitMoveSenderMem, exitMoveThisMem, exitMoveCalldataMem, hpc, u256_land_comm]
      using rd1451⟩

theorem daiJoinExitVatMoveNoCode
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel rad : UInt256}
    (rd1377 : RD daiJoinBytecode I g s0 ⟨1377⟩
      [rad, UInt256.ofNat I.codeOwner, solcSourceWord I, joinMoveSelectorPlainWord,
        daiJoinVatTargetWord σ I, exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (daiJoinVatTargetWord σ I) = ⟨0⟩) :
    RDrev daiJoinBytecode g s0 := by
  obtain ⟨_, _, rd1451⟩ := daiJoinExitToVatMoveExtcodesizeGuard rd1377
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨1451⟩) (okPc := ⟨1463⟩) rd1451
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem daiJoinExitVatMoveCallReady
    {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ} {sel rad : UInt256}
    (rd1377 : RD daiJoinBytecode I g s0 ⟨1377⟩
      [rad, UInt256.ofNat I.codeOwner, solcSourceWord I, joinMoveSelectorPlainWord,
        daiJoinVatTargetWord σ I, exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ (daiJoinVatTargetWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD daiJoinBytecode I g s0 ⟨1466⟩
      (gasWord :: daiJoinVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord ::
        daiJoinVatTargetWord σ I :: exitWadWord I :: exitUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (exitMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd1451⟩ := daiJoinExitToVatMoveExtcodesizeGuard rd1377
  obtain ⟨gasWord, k', C', rd1466⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨1451⟩) (okPc := ⟨1463⟩) rd1451
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd1466⟩

theorem daiJoinExitVatMovePostCall
    {cA cA' σ σ₀ σ' I} {g sel rad gasWord : UInt256}
    {rdata : ByteArray} {k C : ℕ}
    (rd1466 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1466⟩
      (gasWord :: daiJoinVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord ::
        daiJoinVatTargetWord σ I :: exitWadWord I :: exitUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (exitMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      rdata (cA', σ') k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σ' σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ I))
          (toExecute σ' (AccountAddress.ofUInt256 (daiJoinVatTargetWord σ I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMoveCalldataMem I rad solcFreePtrMem).readWithPadding 128 100)
          (I.depth + 1) I.header I.perm)
      ∧ RD daiJoinBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1467⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨228⟩ :: joinMoveSelectorPlainWord ::
            daiJoinVatTargetWord σ I :: exitWadWord I :: exitUsrMaskedWord I ::
            ⟨232⟩ :: sel :: [])
          (exitMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
          out (cA'', σ'') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, out, Ain, callGas, k', C', hΘ, rd1467raw, hout⟩ :=
    RD.call rd1466 (by native_decide) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
      native_decide
    have hmin :
        (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      exact umin_ofNat_right_toNat_of_ge (c := 0) (n := out.size)
        (by native_decide) (Nat.zero_le _) hout
    simpa [byteArray_write_len_zero, hmin, haw] using rd1467raw

theorem daiJoinExitVatMoveCallDepthLimit
    {cA cA' σ σ₀ σ' I} {g sel rad gasWord : UInt256}
    {rdata : ByteArray} {k C : ℕ}
    (rd1466 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1466⟩
      (gasWord :: daiJoinVatTargetWord σ I :: ⟨0⟩ :: ⟨128⟩ :: ⟨100⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord ::
        daiJoinVatTargetWord σ I :: exitWadWord I :: exitUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (exitMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      rdata (cA', σ') k C)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1467⟩
      (⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (exitMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      ByteArray.empty (cA', σ') k' C' := by
  obtain ⟨k', C', rd1467raw⟩ :=
    RD.callDepthLimit rd1466 (by native_decide) hdepth
      (by simp only [List.length_cons, List.length_nil]; omega)
  refine ⟨k', C', ?_⟩
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        (⟨128⟩ : UInt256).toNat (⟨100⟩ : UInt256).toNat)
        (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
    native_decide
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide
  simpa [byteArray_write_len_zero, hmin, haw] using rd1467raw

theorem daiJoinExitVatMoveCallFailed {cA σ σ₀ A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (rd1467 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1467⟩
      (⟨0⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev daiJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨1467⟩) (okPc := ⟨1483⟩) rd1467
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem daiJoinExitVatMoveCallSucceeded {cA σ σ₀ A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (rd1467 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1467⟩
      (⟨1⟩ :: ⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C) :
    ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1485⟩
      (⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨1467⟩) (okPc := ⟨1483⟩) rd1467
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem daiJoinExitVatMoveToDaiMintExtcodesizeGuard
    {cA σ σ₀ σ' A I} {g sel rad : UInt256}
    {rdata : ByteArray} {cA' : Batteries.RBSet AccountAddress compare}
    {k C : ℕ}
    (rd1485 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1485⟩
      (⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (exitMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      rdata (cA', σ') k C) :
    ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1560⟩
      (daiJoinDaiTargetWord σ' I :: daiJoinDaiTargetWord σ' I :: ⟨0⟩ ::
        ⟨128⟩ :: ⟨68⟩ :: ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ ::
        exitMintSelectorPlainWord :: daiJoinDaiTargetWord σ' I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (exitMintCalldataMem I (exitMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) rdata (cA', σ') k' C' := by
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have husrCanon : (exitUsrMaskedWord I).toNat < EVM.addressModulus := by
    rw [exitUsrMaskedWord, u256_land_comm]
    exact solcAddrMask_result_canonical (exitUsrWord I)
  have husrMask :
      UInt256.land solcAddrMask (exitUsrMaskedWord I) = exitUsrMaskedWord I :=
    solcAddrMask_clean_left husrCanon
  have hmoveMem : (exitMoveCalldataMem I rad solcFreePtrMem).size = 228 :=
    exitMoveCalldataMem_size I rad solcFreePtrMem_size
  have hmoveRead64 :
      (exitMoveCalldataMem I rad solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    exitMoveCalldataMem_read64 I rad solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Move :
      (if (⟨64⟩ : UInt256).toNat ≥ (exitMoveCalldataMem I rad solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((exitMoveCalldataMem I rad solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmoveMem]; decide) (by decide) hmoveRead64
  have hmintMem :
      (exitMintCalldataMem I (exitMoveCalldataMem I rad solcFreePtrMem)).size = 228 :=
    exitMintCalldataMem_size I hmoveMem
  have hmintRead64 :
      (exitMintCalldataMem I (exitMoveCalldataMem I rad solcFreePtrMem)).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    exitMintCalldataMem_read64 I hmoveMem hmoveRead64
  have hmload64Mint :
      (if (⟨64⟩ : UInt256).toNat ≥
            (exitMintCalldataMem I (exitMoveCalldataMem I rad solcFreePtrMem)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((exitMintCalldataMem I (exitMoveCalldataMem I rad solcFreePtrMem)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmintMem]; decide) (by decide) hmintRead64
  have rd1486 := RD.pop rd1485 (by native_decide) (by evm_ov)
  have rd1488p := evm_run rd1486 with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k1489, C1489, rd1489raw⟩ := rd1488p.sload (by native_decide) (by evm_ov)
  have rd1489 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1489⟩
      (daiJoinSlotWord ⟨2⟩ σ' I :: joinMoveSelectorPlainWord ::
        daiJoinVatTargetWord σ I :: exitWadWord I :: exitUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (exitMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      rdata (cA', σ') k1489 C1489 := by
    simpa [daiJoinSlotWord, solcSlotWord] using rd1489raw
  have rd1560 := evm_run rd1489 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Move (by decide) (by evm_ov),
    raw push4 exitMintSelectorPlainWord (by native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (exitMintSelectorMem (exitMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 0 (exitMintUsrMem I (exitMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) (by native_decide) mem_cost
      (by
        simpa [exitMintUsrMem, hmaskConst]
          using congrArg
            (fun w => w.toByteArray.write 0
              (exitMintSelectorMem (exitMoveCalldataMem I rad solcFreePtrMem)) 132 32)
            husrMask)
      (by decide) (by evm_ov),
    raw push1 ⟨36⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mstore 0 (exitMintCalldataMem I (exitMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) (by native_decide) mem_cost
      (by rfl) (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Mint (by decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push4 exitMintSelectorPlainWord (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap3 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw dup8 (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have hpc :
      ((⟨1489⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 5 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        (⟨1560⟩ : UInt256) := by
    native_decide
  exact ⟨_, _, by
    simpa [daiJoinDaiTargetWord, daiJoinAddressReturnWord, hmaskConst,
      exitMintSelectorShiftedWord, exitMintSelectorPlainWord, exitMintSelectorMem,
      exitMintUsrMem, exitMintCalldataMem, u256_land_comm, hpc]
      using rd1560⟩

theorem daiJoinExitDaiMintNoCode
    {cA σ σ₀ σ' A I} {g sel rad : UInt256}
    {rdata : ByteArray} {cA' : Batteries.RBSet AccountAddress compare}
    {k C : ℕ}
    (rd1485 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1485⟩
      (⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (exitMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      rdata (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ' (daiJoinDaiTargetWord σ' I) = ⟨0⟩) :
    RDrev daiJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd1560⟩ := daiJoinExitVatMoveToDaiMintExtcodesizeGuard rd1485
  exact RD.uniswapExtcodesizeGuardMissing (pc := ⟨1560⟩) (okPc := ⟨1572⟩) rd1560
    hcodeSize
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem daiJoinExitDaiMintCallReady
    {cA σ σ₀ σ' A I} {g sel rad : UInt256}
    {rdata : ByteArray} {cA' : Batteries.RBSet AccountAddress compare}
    {k C : ℕ}
    (rd1485 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1485⟩
      (⟨228⟩ :: joinMoveSelectorPlainWord :: daiJoinVatTargetWord σ I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (exitMoveCalldataMem I rad solcFreePtrMem) (UInt256.ofNat 8)
      rdata (cA', σ') k C)
    (hcodeSize :
      Reasoning.Theory.uniswapExtCodeSizeWord σ' (daiJoinDaiTargetWord σ' I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1575⟩
      (gasWord :: daiJoinDaiTargetWord σ' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ :: exitMintSelectorPlainWord ::
        daiJoinDaiTargetWord σ' I :: exitWadWord I :: exitUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (exitMintCalldataMem I (exitMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) rdata (cA', σ') k' C' := by
  obtain ⟨_, _, rd1560⟩ := daiJoinExitVatMoveToDaiMintExtcodesizeGuard rd1485
  obtain ⟨gasWord, k', C', rd1575⟩ :=
    RD.uniswapExtcodesizeGuardOkGas (pc := ⟨1560⟩) (okPc := ⟨1572⟩) rd1560
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd1575⟩

theorem daiJoinExitDaiMintPostCall
    {cA cA' σ σ₀ σ' A I} {g sel rad gasWord : UInt256}
    {rdata : ByteArray} {k C : ℕ}
    (rd1575 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1575⟩
      (gasWord :: daiJoinDaiTargetWord σ' I :: ⟨0⟩ :: ⟨128⟩ :: ⟨68⟩ ::
        ⟨128⟩ :: ⟨0⟩ :: ⟨196⟩ :: exitMintSelectorPlainWord ::
        daiJoinDaiTargetWord σ' I :: exitWadWord I :: exitUsrMaskedWord I ::
        ⟨232⟩ :: sel :: [])
      (exitMintCalldataMem I (exitMoveCalldataMem I rad solcFreePtrMem))
      (UInt256.ofNat 8) rdata (cA', σ') k C)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA'' : Batteries.RBSet AccountAddress compare) (σ'' : AccountMap)
      (z : Bool) (out : ByteArray) (Ain : Substate) (callGas : UInt256) (k' C' : ℕ),
      (∃ (g'' : UInt256) (A' : Substate),
        (cA'', σ'', g'', A', z, out) = Ethereum.EVM.Θ I.blobVersionedHashes cA' gh bl σ' σ₀ Ain
          (AccountAddress.ofUInt256 (UInt256.ofNat I.codeOwner)) I.sender
          (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I))
          (toExecute σ' (AccountAddress.ofUInt256 (daiJoinDaiTargetWord σ' I)))
          callGas (UInt256.ofNat I.gasPrice) ⟨0⟩ ⟨0⟩
          ((exitMintCalldataMem I (exitMoveCalldataMem I rad solcFreePtrMem)).readWithPadding
            128 68)
          (I.depth + 1) I.header I.perm)
      ∧ RD daiJoinBytecode I (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1576⟩
          ((if z then ⟨1⟩ else ⟨0⟩) :: ⟨196⟩ :: exitMintSelectorPlainWord ::
            daiJoinDaiTargetWord σ' I :: exitWadWord I :: exitUsrMaskedWord I ::
            ⟨232⟩ :: sel :: [])
          (exitMintCalldataMem I (exitMoveCalldataMem I rad solcFreePtrMem))
          (UInt256.ofNat 8) out (cA'', σ'') k' C'
      ∧ out.size < UInt256.size := by
  obtain ⟨cA'', σ'', z, out, Ain, callGas, k', C', hΘ, rd1576raw, hout⟩ :=
    RD.call rd1575 (by native_decide) hdepth (by evm_ov)
  refine ⟨cA'', σ'', z, out, Ain, callGas, k', C', ?_, ?_, hout⟩
  · simpa [initState] using hΘ
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          (⟨128⟩ : UInt256).toNat (⟨68⟩ : UInt256).toNat)
          (⟨128⟩ : UInt256).toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
      native_decide
    have hmin :
        (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      exact umin_ofNat_right_toNat_of_ge (c := 0) (n := out.size)
        (by native_decide) (Nat.zero_le _) hout
    simpa [byteArray_write_len_zero, hmin, haw] using rd1576raw

theorem daiJoinExitDaiMintCallFailed
    {cA σ σ₀ σd A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (rd1576 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1576⟩
      (⟨0⟩ :: ⟨196⟩ :: exitMintSelectorPlainWord :: daiJoinDaiTargetWord σd I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev daiJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.uniswapCallSuccessGuardMissing (pc := ⟨1576⟩) (okPc := ⟨1592⟩) rd1576
    rfl
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem daiJoinExitDaiMintCallSucceeded
    {cA σ σ₀ σd A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (rd1576 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1576⟩
      (⟨1⟩ :: ⟨196⟩ :: exitMintSelectorPlainWord :: daiJoinDaiTargetWord σd I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C) :
    ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1594⟩
      (⟨196⟩ :: exitMintSelectorPlainWord :: daiJoinDaiTargetWord σd I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k' C' := by
  exact RD.uniswapCallSuccessGuardOk (pc := ⟨1576⟩) (okPc := ⟨1592⟩) rd1576
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem daiJoinExitDaiMintSuccessTail
    {cA σ σ₀ σd A I} {g sel : UInt256}
    {mem rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hperm : I.perm = true)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (rd1594 : RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1594⟩
      (⟨196⟩ :: exitMintSelectorPlainWord :: daiJoinDaiTargetWord σd I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      mem (UInt256.ofNat 8) rdata acc k C) :
    RDret daiJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc ByteArray.empty := by
  have hmaskConst :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ = solcAddrMask := by
    native_decide
  have husrCanon : (exitUsrMaskedWord I).toNat < EVM.addressModulus := by
    rw [exitUsrMaskedWord, u256_land_comm]
    exact solcAddrMask_result_canonical (exitUsrWord I)
  have husrMask :
      UInt256.land solcAddrMask (exitUsrMaskedWord I) = exitUsrMaskedWord I :=
    solcAddrMask_clean_left husrCanon
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have heventMem : (exitExitEventMem I mem).size = 228 :=
    exitExitEventMem_size I hmem
  have heventRead64 :
      (exitExitEventMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
    exitExitEventMem_read64 I hmem hread64
  have hmload64Event :
      (if (⟨64⟩ : UInt256).toNat ≥ (exitExitEventMem I mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((exitExitEventMem I mem).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [heventMem]; decide) (by decide) heventRead64
  have rd1616 := evm_run rd1594 with [
    raw pop (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    raw dup5 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw mstore 0 (exitExitEventMem I mem) (UInt256.ofNat 8)
      (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost hmload64Event (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup7 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw swap4 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov)]
  have hpc1616 :
      ((⟨1594⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
        UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + ⟨1⟩ + ⟨1⟩) = (⟨1616⟩ : UInt256) := by
    native_decide
  have rd1616Norm : ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1616⟩
      (⟨128⟩ :: ⟨128⟩ :: exitMintSelectorPlainWord :: exitUsrMaskedWord I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (exitExitEventMem I mem) (UInt256.ofNat 8) rdata acc k' C' := by
    exact ⟨_, _, by
      simpa [exitExitEventMem, hmaskConst, husrMask, hpc1616, u256_land_comm]
        using rd1616⟩
  obtain ⟨_, _, rd1616'⟩ := rd1616Norm
  have rd1649 := rd1616'.pushConst exitEventSignatureWord
    (width := 32) (op := .PUSH32) (by native_decide) (by native_decide) (by evm_ov)
  have rd1659pre := evm_run rd1649 with [
    raw swap3 (by native_decide) (by evm_ov),
    raw pop (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hpc1659 :
      ((⟨1649⟩ : UInt256) + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
        ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) = (⟨1659⟩ : UInt256) := by
    native_decide
  have rd1659Norm : ∃ k' C', RD daiJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1659⟩
      (⟨128⟩ :: ⟨32⟩ :: exitEventSignatureWord :: exitUsrMaskedWord I ::
        exitWadWord I :: exitUsrMaskedWord I :: ⟨232⟩ :: sel :: [])
      (exitExitEventMem I mem) (UInt256.ofNat 8) rdata acc k' C' := by
    exact ⟨_, _, by
      simpa [exitEventSignatureWord, hpc1659] using rd1659pre⟩
  obtain ⟨_, _, rd1659⟩ := rd1659Norm
  have rd1660 := RD.log2
    (a := ⟨128⟩) (b := ⟨32⟩) (c := exitEventSignatureWord)
    (d := exitUsrMaskedWord I)
    (t := [exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 8).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    rd1659 (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1661 := RD.pop (a := exitWadWord I)
    (t := [exitUsrMaskedWord I, ⟨232⟩, sel]) rd1660
    (by native_decide) (by evm_ov)
  have rd1662 := RD.pop (a := exitUsrMaskedWord I) (t := [⟨232⟩, sel]) rd1661
    (by native_decide) (by evm_ov)
  have rd232 := RD.jump (a := ⟨232⟩) (t := [sel]) rd1662
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd232' := RD.jumpdest (pc := ⟨232⟩) (stk := [sel]) rd232
    (by native_decide) (by evm_ov)
  simpa using RD.stop rd232' (by native_decide) (by evm_ov)

theorem daiJoinDecode_exit_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
      (transitionSignature exitTransition).paramTypes I.calldata = some (exitStore I) := by
  simpa [config, exitTransition, exitStore, exitUsrValue, exitWadValue, exitUsrWord,
    exitWadWord, calldataWord] using
    decodeCalldata_legacyAddress_uint256_ok (cd := I.calldata) (x := "usr") (y := "wad")
      hsz68

theorem daiJoinDecode_exit_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (exitTransition.params.map Param.name)
      (transitionSignature exitTransition).paramTypes I.calldata = none := by
  simpa [config, exitTransition] using
    decodeCalldata_legacyAddress_uint256_none_short (cd := I.calldata)
      (x := "usr") (y := "wad") hsz4 hshort

theorem daiJoinReachExitBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = daiJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (daiJoinSelBytes 3)) :
    ∃ k C, RD daiJoinBytecode I g
        (initState cA gh bl σ σ₀ g A I)
        ⟨382⟩ [daiJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : daiJoinSelWord I = ⟨0xef693bed⟩ :=
    daiJoinSelWord_eq_of_beq I hsz 0xef 0x69 0x3b 0xed ⟨0xef693bed⟩
      (by native_decide) (by simpa [daiJoinSelBytes] using hsel)
  have hroot :
      UInt256.gt (armSelNat daiJoinBytecode daiJoinRootSplitPc) (daiJoinSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 3 →
      UInt256.eq
        (armSelNat daiJoinBytecode
          (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc j))
        (daiJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq
        (armSelNat daiJoinBytecode
          (nthArmPc daiJoinBytecode daiJoinHighFirstArmPc 3))
        (daiJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact daiJoinReachHighBody 3 (by omega) ⟨382⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem daiJoinExitX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD daiJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨382⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD daiJoinBytecode I g
        (initState cA gh bl σ σ₀ g A I) ⟨1262⟩
        [exitWadWord I, exitUsrMaskedWord I, ⟨232⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := daiJoinBytecode) (sel := sel)
    (entry := ⟨382⟩) (ret := ⟨232⟩) (decoded := ⟨404⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.solcAddressUint256ExternalMaskAndJumpMasked
    (code := daiJoinBytecode) (decoded := ⟨404⟩) (ret := ⟨232⟩)
    (routine := ⟨1262⟩) (R := [sel]) hdecoded
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [exitWadWord, exitUsrMaskedWord, exitUsrWord, calldataWord] using hroutine⟩

theorem daiJoinExitX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD daiJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨382⟩ [sel]
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
    (entry := ⟨382⟩) (ret := ⟨232⟩) (decoded := ⟨404⟩)
    (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

end Benchmarks.Dss.DaiJoin
