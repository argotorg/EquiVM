import Benchmarks.Dss.GemJoin.Deny
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.GemJoin

/-! ## `join(address,uint256)` -/

abbrev joinUsrWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev joinUsrMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (joinUsrWord I)

abbrev joinUsrValue (I : ExecutionEnv) : Value :=
  .address (AccountAddress.ofNat (joinUsrWord I).toNat)

abbrev joinWadWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev joinWadValue (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (joinWadWord I).toNat)

abbrev joinStore (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "usr" (joinUsrValue I)).insert "wad" (joinWadValue I)

theorem joinStore_index_usr (I : ExecutionEnv) :
    (joinStore I)["usr"] = joinUsrValue I := by
  unfold joinStore
  simp [Std.HashMap.getElem_insert]

theorem joinStore_index_wad (I : ExecutionEnv) :
    (joinStore I)["wad"] = joinWadValue I := by
  unfold joinStore
  simp

theorem gemJoinDecode_join_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
      (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I) := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr", "wad"] [addr, uint256]
    I.calldata = _
  simpa [joinStore, joinUsrValue, joinWadValue, joinUsrWord, joinWadWord, calldataWord] using
    decodeCalldata_legacyAddress_uint256_ok
      (cd := I.calldata) (x := "usr") (y := "wad") hsz68

theorem gemJoinDecode_join_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
      (transitionSignature joinTransition).paramTypes I.calldata = none := by
  show decodeCalldataWithMode config.abiDecodeMode ["usr", "wad"] [addr, uint256]
    I.calldata = none
  simpa using decodeCalldata_legacyAddress_uint256_none_short
    (cd := I.calldata) (x := "usr") (y := "wad") hsz4 hshort

theorem evalExpr_join_live_true (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := joinStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := joinStore I } evm
        (.storage liveRef) = .ok (.int 1) := by
    have hload : storageLocLoad evm (wordLoc ⟨5⟩) = .int 1 := by
      rw [gemJoinStorageLocLoad_uint256, hlive]
      decide +native
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := joinStore I })
      (slot := liveRef)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨5⟩)
      (hbase := by simp [joinStore, liveRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := hload)]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_join_live_false (evm : EVM.State) (I : ExecutionEnv)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := joinStore I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := joinStore I } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := joinStore I })
      (slot := liveRef)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨5⟩)
      (hbase := by simp [joinStore, liveRef])
      (her := by simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact gemJoinStorageLocLoad_uint256 evm ⟨5⟩)
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    exact hlive (uint256_toNat_eq_one (Int.ofNat.inj hbad))
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat) == Value.int 1) =
        false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalExpr_join_wad_lt_true (evm : EVM.State) (I : ExecutionEnv)
    (hwad : (joinWadWord I).toNat < intLimit) :
    evalExpr? config { contract := contract, locals := joinStore I } evm
      (.binary .lt (.var "wad") (.intLit intLimit)) = .ok (.bool true) := by
  have hget : (joinStore I).get? "wad" = some (joinWadValue I) := by
    unfold joinStore
    simp
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [hget]
  simp [EvalResult.ofOption, joinWadValue, evalBinaryOp?]
  exact hwad

theorem evalExpr_join_wad_lt_false (evm : EVM.State) (I : ExecutionEnv)
    (hwad : intLimit ≤ (joinWadWord I).toNat) :
    evalExpr? config { contract := contract, locals := joinStore I } evm
      (.binary .lt (.var "wad") (.intLit intLimit)) = .ok (.bool false) := by
  have hnot : ¬ Int.ofNat (joinWadWord I).toNat < intLimit := by
    exact not_lt.mpr hwad
  have hget : (joinStore I).get? "wad" = some (joinWadValue I) := by
    unfold joinStore
    simp
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [hget]
  simp [EvalResult.ofOption, joinWadValue, evalBinaryOp?]
  exact hwad

theorem gemJoinDecode_slipReturn (out : ByteArray) :
    config.externalABI.decode? "slip" out = some [] := by
  simp [config, externalABI, decodeVoid?]

theorem gemJoinDecode_transferFromReturn_true {out : ByteArray}
    (hlo : 32 ≤ out.size)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ≠ ⟨0⟩) :
    config.externalABI.decode? "transferFrom" out = some [.bool true] := by
  change decodeBoolReturn? out = some [.bool true]
  unfold decodeBoolReturn?
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := out)
  have hnz : ABI.bytesToWord ((out.toList.drop 0).take 32) ≠ ⟨0⟩ := by
    intro hzero
    exact hword (by simpa [List.drop_zero, hwordList] using hzero)
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [boolTy]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [boolTy]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [boolTy].length) (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  have hscalar :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 boolTy out.toList 0 =
        some (.bool true, 0 + 32) := by
    simpa [boolTy] using
      (decodeScalarWordWithMode_legacy_bool_true (bytes := out.toList)
        (start := 0) htake0 hnz)
  rw [hscalar]
  rfl

theorem gemJoinDecode_transferFromReturn_false {out : ByteArray}
    (hlo : 32 ≤ out.size)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) = ⟨0⟩) :
    config.externalABI.decode? "transferFrom" out = some [.bool false] := by
  change decodeBoolReturn? out = some [.bool false]
  unfold decodeBoolReturn?
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0 : ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  have hwordList := bytesToWord_take32_eq_extract0_32 (returndata := out)
  have hzero : ABI.bytesToWord ((out.toList.drop 0).take 32) = ⟨0⟩ := by
    simpa [List.drop_zero, hwordList] using hword
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [boolTy]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [boolTy]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [boolTy].length) (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  have hscalar :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 boolTy out.toList 0 =
        some (.bool false, 0 + 32) := by
    simpa [boolTy] using
      (decodeScalarWordWithMode_legacy_bool_false (bytes := out.toList)
        (start := 0) htake0 hzero)
  rw [hscalar]
  rfl

theorem gemJoinDecode_transferFromReturn_none_short {out : ByteArray}
    (hshort : out.size < 32) :
    config.externalABI.decode? "transferFrom" out = none := by
  change decodeBoolReturn? out = none
  unfold decodeBoolReturn?
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake0n : ¬ ((out.toList.drop 0).take 32).length = 32 := by
    rw [List.drop_zero, List.length_take, hlen]
    omega
  unfold ABI.decodeReturnValuesWithMode?
  rw [abiTupleHeadSize_scalarWords_eq (types := [boolTy]) (by decide)]
  simp only [bind, Option.bind]
  rw [decodeABIValues_scalarWordsWithMode_eq (mode := DecodeMode.legacySolc05)
    (types := [boolTy]) (bytes := out.toList) (cursor := 0)
    (total := 32 * [boolTy].length) (by decide) (by simp)]
  simp only [decodeScalarWordsWithMode?]
  have hscalar :
      decodeScalarWordWithMode? DecodeMode.legacySolc05 boolTy out.toList 0 = none := by
    simpa [boolTy] using
      (decodeScalarWordWithMode_legacy_bool_none_short (bytes := out.toList)
        (start := 0) htake0n)
  rw [hscalar]
  rfl

theorem evalExpr_join_vat (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := joinStore I } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := joinStore I })
    (slot := vatRef)
    (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨1⟩)
    (hbase := by simp [joinStore, vatRef])
    (her := by simp [evalStorageRef, evalStorageRefSteps, vatRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := by exact gemJoinStorageLocLoad_address_offset0 evm ⟨1⟩)]

theorem evalExpr_join_gem (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := joinStore I } evm (.storage gemRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
          solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := joinStore I })
    (slot := gemRef)
    (er := ({ base := "gem", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨3⟩)
    (hbase := by simp [joinStore, gemRef])
    (her := by simp [evalStorageRef, evalStorageRefSteps, gemRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := by exact gemJoinStorageLocLoad_address_offset0 evm ⟨3⟩)]

theorem evalExpr_join_ilk (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := joinStore I } evm (.storage ilkRef) =
      .ok (.fixedBytes bytes32Width
        (EVM.Word.toBytesBE
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩))) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := joinStore I })
    (slot := ilkRef)
    (er := ({ base := "ilk", steps := [] } : EvaledStorageRef))
    (t := .bytes bytes32Width)
    (loc := bytes32Loc ⟨2⟩)
    (hbase := by simp [joinStore, ilkRef])
    (her := by simp [evalStorageRef, evalStorageRefSteps, ilkRef, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, bytes32St])
    (hloc := by rfl)
    (hload := by exact gemJoinStorageLocLoad_bytes32 evm ⟨2⟩)]

theorem evalExpr_join_usr (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := joinStore I } evm (.var "usr") =
      .ok (joinUsrValue I) := by
  simp only [evalExpr?]
  rw [show (joinStore I).get? "usr" = some (joinUsrValue I) by
    unfold joinStore
    simp [Std.HashMap.getElem_insert]]
  unfold EvalResult.ofOption
  rfl

theorem evalExpr_join_wad (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := joinStore I } evm (.var "wad") =
      .ok (joinWadValue I) := by
  simp only [evalExpr?]
  rw [show (joinStore I).get? "wad" = some (joinWadValue I) by
    unfold joinStore
    simp]
  unfold EvalResult.ofOption
  rfl

theorem evalExpr_join_asInt256_wad (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := joinStore I } evm
      (asInt256 (.var "wad")) = .ok (joinWadValue I) := by
  unfold asInt256
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [show (joinStore I).get? "wad" = some (joinWadValue I) by
    unfold joinStore
    simp]
  simp [joinWadValue, int256St, int256Int, castValue?, EvalResult.ofOption]

theorem evalExprs_join_slipArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := joinStore I } evm
      [.storage ilkRef, .var "usr", asInt256 (.var "wad")] =
        .ok
          [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
            joinUsrValue I, joinWadValue I] := by
  simp [evalExprs?, evalExpr_join_ilk evm I, evalExpr_join_usr evm I,
    evalExpr_join_asInt256_wad evm I, EvalResult.bind, bind, pure]

theorem evalExprs_join_transferFromArgs (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := joinStore I } evm
      [sender, thisAddr, .var "wad"] =
        .ok [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
          joinWadValue I] := by
  simp [evalExprs?, sender, thisAddr, evalExpr_join_wad evm I, evalExpr?, envValue,
    EvalResult.bind, bind, pure]

theorem evalExpr_join_vatCodeGuard_true (evm : EVM.State) (I : ExecutionEnv)
    (hcode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
              solcAddrMask).toNat)).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := joinStore I } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_join_vat evm I, evalBinaryOp?,
    EVM.Word.ofNat, hcode]

theorem evalExpr_join_vatCodeGuard_false (evm : EVM.State) (I : ExecutionEnv)
    (hnoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
              solcAddrMask).toNat)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := joinStore I } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_join_vat evm I, evalBinaryOp?,
    EVM.Word.ofNat, hnoCode]

theorem evalExpr_join_gemCodeGuard_true (evm : EVM.State) (I : ExecutionEnv)
    (hcode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
              solcAddrMask).toNat)).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := joinStore I } evm
      (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_join_gem evm I, evalBinaryOp?,
    EVM.Word.ofNat, hcode]

theorem evalExpr_join_gemCodeGuard_false (evm : EVM.State) (I : ExecutionEnv)
    (hnoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (AccountAddress.ofNat
            (UInt256.land
              (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
              solcAddrMask).toNat)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := joinStore I } evm
      (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_join_gem evm I, evalBinaryOp?,
    EVM.Word.ofNat, hnoCode]

abbrev joinVatAddressOf (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      solcAddrMask).toNat

abbrev joinGemAddressOf (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
      solcAddrMask).toNat

abbrev joinLocalsAfterSlip (I : ExecutionEnv) : Store :=
  (joinStore I).insert "slipRet" .unit

abbrev joinLocalsAfterTransferOk (I : ExecutionEnv) : Store :=
  (joinLocalsAfterSlip I).insert "transferFromOk" (.bool true)

abbrev joinLocalsAfterTransferFalse (I : ExecutionEnv) : Store :=
  (joinLocalsAfterSlip I).insert "transferFromOk" (.bool false)

theorem evalExpr_join_gem_afterSlip (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evm
      (.storage gemRef) = .ok (.address (joinGemAddressOf evm)) := by
  rw [evalExpr_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := joinLocalsAfterSlip I })
    (slot := gemRef)
    (er := ({ base := "gem", steps := [] } : EvaledStorageRef))
    (t := .address)
    (loc := addrLoc ⟨3⟩)
    (hbase := by simp [joinLocalsAfterSlip, joinStore, gemRef])
    (her := by
      simp [evalStorageRef, evalStorageRefSteps, joinLocalsAfterSlip, joinStore, gemRef,
        EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by rfl)
    (hload := by exact gemJoinStorageLocLoad_address_offset0 evm ⟨3⟩)]

theorem evalExpr_join_wad_afterSlip (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evm (.var "wad") =
      .ok (joinWadValue I) := by
  simp only [evalExpr?]
  rw [show (joinLocalsAfterSlip I).get? "wad" = some (joinWadValue I) by
    rw [joinLocalsAfterSlip, store_get_ne (L := joinStore I) (k := "slipRet") (a := "wad")
      .unit (by decide +native)]
    unfold joinStore
    simp]
  unfold EvalResult.ofOption
  rfl

theorem evalExprs_join_transferFromArgs_afterSlip (evm : EVM.State) (I : ExecutionEnv) :
    evalExprs? config { contract := contract, locals := joinLocalsAfterSlip I } evm
      [sender, thisAddr, .var "wad"] =
        .ok [.address evm.executionEnv.source, .address evm.executionEnv.codeOwner,
          joinWadValue I] := by
  simp [evalExprs?, sender, thisAddr, evalExpr_join_wad_afterSlip evm I, evalExpr?,
    envValue, EvalResult.bind, bind, pure]

theorem evalExpr_join_gemCodeGuard_afterSlip_true (evm : EVM.State) (I : ExecutionEnv)
    (hcode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinGemAddressOf evm)).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evm
      (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
        .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_join_gem_afterSlip evm I, evalBinaryOp?,
    EVM.Word.ofNat, hcode]

theorem evalExpr_join_gemCodeGuard_afterSlip_false (evm : EVM.State) (I : ExecutionEnv)
    (hnoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (joinGemAddressOf evm)).option 0 (fun acc => acc.code.size))).toNat =
          0) :
    evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evm
      (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
        .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, evalExpr_join_gem_afterSlip evm I, evalBinaryOp?,
    EVM.Word.ofNat, hnoCode]

theorem evalExpr_join_transferFromOk_true (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := joinLocalsAfterTransferOk I } evm
      (.var "transferFromOk") = .ok (.bool true) := by
  simp only [evalExpr?]
  rw [show (joinLocalsAfterTransferOk I).get? "transferFromOk" = some (.bool true) by
    unfold joinLocalsAfterTransferOk
    rw [store_get_self]]
  unfold EvalResult.ofOption
  rfl

theorem evalExpr_join_transferFromOk_false (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? config { contract := contract, locals := joinLocalsAfterTransferFalse I } evm
      (.var "transferFromOk") = .ok (.bool false) := by
  simp only [evalExpr?]
  rw [show (joinLocalsAfterTransferFalse I).get? "transferFromOk" = some (.bool false) by
    unfold joinLocalsAfterTransferFalse
    rw [store_get_self]]
  unfold EvalResult.ofOption
  rfl

theorem gemJoinJoinBodySuccess (evm evmSlip evmTransfer : EVM.State) (I : ExecutionEnv)
    {outSlip outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallSlip :
      typedCallViaEVM config evm (EVM.address (joinVatAddressOf evm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (true, evmSlip, outSlip) true)
    (hgemCode :
      0 < (UInt256.ofNat
        ((evmSlip.lookupAccount (joinGemAddressOf evmSlip)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallTransfer :
      typedCallViaEVM config evmSlip (EVM.address (joinGemAddressOf evmSlip))
        "transferFrom" 0
        [.address evmSlip.executionEnv.source, .address evmSlip.executionEnv.codeOwner,
          joinWadValue I]
        (true, evmTransfer, outTransfer) true)
    (hdecTransfer : config.externalABI.decode? "transferFrom" outTransfer = some [.bool true]) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body
      (.returned { contract := contract, locals := joinLocalsAfterTransferOk I } evmTransfer none) := by
  have hvat :
      evalExpr? config { contract := contract, locals := joinStore I } evm (.storage vatRef) =
        .ok (.address (joinVatAddressOf evm)) := by
    simpa [joinVatAddressOf] using evalExpr_join_vat evm I
  have hvatGuard :
      evalExpr? config { contract := contract, locals := joinStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [joinVatAddressOf] using evalExpr_join_vatCodeGuard_true evm I hvatCode
  have hslipArgs :
      evalExprs? config { contract := contract, locals := joinStore I } evm
        [.storage ilkRef, .var "usr", asInt256 (.var "wad")] =
          .ok
            [.fixedBytes bytes32Width
              (EVM.Word.toBytesBE
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
              joinUsrValue I, joinWadValue I] :=
    evalExprs_join_slipArgs evm I
  have hslipStmt :
      ExecStmt config { contract := contract, locals := joinStore I } evm
        (.externalCall (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, .var "usr", asInt256 (.var "wad")] "slipRet")
        (.ok { contract := contract, locals := joinLocalsAfterSlip I } evmSlip) := by
    simpa [joinLocalsAfterSlip, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hslipArgs hcallSlip
        (gemJoinDecode_slipReturn outSlip)
  have hgem :
      evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.storage gemRef) = .ok (.address (joinGemAddressOf evmSlip)) :=
    evalExpr_join_gem_afterSlip evmSlip I
  have hgemGuard :
      evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_join_gemCodeGuard_afterSlip_true evmSlip I hgemCode
  have htransferArgs :
      evalExprs? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        [sender, thisAddr, .var "wad"] =
          .ok [.address evmSlip.executionEnv.source, .address evmSlip.executionEnv.codeOwner,
            joinWadValue I] :=
    evalExprs_join_transferFromArgs_afterSlip evmSlip I
  have htransferStmt :
      ExecStmt config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.externalCall (.storage gemRef) "transferFrom" (.intLit 0)
          [sender, thisAddr, .var "wad"] "transferFromOk")
        (.ok { contract := contract, locals := joinLocalsAfterTransferOk I } evmTransfer) := by
    simpa [joinLocalsAfterTransferOk, collapseReturns] using
      ExecStmt.externalCallSuccess hgem (by simp [evalExpr?, pure]) htransferArgs
        hcallTransfer hdecTransfer
  refine ExecFuncBody.execBlockOK ?_
  simp only [joinTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_live_true evm I hlive)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_wad_lt_true evm I hwadLow)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
  refine ExecBlock.consNormal hslipStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hgemGuard) ?_
  refine ExecBlock.consNormal htransferStmt ?_
  exact ExecBlock.consNormal
    (ExecStmt.requireTrue (evalExpr_join_transferFromOk_true evmTransfer I))
    ExecBlock.nil

theorem gemJoinJoinBodyRevertsVatNoCode (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatNoCode :
      (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  have hvatGuard :
      evalExpr? config { contract := contract, locals := joinStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    simpa [joinVatAddressOf] using evalExpr_join_vatCodeGuard_false evm I hvatNoCode
  refine ExecFuncBody.execBlockRevert ?_
  simp only [joinTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_live_true evm I hlive)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_wad_lt_true evm I hwadLow)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hvatGuard)

theorem gemJoinJoinBodyRevertsSlipCallFailure
    (evm evmSlip : EVM.State) (I : ExecutionEnv) {outSlip : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSlip :
      typedCallViaEVM config evm (EVM.address (joinVatAddressOf evm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (false, evmSlip, outSlip) true) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := joinStore I } evm (.storage vatRef) =
        .ok (.address (joinVatAddressOf evm)) := by
    simpa [joinVatAddressOf] using evalExpr_join_vat evm I
  have hvatGuard :
      evalExpr? config { contract := contract, locals := joinStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [joinVatAddressOf] using evalExpr_join_vatCodeGuard_true evm I hvatCode
  have hslipArgs :
      evalExprs? config { contract := contract, locals := joinStore I } evm
        [.storage ilkRef, .var "usr", asInt256 (.var "wad")] =
          .ok
            [.fixedBytes bytes32Width
              (EVM.Word.toBytesBE
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
              joinUsrValue I, joinWadValue I] :=
    evalExprs_join_slipArgs evm I
  have hslipStmt :
      ExecStmt config { contract := contract, locals := joinStore I } evm
        (.externalCall (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, .var "usr", asInt256 (.var "wad")] "slipRet")
        .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hslipArgs hcallSlip
  refine ExecFuncBody.execBlockRevert ?_
  simp only [joinTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_live_true evm I hlive)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_wad_lt_true evm I hwadLow)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
  exact ExecBlock.consRevert hslipStmt

theorem gemJoinJoinBodyRevertsGemNoCode
    (evm evmSlip : EVM.State) (I : ExecutionEnv) {outSlip : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSlip :
      typedCallViaEVM config evm (EVM.address (joinVatAddressOf evm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (true, evmSlip, outSlip) true)
    (hgemNoCode :
      (UInt256.ofNat
        ((evmSlip.lookupAccount (joinGemAddressOf evmSlip)).option 0
          (fun acc => acc.code.size))).toNat = 0) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := joinStore I } evm (.storage vatRef) =
        .ok (.address (joinVatAddressOf evm)) := by
    simpa [joinVatAddressOf] using evalExpr_join_vat evm I
  have hvatGuard :
      evalExpr? config { contract := contract, locals := joinStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [joinVatAddressOf] using evalExpr_join_vatCodeGuard_true evm I hvatCode
  have hslipArgs :
      evalExprs? config { contract := contract, locals := joinStore I } evm
        [.storage ilkRef, .var "usr", asInt256 (.var "wad")] =
          .ok
            [.fixedBytes bytes32Width
              (EVM.Word.toBytesBE
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
              joinUsrValue I, joinWadValue I] :=
    evalExprs_join_slipArgs evm I
  have hslipStmt :
      ExecStmt config { contract := contract, locals := joinStore I } evm
        (.externalCall (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, .var "usr", asInt256 (.var "wad")] "slipRet")
        (.ok { contract := contract, locals := joinLocalsAfterSlip I } evmSlip) := by
    simpa [joinLocalsAfterSlip, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hslipArgs hcallSlip
        (gemJoinDecode_slipReturn outSlip)
  have hgemGuard :
      evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
          .ok (.bool false) :=
    evalExpr_join_gemCodeGuard_afterSlip_false evmSlip I hgemNoCode
  refine ExecFuncBody.execBlockRevert ?_
  simp only [joinTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_live_true evm I hlive)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_wad_lt_true evm I hwadLow)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
  refine ExecBlock.consNormal hslipStmt ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse hgemGuard)

theorem gemJoinJoinBodyRevertsTransferCallFailure
    (evm evmSlip evmTransfer : EVM.State) (I : ExecutionEnv)
    {outSlip outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSlip :
      typedCallViaEVM config evm (EVM.address (joinVatAddressOf evm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (true, evmSlip, outSlip) true)
    (hgemCode :
      0 < (UInt256.ofNat
        ((evmSlip.lookupAccount (joinGemAddressOf evmSlip)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallTransfer :
      typedCallViaEVM config evmSlip (EVM.address (joinGemAddressOf evmSlip))
        "transferFrom" 0
        [.address evmSlip.executionEnv.source, .address evmSlip.executionEnv.codeOwner,
          joinWadValue I]
        (false, evmTransfer, outTransfer) true) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := joinStore I } evm (.storage vatRef) =
        .ok (.address (joinVatAddressOf evm)) := by
    simpa [joinVatAddressOf] using evalExpr_join_vat evm I
  have hvatGuard :
      evalExpr? config { contract := contract, locals := joinStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [joinVatAddressOf] using evalExpr_join_vatCodeGuard_true evm I hvatCode
  have hslipArgs :
      evalExprs? config { contract := contract, locals := joinStore I } evm
        [.storage ilkRef, .var "usr", asInt256 (.var "wad")] =
          .ok
            [.fixedBytes bytes32Width
              (EVM.Word.toBytesBE
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
              joinUsrValue I, joinWadValue I] :=
    evalExprs_join_slipArgs evm I
  have hslipStmt :
      ExecStmt config { contract := contract, locals := joinStore I } evm
        (.externalCall (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, .var "usr", asInt256 (.var "wad")] "slipRet")
        (.ok { contract := contract, locals := joinLocalsAfterSlip I } evmSlip) := by
    simpa [joinLocalsAfterSlip, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hslipArgs hcallSlip
        (gemJoinDecode_slipReturn outSlip)
  have hgem :
      evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.storage gemRef) = .ok (.address (joinGemAddressOf evmSlip)) :=
    evalExpr_join_gem_afterSlip evmSlip I
  have hgemGuard :
      evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_join_gemCodeGuard_afterSlip_true evmSlip I hgemCode
  have htransferArgs :
      evalExprs? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        [sender, thisAddr, .var "wad"] =
          .ok [.address evmSlip.executionEnv.source, .address evmSlip.executionEnv.codeOwner,
            joinWadValue I] :=
    evalExprs_join_transferFromArgs_afterSlip evmSlip I
  have htransferStmt :
      ExecStmt config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.externalCall (.storage gemRef) "transferFrom" (.intLit 0)
          [sender, thisAddr, .var "wad"] "transferFromOk")
        .reverted := by
    exact ExecStmt.externalCallFailure hgem (by simp [evalExpr?, pure]) htransferArgs
      hcallTransfer
  refine ExecFuncBody.execBlockRevert ?_
  simp only [joinTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_live_true evm I hlive)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_wad_lt_true evm I hwadLow)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
  refine ExecBlock.consNormal hslipStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hgemGuard) ?_
  exact ExecBlock.consRevert htransferStmt

theorem gemJoinJoinBodyRevertsTransferDecode
    (evm evmSlip evmTransfer : EVM.State) (I : ExecutionEnv)
    {outSlip outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSlip :
      typedCallViaEVM config evm (EVM.address (joinVatAddressOf evm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (true, evmSlip, outSlip) true)
    (hgemCode :
      0 < (UInt256.ofNat
        ((evmSlip.lookupAccount (joinGemAddressOf evmSlip)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallTransfer :
      typedCallViaEVM config evmSlip (EVM.address (joinGemAddressOf evmSlip))
        "transferFrom" 0
        [.address evmSlip.executionEnv.source, .address evmSlip.executionEnv.codeOwner,
          joinWadValue I]
        (true, evmTransfer, outTransfer) true)
    (hdecTransfer : config.externalABI.decode? "transferFrom" outTransfer = none) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := joinStore I } evm (.storage vatRef) =
        .ok (.address (joinVatAddressOf evm)) := by
    simpa [joinVatAddressOf] using evalExpr_join_vat evm I
  have hvatGuard :
      evalExpr? config { contract := contract, locals := joinStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [joinVatAddressOf] using evalExpr_join_vatCodeGuard_true evm I hvatCode
  have hslipArgs :
      evalExprs? config { contract := contract, locals := joinStore I } evm
        [.storage ilkRef, .var "usr", asInt256 (.var "wad")] =
          .ok
            [.fixedBytes bytes32Width
              (EVM.Word.toBytesBE
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
              joinUsrValue I, joinWadValue I] :=
    evalExprs_join_slipArgs evm I
  have hslipStmt :
      ExecStmt config { contract := contract, locals := joinStore I } evm
        (.externalCall (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, .var "usr", asInt256 (.var "wad")] "slipRet")
        (.ok { contract := contract, locals := joinLocalsAfterSlip I } evmSlip) := by
    simpa [joinLocalsAfterSlip, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hslipArgs hcallSlip
        (gemJoinDecode_slipReturn outSlip)
  have hgem :
      evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.storage gemRef) = .ok (.address (joinGemAddressOf evmSlip)) :=
    evalExpr_join_gem_afterSlip evmSlip I
  have hgemGuard :
      evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_join_gemCodeGuard_afterSlip_true evmSlip I hgemCode
  have htransferArgs :
      evalExprs? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        [sender, thisAddr, .var "wad"] =
          .ok [.address evmSlip.executionEnv.source, .address evmSlip.executionEnv.codeOwner,
            joinWadValue I] :=
    evalExprs_join_transferFromArgs_afterSlip evmSlip I
  have htransferStmt :
      ExecStmt config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.externalCall (.storage gemRef) "transferFrom" (.intLit 0)
          [sender, thisAddr, .var "wad"] "transferFromOk")
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hgem (by simp [evalExpr?, pure])
      htransferArgs hcallTransfer hdecTransfer
  refine ExecFuncBody.execBlockRevert ?_
  simp only [joinTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_live_true evm I hlive)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_wad_lt_true evm I hwadLow)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
  refine ExecBlock.consNormal hslipStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hgemGuard) ?_
  exact ExecBlock.consRevert htransferStmt

theorem gemJoinJoinBodyRevertsTransferFalse
    (evm evmSlip evmTransfer : EVM.State) (I : ExecutionEnv)
    {outSlip outTransfer : ByteArray}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      0 < (UInt256.ofNat
        ((evm.lookupAccount (joinVatAddressOf evm)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallSlip :
      typedCallViaEVM config evm (EVM.address (joinVatAddressOf evm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (true, evmSlip, outSlip) true)
    (hgemCode :
      0 < (UInt256.ofNat
        ((evmSlip.lookupAccount (joinGemAddressOf evmSlip)).option 0
          (fun acc => acc.code.size))).toNat)
    (hcallTransfer :
      typedCallViaEVM config evmSlip (EVM.address (joinGemAddressOf evmSlip))
        "transferFrom" 0
        [.address evmSlip.executionEnv.source, .address evmSlip.executionEnv.codeOwner,
          joinWadValue I]
        (true, evmTransfer, outTransfer) true)
    (hdecTransfer : config.externalABI.decode? "transferFrom" outTransfer = some [.bool false]) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  have hvat :
      evalExpr? config { contract := contract, locals := joinStore I } evm (.storage vatRef) =
        .ok (.address (joinVatAddressOf evm)) := by
    simpa [joinVatAddressOf] using evalExpr_join_vat evm I
  have hvatGuard :
      evalExpr? config { contract := contract, locals := joinStore I } evm
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    simpa [joinVatAddressOf] using evalExpr_join_vatCodeGuard_true evm I hvatCode
  have hslipArgs :
      evalExprs? config { contract := contract, locals := joinStore I } evm
        [.storage ilkRef, .var "usr", asInt256 (.var "wad")] =
          .ok
            [.fixedBytes bytes32Width
              (EVM.Word.toBytesBE
                (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)),
              joinUsrValue I, joinWadValue I] :=
    evalExprs_join_slipArgs evm I
  have hslipStmt :
      ExecStmt config { contract := contract, locals := joinStore I } evm
        (.externalCall (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, .var "usr", asInt256 (.var "wad")] "slipRet")
        (.ok { contract := contract, locals := joinLocalsAfterSlip I } evmSlip) := by
    simpa [joinLocalsAfterSlip, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hslipArgs hcallSlip
        (gemJoinDecode_slipReturn outSlip)
  have hgem :
      evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.storage gemRef) = .ok (.address (joinGemAddressOf evmSlip)) :=
    evalExpr_join_gem_afterSlip evmSlip I
  have hgemGuard :
      evalExpr? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.binary .gt (.extCodeSize (.storage gemRef)) (.intLit 0)) =
          .ok (.bool true) :=
    evalExpr_join_gemCodeGuard_afterSlip_true evmSlip I hgemCode
  have htransferArgs :
      evalExprs? config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        [sender, thisAddr, .var "wad"] =
          .ok [.address evmSlip.executionEnv.source, .address evmSlip.executionEnv.codeOwner,
            joinWadValue I] :=
    evalExprs_join_transferFromArgs_afterSlip evmSlip I
  have htransferStmt :
      ExecStmt config { contract := contract, locals := joinLocalsAfterSlip I } evmSlip
        (.externalCall (.storage gemRef) "transferFrom" (.intLit 0)
          [sender, thisAddr, .var "wad"] "transferFromOk")
        (.ok { contract := contract, locals := joinLocalsAfterTransferFalse I } evmTransfer) := by
    simpa [joinLocalsAfterTransferFalse, collapseReturns] using
      ExecStmt.externalCallSuccess hgem (by simp [evalExpr?, pure]) htransferArgs
        hcallTransfer hdecTransfer
  refine ExecFuncBody.execBlockRevert ?_
  simp only [joinTransition, nonpayable, checkedExternalCallStmts, List.cons_append,
    List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_live_true evm I hlive)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_wad_lt_true evm I hwadLow)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hvatGuard) ?_
  refine ExecBlock.consNormal hslipStmt ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue hgemGuard) ?_
  refine ExecBlock.consNormal htransferStmt ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_join_transferFromOk_false evmTransfer I))

/-! ### Runtime calldata for `vat.slip(bytes32,address,int256)` -/

abbrev joinSlipSelectorShifted : UInt256 :=
  ⟨0x7cdd3fde00000000000000000000000000000000000000000000000000000000⟩
abbrev joinSlipSelectorWord : UInt256 := ⟨0x7cdd3fde⟩
abbrev joinSlipOutPtr : UInt256 := ⟨128⟩
abbrev joinSlipInSize : UInt256 := ⟨100⟩
abbrev joinSlipEndPtr : UInt256 := ⟨228⟩

noncomputable def joinSlipSelectorMem (mem : ByteArray) : ByteArray :=
  joinSlipSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def joinSlipIlkMem (ilk : UInt256) (mem : ByteArray) : ByteArray :=
  ilk.toByteArray.write 0 (joinSlipSelectorMem mem) 132 32

noncomputable def joinSlipUsrMem (usr : UInt256) (ilk : UInt256) (mem : ByteArray) :
    ByteArray :=
  usr.toByteArray.write 0 (joinSlipIlkMem ilk mem) 164 32

noncomputable def joinSlipCalldataMem (I : ExecutionEnv) (σ : AccountMap)
    (mem : ByteArray) : ByteArray :=
  (joinWadWord I).toByteArray.write 0
    (joinSlipUsrMem (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I) mem) 196 32

theorem joinSlipSelectorMem_size_of_size96 {mem : ByteArray} (hmem : mem.size = 96) :
    (joinSlipSelectorMem mem).size = 160 := by
  unfold joinSlipSelectorMem
  exact toByteArray_write32_size_of_ge mem joinSlipSelectorShifted 128 96 160 hmem
    (by omega) (by decide +native) (by omega)

theorem joinSlipIlkMem_size_of_size96 (ilk : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (joinSlipIlkMem ilk mem).size = 164 := by
  unfold joinSlipIlkMem
  exact toByteArray_write32_size_of_le (joinSlipSelectorMem mem) ilk 132 160 164
    (joinSlipSelectorMem_size_of_size96 hmem)
    (by rw [joinSlipSelectorMem_size_of_size96 hmem]; omega) (by omega)

theorem joinSlipUsrMem_size_of_size96 (usr ilk : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (joinSlipUsrMem usr ilk mem).size = 196 := by
  unfold joinSlipUsrMem
  exact toByteArray_write32_size_of_le (joinSlipIlkMem ilk mem) usr 164 164 196
    (joinSlipIlkMem_size_of_size96 ilk hmem)
    (by rw [joinSlipIlkMem_size_of_size96 ilk hmem]) (by omega)

theorem joinSlipCalldataMem_size_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (joinSlipCalldataMem I σ mem).size = 228 := by
  unfold joinSlipCalldataMem
  exact toByteArray_write32_size_of_le
    (joinSlipUsrMem (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I) mem) (joinWadWord I)
    196 196 228
    (joinSlipUsrMem_size_of_size96 (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I) hmem)
    (by
      rw [joinSlipUsrMem_size_of_size96 (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I)
        hmem])
    (by omega)

theorem joinSlipSelectorMem_read64_of_size96 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinSlipSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold joinSlipSelectorMem
  rw [toByteArray_write_read_below_of_gap joinSlipSelectorShifted mem 128 64
    (by rw [hmem]) (by omega) (by rw [hmem]; decide +native), hread64]

theorem joinSlipIlkMem_read64_of_size96 (ilk : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinSlipIlkMem ilk mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold joinSlipIlkMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [joinSlipSelectorMem_size_of_size96 hmem]; omega) (by omega),
    joinSlipSelectorMem_read64_of_size96 hmem hread64]

theorem joinSlipUsrMem_read64_of_size96 (usr ilk : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinSlipUsrMem usr ilk mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold joinSlipUsrMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [joinSlipIlkMem_size_of_size96 ilk hmem]) (by omega),
    joinSlipIlkMem_read64_of_size96 ilk hmem hread64]

theorem joinSlipCalldataMem_read64_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinSlipCalldataMem I σ mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold joinSlipCalldataMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by
      rw [joinSlipUsrMem_size_of_size96 (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I)
        hmem])
    (by omega),
    joinSlipUsrMem_read64_of_size96 (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I)
      hmem hread64]

theorem joinSlipCalldataMem_read128_4_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (joinSlipCalldataMem I σ mem).readWithPadding 128 4 = vatSlipSelector := by
  have hUsrSize :=
    joinSlipUsrMem_size_of_size96 (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I) hmem
  have hIlkSize := joinSlipIlkMem_size_of_size96 (gemJoinSlotWord ⟨2⟩ σ I) hmem
  have hSelectorSize := joinSlipSelectorMem_size_of_size96 hmem
  unfold joinSlipCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (joinWadWord I)
      (joinSlipUsrMem (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I) mem) 196 128 4
      (by rw [hUsrSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hUsrSize]; decide +native)]
  unfold joinSlipUsrMem
  rw [toByteArray_write_read_below_len_of_gap (joinUsrMaskedWord I)
      (joinSlipIlkMem (gemJoinSlotWord ⟨2⟩ σ I) mem) 164 128 4
      (by rw [hIlkSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hIlkSize]; decide +native)]
  unfold joinSlipIlkMem
  rw [toByteArray_write_read_below_len_of_gap (gemJoinSlotWord ⟨2⟩ σ I)
      (joinSlipSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; decide +native)]
  unfold joinSlipSelectorMem
  rw [toByteArray_write_read_window_of_gap joinSlipSelectorShifted mem 128 0 4
      (by omega) (by norm_num) (by norm_num) (by rw [hmem]; decide +native)]
  decide +native

theorem joinSlipCalldataMem_read132_32_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (joinSlipCalldataMem I σ mem).readWithPadding 132 32 =
      (gemJoinSlotWord ⟨2⟩ σ I).toByteArray := by
  have hUsrSize :=
    joinSlipUsrMem_size_of_size96 (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I) hmem
  have hIlkSize := joinSlipIlkMem_size_of_size96 (gemJoinSlotWord ⟨2⟩ σ I) hmem
  have hSelectorSize := joinSlipSelectorMem_size_of_size96 hmem
  unfold joinSlipCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (joinWadWord I)
      (joinSlipUsrMem (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I) mem) 196 132 32
      (by rw [hUsrSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hUsrSize]; decide +native)]
  unfold joinSlipUsrMem
  rw [toByteArray_write_read_below_len_of_gap (joinUsrMaskedWord I)
      (joinSlipIlkMem (gemJoinSlotWord ⟨2⟩ σ I) mem) 164 132 32
      (by rw [hIlkSize]) (by omega) (by omega) (by omega)
      (by rw [hIlkSize]; decide +native)]
  unfold joinSlipIlkMem
  rw [toByteArray_write_read_back_of_gap (gemJoinSlotWord ⟨2⟩ σ I)
      (joinSlipSelectorMem mem) 132
      (by rw [hSelectorSize]; decide +native)]

theorem joinSlipCalldataMem_read164_32_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (joinSlipCalldataMem I σ mem).readWithPadding 164 32 =
      (joinUsrMaskedWord I).toByteArray := by
  have hUsrSize :=
    joinSlipUsrMem_size_of_size96 (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I) hmem
  have hIlkSize := joinSlipIlkMem_size_of_size96 (gemJoinSlotWord ⟨2⟩ σ I) hmem
  unfold joinSlipCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (joinWadWord I)
      (joinSlipUsrMem (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I) mem) 196 164 32
      (by rw [hUsrSize]) (by omega) (by omega) (by omega)
      (by rw [hUsrSize]; decide +native)]
  unfold joinSlipUsrMem
  rw [toByteArray_write_read_back_of_gap (joinUsrMaskedWord I)
      (joinSlipIlkMem (gemJoinSlotWord ⟨2⟩ σ I) mem) 164
      (by rw [hIlkSize]; decide +native)]

theorem joinSlipCalldataMem_read196_32_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (joinSlipCalldataMem I σ mem).readWithPadding 196 32 =
      (joinWadWord I).toByteArray := by
  have hUsrSize :=
    joinSlipUsrMem_size_of_size96 (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I) hmem
  unfold joinSlipCalldataMem
  rw [toByteArray_write_read_back_of_gap (joinWadWord I)
      (joinSlipUsrMem (joinUsrMaskedWord I) (gemJoinSlotWord ⟨2⟩ σ I) mem) 196
      (by rw [hUsrSize]; decide +native)]

theorem joinSlipCalldataMem_read128_100_of_size96 (I : ExecutionEnv) (σ : AccountMap)
    {mem : ByteArray} (hmem : mem.size = 96) :
    (joinSlipCalldataMem I σ mem).readWithPadding 128 100 =
      vatSlipSelector ++ (gemJoinSlotWord ⟨2⟩ σ I).toByteArray ++
        (joinUsrMaskedWord I).toByteArray ++ (joinWadWord I).toByteArray := by
  have hsize : (joinSlipCalldataMem I σ mem).size = 228 :=
    joinSlipCalldataMem_size_of_size96 I σ hmem
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split (joinSlipCalldataMem I σ mem) 128 4 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (joinSlipCalldataMem I σ mem) 132 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (joinSlipCalldataMem I σ mem) 164 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [joinSlipCalldataMem_read128_4_of_size96 I σ hmem,
    joinSlipCalldataMem_read132_32_of_size96 I σ hmem,
    joinSlipCalldataMem_read164_32_of_size96 I σ hmem,
    joinSlipCalldataMem_read196_32_of_size96 I σ hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

theorem joinAddressOfNat_toNat_masked (w : UInt256) :
    (AccountAddress.ofNat w.toNat).toNat = (UInt256.land w solcAddrMask).toNat := by
  have hmaskAddr :
      AccountAddress.ofNat w.toNat = AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat := by
    apply Fin.ext
    unfold AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    rw [uland_toNat]
    change w.val.val % AccountAddress.size =
      Nat.land w.val.val solcAddrMask.toNat % AccountAddress.size
    rw [show solcAddrMask.toNat = 2 ^ 160 - 1 by decide]
    rw [nat_land_mask_eq_mod]
    rw [show AccountAddress.size = 2 ^ 160 by rfl]
    rw [Nat.mod_mod]
  have hcanon : (UInt256.land w solcAddrMask).toNat < AccountAddress.size := by
    simpa [EVM.addressModulus] using solcAddrMask_result_canonical w
  rw [hmaskAddr]
  unfold AccountAddress.ofNat
  change (UInt256.land w solcAddrMask).toNat % AccountAddress.size =
    (UInt256.land w solcAddrMask).toNat
  exact Nat.mod_eq_of_lt hcanon

set_option maxHeartbeats 1000000 in
theorem joinSlipEncode_eq (I : ExecutionEnv) (σ : AccountMap) {mem : ByteArray}
    (hmem : mem.size = 96) (hwadLow : (joinWadWord I).toNat < intLimit) :
    config.externalABI.encode? "slip"
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ I)),
          joinUsrValue I, joinWadValue I] =
      some ((joinSlipCalldataMem I σ mem).readWithPadding 128 100) := by
  rw [joinSlipCalldataMem_read128_100_of_size96 I σ hmem]
  have hwadInt : (joinWadWord I).toNat < EVM.twoPow 255 := by
    simpa [intLimit, EVM.twoPow] using hwadLow
  have hilkLen : (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ I)).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size (gemJoinSlotWord ⟨2⟩ σ I)
  have hWadBytes :
      UInt256.toByteArray (EVM.wordOfInt (↑(joinWadWord I).toNat : Int)) =
        (joinWadWord I).toByteArray := by
    rw [EVM.wordOfInt, if_neg (by simp)]
    exact congrArg UInt256.toByteArray (u256_ofNat_toNat (joinWadWord I))
  have husrVal :
      (AccountAddress.ofNat (joinUsrWord I).toNat).val = (joinUsrMaskedWord I).toNat := by
    have h := joinAddressOfNat_toNat_masked (joinUsrWord I)
    simpa [joinUsrMaskedWord, u256_land_comm] using h
  have husrWord :
      EVM.word ↑(AccountAddress.ofNat (joinUsrWord I).toNat) = joinUsrMaskedWord I := by
    change UInt256.ofNat (AccountAddress.ofNat (joinUsrWord I).toNat).val = joinUsrMaskedWord I
    rw [husrVal]
    exact u256_ofNat_toNat _
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    bytes32, bytes32Width, addr, int256, int256Int, vatSlipSelector, selectorBytes,
    joinUsrValue, joinWadValue, husrWord, hwadInt, hilkLen,
    word_toBytesBE_toByteArray_eq_toByteArray, ABI.zeroBytes]
  apply ByteArray.ext
  rw [show UInt256.toByteArray (EVM.wordOfInt (↑(joinWadWord I).toNat : Int)) =
      (joinWadWord I).toByteArray from hWadBytes]
  simp [ByteArray.data_append, Array.append_assoc]

/-! ### Runtime calldata for `gem.transferFrom(address,address,uint256)` -/

abbrev joinTransferFromSelectorShifted : UInt256 :=
  ⟨0x23b872dd00000000000000000000000000000000000000000000000000000000⟩
abbrev joinTransferFromSelectorWord : UInt256 := ⟨0x23b872dd⟩
abbrev joinTransferFromOutPtr : UInt256 := ⟨128⟩
abbrev joinTransferFromInSize : UInt256 := ⟨100⟩
abbrev joinTransferFromOutSize : UInt256 := ⟨32⟩
abbrev joinTransferFromEndPtr : UInt256 := ⟨228⟩

noncomputable def joinTransferFromSelectorMem (mem : ByteArray) : ByteArray :=
  joinTransferFromSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def joinTransferFromSrcMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.ofNat I.source.val).toByteArray.write 0 (joinTransferFromSelectorMem mem) 132 32

noncomputable def joinTransferFromDstMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0 (joinTransferFromSrcMem I mem) 164 32

noncomputable def joinTransferFromCalldataMem (I : ExecutionEnv) (mem : ByteArray) :
    ByteArray :=
  (joinWadWord I).toByteArray.write 0 (joinTransferFromDstMem I mem) 196 32

theorem joinTransferFromSelectorMem_size {mem : ByteArray} (hmem : mem.size = 228) :
    (joinTransferFromSelectorMem mem).size = 228 := by
  unfold joinTransferFromSelectorMem
  exact toByteArray_write32_size_of_le mem joinTransferFromSelectorShifted 128 228 228 hmem
    (by rw [hmem]; omega) (by omega)

theorem joinTransferFromSrcMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (joinTransferFromSrcMem I mem).size = 228 := by
  unfold joinTransferFromSrcMem
  exact toByteArray_write32_size_of_le (joinTransferFromSelectorMem mem)
    (UInt256.ofNat I.source.val) 132 228 228
    (joinTransferFromSelectorMem_size hmem)
    (by rw [joinTransferFromSelectorMem_size hmem]; omega) (by omega)

theorem joinTransferFromDstMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (joinTransferFromDstMem I mem).size = 228 := by
  unfold joinTransferFromDstMem
  exact toByteArray_write32_size_of_le (joinTransferFromSrcMem I mem)
    (UInt256.ofNat I.codeOwner.val) 164 228 228
    (joinTransferFromSrcMem_size I hmem)
    (by rw [joinTransferFromSrcMem_size I hmem]; omega) (by omega)

theorem joinTransferFromCalldataMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (joinTransferFromCalldataMem I mem).size = 228 := by
  unfold joinTransferFromCalldataMem
  exact toByteArray_write32_size_of_le (joinTransferFromDstMem I mem) (joinWadWord I)
    196 228 228
    (joinTransferFromDstMem_size I hmem)
    (by rw [joinTransferFromDstMem_size I hmem]; omega) (by omega)

theorem joinTransferFromSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinTransferFromSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold joinTransferFromSelectorMem
  rw [toByteArray_write_read_below_of_gap joinTransferFromSelectorShifted mem 128 64
    (by omega) (by omega) (by rw [hmem]; decide +native), hread64]

theorem joinTransferFromSrcMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinTransferFromSrcMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold joinTransferFromSrcMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [joinTransferFromSelectorMem_size hmem]; omega) (by omega),
    joinTransferFromSelectorMem_read64 hmem hread64]

theorem joinTransferFromDstMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinTransferFromDstMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold joinTransferFromDstMem
  rw [write32_read_below _ _ 164 64 (by rw [toByteArray_size])
    (by rw [joinTransferFromSrcMem_size I hmem]; omega) (by omega),
    joinTransferFromSrcMem_read64 I hmem hread64]

theorem joinTransferFromCalldataMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (joinTransferFromCalldataMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold joinTransferFromCalldataMem
  rw [write32_read_below _ _ 196 64 (by rw [toByteArray_size])
    (by rw [joinTransferFromDstMem_size I hmem]; omega) (by omega),
    joinTransferFromDstMem_read64 I hmem hread64]

theorem joinTransferFromCalldataMem_read128_4 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (joinTransferFromCalldataMem I mem).readWithPadding 128 4 = gemTransferFromSelector := by
  have hDstSize := joinTransferFromDstMem_size I hmem
  have hSrcSize := joinTransferFromSrcMem_size I hmem
  have hSelectorSize := joinTransferFromSelectorMem_size hmem
  unfold joinTransferFromCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (joinWadWord I)
      (joinTransferFromDstMem I mem) 196 128 4
      (by rw [hDstSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hDstSize]; decide +native)]
  unfold joinTransferFromDstMem
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.codeOwner.val)
      (joinTransferFromSrcMem I mem) 164 128 4
      (by rw [hSrcSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSrcSize]; decide +native)]
  unfold joinTransferFromSrcMem
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.source.val)
      (joinTransferFromSelectorMem mem) 132 128 4
      (by rw [hSelectorSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSelectorSize]; decide +native)]
  unfold joinTransferFromSelectorMem
  rw [toByteArray_write_read_window_of_gap joinTransferFromSelectorShifted mem 128 0 4
      (by omega) (by norm_num) (by norm_num) (by rw [hmem]; decide +native)]
  decide +native

theorem joinTransferFromCalldataMem_read132_32 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (joinTransferFromCalldataMem I mem).readWithPadding 132 32 =
      (UInt256.ofNat I.source.val).toByteArray := by
  have hDstSize := joinTransferFromDstMem_size I hmem
  have hSrcSize := joinTransferFromSrcMem_size I hmem
  have hSelectorSize := joinTransferFromSelectorMem_size hmem
  unfold joinTransferFromCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (joinWadWord I)
      (joinTransferFromDstMem I mem) 196 132 32
      (by rw [hDstSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hDstSize]; decide +native)]
  unfold joinTransferFromDstMem
  rw [toByteArray_write_read_below_len_of_gap (UInt256.ofNat I.codeOwner.val)
      (joinTransferFromSrcMem I mem) 164 132 32
      (by rw [hSrcSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hSrcSize]; decide +native)]
  unfold joinTransferFromSrcMem
  rw [toByteArray_write_read_back_of_gap (UInt256.ofNat I.source.val)
      (joinTransferFromSelectorMem mem) 132
      (by rw [hSelectorSize]; decide +native)]

theorem joinTransferFromCalldataMem_read164_32 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (joinTransferFromCalldataMem I mem).readWithPadding 164 32 =
      (UInt256.ofNat I.codeOwner.val).toByteArray := by
  have hDstSize := joinTransferFromDstMem_size I hmem
  have hSrcSize := joinTransferFromSrcMem_size I hmem
  unfold joinTransferFromCalldataMem
  rw [toByteArray_write_read_below_len_of_gap (joinWadWord I)
      (joinTransferFromDstMem I mem) 196 164 32
      (by rw [hDstSize]; omega) (by omega) (by omega) (by omega)
      (by rw [hDstSize]; decide +native)]
  unfold joinTransferFromDstMem
  rw [toByteArray_write_read_back_of_gap (UInt256.ofNat I.codeOwner.val)
      (joinTransferFromSrcMem I mem) 164
      (by rw [hSrcSize]; decide +native)]

theorem joinTransferFromCalldataMem_read196_32 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (joinTransferFromCalldataMem I mem).readWithPadding 196 32 =
      (joinWadWord I).toByteArray := by
  have hDstSize := joinTransferFromDstMem_size I hmem
  unfold joinTransferFromCalldataMem
  rw [toByteArray_write_read_back_of_gap (joinWadWord I) (joinTransferFromDstMem I mem) 196
      (by rw [hDstSize]; decide +native)]

theorem joinTransferFromCalldataMem_read128_100 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (joinTransferFromCalldataMem I mem).readWithPadding 128 100 =
      gemTransferFromSelector ++ (UInt256.ofNat I.source.val).toByteArray ++
        (UInt256.ofNat I.codeOwner.val).toByteArray ++ (joinWadWord I).toByteArray := by
  have hsize : (joinTransferFromCalldataMem I mem).size = 228 :=
    joinTransferFromCalldataMem_size I hmem
  rw [show 100 = 4 + 96 from rfl,
    byteArray_readWithPadding_split (joinTransferFromCalldataMem I mem) 128 4 96
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 96 = 32 + 64 from rfl,
    byteArray_readWithPadding_split (joinTransferFromCalldataMem I mem) 132 32 64
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [show 64 = 32 + 32 from rfl,
    byteArray_readWithPadding_split (joinTransferFromCalldataMem I mem) 164 32 32
      (by omega) (by omega) (by omega) (by omega) (by omega) (by rw [hsize])]
  rw [joinTransferFromCalldataMem_read128_4 I hmem,
    joinTransferFromCalldataMem_read132_32 I hmem,
    joinTransferFromCalldataMem_read164_32 I hmem,
    joinTransferFromCalldataMem_read196_32 I hmem]
  apply ByteArray.ext
  simp [ByteArray.data_append, Array.append_assoc]

set_option maxHeartbeats 1000000 in
theorem joinTransferFromEncode_eq (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 228) :
    config.externalABI.encode? "transferFrom"
        [.address I.source, .address I.codeOwner, joinWadValue I] =
      some ((joinTransferFromCalldataMem I mem).readWithPadding 128 100) := by
  rw [joinTransferFromCalldataMem_read128_100 I hmem]
  have hsrcWord :
      EVM.word ↑I.source = UInt256.ofNat I.source.val := by rfl
  have hownerWord :
      EVM.word ↑I.codeOwner = UInt256.ofNat I.codeOwner.val := by rfl
  have hwadInt : (joinWadWord I).toNat < EVM.twoPow 256 := (joinWadWord I).val.isLt
  have hWadBytes :
      UInt256.toByteArray (EVM.word (joinWadWord I).toNat) =
        (joinWadWord I).toByteArray := by
    exact congrArg UInt256.toByteArray (u256_ofNat_toNat (joinWadWord I))
  simp [config, externalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
    addr, uint256, uint256Int, gemTransferFromSelector, selectorBytes,
    joinWadValue, hsrcWord, hownerWord, hwadInt,
    word_toBytesBE_toByteArray_eq_toByteArray]
  apply ByteArray.ext
  rw [show UInt256.toByteArray (EVM.word (joinWadWord I).toNat) =
      (joinWadWord I).toByteArray from hWadBytes]
  simp [ByteArray.data_append, Array.append_assoc]

theorem joinTransferFromReturnWrite_size {base out : ByteArray} (L : ℕ)
    (hbase : base.size = 228) (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (out.write 0 base 128 L).size = 228 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hbase
  · rw [write_eq_gen out base 128 L (by omega) hLo (by rw [hbase]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, hbase]
    omega

theorem joinTransferFromReturnWrite_read64 {base out : ByteArray} (L : ℕ)
    (hbase : base.size = 228)
    (hread64 : base.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hL : L ≤ 32) (hLo : L ≤ out.size) :
    (out.write 0 base 128 L).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact hread64
  · rw [write_read_below_gen out base 128 L 64 (by omega) hLo
      (by rw [hbase]; omega) (by omega), hread64]

theorem joinTransferFromReturnWrite_read128_32 {base out : ByteArray}
    (hbase : base.size = 228) (ho32 : 32 ≤ out.size) :
    (out.write 0 base 128 32).readWithPadding 128 32 =
      out.extract 0 32 :=
  write32_read_back out base 128 ho32 (by rw [hbase]; omega)

theorem joinTransferFromMin32_toNat_of_ge {n : ℕ}
    (h32 : 32 ≤ n) (hsize : n < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat n)).toNat = 32 := by
  show (if (⟨32⟩ : UInt256) ≤ UInt256.ofNat n then (⟨32⟩ : UInt256)
    else UInt256.ofNat n).toNat = 32
  rw [if_pos]
  · rfl
  · show (32 : ℕ) ≤ (UInt256.ofNat n).val.val
    rw [show (UInt256.ofNat n).val.val = (UInt256.ofNat n).toNat from rfl,
      ulit_toNat' n hsize]
    exact h32

theorem joinTransferFromMin32_toNat_of_lt {n : ℕ} (h : n < 32) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat n)).toNat = n := by
  show (if (⟨32⟩ : UInt256) ≤ UInt256.ofNat n then (⟨32⟩ : UInt256)
    else UInt256.ofNat n).toNat = n
  have hnsize : n < UInt256.size := by
    have h32 : 32 < UInt256.size := by norm_num [UInt256.size]
    omega
  rw [if_neg, ulit_toNat' n hnsize]
  · show ¬ (32 : ℕ) ≤ (UInt256.ofNat n).val.val
    rw [show (UInt256.ofNat n).val.val = (UInt256.ofNat n).toNat from rfl,
      ulit_toNat' n hnsize]
    omega

set_option maxHeartbeats 1000000 in
theorem RD.gemJoinToSlipExtcodesizeGuard
    {cA σ I} {g sel : UInt256}
    {s0 : State} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g) s0 ⟨634⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g) s0 ⟨717⟩
      (gemJoinAddressReturnWord ⟨1⟩ σ I :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        ⟨0⟩ :: ⟨128⟩ :: joinSlipInSize :: joinSlipOutPtr :: ⟨0⟩ ::
        joinSlipEndPtr :: joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (joinSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) ByteArray.empty
      (cA, σ) k' C' := by
  let target := gemJoinAddressReturnWord ⟨1⟩ σ I
  let rawTarget := gemJoinSlotWord ⟨1⟩ σ I
  let ilk := gemJoinSlotWord ⟨2⟩ σ I
  have rd635 := rd.jumpdest (by decide +native) (by evm_ov)
  have rd637 := rd635.push1 ⟨1⟩ (by decide +native) (by evm_ov)
  obtain ⟨k638, C638, rd638Raw⟩ := rd637.sload (by decide +native) (by evm_ov)
  have rd638 : RD gemJoinBytecode I (Sat256.ofUInt256 g) s0 ⟨638⟩
      (rawTarget :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k638 C638 := by
    simpa [rawTarget, gemJoinSlotWord, solcSlotWord] using rd638Raw
  have rd640 := rd638.push1 ⟨2⟩ (by decide +native) (by evm_ov)
  obtain ⟨k641, C641, rd641Raw⟩ := rd640.sload (by decide +native) (by evm_ov)
  have rd641 : RD gemJoinBytecode I (Sat256.ofUInt256 g) s0 ⟨641⟩
      (ilk :: rawTarget :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k641 C641 := by
    simpa [ilk, gemJoinSlotWord, solcSlotWord] using rd641Raw
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ solcFreePtrMem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (solcFreePtrMem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [solcFreePtrMem_size]; decide) (by decide) solcFreePtrMem_read64
  have hSlipMem : (joinSlipCalldataMem I σ solcFreePtrMem).size = 228 :=
    joinSlipCalldataMem_size_of_size96 I σ solcFreePtrMem_size
  have hSlipRead64 :
      (joinSlipCalldataMem I σ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    joinSlipCalldataMem_read64_of_size96 I σ solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Slip :
      (if (⟨64⟩ : UInt256).toNat ≥ (joinSlipCalldataMem I σ solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((joinSlipCalldataMem I σ solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hSlipMem]; decide) (by decide) hSlipRead64
  have hUsrMaskedCanon : (joinUsrMaskedWord I).toNat < EVM.addressModulus := by
    simpa [joinUsrMaskedWord, u256_land_comm] using
      solcAddrMask_result_canonical (joinUsrWord I)
  have hSolcMaskLiteral :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask := by
    decide +native
  have hUsrMask :
      UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (joinUsrMaskedWord I) =
        joinUsrMaskedWord I := by
    rw [hSolcMaskLiteral]
    exact solcAddrMask_clean_left hUsrMaskedCanon
  have hInSizeExpr :
      UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨100⟩ =
        (⟨100⟩ : UInt256) := by
    decide +native
  have hEndPtrExpr :
      (⟨128⟩ : UInt256) + ⟨100⟩ = (⟨228⟩ : UInt256) := by
    decide +native
  have hUsrMemEq :
      (UInt256.land
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
          (joinUsrMaskedWord I)).toByteArray.write 0
          (joinSlipIlkMem ilk solcFreePtrMem)
          ((⟨128⟩ : UInt256) + (⟨36⟩ : UInt256)).toNat 32 =
        joinSlipUsrMem (joinUsrMaskedWord I) ilk solcFreePtrMem := by
    rw [hUsrMask]
    change (joinUsrMaskedWord I).toByteArray.write 0
        (joinSlipIlkMem ilk solcFreePtrMem) 164 32 =
      joinSlipUsrMem (joinUsrMaskedWord I) ilk solcFreePtrMem
    rfl
  have hSelectorShift :
      UInt256.shiftLeft (⟨1047437295⟩ : UInt256) ⟨225⟩ =
        joinSlipSelectorShifted := by
    decide +native
  have hSelectorMemEq :
      (UInt256.shiftLeft (⟨1047437295⟩ : UInt256) ⟨225⟩).toByteArray.write 0
          solcFreePtrMem 128 32 =
        joinSlipSelectorMem solcFreePtrMem := by
    rw [hSelectorShift]
    rfl
  have rd645 := evm_run rd641 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost hmload64 (by decide) (by evm_ov)]
  have rd645' : RD gemJoinBytecode I (Sat256.ofUInt256 g) s0 ⟨645⟩
      (⟨128⟩ :: ⟨64⟩ :: ilk :: rawTarget :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ)
      (k641 + 1 + 1 + 1) (C641 + 3 + 3 + (0 + 3)) := by
    simpa [ilk, rawTarget] using rd645
  have rd717 := evm_run rd645' with [
    push4 ⟨1047437295⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 6 (joinSlipSelectorMem solcFreePtrMem) (UInt256.ofNat 5)
      (by decide +native) mem_cost hSelectorMemEq (by decide) (by evm_ov),
    push1 ⟨4⟩,
    dup2,
    add,
    swap3,
    swap1,
    swap3,
    raw mstore 3 (joinSlipIlkMem ilk solcFreePtrMem) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    dup6,
    dup2,
    and,
    push1 ⟨36⟩,
    dup5,
    add,
    raw mstore 3 (joinSlipUsrMem (joinUsrMaskedWord I) ilk solcFreePtrMem)
      (UInt256.ofNat 7) (by decide +native) mem_cost hUsrMemEq (by decide) (by evm_ov),
    push1 ⟨68⟩,
    dup4,
    add,
    dup6,
    swap1,
    raw mstore 3 (joinSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
      mem_cost hmload64Slip (by decide) (by evm_ov),
    swap3,
    and,
    swap2,
    push4 joinSlipSelectorWord,
    swap2,
    push1 ⟨100⟩,
    dup1,
    dup3,
    add,
    swap3,
    push1 ⟨0⟩,
    swap3,
    swap1,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    dup4,
    dup8,
    dup1]
  have hpc717 :
      (⟨645⟩ : UInt256) + UInt256.ofNat 5 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 5 +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨717⟩ := by
    decide +native
  rw [hpc717] at rd717
  exact ⟨_, _, by
    simpa [target, rawTarget, ilk, joinSlipSelectorShifted, joinSlipSelectorWord,
      joinSlipSelectorMem, joinSlipIlkMem, joinSlipUsrMem, joinSlipCalldataMem,
      joinSlipInSize, joinSlipOutPtr, joinSlipEndPtr, gemJoinAddressReturnWord,
      gemJoinSlotWord, solcSlotWord, solcAddrMask, hSolcMaskLiteral, hInSizeExpr,
      hEndPtrExpr, hUsrMask, u256_land_comm,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide +native,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨100⟩ = ⟨100⟩
        from by decide +native,
      show (⟨128⟩ : UInt256) + ⟨100⟩ = ⟨228⟩ from by decide +native] using rd717⟩

theorem RD.gemJoinToSlipCallReady
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨634⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (gemJoinAddressReturnWord ⟨1⟩ σ I) ≠ ⟨0⟩) :
    ∃ gasWord k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨732⟩
      (gasWord :: gemJoinAddressReturnWord ⟨1⟩ σ I :: ⟨0⟩ :: ⟨128⟩ ::
        joinSlipInSize :: joinSlipOutPtr :: ⟨0⟩ :: joinSlipEndPtr ::
        joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (joinSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, rd634⟩ := hreach
  obtain ⟨_, _, rd717⟩ := RD.gemJoinToSlipExtcodesizeGuard rd634
  obtain ⟨gasWord, k, C, rd732⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨717⟩) (okPc := ⟨729⟩) rd717
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by evm_ov)
  exact ⟨gasWord, k, C, by simpa [joinSlipOutPtr] using rd732⟩

theorem RD.gemJoinSlipNoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨634⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (gemJoinAddressReturnWord ⟨1⟩ σ I) = ⟨0⟩) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd634⟩ := hreach
  obtain ⟨_, _, rd717⟩ := RD.gemJoinToSlipExtcodesizeGuard rd634
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨717⟩) (okPc := ⟨729⟩) rd717
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp)

theorem RD.gemJoinSlipPostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨634⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (gemJoinAddressReturnWord ⟨1⟩ σ I) ≠ ⟨0⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k C : ℕ),
      RD gemJoinBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨733⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: joinSlipEndPtr :: joinSlipSelectorWord ::
          gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
          ⟨254⟩ :: sel :: [])
        (joinSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) out (cA', σ') k C
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ I)),
          joinUsrValue I, joinWadValue I]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd732⟩ := RD.gemJoinToSlipCallReady hreach hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k733, C733, hΘpack, rd733raw, houtSize⟩ :=
    RD.call rd732 (by decide +native) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k733, C733, ?_, ?_, houtSize⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          (⟨128⟩ : UInt256).toNat joinSlipInSize.toNat)
          joinSlipOutPtr.toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
      unfold joinSlipInSize joinSlipOutPtr
      decide +native
    have hmin : (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat = 0 := by
      have hle : (⟨0⟩ : UInt256) ≤ UInt256.ofNat out.size := by
        show (0 : Nat) ≤ (UInt256.ofNat out.size).val.val
        exact Nat.zero_le _
      simp [min, hle]
    have rd733 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨733⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: joinSlipEndPtr :: joinSlipSelectorWord ::
          gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
          ⟨254⟩ :: sel :: [])
        (out.write 0 (joinSlipCalldataMem I σ solcFreePtrMem) joinSlipOutPtr.toNat
          (min (⟨0⟩ : UInt256) (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 8) out (cA', σ') k733 C733 :=
      haw ▸ rd733raw
    rw [hmin, byteArray_write_len_zero] at rd733
    exact rd733
  · have htgt :
        EVM.address (joinVatAddressOf
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ I) := by
      apply Fin.ext
      simp [EVM.address, EVM.uintN, joinVatAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
      rw [show EVM.twoPow 160 = AccountAddress.size by rfl, Nat.mod_mod]
    refine Reasoning.Theory.callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := gemJoinAddressReturnWord ⟨1⟩ σ I)
      (mem := joinSlipCalldataMem I σ solcFreePtrMem) (inOff := ⟨128⟩)
      (inSize := joinSlipInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from by
        simpa [initState] using h]; decide))
      htgt
      (by simpa [joinSlipInSize] using
        joinSlipEncode_eq I σ solcFreePtrMem_size hwadLow)
      ?_
    simpa [initState, hperm] using hΘ

theorem RD.gemJoinSlipCallFailure
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨733⟩
      (⟨0⟩ :: joinSlipEndPtr :: joinSlipSelectorWord ::
        gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      mem aw out acc k C)
    (houtSize : out.size < UInt256.size) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨733⟩) (okPc := ⟨749⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    houtSize (by simp)

theorem RD.gemJoinSlipCallDepthLimit
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨634⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ
        (gemJoinAddressReturnWord ⟨1⟩ σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨733⟩
      (⟨0⟩ :: joinSlipEndPtr :: joinSlipSelectorWord ::
        gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (joinSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, _, rd732⟩ := RD.gemJoinToSlipCallReady hreach hcodeSize
  obtain ⟨k733, C733, rd733raw⟩ :=
    RD.callDepthLimit rd732 (by decide +native)
      (by simpa [initState] using hdepth) (by simp)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        (⟨128⟩ : UInt256).toNat joinSlipInSize.toNat)
        joinSlipOutPtr.toNat (⟨0⟩ : UInt256).toNat) = UInt256.ofNat 8 := by
    unfold joinSlipInSize joinSlipOutPtr
    decide +native
  have hmin :
      (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide +native
  have rd733 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨733⟩
      (⟨0⟩ :: joinSlipEndPtr :: joinSlipSelectorWord ::
        gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (ByteArray.empty.write 0 (joinSlipCalldataMem I σ solcFreePtrMem)
        joinSlipOutPtr.toNat
        (min (⟨0⟩ : UInt256) (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 8) ByteArray.empty (cA, σ) k733 C733 :=
    haw ▸ rd733raw
  rw [hmin, byteArray_write_len_zero] at rd733
  exact ⟨k733, C733, rd733⟩

theorem RD.gemJoinSlipCallSuccessToTransferSetup
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨733⟩
      (⟨1⟩ :: joinSlipEndPtr :: joinSlipSelectorWord ::
        gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      mem aw out acc k C) :
    ∃ k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨752⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem aw out acc k' C' := by
  obtain ⟨_, _, rd751⟩ :=
    RD.solcCallSuccessGuardOk (pc := ⟨733⟩) (okPc := ⟨749⟩) rd
      (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
      (by simp)
  exact ⟨_, _, RD.pop rd751 (by decide +native) (by simp)⟩

set_option maxHeartbeats 1000000 in
theorem RD.gemJoinToTransferFromExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cAcur : Batteries.RBSet AccountAddress compare} {σcur : AccountMap}
    {outSlip : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨752⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (joinSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cAcur, σcur) k C) :
    ∃ k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨831⟩
      (gemJoinAddressReturnWord ⟨3⟩ σcur I :: gemJoinAddressReturnWord ⟨3⟩ σcur I ::
        ⟨0⟩ :: ⟨128⟩ :: joinTransferFromInSize :: joinTransferFromOutPtr ::
        joinTransferFromOutSize :: joinTransferFromEndPtr :: joinTransferFromSelectorWord ::
        gemJoinAddressReturnWord ⟨3⟩ σcur I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) outSlip (cAcur, σcur) k' C' := by
  let target := gemJoinAddressReturnWord ⟨3⟩ σcur I
  let rawTarget := gemJoinSlotWord ⟨3⟩ σcur I
  have rd754 := rd.push1 ⟨3⟩ (by decide +native) (by evm_ov)
  obtain ⟨k755, C755, rd755raw⟩ := rd754.sload (by decide +native) (by evm_ov)
  have rd755 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨755⟩
      (rawTarget :: joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (joinSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cAcur, σcur) k755 C755 := by
    simpa [rawTarget, gemJoinSlotWord, solcSlotWord] using rd755raw
  have hSlipMem :
      (joinSlipCalldataMem I σ solcFreePtrMem).size = 228 :=
    joinSlipCalldataMem_size_of_size96 I σ solcFreePtrMem_size
  have hSlipRead64 :
      (joinSlipCalldataMem I σ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    joinSlipCalldataMem_read64_of_size96 I σ solcFreePtrMem_size solcFreePtrMem_read64
  have hmload64Slip :
      (if (⟨64⟩ : UInt256).toNat ≥ (joinSlipCalldataMem I σ solcFreePtrMem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((joinSlipCalldataMem I σ solcFreePtrMem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hSlipMem]; decide) (by decide) hSlipRead64
  have hTransferMem :
      (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem)).size = 228 :=
    joinTransferFromCalldataMem_size I hSlipMem
  have hTransferRead64 :
      (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem)).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    joinTransferFromCalldataMem_read64 I hSlipMem hSlipRead64
  have hmload64Transfer :
      (if (⟨64⟩ : UInt256).toNat ≥
            (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem)).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem)).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hTransferMem]; decide) (by decide) hTransferRead64
  have hSelectorShift :
      UInt256.shiftLeft (⟨599290589⟩ : UInt256) ⟨224⟩ =
        joinTransferFromSelectorShifted := by
    decide +native
  have hSelectorMemEq :
      (UInt256.shiftLeft (⟨599290589⟩ : UInt256) ⟨224⟩).toByteArray.write 0
          (joinSlipCalldataMem I σ solcFreePtrMem) 128 32 =
        joinTransferFromSelectorMem (joinSlipCalldataMem I σ solcFreePtrMem) := by
    rw [hSelectorShift]
    rfl
  have hSrcMemEq :
      (UInt256.ofNat I.source.val).toByteArray.write 0
          (joinTransferFromSelectorMem (joinSlipCalldataMem I σ solcFreePtrMem))
          ((⟨128⟩ : UInt256) + ⟨4⟩).toNat 32 =
        joinTransferFromSrcMem I (joinSlipCalldataMem I σ solcFreePtrMem) := by
    change (UInt256.ofNat I.source.val).toByteArray.write 0
        (joinTransferFromSelectorMem (joinSlipCalldataMem I σ solcFreePtrMem)) 132 32 =
      joinTransferFromSrcMem I (joinSlipCalldataMem I σ solcFreePtrMem)
    rfl
  have hDstMemEq :
      (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
          (joinTransferFromSrcMem I (joinSlipCalldataMem I σ solcFreePtrMem))
          ((⟨128⟩ : UInt256) + ⟨36⟩).toNat 32 =
        joinTransferFromDstMem I (joinSlipCalldataMem I σ solcFreePtrMem) := by
    change (UInt256.ofNat I.codeOwner.val).toByteArray.write 0
        (joinTransferFromSrcMem I (joinSlipCalldataMem I σ solcFreePtrMem)) 164 32 =
      joinTransferFromDstMem I (joinSlipCalldataMem I σ solcFreePtrMem)
    rfl
  have hWadMemEq :
      (joinWadWord I).toByteArray.write 0
          (joinTransferFromDstMem I (joinSlipCalldataMem I σ solcFreePtrMem))
          ((⟨128⟩ : UInt256) + ⟨68⟩).toNat 32 =
        joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem) := by
    change (joinWadWord I).toByteArray.write 0
        (joinTransferFromDstMem I (joinSlipCalldataMem I σ solcFreePtrMem)) 196 32 =
      joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem)
    rfl
  have rd831 := evm_run rd755 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
      mem_cost hmload64Slip (by decide) (by evm_ov),
    push4 ⟨599290589⟩,
    push1 ⟨224⟩,
    shl,
    dup2,
    raw mstore 0 (joinTransferFromSelectorMem (joinSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) (by decide +native) mem_cost hSelectorMemEq (by decide) (by evm_ov),
    caller,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (joinTransferFromSrcMem I (joinSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) (by decide +native) mem_cost hSrcMemEq (by decide) (by evm_ov),
    address,
    push1 ⟨36⟩,
    dup3,
    add,
    raw mstore 0 (joinTransferFromDstMem I (joinSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) (by decide +native) mem_cost hDstMemEq (by decide) (by evm_ov),
    push1 ⟨68⟩,
    dup2,
    add,
    dup7,
    swap1,
    raw mstore 0
      (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) (by decide +native) mem_cost hWadMemEq (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
      mem_cost hmload64Transfer (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap1,
    swap3,
    and,
    swap4,
    pop,
    push4 joinTransferFromSelectorWord,
    swap3,
    pop,
    push1 ⟨100⟩,
    dup1,
    dup3,
    add,
    swap3,
    push1 ⟨32⟩,
    swap3,
    swap1,
    swap2,
    swap1,
    dup3,
    swap1,
    sub,
    add,
    dup2,
    push1 ⟨0⟩,
    dup8,
    dup1]
  have hpc831 :
      (⟨755⟩ : UInt256) + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 5 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 5 + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨831⟩ := by
    decide +native
  exact ⟨_, _, by
    simpa [target, rawTarget, joinTransferFromSelectorShifted,
      joinTransferFromSelectorWord, joinTransferFromSelectorMem, joinTransferFromSrcMem,
      joinTransferFromDstMem, joinTransferFromCalldataMem, joinTransferFromInSize,
      joinTransferFromOutPtr, joinTransferFromOutSize, joinTransferFromEndPtr,
      gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord, hpc831, UInt256.add,
      UInt256.sub,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide +native,
      show UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩ + ⟨100⟩ = ⟨100⟩
        from by decide +native,
      show (⟨128⟩ : UInt256) + ⟨100⟩ = ⟨228⟩ from by decide +native]
      using rd831⟩

theorem RD.gemJoinToTransferFromCallReady
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cAcur : Batteries.RBSet AccountAddress compare} {σcur : AccountMap}
    {outSlip : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨752⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (joinSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cAcur, σcur) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σcur
        (gemJoinAddressReturnWord ⟨3⟩ σcur I) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨846⟩
      (gasWord :: gemJoinAddressReturnWord ⟨3⟩ σcur I :: ⟨0⟩ :: ⟨128⟩ ::
        joinTransferFromInSize :: joinTransferFromOutPtr :: joinTransferFromOutSize ::
        joinTransferFromEndPtr :: joinTransferFromSelectorWord ::
        gemJoinAddressReturnWord ⟨3⟩ σcur I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) outSlip (cAcur, σcur) k' C' := by
  obtain ⟨_, _, rd831⟩ := RD.gemJoinToTransferFromExtcodesizeGuard rd
  obtain ⟨gasWord, k, C, rd846⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨831⟩) (okPc := ⟨843⟩) rd831
      hcodeSize
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by jump_dest) (by decide +native)
      (by decide +native) (by decide +native) (by evm_ov)
  exact ⟨gasWord, k, C, by simpa [joinTransferFromOutPtr] using rd846⟩

theorem RD.gemJoinTransferFromNoCode
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cAcur : Batteries.RBSet AccountAddress compare} {σcur : AccountMap}
    {outSlip : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨752⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (joinSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cAcur, σcur) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σcur
        (gemJoinAddressReturnWord ⟨3⟩ σcur I) = ⟨0⟩) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd831⟩ := RD.gemJoinToTransferFromExtcodesizeGuard rd
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨831⟩) (okPc := ⟨843⟩) rd831
    hcodeSize
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by simp)

theorem RD.gemJoinTransferFromPostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cAcur : Batteries.RBSet AccountAddress compare} {σcur : AccountMap}
    {Acur : Substate}
    {outSlip : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨752⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (joinSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cAcur, σcur) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σcur
        (gemJoinAddressReturnWord ⟨3⟩ σcur I) ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (outTransfer : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨847⟩
      ((if z then ⟨1⟩ else ⟨0⟩) :: joinTransferFromEndPtr ::
          joinTransferFromSelectorWord :: gemJoinAddressReturnWord ⟨3⟩ σcur I ::
          joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
        (outTransfer.write 0
          (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem))
          joinTransferFromOutPtr.toNat
          (min joinTransferFromOutSize (UInt256.ofNat outTransfer.size)).toNat)
        (UInt256.ofNat 8) outTransfer (cA', σ') k' C'
    ∧ typedCallViaEVM config
        { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σcur, substate := Acur, createdAccounts := cAcur }
        (EVM.address (joinGemAddressOf
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σcur, substate := Acur, createdAccounts := cAcur })) "transferFrom" 0
        [.address I.source, .address I.codeOwner, joinWadValue I]
        (z,
          { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ', substate := A', createdAccounts := cA' },
          outTransfer) true
    ∧ outTransfer.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd846⟩ := RD.gemJoinToTransferFromCallReady rd hcodeSize
  obtain ⟨cA', σ', z, outTransfer, A_in, callGas, k847, C847, hΘpack, rd847raw,
      houtSize⟩ :=
    RD.call rd846 (by decide +native) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, outTransfer, A', k847, C847, ?_, ?_, houtSize⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
          (⟨128⟩ : UInt256).toNat joinTransferFromInSize.toNat)
          joinTransferFromOutPtr.toNat joinTransferFromOutSize.toNat) =
          UInt256.ofNat 8 := by
      unfold joinTransferFromInSize joinTransferFromOutPtr joinTransferFromOutSize
      decide +native
    exact haw ▸ rd847raw
  · have htgt :
        EVM.address (joinGemAddressOf
            { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σcur, substate := Acur, createdAccounts := cAcur }) =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σcur I) := by
      apply Fin.ext
      simp [EVM.address, EVM.uintN, joinGemAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
      rw [show EVM.twoPow 160 = AccountAddress.size by rfl, Nat.mod_mod]
    refine Reasoning.Theory.callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := gemJoinAddressReturnWord ⟨3⟩ σcur I)
      (mem := joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem))
      (inOff := ⟨128⟩) (inSize := joinTransferFromInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from by
        simpa [initState] using h]; decide))
      htgt
      (by
        have hSlipMem :
            (joinSlipCalldataMem I σ solcFreePtrMem).size = 228 :=
          joinSlipCalldataMem_size_of_size96 I σ solcFreePtrMem_size
        simpa [joinTransferFromInSize] using
          joinTransferFromEncode_eq I hSlipMem)
      ?_
    simpa [initState, hperm] using hΘ

theorem RD.gemJoinTransferFromCallFailure
    {cA gh bl σ σ₀ A I} {g sel gemTarget : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outTransfer : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨847⟩
      (⟨0⟩ :: joinTransferFromEndPtr :: joinTransferFromSelectorWord ::
        gemTarget :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      mem aw outTransfer acc k C)
    (houtSize : outTransfer.size < UInt256.size) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨847⟩) (okPc := ⟨863⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    houtSize (by simp)

theorem RD.gemJoinTransferFromCallDepthLimit
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {cAcur : Batteries.RBSet AccountAddress compare} {σcur : AccountMap}
    {outSlip : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨752⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (joinSlipCalldataMem I σ solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cAcur, σcur) k C)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σcur
        (gemJoinAddressReturnWord ⟨3⟩ σcur I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024) :
    ∃ k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨847⟩
      (⟨0⟩ :: joinTransferFromEndPtr :: joinTransferFromSelectorWord ::
        gemJoinAddressReturnWord ⟨3⟩ σcur I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem))
      (UInt256.ofNat 8) ByteArray.empty (cAcur, σcur) k' C' := by
  obtain ⟨_, _, _, rd846⟩ := RD.gemJoinToTransferFromCallReady rd hcodeSize
  obtain ⟨k847, C847, rd847raw⟩ :=
    RD.callDepthLimit rd846 (by decide +native)
      (by simpa [initState] using hdepth) (by simp)
  have haw :
      UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 8).toNat
        (⟨128⟩ : UInt256).toNat joinTransferFromInSize.toNat)
        joinTransferFromOutPtr.toNat joinTransferFromOutSize.toNat) = UInt256.ofNat 8 := by
    unfold joinTransferFromInSize joinTransferFromOutPtr joinTransferFromOutSize
    decide +native
  have hmin :
      (min joinTransferFromOutSize (UInt256.ofNat ByteArray.empty.size)).toNat = 0 := by
    decide +native
  have rd847 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨847⟩
      (⟨0⟩ :: joinTransferFromEndPtr :: joinTransferFromSelectorWord ::
        gemJoinAddressReturnWord ⟨3⟩ σcur I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (ByteArray.empty.write 0
        (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ solcFreePtrMem))
        joinTransferFromOutPtr.toNat
        (min joinTransferFromOutSize (UInt256.ofNat ByteArray.empty.size)).toNat)
      (UInt256.ofNat 8) ByteArray.empty (cAcur, σcur) k847 C847 :=
    haw ▸ rd847raw
  rw [hmin, byteArray_write_len_zero] at rd847
  exact ⟨k847, C847, rd847⟩

theorem RD.gemJoinTransferFromCallSuccessToDecode
    {cA gh bl σ σ₀ A I} {g sel gemTarget : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outTransfer : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨847⟩
      (⟨1⟩ :: joinTransferFromEndPtr :: joinTransferFromSelectorWord ::
        gemTarget :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      mem aw outTransfer acc k C) :
    ∃ k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨865⟩
      (joinTransferFromEndPtr :: joinTransferFromSelectorWord ::
        gemTarget :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      mem aw outTransfer acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨847⟩) (okPc := ⟨863⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by jump_dest) (by decide +native) (by decide +native)
    (by simp)

theorem RD.gemJoinTransferFromReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g sel gemTarget : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outTransfer : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨865⟩
      (joinTransferFromEndPtr :: joinTransferFromSelectorWord ::
        gemTarget :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer acc k C)
    (hshort : outTransfer.size < 32)
    (hhi : outTransfer.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨865⟩) (okPc := ⟨885⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by simp)

theorem RD.gemJoinTransferFromReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g sel retWord gemTarget : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outTransfer : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨865⟩
      (joinTransferFromEndPtr :: joinTransferFromSelectorWord ::
        gemTarget :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer acc k C)
    (hlo : 32 ≤ outTransfer.size)
    (hhi : outTransfer.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord) :
    ∃ k' C', RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨888⟩
      (retWord :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨865⟩) (okPc := ⟨885⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by decide +native) (by decide +native) (by decide +native) (by decide +native)
      (by jump_dest) (by decide +native) (by decide +native) (by decide +native) (by evm_ov)

theorem solcErrorStringMem0_size_of_size228 {mem : ByteArray} (hmem : mem.size = 228) :
    (solcErrorStringMem0 mem).size = 228 := by
  unfold solcErrorStringMem0
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, hmem, toByteArray_size]

theorem solcErrorStringMem1_size_of_size228 {mem : ByteArray} (hmem : mem.size = 228) :
    (solcErrorStringMem1 mem).size = 228 := by
  unfold solcErrorStringMem1
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem0_size_of_size228 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem0_size_of_size228 hmem,
    toByteArray_size]

theorem solcErrorStringMem2_size_of_size228 (len : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (solcErrorStringMem2 len mem).size = 228 := by
  unfold solcErrorStringMem2
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem1_size_of_size228 hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem1_size_of_size228 hmem,
    toByteArray_size]

theorem solcErrorStringMem3_size_of_size228 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228) :
    (solcErrorStringMem3 len word mem).size = 228 := by
  unfold solcErrorStringMem3
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [solcErrorStringMem2_size_of_size228 len hmem]; omega)]
  simp [ByteArray.size_append, ByteArray.size_extract, solcErrorStringMem2_size_of_size228 len hmem,
    toByteArray_size]

theorem solcErrorStringMem3_read64_of_size228 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (solcErrorStringMem3 len word mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold solcErrorStringMem3
  rw [toByteArray_write_read_below_of_gap word _ 196 64
      (by rw [solcErrorStringMem2_size_of_size228 len hmem]; omega) (by omega)
      (by rw [solcErrorStringMem2_size_of_size228 len hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem2
  rw [toByteArray_write_read_below_of_gap len _ 164 64
      (by rw [solcErrorStringMem1_size_of_size228 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem1_size_of_size228 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem1
  rw [toByteArray_write_read_below_of_gap (⟨32⟩ : UInt256) _ 132 64
      (by rw [solcErrorStringMem0_size_of_size228 hmem]; omega) (by omega)
      (by rw [solcErrorStringMem0_size_of_size228 hmem]; exact lt_usize _ (by norm_num))]
  unfold solcErrorStringMem0
  rw [toByteArray_write_read_below_of_gap solcErrorStringSelector _ 128 64
      (by omega) (by omega) (by rw [hmem]; exact lt_usize _ (by norm_num))]
  exact hread64

theorem solcErrorStringMem3_mload64_of_size228 (len word : UInt256) {mem : ByteArray}
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (if (⟨64⟩ : UInt256).toNat ≥ (solcErrorStringMem3 len word mem).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((solcErrorStringMem3 len word mem).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [solcErrorStringMem3_size_of_size228 len word hmem]; decide)
    (by decide) (solcErrorStringMem3_read64_of_size228 len word hmem hread64)

set_option maxHeartbeats 1000000 in
theorem RD.gemJoinTransferFromReturnFalseReverts
    {cA gh bl σ σ₀ A I} {g sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outTransfer : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨888⟩
      (retWord :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer acc k C)
    (hret : retWord = ⟨0⟩)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have rd891 := rd.pushConst (⟨962⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  have rd892 := rd891.jumpiNT (by decide +native) hret (by evm_ov)
  have rdMload := evm_run rd892 with [
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
      mem_cost hmload64 (by decide +native) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 8)
      (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 8)
      (by decide +native) mem_cost (by rfl) (by decide +native) (by evm_ov),
    raw push1 ⟨23⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 0 (solcErrorStringMem2 ⟨23⟩ mem)
      (UInt256.ofNat 8) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst
    (⟨0x23b2b6a537b4b717b330b4b632b216ba3930b739b332b9⟩ : UInt256)
    (width := 23) (op := .PUSH23) (by decide) (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rdWord := evm_run rdRaw with [
    raw push1 ⟨73⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov)]
  rw [show UInt256.shiftLeft
      (⟨0x23b2b6a537b4b717b330b4b632b216ba3930b739b332b9⟩ : UInt256) ⟨73⟩ =
        ⟨0x47656d4a6f696e2f6661696c65642d7472616e73666572000000000000000000⟩ by decide +native] at rdWord
  exact evm_run rdWord with [
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 0
      (solcErrorStringMem3 ⟨23⟩
        ⟨0x47656d4a6f696e2f6661696c65642d7472616e73666572000000000000000000⟩ mem)
      (UInt256.ofNat 8) (by decide +native) mem_cost (by rfl)
      (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
      mem_cost
      (solcErrorStringMem3_mload64_of_size228 ⟨23⟩
        ⟨0x47656d4a6f696e2f6661696c65642d7472616e73666572000000000000000000⟩
        hmem hread64)
      (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨100⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw rev 0 (by decide +native) mem_cost (by evm_ov)]

set_option maxHeartbeats 1000000 in
theorem RD.gemJoinTransferFromReturnTrueToStop
    {cA gh bl σ σ₀ A I} {g sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem outTransfer : ByteArray} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨888⟩
      (retWord :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer acc k C)
    (hret : retWord ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDret gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) acc ByteArray.empty := by
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have rd891 := rd.pushConst (⟨962⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  have rd962 := rd891.jumpiT (by decide +native) hret (by jump_dest) (by evm_ov)
  have rd967pre := evm_run rd962 with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
      mem_cost hmload64 (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov)]
  have rd970 := rd967pre.mstore 0 ((joinWadWord I).toByteArray.write 0 mem 128 32)
    (UInt256.ofNat 8) (by decide +native) mem_cost (by rfl) (by decide +native)
    (by evm_ov)
  have hmemWrite : ((joinWadWord I).toByteArray.write 0 mem 128 32).size = 228 := by
    exact toByteArray_write32_size_of_le mem (joinWadWord I) 128 228 228 hmem
      (by rw [hmem]; omega) (by omega)
  have hread64Write :
      ((joinWadWord I).toByteArray.write 0 mem 128 32).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [hmem]; omega) (by omega), hread64]
  have hmload64Write :
      (if (⟨64⟩ : UInt256).toNat ≥ ((joinWadWord I).toByteArray.write 0 mem 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          (((joinWadWord I).toByteArray.write 0 mem 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmemWrite]; decide) (by decide) hread64Write
  have rd982pre := evm_run rd970 with [
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
      mem_cost hmload64Write (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨160⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw dup5 (by decide +native) (by evm_ov),
    raw and (by decide +native) (by evm_ov)]
  have hmask :
      UInt256.land (joinUsrMaskedWord I)
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩)
        = joinUsrMaskedWord I := by
    rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    have hcanon : (joinUsrMaskedWord I).toNat < EVM.addressModulus := by
      simpa [joinUsrMaskedWord, u256_land_comm] using
        solcAddrMask_result_canonical (joinUsrWord I)
    exact solcAddrMask_clean hcanon
  rw [hmask] at rd982pre
  have rd1018pre := evm_run rd982pre with [
    raw swap2 (by decide +native) (by evm_ov)]
  have rd1016 := rd1018pre.pushConst
    (⟨0xb4e09949657f21548b58afe74e7b86cd2295da5ff1598ae1e5faecb1cf19ca95⟩ : UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by decide +native) (by evm_ov)
  have rd1025pre := evm_run rd1016 with [
    raw swap2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov)]
  have rd1026 := RD.log2
    (a := ⟨128⟩) (b := ⟨32⟩)
    (c := ⟨0xb4e09949657f21548b58afe74e7b86cd2295da5ff1598ae1e5faecb1cf19ca95⟩)
    (d := joinUsrMaskedWord I)
    (t := [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 8).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    rd1025pre (by decide +native) hperm mem_cost (by decide +native)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd1029pre := evm_run rd1026 with [
    raw pop (by decide +native) (by evm_ov),
    raw pop (by decide +native) (by evm_ov),
    raw jump (by decide +native) (by jump_dest) (by evm_ov)]
  have rd255 := rd1029pre.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop rd255 (by decide +native) (by simp only [List.length_cons, List.length_nil]; omega)

theorem gemJoin_typedCallViaEVM_zero_setSubstate
    {cfg : Config} {evm evm' : EVM.State}
    {tgt : EVM.Address} {name : Ident} {args : List Value}
    {z : Bool} {out : ByteArray} {perm : Bool}
    (hcall : typedCallViaEVM cfg evm tgt name 0 args (z, evm', out) perm)
    (hdepth : evm.executionEnv.depth ≠ 1024) (A0 : Substate) :
    ∃ A',
      typedCallViaEVM cfg { evm with substate := A0 } tgt name 0 args
        (z,
          { { evm with substate := A0 } with
            accountMap := evm'.accountMap,
            substate := A',
            createdAccounts := evm'.createdAccounts },
          out) perm := by
  obtain ⟨calldata, henc, hraw⟩ := hcall
  cases hraw with
  | callMade hvalue hTheta hevm' hvalueLe _hdepth =>
      rename_i valueWord cA' σ' g' A'
      subst evm'
      rcases hTheta with ⟨callGas, A_in, hTheta⟩
      refine ⟨A', ⟨calldata, henc, ?_⟩⟩
      refine callViaEVM.callMade (valueWord := valueWord) (cA' := cA') (σ' := σ')
        (g' := g') (A' := A') (perm := perm) hvalue ⟨callGas, A_in, ?_⟩ ?_ ?_ ?_
      · simpa using hTheta
      · rfl
      · simpa using hvalueLe
      · simpa using hdepth
  | callNotMade _hsubstate _hevm' hfail =>
      exfalso
      exact hfail ⟨(by show (⟨0⟩ : UInt256) ≤ _; exact Fin.zero_le _), hdepth⟩

theorem gemJoinReachJoinBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = gemJoinBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (gemJoinSelBytes 6)) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨210⟩ [gemJoinSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : gemJoinSelWord I = ⟨0x3b4da69f⟩ :=
    gemJoinSelWord_eq_of_beq I hsz 0x3b 0x4d 0xa6 0x9f ⟨0x3b4da69f⟩
      (by decide +native) (by simpa [gemJoinSelBytes] using hsel)
  have hroot :
      UInt256.gt (armSelNat gemJoinBytecode gemJoinRootSplitPc) (gemJoinSelWord I)
        ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc j))
        (gemJoinSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j
    rw [hword]
    decide +native
  have htake :
      UInt256.eq (armSelNat gemJoinBytecode (nthArmPc gemJoinBytecode gemJoinLowFirstArmPc 1))
        (gemJoinSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact gemJoinReachLowBody 1 (by omega) ⟨210⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by decide +native)

theorem gemJoinJoinX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨210⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD gemJoinBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨487⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := gemJoinBytecode) (entry := ⟨210⟩) (ret := ⟨254⟩)
    (decoded := ⟨232⟩) (need := ⟨64⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native)
    (by
      apply ult_zero
      rw [usub_ofNat_word_toNat (by omega : 4 ≤ I.calldata.size) hsize]
      change 64 ≤ I.calldata.size - 4
      omega)
  obtain ⟨_, _, hroutine⟩ := RD.solcAddressUint256ExternalMaskAndJumpMasked
    (code := gemJoinBytecode) (decoded := ⟨232⟩) (ret := ⟨254⟩) (routine := ⟨487⟩)
    (R := [sel]) hdecoded
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [joinWadWord, joinUsrMaskedWord, joinUsrWord, calldataWord] using hroutine⟩

theorem gemJoinJoinX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨210⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev gemJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := gemJoinBytecode) (sel := sel) (entry := ⟨210⟩) (ret := ⟨254⟩)
    (decoded := ⟨232⟩) (need := ⟨64⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt

set_option maxHeartbeats 1000000 in
theorem gemJoinJoinX_liveOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : gemJoinSlotWord ⟨5⟩ σ I = ⟨1⟩)
    (h : RD gemJoinBytecode I g s0 ⟨487⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD gemJoinBytecode I g s0 ⟨561⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd490pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨5⟩ (by decide +native) (by evm_ov)]
  obtain ⟨k491, C491, rd491raw⟩ := rd490pre.sload (by decide +native) (by evm_ov)
  have rd491 : RD gemJoinBytecode I g s0 ⟨491⟩
      (gemJoinSlotWord ⟨5⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k491 C491 := by
    simpa [gemJoinSlotWord] using rd491raw
  have rd494pre := evm_run rd491 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  rw [hlive, u256_eq_refl] at rd494pre
  have rd497 := rd494pre.pushConst (⟨561⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  exact ⟨_, _, rd497.jumpiT (by decide +native) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem gemJoinJoinX_liveRevert {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : gemJoinSlotWord ⟨5⟩ σ I ≠ ⟨1⟩)
    (h : RD gemJoinBytecode I g s0 ⟨487⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev gemJoinBytecode g s0 := by
  have rd490pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨5⟩ (by decide +native) (by evm_ov)]
  obtain ⟨k491, C491, rd491raw⟩ := rd490pre.sload (by decide +native) (by evm_ov)
  have rd491 : RD gemJoinBytecode I g s0 ⟨491⟩
      (gemJoinSlotWord ⟨5⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k491 C491 := by
    simpa [gemJoinSlotWord] using rd491raw
  have rd494pre := evm_run rd491 with [
    raw push1 ⟨1⟩ (by decide +native) (by evm_ov),
    raw eq (by decide +native) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (gemJoinSlotWord ⟨5⟩ σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hlive hbad.symm)
  rw [heq] at rd494pre
  have rd497 := rd494pre.pushConst (⟨561⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  have rd498 := rd497.jumpiNT (by decide +native) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨498⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨0x47656d4a6f696e2f6e6f742d6c697665⟩)
    (shift := ⟨128⟩)
    (word := ⟨0x47656d4a6f696e2f6e6f742d6c69766500000000000000000000000000000000⟩)
    (op := .PUSH16)
    (width := 16)
    rd498
    (by
      unfold solcErrorStringRevertTailWf
      repeat' apply And.intro
      all_goals decide +native)
    (by decide)
    (by decide +native)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem gemJoinJoinX_overflowRevert {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hwadHigh : intLimit ≤ (joinWadWord I).toNat)
    (h : RD gemJoinBytecode I g s0 ⟨561⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev gemJoinBytecode g s0 := by
  have hslt : UInt256.slt (joinWadWord I) (⟨0⟩ : UInt256) = ⟨1⟩ := by
    simpa [intLimit] using
      slt_lit_one_high (a := joinWadWord I) (m := 0) (by norm_num)
        (by simpa [intLimit] using hwadHigh)
  have rd567pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw slt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov)]
  rw [hslt] at rd567pre
  have rd570 := rd567pre.pushConst (⟨634⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  have rd571 := rd570.jumpiNT (by decide +native) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨571⟩)
    (len := ⟨16⟩)
    (rawWord := ⟨0x47656d4a6f696e2f6f766572666c6f77⟩)
    (shift := ⟨128⟩)
    (word := ⟨0x47656d4a6f696e2f6f766572666c6f7700000000000000000000000000000000⟩)
    (op := .PUSH16)
    (width := 16)
    rd571
    (by
      unfold solcErrorStringRevertTailWf
      repeat' apply And.intro
      all_goals decide +native)
    (by decide)
    (by decide +native)
    solcFreePtrMem_size
    solcFreePtrMem_read64
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem gemJoinJoinX_nonoverflowOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hwadLow : (joinWadWord I).toNat < intLimit)
    (h : RD gemJoinBytecode I g s0 ⟨561⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD gemJoinBytecode I g s0 ⟨634⟩
      [joinWadWord I, joinUsrMaskedWord I, ⟨254⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hslt : UInt256.slt (joinWadWord I) (⟨0⟩ : UInt256) = ⟨0⟩ := by
    simpa [intLimit] using
      slt_lit_zero (a := joinWadWord I) (m := 0) (by norm_num)
        (by omega) (by simpa [intLimit] using hwadLow)
  have rd567pre := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨0⟩ (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw slt (by decide +native) (by evm_ov),
    raw iszero (by decide +native) (by evm_ov)]
  rw [hslt] at rd567pre
  have rd570 := rd567pre.pushConst (⟨634⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by decide +native) (by evm_ov)
  exact ⟨_, _, rd570.jumpiT (by decide +native) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem gemJoinX_join_notLive {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ I ≠ ⟨1⟩)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨210⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev gemJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd487⟩ := gemJoinJoinX_decoded (g := g) hsz68 hsize hreach
  exact gemJoinJoinX_liveRevert (I := I) hlive rd487

theorem gemJoinX_join_overflow {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ I = ⟨1⟩)
    (hwadHigh : intLimit ≤ (joinWadWord I).toNat)
    (hreach : ∃ k C, RD gemJoinBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨210⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev gemJoinBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, rd487⟩ := gemJoinJoinX_decoded (g := g) hsz68 hsize hreach
  obtain ⟨_, _, rd561⟩ := gemJoinJoinX_liveOk (I := I) hlive rd487
  exact gemJoinJoinX_overflowRevert (I := I) hwadHigh rd561

theorem gemJoinX_join_vatNoCode {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ I = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatNoCode :
      Reasoning.Theory.extCodeSizeWord σ
        (gemJoinAddressReturnWord ⟨1⟩ σ I) = ⟨0⟩)
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨210⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd487⟩ := gemJoinJoinX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  obtain ⟨_, _, rd561⟩ := gemJoinJoinX_liveOk (I := I) hlive rd487
  obtain ⟨_, _, rd634⟩ := gemJoinJoinX_nonoverflowOk (I := I) hwadLow rd561
  exact RD.gemJoinSlipNoCode ⟨_, _, rd634⟩ hvatNoCode

theorem gemJoinX_join_slipCallDepthLimit {cA gh bl σ σ₀ A I} {g sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ I = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ
        (gemJoinAddressReturnWord ⟨1⟩ σ I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨210⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, rd487⟩ := gemJoinJoinX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
  obtain ⟨_, _, rd561⟩ := gemJoinJoinX_liveOk (I := I) hlive rd487
  obtain ⟨_, _, rd634⟩ := gemJoinJoinX_nonoverflowOk (I := I) hwadLow rd561
  obtain ⟨_, _, rd733⟩ :=
    RD.gemJoinSlipCallDepthLimit ⟨_, _, rd634⟩ hvatCode hdepth
  exact RD.gemJoinSlipCallFailure rd733 (by decide +native)

theorem gemJoinX_join_slipCallFailure {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem out : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨733⟩
      (⟨0⟩ :: joinSlipEndPtr :: joinSlipSelectorWord ::
        gemJoinAddressReturnWord ⟨1⟩ σ I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      mem aw out acc k C)
    (houtSize : out.size < UInt256.size) :
    RDrev gemJoinBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) :=
  RD.gemJoinSlipCallFailure rd houtSize

theorem gemJoinJoinBodyRevertsNotLive (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ ≠ ⟨1⟩) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [joinTransition, nonpayable] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := joinStore I })
      (evm := evm)
      (guard := .binary .eq (.storage liveRef) (.intLit 1))
      (rest :=
        [.require (.binary .lt (.var "wad") (.intLit intLimit))] ++
        checkedExternalCallStmts (.storage vatRef) "slip" (.intLit 0)
          [.storage ilkRef, .var "usr", asInt256 (.var "wad")] "slipRet" ++
        checkedExternalCallStmts (.storage gemRef) "transferFrom" (.intLit 0)
          [sender, thisAddr, .var "wad"] "transferFromOk" ++
        [.require (.var "transferFromOk")])
      hwv
      (evalExpr_join_live_false evm I hlive)

theorem gemJoinJoinBodyRevertsOverflow (evm : EVM.State) (I : ExecutionEnv)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlive : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩ = ⟨1⟩)
    (hwadHigh : intLimit ≤ (joinWadWord I).toNat) :
    ExecTransitionBody config contract evm (joinStore I) joinTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simp only [joinTransition, nonpayable, List.append_assoc, List.singleton_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true hwv)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue (evalExpr_join_live_true evm I hlive)) ?_
  exact ExecBlock.consRevert (ExecStmt.requireFalse (evalExpr_join_wad_lt_false evm I hwadHigh))

theorem gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
    {σ : AccountMap} {target : UInt256} {addr : AccountAddress}
    (haddr : addr = AccountAddress.ofUInt256 target)
    (hne : Reasoning.Theory.extCodeSizeWord σ target ≠ ⟨0⟩) :
    0 < (UInt256.ofNat
      ((σ.find? addr).option 0 (fun acc => acc.code.size))).toNat := by
  subst addr
  unfold Reasoning.Theory.extCodeSizeWord at hne
  cases hacc : σ.find? (AccountAddress.ofUInt256 target) with
  | none =>
      exfalso
      exact hne (by simp [hacc, Option.option])
  | some acc =>
      have hwordNe : UInt256.ofNat acc.code.size ≠ (⟨0⟩ : UInt256) := by
        intro hzero
        exact hne (by simpa [hacc] using hzero)
      have htoNatNe : (UInt256.ofNat acc.code.size).toNat ≠ 0 := by
        intro hzeroNat
        apply hwordNe
        cases hword : UInt256.ofNat acc.code.size with
        | mk val =>
            cases val using Fin.cases
            · rfl
            · simp [UInt256.toNat, hword] at hzeroNat
      simpa [hacc] using Nat.pos_of_ne_zero htoNatNe

theorem gemJoinJoinBodyCoreNotLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨210⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolm : gemJoinSlotWord ⟨5⟩ σ_solm I ≠ ⟨1⟩ := by
    have hword : gemJoinSlotWord ⟨5⟩ σ_evm I = gemJoinSlotWord ⟨5⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
    intro hbad
    exact hlive (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evmSolm (joinStore I) joinTransition.body .reverted := by
    simpa [evmSolm, gemJoinSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      gemJoinJoinBodyRevertsNotLive evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolm
  exact (gemJoinX_join_notLive (g := Sat256.ofUInt256 g) hsz68 hsize hlive hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinJoinBodyCoreOverflow
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ_evm I = ⟨1⟩)
    (hwadHigh : intLimit ≤ (joinWadWord I).toNat)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨210⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hliveSolm : gemJoinSlotWord ⟨5⟩ σ_solm I = ⟨1⟩ := by
    have hword : gemJoinSlotWord ⟨5⟩ σ_evm I = gemJoinSlotWord ⟨5⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
    rw [← hword]
    exact hlive
  have hbody :
      ExecTransitionBody config contract evmSolm (joinStore I) joinTransition.body .reverted := by
    simpa [evmSolm, gemJoinSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      gemJoinJoinBodyRevertsOverflow evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolm hwadHigh
  exact (gemJoinX_join_overflow (g := Sat256.ofUInt256 g) hsz68 hsize hlive hwadHigh hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinJoinBodyCoreVatNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ_evm I = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatNoCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨210⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hLiveSlot :
      gemJoinSlotWord ⟨5⟩ σ_evm I = gemJoinSlotWord ⟨5⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hliveSolm : gemJoinSlotWord ⟨5⟩ σ_solm I = ⟨1⟩ := by
    rw [← hLiveSlot]
    exact hlive
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hword : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hnoCodeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) = ⟨0⟩ := by
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hsolmAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      rw [← hsame]
      exact hvatNoCode
    simpa [hVatSlot] using hsolmAtEvmTarget
  have hvatAddr :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatNoCodeSolm :
      (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    rw [hvatAddr]
    unfold Reasoning.Theory.extCodeSizeWord at hnoCodeSolm
    cases hacc :
      σ_solm.find? (AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I)) with
    | none =>
        simpa [evmSolm, initState, State.lookupAccount, hacc] using
          (show (UInt256.ofNat 0).toNat = 0 from by decide +native)
    | some acc =>
        have hword := congrArg UInt256.toNat hnoCodeSolm
        simpa [evmSolm, initState, State.lookupAccount, hacc] using hword
  have hbody :
      ExecTransitionBody config contract evmSolm (joinStore I) joinTransition.body .reverted := by
    simpa [evmSolm, gemJoinSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount] using
      gemJoinJoinBodyRevertsVatNoCode evmSolm I
        (by simp only [evmSolm, initState]; exact hwv)
        hliveSolm hwadLow hvatNoCodeSolm
  exact (gemJoinX_join_vatNoCode hsz68 hsize hlive hwadLow hvatNoCode hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinJoinBodyCoreSlipCallDepthLimit
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ_evm I = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth = 1024)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨210⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hLiveSlot :
      gemJoinSlotWord ⟨5⟩ σ_evm I = gemJoinSlotWord ⟨5⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hliveSolm : gemJoinSlotWord ⟨5⟩ σ_solm I = ⟨1⟩ := by
    rw [← hLiveSlot]
    exact hlive
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hword : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  let evmSlip :=
    { evmSolm with
      substate := (evmSolm.addAccessedAccount (EVM.address (joinVatAddressOf evmSolm))).substate }
  have hcallSlipDepth :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
          (EVM.Word.toBytesBE
            (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (false, evmSlip, ByteArray.empty) true := by
    simpa [evmSlip, evmSolm, initState] using
      (callNotMade_depthLimit (cfg := config) (evm := evmSolm)
        (tgt := EVM.address (joinVatAddressOf evmSolm)) (name := "slip")
        (args :=
          [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
            joinUsrValue I, joinWadValue I])
        (callPerm := true)
        (by
          simpa [evmSolm, initState, joinSlipInSize] using
            joinSlipEncode_eq I σ_solm solcFreePtrMem_size hwadLow)
        (by simpa [evmSolm, initState] using hdepth))
  have hbody :
      ExecTransitionBody config contract evmSolm (joinStore I) joinTransition.body .reverted := by
    exact gemJoinJoinBodyRevertsSlipCallFailure evmSolm evmSlip I
      (by simp only [evmSolm, initState]; exact hwv)
      hliveSolm hwadLow hvatCodeSolm hcallSlipDepth
  exact (gemJoinX_join_slipCallDepthLimit hsz68 hsize hlive hwadLow hvatCode hdepth hreach)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinJoinBodyCoreSlipCallFailure
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA_slip σ_slip outSlip A_slip k733 C733}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ_evm I = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (rd733 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨733⟩
      (⟨0⟩ :: joinSlipEndPtr :: joinSlipSelectorWord ::
        gemJoinAddressReturnWord ⟨1⟩ σ_evm I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (joinSlipCalldataMem I σ_evm solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cA_slip, σ_slip) k733 C733)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (false, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (houtSlipSize : outSlip.size < UInt256.size)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hrev := RD.gemJoinSlipCallFailure rd733 houtSlipSize
  have hLiveSlot :
      gemJoinSlotWord ⟨5⟩ σ_evm I = gemJoinSlotWord ⟨5⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hliveSolm : gemJoinSlotWord ⟨5⟩ σ_solm I = ⟨1⟩ := by
    rw [← hLiveSlot]
    exact hlive
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hword : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (false, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, _hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, evmSolm, initState]) hAccounts
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  let evmSolmSlip := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (false, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (false, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    simpa [hIlkArg]
      using hcallSlipSolmEvmIlk
  have hbody :
      ExecTransitionBody config contract evmSolm (joinStore I) joinTransition.body .reverted := by
    exact gemJoinJoinBodyRevertsSlipCallFailure evmSolm
      evmSolmSlip I
      (by simp only [evmSolm, initState]; exact hwv)
      hliveSolm hwadLow hvatCodeSolm hcallSlipSolm
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinJoinBodyCoreGemNoCode
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA_slip : Batteries.RBSet AccountAddress compare} {σ_slip : AccountMap}
    {outSlip : ByteArray} {A_slip : Substate} {k752 C752 : ℕ}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ_evm I = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hgemNoCode :
      Reasoning.Theory.extCodeSizeWord σ_slip
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (rd752 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨752⟩
      (joinSlipSelectorWord :: gemJoinAddressReturnWord ⟨1⟩ σ_evm I ::
        joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      (joinSlipCalldataMem I σ_evm solcFreePtrMem) (UInt256.ofNat 8) outSlip
      (cA_slip, σ_slip) k752 C752)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  have hrev := RD.gemJoinTransferFromNoCode rd752 hgemNoCode
  have hLiveSlot :
      gemJoinSlotWord ⟨5⟩ σ_evm I = gemJoinSlotWord ⟨5⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hliveSolm : gemJoinSlotWord ⟨5⟩ σ_solm I = ⟨1⟩ := by
    rw [← hLiveSlot]
    exact hlive
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hword : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, initState]) hAccounts
  let evmSolmSlip : State := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    simpa [hIlkArg] using hcallSlipSolmEvmIlk
  have hGemSlot :
      gemJoinAddressReturnWord ⟨3⟩ σ_slip I =
        gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I := by
    have hword : gemJoinSlotWord ⟨3⟩ σ_slip I =
        gemJoinSlotWord ⟨3⟩ σ_slip_solm I :=
      accountMapEquiv_storage_findD hStateSlip.accountMap I.codeOwner ⟨3⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hgemNoCodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_slip_solm
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) = ⟨0⟩ := by
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hStateSlip.accountMap
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_slip_solm
          (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩ := by
      rw [← hsame]
      exact hgemNoCode
    simpa [hGemSlot] using hzeroAtEvmTarget
  have hgemAddrSolm :
      joinGemAddressOf evmSolmSlip =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) := by
    apply Fin.ext
    simp [evmSolmSlip, evmSolm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
      gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
      AccountAddress.ofNat]
  have hgemNoCodeSolm :
      (UInt256.ofNat
        ((evmSolmSlip.lookupAccount (joinGemAddressOf evmSolmSlip)).option 0
          (fun acc => acc.code.size))).toNat = 0 := by
    rw [hgemAddrSolm]
    unfold Reasoning.Theory.extCodeSizeWord at hgemNoCodeSolmWord
    cases hacc :
      σ_slip_solm.find? (AccountAddress.ofUInt256
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I)) with
    | none =>
        simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount, hacc] using
          (show (UInt256.ofNat 0).toNat = 0 from by decide +native)
    | some acc =>
        have hword := congrArg UInt256.toNat hgemNoCodeSolmWord
        simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount, hacc] using hword
  have hbody :
      ExecTransitionBody config contract evmSolm (joinStore I) joinTransition.body .reverted := by
    exact gemJoinJoinBodyRevertsGemNoCode evmSolm evmSolmSlip I
      (by simp only [evmSolm, initState]; exact hwv)
      hliveSolm hwadLow hvatCodeSolm hcallSlipSolm hgemNoCodeSolm
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinJoinBodyCoreTransferCallFailure
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA_slip cA_transfer : Batteries.RBSet AccountAddress compare}
    {σ_slip σ_transfer : AccountMap}
    {outSlip outTransfer : ByteArray} {A_slip A_transfer : Substate} {k847 C847 : ℕ}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ_evm I = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hgemCode :
      Reasoning.Theory.extCodeSizeWord σ_slip
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (rd847 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨847⟩
      (⟨0⟩ :: joinTransferFromEndPtr :: joinTransferFromSelectorWord ::
        gemJoinAddressReturnWord ⟨3⟩ σ_slip I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (outTransfer.write 0
        (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ_evm solcFreePtrMem))
        joinTransferFromOutPtr.toNat
        (min joinTransferFromOutSize (UInt256.ofNat outTransfer.size)).toNat)
      (UInt256.ofNat 8) outTransfer (cA_transfer, σ_transfer) k847 C847)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (hcallTransferEvmRaw :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }
        (EVM.address (joinGemAddressOf
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }))
        "transferFrom" 0 [.address I.source, .address I.codeOwner, joinWadValue I]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_transfer, substate := A_transfer, createdAccounts := cA_transfer },
          outTransfer) true)
    (houtTransferSize : outTransfer.size < UInt256.size)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  let evmEvmTransfer : State := { evmEvm with
    accountMap := σ_transfer,
    substate := A_transfer,
    createdAccounts := cA_transfer }
  have hrev := RD.gemJoinTransferFromCallFailure rd847 houtTransferSize
  have hLiveSlot :
      gemJoinSlotWord ⟨5⟩ σ_evm I = gemJoinSlotWord ⟨5⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hliveSolm : gemJoinSlotWord ⟨5⟩ σ_solm I = ⟨1⟩ := by
    rw [← hLiveSlot]
    exact hlive
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hword : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, initState]) hAccounts
  let evmSolmSlip : State := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    simpa [hIlkArg] using hcallSlipSolmEvmIlk
  have hGemSlot :
      gemJoinAddressReturnWord ⟨3⟩ σ_slip I =
        gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I := by
    have hword : gemJoinSlotWord ⟨3⟩ σ_slip I =
        gemJoinSlotWord ⟨3⟩ σ_slip_solm I :=
      accountMapEquiv_storage_findD hStateSlip.accountMap I.codeOwner ⟨3⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hgemCodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_slip_solm
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hgemCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hStateSlip.accountMap
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_slip_solm
          (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩ := by
      simpa [hGemSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hgemAddrSolm :
      joinGemAddressOf evmSolmSlip =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) := by
    apply Fin.ext
    simp [evmSolmSlip, evmSolm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
      gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
      AccountAddress.ofNat]
  have hgemCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolmSlip.lookupAccount (joinGemAddressOf evmSolmSlip)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hgemAddrSolm]
    simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_slip_solm) (target := gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I))
        rfl hgemCodeSolmWord
  have hGemAddrOrig :
      joinGemAddressOf evmEvmSlip = joinGemAddressOf evmSolmSlip := by
    have hgemAddrEvm :
        joinGemAddressOf evmEvmSlip =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) := by
      apply Fin.ext
      simp [evmEvmSlip, evmEvm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
    rw [hgemAddrEvm, hgemAddrSolm, hGemSlot]
  have hcallTransferEvm :
      typedCallViaEVM config evmEvmSlip (EVM.address (joinGemAddressOf evmEvmSlip))
        "transferFrom" 0 [.address I.source, .address I.codeOwner, joinWadValue I]
        (false, evmEvmTransfer, outTransfer) true := by
    simpa [evmEvm, evmEvmSlip, evmEvmTransfer] using hcallTransferEvmRaw
  let evmSolmSlipBase : State := { evmSolmSlip with substate := evmEvmSlip.substate }
  obtain ⟨σ_transfer_solm, A_transfer_solm0, hcallTransferSolmBase, _hAccountsTransfer⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmSolmSlipBase)
      hcallTransferEvm hStateSlip.accountMap
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmSolmSlipBase])
      (by
        simpa [evmSolmSlipBase] using hStateSlip.executionEnv.symm)
  have hdepthNeBase : evmSolmSlipBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hI : I.depth = 1024 := by
      simpa [evmSolmSlipBase, evmSolmSlip, evmSolm, initState] using hdepthEq
    rw [hI] at hdepth
    norm_num at hdepth
  obtain ⟨A_transfer_solm, hcallTransferSolmRaw⟩ :=
    gemJoin_typedCallViaEVM_zero_setSubstate hcallTransferSolmBase hdepthNeBase
      evmSolmSlip.substate
  let evmSolmTransfer : State := { evmSolmSlip with
    accountMap := σ_transfer_solm,
    substate := A_transfer_solm,
    createdAccounts := cA_transfer }
  have hcallTransferSolm :
      typedCallViaEVM config evmSolmSlip (EVM.address (joinGemAddressOf evmSolmSlip))
        "transferFrom" 0
        [.address evmSolmSlip.executionEnv.source, .address evmSolmSlip.executionEnv.codeOwner,
          joinWadValue I]
        (false, evmSolmTransfer, outTransfer) true := by
    simpa [evmSolmTransfer, evmSolmSlipBase, evmSolmSlip, evmSolm, initState, hGemAddrOrig]
      using hcallTransferSolmRaw
  have hbody :
      ExecTransitionBody config contract evmSolm (joinStore I) joinTransition.body .reverted := by
    exact gemJoinJoinBodyRevertsTransferCallFailure evmSolm evmSolmSlip evmSolmTransfer I
      (by simp only [evmSolm, initState]; exact hwv)
      hliveSolm hwadLow hvatCodeSolm hcallSlipSolm hgemCodeSolm hcallTransferSolm
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinJoinBodyCoreTransferDecodeShort
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA_slip cA_transfer : Batteries.RBSet AccountAddress compare}
    {σ_slip σ_transfer : AccountMap}
    {outSlip outTransfer : ByteArray} {A_slip A_transfer : Substate} {k865 C865 : ℕ}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ_evm I = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hgemCode :
      Reasoning.Theory.extCodeSizeWord σ_slip
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hshort : outTransfer.size < 32)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (rd865 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨865⟩
      (joinTransferFromEndPtr :: joinTransferFromSelectorWord ::
        gemJoinAddressReturnWord ⟨3⟩ σ_slip I :: joinWadWord I :: joinUsrMaskedWord I ::
        ⟨254⟩ :: sel :: [])
      (outTransfer.write 0
        (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ_evm solcFreePtrMem))
        joinTransferFromOutPtr.toNat
        (min joinTransferFromOutSize (UInt256.ofNat outTransfer.size)).toNat)
      (UInt256.ofNat 8) outTransfer (cA_transfer, σ_transfer) k865 C865)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (hcallTransferEvmRaw :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }
        (EVM.address (joinGemAddressOf
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }))
        "transferFrom" 0 [.address I.source, .address I.codeOwner, joinWadValue I]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_transfer, substate := A_transfer, createdAccounts := cA_transfer },
          outTransfer) true)
    (houtTransferSize : outTransfer.size < UInt256.size)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  let evmEvmTransfer : State := { evmEvm with
    accountMap := σ_transfer,
    substate := A_transfer,
    createdAccounts := cA_transfer }
  have hSlipMem :
      (joinSlipCalldataMem I σ_evm solcFreePtrMem).size = 228 :=
    joinSlipCalldataMem_size_of_size96 I σ_evm solcFreePtrMem_size
  have hSlipRead64 :
      (joinSlipCalldataMem I σ_evm solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    joinSlipCalldataMem_read64_of_size96 I σ_evm solcFreePtrMem_size solcFreePtrMem_read64
  have hBaseMem :
      (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ_evm solcFreePtrMem)).size = 228 :=
    joinTransferFromCalldataMem_size I hSlipMem
  have hBaseRead64 :
      (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ_evm solcFreePtrMem)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    joinTransferFromCalldataMem_read64 I hSlipMem hSlipRead64
  have hmin :
      (min joinTransferFromOutSize (UInt256.ofNat outTransfer.size)).toNat =
        outTransfer.size :=
    joinTransferFromMin32_toNat_of_lt hshort
  have hmem :
      (outTransfer.write 0
        (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ_evm solcFreePtrMem))
        joinTransferFromOutPtr.toNat outTransfer.size).size = 228 :=
    joinTransferFromReturnWrite_size outTransfer.size hBaseMem (by omega) (by omega)
  have hread64 :
      (outTransfer.write 0
        (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ_evm solcFreePtrMem))
        joinTransferFromOutPtr.toNat outTransfer.size).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    joinTransferFromReturnWrite_read64 outTransfer.size hBaseMem hBaseRead64 (by omega) (by omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (outTransfer.write 0
              (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ_evm solcFreePtrMem))
              joinTransferFromOutPtr.toNat outTransfer.size).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((outTransfer.write 0
            (joinTransferFromCalldataMem I (joinSlipCalldataMem I σ_evm solcFreePtrMem))
            joinTransferFromOutPtr.toNat outTransfer.size).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hrev := RD.gemJoinTransferFromReturnDecodeShortReverts
    (by simpa [hmin] using rd865) hshort houtTransferSize hmload64
  have hLiveSlot :
      gemJoinSlotWord ⟨5⟩ σ_evm I = gemJoinSlotWord ⟨5⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hliveSolm : gemJoinSlotWord ⟨5⟩ σ_solm I = ⟨1⟩ := by
    rw [← hLiveSlot]
    exact hlive
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hword : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, initState]) hAccounts
  let evmSolmSlip : State := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    simpa [hIlkArg] using hcallSlipSolmEvmIlk
  have hGemSlot :
      gemJoinAddressReturnWord ⟨3⟩ σ_slip I =
        gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I := by
    have hword : gemJoinSlotWord ⟨3⟩ σ_slip I =
        gemJoinSlotWord ⟨3⟩ σ_slip_solm I :=
      accountMapEquiv_storage_findD hStateSlip.accountMap I.codeOwner ⟨3⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hword]
  have hgemCodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_slip_solm
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hgemCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hStateSlip.accountMap
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_slip_solm
          (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩ := by
      simpa [hGemSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hgemAddrSolm :
      joinGemAddressOf evmSolmSlip =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) := by
    apply Fin.ext
    simp [evmSolmSlip, evmSolm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
      gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
      AccountAddress.ofNat]
  have hgemCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolmSlip.lookupAccount (joinGemAddressOf evmSolmSlip)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hgemAddrSolm]
    simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_slip_solm) (target := gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I))
        rfl hgemCodeSolmWord
  have hGemAddrOrig :
      joinGemAddressOf evmEvmSlip = joinGemAddressOf evmSolmSlip := by
    have hgemAddrEvm :
        joinGemAddressOf evmEvmSlip =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) := by
      apply Fin.ext
      simp [evmEvmSlip, evmEvm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
    rw [hgemAddrEvm, hgemAddrSolm, hGemSlot]
  have hcallTransferEvm :
      typedCallViaEVM config evmEvmSlip (EVM.address (joinGemAddressOf evmEvmSlip))
        "transferFrom" 0 [.address I.source, .address I.codeOwner, joinWadValue I]
        (true, evmEvmTransfer, outTransfer) true := by
    simpa [evmEvm, evmEvmSlip, evmEvmTransfer] using hcallTransferEvmRaw
  let evmSolmSlipBase : State := { evmSolmSlip with substate := evmEvmSlip.substate }
  obtain ⟨σ_transfer_solm, A_transfer_solm0, hcallTransferSolmBase, _hAccountsTransfer⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmSolmSlipBase)
      hcallTransferEvm hStateSlip.accountMap
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmSolmSlipBase])
      (by
        simpa [evmSolmSlipBase] using hStateSlip.executionEnv.symm)
  have hdepthNeBase : evmSolmSlipBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hI : I.depth = 1024 := by
      simpa [evmSolmSlipBase, evmSolmSlip, evmSolm, initState] using hdepthEq
    rw [hI] at hdepth
    norm_num at hdepth
  obtain ⟨A_transfer_solm, hcallTransferSolmRaw⟩ :=
    gemJoin_typedCallViaEVM_zero_setSubstate hcallTransferSolmBase hdepthNeBase
      evmSolmSlip.substate
  let evmSolmTransfer : State := { evmSolmSlip with
    accountMap := σ_transfer_solm,
    substate := A_transfer_solm,
    createdAccounts := cA_transfer }
  have hcallTransferSolm :
      typedCallViaEVM config evmSolmSlip (EVM.address (joinGemAddressOf evmSolmSlip))
        "transferFrom" 0
        [.address evmSolmSlip.executionEnv.source, .address evmSolmSlip.executionEnv.codeOwner,
          joinWadValue I]
        (true, evmSolmTransfer, outTransfer) true := by
    simpa [evmSolmTransfer, evmSolmSlipBase, evmSolmSlip, evmSolm, initState, hGemAddrOrig]
      using hcallTransferSolmRaw
  have hdecTransfer : config.externalABI.decode? "transferFrom" outTransfer = none :=
    gemJoinDecode_transferFromReturn_none_short hshort
  have hbody :
      ExecTransitionBody config contract evmSolm (joinStore I) joinTransition.body .reverted := by
    exact gemJoinJoinBodyRevertsTransferDecode evmSolm evmSolmSlip evmSolmTransfer I
      (by simp only [evmSolm, initState]; exact hwv)
      hliveSolm hwadLow hvatCodeSolm hcallSlipSolm hgemCodeSolm hcallTransferSolm
      hdecTransfer
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  
theorem gemJoinJoinBodyCoreTransferReturnTrueSmall
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {cA_slip cA_transfer : Batteries.RBSet AccountAddress compare}
    {σ_slip σ_transfer : AccountMap}
    {outSlip outTransfer mem : ByteArray} {A_slip A_transfer : Substate} {k888 C888 : ℕ}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ_evm I = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hgemCode :
      Reasoning.Theory.extCodeSizeWord σ_slip
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hret : retWord ≠ ⟨0⟩)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32)) ≠ ⟨0⟩)
    (hlo : 32 ≤ outTransfer.size)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (rd888 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨888⟩
      (retWord :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer (cA_transfer, σ_transfer) k888 C888)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (hcallTransferEvmRaw :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }
        (EVM.address (joinGemAddressOf
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }))
        "transferFrom" 0 [.address I.source, .address I.codeOwner, joinWadValue I]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_transfer, substate := A_transfer, createdAccounts := cA_transfer },
          outTransfer) true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  let evmEvmTransfer : State := { evmEvm with
    accountMap := σ_transfer,
    substate := A_transfer,
    createdAccounts := cA_transfer }
  have hretFinal := RD.gemJoinTransferFromReturnTrueToStop rd888 hret hperm hmem hread64
  have hLiveSlot :
      gemJoinSlotWord ⟨5⟩ σ_evm I = gemJoinSlotWord ⟨5⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hliveSolm : gemJoinSlotWord ⟨5⟩ σ_solm I = ⟨1⟩ := by
    rw [← hLiveSlot]
    exact hlive
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hwordSlot : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hwordSlot]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, initState]) hAccounts
  let evmSolmSlip : State := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    simpa [hIlkArg] using hcallSlipSolmEvmIlk
  have hGemSlot :
      gemJoinAddressReturnWord ⟨3⟩ σ_slip I =
        gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I := by
    have hwordSlot : gemJoinSlotWord ⟨3⟩ σ_slip I =
        gemJoinSlotWord ⟨3⟩ σ_slip_solm I :=
      accountMapEquiv_storage_findD hStateSlip.accountMap I.codeOwner ⟨3⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hwordSlot]
  have hgemCodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_slip_solm
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hgemCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hStateSlip.accountMap
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_slip_solm
          (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩ := by
      simpa [hGemSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hgemAddrSolm :
      joinGemAddressOf evmSolmSlip =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) := by
    apply Fin.ext
    simp [evmSolmSlip, evmSolm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
      gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
      AccountAddress.ofNat]
  have hgemCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolmSlip.lookupAccount (joinGemAddressOf evmSolmSlip)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hgemAddrSolm]
    simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_slip_solm) (target := gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I))
        rfl hgemCodeSolmWord
  have hGemAddrOrig :
      joinGemAddressOf evmEvmSlip = joinGemAddressOf evmSolmSlip := by
    have hgemAddrEvm :
        joinGemAddressOf evmEvmSlip =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) := by
      apply Fin.ext
      simp [evmEvmSlip, evmEvm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
    rw [hgemAddrEvm, hgemAddrSolm, hGemSlot]
  have hcallTransferEvm :
      typedCallViaEVM config evmEvmSlip (EVM.address (joinGemAddressOf evmEvmSlip))
        "transferFrom" 0 [.address I.source, .address I.codeOwner, joinWadValue I]
        (true, evmEvmTransfer, outTransfer) true := by
    simpa [evmEvm, evmEvmSlip, evmEvmTransfer] using hcallTransferEvmRaw
  let evmSolmSlipBase : State := { evmSolmSlip with substate := evmEvmSlip.substate }
  obtain ⟨σ_transfer_solm, A_transfer_solm0, hcallTransferSolmBase, hAccountsTransfer⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmSolmSlipBase)
      hcallTransferEvm hStateSlip.accountMap
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmSolmSlipBase])
      (by
        simpa [evmSolmSlipBase] using hStateSlip.executionEnv.symm)
  have hdepthNeBase : evmSolmSlipBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hI : I.depth = 1024 := by
      simpa [evmSolmSlipBase, evmSolmSlip, evmSolm, initState] using hdepthEq
    rw [hI] at hdepth
    norm_num at hdepth
  obtain ⟨A_transfer_solm, hcallTransferSolmRaw⟩ :=
    gemJoin_typedCallViaEVM_zero_setSubstate hcallTransferSolmBase hdepthNeBase
      evmSolmSlip.substate
  let evmSolmTransfer : State := { evmSolmSlip with
    accountMap := σ_transfer_solm,
    substate := A_transfer_solm,
    createdAccounts := cA_transfer }
  have hcallTransferSolm :
      typedCallViaEVM config evmSolmSlip (EVM.address (joinGemAddressOf evmSolmSlip))
        "transferFrom" 0
        [.address evmSolmSlip.executionEnv.source, .address evmSolmSlip.executionEnv.codeOwner,
          joinWadValue I]
        (true, evmSolmTransfer, outTransfer) true := by
    simpa [evmSolmTransfer, evmSolmSlipBase, evmSolmSlip, evmSolm, initState, hGemAddrOrig]
      using hcallTransferSolmRaw
  have hdecTransfer : config.externalABI.decode? "transferFrom" outTransfer = some [.bool true] :=
    gemJoinDecode_transferFromReturn_true hlo hword
  have hbody :
      ExecTransitionBody config contract evmSolm (joinStore I) joinTransition.body
        (.returned { contract := contract, locals := joinLocalsAfterTransferOk I }
          evmSolmTransfer none) := by
    exact gemJoinJoinBodySuccess evmSolm evmSolmSlip evmSolmTransfer I
      (by simp only [evmSolm, initState]; exact hwv)
      hliveSolm hwadLow hvatCodeSolm hcallSlipSolm hgemCodeSolm hcallTransferSolm
      hdecTransfer
  have hStateTransfer : EVMStateEquiv evmEvmTransfer evmSolmTransfer := by
    refine ⟨?_, ?_, ?_⟩
    · simp [evmEvmTransfer, evmSolmTransfer, evmSolmSlip, evmEvm, evmSolm, initState]
    · simp [evmEvmTransfer, evmSolmTransfer]
    · simpa [evmEvmTransfer, evmSolmTransfer] using hAccountsTransfer
  have henc : returnEquiv ByteArray.empty none joinTransition.returnType := by
    rw [show joinTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
  exact hretFinal.reEquivExecutionGenEVMStateEquiv hcode hdispatch hdecode hbody
    rfl (accountMapEquiv.refl σ_transfer) hStateTransfer henc


theorem gemJoinJoinBodyCoreTransferReturnFalseSmall
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {cA_slip cA_transfer : Batteries.RBSet AccountAddress compare}
    {σ_slip σ_transfer : AccountMap}
    {outSlip outTransfer mem : ByteArray} {A_slip A_transfer : Substate} {k888 C888 : ℕ}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ_evm I = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hgemCode :
      Reasoning.Theory.extCodeSizeWord σ_slip
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hret : retWord = ⟨0⟩)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32)) = ⟨0⟩)
    (hlo : 32 ≤ outTransfer.size)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (rd888 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨888⟩
      (retWord :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer (cA_transfer, σ_transfer) k888 C888)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (hcallTransferEvmRaw :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }
        (EVM.address (joinGemAddressOf
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }))
        "transferFrom" 0 [.address I.source, .address I.codeOwner, joinWadValue I]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_transfer, substate := A_transfer, createdAccounts := cA_transfer },
          outTransfer) true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  let evmEvmTransfer : State := { evmEvm with
    accountMap := σ_transfer,
    substate := A_transfer,
    createdAccounts := cA_transfer }
  have hrev := RD.gemJoinTransferFromReturnFalseReverts rd888 hret hmem hread64
  have hLiveSlot :
      gemJoinSlotWord ⟨5⟩ σ_evm I = gemJoinSlotWord ⟨5⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hliveSolm : gemJoinSlotWord ⟨5⟩ σ_solm I = ⟨1⟩ := by
    rw [← hLiveSlot]
    exact hlive
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hwordSlot : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hwordSlot]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, initState]) hAccounts
  let evmSolmSlip : State := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    simpa [hIlkArg] using hcallSlipSolmEvmIlk
  have hGemSlot :
      gemJoinAddressReturnWord ⟨3⟩ σ_slip I =
        gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I := by
    have hwordSlot : gemJoinSlotWord ⟨3⟩ σ_slip I =
        gemJoinSlotWord ⟨3⟩ σ_slip_solm I :=
      accountMapEquiv_storage_findD hStateSlip.accountMap I.codeOwner ⟨3⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hwordSlot]
  have hgemCodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_slip_solm
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hgemCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hStateSlip.accountMap
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_slip_solm
          (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩ := by
      simpa [hGemSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hgemAddrSolm :
      joinGemAddressOf evmSolmSlip =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) := by
    apply Fin.ext
    simp [evmSolmSlip, evmSolm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
      gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
      AccountAddress.ofNat]
  have hgemCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolmSlip.lookupAccount (joinGemAddressOf evmSolmSlip)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hgemAddrSolm]
    simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_slip_solm) (target := gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I))
        rfl hgemCodeSolmWord
  have hGemAddrOrig :
      joinGemAddressOf evmEvmSlip = joinGemAddressOf evmSolmSlip := by
    have hgemAddrEvm :
        joinGemAddressOf evmEvmSlip =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) := by
      apply Fin.ext
      simp [evmEvmSlip, evmEvm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
    rw [hgemAddrEvm, hgemAddrSolm, hGemSlot]
  have hcallTransferEvm :
      typedCallViaEVM config evmEvmSlip (EVM.address (joinGemAddressOf evmEvmSlip))
        "transferFrom" 0 [.address I.source, .address I.codeOwner, joinWadValue I]
        (true, evmEvmTransfer, outTransfer) true := by
    simpa [evmEvm, evmEvmSlip, evmEvmTransfer] using hcallTransferEvmRaw
  let evmSolmSlipBase : State := { evmSolmSlip with substate := evmEvmSlip.substate }
  obtain ⟨σ_transfer_solm, A_transfer_solm0, hcallTransferSolmBase, hAccountsTransfer⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmSolmSlipBase)
      hcallTransferEvm hStateSlip.accountMap
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmSolmSlipBase])
      (by
        simpa [evmSolmSlipBase] using hStateSlip.executionEnv.symm)
  have hdepthNeBase : evmSolmSlipBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hI : I.depth = 1024 := by
      simpa [evmSolmSlipBase, evmSolmSlip, evmSolm, initState] using hdepthEq
    rw [hI] at hdepth
    norm_num at hdepth
  obtain ⟨A_transfer_solm, hcallTransferSolmRaw⟩ :=
    gemJoin_typedCallViaEVM_zero_setSubstate hcallTransferSolmBase hdepthNeBase
      evmSolmSlip.substate
  let evmSolmTransfer : State := { evmSolmSlip with
    accountMap := σ_transfer_solm,
    substate := A_transfer_solm,
    createdAccounts := cA_transfer }
  have hcallTransferSolm :
      typedCallViaEVM config evmSolmSlip (EVM.address (joinGemAddressOf evmSolmSlip))
        "transferFrom" 0
        [.address evmSolmSlip.executionEnv.source, .address evmSolmSlip.executionEnv.codeOwner,
          joinWadValue I]
        (true, evmSolmTransfer, outTransfer) true := by
    simpa [evmSolmTransfer, evmSolmSlipBase, evmSolmSlip, evmSolm, initState, hGemAddrOrig]
      using hcallTransferSolmRaw
  have hdecTransfer : config.externalABI.decode? "transferFrom" outTransfer = some [.bool false] :=
    gemJoinDecode_transferFromReturn_false hlo hword
  have hbody :
      ExecTransitionBody config contract evmSolm (joinStore I) joinTransition.body .reverted := by
    exact gemJoinJoinBodyRevertsTransferFalse evmSolm evmSolmSlip evmSolmTransfer I
      (by simp only [evmSolm, initState]; exact hwv)
      hliveSolm hwadLow hvatCodeSolm hcallSlipSolm hgemCodeSolm hcallTransferSolm
      hdecTransfer
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody


theorem gemJoinJoinBodyCoreTransferReturnFalseHuge
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {cA_slip cA_transfer : Batteries.RBSet AccountAddress compare}
    {σ_slip σ_transfer : AccountMap}
    {outSlip outTransfer mem : ByteArray} {A_slip A_transfer : Substate} {k888 C888 : ℕ}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩) (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hlive : gemJoinSlotWord ⟨5⟩ σ_evm I = ⟨1⟩)
    (hwadLow : (joinWadWord I).toNat < intLimit)
    (hvatCode :
      Reasoning.Theory.extCodeSizeWord σ_evm
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩)
    (hgemCode :
      Reasoning.Theory.extCodeSizeWord σ_slip
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hret : retWord = ⟨0⟩)
    (hword : UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32)) = ⟨0⟩)
    (hlo : 32 ≤ outTransfer.size) (hhuge : 2 ^ 255 ≤ outTransfer.size)
    (hmem : mem.size = 228)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (joinTransition.params.map Param.name)
        (transitionSignature joinTransition).paramTypes I.calldata = some (joinStore I))
    (rd888 : RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨888⟩
      (retWord :: joinWadWord I :: joinUsrMaskedWord I :: ⟨254⟩ :: sel :: [])
      mem (UInt256.ofNat 8) outTransfer (cA_transfer, σ_transfer) k888 C888)
    (hcallSlipEvmRaw :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (joinVatAddressOf
          (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I))) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, ({ initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }),
          outSlip) true)
    (hcallTransferEvmRaw :
      typedCallViaEVM config
        { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }
        (EVM.address (joinGemAddressOf
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_slip, substate := A_slip, createdAccounts := cA_slip }))
        "transferFrom" 0 [.address I.source, .address I.codeOwner, joinWadValue I]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
            accountMap := σ_transfer, substate := A_transfer, createdAccounts := cA_transfer },
          outTransfer) true)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmEvm := initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evmEvmSlip : State := { evmEvm with
    accountMap := σ_slip,
    substate := A_slip,
    createdAccounts := cA_slip }
  let evmEvmTransfer : State := { evmEvm with
    accountMap := σ_transfer,
    substate := A_transfer,
    createdAccounts := cA_transfer }
  have hrev := RD.gemJoinTransferFromReturnFalseReverts rd888 hret hmem hread64
  have hLiveSlot :
      gemJoinSlotWord ⟨5⟩ σ_evm I = gemJoinSlotWord ⟨5⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨5⟩ ⟨0⟩
  have hliveSolm : gemJoinSlotWord ⟨5⟩ σ_solm I = ⟨1⟩ := by
    rw [← hLiveSlot]
    exact hlive
  have hVatSlot :
      gemJoinAddressReturnWord ⟨1⟩ σ_evm I =
        gemJoinAddressReturnWord ⟨1⟩ σ_solm I := by
    have hwordSlot : gemJoinSlotWord ⟨1⟩ σ_evm I = gemJoinSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hwordSlot]
  have hVatAddrOrig :
      joinVatAddressOf evmEvm = joinVatAddressOf evmSolm := by
    have hvatAddrEvm :
        joinVatAddressOf evmEvm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) := by
      apply Fin.ext
      simp [evmEvm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    have hvatAddrSolm' :
        joinVatAddressOf evmSolm =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
      apply Fin.ext
      simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
        accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
    rw [hvatAddrEvm, hvatAddrSolm', hVatSlot]
  have hcodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_solm
        (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hvatCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (gemJoinAddressReturnWord ⟨1⟩ σ_evm I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_solm
          (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩ := by
      simpa [hVatSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hvatAddrSolm :
      joinVatAddressOf evmSolm =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I) := by
    apply Fin.ext
    simp [evmSolm, joinVatAddressOf, initState, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, gemJoinAddressReturnWord, gemJoinSlotWord, solcSlotWord,
      accountAddress_ofUInt256_eq_ofNat_toNat, AccountAddress.ofNat]
  have hvatCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolm.lookupAccount (joinVatAddressOf evmSolm)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hvatAddrSolm]
    simpa [evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_solm) (target := gemJoinAddressReturnWord ⟨1⟩ σ_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨1⟩ σ_solm I))
        rfl hcodeSolmWord
  have hcallSlipEvm :
      typedCallViaEVM config evmEvm (EVM.address (joinVatAddressOf evmEvm)) "slip" 0
        [.fixedBytes bytes32Width (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, evmEvmSlip, outSlip) true := by
    simpa [evmEvm, evmEvmSlip] using hcallSlipEvmRaw
  obtain ⟨σ_slip_solm, A_slip_solm, hcallSlipSolmRaw, hStateSlip⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallSlipEvm)
      (by simp [evmEvm, evmEvmSlip, initState]) hAccounts
  let evmSolmSlip : State := { evmSolm with
    accountMap := σ_slip_solm,
    substate := A_slip_solm,
    createdAccounts := cA_slip }
  have hIlkSlot :
      gemJoinSlotWord ⟨2⟩ σ_evm I = gemJoinSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have hcallSlipSolmEvmIlk :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE (gemJoinSlotWord ⟨2⟩ σ_evm I)),
          joinUsrValue I, joinWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    simpa [evmSolm, evmSolmSlip, evmEvmSlip, initState, hVatAddrOrig]
      using hcallSlipSolmRaw
  have hcallSlipSolm :
      typedCallViaEVM config evmSolm (EVM.address (joinVatAddressOf evmSolm)) "slip" 0
        [.fixedBytes bytes32Width
            (EVM.Word.toBytesBE
              (Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩)),
          joinUsrValue I, joinWadValue I]
        (true, evmSolmSlip, outSlip) true := by
    have hIlkArg :
        Solm.EVM.storageLoad evmSolm evmSolm.executionEnv.codeOwner ⟨2⟩ =
          gemJoinSlotWord ⟨2⟩ σ_evm I := by
      simpa [evmSolm, initState, Solm.EVM.storageLoad, State.lookupAccount,
        Account.lookupStorage, gemJoinSlotWord, solcSlotWord] using hIlkSlot.symm
    simpa [hIlkArg] using hcallSlipSolmEvmIlk
  have hGemSlot :
      gemJoinAddressReturnWord ⟨3⟩ σ_slip I =
        gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I := by
    have hwordSlot : gemJoinSlotWord ⟨3⟩ σ_slip I =
        gemJoinSlotWord ⟨3⟩ σ_slip_solm I :=
      accountMapEquiv_storage_findD hStateSlip.accountMap I.codeOwner ⟨3⟩ ⟨0⟩
    simp [gemJoinAddressReturnWord, hwordSlot]
  have hgemCodeSolmWord :
      Reasoning.Theory.extCodeSizeWord σ_slip_solm
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) ≠ ⟨0⟩ := by
    intro hzero
    apply hgemCode
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hStateSlip.accountMap
        (gemJoinAddressReturnWord ⟨3⟩ σ_slip I)
    have hzeroAtEvmTarget :
        Reasoning.Theory.extCodeSizeWord σ_slip_solm
          (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = ⟨0⟩ := by
      simpa [hGemSlot] using hzero
    rw [hsame]
    exact hzeroAtEvmTarget
  have hgemAddrSolm :
      joinGemAddressOf evmSolmSlip =
        AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I) := by
    apply Fin.ext
    simp [evmSolmSlip, evmSolm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
      gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
      AccountAddress.ofNat]
  have hgemCodeSolm :
      0 < (UInt256.ofNat
        ((evmSolmSlip.lookupAccount (joinGemAddressOf evmSolmSlip)).option 0
          (fun acc => acc.code.size))).toNat := by
    rw [hgemAddrSolm]
    simpa [evmSolmSlip, evmSolm, initState, State.lookupAccount] using
      gemJoin_extCodeSizeWord_ne_zero_lookup_code_pos
        (σ := σ_slip_solm) (target := gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I)
        (addr := AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip_solm I))
        rfl hgemCodeSolmWord
  have hGemAddrOrig :
      joinGemAddressOf evmEvmSlip = joinGemAddressOf evmSolmSlip := by
    have hgemAddrEvm :
        joinGemAddressOf evmEvmSlip =
          AccountAddress.ofUInt256 (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) := by
      apply Fin.ext
      simp [evmEvmSlip, evmEvm, joinGemAddressOf, initState, Solm.EVM.storageLoad,
        State.lookupAccount, Account.lookupStorage, gemJoinAddressReturnWord,
        gemJoinSlotWord, solcSlotWord, accountAddress_ofUInt256_eq_ofNat_toNat,
        AccountAddress.ofNat]
    rw [hgemAddrEvm, hgemAddrSolm, hGemSlot]
  have hcallTransferEvm :
      typedCallViaEVM config evmEvmSlip (EVM.address (joinGemAddressOf evmEvmSlip))
        "transferFrom" 0 [.address I.source, .address I.codeOwner, joinWadValue I]
        (true, evmEvmTransfer, outTransfer) true := by
    simpa [evmEvm, evmEvmSlip, evmEvmTransfer] using hcallTransferEvmRaw
  let evmSolmSlipBase : State := { evmSolmSlip with substate := evmEvmSlip.substate }
  obtain ⟨σ_transfer_solm, A_transfer_solm0, hcallTransferSolmBase, hAccountsTransfer⟩ :=
    typedCallViaEVM_accountMapEquiv (evm_solm := evmSolmSlipBase)
      hcallTransferEvm hStateSlip.accountMap
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmEvmSlip, evmSolmSlipBase, evmSolmSlip, evmEvm, evmSolm, initState])
      (by simp [evmSolmSlipBase])
      (by
        simpa [evmSolmSlipBase] using hStateSlip.executionEnv.symm)
  have hdepthNeBase : evmSolmSlipBase.executionEnv.depth ≠ 1024 := by
    intro hdepthEq
    have hI : I.depth = 1024 := by
      simpa [evmSolmSlipBase, evmSolmSlip, evmSolm, initState] using hdepthEq
    rw [hI] at hdepth
    norm_num at hdepth
  obtain ⟨A_transfer_solm, hcallTransferSolmRaw⟩ :=
    gemJoin_typedCallViaEVM_zero_setSubstate hcallTransferSolmBase hdepthNeBase
      evmSolmSlip.substate
  let evmSolmTransfer : State := { evmSolmSlip with
    accountMap := σ_transfer_solm,
    substate := A_transfer_solm,
    createdAccounts := cA_transfer }
  have hcallTransferSolm :
      typedCallViaEVM config evmSolmSlip (EVM.address (joinGemAddressOf evmSolmSlip))
        "transferFrom" 0
        [.address evmSolmSlip.executionEnv.source, .address evmSolmSlip.executionEnv.codeOwner,
          joinWadValue I]
        (true, evmSolmTransfer, outTransfer) true := by
    simpa [evmSolmTransfer, evmSolmSlipBase, evmSolmSlip, evmSolm, initState, hGemAddrOrig]
      using hcallTransferSolmRaw
  have hdecTransfer : config.externalABI.decode? "transferFrom" outTransfer = some [.bool false] :=
    gemJoinDecode_transferFromReturn_false hlo hword
  have hbody :
      ExecTransitionBody config contract evmSolm (joinStore I) joinTransition.body .reverted := by
    exact gemJoinJoinBodyRevertsTransferFalse evmSolm evmSolmSlip evmSolmTransfer I
      (by simp only [evmSolm, initState]; exact hwv)
      hliveSolm hwadLow hvatCodeSolm hcallSlipSolm hgemCodeSolm hcallTransferSolm
      hdecTransfer
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem gemJoinJoinBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = gemJoinBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some joinTransition)
    (hreach : ∃ k C, RD gemJoinBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨210⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (gemJoinJoinX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (gemJoinDecode_join_none_short hsz4 hshort)

theorem gemJoinJoinBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = gemJoinBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (gemJoinSelBytes 6))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (gemJoinSelBytes 6) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some joinTransition :=
    gemJoinDispatchJoin hsel
  have hreach := gemJoinReachJoinBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hlive : gemJoinSlotWord ⟨5⟩ σ_evm I = ⟨1⟩
    · by_cases hwadHigh : intLimit ≤ (joinWadWord I).toNat
      · exact gemJoinJoinBodyCoreOverflow hcode hsize hwv hsz68 hlive hwadHigh hdispatch
          (gemJoinDecode_join_ok hsz68) hreach hAccounts
      · have hwadLow : (joinWadWord I).toNat < intLimit := by omega
        by_cases hvatNoCode :
            Reasoning.Theory.extCodeSizeWord σ_evm
              (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) = ⟨0⟩
        · exact gemJoinJoinBodyCoreVatNoCode hcode hsize hwv hsz68 hlive hwadLow
            hvatNoCode hdispatch (gemJoinDecode_join_ok hsz68) hreach hAccounts
        · have hvatCode :
              Reasoning.Theory.extCodeSizeWord σ_evm
                (gemJoinAddressReturnWord ⟨1⟩ σ_evm I) ≠ ⟨0⟩ := hvatNoCode
          by_cases hdepthLt : I.depth.val < 1024
          · obtain ⟨_, _, rd487⟩ :=
              gemJoinJoinX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
            obtain ⟨_, _, rd561⟩ := gemJoinJoinX_liveOk (I := I) hlive rd487
            obtain ⟨_, _, rd634⟩ := gemJoinJoinX_nonoverflowOk (I := I) hwadLow rd561
            obtain ⟨cA_slip, σ_slip, zSlip, outSlip, A_slip, k733, C733,
                rd733, hcallSlipEvmRaw, houtSlipSize⟩ :=
              RD.gemJoinSlipPostCall ⟨_, _, rd634⟩ hvatCode hwadLow hperm hdepthLt
            cases zSlip
            · exact gemJoinJoinBodyCoreSlipCallFailure hcode hsize hwv hsz68 hlive
                hwadLow hvatCode hdepthLt hdispatch (gemJoinDecode_join_ok hsz68)
                rd733 (by simpa using hcallSlipEvmRaw) houtSlipSize hAccounts
            · obtain ⟨_, _, rd752⟩ := RD.gemJoinSlipCallSuccessToTransferSetup rd733
              by_cases hgemNoCode :
                  Reasoning.Theory.extCodeSizeWord σ_slip
                    (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) = (⟨0⟩ : UInt256)
              · exact gemJoinJoinBodyCoreGemNoCode hcode hsize hwv hsz68 hlive
                  hwadLow hvatCode hgemNoCode hdispatch (gemJoinDecode_join_ok hsz68)
                  rd752 (by simpa using hcallSlipEvmRaw) hAccounts
              · have hgemCode :
                    Reasoning.Theory.extCodeSizeWord σ_slip
                      (gemJoinAddressReturnWord ⟨3⟩ σ_slip I) ≠ (⟨0⟩ : UInt256) := hgemNoCode
                obtain ⟨cA_transfer, σ_transfer, zTransfer, outTransfer, A_transfer,
                    k847, C847, rd847, hcallTransferEvmRaw, houtTransferSize⟩ :=
                  RD.gemJoinTransferFromPostCall (Acur := A_slip) rd752 hgemCode
                    hperm hdepthLt
                cases zTransfer
                · exact gemJoinJoinBodyCoreTransferCallFailure hcode hsize hwv hsz68 hlive
                    hwadLow hvatCode hgemCode hdepthLt hdispatch
                    (gemJoinDecode_join_ok hsz68) rd847 (by simpa using hcallSlipEvmRaw)
                    (by simpa using hcallTransferEvmRaw) houtTransferSize hAccounts
                · obtain ⟨_, _, rd865⟩ := RD.gemJoinTransferFromCallSuccessToDecode rd847
                  by_cases hshort : outTransfer.size < 32
                  · exact gemJoinJoinBodyCoreTransferDecodeShort hcode hsize hwv hsz68 hlive
                      hwadLow hvatCode hgemCode hdepthLt hshort hdispatch
                      (gemJoinDecode_join_ok hsz68) rd865
                      (by simpa using hcallSlipEvmRaw)
                      (by simpa using hcallTransferEvmRaw) houtTransferSize hAccounts
                  · have hlo : 32 ≤ outTransfer.size := by omega
                    have hSlipMem :
                        (joinSlipCalldataMem I σ_evm solcFreePtrMem).size = 228 :=
                      joinSlipCalldataMem_size_of_size96 I σ_evm solcFreePtrMem_size
                    have hSlipRead64 :
                        (joinSlipCalldataMem I σ_evm solcFreePtrMem).readWithPadding 64 32 =
                          UInt256.toByteArray ⟨128⟩ :=
                      joinSlipCalldataMem_read64_of_size96 I σ_evm solcFreePtrMem_size
                        solcFreePtrMem_read64
                    have hBaseMem :
                        (joinTransferFromCalldataMem I
                          (joinSlipCalldataMem I σ_evm solcFreePtrMem)).size = 228 :=
                      joinTransferFromCalldataMem_size I hSlipMem
                    have hBaseRead64 :
                        (joinTransferFromCalldataMem I
                          (joinSlipCalldataMem I σ_evm solcFreePtrMem)).readWithPadding 64 32 =
                          UInt256.toByteArray ⟨128⟩ :=
                      joinTransferFromCalldataMem_read64 I hSlipMem hSlipRead64
                    have hmin :
                        (min joinTransferFromOutSize (UInt256.ofNat outTransfer.size)).toNat = 32 :=
                      joinTransferFromMin32_toNat_of_ge hlo houtTransferSize
                    let retWord : UInt256 :=
                      UInt256.ofNat (fromByteArrayBigEndian (outTransfer.extract 0 32))
                    let transferReturnMem : ByteArray :=
                      outTransfer.write 0
                        (joinTransferFromCalldataMem I
                          (joinSlipCalldataMem I σ_evm solcFreePtrMem))
                        joinTransferFromOutPtr.toNat 32
                    have hmem : transferReturnMem.size = 228 :=
                      joinTransferFromReturnWrite_size 32 hBaseMem (by omega) (by omega)
                    have hread64 :
                        transferReturnMem.readWithPadding 64 32 =
                        UInt256.toByteArray ⟨128⟩ :=
                      joinTransferFromReturnWrite_read64 32 hBaseMem hBaseRead64
                        (by omega) (by omega)
                    have hread128 :
                        transferReturnMem.readWithPadding 128 32 =
                        outTransfer.extract 0 32 :=
                      joinTransferFromReturnWrite_read128_32 hBaseMem hlo
                    have hmload64 :
                        (if (⟨64⟩ : UInt256).toNat ≥ transferReturnMem.size
                            ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then
                            ⟨0⟩
                       else
                          UInt256.ofNat
                            (fromByteArrayBigEndian
                              (transferReturnMem.readWithPadding
                                (⟨64⟩ : UInt256).toNat 32))) =
                      ⟨128⟩ := by
                      exact mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
                    have hnot128 :
                        ¬ ((⟨128⟩ : UInt256).toNat ≥ transferReturnMem.size
                            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩) := by
                      exact not_or.mpr
                        ⟨by
                          rw [hmem]
                          decide +native,
                        by decide +native⟩
                    have hmload128 :
                        (if (⟨128⟩ : UInt256).toNat ≥ transferReturnMem.size
                            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 8 * ⟨32⟩ then
                            ⟨0⟩
                         else
                            UInt256.ofNat
                              (fromByteArrayBigEndian
                                (transferReturnMem.readWithPadding
                                    (⟨128⟩ : UInt256).toNat 32))) =
                          retWord := by
                        rw [if_neg hnot128]
                        rw [show (⟨128⟩ : UInt256).toNat = 128 by decide +native]
                        rw [hread128]
                    obtain ⟨_, _, rd888⟩ :=
                      RD.gemJoinTransferFromReturnDecodeOk (retWord := retWord)
                        (by simpa [hmin] using rd865) hlo houtTransferSize hmload64 hmload128
                    by_cases hretZero : retWord = ⟨0⟩
                    · have hword :
                          UInt256.ofNat
                            (fromByteArrayBigEndian (outTransfer.extract 0 32)) = ⟨0⟩ := by
                        simpa [retWord] using hretZero
                      exact gemJoinJoinBodyCoreTransferReturnFalseSmall hcode hsize hwv hperm
                        hsz68 hlive hwadLow hvatCode hgemCode hdepthLt hretZero
                        hword hlo hmem hread64 hdispatch
                        (gemJoinDecode_join_ok hsz68) rd888
                        hcallSlipEvmRaw hcallTransferEvmRaw hAccounts
                    · have hword :
                          UInt256.ofNat
                            (fromByteArrayBigEndian (outTransfer.extract 0 32)) ≠ ⟨0⟩ := by
                        simpa [retWord] using hretZero
                      exact gemJoinJoinBodyCoreTransferReturnTrueSmall hcode hsize hwv hperm
                        hsz68 hlive hwadLow hvatCode hgemCode hdepthLt hretZero
                        hword hlo hmem hread64 hdispatch
                        (gemJoinDecode_join_ok hsz68) rd888
                        hcallSlipEvmRaw hcallTransferEvmRaw hAccounts
          · have hdepthEq : I.depth = 1024 := by
              apply Fin.ext
              have hle : I.depth.val ≤ 1024 := Nat.le_of_lt_succ I.depth.isLt
              omega
            exact gemJoinJoinBodyCoreSlipCallDepthLimit hcode hsize hwv hsz68 hlive
              hwadLow hvatCode hdepthEq hdispatch (gemJoinDecode_join_ok hsz68) hreach
              hAccounts
    · exact gemJoinJoinBodyCoreNotLive hcode hsize hwv hsz68 hlive hdispatch
        (gemJoinDecode_join_ok hsz68) hreach hAccounts
  · exact gemJoinJoinBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.GemJoin
