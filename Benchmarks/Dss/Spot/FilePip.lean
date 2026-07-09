import Benchmarks.Dss.Spot.FileMat

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace Benchmarks.Dss.Spot

/-! ## `file(bytes32,bytes32,address)` -/

abbrev filePipIlkBytes (I : ExecutionEnv) : List UInt8 := fileMatIlkBytes I
abbrev filePipWhatBytes (I : ExecutionEnv) : List UInt8 := fileMatWhatBytes I
abbrev filePipIlkWord (I : ExecutionEnv) : UInt256 := fileMatIlkWord I
abbrev filePipWhatWord (I : ExecutionEnv) : UInt256 := fileMatWhatWord I
abbrev filePipWord (I : ExecutionEnv) : UInt256 := calldataWord I.calldata 68
abbrev filePipMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (filePipWord I)
abbrev filePipAddress (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (filePipWord I).toNat
abbrev filePipIlkKey (I : ExecutionEnv) : KeyValue := fileMatIlkKey I
abbrev filePipSlotFor (I : ExecutionEnv) : UInt256 := fileMatPipSlotFor I
abbrev filePipEvaledRef (I : ExecutionEnv) : EvaledStorageRef :=
  { base := "ilks", steps := [.mindex (filePipIlkKey I), .field "pip"] }

abbrev filePipBytes : List UInt8 :=
  [112, 105, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev filePipLocals (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "ilk" (.fixedBytes bytes32Width (filePipIlkBytes I))).insert
    "what" (.fixedBytes bytes32Width (filePipWhatBytes I))).insert
    "pip_" (.address (filePipAddress I))

noncomputable abbrev filePipIlkHashMem (I : ExecutionEnv) : ByteArray :=
  fileMatIlkHashMem I

theorem filePipMaskedWord_canonical (I : ExecutionEnv) :
    (filePipMaskedWord I).toNat < EVM.addressModulus := by
  rw [filePipMaskedWord, u256_land_comm solcAddrMask (filePipWord I)]
  exact solcAddrMask_result_canonical (filePipWord I)

theorem filePipAddress_value_masked (I : ExecutionEnv) :
    (.address (filePipAddress I) : Value) =
      .address (AccountAddress.ofNat (filePipMaskedWord I).toNat) := by
  simpa [filePipAddress, filePipMaskedWord, filePipWord] using
    (solcAddressValue_masked (calldataWord I.calldata 68))

theorem filePipWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hbs : filePipWhatBytes I = bs) :
    filePipWhatWord I = ABI.bytesToWord bs :=
  fileMatWhatWord_eq_of_bytes_eq hsz68 hbs

theorem filePipWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz68 : 68 ≤ I.calldata.size) (hneq : filePipWhatBytes I ≠ bs)
    (hbsLen : bs.length = 32) :
    filePipWhatWord I ≠ ABI.bytesToWord bs :=
  fileMatWhatWord_ne_of_bytes_ne hsz68 hneq hbsLen

theorem filePipPipSlotFor_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    filePipSlotFor I = solcMappingSlot ⟨1⟩ (filePipIlkWord I) :=
  fileMatPipSlotFor_eq hsz36

theorem filePipIlkHashMem_size (I : ExecutionEnv) :
    (filePipIlkHashMem I).size = 96 :=
  fileMatIlkHashMem_size I

theorem filePipIlkHashMem_read64 (I : ExecutionEnv) :
    (filePipIlkHashMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  fileMatIlkHashMem_read64 I

theorem decodeABIValues_bytes32_bytes32_address_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32)
    (hlen64 : ((bytes.drop 64).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiBytes32, abiAddress] bytes 0 0 96 96
        DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .fixedBytes abiBytes32Width ((bytes.drop 32).take 32),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 64).take 32)).toNat)], 96) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  have hlen32le : 32 ≤ bytes.length - 32 := by
    rw [List.length_take, List.length_drop] at hlen32
    omega
  rw [if_pos hlen32le]
  have hlen64le : 32 ≤ bytes.length - 64 := by
    rw [List.length_take, List.length_drop] at hlen64
    omega
  simp [readWord?, readBytes?, decodeABIWord?, UInt256.toNat, hlen64]

theorem decodeABIValues_bytes32_bytes32_address_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 96) :
    decodeABIValues? [abiBytes32, abiBytes32, abiAddress] bytes 0 0 96 96
        DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    Bool.false_eq_true, if_false, staticABIEncodedSize?, bind, Option.bind, Nat.zero_add]
  by_cases h32 : bytes.length < 32
  · have hnot : ¬ 32 ≤ bytes.length := by omega
    simp [decodeABIValue?, readBytes?, hnot]
  · have htake0 : (bytes.take 32).length = 32 := by
      rw [List.length_take]
      omega
    simp [decodeABIValue?, readBytes?, htake0]
    by_cases h64 : bytes.length < 64
    · have htake32n : ¬ ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hnot : ¬ 32 ≤ bytes.length - 32 := by
        rw [List.length_take, List.length_drop] at htake32n
        omega
      simp [readBytes?, hnot]
    · have htake32 : ((bytes.drop 32).take 32).length = 32 := by
        rw [List.length_take, List.length_drop]
        omega
      have hlen32le : 32 ≤ bytes.length - 32 := by omega
      rw [if_pos hlen32le]
      have hnot : ¬ 32 ≤ bytes.length - 64 := by omega
      simp [readWord?, readBytes?, hnot]

theorem decodeCalldata_legacyBytes32_bytes32_address_ok {cd : ByteArray}
    {x y z : Solm.Ident} (hsz100 : 100 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiBytes32, abiBytes32, abiAddress] cd =
      some ((((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.fixedBytes abiBytes32Width ((cd.toList.drop 36).take 32))).insert z
        (.address (AccountAddress.ofNat (calldataWord cd 68).toNat))) := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((cd.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake36 : ((cd.toList.drop 36).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have htake68 : ((cd.toList.drop 68).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword68 : ABI.bytesToWord ((cd.toList.drop 68).take 32) = calldataWord cd 68 :=
    decode_word_at_eq cd 68 (by omega) (by norm_num)
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiAddress] = some 96 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_bytes32_address_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake68)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 96)]
  simp [decodeCalldata.insertValues]
  rw [hword68]

theorem decodeCalldata_legacyBytes32_bytes32_address_none_short {cd : ByteArray}
    {x y z : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 100) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y, z]
        [abiBytes32, abiBytes32, abiAddress] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiBytes32, abiAddress] = some 96 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 96
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_bytes32_address_legacy_none_short
      (bytes := cd.toList.drop 4) (by
        rw [List.length_drop, htlen]
        omega)]

theorem spotDecode_filePip_ok {I : ExecutionEnv} (hsz100 : 100 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (filePipTransition.params.map Param.name)
      (transitionSignature filePipTransition).paramTypes I.calldata =
        some (filePipLocals I) := by
  simpa [config, filePipTransition, bytes32, bytes32Width, addr, filePipLocals,
    filePipIlkBytes, filePipWhatBytes, filePipAddress, abiBytes32, abiBytes32Width,
    abiAddress] using
    (decodeCalldata_legacyBytes32_bytes32_address_ok
      (cd := I.calldata) (x := "ilk") (y := "what") (z := "pip_") hsz100)

theorem spotDecode_filePip_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100) :
    decodeCalldataWithMode config.abiDecodeMode (filePipTransition.params.map Param.name)
      (transitionSignature filePipTransition).paramTypes I.calldata = none := by
  simpa [config, filePipTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_bytes32_address_none_short
      (cd := I.calldata) (x := "ilk") (y := "what") (z := "pip_") hsz4 hshort)

theorem filePipLocals_get_ilk (I : ExecutionEnv) :
    (filePipLocals I).get? "ilk" =
      some (.fixedBytes bytes32Width (filePipIlkBytes I)) := by
  rw [filePipLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_self]

theorem filePipLocals_get_what (I : ExecutionEnv) :
    (filePipLocals I).get? "what" =
      some (.fixedBytes bytes32Width (filePipWhatBytes I)) := by
  rw [filePipLocals, store_get_ne _ _ (by decide), store_get_self]

theorem filePipLocals_get_pip (I : ExecutionEnv) :
    (filePipLocals I).get? "pip_" = some (.address (filePipAddress I)) := by
  rw [filePipLocals, store_get_self]

theorem filePipLocals_get_wards (I : ExecutionEnv) :
    (filePipLocals I).get? "wards" = none := by
  rw [filePipLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem filePipLocals_get_live (I : ExecutionEnv) :
    (filePipLocals I).get? "live" = none := by
  rw [filePipLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem filePipLocals_get_ilks (I : ExecutionEnv) :
    (filePipLocals I).get? "ilks" = none := by
  rw [filePipLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_filePipAddress {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "pip_" = some (.address (filePipAddress I))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "pip_") =
      .ok (.address (filePipAddress I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "pip_") =
    .ok (.address (filePipAddress I))
  rw [h]
  rfl

theorem evalExpr_filePipWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (filePipWhatBytes I)))
    (hwhat : filePipWhatBytes I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  exact evalExpr_fileMatWhatEq_true (evm := evm) (I := I) (locals := locals)
    (bs := bs) hget hwhat

theorem evalExpr_filePipWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (filePipWhatBytes I)))
    (hwhat : filePipWhatBytes I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  exact evalExpr_fileMatWhatEq_false (evm := evm) (I := I) (locals := locals)
    (bs := bs) hget hwhat

theorem assign_filePipStorage (evm : EVM.State) (I : ExecutionEnv)
    (hsz36 : 36 ≤ I.calldata.size) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner (filePipSlotFor I)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (filePipSlotFor I))
        (filePipMaskedWord I))
    assignStorageRef? config { contract := contract, locals := filePipLocals I } evm
      .storage (ilksF (.var "ilk") "pip") (.address (filePipAddress I)) =
        .ok ({ contract := contract, locals := filePipLocals I }, evm') := by
  intro evm'
  rw [filePipAddress_value_masked I]
  have hstore :
      storageLocStore evm (addrLoc (filePipSlotFor I))
          (.address (AccountAddress.ofNat (filePipMaskedWord I).toNat)) =
        some evm' := by
    simpa [addrLoc, evm'] using
      storageLocStore_address_offset0 evm (filePipSlotFor I) (filePipMaskedWord I)
        (filePipMaskedWord_canonical I)
  exact assignStorageRef_storage_scalar_value
    (cfg := config)
    (solm := { contract := contract, locals := filePipLocals I })
    (slot := ilksF (.var "ilk") "pip")
    (ty := .elem .address)
    (er := filePipEvaledRef I)
    (loc := addrLoc (filePipSlotFor I))
    (hbase := filePipLocals_get_ilks I)
    (her := by
      have hkeyLen : (filePipIlkBytes I).length = ↑bytes32Width + 1 := by
        simpa [bytes32Width] using fileMatIlkBytes_length (I := I) hsz36
      simp [filePipEvaledRef, filePipIlkKey, filePipIlkBytes, evalStorageRef,
        evalStorageRefSteps, evalStorageRefStep, ilksF, evalExpr?, valueToKey?,
        ← Std.HashMap.get?_eq_getElem?, filePipLocals_get_ilk I, EvalResult.ofOption,
        EvalResult.bind, pure, bind, hkeyLen])
    (hty := by
      simp [filePipIlkKey, storageTypeAt?, storageTypeStep?, contract, storageDecls,
        IlkStructTy, addrSt])
    (hloc := by rfl)
    (hscalar := by trivial)
    (hstore := hstore)

theorem spotFilePipSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : spotLiveWord σ I = ⟨1⟩)
    (hwhat : filePipWhatBytes I = filePipBytes) :
    let locals := filePipLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner (filePipSlotFor I)
      (setAddressOffset0Word
        (Solm.EVM.storageLoad evm0 I.codeOwner (filePipSlotFor I))
        (filePipMaskedWord I))
    ExecTransitionBody config contract evm0 locals filePipTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using filePipLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_live_true_of_none evm0 locals
      (by simpa [locals] using filePipLocals_get_live I)
      (by
        simpa [evm0, spotLiveWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hlive)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") pipParamLit) = .ok (.bool true) := by
    simpa [pipParamLit, filePipBytes] using
      (evalExpr_filePipWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := filePipBytes) (by simpa [locals] using filePipLocals_get_what I) hwhat)
  have hpip :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "pip_") =
        .ok (.address (filePipAddress I)) := by
    exact evalExpr_filePipAddress (evm := evm0) (I := I) (locals := locals)
      (by simpa [locals] using filePipLocals_get_pip I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (ilksF (.var "ilk") "pip") (.address (filePipAddress I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using assign_filePipStorage evm0 I hsz36
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage (ilksF (.var "ilk") "pip") (.var "pip_")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hpip hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 filePipTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem spotFilePipSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I ≠ ⟨1⟩) :
    let locals := filePipLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals filePipTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    exact evalExpr_auth_false_of_wards_none evm0 I locals
      (by simpa [locals] using filePipLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  refine ExecFuncBody.execBlockRevert ?_
  simpa [filePipTransition, nonpayable, auth, requireLive] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.require (.binary .eq (.storage liveRef) (.intLit 1)),
        .ite (.binary .eq (.var "what") pipParamLit)
          [.assign .storage (ilksF (.var "ilk") "pip") (.var "pip_")]
          [.require (.boolLit false)]])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem spotFilePipSourceBodyNotLive {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : spotLiveWord σ I ≠ ⟨1⟩) :
    let locals := filePipLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals filePipTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using filePipLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
    exact evalExpr_live_false_of_none evm0 locals
      (by simpa [locals] using filePipLocals_get_live I)
      (by
        simpa [evm0, spotLiveWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hlive)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 filePipTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hliveGuard)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem spotFilePipSourceBodyUnrecognized {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : spotLiveWord σ I = ⟨1⟩)
    (hwhat : filePipWhatBytes I ≠ filePipBytes) :
    let locals := filePipLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals filePipTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_auth_true_of_wards_none evm0 I locals
      (by simpa [locals] using filePipLocals_get_wards I)
      (by simp [evm0, initState])
      (by
        simpa [evm0, relyAuthWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hauth)
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    exact evalExpr_live_true_of_none evm0 locals
      (by simpa [locals] using filePipLocals_get_live I)
      (by
        simpa [evm0, spotLiveWord, spotSlotWord, initState, Solm.EVM.storageLoad,
          State.lookupAccount] using hlive)
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") pipParamLit) = .ok (.bool false) := by
    simpa [pipParamLit, filePipBytes] using
      (evalExpr_filePipWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := filePipBytes) (by simpa [locals] using filePipLocals_get_what I) hwhat)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 filePipTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem spotReachFilePipBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = spotBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (spotSelBytes 4)) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨548⟩ [spotSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : spotSelWord I = ⟨0xebecb39d⟩ :=
    spotSelWord_eq_of_beq I hsz 0xeb 0xec 0xb3 0x9d ⟨0xebecb39d⟩
      (by native_decide) (by simpa [spotSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat spotBytecode spotRootSplitPc) (spotSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 5 →
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc j))
        (spotSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat spotBytecode (nthArmPc spotBytecode spotHighFirstArmPc 5))
        (spotSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact spotReachHighBody 5 (by omega) ⟨548⟩ hcode hwv hsz hsize hroot heq0 htake
    (by jump_dest) (by native_decide)

theorem RD.spotFilePipDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨570⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = spotBytecode)
    (hroutine : (D_J code 0).contains ⟨1837⟩ = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1837⟩
      (UInt256.land solcAddrMask (calldataWord ee.calldata 68) ::
        calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd571 := h.jumpdest (by native_decide) (by evm_ov)
  have rd572 := rd571.pop (by native_decide) (by evm_ov)
  have rd573 := rd572.dup1 (by native_decide) (by evm_ov)
  have rd574 := rd573.calldataload (by native_decide) (by evm_ov)
  have rd575 := rd574.swap1 (by native_decide) (by evm_ov)
  have rd577 := rd575.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd578 := rd577.dup2 (by native_decide) (by evm_ov)
  have rd579 := rd578.add (by native_decide) (by evm_ov)
  have rd580 := rd579.calldataload (by native_decide) (by evm_ov)
  have rd581 := rd580.swap1 (by native_decide) (by evm_ov)
  have rd583 := rd581.push1 ⟨64⟩ (by native_decide) (by evm_ov)
  have rd584 := rd583.add (by native_decide) (by evm_ov)
  have rd585 := rd584.calldataload (by native_decide) (by evm_ov)
  have rd593pre := evm_run rd585 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov)]
  have rd597 := rd593pre.push2 ⟨1837⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show (⟨68⟩ : UInt256).toNat = 68 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide, u256_land_comm]
      using rd597.jump (by native_decide) hroutine (by evm_ov)⟩

theorem spotFilePipX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz100 : 100 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨548⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD spotBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1837⟩
        [filePipMaskedWord I, filePipWhatWord I, filePipIlkWord I, ⟨214⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := spotBytecode) (sel := sel) (entry := ⟨548⟩) (ret := ⟨214⟩)
    (decoded := ⟨570⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by exact solcDecodeLenCheckOkUnsigned (by simpa using hsz100) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.spotFilePipDecodeToRoutine
    (code := spotBytecode) (ret := ⟨214⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [filePipMaskedWord, filePipWord, filePipWhatWord, filePipIlkWord] using hroutine⟩

theorem spotFilePipX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1837⟩
      [filePipMaskedWord I, filePipWhatWord I, filePipIlkWord I, ⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD spotBytecode I g s0 ⟨1919⟩
      [filePipMaskedWord I, filePipWhatWord I, filePipIlkWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1843pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1844 := rd1843pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1848pre := evm_run rd1844 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1849 := rd1848pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1852pre := evm_run rd1849 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1853 := rd1852pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1854, C1854, rd1854raw⟩ := rd1853.sload (by native_decide) (by evm_ov)
  have rd1854 : RD spotBytecode I g s0 ⟨1854⟩
      (relyAuthWord σ I :: filePipMaskedWord I :: filePipWhatWord I :: filePipIlkWord I ::
        ⟨214⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1854 C1854 := by
    simpa [relyAuthWord, spotSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1854raw
  have rd1857pre := evm_run rd1854 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd1857pre
  have rd1860 := rd1857pre.pushConst (⟨1919⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1860.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem spotFilePipX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1837⟩
      [filePipMaskedWord I, filePipWhatWord I, filePipIlkWord I, ⟨214⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd1843pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd1844 := rd1843pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1848pre := evm_run rd1844 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1849 := rd1848pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd1852pre := evm_run rd1849 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd1853 := rd1852pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k1854, C1854, rd1854raw⟩ := rd1853.sload (by native_decide) (by evm_ov)
  have rd1854 : RD spotBytecode I g s0 ⟨1854⟩
      (relyAuthWord σ I :: filePipMaskedWord I :: filePipWhatWord I :: filePipIlkWord I ::
        ⟨214⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k1854 C1854 := by
    simpa [relyAuthWord, spotSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd1854raw
  have rd1857pre := evm_run rd1854 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd1857pre
  have rd1860 := rd1857pre.pushConst (⟨1919⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1861 := rd1860.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.spotCodecopyAuthRevertTail ⟨2134⟩ ⟨22⟩ rd1861
    (by
      unfold spotCodecopyAuthRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem spotFilePipX_liveOk {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : spotLiveWord σ I = ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1919⟩
      [filePipMaskedWord I, filePipWhatWord I, filePipIlkWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD spotBytecode I g s0 ⟨1993⟩
      [filePipMaskedWord I, filePipWhatWord I, filePipIlkWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd1922 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1923raw⟩ := rd1922.sload (by native_decide) (by evm_ov)
  have hliveRaw :
      (σ.find? I.codeOwner |>.option ⟨0⟩
        (fun acc => acc.storage.findD ⟨4⟩ ⟨0⟩)) = ⟨1⟩ := by
    simpa [spotLiveWord, spotSlotWord, solcSlotWord] using hlive
  rw [hliveRaw] at rd1923raw
  have rd1926pre := evm_run rd1923raw with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [uInt256_eq_self] at rd1926pre
  have rd1929 := rd1926pre.pushConst (⟨1993⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1929.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

theorem spotFilePipX_notLive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : spotLiveWord σ I ≠ ⟨1⟩)
    (h : RD spotBytecode I g s0 ⟨1919⟩
      [filePipMaskedWord I, filePipWhatWord I, filePipIlkWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g s0 := by
  have rd1922 := h.jumpdest (by native_decide) (by evm_ov)
    |>.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1923raw⟩ := rd1922.sload (by native_decide) (by evm_ov)
  have rd1926pre := evm_run rd1923raw with [
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
  rw [heq0] at rd1926pre
  have rd1929 := rd1926pre.pushConst (⟨1993⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1930 := rd1929.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1930⟩)
    (len := ⟨16⟩)
    (rawWord := spotNotLiveRawWord)
    (shift := ⟨128⟩)
    (word := UInt256.shiftLeft spotNotLiveRawWord ⟨128⟩)
    (op := .PUSH16)
    (width := 16)
    rd1930
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    rfl
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem spotFilePipX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hsz36 : 36 ≤ I.calldata.size) (hperm : I.perm = true)
    (hmatch : filePipWhatWord I = ABI.bytesToWord filePipBytes)
    (h : RD spotBytecode I g s0 ⟨1993⟩
      [filePipMaskedWord I, filePipWhatWord I, filePipIlkWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret spotBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ (filePipSlotFor I)
        (setAddressOffset0Word (spotSlotWord (filePipSlotFor I) σ I) (filePipMaskedWord I)))
      ByteArray.empty := by
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((filePipIlkHashMem I).readWithPadding 0 64))) =
        solcMappingSlot ⟨1⟩ (filePipIlkWord I) := by
    simpa [filePipIlkHashMem, filePipIlkWord] using
      twoWordHashMem_solcMappingSlot (⟨1⟩ : UInt256) (fileMatIlkWord I)
        (relyAuthHashMem_size I)
  have rd1994 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1995 := rd1994.dup2 (by native_decide) (by evm_ov)
  have rd1999 := rd1995.pushConst (⟨460439⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd2001 := rd1999.push1 ⟨236⟩ (by native_decide) (by evm_ov)
  have rd2002 := rd2001.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨460439⟩ : UInt256) ⟨236⟩ =
      ABI.bytesToWord filePipBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd2002
  have rd2003 := rd2002.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd2003
  have rd2004 := rd2003.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2004
  have rd2007 := rd2004.pushConst (⟨1189⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd2008 := rd2007.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd2010 := rd2008.push1 ⟨0⟩ (by native_decide) (by evm_ov)
  have rd2011 := rd2010.dup4 (by native_decide) (by evm_ov)
  have rd2012pre := rd2011.dup2 (by native_decide) (by evm_ov)
  have rd2013 := rd2012pre.mstore 0 (wordAt0Mem (filePipIlkWord I) (relyAuthHashMem I))
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2017pre := evm_run rd2013 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov)]
  have rd2018 := rd2017pre.mstore 0 (filePipIlkHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide) (by evm_ov)
  have rd2021pre := evm_run rd2018 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd2022 := rd2021pre.keccak256 0 (solcMappingSlot ⟨1⟩ (filePipIlkWord I))
    (UInt256.ofNat 3) (by native_decide) mem_cost hslot (by native_decide) (by evm_ov)
  have rd2023 := rd2022.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2024⟩ := rd2023.sload (by native_decide) (by evm_ov)
  have rd2026 := rd2024.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2028 := rd2026.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2030 := rd2028.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2031 := rd2030.shl (by native_decide) (by evm_ov)
  have rd2032 := rd2031.sub (by native_decide) (by evm_ov)
  have rd2033 := rd2032.not (by native_decide) (by evm_ov)
  have rd2034 := rd2033.and (by native_decide) (by evm_ov)
  have rd2036 := rd2034.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2038 := rd2036.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd2040 := rd2038.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd2041 := rd2040.shl (by native_decide) (by evm_ov)
  have rd2042 := rd2041.sub (by native_decide) (by evm_ov)
  have rd2043 := rd2042.dup4 (by native_decide) (by evm_ov)
  have rd2044 := rd2043.and (by native_decide) (by evm_ov)
  have rd2045 := rd2044.lor (by native_decide) (by evm_ov)
  have rd2046 := rd2045.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd2047⟩ := rd2046.sstore hperm (by native_decide) (by evm_ov)
  have hword :
      UInt256.lor (UInt256.land (filePipMaskedWord I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (spotSlotWord (solcMappingSlot ⟨1⟩ (filePipIlkWord I)) σ I)) =
        setAddressOffset0Word (spotSlotWord (solcMappingSlot ⟨1⟩ (filePipIlkWord I)) σ I)
          (filePipMaskedWord I) := by
    calc
      UInt256.lor (UInt256.land (filePipMaskedWord I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (spotSlotWord (solcMappingSlot ⟨1⟩ (filePipIlkWord I)) σ I)) =
          UInt256.lor (UInt256.land (filePipMaskedWord I) solcAddrMask)
            (UInt256.land (spotSlotWord (solcMappingSlot ⟨1⟩ (filePipIlkWord I)) σ I)
              (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask)
              (spotSlotWord (solcMappingSlot ⟨1⟩ (filePipIlkWord I)) σ I)]
      _ = UInt256.lor
            (UInt256.land (spotSlotWord (solcMappingSlot ⟨1⟩ (filePipIlkWord I)) σ I)
              (UInt256.lnot solcAddrMask))
            (UInt256.land (filePipMaskedWord I) solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (spotSlotWord (solcMappingSlot ⟨1⟩ (filePipIlkWord I)) σ I)
            (filePipMaskedWord I) := by
            rfl
  have hwordRaw :
      UInt256.lor (UInt256.land (filePipMaskedWord I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask)
            (σ.find? I.codeOwner |>.option ⟨0⟩
              (fun acc => acc.storage.findD (solcMappingSlot ⟨1⟩ (filePipIlkWord I)) ⟨0⟩))) =
        setAddressOffset0Word
          (σ.find? I.codeOwner |>.option ⟨0⟩
            (fun acc => acc.storage.findD (solcMappingSlot ⟨1⟩ (filePipIlkWord I)) ⟨0⟩))
          (filePipMaskedWord I) := by
    simpa [spotSlotWord, solcSlotWord] using hword
  have rd2050 := rd2047.push2 ⟨1266⟩ (by native_decide) (by evm_ov)
  have rd1266 := rd2050.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1267 := rd1266.jumpdest (by native_decide) (by evm_ov)
  have rd1268 := rd1267.pop (by native_decide) (by evm_ov)
  have rd1269 := rd1268.pop (by native_decide) (by evm_ov)
  have rd1270 := rd1269.pop (by native_decide) (by evm_ov)
  have rd214 := rd1270.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd215 := rd214.jumpdest (by native_decide) (by evm_ov)
  simpa [spotSlotWord, solcSlotWord, filePipPipSlotFor_eq hsz36, hwordRaw,
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    using RD.stop rd215 (by native_decide) (by evm_ov)

theorem spotFilePipX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hneq : filePipWhatWord I ≠ ABI.bytesToWord filePipBytes)
    (h : RD spotBytecode I g s0 ⟨1993⟩
      [filePipMaskedWord I, filePipWhatWord I, filePipIlkWord I, ⟨214⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g s0 := by
  have rd1994 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1995 := rd1994.dup2 (by native_decide) (by evm_ov)
  have rd1999 := rd1995.pushConst (⟨460439⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd2001 := rd1999.push1 ⟨236⟩ (by native_decide) (by evm_ov)
  have rd2002 := rd2001.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨460439⟩ : UInt256) ⟨236⟩ =
      ABI.bytesToWord filePipBytes := by
    native_decide
  rw [hconst] at rd2002
  have rd2003 := rd2002.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord filePipBytes) (filePipWhatWord I) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd2003
  have rd2004 := rd2003.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2004
  have rd2007 := rd2004.pushConst (⟨1189⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1189 := rd2007.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact RD.spotFileUnrecognizedRevert rd1189
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem spotFilePipX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 100)
    (hreach : ∃ k C, RD spotBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨548⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev spotBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨96⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 96
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := spotBytecode) (sel := sel) (entry := ⟨548⟩) (ret := ⟨214⟩)
    (decoded := ⟨570⟩) (need := ⟨96⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem spotFilePipBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : spotLiveWord σ_evm I = ⟨1⟩)
    (hwhat : filePipWhatBytes I = filePipBytes)
    (hdispatch : dispatchMsg contract I.calldata = some filePipTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (filePipTransition.params.map Param.name)
        (transitionSignature filePipTransition).paramTypes I.calldata = some (filePipLocals I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨548⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let pipSlot := filePipSlotFor I
  let pipWord := filePipMaskedWord I
  let storedEvm := setAddressOffset0Word (spotSlotWord pipSlot σ_evm I) pipWord
  let storedSolm := setAddressOffset0Word (spotSlotWord pipSlot σ_solm I) pipWord
  let locals := filePipLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner pipSlot storedSolm
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
  have hstored : storedEvm = storedSolm := by
    have hword : spotSlotWord pipSlot σ_evm I = spotSlotWord pipSlot σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner pipSlot ⟨0⟩
    simp [storedEvm, storedSolm, hword]
  have hbody :
      ExecTransitionBody config contract evm0 locals filePipTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, pipSlot, pipWord, storedSolm, spotSlotWord, initState,
      Solm.EVM.storageLoad, State.lookupAccount] using
      (spotFilePipSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv (by omega) hauthSolm
        hliveSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := spotFilePipX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  obtain ⟨_, _, hauthz⟩ := spotFilePipX_authorized (I := I) hauth hdecoded
  obtain ⟨_, _, hlivez⟩ := spotFilePipX_liveOk (I := I) hlive hauthz
  have hmatch : filePipWhatWord I = ABI.bytesToWord filePipBytes :=
    filePipWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := spotFilePipX_storeAuthorized (I := I) (by omega) hperm hmatch hlivez
  exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    (by
      simpa [evm1, evm0, initState, storageStore_accountMap, pipSlot, storedSolm, ← hstored,
        storedEvm] using
        accountMapEquiv_sstoreAccountMap I.codeOwner pipSlot storedEvm hAccounts)
    (by
      simpa [filePipTransition] using
        (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
          (dvs := []) rfl (by native_decide) (by native_decide)))

theorem spotFilePipBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some filePipTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (filePipTransition.params.map Param.name)
        (transitionSignature filePipTransition).paramTypes I.calldata = some (filePipLocals I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨548⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := filePipLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : relyAuthWord σ_solm I ≠ ⟨1⟩ := by
    have hword : relyAuthWord σ_evm I = relyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (relyAuthStorageSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals filePipTransition.body .reverted := by
    simpa [evm0, locals] using
      (spotFilePipSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := spotFilePipX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  exact (spotFilePipX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem spotFilePipBodyCoreNotLive
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : spotLiveWord σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some filePipTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (filePipTransition.params.map Param.name)
        (transitionSignature filePipTransition).paramTypes I.calldata = some (filePipLocals I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨548⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := filePipLocals I
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
      ExecTransitionBody config contract evm0 locals filePipTransition.body .reverted := by
    simpa [evm0, locals] using
      (spotFilePipSourceBodyNotLive (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm)
  obtain ⟨_, _, hdecoded⟩ := spotFilePipX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  obtain ⟨_, _, hauthz⟩ := spotFilePipX_authorized (I := I) hauth hdecoded
  exact (spotFilePipX_notLive (I := I) hlive hauthz)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem spotFilePipBodyCoreUnrecognized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz100 : 100 ≤ I.calldata.size)
    (hauth : relyAuthWord σ_evm I = ⟨1⟩)
    (hlive : spotLiveWord σ_evm I = ⟨1⟩)
    (hwhat : filePipWhatBytes I ≠ filePipBytes)
    (hdispatch : dispatchMsg contract I.calldata = some filePipTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (filePipTransition.params.map Param.name)
        (transitionSignature filePipTransition).paramTypes I.calldata = some (filePipLocals I))
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨548⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := filePipLocals I
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
      ExecTransitionBody config contract evm0 locals filePipTransition.body .reverted := by
    simpa [evm0, locals] using
      (spotFilePipSourceBodyUnrecognized (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := spotFilePipX_decoded (g := Sat256.ofUInt256 g)
    hsz100 hsize hreach
  obtain ⟨_, _, hauthz⟩ := spotFilePipX_authorized (I := I) hauth hdecoded
  obtain ⟨_, _, hlivez⟩ := spotFilePipX_liveOk (I := I) hlive hauthz
  have hneq : filePipWhatWord I ≠ ABI.bytesToWord filePipBytes :=
    filePipWhatWord_ne_of_bytes_ne (by omega) hwhat (by native_decide)
  exact (spotFilePipX_unrecognized hneq hlivez)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem spotFilePipBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = spotBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 100)
    (hdispatch : dispatchMsg contract I.calldata = some filePipTransition)
    (hreach : ∃ k C, RD spotBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨548⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (spotFilePipX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch (spotDecode_filePip_none_short hsz4 hshort)

theorem spotFilePipBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = spotBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (spotSelBytes 4))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (spotSelBytes 4) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some filePipTransition :=
    spotDispatchFilePip hsel
  have hreach := spotReachFilePipBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz100 : 100 ≤ I.calldata.size
  · by_cases hauth : relyAuthWord σ_evm I = ⟨1⟩
    · by_cases hlive : spotLiveWord σ_evm I = ⟨1⟩
      · by_cases hwhat : filePipWhatBytes I = filePipBytes
        · exact spotFilePipBodyCoreOk hcode hsize _hperm hwv hsz100 hauth hlive hwhat
            hdispatch (spotDecode_filePip_ok hsz100) hreach hAccounts
        · exact spotFilePipBodyCoreUnrecognized hcode hsize hwv hsz100 hauth hlive hwhat
            hdispatch (spotDecode_filePip_ok hsz100) hreach hAccounts
      · exact spotFilePipBodyCoreNotLive hcode hsize hwv hsz100 hauth hlive
          hdispatch (spotDecode_filePip_ok hsz100) hreach hAccounts
    · exact spotFilePipBodyCoreUnauthorized hcode hsize hwv hsz100 hauth hdispatch
        (spotDecode_filePip_ok hsz100) hreach hAccounts
  · exact spotFilePipBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Spot
