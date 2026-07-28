import Benchmarks.Dss.Flipper.Dispatch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Flipper

/-! ## `file(bytes32,address)` -/

abbrev fileAddressWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileAddressData (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 36).toNat

abbrev fileAddressDataWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileAddressDataKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (fileAddressDataWord I)

abbrev fileAddressCatBytes : List UInt8 :=
  [99, 97, 116] ++ zeroPad29

abbrev fileAddressLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileAddressWhat I))).insert
    "data" (.address (fileAddressData I))

theorem fileAddressWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileAddressWhat I).length = 32 := by
  simp [fileAddressWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileAddressWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (fileAddressWhat I) = calldataWord I.calldata 4 := by
  simpa [fileAddressWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem fileAddressWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hbs : fileAddressWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileAddressWhatWord_eq (I := I) hsz36).symm

theorem fileAddressWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size)
    (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileAddressWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileAddressWhat I)
    (fileAddressWhat_length (I := I) hsz36)
  rw [fileAddressWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileAddressWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : fileAddressWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileAddressWhat_eq_of_word_eq hsz36 hword hbsLen)

theorem fileAddressDataKey_canonical (I : ExecutionEnv) :
    (fileAddressDataKey I).toNat < EVM.addressModulus := by
  unfold fileAddressDataKey
  rw [u256_land_comm solcAddrMask (fileAddressDataWord I)]
  exact solcAddrMask_result_canonical (fileAddressDataWord I)

theorem fileAddressData_value_masked (I : ExecutionEnv) :
    (.address (fileAddressData I) : Value) =
      .address (AccountAddress.ofNat (fileAddressDataKey I).toNat) := by
  simpa [fileAddressData, fileAddressDataKey, fileAddressDataWord] using
    (solcAddressValue_masked (calldataWord I.calldata 36))

theorem decodeABIValues_bytes32_address_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiAddress] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, UInt256.toNat, hlen32]

theorem decodeABIValues_bytes32_address_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiBytes32, abiAddress] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiAddress, isDynamicABIType,
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

theorem decodeCalldata_legacyBytes32_address_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiAddress] cd =
      some (((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.address (AccountAddress.ofNat (calldataWord cd 36).toNat))) := by
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
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by native_decide]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_address_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem decodeCalldata_legacyBytes32_address_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiAddress] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiAddress, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiAddress] = some 64 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_address_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

theorem flipperDecode_fileAddress_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata =
        some (fileAddressLocals I) := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr, fileAddressLocals,
    fileAddressWhat, fileAddressData, abiBytes32, abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_address_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem flipperDecode_fileAddress_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata = none := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_address_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem fileAddressLocals_get_what (I : ExecutionEnv) :
    (fileAddressLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileAddressWhat I)) := by
  rw [fileAddressLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileAddressLocals_get_data (I : ExecutionEnv) :
    (fileAddressLocals I).get? "data" = some (.address (fileAddressData I)) := by
  rw [fileAddressLocals, store_get_self]

theorem fileAddressLocals_get_wards (I : ExecutionEnv) :
    (fileAddressLocals I).get? "wards" = none := by
  rw [fileAddressLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileAddressLocals_get_cat (I : ExecutionEnv) :
    (fileAddressLocals I).get? "cat" = none := by
  rw [fileAddressLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileAddressData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.address (fileAddressData I))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.address (fileAddressData I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.address (fileAddressData I))
  rw [h]
  rfl

theorem evalExpr_fileAddressWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileAddressWhat I)))
    (hwhat : fileAddressWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileAddressWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileAddressWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileAddressWhatEq_false {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileAddressWhat I)))
    (hwhat : fileAddressWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileAddressWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileAddressWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem assign_fileAddressCatStorage (evm : EVM.State) (I : ExecutionEnv) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨7⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨7⟩)
        (fileAddressDataKey I))
    assignStorageRef? config { contract := contract, locals := fileAddressLocals I } evm
      .storage catRef (.address (fileAddressData I)) =
        .ok ({ contract := contract, locals := fileAddressLocals I }, evm') := by
  intro evm'
  rw [fileAddressData_value_masked I]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := ({ base := "cat", steps := [] } : EvaledStorageRef))
      (loc := addrLoc ⟨7⟩)
      (hbase := fileAddressLocals_get_cat I)
      (her := by simp [catRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
      (hloc := by rfl)
      (hscalar := by trivial)
  simpa [addrLoc, evm'] using
    storageLocStore_address_offset0 evm ⟨7⟩ (fileAddressDataKey I)
      (fileAddressDataKey_canonical I)

theorem flipperFileAddressSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressCatBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨7⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm0 I.codeOwner ⟨7⟩)
        (fileAddressDataKey I))
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0] using
      flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catParamLit) = .ok (.bool true) := by
    simpa [catParamLit, fileAddressCatBytes] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressCatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (fileAddressData I)) := by
    exact evalExpr_fileAddressData (evm := evm0) (I := I) (locals := locals)
      (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage catRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, evm0, initState] using assign_fileAddressCatStorage evm0 I
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage catRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        fileAddressTransition.body (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem flipperFileAddressSourceBodyAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I ≠ ⟨1⟩) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0] using
      flipperAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauth
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileAddressTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [.ite (.binary .eq (.var "what") catParamLit)
        [.assign .storage catRef (.var "data")] [.require (.boolLit false)]])
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem flipperFileAddressSourceBodyUnrecognized {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I ≠ fileAddressCatBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0] using
      flipperAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catParamLit) = .ok (.bool false) := by
    simpa [catParamLit, fileAddressCatBytes] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressCatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        fileAddressTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem flipperReachFileAddressBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = flipperBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (flipperSelBytes 6)) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨886⟩ [flipperSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : flipperSelWord I = ⟨0xd4e8be83⟩ :=
    flipperSelWord_eq_of_beq I hsz 0xd4 0xe8 0xbe 0x83 ⟨0xd4e8be83⟩
      (by native_decide) (by simpa [flipperSelBytes] using hsel)
  have hroot : UInt256.gt (armSelNat flipperBytecode flipperRootSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat flipperBytecode flipperLowSplitPc)
      (flipperSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowHighFirstArmPc j))
        (flipperSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat flipperBytecode
        (nthArmPc flipperBytecode flipperLowHighFirstArmPc 2))
        (flipperSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact flipperReachLowHighBody 2 (by omega) ⟨886⟩ hcode hwv hsz hsize hroot hlow
    heq0 htake (by jump_dest) (by native_decide)

theorem RD.flipperFileAddressDecodeToRoutine {code : ByteArray} {g : Sat256}
    {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256}
    {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨908⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = flipperBytecode)
    (hroutine : (D_J code 0).contains ⟨5821⟩ = true)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨5821⟩
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd909 := h.jumpdest (by native_decide) (by evm_ov)
  have rd910 := rd909.pop (by native_decide) (by evm_ov)
  have rd911 := rd910.dup1 (by native_decide) (by evm_ov)
  have rd912 := rd911.calldataload (by native_decide) (by evm_ov)
  have rd913 := rd912.swap1 (by native_decide) (by evm_ov)
  have rd915 := rd913.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd916 := rd915.add (by native_decide) (by evm_ov)
  have rd917 := rd916.calldataload (by native_decide) (by evm_ov)
  have rd919 := rd917.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd921 := rd919.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd923 := rd921.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd924 := rd923.shl (by native_decide) (by evm_ov)
  have rd925 := rd924.sub (by native_decide) (by evm_ov)
  have rd926 := rd925.and (by native_decide) (by evm_ov)
  have rd929 := rd926.push2 ⟨5821⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd929.jump (by native_decide) hroutine (by evm_ov)⟩

theorem flipperFileAddressX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨886⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD flipperBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨5821⟩
        [fileAddressDataKey I, calldataWord I.calldata 4, ⟨323⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcExternalStaticArgsLenOk
    (code := flipperBytecode) (sel := sel) (entry := ⟨886⟩) (ret := ⟨323⟩)
    (decoded := ⟨908⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest)
    (by
      exact solcDecodeLenCheckOkUnsigned (by simpa using hsz68) hsize)
  obtain ⟨_, _, hroutine⟩ := RD.flipperFileAddressDecodeToRoutine
    (code := flipperBytecode) (ret := ⟨323⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileAddressDataKey, fileAddressDataWord] using hroutine⟩

theorem flipperFileAddressX_authorized {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I = ⟨1⟩)
    (h : RD flipperBytecode I g s0 ⟨5821⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨323⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD flipperBytecode I g s0 ⟨5903⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [flipperCallerWardsSlot, flipperSlotWord] using hauth
  exact RD.flipperAuthCheckOk
    (code := flipperBytecode) (pc := ⟨5821⟩) (okPc := ⟨5903⟩)
    (key := fileAddressDataKey I) (ret := calldataWord I.calldata 4) (R := [⟨323⟩, sel])
    h
    (by
      unfold flipperAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by jump_dest) (by simp)

theorem flipperFileAddressX_unauthorized {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ I ≠ ⟨1⟩)
    (h : RD flipperBytecode I g s0 ⟨5821⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨323⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
    simpa [flipperCallerWardsSlot, flipperSlotWord] using hauth
  exact RD.flipperAuthCheckRevert
    (pc := ⟨5821⟩) (okPc := ⟨5903⟩) (key := fileAddressDataKey I)
    (ret := calldataWord I.calldata 4) (R := [⟨323⟩, sel])
    h
    (by
      unfold flipperAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold flipperAuthCodecopyRevertTailWf flipperAuthTailPc
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by simp)

theorem flipperFileAddressX_storeAuthorized {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256} (hperm : I.perm = true)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressCatBytes)
    (h : RD flipperBytecode I g s0 ⟨5903⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret flipperBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨7⟩
        (setAddressOffset0Word (solcSlotWord σ I ⟨7⟩) (fileAddressDataKey I)))
      ByteArray.empty := by
  have rd5904 := h.jumpdest (by native_decide) (by evm_ov)
  have rd5905 := rd5904.dup2 (by native_decide) (by evm_ov)
  have rd5909 := rd5905.pushConst (⟨1628253⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd5911 := rd5909.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd5912 := rd5911.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨1628253⟩ : UInt256) ⟨234⟩ =
      ABI.bytesToWord fileAddressCatBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd5912
  have rd5913 := rd5912.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd5913
  have rd5914 := rd5913.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd5914
  have rd5917 := rd5914.pushConst (⟨1911⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd5918 := rd5917.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd5920 := rd5918.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  have rd5921 := rd5920.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5922⟩ := rd5921.sload (by native_decide) (by evm_ov)
  have rd5924 := rd5922.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5926 := rd5924.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5928 := rd5926.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd5929 := rd5928.shl (by native_decide) (by evm_ov)
  have rd5930 := rd5929.sub (by native_decide) (by evm_ov)
  have rd5931 := rd5930.not (by native_decide) (by evm_ov)
  have rd5932 := rd5931.and (by native_decide) (by evm_ov)
  have rd5934 := rd5932.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5936 := rd5934.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd5938 := rd5936.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd5939 := rd5938.shl (by native_decide) (by evm_ov)
  have rd5940 := rd5939.sub (by native_decide) (by evm_ov)
  have rd5941 := rd5940.dup4 (by native_decide) (by evm_ov)
  have rd5942 := rd5941.and (by native_decide) (by evm_ov)
  have rd5943 := rd5942.lor (by native_decide) (by evm_ov)
  have rd5944 := rd5943.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd5945⟩ := rd5944.sstore hperm (by native_decide) (by evm_ov)
  have rd5948 := rd5945.push2 ⟨1988⟩ (by native_decide) (by evm_ov)
  have rd1988 := rd5948.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1989 := rd1988.jumpdest (by native_decide) (by evm_ov)
  have rd1990 := rd1989.pop (by native_decide) (by evm_ov)
  have rd1991 := rd1990.pop (by native_decide) (by evm_ov)
  have hword :
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ I ⟨7⟩)) =
        setAddressOffset0Word (solcSlotWord σ I ⟨7⟩) (fileAddressDataKey I) := by
    calc
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ I ⟨7⟩)) =
          UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
            (UInt256.land (solcSlotWord σ I ⟨7⟩) (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σ I ⟨7⟩)]
      _ = UInt256.lor (UInt256.land (solcSlotWord σ I ⟨7⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land (fileAddressDataKey I) solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (solcSlotWord σ I ⟨7⟩) (fileAddressDataKey I) := by
            rfl
  have rd323 := rd1991.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd324 := rd323.jumpdest (by native_decide) (by evm_ov)
  simpa [solcSlotWord, setAddressOffset0Word, hword,
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide]
    using RD.stop rd324 (by native_decide) (by evm_ov)

theorem flipperFileAddressX_unrecognized {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel : UInt256}
    (hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressCatBytes)
    (h : RD flipperBytecode I g s0 ⟨5903⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨323⟩, sel]
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g s0 := by
  have rd5904 := h.jumpdest (by native_decide) (by evm_ov)
  have rd5905 := rd5904.dup2 (by native_decide) (by evm_ov)
  have rd5909 := rd5905.pushConst (⟨1628253⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd5911 := rd5909.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd5912 := rd5911.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft (⟨1628253⟩ : UInt256) ⟨234⟩ =
      ABI.bytesToWord fileAddressCatBytes := by
    native_decide
  rw [hconst] at rd5912
  have rd5913 := rd5912.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileAddressCatBytes)
      (calldataWord I.calldata 4) = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd5913
  have rd5914 := rd5913.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd5914
  have rd5917 := rd5914.pushConst (⟨1911⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd1911 := rd5917.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)
  exact RD.flipperFileUnrecognizedRevert rd1911
    (twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size)
    (twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64)
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem flipperFileAddressX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256}
    {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD flipperBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨886⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev flipperBytecode g (initState cA gh bl σ σ₀ g A I) := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  exact RD.solcExternalStaticArgsShortReverts
    (code := flipperBytecode) (sel := sel) (entry := ⟨886⟩) (ret := ⟨323⟩)
    (decoded := ⟨908⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem flipperFileAddressBodyCoreOk
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flipperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressCatBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨886⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let data := fileAddressDataKey I
  let locals := fileAddressLocals I
  let stored := setAddressOffset0Word (solcSlotWord σ_evm I ⟨7⟩) data
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨7⟩ stored
  have hauthSolm : flipperSlotWord (flipperCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    have hword : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I =
        flipperSlotWord (flipperCallerWardsSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (flipperCallerWardsSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hcatWord : flipperSlotWord ⟨7⟩ σ_evm I = flipperSlotWord ⟨7⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨7⟩ ⟨0⟩
  have hstoredSolm :
      stored = setAddressOffset0Word (solcSlotWord σ_solm I ⟨7⟩) data := by
    simpa [stored, flipperSlotWord] using congrArg (fun old => setAddressOffset0Word old data)
      hcatWord
  have hbody :
      ExecTransitionBody config contract evm0 locals fileAddressTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, stored, data, hstoredSolm, solcSlotWord, initState,
      Solm.EVM.storageLoad] using
      (flipperFileAddressSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := flipperFileAddressX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flipperFileAddressX_authorized (I := I) hauth hdecoded
  have hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressCatBytes :=
    fileAddressWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hret := flipperFileAddressX_storeAuthorized hperm hmatch hswitch
  have hret' :
      RDret flipperBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨7⟩ stored) ByteArray.empty := by
    simpa [stored, data] using hret
  exact hret'.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    (by simp [evm1, evm0, initState, storageStore_createdAccounts])
    (by
      simpa [evm1, evm0, initState, storageStore_accountMap, stored, data, hstoredSolm,
        solcSlotWord, Solm.EVM.storageLoad] using
        accountMapEquiv_sstoreAccountMap I.codeOwner ⟨7⟩ stored hAccounts)
    (by
      rw [show fileAddressTransition.returnType = [] by rfl]
      exact returnEquiv.fallthrough rfl (by rfl) (by native_decide))

theorem flipperFileAddressBodyCoreUnauthorized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flipperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I ≠ ⟨1⟩)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨886⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileAddressLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : flipperSlotWord (flipperCallerWardsSlot I) σ_solm I ≠ ⟨1⟩ := by
    have hword : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I =
        flipperSlotWord (flipperCallerWardsSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (flipperCallerWardsSlot I) ⟨0⟩
    intro hbad
    exact hauth (by rw [hword, hbad])
  have hbody :
      ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
    simpa [evm0, locals] using
      (flipperFileAddressSourceBodyAuthReverts (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm)
  obtain ⟨_, _, hdecoded⟩ := flipperFileAddressX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  exact (flipperFileAddressX_unauthorized (I := I) hauth hdecoded)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperFileAddressBodyCoreUnrecognized
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flipperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hauth : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hwhat : fileAddressWhat I ≠ fileAddressCatBytes)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨886⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileAddressLocals I
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hauthSolm : flipperSlotWord (flipperCallerWardsSlot I) σ_solm I = ⟨1⟩ := by
    have hword : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I =
        flipperSlotWord (flipperCallerWardsSlot I) σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (flipperCallerWardsSlot I) ⟨0⟩
    rw [← hword]
    exact hauth
  have hbody :
      ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
    simpa [evm0, locals] using
      (flipperFileAddressSourceBodyUnrecognized (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwhat)
  obtain ⟨_, _, hdecoded⟩ := flipperFileAddressX_decoded (g := Sat256.ofUInt256 g)
    hsz68 hsize hreach
  obtain ⟨_, _, hswitch⟩ := flipperFileAddressX_authorized (I := I) hauth hdecoded
  have hneq : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressCatBytes :=
    fileAddressWhatWord_ne_of_bytes_ne (by omega) hwhat (by native_decide)
  exact (flipperFileAddressX_unrecognized hneq hswitch)
    |>.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem flipperFileAddressBodyCoreDecodeFailed_short
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = flipperBytecode) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hreach : ∃ k C, RD flipperBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨886⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  exact (flipperFileAddressX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize hshort hreach)
    |>.reEquivDecodingFailed hcode hdispatch
      (flipperDecode_fileAddress_none_short hsz4 hshort)

theorem flipperFileAddressBodyCore {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = flipperBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (flipperSelBytes 6))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (flipperSelBytes 6) rfl hsel
  have hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition :=
    flipperDispatchFileAddress hsel
  have hreach := flipperReachFileAddressBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · by_cases hauth : flipperSlotWord (flipperCallerWardsSlot I) σ_evm I = ⟨1⟩
    · by_cases hwhat : fileAddressWhat I = fileAddressCatBytes
      · exact flipperFileAddressBodyCoreOk hcode hsize hperm hwv hsz68 hauth hwhat
          hdispatch (flipperDecode_fileAddress_ok hsz68) hreach hAccounts
      · exact flipperFileAddressBodyCoreUnrecognized hcode hsize hwv hsz68 hauth hwhat
          hdispatch (flipperDecode_fileAddress_ok hsz68) hreach hAccounts
    · exact flipperFileAddressBodyCoreUnauthorized hcode hsize hwv hsz68 hauth hdispatch
        (flipperDecode_fileAddress_ok hsz68) hreach hAccounts
  · exact flipperFileAddressBodyCoreDecodeFailed_short hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Flipper
