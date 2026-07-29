import Benchmarks.Dss.End.FileUint

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.End

/-! ## `file(bytes32,address)` -/

abbrev endFileAddressConcreteSelector : ByteArray := selectorBytes 0xd4 0xe8 0xbe 0x83

abbrev endFileAddressWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev endFileAddressDataWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev endFileAddressDataMaskedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (endFileAddressDataWord I)

abbrev endFileAddressData (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (endFileAddressDataWord I).toNat

abbrev endFileAddressLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (endFileAddressWhat I))).insert
    "data" (.address (endFileAddressData I))

abbrev endFileAddressVatBytes : List UInt8 :=
  [118, 97, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev endFileAddressCatBytes : List UInt8 :=
  [99, 97, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev endFileAddressDogBytes : List UInt8 :=
  [100, 111, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev endFileAddressVowBytes : List UInt8 :=
  [118, 111, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev endFileAddressPotBytes : List UInt8 :=
  [112, 111, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev endFileAddressSpotBytes : List UInt8 :=
  [115, 112, 111, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev endFileAddressCureBytes : List UInt8 :=
  [99, 117, 114, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem endFileAddressWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (endFileAddressWhat I).length = 32 := by
  simp [endFileAddressWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem endFileAddressBytes_lengths :
    endFileAddressVatBytes.length = 32 ∧ endFileAddressCatBytes.length = 32 ∧
    endFileAddressDogBytes.length = 32 ∧ endFileAddressVowBytes.length = 32 ∧
    endFileAddressPotBytes.length = 32 ∧ endFileAddressSpotBytes.length = 32 ∧
    endFileAddressCureBytes.length = 32 := by
  native_decide

theorem endFileAddressVatBytes_word :
    ABI.bytesToWord endFileAddressVatBytes =
      UInt256.shiftLeft (⟨0x1d985d⟩ : UInt256) ⟨234⟩ := by
  native_decide

theorem endFileAddressCatBytes_word :
    ABI.bytesToWord endFileAddressCatBytes =
      UInt256.shiftLeft (⟨0x18d85d⟩ : UInt256) ⟨234⟩ := by
  native_decide

theorem endFileAddressDogBytes_word :
    ABI.bytesToWord endFileAddressDogBytes =
      UInt256.shiftLeft (⟨0x646f67⟩ : UInt256) ⟨232⟩ := by
  native_decide

theorem endFileAddressVowBytes_word :
    ABI.bytesToWord endFileAddressVowBytes =
      UInt256.shiftLeft (⟨0x766f77⟩ : UInt256) ⟨232⟩ := by
  native_decide

theorem endFileAddressPotBytes_word :
    ABI.bytesToWord endFileAddressPotBytes =
      UInt256.shiftLeft (⟨0x1c1bdd⟩ : UInt256) ⟨234⟩ := by
  native_decide

theorem endFileAddressSpotBytes_word :
    ABI.bytesToWord endFileAddressSpotBytes =
      UInt256.shiftLeft (⟨0x1cdc1bdd⟩ : UInt256) ⟨226⟩ := by
  native_decide

theorem endFileAddressCureBytes_word :
    ABI.bytesToWord endFileAddressCureBytes =
      UInt256.shiftLeft (⟨0x63757265⟩ : UInt256) ⟨224⟩ := by
  native_decide

theorem endFileAddressWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (endFileAddressWhat I) = calldataWord I.calldata 4 := by
  simpa [endFileAddressWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem endFileAddressWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hbs : endFileAddressWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (endFileAddressWhatWord_eq (I := I) hsz36).symm

theorem endFileAddressWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    endFileAddressWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := endFileAddressWhat I)
    (endFileAddressWhat_length (I := I) hsz36)
  rw [endFileAddressWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem endFileAddressWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : endFileAddressWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (endFileAddressWhat_eq_of_word_eq hsz36 hword hbsLen)

theorem endFileAddressDataMaskedWord_canonical (I : ExecutionEnv) :
    (endFileAddressDataMaskedWord I).toNat < EVM.addressModulus := by
  unfold endFileAddressDataMaskedWord
  rw [u256_land_comm solcAddrMask (endFileAddressDataWord I)]
  exact solcAddrMask_result_canonical (endFileAddressDataWord I)

theorem endFileAddressData_value_masked (I : ExecutionEnv) :
    (.address (endFileAddressData I) : Value) =
      .address (AccountAddress.ofNat (endFileAddressDataMaskedWord I).toNat) := by
  simpa [endFileAddressData, endFileAddressDataMaskedWord, endFileAddressDataWord] using
    (solcAddressValue_masked (calldataWord I.calldata 36))

theorem endDecode_fileAddress_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata =
        some (endFileAddressLocals I) := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr, endFileAddressLocals,
    endFileAddressWhat, endFileAddressData, abiBytes32, abiBytes32Width, abiAddress] using
    (endDecode_legacyBytes32_address_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem endDecode_fileAddress_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata = none := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (endDecode_legacyBytes32_address_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem endFileAddressLocals_get_what (I : ExecutionEnv) :
    (endFileAddressLocals I).get? "what" =
      some (.fixedBytes bytes32Width (endFileAddressWhat I)) := by
  rw [endFileAddressLocals, store_get_ne _ _ (by decide), store_get_self]

theorem endFileAddressLocals_get_data (I : ExecutionEnv) :
    (endFileAddressLocals I).get? "data" = some (.address (endFileAddressData I)) := by
  rw [endFileAddressLocals, store_get_self]

theorem evalExpr_endFileAddressData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.address (endFileAddressData I))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.address (endFileAddressData I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.address (endFileAddressData I))
  rw [h]
  rfl

theorem evalExpr_endFileAddressWhatEq_true {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (endFileAddressWhat I)))
    (hwhat : endFileAddressWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (endFileAddressWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (endFileAddressWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_endFileAddressWhatEq_false {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (endFileAddressWhat I)))
    (hwhat : endFileAddressWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (endFileAddressWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (endFileAddressWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalStorageRef_endFileAddress_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := endFileAddressLocals I } evm
      (wardsRef sender) = .ok (endRelyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue,
    endRelyAuthEvaledRef, endRelyAuthKey, hsrc, valueToKey?, EvalResult.bind,
    EvalResult.ofOption, bind, pure, evalExpr?]

theorem evalExpr_endFileAddress_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endRelyAuthStorageSlot I) =
        ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileAddressLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFileAddressLocals I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endFileAddressLocals I })
      (slot := wardsRef sender)
      (er := endRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (endRelyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simp [endFileAddressLocals, wardsRef])
      (her := evalStorageRef_endFileAddress_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using endStorageLocLoad_uint256 evm (endRelyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_endFileAddress_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (endRelyAuthStorageSlot I) ≠
        ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileAddressLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFileAddressLocals I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (endRelyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endFileAddressLocals I })
      (slot := wardsRef sender)
      (er := endRelyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (endRelyAuthStorageSlot I))
      (hbase := by simp [endFileAddressLocals, wardsRef])
      (her := evalStorageRef_endFileAddress_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by exact endStorageLocLoad_uint256 evm (endRelyAuthStorageSlot I))
  have hne :
      Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endRelyAuthStorageSlot I)).toNat) ≠ Value.int 1 := by
    intro hbad
    rw [Value.int.injEq] at hbad
    apply hload
    exact endUInt256_toNat_eq_one (Int.ofNat.inj hbad)
  have hbeq :
      (Value.int (Int.ofNat
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
            (endRelyAuthStorageSlot I)).toNat) == Value.int 1) = false := by
    exact beq_eq_false_iff_ne.mpr hne
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  change evalBinaryOp? BinaryOp.eq
      (Value.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (endRelyAuthStorageSlot I)).toNat))
      (Value.int 1) = .ok (.bool false)
  simp only [evalBinaryOp?]
  rw [hbeq]

theorem evalStorageRef_endFileAddress_live (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := endFileAddressLocals I } evm
      liveRef = .ok endLiveEvaledRef := by
  simp [endLiveEvaledRef, liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind,
    pure, bind]

theorem evalExpr_endFileAddress_live_true (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileAddressLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFileAddressLocals I } evm
        (.storage liveRef) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endFileAddressLocals I })
      (slot := liveRef)
      (er := endLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (value := .int 1)
      (hbase := by simp [endFileAddressLocals, liveRef])
      (her := evalStorageRef_endFileAddress_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using endStorageLocLoad_uint256 evm ⟨8⟩)]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_endFileAddress_live_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := endFileAddressLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := endFileAddressLocals I } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := endFileAddressLocals I })
      (slot := liveRef)
      (er := endLiveEvaledRef)
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (hbase := by simp [endFileAddressLocals, liveRef])
      (her := evalStorageRef_endFileAddress_live evm I)
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
    exact endUInt256_toNat_eq_one (Int.ofNat.inj hbad)
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

def endFileAddressPostState (evm : EVM.State) (I : ExecutionEnv) (slot : UInt256) :
    EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
      (endFileAddressDataMaskedWord I))

theorem endFileAddressAssignAddress (evm : EVM.State) (I : ExecutionEnv)
    (slot : UInt256) (ref : StorageRef) (er : EvaledStorageRef)
    (hbase : (endFileAddressLocals I).get? ref.base = none)
    (her :
      evalStorageRef config { contract := contract, locals := endFileAddressLocals I } evm ref =
        .ok er)
    (hty : storageTypeAt? contract.storage er = some addrSt)
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    assignStorageRef? config { contract := contract, locals := endFileAddressLocals I } evm
      .storage ref (.address (endFileAddressData I)) =
        .ok ({ contract := contract, locals := endFileAddressLocals I },
          endFileAddressPostState evm I slot) := by
  rw [endFileAddressData_value_masked I]
  apply assignStorageRef_storage_scalar_value
      (ty := addrSt)
      (er := er)
      (loc := addrLoc slot)
      (hbase := hbase)
      (her := her)
      (hty := hty)
      (hloc := hloc)
      (hscalar := by trivial)
  simpa [addrLoc, endFileAddressPostState] using
    storageLocStore_address_offset0 evm slot (endFileAddressDataMaskedWord I)
      (endFileAddressDataMaskedWord_canonical I)

/-! ### Dispatch reachability -/

abbrev endFileAddressHighSplitPc : UInt256 := ⟨43⟩
abbrev endFileAddressHigh2SplitPc : UInt256 := ⟨54⟩
abbrev endFileAddressGroupJumpdestPc : UInt256 := ⟨113⟩
abbrev endFileAddressFirstArmPc : UInt256 := ⟨114⟩
abbrev endFileAddressEntryPc : UInt256 := ⟨1098⟩
abbrev endFileAddressDecodedPc : UInt256 := ⟨1120⟩
abbrev endFileAddressAuthPc : UInt256 := ⟨8268⟩
abbrev endFileAddressLivePc : UInt256 := ⟨8357⟩
abbrev endFileAddressSwitchPc : UInt256 := ⟨8427⟩
abbrev endFileAddressEventPc : UInt256 := ⟨8747⟩

theorem endFileAddressHighSplitWellFormed :
    selectorSplitWellFormed endBytecode endFileAddressHighSplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endFileAddressHigh2SplitWellFormed :
    selectorSplitWellFormed endBytecode endFileAddressHigh2SplitPc := by
  dsimp [selectorSplitWellFormed]
  repeat' first | apply And.intro | native_decide

set_option maxHeartbeats 1000000 in
theorem endFileAddressArmsWellFormed :
    ∀ j, j ≤ 0 → armWellFormed endBytecode (nthArmPc endBytecode endFileAddressFirstArmPc j) := by
  intro j hj
  interval_cases j
  dsimp [armWellFormed]
  repeat' first | apply And.intro | native_decide

theorem endReachFileAddressBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I endFileAddressConcreteSelector) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        endFileAddressEntryPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
        ByteArray.empty (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xd4e8be83⟩ :=
    endSelWord_eq_of_beq I hsz 0xd4 0xe8 0xbe 0x83 ⟨0xd4e8be83⟩
      (by native_decide)
      (by simpa [selIs, endFileAddressConcreteSelector, selectorBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    endReachRootSplit (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have h43 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endFileAddressHighSplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [endRootSplitPc, endFileAddressHighSplitPc, selArmNextPc, armTgtWidth,
      selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h32 endRootSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h54 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endFileAddressHigh2SplitPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [endFileAddressHighSplitPc, endFileAddressHigh2SplitPc, selArmNextPc,
      armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc, selArmPush4Pc] using
      RD.selectorSplitNotTakenAuto h43 endFileAddressHighSplitWellFormed
        (by rw [hword]; native_decide) (by simp)
  have h113 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endFileAddressGroupJumpdestPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 5) (C32 + 22 + 22 + 22) := by
    simpa [endFileAddressHigh2SplitPc, endFileAddressGroupJumpdestPc] using
      RD.selectorSplitTakenAuto h54 endFileAddressHigh2SplitWellFormed
        (by rw [hword]; native_decide) (by jump_dest) (by simp)
  have h114 : RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      endFileAddressFirstArmPc [endSelWord I] solcFreePtrMem (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) (k32 + 5 + 5 + 5 + 1) (C32 + 22 + 22 + 22 + 1) := by
    simpa [endFileAddressFirstArmPc] using h113.jumpdest (by native_decide) (by simp)
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endFileAddressFirstArmPc j))
        (endSelWord I) = ⟨0⟩ := by
    intro j hj
    omega
  have htake :
      UInt256.eq (armSelNat endBytecode (nthArmPc endBytecode endFileAddressFirstArmPc 0))
        (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact RD.dispatchTo endFileAddressEntryPc 0 h114
    (fun j hj => endFileAddressArmsWellFormed j hj)
    heq0 htake (by jump_dest) (by native_decide) (by simp)

/-! ### Runtime trace -/

theorem RD.endFileAddressDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 endFileAddressDecodedPc (de :: ⟨4⟩ :: ret :: sel :: R)
        mem aw rdata acc k C)
    (hwf : code = endBytecode)
    (hroutine : (D_J code 0).contains endFileAddressAuthPc = true)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 endFileAddressAuthPc
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd1121 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1122 := rd1121.pop (by native_decide) (by evm_ov)
  have rd1123 := rd1122.dup1 (by native_decide) (by evm_ov)
  have rd1124 := rd1123.calldataload (by native_decide) (by evm_ov)
  have rd1125 := rd1124.swap1 (by native_decide) (by evm_ov)
  have rd1127 := rd1125.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd1128 := rd1127.add (by native_decide) (by evm_ov)
  have rd1129 := rd1128.calldataload (by native_decide) (by evm_ov)
  have rd1131 := rd1129.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1133 := rd1131.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd1135 := rd1133.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd1136 := rd1135.shl (by native_decide) (by evm_ov)
  have rd1137 := rd1136.sub (by native_decide) (by evm_ov)
  have rd1138 := rd1137.and (by native_decide) (by evm_ov)
  have rd1141 := rd1138.push2 endFileAddressAuthPc (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [endFileAddressAuthPc, endFileAddressDecodedPc, calldataWord,
      show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (UInt256.add (⟨32⟩ : UInt256) ⟨4⟩).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd1141.jump (by native_decide) hroutine (by evm_ov)⟩

theorem endFileAddressX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFileAddressEntryPc [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g
        (initState cA gh bl σ σ₀ g A I) endFileAddressAuthPc
        [endFileAddressDataMaskedWord I, calldataWord I.calldata 4, endRelyReturnPc, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := endBytecode) (sel := sel)
    (entry := endFileAddressEntryPc) (ret := endRelyReturnPc)
    (decoded := endFileAddressDecodedPc) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.endFileAddressDecodeToRoutine
    (code := endBytecode) (ret := endRelyReturnPc) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [endFileAddressDataMaskedWord, endFileAddressDataWord] using hroutine⟩

theorem endFileAddressX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) endFileAddressEntryPc [sel]
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
    (entry := endFileAddressEntryPc) (ret := endRelyReturnPc)
    (decoded := endFileAddressDecodedPc) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

theorem endFileAddressX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (h : RD endBytecode I g s0 endFileAddressAuthPc
      [endFileAddressDataMaskedWord I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 endFileAddressLivePc
      [endFileAddressDataMaskedWord I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [endRelyAuthWord, endSlotWord, endRelyAuthStorageSlot_eq_mapSlot_source I,
      mapSlot] using hauth
  simpa [endRelyAuthHashMem] using
    RD.endAuthCheckOk
      (code := endBytecode) (pc := endFileAddressAuthPc) (okPc := endFileAddressLivePc)
      (key := endFileAddressDataMaskedWord I) (ret := calldataWord I.calldata 4)
      (R := [endRelyReturnPc, sel])
      h
      (by
        unfold endAuthCheckWf
        repeat' first | apply And.intro | native_decide)
      hauthSolc (by jump_dest) (by simp)

theorem endFileAddressX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : endRelyAuthWord σ I ≠ ⟨1⟩)
    (h : RD endBytecode I g s0 endFileAddressAuthPc
      [endFileAddressDataMaskedWord I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hauthSolc :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
    simpa [endRelyAuthWord, endSlotWord, endRelyAuthStorageSlot_eq_mapSlot_source I,
      mapSlot] using hauth
  exact RD.endAuthCheckRevert
    (code := endBytecode) (pc := endFileAddressAuthPc) (okPc := endFileAddressLivePc)
    (key := endFileAddressDataMaskedWord I) (ret := calldataWord I.calldata 4)
    (R := [endRelyReturnPc, sel])
    h
    (by
      unfold endAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf endAuthTailPc endNotAuthorizedRawWord
      repeat' first | apply And.intro | native_decide)
    hauthSolc (by simp)

theorem endFileAddressX_live {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (h : RD endBytecode I g s0 endFileAddressLivePc
      [endFileAddressDataMaskedWord I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 endFileAddressSwitchPc
      [endFileAddressDataMaskedWord I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hliveSolc : solcSlotWord σ I ⟨8⟩ = ⟨1⟩ := by
    simpa [endSlotWord] using hlive
  exact RD.endLiveGuardOk
    (code := endBytecode) (pc := endFileAddressLivePc) (okPc := endFileAddressSwitchPc)
    (key := endFileAddressDataMaskedWord I) (ret := calldataWord I.calldata 4)
    (R := [endRelyReturnPc, sel])
    h
    (by
      unfold endLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    hliveSolc (by jump_dest) (by simp)

theorem endFileAddressX_notLive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : endSlotWord ⟨8⟩ σ I ≠ ⟨1⟩)
    (h : RD endBytecode I g s0 endFileAddressLivePc
      [endFileAddressDataMaskedWord I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hliveSolc : solcSlotWord σ I ⟨8⟩ ≠ ⟨1⟩ := by
    simpa [endSlotWord] using hlive
  exact RD.endLiveGuardRevert
    (code := endBytecode) (pc := endFileAddressLivePc) (okPc := endFileAddressSwitchPc)
    (key := endFileAddressDataMaskedWord I) (ret := calldataWord I.calldata 4)
    (R := [endRelyReturnPc, sel])
    h
    (by
      unfold endLiveGuardWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf endLiveGuardTailPc endNotLiveRawWord
      repeat' first | apply And.intro | native_decide)
    hliveSolc (endRelyAuthHashMem_size I) (endRelyAuthHashMem_read64 I) (by simp)

noncomputable def endFileAddressLogDataMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.toByteArray (endFileAddressDataMaskedWord I)).write 0 (endRelyAuthHashMem I) 128 32

theorem endFileAddressLogDataMem_size (I : ExecutionEnv) :
    (endFileAddressLogDataMem I).size = 160 := by
  unfold endFileAddressLogDataMem
  exact toByteArray_write32_size_of_ge (endRelyAuthHashMem I)
    (endFileAddressDataMaskedWord I) 128 96 160
    (endRelyAuthHashMem_size I) (by omega)
    (by simpa using lt_usize 32 (by norm_num))
    (by omega)

theorem endFileAddressLogDataMem_read64 (I : ExecutionEnv) :
    (endFileAddressLogDataMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold endFileAddressLogDataMem
  rw [toByteArray_write_read_below_of_gap (endFileAddressDataMaskedWord I)
    (endRelyAuthHashMem I) 128 64
    (by rw [endRelyAuthHashMem_size I]) (by omega)
    (by rw [endRelyAuthHashMem_size I]; exact lt_usize _ (by norm_num))]
  exact endRelyAuthHashMem_read64 I

set_option maxHeartbeats 2000000 in
theorem endFileAddressX_logReturn {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {what sel : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (h : RD endBytecode I g s0 endFileAddressEventPc
      [endFileAddressDataMaskedWord I, what, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDret endBytecode g s0 acc ByteArray.empty := by
  have hmaskR :
      UInt256.land (endFileAddressDataMaskedWord I) solcAddrMask =
        endFileAddressDataMaskedWord I := by
    exact solcAddrMask_clean (endFileAddressDataMaskedWord_canonical I)
  have hmaskL :
      UInt256.land solcAddrMask (endFileAddressDataMaskedWord I) =
        endFileAddressDataMaskedWord I := by
    rw [u256_land_comm solcAddrMask (endFileAddressDataMaskedWord I)]
    exact hmaskR
  have rd8762pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [endRelyAuthHashMem_size I]; decide) (by decide)
        (endRelyAuthHashMem_read64 I))
      (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8763 := rd8762pre.mstore 6 (endFileAddressLogDataMem I)
    (UInt256.ofNat 5) (by native_decide) mem_cost
    (by
      simp [endFileAddressLogDataMem, hmaskR,
        show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
      rw [show (⟨128⟩ : UInt256).toNat = 128 from by native_decide]
    )
    (by native_decide) (by evm_ov)
  have rd8767pre := evm_run rd8763 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [endFileAddressLogDataMem_size I]; decide) (by decide)
        (endFileAddressLogDataMem_read64 I))
      (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd8801 := rd8767pre.pushConst
    (⟨0x8fef588b5fc1afbf5b2f06c1a435d513f208da2e6704c3d8f0e0ec91167066ba⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd8810pre := evm_run rd8801 with [
    raw swap2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd8811 := RD.log2
    (a := ⟨128⟩) (b := ⟨32⟩)
    (c := ⟨0x8fef588b5fc1afbf5b2f06c1a435d513f208da2e6704c3d8f0e0ec91167066ba⟩)
    (d := what)
    (t := [endFileAddressDataMaskedWord I, what, endRelyReturnPc, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 5).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    rd8810pre (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd8812 := RD.pop (a := endFileAddressDataMaskedWord I) (t := [what, endRelyReturnPc, sel])
    rd8811 (by native_decide) (by evm_ov)
  have rd8813 := RD.pop (a := what) (t := [endRelyReturnPc, sel])
    rd8812 (by native_decide) (by evm_ov)
  have rd562 := RD.jump (a := endRelyReturnPc) (t := [sel]) rd8813
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := endRelyReturnPc) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

theorem RD.endFileAddressSkipVat {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 endFileAddressSwitchPc (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord endFileAddressVatBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 ⟨8473⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd8428 := h.jumpdest (by native_decide) (by evm_ov)
  have rd8429 := rd8428.dup2 (by native_decide) (by evm_ov)
  have rd8433 := rd8429.pushConst (⟨0x1d985d⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8435 := rd8433.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd8436 := rd8435.shl (by native_decide) (by evm_ov)
  rw [← endFileAddressVatBytes_word] at rd8436
  have rd8437 := rd8436.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord endFileAddressVatBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd8437
  have rd8438 := rd8437.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd8438
  have rd8441 := rd8438.push2 ⟨8473⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd8441.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

theorem RD.endFileAddressStoreVat {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD endBytecode ee g s0 endFileAddressSwitchPc (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord endFileAddressVatBytes)
    (hperm : ee.perm = true)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 endFileAddressEventPc
      (data :: what :: ret :: sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨1⟩
        (setAddressOffset0Word (solcSlotWord σ ee ⟨1⟩) data)) k' C' := by
  have rd8428 := h.jumpdest (by native_decide) (by evm_ov)
  have rd8429 := rd8428.dup2 (by native_decide) (by evm_ov)
  have rd8433 := rd8429.pushConst (⟨0x1d985d⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd8435 := rd8433.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd8436 := rd8435.shl (by native_decide) (by evm_ov)
  rw [hmatch, ← endFileAddressVatBytes_word] at rd8436
  have rd8437 := rd8436.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd8437
  have rd8438 := rd8437.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd8438
  have rd8441 := rd8438.push2 ⟨8473⟩ (by native_decide) (by evm_ov)
  have rd8442 := rd8441.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd8444 := rd8442.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd8445 := rd8444.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd8446⟩ := rd8445.sload (by native_decide) (by evm_ov)
  have rd8448 := rd8446.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd8450 := rd8448.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd8452 := rd8450.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd8453 := rd8452.shl (by native_decide) (by evm_ov)
  have rd8454 := rd8453.sub (by native_decide) (by evm_ov)
  have rd8455 := rd8454.not (by native_decide) (by evm_ov)
  have rd8456 := rd8455.and (by native_decide) (by evm_ov)
  have rd8458 := rd8456.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd8460 := rd8458.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd8462 := rd8460.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd8463 := rd8462.shl (by native_decide) (by evm_ov)
  have rd8464 := rd8463.sub (by native_decide) (by evm_ov)
  have rd8465 := rd8464.dup4 (by native_decide) (by evm_ov)
  have rd8466 := rd8465.and (by native_decide) (by evm_ov)
  have rd8467 := rd8466.or (by native_decide) (by evm_ov)
  have rd8468 := rd8467.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd8469⟩ := rd8468.sstore hperm (by native_decide) (by evm_ov)
  have rd8472 := rd8469.push2 endFileAddressEventPc (by native_decide) (by evm_ov)
  have hword :
      UInt256.lor (UInt256.land data solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨1⟩)) =
        setAddressOffset0Word (solcSlotWord σ ee ⟨1⟩) data := by
    calc
      UInt256.lor (UInt256.land data solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨1⟩)) =
          UInt256.lor (UInt256.land data solcAddrMask)
            (UInt256.land (solcSlotWord σ ee ⟨1⟩) (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨1⟩)]
      _ = UInt256.lor (UInt256.land (solcSlotWord σ ee ⟨1⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land data solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (solcSlotWord σ ee ⟨1⟩) data := by
            rfl
  exact ⟨_, _, by
    simpa [endFileAddressEventPc, solcSlotWord, hword, hmatch,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd8472.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem endFileAddressStoreWord_eq (old data : UInt256) :
    UInt256.lor (UInt256.land data solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
      setAddressOffset0Word old data := by
  calc
    UInt256.lor (UInt256.land data solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
        UInt256.lor (UInt256.land data solcAddrMask)
          (UInt256.land old (UInt256.lnot solcAddrMask)) := by
          rw [u256_land_comm (UInt256.lnot solcAddrMask) old]
    _ = UInt256.lor (UInt256.land old (UInt256.lnot solcAddrMask))
          (UInt256.land data solcAddrMask) := by
          exact u256_lor_comm _ _
    _ = setAddressOffset0Word old data := by
          rfl

theorem RD.endFileAddressSkipCat {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨8473⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord endFileAddressCatBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 ⟨8519⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd := h.jumpdest (by native_decide) (by evm_ov)
  have rd := rd.dup2 (by native_decide) (by evm_ov)
  have rd := rd.pushConst (⟨0x18d85d⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd := rd.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  rw [← endFileAddressCatBytes_word] at rd
  have rd := rd.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord endFileAddressCatBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd
  have rd := rd.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd
  have rd := rd.push2 ⟨8519⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

theorem RD.endFileAddressStoreCat {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD endBytecode ee g s0 ⟨8473⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord endFileAddressCatBytes)
    (hperm : ee.perm = true)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 endFileAddressEventPc
      (data :: what :: ret :: sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨2⟩
        (setAddressOffset0Word (solcSlotWord σ ee ⟨2⟩) data)) k' C' := by
  have rd := h.jumpdest (by native_decide) (by evm_ov)
  have rd := rd.dup2 (by native_decide) (by evm_ov)
  have rd := rd.pushConst (⟨0x18d85d⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd := rd.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  rw [hmatch, ← endFileAddressCatBytes_word] at rd
  have rd := rd.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd
  have rd := rd.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd
  have rd := rd.push2 ⟨8519⟩ (by native_decide) (by evm_ov)
  have rd := rd.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd := rd.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd := rd.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd⟩ := rd.sload (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  have rd := rd.sub (by native_decide) (by evm_ov)
  have rd := rd.not (by native_decide) (by evm_ov)
  have rd := rd.and (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  have rd := rd.sub (by native_decide) (by evm_ov)
  have rd := rd.dup4 (by native_decide) (by evm_ov)
  have rd := rd.and (by native_decide) (by evm_ov)
  have rd := rd.or (by native_decide) (by evm_ov)
  have rd := rd.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd⟩ := rd.sstore hperm (by native_decide) (by evm_ov)
  have rd := rd.push2 endFileAddressEventPc (by native_decide) (by evm_ov)
  have hword := endFileAddressStoreWord_eq (solcSlotWord σ ee ⟨2⟩) data
  exact ⟨_, _, by
    simpa [endFileAddressEventPc, solcSlotWord, hword, hmatch,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.endFileAddressSkipDog {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨8519⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord endFileAddressDogBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 ⟨8565⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd := h.jumpdest (by native_decide) (by evm_ov)
  have rd := rd.dup2 (by native_decide) (by evm_ov)
  have rd := rd.pushConst (⟨0x646f67⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd := rd.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  rw [← endFileAddressDogBytes_word] at rd
  have rd := rd.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord endFileAddressDogBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd
  have rd := rd.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd
  have rd := rd.push2 ⟨8565⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

theorem RD.endFileAddressStoreDog {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD endBytecode ee g s0 ⟨8519⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord endFileAddressDogBytes)
    (hperm : ee.perm = true)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 endFileAddressEventPc
      (data :: what :: ret :: sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨3⟩
        (setAddressOffset0Word (solcSlotWord σ ee ⟨3⟩) data)) k' C' := by
  have rd := h.jumpdest (by native_decide) (by evm_ov)
  have rd := rd.dup2 (by native_decide) (by evm_ov)
  have rd := rd.pushConst (⟨0x646f67⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd := rd.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  rw [hmatch, ← endFileAddressDogBytes_word] at rd
  have rd := rd.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd
  have rd := rd.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd
  have rd := rd.push2 ⟨8565⟩ (by native_decide) (by evm_ov)
  have rd := rd.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd := rd.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd := rd.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd⟩ := rd.sload (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  have rd := rd.sub (by native_decide) (by evm_ov)
  have rd := rd.not (by native_decide) (by evm_ov)
  have rd := rd.and (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  have rd := rd.sub (by native_decide) (by evm_ov)
  have rd := rd.dup4 (by native_decide) (by evm_ov)
  have rd := rd.and (by native_decide) (by evm_ov)
  have rd := rd.or (by native_decide) (by evm_ov)
  have rd := rd.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd⟩ := rd.sstore hperm (by native_decide) (by evm_ov)
  have rd := rd.push2 endFileAddressEventPc (by native_decide) (by evm_ov)
  have hword := endFileAddressStoreWord_eq (solcSlotWord σ ee ⟨3⟩) data
  exact ⟨_, _, by
    simpa [endFileAddressEventPc, solcSlotWord, hword, hmatch,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.endFileAddressSkipVow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨8565⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord endFileAddressVowBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 ⟨8611⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd := h.jumpdest (by native_decide) (by evm_ov)
  have rd := rd.dup2 (by native_decide) (by evm_ov)
  have rd := rd.pushConst (⟨0x766f77⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd := rd.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  rw [← endFileAddressVowBytes_word] at rd
  have rd := rd.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord endFileAddressVowBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd
  have rd := rd.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd
  have rd := rd.push2 ⟨8611⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

theorem RD.endFileAddressStoreVow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD endBytecode ee g s0 ⟨8565⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord endFileAddressVowBytes)
    (hperm : ee.perm = true)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 endFileAddressEventPc
      (data :: what :: ret :: sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨4⟩
        (setAddressOffset0Word (solcSlotWord σ ee ⟨4⟩) data)) k' C' := by
  have rd := h.jumpdest (by native_decide) (by evm_ov)
  have rd := rd.dup2 (by native_decide) (by evm_ov)
  have rd := rd.pushConst (⟨0x766f77⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd := rd.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  rw [hmatch, ← endFileAddressVowBytes_word] at rd
  have rd := rd.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd
  have rd := rd.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd
  have rd := rd.push2 ⟨8611⟩ (by native_decide) (by evm_ov)
  have rd := rd.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd := rd.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd := rd.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd⟩ := rd.sload (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  have rd := rd.sub (by native_decide) (by evm_ov)
  have rd := rd.not (by native_decide) (by evm_ov)
  have rd := rd.and (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  have rd := rd.sub (by native_decide) (by evm_ov)
  have rd := rd.dup4 (by native_decide) (by evm_ov)
  have rd := rd.and (by native_decide) (by evm_ov)
  have rd := rd.or (by native_decide) (by evm_ov)
  have rd := rd.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd⟩ := rd.sstore hperm (by native_decide) (by evm_ov)
  have rd := rd.push2 endFileAddressEventPc (by native_decide) (by evm_ov)
  have hword := endFileAddressStoreWord_eq (solcSlotWord σ ee ⟨4⟩) data
  exact ⟨_, _, by
    simpa [endFileAddressEventPc, solcSlotWord, hword, hmatch,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.endFileAddressSkipPot {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨8611⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord endFileAddressPotBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 ⟨8657⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd := h.jumpdest (by native_decide) (by evm_ov)
  have rd := rd.dup2 (by native_decide) (by evm_ov)
  have rd := rd.pushConst (⟨0x1c1bdd⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd := rd.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  rw [← endFileAddressPotBytes_word] at rd
  have rd := rd.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord endFileAddressPotBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd
  have rd := rd.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd
  have rd := rd.push2 ⟨8657⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

theorem RD.endFileAddressStorePot {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD endBytecode ee g s0 ⟨8611⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord endFileAddressPotBytes)
    (hperm : ee.perm = true)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 endFileAddressEventPc
      (data :: what :: ret :: sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨5⟩
        (setAddressOffset0Word (solcSlotWord σ ee ⟨5⟩) data)) k' C' := by
  have rd := h.jumpdest (by native_decide) (by evm_ov)
  have rd := rd.dup2 (by native_decide) (by evm_ov)
  have rd := rd.pushConst (⟨0x1c1bdd⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd := rd.push1 ⟨234⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  rw [hmatch, ← endFileAddressPotBytes_word] at rd
  have rd := rd.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd
  have rd := rd.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd
  have rd := rd.push2 ⟨8657⟩ (by native_decide) (by evm_ov)
  have rd := rd.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd := rd.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  have rd := rd.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd⟩ := rd.sload (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  have rd := rd.sub (by native_decide) (by evm_ov)
  have rd := rd.not (by native_decide) (by evm_ov)
  have rd := rd.and (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  have rd := rd.sub (by native_decide) (by evm_ov)
  have rd := rd.dup4 (by native_decide) (by evm_ov)
  have rd := rd.and (by native_decide) (by evm_ov)
  have rd := rd.or (by native_decide) (by evm_ov)
  have rd := rd.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd⟩ := rd.sstore hperm (by native_decide) (by evm_ov)
  have rd := rd.push2 endFileAddressEventPc (by native_decide) (by evm_ov)
  have hword := endFileAddressStoreWord_eq (solcSlotWord σ ee ⟨5⟩) data
  exact ⟨_, _, by
    simpa [endFileAddressEventPc, solcSlotWord, hword, hmatch,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.endFileAddressSkipSpot {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨8657⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord endFileAddressSpotBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 ⟨8704⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd := h.jumpdest (by native_decide) (by evm_ov)
  have rd := rd.dup2 (by native_decide) (by evm_ov)
  have rd := rd.pushConst (⟨0x1cdc1bdd⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd := rd.push1 ⟨226⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  rw [← endFileAddressSpotBytes_word] at rd
  have rd := rd.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord endFileAddressSpotBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd
  have rd := rd.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd
  have rd := rd.push2 ⟨8704⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

theorem RD.endFileAddressStoreSpot {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD endBytecode ee g s0 ⟨8657⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord endFileAddressSpotBytes)
    (hperm : ee.perm = true)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 endFileAddressEventPc
      (data :: what :: ret :: sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨6⟩
        (setAddressOffset0Word (solcSlotWord σ ee ⟨6⟩) data)) k' C' := by
  have rd := h.jumpdest (by native_decide) (by evm_ov)
  have rd := rd.dup2 (by native_decide) (by evm_ov)
  have rd := rd.pushConst (⟨0x1cdc1bdd⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd := rd.push1 ⟨226⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  rw [hmatch, ← endFileAddressSpotBytes_word] at rd
  have rd := rd.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd
  have rd := rd.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd
  have rd := rd.push2 ⟨8704⟩ (by native_decide) (by evm_ov)
  have rd := rd.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd := rd.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  have rd := rd.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd⟩ := rd.sload (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  have rd := rd.sub (by native_decide) (by evm_ov)
  have rd := rd.not (by native_decide) (by evm_ov)
  have rd := rd.and (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  have rd := rd.sub (by native_decide) (by evm_ov)
  have rd := rd.dup4 (by native_decide) (by evm_ov)
  have rd := rd.and (by native_decide) (by evm_ov)
  have rd := rd.or (by native_decide) (by evm_ov)
  have rd := rd.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd⟩ := rd.sstore hperm (by native_decide) (by evm_ov)
  have rd := rd.push2 endFileAddressEventPc (by native_decide) (by evm_ov)
  have hword := endFileAddressStoreWord_eq (solcSlotWord σ ee ⟨6⟩) data
  exact ⟨_, _, by
    simpa [endFileAddressEventPc, solcSlotWord, hword, hmatch,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

theorem RD.endFileAddressSkipCure {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD endBytecode ee g s0 ⟨8704⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord endFileAddressCureBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 endFileUintUnrecognizedPc
      (data :: what :: ret :: sel :: R) mem (UInt256.ofNat 3) rdata acc k' C' := by
  have rd := h.jumpdest (by native_decide) (by evm_ov)
  have rd := rd.dup2 (by native_decide) (by evm_ov)
  have rd := rd.pushConst (⟨0x63757265⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd := rd.push1 ⟨224⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  rw [← endFileAddressCureBytes_word] at rd
  have rd := rd.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord endFileAddressCureBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd
  have rd := rd.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd
  have rd := rd.push2 endFileUintUnrecognizedPc (by native_decide) (by evm_ov)
  exact ⟨_, _, rd.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)⟩

theorem RD.endFileAddressStoreCure {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD endBytecode ee g s0 ⟨8704⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord endFileAddressCureBytes)
    (hperm : ee.perm = true)
    (hov : R.length + 19 ≤ 1024) :
    ∃ k' C', RD endBytecode ee g s0 endFileAddressEventPc
      (data :: what :: ret :: sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨7⟩
        (setAddressOffset0Word (solcSlotWord σ ee ⟨7⟩) data)) k' C' := by
  have rd := h.jumpdest (by native_decide) (by evm_ov)
  have rd := rd.dup2 (by native_decide) (by evm_ov)
  have rd := rd.pushConst (⟨0x63757265⟩ : UInt256)
    (width := 4) (op := .PUSH4) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd := rd.push1 ⟨224⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  rw [hmatch, ← endFileAddressCureBytes_word] at rd
  have rd := rd.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd
  have rd := rd.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd
  have rd := rd.push2 endFileUintUnrecognizedPc (by native_decide) (by evm_ov)
  have rd := rd.jumpiNT (by native_decide) (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by evm_ov)
  have rd := rd.push1 ⟨7⟩ (by native_decide) (by evm_ov)
  have rd := rd.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd⟩ := rd.sload (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  have rd := rd.sub (by native_decide) (by evm_ov)
  have rd := rd.not (by native_decide) (by evm_ov)
  have rd := rd.and (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd := rd.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd := rd.shl (by native_decide) (by evm_ov)
  have rd := rd.sub (by native_decide) (by evm_ov)
  have rd := rd.dup4 (by native_decide) (by evm_ov)
  have rd := rd.and (by native_decide) (by evm_ov)
  have rd := rd.or (by native_decide) (by evm_ov)
  have rd := rd.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd⟩ := rd.sstore hperm (by native_decide) (by evm_ov)
  have hword := endFileAddressStoreWord_eq (solcSlotWord σ ee ⟨7⟩) data
  exact ⟨_, _, by
    simpa [endFileAddressEventPc, solcSlotWord, hword, hmatch,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd⟩

theorem endFileAddressX_unrecognized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hnotVatWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressVatBytes)
    (hnotCatWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressCatBytes)
    (hnotDogWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressDogBytes)
    (hnotVowWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressVowBytes)
    (hnotPotWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressPotBytes)
    (hnotSpotWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressSpotBytes)
    (hnotCureWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressCureBytes)
    (h : RD endBytecode I g s0 endFileAddressSwitchPc
      [endFileAddressDataMaskedWord I, calldataWord I.calldata 4, endRelyReturnPc, sel]
      (endRelyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  obtain ⟨_, _, hcatPc⟩ := RD.endFileAddressSkipVat h hnotVatWord (by simp)
  obtain ⟨_, _, hdogPc⟩ := RD.endFileAddressSkipCat hcatPc hnotCatWord (by simp)
  obtain ⟨_, _, hvowPc⟩ := RD.endFileAddressSkipDog hdogPc hnotDogWord (by simp)
  obtain ⟨_, _, hpotPc⟩ := RD.endFileAddressSkipVow hvowPc hnotVowWord (by simp)
  obtain ⟨_, _, hspotPc⟩ := RD.endFileAddressSkipPot hpotPc hnotPotWord (by simp)
  obtain ⟨_, _, hcurePc⟩ := RD.endFileAddressSkipSpot hspotPc hnotSpotWord (by simp)
  obtain ⟨_, _, hunrecPc⟩ := RD.endFileAddressSkipCure hcurePc hnotCureWord (by simp)
  exact RD.endFileUintUnrecognizedRevert hunrecPc
    (endRelyAuthHashMem_size I) (endRelyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

/-! ### Source execution -/

theorem endFileAddressSourceAuthReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I ≠ ⟨1⟩) :
    let locals := endFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileAddress_auth_false evm0 I (by simp [evm0, initState]) hauth
  refine ExecFuncBody.execBlockRevert ?_
  simpa [fileAddressTransition, nonpayable, auth] using
    nonpayableSecondRequireReverts
      (cfg := config)
      (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := ([
        .require (.binary .eq (.storage liveRef) (.intLit 1)),
        .ite (.binary .eq (.var "what") vatLit) [ .assign .storage vatRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") catLit) [ .assign .storage catRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
        [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
        [ .require (.boolLit false) ] ] ] ] ] ] ]
      ] : List Stmt))
      (by simp [evm0, initState]; exact hwv)
      hguard

theorem endFileAddressSourceLiveReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I ≠ ⟨1⟩) :
    let locals := endFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguardAuth :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
    simpa [locals, evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_endFileAddress_live_false evm0 I hlive
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguardLive)
  simpa [ExecTransitionBody, fileAddressTransition, nonpayable, auth, locals, evm0] using
    ExecFuncBody.execBlockRevert hblock

theorem endFileAddressSourceVatOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hwhat : endFileAddressWhat I = endFileAddressVatBytes) :
    let locals := endFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := endFileAddressPostState evm0 I ⟨1⟩
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_endFileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool true) := by
    simpa [vatLit, strLit3, endFileAddressVatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (endFileAddressData I)) := by
    simpa [locals] using
      evalExpr_endFileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simpa [locals] using endFileAddressLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage vatRef (.address (endFileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using
      endFileAddressAssignAddress evm0 I ⟨1⟩ vatRef
        ({ base := "vat", steps := [] } : EvaledStorageRef)
        (by simp [endFileAddressLocals, vatRef])
        (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by rfl)
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage vatRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hvat hthen) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem endFileAddressSourceCatOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hnotVat : endFileAddressWhat I ≠ endFileAddressVatBytes)
    (hwhat : endFileAddressWhat I = endFileAddressCatBytes) :
    let locals := endFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := endFileAddressPostState evm0 I ⟨2⟩
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_endFileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, strLit3, endFileAddressVatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool true) := by
    simpa [catLit, strLit3, endFileAddressCatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressCatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (endFileAddressData I)) := by
    simpa [locals] using
      evalExpr_endFileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simpa [locals] using endFileAddressLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage catRef (.address (endFileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using
      endFileAddressAssignAddress evm0 I ⟨2⟩ catRef
        ({ base := "cat", steps := [] } : EvaledStorageRef)
        (by simp [endFileAddressLocals, catRef])
        (by simp [catRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by rfl)
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage catRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") catLit) [ .assign .storage catRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcat hthen) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvat hcatBlock) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem endFileAddressSourceDogOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hnotVat : endFileAddressWhat I ≠ endFileAddressVatBytes)
    (hnotCat : endFileAddressWhat I ≠ endFileAddressCatBytes)
    (hwhat : endFileAddressWhat I = endFileAddressDogBytes) :
    let locals := endFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := endFileAddressPostState evm0 I ⟨3⟩
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_endFileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, strLit3, endFileAddressVatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool false) := by
    simpa [catLit, strLit3, endFileAddressCatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressCatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotCat)
  have hdog :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dogLit) = .ok (.bool true) := by
    simpa [dogLit, strLit3, endFileAddressDogBytes, locals] using
      (evalExpr_endFileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressDogBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (endFileAddressData I)) := by
    simpa [locals] using
      evalExpr_endFileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simpa [locals] using endFileAddressLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage dogRef (.address (endFileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using
      endFileAddressAssignAddress evm0 I ⟨3⟩ dogRef
        ({ base := "dog", steps := [] } : EvaledStorageRef)
        (by simp [endFileAddressLocals, dogRef])
        (by simp [dogRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by rfl)
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage dogRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hdogBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hdog hthen) ExecBlock.nil
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") catLit) [ .assign .storage catRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcat hdogBlock) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvat hcatBlock) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem endFileAddressSourceVowOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hnotVat : endFileAddressWhat I ≠ endFileAddressVatBytes)
    (hnotCat : endFileAddressWhat I ≠ endFileAddressCatBytes)
    (hnotDog : endFileAddressWhat I ≠ endFileAddressDogBytes)
    (hwhat : endFileAddressWhat I = endFileAddressVowBytes) :
    let locals := endFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := endFileAddressPostState evm0 I ⟨4⟩
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_endFileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, strLit3, endFileAddressVatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool false) := by
    simpa [catLit, strLit3, endFileAddressCatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressCatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotCat)
  have hdog :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dogLit) = .ok (.bool false) := by
    simpa [dogLit, strLit3, endFileAddressDogBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressDogBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotDog)
  have hvow :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowLit) = .ok (.bool true) := by
    simpa [vowLit, strLit3, endFileAddressVowBytes, locals] using
      (evalExpr_endFileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVowBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (endFileAddressData I)) := by
    simpa [locals] using
      evalExpr_endFileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simpa [locals] using endFileAddressLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage vowRef (.address (endFileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using
      endFileAddressAssignAddress evm0 I ⟨4⟩ vowRef
        ({ base := "vow", steps := [] } : EvaledStorageRef)
        (by simp [endFileAddressLocals, vowRef])
        (by simp [vowRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by rfl)
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage vowRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hvowBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hvow hthen) ExecBlock.nil
  have hdogBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hdog hvowBlock) ExecBlock.nil
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") catLit) [ .assign .storage catRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcat hdogBlock) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvat hcatBlock) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem endFileAddressSourcePotOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hnotVat : endFileAddressWhat I ≠ endFileAddressVatBytes)
    (hnotCat : endFileAddressWhat I ≠ endFileAddressCatBytes)
    (hnotDog : endFileAddressWhat I ≠ endFileAddressDogBytes)
    (hnotVow : endFileAddressWhat I ≠ endFileAddressVowBytes)
    (hwhat : endFileAddressWhat I = endFileAddressPotBytes) :
    let locals := endFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := endFileAddressPostState evm0 I ⟨5⟩
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_endFileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, strLit3, endFileAddressVatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool false) := by
    simpa [catLit, strLit3, endFileAddressCatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressCatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotCat)
  have hdog :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dogLit) = .ok (.bool false) := by
    simpa [dogLit, strLit3, endFileAddressDogBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressDogBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotDog)
  have hvow :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowLit) = .ok (.bool false) := by
    simpa [vowLit, strLit3, endFileAddressVowBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVowBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotVow)
  have hpot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") potLit) = .ok (.bool true) := by
    simpa [potLit, strLit3, endFileAddressPotBytes, locals] using
      (evalExpr_endFileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressPotBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (endFileAddressData I)) := by
    simpa [locals] using
      evalExpr_endFileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simpa [locals] using endFileAddressLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage potRef (.address (endFileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using
      endFileAddressAssignAddress evm0 I ⟨5⟩ potRef
        ({ base := "pot", steps := [] } : EvaledStorageRef)
        (by simp [endFileAddressLocals, potRef])
        (by simp [potRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by rfl)
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage potRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hpotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hpot hthen) ExecBlock.nil
  have hvowBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvow hpotBlock) ExecBlock.nil
  have hdogBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hdog hvowBlock) ExecBlock.nil
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") catLit) [ .assign .storage catRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcat hdogBlock) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvat hcatBlock) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem endFileAddressSourceSpotOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hnotVat : endFileAddressWhat I ≠ endFileAddressVatBytes)
    (hnotCat : endFileAddressWhat I ≠ endFileAddressCatBytes)
    (hnotDog : endFileAddressWhat I ≠ endFileAddressDogBytes)
    (hnotVow : endFileAddressWhat I ≠ endFileAddressVowBytes)
    (hnotPot : endFileAddressWhat I ≠ endFileAddressPotBytes)
    (hwhat : endFileAddressWhat I = endFileAddressSpotBytes) :
    let locals := endFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := endFileAddressPostState evm0 I ⟨6⟩
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_endFileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, strLit3, endFileAddressVatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool false) := by
    simpa [catLit, strLit3, endFileAddressCatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressCatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotCat)
  have hdog :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dogLit) = .ok (.bool false) := by
    simpa [dogLit, strLit3, endFileAddressDogBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressDogBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotDog)
  have hvow :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowLit) = .ok (.bool false) := by
    simpa [vowLit, strLit3, endFileAddressVowBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVowBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotVow)
  have hpot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") potLit) = .ok (.bool false) := by
    simpa [potLit, strLit3, endFileAddressPotBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressPotBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotPot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") spotLit) = .ok (.bool true) := by
    simpa [spotLit, strLit4, endFileAddressSpotBytes, locals] using
      (evalExpr_endFileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressSpotBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (endFileAddressData I)) := by
    simpa [locals] using
      evalExpr_endFileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simpa [locals] using endFileAddressLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage spotRef (.address (endFileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using
      endFileAddressAssignAddress evm0 I ⟨6⟩ spotRef
        ({ base := "spot", steps := [] } : EvaledStorageRef)
        (by simp [endFileAddressLocals, spotRef])
        (by simp [spotRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by rfl)
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage spotRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hspotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hspot hthen) ExecBlock.nil
  have hpotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hpot hspotBlock) ExecBlock.nil
  have hvowBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvow hpotBlock) ExecBlock.nil
  have hdogBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hdog hvowBlock) ExecBlock.nil
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") catLit) [ .assign .storage catRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcat hdogBlock) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvat hcatBlock) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem endFileAddressSourceCureOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hnotVat : endFileAddressWhat I ≠ endFileAddressVatBytes)
    (hnotCat : endFileAddressWhat I ≠ endFileAddressCatBytes)
    (hnotDog : endFileAddressWhat I ≠ endFileAddressDogBytes)
    (hnotVow : endFileAddressWhat I ≠ endFileAddressVowBytes)
    (hnotPot : endFileAddressWhat I ≠ endFileAddressPotBytes)
    (hnotSpot : endFileAddressWhat I ≠ endFileAddressSpotBytes)
    (hwhat : endFileAddressWhat I = endFileAddressCureBytes) :
    let locals := endFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := endFileAddressPostState evm0 I ⟨7⟩
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguardAuth :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_endFileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, strLit3, endFileAddressVatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool false) := by
    simpa [catLit, strLit3, endFileAddressCatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressCatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotCat)
  have hdog :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dogLit) = .ok (.bool false) := by
    simpa [dogLit, strLit3, endFileAddressDogBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressDogBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotDog)
  have hvow :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowLit) = .ok (.bool false) := by
    simpa [vowLit, strLit3, endFileAddressVowBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVowBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotVow)
  have hpot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") potLit) = .ok (.bool false) := by
    simpa [potLit, strLit3, endFileAddressPotBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressPotBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotPot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") spotLit) = .ok (.bool false) := by
    simpa [spotLit, strLit4, endFileAddressSpotBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressSpotBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotSpot)
  have hcure :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") cureLit) = .ok (.bool true) := by
    simpa [cureLit, strLit4, endFileAddressCureBytes, locals] using
      (evalExpr_endFileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressCureBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (endFileAddressData I)) := by
    simpa [locals] using
      evalExpr_endFileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simpa [locals] using endFileAddressLocals_get_data I)
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage cureRef (.address (endFileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1] using
      endFileAddressAssignAddress evm0 I ⟨7⟩ cureRef
        ({ base := "cure", steps := [] } : EvaledStorageRef)
        (by simp [endFileAddressLocals, cureRef])
        (by simp [cureRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by rfl)
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage cureRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hcureBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcure hthen) ExecBlock.nil
  have hspotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hspot hcureBlock) ExecBlock.nil
  have hpotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hpot hspotBlock) ExecBlock.nil
  have hvowBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvow hpotBlock) ExecBlock.nil
  have hdogBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hdog hvowBlock) ExecBlock.nil
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") catLit) [ .assign .storage catRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ] ]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcat hdogBlock) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvat hcatBlock) ExecBlock.nil
  simpa [ExecTransitionBody, locals, evm0, evm1] using ExecFuncBody.execBlockOK hblock

theorem endFileAddressSourceUnrecognizedReverts {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : endRelyAuthWord σ I = ⟨1⟩)
    (hlive : endSlotWord ⟨8⟩ σ I = ⟨1⟩)
    (hnotVat : endFileAddressWhat I ≠ endFileAddressVatBytes)
    (hnotCat : endFileAddressWhat I ≠ endFileAddressCatBytes)
    (hnotDog : endFileAddressWhat I ≠ endFileAddressDogBytes)
    (hnotVow : endFileAddressWhat I ≠ endFileAddressVowBytes)
    (hnotPot : endFileAddressWhat I ≠ endFileAddressPotBytes)
    (hnotSpot : endFileAddressWhat I ≠ endFileAddressSpotBytes)
    (hnotCure : endFileAddressWhat I ≠ endFileAddressCureBytes) :
    let locals := endFileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguardAuth :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endRelyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_endFileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hguardLive :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, endSlotWord, initState, Solm.EVM.storageLoad, State.lookupAccount]
      using evalExpr_endFileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, strLit3, endFileAddressVatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool false) := by
    simpa [catLit, strLit3, endFileAddressCatBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressCatBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotCat)
  have hdog :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dogLit) = .ok (.bool false) := by
    simpa [dogLit, strLit3, endFileAddressDogBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressDogBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotDog)
  have hvow :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowLit) = .ok (.bool false) := by
    simpa [vowLit, strLit3, endFileAddressVowBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressVowBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotVow)
  have hpot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") potLit) = .ok (.bool false) := by
    simpa [potLit, strLit3, endFileAddressPotBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressPotBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotPot)
  have hspot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") spotLit) = .ok (.bool false) := by
    simpa [spotLit, strLit4, endFileAddressSpotBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressSpotBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotSpot)
  have hcure :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") cureLit) = .ok (.bool false) := by
    simpa [cureLit, strLit4, endFileAddressCureBytes, locals] using
      (evalExpr_endFileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := endFileAddressCureBytes)
        (by simpa [locals] using endFileAddressLocals_get_what I) hnotCure)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hunrec :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hcureBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcure hunrec)
  have hspotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hspot hcureBlock)
  have hpotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hpot hspotBlock)
  have hvowBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hvow hpotBlock)
  have hdogBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hdog hvowBlock)
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .ite (.binary .eq (.var "what") catLit) [ .assign .storage catRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") dogLit) [ .assign .storage dogRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") vowLit) [ .assign .storage vowRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") potLit) [ .assign .storage potRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") spotLit) [ .assign .storage spotRef (.var "data") ]
          [ .ite (.binary .eq (.var "what") cureLit) [ .assign .storage cureRef (.var "data") ]
          [ .require (.boolLit false) ] ] ] ] ] ] ]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcat hdogBlock)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardAuth) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardLive) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hvat hcatBlock)
  simpa [ExecTransitionBody, locals, evm0] using ExecFuncBody.execBlockRevert hblock

theorem endFileAddressBodyCoreStore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {slot : UInt256}
    (hcode : I.code = endBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (endFileAddressLocals I))
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (endFileAddressLocals I) fileAddressTransition.body
        (.returned { contract := contract, locals := endFileAddressLocals I }
          (endFileAddressPostState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I) I slot) none))
    (hret :
      RDret endBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm slot
          (setAddressOffset0Word (solcSlotWord σ_evm I slot)
            (endFileAddressDataMaskedWord I)))
        ByteArray.empty)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let stored :=
    setAddressOffset0Word (solcSlotWord σ_evm I slot) (endFileAddressDataMaskedWord I)
  have hslotWord : endSlotWord slot σ_evm I = endSlotWord slot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner slot ⟨0⟩
  have hstoredSolm :
      stored =
        setAddressOffset0Word (solcSlotWord σ_solm I slot)
          (endFileAddressDataMaskedWord I) := by
    simpa [stored, endSlotWord] using
      congrArg (fun old => setAddressOffset0Word old (endFileAddressDataMaskedWord I))
        hslotWord
  have hcreated :
      (cA, sstoreAccountMap I.codeOwner σ_evm slot stored).1 =
        (endFileAddressPostState evmSolm I slot).createdAccounts := by
    simp [endFileAddressPostState, evmSolm, initState, storageStore_createdAccounts]
  have haccounts :
      accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm slot stored)
        (endFileAddressPostState evmSolm I slot).accountMap := by
    have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner slot stored hAccounts
    simpa [endFileAddressPostState, evmSolm, initState, storageStore_accountMap, stored,
      hstoredSolm, solcSlotWord, endSlotWord, Solm.EVM.storageLoad] using hbase
  have henc : returnEquiv ByteArray.empty none fileAddressTransition.returnType := by
    simpa [fileAddressTransition] using
      (returnEquiv.fallthrough (o := ByteArray.empty) (r := none) (t := [])
        (dvs := []) rfl (by native_decide) (by native_decide))
  have hret' :
      RDret endBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm slot stored) ByteArray.empty := by
    simpa [stored] using hret
  simpa [evmSolm] using
    hret'.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode
      (by simpa [evmSolm] using hbody) hcreated haccounts henc

theorem endFileAddressBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = endBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (selectorOf fileAddressTransition))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsel' : selIs I endFileAddressConcreteSelector := by
    simpa [endFileAddressSelectorBytes, endFileAddressConcreteSelector] using hsel
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I endFileAddressConcreteSelector (by rfl) hsel'
  have hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition :=
    endDispatchFileAddress hsel
  have hreach := endReachFileAddressBody (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hcode hwv hsz4 hsize hsel'
  by_cases hsz68 : 68 ≤ I.calldata.size
  · have hdecode := endDecode_fileAddress_ok (I := I) hsz68
    obtain ⟨_, _, hdecoded⟩ :=
      endFileAddressX_decoded (g := Sat256.ofUInt256 g) hsz68 hsize hreach
    let evmSolm := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hauthCouple : endRelyAuthWord σ_evm I = endRelyAuthWord σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner (endRelyAuthStorageSlot I) ⟨0⟩
    by_cases hauth : endRelyAuthWord σ_evm I = ⟨1⟩
    · have hauthSolm : endRelyAuthWord σ_solm I = ⟨1⟩ := by
        rw [← hauthCouple]
        exact hauth
      obtain ⟨_, _, hauthPc⟩ := endFileAddressX_authorized (I := I) hauth hdecoded
      have hliveCouple : endSlotWord ⟨8⟩ σ_evm I = endSlotWord ⟨8⟩ σ_solm I :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
      by_cases hlive : endSlotWord ⟨8⟩ σ_evm I = ⟨1⟩
      · have hliveSolm : endSlotWord ⟨8⟩ σ_solm I = ⟨1⟩ := by
          rw [← hliveCouple]
          exact hlive
        obtain ⟨_, _, hswitch⟩ := endFileAddressX_live (I := I) hlive hauthPc
        have hsz36 : 36 ≤ I.calldata.size := by omega
        by_cases hvat : endFileAddressWhat I = endFileAddressVatBytes
        · have hvatWord :
              calldataWord I.calldata 4 = ABI.bytesToWord endFileAddressVatBytes :=
            endFileAddressWhatWord_eq_of_bytes_eq hsz36 hvat
          have hbody :
              ExecTransitionBody config contract evmSolm (endFileAddressLocals I)
                fileAddressTransition.body
                (.returned { contract := contract, locals := endFileAddressLocals I }
                  (endFileAddressPostState evmSolm I ⟨1⟩) none) := by
            simpa [evmSolm] using
              endFileAddressSourceVatOk (cA := cA) (gh := gh) (bl := bl)
                (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                hwv hauthSolm hliveSolm hvat
          obtain ⟨_, _, hstore⟩ :=
            RD.endFileAddressStoreVat hswitch hvatWord hperm (by simp)
          have hret := endFileAddressX_logReturn (I := I) (g := Sat256.ofUInt256 g)
            hperm hstore
          exact endFileAddressBodyCoreStore hcode hdispatch hdecode hbody hret hAccounts
        · have hnotVatWord :
              calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressVatBytes :=
            endFileAddressWhatWord_ne_of_bytes_ne hsz36 hvat (by native_decide)
          obtain ⟨_, _, hcatPc⟩ := RD.endFileAddressSkipVat hswitch hnotVatWord (by simp)
          by_cases hcat : endFileAddressWhat I = endFileAddressCatBytes
          · have hcatWord :
                calldataWord I.calldata 4 = ABI.bytesToWord endFileAddressCatBytes :=
              endFileAddressWhatWord_eq_of_bytes_eq hsz36 hcat
            have hbody :
                ExecTransitionBody config contract evmSolm (endFileAddressLocals I)
                  fileAddressTransition.body
                  (.returned { contract := contract, locals := endFileAddressLocals I }
                    (endFileAddressPostState evmSolm I ⟨2⟩) none) := by
              simpa [evmSolm] using
                endFileAddressSourceCatOk (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hwv hauthSolm hliveSolm hvat hcat
            obtain ⟨_, _, hstore⟩ :=
              RD.endFileAddressStoreCat hcatPc hcatWord hperm (by simp)
            have hret := endFileAddressX_logReturn (I := I) (g := Sat256.ofUInt256 g)
              hperm hstore
            exact endFileAddressBodyCoreStore hcode hdispatch hdecode hbody hret hAccounts
          · have hnotCatWord :
                calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressCatBytes :=
              endFileAddressWhatWord_ne_of_bytes_ne hsz36 hcat (by native_decide)
            obtain ⟨_, _, hdogPc⟩ := RD.endFileAddressSkipCat hcatPc hnotCatWord (by simp)
            by_cases hdog : endFileAddressWhat I = endFileAddressDogBytes
            · have hdogWord :
                  calldataWord I.calldata 4 = ABI.bytesToWord endFileAddressDogBytes :=
                endFileAddressWhatWord_eq_of_bytes_eq hsz36 hdog
              have hbody :
                  ExecTransitionBody config contract evmSolm (endFileAddressLocals I)
                    fileAddressTransition.body
                    (.returned { contract := contract, locals := endFileAddressLocals I }
                      (endFileAddressPostState evmSolm I ⟨3⟩) none) := by
                simpa [evmSolm] using
                  endFileAddressSourceDogOk (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hauthSolm hliveSolm hvat hcat hdog
              obtain ⟨_, _, hstore⟩ :=
                RD.endFileAddressStoreDog hdogPc hdogWord hperm (by simp)
              have hret := endFileAddressX_logReturn (I := I) (g := Sat256.ofUInt256 g)
                hperm hstore
              exact endFileAddressBodyCoreStore hcode hdispatch hdecode hbody hret hAccounts
            · have hnotDogWord :
                  calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressDogBytes :=
                endFileAddressWhatWord_ne_of_bytes_ne hsz36 hdog (by native_decide)
              obtain ⟨_, _, hvowPc⟩ := RD.endFileAddressSkipDog hdogPc hnotDogWord (by simp)
              by_cases hvow : endFileAddressWhat I = endFileAddressVowBytes
              · have hvowWord :
                    calldataWord I.calldata 4 = ABI.bytesToWord endFileAddressVowBytes :=
                  endFileAddressWhatWord_eq_of_bytes_eq hsz36 hvow
                have hbody :
                    ExecTransitionBody config contract evmSolm (endFileAddressLocals I)
                      fileAddressTransition.body
                      (.returned { contract := contract, locals := endFileAddressLocals I }
                        (endFileAddressPostState evmSolm I ⟨4⟩) none) := by
                  simpa [evmSolm] using
                    endFileAddressSourceVowOk (cA := cA) (gh := gh) (bl := bl)
                      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                      hwv hauthSolm hliveSolm hvat hcat hdog hvow
                obtain ⟨_, _, hstore⟩ :=
                  RD.endFileAddressStoreVow hvowPc hvowWord hperm (by simp)
                have hret := endFileAddressX_logReturn (I := I) (g := Sat256.ofUInt256 g)
                  hperm hstore
                exact endFileAddressBodyCoreStore hcode hdispatch hdecode hbody hret hAccounts
              · have hnotVowWord :
                    calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressVowBytes :=
                  endFileAddressWhatWord_ne_of_bytes_ne hsz36 hvow (by native_decide)
                obtain ⟨_, _, hpotPc⟩ :=
                  RD.endFileAddressSkipVow hvowPc hnotVowWord (by simp)
                by_cases hpot : endFileAddressWhat I = endFileAddressPotBytes
                · have hpotWord :
                      calldataWord I.calldata 4 = ABI.bytesToWord endFileAddressPotBytes :=
                    endFileAddressWhatWord_eq_of_bytes_eq hsz36 hpot
                  have hbody :
                      ExecTransitionBody config contract evmSolm (endFileAddressLocals I)
                        fileAddressTransition.body
                        (.returned { contract := contract, locals := endFileAddressLocals I }
                          (endFileAddressPostState evmSolm I ⟨5⟩) none) := by
                    simpa [evmSolm] using
                      endFileAddressSourcePotOk (cA := cA) (gh := gh) (bl := bl)
                        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                        hwv hauthSolm hliveSolm hvat hcat hdog hvow hpot
                  obtain ⟨_, _, hstore⟩ :=
                    RD.endFileAddressStorePot hpotPc hpotWord hperm (by simp)
                  have hret := endFileAddressX_logReturn (I := I) (g := Sat256.ofUInt256 g)
                    hperm hstore
                  exact endFileAddressBodyCoreStore hcode hdispatch hdecode hbody hret hAccounts
                · have hnotPotWord :
                      calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressPotBytes :=
                    endFileAddressWhatWord_ne_of_bytes_ne hsz36 hpot (by native_decide)
                  obtain ⟨_, _, hspotPc⟩ :=
                    RD.endFileAddressSkipPot hpotPc hnotPotWord (by simp)
                  by_cases hspot : endFileAddressWhat I = endFileAddressSpotBytes
                  · have hspotWord :
                        calldataWord I.calldata 4 = ABI.bytesToWord endFileAddressSpotBytes :=
                      endFileAddressWhatWord_eq_of_bytes_eq hsz36 hspot
                    have hbody :
                        ExecTransitionBody config contract evmSolm (endFileAddressLocals I)
                          fileAddressTransition.body
                          (.returned { contract := contract, locals := endFileAddressLocals I }
                            (endFileAddressPostState evmSolm I ⟨6⟩) none) := by
                      simpa [evmSolm] using
                        endFileAddressSourceSpotOk (cA := cA) (gh := gh) (bl := bl)
                          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                          hwv hauthSolm hliveSolm hvat hcat hdog hvow hpot hspot
                    obtain ⟨_, _, hstore⟩ :=
                      RD.endFileAddressStoreSpot hspotPc hspotWord hperm (by simp)
                    have hret := endFileAddressX_logReturn (I := I) (g := Sat256.ofUInt256 g)
                      hperm hstore
                    exact endFileAddressBodyCoreStore hcode hdispatch hdecode hbody hret hAccounts
                  · have hnotSpotWord :
                        calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressSpotBytes :=
                      endFileAddressWhatWord_ne_of_bytes_ne hsz36 hspot (by native_decide)
                    obtain ⟨_, _, hcurePc⟩ :=
                      RD.endFileAddressSkipSpot hspotPc hnotSpotWord (by simp)
                    by_cases hcure : endFileAddressWhat I = endFileAddressCureBytes
                    · have hcureWord :
                          calldataWord I.calldata 4 = ABI.bytesToWord endFileAddressCureBytes :=
                        endFileAddressWhatWord_eq_of_bytes_eq hsz36 hcure
                      have hbody :
                          ExecTransitionBody config contract evmSolm (endFileAddressLocals I)
                            fileAddressTransition.body
                            (.returned { contract := contract, locals := endFileAddressLocals I }
                              (endFileAddressPostState evmSolm I ⟨7⟩) none) := by
                        simpa [evmSolm] using
                          endFileAddressSourceCureOk (cA := cA) (gh := gh) (bl := bl)
                            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            hwv hauthSolm hliveSolm hvat hcat hdog hvow hpot hspot hcure
                      obtain ⟨_, _, hstore⟩ :=
                        RD.endFileAddressStoreCure hcurePc hcureWord hperm (by simp)
                      have hret := endFileAddressX_logReturn (I := I)
                        (g := Sat256.ofUInt256 g) hperm hstore
                      exact endFileAddressBodyCoreStore hcode hdispatch hdecode hbody hret hAccounts
                    · have hnotCureWord :
                          calldataWord I.calldata 4 ≠ ABI.bytesToWord endFileAddressCureBytes :=
                        endFileAddressWhatWord_ne_of_bytes_ne hsz36 hcure (by native_decide)
                      have hbody :
                          ExecTransitionBody config contract evmSolm (endFileAddressLocals I)
                            fileAddressTransition.body .reverted := by
                        simpa [evmSolm] using
                          endFileAddressSourceUnrecognizedReverts
                            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                            (σ₀ := σ₀) (A := A) (I := I) (g := g)
                            hwv hauthSolm hliveSolm hvat hcat hdog hvow hpot hspot hcure
                      exact (endFileAddressX_unrecognized hnotVatWord hnotCatWord
                        hnotDogWord hnotVowWord hnotPotWord hnotSpotWord hnotCureWord hswitch)
                        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
      · have hliveSolm : endSlotWord ⟨8⟩ σ_solm I ≠ ⟨1⟩ := by
          intro hbad
          exact hlive (by rw [hliveCouple, hbad])
        have hbody :
            ExecTransitionBody config contract evmSolm (endFileAddressLocals I)
              fileAddressTransition.body .reverted := by
          simpa [evmSolm] using
            endFileAddressSourceLiveReverts
              (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := g) hwv hauthSolm hliveSolm
        exact (endFileAddressX_notLive (I := I) hlive hauthPc)
          |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
    · have hauthSolm : endRelyAuthWord σ_solm I ≠ ⟨1⟩ := by
        intro hbad
        exact hauth (by rw [hauthCouple, hbad])
      have hbody :
          ExecTransitionBody config contract evmSolm (endFileAddressLocals I)
            fileAddressTransition.body .reverted := by
        simpa [evmSolm] using
          endFileAddressSourceAuthReverts
            (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hwv hauthSolm
      exact (endFileAddressX_unauthorized (I := I) hauth hdecoded)
        |>.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · exact (endFileAddressX_shortarg (g := Sat256.ofUInt256 g) hsz4 hsize (by omega) hreach)
      |>.reEquivDecodingFailed hcode hdispatch
        (endDecode_fileAddress_none_short hsz4 (by omega))

end Benchmarks.Dss.End
