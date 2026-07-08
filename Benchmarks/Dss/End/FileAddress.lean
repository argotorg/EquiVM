import Benchmarks.Dss.End.FileUint

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

/-! ## `file(bytes32,address)` -/

abbrev fileAddressWhat (I : ExecutionEnv) : List UInt8 :=
  EVM.Word.toBytesBE (calldataWord I.calldata 4)

abbrev fileAddressDataWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileAddressDataKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (fileAddressDataWord I)

abbrev fileAddressData (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (fileAddressDataWord I).toNat

abbrev fileAddressLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileAddressWhat I))).insert
    "data" (.address (fileAddressData I))

def fileAddressLiveWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  endSlotWord ⟨8⟩ σ I

def fileAddressPostState (evm : EVM.State) (slot : UInt256) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
      (fileAddressDataKey I))

abbrev fileAddressVatBytes : List UInt8 :=
  [118, 97, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileAddressCatBytes : List UInt8 :=
  [99, 97, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileAddressDogBytes : List UInt8 :=
  [100, 111, 103, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileAddressVowBytes : List UInt8 :=
  [118, 111, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileAddressPotBytes : List UInt8 :=
  [112, 111, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileAddressSpotBytes : List UInt8 :=
  [115, 112, 111, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileAddressCureBytes : List UInt8 :=
  [99, 117, 114, 101, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem fileAddressWhat_length (I : ExecutionEnv) :
    (fileAddressWhat I).length = 32 := by
  simpa [fileAddressWhat] using word_toBytesBE_toByteArray_size (calldataWord I.calldata 4)

theorem fileAddressBytes_lengths :
    fileAddressVatBytes.length = 32 ∧ fileAddressCatBytes.length = 32 ∧
    fileAddressDogBytes.length = 32 ∧ fileAddressVowBytes.length = 32 ∧
    fileAddressPotBytes.length = 32 ∧ fileAddressSpotBytes.length = 32 ∧
    fileAddressCureBytes.length = 32 := by
  native_decide

theorem fileAddressConstWords :
    ABI.bytesToWord fileAddressVatBytes =
        UInt256.shiftLeft (⟨0x1d985d⟩ : UInt256) ⟨234⟩ ∧
    ABI.bytesToWord fileAddressCatBytes =
        UInt256.shiftLeft (⟨0x18d85d⟩ : UInt256) ⟨234⟩ ∧
    ABI.bytesToWord fileAddressDogBytes =
        UInt256.shiftLeft (⟨0x646f67⟩ : UInt256) ⟨232⟩ ∧
    ABI.bytesToWord fileAddressVowBytes =
        UInt256.shiftLeft (⟨0x766f77⟩ : UInt256) ⟨232⟩ ∧
    ABI.bytesToWord fileAddressPotBytes =
        UInt256.shiftLeft (⟨0x1c1bdd⟩ : UInt256) ⟨234⟩ ∧
    ABI.bytesToWord fileAddressSpotBytes =
        UInt256.shiftLeft (⟨0x1cdc1bdd⟩ : UInt256) ⟨226⟩ ∧
    ABI.bytesToWord fileAddressCureBytes =
        UInt256.shiftLeft (⟨0x63757265⟩ : UInt256) ⟨224⟩ := by
  native_decide

theorem fileAddressData_value_masked (I : ExecutionEnv) :
    (.address (fileAddressData I) : Value) =
      .address (AccountAddress.ofNat (fileAddressDataKey I).toNat) := by
  simpa [fileAddressData, fileAddressDataKey, fileAddressDataWord] using
    (solcAddressValue_masked (fileAddressDataWord I))

theorem fileAddressWhatWord_eq (I : ExecutionEnv) :
    ABI.bytesToWord (fileAddressWhat I) = calldataWord I.calldata 4 := by
  simp [fileAddressWhat, bytesToWord_toBytesBE]

theorem fileAddressWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hbs : fileAddressWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileAddressWhatWord_eq I).symm

theorem fileAddressWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hneq : fileAddressWhat I ≠ bs) (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  apply hneq
  rw [fileAddressWhat, hword]
  exact toBytesBE_bytesToWord_of_length hbsLen

theorem endDecode_fileAddress_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata =
        some (fileAddressLocals I) := by
  simpa [config, fileAddressTransition, fileAddressLocals, fileAddressWhat, fileAddressData,
    bytes32, bytes32Width, addr, abiBytes32, abiBytes32Width, abiAddress] using
    (endDecodeCalldata_legacyBytes32Address_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem endDecode_fileAddress_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata = none := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (endDecodeCalldata_legacyBytes32Address_none_short (cd := I.calldata)
      (x := "what") (y := "data") hsz4 hshort)

theorem endDispatchFileAddressLocal {I : ExecutionEnv}
    (hsel : selIs I (endSelBytes 20)) :
    dispatchMsg contract I.calldata = some fileAddressTransition := by
  have hcd : I.calldata.extract 0 4 = endSelBytes 20 := (byteArray_eq_of_beq hsel).symm
  rw [dispatchMsg_eq_dispatchList contract I.calldata (by rfl) (by rfl)]
  change dispatchList transitions I.calldata = some fileAddressTransition
  unfold transitions
  simp [dispatchList, selectorOf, hcd, fileAddressSelectorBytes]
  native_decide

theorem fileAddressLocals_get_what (I : ExecutionEnv) :
    (fileAddressLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileAddressWhat I)) := by
  rw [fileAddressLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileAddressLocals_get_data (I : ExecutionEnv) :
    (fileAddressLocals I).get? "data" =
      some (.address (fileAddressData I)) := by
  rw [fileAddressLocals, store_get_self]

theorem evalExpr_fileAddressData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.address (fileAddressData I))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.address (fileAddressData I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.address (fileAddressData I))
  rw [h]
  rfl

theorem evalExpr_fileAddressWhatEq_true {evm : EVM.State} {I : ExecutionEnv}
    {locals : Store} {bs : List UInt8}
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

theorem evalStorageRef_fileAddress_live (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef config { contract := contract, locals := fileAddressLocals I } evm liveRef =
      .ok ({ base := "live", steps := [] } : EvaledStorageRef) := by
  simp [evalStorageRef, evalStorageRefSteps, liveRef, EvalResult.bind, pure, bind]

theorem evalExpr_fileAddress_live_true (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileAddressLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileAddressLocals I } evm
        (.storage liveRef) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileAddressLocals I })
      (slot := liveRef)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (value := .int 1)
      (hbase := by simp [fileAddressLocals, liveRef])
      (her := evalStorageRef_fileAddress_live evm I)
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by simpa [hload] using endStorageLocLoad_uint256 evm ⟨8⟩)]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_fileAddress_live_false (evm : EVM.State) (I : ExecutionEnv)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileAddressLocals I } evm
      (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileAddressLocals I } evm
        (.storage liveRef) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileAddressLocals I })
      (slot := liveRef)
      (er := ({ base := "live", steps := [] } : EvaledStorageRef))
      (t := .int uint256Int)
      (loc := wordLoc ⟨8⟩)
      (hbase := by simp [fileAddressLocals, liveRef])
      (her := evalStorageRef_fileAddress_live evm I)
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

theorem evalStorageRef_fileAddress_auth (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source) :
    evalStorageRef config { contract := contract, locals := fileAddressLocals I } evm
      (wardsRef sender) = .ok (relyAuthEvaledRef I) := by
  simp [evalStorageRef, evalStorageRefStep, wardsRef, sender, envValue, relyAuthEvaledRef,
    relyAuthKey, hsrc, valueToKey?, EvalResult.bind, EvalResult.ofOption, bind, pure,
    evalExpr?]

theorem evalExpr_fileAddress_auth_true (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) = ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileAddressLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileAddressLocals I } evm
        (.storage (wardsRef sender)) = .ok (.int 1) := by
    rw [evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileAddressLocals I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (value := .int 1)
      (hbase := by simp [fileAddressLocals, wardsRef])
      (her := evalStorageRef_fileAddress_auth evm I hsrc)
      (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
      (hloc := by rfl)
      (hload := by
        simpa [hload] using endStorageLocLoad_uint256 evm (relyAuthStorageSlot I))]
  simp only [evalExpr?, hstorage, EvalResult.bind, bind, pure]
  rfl

theorem evalExpr_fileAddress_auth_false (evm : EVM.State) (I : ExecutionEnv)
    (hsrc : evm.executionEnv.source = I.source)
    (hload : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (relyAuthStorageSlot I) ≠ ⟨1⟩) :
    evalExpr? config { contract := contract, locals := fileAddressLocals I } evm
      (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool false) := by
  have hstorage :
      evalExpr? config { contract := contract, locals := fileAddressLocals I } evm
        (.storage (wardsRef sender)) =
          .ok (.int (Int.ofNat
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
              (relyAuthStorageSlot I)).toNat)) := by
    exact evalExpr_storage_scalar_value
      (cfg := config)
      (solm := { contract := contract, locals := fileAddressLocals I })
      (slot := wardsRef sender)
      (er := relyAuthEvaledRef I)
      (t := .int uint256Int)
      (loc := wordLoc (relyAuthStorageSlot I))
      (hbase := by simp [fileAddressLocals, wardsRef])
      (her := evalStorageRef_fileAddress_auth evm I hsrc)
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

theorem assign_fileAddressStorage (evm : EVM.State) (I : ExecutionEnv)
    (base : Solm.Ident) (ref : StorageRef) (slot : UInt256)
    (hbase : (fileAddressLocals I).get? base = none)
    (href : ref = { base := base })
    (hty : storageTypeAt? contract.storage ({ base := base, steps := [] } : EvaledStorageRef) =
      some (.elem .address))
    (hloc : config.storage.layout ({ base := base, steps := [] } : EvaledStorageRef) =
      fun _ => some (addrLoc slot)) :
    assignStorageRef? config { contract := contract, locals := fileAddressLocals I } evm
      .storage ref (.address (fileAddressData I)) =
        .ok ({ contract := contract, locals := fileAddressLocals I },
          fileAddressPostState evm slot I) := by
  subst href
  rw [fileAddressData_value_masked I]
  exact assignStorageRef_storage_scalar_value
    (ty := .elem .address)
    (er := ({ base := base, steps := [] } : EvaledStorageRef))
    (loc := addrLoc slot)
    (hbase := hbase)
    (her := by simp [evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := hty)
    (hloc := hloc)
    (hscalar := by trivial)
    (hstore := by
      simpa [fileAddressPostState, addrLoc] using
        storageLocStore_address_offset0 evm slot (fileAddressDataKey I) (by
          simpa [fileAddressDataKey, fileAddressDataWord,
            u256_land_comm solcAddrMask (fileAddressDataWord I)] using
            solcAddrMask_result_canonical (fileAddressDataWord I)))

theorem endFileAddressSourceBodyVatOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : fileAddressLiveWord σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressVatBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileAddressPostState evm0 ⟨1⟩ I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, fileAddressLiveWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool true) := by
    simpa [vatLit, fileAddressVatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [locals] using
      evalExpr_fileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage vatRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, vatRef] using
      assign_fileAddressStorage evm0 I "vat" vatRef ⟨1⟩
        (by simp [fileAddressLocals])
        rfl
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by
          funext evm
          simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, addrLoc])
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
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hvat hthen) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals, fileAddressTransition, nonpayable, auth] using
    ExecFuncBody.execBlockOK hblock

theorem endFileAddressSourceBodyCatOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : fileAddressLiveWord σ I = ⟨1⟩)
    (hnotVat : fileAddressWhat I ≠ fileAddressVatBytes)
    (hwhat : fileAddressWhat I = fileAddressCatBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileAddressPostState evm0 ⟨2⟩ I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, fileAddressLiveWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, fileAddressVatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool true) := by
    simpa [catLit, fileAddressCatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressCatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [locals] using
      evalExpr_fileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage catRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, catRef] using
      assign_fileAddressStorage evm0 I "cat" catRef ⟨2⟩
        (by simp [fileAddressLocals])
        rfl
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by
          funext evm
          simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, addrLoc])
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage catRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") catLit) [.assign .storage catRef (.var "data")]
          [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcat hthen) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvat hcatBlock) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals, fileAddressTransition, nonpayable, auth] using
    ExecFuncBody.execBlockOK hblock

theorem endFileAddressSourceBodyDogOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : fileAddressLiveWord σ I = ⟨1⟩)
    (hnotVat : fileAddressWhat I ≠ fileAddressVatBytes)
    (hnotCat : fileAddressWhat I ≠ fileAddressCatBytes)
    (hwhat : fileAddressWhat I = fileAddressDogBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileAddressPostState evm0 ⟨3⟩ I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, fileAddressLiveWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, fileAddressVatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool false) := by
    simpa [catLit, fileAddressCatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressCatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotCat)
  have hdog :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dogLit) = .ok (.bool true) := by
    simpa [dogLit, fileAddressDogBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressDogBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [locals] using
      evalExpr_fileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage dogRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, dogRef] using
      assign_fileAddressStorage evm0 I "dog" dogRef ⟨3⟩
        (by simp [fileAddressLocals])
        rfl
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by
          funext evm
          simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, addrLoc])
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage dogRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hdogBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hdog hthen) ExecBlock.nil
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") catLit) [.assign .storage catRef (.var "data")]
          [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcat hdogBlock) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvat hcatBlock) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals, fileAddressTransition, nonpayable, auth] using
    ExecFuncBody.execBlockOK hblock

theorem endFileAddressSourceBodyVowOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : fileAddressLiveWord σ I = ⟨1⟩)
    (hnotVat : fileAddressWhat I ≠ fileAddressVatBytes)
    (hnotCat : fileAddressWhat I ≠ fileAddressCatBytes)
    (hnotDog : fileAddressWhat I ≠ fileAddressDogBytes)
    (hwhat : fileAddressWhat I = fileAddressVowBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileAddressPostState evm0 ⟨4⟩ I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, fileAddressLiveWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, fileAddressVatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool false) := by
    simpa [catLit, fileAddressCatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressCatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotCat)
  have hdog :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dogLit) = .ok (.bool false) := by
    simpa [dogLit, fileAddressDogBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressDogBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotDog)
  have hvow :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowLit) = .ok (.bool true) := by
    simpa [vowLit, fileAddressVowBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVowBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [locals] using
      evalExpr_fileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage vowRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, vowRef] using
      assign_fileAddressStorage evm0 I "vow" vowRef ⟨4⟩
        (by simp [fileAddressLocals])
        rfl
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by
          funext evm
          simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, addrLoc])
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage vowRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hvowBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hvow hthen) ExecBlock.nil
  have hdogBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hdog hvowBlock) ExecBlock.nil
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") catLit) [.assign .storage catRef (.var "data")]
          [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcat hdogBlock) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvat hcatBlock) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals, fileAddressTransition, nonpayable, auth] using
    ExecFuncBody.execBlockOK hblock

theorem endFileAddressSourceBodyPotOk {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : relyAuthWord σ I = ⟨1⟩)
    (hlive : fileAddressLiveWord σ I = ⟨1⟩)
    (hnotVat : fileAddressWhat I ≠ fileAddressVatBytes)
    (hnotCat : fileAddressWhat I ≠ fileAddressCatBytes)
    (hnotDog : fileAddressWhat I ≠ fileAddressDogBytes)
    (hnotVow : fileAddressWhat I ≠ fileAddressVowBytes)
    (hwhat : fileAddressWhat I = fileAddressPotBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := fileAddressPostState evm0 ⟨5⟩ I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage (wardsRef sender)) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, relyAuthWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_auth_true evm0 I (by simp [evm0, initState]) hauth
  have hliveGuard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.storage liveRef) (.intLit 1)) = .ok (.bool true) := by
    simpa [locals, evm0, fileAddressLiveWord, endSlotWord, initState, Solm.EVM.storageLoad,
      State.lookupAccount] using
      evalExpr_fileAddress_live_true evm0 I hlive
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vatLit) = .ok (.bool false) := by
    simpa [vatLit, fileAddressVatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVat)
  have hcat :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") catLit) = .ok (.bool false) := by
    simpa [catLit, fileAddressCatBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressCatBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotCat)
  have hdog :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dogLit) = .ok (.bool false) := by
    simpa [dogLit, fileAddressDogBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressDogBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotDog)
  have hvow :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowLit) = .ok (.bool false) := by
    simpa [vowLit, fileAddressVowBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVowBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVow)
  have hpot :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") potLit) = .ok (.bool true) := by
    simpa [potLit, fileAddressPotBytes, strLit3, locals] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressPotBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [locals] using
      evalExpr_fileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals])
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage potRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [locals, evm1, potRef] using
      assign_fileAddressStorage evm0 I "pot" potRef ⟨5⟩
        (by simp [fileAddressLocals])
        rfl
        (by simp [storageTypeAt?, contract, storageDecls, addrSt])
        (by
          funext evm
          simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, addrLoc])
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage potRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hpotBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hpot hthen) ExecBlock.nil
  have hvowBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvow hpotBlock) ExecBlock.nil
  have hdogBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hdog hvowBlock) ExecBlock.nil
  have hcatBlock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") catLit) [.assign .storage catRef (.var "data")]
          [.ite (.binary .eq (.var "what") dogLit) [.assign .storage dogRef (.var "data")]
          [.ite (.binary .eq (.var "what") vowLit) [.assign .storage vowRef (.var "data")]
          [.ite (.binary .eq (.var "what") potLit) [.assign .storage potRef (.var "data")]
          [.ite (.binary .eq (.var "what") spotLit) [.assign .storage spotRef (.var "data")]
          [.ite (.binary .eq (.var "what") cureLit) [.assign .storage cureRef (.var "data")]
          [.require (.boolLit false)] ] ] ] ] ]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hcat hdogBlock) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hliveGuard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hvat hcatBlock) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals, fileAddressTransition, nonpayable, auth] using
    ExecFuncBody.execBlockOK hblock

theorem endReachFileAddressBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = endBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (endSelBytes 20)) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨1098⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : endSelWord I = ⟨0xd4e8be83⟩ :=
    endSelWord_eq_of_beq I hsz 0xd4 0xe8 0xbe 0x83 ⟨0xd4e8be83⟩
      (by native_decide) (by simpa [endSelBytes] using hsel)
  obtain ⟨_, _, h32⟩ :=
    endReachRootSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hcode hwv hsz hsize
  have hroot :
      UInt256.gt (armSelNat endBytecode (⟨32⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h43raw := RD.selectorSplitNotTakenAuto h32
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    hroot (by simp)
  have h43ex : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨43⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
        selArmPush4Pc] using h43raw⟩
  obtain ⟨_, _, h43⟩ := h43ex
  have h43gt :
      UInt256.gt (armSelNat endBytecode (⟨43⟩ : UInt256)) (endSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have h54raw := RD.selectorSplitNotTakenAuto h43
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h43gt (by simp)
  have h54ex : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨54⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
    exact ⟨_, _, by
      simpa [selArmNextPc, armTgtWidth, selArmJumpiPc, selArmPushTgtPc, selArmEqPc,
        selArmPush4Pc] using h54raw⟩
  obtain ⟨_, _, h54⟩ := h54ex
  have h54gt :
      UInt256.gt (armSelNat endBytecode (⟨54⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h113raw := RD.selectorSplitTakenAuto h54
    (by dsimp [selectorSplitWellFormed]; repeat' first | apply And.intro | native_decide)
    h54gt (by jump_dest) (by simp)
  have h113ex : ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨113⟩ [endSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
    exact ⟨_, _, h113raw⟩
  obtain ⟨_, _, h113⟩ := h113ex
  have h114 := h113.jumpdest (by native_decide) (by simp only [List.length_singleton]; omega)
  have htake :
      UInt256.eq (armSelNat endBytecode (⟨114⟩ : UInt256)) (endSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h1098 := h114.selectorArmTakenAuto
    (by dsimp [armWellFormed]; repeat' first | apply And.intro | native_decide)
    htake (by jump_dest) (by simp)
  exact ⟨_, _, h1098⟩

theorem RD.endFileAddressDecodeToRoutine {cA σ I} {g : Sat256} {s0 : State}
    {k C : ℕ} {sel de : UInt256}
    (h : RD endBytecode I g s0 ⟨1120⟩
      (de :: ⟨4⟩ :: ⟨562⟩ :: [sel])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨8268⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  obtain ⟨_, _, rd8268⟩ := RD.solcBytes32AddressExternalMaskAndJumpMasked
    (code := endBytecode) (decoded := ⟨1120⟩) (ret := ⟨562⟩) (routine := ⟨8268⟩)
    (R := [sel]) h
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by simp)
  exact ⟨_, _, by simpa [fileAddressDataKey, fileAddressDataWord] using rd8268⟩

theorem endFileAddressX_decoded {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz68 : 68 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k C, RD endBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨8268⟩
        [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
        solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := endBytecode) (sel := sel) (entry := ⟨1098⟩) (ret := ⟨562⟩)
    (decoded := ⟨1120⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  exact RD.endFileAddressDecodeToRoutine hdecoded

theorem endFileAddressX_shortarg {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hsz4 : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hshort : I.calldata.size < 68)
    (hreach : ∃ k C, RD endBytecode I g
      (initState cA gh bl σ σ₀ g A I) ⟨1098⟩ [sel]
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
    (entry := ⟨1098⟩) (ret := ⟨562⟩) (decoded := ⟨1120⟩)
    (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt

set_option maxHeartbeats 1000000 in
theorem endFileAddressX_authorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I = ⟨1⟩)
    (h : RD endBytecode I g s0 ⟨8268⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨8357⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd8274pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8275 := rd8274pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd8279pre := evm_run rd8275 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd8280 := rd8279pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd8283pre := evm_run rd8280 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd8284 := rd8283pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k8285, C8285, rd8285raw⟩ := rd8284.sload (by native_decide) (by evm_ov)
  have rd8285 : RD endBytecode I g s0 ⟨8285⟩
      (relyAuthWord σ I :: fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k8285 C8285 := by
    simpa [relyAuthWord, endSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd8285raw
  have rd8288pre := evm_run rd8285 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hauth, u256_eq_refl] at rd8288pre
  have rd8291 := rd8288pre.pushConst (⟨8357⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd8291.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem endFileAddressX_unauthorized {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hauth : relyAuthWord σ I ≠ ⟨1⟩)
    (h : RD endBytecode I g s0 ⟨8268⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have hauthSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((relyAuthHashMem I).readWithPadding 0 64))) =
        mapSlot (relySourceWord I) ⟨0⟩ := by
    simpa [relyAuthHashMem, mapSlot, solcMappingSlot] using
      twoWordHashMem_solcMappingSlot (⟨0⟩ : UInt256) (relySourceWord I)
        solcFreePtrMem_size
  have rd8274pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw caller (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8275 := rd8274pre.mstore 0 (wordAt0Mem (relySourceWord I) solcFreePtrMem)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd8279pre := evm_run rd8275 with [
    raw push1 ⟨32⟩ (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd8280 := rd8279pre.mstore 0 (relyAuthHashMem I)
    (UInt256.ofNat 3) (by native_decide) mem_cost (by rfl) (by native_decide)
    (by evm_ov)
  have rd8283pre := evm_run rd8280 with [
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have rd8284 := rd8283pre.keccak256 0 (mapSlot (relySourceWord I) ⟨0⟩)
    (UInt256.ofNat 3) (by native_decide) mem_cost hauthSlot (by native_decide)
    (by evm_ov)
  obtain ⟨k8285, C8285, rd8285raw⟩ := rd8284.sload (by native_decide) (by evm_ov)
  have rd8285 : RD endBytecode I g s0 ⟨8285⟩
      (relyAuthWord σ I :: fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k8285 C8285 := by
    simpa [relyAuthWord, endSlotWord, relyAuthStorageSlot_eq_mapSlot_source I] using rd8285raw
  have rd8288pre := evm_run rd8285 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (relyAuthWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hauth hbad.symm)
  rw [heq] at rd8288pre
  have rd8291 := rd8288pre.pushConst (⟨8357⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd8292 := rd8291.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨8292⟩)
    (len := ⟨18⟩)
    (rawWord := ⟨0x115b990bdb9bdd0b585d5d1a1bdc9a5e9959⟩)
    (shift := ⟨114⟩)
    (word := ⟨0x456e642f6e6f742d617574686f72697a65640000000000000000000000000000⟩)
    (op := .PUSH18)
    (width := 18)
    rd8292
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    relyNotAuthorizedWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

set_option maxHeartbeats 1000000 in
theorem endFileAddressX_live {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : fileAddressLiveWord σ I = ⟨1⟩)
    (h : RD endBytecode I g s0 ⟨8357⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨8427⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd8361pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k8361, C8361, rd8361raw⟩ := rd8361pre.sload (by native_decide) (by evm_ov)
  have rd8361 : RD endBytecode I g s0 ⟨8361⟩
      (fileAddressLiveWord σ I :: fileAddressDataKey I :: calldataWord I.calldata 4 ::
        ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k8361 C8361 := by
    simpa [fileAddressLiveWord, endSlotWord] using rd8361raw
  have rd8364pre := evm_run rd8361 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  rw [hlive, u256_eq_refl] at rd8364pre
  have rd8367 := rd8364pre.pushConst (⟨8427⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  exact ⟨_, _, rd8367.jumpiT (by native_decide) one_ne_zero_uint
    (by jump_dest) (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem endFileAddressX_notLive {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hlive : fileAddressLiveWord σ I ≠ ⟨1⟩)
    (h : RD endBytecode I g s0 ⟨8357⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDrev endBytecode g s0 := by
  have rd8361pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨8⟩ (by native_decide) (by evm_ov)]
  obtain ⟨k8361, C8361, rd8361raw⟩ := rd8361pre.sload (by native_decide) (by evm_ov)
  have rd8361 : RD endBytecode I g s0 ⟨8361⟩
      (fileAddressLiveWord σ I :: fileAddressDataKey I :: calldataWord I.calldata 4 ::
        ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k8361 C8361 := by
    simpa [fileAddressLiveWord, endSlotWord] using rd8361raw
  have rd8364pre := evm_run rd8361 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have heq : UInt256.eq (⟨1⟩ : UInt256) (fileAddressLiveWord σ I) = ⟨0⟩ := by
    exact u256_eq_of_ne (by intro hbad; exact hlive hbad.symm)
  rw [heq] at rd8364pre
  have rd8367 := rd8364pre.pushConst (⟨8427⟩ : UInt256)
    (width := 2) (op := .PUSH2) (by decide) (by native_decide) (by evm_ov)
  have rd8368 := rd8367.jumpiNT (by native_decide) rfl (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨8368⟩)
    (len := ⟨12⟩)
    (rawWord := ⟨0x456e642f6e6f742d6c697665⟩)
    (shift := ⟨160⟩)
    (word := ⟨0x456e642f6e6f742d6c6976650000000000000000000000000000000000000000⟩)
    (op := .PUSH12)
    (width := 12)
    rd8368
    (by
      unfold solcErrorStringRevertTailWf
      repeat' first | apply And.intro | native_decide)
    (by decide)
    fileUintNotLiveWord
    (relyAuthHashMem_size I)
    (relyAuthHashMem_read64 I)
    (by simp only [List.length_cons, List.length_nil]; omega)

noncomputable def fileAddressLogDataMem (I : ExecutionEnv) : ByteArray :=
  (fileAddressDataKey I).toByteArray.write 0 (relyAuthHashMem I) 128 32

theorem fileAddressLogDataMem_size (I : ExecutionEnv) :
    (fileAddressLogDataMem I).size = 160 := by
  unfold fileAddressLogDataMem
  exact toByteArray_write32_size_of_ge (relyAuthHashMem I) (fileAddressDataKey I) 128 96 160
    (relyAuthHashMem_size I) (by omega)
    (by native_decide)
    (by omega)

theorem fileAddressLogDataMem_read64 (I : ExecutionEnv) :
    (fileAddressLogDataMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold fileAddressLogDataMem
  rw [toByteArray_write_read_below_of_gap (fileAddressDataKey I) (relyAuthHashMem I) 128 64
    (by rw [relyAuthHashMem_size I]) (by omega)
    (by rw [relyAuthHashMem_size I]; exact lt_usize _ (by norm_num))]
  exact relyAuthHashMem_read64 I

theorem endFileAddressX_logReturn {I} {g : Sat256} {s0 : State} {k C : ℕ}
    {what sel : UInt256} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hperm : I.perm = true)
    (h : RD endBytecode I g s0 ⟨8747⟩
      [fileAddressDataKey I, what, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty acc k C) :
    RDret endBytecode g s0 acc ByteArray.empty := by
  have rd8751pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  have rd8752 := rd8751pre.mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
    mem_cost
    (mloadFreePtrValue (by rw [relyAuthHashMem_size I]; decide) (by decide)
      (relyAuthHashMem_read64 I))
    (by native_decide) (by evm_ov)
  have rd8762pre := evm_run rd8752 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8763 := rd8762pre.mstore 6 (fileAddressLogDataMem I)
    (UInt256.ofNat 5) (by native_decide) mem_cost (by
      have hclean : UInt256.land (fileAddressDataKey I) solcAddrMask = fileAddressDataKey I := by
        exact solcAddrMask_clean (by
          simpa [fileAddressDataKey, fileAddressDataWord,
            u256_land_comm solcAddrMask (fileAddressDataWord I)] using
            solcAddrMask_result_canonical (fileAddressDataWord I))
      simp [fileAddressLogDataMem, hclean,
        show (⟨128⟩ : UInt256).toNat = 128 from by decide,
        show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide])
    (by native_decide) (by evm_ov)
  have rd8768pre := evm_run rd8763 with [
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 5) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [fileAddressLogDataMem_size I]; decide) (by decide)
        (fileAddressLogDataMem_read64 I))
      (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw swap2 (by native_decide) (by evm_ov)]
  have rd8801 := rd8768pre.pushConst
    (⟨0x8fef588b5fc1afbf5b2f06c1a435d513f208da2e6704c3d8f0e0ec91167066ba⟩ :
      UInt256)
    (width := 32) (op := .PUSH32) (by decide) (by native_decide) (by evm_ov)
  have rd8809pre := evm_run rd8801 with [
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
    (t := [fileAddressDataKey I, what, ⟨562⟩, sel])
    0
    (UInt256.ofNat
      (MachineState.M (UInt256.ofNat 5).toNat (⟨128⟩ : UInt256).toNat
        (⟨32⟩ : UInt256).toNat))
    rd8809pre (by native_decide) hperm mem_cost (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd8811 := RD.pop (a := fileAddressDataKey I) (t := [what, ⟨562⟩, sel])
    rd8811 (by native_decide) (by evm_ov)
  have rd8812 := RD.pop (a := what) (t := [⟨562⟩, sel])
    rd8811 (by native_decide) (by evm_ov)
  have rd562 := RD.jump (a := ⟨562⟩) (t := [sel]) rd8812
    (by native_decide) (by jump_dest) (by evm_ov)
  have rd563 := RD.jumpdest (pc := ⟨562⟩) (stk := [sel]) rd562
    (by native_decide) (by evm_ov)
  exact RD.stop rd563 (by native_decide) (by evm_ov)

set_option maxHeartbeats 3000000 in
theorem endFileAddressX_vat_ok {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hwhatWord : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressVatBytes)
    (h : RD endBytecode I g s0 ⟨8427⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (setAddressOffset0Word (endSlotWord ⟨1⟩ σ I) (fileAddressDataKey I)))
      ByteArray.empty := by
  have rd8429pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8433 := rd8429pre.pushConst (⟨0x1d985d⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd8438pre := evm_run rd8433 with [
    raw push1 ⟨234⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  have hvatWord :
      ABI.bytesToWord fileAddressVatBytes =
        UInt256.shiftLeft (⟨0x1d985d⟩ : UInt256) ⟨234⟩ :=
    fileAddressConstWords.1
  rw [hwhatWord, hvatWord, u256_eq_refl] at rd8438pre
  have rd8442pre := evm_run rd8438pre with [
    raw push2 ⟨8473⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  have rd8445pre := evm_run rd8442pre with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k8446, C8446, rd8446raw⟩ := rd8445pre.sload (by native_decide) (by evm_ov)
  have rd8446 : RD endBytecode I g s0 ⟨8446⟩
      (endSlotWord ⟨1⟩ σ I :: ⟨1⟩ :: fileAddressDataKey I ::
        UInt256.shiftLeft (⟨0x1d985d⟩ : UInt256) ⟨234⟩ :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k8446 C8446 := by
    simpa [endSlotWord] using rd8446raw
  have rd8468pre := evm_run rd8446 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hstoreWord :
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨1⟩ σ I)) =
        setAddressOffset0Word (endSlotWord ⟨1⟩ σ I) (fileAddressDataKey I) := by
    calc
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨1⟩ σ I)) =
          UInt256.lor (UInt256.land (endSlotWord ⟨1⟩ σ I) (UInt256.lnot solcAddrMask))
            (UInt256.land (fileAddressDataKey I) solcAddrMask) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (endSlotWord ⟨1⟩ σ I)]
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (endSlotWord ⟨1⟩ σ I) (fileAddressDataKey I) := by
            rfl
  obtain ⟨k8469, C8469, rd8469raw⟩ := rd8468pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hpc8469 :
      (⟨8446⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨8469⟩ := by
    native_decide
  rw [hpc8469] at rd8469raw
  simp only [
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd8469raw
  rw [hstoreWord] at rd8469raw
  have rd8469 : RD endBytecode I g s0 ⟨8469⟩
      [fileAddressDataKey I, UInt256.shiftLeft (⟨0x1d985d⟩ : UInt256) ⟨234⟩, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨1⟩
        (setAddressOffset0Word (endSlotWord ⟨1⟩ σ I) (fileAddressDataKey I))) k8469 C8469 := by
    simpa [endSlotWord,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd8469raw
  have rd8747 := evm_run rd8469 with [
    raw push2 ⟨8747⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact endFileAddressX_logReturn hperm rd8747

set_option maxHeartbeats 1000000 in
theorem endFileAddressX_skip_vat {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hnotVatWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressVatBytes)
    (h : RD endBytecode I g s0 ⟨8427⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨8473⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd8429pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8433 := rd8429pre.pushConst (⟨0x1d985d⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd8437pre := evm_run rd8433 with [
    raw push1 ⟨234⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have hvatWord :
      ABI.bytesToWord fileAddressVatBytes =
        UInt256.shiftLeft (⟨0x1d985d⟩ : UInt256) ⟨234⟩ :=
    fileAddressConstWords.1
  have hvatEq :
      UInt256.eq
          (UInt256.shiftLeft (⟨0x1d985d⟩ : UInt256) ⟨234⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← hvatWord]
    exact u256_eq_of_ne (by intro hbad; exact hnotVatWord hbad.symm)
  rw [hvatEq] at rd8437pre
  have rd8473 := evm_run rd8437pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨8473⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd8473⟩

set_option maxHeartbeats 3000000 in
theorem endFileAddressX_cat_ok {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hwhatWord : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressCatBytes)
    (h : RD endBytecode I g s0 ⟨8473⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (setAddressOffset0Word (endSlotWord ⟨2⟩ σ I) (fileAddressDataKey I)))
      ByteArray.empty := by
  have rd8475pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8479 := rd8475pre.pushConst (⟨0x18d85d⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd8484pre := evm_run rd8479 with [
    raw push1 ⟨234⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  have hcatWord :
      ABI.bytesToWord fileAddressCatBytes =
        UInt256.shiftLeft (⟨0x18d85d⟩ : UInt256) ⟨234⟩ :=
    fileAddressConstWords.2.1
  rw [hwhatWord, hcatWord, u256_eq_refl] at rd8484pre
  have rd8488pre := evm_run rd8484pre with [
    raw push2 ⟨8519⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  have rd8491pre := evm_run rd8488pre with [
    raw push1 ⟨2⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k8492, C8492, rd8492raw⟩ := rd8491pre.sload (by native_decide) (by evm_ov)
  have rd8492 : RD endBytecode I g s0 ⟨8492⟩
      (endSlotWord ⟨2⟩ σ I :: ⟨2⟩ :: fileAddressDataKey I ::
        UInt256.shiftLeft (⟨0x18d85d⟩ : UInt256) ⟨234⟩ :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k8492 C8492 := by
    simpa [endSlotWord] using rd8492raw
  have rd8514pre := evm_run rd8492 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hstoreWord :
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨2⟩ σ I)) =
        setAddressOffset0Word (endSlotWord ⟨2⟩ σ I) (fileAddressDataKey I) := by
    calc
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨2⟩ σ I)) =
          UInt256.lor (UInt256.land (endSlotWord ⟨2⟩ σ I) (UInt256.lnot solcAddrMask))
            (UInt256.land (fileAddressDataKey I) solcAddrMask) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (endSlotWord ⟨2⟩ σ I)]
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (endSlotWord ⟨2⟩ σ I) (fileAddressDataKey I) := by
            rfl
  obtain ⟨k8515, C8515, rd8515raw⟩ := rd8514pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hpc8515 :
      (⟨8492⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨8515⟩ := by
    native_decide
  rw [hpc8515] at rd8515raw
  simp only [
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd8515raw
  rw [hstoreWord] at rd8515raw
  have rd8515 : RD endBytecode I g s0 ⟨8515⟩
      [fileAddressDataKey I, UInt256.shiftLeft (⟨0x18d85d⟩ : UInt256) ⟨234⟩, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (setAddressOffset0Word (endSlotWord ⟨2⟩ σ I) (fileAddressDataKey I))) k8515 C8515 := by
    simpa [endSlotWord] using rd8515raw
  have rd8747 := evm_run rd8515 with [
    raw push2 ⟨8747⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact endFileAddressX_logReturn hperm rd8747

set_option maxHeartbeats 1000000 in
theorem endFileAddressX_skip_cat {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hnotCatWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressCatBytes)
    (h : RD endBytecode I g s0 ⟨8473⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨8519⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd8475pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8479 := rd8475pre.pushConst (⟨0x18d85d⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd8483pre := evm_run rd8479 with [
    raw push1 ⟨234⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have hcatWord :
      ABI.bytesToWord fileAddressCatBytes =
        UInt256.shiftLeft (⟨0x18d85d⟩ : UInt256) ⟨234⟩ :=
    fileAddressConstWords.2.1
  have hcatEq :
      UInt256.eq
          (UInt256.shiftLeft (⟨0x18d85d⟩ : UInt256) ⟨234⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← hcatWord]
    exact u256_eq_of_ne (by intro hbad; exact hnotCatWord hbad.symm)
  rw [hcatEq] at rd8483pre
  have rd8519 := evm_run rd8483pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨8519⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd8519⟩

set_option maxHeartbeats 3000000 in
theorem endFileAddressX_dog_ok {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hwhatWord : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressDogBytes)
    (h : RD endBytecode I g s0 ⟨8519⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩
        (setAddressOffset0Word (endSlotWord ⟨3⟩ σ I) (fileAddressDataKey I)))
      ByteArray.empty := by
  have rd8521pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8525 := rd8521pre.pushConst (⟨0x646f67⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd8530pre := evm_run rd8525 with [
    raw push1 ⟨232⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  have hdogWord :
      ABI.bytesToWord fileAddressDogBytes =
        UInt256.shiftLeft (⟨0x646f67⟩ : UInt256) ⟨232⟩ :=
    fileAddressConstWords.2.2.1
  rw [hwhatWord, hdogWord, u256_eq_refl] at rd8530pre
  have rd8534pre := evm_run rd8530pre with [
    raw push2 ⟨8565⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  have rd8537pre := evm_run rd8534pre with [
    raw push1 ⟨3⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k8538, C8538, rd8538raw⟩ := rd8537pre.sload (by native_decide) (by evm_ov)
  have rd8538 : RD endBytecode I g s0 ⟨8538⟩
      (endSlotWord ⟨3⟩ σ I :: ⟨3⟩ :: fileAddressDataKey I ::
        UInt256.shiftLeft (⟨0x646f67⟩ : UInt256) ⟨232⟩ :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k8538 C8538 := by
    simpa [endSlotWord] using rd8538raw
  have rd8560pre := evm_run rd8538 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hstoreWord :
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨3⟩ σ I)) =
        setAddressOffset0Word (endSlotWord ⟨3⟩ σ I) (fileAddressDataKey I) := by
    calc
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨3⟩ σ I)) =
          UInt256.lor (UInt256.land (endSlotWord ⟨3⟩ σ I) (UInt256.lnot solcAddrMask))
            (UInt256.land (fileAddressDataKey I) solcAddrMask) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (endSlotWord ⟨3⟩ σ I)]
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (endSlotWord ⟨3⟩ σ I) (fileAddressDataKey I) := by
            rfl
  obtain ⟨k8561, C8561, rd8561raw⟩ := rd8560pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hpc8561 :
      (⟨8538⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨8561⟩ := by
    native_decide
  rw [hpc8561] at rd8561raw
  simp only [
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd8561raw
  rw [hstoreWord] at rd8561raw
  have rd8561 : RD endBytecode I g s0 ⟨8561⟩
      [fileAddressDataKey I, UInt256.shiftLeft (⟨0x646f67⟩ : UInt256) ⟨232⟩, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩
        (setAddressOffset0Word (endSlotWord ⟨3⟩ σ I) (fileAddressDataKey I))) k8561 C8561 := by
    simpa [endSlotWord] using rd8561raw
  have rd8747 := evm_run rd8561 with [
    raw push2 ⟨8747⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact endFileAddressX_logReturn hperm rd8747

set_option maxHeartbeats 1000000 in
theorem endFileAddressX_skip_dog {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hnotDogWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressDogBytes)
    (h : RD endBytecode I g s0 ⟨8519⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨8565⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd8521pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8525 := rd8521pre.pushConst (⟨0x646f67⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd8529pre := evm_run rd8525 with [
    raw push1 ⟨232⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have hdogWord :
      ABI.bytesToWord fileAddressDogBytes =
        UInt256.shiftLeft (⟨0x646f67⟩ : UInt256) ⟨232⟩ :=
    fileAddressConstWords.2.2.1
  have hdogEq :
      UInt256.eq
          (UInt256.shiftLeft (⟨0x646f67⟩ : UInt256) ⟨232⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← hdogWord]
    exact u256_eq_of_ne (by intro hbad; exact hnotDogWord hbad.symm)
  rw [hdogEq] at rd8529pre
  have rd8565 := evm_run rd8529pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨8565⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd8565⟩

set_option maxHeartbeats 3000000 in
theorem endFileAddressX_vow_ok {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hwhatWord : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressVowBytes)
    (h : RD endBytecode I g s0 ⟨8565⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨4⟩
        (setAddressOffset0Word (endSlotWord ⟨4⟩ σ I) (fileAddressDataKey I)))
      ByteArray.empty := by
  have rd8567pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8571 := rd8567pre.pushConst (⟨0x766f77⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd8576pre := evm_run rd8571 with [
    raw push1 ⟨232⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  have hvowWord :
      ABI.bytesToWord fileAddressVowBytes =
        UInt256.shiftLeft (⟨0x766f77⟩ : UInt256) ⟨232⟩ :=
    fileAddressConstWords.2.2.2.1
  rw [hwhatWord, hvowWord, u256_eq_refl] at rd8576pre
  have rd8580pre := evm_run rd8576pre with [
    raw push2 ⟨8611⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  have rd8583pre := evm_run rd8580pre with [
    raw push1 ⟨4⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k8584, C8584, rd8584raw⟩ := rd8583pre.sload (by native_decide) (by evm_ov)
  have rd8584 : RD endBytecode I g s0 ⟨8584⟩
      (endSlotWord ⟨4⟩ σ I :: ⟨4⟩ :: fileAddressDataKey I ::
        UInt256.shiftLeft (⟨0x766f77⟩ : UInt256) ⟨232⟩ :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k8584 C8584 := by
    simpa [endSlotWord] using rd8584raw
  have rd8606pre := evm_run rd8584 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hstoreWord :
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨4⟩ σ I)) =
        setAddressOffset0Word (endSlotWord ⟨4⟩ σ I) (fileAddressDataKey I) := by
    calc
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨4⟩ σ I)) =
          UInt256.lor (UInt256.land (endSlotWord ⟨4⟩ σ I) (UInt256.lnot solcAddrMask))
            (UInt256.land (fileAddressDataKey I) solcAddrMask) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (endSlotWord ⟨4⟩ σ I)]
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (endSlotWord ⟨4⟩ σ I) (fileAddressDataKey I) := by
            rfl
  obtain ⟨k8607, C8607, rd8607raw⟩ := rd8606pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hpc8607 :
      (⟨8584⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨8607⟩ := by
    native_decide
  rw [hpc8607] at rd8607raw
  simp only [
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd8607raw
  rw [hstoreWord] at rd8607raw
  have rd8607 : RD endBytecode I g s0 ⟨8607⟩
      [fileAddressDataKey I, UInt256.shiftLeft (⟨0x766f77⟩ : UInt256) ⟨232⟩, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨4⟩
        (setAddressOffset0Word (endSlotWord ⟨4⟩ σ I) (fileAddressDataKey I))) k8607 C8607 := by
    simpa [endSlotWord] using rd8607raw
  have rd8747 := evm_run rd8607 with [
    raw push2 ⟨8747⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact endFileAddressX_logReturn hperm rd8747

set_option maxHeartbeats 1000000 in
theorem endFileAddressX_skip_vow {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hnotVowWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressVowBytes)
    (h : RD endBytecode I g s0 ⟨8565⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨8611⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd8567pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8571 := rd8567pre.pushConst (⟨0x766f77⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd8575pre := evm_run rd8571 with [
    raw push1 ⟨232⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have hvowWord :
      ABI.bytesToWord fileAddressVowBytes =
        UInt256.shiftLeft (⟨0x766f77⟩ : UInt256) ⟨232⟩ :=
    fileAddressConstWords.2.2.2.1
  have hvowEq :
      UInt256.eq
          (UInt256.shiftLeft (⟨0x766f77⟩ : UInt256) ⟨232⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← hvowWord]
    exact u256_eq_of_ne (by intro hbad; exact hnotVowWord hbad.symm)
  rw [hvowEq] at rd8575pre
  have rd8611 := evm_run rd8575pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨8611⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd8611⟩

set_option maxHeartbeats 3000000 in
theorem endFileAddressX_pot_ok {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256} (hperm : I.perm = true)
    (hwhatWord : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressPotBytes)
    (h : RD endBytecode I g s0 ⟨8611⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    RDret endBytecode g s0
      (cA, sstoreAccountMap I.codeOwner σ ⟨5⟩
        (setAddressOffset0Word (endSlotWord ⟨5⟩ σ I) (fileAddressDataKey I)))
      ByteArray.empty := by
  have rd8613pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8617 := rd8613pre.pushConst (⟨0x1c1bdd⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd8622pre := evm_run rd8617 with [
    raw push1 ⟨234⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov),
    raw iszero (by native_decide) (by evm_ov)]
  have hpotWord :
      ABI.bytesToWord fileAddressPotBytes =
        UInt256.shiftLeft (⟨0x1c1bdd⟩ : UInt256) ⟨234⟩ :=
    fileAddressConstWords.2.2.2.2.1
  rw [hwhatWord, hpotWord, u256_eq_refl] at rd8622pre
  have rd8626pre := evm_run rd8622pre with [
    raw push2 ⟨8657⟩ (by native_decide) (by evm_ov),
    raw jumpiNT (by native_decide) rfl (by evm_ov)]
  have rd8629pre := evm_run rd8626pre with [
    raw push1 ⟨5⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov)]
  obtain ⟨k8630, C8630, rd8630raw⟩ := rd8629pre.sload (by native_decide) (by evm_ov)
  have rd8630 : RD endBytecode I g s0 ⟨8630⟩
      (endSlotWord ⟨5⟩ σ I :: ⟨5⟩ :: fileAddressDataKey I ::
        UInt256.shiftLeft (⟨0x1c1bdd⟩ : UInt256) ⟨234⟩ :: ⟨562⟩ :: [sel])
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k8630 C8630 := by
    simpa [endSlotWord] using rd8630raw
  have rd8652pre := evm_run rd8630 with [
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw not (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw dup4 (by native_decide) (by evm_ov),
    raw and (by native_decide) (by evm_ov),
    raw lor (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov)]
  have hstoreWord :
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨5⟩ σ I)) =
        setAddressOffset0Word (endSlotWord ⟨5⟩ σ I) (fileAddressDataKey I) := by
    calc
      UInt256.lor (UInt256.land (fileAddressDataKey I) solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (endSlotWord ⟨5⟩ σ I)) =
          UInt256.lor (UInt256.land (endSlotWord ⟨5⟩ σ I) (UInt256.lnot solcAddrMask))
            (UInt256.land (fileAddressDataKey I) solcAddrMask) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (endSlotWord ⟨5⟩ σ I)]
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (endSlotWord ⟨5⟩ σ I) (fileAddressDataKey I) := by
            rfl
  obtain ⟨k8653, C8653, rd8653raw⟩ := rd8652pre.sstore hperm (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have hpc8653 :
      (⟨8630⟩ : UInt256) + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 +
          UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ =
        ⟨8653⟩ := by
    native_decide
  rw [hpc8653] at rd8653raw
  simp only [
    show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
      solcAddrMask from by decide] at rd8653raw
  rw [hstoreWord] at rd8653raw
  have rd8653 : RD endBytecode I g s0 ⟨8653⟩
      [fileAddressDataKey I, UInt256.shiftLeft (⟨0x1c1bdd⟩ : UInt256) ⟨234⟩, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty
      (cA, sstoreAccountMap I.codeOwner σ ⟨5⟩
        (setAddressOffset0Word (endSlotWord ⟨5⟩ σ I) (fileAddressDataKey I))) k8653 C8653 := by
    simpa [endSlotWord] using rd8653raw
  have rd8747 := evm_run rd8653 with [
    raw push2 ⟨8747⟩ (by native_decide) (by evm_ov),
    raw jump (by native_decide) (by jump_dest) (by evm_ov)]
  exact endFileAddressX_logReturn hperm rd8747

set_option maxHeartbeats 1000000 in
theorem endFileAddressX_skip_pot {cA σ I} {g : Sat256} {s0 : State} {k C : ℕ}
    {sel : UInt256}
    (hnotPotWord : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressPotBytes)
    (h : RD endBytecode I g s0 ⟨8611⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C) :
    ∃ k' C', RD endBytecode I g s0 ⟨8657⟩
      [fileAddressDataKey I, calldataWord I.calldata 4, ⟨562⟩, sel]
      (relyAuthHashMem I) (UInt256.ofNat 3) ByteArray.empty (cA, σ) k' C' := by
  have rd8613pre := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov)]
  have rd8617 := rd8613pre.pushConst (⟨0x1c1bdd⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd8621pre := evm_run rd8617 with [
    raw push1 ⟨234⟩ (by native_decide) (by evm_ov),
    raw shl (by native_decide) (by evm_ov),
    raw eq (by native_decide) (by evm_ov)]
  have hpotWord :
      ABI.bytesToWord fileAddressPotBytes =
        UInt256.shiftLeft (⟨0x1c1bdd⟩ : UInt256) ⟨234⟩ :=
    fileAddressConstWords.2.2.2.2.1
  have hpotEq :
      UInt256.eq
          (UInt256.shiftLeft (⟨0x1c1bdd⟩ : UInt256) ⟨234⟩)
          (calldataWord I.calldata 4) = ⟨0⟩ := by
    rw [← hpotWord]
    exact u256_eq_of_ne (by intro hbad; exact hnotPotWord hbad.symm)
  rw [hpotEq] at rd8621pre
  have rd8657 := evm_run rd8621pre with [
    raw iszero (by native_decide) (by evm_ov),
    raw push2 ⟨8657⟩ (by native_decide) (by evm_ov),
    raw jumpiT (by native_decide) one_ne_zero_uint (by jump_dest) (by evm_ov)]
  exact ⟨_, _, rd8657⟩

end Benchmarks.Dss.End
