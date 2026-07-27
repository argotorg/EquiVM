import Benchmarks.Dss.Dog.Dispatch
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement
open Benchmarks.Dss.Dog.Immutables

set_option maxHeartbeats 0

namespace Benchmarks.Dss.Dog

/-! ## `file(bytes32,address)` -/

abbrev fileAddressWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileAddressData (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 36).toNat

abbrev fileAddressDataWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileAddressDataKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (fileAddressDataWord I)

abbrev fileAddressVowBytes : List UInt8 :=
  [118, 111, 119] ++ List.replicate 29 0

abbrev fileAddressLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileAddressWhat I))).insert
    "data" (.address (fileAddressData I))

abbrev dogFileAddressLogTopic : UInt256 :=
  ⟨65103624907084577414431664178121565314709747119730508611619433015502684841658⟩

theorem fileAddressVowBytes_length : fileAddressVowBytes.length = 32 := by
  native_decide

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
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
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

theorem fileAddressData_value_masked (I : ExecutionEnv) :
    (.address (fileAddressData I) : Value) =
      .address (AccountAddress.ofNat (fileAddressDataKey I).toNat) := by
  simpa [fileAddressData, fileAddressDataKey, fileAddressDataWord] using
    (solcAddressValue_masked (calldataWord I.calldata 36))

theorem fileAddressDataKey_canonical (I : ExecutionEnv) :
    (fileAddressDataKey I).toNat < EVM.addressModulus := by
  rw [fileAddressDataKey, u256_land_comm solcAddrMask (fileAddressDataWord I)]
  exact solcAddrMask_result_canonical (fileAddressDataWord I)

theorem dogDecode_fileAddress_ok {v : DogImmutables} {I : ExecutionEnv}
    (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata =
        some (fileAddressLocals I) := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr, fileAddressWhat,
    fileAddressData, fileAddressLocals, abiBytes32, abiBytes32Width, abiAddress] using
    (dogDecodeCalldataWithMode_legacyBytes32_address_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem dogDecode_fileAddress_none_short {v : DogImmutables} {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode (config v).abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata = none := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (dogDecodeCalldataWithMode_legacyBytes32_address_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem fileAddressLocals_get_what (I : ExecutionEnv) :
    (fileAddressLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileAddressWhat I)) := by
  rw [fileAddressLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileAddressLocals_get_data (I : ExecutionEnv) :
    (fileAddressLocals I).get? "data" =
      some (.address (fileAddressData I)) := by
  rw [fileAddressLocals, store_get_self]

theorem fileAddressLocals_get_vow (I : ExecutionEnv) :
    (fileAddressLocals I).get? "vow" = none := by
  rw [fileAddressLocals, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem evalExpr_fileAddressWhatEq_true {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileAddressWhat I)))
    (hwhat : fileAddressWhat I = bs) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "what") =
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

theorem evalExpr_fileAddressWhatEq_false {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store} {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileAddressWhat I)))
    (hwhat : fileAddressWhat I ≠ bs) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "what") =
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

theorem evalExpr_fileAddressData {v : DogImmutables} {evm : EVM.State}
    {I : ExecutionEnv} {locals : Store}
    (hget : locals.get? "data" = some (.address (fileAddressData I))) :
    evalExpr? (config v) { contract := contract v, locals := locals } evm (.var "data") =
      .ok (.address (fileAddressData I)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.address (fileAddressData I))
  rw [hget]
  rfl

theorem assign_fileAddressVowStorage (v : DogImmutables) (evm : EVM.State)
    {locals : Store} (data : UInt256) (hbase : locals.get? "vow" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
        (UInt256.land solcAddrMask data))
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage vowRef (.address (AccountAddress.ofNat data.toNat)) =
        .ok ({ contract := contract v, locals := locals }, evm') := by
  intro evm'
  have hvalue :
      (.address (AccountAddress.ofNat data.toNat) : Value) =
        .address (AccountAddress.ofNat (UInt256.land solcAddrMask data).toNat) := by
    simpa using (solcAddressValue_masked data)
  rw [hvalue]
  have her :
      evalStorageRef (config v) { contract := contract v, locals := locals } evm vowRef =
        .ok { base := "vow", steps := [] } := by
    simp [vowRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (addrLoc ⟨2⟩)
          (.address (AccountAddress.ofNat (UInt256.land solcAddrMask data).toNat)) =
        some evm' := by
    simpa [addrLoc, evm'] using
      storageLocStore_address_offset0 evm ⟨2⟩ (UInt256.land solcAddrMask data) (by
        rw [u256_land_comm solcAddrMask data]
        exact solcAddrMask_result_canonical data)
  exact assignStorageRef_storage_scalar_value
    (ty := .elem .address) (loc := addrLoc ⟨2⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hscalar := by trivial)
    (hstore := hstore)

theorem fileAddressVowSourceBody {v : DogImmutables} {cA gh bl σ σ₀ A I}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressVowBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨2⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm0 I.codeOwner ⟨2⟩)
        (fileAddressDataKey I))
    ExecTransitionBody (config v) (contract v) evm0 locals fileAddressTransition.body
      (.returned { contract := contract v, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileAddressLocals]) hauth
  have hcond :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.var "what") vowParamLit) = .ok (.bool true) := by
    simpa [vowParamLit, fileAddressVowBytes] using
      (evalExpr_fileAddressWhatEq_true (v := v) (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVowBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0 (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [locals] using
      (evalExpr_fileAddressData (v := v) (evm := evm0) (I := I) (locals := locals)
        (by simp [locals, fileAddressLocals]))
  have hassign :
      assignStorageRef? (config v) { contract := contract v, locals := locals } evm0
        .storage vowRef (.address (fileAddressData I)) =
          .ok ({ contract := contract v, locals := locals }, evm1) := by
    simpa [evm1, fileAddressData, fileAddressDataKey, fileAddressDataWord] using
      (assign_fileAddressVowStorage v evm0 (locals := locals) (fileAddressDataWord I)
        (by simpa [locals] using fileAddressLocals_get_vow I))
  have hthen :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [.assign .storage vowRef (.var "data")]
        (.ok { contract := contract v, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileAddressTransition.body (.ok { contract := contract v, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals] using ExecFuncBody.execBlockOK hblock

theorem fileAddressUnrecognizedSourceBody {v : DogImmutables} {cA gh bl σ σ₀ A I}
    {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : dogSlotWord (dogCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotVow : fileAddressWhat I ≠ fileAddressVowBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody (config v) (contract v) evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguard := dogAuthGuardEval_true (v := v) (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileAddressLocals]) hauth
  have hcond :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.binary .eq (.var "what") vowParamLit) = .ok (.bool false) := by
    simpa [vowParamLit, fileAddressVowBytes] using
      (evalExpr_fileAddressWhatEq_false (v := v) (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVowBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVow)
  have hreqFalse :
      evalExpr? (config v) { contract := contract v, locals := locals } evm0
        (.boolLit false) = .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        [.require (.boolLit false)] .reverted := by
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)
  have hblock :
      ExecBlock (config v) { contract := contract v, locals := locals } evm0
        fileAddressTransition.body .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond helse)
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

theorem dogReachFileAddressBody {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (dogSelBytes 9)) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨585⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  have hword : solcSelectorWord I = ⟨0xd4e8be83⟩ :=
    solcSelectorWord_eq_of_beq I hsz 0xd4 0xe8 0xbe 0x83 ⟨0xd4e8be83⟩
      (by native_decide) (by simpa [dogSelBytes] using hsel)
  obtain ⟨k32, C32, h32⟩ :=
    dogReachSelector (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hrootWidth : armTgtWidth code (⟨32⟩ : UInt256) = 2 := by
    dsimp [armTgtWidth]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hhighTgt : armTgt code (⟨43⟩ : UInt256) = ⟨113⟩ := by
    dsimp [armTgt]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPushTgtPc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have hroot :
      UInt256.gt (armSelNat code (⟨32⟩ : UInt256)) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨32⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h43 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨43⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5) (C32 + 22) := by
    simpa [selArmNextPc, hrootWidth] using
      RD.selectorSplitNotTakenAuto h32 (dogRootSplitWellFormed hpatch) hroot (by simp)
  have hhigh :
      UInt256.gt (armSelNat code (⟨43⟩ : UInt256)) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    dsimp [armSelNat]
    rw [dogPushAtPatchedEqTemplate1405 (pc := selArmPush4Pc (⟨43⟩ : UInt256))
      hpatch (by native_decide)]
    native_decide
  have h113 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨113⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5) (C32 + 22 + 22) := by
    simpa [hhighTgt] using
      RD.selectorSplitTakenAuto h43 (dogHighSplitWellFormed hpatch) hhigh
        (by
          rw [hhighTgt]
          exact dogPatchedDJumpPrefix1405 ⟨113⟩ hpatch (by native_decide))
        (by simp)
  have h114 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨114⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5 + 1) (C32 + 22 + 22 + 1) := by
    simpa using
      h113.jumpdest
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by simp only [List.length_singleton]; omega)
  have hhole : UInt256.eq (dogSelectorWord 1) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hwards : UInt256.eq (dogSelectorWord 16) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hdigs : UInt256.eq (dogSelectorWord 6) (solcSelectorWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hfileAddress : UInt256.eq (dogSelectorWord 9) (solcSelectorWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have h125 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨125⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5 + 1 + 5) (C32 + 22 + 22 + 1 + 22) := by
    simpa [selArmNextPc] using
      h114.selectorArmNotTaken (selNat := dogSelectorWord 1) (tgt := (⟨504⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hhole
        (by simp)
  have h136 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨136⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5 + 1 + 5 + 5) (C32 + 22 + 22 + 1 + 22 + 22) := by
    simpa [selArmNextPc] using
      h125.selectorArmNotTaken (selNat := dogSelectorWord 16) (tgt := (⟨512⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hwards
        (by simp)
  have h147 : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨147⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) (k32 + 5 + 5 + 1 + 5 + 5 + 5) (C32 + 22 + 22 + 1 + 22 + 22 + 22) := by
    simpa [selArmNextPc] using
      h136.selectorArmNotTaken (selNat := dogSelectorWord 6) (tgt := (⟨550⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hdigs
        (by simp)
  have h585 := by
    simpa using
      h147.selectorArmTaken (selNat := dogSelectorWord 9) (tgt := (⟨585⟩ : UInt256))
        (width := 2) (op := .PUSH2)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        (by
          rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
        hfileAddress
        (dogPatchedDJumpPrefix1405 ⟨585⟩ hpatch (by native_decide))
        (by simp)
  exact ⟨_, _, h585⟩

theorem RD.dogFileAddressDecodeToRoutine {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {ret de sel : UInt256} {R : List UInt256} {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨607⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hroutine : (D_J code 0).contains ⟨2146⟩ = true)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨2146⟩
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  have rd608 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd609 := rd608.pop
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd610 := rd609.dup1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd611 := rd610.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd612 := rd611.swap1
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd614 := rd612.push1 ⟨32⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd615 := rd614.add
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd616 := rd615.calldataload
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd618 := rd616.push1 ⟨1⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd620 := rd618.push1 ⟨1⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd622 := rd620.push1 ⟨160⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd623 := rd622.shl
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd624 := rd623.sub
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd625 := rd624.and
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  have rd628 := rd625.push2 ⟨2146⟩
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (UInt256.add (⟨32⟩ : UInt256) ⟨4⟩).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd628.jump
        (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
        hroutine (by evm_ov)⟩

theorem RD.dogFileAddressToSwitch {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨585⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2235⟩
      (fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨313⟩ :: sel :: [])
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := code) (sel := sel) (entry := ⟨585⟩) (ret := ⟨313⟩)
    (decoded := ⟨607⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedDJumpPrefix1405 ⟨607⟩ hpatch (by native_decide)) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.dogFileAddressDecodeToRoutine
    (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hdecoded (dogPatchedJumpDest hpatch (by native_decide))
    (by simp)
  obtain ⟨_, _, hafterAuth⟩ := RD.dogAuthCheckOk
    (code := code) (pc := ⟨2146⟩) (okPc := ⟨2235⟩)
    (key := fileAddressDataKey I) (ret := calldataWord I.calldata 4) (R := [⟨313⟩, sel])
    (by simpa [fileAddressDataKey, fileAddressDataWord] using hroutine)
    (by
      unfold dogAuthCheckWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    hauth (dogPatchedJumpDest hpatch (by native_decide)) (by simp)
  exact ⟨_, _, hafterAuth⟩

theorem RD.dogFileAddressAuthRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨585⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := code) (sel := sel) (entry := ⟨585⟩) (ret := ⟨313⟩)
    (decoded := ⟨607⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (dogPatchedDJumpPrefix1405 ⟨607⟩ hpatch (by native_decide)) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.dogFileAddressDecodeToRoutine
    (v := v) (code := code) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hdecoded (dogPatchedJumpDest hpatch (by native_decide))
    (by simp)
  exact RD.dogAuthCheckRevert
    (code := code) (pc := ⟨2146⟩) (okPc := ⟨2235⟩)
    (key := fileAddressDataKey I) (ret := calldataWord I.calldata 4) (R := [⟨313⟩, sel])
    (by simpa [fileAddressDataKey, fileAddressDataWord] using hroutine)
    (by
      unfold dogAuthCheckWf
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    (by
      unfold solcErrorStringRevertTailWf dogAuthTailPc dogNotAuthorizedRawWord
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]
          native_decide)
    hauth (by simp)

theorem RD.dogFileAddressStoreVowLog {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2235⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileAddressVowBytes)
    (hret : (D_J code 0).contains ret = true)
    (hperm : ee.perm = true)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 28 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret (sel :: R)
      (writeWord mem 128 (UInt256.land data solcAddrMask))
      (UInt256.ofNat 5) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨2⟩
        (setAddressOffset0Word (solcSlotWord σ ee ⟨2⟩) data)) k' C' := by
  have rd2236 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  have rd2243 := evm_run rd2236 with [
    raw dup2
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd2241 := rd2243.pushConst (⟨7761783⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide)
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2244 := evm_run rd2241 with [
    raw push1 ⟨232⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have hconst : UInt256.shiftLeft ⟨7761783⟩ ⟨232⟩ =
      ABI.bytesToWord fileAddressVowBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd2244
  have rd2245 := rd2244.eq
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  rw [uInt256_eq_self] at rd2245
  have rd2246 := rd2245.iszero
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2246
  have rd2249 := rd2246.push2 ⟨1099⟩
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  have rd2250 := rd2249.jumpiNT
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rdStorePrefix := evm_run rd2250 with [
    raw push1 ⟨2⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd2254⟩ := rdStorePrefix.sload
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  have rd2275 := evm_run rd2254 with [
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw not
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw and
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup4
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw and
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw lor
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rdStore⟩ := rd2275.sstore hperm
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  have hword :
      UInt256.lor (UInt256.land data solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨2⟩)) =
        setAddressOffset0Word (solcSlotWord σ ee ⟨2⟩) data := by
    calc
      UInt256.lor (UInt256.land data solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨2⟩)) =
          UInt256.lor (UInt256.land data solcAddrMask)
            (UInt256.land (solcSlotWord σ ee ⟨2⟩) (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨2⟩)]
      _ = UInt256.lor (UInt256.land (solcSlotWord σ ee ⟨2⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land data solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (solcSlotWord σ ee ⟨2⟩) data := by
            rfl
  have rdMloadPrefix := evm_run rdStore with [
    raw push1 ⟨64⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdMload := by
    simpa [solcSlotWord, setAddressOffset0Word, hword,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using
      rdMloadPrefix.mload 0 ⟨128⟩ (UInt256.ofNat 3)
        (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
        mem_cost
        (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
        (by native_decide) (by evm_ov)
  have rdMstorePrefix := evm_run rdMload with [
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨160⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup4
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw and
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdMstore := rdMstorePrefix.mstore 6 (writeWord mem 128 (UInt256.land data solcAddrMask))
    (UInt256.ofNat 5)
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    mem_cost (by rfl) (by native_decide) (by evm_ov)
  have hread64' :
      (writeWord mem 128 (UInt256.land data solcAddrMask)).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ := by
    rw [writeWord_read_preserved mem 128 64 (UInt256.land data solcAddrMask)
      (by rw [hmem]; native_decide)
      (Or.inl ⟨by norm_num, by rw [hmem]⟩)]
    exact hread64
  have rdMload2Prefix := rdMstore.swap1
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  have rdMload2 := rdMload2Prefix.mload 0 ⟨128⟩ (UInt256.ofNat 5)
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    mem_cost
    (mloadFreePtrValue
      (by
        have hsz := writeWord_size mem 128 (UInt256.land data solcAddrMask)
          (by rw [hmem]; native_decide)
        rw [hsz, hmem]
        decide)
      (by decide) hread64')
    (by native_decide) (by evm_ov)
  have rdTopicStack := evm_run rdMload2 with [
    raw dup4
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdTopic := rdTopicStack.pushConst dogFileAddressLogTopic
    (width := 32) (op := .PUSH32) (by decide)
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons]; omega)
  have rdLogStack := evm_run rdTopic with [
    raw swap2
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rdLog := RD.log2 0 (UInt256.ofNat 5) rdLogStack
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    hperm mem_cost (by native_decide) (by evm_ov)
  have rdPop1 := rdLog.pop
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  have rdPop2 := rdPop1.pop
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  exact ⟨_, _, rdPop2.jump
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    hret (by evm_ov)⟩

theorem RD.dogFileAddressUnrecognizedRevert {v : DogImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2235⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileAddressVowBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 9 ≤ 1024) :
    RDrev code g s0 := by
  have rd2236 := h.jumpdest
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  have rd2243 := evm_run rd2236 with [
    raw dup2
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd2241 := rd2243.pushConst (⟨7761783⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide)
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2244 := evm_run rd2241 with [
    raw push1 ⟨232⟩
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl
      (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have hconst : UInt256.shiftLeft ⟨7761783⟩ ⟨232⟩ =
      ABI.bytesToWord fileAddressVowBytes := by
    native_decide
  rw [hconst] at rd2244
  have rd2245 := rd2244.eq
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileAddressVowBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd2245
  have rd2246 := rd2245.iszero
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2246
  have rd2249 := rd2246.push2 ⟨1099⟩
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    (by evm_ov)
  have rd1099 := rd2249.jumpiT
    (by rw [dogDecodePatchedEqTemplateAway hpatch (by native_decide) (by native_decide)]; native_decide)
    one_ne_zero_uint (dogPatchedDJumpPrefix1405 ⟨1099⟩ hpatch (by native_decide))
    (by evm_ov)
  have rd1100 := rd1099.jumpdest
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by evm_ov)
  exact RD.dogErrorStringRevertTailDirect
    (pc := ⟨1100⟩) (len := ⟨27⟩) (word := dogFileUnrecognizedRawWord)
    (op := .PUSH32) (width := 32) rd1100
    (by
      unfold dogErrorStringRevertTailDirectWf dogFileUnrecognizedRawWord
      repeat' first
        | apply And.intro
        | rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
          native_decide)
    (by decide) hmem hread64 (by simp only [List.length_cons]; omega)

theorem RD.dogFileAddressSuccess {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨585⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressVowBytes) :
    RDret code g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨2⟩
        (setAddressOffset0Word (solcSlotWord σ I ⟨2⟩) (fileAddressDataKey I)))
      ByteArray.empty := by
  obtain ⟨_, _, hswitch⟩ := RD.dogFileAddressToSwitch hpatch hreach hsz68 hsize hauth
  have hword :
      calldataWord I.calldata 4 = ABI.bytesToWord fileAddressVowBytes :=
    fileAddressWhatWord_eq_of_bytes_eq (by omega) hwhat
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  obtain ⟨_, _, hretPc⟩ := RD.dogFileAddressStoreVowLog
    (v := v) (code := code) (data := fileAddressDataKey I)
    (what := calldataWord I.calldata 4) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hswitch hword (dogPatchedDJumpPrefix1405 ⟨313⟩ hpatch (by native_decide))
    hperm hmemAuth hread64 (by simp)
  have hretPc' := hretPc.jumpdest
    (by
      rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
      native_decide)
    (by evm_ov)
  exact RD.stop hretPc'
    (by
      change decode code (⟨314⟩ : UInt256) = some (.STOP, .none)
      rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length_singleton]; omega)

theorem RD.dogFileAddressUnrecognizedParamRevert {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I)
      ⟨585⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotVow : fileAddressWhat I ≠ fileAddressVowBytes) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hswitch⟩ := RD.dogFileAddressToSwitch hpatch hreach hsz68 hsize hauth
  have hneq :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressVowBytes :=
    fileAddressWhatWord_ne_of_bytes_ne (by omega) hnotVow fileAddressVowBytes_length
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  exact RD.dogFileAddressUnrecognizedRevert
    (v := v) (code := code) (data := fileAddressDataKey I)
    (what := calldataWord I.calldata 4) (ret := ⟨313⟩) (sel := sel) (R := [])
    hpatch hswitch hneq hmemAuth hread64 (by simp)

theorem dogFileAddressBodyCoreOk
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg (contract v) I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode (config v).abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata = some (fileAddressLocals I))
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨585⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  let dataKey := fileAddressDataKey I
  let callerSlot := dogCallerWardsSlot I
  let locals := fileAddressLocals I
  have hcallerWord : dogSlotWord callerSlot σ_evm I = dogSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hvowWord : dogSlotWord ⟨2⟩ σ_evm I = dogSlotWord ⟨2⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨2⟩ ⟨0⟩
  have henc : returnEquiv ByteArray.empty none fileAddressTransition.returnType := by
    rw [show fileAddressTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  by_cases hauthEvm : dogSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : dogSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, dogCallerWardsSlot, dogSlotWord] using hauthEvm
    by_cases hwhat : fileAddressWhat I = fileAddressVowBytes
    · let stored := setAddressOffset0Word (dogSlotWord ⟨2⟩ σ_evm I) dataKey
      let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨2⟩ stored
      have hstoredSolm :
          stored = setAddressOffset0Word (dogSlotWord ⟨2⟩ σ_solm I) dataKey := by
        simpa [stored] using congrArg (fun old => setAddressOffset0Word old dataKey) hvowWord
      have hbody :
          ExecTransitionBody (config v) (contract v) evm0 locals fileAddressTransition.body
            (.returned { contract := contract v, locals := locals } evm1 none) := by
        simpa [evm0, evm1, locals, dataKey, stored, hstoredSolm, dogSlotWord, solcSlotWord,
          initState, Solm.EVM.storageLoad] using
          (fileAddressVowSourceBody (v := v) (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hauthSolm hwhat)
      have hret := RD.dogFileAddressSuccess hpatch hreach hperm hsz68 hsize hauthSolc hwhat
      have hcreated :
          (cA, sstoreAccountMap I.codeOwner σ_evm ⟨2⟩ stored).1 = evm1.createdAccounts := by
        simp [evm1, evm0, initState, storageStore_createdAccounts]
      have haccounts :
          accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨2⟩ stored)
            evm1.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩ stored hAccounts
        simpa [evm1, evm0, initState, storageStore_accountMap, stored, hstoredSolm,
          dogSlotWord, solcSlotWord, Solm.EVM.storageLoad] using hbase
      have hret' :
          RDret code (Sat256.ofUInt256 g)
            (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
            (cA, sstoreAccountMap I.codeOwner σ_evm ⟨2⟩ stored) ByteArray.empty := by
        simpa [stored, dataKey, dogSlotWord] using hret
      exact hret'.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
        hcreated haccounts henc
    · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody (config v) (contract v) evm0 locals fileAddressTransition.body
            .reverted := by
        simpa [evm0, locals] using
          (fileAddressUnrecognizedSourceBody (v := v) (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hauthSolm hwhat)
      have hrev := RD.dogFileAddressUnrecognizedParamRevert
        hpatch hreach hsz68 hsize hauthSolc hwhat
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : dogSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody :
        ExecTransitionBody (config v) (contract v) evm0 locals fileAddressTransition.body
          .reverted := by
      have hguard := dogAuthGuardEval_false (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals, fileAddressLocals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config v) (solm := { contract := contract v, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [
          .ite
            (.binary .eq (.var "what") vowParamLit)
            [ .assign .storage vowRef (.var "data") ]
            [ .require (.boolLit false) ] ])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, fileAddressTransition, nonpayable, auth, evm0, locals] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, dogCallerWardsSlot, dogSlotWord] using hauthEvm
    have hrev := RD.dogFileAddressAuthRevert hpatch hreach hsz68 hsize hauthSolc
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem dogFileAddressBodyCoreDecodeFailed_short
    {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code) (hsize : I.calldata.size < UInt256.size)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hdispatch : dispatchMsg (contract v) I.calldata = some fileAddressTransition)
    (hreach : ∃ k C, RD code I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨585⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := code) (sel := sel) (entry := ⟨585⟩) (ret := ⟨313⟩)
    (decoded := ⟨607⟩) (need := ⟨64⟩) hreach
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    (by rw [dogDecodePatchedEqTemplate1405 hpatch (by native_decide)]; native_decide)
    hlt
  exact hrev.reEquivDecodingFailed hcode hdispatch
    (dogDecode_fileAddress_none_short (v := v) hsz4 hshort)

theorem dogFileAddressBodyCore {v : DogImmutables} {code : ByteArray}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hpatch : patchRuntime dogBytecode (patches v) = some code)
    (hcode : I.code = code)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (dogSelBytes 9))
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I (dogSelBytes 9) rfl hsel
  have hdispatch : dispatchMsg (contract v) I.calldata = some fileAddressTransition :=
    dogDispatchFileAddress hsel
  have hreach := dogReachFileAddressBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    hpatch hcode hwv hsz4 hsize hsel
  by_cases hsz68 : 68 ≤ I.calldata.size
  · exact dogFileAddressBodyCoreOk hpatch hcode hwv hperm hsz68 hsize hdispatch
      (dogDecode_fileAddress_ok (v := v) hsz68) hreach hAccounts
  · exact dogFileAddressBodyCoreDecodeFailed_short hpatch hcode hsize hsz4 (by omega)
      hdispatch hreach

end Benchmarks.Dss.Dog
