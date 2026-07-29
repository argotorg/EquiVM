import Benchmarks.Dss.Cat.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cat

/-! ## `file(bytes32,address)` — HIGH-HIGH dispatch arm 0, entry ⟨591⟩

`vow` (slot 4, an address slot) is stored via a read-modify-write that preserves the high 96 bits.
Structurally like `Cat/FileUint.lean` but with a masked address decode and an address store. -/

abbrev fileAddressWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileAddressData (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 36).toNat

abbrev fileAddressDataWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileAddressDataKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (fileAddressDataWord I)

abbrev fileAddressVowBytes : List UInt8 :=
  [118, 111, 119, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

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

theorem fileAddressDataKey_canonical (I : ExecutionEnv) :
    (fileAddressDataKey I).toNat < EVM.addressModulus := by
  rw [fileAddressDataKey, u256_land_comm solcAddrMask (fileAddressDataWord I)]
  exact solcAddrMask_result_canonical (fileAddressDataWord I)

theorem fileAddressData_value_masked (I : ExecutionEnv) :
    (.address (fileAddressData I) : Value) =
      .address (AccountAddress.ofNat (fileAddressDataKey I).toNat) := by
  simpa [fileAddressData, fileAddressDataKey, fileAddressDataWord] using
    (solcAddressValue_masked (calldataWord I.calldata 36))

/-! ### ABI decode (`bytes32`, `address`) -/

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

/-! ### Dispatch / decode / locals -/

theorem catDispatch_fileAddress {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩) :
    dispatchMsg contract I.calldata = some fileAddressTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [biteTransition, boxTransition, cageTransition, clawTransition, denyTransition])
    (post := [fileIlkFlipTransition, fileIlkUintTransition, fileUintTransition, ilksTransition,
      litterTransition, liveTransition, relyTransition, vatTransition, vowTransition,
      wardsTransition])
    (ti := fileAddressTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, biteSelectorBytes, boxSelectorBytes, cageSelectorBytes,
        clawSelectorBytes, denySelectorBytes, hcd]
      native_decide
  · rw [selectorOf, fileAddressSelectorBytes]
    exact hsel

abbrev fileAddressLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileAddressWhat I))).insert
    "data" (.address (fileAddressData I))

theorem fileAddressLocals_get_what (I : ExecutionEnv) :
    (fileAddressLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileAddressWhat I)) := by
  rw [fileAddressLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileAddressLocals_get_data (I : ExecutionEnv) :
    (fileAddressLocals I).get? "data" =
      some (.address (fileAddressData I)) := by
  rw [fileAddressLocals, store_get_self]

theorem catDecode_fileAddress_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata =
        some (fileAddressLocals I) := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr, fileAddressWhat,
    fileAddressData, fileAddressLocals, abiBytes32, abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_address_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem catDecode_fileAddress_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata = none := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_address_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

/-! ### Solm eval helpers -/

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

/-! ### Address store (`vow := data`, slot 4) -/

theorem assign_fileAddressVowStorage (evm : EVM.State) {locals : Store} (data : UInt256)
    (hbase : locals.get? "vow" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨4⟩)
        (UInt256.land solcAddrMask data))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage vowRef (.address (AccountAddress.ofNat data.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have hvalue :
      (.address (AccountAddress.ofNat data.toNat) : Value) =
        .address (AccountAddress.ofNat (UInt256.land solcAddrMask data).toNat) := by
    simpa using (solcAddressValue_masked data)
  rw [hvalue]
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm vowRef =
        .ok { base := "vow", steps := [] } := by
    simp [vowRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (addrLoc ⟨4⟩)
          (.address (AccountAddress.ofNat (UInt256.land solcAddrMask data).toNat)) =
        some evm' := by
    simpa [addrLoc, evm'] using
      storageLocStore_address_offset0 evm ⟨4⟩ (UInt256.land solcAddrMask data) (by
        rw [u256_land_comm solcAddrMask data]
        exact solcAddrMask_result_canonical data)
  exact assignStorageRef_storage_scalar_value
    (ty := .elem .address) (loc := addrLoc ⟨4⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hscalar := by trivial)
    (hstore := hstore)

theorem fileAddressVowSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressVowBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨4⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm0 I.codeOwner ⟨4⟩) (fileAddressDataKey I))
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileAddressLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowParamLit) = .ok (.bool true) := by
    simpa [vowParamLit, fileAddressVowBytes, zeroPad29] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVowBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [locals] using
      (evalExpr_fileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals]))
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage vowRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [fileAddressData, fileAddressDataKey, fileAddressDataWord, evm1] using
      (assign_fileAddressVowStorage evm0 (locals := locals)
        (calldataWord I.calldata 36) (by simp [locals, fileAddressLocals]))
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage vowRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals] using ExecFuncBody.execBlockOK hblock

theorem fileAddressUnrecognizedSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotVow : fileAddressWhat I ≠ fileAddressVowBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileAddressLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") vowParamLit) = .ok (.bool false) := by
    simpa [vowParamLit, fileAddressVowBytes, zeroPad29] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressVowBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotVow)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hcond
      (ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)))
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

/-! ### Reachability (HIGH-HIGH arm 0) -/

theorem catReachFileAddressBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨591⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : catSelWord I = ⟨3572022915⟩ :=
    catSelWord_eq_of_beq I hsz 0xd4 0xe8 0xbe 0x83 ⟨3572022915⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat catBytecode catHighSplitPc) (catSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 0 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj
    exact absurd hj (by omega)
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catHighHighFirstArmPc 0))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact catReachHighHighBody 0 (by omega) ⟨591⟩ hcode hwv hsz hsize hroot hhigh heq0 htake
    (by jump_dest) (by native_decide)

/-! ### Entry bridge: decoded ⟨613⟩ → routine ⟨3080⟩ (load `what`@4, `data`@36, mask `data`) -/

theorem RD.catFileAddressDecodeToRoutine {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD catBytecode ee g s0 ⟨613⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hroutine : (D_J catBytecode 0).contains ⟨3080⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ⟨3080⟩
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  have rd614 := h.jumpdest (by native_decide) (by evm_ov)
  have rd615 := rd614.pop (by native_decide) (by evm_ov)
  have rd616 := rd615.dup1 (by native_decide) (by evm_ov)
  have rd617 := rd616.calldataload (by native_decide) (by evm_ov)
  have rd618 := rd617.swap1 (by native_decide) (by evm_ov)
  have rd620 := rd618.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd621 := rd620.add (by native_decide) (by evm_ov)
  have rd622 := rd621.calldataload (by native_decide) (by evm_ov)
  have rd624 := rd622.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd626 := rd624.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd628 := rd626.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd629 := rd628.shl (by native_decide) (by evm_ov)
  have rd630 := rd629.sub (by native_decide) (by evm_ov)
  have rd631 := rd630.and (by native_decide) (by evm_ov)
  have rd634 := rd631.push2 ⟨3080⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide, solcAddrMask]
      using rd634.jump (by native_decide) hroutine (by evm_ov)⟩

/-! ### Auth wrappers (reach ⟨591⟩ → auth check at ⟨3080⟩, okPc ⟨3169⟩) -/

theorem RD.catFileAddressToSwitch {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨591⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨3169⟩
      (fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨302⟩ :: sel :: [])
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := catBytecode) (sel := sel) (entry := ⟨591⟩) (ret := ⟨302⟩)
    (decoded := ⟨613⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.catFileAddressDecodeToRoutine
    (ret := ⟨302⟩) (sel := sel) (R := []) hdecoded (by jump_dest) (by simp)
  obtain ⟨_, _, hafterAuth⟩ := RD.catAuthCheckOk
    (code := catBytecode) (pc := ⟨3080⟩) (okPc := ⟨3169⟩)
    (key := fileAddressDataKey I) (ret := calldataWord I.calldata 4) (R := [⟨302⟩, sel])
    (by simpa [fileAddressDataKey, fileAddressDataWord] using hroutine)
    (by
      unfold catAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauth (by jump_dest) (by simp)
  exact ⟨_, _, hafterAuth⟩

theorem RD.catFileAddressAuthRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨591⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := catBytecode) (sel := sel) (entry := ⟨591⟩) (ret := ⟨302⟩)
    (decoded := ⟨613⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.catFileAddressDecodeToRoutine
    (ret := ⟨302⟩) (sel := sel) (R := []) hdecoded (by jump_dest) (by simp)
  exact RD.catAuthCheckRevert
    (code := catBytecode) (pc := ⟨3080⟩) (okPc := ⟨3169⟩)
    (key := fileAddressDataKey I) (ret := calldataWord I.calldata 4) (R := [⟨302⟩, sel])
    (by simpa [fileAddressDataKey, fileAddressDataWord] using hroutine)
    (by
      unfold catAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf catAuthTailPc catNotAuthorizedRawWord
      repeat' first | apply And.intro | native_decide)
    hauth (by simp)

/-! ### `vow` store (read-modify-write, slot 4) at ⟨3169⟩ -/

theorem setAddressOffset0Word_bytecode (old dataKey : UInt256) :
    UInt256.lor (UInt256.land dataKey solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old) =
      setAddressOffset0Word old dataKey := by
  unfold setAddressOffset0Word
  rw [u256_lor_comm (UInt256.land dataKey solcAddrMask)
        (UInt256.land (UInt256.lnot solcAddrMask) old),
    u256_land_comm (UInt256.lnot solcAddrMask) old]

theorem RD.catFileAddressStoreVow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {dataKey what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD catBytecode ee g s0 ⟨3169⟩ (dataKey :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileAddressVowBytes)
    (hret : (D_J catBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ret (sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨4⟩
        (setAddressOffset0Word (solcSlotWord σ ee ⟨4⟩) dataKey)) k' C' := by
  -- switch 3169-3183 (vow matches → not taken)
  have rd3170 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3171 := rd3170.dup2 (by native_decide) (by evm_ov)
  have rd3175 := rd3171.pushConst ⟨7761783⟩ (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd3177 := rd3175.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd3178 := rd3177.shl (by native_decide) (by evm_ov)
  have hconst :
      UInt256.shiftLeft ⟨7761783⟩ ⟨232⟩ = ABI.bytesToWord fileAddressVowBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd3178
  have rd3179 := rd3178.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd3179
  have rd3180 := rd3179.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd3180
  have rd3183 := rd3180.push2 ⟨953⟩ (by native_decide) (by evm_ov)
  have rd3184 := rd3183.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  -- store 3184-3214
  have rd3186 := rd3184.push1 ⟨4⟩ (by native_decide) (by evm_ov)
  have rd3187 := rd3186.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3188⟩ := rd3187.sload (by native_decide) (by evm_ov)
  have rd3190 := rd3188.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3192 := rd3190.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3194 := rd3192.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd3195 := rd3194.shl (by native_decide) (by evm_ov)
  have rd3196 := rd3195.sub (by native_decide) (by evm_ov)
  have rd3197 := rd3196.not (by native_decide) (by evm_ov)
  have rd3198 := rd3197.and (by native_decide) (by evm_ov)
  have rd3200 := rd3198.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3202 := rd3200.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd3204 := rd3202.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd3205 := rd3204.shl (by native_decide) (by evm_ov)
  have rd3206 := rd3205.sub (by native_decide) (by evm_ov)
  have rd3207 := rd3206.dup4 (by native_decide) (by evm_ov)
  have rd3208 := rd3207.and (by native_decide) (by evm_ov)
  have rd3209 := rd3208.or (by native_decide) (by evm_ov)
  rw [show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
    solcAddrMask from by decide] at rd3209
  rw [setAddressOffset0Word_bytecode] at rd3209
  have rd3210 := rd3209.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd3211⟩ := rd3210.sstore hperm (by native_decide) (by evm_ov)
  have rd3214 := rd3211.push2 ⟨1144⟩ (by native_decide) (by evm_ov)
  have rd1144 := rd3214.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd1145 := rd1144.jumpdest (by native_decide) (by evm_ov)
  have rd1146 := rd1145.pop (by native_decide) (by evm_ov)
  have rd1147 := rd1146.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1147.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.catFileAddressSkipVow {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {dataKey what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD catBytecode ee g s0 ⟨3169⟩ (dataKey :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileAddressVowBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ⟨953⟩ (dataKey :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd3170 := h.jumpdest (by native_decide) (by evm_ov)
  have rd3171 := rd3170.dup2 (by native_decide) (by evm_ov)
  have rd3175 := rd3171.pushConst ⟨7761783⟩ (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd3177 := rd3175.push1 ⟨232⟩ (by native_decide) (by evm_ov)
  have rd3178 := rd3177.shl (by native_decide) (by evm_ov)
  have hconst :
      UInt256.shiftLeft ⟨7761783⟩ ⟨232⟩ = ABI.bytesToWord fileAddressVowBytes := by
    native_decide
  rw [hconst] at rd3178
  have rd3179 := rd3178.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileAddressVowBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd3179
  have rd3180 := rd3179.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd3180
  have rd3183 := rd3180.push2 ⟨953⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd3183.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

/-! ### Unrecognized-param revert at ⟨953⟩ (byte-identical to Vow `file(bytes32,uint256)` @2156) -/

abbrev catFileAddressUnrecognizedRawWord : UInt256 :=
  ⟨30477146900841294791694925804285198379011926721857912948232373309380849827840⟩

theorem RD.catFileAddressUnrecognizedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD catBytecode ee g s0 ⟨953⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev catBytecode g s0 := by
  have rdMload := evm_run h with [
    raw jumpdest (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by native_decide) (by evm_ov),
    raw dup1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
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
  have rdRaw := rdPrefix.pushConst catFileAddressUnrecognizedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ catFileAddressUnrecognizedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ catFileAddressUnrecognizedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

/-! ### Success / revert wrappers -/

theorem RD.catFileAddressVowSuccess {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨591⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressVowBytes) :
    RDret catBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨4⟩
        (setAddressOffset0Word (solcSlotWord σ I ⟨4⟩) (fileAddressDataKey I))) ByteArray.empty := by
  obtain ⟨_, _, hswitch⟩ := RD.catFileAddressToSwitch hreach hsz68 hsize hauth
  have hword : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressVowBytes :=
    fileAddressWhatWord_eq_of_bytes_eq (by omega) hwhat
  obtain ⟨_, _, hretPc⟩ := RD.catFileAddressStoreVow
    (dataKey := fileAddressDataKey I) (what := calldataWord I.calldata 4) (ret := ⟨302⟩)
    (sel := sel) (R := []) hswitch hword (by jump_dest) hperm (by simp)
  have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop hretPc' (by native_decide) (by simp)

theorem RD.catFileAddressUnrecognizedParamRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨591⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotVow : fileAddressWhat I ≠ fileAddressVowBytes) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hswitch⟩ := RD.catFileAddressToSwitch hreach hsz68 hsize hauth
  have hvowNe : calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressVowBytes :=
    fileAddressWhatWord_ne_of_bytes_ne (by omega) hnotVow (by native_decide)
  obtain ⟨_, _, htailPc⟩ := RD.catFileAddressSkipVow
    (dataKey := fileAddressDataKey I) (what := calldataWord I.calldata 4) (ret := ⟨302⟩)
    (sel := sel) (R := []) hswitch hvowNe (by simp)
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size solcFreePtrMem_read64
  exact RD.catFileAddressUnrecognizedRevert htailPc hmemAuth hread64 (by simp)

/-! ### Body core / short / top -/

theorem catFileAddressBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨591⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := catCallerWardsSlot I
  let locals := fileAddressLocals I
  have hcallerWord : catSlotWord callerSlot σ_evm I = catSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have henc : returnEquiv ByteArray.empty none fileAddressTransition.returnType := by
    rw [show fileAddressTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  by_cases hauthEvm : catSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : catSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, catCallerWardsSlot, catSlotWord] using hauthEvm
    by_cases hvow : fileAddressWhat I = fileAddressVowBytes
    · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨4⟩
        (setAddressOffset0Word (Solm.EVM.storageLoad evm0 I.codeOwner ⟨4⟩) (fileAddressDataKey I))
      have hbody :
          ExecTransitionBody config contract evm0 locals fileAddressTransition.body
            (.returned { contract := contract, locals := locals } evm1 none) := by
        simpa [evm0, evm1, locals] using
          (fileAddressVowSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hvow)
      have hret := RD.catFileAddressVowSuccess hreach hperm hsz68 hsize hauthSolc hvow
      have hcreated :
          (cA, sstoreAccountMap I.codeOwner σ_evm ⟨4⟩
            (setAddressOffset0Word (solcSlotWord σ_evm I ⟨4⟩) (fileAddressDataKey I))).1 =
            evm1.createdAccounts := by
        simp [evm1, evm0, initState, storageStore_createdAccounts]
      have hslot4 : solcSlotWord σ_evm I ⟨4⟩ = solcSlotWord σ_solm I ⟨4⟩ :=
        accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨4⟩ ⟨0⟩
      have haccounts :
          accountMapEquiv
            (sstoreAccountMap I.codeOwner σ_evm ⟨4⟩
              (setAddressOffset0Word (solcSlotWord σ_evm I ⟨4⟩) (fileAddressDataKey I)))
            evm1.accountMap := by
        have hsl : Solm.EVM.storageLoad evm0 I.codeOwner ⟨4⟩ = solcSlotWord σ_evm I ⟨4⟩ := by
          rw [hslot4]
          simp [evm0, initState, Solm.EVM.storageLoad, State.lookupAccount,
            Account.lookupStorage, solcSlotWord]
        have hEq :
            evm1.accountMap =
              sstoreAccountMap I.codeOwner σ_solm ⟨4⟩
                (setAddressOffset0Word (solcSlotWord σ_evm I ⟨4⟩) (fileAddressDataKey I)) := by
          show (Solm.EVM.storageStore evm0 I.codeOwner ⟨4⟩
              (setAddressOffset0Word (Solm.EVM.storageLoad evm0 I.codeOwner ⟨4⟩)
                (fileAddressDataKey I))).accountMap = _
          rw [storageStore_accountMap, hsl]
          simp [evm0, initState]
        rw [hEq]
        exact accountMapEquiv_sstoreAccountMap I.codeOwner ⟨4⟩ _ hAccounts
      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
        hcreated haccounts henc
    · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody config contract evm0 locals fileAddressTransition.body
            .reverted := by
        simpa [evm0, locals] using
          (fileAddressUnrecognizedSourceBody (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hvow)
      have hrev := RD.catFileAddressUnrecognizedParamRevert hreach hsz68 hsize hauthSolc hvow
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : catSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody :
        ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
      have hguard := catAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals, fileAddressLocals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals })
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
      simpa [callerSlot, catCallerWardsSlot, catSlotWord] using hauthEvm
    have hrev := RD.catFileAddressAuthRevert hreach hsz68 hsize hauthSolc
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem catFileAddressShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach :=
    catReachFileAddressBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := catBytecode) (sel := catSelWord I) (entry := ⟨591⟩) (ret := ⟨302⟩)
    (decoded := ⟨613⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (catDispatch_fileAddress hsel)
    (catDecode_fileAddress_none_short hsz4 hshort)

theorem catFileAddressBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ (by native_decide) hsel
  by_cases hshort : I.calldata.size < 68
  · exact catFileAddressShort hcode hsize hperm hwv hsz hshort hsel hAccounts
  · have hsz68 : 68 ≤ I.calldata.size := by omega
    exact catFileAddressBodyCore (sel := catSelWord I) hcode hwv hperm hsz68 hsize
      (catDispatch_fileAddress hsel)
      (catDecode_fileAddress_ok hsz68)
      (catReachFileAddressBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
      hAccounts

end Benchmarks.Dss.Cat
