import Benchmarks.Dss.Vow.Deny

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `file(bytes32,uint256)` -/

abbrev fileUintWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileUintData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileUintWaitBytes : List UInt8 :=
  [119, 97, 105, 116, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileUintBumpBytes : List UInt8 :=
  [98, 117, 109, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileUintSumpBytes : List UInt8 :=
  [115, 117, 109, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileUintDumpBytes : List UInt8 :=
  [100, 117, 109, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileUintHumpBytes : List UInt8 :=
  [104, 117, 109, 112, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

theorem fileUintWhat_length {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    (fileUintWhat I).length = 32 := by
  simp [fileUintWhat, List.length_take, List.length_drop, byteArray_toList_eq]
  omega

theorem fileUintWhatWord_eq {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    ABI.bytesToWord (fileUintWhat I) = calldataWord I.calldata 4 := by
  simpa [fileUintWhat] using decode_word_at_eq I.calldata 4 (by omega) (by norm_num)

theorem fileUintWhatWord_eq_of_bytes_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hbs : fileUintWhat I = bs) :
    calldataWord I.calldata 4 = ABI.bytesToWord bs := by
  rw [← hbs]
  exact (fileUintWhatWord_eq (I := I) hsz36).symm

theorem fileUintWhat_eq_of_word_eq {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hword : calldataWord I.calldata 4 = ABI.bytesToWord bs)
    (hbsLen : bs.length = 32) :
    fileUintWhat I = bs := by
  have hto := toBytesBE_bytesToWord_of_length (bs := fileUintWhat I)
    (fileUintWhat_length (I := I) hsz36)
  rw [fileUintWhatWord_eq (I := I) hsz36, hword] at hto
  exact hto.symm.trans (toBytesBE_bytesToWord_of_length (bs := bs) hbsLen)

theorem fileUintWhatWord_ne_of_bytes_ne {I : ExecutionEnv} {bs : List UInt8}
    (hsz36 : 36 ≤ I.calldata.size) (hneq : fileUintWhat I ≠ bs)
    (hbsLen : bs.length = 32) :
    calldataWord I.calldata 4 ≠ ABI.bytesToWord bs := by
  intro hword
  exact hneq (fileUintWhat_eq_of_word_eq hsz36 hword hbsLen)

theorem decodeABIValues_bytes32_uint256_legacy_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32)
    (hlen32 : ((bytes.drop 32).take 32).length = 32) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      some ([.fixedBytes abiBytes32Width (bytes.take 32),
        .int (Int.ofNat (ABI.bytesToWord ((bytes.drop 32).take 32)).toNat)], 64) := by
  simp [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
    staticABIEncodedSize?, decodeABIValue?, readBytes?, hlen0]
  simp [readWord?, readBytes?, decodeABIWord?, hlen32]
  rw [Int.emod_eq_of_lt]
  · simp [UInt256.toNat]
  · exact Int.natCast_nonneg _
  · exact_mod_cast (ABI.bytesToWord ((bytes.drop 32).take 32)).val.isLt

theorem decodeABIValues_bytes32_uint256_legacy_none_short {bytes : List UInt8}
    (hshort : bytes.length < 64) :
    decodeABIValues? [abiBytes32, abiUInt256] bytes 0 0 64 64 DecodeMode.legacySolc05 =
      none := by
  simp only [decodeABIValues?, abiBytes32, abiBytes32Width, abiUInt256, isDynamicABIType,
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

theorem decodeCalldata_legacyBytes32_uint256_ok {cd : ByteArray} {x y : Solm.Ident}
    (hsz68 : 68 ≤ cd.size) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiUInt256] cd =
      some (((∅ : Solm.Store).insert x
        (.fixedBytes abiBytes32Width ((cd.toList.drop 4).take 32))).insert y
        (.int (Int.ofNat (calldataWord cd 36).toNat))) := by
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
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by decide +native]
  simp only [bind, Option.bind]
  rw [decodeABIValues_bytes32_uint256_legacy_ok (bytes := cd.toList.drop 4)
    (by simpa using htake4)
    (by simpa [List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using htake36)]
  rw [if_neg (by rw [List.length_drop, htlen]; omega : ¬ (cd.toList.drop 4).length < 64)]
  simp [decodeCalldata.insertValues]
  rw [hword36]

theorem decodeCalldata_legacyBytes32_uint256_none_short {cd : ByteArray}
    {x y : Solm.Ident} (hsz4 : 4 ≤ cd.size) (hshort : cd.size < 68) :
    decodeCalldataWithMode DecodeMode.legacySolc05 [x, y] [abiBytes32, abiUInt256] cd =
      none := by
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  unfold decodeCalldataWithMode decodeCalldata
  rw [if_neg (by rw [htlen]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [abiBytes32, abiUInt256, isDynamicABIType])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by decide +native]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_uint256_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

theorem vowDispatch_fileUint {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩) :
    dispatchMsg contract I.calldata = some fileUintTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition])
    (post := [fileAddressTransition, flapTransition, flapperTransition, flogTransition,
      flopTransition, flopperTransition, healTransition, humpTransition, kissTransition,
      liveTransition, relyTransition, sinTransition, sumpTransition, vatTransition, waitTransition,
      wardsTransition])
    (ti := fileUintTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x29, 0xae, 0x81, 0x14]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes, hcd]
      decide +native
  · rw [selectorOf, fileUintSelectorBytes]
    exact hsel

theorem vowDecode_fileUint_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata =
        some (((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileUintWhat I))).insert
          "data" (.int (Int.ofNat (fileUintData I).toNat))) := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileUintWhat, fileUintData, abiBytes32, abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem vowDecode_fileUint_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata = none := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

abbrev fileUintLocals (I : ExecutionEnv) : Store :=
  ((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileUintWhat I))).insert
    "data" (.int (Int.ofNat (fileUintData I).toNat))

theorem fileUintLocals_get_what (I : ExecutionEnv) :
    (fileUintLocals I).get? "what" =
      some (.fixedBytes bytes32Width (fileUintWhat I)) := by
  rw [fileUintLocals, store_get_ne _ _ (by decide), store_get_self]

theorem fileUintLocals_get_data (I : ExecutionEnv) :
    (fileUintLocals I).get? "data" =
      some (.int (Int.ofNat (fileUintData I).toNat)) := by
  rw [fileUintLocals, store_get_self]

theorem evalExpr_fileUintData {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (h : locals.get? "data" = some (.int (Int.ofNat (fileUintData I).toNat))) :
    evalExpr? config { contract := contract, locals := locals } evm (.var "data") =
      .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
  rw [evalExpr?]
  change EvalResult.ofOption EvalError.unboundVariable (locals.get? "data") =
    .ok (.int (Int.ofNat (fileUintData I).toNat))
  rw [h]
  rfl

theorem evalExpr_fileUintWhatEq_true {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileUintWhat I)))
    (hwhat : fileUintWhat I = bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool true) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem evalExpr_fileUintWhatEq_false {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    {bs : List UInt8}
    (hget : locals.get? "what" = some (.fixedBytes bytes32Width (fileUintWhat I)))
    (hwhat : fileUintWhat I ≠ bs) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .eq (.var "what") (.fixedBytesLit bytes32Width bs)) = .ok (.bool false) := by
  have hvar :
      evalExpr? config { contract := contract, locals := locals } evm (.var "what") =
        .ok (.fixedBytes bytes32Width (fileUintWhat I)) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "what") =
      .ok (.fixedBytes bytes32Width (fileUintWhat I))
    rw [hget]
    rfl
  rw [evalExpr?]
  simp only [hvar, EvalResult.bind, bind]
  simp [evalExpr?, evalBinaryOp?, hwhat]
  all_goals decide

theorem assign_fileUintWaitStorage (evm : EVM.State) {locals : Store} (data : UInt256)
    (hbase : locals.get? "wait" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨7⟩ data
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage waitRef (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm waitRef =
        .ok { base := "wait", steps := [] } := by
    simp [waitRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨7⟩) (.int (Int.ofNat data.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨7⟩ data
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨7⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem assign_fileUintBumpStorage (evm : EVM.State) {locals : Store} (data : UInt256)
    (hbase : locals.get? "bump" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨10⟩ data
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage bumpRef (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm bumpRef =
        .ok { base := "bump", steps := [] } := by
    simp [bumpRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨10⟩) (.int (Int.ofNat data.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨10⟩ data
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨10⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem assign_fileUintSumpStorage (evm : EVM.State) {locals : Store} (data : UInt256)
    (hbase : locals.get? "sump" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨9⟩ data
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage sumpRef (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm sumpRef =
        .ok { base := "sump", steps := [] } := by
    simp [sumpRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨9⟩) (.int (Int.ofNat data.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨9⟩ data
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨9⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem assign_fileUintDumpStorage (evm : EVM.State) {locals : Store} (data : UInt256)
    (hbase : locals.get? "dump" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ data
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage dumpRef (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm dumpRef =
        .ok { base := "dump", steps := [] } := by
    simp [dumpRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨8⟩) (.int (Int.ofNat data.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨8⟩ data
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨8⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem assign_fileUintHumpStorage (evm : EVM.State) {locals : Store} (data : UInt256)
    (hbase : locals.get? "hump" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨11⟩ data
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage humpRef (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm humpRef =
        .ok { base := "hump", steps := [] } := by
    simp [humpRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨11⟩) (.int (Int.ofNat data.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨11⟩ data
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨11⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem fileUintWaitSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileUintWhat I = fileUintWaitBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨7⟩ (fileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileUintLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") waitParamLit) = .ok (.bool true) := by
    simpa [waitParamLit, fileUintWaitBytes] using
      (evalExpr_fileUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintWaitBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
    simpa [locals] using
      (evalExpr_fileUintData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals]))
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage waitRef (.int (Int.ofNat (fileUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1] using
      (assign_fileUintWaitStorage evm0 (locals := locals) (fileUintData I)
        (by simp [locals, fileUintLocals]))
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage waitRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileUintTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hcond hthen) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals] using ExecFuncBody.execBlockOK hblock

theorem fileUintBumpSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotWait : fileUintWhat I ≠ fileUintWaitBytes)
    (hwhat : fileUintWhat I = fileUintBumpBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨10⟩ (fileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileUintLocals]) hauth
  have hwait :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") waitParamLit) = .ok (.bool false) := by
    simpa [waitParamLit, fileUintWaitBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintWaitBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotWait)
  have hbump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") bumpParamLit) = .ok (.bool true) := by
    simpa [bumpParamLit, fileUintBumpBytes] using
      (evalExpr_fileUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintBumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
    simpa [locals] using
      (evalExpr_fileUintData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals]))
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage bumpRef (.int (Int.ofNat (fileUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1] using
      (assign_fileUintBumpStorage evm0 (locals := locals) (fileUintData I)
        (by simp [locals, fileUintLocals]))
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage bumpRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") bumpParamLit)
          [.assign .storage bumpRef (.var "data")]
          [.ite (.binary .eq (.var "what") sumpParamLit)
            [.assign .storage sumpRef (.var "data")]
            [.ite (.binary .eq (.var "what") dumpParamLit)
              [.assign .storage dumpRef (.var "data")]
              [.ite (.binary .eq (.var "what") humpParamLit)
                [.assign .storage humpRef (.var "data")]
                [.require (.boolLit false)]]]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hbump hthen) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileUintTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hwait helse) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals] using ExecFuncBody.execBlockOK hblock

theorem fileUintSumpSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotWait : fileUintWhat I ≠ fileUintWaitBytes)
    (hnotBump : fileUintWhat I ≠ fileUintBumpBytes)
    (hwhat : fileUintWhat I = fileUintSumpBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨9⟩ (fileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileUintLocals]) hauth
  have hwait :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") waitParamLit) = .ok (.bool false) := by
    simpa [waitParamLit, fileUintWaitBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintWaitBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotWait)
  have hbump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") bumpParamLit) = .ok (.bool false) := by
    simpa [bumpParamLit, fileUintBumpBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintBumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotBump)
  have hsump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") sumpParamLit) = .ok (.bool true) := by
    simpa [sumpParamLit, fileUintSumpBytes] using
      (evalExpr_fileUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintSumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
    simpa [locals] using
      (evalExpr_fileUintData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals]))
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage sumpRef (.int (Int.ofNat (fileUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1] using
      (assign_fileUintSumpStorage evm0 (locals := locals) (fileUintData I)
        (by simp [locals, fileUintLocals]))
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage sumpRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hsumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") sumpParamLit)
          [.assign .storage sumpRef (.var "data")]
          [.ite (.binary .eq (.var "what") dumpParamLit)
            [.assign .storage dumpRef (.var "data")]
            [.ite (.binary .eq (.var "what") humpParamLit)
              [.assign .storage humpRef (.var "data")]
              [.require (.boolLit false)]]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hsump hthen) ExecBlock.nil
  have hbumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") bumpParamLit)
          [.assign .storage bumpRef (.var "data")]
          [.ite (.binary .eq (.var "what") sumpParamLit)
            [.assign .storage sumpRef (.var "data")]
            [.ite (.binary .eq (.var "what") dumpParamLit)
              [.assign .storage dumpRef (.var "data")]
              [.ite (.binary .eq (.var "what") humpParamLit)
                [.assign .storage humpRef (.var "data")]
                [.require (.boolLit false)]]]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbump hsumpElse) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileUintTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hwait hbumpElse) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals] using ExecFuncBody.execBlockOK hblock

theorem fileUintDumpSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotWait : fileUintWhat I ≠ fileUintWaitBytes)
    (hnotBump : fileUintWhat I ≠ fileUintBumpBytes)
    (hnotSump : fileUintWhat I ≠ fileUintSumpBytes)
    (hwhat : fileUintWhat I = fileUintDumpBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨8⟩ (fileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileUintLocals]) hauth
  have hwait :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") waitParamLit) = .ok (.bool false) := by
    simpa [waitParamLit, fileUintWaitBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintWaitBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotWait)
  have hbump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") bumpParamLit) = .ok (.bool false) := by
    simpa [bumpParamLit, fileUintBumpBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintBumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotBump)
  have hsump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") sumpParamLit) = .ok (.bool false) := by
    simpa [sumpParamLit, fileUintSumpBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintSumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotSump)
  have hdump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dumpParamLit) = .ok (.bool true) := by
    simpa [dumpParamLit, fileUintDumpBytes] using
      (evalExpr_fileUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintDumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
    simpa [locals] using
      (evalExpr_fileUintData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals]))
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage dumpRef (.int (Int.ofNat (fileUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1] using
      (assign_fileUintDumpStorage evm0 (locals := locals) (fileUintData I)
        (by simp [locals, fileUintLocals]))
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage dumpRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hdumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dumpParamLit)
          [.assign .storage dumpRef (.var "data")]
          [.ite (.binary .eq (.var "what") humpParamLit)
            [.assign .storage humpRef (.var "data")]
            [.require (.boolLit false)]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hdump hthen) ExecBlock.nil
  have hsumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") sumpParamLit)
          [.assign .storage sumpRef (.var "data")]
          [.ite (.binary .eq (.var "what") dumpParamLit)
            [.assign .storage dumpRef (.var "data")]
            [.ite (.binary .eq (.var "what") humpParamLit)
              [.assign .storage humpRef (.var "data")]
              [.require (.boolLit false)]]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hsump hdumpElse) ExecBlock.nil
  have hbumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") bumpParamLit)
          [.assign .storage bumpRef (.var "data")]
          [.ite (.binary .eq (.var "what") sumpParamLit)
            [.assign .storage sumpRef (.var "data")]
            [.ite (.binary .eq (.var "what") dumpParamLit)
              [.assign .storage dumpRef (.var "data")]
              [.ite (.binary .eq (.var "what") humpParamLit)
                [.assign .storage humpRef (.var "data")]
                [.require (.boolLit false)]]]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbump hsumpElse) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileUintTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hwait hbumpElse) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals] using ExecFuncBody.execBlockOK hblock

theorem fileUintHumpSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotWait : fileUintWhat I ≠ fileUintWaitBytes)
    (hnotBump : fileUintWhat I ≠ fileUintBumpBytes)
    (hnotSump : fileUintWhat I ≠ fileUintSumpBytes)
    (hnotDump : fileUintWhat I ≠ fileUintDumpBytes)
    (hwhat : fileUintWhat I = fileUintHumpBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨11⟩ (fileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileUintLocals]) hauth
  have hwait :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") waitParamLit) = .ok (.bool false) := by
    simpa [waitParamLit, fileUintWaitBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintWaitBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotWait)
  have hbump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") bumpParamLit) = .ok (.bool false) := by
    simpa [bumpParamLit, fileUintBumpBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintBumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotBump)
  have hsump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") sumpParamLit) = .ok (.bool false) := by
    simpa [sumpParamLit, fileUintSumpBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintSumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotSump)
  have hdump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dumpParamLit) = .ok (.bool false) := by
    simpa [dumpParamLit, fileUintDumpBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintDumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotDump)
  have hhump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") humpParamLit) = .ok (.bool true) := by
    simpa [humpParamLit, fileUintHumpBytes] using
      (evalExpr_fileUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintHumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
    simpa [locals] using
      (evalExpr_fileUintData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals]))
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage humpRef (.int (Int.ofNat (fileUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1] using
      (assign_fileUintHumpStorage evm0 (locals := locals) (fileUintData I)
        (by simp [locals, fileUintLocals]))
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage humpRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have hhumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") humpParamLit)
          [.assign .storage humpRef (.var "data")]
          [.require (.boolLit false)]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hhump hthen) ExecBlock.nil
  have hdumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dumpParamLit)
          [.assign .storage dumpRef (.var "data")]
          [.ite (.binary .eq (.var "what") humpParamLit)
            [.assign .storage humpRef (.var "data")]
            [.require (.boolLit false)]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hdump hhumpElse) ExecBlock.nil
  have hsumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") sumpParamLit)
          [.assign .storage sumpRef (.var "data")]
          [.ite (.binary .eq (.var "what") dumpParamLit)
            [.assign .storage dumpRef (.var "data")]
            [.ite (.binary .eq (.var "what") humpParamLit)
              [.assign .storage humpRef (.var "data")]
              [.require (.boolLit false)]]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hsump hdumpElse) ExecBlock.nil
  have hbumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") bumpParamLit)
          [.assign .storage bumpRef (.var "data")]
          [.ite (.binary .eq (.var "what") sumpParamLit)
            [.assign .storage sumpRef (.var "data")]
            [.ite (.binary .eq (.var "what") dumpParamLit)
              [.assign .storage dumpRef (.var "data")]
              [.ite (.binary .eq (.var "what") humpParamLit)
                [.assign .storage humpRef (.var "data")]
                [.require (.boolLit false)]]]]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteFalse hbump hsumpElse) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileUintTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hwait hbumpElse) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals] using ExecFuncBody.execBlockOK hblock

theorem fileUintUnrecognizedSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotWait : fileUintWhat I ≠ fileUintWaitBytes)
    (hnotBump : fileUintWhat I ≠ fileUintBumpBytes)
    (hnotSump : fileUintWhat I ≠ fileUintSumpBytes)
    (hnotDump : fileUintWhat I ≠ fileUintDumpBytes)
    (hnotHump : fileUintWhat I ≠ fileUintHumpBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
  intro locals evm0
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileUintLocals]) hauth
  have hwait :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") waitParamLit) = .ok (.bool false) := by
    simpa [waitParamLit, fileUintWaitBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintWaitBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotWait)
  have hbump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") bumpParamLit) = .ok (.bool false) := by
    simpa [bumpParamLit, fileUintBumpBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintBumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotBump)
  have hsump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") sumpParamLit) = .ok (.bool false) := by
    simpa [sumpParamLit, fileUintSumpBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintSumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotSump)
  have hdump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") dumpParamLit) = .ok (.bool false) := by
    simpa [dumpParamLit, fileUintDumpBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintDumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotDump)
  have hhump :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") humpParamLit) = .ok (.bool false) := by
    simpa [humpParamLit, fileUintHumpBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintHumpBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotHump)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hhumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") humpParamLit)
          [.assign .storage humpRef (.var "data")]
          [.require (.boolLit false)]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hhump
      (ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)))
  have hdumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") dumpParamLit)
          [.assign .storage dumpRef (.var "data")]
          [.ite (.binary .eq (.var "what") humpParamLit)
            [.assign .storage humpRef (.var "data")]
            [.require (.boolLit false)]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hdump hhumpElse)
  have hsumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") sumpParamLit)
          [.assign .storage sumpRef (.var "data")]
          [.ite (.binary .eq (.var "what") dumpParamLit)
            [.assign .storage dumpRef (.var "data")]
            [.ite (.binary .eq (.var "what") humpParamLit)
              [.assign .storage humpRef (.var "data")]
              [.require (.boolLit false)]]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hsump hdumpElse)
  have hbumpElse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite (.binary .eq (.var "what") bumpParamLit)
          [.assign .storage bumpRef (.var "data")]
          [.ite (.binary .eq (.var "what") sumpParamLit)
            [.assign .storage sumpRef (.var "data")]
            [.ite (.binary .eq (.var "what") dumpParamLit)
              [.assign .storage dumpRef (.var "data")]
              [.ite (.binary .eq (.var "what") humpParamLit)
                [.assign .storage humpRef (.var "data")]
                [.require (.boolLit false)]]]]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hbump hsumpElse)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileUintTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hwait hbumpElse)
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

theorem vowReachFileUintBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨414⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨699302164⟩ :=
    vowSelWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨699302164⟩
      (by decide +native) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  have heq0 : ∀ j, j < 3 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> decide +native
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc 3))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    decide +native
  exact vowReachLowLowBody 3 (by omega) ⟨414⟩ hcode hwv hsz hsize hroot hlow heq0
    htake (by jump_dest) (by decide +native)

theorem RD.vowFileUintDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨436⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = vowBytecode)
    (hroutine : (D_J code 0).contains ⟨1942⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1942⟩
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd437 := h.jumpdest (by decide +native) (by evm_ov)
  have rd438 := rd437.pop (by decide +native) (by evm_ov)
  have rd439 := rd438.dup1 (by decide +native) (by evm_ov)
  have rd440 := rd439.calldataload (by decide +native) (by evm_ov)
  have rd441 := rd440.swap1 (by decide +native) (by evm_ov)
  have rd443 := rd441.push1 ⟨32⟩ (by decide +native) (by evm_ov)
  have rd444 := rd443.add (by decide +native) (by evm_ov)
  have rd445 := rd444.calldataload (by decide +native) (by evm_ov)
  have rd448 := rd445.push2 ⟨1942⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd448.jump (by decide +native) hroutine (by evm_ov)⟩

theorem RD.vowFileUintToSwitch {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨414⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨2031⟩
      (fileUintData I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨414⟩) (ret := ⟨412⟩)
    (decoded := ⟨436⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.vowFileUintDecodeToRoutine
    (code := vowBytecode) (ret := ⟨412⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  obtain ⟨_, _, hafterAuth⟩ := RD.vowAuthCheckOk
    (code := vowBytecode) (pc := ⟨1942⟩) (okPc := ⟨2031⟩)
    (key := fileUintData I) (ret := calldataWord I.calldata 4) (R := [⟨412⟩, sel])
    (by simpa [fileUintData] using hroutine)
    (by
      unfold vowAuthCheckWf
      repeat' first | apply And.intro | decide +native)
    hauth (by jump_dest) (by simp)
  exact ⟨_, _, hafterAuth⟩

theorem RD.vowFileUintAuthRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨414⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩) :
    RDrev vowBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨414⟩) (ret := ⟨412⟩)
    (decoded := ⟨436⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.vowFileUintDecodeToRoutine
    (code := vowBytecode) (ret := ⟨412⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact RD.vowAuthCheckRevert
    (code := vowBytecode) (pc := ⟨1942⟩) (okPc := ⟨2031⟩)
    (key := fileUintData I) (ret := calldataWord I.calldata 4) (R := [⟨412⟩, sel])
    (by simpa [fileUintData] using hroutine)
    (by
      unfold vowAuthCheckWf
      repeat' first | apply And.intro | decide +native)
    (by
      unfold solcErrorStringRevertTailWf vowAuthTailPc vowNotAuthorizedRawWord
      repeat' first | apply And.intro | decide +native)
    hauth (by simp)

theorem RD.vowFileUintStoreWait {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vowBytecode ee g s0 ⟨2031⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileUintWaitBytes)
    (hret : (D_J vowBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ret (sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨7⟩ data) k' C' := by
  have rd2032 := h.jumpdest (by decide +native) (by evm_ov)
  have rd2033 := rd2032.dup2 (by decide +native) (by evm_ov)
  have rd2038 := rd2033.push4 ⟨500718173⟩ (by decide +native) (by evm_ov)
  have rd2040 := rd2038.push1 ⟨226⟩ (by decide +native) (by evm_ov)
  have rd2041 := rd2040.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨500718173⟩ ⟨226⟩ = ABI.bytesToWord fileUintWaitBytes := by
    decide +native
  rw [hmatch, ← hconst] at rd2041
  have rd2042 := rd2041.eq (by decide +native) (by evm_ov)
  rw [uInt256_eq_self] at rd2042
  have rd2043 := rd2042.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2043
  have rd2046 := rd2043.push2 ⟨2056⟩ (by decide +native) (by evm_ov)
  have rd2047 := rd2046.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd2049 := rd2047.push1 ⟨7⟩ (by decide +native) (by evm_ov)
  have rd2050 := rd2049.dup2 (by decide +native) (by evm_ov)
  have rd2051 := rd2050.swap1 (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd2052⟩ := rd2051.sstore hperm (by decide +native) (by evm_ov)
  have rd2055 := rd2052.push2 ⟨2233⟩ (by decide +native) (by evm_ov)
  have rd2233 := rd2055.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd2234 := rd2233.jumpdest (by decide +native) (by evm_ov)
  have rd2235 := rd2234.pop (by decide +native) (by evm_ov)
  have rd2236 := rd2235.pop (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2236.jump (by decide +native) hret (by evm_ov)⟩

theorem RD.vowFileUintSkipWait {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vowBytecode ee g s0 ⟨2031⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileUintWaitBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2056⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd2032 := h.jumpdest (by decide +native) (by evm_ov)
  have rd2033 := rd2032.dup2 (by decide +native) (by evm_ov)
  have rd2038 := rd2033.push4 ⟨500718173⟩ (by decide +native) (by evm_ov)
  have rd2040 := rd2038.push1 ⟨226⟩ (by decide +native) (by evm_ov)
  have rd2041 := rd2040.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨500718173⟩ ⟨226⟩ = ABI.bytesToWord fileUintWaitBytes := by
    decide +native
  rw [hconst] at rd2041
  have rd2042 := rd2041.eq (by decide +native) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileUintWaitBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd2042
  have rd2043 := rd2042.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2043
  have rd2046 := rd2043.push2 ⟨2056⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2046.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

theorem RD.vowFileUintStoreBump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vowBytecode ee g s0 ⟨2056⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileUintBumpBytes)
    (hret : (D_J vowBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ret (sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨10⟩ data) k' C' := by
  have rd2057 := h.jumpdest (by decide +native) (by evm_ov)
  have rd2058 := rd2057.dup2 (by decide +native) (by evm_ov)
  have rd2063 := rd2058.push4 ⟨103241431⟩ (by decide +native) (by evm_ov)
  have rd2065 := rd2063.push1 ⟨228⟩ (by decide +native) (by evm_ov)
  have rd2066 := rd2065.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨103241431⟩ ⟨228⟩ = ABI.bytesToWord fileUintBumpBytes := by
    decide +native
  rw [hmatch, ← hconst] at rd2066
  have rd2067 := rd2066.eq (by decide +native) (by evm_ov)
  rw [uInt256_eq_self] at rd2067
  have rd2068 := rd2067.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2068
  have rd2071 := rd2068.push2 ⟨2081⟩ (by decide +native) (by evm_ov)
  have rd2072 := rd2071.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd2074 := rd2072.push1 ⟨10⟩ (by decide +native) (by evm_ov)
  have rd2075 := rd2074.dup2 (by decide +native) (by evm_ov)
  have rd2076 := rd2075.swap1 (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd2077⟩ := rd2076.sstore hperm (by decide +native) (by evm_ov)
  have rd2080 := rd2077.push2 ⟨2233⟩ (by decide +native) (by evm_ov)
  have rd2233 := rd2080.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd2234 := rd2233.jumpdest (by decide +native) (by evm_ov)
  have rd2235 := rd2234.pop (by decide +native) (by evm_ov)
  have rd2236 := rd2235.pop (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2236.jump (by decide +native) hret (by evm_ov)⟩

theorem RD.vowFileUintSkipBump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vowBytecode ee g s0 ⟨2056⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileUintBumpBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2081⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd2057 := h.jumpdest (by decide +native) (by evm_ov)
  have rd2058 := rd2057.dup2 (by decide +native) (by evm_ov)
  have rd2063 := rd2058.push4 ⟨103241431⟩ (by decide +native) (by evm_ov)
  have rd2065 := rd2063.push1 ⟨228⟩ (by decide +native) (by evm_ov)
  have rd2066 := rd2065.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨103241431⟩ ⟨228⟩ = ABI.bytesToWord fileUintBumpBytes := by
    decide +native
  rw [hconst] at rd2066
  have rd2067 := rd2066.eq (by decide +native) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileUintBumpBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd2067
  have rd2068 := rd2067.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2068
  have rd2071 := rd2068.push2 ⟨2081⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2071.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

theorem RD.vowFileUintStoreSump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vowBytecode ee g s0 ⟨2081⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileUintSumpBytes)
    (hret : (D_J vowBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ret (sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨9⟩ data) k' C' := by
  have rd2082 := h.jumpdest (by decide +native) (by evm_ov)
  have rd2083 := rd2082.dup2 (by decide +native) (by evm_ov)
  have rd2088 := rd2083.push4 ⟨121067223⟩ (by decide +native) (by evm_ov)
  have rd2090 := rd2088.push1 ⟨228⟩ (by decide +native) (by evm_ov)
  have rd2091 := rd2090.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨121067223⟩ ⟨228⟩ = ABI.bytesToWord fileUintSumpBytes := by
    decide +native
  rw [hmatch, ← hconst] at rd2091
  have rd2092 := rd2091.eq (by decide +native) (by evm_ov)
  rw [uInt256_eq_self] at rd2092
  have rd2093 := rd2092.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2093
  have rd2096 := rd2093.push2 ⟨2106⟩ (by decide +native) (by evm_ov)
  have rd2097 := rd2096.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd2099 := rd2097.push1 ⟨9⟩ (by decide +native) (by evm_ov)
  have rd2100 := rd2099.dup2 (by decide +native) (by evm_ov)
  have rd2101 := rd2100.swap1 (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd2102⟩ := rd2101.sstore hperm (by decide +native) (by evm_ov)
  have rd2105 := rd2102.push2 ⟨2233⟩ (by decide +native) (by evm_ov)
  have rd2233 := rd2105.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd2234 := rd2233.jumpdest (by decide +native) (by evm_ov)
  have rd2235 := rd2234.pop (by decide +native) (by evm_ov)
  have rd2236 := rd2235.pop (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2236.jump (by decide +native) hret (by evm_ov)⟩

theorem RD.vowFileUintSkipSump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vowBytecode ee g s0 ⟨2081⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileUintSumpBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2106⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd2082 := h.jumpdest (by decide +native) (by evm_ov)
  have rd2083 := rd2082.dup2 (by decide +native) (by evm_ov)
  have rd2088 := rd2083.push4 ⟨121067223⟩ (by decide +native) (by evm_ov)
  have rd2090 := rd2088.push1 ⟨228⟩ (by decide +native) (by evm_ov)
  have rd2091 := rd2090.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨121067223⟩ ⟨228⟩ = ABI.bytesToWord fileUintSumpBytes := by
    decide +native
  rw [hconst] at rd2091
  have rd2092 := rd2091.eq (by decide +native) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileUintSumpBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd2092
  have rd2093 := rd2092.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2093
  have rd2096 := rd2093.push2 ⟨2106⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2096.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

theorem RD.vowFileUintStoreDump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vowBytecode ee g s0 ⟨2106⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileUintDumpBytes)
    (hret : (D_J vowBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ret (sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨8⟩ data) k' C' := by
  have rd2107 := h.jumpdest (by decide +native) (by evm_ov)
  have rd2108 := rd2107.dup2 (by decide +native) (by evm_ov)
  have rd2113 := rd2108.push4 ⟨105338583⟩ (by decide +native) (by evm_ov)
  have rd2115 := rd2113.push1 ⟨228⟩ (by decide +native) (by evm_ov)
  have rd2116 := rd2115.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨105338583⟩ ⟨228⟩ = ABI.bytesToWord fileUintDumpBytes := by
    decide +native
  rw [hmatch, ← hconst] at rd2116
  have rd2117 := rd2116.eq (by decide +native) (by evm_ov)
  rw [uInt256_eq_self] at rd2117
  have rd2118 := rd2117.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2118
  have rd2121 := rd2118.push2 ⟨2131⟩ (by decide +native) (by evm_ov)
  have rd2122 := rd2121.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd2124 := rd2122.push1 ⟨8⟩ (by decide +native) (by evm_ov)
  have rd2125 := rd2124.dup2 (by decide +native) (by evm_ov)
  have rd2126 := rd2125.swap1 (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd2127⟩ := rd2126.sstore hperm (by decide +native) (by evm_ov)
  have rd2130 := rd2127.push2 ⟨2233⟩ (by decide +native) (by evm_ov)
  have rd2233 := rd2130.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd2234 := rd2233.jumpdest (by decide +native) (by evm_ov)
  have rd2235 := rd2234.pop (by decide +native) (by evm_ov)
  have rd2236 := rd2235.pop (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2236.jump (by decide +native) hret (by evm_ov)⟩

theorem RD.vowFileUintSkipDump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vowBytecode ee g s0 ⟨2106⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileUintDumpBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2131⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd2107 := h.jumpdest (by decide +native) (by evm_ov)
  have rd2108 := rd2107.dup2 (by decide +native) (by evm_ov)
  have rd2113 := rd2108.push4 ⟨105338583⟩ (by decide +native) (by evm_ov)
  have rd2115 := rd2113.push1 ⟨228⟩ (by decide +native) (by evm_ov)
  have rd2116 := rd2115.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨105338583⟩ ⟨228⟩ = ABI.bytesToWord fileUintDumpBytes := by
    decide +native
  rw [hconst] at rd2116
  have rd2117 := rd2116.eq (by decide +native) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileUintDumpBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd2117
  have rd2118 := rd2117.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2118
  have rd2121 := rd2118.push2 ⟨2131⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2121.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

theorem RD.vowFileUintStoreHump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vowBytecode ee g s0 ⟨2131⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileUintHumpBytes)
    (hret : (D_J vowBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ret (sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨11⟩ data) k' C' := by
  have rd2132 := h.jumpdest (by decide +native) (by evm_ov)
  have rd2133 := rd2132.dup2 (by decide +native) (by evm_ov)
  have rd2138 := rd2133.push4 ⟨109532887⟩ (by decide +native) (by evm_ov)
  have rd2140 := rd2138.push1 ⟨228⟩ (by decide +native) (by evm_ov)
  have rd2141 := rd2140.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨109532887⟩ ⟨228⟩ = ABI.bytesToWord fileUintHumpBytes := by
    decide +native
  rw [hmatch, ← hconst] at rd2141
  have rd2142 := rd2141.eq (by decide +native) (by evm_ov)
  rw [uInt256_eq_self] at rd2142
  have rd2143 := rd2142.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd2143
  have rd2146 := rd2143.push2 ⟨2156⟩ (by decide +native) (by evm_ov)
  have rd2147 := rd2146.jumpiNT (by decide +native)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd2149 := rd2147.push1 ⟨11⟩ (by decide +native) (by evm_ov)
  have rd2150 := rd2149.dup2 (by decide +native) (by evm_ov)
  have rd2151 := rd2150.swap1 (by decide +native) (by evm_ov)
  obtain ⟨_, _, rd2152⟩ := rd2151.sstore hperm (by decide +native) (by evm_ov)
  have rd2155 := rd2152.push2 ⟨2233⟩ (by decide +native) (by evm_ov)
  have rd2233 := rd2155.jump (by decide +native) (by jump_dest) (by evm_ov)
  have rd2234 := rd2233.jumpdest (by decide +native) (by evm_ov)
  have rd2235 := rd2234.pop (by decide +native) (by evm_ov)
  have rd2236 := rd2235.pop (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2236.jump (by decide +native) hret (by evm_ov)⟩

theorem RD.vowFileUintSkipHump {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vowBytecode ee g s0 ⟨2131⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileUintHumpBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2156⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd2132 := h.jumpdest (by decide +native) (by evm_ov)
  have rd2133 := rd2132.dup2 (by decide +native) (by evm_ov)
  have rd2138 := rd2133.push4 ⟨109532887⟩ (by decide +native) (by evm_ov)
  have rd2140 := rd2138.push1 ⟨228⟩ (by decide +native) (by evm_ov)
  have rd2141 := rd2140.shl (by decide +native) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨109532887⟩ ⟨228⟩ = ABI.bytesToWord fileUintHumpBytes := by
    decide +native
  rw [hconst] at rd2141
  have rd2142 := rd2141.eq (by decide +native) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileUintHumpBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd2142
  have rd2143 := rd2142.iszero (by decide +native) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd2143
  have rd2146 := rd2143.push2 ⟨2156⟩ (by decide +native) (by evm_ov)
  exact ⟨_, _, rd2146.jumpiT (by decide +native) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

abbrev vowFileUintUnrecognizedRawWord : UInt256 :=
  ⟨39095847588069293923093613317176741730294750524144098737109233846858920493056⟩

theorem RD.vowFileUintUnrecognizedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {stk : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vowBytecode ee g s0 ⟨2156⟩ stk mem (UInt256.ofNat 3) rdata acc k C)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : stk.length + 5 ≤ 1024) :
    RDrev vowBytecode g s0 := by
  have rdMload := evm_run h with [
    raw jumpdest (by decide +native) (by evm_ov),
    raw push1 ⟨64⟩ (by decide +native) (by evm_ov),
    raw dup1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by decide +native)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rdSelectorRaw := rdMload.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by decide +native)
    (by simp only [List.length_cons]; omega)
  have rdPrefix := evm_run rdSelectorRaw with [
    raw push1 ⟨229⟩ (by decide +native) (by evm_ov),
    raw shl (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw mstore 6 (solcErrorStringMem0 mem) (UInt256.ofNat 5)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨32⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨4⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (solcErrorStringMem1 mem) (UInt256.ofNat 6)
      (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw push1 ⟨27⟩ (by decide +native) (by evm_ov),
    raw push1 ⟨36⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (solcErrorStringMem2 ⟨27⟩ mem)
      (UInt256.ofNat 7) (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rdRaw := rdPrefix.pushConst vowFileUintUnrecognizedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by decide +native)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by decide +native) (by evm_ov),
    raw dup3 (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ vowFileUintUnrecognizedRawWord mem)
      (UInt256.ofNat 8) (by decide +native) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by decide +native)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ vowFileUintUnrecognizedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw dup2 (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw sub (by decide +native) (by evm_ov),
    raw push1 ⟨100⟩ (by decide +native) (by evm_ov),
    raw add (by decide +native) (by evm_ov),
    raw swap1 (by decide +native) (by evm_ov),
    raw rev 0 (by decide +native) mem_cost (by evm_ov)]

theorem RD.vowFileUintWaitSuccess {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨414⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hwhat : fileUintWhat I = fileUintWaitBytes) :
    RDret vowBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨7⟩ (fileUintData I)) ByteArray.empty := by
  obtain ⟨_, _, hswitch⟩ := RD.vowFileUintToSwitch hreach hsz68 hsize hauth
  have hword :
      calldataWord I.calldata 4 = ABI.bytesToWord fileUintWaitBytes :=
    fileUintWhatWord_eq_of_bytes_eq (by omega) hwhat
  obtain ⟨_, _, hretPc⟩ := RD.vowFileUintStoreWait
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hswitch hword (by jump_dest) hperm (by simp)
  have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop hretPc' (by decide +native) (by simp)

theorem RD.vowFileUintBumpSuccess {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨414⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotWait : fileUintWhat I ≠ fileUintWaitBytes)
    (hwhat : fileUintWhat I = fileUintBumpBytes) :
    RDret vowBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨10⟩ (fileUintData I)) ByteArray.empty := by
  obtain ⟨_, _, hswitch⟩ := RD.vowFileUintToSwitch hreach hsz68 hsize hauth
  have hwaitNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintWaitBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotWait (by decide +native)
  obtain ⟨_, _, hbumpPc⟩ := RD.vowFileUintSkipWait
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hswitch hwaitNe (by simp)
  have hword :
      calldataWord I.calldata 4 = ABI.bytesToWord fileUintBumpBytes :=
    fileUintWhatWord_eq_of_bytes_eq (by omega) hwhat
  obtain ⟨_, _, hretPc⟩ := RD.vowFileUintStoreBump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hbumpPc hword (by jump_dest) hperm (by simp)
  have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop hretPc' (by decide +native) (by simp)

theorem RD.vowFileUintSumpSuccess {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨414⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotWait : fileUintWhat I ≠ fileUintWaitBytes)
    (hnotBump : fileUintWhat I ≠ fileUintBumpBytes)
    (hwhat : fileUintWhat I = fileUintSumpBytes) :
    RDret vowBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨9⟩ (fileUintData I)) ByteArray.empty := by
  obtain ⟨_, _, hswitch⟩ := RD.vowFileUintToSwitch hreach hsz68 hsize hauth
  have hwaitNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintWaitBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotWait (by decide +native)
  obtain ⟨_, _, hbumpPc⟩ := RD.vowFileUintSkipWait
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hswitch hwaitNe (by simp)
  have hbumpNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintBumpBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotBump (by decide +native)
  obtain ⟨_, _, hsumpPc⟩ := RD.vowFileUintSkipBump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hbumpPc hbumpNe (by simp)
  have hword :
      calldataWord I.calldata 4 = ABI.bytesToWord fileUintSumpBytes :=
    fileUintWhatWord_eq_of_bytes_eq (by omega) hwhat
  obtain ⟨_, _, hretPc⟩ := RD.vowFileUintStoreSump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hsumpPc hword (by jump_dest) hperm (by simp)
  have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop hretPc' (by decide +native) (by simp)

theorem RD.vowFileUintDumpSuccess {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨414⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotWait : fileUintWhat I ≠ fileUintWaitBytes)
    (hnotBump : fileUintWhat I ≠ fileUintBumpBytes)
    (hnotSump : fileUintWhat I ≠ fileUintSumpBytes)
    (hwhat : fileUintWhat I = fileUintDumpBytes) :
    RDret vowBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨8⟩ (fileUintData I)) ByteArray.empty := by
  obtain ⟨_, _, hswitch⟩ := RD.vowFileUintToSwitch hreach hsz68 hsize hauth
  have hwaitNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintWaitBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotWait (by decide +native)
  obtain ⟨_, _, hbumpPc⟩ := RD.vowFileUintSkipWait
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hswitch hwaitNe (by simp)
  have hbumpNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintBumpBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotBump (by decide +native)
  obtain ⟨_, _, hsumpPc⟩ := RD.vowFileUintSkipBump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hbumpPc hbumpNe (by simp)
  have hsumpNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintSumpBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotSump (by decide +native)
  obtain ⟨_, _, hdumpPc⟩ := RD.vowFileUintSkipSump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hsumpPc hsumpNe (by simp)
  have hword :
      calldataWord I.calldata 4 = ABI.bytesToWord fileUintDumpBytes :=
    fileUintWhatWord_eq_of_bytes_eq (by omega) hwhat
  obtain ⟨_, _, hretPc⟩ := RD.vowFileUintStoreDump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hdumpPc hword (by jump_dest) hperm (by simp)
  have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop hretPc' (by decide +native) (by simp)

theorem RD.vowFileUintHumpSuccess {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨414⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotWait : fileUintWhat I ≠ fileUintWaitBytes)
    (hnotBump : fileUintWhat I ≠ fileUintBumpBytes)
    (hnotSump : fileUintWhat I ≠ fileUintSumpBytes)
    (hnotDump : fileUintWhat I ≠ fileUintDumpBytes)
    (hwhat : fileUintWhat I = fileUintHumpBytes) :
    RDret vowBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨11⟩ (fileUintData I)) ByteArray.empty := by
  obtain ⟨_, _, hswitch⟩ := RD.vowFileUintToSwitch hreach hsz68 hsize hauth
  have hwaitNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintWaitBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotWait (by decide +native)
  obtain ⟨_, _, hbumpPc⟩ := RD.vowFileUintSkipWait
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hswitch hwaitNe (by simp)
  have hbumpNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintBumpBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotBump (by decide +native)
  obtain ⟨_, _, hsumpPc⟩ := RD.vowFileUintSkipBump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hbumpPc hbumpNe (by simp)
  have hsumpNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintSumpBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotSump (by decide +native)
  obtain ⟨_, _, hdumpPc⟩ := RD.vowFileUintSkipSump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hsumpPc hsumpNe (by simp)
  have hdumpNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintDumpBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotDump (by decide +native)
  obtain ⟨_, _, hhumpPc⟩ := RD.vowFileUintSkipDump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hdumpPc hdumpNe (by simp)
  have hword :
      calldataWord I.calldata 4 = ABI.bytesToWord fileUintHumpBytes :=
    fileUintWhatWord_eq_of_bytes_eq (by omega) hwhat
  obtain ⟨_, _, hretPc⟩ := RD.vowFileUintStoreHump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hhumpPc hword (by jump_dest) hperm (by simp)
  have hretPc' := hretPc.jumpdest (by decide +native) (by evm_ov)
  exact RD.stop hretPc' (by decide +native) (by simp)

theorem RD.vowFileUintUnrecognizedParamRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨414⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotWait : fileUintWhat I ≠ fileUintWaitBytes)
    (hnotBump : fileUintWhat I ≠ fileUintBumpBytes)
    (hnotSump : fileUintWhat I ≠ fileUintSumpBytes)
    (hnotDump : fileUintWhat I ≠ fileUintDumpBytes)
    (hnotHump : fileUintWhat I ≠ fileUintHumpBytes) :
    RDrev vowBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hswitch⟩ := RD.vowFileUintToSwitch hreach hsz68 hsize hauth
  have hwaitNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintWaitBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotWait (by decide +native)
  obtain ⟨_, _, hbumpPc⟩ := RD.vowFileUintSkipWait
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hswitch hwaitNe (by simp)
  have hbumpNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintBumpBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotBump (by decide +native)
  obtain ⟨_, _, hsumpPc⟩ := RD.vowFileUintSkipBump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hbumpPc hbumpNe (by simp)
  have hsumpNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintSumpBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotSump (by decide +native)
  obtain ⟨_, _, hdumpPc⟩ := RD.vowFileUintSkipSump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hsumpPc hsumpNe (by simp)
  have hdumpNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintDumpBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotDump (by decide +native)
  obtain ⟨_, _, hhumpPc⟩ := RD.vowFileUintSkipDump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hdumpPc hdumpNe (by simp)
  have hhumpNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintHumpBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotHump (by decide +native)
  obtain ⟨_, _, htailPc⟩ := RD.vowFileUintSkipHump
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hhumpPc hhumpNe (by simp)
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  exact RD.vowFileUintUnrecognizedRevert htailPc hmemAuth hread64 (by simp)

theorem vowFileUintBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileUintTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
        (transitionSignature fileUintTransition).paramTypes I.calldata =
          some (fileUintLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨414⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let data := fileUintData I
  let callerSlot := vowCallerWardsSlot I
  let locals := fileUintLocals I
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have henc : returnEquiv ByteArray.empty none fileUintTransition.returnType := by
    rw [show fileUintTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by decide +native)
  by_cases hauthEvm : vowSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
    by_cases hwait : fileUintWhat I = fileUintWaitBytes
    · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨7⟩ data
      have hbody :
          ExecTransitionBody config contract evm0 locals fileUintTransition.body
            (.returned { contract := contract, locals := locals } evm1 none) := by
        simpa [evm0, evm1, locals, data] using
          (fileUintWaitSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwait)
      have hret := RD.vowFileUintWaitSuccess hreach hperm hsz68 hsize hauthSolc hwait
      have hcreated :
          (cA, sstoreAccountMap I.codeOwner σ_evm ⟨7⟩ data).1 = evm1.createdAccounts := by
        simp [evm1, evm0, initState, storageStore_createdAccounts]
      have haccounts :
          accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨7⟩ data)
            evm1.accountMap := by
        simpa [evm1, evm0, initState, storageStore_accountMap, data] using
          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨7⟩ data hAccounts
      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
        hcreated haccounts henc
    · by_cases hbump : fileUintWhat I = fileUintBumpBytes
      · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
        let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨10⟩ data
        have hbody :
            ExecTransitionBody config contract evm0 locals fileUintTransition.body
              (.returned { contract := contract, locals := locals } evm1 none) := by
          simpa [evm0, evm1, locals, data] using
            (fileUintBumpSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
              (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwait hbump)
        have hret := RD.vowFileUintBumpSuccess hreach hperm hsz68 hsize hauthSolc hwait
          hbump
        have hcreated :
            (cA, sstoreAccountMap I.codeOwner σ_evm ⟨10⟩ data).1 =
              evm1.createdAccounts := by
          simp [evm1, evm0, initState, storageStore_createdAccounts]
        have haccounts :
            accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨10⟩ data)
              evm1.accountMap := by
          simpa [evm1, evm0, initState, storageStore_accountMap, data] using
            accountMapEquiv_sstoreAccountMap I.codeOwner ⟨10⟩ data hAccounts
        exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
          hcreated haccounts henc
      · by_cases hsump : fileUintWhat I = fileUintSumpBytes
        · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
          let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨9⟩ data
          have hbody :
              ExecTransitionBody config contract evm0 locals fileUintTransition.body
                (.returned { contract := contract, locals := locals } evm1 none) := by
            simpa [evm0, evm1, locals, data] using
              (fileUintSumpSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
                (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hwait hbump
                hsump)
          have hret := RD.vowFileUintSumpSuccess hreach hperm hsz68 hsize hauthSolc
            hwait hbump hsump
          have hcreated :
              (cA, sstoreAccountMap I.codeOwner σ_evm ⟨9⟩ data).1 =
                evm1.createdAccounts := by
            simp [evm1, evm0, initState, storageStore_createdAccounts]
          have haccounts :
              accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨9⟩ data)
                evm1.accountMap := by
            simpa [evm1, evm0, initState, storageStore_accountMap, data] using
              accountMapEquiv_sstoreAccountMap I.codeOwner ⟨9⟩ data hAccounts
          exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
            hcreated haccounts henc
        · by_cases hdump : fileUintWhat I = fileUintDumpBytes
          · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
            let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨8⟩ data
            have hbody :
                ExecTransitionBody config contract evm0 locals fileUintTransition.body
                  (.returned { contract := contract, locals := locals } evm1 none) := by
              simpa [evm0, evm1, locals, data] using
                (fileUintDumpSourceBody (cA := cA) (gh := gh) (bl := bl)
                  (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                  hwv hauthSolm hwait hbump hsump hdump)
            have hret := RD.vowFileUintDumpSuccess hreach hperm hsz68 hsize hauthSolc
              hwait hbump hsump hdump
            have hcreated :
                (cA, sstoreAccountMap I.codeOwner σ_evm ⟨8⟩ data).1 =
                  evm1.createdAccounts := by
              simp [evm1, evm0, initState, storageStore_createdAccounts]
            have haccounts :
                accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨8⟩ data)
                  evm1.accountMap := by
              simpa [evm1, evm0, initState, storageStore_accountMap, data] using
                accountMapEquiv_sstoreAccountMap I.codeOwner ⟨8⟩ data hAccounts
            exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
              hcreated haccounts henc
          · by_cases hhump : fileUintWhat I = fileUintHumpBytes
            · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨11⟩ data
              have hbody :
                  ExecTransitionBody config contract evm0 locals fileUintTransition.body
                    (.returned { contract := contract, locals := locals } evm1 none) := by
                simpa [evm0, evm1, locals, data] using
                  (fileUintHumpSourceBody (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hauthSolm hwait hbump hsump hdump hhump)
              have hret := RD.vowFileUintHumpSuccess hreach hperm hsz68 hsize
                hauthSolc hwait hbump hsump hdump hhump
              have hcreated :
                  (cA, sstoreAccountMap I.codeOwner σ_evm ⟨11⟩ data).1 =
                    evm1.createdAccounts := by
                simp [evm1, evm0, initState, storageStore_createdAccounts]
              have haccounts :
                  accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨11⟩ data)
                    evm1.accountMap := by
                simpa [evm1, evm0, initState, storageStore_accountMap, data] using
                  accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩ data hAccounts
              exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
                hcreated haccounts henc
            · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
              have hbody :
                  ExecTransitionBody config contract evm0 locals fileUintTransition.body
                    .reverted := by
                simpa [evm0, locals] using
                  (fileUintUnrecognizedSourceBody (cA := cA) (gh := gh) (bl := bl)
                    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
                    hwv hauthSolm hwait hbump hsump hdump hhump)
              have hrev := RD.vowFileUintUnrecognizedParamRevert hreach hsz68 hsize
                hauthSolc hwait hbump hsump hdump hhump
              exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : vowSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody : ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
      have hguard := vowAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals, fileUintLocals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [
          .ite
            (.binary .eq (.var "what") waitParamLit)
            [ .assign .storage waitRef (.var "data") ]
            [ .ite
                (.binary .eq (.var "what") bumpParamLit)
                [ .assign .storage bumpRef (.var "data") ]
                [ .ite
                    (.binary .eq (.var "what") sumpParamLit)
                    [ .assign .storage sumpRef (.var "data") ]
                    [ .ite
                        (.binary .eq (.var "what") dumpParamLit)
                        [ .assign .storage dumpRef (.var "data") ]
                        [ .ite
                            (.binary .eq (.var "what") humpParamLit)
                            [ .assign .storage humpRef (.var "data") ]
                            [ .require (.boolLit false) ] ] ] ] ] ])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, fileUintTransition, nonpayable, auth, evm0, locals] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
    have hrev := RD.vowFileUintAuthRevert hreach hsz68 hsize hauthSolc
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFileUintBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  exact vowFileUintBodyCore (sel := vowSelWord I) hcode hwv hperm hsz68 hsize
    (vowDispatch_fileUint hsel)
    (by simpa [fileUintLocals] using vowDecode_fileUint_ok (I := I) hsz68)
    (vowReachFileUintBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts

theorem vowFileUintShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsel : selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach :=
    vowReachFileUintBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vowBytecode) (sel := vowSelWord I) (entry := ⟨414⟩) (ret := ⟨412⟩)
    (decoded := ⟨436⟩) (need := ⟨64⟩) hreach
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) (by decide +native)
    (by decide +native) (by decide +native) (by decide +native) hlt
  exact hrev.reEquivDecodingFailed hcode (vowDispatch_fileUint hsel)
    (vowDecode_fileUint_none_short hsz4 hshort)

end Benchmarks.Dss.Vow
