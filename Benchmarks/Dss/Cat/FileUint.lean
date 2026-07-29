import Benchmarks.Dss.Cat.Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Cat

/-! ## `file(bytes32,uint256)` — LOW-LOW dispatch arm 1, entry ⟨304⟩

Single recognized parameter `"box"` (slot 5, scalar `uint256`). `what=="box"` stores
`box := data` and returns; any other `what` reverts with `"Cat/file-unrecognized-param"`;
auth-fail reverts with `"Cat/not-authorized"`. -/

abbrev fileUintWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileUintData (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileUintBoxBytes : List UInt8 :=
  [98, 111, 120, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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

/-! ### ABI-decode helpers (contract-agnostic, ported from `Vow/FileUint.lean`) -/

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
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by native_decide]
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
  rw [show abiTupleHeadSize? [abiBytes32, abiUInt256] = some 64 by native_decide]
  simp only [bind, Option.bind]
  by_cases hbytes : (cd.toList.drop 4).length < 64
  · rw [if_pos hbytes]
  · rw [if_neg hbytes]
    rw [decodeABIValues_bytes32_uint256_legacy_none_short (bytes := cd.toList.drop 4) (by
      rw [List.length_drop, htlen]
      omega)]

/-! ### Locals + expression evaluation -/

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

theorem assign_fileUintBoxStorage (evm : EVM.State) {locals : Store} (data : UInt256)
    (hbase : locals.get? "box" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ data
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage boxRef (.int (Int.ofNat data.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm boxRef =
        .ok { base := "box", steps := [] } := by
    simp [boxRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨5⟩) (.int (Int.ofNat data.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨5⟩ data
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨5⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

/-! ### Dispatch, ABI decode, reachability -/

theorem catDispatch_fileUint {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩) :
    dispatchMsg contract I.calldata = some fileUintTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [biteTransition, boxTransition, cageTransition, clawTransition, denyTransition,
      fileAddressTransition, fileIlkFlipTransition, fileIlkUintTransition])
    (post := [ilksTransition, litterTransition, liveTransition, relyTransition,
      vatTransition, vowTransition, wardsTransition])
    (ti := fileUintTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x29, 0xae, 0x81, 0x14]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, biteSelectorBytes, boxSelectorBytes, cageSelectorBytes,
        clawSelectorBytes, denySelectorBytes, fileAddressSelectorBytes,
        fileIlkFlipSelectorBytes, fileIlkUintSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, fileUintSelectorBytes]
    exact hsel

theorem catDecode_fileUint_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata =
        some (fileUintLocals I) := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int,
    fileUintWhat, fileUintData, abiBytes32, abiBytes32Width, abiUInt256, fileUintLocals] using
    (decodeCalldata_legacyBytes32_uint256_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem catDecode_fileUint_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
      (transitionSignature fileUintTransition).paramTypes I.calldata = none := by
  simpa [config, fileUintTransition, bytes32, bytes32Width, uint256, uint256Int, abiBytes32,
    abiBytes32Width, abiUInt256] using
    (decodeCalldata_legacyBytes32_uint256_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

theorem catReachFileUintBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨304⟩ [catSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : catSelWord I = ⟨699302164⟩ :=
    catSelWord_eq_of_beq I hsz 0x29 0xae 0x81 0x14 ⟨699302164⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat catBytecode catRootSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat catBytecode catLowSplitPc) (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 1 →
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc j))
        (catSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat catBytecode (nthArmPc catBytecode catLowLowFirstArmPc 1))
        (catSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact catReachLowLowBody 1 (by omega) ⟨304⟩ hcode hwv hsz hsize hroot hlow heq0
    htake (by jump_dest) (by native_decide)

/-! ### Entry bridge: decode length check + decode-to-routine -/

theorem RD.catFileUintDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨326⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = catBytecode)
    (hroutine : (D_J code 0).contains ⟨1035⟩ = true)
    (hov : R.length + 8 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨1035⟩
      (calldataWord ee.calldata 36 :: calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd327 := h.jumpdest (by native_decide) (by evm_ov)
  have rd328 := rd327.pop (by native_decide) (by evm_ov)
  have rd329 := rd328.dup1 (by native_decide) (by evm_ov)
  have rd330 := rd329.calldataload (by native_decide) (by evm_ov)
  have rd331 := rd330.swap1 (by native_decide) (by evm_ov)
  have rd333 := rd331.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd334 := rd333.add (by native_decide) (by evm_ov)
  have rd335 := rd334.calldataload (by native_decide) (by evm_ov)
  have rd338 := rd335.push2 ⟨1035⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (⟨36⟩ : UInt256).toNat = 36 from by decide]
      using rd338.jump (by native_decide) hroutine (by evm_ov)⟩

theorem RD.catFileUintToSwitch {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨304⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩) :
    ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨1124⟩
      (fileUintData I :: calldataWord I.calldata 4 :: ⟨302⟩ :: sel :: [])
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := catBytecode) (sel := sel) (entry := ⟨304⟩) (ret := ⟨302⟩)
    (decoded := ⟨326⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.catFileUintDecodeToRoutine
    (code := catBytecode) (ret := ⟨302⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  obtain ⟨_, _, hafterAuth⟩ := RD.catAuthCheckOk
    (code := catBytecode) (pc := ⟨1035⟩) (okPc := ⟨1124⟩)
    (key := fileUintData I) (ret := calldataWord I.calldata 4) (R := [⟨302⟩, sel])
    (by simpa [fileUintData] using hroutine)
    (by
      unfold catAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauth (by jump_dest) (by simp)
  exact ⟨_, _, hafterAuth⟩

theorem RD.catFileUintAuthRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨304⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := catBytecode) (sel := sel) (entry := ⟨304⟩) (ret := ⟨302⟩)
    (decoded := ⟨326⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.catFileUintDecodeToRoutine
    (code := catBytecode) (ret := ⟨302⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact RD.catAuthCheckRevert
    (code := catBytecode) (pc := ⟨1035⟩) (okPc := ⟨1124⟩)
    (key := fileUintData I) (ret := calldataWord I.calldata 4) (R := [⟨302⟩, sel])
    (by simpa [fileUintData] using hroutine)
    (by
      unfold catAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf catAuthTailPc catNotAuthorizedRawWord
      repeat' first | apply And.intro | native_decide)
    hauth (by simp)

/-! ### `"box"` switch (pc ⟨1124⟩): store `box := data` or skip to unrecognized-param revert -/

theorem RD.catFileUintStoreBox {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD catBytecode ee g s0 ⟨1124⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileUintBoxBytes)
    (hret : (D_J catBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ret (sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨5⟩ data) k' C' := by
  have rd1125 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1126 := rd1125.dup2 (by native_decide) (by evm_ov)
  have rd1130 := rd1126.pushConst (⟨806383⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd1132 := rd1130.push1 ⟨235⟩ (by native_decide) (by evm_ov)
  have rd1133 := rd1132.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨806383⟩ ⟨235⟩ = ABI.bytesToWord fileUintBoxBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd1133
  have rd1134 := rd1133.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd1134
  have rd1135 := rd1134.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1135
  have rd1138 := rd1135.push2 ⟨953⟩ (by native_decide) (by evm_ov)
  have rd1139 := rd1138.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1141 := rd1139.push1 ⟨5⟩ (by native_decide) (by evm_ov)
  have rd1142 := rd1141.dup2 (by native_decide) (by evm_ov)
  have rd1143 := rd1142.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1144⟩ := rd1143.sstore hperm (by native_decide) (by evm_ov)
  have rd1145 := rd1144.jumpdest (by native_decide) (by evm_ov)
  have rd1146 := rd1145.pop (by native_decide) (by evm_ov)
  have rd1147 := rd1146.pop (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1147.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.catFileUintSkipBox {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD catBytecode ee g s0 ⟨1124⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileUintBoxBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD catBytecode ee g s0 ⟨953⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd1125 := h.jumpdest (by native_decide) (by evm_ov)
  have rd1126 := rd1125.dup2 (by native_decide) (by evm_ov)
  have rd1130 := rd1126.pushConst (⟨806383⟩ : UInt256) (width := 3) (op := .PUSH3)
    (by decide) (by native_decide) (by evm_ov)
  have rd1132 := rd1130.push1 ⟨235⟩ (by native_decide) (by evm_ov)
  have rd1133 := rd1132.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨806383⟩ ⟨235⟩ = ABI.bytesToWord fileUintBoxBytes := by
    native_decide
  rw [hconst] at rd1133
  have rd1134 := rd1133.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileUintBoxBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd1134
  have rd1135 := rd1134.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1135
  have rd1138 := rd1135.push2 ⟨953⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1138.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

/-! ### `"Cat/file-unrecognized-param"` revert (pc ⟨953⟩) -/

abbrev catFileUintUnrecognizedRawWord : UInt256 :=
  ⟨30477146900841294791694925804285198379011926721857912948232373309380849827840⟩

theorem RD.catFileUintUnrecognizedRevert {g : Sat256} {s0 : State} {ee : ExecutionEnv}
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
  have rdRaw := rdPrefix.pushConst catFileUintUnrecognizedRawWord
    (width := 32) (op := .PUSH32) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  exact evm_run rdRaw with [
    raw push1 ⟨68⟩ (by native_decide) (by evm_ov),
    raw dup3 (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw mstore 3 (solcErrorStringMem3 ⟨27⟩ catFileUintUnrecognizedRawWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64 ⟨27⟩ catFileUintUnrecognizedRawWord hmem hread64)
      (by decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw dup2 (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw sub (by native_decide) (by evm_ov),
    raw push1 ⟨100⟩ (by native_decide) (by evm_ov),
    raw add (by native_decide) (by evm_ov),
    raw swap1 (by native_decide) (by evm_ov),
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

/-! ### Success + revert reachability wrappers -/

theorem RD.catFileUintBoxSuccess {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨304⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hwhat : fileUintWhat I = fileUintBoxBytes) :
    RDret catBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨5⟩ (fileUintData I)) ByteArray.empty := by
  obtain ⟨_, _, hswitch⟩ := RD.catFileUintToSwitch hreach hsz68 hsize hauth
  have hword :
      calldataWord I.calldata 4 = ABI.bytesToWord fileUintBoxBytes :=
    fileUintWhatWord_eq_of_bytes_eq (by omega) hwhat
  obtain ⟨_, _, hretPc⟩ := RD.catFileUintStoreBox
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨302⟩)
    (sel := sel) (R := []) hswitch hword (by jump_dest) hperm (by simp)
  have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop hretPc' (by native_decide) (by simp)

theorem RD.catFileUintUnrecognizedParamRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD catBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨304⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotBox : fileUintWhat I ≠ fileUintBoxBytes) :
    RDrev catBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hswitch⟩ := RD.catFileUintToSwitch hreach hsz68 hsize hauth
  have hboxNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileUintBoxBytes :=
    fileUintWhatWord_ne_of_bytes_ne (by omega) hnotBox (by native_decide)
  obtain ⟨_, _, htailPc⟩ := RD.catFileUintSkipBox
    (data := fileUintData I) (what := calldataWord I.calldata 4) (ret := ⟨302⟩)
    (sel := sel) (R := []) hswitch hboxNe (by simp)
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  exact RD.catFileUintUnrecognizedRevert htailPc hmemAuth hread64 (by simp)

/-! ### Solm-side source bodies -/

theorem fileUintBoxSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileUintWhat I = fileUintBoxBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨5⟩ (fileUintData I)
    ExecTransitionBody config contract evm0 locals fileUintTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileUintLocals]) hauth
  have hcond :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") boxParamLit) = .ok (.bool true) := by
    simpa [boxParamLit, fileUintBoxBytes] using
      (evalExpr_fileUintWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintBoxBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.int (Int.ofNat (fileUintData I).toNat)) := by
    simpa [locals] using
      (evalExpr_fileUintData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals]))
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage boxRef (.int (Int.ofNat (fileUintData I).toNat)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1] using
      (assign_fileUintBoxStorage evm0 (locals := locals) (fileUintData I)
        (by simp [locals, fileUintLocals]))
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage boxRef (.var "data")]
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

theorem fileUintUnrecognizedSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : catSlotWord (catCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotBox : fileUintWhat I ≠ fileUintBoxBytes) :
    let locals := fileUintLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
  intro locals evm0
  have hguard := catAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileUintLocals]) hauth
  have hbox :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") boxParamLit) = .ok (.bool false) := by
    simpa [boxParamLit, fileUintBoxBytes] using
      (evalExpr_fileUintWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileUintBoxBytes) (by simpa [locals] using fileUintLocals_get_what I)
        hnotBox)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileUintTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hbox
      (ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)))
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

/-! ### Body core + top-level -/

theorem catFileUintBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = catBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileUintTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileUintTransition.params.map Param.name)
        (transitionSignature fileUintTransition).paramTypes I.calldata =
          some (fileUintLocals I))
    (hreach : ∃ k C, RD catBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨304⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let data := fileUintData I
  let callerSlot := catCallerWardsSlot I
  let locals := fileUintLocals I
  have hcallerWord : catSlotWord callerSlot σ_evm I = catSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have henc : returnEquiv ByteArray.empty none fileUintTransition.returnType := by
    rw [show fileUintTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  by_cases hauthEvm : catSlotWord callerSlot σ_evm I = ⟨1⟩
  · have hauthSolm : catSlotWord callerSlot σ_solm I = ⟨1⟩ := by
      rw [← hcallerWord]
      exact hauthEvm
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
      simpa [callerSlot, catCallerWardsSlot, catSlotWord] using hauthEvm
    by_cases hbox : fileUintWhat I = fileUintBoxBytes
    · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨5⟩ data
      have hbody :
          ExecTransitionBody config contract evm0 locals fileUintTransition.body
            (.returned { contract := contract, locals := locals } evm1 none) := by
        simpa [evm0, evm1, locals, data] using
          (fileUintBoxSourceBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm)
            (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hauthSolm hbox)
      have hret := RD.catFileUintBoxSuccess hreach hperm hsz68 hsize hauthSolc hbox
      have hcreated :
          (cA, sstoreAccountMap I.codeOwner σ_evm ⟨5⟩ data).1 = evm1.createdAccounts := by
        simp [evm1, evm0, initState, storageStore_createdAccounts]
      have haccounts :
          accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨5⟩ data)
            evm1.accountMap := by
        simpa [evm1, evm0, initState, storageStore_accountMap, data] using
          accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩ data hAccounts
      exact hret.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
        hcreated haccounts henc
    · let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
      have hbody :
          ExecTransitionBody config contract evm0 locals fileUintTransition.body
            .reverted := by
        simpa [evm0, locals] using
          (fileUintUnrecognizedSourceBody (cA := cA) (gh := gh) (bl := bl)
            (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
            hwv hauthSolm hbox)
      have hrev := RD.catFileUintUnrecognizedParamRevert hreach hsz68 hsize hauthSolc hbox
      exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody
  · have hauthSolm : catSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
      intro hsolm
      exact hauthEvm (by rw [hcallerWord, hsolm])
    let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
    have hbody :
        ExecTransitionBody config contract evm0 locals fileUintTransition.body .reverted := by
      have hguard := catAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
        (g := Sat256.ofUInt256 g) (locals := locals)
        (by simp [locals, fileUintLocals]) hauthSolm
      have hblock := nonpayableSecondRequireReverts
        (cfg := config) (solm := { contract := contract, locals := locals })
        (evm := evm0)
        (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
        (rest := [
          .ite
            (.binary .eq (.var "what") boxParamLit)
            [ .assign .storage boxRef (.var "data") ]
            [ .require (.boolLit false) ] ])
        (by simp [evm0, initState]; exact hwv)
        hguard
      simpa [ExecTransitionBody, fileUintTransition, nonpayable, auth, evm0, locals] using
        ExecFuncBody.execBlockRevert hblock
    have hauthSolc :
        solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
      simpa [callerSlot, catCallerWardsSlot, catSlotWord] using hauthEvm
    have hrev := RD.catFileUintAuthRevert hreach hsz68 hsize hauthSolc
    exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem catFileUintShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsel : selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach :=
    catReachFileUintBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := catBytecode) (sel := catSelWord I) (entry := ⟨304⟩) (ret := ⟨302⟩)
    (decoded := ⟨326⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (catDispatch_fileUint hsel)
    (catDecode_fileUint_none_short hsz4 hshort)

theorem catFileUintBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = catBytecode)
    (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size :=
    calldata_size_ge_of_selIs I ⟨#[0x29, 0xae, 0x81, 0x14]⟩ (by native_decide) hsel
  by_cases hshort : I.calldata.size < 68
  · exact catFileUintShort hcode hsize hperm hwv hsz hshort hsel hAccounts
  · have hsz68 : 68 ≤ I.calldata.size := by omega
    exact catFileUintBodyCore (sel := catSelWord I) hcode hwv hperm hsz68 hsize
      (catDispatch_fileUint hsel)
      (catDecode_fileUint_ok hsz68)
      (catReachFileUintBody (g := Sat256.ofUInt256 g) hcode hwv hsz hsize hsel)
      hAccounts

end Benchmarks.Dss.Cat
