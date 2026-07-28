import Benchmarks.Dss.Vow.Arithmetic
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `kiss(uint256)` -/

abbrev kissRad (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev kissLocals (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "rad" (.int (Int.ofNat (kissRad I).toNat))

abbrev kissVatAddress (σ : AccountMap) (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (vowAddressReturnWord ⟨1⟩ σ I).toNat

abbrev kissDaiTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (vowSlotWord ⟨1⟩ σ I) solcAddrMask

abbrev kissDaiSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨907205027⟩ ⟨225⟩

abbrev kissDaiSelector : ByteArray :=
  ⟨#[0x6c, 0x25, 0xb3, 0x46]⟩

noncomputable def kissDaiSelectorMem : ByteArray :=
  kissDaiSelectorShifted.toByteArray.write 0 solcFreePtrMem 128 32

noncomputable def kissDaiCalldataMem (I : ExecutionEnv) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0 kissDaiSelectorMem 132 32

noncomputable def kissDaiOutPtr (I : ExecutionEnv) : UInt256 :=
  if (⟨64⟩ : UInt256).toNat ≥ (kissDaiCalldataMem I).size
      ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then
    ⟨0⟩
  else
    UInt256.ofNat
      (fromByteArrayBigEndian ((kissDaiCalldataMem I).readWithPadding
        (⟨64⟩ : UInt256).toNat 32))

noncomputable def kissDaiInSize (I : ExecutionEnv) : UInt256 :=
  UInt256.add (UInt256.sub ⟨128⟩ (kissDaiOutPtr I)) ⟨36⟩

noncomputable def kissDaiEndPtr (_I : ExecutionEnv) : UInt256 :=
  (⟨128⟩ : UInt256) + ⟨36⟩

theorem kissDaiSelectorMem_size : kissDaiSelectorMem.size = 160 :=
  solcReturnMem_size _

theorem kissDaiSelectorMem_read64 :
    kissDaiSelectorMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  solcReturnMem_read64 _

theorem kissDaiCalldataMem_size (I : ExecutionEnv) :
    (kissDaiCalldataMem I).size = 164 := by
  unfold kissDaiCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [kissDaiSelectorMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, kissDaiSelectorMem_size, toByteArray_size]
  omega

theorem kissDaiCalldataMem_read64 (I : ExecutionEnv) :
    (kissDaiCalldataMem I).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold kissDaiCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [kissDaiSelectorMem_size]; omega) (by omega), kissDaiSelectorMem_read64]

theorem kissDaiWrite_size (I : ExecutionEnv) (o : ByteArray) (L : ℕ)
    (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (kissDaiCalldataMem I) 128 L).size = 164 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact kissDaiCalldataMem_size I
  · rw [write_eq_gen o (kissDaiCalldataMem I) 128 L (by omega) hLo
      (by rw [kissDaiCalldataMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, kissDaiCalldataMem_size]
    omega

theorem kissDaiWrite_read64 (I : ExecutionEnv) (o : ByteArray) (L : ℕ)
    (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (kissDaiCalldataMem I) 128 L).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact kissDaiCalldataMem_read64 I
  · rw [write_read_below_gen o (kissDaiCalldataMem I) 128 L 64 (by omega) hLo
      (by rw [kissDaiCalldataMem_size]; omega) (by omega), kissDaiCalldataMem_read64]

theorem kissDaiWrite_read128_32 (I : ExecutionEnv) (o : ByteArray)
    (ho32 : 32 ≤ o.size) :
    (o.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding 128 32 =
      o.extract 0 32 :=
  write32_read_back o (kissDaiCalldataMem I) 128 ho32
    (by rw [kissDaiCalldataMem_size]; omega)

theorem kissDaiMin32_toNat_of_ge {n : ℕ}
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

theorem kissDaiMin32_toNat_of_lt {n : ℕ} (h : n < 32) :
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

theorem kissDaiDecode_ok {o : ByteArray} (ho32 : 32 ≤ o.size) :
    config.externalABI.decode? "dai" o =
      some [.int (Int.ofNat (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat)] := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_ok (returndata := o) ho32
  have hlt := fromByteArrayBigEndian_extract0_32_lt (returndata := o) ho32
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 o =
        some (.int (Int.ofNat (fromByteArrayBigEndian (o.extract 0 32)))) := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 o =
    some [.int (Int.ofNat (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat)]
  unfold decodeReturn?
  rw [hdec']
  simp [UInt256.toNat_ofNat_of_lt hlt, Int.ofNat_eq_natCast]

theorem kissDaiDecode_none_short {o : ByteArray} (hshort : o.size < 32) :
    config.externalABI.decode? "dai" o = none := by
  have hdec := decodeReturnValueWithMode_legacy_uint256_none_short (returndata := o) hshort
  have hdec' :
      ABI.decodeReturnValueWithMode? DecodeMode.legacySolc05 uint256 o = none := by
    simpa [uint256, uint256Int, abiUInt256] using hdec
  change decodeReturn? uint256 o = none
  unfold decodeReturn?
  rw [hdec']
  rfl

theorem kissDaiSelectorMem_selector :
    kissDaiSelectorMem.extract 128 132 = kissDaiSelector := by
  rw [show kissDaiSelectorMem = solcReturnMem kissDaiSelectorShifted from rfl,
    solcReturnMem_eq,
    extract_append_right_window _ _ _ _ (by rw [solcFreePtrMem_pad_size]),
    solcFreePtrMem_pad_size, show (128 : ℕ) - 128 = 0 from rfl,
    show (132 : ℕ) - 128 = 4 from rfl, toByteArray_eq_toBytesBE]
  native_decide

theorem kissDaiCalldataMem_read128_36 (I : ExecutionEnv) :
    (kissDaiCalldataMem I).readWithPadding 128 36 =
      kissDaiSelector ++ (UInt256.ofNat I.codeOwner.val).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [kissDaiCalldataMem_size]), kissDaiCalldataMem,
    write32_eq _ kissDaiSelectorMem 132 (by rw [toByteArray_size])
      (by rw [kissDaiSelectorMem_size]; omega)]
  have hAsz : (kissDaiSelectorMem.extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, kissDaiSelectorMem_size]
    omega
  have hBsz : (((UInt256.ofNat I.codeOwner.val).toByteArray).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      (kissDaiSelectorMem.extract 0 132 ++
        ((UInt256.ofNat I.codeOwner.val).toByteArray).extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull :
      ((UInt256.ofNat I.codeOwner.val).toByteArray).extract 0 32 =
        (UInt256.ofNat I.codeOwner.val).toByteArray := by
    have h := @ByteArray.extract_zero_size (UInt256.ofNat I.codeOwner.val).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), kissDaiSelectorMem_selector,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem kissDaiOutPtr_eq (I : ExecutionEnv) :
    kissDaiOutPtr I = ⟨128⟩ := by
  unfold kissDaiOutPtr
  exact mloadFreePtrValue (by rw [kissDaiCalldataMem_size]; decide) (by decide)
    (kissDaiCalldataMem_read64 I)

theorem kissDaiInSize_eq (I : ExecutionEnv) :
    kissDaiInSize I = ⟨36⟩ := by
  rw [kissDaiInSize, kissDaiOutPtr_eq]
  native_decide

theorem kissDaiEndPtr_eq (I : ExecutionEnv) :
    kissDaiEndPtr I = ⟨164⟩ := by
  rw [kissDaiEndPtr]
  native_decide

theorem kissVatAddress_eq_daiTarget (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (kissVatAddress σ I) = AccountAddress.ofUInt256 (kissDaiTargetWord σ I) := by
  apply Fin.ext
  simp [kissVatAddress, kissDaiTargetWord, vowAddressReturnWord]
  rfl

theorem kissDaiEncode_eq (I : ExecutionEnv) :
    config.externalABI.encode? "dai" [.address I.codeOwner] =
      some ((kissDaiCalldataMem I).readWithPadding
        (kissDaiOutPtr I).toNat (kissDaiInSize I).toNat) := by
  rw [kissDaiOutPtr_eq, kissDaiInSize_eq]
  change config.externalABI.encode? "dai" [.address I.codeOwner] =
    some ((kissDaiCalldataMem I).readWithPadding 128 36)
  rw [kissDaiCalldataMem_read128_36]
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr,
    vatDaiSelector, selectorBytes, kissDaiSelector]
  rw [show EVM.word (↑I.codeOwner : ℕ) = UInt256.ofNat (↑I.codeOwner : ℕ) from rfl]
  rw [word_toBytesBE_toByteArray_eq_toByteArray]

abbrev kissLocalsVatDai (I : ExecutionEnv) (vatDai : UInt256) : Store :=
  (kissLocals I).insert "vatDai" (.int (Int.ofNat vatDai.toNat))

abbrev kissLocalsVatDaiAshNew (I : ExecutionEnv) (vatDai AshNew : UInt256) : Store :=
  (kissLocalsVatDai I vatDai).insert "AshNew" (.int (Int.ofNat AshNew.toNat))

abbrev kissLocalsDone (I : ExecutionEnv) (vatDai AshNew : UInt256) : Store :=
  (kissLocalsVatDaiAshNew I vatDai AshNew).insert "_healRet" .unit

abbrev kissLocalsAshNew (locals : Store) (AshNew : UInt256) : Store :=
  locals.insert "AshNew" (.int (Int.ofNat AshNew.toNat))

abbrev kissFrameAshNew (locals : Store) (AshNew : UInt256) : Frame :=
  { contract := contract, locals := kissLocalsAshNew locals AshNew }

theorem kissLocals_get_rad (I : ExecutionEnv) :
    (kissLocals I).get? "rad" = some (.int (Int.ofNat (kissRad I).toNat)) := by
  rw [kissLocals, store_get_self]

theorem kissLocalsVatDai_get_rad (I : ExecutionEnv) (vatDai : UInt256) :
    (kissLocalsVatDai I vatDai).get? "rad" =
      some (.int (Int.ofNat (kissRad I).toNat)) := by
  rw [kissLocalsVatDai, store_get_ne _ _ (by decide), kissLocals_get_rad]

theorem kissLocalsVatDai_get_vatDai (I : ExecutionEnv) (vatDai : UInt256) :
    (kissLocalsVatDai I vatDai).get? "vatDai" =
      some (.int (Int.ofNat vatDai.toNat)) := by
  rw [kissLocalsVatDai, store_get_self]

theorem kissLocalsVatDaiAshNew_get_rad (I : ExecutionEnv) (vatDai AshNew : UInt256) :
    (kissLocalsVatDaiAshNew I vatDai AshNew).get? "rad" =
      some (.int (Int.ofNat (kissRad I).toNat)) := by
  rw [kissLocalsVatDaiAshNew, store_get_ne _ _ (by decide),
    kissLocalsVatDai_get_rad]

theorem kissLocalsVatDaiAshNew_get_AshNew (I : ExecutionEnv) (vatDai AshNew : UInt256) :
    (kissLocalsVatDaiAshNew I vatDai AshNew).get? "AshNew" =
      some (.int (Int.ofNat AshNew.toNat)) := by
  rw [kissLocalsVatDaiAshNew, store_get_self]

abbrev kissAshEvaledRef : EvaledStorageRef :=
  { base := "Ash", steps := [] }

abbrev kissVatEvaledRef : EvaledStorageRef :=
  { base := "vat", steps := [] }

theorem evalExpr_kissAshStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "Ash" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage AshRef) =
      .ok (.int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩).toNat)) := by
  rw [evalExpr_storage_scalar (er := kissAshEvaledRef) (t := .int uint256Int)
    (loc := wordLoc ⟨6⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_uint256 _ ⟨6⟩)
  · exact hbase
  · simp [kissAshEvaledRef, AshRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, kissAshEvaledRef]

theorem evalExpr_kissVatStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (AccountAddress.ofNat
        (UInt256.land
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
          solcAddrMask).toNat)) := by
  rw [evalExpr_storage_scalar (er := kissVatEvaledRef) (t := .address)
    (loc := addrLoc ⟨1⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_address_offset0 _ ⟨1⟩)
  · exact hbase
  · simp [kissVatEvaledRef, vatRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, addrSt]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, kissVatEvaledRef]

theorem evalExprs_kissThis (evm : EVM.State) (locals : Store) :
    evalExprs? config { contract := contract, locals := locals } evm [thisAddr] =
      .ok [.address evm.executionEnv.codeOwner] := by
  simp [evalExprs?, thisAddr, evalExpr?, envValue, pure, bind, EvalResult.bind]

theorem evalExprs_kissRad (evm : EVM.State) {I : ExecutionEnv} {locals : Store}
    (hrad : locals.get? "rad" = some (.int (Int.ofNat (kissRad I).toNat))) :
    evalExprs? config { contract := contract, locals := locals } evm [.var "rad"] =
      .ok [.int (Int.ofNat (kissRad I).toNat)] := by
  have hradEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "rad") =
        .ok (.int (Int.ofNat (kissRad I).toNat)) :=
    evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "rad")
      (value := kissRad I) hrad
  simp [evalExprs?, hradEval, bind, EvalResult.bind, pure]

theorem evalExpr_kissVatCodeGuard_true {evm : EVM.State} {locals : Store}
    {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExpr_kissVatCodeGuard_false {evm : EVM.State} {locals : Store}
    {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address target))
    (hcode :
      (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat = 0) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem assign_kissAshStorage (evm : EVM.State) {locals : Store} (AshNew : UInt256)
    (hbase : locals.get? "Ash" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩ AshNew
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage AshRef (.int (Int.ofNat AshNew.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm AshRef =
        .ok kissAshEvaledRef := by
    simp [kissAshEvaledRef, AshRef, evalStorageRef, evalStorageRefSteps,
      EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨6⟩) (.int (Int.ofNat AshNew.toNat)) = some evm' := by
    simpa [evm'] using storageLocStore_uint256 evm ⟨6⟩ AshNew
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨6⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw, kissAshEvaledRef])
    (hstore := hstore)

theorem kissInternalSubReturn (I : ExecutionEnv) (evm : EVM.State)
    {locals : Store} {AshVal AshNew : UInt256}
    (hAshLoad :
      Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩ = AshVal)
    (hrad : locals.get? "rad" = some (.int (Int.ofNat (kissRad I).toNat)))
    (hbaseAsh : locals.get? "Ash" = none)
    (hAshNew : AshNew = UInt256.sub AshVal (kissRad I))
    (hle : (kissRad I).toNat ≤ AshVal.toNat) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "sub" [.storage AshRef, .var "rad"] "AshNew")
      (.ok (kissFrameAshNew locals AshNew) evm) := by
  have hAsh :
      evalExpr? config { contract := contract, locals := locals } evm (.storage AshRef) =
        .ok (.int (Int.ofNat AshVal.toNat)) := by
    simpa [hAshLoad] using evalExpr_kissAshStorage (evm := evm) (locals := locals) hbaseAsh
  have hradEval :
      evalExpr? config { contract := contract, locals := locals } evm (.var "rad") =
        .ok (.int (Int.ofNat (kissRad I).toNat)) :=
    evalExpr_varUInt256 (evm := evm) (locals := locals) (name := "rad")
      (value := kissRad I) hrad
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm
        [.storage AshRef, .var "rad"] =
          .ok [.int (Int.ofNat AshVal.toNat), .int (Int.ofNat (kissRad I).toNat)] := by
    simp [evalExprs?, hAsh, hradEval, bind, EvalResult.bind, pure]
  have hbind :
      bindParams? subFunction.params
        [.int (Int.ofNat AshVal.toNat), .int (Int.ofNat (kissRad I).toNat)] =
          some (uintBinaryLocals AshVal (kissRad I)) := by
    simp [subFunction, uint256, bindParams?, uintBinaryLocals]
  have hbody := execSubFunctionReturn (evm := evm) (x := AshVal) (y := kissRad I)
    (diff := AshNew) hAshNew hle
  simpa [kissFrameAshNew, kissLocalsAshNew, resumeAfterInternalCall] using
    (internalCallFunctionReturn
      (cfg := config) (caller := { contract := contract, locals := locals })
      (evm := evm) (calleeEvm := evm) (name := "sub") (retVar := "AshNew")
      (args := [.storage AshRef, .var "rad"])
      (argVals := [.int (Int.ofNat AshVal.toNat), .int (Int.ofNat (kissRad I).toNat)])
      (callee := subFunction) (locals := uintBinaryLocals AshVal (kissRad I))
      (calleeSolm := { contract := contract, locals := uintBinaryLocalsZ AshVal (kissRad I) AshNew })
      (value := some [.int (Int.ofNat AshNew.toNat)])
      hargs (by rfl) hbind hbody)

theorem vowDispatch_kiss {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0x25, 0x06, 0x85, 0x5a]⟩) :
    dispatchMsg contract I.calldata = some kissTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition, fileAddressTransition, flapTransition,
      flapperTransition, flogTransition, flopTransition, flopperTransition, healTransition,
      humpTransition])
    (post := [liveTransition, relyTransition, sinTransition, sumpTransition, vatTransition,
      waitTransition, wardsTransition])
    (ti := kissTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0x25, 0x06, 0x85, 0x5a]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, fileAddressSelectorBytes, flapSelectorBytes,
        flapperSelectorBytes, flogSelectorBytes, flopSelectorBytes, flopperSelectorBytes,
        healSelectorBytes, humpSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, kissSelectorBytes]
    exact hsel

theorem vowDecode_kiss_ok {I : ExecutionEnv} (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (kissTransition.params.map Param.name)
      (transitionSignature kissTransition).paramTypes I.calldata =
        some (kissLocals I) := by
  simpa [config, kissTransition, kissLocals, kissRad, uint256, uint256Int] using
    (decodeCalldata_legacyUInt256_ok (cd := I.calldata) (x := "rad") hsz36)

theorem vowDecode_kiss_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode config.abiDecodeMode (kissTransition.params.map Param.name)
      (transitionSignature kissTransition).paramTypes I.calldata = none := by
  simpa [config, kissTransition, uint256, uint256Int] using
    (decodeCalldata_legacyUInt256_none_short (cd := I.calldata) (x := "rad") hsz4 hshort)

theorem vowReachKissBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0x25, 0x06, 0x85, 0x5a]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨383⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨621184346⟩ :=
    vowSelWord_eq_of_beq I hsz 0x25 0x06 0x85 0x5a ⟨621184346⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have hlow : UInt256.gt (armSelNat vowBytecode vowLowSplitPc) (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowLowLowFirstArmPc 2))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachLowLowBody 2 (by omega) ⟨383⟩ hcode hwv hsz hsize hroot hlow heq0
    htake (by jump_dest) (by native_decide)

theorem RD.vowKissDecodeToRoutine
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨383⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1549⟩
      [kissRad I, ⟨412⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  let rad := kissRad I
  obtain ⟨_, _, hdecoded⟩ := RD.solcOneAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨383⟩) (ret := ⟨412⟩)
    (decoded := ⟨405⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz36 hsize
  have rd406 := hdecoded.jumpdest (by native_decide) (by evm_ov)
  have rd407 := rd406.pop (by native_decide) (by evm_ov)
  have rd408 := rd407.calldataload (by native_decide) (by evm_ov)
  have rd411 := rd408.push2 ⟨1549⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [rad, kissRad, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using rd411.jump (by native_decide) (by jump_dest) (by evm_ov)⟩

abbrev vowNotEnoughAshRawWord : UInt256 :=
  ⟨941198294658618934345303558433343980449389⟩

theorem RD.vowKissNotEnoughAsh
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨383⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hnotEnough : (vowSlotWord ⟨6⟩ σ I).toNat < (kissRad I).toNat) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  obtain ⟨_, _, hroutine⟩ := RD.vowKissDecodeToRoutine hreach hsz36 hsize
  have rd1550 := hroutine.jumpdest (by native_decide) (by evm_ov)
  have rd1552 := rd1550.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1553⟩ := rd1552.sload (by native_decide) (by evm_ov)
  have rd1554 := rd1553.dup2 (by native_decide) (by evm_ov)
  have rd1555₀ := rd1554.gt (by native_decide) (by evm_ov)
  have hgt :
      UInt256.gt (kissRad I)
        (Option.option ⟨0⟩ (fun ac => ac.storage.findD ⟨6⟩ ⟨0⟩) (σ.find? I.codeOwner)) =
        ⟨1⟩ :=
    ugt_one (by simpa [vowSlotWord, solcSlotWord] using hnotEnough)
  have rd1555 := rd1555₀
  rw [hgt] at rd1555
  have rd1556₀ := rd1555.iszero (by native_decide) (by evm_ov)
  have rd1556 := rd1556₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1556
  have rd1559 := rd1556.push2 ⟨1625⟩ (by native_decide) (by evm_ov)
  have rdTail₀ := rd1559.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  exact RD.solcErrorStringRevertTail
    (pc := ⟨1560⟩) (len := ⟨18⟩) (rawWord := vowNotEnoughAshRawWord)
    (shift := ⟨115⟩) (op := .PUSH18) (width := 18)
    (word := UInt256.shiftLeft vowNotEnoughAshRawWord ⟨115⟩)
    (by simpa [vowSlotWord] using rdTail₀)
    (by
      unfold solcErrorStringRevertTailWf vowNotEnoughAshRawWord
      repeat' first | apply And.intro | native_decide)
    (by decide) (by rfl) solcFreePtrMem_size solcFreePtrMem_read64 (by simp)

theorem RD.vowKissAshEnough
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨383⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1625⟩
      [kissRad I, ⟨412⟩, sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
      (cA, σ) k C := by
  obtain ⟨_, _, hroutine⟩ := RD.vowKissDecodeToRoutine hreach hsz36 hsize
  have rd1550 := hroutine.jumpdest (by native_decide) (by evm_ov)
  have rd1552 := rd1550.push1 ⟨6⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1553⟩ := rd1552.sload (by native_decide) (by evm_ov)
  have rd1554 := rd1553.dup2 (by native_decide) (by evm_ov)
  have rd1555₀ := rd1554.gt (by native_decide) (by evm_ov)
  have hgt :
      UInt256.gt (kissRad I)
        (Option.option ⟨0⟩ (fun ac => ac.storage.findD ⟨6⟩ ⟨0⟩) (σ.find? I.codeOwner)) =
        ⟨0⟩ :=
    ugt_zero (by simpa [vowSlotWord, solcSlotWord] using hashEnough)
  have rd1555 := rd1555₀
  rw [hgt] at rd1555
  have rd1556₀ := rd1555.iszero (by native_decide) (by evm_ov)
  have rd1556 := rd1556₀
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd1556
  have rd1559 := rd1556.push2 ⟨1625⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd1559.jumpiT (by native_decide)
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (by jump_dest) (by evm_ov)⟩

theorem RD.vowKissToDaiExtcodesizeGuard
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨383⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat) :
    ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1688⟩
      (kissDaiTargetWord σ I :: kissDaiTargetWord σ I :: kissDaiOutPtr I :: kissDaiInSize I ::
        kissDaiOutPtr I :: ⟨32⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        kissDaiTargetWord σ I :: kissRad I :: ⟨412⟩ :: sel :: [])
      (kissDaiCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  let target := kissDaiTargetWord σ I
  obtain ⟨_, _, rd1625⟩ := RD.vowKissAshEnough hreach hsz36 hsize hashEnough
  have rd1626 := rd1625.jumpdest (by native_decide) (by evm_ov)
  have rd1628 := rd1626.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd1629⟩ := rd1628.sload (by native_decide) (by evm_ov)
  obtain ⟨k1688, C1688, rd1688⟩ : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1688⟩
      (target :: target :: kissDaiOutPtr I :: kissDaiInSize I ::
        kissDaiOutPtr I :: ⟨32⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        target :: kissRad I :: ⟨412⟩ :: sel :: [])
      (kissDaiCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
    have rdRaw := evm_run rd1629 with [
      push1 ⟨64⟩,
      dup1,
      raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
        mem_cost solcFreePtrMem_mload64 (by decide) (by evm_ov),
      push4 ⟨907205027⟩,
      push1 ⟨225⟩,
      shl,
      dup2,
      raw mstore 6 kissDaiSelectorMem (UInt256.ofNat 5) (by native_decide)
        mem_cost (by rfl) (by decide) (by evm_ov),
      address,
      push1 ⟨4⟩,
      dup3,
      add,
      raw mstore 3 (kissDaiCalldataMem I) (UInt256.ofNat 6) (by native_decide)
        mem_cost (by rfl) (by decide) (by evm_ov),
      swap1,
      raw mload 0 (kissDaiOutPtr I) (UInt256.ofNat 6) (by native_decide)
        mem_cost (by rfl) (by decide) (by evm_ov),
      push1 ⟨1⟩,
      push1 ⟨1⟩,
      push1 ⟨160⟩,
      shl,
      sub,
      swap1,
      swap3,
      and,
      swap2,
      push4 ⟨1814410054⟩,
      swap2,
      push1 ⟨36⟩,
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
      dup7,
      dup1]
    exact ⟨_, _, by
      simpa [target, kissDaiTargetWord, kissDaiSelectorShifted, kissDaiSelectorMem,
        kissDaiCalldataMem, kissDaiOutPtr, kissDaiInSize, kissDaiEndPtr, vowSlotWord,
        solcSlotWord, solcAddrMask] using rdRaw⟩
  exact ⟨k1688, C1688, by simpa [target] using rd1688⟩

theorem RD.vowKissToDaiStaticcall
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨383⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩) :
    ∃ gasWord k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1703⟩
      (gasWord :: kissDaiTargetWord σ I :: kissDaiOutPtr I :: kissDaiInSize I ::
        kissDaiOutPtr I :: ⟨32⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        kissDaiTargetWord σ I :: kissRad I :: ⟨412⟩ :: sel :: [])
      (kissDaiCalldataMem I) (UInt256.ofNat 6) ByteArray.empty (cA, σ) k C := by
  let target := kissDaiTargetWord σ I
  obtain ⟨_, _, rd1688⟩ :=
    RD.vowKissToDaiExtcodesizeGuard hreach hsz36 hsize hashEnough
  obtain ⟨gasWord, k, C, rd1703⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨1688⟩) (okPc := ⟨1700⟩) rd1688
      (by simpa [target] using hcodeSize)
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by evm_ov)
  exact ⟨gasWord, k, C, by simpa [target] using rd1703⟩

theorem RD.vowKissDaiNoCode
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨383⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) = ⟨0⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  let target := kissDaiTargetWord σ I
  obtain ⟨_, _, rd1688⟩ :=
    RD.vowKissToDaiExtcodesizeGuard hreach hsz36 hsize hashEnough
  exact RD.solcExtcodesizeGuardMissing (pc := ⟨1688⟩) (okPc := ⟨1700⟩) rd1688
    (by simpa [target] using hcodeSize)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by simp)

theorem RD.vowKissDaiPostCall
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨383⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (kissDaiTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (o : ByteArray) (A' : Substate) (k C : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1704⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
          kissDaiTargetWord σ I :: kissRad I :: ⟨412⟩ :: sel :: [])
        (o.write 0 (kissDaiCalldataMem I) 128
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 6) o (cA', σ') k C
    ∧ typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, o) false
    ∧ o.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd1703⟩ :=
    RD.vowKissToDaiStaticcall hreach hsz36 hsize hashEnough hcodeSize
  obtain ⟨cA', σ', z, o, A_in, callGas, k1704, C1704, hΘpack, rd1704raw, hosz⟩ :=
    RD.solcStaticcall rd1703 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, o, A', k1704, C1704, ?_, ?_, hosz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          (kissDaiOutPtr I).toNat (kissDaiInSize I).toNat)
          (kissDaiOutPtr I).toNat (⟨32⟩ : UInt256).toNat) = UInt256.ofNat 6 := by
      rw [kissDaiOutPtr_eq, kissDaiInSize_eq]
      native_decide
    have hoff : (kissDaiOutPtr I).toNat = 128 := by
      rw [kissDaiOutPtr_eq]
      native_decide
    have rd1704 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1704⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
          kissDaiTargetWord σ I :: kissRad I :: ⟨412⟩ :: sel :: [])
        (o.write 0 (kissDaiCalldataMem I) (kissDaiOutPtr I).toNat
          (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
        (UInt256.ofNat 6) o (cA', σ') k1704 C1704 :=
      haw ▸ rd1704raw
    rw [hoff] at rd1704
    exact rd1704
  · refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := false) (targetWord := kissDaiTargetWord σ I)
      (mem := kissDaiCalldataMem I) (inOff := kissDaiOutPtr I)
      (inSize := kissDaiInSize I)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (kissVatAddress_eq_daiTarget σ I) (kissDaiEncode_eq I) ?_
    simpa [initState] using hΘ

theorem RD.vowKissDaiCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ} {rest : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1704⟩
      (⟨0⟩ :: rest) mem aw o acc k C)
    (hosz : o.size < UInt256.size)
    (hov : rest.length + 5 ≤ 1024) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨1704⟩) (okPc := ⟨1720⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide) hosz hov

theorem RD.vowKissDaiCallSuccessToDecode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {aw : UInt256} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1704⟩
      (⟨1⟩ :: d0 :: d1 :: d2 :: R) mem aw o acc k C)
    (hov : R.length + 6 ≤ 1024) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1722⟩
      (d0 :: d1 :: d2 :: R) mem aw o acc k' C' := by
  exact RD.solcCallSuccessGuardOk (pc := ⟨1704⟩) (okPc := ⟨1720⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide)
    (by simpa only [List.length_cons] using hov)

theorem RD.vowKissDaiReturnDecodeOk
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel retWord : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1722⟩
      (d0 :: d1 :: d2 :: kissRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hlo : 32 ≤ o.size)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord) :
    ∃ k' C', RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1745⟩
      (retWord :: kissRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k' C' := by
  exact RD.solcUint256ReturnWordDecodeOk (pc := ⟨1722⟩) (okPc := ⟨1742⟩) rd
    hlo hhi
    mem_cost (by decide) hMload64Value hMload128Value mem_cost (by decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) (by native_decide) (by native_decide) (by native_decide) (by evm_ov)

theorem RD.vowKissDaiReturnDecodeShortReverts
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ} {d0 d1 d2 : UInt256}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1722⟩
      (d0 :: d1 :: d2 :: kissRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hshort : o.size < 32)
    (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcUint256ReturnWordDecodeShortReverts (pc := ⟨1722⟩) (okPc := ⟨1742⟩) rd
    hshort hhi
    mem_cost (by decide) hMload64Value
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by simp)

abbrev vowInsufficientSurplusRawWord : UInt256 :=
  ⟨2119390144524583947005257462634672329208299090220883408243⟩

abbrev vowInsufficientSurplusStringWord : UInt256 :=
  UInt256.shiftLeft vowInsufficientSurplusRawWord ⟨64⟩

set_option maxHeartbeats 1000000 in
theorem RD.vowKissInsufficientSurplus
    {cA gh bl σ σ₀ A I} {g : UInt256} {sel vatDai : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem o : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨1745⟩
      (vatDai :: kissRad I :: ⟨412⟩ :: sel :: [])
      mem (UInt256.ofNat 6) o acc k C)
    (hinsuff : vatDai.toNat < (kissRad I).toNat)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  have rd1746 := rd.dup2 (by native_decide) (by evm_ov)
  have rd1747₀ := rd1746.gt (by native_decide) (by evm_ov)
  have hgt : UInt256.gt (kissRad I) vatDai = ⟨1⟩ :=
    ugt_one hinsuff
  have rd1747 := rd1747₀
  rw [hgt] at rd1747
  have rd1748₀ := rd1747.iszero (by native_decide) (by evm_ov)
  have rd1748 := rd1748₀
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd1748
  have rd1751 := rd1748.push2 ⟨1823⟩ (by native_decide) (by evm_ov)
  have rd1752 := rd1751.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd1756 := evm_run rd1752 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost
      (mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64)
      (by decide) (by evm_ov)]
  have rd1760 := rd1756.pushConst (⟨4594637⟩ : UInt256)
    (width := 3) (op := .PUSH3) (by decide) (by native_decide) (by evm_ov)
  have rd1779 := evm_run rd1760 with [
    push1 ⟨229⟩,
    shl,
    dup2,
    raw mstore 0 (solcErrorStringMem0 mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨32⟩,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 0 (solcErrorStringMem1 mem) (UInt256.ofNat 6) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨24⟩,
    push1 ⟨36⟩,
    dup3,
    add,
    raw mstore 3 (solcErrorStringMem2 (⟨24⟩ : UInt256) mem)
      (UInt256.ofNat 7) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov)]
  have rd1804 := rd1779.pushConst vowInsufficientSurplusRawWord
    (width := 24) (op := .PUSH24) (by decide) (by native_decide) (by evm_ov)
  have rd1807₀ := evm_run rd1804 with [
    push1 ⟨64⟩,
    shl]
  have rd1807 := rd1807₀
  rw [show UInt256.shiftLeft vowInsufficientSurplusRawWord ⟨64⟩ =
      vowInsufficientSurplusStringWord from rfl] at rd1807
  exact evm_run rd1807 with [
    push1 ⟨68⟩,
    dup3,
    add,
    raw mstore 3
      (solcErrorStringMem3 (⟨24⟩ : UInt256) vowInsufficientSurplusStringWord mem)
      (UInt256.ofNat 8) (by native_decide) mem_cost (by rfl) (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 8) (by native_decide)
      mem_cost
      (solcErrorStringMem3_mload64_of_size164 (⟨24⟩ : UInt256)
        vowInsufficientSurplusStringWord hmem hread64)
      (by decide) (by evm_ov),
    swap1,
    dup2,
    swap1,
    sub,
    push1 ⟨100⟩,
    add,
    swap1,
    raw rev 0 (by native_decide) mem_cost (by evm_ov)]

theorem vowKissSourceNotEnoughAsh
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hnotEnough : (vowSlotWord ⟨6⟩ σ I).toNat < (kissRad I).toNat) :
    let locals := kissLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals kissTransition.body .reverted := by
  intro locals evm0
  have hrad :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (kissRad I).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm0)
      (locals := locals) (name := "rad") (value := kissRad I)
      (by simp [locals])
  have hash :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage AshRef) =
        .ok (.int (Int.ofNat (vowSlotWord ⟨6⟩ σ I).toNat)) := by
    simpa [evm0, initState, vowSlotWord] using
      evalExpr_kissAshStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hreq :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .le (.var "rad") (.storage AshRef)) = .ok (.bool false) :=
    evalExpr_le_uint256_false hrad hash hnotEnough
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 kissTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreq)
  simpa [ExecTransitionBody, evm0, locals, kissTransition, nonpayable] using
    ExecFuncBody.execBlockRevert hblock

theorem vowKissSourceNoVatCode
    {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat)
    (hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat = 0) :
    let locals := kissLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals kissTransition.body .reverted := by
  intro locals evm0
  have hrad :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (kissRad I).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm0)
      (locals := locals) (name := "rad") (value := kissRad I)
      (by simp [locals])
  have hash :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage AshRef) =
        .ok (.int (Int.ofNat (vowSlotWord ⟨6⟩ σ I).toNat)) := by
    simpa [evm0, initState, vowSlotWord] using
      evalExpr_kissAshStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hreqAsh :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .le (.var "rad") (.storage AshRef)) = .ok (.bool true) :=
    evalExpr_le_uint256_true hrad hash hashEnough
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool false) := by
    exact evalExpr_kissVatCodeGuard_false hvat (by simpa [evm0] using hvatNoCode)
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 kissTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqAsh) ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hguard)
  simpa [ExecTransitionBody, evm0, locals, kissTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowKissSourceDaiCallFailure
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (false, evmDai, out) false) :
    let locals := kissLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals kissTransition.body .reverted := by
  intro locals evm0
  have hrad :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (kissRad I).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm0)
      (locals := locals) (name := "rad") (value := kissRad I)
      (by simp [locals])
  have hash :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage AshRef) =
        .ok (.int (Int.ofNat (vowSlotWord ⟨6⟩ σ I).toNat)) := by
    simpa [evm0, initState, vowSlotWord] using
      evalExpr_kissAshStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hreqAsh :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .le (.var "rad") (.storage AshRef)) = .ok (.bool true) :=
    evalExpr_le_uint256_true hrad hash hashEnough
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallFailure hvat (by simp [evalExpr?, pure]) hargs hcallDai
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 kissTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqAsh) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, locals, kissTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowKissSourceDaiDecodeRevert
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai : EVM.State} {out : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, out) false)
    (hdecDai : config.externalABI.decode? "dai" out = none) :
    let locals := kissLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals kissTransition.body .reverted := by
  intro locals evm0
  have hrad :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (kissRad I).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm0)
      (locals := locals) (name := "rad") (value := kissRad I)
      (by simp [locals])
  have hash :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage AshRef) =
        .ok (.int (Int.ofNat (vowSlotWord ⟨6⟩ σ I).toNat)) := by
    simpa [evm0, initState, vowSlotWord] using
      evalExpr_kissAshStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hreqAsh :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .le (.var "rad") (.storage AshRef)) = .ok (.bool true) :=
    evalExpr_le_uint256_true hrad hash hashEnough
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
          (perm := false))
        .reverted := by
    exact ExecStmt.externalCallReturnDecodeRevert hvat (by simp [evalExpr?, pure])
      hargs hcallDai hdecDai
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 kissTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqAsh) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert hcallStmt
  simpa [ExecTransitionBody, evm0, locals, kissTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowKissSourceInsufficientSurplus
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai : EVM.State} {out : ByteArray}
    {vatDai : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, out) false)
    (hdecDai :
      config.externalABI.decode? "dai" out =
        some [.int (Int.ofNat vatDai.toNat)])
    (hinsuff : vatDai.toNat < (kissRad I).toNat) :
    let locals := kissLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals kissTransition.body .reverted := by
  intro locals evm0
  have hrad :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (kissRad I).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm0)
      (locals := locals) (name := "rad") (value := kissRad I)
      (by simp [locals])
  have hash :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage AshRef) =
        .ok (.int (Int.ofNat (vowSlotWord ⟨6⟩ σ I).toNat)) := by
    simpa [evm0, initState, vowSlotWord] using
      evalExpr_kissAshStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hreqAsh :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .le (.var "rad") (.storage AshRef)) = .ok (.bool true) :=
    evalExpr_le_uint256_true hrad hash hashEnough
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai" (perm := false))
        (.ok { contract := contract, locals := kissLocalsVatDai I vatDai } evmDai) := by
    simpa [locals, kissLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargs hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := kissLocalsVatDai I vatDai } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (kissRad I).toNat)) := by
    exact evalExpr_varUInt256 (evm := evmDai) (locals := kissLocalsVatDai I vatDai)
      (name := "rad") (value := kissRad I) (kissLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := kissLocalsVatDai I vatDai } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    exact evalExpr_varUInt256 (evm := evmDai) (locals := kissLocalsVatDai I vatDai)
      (name := "vatDai") (value := vatDai) (kissLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := kissLocalsVatDai I vatDai } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool false) :=
    evalExpr_le_uint256_false hradDai hvatDai hinsuff
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .le (.var "rad") (.storage AshRef)),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
            (perm := false),
          .require (.binary .le (.var "rad") (.var "vatDai")),
          .internalCall "sub" [.storage AshRef, .var "rad"] "AshNew",
          .assign .storage AshRef (.var "AshNew"),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "heal" (.intLit 0) [.var "rad"] "_healRet" ]
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqAsh) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallStmt ?_
    exact ExecBlock.consRevert (ExecStmt.requireFalse hreqSurplus)
  simpa [ExecTransitionBody, evm0, locals, kissTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockRevert hblock

theorem vowKissSourceSuccess
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmDai evmHeal : EVM.State}
    {outDai outHeal : ByteArray} {vatDai AshNew : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ I).toNat)
    (hvatCode :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ I)) "dai" 0 [.address I.codeOwner]
        (true, evmDai, outDai) false)
    (hdecDai :
      config.externalABI.decode? "dai" outDai =
        some [.int (Int.ofNat vatDai.toNat)])
    (hvatDaiEnough : (kissRad I).toNat ≤ vatDai.toNat)
    (hAshLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨6⟩ =
        vowSlotWord ⟨6⟩ σ I)
    (hvatLoadDai :
      Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I)
    (hAshNew : AshNew = UInt256.sub (vowSlotWord ⟨6⟩ σ I) (kissRad I))
    (hvatCodeHeal :
      0 < (UInt256.ofNat
        (((Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew).lookupAccount
          (kissVatAddress σ I)).option 0 (fun acc => acc.code.size))).toNat)
    (hcallHeal :
      typedCallViaEVM config
        (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew)
        (EVM.address (kissVatAddress σ I)) "heal" 0
        [.int (Int.ofNat (kissRad I).toNat)] (true, evmHeal, outHeal) true)
    (hdecHeal : config.externalABI.decode? "heal" outHeal = some []) :
    let locals := kissLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals kissTransition.body
      (.returned { contract := contract, locals := kissLocalsDone I vatDai AshNew } evmHeal none) := by
  intro locals evm0
  let evmAsh := Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew
  let locals1 := kissLocalsVatDai I vatDai
  let locals2 := kissLocalsVatDaiAshNew I vatDai AshNew
  have hrad :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "rad") =
        .ok (.int (Int.ofNat (kissRad I).toNat)) := by
    simpa [locals] using evalExpr_varUInt256 (evm := evm0)
      (locals := locals) (name := "rad") (value := kissRad I)
      (by simp [locals])
  have hash :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage AshRef) =
        .ok (.int (Int.ofNat (vowSlotWord ⟨6⟩ σ I).toNat)) := by
    simpa [evm0, initState, vowSlotWord] using
      evalExpr_kissAshStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hreqAsh :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .le (.var "rad") (.storage AshRef)) = .ok (.bool true) :=
    evalExpr_le_uint256_true hrad hash hashEnough
  have hvat :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [evm0, initState, kissVatAddress, vowAddressReturnWord, vowSlotWord] using
      evalExpr_kissVatStorage (evm := evm0) (locals := locals)
        (by simp [locals, kissLocals])
  have hguard :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvat (by simpa [evm0] using hvatCode)
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm0 [thisAddr] =
        .ok [.address I.codeOwner] := by
    simpa [evm0, initState] using evalExprs_kissThis evm0 locals
  have hcallDaiStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai" (perm := false))
        (.ok { contract := contract, locals := locals1 } evmDai) := by
    simpa [locals, locals1, kissLocalsVatDai, collapseReturns] using
      ExecStmt.externalCallSuccess hvat (by simp [evalExpr?, pure]) hargs hcallDai hdecDai
  have hradDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "rad") = .ok (.int (Int.ofNat (kissRad I).toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := kissLocalsVatDai I vatDai)
        (name := "rad") (value := kissRad I) (kissLocalsVatDai_get_rad I vatDai)
  have hvatDai :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.var "vatDai") = .ok (.int (Int.ofNat vatDai.toNat)) := by
    simpa [locals1] using
      evalExpr_varUInt256 (evm := evmDai) (locals := kissLocalsVatDai I vatDai)
        (name := "vatDai") (value := vatDai) (kissLocalsVatDai_get_vatDai I vatDai)
  have hreqSurplus :
      evalExpr? config { contract := contract, locals := locals1 } evmDai
        (.binary .le (.var "rad") (.var "vatDai")) = .ok (.bool true) :=
    evalExpr_le_uint256_true hradDai hvatDai hvatDaiEnough
  have hsubStmt :
      ExecStmt config { contract := contract, locals := locals1 } evmDai
        (.internalCall "sub" [.storage AshRef, .var "rad"] "AshNew")
        (.ok { contract := contract, locals := locals2 } evmDai) := by
    simpa [locals1, locals2, kissFrameAshNew, kissLocalsAshNew, kissLocalsVatDaiAshNew] using
      (kissInternalSubReturn I evmDai (locals := locals1)
        (AshVal := vowSlotWord ⟨6⟩ σ I) (AshNew := AshNew) hAshLoadDai
        (by simpa [locals1] using kissLocalsVatDai_get_rad I vatDai)
        (by simp [locals1, kissLocalsVatDai, kissLocals])
        hAshNew hashEnough)
  have hAshNewVar :
      evalExpr? config { contract := contract, locals := locals2 } evmDai (.var "AshNew") =
        .ok (.int (Int.ofNat AshNew.toNat)) := by
    simpa [locals2] using
      evalExpr_varUInt256 (evm := evmDai) (locals := kissLocalsVatDaiAshNew I vatDai AshNew)
        (name := "AshNew") (value := AshNew)
        (kissLocalsVatDaiAshNew_get_AshNew I vatDai AshNew)
  have hassignAsh :
      assignStorageRef? config { contract := contract, locals := locals2 } evmDai
        .storage AshRef (.int (Int.ofNat AshNew.toNat)) =
          .ok ({ contract := contract, locals := locals2 }, evmAsh) := by
    simpa [evmAsh, locals2] using
      assign_kissAshStorage evmDai (locals := locals2) AshNew
        (by simp [locals2, kissLocalsVatDaiAshNew, kissLocalsVatDai, kissLocals])
  have hvatLoadAsh :
      Solm.EVM.storageLoad evmAsh evmAsh.executionEnv.codeOwner ⟨1⟩ =
        vowSlotWord ⟨1⟩ σ I := by
    calc
      Solm.EVM.storageLoad evmAsh evmAsh.executionEnv.codeOwner ⟨1⟩
          = Solm.EVM.storageLoad
              (Solm.EVM.storageStore evmDai evmDai.executionEnv.codeOwner ⟨6⟩ AshNew)
              evmDai.executionEnv.codeOwner ⟨1⟩ := by
            simp [evmAsh, storageStore_executionEnv]
      _ = Solm.EVM.storageLoad evmDai evmDai.executionEnv.codeOwner ⟨1⟩ := by
            exact storageLoad_storageStore_ne evmDai evmDai.executionEnv.codeOwner
              (by decide : (⟨1⟩ : UInt256) ≠ ⟨6⟩)
      _ = vowSlotWord ⟨1⟩ σ I := hvatLoadDai
  have hvatHeal :
      evalExpr? config { contract := contract, locals := locals2 } evmAsh (.storage vatRef) =
        .ok (.address (kissVatAddress σ I)) := by
    simpa [kissVatAddress, vowAddressReturnWord, hvatLoadAsh] using
      evalExpr_kissVatStorage (evm := evmAsh) (locals := locals2)
        (by simp [locals2, kissLocalsVatDaiAshNew, kissLocalsVatDai, kissLocals])
  have hguardHeal :
      evalExpr? config { contract := contract, locals := locals2 } evmAsh
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_kissVatCodeGuard_true hvatHeal (by simpa [evmAsh] using hvatCodeHeal)
  have hargsHeal :
      evalExprs? config { contract := contract, locals := locals2 } evmAsh [.var "rad"] =
        .ok [.int (Int.ofNat (kissRad I).toNat)] := by
    simpa [locals2] using
      evalExprs_kissRad (evm := evmAsh) (I := I)
        (locals := kissLocalsVatDaiAshNew I vatDai AshNew)
        (kissLocalsVatDaiAshNew_get_rad I vatDai AshNew)
  have hcallHealStmt :
      ExecStmt config { contract := contract, locals := locals2 } evmAsh
        (.externalCall (.storage vatRef) "heal" (.intLit 0) [.var "rad"] "_healRet")
        (.ok { contract := contract, locals := kissLocalsDone I vatDai AshNew } evmHeal) := by
    simpa [kissLocalsDone, locals2, collapseReturns] using
      ExecStmt.externalCallSuccess hvatHeal (by simp [evalExpr?, pure]) hargsHeal hcallHeal
        hdecHeal
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0
        [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
          .require (.binary .le (.var "rad") (.storage AshRef)),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "dai" (.intLit 0) [thisAddr] "vatDai"
            (perm := false),
          .require (.binary .le (.var "rad") (.var "vatDai")),
          .internalCall "sub" [.storage AshRef, .var "rad"] "AshNew",
          .assign .storage AshRef (.var "AshNew"),
          .require (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)),
          .externalCall (.storage vatRef) "heal" (.intLit 0) [.var "rad"] "_healRet" ]
        (.ok { contract := contract, locals := kissLocalsDone I vatDai AshNew } evmHeal) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqAsh) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    refine ExecBlock.consNormal hcallDaiStmt ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hreqSurplus) ?_
    refine ExecBlock.consNormal hsubStmt ?_
    refine ExecBlock.consNormal (ExecStmt.assign hAshNewVar hassignAsh) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardHeal) ?_
    exact ExecBlock.consNormal hcallHealStmt ExecBlock.nil
  simpa [ExecTransitionBody, evm0, locals, kissTransition, nonpayable,
    checkedExternalCallStmts] using ExecFuncBody.execBlockOK hblock

set_option maxHeartbeats 1000000 in
theorem vowKissDaiSuccessInsufficientSurplusBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {A'_evm : Substate} {o : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some kissTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kissTransition.params.map Param.name)
        (transitionSignature kissTransition).paramTypes I.calldata = some (kissLocals I))
    (rd1704 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1704⟩
      (⟨1⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        kissDaiTargetWord σ_evm I :: kissRad I :: ⟨412⟩ :: sel :: [])
      (o.write 0 (kissDaiCalldataMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
      (UInt256.ofNat 6) o (cA', σ'_evm) k C)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_evm I)) "dai" 0 [.address I.codeOwner]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          o) false)
    (hosz : o.size < UInt256.size)
    (ho32 : 32 ≤ o.size)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_evm I).toNat)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hinsuff :
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))).toNat < (kissRad I).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let vatDai : UInt256 := UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32))
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 :=
    kissDaiMin32_toNat_of_ge ho32 hosz
  have rd1704' := rd1704
  rw [hmin] at rd1704'
  obtain ⟨_, _, rd1722⟩ :=
    RD.vowKissDaiCallSuccessToDecode rd1704' (by simp)
  have hmem : (o.write 0 (kissDaiCalldataMem I) 128 32).size = 164 :=
    kissDaiWrite_size I o 32 (by omega) ho32
  have hread64 :
      (o.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    kissDaiWrite_read64 I o 32 (by omega) ho32
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (o.write 0 (kissDaiCalldataMem I) 128 32).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((o.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hmload128 :
      (if (⟨128⟩ : UInt256).toNat ≥ (o.write 0 (kissDaiCalldataMem I) 128 32).size
          ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((o.write 0 (kissDaiCalldataMem I) 128 32).readWithPadding
            (⟨128⟩ : UInt256).toNat 32))) =
        vatDai := by
    have hnot :
        ¬ ((⟨128⟩ : UInt256).toNat ≥ (o.write 0 (kissDaiCalldataMem I) 128 32).size
            ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩) := by
      rw [hmem]
      native_decide
    rw [if_neg hnot, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      kissDaiWrite_read128_32 I o ho32]
  obtain ⟨_, _, rd1745⟩ :=
    RD.vowKissDaiReturnDecodeOk (retWord := vatDai) rd1722 ho32 hosz hmload64 hmload128
  have hrev := RD.vowKissInsufficientSurplus rd1745
    (by simpa [vatDai] using hinsuff) hmem hread64
  have hAsh :
      vowSlotWord ⟨6⟩ σ_evm I = vowSlotWord ⟨6⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hashEnoughSolm : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_solm I).toNat := by
    simpa [← hAsh] using hashEnough
  have hVatAddr : kissVatAddress σ_evm I = kissVatAddress σ_solm I := by
    apply Fin.ext
    have hVat :
        vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [kissVatAddress, vowAddressReturnWord, hVat]
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hStateCall⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallDai)
      (by simp [initState]) hAccounts
  have hcallSolm :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          o) false := by
    simpa [hVatAddr] using hcallSolmRaw
  have hdecDai :
      config.externalABI.decode? "dai" o = some [.int (Int.ofNat vatDai.toNat)] := by
    simpa [vatDai] using kissDaiDecode_ok (o := o) ho32
  have hbody := vowKissSourceInsufficientSurplus (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai :=
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
    (out := o) (vatDai := vatDai) hwv hashEnoughSolm hvatCodeSolm hcallSolm
    hdecDai (by simpa [vatDai] using hinsuff)
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowKissNoVatCodeBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some kissTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kissTransition.params.map Param.name)
        (transitionSignature kissTransition).paramTypes I.calldata = some (kissLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨383⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_evm I).toNat)
    (hnoCode :
      Reasoning.Theory.extCodeSizeWord σ_evm (kissDaiTargetWord σ_evm I) = ⟨0⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hAsh :
      vowSlotWord ⟨6⟩ σ_evm I = vowSlotWord ⟨6⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hashEnoughSolm : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_solm I).toNat := by
    simpa [← hAsh] using hashEnough
  have hVat :
      vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
  have hTarget : kissDaiTargetWord σ_evm I = kissDaiTargetWord σ_solm I := by
    simp [kissDaiTargetWord, hVat]
  have hnoCodeSolm :
      Reasoning.Theory.extCodeSizeWord σ_solm (kissDaiTargetWord σ_solm I) = ⟨0⟩ := by
    have hsame :=
      Reasoning.Theory.extCodeSizeWord_accountMapEquiv hAccounts
        (kissDaiTargetWord σ_evm I)
    have hsolmTargetEvm :
        Reasoning.Theory.extCodeSizeWord σ_solm (kissDaiTargetWord σ_evm I) = ⟨0⟩ := by
      rw [← hsame]
      exact hnoCode
    simpa [hTarget] using hsolmTargetEvm
  have hvatAddr :
      kissVatAddress σ_solm I = AccountAddress.ofUInt256 (kissDaiTargetWord σ_solm I) := by
    apply Fin.ext
    simp [kissVatAddress, kissDaiTargetWord, vowAddressReturnWord,
      accountAddress_ofUInt256_eq_ofNat_toNat]
  have hvatNoCode :
      (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat = 0 := by
    rw [hvatAddr]
    unfold Reasoning.Theory.extCodeSizeWord at hnoCodeSolm
    cases hacc :
      σ_solm.find? (AccountAddress.ofUInt256 (kissDaiTargetWord σ_solm I)) with
    | none =>
        simpa [initState, State.lookupAccount, hacc] using
          (show (UInt256.ofNat 0).toNat = 0 from by native_decide)
    | some acc =>
        have hword := congrArg UInt256.toNat hnoCodeSolm
        simpa [initState, State.lookupAccount, hacc] using hword
  have hbody := vowKissSourceNoVatCode (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    hwv hashEnoughSolm hvatNoCode
  have hrev := RD.vowKissDaiNoCode hreach hsz36 hsize hashEnough hnoCode
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowKissDaiCallFailureBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {A'_evm : Substate} {o mem : ByteArray} {aw : UInt256} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some kissTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kissTransition.params.map Param.name)
        (transitionSignature kissTransition).paramTypes I.calldata = some (kissLocals I))
    (rd1704 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1704⟩
      (⟨0⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        kissDaiTargetWord σ_evm I :: kissRad I :: ⟨412⟩ :: sel :: [])
      mem aw o (cA', σ'_evm) k C)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_evm I)) "dai" 0 [.address I.codeOwner]
        (false,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          o) false)
    (hosz : o.size < UInt256.size)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_evm I).toNat)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hrev := RD.vowKissDaiCallFailure rd1704 hosz (by simp)
  have hAsh :
      vowSlotWord ⟨6⟩ σ_evm I = vowSlotWord ⟨6⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hashEnoughSolm : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_solm I).toNat := by
    simpa [← hAsh] using hashEnough
  have hVatAddr : kissVatAddress σ_evm I = kissVatAddress σ_solm I := by
    apply Fin.ext
    have hVat :
        vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [kissVatAddress, vowAddressReturnWord, hVat]
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hStateCall⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallDai)
      (by simp [initState]) hAccounts
  have hcallSolm :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (false,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          o) false := by
    simpa [hVatAddr] using hcallSolmRaw
  have hbody := vowKissSourceDaiCallFailure (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai :=
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
    (out := o) hwv hashEnoughSolm hvatCodeSolm hcallSolm
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowKissDaiDecodeShortBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    {cA' : Batteries.RBSet AccountAddress compare} {σ'_evm : AccountMap}
    {A'_evm : Substate} {o : ByteArray} {k C : ℕ}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hdispatch : dispatchMsg contract I.calldata = some kissTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kissTransition.params.map Param.name)
        (transitionSignature kissTransition).paramTypes I.calldata = some (kissLocals I))
    (rd1704 : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨1704⟩
      (⟨1⟩ :: kissDaiEndPtr I :: ⟨1814410054⟩ ::
        kissDaiTargetWord σ_evm I :: kissRad I :: ⟨412⟩ :: sel :: [])
      (o.write 0 (kissDaiCalldataMem I) 128
        (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat)
      (UInt256.ofNat 6) o (cA', σ'_evm) k C)
    (hcallDai :
      typedCallViaEVM config (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_evm I)) "dai" 0 [.address I.codeOwner]
        (true,
          { initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_evm
              substate := A'_evm
              createdAccounts := cA' },
          o) false)
    (hosz : o.size < UInt256.size)
    (hshort : o.size < 32)
    (hashEnough : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_evm I).toNat)
    (hvatCodeSolm :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (kissVatAddress σ_solm I)).option 0 (fun acc => acc.code.size))).toNat)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hmin : (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size :=
    kissDaiMin32_toNat_of_lt hshort
  have rd1704' := rd1704
  rw [hmin] at rd1704'
  obtain ⟨_, _, rd1722⟩ :=
    RD.vowKissDaiCallSuccessToDecode rd1704' (by simp)
  have hmem : (o.write 0 (kissDaiCalldataMem I) 128 o.size).size = 164 :=
    kissDaiWrite_size I o o.size (by omega) (by omega)
  have hread64 :
      (o.write 0 (kissDaiCalldataMem I) 128 o.size).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    kissDaiWrite_read64 I o o.size (by omega) (by omega)
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ (o.write 0 (kissDaiCalldataMem I) 128 o.size).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((o.write 0 (kissDaiCalldataMem I) 128 o.size).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hrev := RD.vowKissDaiReturnDecodeShortReverts rd1722 hshort hosz hmload64
  have hAsh :
      vowSlotWord ⟨6⟩ σ_evm I = vowSlotWord ⟨6⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hashEnoughSolm : (kissRad I).toNat ≤ (vowSlotWord ⟨6⟩ σ_solm I).toNat := by
    simpa [← hAsh] using hashEnough
  have hVatAddr : kissVatAddress σ_evm I = kissVatAddress σ_solm I := by
    apply Fin.ext
    have hVat :
        vowSlotWord ⟨1⟩ σ_evm I = vowSlotWord ⟨1⟩ σ_solm I :=
      accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨1⟩ ⟨0⟩
    simp [kissVatAddress, vowAddressReturnWord, hVat]
  obtain ⟨σ'_solm, A'_solm, hcallSolmRaw, _hStateCall⟩ :=
    typedCallViaEVM_initState_EVMStateEquiv (hcall := hcallDai)
      (by simp [initState]) hAccounts
  have hcallSolm :
      typedCallViaEVM config (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (kissVatAddress σ_solm I)) "dai" 0 [.address I.codeOwner]
        (true,
          { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ'_solm
              substate := A'_solm
              createdAccounts := cA' },
          o) false := by
    simpa [hVatAddr] using hcallSolmRaw
  have hdecDai : config.externalABI.decode? "dai" o = none :=
    kissDaiDecode_none_short hshort
  have hbody := vowKissSourceDaiDecodeRevert (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
    (evmDai :=
      { initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I with
          accountMap := σ'_solm
          substate := A'_solm
          createdAccounts := cA' })
    (out := o) hwv hashEnoughSolm hvatCodeSolm hcallSolm hdecDai
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowKissNotEnoughAshBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some kissTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (kissTransition.params.map Param.name)
        (transitionSignature kissTransition).paramTypes I.calldata = some (kissLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨383⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hnotEnough : (vowSlotWord ⟨6⟩ σ_evm I).toNat < (kissRad I).toNat) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hAsh : vowSlotWord ⟨6⟩ σ_evm I = vowSlotWord ⟨6⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨6⟩ ⟨0⟩
  have hnotEnoughSolm : (vowSlotWord ⟨6⟩ σ_solm I).toNat < (kissRad I).toNat := by
    simpa [hAsh] using hnotEnough
  have hbody := vowKissSourceNotEnoughAsh (cA := cA) (gh := gh) (bl := bl)
    (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g) hwv hnotEnoughSolm
  have hrev := RD.vowKissNotEnoughAsh hreach hsz36 hsize hnotEnough
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowKissShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 36)
    (hsel : selIs I ⟨#[0x25, 0x06, 0x85, 0x5a]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach :=
    vowReachKissBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 32
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vowBytecode) (sel := vowSelWord I) (entry := ⟨383⟩) (ret := ⟨412⟩)
    (decoded := ⟨405⟩) (need := ⟨32⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (vowDispatch_kiss hsel)
    (vowDecode_kiss_none_short hsz4 hshort)

end Benchmarks.Dss.Vow
