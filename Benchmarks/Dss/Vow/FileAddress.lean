import Benchmarks.Dss.Vow.FileUint
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000
set_option maxHeartbeats 0

namespace Benchmarks.Dss.Vow

/-! ## `file(bytes32,address)` -/

abbrev fileAddressWhat (I : ExecutionEnv) : List UInt8 :=
  (I.calldata.toList.drop 4).take 32

abbrev fileAddressData (I : ExecutionEnv) : AccountAddress :=
  AccountAddress.ofNat (calldataWord I.calldata 36).toNat

abbrev fileAddressDataWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 36

abbrev fileAddressDataKey (I : ExecutionEnv) : UInt256 :=
  UInt256.land solcAddrMask (fileAddressDataWord I)

abbrev fileAddressFlapperBytes : List UInt8 :=
  [102, 108, 97, 112, 112, 101, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]

abbrev fileAddressFlopperBytes : List UInt8 :=
  [102, 108, 111, 112, 112, 101, 114, 0, 0, 0, 0, 0, 0, 0, 0, 0,
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

theorem vowDispatch_fileAddress {I : ExecutionEnv}
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩) :
    dispatchMsg contract I.calldata = some fileAddressTransition := by
  apply dispatchMsg_eq_some_of_split (hfallback := by rfl)
    (pre := [AshTransition, SinTransition, bumpTransition, cageTransition, denyTransition,
      dumpTransition, fessTransition, fileUintTransition])
    (post := [flapTransition, flapperTransition, flogTransition, flopTransition,
      flopperTransition, healTransition, humpTransition, kissTransition, liveTransition,
      relyTransition, sinTransition, sumpTransition, vatTransition, waitTransition,
      wardsTransition])
    (ti := fileAddressTransition)
    (htr := by rfl)
  · intro t ht
    have hcd : I.calldata.extract 0 4 = (⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩ : ByteArray) :=
      (byteArray_eq_of_beq hsel).symm
    simp at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      simp [selectorOf, AshSelectorBytes, SinSelectorBytes, bumpSelectorBytes,
        cageSelectorBytes, denySelectorBytes, dumpSelectorBytes, fessSelectorBytes,
        fileUintSelectorBytes, hcd]
      native_decide
  · rw [selectorOf, fileAddressSelectorBytes]
    exact hsel

theorem vowDecode_fileAddress_ok {I : ExecutionEnv} (hsz68 : 68 ≤ I.calldata.size) :
    decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata =
        some (((∅ : Store).insert "what" (.fixedBytes bytes32Width (fileAddressWhat I))).insert
          "data" (.address (fileAddressData I))) := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr, fileAddressWhat,
    fileAddressData, abiBytes32, abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_address_ok (cd := I.calldata) (x := "what")
      (y := "data") hsz68)

theorem vowDecode_fileAddress_none_short {I : ExecutionEnv}
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68) :
    decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
      (transitionSignature fileAddressTransition).paramTypes I.calldata = none := by
  simpa [config, fileAddressTransition, bytes32, bytes32Width, addr, abiBytes32,
    abiBytes32Width, abiAddress] using
    (decodeCalldata_legacyBytes32_address_none_short (cd := I.calldata) (x := "what")
      (y := "data") hsz4 hshort)

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

abbrev fileAddressLocalsNope (I : ExecutionEnv) : Store :=
  (fileAddressLocals I).insert "_nopeRet" .unit

abbrev fileAddressLocalsNopeHope (I : ExecutionEnv) : Store :=
  (fileAddressLocalsNope I).insert "_hopeRet" .unit

theorem fileAddressLocalsNope_get_data (I : ExecutionEnv) :
    (fileAddressLocalsNope I).get? "data" =
      some (.address (fileAddressData I)) := by
  rw [fileAddressLocalsNope, store_get_ne _ _ (by decide), fileAddressLocals_get_data]

theorem fileAddressLocalsNope_get_vat (I : ExecutionEnv) :
    (fileAddressLocalsNope I).get? "vat" = none := by
  rw [fileAddressLocalsNope, fileAddressLocals, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem fileAddressLocalsNope_get_flapper (I : ExecutionEnv) :
    (fileAddressLocalsNope I).get? "flapper" = none := by
  rw [fileAddressLocalsNope, fileAddressLocals, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
  simp

theorem vowExternalABI_decode_nope (out : ByteArray) :
    config.externalABI.decode? "nope" out = some ([] : List Solm.Value) := by
  simp [config, vowExternalABI, decodeVoid?]

theorem vowExternalABI_decode_hope (out : ByteArray) :
    config.externalABI.decode? "hope" out = some ([] : List Solm.Value) := by
  simp [config, vowExternalABI, decodeVoid?]

abbrev fileAddressVatAddressOf (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      solcAddrMask).toNat

abbrev fileAddressFlapperAddressOf (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat
    (UInt256.land (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      solcAddrMask).toNat

abbrev fileAddressSetFlapperEVM (evm : EVM.State) (I : ExecutionEnv) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      (fileAddressDataKey I))

abbrev fileAddressVatTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  vowAddressReturnWord ⟨1⟩ σ I

abbrev fileAddressFlapperTargetWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  vowAddressReturnWord ⟨2⟩ σ I

theorem fileAddressVatAddress_eq_target (σ : AccountMap) (I : ExecutionEnv) :
    EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat) =
      AccountAddress.ofUInt256 (fileAddressVatTargetWord σ I) := by
  apply Fin.ext
  simp [fileAddressVatTargetWord, vowAddressReturnWord]
  rfl

abbrev fileAddressNopeSelectorShifted : UInt256 :=
  UInt256.shiftLeft ⟨1848021117⟩ ⟨225⟩

abbrev fileAddressCallOutPtr : UInt256 :=
  ⟨128⟩

abbrev fileAddressCallOutSize : UInt256 :=
  ⟨0⟩

abbrev fileAddressCallInSize : UInt256 :=
  UInt256.add (UInt256.sub fileAddressCallOutPtr fileAddressCallOutPtr) ⟨36⟩

abbrev fileAddressCallEndPtr : UInt256 :=
  UInt256.add fileAddressCallOutPtr ⟨36⟩

noncomputable def fileAddressNopeSelectorMem (mem : ByteArray) : ByteArray :=
  fileAddressNopeSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def fileAddressNopeCalldataMem (arg : UInt256) (mem : ByteArray) : ByteArray :=
  arg.toByteArray.write 0 (fileAddressNopeSelectorMem mem) 132 32

theorem fileAddressCallInSize_eq : fileAddressCallInSize = ⟨36⟩ := by
  unfold fileAddressCallInSize fileAddressCallOutPtr
  native_decide

theorem fileAddressCallEndPtr_eq : fileAddressCallEndPtr = ⟨164⟩ := by
  unfold fileAddressCallEndPtr fileAddressCallOutPtr
  native_decide

theorem fileAddressNopeSelectorMem_size {mem : ByteArray} (hmem : mem.size = 96) :
    (fileAddressNopeSelectorMem mem).size = 160 := by
  unfold fileAddressNopeSelectorMem
  have hgap : 128 - 96 < USize.size := by native_decide
  exact toByteArray_write32_size_of_ge mem fileAddressNopeSelectorShifted 128 96 160 hmem
    (by omega) hgap (by omega)

theorem fileAddressNopeSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (fileAddressNopeSelectorMem mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold fileAddressNopeSelectorMem
  have hgap : 128 - mem.size < USize.size := by
    rw [hmem]
    native_decide
  rw [toByteArray_write_read_below_of_gap fileAddressNopeSelectorShifted mem 128 64
    (by rw [hmem]) (by norm_num) hgap, hread64]

theorem fileAddressNopeSelectorMem_selector {mem : ByteArray} (hmem : mem.size = 96) :
    (fileAddressNopeSelectorMem mem).extract 128 132 = vatNopeSelector := by
  unfold fileAddressNopeSelectorMem
  have hgap : 128 - mem.size < USize.size := by
    rw [hmem]
    native_decide
  rw [toByteArray_write_eq fileAddressNopeSelectorShifted mem 128
    (by rw [hmem]; omega) hgap]
  have hprefix :
      (mem ++ ffi.ByteArray.zeroes (128 - mem.size)).size = 128 := by
    rw [ByteArray.size_append, ByteArray_zeroes_size, hmem]
  rw [extract_append_right_window _ _ 128 132 (by rw [hprefix]), hprefix,
    show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    toByteArray_eq_toBytesBE]
  native_decide

theorem fileAddressNopeCalldataMem_size (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (fileAddressNopeCalldataMem arg mem).size = 164 := by
  unfold fileAddressNopeCalldataMem
  exact toByteArray_write32_size_of_le (fileAddressNopeSelectorMem mem) arg 132 160 164
    (fileAddressNopeSelectorMem_size hmem)
    (by rw [fileAddressNopeSelectorMem_size hmem]; omega)
    (by omega)

theorem fileAddressNopeCalldataMem_read64 (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (fileAddressNopeCalldataMem arg mem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold fileAddressNopeCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [fileAddressNopeSelectorMem_size hmem]; omega) (by omega)]
  exact fileAddressNopeSelectorMem_read64 hmem hread64

theorem fileAddressNopeCalldataMem_read128_36 (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (fileAddressNopeCalldataMem arg mem).readWithPadding 128 36 =
      vatNopeSelector ++ arg.toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [fileAddressNopeCalldataMem_size arg hmem]), fileAddressNopeCalldataMem,
    write32_eq _ (fileAddressNopeSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [fileAddressNopeSelectorMem_size hmem]; omega)]
  have hAsz : ((fileAddressNopeSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, fileAddressNopeSelectorMem_size hmem]
    omega
  have hBsz : (arg.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((fileAddressNopeSelectorMem mem).extract 0 132 ++
        arg.toByteArray.extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : arg.toByteArray.extract 0 32 = arg.toByteArray := by
    have h := @ByteArray.extract_zero_size arg.toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), fileAddressNopeSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem fileAddressNopeEncode_eq (w : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    config.externalABI.encode? "nope"
        [.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)] =
      some ((fileAddressNopeCalldataMem (UInt256.land w solcAddrMask) mem).readWithPadding
        fileAddressCallOutPtr.toNat fileAddressCallInSize.toNat) := by
  rw [fileAddressCallInSize_eq]
  change config.externalABI.encode? "nope"
      [.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)] =
    some ((fileAddressNopeCalldataMem (UInt256.land w solcAddrMask) mem).readWithPadding
      128 36)
  rw [fileAddressNopeCalldataMem_read128_36 _ hmem]
  have hcanon := solcAddrMask_result_canonical w
  have haddrVal : (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat).val =
      (UInt256.land w solcAddrMask).toNat := by
    unfold AccountAddress.ofNat
    simp only [Fin.val_ofNat]
    apply Nat.mod_eq_of_lt
    simpa [EVM.addressModulus, EVM.twoPow, AccountAddress.size] using hcanon
  have hword :
      EVM.word ↑(AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat) =
        UInt256.land w solcAddrMask := by
    change UInt256.ofNat (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat).val =
      UInt256.land w solcAddrMask
    rw [haddrVal]
    exact u256_ofNat_toNat _
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.abiTupleHeadSize?,
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, vatNopeSelector, selectorBytes,
    hword, word_toBytesBE_toByteArray_eq_toByteArray]

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

theorem evalExpr_fileAddressVatStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "vat" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
      .ok (.address (fileAddressVatAddressOf evm)) := by
  rw [evalExpr_storage_scalar (er := ({ base := "vat", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨1⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_address_offset0 _ ⟨1⟩)
  · exact hbase
  · simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, addrSt]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]

theorem evalExpr_fileAddressFlapperStorage (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "flapper" = none) :
    evalExpr? config { contract := contract, locals := locals } evm (.storage flapperRef) =
      .ok (.address (fileAddressFlapperAddressOf evm)) := by
  rw [evalExpr_storage_scalar (er := ({ base := "flapper", steps := [] } : EvaledStorageRef))
    (t := .address) (loc := addrLoc ⟨2⟩)]
  · exact congrArg EvalResult.ok (vowStorageLocLoad_address_offset0 _ ⟨2⟩)
  · exact hbase
  · simp [flapperRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, addrSt]
  · funext evm
    simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw]

theorem evalExpr_fileAddressVatCodeGuard_true {evm : EVM.State} {locals : Store}
    {target : AccountAddress}
    (hreceiver :
      evalExpr? config { contract := contract, locals := locals } evm (.storage vatRef) =
        .ok (.address target))
    (hcode :
      0 < (UInt256.ofNat ((evm.lookupAccount target).option 0 (fun acc => acc.code.size))).toNat) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
  simp [evalExpr?, EvalResult.bind, bind, hreceiver, evalBinaryOp?, EVM.Word.ofNat, hcode]

theorem evalExprs_fileAddressNopeArgs (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "flapper" = none) :
    evalExprs? config { contract := contract, locals := locals } evm [.storage flapperRef] =
      .ok [.address (fileAddressFlapperAddressOf evm)] := by
  have hflapper := evalExpr_fileAddressFlapperStorage evm (locals := locals) hbase
  simp [evalExprs?, hflapper, EvalResult.bind, bind, pure]

theorem evalExprs_fileAddressHopeArgs {evm : EVM.State} {I : ExecutionEnv} {locals : Store}
    (hdata : locals.get? "data" = some (.address (fileAddressData I))) :
    evalExprs? config { contract := contract, locals := locals } evm [.var "data"] =
      .ok [.address (fileAddressData I)] := by
  have hdataEval := evalExpr_fileAddressData (evm := evm) (I := I) (locals := locals) hdata
  simp [evalExprs?, hdataEval, EvalResult.bind, bind, pure]

theorem assign_fileAddressFlopperStorage (evm : EVM.State) {locals : Store} (data : UInt256)
    (hbase : locals.get? "flopper" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
        (UInt256.land solcAddrMask data))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage flopperRef (.address (AccountAddress.ofNat data.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have hvalue :
      (.address (AccountAddress.ofNat data.toNat) : Value) =
        .address (AccountAddress.ofNat (UInt256.land solcAddrMask data).toNat) := by
    simpa using (solcAddressValue_masked data)
  rw [hvalue]
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm flopperRef =
        .ok { base := "flopper", steps := [] } := by
    simp [flopperRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (addrLoc ⟨3⟩)
          (.address (AccountAddress.ofNat (UInt256.land solcAddrMask data).toNat)) =
        some evm' := by
    simpa [addrLoc, evm'] using
      storageLocStore_address_offset0 evm ⟨3⟩ (UInt256.land solcAddrMask data) (by
        rw [u256_land_comm solcAddrMask data]
        exact solcAddrMask_result_canonical data)
  exact assignStorageRef_storage_scalar_value
    (ty := .elem .address) (loc := addrLoc ⟨3⟩)
    (hbase := hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hscalar := by trivial)
    (hstore := hstore)

theorem assign_fileAddressFlapperStorage (evm : EVM.State) {locals : Store} (data : UInt256)
    (hbase : locals.get? "flapper" = none) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
        (UInt256.land solcAddrMask data))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage flapperRef (.address (AccountAddress.ofNat data.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have hvalue :
      (.address (AccountAddress.ofNat data.toNat) : Value) =
        .address (AccountAddress.ofNat (UInt256.land solcAddrMask data).toNat) := by
    simpa using (solcAddressValue_masked data)
  rw [hvalue]
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm flapperRef =
        .ok { base := "flapper", steps := [] } := by
    simp [flapperRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
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

theorem fileAddressFlapperSourceSuccess
    {cA gh bl σ σ₀ A I} {g : UInt256} {evmNope evmHope : EVM.State}
    {outNope outHope : ByteArray}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hwhat : fileAddressWhat I = fileAddressFlapperBytes)
    (hvatCodeNope :
      0 < (UInt256.ofNat
        (((initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I).lookupAccount
          (fileAddressVatAddressOf
            (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcallNope :
      typedCallViaEVM config (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (fileAddressVatAddressOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))) "nope" 0
        [.address (fileAddressFlapperAddressOf
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))]
        (true, evmNope, outNope) true)
    (hvatCodeHope :
      0 < (UInt256.ofNat
        (((fileAddressSetFlapperEVM evmNope I).lookupAccount
          (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNope I))).option 0
            (fun acc => acc.code.size))).toNat)
    (hcallHope :
      typedCallViaEVM config (fileAddressSetFlapperEVM evmNope I)
        (EVM.address (fileAddressVatAddressOf (fileAddressSetFlapperEVM evmNope I)))
        "hope" 0 [.address (fileAddressData I)] (true, evmHope, outHope) true) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := fileAddressLocalsNopeHope I } evmHope none) := by
  intro locals evm0
  let localsNope := fileAddressLocalsNope I
  let evmSet := fileAddressSetFlapperEVM evmNope I
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileAddressLocals]) hauth
  have hflapper :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") flapperParamLit) = .ok (.bool true) := by
    simpa [flapperParamLit, fileAddressFlapperBytes] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressFlapperBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hvatNope :
      evalExpr? config { contract := contract, locals := locals } evm0 (.storage vatRef) =
        .ok (.address (fileAddressVatAddressOf evm0)) := by
    simpa [locals] using
      evalExpr_fileAddressVatStorage evm0 (locals := locals)
        (by simp [locals, fileAddressLocals])
  have hguardNope :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_fileAddressVatCodeGuard_true hvatNope (by simpa [evm0] using hvatCodeNope)
  have hargsNope :
      evalExprs? config { contract := contract, locals := locals } evm0 [.storage flapperRef] =
        .ok [.address (fileAddressFlapperAddressOf evm0)] := by
    simpa [locals] using
      evalExprs_fileAddressNopeArgs evm0 (locals := locals)
        (by simp [locals, fileAddressLocals])
  have hcallNopeStmt :
      ExecStmt config { contract := contract, locals := locals } evm0
        (.externalCall (.storage vatRef) "nope" (.intLit 0) [.storage flapperRef] "_nopeRet")
        (.ok { contract := contract, locals := localsNope } evmNope) := by
    simpa [locals, localsNope, fileAddressLocalsNope, collapseReturns, config, vowExternalABI,
      decodeVoid?] using
        ExecStmt.externalCallSuccess hvatNope (by simp [evalExpr?, pure]) hargsNope
          hcallNope (vowExternalABI_decode_nope outNope)
  have hdataNope :
      evalExpr? config { contract := contract, locals := localsNope } evmNope (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [localsNope, fileAddressLocalsNope] using
      (evalExpr_fileAddressData (evm := evmNope) (I := I) (locals := localsNope)
        (by simpa [localsNope] using fileAddressLocalsNope_get_data I))
  have hassign :
      assignStorageRef? config { contract := contract, locals := localsNope } evmNope
        .storage flapperRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := localsNope }, evmSet) := by
    simpa [fileAddressData, fileAddressDataKey, fileAddressDataWord, evmSet,
      fileAddressSetFlapperEVM] using
      (assign_fileAddressFlapperStorage evmNope (locals := localsNope)
        (calldataWord I.calldata 36)
        (by simp [localsNope]))
  have hvatHope :
      evalExpr? config { contract := contract, locals := localsNope } evmSet (.storage vatRef) =
        .ok (.address (fileAddressVatAddressOf evmSet)) := by
    simpa [localsNope] using
      evalExpr_fileAddressVatStorage evmSet (locals := localsNope)
        (by simp [localsNope])
  have hguardHope :
      evalExpr? config { contract := contract, locals := localsNope } evmSet
        (.binary .gt (.extCodeSize (.storage vatRef)) (.intLit 0)) = .ok (.bool true) := by
    exact evalExpr_fileAddressVatCodeGuard_true hvatHope (by simpa [evmSet] using hvatCodeHope)
  have hargsHope :
      evalExprs? config { contract := contract, locals := localsNope } evmSet [.var "data"] =
        .ok [.address (fileAddressData I)] := by
    simpa [localsNope, fileAddressLocalsNope] using
      evalExprs_fileAddressHopeArgs (evm := evmSet) (I := I) (locals := localsNope)
        (by simpa [localsNope] using fileAddressLocalsNope_get_data I)
  have hcallHopeStmt :
      ExecStmt config { contract := contract, locals := localsNope } evmSet
        (.externalCall (.storage vatRef) "hope" (.intLit 0) [.var "data"] "_hopeRet")
        (.ok { contract := contract, locals := fileAddressLocalsNopeHope I } evmHope) := by
    simpa [localsNope, fileAddressLocalsNopeHope, collapseReturns, config, vowExternalABI,
      decodeVoid?] using
        ExecStmt.externalCallSuccess hvatHope (by simp [evalExpr?, pure]) hargsHope hcallHope
          (vowExternalABI_decode_hope outHope)
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        (checkedExternalCallStmts (.storage vatRef) "nope" (.intLit 0)
            [.storage flapperRef] "_nopeRet" ++
          [ .assign .storage flapperRef (.var "data") ] ++
          checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
            [.var "data"] "_hopeRet")
        (.ok { contract := contract, locals := fileAddressLocalsNopeHope I } evmHope) := by
    simp only [checkedExternalCallStmts, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardNope) ?_
    refine ExecBlock.consNormal hcallNopeStmt ?_
    refine ExecBlock.consNormal (ExecStmt.assign hdataNope hassign) ?_
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguardHope) ?_
    exact ExecBlock.consNormal hcallHopeStmt ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := fileAddressLocalsNopeHope I } evmHope) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteTrue hflapper hthen) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, locals, fileAddressTransition, nonpayable, auth] using
    ExecFuncBody.execBlockOK hblock

theorem fileAddressFlopperSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotFlapper : fileAddressWhat I ≠ fileAddressFlapperBytes)
    (hwhat : fileAddressWhat I = fileAddressFlopperBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨3⟩
      (setAddressOffset0Word (Solm.EVM.storageLoad evm0 I.codeOwner ⟨3⟩)
        (fileAddressDataKey I))
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body
      (.returned { contract := contract, locals := locals } evm1 none) := by
  intro locals evm0 evm1
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileAddressLocals]) hauth
  have hflapper :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") flapperParamLit) = .ok (.bool false) := by
    simpa [flapperParamLit, fileAddressFlapperBytes] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressFlapperBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotFlapper)
  have hflopper :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") flopperParamLit) = .ok (.bool true) := by
    simpa [flopperParamLit, fileAddressFlopperBytes] using
      (evalExpr_fileAddressWhatEq_true (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressFlopperBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hwhat)
  have hdata :
      evalExpr? config { contract := contract, locals := locals } evm0 (.var "data") =
        .ok (.address (fileAddressData I)) := by
    simpa [locals] using
      (evalExpr_fileAddressData (evm := evm0) (I := I) (locals := locals)
        (by simp [locals]))
  have hassign :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage flopperRef (.address (fileAddressData I)) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [fileAddressData, fileAddressDataKey, fileAddressDataWord, evm1] using
      (assign_fileAddressFlopperStorage evm0 (locals := locals)
        (calldataWord I.calldata 36) (by simp [locals, fileAddressLocals]))
  have hthen :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.assign .storage flopperRef (.var "data")]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.assign hdata hassign) ExecBlock.nil
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite
          (.binary .eq (.var "what") flopperParamLit)
          [.assign .storage flopperRef (.var "data")]
          [.require (.boolLit false)]]
        (.ok { contract := contract, locals := locals } evm1) := by
    exact ExecBlock.consNormal (ExecStmt.iteTrue hflopper hthen) ExecBlock.nil
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        (.ok { contract := contract, locals := locals } evm1) := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consNormal (ExecStmt.iteFalse hflapper helse) ExecBlock.nil
  simpa [ExecTransitionBody, evm0, evm1, locals] using ExecFuncBody.execBlockOK hblock

theorem fileAddressUnrecognizedSourceBody {cA gh bl σ σ₀ A I} {g : UInt256}
    (hwv : I.weiValue = ⟨0⟩)
    (hauth : vowSlotWord (vowCallerWardsSlot I) σ I = ⟨1⟩)
    (hnotFlapper : fileAddressWhat I ≠ fileAddressFlapperBytes)
    (hnotFlopper : fileAddressWhat I ≠ fileAddressFlopperBytes) :
    let locals := fileAddressLocals I
    let evm0 := initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I
    ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
  intro locals evm0
  have hguard := vowAuthGuardEval_true (cA := cA) (gh := gh) (bl := bl)
    (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
    (locals := locals) (by simp [locals, fileAddressLocals]) hauth
  have hflapper :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") flapperParamLit) = .ok (.bool false) := by
    simpa [flapperParamLit, fileAddressFlapperBytes] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressFlapperBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotFlapper)
  have hflopper :
      evalExpr? config { contract := contract, locals := locals } evm0
        (.binary .eq (.var "what") flopperParamLit) = .ok (.bool false) := by
    simpa [flopperParamLit, fileAddressFlopperBytes] using
      (evalExpr_fileAddressWhatEq_false (evm := evm0) (I := I) (locals := locals)
        (bs := fileAddressFlopperBytes) (by simpa [locals] using fileAddressLocals_get_what I)
        hnotFlopper)
  have hreqFalse :
      evalExpr? config { contract := contract, locals := locals } evm0 (.boolLit false) =
        .ok (.bool false) := by
    simp [evalExpr?, pure]
  have helse :
      ExecBlock config { contract := contract, locals := locals } evm0
        [.ite
          (.binary .eq (.var "what") flopperParamLit)
          [.assign .storage flopperRef (.var "data")]
          [.require (.boolLit false)]]
        .reverted := by
    exact ExecBlock.consRevert (ExecStmt.iteFalse hflopper
      (ExecBlock.consRevert (ExecStmt.requireFalse hreqFalse)))
  have hblock :
      ExecBlock config { contract := contract, locals := locals } evm0 fileAddressTransition.body
        .reverted := by
    refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
    · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
    refine ExecBlock.consNormal (ExecStmt.requireTrue hguard) ?_
    exact ExecBlock.consRevert (ExecStmt.iteFalse hflapper helse)
  simpa [ExecTransitionBody, evm0, locals] using ExecFuncBody.execBlockRevert hblock

theorem vowReachFileAddressBody {cA gh bl σ σ₀ A I} {g : Sat256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
        ⟨737⟩ [vowSelWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty
        (cA, σ) k C := by
  have hword : vowSelWord I = ⟨3572022915⟩ :=
    vowSelWord_eq_of_beq I hsz 0xd4 0xe8 0xbe 0x83 ⟨3572022915⟩
      (by native_decide) hsel
  have hroot : UInt256.gt (armSelNat vowBytecode vowRootSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have hhigh : UInt256.gt (armSelNat vowBytecode vowHighSplitPc) (vowSelWord I) = ⟨0⟩ := by
    rw [hword]
    native_decide
  have heq0 : ∀ j, j < 2 →
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc j))
        (vowSelWord I) = ⟨0⟩ := by
    intro j hj
    interval_cases j <;> rw [hword] <;> native_decide
  have htake :
      UInt256.eq (armSelNat vowBytecode (nthArmPc vowBytecode vowHighHighFirstArmPc 2))
        (vowSelWord I) ≠ ⟨0⟩ := by
    rw [hword]
    native_decide
  exact vowReachHighHighBody 2 (by omega) ⟨737⟩ hcode hwv hsz hsize hroot hhigh heq0
    htake (by jump_dest) (by native_decide)

theorem RD.vowFileAddressDecodeToRoutine {code : ByteArray} {g : Sat256} {s0 : State}
    {ee : ExecutionEnv} {k C : ℕ} {ret de sel : UInt256} {R : List UInt256}
    {mem rdata : ByteArray} {aw : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD code ee g s0 ⟨759⟩ (de :: ⟨4⟩ :: ret :: sel :: R) mem aw rdata acc k C)
    (hwf : code = vowBytecode)
    (hroutine : (D_J code 0).contains ⟨4108⟩ = true)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨4108⟩
      (UInt256.land solcAddrMask (calldataWord ee.calldata 36) ::
        calldataWord ee.calldata 4 :: ret :: sel :: R)
      mem aw rdata acc k' C' := by
  subst hwf
  have rd760 := h.jumpdest (by native_decide) (by evm_ov)
  have rd761 := rd760.pop (by native_decide) (by evm_ov)
  have rd762 := rd761.dup1 (by native_decide) (by evm_ov)
  have rd763 := rd762.calldataload (by native_decide) (by evm_ov)
  have rd764 := rd763.swap1 (by native_decide) (by evm_ov)
  have rd766 := rd764.push1 ⟨32⟩ (by native_decide) (by evm_ov)
  have rd767 := rd766.add (by native_decide) (by evm_ov)
  have rd768 := rd767.calldataload (by native_decide) (by evm_ov)
  have rd770 := rd768.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd772 := rd770.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd774 := rd772.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd775 := rd774.shl (by native_decide) (by evm_ov)
  have rd776 := rd775.sub (by native_decide) (by evm_ov)
  have rd777 := rd776.and (by native_decide) (by evm_ov)
  have rd780 := rd777.push2 ⟨4108⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, by
    simpa [calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide,
      show (UInt256.add (⟨32⟩ : UInt256) ⟨4⟩).toNat = 36 from by decide,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd780.jump (by native_decide) hroutine (by evm_ov)⟩

theorem RD.vowFileAddressToSwitch {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨737⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩) :
    ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I) ⟨4197⟩
      (fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem)
      (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨737⟩) (ret := ⟨412⟩)
    (decoded := ⟨759⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.vowFileAddressDecodeToRoutine
    (code := vowBytecode) (ret := ⟨412⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  obtain ⟨_, _, hafterAuth⟩ := RD.vowAuthCheckOk
    (code := vowBytecode) (pc := ⟨4108⟩) (okPc := ⟨4197⟩)
    (key := fileAddressDataKey I) (ret := calldataWord I.calldata 4) (R := [⟨412⟩, sel])
    (by simpa [fileAddressDataKey, fileAddressDataWord] using hroutine)
    (by
      unfold vowAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    hauth (by jump_dest) (by simp)
  exact ⟨_, _, hafterAuth⟩

theorem RD.vowFileAddressAuthRevert {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨737⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩) :
    RDrev vowBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hdecoded⟩ := RD.solcTwoAddressExternalLenOk
    (code := vowBytecode) (sel := sel) (entry := ⟨737⟩) (ret := ⟨412⟩)
    (decoded := ⟨759⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by jump_dest) hsz68 hsize
  obtain ⟨_, _, hroutine⟩ := RD.vowFileAddressDecodeToRoutine
    (code := vowBytecode) (ret := ⟨412⟩) (sel := sel) (R := [])
    hdecoded rfl (by jump_dest) (by simp)
  exact RD.vowAuthCheckRevert
    (code := vowBytecode) (pc := ⟨4108⟩) (okPc := ⟨4197⟩)
    (key := fileAddressDataKey I) (ret := calldataWord I.calldata 4) (R := [⟨412⟩, sel])
    (by simpa [fileAddressDataKey, fileAddressDataWord] using hroutine)
    (by
      unfold vowAuthCheckWf
      repeat' first | apply And.intro | native_decide)
    (by
      unfold solcErrorStringRevertTailWf vowAuthTailPc vowNotAuthorizedRawWord
      repeat' first | apply And.intro | native_decide)
    hauth (by simp)

theorem RD.vowFileAddressSkipFlapper {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vowBytecode ee g s0 ⟨4197⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileAddressFlapperBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨4448⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd4198 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4199 := rd4198.dup2 (by native_decide) (by evm_ov)
  have rd4207 := rd4199.pushConst (⟨14414806689264313⟩ : UInt256)
    (width := 7) (op := .PUSH7) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4209 := rd4207.push1 ⟨201⟩ (by native_decide) (by evm_ov)
  have rd4210 := rd4209.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨14414806689264313⟩ ⟨201⟩ =
      ABI.bytesToWord fileAddressFlapperBytes := by
    native_decide
  rw [hconst] at rd4210
  have rd4211 := rd4210.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileAddressFlapperBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd4211
  have rd4212 := rd4211.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4212
  have rd4215 := rd4212.push2 ⟨4448⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4215.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

set_option maxHeartbeats 1000000 in
theorem RD.vowFileAddressFlapperToNopeExtcodesizeGuard
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vowBytecode ee g s0 ⟨4197⟩ (data :: what :: ret :: sel :: []) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileAddressFlapperBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨4284⟩
      (fileAddressVatTargetWord σ ee :: fileAddressVatTargetWord σ ee ::
        fileAddressCallOutSize :: fileAddressCallOutPtr :: fileAddressCallInSize ::
        fileAddressCallOutPtr :: fileAddressCallOutSize :: fileAddressCallEndPtr ::
        ⟨3696042234⟩ :: fileAddressVatTargetWord σ ee :: data :: what :: ret :: sel :: [])
      (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ ee) mem)
      (UInt256.ofNat 6) rdata (cA, σ) k' C' := by
  have rd4198 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4199 := rd4198.dup2 (by native_decide) (by evm_ov)
  have rd4207 := rd4199.pushConst (⟨14414806689264313⟩ : UInt256)
    (width := 7) (op := .PUSH7) (by decide) (by native_decide)
    (by simp only [List.length_cons, List.length_nil]; omega)
  have rd4209 := rd4207.push1 ⟨201⟩ (by native_decide) (by evm_ov)
  have rd4210 := rd4209.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨14414806689264313⟩ ⟨201⟩ =
      ABI.bytesToWord fileAddressFlapperBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd4210
  have rd4211 := rd4210.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd4211
  have rd4212 := rd4211.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4212
  have rd4215 := rd4212.push2 ⟨4448⟩ (by native_decide) (by evm_ov)
  have rd4216 := rd4215.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd4218 := rd4216.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4219₀⟩ := rd4218.sload (by native_decide) (by evm_ov)
  have rd4219 := by
    simpa [vowSlotWord, solcSlotWord] using rd4219₀
  have rd4221 := rd4219.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4222₀⟩ := rd4221.sload (by native_decide) (by evm_ov)
  have rd4222 := by
    simpa [vowSlotWord, solcSlotWord] using rd4222₀
  have hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 3 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hmem]; decide) (by decide) hread64
  have hNopeMem : (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ ee) mem).size =
      164 :=
    fileAddressNopeCalldataMem_size _ hmem
  have hNopeRead64 :
      (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ ee) mem).readWithPadding
          64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    fileAddressNopeCalldataMem_read64 _ hmem hread64
  have hmload64Nope :
      (if (⟨64⟩ : UInt256).toNat ≥
            (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ ee) mem).size
          ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian
          ((fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ ee) mem).readWithPadding
            (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ :=
    mloadFreePtrValue (by rw [hNopeMem]; decide) (by decide) hNopeRead64
  have rd4284 := evm_run rd4222 with [
    push1 ⟨64⟩,
    dup1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by native_decide)
      mem_cost hmload64 (by decide) (by evm_ov),
    push4 ⟨1848021117⟩,
    push1 ⟨225⟩,
    shl,
    dup2,
    raw mstore 6 (fileAddressNopeSelectorMem mem) (UInt256.ofNat 5) (by native_decide)
      mem_cost (by rfl) (by decide) (by evm_ov),
    push1 ⟨1⟩,
    push1 ⟨1⟩,
    push1 ⟨160⟩,
    shl,
    sub,
    swap3,
    dup4,
    and,
    push1 ⟨4⟩,
    dup3,
    add,
    raw mstore 3 (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ ee) mem)
      (UInt256.ofNat 6) (by native_decide) mem_cost (by
        simp [fileAddressNopeCalldataMem, fileAddressFlapperTargetWord, vowAddressReturnWord,
          vowSlotWord, solcSlotWord, solcAddrMask, u256_land_comm,
          show (((⟨128⟩ : UInt256) + ⟨4⟩).toNat) = 132 from by native_decide,
          show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            solcAddrMask from by decide])
      (by decide) (by evm_ov),
    swap1,
    raw mload 0 ⟨128⟩ (UInt256.ofNat 6) (by native_decide)
      mem_cost hmload64Nope (by decide) (by evm_ov),
    swap2,
    swap1,
    swap3,
    and,
    swap2,
    push4 ⟨3696042234⟩,
    swap2,
    push1 ⟨36⟩,
    dup1,
    dup4,
    add,
    swap3,
    push1 fileAddressCallOutSize,
    swap3,
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
  exact ⟨_, _, by
    simpa [fileAddressVatTargetWord, fileAddressFlapperTargetWord, vowAddressReturnWord,
      fileAddressNopeSelectorShifted, fileAddressNopeSelectorMem, fileAddressNopeCalldataMem,
      fileAddressCallOutPtr, fileAddressCallOutSize, fileAddressCallInSize,
      fileAddressCallEndPtr, vowSlotWord, solcSlotWord, solcAddrMask, hmatch, hconst,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide] using rd4284⟩

theorem RD.vowFileAddressFlapperToNopeCall
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vowBytecode ee g s0 ⟨4197⟩ (data :: what :: ret :: sel :: []) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileAddressFlapperBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (fileAddressVatTargetWord σ ee) ≠ ⟨0⟩) :
    ∃ gasWord k' C', RD vowBytecode ee g s0 ⟨4299⟩
      (gasWord :: fileAddressVatTargetWord σ ee :: fileAddressCallOutSize ::
        fileAddressCallOutPtr :: fileAddressCallInSize :: fileAddressCallOutPtr ::
        fileAddressCallOutSize :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ ee :: data :: what :: ret :: sel :: [])
      (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ ee) mem)
      (UInt256.ofNat 6) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, rd4284⟩ :=
    RD.vowFileAddressFlapperToNopeExtcodesizeGuard h hmatch hmem hread64
  obtain ⟨gasWord, k', C', rd4299⟩ :=
    RD.solcExtcodesizeGuardOkGas (pc := ⟨4284⟩) (okPc := ⟨4296⟩) rd4284
      hcodeSize
      (by native_decide) (by native_decide) (by native_decide) (by native_decide)
      (by native_decide) (by native_decide) (by jump_dest) (by native_decide)
      (by native_decide) (by native_decide) (by simp)
  exact ⟨gasWord, k', C', by simpa using rd4299⟩

theorem RD.vowFileAddressNopePostCall
    {cA gh bl σ σ₀ A I} {g sel : UInt256} {mem rdata : ByteArray} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4197⟩
      (fileAddressDataKey I :: calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: []) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : calldataWord I.calldata 4 = ABI.bytesToWord fileAddressFlapperBytes)
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hcodeSize :
      Reasoning.Theory.extCodeSizeWord σ (fileAddressVatTargetWord σ I) ≠ ⟨0⟩)
    (hdepth : I.depth.val < 1024)
    (hperm : I.perm = true) :
    ∃ (cA' : Batteries.RBSet AccountAddress compare) (σ' : AccountMap) (z : Bool)
      (out : ByteArray) (A' : Substate) (k' C' : ℕ),
      RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
          fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
          calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
        (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I) mem)
        (UInt256.ofNat 6) out (cA', σ') k' C'
    ∧ typedCallViaEVM config
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (EVM.address (AccountAddress.ofNat (fileAddressVatTargetWord σ I).toNat))
        "nope" 0
        [.address (AccountAddress.ofNat (fileAddressFlapperTargetWord σ I).toNat)]
        (z, { initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I with
              accountMap := σ', substate := A', createdAccounts := cA' }, out) true
    ∧ out.size < UInt256.size := by
  obtain ⟨gasWord, _, _, rd4299⟩ :=
    RD.vowFileAddressFlapperToNopeCall rd hmatch hmem hread64 hcodeSize
  obtain ⟨cA', σ', z, out, A_in, callGas, k4300, C4300, hΘpack, rd4300raw, houtsz⟩ :=
    RD.call rd4299 (by native_decide) hdepth (by evm_ov)
  obtain ⟨g'', A', hΘ⟩ := hΘpack
  refine ⟨cA', σ', z, out, A', k4300, C4300, ?_, ?_, houtsz⟩
  · have haw :
        UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat
          fileAddressCallOutPtr.toNat fileAddressCallInSize.toNat)
          fileAddressCallOutPtr.toNat fileAddressCallOutSize.toNat) = UInt256.ofNat 6 := by
      rw [fileAddressCallInSize_eq]
      unfold fileAddressCallOutPtr fileAddressCallOutSize
      native_decide
    have hmin : (min fileAddressCallOutSize (UInt256.ofNat out.size)).toNat = 0 := by
      unfold fileAddressCallOutSize
      rfl
    have rd4300 : RD vowBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
        ((if z then ⟨1⟩ else ⟨0⟩) :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
          fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
          calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
        (out.write 0 (fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I) mem)
          fileAddressCallOutPtr.toNat
          (min fileAddressCallOutSize (UInt256.ofNat out.size)).toNat)
        (UInt256.ofNat 6) out (cA', σ') k4300 C4300 :=
      haw ▸ rd4300raw
    rw [hmin, byteArray_write_len_zero] at rd4300
    exact rd4300
  · have hmask :
        UInt256.land (fileAddressFlapperTargetWord σ I) solcAddrMask =
          fileAddressFlapperTargetWord σ I := by
      simpa [fileAddressFlapperTargetWord, vowAddressReturnWord] using
        (solcAddrMask_clean
          (w := UInt256.land (vowSlotWord ⟨2⟩ σ I) solcAddrMask)
          (solcAddrMask_result_canonical (vowSlotWord ⟨2⟩ σ I)))
    refine callCoincides (A_in := A_in) (g'' := g'') (callGas := callGas)
      (callPerm := true) (targetWord := fileAddressVatTargetWord σ I)
      (mem := fileAddressNopeCalldataMem (fileAddressFlapperTargetWord σ I) mem)
      (inOff := fileAddressCallOutPtr) (inSize := fileAddressCallInSize)
      (fun h => absurd hdepth (by rw [show I.depth = (1024 : Fin 1025) from h]; decide))
      (fileAddressVatAddress_eq_target σ I) ?_ ?_
    · simpa [hmask] using fileAddressNopeEncode_eq (fileAddressFlapperTargetWord σ I) hmem
    · simpa [initState, hperm] using hΘ

theorem RD.vowFileAddressNopeCallFailure
    {cA gh bl σ σ₀ A I} {g sel : UInt256}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    (rd : RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨4300⟩
      (⟨0⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ I :: fileAddressDataKey I ::
        calldataWord I.calldata 4 :: ⟨412⟩ :: sel :: [])
      mem aw rdata acc k C)
    (hrdataSize : rdata.size < UInt256.size) :
    RDrev vowBytecode (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) := by
  exact RD.solcCallSuccessGuardMissing (pc := ⟨4300⟩) (okPc := ⟨4316⟩) rd
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    hrdataSize (by simp)

theorem RD.vowFileAddressNopeSuccessStoreFlapper
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (rd : RD vowBytecode ee g s0 ⟨4300⟩
      (⟨1⟩ :: fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ ee :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA, σ) k C)
    (hperm : ee.perm = true) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨4350⟩
      (UInt256.land solcAddrMask data :: solcAddrMask :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ ee :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨2⟩
        (setAddressOffset0Word (solcSlotWord σ ee ⟨2⟩) data)) k' C' := by
  obtain ⟨k4318, C4318, rd4318⟩ := RD.solcCallSuccessGuardOk
    (pc := ⟨4300⟩) (okPc := ⟨4316⟩) rd
    (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by jump_dest) (by native_decide) (by native_decide) (by simp)
  have rd4318' : RD vowBytecode ee g s0 ⟨4318⟩
      (fileAddressCallEndPtr :: ⟨3696042234⟩ ::
        fileAddressVatTargetWord σ ee :: data :: what :: ret :: sel :: [])
      mem (UInt256.ofNat 6) rdata (cA, σ) k4318 C4318 := by
    simpa [show ((⟨4316⟩ : UInt256) + ⟨1⟩ + ⟨1⟩) = ⟨4318⟩ from by native_decide]
      using rd4318
  have rd4319 := rd4318'.pop (by native_decide) (by evm_ov)
  have rd4321 := rd4319.push1 ⟨2⟩ (by native_decide) (by evm_ov)
  have rd4322 := rd4321.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4323⟩ := rd4322.sload (by native_decide) (by evm_ov)
  have rd4325 := rd4323.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4327 := rd4325.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4329 := rd4327.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4330 := rd4329.shl (by native_decide) (by evm_ov)
  have rd4331 := rd4330.sub (by native_decide) (by evm_ov)
  have rd4332 := rd4331.not (by native_decide) (by evm_ov)
  have rd4333 := rd4332.and (by native_decide) (by evm_ov)
  have rd4335 := rd4333.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4337 := rd4335.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4339 := rd4337.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4340 := rd4339.shl (by native_decide) (by evm_ov)
  have rd4341 := rd4340.sub (by native_decide) (by evm_ov)
  have rd4342 := rd4341.dup6 (by native_decide) (by evm_ov)
  have rd4343 := rd4342.dup2 (by native_decide) (by evm_ov)
  have rd4344 := rd4343.and (by native_decide) (by evm_ov)
  have rd4345 := rd4344.swap2 (by native_decide) (by evm_ov)
  have rd4346 := rd4345.dup3 (by native_decide) (by evm_ov)
  have rd4347 := rd4346.lor (by native_decide) (by evm_ov)
  have rd4348 := rd4347.swap1 (by native_decide) (by evm_ov)
  have rd4349 := rd4348.swap3 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4350⟩ := rd4349.sstore hperm (by native_decide) (by evm_ov)
  have hword :
      UInt256.lor (UInt256.land solcAddrMask data)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨2⟩)) =
        setAddressOffset0Word (solcSlotWord σ ee ⟨2⟩) data := by
    calc
      UInt256.lor (UInt256.land solcAddrMask data)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨2⟩)) =
          UInt256.lor (UInt256.land data solcAddrMask)
            (UInt256.land (solcSlotWord σ ee ⟨2⟩) (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm solcAddrMask data,
              u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨2⟩)]
      _ = UInt256.lor (UInt256.land (solcSlotWord σ ee ⟨2⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land data solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (solcSlotWord σ ee ⟨2⟩) data := by
            rfl
  have hpc4350 :
      (⟨4318⟩ : UInt256) + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + UInt256.ofNat 2 + UInt256.ofNat 2 +
          ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ +
          ⟨1⟩ + ⟨1⟩ = ⟨4350⟩ := by
    native_decide
  rw [hpc4350] at rd4350
  exact ⟨_, _, by
    simpa [solcSlotWord, hword,
        show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
          solcAddrMask from by decide]
      using rd4350⟩

theorem RD.vowFileAddressSkipFlopper {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (h : RD vowBytecode ee g s0 ⟨4448⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k C)
    (hneq : what ≠ ABI.bytesToWord fileAddressFlopperBytes)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ⟨2156⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata acc k' C' := by
  have rd4449 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4450 := rd4449.dup2 (by native_decide) (by evm_ov)
  have rd4458 := rd4450.pushConst (⟨14414836754035385⟩ : UInt256)
    (width := 7) (op := .PUSH7) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4460 := rd4458.push1 ⟨201⟩ (by native_decide) (by evm_ov)
  have rd4461 := rd4460.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨14414836754035385⟩ ⟨201⟩ =
      ABI.bytesToWord fileAddressFlopperBytes := by
    native_decide
  rw [hconst] at rd4461
  have rd4462 := rd4461.eq (by native_decide) (by evm_ov)
  have heq0 : UInt256.eq (ABI.bytesToWord fileAddressFlopperBytes) what = ⟨0⟩ := by
    exact u256_eq_of_ne (fun h => hneq h.symm)
  rw [heq0] at rd4462
  have rd4463 := rd4462.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨0⟩ : UInt256) = ⟨1⟩ from by decide] at rd4463
  have rd4466 := rd4463.push2 ⟨2156⟩ (by native_decide) (by evm_ov)
  exact ⟨_, _, rd4466.jumpiT (by native_decide) one_ne_zero_uint (by jump_dest)
    (by evm_ov)⟩

theorem RD.vowFileAddressStoreFlopper {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {k C : ℕ} {data what ret sel : UInt256} {R : List UInt256} {mem rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (h : RD vowBytecode ee g s0 ⟨4448⟩ (data :: what :: ret :: sel :: R) mem
      (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hmatch : what = ABI.bytesToWord fileAddressFlopperBytes)
    (hret : (D_J vowBytecode 0).contains ret = true)
    (hperm : ee.perm = true)
    (hov : R.length + 21 ≤ 1024) :
    ∃ k' C', RD vowBytecode ee g s0 ret (sel :: R) mem (UInt256.ofNat 3) rdata
      (cA, sstoreAccountMap ee.codeOwner σ ⟨3⟩
        (setAddressOffset0Word (solcSlotWord σ ee ⟨3⟩) data)) k' C' := by
  have rd4449 := h.jumpdest (by native_decide) (by evm_ov)
  have rd4450 := rd4449.dup2 (by native_decide) (by evm_ov)
  have rd4458 := rd4450.pushConst (⟨14414836754035385⟩ : UInt256)
    (width := 7) (op := .PUSH7) (by decide) (by native_decide)
    (by simp only [List.length_cons]; omega)
  have rd4460 := rd4458.push1 ⟨201⟩ (by native_decide) (by evm_ov)
  have rd4461 := rd4460.shl (by native_decide) (by evm_ov)
  have hconst : UInt256.shiftLeft ⟨14414836754035385⟩ ⟨201⟩ =
      ABI.bytesToWord fileAddressFlopperBytes := by
    native_decide
  rw [hmatch, ← hconst] at rd4461
  have rd4462 := rd4461.eq (by native_decide) (by evm_ov)
  rw [uInt256_eq_self] at rd4462
  have rd4463 := rd4462.iszero (by native_decide) (by evm_ov)
  rw [show UInt256.isZero (⟨1⟩ : UInt256) = ⟨0⟩ from by decide] at rd4463
  have rd4466 := rd4463.push2 ⟨2156⟩ (by native_decide) (by evm_ov)
  have rd4467 := rd4466.jumpiNT (by native_decide)
    (by decide : (⟨0⟩ : UInt256) = ⟨0⟩) (by evm_ov)
  have rd4469 := rd4467.push1 ⟨3⟩ (by native_decide) (by evm_ov)
  have rd4470 := rd4469.dup1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4471⟩ := rd4470.sload (by native_decide) (by evm_ov)
  have rd4473 := rd4471.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4475 := rd4473.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4477 := rd4475.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4478 := rd4477.shl (by native_decide) (by evm_ov)
  have rd4479 := rd4478.sub (by native_decide) (by evm_ov)
  have rd4480 := rd4479.not (by native_decide) (by evm_ov)
  have rd4481 := rd4480.and (by native_decide) (by evm_ov)
  have rd4483 := rd4481.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4485 := rd4483.push1 ⟨1⟩ (by native_decide) (by evm_ov)
  have rd4487 := rd4485.push1 ⟨160⟩ (by native_decide) (by evm_ov)
  have rd4488 := rd4487.shl (by native_decide) (by evm_ov)
  have rd4489 := rd4488.sub (by native_decide) (by evm_ov)
  have rd4490 := rd4489.dup4 (by native_decide) (by evm_ov)
  have rd4491 := rd4490.and (by native_decide) (by evm_ov)
  have rd4492 := rd4491.lor (by native_decide) (by evm_ov)
  have rd4493 := rd4492.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, rd4494⟩ := rd4493.sstore hperm (by native_decide) (by evm_ov)
  have rd4497 := rd4494.push2 ⟨2233⟩ (by native_decide) (by evm_ov)
  have rd2233 := rd4497.jump (by native_decide) (by jump_dest) (by evm_ov)
  have rd2234 := rd2233.jumpdest (by native_decide) (by evm_ov)
  have rd2235 := rd2234.pop (by native_decide) (by evm_ov)
  have rd2236 := rd2235.pop (by native_decide) (by evm_ov)
  have hword :
      UInt256.lor (UInt256.land data solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨3⟩)) =
        setAddressOffset0Word (solcSlotWord σ ee ⟨3⟩) data := by
    calc
      UInt256.lor (UInt256.land data solcAddrMask)
          (UInt256.land (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨3⟩)) =
          UInt256.lor (UInt256.land data solcAddrMask)
            (UInt256.land (solcSlotWord σ ee ⟨3⟩) (UInt256.lnot solcAddrMask)) := by
            rw [u256_land_comm (UInt256.lnot solcAddrMask) (solcSlotWord σ ee ⟨3⟩)]
      _ = UInt256.lor (UInt256.land (solcSlotWord σ ee ⟨3⟩) (UInt256.lnot solcAddrMask))
            (UInt256.land data solcAddrMask) := by
            exact u256_lor_comm _ _
      _ = setAddressOffset0Word (solcSlotWord σ ee ⟨3⟩) data := by
            rfl
  exact ⟨_, _, by
    simpa [solcSlotWord, setAddressOffset0Word, hword,
      show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        solcAddrMask from by decide]
      using rd2236.jump (by native_decide) hret (by evm_ov)⟩

theorem RD.vowFileAddressFlopperSuccess {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨737⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hperm : I.perm = true)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotFlapper : fileAddressWhat I ≠ fileAddressFlapperBytes)
    (hwhat : fileAddressWhat I = fileAddressFlopperBytes) :
    RDret vowBytecode g (initState cA gh bl σ σ₀ g A I)
      (cA, sstoreAccountMap I.codeOwner σ ⟨3⟩
        (setAddressOffset0Word (solcSlotWord σ I ⟨3⟩) (fileAddressDataKey I)))
      ByteArray.empty := by
  obtain ⟨_, _, hswitch⟩ := RD.vowFileAddressToSwitch hreach hsz68 hsize hauth
  have hflapperNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressFlapperBytes :=
    fileAddressWhatWord_ne_of_bytes_ne (by omega) hnotFlapper (by native_decide)
  obtain ⟨_, _, hflopperPc⟩ := RD.vowFileAddressSkipFlapper
    (data := fileAddressDataKey I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hswitch hflapperNe (by simp)
  have hword :
      calldataWord I.calldata 4 = ABI.bytesToWord fileAddressFlopperBytes :=
    fileAddressWhatWord_eq_of_bytes_eq (by omega) hwhat
  obtain ⟨_, _, hretPc⟩ := RD.vowFileAddressStoreFlopper
    (data := fileAddressDataKey I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hflopperPc hword (by jump_dest) hperm (by simp)
  have hretPc' := hretPc.jumpdest (by native_decide) (by evm_ov)
  exact RD.stop hretPc' (by native_decide) (by simp)

theorem RD.vowFileAddressUnrecognizedParamRevert
    {cA gh bl σ σ₀ A I} {g : Sat256} {sel : UInt256}
    (hreach : ∃ k C, RD vowBytecode I g (initState cA gh bl σ σ₀ g A I)
      ⟨737⟩ [sel] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hauth :
      solcSlotWord σ I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩)
    (hnotFlapper : fileAddressWhat I ≠ fileAddressFlapperBytes)
    (hnotFlopper : fileAddressWhat I ≠ fileAddressFlopperBytes) :
    RDrev vowBytecode g (initState cA gh bl σ σ₀ g A I) := by
  obtain ⟨_, _, hswitch⟩ := RD.vowFileAddressToSwitch hreach hsz68 hsize hauth
  have hflapperNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressFlapperBytes :=
    fileAddressWhatWord_ne_of_bytes_ne (by omega) hnotFlapper (by native_decide)
  obtain ⟨_, _, hflopperPc⟩ := RD.vowFileAddressSkipFlapper
    (data := fileAddressDataKey I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hswitch hflapperNe (by simp)
  have hflopperNe :
      calldataWord I.calldata 4 ≠ ABI.bytesToWord fileAddressFlopperBytes :=
    fileAddressWhatWord_ne_of_bytes_ne (by omega) hnotFlopper (by native_decide)
  obtain ⟨_, _, htailPc⟩ := RD.vowFileAddressSkipFlopper
    (data := fileAddressDataKey I) (what := calldataWord I.calldata 4) (ret := ⟨412⟩)
    (sel := sel) (R := []) hflopperPc hflopperNe (by simp)
  have hmemAuth :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).size = 96 :=
    twoWordHashMem_size_96 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
  have hread64 :
      (twoWordHashMem (solcSourceWord I) ⟨0⟩ solcFreePtrMem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩ :=
    twoWordHashMem_read64 (solcSourceWord I) ⟨0⟩ solcFreePtrMem_size
      solcFreePtrMem_read64
  exact RD.vowFileUintUnrecognizedRevert htailPc hmemAuth hread64 (by simp)

theorem vowFileAddressFlopperAuthorizedBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hnotFlapper : fileAddressWhat I ≠ fileAddressFlapperBytes)
    (hwhat : fileAddressWhat I = fileAddressFlopperBytes) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let dataKey := fileAddressDataKey I
  let locals := fileAddressLocals I
  let callerSlot := vowCallerWardsSlot I
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hflopperWord : vowSlotWord ⟨3⟩ σ_evm I = vowSlotWord ⟨3⟩ σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨3⟩ ⟨0⟩
  have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauthEvm
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
  let stored := setAddressOffset0Word (solcSlotWord σ_evm I ⟨3⟩) dataKey
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let evm1 := Solm.EVM.storageStore evm0 I.codeOwner ⟨3⟩ stored
  have hstoredSolm :
      stored = setAddressOffset0Word (solcSlotWord σ_solm I ⟨3⟩) dataKey := by
    simpa [stored, vowSlotWord] using congrArg (fun old => setAddressOffset0Word old dataKey)
      hflopperWord
  have hbody :
      ExecTransitionBody config contract evm0 locals fileAddressTransition.body
        (.returned { contract := contract, locals := locals } evm1 none) := by
    simpa [evm0, evm1, locals, dataKey, stored, hstoredSolm, solcSlotWord, initState,
      Solm.EVM.storageLoad] using
        (fileAddressFlopperSourceBody (cA := cA) (gh := gh) (bl := bl)
          (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          hwv hauthSolm hnotFlapper hwhat)
  have hret := RD.vowFileAddressFlopperSuccess hreach hperm hsz68 hsize hauthSolc
    hnotFlapper hwhat
  have hcreated :
      (cA, sstoreAccountMap I.codeOwner σ_evm ⟨3⟩ stored).1 = evm1.createdAccounts := by
    simp [evm1, evm0, initState, storageStore_createdAccounts]
  have haccounts :
      accountMapEquiv (sstoreAccountMap I.codeOwner σ_evm ⟨3⟩ stored)
        evm1.accountMap := by
    have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩ stored hAccounts
    simpa [evm1, evm0, initState, storageStore_accountMap, stored, hstoredSolm, solcSlotWord,
      Solm.EVM.storageLoad] using hbase
  have henc : returnEquiv ByteArray.empty none fileAddressTransition.returnType := by
    rw [show fileAddressTransition.returnType = [] by rfl]
    exact returnEquiv.fallthrough rfl (by rfl) (by native_decide)
  have hret' :
      RDret vowBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cA, sstoreAccountMap I.codeOwner σ_evm ⟨3⟩ stored) ByteArray.empty := by
    simpa [stored, dataKey] using hret
  exact hret'.reEquivExecutionGenAccountMapEquiv hcode hdispatch hdecode hbody
    hcreated haccounts henc

theorem vowFileAddressUnrecognizedAuthorizedBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I = ⟨1⟩)
    (hnotFlapper : fileAddressWhat I ≠ fileAddressFlapperBytes)
    (hnotFlopper : fileAddressWhat I ≠ fileAddressFlopperBytes) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileAddressLocals I
  let callerSlot := vowCallerWardsSlot I
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hauthSolm : vowSlotWord callerSlot σ_solm I = ⟨1⟩ := by
    rw [← hcallerWord]
    exact hauthEvm
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) = ⟨1⟩ := by
    simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
    simpa [evm0, locals] using
      (fileAddressUnrecognizedSourceBody (cA := cA) (gh := gh) (bl := bl)
        (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hwv hauthSolm hnotFlapper hnotFlopper)
  have hrev := RD.vowFileAddressUnrecognizedParamRevert hreach hsz68 hsize hauthSolc
    hnotFlapper hnotFlopper
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFileAddressAuthRevertBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hauthEvm : vowSlotWord (vowCallerWardsSlot I) σ_evm I ≠ ⟨1⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let locals := fileAddressLocals I
  let callerSlot := vowCallerWardsSlot I
  have hcallerWord : vowSlotWord callerSlot σ_evm I = vowSlotWord callerSlot σ_solm I :=
    accountMapEquiv_storage_findD hAccounts I.codeOwner callerSlot ⟨0⟩
  have hauthSolm : vowSlotWord callerSlot σ_solm I ≠ ⟨1⟩ := by
    intro hsolm
    exact hauthEvm (by rw [hcallerWord, hsolm])
  let evm0 := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody : ExecTransitionBody config contract evm0 locals fileAddressTransition.body .reverted := by
    have hguard := vowAuthGuardEval_false (cA := cA) (gh := gh) (bl := bl)
      (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (locals := locals)
      (by simp [locals, fileAddressLocals]) hauthSolm
    have hblock := nonpayableSecondRequireReverts
      (cfg := config) (solm := { contract := contract, locals := locals })
      (evm := evm0)
      (guard := .binary .eq (.storage (wardsRef sender)) (.intLit 1))
      (rest := [
        .ite
          (.binary .eq (.var "what") flapperParamLit)
          (checkedExternalCallStmts (.storage vatRef) "nope" (.intLit 0)
              [.storage flapperRef] "_nopeRet" ++
            [ .assign .storage flapperRef (.var "data") ] ++
            checkedExternalCallStmts (.storage vatRef) "hope" (.intLit 0)
              [.var "data"] "_hopeRet")
          [ .ite
              (.binary .eq (.var "what") flopperParamLit)
              [ .assign .storage flopperRef (.var "data") ]
              [ .require (.boolLit false) ] ] ])
      (by simp [evm0, initState]; exact hwv)
      hguard
    simpa [ExecTransitionBody, fileAddressTransition, nonpayable, auth, evm0, locals] using
      ExecFuncBody.execBlockRevert hblock
  have hauthSolc :
      solcSlotWord σ_evm I (solcMappingSlot ⟨0⟩ (solcSourceWord I)) ≠ ⟨1⟩ := by
    simpa [callerSlot, vowCallerWardsSlot, vowSlotWord] using hauthEvm
  have hrev := RD.vowFileAddressAuthRevert hreach hsz68 hsize hauthSolc
  exact hrev.reEquivExecutionRevert hcode hdispatch hdecode hbody

theorem vowFileAddressNonFlapperBodyCore
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {sel : UInt256}
    (hcode : I.code = vowBytecode) (hwv : I.weiValue = ⟨0⟩)
    (hperm : I.perm = true) (hsz68 : 68 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hdispatch : dispatchMsg contract I.calldata = some fileAddressTransition)
    (hdecode :
      decodeCalldataWithMode config.abiDecodeMode (fileAddressTransition.params.map Param.name)
        (transitionSignature fileAddressTransition).paramTypes I.calldata =
          some (fileAddressLocals I))
    (hreach : ∃ k C, RD vowBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨737⟩ [sel]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ_evm) k C)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hnotFlapper : fileAddressWhat I ≠ fileAddressFlapperBytes) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let callerSlot := vowCallerWardsSlot I
  by_cases hauthEvm : vowSlotWord callerSlot σ_evm I = ⟨1⟩
  · by_cases hflopper : fileAddressWhat I = fileAddressFlopperBytes
    · exact vowFileAddressFlopperAuthorizedBodyCore (sel := sel) hcode hwv hperm hsz68 hsize
        hdispatch hdecode hreach hAccounts (by simpa [callerSlot] using hauthEvm)
        hnotFlapper hflopper
    · exact vowFileAddressUnrecognizedAuthorizedBodyCore (sel := sel) hcode hwv hsz68 hsize
        hdispatch hdecode hreach hAccounts (by simpa [callerSlot] using hauthEvm)
        hnotFlapper hflopper
  · exact vowFileAddressAuthRevertBodyCore (sel := sel) hcode hwv hsz68 hsize hdispatch
      hdecode hreach hAccounts (by simpa [callerSlot] using hauthEvm)

theorem vowFileAddressNonFlapperBody {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz68 : 68 ≤ I.calldata.size)
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hnotFlapper : fileAddressWhat I ≠ fileAddressFlapperBytes) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hsz4 : 4 ≤ I.calldata.size := by omega
  exact vowFileAddressNonFlapperBodyCore (sel := vowSelWord I) hcode hwv hperm hsz68 hsize
    (vowDispatch_fileAddress hsel)
    (by simpa [fileAddressLocals] using vowDecode_fileAddress_ok (I := I) hsz68)
    (vowReachFileAddressBody (g := Sat256.ofUInt256 g) hcode hwv hsz4 hsize hsel)
    hAccounts hnotFlapper

theorem vowFileAddressShort {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    (hcode : I.code = vowBytecode) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true) (hwv : I.weiValue = ⟨0⟩)
    (hsz4 : 4 ≤ I.calldata.size) (hshort : I.calldata.size < 68)
    (hsel : selIs I ⟨#[0xd4, 0xe8, 0xbe, 0x83]⟩)
    (_hAccounts : accountMapEquiv σ_evm σ_solm) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hreach :=
    vowReachFileAddressBody (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
      (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      hcode hwv hsz4 hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨64⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by simpa using hsz4) hsize]
    change I.calldata.size - 4 < 64
    omega
  have hrev := RD.solcExternalStaticArgsShortReverts
    (code := vowBytecode) (sel := vowSelWord I) (entry := ⟨737⟩) (ret := ⟨412⟩)
    (decoded := ⟨759⟩) (need := ⟨64⟩) hreach
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide) (by native_decide) hlt
  exact hrev.reEquivDecodingFailed hcode (vowDispatch_fileAddress hsel)
    (vowDecode_fileAddress_none_short hsz4 hshort)

end Benchmarks.Dss.Vow
