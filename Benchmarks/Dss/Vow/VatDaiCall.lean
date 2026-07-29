import Benchmarks.Dss.Vow.Kiss

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Vow

/-! Shared memory facts for solc-generated `vat.dai(address(this))` calls from any
    164-byte memory with the standard free-memory pointer at offset 64. -/

noncomputable def vatDaiSelectorMem (mem : ByteArray) : ByteArray :=
  kissDaiSelectorShifted.toByteArray.write 0 mem 128 32

noncomputable def vatDaiCalldataMem (I : ExecutionEnv) (mem : ByteArray) : ByteArray :=
  (UInt256.ofNat I.codeOwner.val).toByteArray.write 0 (vatDaiSelectorMem mem) 132 32

noncomputable def vatDaiCalldataMemFor (arg : UInt256) (mem : ByteArray) : ByteArray :=
  arg.toByteArray.write 0 (vatDaiSelectorMem mem) 132 32

theorem vatDaiSelectorMem_size {mem : ByteArray} (hmem : mem.size = 164) :
    (vatDaiSelectorMem mem).size = 164 := by
  unfold vatDaiSelectorMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by rw [hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, hmem, toByteArray_size]
  omega

theorem vatDaiSelectorMem_read64 {mem : ByteArray} (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (vatDaiSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold vatDaiSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
    (by rw [hmem]; omega) (by omega), hread64]

theorem vatDaiCalldataMem_size (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (vatDaiCalldataMem I mem).size = 164 := by
  unfold vatDaiCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [vatDaiSelectorMem_size hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, vatDaiSelectorMem_size hmem, toByteArray_size]
  omega

theorem vatDaiCalldataMem_read64 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (vatDaiCalldataMem I mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold vatDaiCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [vatDaiSelectorMem_size hmem]; omega) (by omega),
    vatDaiSelectorMem_read64 hmem hread64]

theorem vatDaiCalldataMemFor_size (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (vatDaiCalldataMemFor arg mem).size = 164 := by
  unfold vatDaiCalldataMemFor
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [vatDaiSelectorMem_size hmem]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, vatDaiSelectorMem_size hmem, toByteArray_size]
  omega

theorem vatDaiCalldataMemFor_read64 (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (vatDaiCalldataMemFor arg mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold vatDaiCalldataMemFor
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [vatDaiSelectorMem_size hmem]; omega) (by omega),
    vatDaiSelectorMem_read64 hmem hread64]

theorem vatDaiSelectorMem_size_of_size96 {mem : ByteArray} (hmem : mem.size = 96) :
    (vatDaiSelectorMem mem).size = 160 := by
  unfold vatDaiSelectorMem
  exact toByteArray_write32_size_of_ge mem kissDaiSelectorShifted 128 96 160 hmem
    (by omega) (by native_decide) (by omega)

theorem vatDaiSelectorMem_read64_of_size96 {mem : ByteArray} (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (vatDaiSelectorMem mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold vatDaiSelectorMem
  rw [toByteArray_write_read_below_of_gap kissDaiSelectorShifted mem 128 64
    (by rw [hmem]) (by omega) (by rw [hmem]; native_decide), hread64]

theorem vatDaiCalldataMemFor_size_of_size96 (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (vatDaiCalldataMemFor arg mem).size = 164 := by
  unfold vatDaiCalldataMemFor
  exact toByteArray_write32_size_of_le (vatDaiSelectorMem mem) arg 132 160 164
    (vatDaiSelectorMem_size_of_size96 hmem)
    (by rw [vatDaiSelectorMem_size_of_size96 hmem]; omega)
    (by omega)

theorem vatDaiCalldataMemFor_read64_of_size96 (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (vatDaiCalldataMemFor arg mem).readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
  unfold vatDaiCalldataMemFor
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [vatDaiSelectorMem_size_of_size96 hmem]; omega) (by omega),
    vatDaiSelectorMem_read64_of_size96 hmem hread64]

theorem vatDaiSelectorMem_selector {mem : ByteArray} (hmem : mem.size = 164) :
    (vatDaiSelectorMem mem).extract 128 132 = kissDaiSelector := by
  unfold vatDaiSelectorMem
  rw [write32_eq _ _ 128 (by rw [toByteArray_size]) (by rw [hmem]; omega)]
  have hAsz : (mem.extract 0 128).size = 128 := by
    rw [ByteArray.size_extract, hmem]
    omega
  have hBsz : (kissDaiSelectorShifted.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hABsz :
      (mem.extract 0 128 ++ kissDaiSelectorShifted.toByteArray.extract 0 32).size = 160 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  rw [extract_append_left _ _ 128 132 (by rw [hABsz]; omega),
    extract_append_right_window _ _ 128 132 (by rw [hAsz]),
    hAsz, show 128 - 128 = 0 from rfl, show 132 - 128 = 4 from rfl,
    extract_extract_BA,
    show 0 + 0 = 0 from rfl, show min (0 + 4) 32 = 4 from by omega,
    toByteArray_eq_toBytesBE]
  native_decide

theorem vatDaiSelectorMem_selector_of_size96 {mem : ByteArray} (hmem : mem.size = 96) :
    (vatDaiSelectorMem mem).extract 128 132 = kissDaiSelector := by
  have hread : (vatDaiSelectorMem mem).readWithPadding 128 4 = kissDaiSelector := by
    unfold vatDaiSelectorMem
    rw [toByteArray_write_read_window_of_gap kissDaiSelectorShifted mem 128 0 4
      (by omega) (by norm_num) (by norm_num) (by rw [hmem]; native_decide),
      show 0 + 4 = 4 from rfl,
      toByteArray_eq_toBytesBE]
    native_decide
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
      (by rw [vatDaiSelectorMem_size_of_size96 hmem]; omega)] at hread
  simpa using hread

theorem vatDaiCalldataMem_read128_36 (I : ExecutionEnv) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (vatDaiCalldataMem I mem).readWithPadding 128 36 =
      kissDaiSelector ++ (UInt256.ofNat I.codeOwner.val).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [vatDaiCalldataMem_size I hmem]), vatDaiCalldataMem,
    write32_eq _ (vatDaiSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [vatDaiSelectorMem_size hmem]; omega)]
  have hAsz : ((vatDaiSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, vatDaiSelectorMem_size hmem]
    omega
  have hBsz : (((UInt256.ofNat I.codeOwner.val).toByteArray).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((vatDaiSelectorMem mem).extract 0 132 ++
        ((UInt256.ofNat I.codeOwner.val).toByteArray).extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull :
      ((UInt256.ofNat I.codeOwner.val).toByteArray).extract 0 32 =
        (UInt256.ofNat I.codeOwner.val).toByteArray := by
    have h := @ByteArray.extract_zero_size (UInt256.ofNat I.codeOwner.val).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), vatDaiSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem vatDaiCalldataMemFor_read128_36_of_size96 (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    (vatDaiCalldataMemFor arg mem).readWithPadding 128 36 =
      kissDaiSelector ++ arg.toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [vatDaiCalldataMemFor_size_of_size96 arg hmem]), vatDaiCalldataMemFor,
    write32_eq _ (vatDaiSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [vatDaiSelectorMem_size_of_size96 hmem]; omega)]
  have hAsz : ((vatDaiSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, vatDaiSelectorMem_size_of_size96 hmem]
    omega
  have hBsz : (arg.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((vatDaiSelectorMem mem).extract 0 132 ++ arg.toByteArray.extract 0 32).size =
        164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : arg.toByteArray.extract 0 32 = arg.toByteArray := by
    have h := @ByteArray.extract_zero_size arg.toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), vatDaiSelectorMem_selector_of_size96 hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem vatDaiCalldataMemFor_read128_36 (arg : UInt256) {mem : ByteArray}
    (hmem : mem.size = 164) :
    (vatDaiCalldataMemFor arg mem).readWithPadding 128 36 =
      kissDaiSelector ++ arg.toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [vatDaiCalldataMemFor_size arg hmem]), vatDaiCalldataMemFor,
    write32_eq _ (vatDaiSelectorMem mem) 132 (by rw [toByteArray_size])
      (by rw [vatDaiSelectorMem_size hmem]; omega)]
  have hAsz : ((vatDaiSelectorMem mem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, vatDaiSelectorMem_size hmem]
    omega
  have hBsz : (arg.toByteArray.extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((vatDaiSelectorMem mem).extract 0 132 ++ arg.toByteArray.extract 0 32).size =
        164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull : arg.toByteArray.extract 0 32 = arg.toByteArray := by
    have h := @ByteArray.extract_zero_size arg.toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), vatDaiSelectorMem_selector hmem,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem vatDaiEncode_eq (I : ExecutionEnv) {mem : ByteArray} (hmem : mem.size = 164) :
    config.externalABI.encode? "dai" [.address I.codeOwner] =
      some ((vatDaiCalldataMem I mem).readWithPadding 128 36) := by
  rw [vatDaiCalldataMem_read128_36 I hmem]
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr,
    vatDaiSelector, selectorBytes, kissDaiSelector]
  rw [show EVM.word (↑I.codeOwner : ℕ) = UInt256.ofNat (↑I.codeOwner : ℕ) from rfl]
  rw [word_toBytesBE_toByteArray_eq_toByteArray]

theorem vatDaiEncodeMasked_eq (w : UInt256) {mem : ByteArray} (hmem : mem.size = 164) :
    config.externalABI.encode? "dai"
        [.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)] =
      some ((vatDaiCalldataMemFor (UInt256.land w solcAddrMask) mem).readWithPadding
        128 36) := by
  rw [vatDaiCalldataMemFor_read128_36 _ hmem]
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
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, vatDaiSelector, selectorBytes,
    kissDaiSelector, hword, word_toBytesBE_toByteArray_eq_toByteArray]

theorem vatDaiEncodeMasked_eq_of_size96 (w : UInt256) {mem : ByteArray}
    (hmem : mem.size = 96) :
    config.externalABI.encode? "dai"
        [.address (AccountAddress.ofNat (UInt256.land w solcAddrMask).toNat)] =
      some ((vatDaiCalldataMemFor (UInt256.land w solcAddrMask) mem).readWithPadding
        128 36) := by
  rw [vatDaiCalldataMemFor_read128_36_of_size96 _ hmem]
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
    ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr, vatDaiSelector, selectorBytes,
    kissDaiSelector, hword, word_toBytesBE_toByteArray_eq_toByteArray]

theorem vatDaiWrite_size (I : ExecutionEnv) {mem : ByteArray} (o : ByteArray) (L : ℕ)
    (hmem : mem.size = 164) (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (vatDaiCalldataMem I mem) 128 L).size = 164 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact vatDaiCalldataMem_size I hmem
  · rw [write_eq_gen o (vatDaiCalldataMem I mem) 128 L (by omega) hLo
      (by rw [vatDaiCalldataMem_size I hmem]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, vatDaiCalldataMem_size I hmem]
    omega

theorem vatDaiWrite_read64 (I : ExecutionEnv) {mem : ByteArray} (o : ByteArray) (L : ℕ)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (vatDaiCalldataMem I mem) 128 L).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact vatDaiCalldataMem_read64 I hmem hread64
  · rw [write_read_below_gen o (vatDaiCalldataMem I mem) 128 L 64
      (by omega) hLo (by rw [vatDaiCalldataMem_size I hmem]; omega) (by omega),
      vatDaiCalldataMem_read64 I hmem hread64]

theorem vatDaiWrite_read128_32 (I : ExecutionEnv) {mem : ByteArray} (o : ByteArray)
    (hmem : mem.size = 164) (ho32 : 32 ≤ o.size) :
    (o.write 0 (vatDaiCalldataMem I mem) 128 32).readWithPadding 128 32 =
      o.extract 0 32 :=
  write32_read_back o (vatDaiCalldataMem I mem) 128 ho32
    (by rw [vatDaiCalldataMem_size I hmem]; omega)

end Benchmarks.Dss.Vow
