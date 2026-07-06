import Benchmarks.Dss.Vow.Heal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.Dss.Vow

/-! Shared memory facts for solc-generated `vat.sin(address(this))` calls from initial memory. -/

theorem initialHealSinSelectorMem_size :
    (healSinSelectorMem solcFreePtrMem).size = 160 :=
  by simpa [healSinSelectorMem, solcReturnMem] using solcReturnMem_size healSinSelectorShifted

theorem initialHealSinSelectorMem_read64 :
    (healSinSelectorMem solcFreePtrMem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ :=
  by simpa [healSinSelectorMem, solcReturnMem] using solcReturnMem_read64 healSinSelectorShifted

theorem initialHealSinCalldataMem_size (I : ExecutionEnv) :
    (healSinCalldataMem I solcFreePtrMem).size = 164 := by
  unfold healSinCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
    (by rw [initialHealSinSelectorMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract,
    ByteArray.size_extract, initialHealSinSelectorMem_size, toByteArray_size]
  omega

theorem initialHealSinCalldataMem_read64 (I : ExecutionEnv) :
    (healSinCalldataMem I solcFreePtrMem).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold healSinCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
    (by rw [initialHealSinSelectorMem_size]; omega) (by omega),
    initialHealSinSelectorMem_read64]

theorem initialHealSinSelectorMem_selector :
    (healSinSelectorMem solcFreePtrMem).extract 128 132 = vatSinSelector := by
  rw [show healSinSelectorMem solcFreePtrMem = solcReturnMem healSinSelectorShifted from rfl,
    solcReturnMem_eq,
    extract_append_right_window _ _ _ _ (by rw [solcFreePtrMem_pad_size]),
    solcFreePtrMem_pad_size, show (128 : ℕ) - 128 = 0 from rfl,
    show (132 : ℕ) - 128 = 4 from rfl, toByteArray_eq_toBytesBE]
  native_decide

theorem initialHealSinCalldataMem_read128_36 (I : ExecutionEnv) :
    (healSinCalldataMem I solcFreePtrMem).readWithPadding 128 36 =
      vatSinSelector ++ (UInt256.ofNat I.codeOwner.val).toByteArray := by
  rw [readWithPadding_eq_extract' _ 128 36 (by norm_num) (by norm_num)
      (by rw [initialHealSinCalldataMem_size]), healSinCalldataMem,
    write32_eq _ (healSinSelectorMem solcFreePtrMem) 132 (by rw [toByteArray_size])
      (by rw [initialHealSinSelectorMem_size]; omega)]
  have hAsz : ((healSinSelectorMem solcFreePtrMem).extract 0 132).size = 132 := by
    rw [ByteArray.size_extract, initialHealSinSelectorMem_size]
    omega
  have hBsz : (((UInt256.ofNat I.codeOwner.val).toByteArray).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract, toByteArray_size]
    omega
  have hPsz :
      ((healSinSelectorMem solcFreePtrMem).extract 0 132 ++
        ((UInt256.ofNat I.codeOwner.val).toByteArray).extract 0 32).size = 164 := by
    rw [ByteArray.size_append, hAsz, hBsz]
  have hBfull :
      ((UInt256.ofNat I.codeOwner.val).toByteArray).extract 0 32 =
        (UInt256.ofNat I.codeOwner.val).toByteArray := by
    have h := @ByteArray.extract_zero_size (UInt256.ofNat I.codeOwner.val).toByteArray
    rwa [toByteArray_size] at h
  rw [extract_append_left _ _ _ _ (by rw [hPsz]),
    extract_append_span _ _ 128 164 (by rw [hAsz]; omega) (by rw [hAsz]; omega),
    hAsz, extract_prefix _ 132 128 132 (by omega), initialHealSinSelectorMem_selector,
    extract_extract_BA, show (0 : ℕ) + 0 = 0 from rfl,
    show min (0 + (164 - 132)) 32 = 32 from by omega, hBfull]

theorem initialHealSinEncode_eq (I : ExecutionEnv) :
    config.externalABI.encode? "sin" [.address I.codeOwner] =
      some ((healSinCalldataMem I solcFreePtrMem).readWithPadding
        healSinOutPtr.toNat healSinInSize.toNat) := by
  rw [healSinInSize_eq]
  change config.externalABI.encode? "sin" [.address I.codeOwner] =
    some ((healSinCalldataMem I solcFreePtrMem).readWithPadding 128 36)
  rw [initialHealSinCalldataMem_read128_36]
  simp [config, vowExternalABI, ABI.encodeCallWithSelector?, ABI.encodeABIValues?,
    ABI.encodeABIValuesFrom?, ABI.encodeABIValue?, ABI.encodeABIWord?,
    ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType, addr,
    vatSinSelector, selectorBytes]
  rw [show EVM.word (↑I.codeOwner : ℕ) = UInt256.ofNat (↑I.codeOwner : ℕ) from rfl]
  rw [word_toBytesBE_toByteArray_eq_toByteArray]

theorem initialHealSinWrite_size (I : ExecutionEnv) (o : ByteArray) (L : ℕ)
    (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (healSinCalldataMem I solcFreePtrMem) 128 L).size = 164 := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact initialHealSinCalldataMem_size I
  · rw [write_eq_gen o (healSinCalldataMem I solcFreePtrMem) 128 L (by omega) hLo
      (by rw [initialHealSinCalldataMem_size I]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, initialHealSinCalldataMem_size]
    omega

theorem initialHealSinWrite_read64 (I : ExecutionEnv) (o : ByteArray) (L : ℕ)
    (hL : L ≤ 32) (hLo : L ≤ o.size) :
    (o.write 0 (healSinCalldataMem I solcFreePtrMem) 128 L).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h
    rw [byteArray_write_len_zero]
    exact initialHealSinCalldataMem_read64 I
  · rw [write_read_below_gen o (healSinCalldataMem I solcFreePtrMem) 128 L 64
      (by omega) hLo (by rw [initialHealSinCalldataMem_size I]; omega) (by omega),
      initialHealSinCalldataMem_read64]

theorem initialHealSinWrite_read128_32 (I : ExecutionEnv) (o : ByteArray)
    (ho32 : 32 ≤ o.size) :
    (o.write 0 (healSinCalldataMem I solcFreePtrMem) 128 32).readWithPadding 128 32 =
      o.extract 0 32 :=
  write32_read_back o (healSinCalldataMem I solcFreePtrMem) 128 ho32
    (by rw [initialHealSinCalldataMem_size I]; omega)

end Benchmarks.Dss.Vow
