import Examples.UniswapV2Pair.Dispatch
import Reasoning.Memory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

/-! ## Shared external-call calldata buffers -/

abbrev balanceOfSelectorWord : UInt256 := ⟨1889567281⟩

abbrev balanceOfSelectorShifted : UInt256 :=
  UInt256.shiftLeft balanceOfSelectorWord ⟨224⟩

abbrev transferSelectorWord : UInt256 := ⟨2835717307⟩

abbrev transferSelectorShifted : UInt256 :=
  UInt256.shiftLeft transferSelectorWord ⟨224⟩

noncomputable def balanceOfThisSelectorMem : ByteArray :=
  (UInt256.toByteArray balanceOfSelectorShifted).write 0 solcFreePtrMem 128 32

noncomputable def transferSelectorMem : ByteArray :=
  (UInt256.toByteArray transferSelectorShifted).write 0 solcFreePtrMem 128 32

noncomputable def balanceOfThisCalldataMem (self : UInt256) : ByteArray :=
  (UInt256.toByteArray self).write 0 balanceOfThisSelectorMem 132 32

noncomputable def transferArgsMem (recipient : UInt256) : ByteArray :=
  (UInt256.toByteArray recipient).write 0 transferSelectorMem 132 32

noncomputable def transferCalldataMem (recipient value : UInt256) : ByteArray :=
  (UInt256.toByteArray value).write 0 (transferArgsMem recipient) 164 32

noncomputable def balanceOfThisStaticcallMem (self : UInt256) (o : ByteArray) : ByteArray :=
  o.write 0 (balanceOfThisCalldataMem self) 128 (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

noncomputable def balanceOfThisRebuiltSelectorMem (self : UInt256) (o : ByteArray) : ByteArray :=
  (UInt256.toByteArray balanceOfSelectorShifted).write 0
    (balanceOfThisStaticcallMem self o) 128 32

noncomputable def balanceOfThisRebuiltCalldataMem (self : UInt256) (o : ByteArray) : ByteArray :=
  (UInt256.toByteArray self).write 0 (balanceOfThisRebuiltSelectorMem self o) 132 32

noncomputable def balanceOfThisRebuiltStaticcallMem
    (self : UInt256) (oPrev o : ByteArray) : ByteArray :=
  o.write 0 (balanceOfThisRebuiltCalldataMem self oPrev) 128
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat

abbrev balanceOfThisStaticcallActiveWords : UInt256 :=
  UInt256.ofNat (MachineState.M (MachineState.M (UInt256.ofNat 6).toNat 128 36) 128 32)

theorem balanceOfThisSelectorMem_size : balanceOfThisSelectorMem.size = 160 :=
  solcReturnMem_size balanceOfSelectorShifted

theorem balanceOfThisSelectorMem_read64 :
    balanceOfThisSelectorMem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ :=
  solcReturnMem_read64 balanceOfSelectorShifted

theorem transferSelectorMem_size : transferSelectorMem.size = 160 :=
  solcReturnMem_size transferSelectorShifted

theorem transferArgsMem_size (recipient : UInt256) :
    (transferArgsMem recipient).size = 164 := by
  unfold transferArgsMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferSelectorMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferSelectorMem_size,
    toByteArray_size]
  omega

theorem transferCalldataMem_size (recipient value : UInt256) :
    (transferCalldataMem recipient value).size = 196 := by
  unfold transferCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [transferArgsMem_size])]
  rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, transferArgsMem_size, toByteArray_size]
  omega

theorem transferCalldataMem_read128_4 (recipient value : UInt256) :
    (transferCalldataMem recipient value).readWithPadding 128 4 =
      transferSelector := by
  unfold transferCalldataMem
  rw [write32_read_below_len _ _ 164 128 4 (by rw [toByteArray_size])
      (by rw [transferArgsMem_size])
      (by omega)
      (by rw [transferArgsMem_size]; omega)
      (by norm_num) (by norm_num)]
  unfold transferArgsMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by rw [transferSelectorMem_size]; omega) (by omega)
      (by rw [transferSelectorMem_size]; omega)
      (by norm_num) (by norm_num)]
  have hzero32 : (ffi.ByteArray.zeroes (USize.ofNat 32)).size = 32 := by
    rw [ByteArray_zeroes_size]
    exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))
  rw [show transferSelectorMem = solcReturnMem transferSelectorShifted from rfl]
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
      (by rw [solcReturnMem_size]; omega)]
  rw [solcReturnMem_eq]
  rw [extract_append_right_window
      (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32))
      (UInt256.toByteArray transferSelectorShifted) 128 132 (by
        simp [ByteArray.size_append, solcFreePtrMem_size, hzero32])]
  rw [ByteArray.size_append, solcFreePtrMem_size, hzero32]
  native_decide

theorem transferCalldataMem_read132_32 (recipient value : UInt256) :
    (transferCalldataMem recipient value).readWithPadding 132 32 =
      UInt256.toByteArray recipient := by
  unfold transferCalldataMem
  rw [write32_read_below _ _ 164 132 (by rw [toByteArray_size])
      (by rw [transferArgsMem_size])
      (by omega)]
  unfold transferArgsMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [transferSelectorMem_size]; omega)]
  rw [show (UInt256.toByteArray recipient).extract 0 32 = UInt256.toByteArray recipient by
    rw [show 32 = (UInt256.toByteArray recipient).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem transferCalldataMem_read164_32 (recipient value : UInt256) :
    (transferCalldataMem recipient value).readWithPadding 164 32 =
      UInt256.toByteArray value := by
  unfold transferCalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [transferArgsMem_size])]
  rw [show (UInt256.toByteArray value).extract 0 32 = UInt256.toByteArray value by
    rw [show 32 = (UInt256.toByteArray value).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem balanceOfThisCalldataMem_size (self : UInt256) :
    (balanceOfThisCalldataMem self).size = 164 := by
  unfold balanceOfThisCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [balanceOfThisSelectorMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, balanceOfThisSelectorMem_size,
    toByteArray_size]
  omega

theorem balanceOfThisCalldataMem_read64 (self : UInt256) :
    (balanceOfThisCalldataMem self).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfThisCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [balanceOfThisSelectorMem_size]; omega) (by omega),
    balanceOfThisSelectorMem_read64]

theorem balanceOfThisCalldataMem_mload64 (self : UInt256) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfThisCalldataMem self).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 6 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisCalldataMem self).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue (by rw [balanceOfThisCalldataMem_size]; decide) (by decide)
    (balanceOfThisCalldataMem_read64 self)

theorem transferCalldataMem_read128_68 (recipient value : UInt256) :
    (transferCalldataMem recipient value).readWithPadding 128 68 =
      transferSelector ++ UInt256.toByteArray recipient ++ UInt256.toByteArray value := by
  rw [byteArray_readWithPadding_split _ 128 4 64 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by simp [transferCalldataMem_size])]
  rw [byteArray_readWithPadding_split _ 132 32 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by simp [transferCalldataMem_size])]
  rw [transferCalldataMem_read128_4, transferCalldataMem_read132_32,
    transferCalldataMem_read164_32, ByteArray.append_assoc]

theorem transferCalldataMem_encode (recipient : AccountAddress) (value : UInt256) :
    config.externalABI.encode? "transfer"
        [.address recipient, .int (Int.ofNat value.toNat)] =
      some ((transferCalldataMem (UInt256.ofNat recipient.val) value).readWithPadding 128 68) := by
  rw [transferCalldataMem_read128_68]
  change uniswapExternalABI.encode? "transfer"
      [.address recipient, .int (Int.ofNat value.toNat)] =
    some (transferSelector ++
      (UInt256.ofNat recipient.val).toByteArray ++ UInt256.toByteArray value)
  have hvalueWord : EVM.word value.toNat = value := by
    exact u256_ofNat_toNat value
  have hrecipientWord : EVM.word recipient.val = UInt256.ofNat recipient.val := by
    apply u256_inj
    rfl
  have hvalueLt : value.toNat < EVM.twoPow 256 := by
    change value.val.val < UInt256.size
    exact value.val.isLt
  unfold uniswapExternalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [addr, uint256, uint256Int, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
    ABI.isDynamicABIType, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.encodeABIValuesFrom?,
    hvalueLt, hrecipientWord, hvalueWord, word_toBytesBE_toByteArray_eq_toByteArray]
  rw [ByteArray.append_assoc]

theorem balanceOfThisSelectorMem_read128_4 :
    balanceOfThisSelectorMem.readWithPadding 128 4 = balanceOfSelector := by
  have hzero32 : (ffi.ByteArray.zeroes (USize.ofNat 32)).size = 32 := by
    rw [ByteArray_zeroes_size]
    exact USize.toNat_ofNat_of_lt' (lt_usize _ (by norm_num))
  rw [show balanceOfThisSelectorMem = solcReturnMem balanceOfSelectorShifted from rfl]
  rw [readWithPadding_eq_extract' _ 128 4 (by norm_num) (by norm_num)
      (by rw [solcReturnMem_size]; omega)]
  rw [solcReturnMem_eq]
  rw [extract_append_right_window
      (solcFreePtrMem ++ ffi.ByteArray.zeroes (USize.ofNat 32))
      (UInt256.toByteArray balanceOfSelectorShifted) 128 132 (by
        simp [ByteArray.size_append, solcFreePtrMem_size, hzero32])]
  rw [ByteArray.size_append, solcFreePtrMem_size, hzero32]
  native_decide

theorem balanceOfThisCalldataMem_read132_32 (self : UInt256) :
    (balanceOfThisCalldataMem self).readWithPadding 132 32 = UInt256.toByteArray self := by
  unfold balanceOfThisCalldataMem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by simp [balanceOfThisSelectorMem_size])]
  rw [show (UInt256.toByteArray self).extract 0 32 = UInt256.toByteArray self by
    rw [show 32 = (UInt256.toByteArray self).size by rw [toByteArray_size]]
    exact byteArray_extract_self _]

theorem balanceOfThisCalldataMem_read128_4 (self : UInt256) :
    (balanceOfThisCalldataMem self).readWithPadding 128 4 = balanceOfSelector := by
  unfold balanceOfThisCalldataMem
  rw [write32_read_below_len _ _ 132 128 4 (by rw [toByteArray_size])
      (by simp [balanceOfThisSelectorMem_size]) (by omega)
      (by simp [balanceOfThisSelectorMem_size]) (by norm_num) (by norm_num)]
  exact balanceOfThisSelectorMem_read128_4

theorem balanceOfThisCalldataMem_read128_36 (self : UInt256) :
    (balanceOfThisCalldataMem self).readWithPadding 128 36 =
      balanceOfSelector ++ UInt256.toByteArray self := by
  rw [byteArray_readWithPadding_split _ 128 4 32 (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by simp [balanceOfThisCalldataMem_size])]
  rw [balanceOfThisCalldataMem_read128_4, balanceOfThisCalldataMem_read132_32]

theorem balanceOfThisCalldataMem_encode (self : AccountAddress) :
    config.externalABI.encode? "balanceOf" [.address self] =
      some ((balanceOfThisCalldataMem (UInt256.ofNat self.val)).readWithPadding 128 36) := by
  rw [balanceOfThisCalldataMem_read128_36]
  change uniswapExternalABI.encode? "balanceOf" [.address self] =
    some (balanceOfSelector ++ (UInt256.ofNat self.val).toByteArray)
  unfold uniswapExternalABI ABI.encodeCallWithSelector? ABI.encodeABIValues?
  simp [addr, ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?,
    ABI.isDynamicABIType, ABI.encodeABIValue?, ABI.encodeABIWord?, ABI.encodeABIValuesFrom?]
  rw [word_toBytesBE_toByteArray_eq_toByteArray]
  rfl

-- LIBRARY CANDIDATE: Reasoning.EVMWord — `min (literal word) (UInt256.ofNat n)` collapses
-- to the literal when `n` is large enough and in range.
theorem balanceOfThisStaticcallWriteLen_of_size_ge (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 := by
  simpa using
    umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) hlo hhi

theorem balanceOfThisStaticcallMem_size_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisStaticcallMem self o).size = 164 := by
  unfold balanceOfThisStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge o hlo hhi]
  rw [write32_eq _ _ _ hlo (by rw [balanceOfThisCalldataMem_size]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, balanceOfThisCalldataMem_size]
  omega

-- LIBRARY CANDIDATE: Reasoning.Memory — free-pointer read below an external-call returndata
-- write into the ABI output region.
theorem balanceOfThisStaticcallMem_read64_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisStaticcallMem self o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfThisStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge o hlo hhi]
  rw [write32_read_below _ _ 128 64 hlo
    (by rw [balanceOfThisCalldataMem_size]; omega) (by omega)]
  exact balanceOfThisCalldataMem_read64 self

theorem balanceOfThisStaticcallMem_mload64_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfThisStaticcallMem self o).size
        ∨ (⟨64⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisStaticcallMem self o).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [balanceOfThisStaticcallMem_size_of_size_ge self o hlo hhi]; decide)
    (by decide)
    (balanceOfThisStaticcallMem_read64_of_size_ge self o hlo hhi)

theorem balanceOfThisStaticcallWriteLen_of_size_lt (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = o.size := by
  simpa using
    umin_ofNat_right_toNat_of_lt (c := 32) (n := o.size) (by decide) hshort hhi

theorem balanceOfThisStaticcallMem_size_of_size_lt (self : UInt256) (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (balanceOfThisStaticcallMem self o).size = 164 := by
  unfold balanceOfThisStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_lt o hshort hhi]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero, balanceOfThisCalldataMem_size]
  · rw [write_eq_gen _ _ 128 o.size hzero le_rfl
      (by rw [balanceOfThisCalldataMem_size]; omega),
      ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
      ByteArray.size_extract, ByteArray.size_extract, balanceOfThisCalldataMem_size]
    omega

theorem balanceOfThisStaticcallMem_read64_of_size_lt (self : UInt256) (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (balanceOfThisStaticcallMem self o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfThisStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_lt o hshort hhi]
  by_cases hzero : o.size = 0
  · rw [hzero, byteArray_write_len_zero]
    exact balanceOfThisCalldataMem_read64 self
  · rw [write_read_below_gen _ _ 128 o.size 64 hzero le_rfl
      (by rw [balanceOfThisCalldataMem_size]; omega) (by omega)]
    exact balanceOfThisCalldataMem_read64 self

theorem balanceOfThisStaticcallMem_mload64_of_size_lt (self : UInt256) (o : ByteArray)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfThisStaticcallMem self o).size
        ∨ (⟨64⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisStaticcallMem self o).readWithPadding (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [balanceOfThisStaticcallMem_size_of_size_lt self o hshort hhi]; decide)
    (by decide)
    (balanceOfThisStaticcallMem_read64_of_size_lt self o hshort hhi)

-- LIBRARY CANDIDATE: Reasoning.Memory — read back the first ABI return word copied by a
-- CALL-like opcode into the output region.
theorem balanceOfThisStaticcallMem_read128_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisStaticcallMem self o).readWithPadding 128 32 = o.extract 0 32 := by
  unfold balanceOfThisStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge o hlo hhi]
  exact write32_read_back _ _ 128 hlo (by rw [balanceOfThisCalldataMem_size]; omega)

theorem balanceOfThisStaticcallMem_mload128_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (balanceOfThisStaticcallMem self o).size
        ∨ (⟨128⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisStaticcallMem self o).readWithPadding (⟨128⟩ : UInt256).toNat 32)))
      = UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) := by
  rw [if_neg]
  · rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      balanceOfThisStaticcallMem_read128_of_size_ge self o hlo hhi]
  · rw [not_or]
    constructor
    · rw [balanceOfThisStaticcallMem_size_of_size_ge self o hlo hhi]
      decide
    · decide

theorem balanceOfThisRebuiltSelectorMem_size_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltSelectorMem self o).size = 164 := by
  unfold balanceOfThisRebuiltSelectorMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [balanceOfThisStaticcallMem_size_of_size_ge self o hlo hhi]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    balanceOfThisStaticcallMem_size_of_size_ge self o hlo hhi, toByteArray_size]
  omega

theorem balanceOfThisRebuiltSelectorMem_read64_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltSelectorMem self o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfThisRebuiltSelectorMem
  rw [write32_read_below _ _ 128 64 (by rw [toByteArray_size])
      (by rw [balanceOfThisStaticcallMem_size_of_size_ge self o hlo hhi]; omega) (by omega),
    balanceOfThisStaticcallMem_read64_of_size_ge self o hlo hhi]

theorem balanceOfThisRebuiltCalldataMem_size_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltCalldataMem self o).size = 164 := by
  unfold balanceOfThisRebuiltCalldataMem
  rw [write32_eq _ _ _ (by rw [toByteArray_size])
      (by rw [balanceOfThisRebuiltSelectorMem_size_of_size_ge self o hlo hhi]; omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    balanceOfThisRebuiltSelectorMem_size_of_size_ge self o hlo hhi, toByteArray_size]
  omega

-- LIBRARY CANDIDATE: Reasoning.Memory — free-pointer read survives repeated
-- calldata-buffer rewrites above the free-pointer word.
theorem balanceOfThisRebuiltCalldataMem_read64_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltCalldataMem self o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfThisRebuiltCalldataMem
  rw [write32_read_below _ _ 132 64 (by rw [toByteArray_size])
      (by rw [balanceOfThisRebuiltSelectorMem_size_of_size_ge self o hlo hhi]; omega)
      (by omega),
    balanceOfThisRebuiltSelectorMem_read64_of_size_ge self o hlo hhi]

theorem balanceOfThisRebuiltCalldataMem_mload64_of_size_ge (self : UInt256) (o : ByteArray)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfThisRebuiltCalldataMem self o).size
        ∨ (⟨64⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisRebuiltCalldataMem self o).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by rw [balanceOfThisRebuiltCalldataMem_size_of_size_ge self o hlo hhi]; decide)
    (by decide)
    (balanceOfThisRebuiltCalldataMem_read64_of_size_ge self o hlo hhi)

theorem balanceOfThisRebuiltStaticcallMem_size_of_size_ge
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltStaticcallMem self oPrev o).size = 164 := by
  unfold balanceOfThisRebuiltStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge o hlo hhi]
  rw [write32_eq _ _ _ hlo
      (by rw [balanceOfThisRebuiltCalldataMem_size_of_size_ge self oPrev hprevlo hprevhi];
          omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract,
    balanceOfThisRebuiltCalldataMem_size_of_size_ge self oPrev hprevlo hprevhi]
  omega

-- LIBRARY CANDIDATE: Reasoning.Memory — free-pointer read survives a second
-- external-call returndata write into the ABI output region.
theorem balanceOfThisRebuiltStaticcallMem_read64_of_size_ge
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltStaticcallMem self oPrev o).readWithPadding 64 32 =
      UInt256.toByteArray ⟨128⟩ := by
  unfold balanceOfThisRebuiltStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge o hlo hhi]
  rw [write32_read_below _ _ 128 64 hlo
      (by rw [balanceOfThisRebuiltCalldataMem_size_of_size_ge self oPrev hprevlo hprevhi];
          omega) (by omega),
    balanceOfThisRebuiltCalldataMem_read64_of_size_ge self oPrev hprevlo hprevhi]

theorem balanceOfThisRebuiltStaticcallMem_mload64_of_size_ge
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨64⟩ : UInt256).toNat ≥ (balanceOfThisRebuiltStaticcallMem self oPrev o).size
        ∨ (⟨64⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisRebuiltStaticcallMem self oPrev o).readWithPadding
          (⟨64⟩ : UInt256).toNat 32)))
      = ⟨128⟩ :=
  mloadFreePtrValue
    (by
      rw [balanceOfThisRebuiltStaticcallMem_size_of_size_ge self oPrev o hprevlo hprevhi
        hlo hhi]
      decide)
    (by decide)
    (balanceOfThisRebuiltStaticcallMem_read64_of_size_ge self oPrev o hprevlo hprevhi
      hlo hhi)

-- LIBRARY CANDIDATE: Reasoning.Memory — read back the first ABI return word copied by a
-- second CALL-like opcode into a rebuilt output region.
theorem balanceOfThisRebuiltStaticcallMem_read128_of_size_ge
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (balanceOfThisRebuiltStaticcallMem self oPrev o).readWithPadding 128 32 =
      o.extract 0 32 := by
  unfold balanceOfThisRebuiltStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge o hlo hhi]
  exact write32_read_back _ _ 128 hlo
    (by
      rw [balanceOfThisRebuiltCalldataMem_size_of_size_ge self oPrev hprevlo hprevhi]
      omega)

theorem balanceOfThisRebuiltStaticcallMem_mload128_of_size_ge
    (self : UInt256) (oPrev o : ByteArray)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size) :
    (if (⟨128⟩ : UInt256).toNat ≥ (balanceOfThisRebuiltStaticcallMem self oPrev o).size
        ∨ (⟨128⟩ : UInt256) ≥ balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((balanceOfThisRebuiltStaticcallMem self oPrev o).readWithPadding
          (⟨128⟩ : UInt256).toNat 32)))
      = UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) := by
  rw [if_neg]
  · rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
      balanceOfThisRebuiltStaticcallMem_read128_of_size_ge self oPrev o hprevlo hprevhi
        hlo hhi]
  · rw [not_or]
    constructor
    · rw [balanceOfThisRebuiltStaticcallMem_size_of_size_ge self oPrev o hprevlo hprevhi
        hlo hhi]
      decide
    · decide

end UniswapV2Pair

namespace Reasoning.Reach

-- LIBRARY CANDIDATE: Reasoning.Reach — generic solc high-level-call uint256 return decoder
-- after a successful CALL-like opcode, parameterized by the output buffer and dead stack pops.
set_option maxHeartbeats 2000000 in
theorem RD.uniswapUint256ReturnWordDecodeOk {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {d0 d1 d2 retWord : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R) mem
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k C)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥
            UniswapV2Pair.balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hMload128Value :
      (if (⟨128⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨128⟩ : UInt256) ≥
            UniswapV2Pair.balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
        retWord)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPopLen : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hMload128 : decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.MLOAD, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) (retWord :: R)
      mem UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k' C' := by
  have rdPop0 := RD.pop h hPop0 (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 hPop1 (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 hPop2 (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ hPush64 (by omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ UniswapV2Pair.balanceOfThisStaticcallActiveWords
    rdPush64 hMload64
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
      native_decide)
    hMload64Value
    (by native_decide)
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 hReturndatasize
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ hPush32
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 hDup2 (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 hLt (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256) = ⟨0⟩ := by
    apply Reasoning.Theory.ult_zero
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' o.size hhi]
    exact hlo
  have rdIszero := RD.iszero rdLt hIszero (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero okPc hPushOk
    (by simp only [List.length_cons]; omega)
  have hcond : UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256)) ≠ ⟨0⟩ := by
    rw [hlt]
    decide
  have rdJumpi := RD.jumpiT rdPushOk hJumpi hcond hjd
    (by simp only [List.length_cons]; omega)
  have rdJumpdest := RD.jumpdest rdJumpi hJumpdest
    (by simp only [List.length_cons]; omega)
  have rdPopLen := RD.pop rdJumpdest hPopLen (by simp only [List.length_cons]; omega)
  have rdMload128 := RD.mload 0 retWord UniswapV2Pair.balanceOfThisStaticcallActiveWords
    rdPopLen hMload128
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
      native_decide)
    hMload128Value
    (by native_decide)
    (by omega)
  exact ⟨_, _, rdMload128⟩

set_option maxHeartbeats 2000000 in
theorem RD.uniswapUint256ReturnWordDecodeShortReverts {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc : UInt256} {mem o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R) mem
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k C)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size)
    (hMload64Value :
      (if (⟨64⟩ : UInt256).toNat ≥ mem.size
          ∨ (⟨64⟩ : UInt256) ≥
            UniswapV2Pair.balanceOfThisStaticcallActiveWords * ⟨32⟩ then ⟨0⟩
       else UInt256.ofNat
         (fromByteArrayBigEndian (mem.readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hPush0 :
      decode code
          (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
            ⟨1⟩) =
        some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero :
      decode code
          ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
                UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
              ⟨1⟩) + UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hRevert :
      decode code
          (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
                  UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
                ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩) =
        some (.REVERT, .none))
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  have rdPop0 := RD.pop h hPop0 (by simp only [List.length_cons]; omega)
  have rdPop1 := RD.pop rdPop0 hPop1 (by simp only [List.length_cons]; omega)
  have rdPop2 := RD.pop rdPop1 hPop2 (by omega)
  have rdPush64 := RD.push1 rdPop2 ⟨64⟩ hPush64 (by omega)
  have rdMload64 := RD.mload 0 ⟨128⟩ UniswapV2Pair.balanceOfThisStaticcallActiveWords
    rdPush64 hMload64
    (fun s haw hstk => by
      simp [memoryExpansionCost, memoryExpansionCost.μᵢ', Cₘ, haw, hstk]
      native_decide)
    hMload64Value
    (by native_decide)
    (by omega)
  have rdReturndatasize := RD.returndatasize rdMload64 hReturndatasize
    (by simp only [List.length_cons]; omega)
  have rdPush32 := RD.push1 rdReturndatasize ⟨32⟩ hPush32
    (by simp only [List.length_cons]; omega)
  have rdDup2 := RD.dup2 rdPush32 hDup2 (by simp only [List.length_cons]; omega)
  have rdLt := RD.lt rdDup2 hLt (by simp only [List.length_cons]; omega)
  have hlt : UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256) = ⟨1⟩ := by
    apply Reasoning.Theory.ult_one
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide, ulit_toNat' o.size hhi]
    exact hshort
  have rdIszero := RD.iszero rdLt hIszero (by simp only [List.length_cons]; omega)
  have rdPushOk := RD.push2 rdIszero okPc hPushOk
    (by simp only [List.length_cons]; omega)
  have hcond :
      UInt256.isZero (UInt256.lt (UInt256.ofNat o.size) (⟨32⟩ : UInt256)) = ⟨0⟩ := by
    rw [hlt]
    decide
  have rdFallthrough := RD.jumpiNT rdPushOk hJumpi hcond
    (by simp only [List.length_cons]; omega)
  exact RD.uniswapPush1Dup1Revert0 rdFallthrough hPush0 hDupZero hRevert
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBalanceOfReturnWordDecodeOk {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc self : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R)
      (UniswapV2Pair.balanceOfThisStaticcallMem self o)
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k C)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPopLen : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hMload128 : decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.MLOAD, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) :: R)
      (UniswapV2Pair.balanceOfThisStaticcallMem self o)
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k' C' := by
  exact RD.uniswapUint256ReturnWordDecodeOk h hlo hhi
    (UniswapV2Pair.balanceOfThisStaticcallMem_mload64_of_size_ge self o hlo hhi)
    (UniswapV2Pair.balanceOfThisStaticcallMem_mload128_of_size_ge self o hlo hhi)
    hPop0 hPop1 hPop2 hPush64 hMload64 hReturndatasize hPush32 hDup2 hLt hIszero
    hPushOk hJumpi hjd hJumpdest hPopLen hMload128 hov

set_option maxHeartbeats 1000000 in
theorem RD.uniswapBalanceOfReturnWordDecodeShortReverts {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc self : UInt256} {o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R)
      (UniswapV2Pair.balanceOfThisStaticcallMem self o)
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k C)
    (hshort : o.size < 32) (hhi : o.size < UInt256.size)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hPush0 :
      decode code
          (((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
            ⟨1⟩) =
        some (.Push .PUSH1, some (⟨0⟩, 1)))
    (hDupZero :
      decode code
          ((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
                UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
              ⟨1⟩) + UInt256.ofNat 2) =
        some (.DUP1, .none))
    (hRevert :
      decode code
          (((((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
                  UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) +
                ⟨1⟩) + UInt256.ofNat 2) + ⟨1⟩) =
        some (.REVERT, .none))
    (hov : R.length + 4 ≤ 1024) :
    RDrev code g s0 := by
  exact RD.uniswapUint256ReturnWordDecodeShortReverts h hshort hhi
    (UniswapV2Pair.balanceOfThisStaticcallMem_mload64_of_size_lt self o hshort hhi)
    hPop0 hPop1 hPop2 hPush64 hMload64 hReturndatasize hPush32 hDup2 hLt hIszero
    hPushOk hJumpi hPush0 hDupZero hRevert hov

theorem RD.uniswapRebuiltBalanceOfReturnWordDecodeOk {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc okPc self : UInt256} {oPrev o : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {d0 d1 d2 : UInt256} {R : List UInt256}
    (h : RD code ee g s0 pc (d0 :: d1 :: d2 :: R)
      (UniswapV2Pair.balanceOfThisRebuiltStaticcallMem self oPrev o)
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k C)
    (hprevlo : 32 ≤ oPrev.size) (hprevhi : oPrev.size < UInt256.size)
    (hlo : 32 ≤ o.size) (hhi : o.size < UInt256.size)
    (hPop0 : decode code pc = some (.POP, .none))
    (hPop1 : decode code (pc + ⟨1⟩) = some (.POP, .none))
    (hPop2 : decode code (pc + ⟨1⟩ + ⟨1⟩) = some (.POP, .none))
    (hPush64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨64⟩, 1)))
    (hMload64 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2) =
        some (.MLOAD, .none))
    (hReturndatasize :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩) =
        some (.RETURNDATASIZE, .none))
    (hPush32 :
      decode code (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH1, some (⟨32⟩, 1)))
    (hDup2 :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2) =
        some (.DUP2, .none))
    (hLt :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩) =
        some (.LT, .none))
    (hIszero :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩) =
        some (.ISZERO, .none))
    (hPushOk :
      decode code
          (pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
            UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) =
        some (.Push .PUSH2, some (okPc, 2)))
    (hJumpi :
      decode code
          ((pc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩ + UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ +
              UInt256.ofNat 2 + ⟨1⟩ + ⟨1⟩ + ⟨1⟩) + UInt256.ofNat 3) =
        some (.JUMPI, .none))
    (hjd : (D_J code 0).contains okPc = true)
    (hJumpdest : decode code okPc = some (.JUMPDEST, .none))
    (hPopLen : decode code (okPc + ⟨1⟩) = some (.POP, .none))
    (hMload128 : decode code (okPc + ⟨1⟩ + ⟨1⟩) = some (.MLOAD, .none))
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD code ee g s0 (okPc + ⟨1⟩ + ⟨1⟩ + ⟨1⟩)
      (UInt256.ofNat (fromByteArrayBigEndian (o.extract 0 32)) :: R)
      (UniswapV2Pair.balanceOfThisRebuiltStaticcallMem self oPrev o)
      UniswapV2Pair.balanceOfThisStaticcallActiveWords o acc k' C' := by
  exact RD.uniswapUint256ReturnWordDecodeOk h hlo hhi
    (UniswapV2Pair.balanceOfThisRebuiltStaticcallMem_mload64_of_size_ge self oPrev o
      hprevlo hprevhi hlo hhi)
    (UniswapV2Pair.balanceOfThisRebuiltStaticcallMem_mload128_of_size_ge self oPrev o
      hprevlo hprevhi hlo hhi)
    hPop0 hPop1 hPop2 hPush64 hMload64 hReturndatasize hPush32 hDup2 hLt hIszero
    hPushOk hJumpi hjd hJumpdest hPopLen hMload128 hov

end Reasoning.Reach
