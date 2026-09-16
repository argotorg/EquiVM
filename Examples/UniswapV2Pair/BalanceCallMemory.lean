import Examples.UniswapV2Pair.ExternalCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

theorem balanceOfThisSelectorMem_read96_zero :
    balanceOfThisSelectorMem.readWithPadding 96 32 = UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold balanceOfThisSelectorMem solcFreePtrMem
  native_decide

theorem balanceOfThisCalldataMem_read96_zero (self : UInt256) :
    (balanceOfThisCalldataMem self).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold balanceOfThisCalldataMem
  rw [write32_read_below _ _ 132 96 (by rw [toByteArray_size])
      (by rw [balanceOfThisSelectorMem_size]; omega) (by omega)]
  exact balanceOfThisSelectorMem_read96_zero

theorem balanceOfThisStaticcallMem_read96_zero_of_size_ge
    (self : UInt256) {o : ByteArray}
    (ho32 : 32 ≤ o.size) (hoSize : o.size < UInt256.size) :
    (balanceOfThisStaticcallMem self o).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold balanceOfThisStaticcallMem
  have hlen : (min (⟨32⟩ : UInt256) (UInt256.ofNat o.size)).toNat = 32 := by
    simpa using
      umin_ofNat_right_toNat_of_ge (c := 32) (n := o.size) (by decide) ho32 hoSize
  rw [hlen]
  rw [write_read_below_gen o (balanceOfThisCalldataMem self) 128 32 96
      (by decide) ho32 (by rw [balanceOfThisCalldataMem_size]; omega) (by omega)]
  exact balanceOfThisCalldataMem_read96_zero self

theorem balanceOfThisRebuiltStaticcallMem_read96_zero
    (self : UInt256) (out0 out1 : ByteArray)
    (ho0 : 32 ≤ out0.size) (hs0 : out0.size < UInt256.size)
    (ho1 : 32 ≤ out1.size) (hs1 : out1.size < UInt256.size) :
    (balanceOfThisRebuiltStaticcallMem self out0 out1).readWithPadding 96 32 =
      UInt256.toByteArray (⟨0⟩ : UInt256) := by
  unfold balanceOfThisRebuiltStaticcallMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge out1 ho1 hs1,
    write32_read_below _ _ 128 96 ho1
      (by rw [balanceOfThisRebuiltCalldataMem_size_of_size_ge self out0 ho0 hs0]; omega) (by omega)]
  unfold balanceOfThisRebuiltCalldataMem
  rw [write32_read_below _ _ 132 96 (by rw [toByteArray_size])
    (by rw [balanceOfThisRebuiltSelectorMem_size_of_size_ge self out0 ho0 hs0]; omega) (by omega)]
  unfold balanceOfThisRebuiltSelectorMem
  rw [write32_read_below _ _ 128 96 (by rw [toByteArray_size])
    (by rw [balanceOfThisStaticcallMem_size_of_size_ge self out0 ho0 hs0]; omega) (by omega)]
  exact balanceOfThisStaticcallMem_read96_zero_of_size_ge self ho0 hs0

end UniswapV2Pair
