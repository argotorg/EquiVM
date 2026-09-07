import Reasoning.MemCascade
import Examples.UniswapV2Pair.MemorySteps
import Examples.UniswapV2Pair.ExternalCalls
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

noncomputable def balanceDynamicSelectorMem (base : ByteArray) (ptr : UInt256) : ByteArray :=
  balanceOfSelectorShifted.toByteArray.write 0 base ptr.toNat 32
noncomputable def balanceDynamicCalldataMem (base : ByteArray) (ptr self : UInt256) : ByteArray :=
  self.toByteArray.write 0 (balanceDynamicSelectorMem base ptr) (ptr + ⟨4⟩).toNat 32
abbrev balanceDynamicSelectorWords (aw ptr : UInt256) : UInt256 := memoryWordActiveWords aw ptr
abbrev balanceDynamicCalldataWords (aw ptr : UInt256) : UInt256 :=
  memoryWordActiveWords (balanceDynamicSelectorWords aw ptr) (ptr + ⟨4⟩)
noncomputable def balanceDynamicReturnMem (base : ByteArray) (ptr self : UInt256) (out : ByteArray) : ByteArray :=
  out.write 0 (balanceDynamicCalldataMem base ptr self) ptr.toNat
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat

theorem balanceDynamicSelectorMem_size {base : ByteArray} (ptr : UInt256)
    (hgap : ptr.toNat - base.size < USize.size) :
    (balanceDynamicSelectorMem base ptr).size = max base.size (ptr.toNat + 32) := by
  exact writeWord_size base ptr.toNat balanceOfSelectorShifted hgap

theorem balanceDynamicCalldataMem_size {base : ByteArray} (ptr self : UInt256)
    (hgap : ptr.toNat - base.size < USize.size) (hfit : ptr.toNat + 4 < UInt256.size) :
    (balanceDynamicCalldataMem base ptr self).size = max base.size (ptr.toNat + 36) := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 hfit
  have hs := balanceDynamicSelectorMem_size ptr hgap
  have h := toByteArray_write32_size_of_le (balanceDynamicSelectorMem base ptr) self (ptr + ⟨4⟩).toNat
    (max base.size (ptr.toNat + 32)) (max base.size (ptr.toNat + 36)) hs (by rw [h4, hs]; omega) (by rw [h4]; omega)
  exact h

theorem balanceDynamicSelectorMem_read_below {base : ByteArray} (ptr : UInt256) (read : Nat)
    (hin : read + 32 ≤ base.size) (hlo : read + 32 ≤ ptr.toNat) (hgap : ptr.toNat - base.size < USize.size) :
    (balanceDynamicSelectorMem base ptr).readWithPadding read 32 = base.readWithPadding read 32 := by
  exact toByteArray_write_read_below_of_gap balanceOfSelectorShifted base ptr.toNat read hin hlo hgap

theorem balanceDynamicCalldataMem_read_below {base : ByteArray} (ptr self : UInt256) (read : Nat)
    (hin : read + 32 ≤ base.size) (hlo : read + 32 ≤ ptr.toNat)
    (hgap : ptr.toNat - base.size < USize.size) (hfit : ptr.toNat + 4 < UInt256.size) :
    (balanceDynamicCalldataMem base ptr self).readWithPadding read 32 = base.readWithPadding read 32 := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 hfit
  have hs := balanceDynamicSelectorMem_size ptr hgap
  unfold balanceDynamicCalldataMem
  rw [write32_read_below _ _ (ptr + ⟨4⟩).toNat read (by rw [toByteArray_size])
    (by rw [h4, hs]; omega) (by rw [h4]; omega)]
  exact balanceDynamicSelectorMem_read_below ptr read hin hlo hgap

theorem balanceDynamicCalldataMem_calldata {base : ByteArray} (ptr self : UInt256)
    (hgap : ptr.toNat - base.size < USize.size) (hfit : ptr.toNat + 4 < UInt256.size) :
    (balanceDynamicCalldataMem base ptr self).readWithPadding ptr.toNat 36 =
      (balanceOfThisCalldataMem self).readWithPadding 128 36 := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 hfit
  have hs := balanceDynamicSelectorMem_size ptr hgap
  have h4read : (balanceDynamicCalldataMem base ptr self).readWithPadding ptr.toNat 4 = balanceOfSelector := by
    unfold balanceDynamicCalldataMem
    rw [write32_read_below_len _ _ (ptr + ⟨4⟩).toNat ptr.toNat 4 (by rw [toByteArray_size])
      (by rw [h4, hs]; omega) (by rw [h4]) (by rw [hs]; omega) (by decide) (by decide)]
    have h := toByteArray_write_read_window_of_gap balanceOfSelectorShifted base ptr.toNat 0 4
      (by decide) (by decide) (by decide) hgap
    simp only [Nat.add_zero] at h
    exact h.trans (by native_decide)
  have hword : (balanceDynamicCalldataMem base ptr self).readWithPadding (ptr.toNat + 4) 32 = self.toByteArray := by
    rw [← h4]
    have h := toByteArray_write32_read_back (balanceDynamicSelectorMem base ptr) self (ptr + ⟨4⟩).toNat
      (by rw [h4, hs]; omega)
    exact h
  rw [balanceOfThisCalldataMem_read128_36]
  rw [byteArray_readWithPadding_split _ ptr.toNat 4 32 (by decide) (by decide) (by decide) (by decide)
    (by decide) (by rw [balanceDynamicCalldataMem_size ptr self hgap hfit]; omega), h4read, hword]

theorem balanceDynamicWords_bounds (aw ptr : UInt256)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + 67 < UInt256.size) :
    ((balanceDynamicSelectorWords aw ptr).toNat * 32 < UInt256.size ∧
      ptr.toNat + 32 ≤ (balanceDynamicSelectorWords aw ptr).toNat * 32) ∧
    ((balanceDynamicCalldataWords aw ptr).toNat * 32 < UInt256.size ∧
      ptr.toNat + 36 ≤ (balanceDynamicCalldataWords aw ptr).toNat * 32) := by
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 := uadd_word_ofNat_toNat ptr 4 (by omega)
  have hb0 := UInt256_ofNat_M_mul32_lt aw ptr haw (by omega)
  have hc0 := UInt256_ofNat_M_covers aw ptr haw (by omega)
  have hb1 := UInt256_ofNat_M_mul32_lt (balanceDynamicSelectorWords aw ptr) (ptr + ⟨4⟩) hb0 (by rw [h4]; omega)
  have hc1 := UInt256_ofNat_M_covers (balanceDynamicSelectorWords aw ptr) (ptr + ⟨4⟩) hb0 (by rw [h4]; omega)
  refine ⟨⟨hb0, hc0⟩, ⟨hb1, ?_⟩⟩
  change (ptr + ⟨4⟩).toNat + 32 ≤ (balanceDynamicCalldataWords aw ptr).toNat * 32 at hc1
  rw [h4] at hc1
  omega

theorem balanceDynamicCalldataMem_mload64 {base : ByteArray} (aw ptr self : UInt256)
    (hin : 96 ≤ base.size) (hlo : 96 ≤ ptr.toNat)
    (hgap : ptr.toNat - base.size < USize.size) (hfit : ptr.toNat + 67 < UInt256.size)
    (haw : aw.toNat * 32 < UInt256.size) (hread : base.readWithPadding 64 32 = ptr.toByteArray) :
    memoryWordLoad (balanceDynamicCalldataMem base ptr self) (balanceDynamicCalldataWords aw ptr) ⟨64⟩ = ptr ∧
    memoryWordActiveWords (balanceDynamicCalldataWords aw ptr) ⟨64⟩ = balanceDynamicCalldataWords aw ptr := by
  obtain ⟨_, hb, hc⟩ := balanceDynamicWords_bounds aw ptr haw hfit
  have hc64 : (⟨64⟩ : UInt256).toNat + 32 ≤ (balanceDynamicCalldataWords aw ptr).toNat * 32 := by change 64 + 32 ≤ _; omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hc64⟩
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [balanceDynamicCalldataMem_size ptr self hgap (by omega)]; omega
  · exact UInt256_mload_haw_of_cover _ _ hb hc64
  · exact (balanceDynamicCalldataMem_read_below ptr self 64 hin hlo hgap (by omega)).trans hread

end UniswapV2Pair
