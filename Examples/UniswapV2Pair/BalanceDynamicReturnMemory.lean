import Examples.UniswapV2Pair.BalanceDynamicMemory
import Examples.UniswapV2Pair.ByteArrayWriteMemory
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

theorem balanceDynamicReturnWriteLen (out : ByteArray) (hout : out.size < UInt256.size) :
    (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 32 out.size := by
  by_cases hlo : 32 ≤ out.size
  · rw [balanceOfThisStaticcallWriteLen_of_size_ge out hlo hout, Nat.min_eq_left hlo]
  · rw [balanceOfThisStaticcallWriteLen_of_size_lt out (by omega) hout, Nat.min_eq_right (by omega)]

theorem balanceDynamicReturnMem_size {base : ByteArray} (ptr self : UInt256) (out : ByteArray)
    (hgap : ptr.toNat - base.size < USize.size) (hfit : ptr.toNat + 4 < UInt256.size)
    (hout : out.size < UInt256.size) :
    (balanceDynamicReturnMem base ptr self out).size = max base.size (ptr.toNat + 36) := by
  have hs := balanceDynamicCalldataMem_size ptr self hgap hfit
  unfold balanceDynamicReturnMem
  rw [balanceDynamicReturnWriteLen out hout]
  rw [byteArray_write_size_of_inBounds _ _ ptr.toNat (min 32 out.size) (Nat.min_le_right _ _)
    (by rw [hs]; omega), hs]

theorem balanceDynamicReturnMem_read_below {base : ByteArray} (ptr self : UInt256) (out : ByteArray) (read : Nat)
    (hin : read + 32 ≤ base.size) (hlo : read + 32 ≤ ptr.toNat)
    (hgap : ptr.toNat - base.size < USize.size) (hfit : ptr.toNat + 4 < UInt256.size)
    (hout : out.size < UInt256.size) :
    (balanceDynamicReturnMem base ptr self out).readWithPadding read 32 = base.readWithPadding read 32 := by
  have hs := balanceDynamicCalldataMem_size ptr self hgap hfit
  unfold balanceDynamicReturnMem
  rw [balanceDynamicReturnWriteLen out hout]
  by_cases he : min 32 out.size = 0
  · rw [he, byteArray_write_len_zero]
    exact balanceDynamicCalldataMem_read_below ptr self read hin hlo hgap hfit
  · rw [write_read_below_gen out _ ptr.toNat (min 32 out.size) read he (Nat.min_le_right _ _)
      (by rw [hs]; omega) hlo]
    exact balanceDynamicCalldataMem_read_below ptr self read hin hlo hgap hfit

theorem balanceDynamicReturnMem_read_ptr {base : ByteArray} (ptr self : UInt256) (out : ByteArray)
    (hgap : ptr.toNat - base.size < USize.size) (hfit : ptr.toNat + 4 < UInt256.size)
    (hout : out.size < UInt256.size) (hlo : 32 ≤ out.size) :
    (balanceDynamicReturnMem base ptr self out).readWithPadding ptr.toNat 32 = out.extract 0 32 := by
  unfold balanceDynamicReturnMem
  rw [balanceOfThisStaticcallWriteLen_of_size_ge out hlo hout]
  have h := write32_read_back out (balanceDynamicCalldataMem base ptr self) ptr.toNat hlo
    (by rw [balanceDynamicCalldataMem_size ptr self hgap hfit]; omega)
  exact h

theorem balanceDynamicReturnMem_mload64 {base : ByteArray} (aw ptr self : UInt256) (out : ByteArray)
    (hin : 96 ≤ base.size) (hlo : 96 ≤ ptr.toNat)
    (hgap : ptr.toNat - base.size < USize.size) (hfit : ptr.toNat + 67 < UInt256.size)
    (haw : aw.toNat * 32 < UInt256.size) (hread : base.readWithPadding 64 32 = ptr.toByteArray)
    (hout : out.size < UInt256.size) :
    memoryWordLoad (balanceDynamicReturnMem base ptr self out) (balanceDynamicCalldataWords aw ptr) ⟨64⟩ = ptr ∧
    memoryWordActiveWords (balanceDynamicCalldataWords aw ptr) ⟨64⟩ = balanceDynamicCalldataWords aw ptr := by
  obtain ⟨_, hb, hc⟩ := balanceDynamicWords_bounds aw ptr haw hfit
  have hc64 : (⟨64⟩ : UInt256).toNat + 32 ≤ (balanceDynamicCalldataWords aw ptr).toNat * 32 := by change 64 + 32 ≤ _; omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hc64⟩
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [balanceDynamicReturnMem_size ptr self out hgap (by omega) hout]; omega
  · exact UInt256_mload_haw_of_cover _ _ hb hc64
  · exact (balanceDynamicReturnMem_read_below ptr self out 64 hin hlo hgap (by omega) hout).trans hread

theorem balanceDynamicReturnMem_mload_ptr {base : ByteArray} (aw ptr self : UInt256) (out : ByteArray)
    (hgap : ptr.toNat - base.size < USize.size) (hfit : ptr.toNat + 67 < UInt256.size)
    (haw : aw.toNat * 32 < UInt256.size) (hout : out.size < UInt256.size) (hlo : 32 ≤ out.size) :
    memoryWordLoad (balanceDynamicReturnMem base ptr self out) (balanceDynamicCalldataWords aw ptr) ptr =
      UInt256.ofNat (fromByteArrayBigEndian (out.extract 0 32)) ∧
    memoryWordActiveWords (balanceDynamicCalldataWords aw ptr) ptr = balanceDynamicCalldataWords aw ptr := by
  obtain ⟨_, hb, hc⟩ := balanceDynamicWords_bounds aw ptr haw hfit
  have hcover : ptr.toNat + 32 ≤ (balanceDynamicCalldataWords aw ptr).toNat * 32 := by omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hcover⟩
  have h := mloadValue_eq_readWithPadding_of_lt_size (balanceDynamicReturnMem base ptr self out)
    (balanceDynamicCalldataWords aw ptr) ptr _ (balanceDynamicReturnMem_size ptr self out hgap (by omega) hout)
    (by omega) (UInt256_mload_haw_of_cover _ _ hb hcover)
  exact h.trans (congrArg (fun bytes => UInt256.ofNat (fromByteArrayBigEndian bytes))
    (balanceDynamicReturnMem_read_ptr ptr self out hgap (by omega) hout hlo))

theorem balanceDynamicReturnMem_invariants {base : ByteArray} (aw ptr self : UInt256)
    (out : ByteArray) (hin : 96 ≤ base.size) (hlo : 96 ≤ ptr.toNat)
    (hgap : ptr.toNat - base.size < USize.size) (hfit : ptr.toNat + 67 < UInt256.size)
    (haw : aw.toNat * 32 < UInt256.size) (hread : base.readWithPadding 64 32 = ptr.toByteArray)
    (hout : out.size < UInt256.size) :
    96 ≤ (balanceDynamicReturnMem base ptr self out).size ∧
    ptr.toNat - (balanceDynamicReturnMem base ptr self out).size < USize.size ∧
    (balanceDynamicCalldataWords aw ptr).toNat * 32 < UInt256.size ∧
    96 ≤ (balanceDynamicCalldataWords aw ptr).toNat * 32 ∧
    (balanceDynamicReturnMem base ptr self out).readWithPadding 64 32 = ptr.toByteArray := by
  have hs := balanceDynamicReturnMem_size ptr self out hgap (by omega) hout
  obtain ⟨_, hb, hc⟩ := balanceDynamicWords_bounds aw ptr haw hfit
  refine ⟨by omega, ?_, hb, by omega, ?_⟩
  · rw [hs, Nat.sub_eq_zero_of_le (by omega)]
    exact lt_usize 0 (by omega)
  · exact (balanceDynamicReturnMem_read_below ptr self out 64 hin hlo hgap (by omega) hout).trans hread

end UniswapV2Pair
