import Examples.UniswapV2Pair.SwapCallbackCalldata
import Examples.UniswapV2Pair.SafeTransferMemoryReady
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

noncomputable def swapCallbackMem (I : ExecutionEnv) (mem : ByteArray) (ptr amount0Out amount1Out dataPtr dataLen : UInt256) : ByteArray :=
  swapCallbackPaddedMem I.calldata
    (swapCallbackHeadMem5 mem ptr (UInt256.ofNat I.source.val) amount0Out amount1Out dataLen) ptr dataPtr dataLen
abbrev swapCallbackWords (aw ptr dataLen : UInt256) : UInt256 :=
  swapCallbackPaddedWords (swapCallbackHeadWords5 aw ptr) ptr dataLen
abbrev swapCallbackCallLen (ptr dataLen : UInt256) : UInt256 :=
  UInt256.sub ((ptr + ⟨164⟩) + swapCallbackPaddedLen dataLen) ptr

theorem swapCallbackWords_bounds (aw ptr dataLen : UInt256)
    (haw : aw.toNat * 32 < UInt256.size) (hfit : ptr.toNat + dataLen.toNat + 227 < UInt256.size) :
    (swapCallbackWords aw ptr dataLen).toNat * 32 < UInt256.size ∧
      ptr.toNat + 196 + dataLen.toNat ≤ (swapCallbackWords aw ptr dataLen).toNat * 32 := by
  have h164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 (by omega)
  have hend : ((ptr + ⟨164⟩) + dataLen).toNat = ptr.toNat + 164 + dataLen.toNat := by
    rw [uadd_toNat, h164, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hbHead, _⟩ := swapCallbackHeadWords5_bounds aw ptr haw (by omega)
  have hbCopyNat : MachineState.M (swapCallbackHeadWords5 aw ptr).toNat (ptr + ⟨164⟩).toNat dataLen.toNat * 32 < UInt256.size :=
    MachineState_M_mul32_lt_of_bounds hbHead (by rw [h164]; omega)
  have hbCopy : (swapCallbackCopyWords (swapCallbackHeadWords5 aw ptr) ptr dataLen).toNat * 32 < UInt256.size := by
    unfold swapCallbackCopyWords
    rw [UInt256.toNat_ofNat_of_lt (by omega)]
    exact hbCopyNat
  have hb := UInt256_ofNat_M_mul32_lt (swapCallbackCopyWords (swapCallbackHeadWords5 aw ptr) ptr dataLen)
    ((ptr + ⟨164⟩) + dataLen) hbCopy (by rw [hend]; omega)
  have hc := UInt256_ofNat_M_covers (swapCallbackCopyWords (swapCallbackHeadWords5 aw ptr) ptr dataLen)
    ((ptr + ⟨164⟩) + dataLen) hbCopy (by rw [hend]; omega)
  refine ⟨hb, ?_⟩
  calc ptr.toNat + 196 + dataLen.toNat = ((ptr + ⟨164⟩) + dataLen).toNat + 32 := by rw [hend]; omega
       _ ≤ _ := hc

theorem swapCallbackMem_size {I : ExecutionEnv} {mem : ByteArray} (ptr amount0Out amount1Out dataPtr dataLen : UInt256)
    (hready : SafeTransferMemoryReady mem aw ptr)
    (hdata : dataPtr.toNat + dataLen.toNat ≤ I.calldata.size) (hlen : dataLen.toNat ≠ 0)
    (hfit : ptr.toNat + dataLen.toNat + 227 < UInt256.size) :
    (swapCallbackMem I mem ptr amount0Out amount1Out dataPtr dataLen).size = ptr.toNat + 196 + dataLen.toNat := by
  apply swapCallbackPaddedMem_size ptr dataPtr dataLen _ hdata hlen (by omega)
  rw [swapCallbackHeadMem5_size _ _ _ _ _ hready.gap (by omega), Nat.max_eq_right (by have := hready.sizeHi; omega)]

theorem swapCallbackMem_read64 {I : ExecutionEnv} {mem : ByteArray} (ptr amount0Out amount1Out dataPtr dataLen : UInt256)
    (hready : SafeTransferMemoryReady mem aw ptr)
    (hdata : dataPtr.toNat + dataLen.toNat ≤ I.calldata.size) (hlen : dataLen.toNat ≠ 0)
    (hfit : ptr.toNat + dataLen.toNat + 227 < UInt256.size) :
    (swapCallbackMem I mem ptr amount0Out amount1Out dataPtr dataLen).readWithPadding 64 32 = ptr.toByteArray := by
  have hs : (swapCallbackHeadMem5 mem ptr (UInt256.ofNat I.source.val) amount0Out amount1Out dataLen).size = ptr.toNat + 164 := by
    rw [swapCallbackHeadMem5_size _ _ _ _ _ hready.gap (by omega), Nat.max_eq_right (by have := hready.sizeHi; omega)]
  unfold swapCallbackMem
  rw [swapCallbackPaddedMem_read_below _ _ _ 64 32 hs hdata hlen (by omega) (by rw [hs]; omega) (by decide) (by decide),
    swapCallbackHeadMem5_read_below _ _ _ _ _ 64 hready.sizeLo (by have := hready.ptrLo; omega)
      hready.gap (by omega), hready.read64]

theorem swapCallbackCallLen_toNat (ptr dataLen : UInt256)
    (hfit : ptr.toNat + dataLen.toNat + 195 < UInt256.size) :
    (swapCallbackCallLen ptr dataLen).toNat = 164 + (swapCallbackPaddedLen dataLen).toNat := by
  have hr := swapCallbackPaddedLen_bounds dataLen (by omega)
  have h164 : (ptr + ⟨164⟩).toNat = ptr.toNat + 164 := uadd_word_ofNat_toNat ptr 164 (by omega)
  have hend : ((ptr + ⟨164⟩) + swapCallbackPaddedLen dataLen).toNat =
      ptr.toNat + 164 + (swapCallbackPaddedLen dataLen).toNat := by
    rw [uadd_toNat, h164, Nat.mod_eq_of_lt (by omega)]
  unfold swapCallbackCallLen
  rw [usub_toNat (by rw [hend]; omega), hend]
  omega

theorem swapCallbackMem_calldata {I : ExecutionEnv} {mem : ByteArray} (ptr amount0Out amount1Out dataPtr dataLen : UInt256)
    (hready : SafeTransferMemoryReady mem aw ptr)
    (hdata : dataPtr.toNat + dataLen.toNat ≤ I.calldata.size) (hlen : dataLen.toNat ≠ 0)
    (hfit : ptr.toNat + dataLen.toNat + 227 < UInt256.size) (hsmall : dataLen.toNat + 196 < 2 ^ 64) :
    (swapCallbackMem I mem ptr amount0Out amount1Out dataPtr dataLen).readWithPadding ptr.toNat
        (swapCallbackCallLen ptr dataLen).toNat =
      swapCallbackCalldata I.source amount0Out amount1Out
        (I.calldata.extract dataPtr.toNat (dataPtr.toNat + dataLen.toNat)) := by
  have hs : (swapCallbackHeadMem5 mem ptr (UInt256.ofNat I.source.val) amount0Out amount1Out dataLen).size = ptr.toNat + 164 := by
    rw [swapCallbackHeadMem5_size _ _ _ _ _ hready.gap (by omega), Nat.max_eq_right (by have := hready.sizeHi; omega)]
  have hsize : (I.calldata.extract dataPtr.toNat (dataPtr.toNat + dataLen.toNat)).size = dataLen.toNat := by
    rw [ByteArray.size_extract]; omega
  unfold swapCallbackMem
  rw [swapCallbackCallLen_toNat ptr dataLen (by omega),
    swapCallbackPaddedMem_calldata ptr dataPtr dataLen hs hdata hlen (by omega) hsmall,
    swapCallbackHeadMem5_calldata _ _ _ _ _ hready.gap (by omega)]
  unfold swapCallbackCalldata
  rw [hsize, u256_ofNat_toNat]

theorem swapCallbackMem_mload64 {I : ExecutionEnv} {mem : ByteArray} (ptr amount0Out amount1Out dataPtr dataLen : UInt256)
    (hready : SafeTransferMemoryReady mem aw ptr)
    (hdata : dataPtr.toNat + dataLen.toNat ≤ I.calldata.size) (hlen : dataLen.toNat ≠ 0)
    (hfit : ptr.toNat + dataLen.toNat + 227 < UInt256.size) :
    memoryWordLoad (swapCallbackMem I mem ptr amount0Out amount1Out dataPtr dataLen)
        (swapCallbackWords aw ptr dataLen) ⟨64⟩ = ptr ∧
      memoryWordActiveWords (swapCallbackWords aw ptr dataLen) ⟨64⟩ = swapCallbackWords aw ptr dataLen := by
  obtain ⟨hb, hc⟩ := swapCallbackWords_bounds aw ptr dataLen hready.wordsHi hfit
  have hc64 : (⟨64⟩ : UInt256).toNat + 32 ≤ (swapCallbackWords aw ptr dataLen).toNat * 32 := by
    change 64 + 32 ≤ _; omega
  refine ⟨?_, UInt256_M_same_of_cover _ _ hb hc64⟩
  apply mloadWordValue_of_readWithPadding
  · change 64 < _
    rw [swapCallbackMem_size _ _ _ _ _ hready hdata hlen hfit]; omega
  · exact UInt256_mload_haw_of_cover _ _ hb hc64
  · exact swapCallbackMem_read64 _ _ _ _ _ hready hdata hlen hfit

end UniswapV2Pair
