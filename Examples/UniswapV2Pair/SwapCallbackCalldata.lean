import Examples.UniswapV2Pair.SwapCallbackCopyMemory
import Examples.UniswapV2Pair.SwapCallbackHeadMemory
import Examples.UniswapV2Pair.SwapCallbackABI
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: the ABI byte-list padding agrees with bytearray zero padding.
theorem padRightToWord_toByteArray (data : ByteArray) :
    (ABI.padRightToWord data.toList).toByteArray =
      data ++ ffi.ByteArray.zeroes (ABI.paddedSize data.size - data.size) := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [ABI.padRightToWord, ABI.zeroBytes, byteArray_zeroes_toList, byteArray_toList_eq]

set_option maxHeartbeats 1000000 in
theorem swapCallbackPaddedMem_calldata {calldata mem : ByteArray} (ptr dataPtr dataLen : UInt256)
    (hmem : mem.size = ptr.toNat + 164) (hdata : dataPtr.toNat + dataLen.toNat ≤ calldata.size)
    (hlen : dataLen.toNat ≠ 0) (hfit : ptr.toNat + 164 + dataLen.toNat < UInt256.size)
    (hsmall : dataLen.toNat + 196 < 2 ^ 64) :
    (swapCallbackPaddedMem calldata mem ptr dataPtr dataLen).readWithPadding ptr.toNat
        (164 + (swapCallbackPaddedLen dataLen).toNat) =
      mem.readWithPadding ptr.toNat 164 ++
        (ABI.padRightToWord (calldata.extract dataPtr.toNat (dataPtr.toNat + dataLen.toNat)).toList).toByteArray := by
  have hnum : 2 ^ 64 < UInt256.size := by native_decide
  have hround := swapCallbackPaddedLen_bounds dataLen (by omega)
  let data := calldata.extract dataPtr.toNat (dataPtr.toNat + dataLen.toNat)
  have hsdata : data.size = dataLen.toNat := by dsimp only [data]; rw [ByteArray.size_extract]; omega
  have hrounded : (swapCallbackPaddedLen dataLen).toNat = ABI.paddedSize data.size := by
    rw [swapCallbackPaddedLen_toNat dataLen (by omega), ABI.paddedSize, hsdata, Nat.mul_comm]
  rw [swapCallbackPaddedMem_eq_append ptr dataPtr dataLen hmem hdata hlen hfit,
    readWithPadding_eq_extract' _ ptr.toNat _ (by omega) (by omega)
      (by rw [ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract, toByteArray_size]; omega),
    ByteArray.append_assoc, extract_append_span _ _ _ _ (by omega) (by omega)]
  rw [show ptr.toNat + (164 + (swapCallbackPaddedLen dataLen).toNat) - mem.size =
      (swapCallbackPaddedLen dataLen).toNat by omega]
  change mem.extract ptr.toNat mem.size ++
    (data ++ (⟨0⟩ : UInt256).toByteArray).extract 0 (swapCallbackPaddedLen dataLen).toNat = _
  rw [extract_append_span _ _ _ _ (by omega) (by omega), byteArray_extract_self,
    zero_toByteArray_eq_zeroes32,
    zeroes32_extract_zeroes _ (by omega)]
  rw [show mem.size = ptr.toNat + 164 from hmem,
    ← readWithPadding_eq_extract' mem ptr.toNat 164 (by omega) (by omega) (by omega)]
  rw [padRightToWord_toByteArray, ← hrounded]

end UniswapV2Pair
