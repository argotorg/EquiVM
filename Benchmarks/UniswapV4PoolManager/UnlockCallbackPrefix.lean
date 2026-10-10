import Benchmarks.UniswapV4PoolManager.UnlockABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: precompile length words and in-bounds ABI words have the same value.
theorem nat_of_slice_word {data : ByteArray} {start : Nat} (hs : start+32 ≤ data.size) :
    nat_of_slice data start 32 = (calldataWord data start).toNat := by
  have he : (data.extract start (start+32)).size = 32 := by rw [ByteArray.size_extract]; omega
  rw [nat_of_slice, ByteArray.readWithoutPadding, if_neg (by omega), Nat.min_eq_left (by omega), he]
  simp only [Nat.sub_self, Nat.mul_zero, Nat.shiftLeft_zero]
  rw [← calldataWord_bytes_at hs, fromByteArrayBigEndian_toByteArray]

theorem unlockCallbackRequest_size (data : ByteArray) :
    68 ≤ (unlockCallbackSelector++bytesReturnEncoding data).size := by
  simp only [bytesReturnEncoding, bytesValueEncoding, ByteArray.size_append, toByteArray_size]
  change 68 ≤ 4+(32+(32+data.size+_))
  omega

theorem unlockCallbackRequest_head (data : ByteArray) :
    (unlockCallbackSelector++bytesReturnEncoding data).extract 0 32 =
      unlockCallbackSelector++ByteArray.zeroes 28 := by
  rw [bytesReturnEncoding, ← ByteArray.append_assoc, extract_append_left _ _ _ _ (by
    rw [ByteArray.size_append, toByteArray_size]; change 32 ≤ 4+32; omega)]
  rw [ByteArray.extract_append]
  change unlockCallbackSelector.extract 0 32 ++ (⟨32⟩ : UInt256).toByteArray.extract 0 28 = _
  have hs : unlockCallbackSelector.extract 0 32 = unlockCallbackSelector := by decide +kernel
  have hw : (⟨32⟩ : UInt256).toByteArray.extract 0 28 = ByteArray.zeroes 28 := by decide +kernel
  rw [hs, hw]

theorem unlockCallbackRequest_firstWord (data : ByteArray) :
    nat_of_slice (unlockCallbackSelector++bytesReturnEncoding data) 0 32 =
      unlockCallbackSelectorWord.toNat := by
  have hs := unlockCallbackRequest_size data
  have he : ((unlockCallbackSelector++bytesReturnEncoding data).extract 0 32).size = 32 := by
    rw [ByteArray.size_extract]; omega
  rw [nat_of_slice, ByteArray.readWithoutPadding, if_neg (by omega), Nat.min_eq_left (by omega)]
  change fromByteArrayBigEndian ((unlockCallbackSelector++bytesReturnEncoding data).extract 0 32) <<<
      (8*(32-((unlockCallbackSelector++bytesReturnEncoding data).extract 0 32).size)) = _
  rw [he, Nat.sub_self, Nat.mul_zero, Nat.shiftLeft_zero, unlockCallbackRequest_head]
  decide +kernel

theorem unlockCallbackRequest_not_return (data : ByteArray) :
    ¬BytesReturnBounds (unlockCallbackSelector++bytesReturnEncoding data) := by
  intro hb
  have hword := unlockCallbackRequest_firstWord data
  rw [nat_of_slice_word (by have := unlockCallbackRequest_size data; omega)] at hword
  have hsmall := hb.2.2.1
  rw [hword] at hsmall
  exact (show ¬unlockCallbackSelectorWord.toNat ≤ solcMaxU64 from by decide +kernel) hsmall

end Benchmarks.UniswapV4PoolManager
