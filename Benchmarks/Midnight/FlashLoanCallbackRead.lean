import Benchmarks.Midnight.FlashLoanCallbackMemory

/-! Equality of the callback's runtime input bytes and its source ABI encoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem readWithPadding_split_inbounds (mem : ByteArray) (start first last : Nat)
    (h : start + first + last ≤ mem.size) :
    mem.readWithPadding start (first + last) =
      mem.readWithPadding start first ++ mem.readWithPadding (start + first) last := by
  by_cases hf : first = 0
  · subst first
    simp only [Nat.zero_add, Nat.add_zero, byteArray_readWithPadding_zero, ByteArray.empty_append]
  by_cases hl : last = 0
  · subst last
    simp only [Nat.add_zero, byteArray_readWithPadding_zero, ByteArray.append_empty]
  exact byteArray_readWithPadding_split_unbounded _ _ _ _ (by omega) (by omega) h

theorem flashLoanCallbackMemory_read (mem bytes : ByteArray) (sender : AccountAddress)
    (root tp tn ap an dp dl : Nat) (ha : ap + 32 * an ≤ bytes.size)
    (hd : dp + dl ≤ bytes.size) (hdl : dl < 2^64)
    (hb : root + 228 + 32 * tn + 32 * an < UInt256.size) :
    (flashLoanCallbackMemory mem bytes sender root tp tn ap an dp dl).readWithPadding root
        (flashLoanCallbackSize tn an dl) =
      flashLoanCallbackCalldata sender (calldataArrayWords bytes tn tp)
        (calldataArrayWords bytes an ap) (bytes.extract dp (dp + dl)) := by
  have hs := flashLoanCallbackMemory_size mem bytes sender root tp tn ap an dp dl ha hd
  have hw := flashLoanCallbackMemory_words mem bytes sender root tp tn ap an dp dl ha hd hb
  have hr := hw.read
  rw [flashLoanCallbackWords_length] at hr
  have htail : (flashLoanCallbackMemory mem bytes sender root tp tn ap an dp dl).readWithPadding
      (root + 228 + 32 * tn + 32 * an) (paddedSize dl) =
      bytes.extract dp (dp + dl) ++ ByteArray.zeroes (paddedSize dl - dl) := by
    have he : root + 228 + 32 * tn + 32 * an = (root + 196 + 32 * tn + 32 * an) + 32 := by omega
    rw [he]
    unfold flashLoanCallbackMemory calldataBytesEncodeMemory
    exact copyZeroMemory_read_padded _ _ _ _ _ hd hdl
  have hsize : (bytes.extract dp (dp + dl)).size = dl := by
    rw [ByteArray.size_extract]; omega
  have he : flashLoanCallbackSize tn an dl = 4 + (32 * (7 + tn + an) + paddedSize dl) := by
    unfold flashLoanCallbackSize returnDataAllocation paddedSize
    omega
  have hpad := paddedSize_le_add31 dl
  rw [he, readWithPadding_split_inbounds _ _ _ _ (by rw [hs]; omega),
    flashLoanCallbackMemory_selector _ _ _ _ _ _ _ _ _ _ ha hd,
    readWithPadding_split_inbounds _ _ _ _ (by rw [hs]; omega), hr,
    show root + 4 + 32 * (7 + tn + an) = root + 228 + 32 * tn + 32 * an by omega, htail]
  simp only [flashLoanCallbackCalldata, flashLoanCallbackWords, calldataArrayWords_length,
    wordArrayBytes_append, wordArrayBytes, ByteArray.append_empty,
    ByteArray.append_assoc, hsize]

end Benchmarks.Midnight
