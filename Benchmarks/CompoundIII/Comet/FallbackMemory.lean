import Reasoning.HeapMemory

open Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: copying an entire byte array to offset zero has no size restriction.
theorem fallbackCopy_read (src mem : ByteArray) :
    (src.write 0 mem 0 src.size).readWithPadding 0 src.size = src := by
  by_cases hz : src.size = 0
  · have he := byteArray_eq_empty_of_size_eq_zero src hz
    subst src
    simp [ByteArray.write, ByteArray.readWithPadding, ByteArray.readWithoutPadding,
      zeroes_zero]
  · have hs := byteArray_write_all_size src mem 0 (Nat.zero_le _)
    rw [readWithPadding_eq_extract_unbounded _ 0 src.size (by omega) (by rw [hs]; omega)]
    apply ByteArray.ext
    rw [ByteArray.data_extract, write0_data src mem src.size hz le_rfl]
    rw [Array.extract_append_of_stop_le_size_left]
    · rw [Array.extract_extract]
      simp
    · rw [Array.size_extract]
      have : src.data.size = src.size := rfl
      omega

end Benchmarks.CompoundIII.Comet
