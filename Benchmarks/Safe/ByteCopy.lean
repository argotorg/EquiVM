import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- GENERALIZES copyWhole_read to any in-bounds source slice.
theorem copySlice_read (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size) :
    (src.write srcOff mem dest len).readWithPadding dest len =
      src.extract srcOff (srcOff + len) := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_readWithPadding_zero]
    apply ByteArray.ext
    simp
  · rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by
      rw [copyWindow_size src mem srcOff dest len hz hsrc hdest]; omega)]
    simpa only [Nat.add_zero] using
      copyWindow_extract src mem srcOff dest len 0 len hz hsrc hdest (by omega)

-- LIBRARY CANDIDATE: a whole-buffer copy can be read back at any destination in memory.
theorem copyWhole_read (src mem : ByteArray) (dest : Nat) (hdest : dest ≤ mem.size) :
    (src.write 0 mem dest src.size).readWithPadding dest src.size = src := by
  simpa only [Nat.zero_add, byteArray_extract_self] using
    copySlice_read src mem 0 dest src.size (by omega) hdest

-- GENERALIZES copyWindow_read_preserved to arbitrary read lengths below the destination.
theorem copyWindowReadBelow (src mem : ByteArray) (srcOff dest len off count : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hbelow : off + count ≤ dest) :
    (src.write srcOff mem dest len).readWithPadding off count =
      mem.readWithPadding off count := by
  by_cases hz : len = 0
  · rw [hz, byteArray_write_zero_length]
  by_cases hc : count = 0
  · simp only [hc, byteArray_readWithPadding_zero]
  have hp : (mem.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  have hs : (src.extract srcOff (srcOff + len)).size = len := by
    rw [ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by
      have := byteArray_write_size_ge_base src mem srcOff dest len; omega),
    readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by omega),
    copyWindow_eq src mem srcOff dest len hz hsrc hdest,
    extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hp, hs]; omega),
    extract_append_left _ _ _ _ (by rw [hp]; omega), extract_extract_BA]
  congr 1 <;> omega

-- GENERALIZES copyWindow_read_preserved to arbitrary read lengths above the destination.
theorem copyWindowReadAbove (src mem : ByteArray) (srcOff dest len off count : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hin : off + count ≤ mem.size) (habove : dest + len ≤ off) :
    (src.write srcOff mem dest len).readWithPadding off count =
      mem.readWithPadding off count := by
  by_cases hz : len = 0
  · rw [hz, byteArray_write_zero_length]
  by_cases hc : count = 0
  · simp only [hc, byteArray_readWithPadding_zero]
  have hp : (mem.extract 0 dest ++ src.extract srcOff (srcOff + len)).size =
      dest + len := by
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract]
    omega
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by
      have := byteArray_write_size_ge_base src mem srcOff dest len; omega),
    readWithPadding_eq_extract_unbounded _ _ _ (by omega) hin,
    copyWindow_eq src mem srcOff dest len hz hsrc hdest,
    extract_append_right_window _ _ _ _ (by rw [hp]; omega), hp, extract_extract_BA]
  congr 1 <;> omega

end Benchmarks.Safe
