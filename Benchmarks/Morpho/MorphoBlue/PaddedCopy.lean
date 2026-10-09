import Benchmarks.Morpho.MorphoBlue.ReturnDataMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

-- GENERALIZES copyWindow_size to include empty calldata payloads.
theorem copyWindow_size_or_zero (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size) :
    (src.write srcOff mem dest len).size = max mem.size (dest + len) := by
  by_cases hz : len = 0
  · simp only [hz, byteArray_write_len_zero, Nat.add_zero, Nat.max_eq_left hdest]
  · exact copyWindow_size src mem srcOff dest len hz hsrc hdest

-- GENERALIZES copyWindow_read_preserved to arbitrary windows below the destination.
theorem copyWindow_read_below_len (src mem : ByteArray) (srcOff dest len read count : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hbelow : read + count ≤ dest) :
    (src.write srcOff mem dest len).readWithPadding read count = mem.readWithPadding read count := by
  by_cases hz : len = 0
  · rw [hz, byteArray_write_len_zero]
  by_cases hc : count = 0
  · simp only [hc, byteArray_readWithPadding_zero]
  have hp : (mem.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  have hs : (src.extract srcOff (srcOff + len)).size = len := by rw [ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by
      rw [copyWindow_size src mem srcOff dest len hz hsrc hdest]; omega),
    copyWindow_eq src mem srcOff dest len hz hsrc hdest,
    extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hp, hs]; omega),
    extract_append_left _ _ _ _ (by rw [hp]; omega), extract_extract_BA]
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by omega)]
  congr 1 <;> omega

-- GENERALIZES copyWindow_read_word to the complete copied range, including empty ranges.
theorem copyWindow_read_all (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size) :
    (src.write srcOff mem dest len).readWithPadding dest len = src.readWithPadding srcOff len := by
  by_cases hz : len = 0
  · simp only [hz, byteArray_readWithPadding_zero]
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by
      rw [copyWindow_size src mem srcOff dest len hz hsrc hdest]; omega),
    readWithPadding_eq_extract_unbounded _ _ _ (by omega) hsrc]
  simpa only [Nat.add_zero] using copyWindow_extract src mem srcOff dest len 0 len hz hsrc hdest (by omega)

-- LIBRARY CANDIDATE: solc's calldata copy followed by its cleanup MSTORE.
def copyWithZeroWord (src mem : ByteArray) (srcOff dest len : Nat) : ByteArray :=
  writeWord (src.write srcOff mem dest len) (dest + len) (UInt256.ofNat 0)

theorem copyWithZeroWord_size (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size) :
    (copyWithZeroWord src mem srcOff dest len).size = max mem.size (dest + len + 32) := by
  have hs := copyWindow_size_or_zero src mem srcOff dest len hsrc hdest
  rw [copyWithZeroWord, writeWord_size _ _ _ (by rw [hs]; have hu := USize.size_pos; omega), hs]
  omega

theorem copyWithZeroWord_preserve (src mem : ByteArray) (srcOff dest len read count : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size)
    (hbelow : read + count ≤ dest) :
    (copyWithZeroWord src mem srcOff dest len).readWithPadding read count = mem.readWithPadding read count := by
  by_cases hc : count = 0
  · simp only [hc, byteArray_readWithPadding_zero]
  have hs := copyWindow_size_or_zero src mem srcOff dest len hsrc hdest
  unfold copyWithZeroWord Reasoning.Theory.writeWord
  rw [toByteArray_write_read_below_len_of_gap_unbounded _ _ _ _ _ (by rw [hs]; omega)
    (by omega) (by omega) (by rw [hs]; have hu := USize.size_pos; omega)]
  exact copyWindow_read_below_len src mem srcOff dest len read count hsrc hdest hbelow

theorem copyWithZeroWord_read (src mem : ByteArray) (srcOff dest len padding : Nat)
    (hsrc : srcOff + len ≤ src.size) (hdest : dest ≤ mem.size) (hpad : padding ≤ 32) :
    (copyWithZeroWord src mem srcOff dest len).readWithPadding dest (len + padding) =
      src.readWithPadding srcOff len ++ ByteArray.zeroes padding := by
  have hs := copyWindow_size_or_zero src mem srcOff dest len hsrc hdest
  have hg : dest + len - (src.write srcOff mem dest len).size < USize.size := by
    rw [hs]; have hu := USize.size_pos; omega
  have hleft : (copyWithZeroWord src mem srcOff dest len).readWithPadding dest len =
      src.readWithPadding srcOff len := by
    by_cases hz : len = 0
    · simp only [hz, byteArray_readWithPadding_zero]
    unfold copyWithZeroWord Reasoning.Theory.writeWord
    rw [toByteArray_write_read_below_len_of_gap_unbounded _ _ _ _ _ (by rw [hs]; omega)
      (by omega) (by omega) hg]
    exact copyWindow_read_all src mem srcOff dest len hsrc hdest
  have hright : (copyWithZeroWord src mem srcOff dest len).readWithPadding (dest + len) padding =
      ByteArray.zeroes padding := by
    by_cases hz : padding = 0
    · simp only [hz, byteArray_readWithPadding_zero, zeroes_zero (n := 0) rfl]
    have hr := writeWord_read_window (src.write srcOff mem dest len) (dest + len) 0 padding
      (UInt256.ofNat 0) (by omega) (by omega) (by omega) hg
    simp only [Nat.add_zero, Nat.zero_add] at hr
    change (copyWithZeroWord src mem srcOff dest len).readWithPadding (dest + len) padding = _ at hr
    rw [show (UInt256.ofNat 0).toByteArray = ByteArray.zeroes 32 from zero_toByteArray_eq_zeroes32,
      zeroes32_extract_zeroes padding hpad] at hr
    exact hr
  by_cases hz : len = 0
  · simpa only [hz, Nat.add_zero, Nat.zero_add, byteArray_readWithPadding_zero, ByteArray.empty_append]
      using hright
  by_cases hp : padding = 0
  · simpa only [hp, Nat.add_zero, zeroes_zero (n := 0) rfl, ByteArray.append_empty] using hleft
  rw [byteArray_readWithPadding_split_unbounded _ _ _ _ (by omega) (by omega)
    (by rw [copyWithZeroWord_size src mem srcOff dest len hsrc hdest]; omega), hleft, hright]

end Benchmarks.Morpho.MorphoBlue
