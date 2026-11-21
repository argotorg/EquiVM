import Benchmarks.Midnight.MemoryPrefix

/-! In-bounds source copies into sparse EVM memory, followed by Solidity's zero padding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem copySparse_size (src mem : ByteArray) (srcOff dest len : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) :
    (src.write srcOff mem dest len).size = max mem.size (dest + len) := by
  by_cases hd : dest ≤ mem.size
  · exact copyWindow_size src mem srcOff dest len hpos hsrc hd
  · rw [byteArray_write_from_ge_eq_no_gap_bound _ _ _ _ _ hpos hsrc (by omega)]
    simp only [ByteArray.size_append, ByteArray_zeroes_size, ByteArray.size_extract]
    omega

theorem copySparse_read (src mem : ByteArray) (srcOff dest len off count : Nat)
    (hsrc : srcOff + len ≤ src.size) (hc : 0 < count) (hw : off + count ≤ len) :
    (src.write srcOff mem dest len).readWithPadding (dest + off) count =
      src.readWithPadding (srcOff + off) count := by
  rw [readWithPadding_eq_extract_unbounded _ _ _ hc (by
      rw [copySparse_size _ _ _ _ _ (by omega) hsrc]; omega),
    readWithPadding_eq_extract_unbounded _ _ _ hc (by omega)]
  by_cases hd : dest ≤ mem.size
  · exact copyWindow_extract src mem srcOff dest len off count (by omega) hsrc hd hw
  · have hp : (mem ++ ByteArray.zeroes (dest - mem.size)).size = dest := by
      rw [ByteArray.size_append, ByteArray_zeroes_size]; omega
    rw [byteArray_write_from_ge_eq_no_gap_bound _ _ _ _ _ (by omega) hsrc (by omega),
      extract_append_right_window _ _ _ _ (by rw [hp]; omega), hp, extract_extract_BA]
    congr 1 <;> omega

theorem copySparse_read_before (src mem : ByteArray) (srcOff dest len read count : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hc : 0 < count)
    (hin : read + count ≤ mem.size) (hb : read + count ≤ dest) :
    (src.write srcOff mem dest len).readWithPadding read count =
      mem.readWithPadding read count := by
  rw [readWithPadding_eq_extract_unbounded _ _ _ hc (by
      rw [copySparse_size _ _ _ _ _ hpos hsrc]; omega),
    readWithPadding_eq_extract_unbounded _ _ _ hc hin]
  by_cases hd : dest ≤ mem.size
  · have hp : (mem.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
    rw [copyWindow_eq _ _ _ _ _ hpos hsrc hd,
      extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hp]; omega),
      extract_append_left _ _ _ _ (by rw [hp]; omega), extract_extract_BA]
    congr 1 <;> omega
  · rw [byteArray_write_from_ge_eq_no_gap_bound _ _ _ _ _ hpos hsrc (by omega),
      extract_append_left _ _ _ _ (by rw [ByteArray.size_append, ByteArray_zeroes_size]; omega),
      extract_append_left _ _ _ _ hin]

def copyZeroMemory (src mem : ByteArray) (srcOff dest len : Nat) : ByteArray :=
  writeWord (src.write srcOff mem dest len) (dest + len) ⟨0⟩

theorem copyZeroMemory_size (src mem : ByteArray) (srcOff dest len : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) :
    (copyZeroMemory src mem srcOff dest len).size = max mem.size (dest + len + 32) := by
  rw [copyZeroMemory, writeWord_sparse_size, copySparse_size _ _ _ _ _ hpos hsrc]
  omega

theorem copyZeroMemory_read (src mem : ByteArray) (srcOff dest len : Nat)
    (hpos : 0 < len) (hsrc : srcOff + len ≤ src.size) (hsmall : len < 2^64) :
    (copyZeroMemory src mem srcOff dest len).readWithPadding dest len =
      src.readWithPadding srcOff len := by
  rw [copyZeroMemory, writeWord_sparse_read_preserved_len _ _ _ _ _
    (by rw [copySparse_size _ _ _ _ _ (by omega) hsrc]; omega) (Or.inl le_rfl) hpos hsmall]
  simpa only [Nat.add_zero] using copySparse_read src mem srcOff dest len 0 len hsrc hpos (by omega)

theorem copyZeroMemory_read_before (src mem : ByteArray) (srcOff dest len read count : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hc : 0 < count) (hsmall : count < 2^64)
    (hin : read + count ≤ mem.size) (hb : read + count ≤ dest) :
    (copyZeroMemory src mem srcOff dest len).readWithPadding read count =
      mem.readWithPadding read count := by
  rw [copyZeroMemory, writeWord_sparse_read_preserved_len _ _ _ _ _
    (by rw [copySparse_size _ _ _ _ _ hpos hsrc]; omega) (Or.inl (by omega)) hc hsmall]
  exact copySparse_read_before src mem srcOff dest len read count hpos hsrc hc hin hb

theorem copyZeroMemory_load_before (src mem : ByteArray) (srcOff dest len : Nat) (read : UInt256)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size)
    (hin : read.toNat + 32 ≤ mem.size) (hb : read.toNat + 32 ≤ dest) :
    memLoad read (copyZeroMemory src mem srcOff dest len) = memLoad read mem := by
  rw [memLoad, memLoad, if_neg (by
      rw [copyZeroMemory_size _ _ _ _ _ hpos hsrc]; omega), if_neg (by omega)]
  rw [copyZeroMemory_read_before _ _ _ _ _ _ _ hpos hsrc (by decide) (by decide) hin hb]

theorem copyZeroMemory_prefix (src mem : ByteArray) (srcOff dest len limit : Nat)
    (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size) (hb : limit ≤ dest) :
    MemoryPrefix mem (copyZeroMemory src mem srcOff dest len) limit := by
  refine ⟨?_, fun off _ hlim hin ↦ ?_⟩
  · rw [copyZeroMemory_size _ _ _ _ _ hpos hsrc]; omega
  · exact copyZeroMemory_read_before _ _ _ _ _ _ _ hpos hsrc (by decide) (by decide) hin (by omega)

end Benchmarks.Midnight
