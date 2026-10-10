import Benchmarks.UniswapV4PoolManager.BytesMemory
import Benchmarks.UniswapV4PoolManager.WordArrayMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: loading the word just stored at an arbitrary offset.
theorem writeWord_sparse_load_back (mem : ByteArray) (ptr word : UInt256) :
    memLoad ptr (writeWord mem ptr.toNat word) = word := by
  apply mloadWordValue_of_readWithPadding
  · rw [writeWord_sparse_size]; omega
  · exact writeWord_sparse_read_back _ _ _

-- LIBRARY CANDIDATE: a sparse store preserves a preceding word load.
theorem writeWord_sparse_load_before (mem : ByteArray) (off : Nat) (word read : UInt256)
    (hin : read.toNat+32 ≤ mem.size) (hbefore : read.toNat+32 ≤ off) :
    memLoad read (writeWord mem off word) = memLoad read mem := by
  rw [memLoad, memLoad, if_neg (by rw [writeWord_sparse_size]; omega), if_neg (by omega),
    writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨hbefore, hin⟩)]

-- GENERALIZES copyWindow_size to include empty copies.
theorem copyWindow_size_any (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : srcOff+len ≤ src.size) (hdest : dest ≤ mem.size) :
    (src.write srcOff mem dest len).size = max mem.size (dest+len) := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_write_len_zero, Nat.add_zero, Nat.max_eq_left hdest]
  · exact copyWindow_size src mem srcOff dest len hz hsrc hdest

-- GENERALIZES copyWindow_read_word to arbitrary windows, including empty ones.
theorem copyWindow_read_any (src mem : ByteArray) (srcOff dest len off count : Nat)
    (hsrc : srcOff+len ≤ src.size) (hdest : dest ≤ mem.size)
    (hwithin : off+count ≤ len) :
    (src.write srcOff mem dest len).readWithPadding (dest+off) count =
      src.readWithPadding (srcOff+off) count := by
  by_cases hz : count = 0
  · subst count; simp only [byteArray_readWithPadding_zero]
  rw [readWithPadding_eq_extract_any _ _ _ (by
      rw [copyWindow_size_any _ _ _ _ _ hsrc hdest]; omega),
    readWithPadding_eq_extract_any _ _ _ (by omega),
    copyWindow_extract src mem srcOff dest len off count (by omega) hsrc hdest hwithin]

-- GENERALIZES copyWindow_read_preserved to arbitrary disjoint windows and empty copies.
theorem copyWindow_read_preserved_any (src mem : ByteArray) (srcOff dest len read count : Nat)
    (hsrc : srcOff+len ≤ src.size) (hdest : dest ≤ mem.size)
    (hin : read+count ≤ mem.size) (hdis : read+count ≤ dest ∨ dest+len ≤ read) :
    (src.write srcOff mem dest len).readWithPadding read count = mem.readWithPadding read count := by
  by_cases hz : count = 0
  · subst count; simp only [byteArray_readWithPadding_zero]
  by_cases hl : len = 0
  · subst len; rw [byteArray_write_len_zero]
  have hp : (mem.extract 0 dest).size = dest := by rw [ByteArray.size_extract]; omega
  have hs : (src.extract srcOff (srcOff+len)).size = len := by rw [ByteArray.size_extract]; omega
  rw [readWithPadding_eq_extract_any _ _ _ (by
      rw [copyWindow_size_any _ _ _ _ _ hsrc hdest]; omega),
    readWithPadding_eq_extract_any _ _ _ hin, copyWindow_eq src mem srcOff dest len hl hsrc hdest]
  rcases hdis with hlo | hhi
  · rw [extract_append_left _ _ _ _ (by rw [ByteArray.size_append, hp, hs]; omega),
      extract_append_left _ _ _ _ (by rw [hp]; omega), extract_extract_BA]
    congr 1 <;> omega
  · rw [extract_append_right_window _ _ _ _ (by rw [ByteArray.size_append, hp, hs]; omega),
      ByteArray.size_append, hp, hs, extract_extract_BA]
    congr 1 <;> omega

-- LIBRARY CANDIDATE: Solidity's copy followed by a zero word, at any in-memory destination.
def copyZeroMemory (src mem : ByteArray) (srcOff dest len : Nat) : ByteArray :=
  writeWord (src.write srcOff mem dest len) (dest+len) ⟨0⟩

theorem copyZeroMemory_size (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : srcOff+len ≤ src.size) (hdest : dest ≤ mem.size) :
    (copyZeroMemory src mem srcOff dest len).size = max mem.size (dest+len+32) := by
  rw [copyZeroMemory, writeWord_sparse_size, copyWindow_size_any _ _ _ _ _ hsrc hdest]
  omega

theorem copyZeroMemory_read_before (src mem : ByteArray) (srcOff dest len read count : Nat)
    (hsrc : srcOff+len ≤ src.size) (hdest : dest ≤ mem.size)
    (hbefore : read+count ≤ dest) :
    (copyZeroMemory src mem srcOff dest len).readWithPadding read count =
      mem.readWithPadding read count := by
  rw [copyZeroMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
      (by rw [copyWindow_size_any _ _ _ _ _ hsrc hdest]; omega) (.inl (by omega)),
    copyWindow_read_preserved_any _ _ _ _ _ _ _ hsrc hdest (by omega) (.inl hbefore)]

theorem copyZeroMemory_read_payload (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : srcOff+len ≤ src.size) (hdest : dest ≤ mem.size) :
    (copyZeroMemory src mem srcOff dest len).readWithPadding dest len =
      src.readWithPadding srcOff len := by
  rw [copyZeroMemory, writeWord_sparse_read_preserved_unbounded _ _ _ _ _
    (by rw [copyWindow_size_any _ _ _ _ _ hsrc hdest]; omega) (.inl (le_refl _))]
  simpa only [Nat.add_zero] using copyWindow_read_any src mem srcOff dest len 0 len
    hsrc hdest (by omega)

theorem copyZeroMemory_read_padding (src mem : ByteArray) (srcOff dest len count : Nat)
    (hc : count ≤ 32) :
    (copyZeroMemory src mem srcOff dest len).readWithPadding (dest+len) count =
      ByteArray.zeroes count := by
  by_cases hz : count = 0
  · subst count; rw [byteArray_readWithPadding_zero, zeroes_zero (by rfl)]
  have hr := writeWord_sparse_read_window (src.write srcOff mem dest len) (dest+len)
    0 count ⟨0⟩ (by omega) (by omega) (by omega)
  simpa only [Nat.add_zero, Nat.zero_add, zero_toByteArray_eq_zeroes32, zeroes32_extract_zeroes count hc]
    using hr

theorem copyZeroMemory_read_padded (src mem : ByteArray) (srcOff dest len : Nat)
    (hsrc : srcOff+len ≤ src.size) (hdest : dest ≤ mem.size) :
    (copyZeroMemory src mem srcOff dest len).readWithPadding dest (paddedSize len) =
      src.readWithPadding srcOff len ++ ByteArray.zeroes (paddedSize len-len) := by
  have hlo := nat_le_paddedSize len
  have hhi := paddedSize_le_add31 len
  rw [show paddedSize len = len+(paddedSize len-len) by omega,
    readWithPadding_split _ _ _ _ (by rw [copyZeroMemory_size _ _ _ _ _ hsrc hdest]; omega),
    copyZeroMemory_read_payload _ _ _ _ _ hsrc hdest,
    copyZeroMemory_read_padding _ _ _ _ _ _ (by omega)]
  congr 2
  omega

theorem copyZeroMemory_read_prefix (src mem : ByteArray) (srcOff dest len read head : Nat)
    (hsrc : srcOff+len ≤ src.size) (hdest : dest ≤ mem.size) (hhead : read+head = dest) :
    (copyZeroMemory src mem srcOff dest len).readWithPadding read (head+paddedSize len) =
      mem.readWithPadding read head ++
      (src.readWithPadding srcOff len ++ ByteArray.zeroes (paddedSize len-len)) := by
  have := paddedSize_le_add31 len
  rw [readWithPadding_split _ _ _ _ (by rw [copyZeroMemory_size _ _ _ _ _ hsrc hdest]; omega),
    copyZeroMemory_read_before _ _ _ _ _ _ _ hsrc hdest (by omega), hhead,
    copyZeroMemory_read_padded _ _ _ _ _ hsrc hdest]

theorem copyZeroMemory_load_before (src mem : ByteArray) (srcOff dest len : Nat) (read : UInt256)
    (hsrc : srcOff+len ≤ src.size) (hdest : dest ≤ mem.size)
    (hbefore : read.toNat+32 ≤ dest) :
    memLoad read (copyZeroMemory src mem srcOff dest len) = memLoad read mem := by
  rw [memLoad, memLoad, if_neg (by rw [copyZeroMemory_size _ _ _ _ _ hsrc hdest]; omega),
    if_neg (by omega), copyZeroMemory_read_before _ _ _ _ _ _ _ hsrc hdest hbefore]

end Benchmarks.UniswapV4PoolManager
