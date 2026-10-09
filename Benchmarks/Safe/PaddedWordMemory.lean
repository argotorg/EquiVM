import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a sparse-memory read beyond its stored bytes is zero padded.
theorem readPastMemory (mem : ByteArray) (off len : Nat) (h : mem.size ≤ off) :
    mem.readWithPadding off len = ByteArray.zeroes len := by
  simp [ByteArray.readWithPadding, ByteArray.readWithoutPadding, h]

-- LIBRARY CANDIDATE: any in-bounds window of a zero-filled buffer is zero filled.
theorem zeroes_extract_window (size off len : Nat) (h : off + len ≤ size) :
    (ByteArray.zeroes size).extract off (off + len) = ByteArray.zeroes len := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  rw [ByteArray.data_extract, Array.toList_extract, byteArray_zeroes_toList,
    byteArray_zeroes_toList]
  simp only [List.extract_eq_take_drop, List.drop_replicate, List.take_replicate]
  congr 1
  omega

-- LIBRARY CANDIDATE: word-aligned reads cannot straddle an aligned memory boundary.
theorem alignedReadBounds (size off : Nat) (hs : size % 32 = 0) (ho : off % 32 = 0) :
    off + 32 ≤ size ∨ size ≤ off := by
  omega

-- GENERALIZES sparse word-write preservation to reads wholly beyond stored memory.
theorem writeWord_read_disjoint_padded (mem : ByteArray) (off read : Nat) (word : UInt256)
    (hread : read + 32 ≤ mem.size ∨ mem.size ≤ read)
    (hdisj : read + 32 ≤ off ∨ off + 32 ≤ read) :
    (writeWord mem off word).readWithPadding read 32 = mem.readWithPadding read 32 := by
  rcases hread with hin | hout
  · exact writeWord_sparse_read_preserved mem off read word
      (hdisj.elim (fun h ↦ .inl ⟨h, hin⟩) (fun h ↦ .inr ⟨h, hin⟩))
  · rw [readPastMemory mem read 32 hout]
    rcases hdisj with hbefore | hafter
    · have hprefix : (mem ++ ByteArray.zeroes (off - mem.size)).size = off := by
        rw [ByteArray.size_append, ByteArray_zeroes_size]
        omega
      rw [writeWord_sparse_eq mem off word (by omega)]
      rw [readWithPadding_eq_extract _ read (by
        rw [ByteArray.size_append, hprefix, toByteArray_size]
        omega)]
      rw [extract_append_left _ _ _ _ (by rw [hprefix]; omega)]
      rw [extract_append_right_window _ _ _ _ hout]
      have he : read + 32 - mem.size = (read - mem.size) + 32 := by omega
      rw [he]
      exact zeroes_extract_window _ _ _ (by omega)
    · exact readPastMemory _ read 32 (by rw [writeWord_sparse_size]; omega)

-- LIBRARY CANDIDATE: word writes at aligned addresses preserve aligned memory size.
theorem writeWord_size_aligned (mem : ByteArray) (off : Nat) (word : UInt256)
    (hm : mem.size % 32 = 0) (ho : off % 32 = 0) :
    (writeWord mem off word).size % 32 = 0 := by
  rw [writeWord_sparse_size]
  by_cases h : mem.size ≤ off + 32
  · rw [Nat.max_eq_right h]
    omega
  · rw [Nat.max_eq_left (by omega)]
    exact hm

-- LIBRARY CANDIDATE: mapping scratch writes preserve even implicit zero-filled words.
theorem twoWordHashMem_read_padded (mem : ByteArray) (key slot : UInt256) (read : Nat)
    (hm : 64 ≤ mem.size) (halign : mem.size % 32 = 0)
    (hr : 64 ≤ read) (hread : read % 32 = 0) :
    (twoWordHashMem key slot mem).readWithPadding read 32 = mem.readWithPadding read 32 := by
  have hs : (writeWord mem 0 key).size = mem.size := by
    rw [writeWord_sparse_size, Nat.max_eq_left (by omega)]
  change (writeWord (writeWord mem 0 key) 32 slot).readWithPadding read 32 = _
  rw [writeWord_read_disjoint_padded _ 32 read slot
    (by rw [hs]; exact alignedReadBounds _ _ halign hread) (.inr (by omega))]
  exact writeWord_read_disjoint_padded _ 0 read key
    (alignedReadBounds _ _ halign hread) (.inr (by omega))

end Benchmarks.Safe
