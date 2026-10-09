import Benchmarks.Safe.WordArrayMemory
import Benchmarks.Safe.Memory
import Benchmarks.Safe.AddressArrayEncoding

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: padding always supplies the requested number of bytes.
theorem paddedReadSize (mem : ByteArray) (off len : Nat) :
    (mem.readWithPadding off len).size = len := by
  unfold ByteArray.readWithPadding
  rw [ByteArray.size_append, ByteArray_zeroes_size]
  have hh := Ethereum.EVM.ByteArray.readWithoutPadding_size_le mem off len
  omega

-- LIBRARY CANDIDATE: expose arbitrary memory as a finite list of its word reads.
def memoryWords (mem : ByteArray) (src count : Nat) : List UInt256 :=
  (List.range count).map (fun i ↦ uInt256OfByteArray (mem.readWithPadding (src + 32 * i) 32))

theorem memoryWords_length (mem : ByteArray) (src count : Nat) :
    (memoryWords mem src count).length = count := by simp [memoryWords]

theorem memoryWords_view (mem : ByteArray) (src count : Nat) :
    WordArrayMemory mem src (memoryWords mem src count) := by
  intro i hi
  simp only [memoryWords, List.getElem_map, List.getElem_range]
  exact (toByteArray_uInt256OfByteArray_of_size32 (paddedReadSize mem _ 32)).symm

-- LIBRARY CANDIDATE: extracting a prefix commutes with an in-bounds memory read.
theorem paddedReadPrefix (mem : ByteArray) (off len full : Nat)
    (hin : off + full ≤ mem.size) (hl : len ≤ full) :
    (mem.readWithPadding off full).extract 0 len = mem.readWithPadding off len := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_readWithPadding_zero]
    apply ByteArray.ext
    simp [ByteArray.data_extract]
  · rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) hin,
      readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by omega), extract_extract_BA]
    simp only [Nat.add_zero, Nat.min_eq_left (by omega : off + len ≤ off + full)]

-- LIBRARY CANDIDATE: a window of an in-bounds memory read is the corresponding memory read.
theorem paddedReadWindow (mem : ByteArray) (off start len full : Nat)
    (hin : off + full ≤ mem.size) (hl : start + len ≤ full) :
    (mem.readWithPadding off full).extract start (start + len) =
      mem.readWithPadding (off + start) len := by
  by_cases hz : len = 0
  · subst len
    rw [byteArray_readWithPadding_zero]
    apply ByteArray.ext
    simp
  · rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) hin,
      readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by omega), extract_extract_BA]
    congr 1 <;> omega

theorem memoryWords_prefix (mem : ByteArray) (src len count : Nat)
    (hin : src + 32 * count ≤ mem.size) (hl : len ≤ 32 * count) :
    (wordBytes (memoryWords mem src count)).extract 0 len = mem.readWithPadding src len := by
  have hr := (memoryWords_view mem src count).read mem src (memoryWords mem src count)
    (by simpa only [memoryWords_length] using hin)
  rw [memoryWords_length] at hr
  rw [← hr]
  exact paddedReadPrefix mem src len (32 * count) hin hl

-- LIBRARY CANDIDATE: the cleanup MSTORE supplies zero bytes after a copied byte buffer.
theorem zeroTailRead (mem : ByteArray) (ptr len padded : Nat)
    (hin : ptr + len ≤ mem.size) (hl : len ≤ padded) (hp : padded ≤ len + 32) :
    (writeWord mem (ptr + len) ⟨0⟩).readWithPadding ptr padded =
      mem.readWithPadding ptr len ++ ByteArray.zeroes (padded - len) := by
  have htail : (writeWord mem (ptr + len) ⟨0⟩).readWithPadding (ptr + len) (padded - len) =
      ByteArray.zeroes (padded - len) := by
    by_cases hz : padded - len = 0
    · rw [hz, byteArray_readWithPadding_zero, zeroes_zero rfl]
    · have hr := writeWord_sparse_read_window mem (ptr + len) 0 (padded - len) ⟨0⟩
        (by omega) (by omega) (by omega)
      rw [show (⟨0⟩ : UInt256).toByteArray = ByteArray.zeroes 32 from by decide +kernel] at hr
      have he : (ByteArray.zeroes 32).extract 0 (padded - len) =
          ByteArray.zeroes (padded - len) := by
        simpa only [Nat.zero_add] using zeroes_extract_window 32 0 (padded - len) (by omega)
      simpa only [Nat.add_zero, Nat.zero_add, he] using hr
  have hprefix : (writeWord mem (ptr + len) ⟨0⟩).readWithPadding ptr len =
      mem.readWithPadding ptr len := by
    by_cases hz : len = 0
    · simp only [hz, byteArray_readWithPadding_zero]
    · exact write32_read_below_len_unbounded _ _ _ _ _ (by rw [toByteArray_size])
        hin (le_refl _) hin (by omega)
  by_cases hz : len = 0
  · simpa only [hz, Nat.add_zero, Nat.sub_zero, byteArray_readWithPadding_zero,
      ByteArray.empty_append] using htail
  by_cases he : padded = len
  · rw [he, Nat.sub_self, zeroes_zero rfl, ByteArray.append_empty, hprefix]
  · rw [show padded = len + (padded - len) by omega,
      byteArray_readWithPadding_split_unbounded _ _ _ _ (by omega) (by omega) (by
        rw [writeWord_sparse_size]; omega), hprefix, htail]
    simp only [Nat.add_sub_cancel_left]

-- GENERALIZES writeWord_sparse_read_preserved to unrestricted read lengths below the write.
theorem writeWordReadBelow (mem : ByteArray) (dst off count : Nat) (word : UInt256)
    (hin : off + count ≤ mem.size) (ha : off + count ≤ dst) :
    (writeWord mem dst word).readWithPadding off count = mem.readWithPadding off count := by
  by_cases hz : count = 0
  · simp only [hz, byteArray_readWithPadding_zero]
  by_cases hd : dst ≤ mem.size
  · exact write32_read_below_len_unbounded _ _ _ _ _ (by rw [toByteArray_size])
      hd ha hin (by omega)
  · rw [writeWord_sparse_eq _ _ _ (by omega),
      readAppendPrefixLen _ _ _ _ (by rw [ByteArray.size_append]; omega),
      readAppendPrefixLen _ _ _ _ hin]

-- GENERALIZES write32_read_above_len to unrestricted read lengths.
set_option maxHeartbeats 1000000 in
theorem writeWordReadAbove (mem : ByteArray) (dst off count : Nat) (word : UInt256)
    (hin : off + count ≤ mem.size) (ha : dst + 32 ≤ off) :
    (writeWord mem dst word).readWithPadding off count = mem.readWithPadding off count := by
  by_cases hz : count = 0
  · simp only [hz, byteArray_readWithPadding_zero]
  have hp : (mem.extract 0 dst ++ word.toByteArray.extract 0 32).size = dst + 32 := by
    rw [ByteArray.size_append, ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
    omega
  have ht : (mem.extract (dst + 32) mem.size).size = mem.size - (dst + 32) := by
    rw [ByteArray.size_extract]; omega
  unfold Reasoning.Theory.writeWord
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by
      rw [ByteArray.size_append, hp, ht]; omega),
    readWithPadding_eq_extract_unbounded _ _ _ (by omega) hin,
    extract_append_right_window _ _ _ _ (by rw [hp]; omega), hp, extract_extract_BA]
  congr 1 <;> omega

end Benchmarks.Safe
