import Benchmarks.Safe.ByteCopy
import Benchmarks.Safe.MemoryPreserves
import Benchmarks.Safe.WordArrayBuffer
import Benchmarks.Safe.CalldataWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: allocating a length-prefixed calldata slice with a zero cleanup word.
def calldataBufferHeader (mem : ByteArray) (ptr count finish : Nat) : ByteArray :=
  writeWord (writeWord mem 64 (UInt256.ofNat finish)) ptr (UInt256.ofNat count)

def calldataBufferMemory (cd mem : ByteArray) (src ptr len count finish : Nat) : ByteArray :=
  writeWord (cd.write src (calldataBufferHeader mem ptr count finish) (ptr + 32) len)
    (ptr + 32 + len) ⟨0⟩

theorem calldataBufferHeader_size (mem : ByteArray) (ptr count finish : Nat)
    (hm : 96 ≤ mem.size) :
    (calldataBufferHeader mem ptr count finish).size = max mem.size (ptr + 32) := by
  rw [calldataBufferHeader, writeWord_sparse_size, writeWord_sparse_size]
  omega

theorem calldataBufferMemory_size (cd mem : ByteArray) (src ptr len count finish : Nat)
    (hm : 96 ≤ mem.size) (hs : src + len ≤ cd.size) :
    (calldataBufferMemory cd mem src ptr len count finish).size =
      max mem.size (ptr + 64 + len) := by
  rw [calldataBufferMemory, writeWord_sparse_size]
  by_cases hz : len = 0
  · rw [hz, byteArray_write_zero_length, calldataBufferHeader_size _ _ _ _ hm]
    omega
  · rw [copyWindow_size _ _ _ _ _ (by omega) hs
      (by rw [calldataBufferHeader_size _ _ _ _ hm]; omega),
      calldataBufferHeader_size _ _ _ _ hm]
    omega

theorem calldataBufferMemory_payload (cd mem : ByteArray) (src ptr len count finish : Nat)
    (hm : 96 ≤ mem.size) (hs : src + len ≤ cd.size) :
    (calldataBufferMemory cd mem src ptr len count finish).readWithPadding (ptr + 32) len =
      cd.extract src (src + len) := by
  have hd : ptr + 32 ≤ (calldataBufferHeader mem ptr count finish).size := by
    rw [calldataBufferHeader_size _ _ _ _ hm]; omega
  have hi : ptr + 32 + len ≤
      (cd.write src (calldataBufferHeader mem ptr count finish) (ptr + 32) len).size := by
    by_cases hz : len = 0
    · rw [hz, byteArray_write_zero_length]; omega
    · rw [copyWindow_size _ _ _ _ _ (by omega) hs hd]; omega
  rw [calldataBufferMemory, writeWordReadBelow _ _ _ _ _ hi (by omega),
    copySlice_read _ _ _ _ _ hs hd]

theorem calldataBufferMemory_length (cd mem : ByteArray) (src ptr len count finish : Nat)
    (hm : 96 ≤ mem.size) (hs : src + len ≤ cd.size) :
    (calldataBufferMemory cd mem src ptr len count finish).readWithPadding ptr 32 =
      (UInt256.ofNat count).toByteArray := by
  have hd : ptr + 32 ≤ (calldataBufferHeader mem ptr count finish).size := by
    rw [calldataBufferHeader_size _ _ _ _ hm]; omega
  have hcopy := byteArray_write_size_ge_base cd
    (calldataBufferHeader mem ptr count finish) src (ptr + 32) len
  rw [calldataBufferMemory, writeWordReadBelow _ _ _ _ _ (by omega) (by omega),
    copyWindowReadBelow _ _ _ _ _ _ _ hs hd (by omega), calldataBufferHeader,
    writeWord_sparse_read_back]

theorem calldataBufferMemory_free (cd mem : ByteArray) (src ptr len count finish : Nat)
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) (hs : src + len ≤ cd.size) :
    memLoad ⟨64⟩ (calldataBufferMemory cd mem src ptr len count finish) =
      UInt256.ofNat finish := by
  apply memLoad_of_wordRead
  change (calldataBufferMemory cd mem src ptr len count finish).readWithPadding 64 32 = _
  have hd : ptr + 32 ≤ (calldataBufferHeader mem ptr count finish).size := by
    rw [calldataBufferHeader_size _ _ _ _ hm]; omega
  have hcopy := byteArray_write_size_ge_base cd
    (calldataBufferHeader mem ptr count finish) src (ptr + 32) len
  rw [calldataBufferMemory, writeWordReadBelow _ _ _ _ _ (by omega) (by omega),
    copyWindowReadBelow _ _ _ _ _ _ _ hs hd (by omega), calldataBufferHeader,
    writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨by omega, by rw [writeWord_sparse_size]; omega⟩), writeWord_sparse_read_back]

theorem calldataBufferMemory_preserved (cd mem : ByteArray) (src ptr len count finish : Nat)
    (hm : 96 ≤ mem.size) (hs : src + len ≤ cd.size) :
    MemoryPreserves mem (calldataBufferMemory cd mem src ptr len count finish) 96 ptr := by
  refine ⟨?_, ?_⟩
  · rw [calldataBufferMemory_size _ _ _ _ _ _ _ hm hs]; omega
  · intro off width hlo hhi hin
    have hh := calldataBufferHeader_size mem ptr count finish hm
    have hcopy := byteArray_write_size_ge_base cd
      (calldataBufferHeader mem ptr count finish) src (ptr + 32) len
    rw [calldataBufferMemory, writeWordReadBelow _ _ _ _ _ (by omega) (by omega),
      copyWindowReadBelow _ _ _ _ _ _ _ hs (by omega) (by omega), calldataBufferHeader,
      writeWordReadBelow _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) (by omega),
      writeWordReadAbove _ _ _ _ _ hin (by omega)]

theorem calldataBufferMemory_bytes (cd mem : ByteArray) (src ptr len finish : Nat)
    (hm : 96 ≤ mem.size) (hs : src + len ≤ cd.size) (hp : ptr < UInt256.size) :
    BytesMemory (calldataBufferMemory cd mem src ptr len len finish) ptr
      (cd.extract src (src + len)) := by
  have hl : (cd.extract src (src + len)).size = len := by
    rw [ByteArray.size_extract]; omega
  refine ⟨?_, ?_, ?_⟩
  · apply memLoad_of_wordRead
    rw [ulit_toNat' ptr hp, hl]
    exact calldataBufferMemory_length _ _ _ _ _ _ _ hm hs
  · rw [hl]
    exact calldataBufferMemory_payload _ _ _ _ _ _ _ hm hs
  · rw [hl, calldataBufferMemory_size _ _ _ _ _ _ _ hm hs]; omega

theorem calldataBufferMemory_words (cd mem : ByteArray) (src ptr count finish : Nat)
    (hm : 96 ≤ mem.size) (hs : src + 32 * count ≤ cd.size) :
    WordArrayBuffer (calldataBufferMemory cd mem src ptr (32 * count) count finish) ptr
      (calldataWords cd src count) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [calldataWords_length, calldataBufferMemory_size _ _ _ _ _ _ _ hm hs]; omega
  · rw [calldataWords_length]
    exact calldataBufferMemory_length _ _ _ _ _ _ _ hm hs
  · intro i hi
    have hi' : i < count := by rwa [calldataWords_length] at hi
    have hr := paddedReadWindow
      (calldataBufferMemory cd mem src ptr (32 * count) count finish)
      (ptr + 32) (32 * i) 32 (32 * count)
      (by rw [calldataBufferMemory_size _ _ _ _ _ _ _ hm hs]; omega) (by omega)
    have hread : (calldataBufferMemory cd mem src ptr (32 * count) count finish).readWithPadding
        (ptr + 32) (32 * count) = cd.readWithPadding src (32 * count) := by
      rw [calldataBufferMemory_payload _ _ _ _ _ _ _ hm hs,
        readWithPadding_eq_extract_unbounded _ _ _ (by omega) hs]
    rw [hread, paddedReadWindow cd src (32 * i) 32 (32 * count) hs (by omega)] at hr
    exact hr.symm.trans (calldataWords_view cd src count hs i hi)

end Benchmarks.Safe
