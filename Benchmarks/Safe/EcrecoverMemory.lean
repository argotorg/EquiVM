import Benchmarks.Safe.EcrecoverSource
import Benchmarks.Safe.WordWrites
import Benchmarks.Safe.ByteCopy
import Benchmarks.Safe.GuardCallMemory
import Benchmarks.Safe.MemoryBytesDecoded

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def ecrecoverInputMemory (mem : ByteArray) (ptr : Nat) (p : EcrecoverInput) : ByteArray :=
  writeWords (writeWord (writeWord mem ptr ⟨0⟩) 64 (UInt256.ofNat (ptr + 32)))
    (ptr + 32) (ecrecoverWords p)

def ecrecoverOutputMemory (mem : ByteArray) (ptr : Nat) (p : EcrecoverInput)
    (out : ByteArray) : ByteArray :=
  out.write 0 (ecrecoverInputMemory mem ptr p) ptr (min 32 out.size)

theorem ecrecoverInputMemory_size (mem : ByteArray) (ptr : Nat) (p : EcrecoverInput)
    (hp : 96 ≤ ptr) :
    (ecrecoverInputMemory mem ptr p).size = max mem.size (ptr + 160) := by
  rw [ecrecoverInputMemory, writeWords_size_nonempty _ _ _ (by simp [ecrecoverWords])]
  simp only [writeWord_sparse_size, ecrecoverWords, List.length_cons, List.length_nil]
  omega

theorem ecrecoverInputMemory_read (mem : ByteArray) (ptr : Nat) (p : EcrecoverInput) :
    (ecrecoverInputMemory mem ptr p).readWithPadding (ptr + 32) 128 =
      wordBytes (ecrecoverWords p) := writeWords_read _ _ _

theorem ecrecoverInputMemory_free (mem : ByteArray) (ptr : Nat) (p : EcrecoverInput)
    (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (ecrecoverInputMemory mem ptr p) = UInt256.ofNat (ptr + 32) := by
  apply memLoad_of_wordRead
  change (ecrecoverInputMemory mem ptr p).readWithPadding 64 32 = _
  rw [ecrecoverInputMemory, writeWords_readBelow _ _ _ _ _ (by
    simp only [writeWord_sparse_size]; omega) (by omega), writeWord_sparse_read_back]

theorem ecrecoverInputMemory_zero (mem : ByteArray) (ptr : Nat) (p : EcrecoverInput)
    (hp : 96 ≤ ptr) :
    (ecrecoverInputMemory mem ptr p).readWithPadding ptr 32 = (⟨0⟩ : UInt256).toByteArray := by
  rw [ecrecoverInputMemory, writeWords_readBelow _ _ _ _ _ (by
    simp only [writeWord_sparse_size]; omega) (by omega),
    writeWordReadAbove _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) hp,
    writeWord_sparse_read_back]

theorem ecrecoverInputMemory_preserved (mem : ByteArray) (ptr off count : Nat)
    (p : EcrecoverInput) (hin : off + count ≤ mem.size) (hl : 96 ≤ off)
    (hh : off + count ≤ ptr) :
    (ecrecoverInputMemory mem ptr p).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [ecrecoverInputMemory, writeWords_readBelow _ _ _ _ _ (by
    simp only [writeWord_sparse_size]; omega) (by omega),
    writeWordReadAbove _ _ _ _ _ (by rw [writeWord_sparse_size]; omega) hl,
    writeWordReadBelow _ _ _ _ _ hin hh]

theorem ecrecoverOutputMemory_size (mem out : ByteArray) (ptr : Nat) (p : EcrecoverInput)
    (hp : 96 ≤ ptr) :
    (ecrecoverOutputMemory mem ptr p out).size = max mem.size (ptr + 160) := by
  by_cases hz : out.size = 0
  · simp only [ecrecoverOutputMemory, hz, Nat.min_zero, byteArray_write_zero_length,
      ecrecoverInputMemory_size _ _ _ hp]
  rw [ecrecoverOutputMemory, copyWindow_size _ _ _ _ _ (by omega) (by omega)
    (by rw [ecrecoverInputMemory_size _ _ _ hp]; omega), ecrecoverInputMemory_size _ _ _ hp]
  omega

theorem ecrecoverOutputMemory_preserved (mem out : ByteArray) (ptr off count : Nat)
    (p : EcrecoverInput) (hin : off + count ≤ mem.size) (hl : 96 ≤ off)
    (hh : off + count ≤ ptr) :
    (ecrecoverOutputMemory mem ptr p out).readWithPadding off count =
      mem.readWithPadding off count := by
  rw [ecrecoverOutputMemory, copyWindowReadBelow _ _ _ _ _ _ _ (by omega)
    (by rw [ecrecoverInputMemory_size _ _ _ (by omega)]; omega) hh,
    ecrecoverInputMemory_preserved _ _ _ _ _ hin hl hh]

theorem ecrecoverOutputMemory_free (mem out : ByteArray) (ptr : Nat) (p : EcrecoverInput)
    (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (ecrecoverOutputMemory mem ptr p out) = UInt256.ofNat (ptr + 32) := by
  rw [ecrecoverOutputMemory, memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    copyWindowReadBelow _ _ _ _ _ _ _ (by omega)
      (by rw [ecrecoverInputMemory_size _ _ _ hp]; omega) hp,
    ← show (⟨64⟩ : UInt256).toNat = 64 from rfl, ← memLoadReadWord,
    ecrecoverInputMemory_free _ _ _ hp]

theorem ecrecoverOutputMemory_word (mem out : ByteArray) (ptr : Nat) (p : EcrecoverInput)
    (hp : 96 ≤ ptr) (hb : ptr < UInt256.size) (ho : EcrecoverOutput out) :
    memLoad (UInt256.ofNat ptr) (ecrecoverOutputMemory mem ptr p out) = calldataWord out 0 := by
  apply memLoad_of_wordRead
  rw [ulit_toNat' ptr hb]
  rcases ho with rfl | ⟨hs, _⟩
  · simp only [ecrecoverOutputMemory, ByteArray.size_empty, Nat.min_zero,
      byteArray_write_zero_length, ecrecoverInputMemory_zero _ _ _ hp]
    decide +kernel
  · exact callOutputWordAt _ out ptr (by rw [ecrecoverInputMemory_size _ _ _ hp]; omega)
      (by omega)

end Benchmarks.Safe
