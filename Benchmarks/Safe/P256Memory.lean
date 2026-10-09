import Benchmarks.Safe.P256Source
import Benchmarks.Safe.WordWrites
import Benchmarks.Safe.ByteCopy
import Benchmarks.Safe.GuardCallMemory
import Benchmarks.Safe.MemoryBytesDecoded

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def p256InputMemory (mem : ByteArray) (ptr : Nat) (p : P256Input) : ByteArray :=
  writeWords mem ptr (p256Words p)

def p256OutputMemory (mem : ByteArray) (ptr : Nat) (p : P256Input) (out : ByteArray) :
    ByteArray := out.write 0 (p256InputMemory mem ptr p) 0 (min 32 out.size)

theorem p256InputMemory_size (mem : ByteArray) (ptr : Nat) (p : P256Input) :
    (p256InputMemory mem ptr p).size = max mem.size (ptr + 160) :=
  writeWords_size_nonempty mem ptr (p256Words p) (by simp [p256Words])

theorem p256InputMemory_read (mem : ByteArray) (ptr : Nat) (p : P256Input) :
    (p256InputMemory mem ptr p).readWithPadding ptr 160 = wordBytes (p256Words p) :=
  writeWords_read mem ptr (p256Words p)

theorem p256OutputMemory_readBelow (mem out : ByteArray) (ptr off count : Nat) (p : P256Input)
    (hin : off + count ≤ mem.size) (hl : 32 ≤ off) (hh : off + count ≤ ptr) :
    (p256OutputMemory mem ptr p out).readWithPadding off count =
      mem.readWithPadding off count := by
  unfold p256OutputMemory
  rw [copyWindowReadAbove out _ 0 0 (min 32 out.size) off count
    (by omega) (Nat.zero_le _) (by rw [p256InputMemory_size]; omega) (by omega)]
  exact writeWords_readBelow _ _ _ _ _ hin hh

theorem p256OutputMemory_free {mem out : ByteArray} {ptr : Nat} {p : P256Input}
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr) :
    memLoad ⟨64⟩ (p256OutputMemory mem ptr p out) = memLoad ⟨64⟩ mem := by
  simp only [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    p256OutputMemory_readBelow mem out ptr 64 32 p hm (by decide) hp]

theorem p256OutputMemory_word (mem out : ByteArray) (ptr : Nat) (p : P256Input)
    (hl : 32 ≤ out.size) :
    memLoad ⟨0⟩ (p256OutputMemory mem ptr p out) = calldataWord out 0 :=
  memLoad_of_wordRead _ _ _ (callOutputWordAt _ out 0 (Nat.zero_le _) hl)

theorem p256OutputMemory_lower (mem out : ByteArray) (ptr : Nat) (p : P256Input) :
    mem.size ≤ (p256OutputMemory mem ptr p out).size := by
  have hh := byteArray_write_size_ge_base out (p256InputMemory mem ptr p) 0 0 (min 32 out.size)
  rw [p256InputMemory_size] at hh
  exact le_trans (Nat.le_max_left _ _) hh

end Benchmarks.Safe
