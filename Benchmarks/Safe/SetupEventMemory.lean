import Benchmarks.Safe.AddressArrayEncoding
import Benchmarks.Safe.CalldataWords
import Benchmarks.Safe.MemoryBytesDecoded

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def setupEventHeader (mem : ByteArray) (ptr count : Nat) : ByteArray :=
  writeWord (writeWord mem ptr ⟨128⟩) (ptr + 128) (UInt256.ofNat count)

def setupEventMemory (mem : ByteArray) (ptr : Nat) (words : List UInt256)
    (threshold target fallbackHandler : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord
    (setupEventHeader mem ptr words.length ++ wordBytes words)
    (ptr + 32) threshold) (ptr + 64) target) (ptr + 96) fallbackHandler

theorem setupEventHeader_size (mem : ByteArray) (ptr count : Nat) (hm : mem.size ≤ ptr) :
    (setupEventHeader mem ptr count).size = ptr + 160 := by
  simp only [setupEventHeader, writeWord_sparse_size]
  omega

theorem setupEventMemory_size (mem : ByteArray) (ptr : Nat) (words : List UInt256)
    (threshold target fallbackHandler : UInt256) (hm : mem.size ≤ ptr) :
    (setupEventMemory mem ptr words threshold target fallbackHandler).size =
      ptr + 160 + 32 * words.length := by
  simp only [setupEventMemory, writeWord_sparse_size, ByteArray.size_append,
    setupEventHeader_size mem ptr words.length hm, wordBytes_size]
  omega

theorem setupEventHeader_read (mem : ByteArray) (ptr count off : Nat)
    (hm : mem.size ≤ ptr) (ho : off + 32 ≤ ptr)
    (hr : off + 32 ≤ mem.size ∨ mem.size ≤ off) :
    (setupEventHeader mem ptr count).readWithPadding off 32 = mem.readWithPadding off 32 := by
  rw [setupEventHeader, writeWord_sparse_read_preserved _ _ _ _
    (.inl ⟨by omega, by rw [writeWord_sparse_size]; omega⟩),
    writeWord_read_disjoint_padded _ _ _ _ hr (.inl ho)]

theorem setupEventMemory_read (mem : ByteArray) (ptr : Nat) (words : List UInt256)
    (threshold target fallbackHandler : UInt256) (off : Nat)
    (hm : mem.size ≤ ptr) (ho : off + 32 ≤ ptr)
    (hr : off + 32 ≤ mem.size ∨ mem.size ≤ off) :
    (setupEventMemory mem ptr words threshold target fallbackHandler).readWithPadding off 32 =
      mem.readWithPadding off 32 := by
  have hs : (setupEventHeader mem ptr words.length ++ wordBytes words).size =
      ptr + 160 + 32 * words.length := by
    rw [ByteArray.size_append, setupEventHeader_size _ _ _ hm, wordBytes_size]
  rw [setupEventMemory, writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨by omega, by rw [writeWord_sparse_size, writeWord_sparse_size, hs]; omega⟩),
    writeWord_sparse_read_preserved _ _ _ _
      (.inl ⟨by omega, by rw [writeWord_sparse_size, hs]; omega⟩),
    writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by omega, by rw [hs]; omega⟩),
    readAppendPrefix _ _ _ (by rw [setupEventHeader_size _ _ _ hm]; omega),
    setupEventHeader_read _ _ _ _ hm ho hr]

theorem setupEventMemory_load (mem : ByteArray) (ptr : Nat) (words : List UInt256)
    (threshold target fallbackHandler off : UInt256)
    (hm : mem.size ≤ ptr) (ho : off.toNat + 32 ≤ ptr)
    (hr : off.toNat + 32 ≤ mem.size ∨ mem.size ≤ off.toNat) :
    memLoad off (setupEventMemory mem ptr words threshold target fallbackHandler) =
      memLoad off mem := by
  rw [memLoadReadWord, setupEventMemory_read _ _ _ _ _ _ _ hm ho hr, ← memLoadReadWord]

end Benchmarks.Safe
