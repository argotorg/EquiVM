import Benchmarks.Midnight.MemoryBytesEncodeMemory

/-! Fixed-prefix reads and the length word of a memory-to-memory bytes encoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: a bytes encoder preserves earlier byte windows, including selectors.
theorem memoryBytesEncodeMemory_read_before (mem : ByteArray)
    (ptr output len read count : Nat) (hs : ptr + 32 + len ≤ mem.size)
    (hc : 0 < count) (hc64 : count < 2^64)
    (hin : read + count ≤ mem.size) (hl : read + count ≤ output) :
    (memoryBytesEncodeMemory mem ptr output len).readWithPadding read count =
      mem.readWithPadding read count := by
  rw [memoryBytesEncodeMemory_eq]
  exact calldataBytesEncodeMemory_read_before _ _ _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) hc hc64 hin hl

-- LIBRARY CANDIDATE: the length prefix is a singleton array of ABI words.
theorem memoryBytesEncodeMemory_header (mem : ByteArray) (ptr output len : Nat)
    (hs : ptr + 32 + len ≤ mem.size) (hb : output + 32 < UInt256.size) :
    MemoryWords (memoryBytesEncodeMemory mem ptr output len) output [UInt256.ofNat len] := by
  rw [memoryBytesEncodeMemory_eq]
  exact calldataBytesEncodeMemory_header _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) hb

end Benchmarks.Midnight
