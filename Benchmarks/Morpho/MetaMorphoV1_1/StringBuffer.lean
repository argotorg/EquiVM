import Benchmarks.Morpho.MetaMorphoV1_1.StringMemoryRead
import Benchmarks.Morpho.MetaMorphoV1_1.HeapWordWindow

/-! Contents and preservation of an allocated memory string. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

structure StringBuffer (mem : ByteArray) (ptr : Nat) (bytes : ByteArray) : Prop where
  size : ptr + 32 + paddedSize bytes.size ≤ mem.size
  length : memLoad (UInt256.ofNat ptr) mem = UInt256.ofNat bytes.size
  data : mem.readWithPadding (ptr + 32) bytes.size = bytes

theorem StringBuffer.preserve {before after bytes : ByteArray} {ptr limit : Nat}
    (buffer : StringBuffer before ptr bytes) (h : MemoryPrefix before after limit)
    (hlo : 96 ≤ ptr) (hfit : ptr < UInt256.size)
    (hlimit : ptr + 32 + paddedSize bytes.size ≤ limit) : StringBuffer after ptr bytes := by
  have hcover : bytes.size ≤ paddedSize bytes.size := by unfold paddedSize; omega
  refine ⟨le_trans buffer.size h.size,
    (h.load_preserved hlo (by omega) (by have := buffer.size; omega) hfit).trans buffer.length, ?_⟩
  have heq : after.readWithPadding (ptr + 32) (paddedSize bytes.size) =
      before.readWithPadding (ptr + 32) (paddedSize bytes.size) :=
    SourceMemory.memoryPrefix_read_words h ((bytes.size + 31) / 32) (ptr + 32)
      (by omega) hlimit buffer.size
  rw [← memoryRead_prefix after (ptr + 32) (paddedSize bytes.size) bytes.size hcover
      (le_trans buffer.size h.size), heq,
    memoryRead_prefix before (ptr + 32) (paddedSize bytes.size) bytes.size hcover buffer.size,
    buffer.data]

end Benchmarks.Morpho.MetaMorphoV1_1
