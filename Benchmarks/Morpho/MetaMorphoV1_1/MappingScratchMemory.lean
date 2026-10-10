import Benchmarks.Morpho.MetaMorphoV1_1.HeapWordWindow

/-! Mapping-hash scratch writes preserve the allocated heap and its cursor. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

-- LIBRARY CANDIDATE: heap preservation by a two-word mapping-hash scratch buffer.
theorem twoWordHashMem_prefix (mem : ByteArray) (key slot : UInt256) (limit : Nat) :
    MemoryPrefix mem (twoWordHashMem key slot mem) limit :=
  (memoryPrefix_sparse_writeWord mem 0 limit key (.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord (wordAt0Mem key mem) 32 limit slot (.inr (by decide)))

-- LIBRARY CANDIDATE: arbitrary allocation cursors survive mapping-hash scratch writes.
theorem twoWordHashMem_free {mem : ByteArray} (key slot : UInt256)
    (hmem : 96 ≤ mem.size) :
    memLoad ⟨64⟩ (twoWordHashMem key slot mem) = memLoad ⟨64⟩ mem := by
  simp only [memLoad, show (⟨64⟩ : UInt256).toNat = 64 from rfl,
    twoWordHashMem_read64_preserved_of_ge96 key slot hmem,
    twoWordHashMem_size_of_ge_64' key slot (by omega : 64 ≤ mem.size)]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
