import Benchmarks.CompoundIII.Comet.MappingScratch

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: hashing a mapping key changes only the EVM scratch words.
theorem twoWordHashMem_prefix (mem : ByteArray) (key slot : UInt256) (limit : Nat) :
    MemoryPrefix mem (twoWordHashMem key slot mem) limit :=
  (memoryPrefix_sparse_writeWord mem 0 limit key (Or.inr (by decide))).trans
    (memoryPrefix_sparse_writeWord _ 32 limit slot (Or.inr (by decide)))

end Benchmarks.CompoundIII.Comet
