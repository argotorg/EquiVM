import Benchmarks.Safe.TransactionHashTrace
import Benchmarks.Safe.MemoryPreserves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem transactionHashMemory_preserves (mem : ByteArray) (ptr : Nat) (I : ExecutionEnv)
    (off : UInt256) (tx : SafeTransaction)
    (hi : off.toNat + tx.payload.size ≤ I.calldata.size) :
    MemoryPreserves mem (transactionHashMemory mem ptr I off tx) 0 ptr := by
  have hs := byteArray_write_size_ge_base I.calldata (domainMemoryAt mem ptr I)
    off.toNat ptr tx.payload.size
  have hd := domainMemoryAt_size mem ptr I
  refine ⟨?_, ?_⟩
  · rw [transactionHashMemory, transactionFinalMemory_size]
    omega
  · intro start count _ hb hin
    rw [transactionHashMemory, transactionFinalMemory_preserved _ _ _ _ _ _ (by omega) hb,
      copyWindowReadBelow _ _ _ _ _ _ _ hi (by omega) hb,
      domainMemoryAt, writeWords_readBelow _ _ _ _ _ hin hb]

end Benchmarks.Safe
