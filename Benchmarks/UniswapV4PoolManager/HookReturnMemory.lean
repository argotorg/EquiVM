import Benchmarks.UniswapV4PoolManager.MemorySlice
import Benchmarks.UniswapV4PoolManager.BytesDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

/-- A hook preserves the caller's saved memory and leaves a specified allocation margin. -/
structure HookReturnMemory (room : Nat) (before after : ByteArray) (start free : UInt256) : Prop where
  freeLoad : memLoad (UInt256.ofNat 64) after = free
  lower : start.toNat ≤ free.toNat
  bound : free.toNat+room ≤ solcMaxU64
  saved : ∀ base data, MemorySlice before base data → 96 ≤ base → base+data.size ≤ start.toNat →
    MemorySlice after base data

end Benchmarks.UniswapV4PoolManager
