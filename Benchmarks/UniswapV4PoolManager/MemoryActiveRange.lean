import Benchmarks.UniswapV4PoolManager.MemoryGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: every word access inside a reserved range keeps active memory fixed.
theorem memoryWords_eq_self_of_range {aw base : UInt256} {n room : Nat}
    (h : base.toNat+room ≤ aw.toNat*32) (hn : n+32 ≤ room) :
    M aw (base+UInt256.ofNat n) ⟨32⟩ = aw := by
  apply memoryWords_eq_self
  have ho : (base+UInt256.ofNat n).toNat ≤ base.toNat+n := by
    rw [uadd_toNat]
    change (base.toNat+n%UInt256.size)%UInt256.size ≤ base.toNat+n
    exact (Nat.mod_le _ _).trans (Nat.add_le_add_left (Nat.mod_le _ _) _)
  change (base+UInt256.ofNat n).toNat+32 ≤ aw.toNat*32
  omega

end Benchmarks.UniswapV4PoolManager
