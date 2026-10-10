import Benchmarks.UniswapV4PoolManager.AccountPoolTrace
import Benchmarks.UniswapV4PoolManager.PoolKeyPreservation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem PoolKeyView.accountDelta {mem ptr key} (h : PoolKeyView mem ptr key)
    (target currency : AccountAddress) (delta : Int) (hlo : 64 ≤ ptr.toNat) :
    PoolKeyView (accountDeltaMemory mem target currency delta) ptr key := by
  unfold accountDeltaMemory conditionalHashMemory
  split
  · exact h.twoWordHash _ _ hlo
  · exact h

theorem PoolKeyView.accountPool {mem ptr key} (h : PoolKeyView mem ptr key)
    (delta : UInt256) (target : AccountAddress) (hlo : 64 ≤ ptr.toNat) :
    PoolKeyView (accountPoolMemory mem key delta target) ptr key :=
  (h.accountDelta target _ _ hlo).accountDelta target _ _ hlo

theorem accountPoolMemory_size (mem : ByteArray) (key : PoolKeyWords) (delta : UInt256)
    (target : AccountAddress) (hm : 64 ≤ mem.size) :
    (accountPoolMemory mem key delta target).size = mem.size := by
  rw [accountPoolMemory, accountDeltaMemory_size _ _ _ _ (by rw [accountDeltaMemory_size _ _ _ _ hm]; exact hm),
    accountDeltaMemory_size _ _ _ _ hm]

theorem accountPoolMemory_load (mem : ByteArray) (key : PoolKeyWords) (delta : UInt256)
    (target : AccountAddress) (read : UInt256) (hoff : 64 ≤ read.toNat) (hin : read.toNat+32 ≤ mem.size) :
    memLoad read (accountPoolMemory mem key delta target) = memLoad read mem := by
  rw [accountPoolMemory, accountDeltaMemory_load _ _ _ _ _ hoff
    (by rw [accountDeltaMemory_size _ _ _ _ (by omega)]; exact hin), accountDeltaMemory_load _ _ _ _ _ hoff hin]

theorem accountPoolPost_env (evm : State) (key : PoolKeyWords) (delta : UInt256) (target : AccountAddress) :
    (accountPoolPost evm key delta target).executionEnv = evm.executionEnv := by
  rw [accountPoolPost, accountDeltaPost_env, accountDeltaPost_env]

theorem accountPoolPost_world (evm : State) (key : PoolKeyWords) (delta : UInt256) (target : AccountAddress) :
    (accountPoolPost evm key delta target).σ₀ = evm.σ₀ := by
  rw [accountPoolPost, accountDeltaPost_world, accountDeltaPost_world]

end Benchmarks.UniswapV4PoolManager
