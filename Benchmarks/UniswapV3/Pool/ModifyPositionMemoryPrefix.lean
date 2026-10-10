import Benchmarks.UniswapV3.Pool.ModifyPositionPrefixTrace
import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleOracleTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem modifyPositionPrefixMemory_prefix (mem : ByteArray) (p : UInt256)
    (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs) (evm : EVM.State)
    (hb : p.toNat + 826 ≤ 2 ^ 200) :
    MemoryPrefix mem (modifyPositionPrefixMemory mem p v a evm) p.toNat := by
  have hp : (p + (⟨224⟩ : UInt256)).toNat = p.toNat + 224 :=
    uadd_word_ofNat_toNat p 224 (by change _ < 2 ^ 256; omega)
  have h1 := wordArrayAllocMem_prefix mem p (slot0StructWords evm.accountMap evm.executionEnv)
  have h2 := updatePositionMemory_prefix
    (wordArrayAllocMem mem p (slot0StructWords evm.accountMap evm.executionEnv))
    (p + ⟨224⟩) v (modifyPositionUpdateArgs a evm) evm (by rw [hp]; omega)
  exact h1.trans (h2.mono (by rw [hp]; omega))

theorem modifyPositionMiddleMemory_prefix (mem : ByteArray) (free : UInt256)
    (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs) (evm : EVM.State)
    (hb : free.toNat + 384 ≤ 2 ^ 200) :
    MemoryPrefix mem (modifyPositionMiddleMemory mem free v a evm) free.toNat :=
  oracleWriteMemory_prefix mem free (modifyPositionMiddleOracleArgs v a evm)
    (modifyPositionUpdatedState v a evm) hb

theorem modifyPositionMiddleFree_bounds (free : UInt256) (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) (hb : free.toNat + 384 ≤ 2 ^ 200) :
    free.toNat ≤ (modifyPositionMiddleFree free v a evm).toNat ∧
      (modifyPositionMiddleFree free v a evm).toNat ≤ free.toNat + 384 :=
  oracleWriteFree_bounds free (modifyPositionMiddleOracleArgs v a evm)
    (modifyPositionUpdatedState v a evm) hb

end Benchmarks.UniswapV3.Pool
