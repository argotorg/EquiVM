import Benchmarks.UniswapV4PoolManager.PoolKeyEncodeMemory
import Benchmarks.UniswapV4PoolManager.AfterSwapMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_045

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

theorem afterSwapKeyEncodeMemory {I : ExecutionEnv} {mem : ByteArray} {free keyPtr : UInt256} {key : PoolKeyWords}
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+228 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) :
    poolManager_block_16079_memory (mem := poolManager_block_15936_memory (ee := I) (mem := mem) (x3 := keyPtr))
      (x0 := UInt256.ofNat 96) (x1 := keyPtr) (x2 := UInt256.ofNat 128)
      (x3 := UInt256.ofNat 1461501637330902918203684832716283019655932542975)
      (x4 := UInt256.ofNat 128) (x5 := free+UInt256.ofNat 68) =
      wordCallMemory mem (free.toNat+32) afterSwapSelectorWord (accountWord I.source :: poolKeyWordList key) := by
  have hm : poolManager_block_16079_memory (mem := poolManager_block_15936_memory (ee := I) (mem := mem) (x3 := keyPtr))
      (x0 := UInt256.ofNat 96) (x1 := keyPtr) (x2 := UInt256.ofNat 128)
      (x3 := UInt256.ofNat 1461501637330902918203684832716283019655932542975)
      (x4 := UInt256.ofNat 128) (x5 := free+UInt256.ofNat 68) =
      writeWord (poolKeyPrefixMemory mem free keyPtr afterSwapSelectorWord (accountWord I.source))
        ((free+UInt256.ofNat 68)+UInt256.ofNat 128).toNat
        (UInt256.land (memLoad (keyPtr+UInt256.ofNat 128)
          (poolKeyPrefixMemory mem free keyPtr afterSwapSelectorWord (accountWord I.source))) solcAddrMask) := by
    simp only [poolManager_block_16079_memory, poolManager_block_15936_memory, hfree,
      poolKeyPrefixMemory, afterSwapSelectorWord, accountWord, solcAddrMask, Reasoning.Theory.writeWord]
    rfl
  have h68 := uadd_word_ofNat_toNat free 68 (by omega : free.toNat+68 < UInt256.size)
  have h196 : ((free+UInt256.ofNat 68)+UInt256.ofNat 128).toNat = free.toNat+196 := by
    rw [uadd_word_ofNat_toNat _ 128 (by rw [h68]; omega), h68]
  rw [hm, poolKeyPrefixMemory_hook hv hc hb (by omega),
    poolKeyPrefixMemory_eq hv hc hb (by omega), h196]
  simp only [wordCallMemory, poolKeyPrefixWords, poolKeyWordList, wordSequenceMemory, Nat.add_assoc]

end Benchmarks.UniswapV4PoolManager
