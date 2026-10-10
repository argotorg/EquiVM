import Benchmarks.UniswapV4PoolManager.PoolKeyEncodeMemory
import Benchmarks.UniswapV4PoolManager.BeforeSwapMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_043

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
open poolManagerBlocks
set_option maxRecDepth 5000

def beforeSwapKeyPrefixMemory (mem : ByteArray) (free keyPtr sender : UInt256) : ByteArray :=
  let m0 := writeWord mem (free+UInt256.ofNat 32).toNat beforeSwapSelectorWord
  let m1 := writeWord m0 (free+UInt256.ofNat 36).toNat sender
  let m2 := writeWord m1 (free+UInt256.ofNat 68).toNat (UInt256.land (memLoad keyPtr m1) solcAddrMask)
  let m3 := writeWord m2 ((free+UInt256.ofNat 68)+UInt256.ofNat 32).toNat
    (UInt256.land (memLoad (keyPtr+UInt256.ofNat 32) m2) solcAddrMask)
  writeWord m3 ((free+UInt256.ofNat 68)+UInt256.ofNat 64).toNat
    (UInt256.land (memLoad (keyPtr+UInt256.ofNat 64) m3) (UInt256.ofNat 16777215))

theorem beforeSwapKeyEncodeMemory {mem : ByteArray} {free keyPtr sender : UInt256} {key : PoolKeyWords}
    (hv : PoolKeyView mem keyPtr key) (hc : PoolKeyCanonical key)
    (hb : keyPtr.toNat+160 ≤ free.toNat) (hf : free.toNat+228 < UInt256.size) :
    poolManager_block_15370_memory
      (mem := beforeSwapKeyPrefixMemory mem free keyPtr sender)
      (x0 := UInt256.signextend ⟨2⟩ (memLoad (keyPtr+UInt256.ofNat 96)
        (beforeSwapKeyPrefixMemory mem free keyPtr sender)))
      (x1 := keyPtr) (x2 := UInt256.ofNat 128) (x3 := solcAddrMask) (x4 := UInt256.ofNat 128) (x5 := free+UInt256.ofNat 68) =
      wordCallMemory mem (free.toNat+32) beforeSwapSelectorWord (sender :: poolKeyWordList key) := by
  have hm : poolManager_block_15370_memory
      (mem := beforeSwapKeyPrefixMemory mem free keyPtr sender)
      (x0 := UInt256.signextend ⟨2⟩ (memLoad (keyPtr+UInt256.ofNat 96)
        (beforeSwapKeyPrefixMemory mem free keyPtr sender)))
      (x1 := keyPtr) (x2 := UInt256.ofNat 128) (x3 := solcAddrMask) (x4 := UInt256.ofNat 128) (x5 := free+UInt256.ofNat 68) =
      writeWord (poolKeyPrefixMemory mem free keyPtr beforeSwapSelectorWord sender)
        ((free+UInt256.ofNat 68)+UInt256.ofNat 128).toNat
        (UInt256.land (memLoad (keyPtr+UInt256.ofNat 128)
          (poolKeyPrefixMemory mem free keyPtr beforeSwapSelectorWord sender)) solcAddrMask) := rfl
  have h68 := uadd_word_ofNat_toNat free 68 (by omega : free.toNat+68 < UInt256.size)
  have h196 : ((free+UInt256.ofNat 68)+UInt256.ofNat 128).toNat = free.toNat+196 := by
    rw [uadd_word_ofNat_toNat _ 128 (by rw [h68]; omega), h68]
  rw [hm, poolKeyPrefixMemory_hook hv hc hb (by omega),
    poolKeyPrefixMemory_eq hv hc hb (by omega), h196]
  simp only [wordCallMemory, poolKeyPrefixWords, poolKeyWordList, wordSequenceMemory, Nat.add_assoc]

end Benchmarks.UniswapV4PoolManager
