import Benchmarks.UniswapV4PoolManager.PoolKeyPreservation
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_029

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def donateEventMemory (mem : ByteArray) (free amount0 amount1 : UInt256) : ByteArray :=
  wordSequenceMemory mem free.toNat [amount0, amount1]

theorem donateEventMemory_compiled {mem : ByteArray} {free amount0 amount1 : UInt256}
    (hf : free.toNat+32 < UInt256.size) (hfree : memLoad (UInt256.ofNat 64) mem = free) :
    poolManagerBlocks.poolManager_block_10297_taken_memory (mem := mem) (x4 := amount1)
      (x5 := amount0) (x8 := UInt256.ofNat 32) = donateEventMemory mem free amount0 amount1 := by
  simp only [poolManagerBlocks.poolManager_block_10297_taken_memory, hfree,
    uadd_word_ofNat_toNat free 32 hf, donateEventMemory, wordSequenceMemory, Reasoning.Theory.writeWord]

theorem PoolKeyView.donateEvent {mem : ByteArray} {ptr : UInt256} {key : PoolKeyWords}
    (h : PoolKeyView mem ptr key) (free amount0 amount1 : UInt256) (hb : ptr.toNat+160 ≤ free.toNat) :
    PoolKeyView (donateEventMemory mem free amount0 amount1) ptr key :=
  ⟨h.slice.wordSequence _ _ (by simpa only [wordBytes_size, poolKeyWordList, List.length_cons, List.length_nil] using hb), h.fits⟩

theorem donateEventMemory_size (mem : ByteArray) (free amount0 amount1 : UInt256) :
    (donateEventMemory mem free amount0 amount1).size = max mem.size (free.toNat+64) := by
  simp only [donateEventMemory, wordSequenceMemory, writeWord_sparse_size]
  omega

theorem donateEventMemory_free (mem : ByteArray) (free amount0 amount1 : UInt256)
    (hmem : 96 ≤ mem.size) (hlo : 96 ≤ free.toNat) :
    memLoad (UInt256.ofNat 64) (donateEventMemory mem free amount0 amount1) = memLoad (UInt256.ofNat 64) mem := by
  have h64 : (UInt256.ofNat 64).toNat = 64 := rfl
  rw [memLoad, memLoad, h64,
    if_neg (by rw [donateEventMemory_size]; omega), if_neg (by omega)]
  rw [donateEventMemory, wordSequenceMemory_read_below _ _ _ _ hmem hlo]

end Benchmarks.UniswapV4PoolManager
