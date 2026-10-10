import Benchmarks.UniswapV4PoolManager.SwapPoolSource
import Benchmarks.UniswapV4PoolManager.PoolSwapMemory
import Benchmarks.UniswapV4PoolManager.WordStructInitMemory
import Benchmarks.UniswapV4PoolManager.MemorySlice
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_007

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def swapPoolMemory (mem : ByteArray) (free : UInt256) (p : PoolSwapParamsWords) : ByteArray :=
  wordSequenceMemory (writeWord mem 64 (free+UInt256.ofNat 160)) free.toNat (poolSwapParamsWordList p)

theorem swapPoolMemory_compiled {mem : ByteArray} {free rawFee : UInt256} {p : PoolSwapParamsWords}
    (hf : free.toNat+160 < UInt256.size) (he : UInt256.land rawFee (UInt256.ofNat 16777215) = p.lpFeeOverride) :
    poolManagerBlocks.poolManager_block_1669_taken_memory (mem := writeWord mem 64 (free+UInt256.ofNat 160))
      (x0 := p.amountSpecified) (x1 := p.tickSpacing) (x2 := UInt256.fromBool p.zeroForOne)
      (x3 := p.priceLimit) (x4 := rawFee) (x9 := free) = swapPoolMemory mem free p := by
  have h32 := uadd_word_ofNat_toNat free 32 (by omega)
  have h64 := uadd_word_ofNat_toNat free 64 (by omega)
  have h96 := uadd_word_ofNat_toNat free 96 (by omega)
  have h128 := uadd_word_ofNat_toNat free 128 (by omega)
  have hc : UInt256.land (UInt256.ofNat 16777215) rawFee = p.lpFeeOverride :=
    (u256_land_comm _ _).trans he
  simp only [poolManagerBlocks.poolManager_block_1669_taken_memory, hc,
    swapPoolMemory, poolSwapParamsWordList, wordSequenceMemory, Reasoning.Theory.writeWord,
    h32, h64, h96, h128, Nat.add_assoc]

theorem swapPoolMemory_params (mem : ByteArray) (free : UInt256) (p : PoolSwapParamsWords)
    (hf : free.toNat+160 < UInt256.size) :
    WordStructView (swapPoolMemory mem free p) free (poolSwapParamsWordList p) :=
  wordStructView_sequence _ _ _ (by intro h; cases h) hf

theorem MemorySlice.swapPool {mem data : ByteArray} {base : Nat} (h : MemorySlice mem base data)
    (free : UInt256) (p : PoolSwapParamsWords) (hl : 96 ≤ base) (hb : base+data.size ≤ free.toNat) :
    MemorySlice (swapPoolMemory mem free p) base data :=
  (h.writeWord 64 (free+UInt256.ofNat 160) (.inr hl)).wordSequence _ _ hb

theorem swapPoolMemory_free (mem : ByteArray) (free : UInt256) (p : PoolSwapParamsWords)
    (hl : 96 ≤ free.toNat) : memLoad (UInt256.ofNat 64) (swapPoolMemory mem free p) = free+UInt256.ofNat 160 := by
  rw [swapPoolMemory, wordSequenceMemory_load_before _ _ _ _
    (by change 96 ≤ _; rw [writeWord_sparse_size]; omega) hl]
  exact writeWord_sparse_load_back mem (UInt256.ofNat 64) _

end Benchmarks.UniswapV4PoolManager
