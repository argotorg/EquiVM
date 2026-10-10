import Benchmarks.UniswapV4PoolManager.PoolSwapReturnMemory
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_007

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def swapWrapperEventWords (delta fee : UInt256) (r : PoolSwapResultWords) : List UInt256 :=
  [UInt256.signextend (UInt256.ofNat 15) (UInt256.sar (UInt256.ofNat 128) delta),
   UInt256.signextend (UInt256.ofNat 15) delta, r.price, r.liquidity, r.tick, fee]

def swapWrapperEventMemory (mem : ByteArray) (free delta fee : UInt256) (r : PoolSwapResultWords) : ByteArray :=
  wordSequenceMemory mem free.toNat (swapWrapperEventWords delta fee r)

theorem swapWrapperEventMemory_compiled {mem : ByteArray} {free state delta fee : UInt256}
    {r : PoolSwapResultWords} (hr : WordStructView mem state (poolSwapResultWordList r))
    (hp : r.price.toNat < 2^160) (hl : r.liquidity.toNat < 2^128)
    (ht : int24Canonical r.tick) (he : fee.toNat < 2^24) (hf : free.toNat+192 < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = free) :
    poolManagerBlocks.poolManager_block_1766_memory (mem := mem) (x2 := fee) (x3 := UInt256.ofNat 16777215)
      (x5 := state) (x7 := delta) (x15 := UInt256.ofNat 32) = swapWrapperEventMemory mem free delta fee r := by
  have hpread : memLoad state mem = r.price := hr.load_zero (by decide : 0 < 3)
  have htread : memLoad (state+UInt256.ofNat 32) mem = r.tick := hr.load 1 (by decide : 1 < 3)
  have hlread : memLoad (state+UInt256.ofNat 64) mem = r.liquidity := hr.load 2 (by decide : 2 < 3)
  have hpc : UInt256.land r.price (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = r.price :=
    solcAddrMask_clean hp
  have hlc : UInt256.land r.liquidity (UInt256.ofNat 340282366920938463463374607431768211455) = r.liquidity :=
    u256LandMaskCleanOfToNat _ _ rfl hl
  have htc : UInt256.signextend (UInt256.ofNat 2) r.tick = r.tick := (signextend24_eq_iff _).mpr ht
  have hec : UInt256.land fee (UInt256.ofNat 16777215) = fee := u256LandMaskCleanOfToNat _ _ rfl he
  have h32 := uadd_word_ofNat_toNat free 32 (by omega)
  have h64 := uadd_word_ofNat_toNat free 64 (by omega)
  have h96 := uadd_word_ofNat_toNat free 96 (by omega)
  have h128 := uadd_word_ofNat_toNat free 128 (by omega)
  have h160 := uadd_word_ofNat_toNat free 160 (by omega)
  simp only [poolManagerBlocks.poolManager_block_1766_memory, hpread, htread, hlread, hpc, hlc, htc, hec,
    hfree, swapWrapperEventMemory, swapWrapperEventWords, wordSequenceMemory, Reasoning.Theory.writeWord,
    h32, h64, h96, h128, h160, Nat.add_assoc]

theorem swapWrapperEventMemory_size (mem : ByteArray) (free delta fee : UInt256) (r : PoolSwapResultWords) :
    (swapWrapperEventMemory mem free delta fee r).size = max mem.size (free.toNat+192) :=
  wordSequenceMemory_size_nonempty _ _ _ (by intro h; cases h)

theorem swapWrapperEventMemory_free (mem : ByteArray) (free delta fee : UInt256) (r : PoolSwapResultWords)
    (hi : 96 ≤ mem.size) (hl : 96 ≤ free.toNat) :
    memLoad (UInt256.ofNat 64) (swapWrapperEventMemory mem free delta fee r) =
      memLoad (UInt256.ofNat 64) mem := wordSequenceMemory_load_before _ _ _ _ hi hl

theorem MemorySlice.swapWrapperEvent {mem data : ByteArray} {base : Nat} (h : MemorySlice mem base data)
    (free delta fee : UInt256) (r : PoolSwapResultWords) (hb : base+data.size ≤ free.toNat) :
    MemorySlice (swapWrapperEventMemory mem free delta fee r) base data := h.wordSequence _ _ hb

end Benchmarks.UniswapV4PoolManager
