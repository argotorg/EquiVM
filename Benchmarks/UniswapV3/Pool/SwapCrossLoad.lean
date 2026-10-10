import Benchmarks.UniswapV3.Pool.SwapCrossGlobal1

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapCrossLoadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (c : SwapCacheData) (s : SwapStateData) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3775⟩
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hc : SwapCacheMemory mem cache c)
    (hs : SwapStateMemory mem p s) (hd : SwapIterationMemory mem q d)
    (hbc : cache.toNat + 192 ≤ 2 ^ 200) (hbp : p.toNat + 224 ≤ 2 ^ 200)
    (hbq : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 24 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨13596⟩
        (tickCrossWords (swapCrossArgs a.zeroForOne c s d σ ee) ++ [⟨3851⟩, ⟨0⟩, q] ++
          swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  obtain ⟨a1, k1, C1, hC1, r1, hm1, hmono1⟩ :=
    swapCrossGlobal0X (v := v) a s d rd hm hs hd hbp hbq (by omega)
  obtain ⟨a2, k2, C2, hC2, r2, hm2, hmono2⟩ :=
    swapCrossGlobal1X (v := v) a s (EVM.wordOfInt d.tickNext)
      (if a.zeroForOne then s.feeGrowth else feeGrowthWord false σ ee) r1 hm1 hs hbp (by omega)
  have hbound : cache.toNat + 32 * c.words.length < UInt256.size := by
    change cache.toNat + 192 < 2 ^ 256; omega
  have hsec : memLoad (cache + UInt256.ofNat 128) mem = c.secondsPerLiquidity :=
    WordArrayMemory.load hc 4 (by change 4 < 6; decide) hbound
  have hcum : memLoad (cache + UInt256.ofNat 96) mem = EVM.wordOfInt c.tickCumulative :=
    WordArrayMemory.load hc 3 (by change 3 < 6; decide) hbound
  have htime : memLoad (cache + UInt256.ofNat 64) mem = c.blockTimestamp :=
    WordArrayMemory.load hc 2 (by change 2 < 6; decide) hbound
  have hb128 : (cache + UInt256.ofNat 128).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat cache 128 (by change _ < 2 ^ 256; omega)]; omega
  have hb96 : (cache + UInt256.ofNat 96).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat cache 96 (by change _ < 2 ^ 256; omega)]; omega
  have hb64 : (cache + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat cache 64 (by change _ < 2 ^ 256; omega)]; omega
  have hm3 := hm2.expand32 (cache + UInt256.ofNat 128) hb128
  have hm4 := hm3.expand32 (cache + UInt256.ofNat 96) hb96
  have hm5 := hm4.expand32 (cache + UInt256.ofNat 64) hb64
  have hmono3 := expandedWords_mono (off := cache + UInt256.ofNat 128) (size := ⟨32⟩)
    hm2.active hb128
  have hmono4 := expandedWords_mono (off := cache + UInt256.ofNat 96) (size := ⟨32⟩)
    hm3.active hb96
  have hmono5 := expandedWords_mono (off := cache + UInt256.ofNat 64) (size := ⟨32⟩)
    hm4.active hb64
  have r3 := uniswapV3Pool_block_3823 (immWords := wordsOf (immStore v))
    (by change R.length + 10 + 14 ≤ 1024; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r2
  simp only [uniswapV3Pool_block_3823_stack, hsec, hcum, htime] at r3
  refine ⟨_, _, _, ?_, r3, hm5,
    hmono1.trans (hmono2.trans (hmono3.trans (hmono4.trans hmono5)))⟩
  dsimp only [memExpansionCost, M, expandedWords]; omega

end Benchmarks.UniswapV3.Pool
