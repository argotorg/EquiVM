import Benchmarks.UniswapV3.Pool.SwapIterationTargetCompare

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapIterationTargetSelectX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free current callRet exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3286⟩
      ((swapIterationChooseLimit a d).toUInt256 ::
        swapIterationCompareWords a current callRet q p exactWord cache snap
        dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hd : SwapIterationMemory mem q d)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 18 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3302⟩
        (swapIterationTarget a d ::
          swapIterationCompareWords a current callRet q p exactWord cache snap
            dataStart dataLength ret R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  have ho : (swapIterationCompareWords a current callRet q p exactWord cache snap
      dataStart dataLength ret R).length + 2 ≤ 1024 := by
    change R.length + 16 + 2 ≤ 1024
    omega
  cases he : swapIterationChooseLimit a d
  · have r1 := uniswapV3Pool_block_3286_fallthrough (immWords := wordsOf (immStore v)) ho
      (by rw [he]; rfl) rd
    have r2 := uniswapV3Pool_block_3291 (immWords := wordsOf (immStore v))
      (by change R.length + 13 + 5 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have hload : memLoad (UInt256.ofNat 96 + q) mem = d.priceNext := by
      rw [u256_add_comm]
      exact SwapIterationMemory.load_priceNext hd (by change _ < 2 ^ 256; omega)
    have hbound : (UInt256.ofNat 96 + q).toNat + 32 ≤ 2 ^ 200 := by
      rw [u256_add_comm, uadd_word_ofNat_toNat q 96 (by change _ < 2 ^ 256; omega)]
      omega
    refine ⟨_, k + 3 + 6, C + 14 + (23 + memExpansionCost aw (UInt256.ofNat 96 + q) ⟨32⟩),
      ?_, ?_, hm.expand32 (UInt256.ofNat 96 + q) hbound, expandedWords_mono hm.active hbound⟩
    · dsimp only [memExpansionCost, M, expandedWords]; omega
    · simpa only [uniswapV3Pool_block_3291_stack, hload, swapIterationTarget, he,
        Bool.false_eq_true, if_false] using r2
  · have r1 := uniswapV3Pool_block_3286_taken (immWords := wordsOf (immStore v)) ho
      (by rw [he]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_3300 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 13 ≤ 1024; omega) r1
    refine ⟨aw, k + 3 + 2, C + 14 + 4, ?_, ?_, hm, Nat.le_refl _⟩
    · omega
    · simpa only [uniswapV3Pool_block_3300_stack, swapIterationTarget, he, if_true,
        swapIterationCompareWords, swapLoopWords, swapWords, List.cons_append, List.nil_append]
        using r2

theorem swapIterationTargetX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free current callRet exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 (if a.zeroForOne then ⟨3260⟩ else ⟨3231⟩)
      (swapIterationCompareWords a current callRet q p exactWord cache snap
        dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hd : SwapIterationMemory mem q d)
    (ha : a.Fits) (hf : d.priceNext.toNat < 2 ^ 160)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 21 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3302⟩
        (swapIterationTarget a d ::
          swapIterationCompareWords a current callRet q p exactWord cache snap
            dataStart dataLength ret R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  obtain ⟨a1, k1, C1, hC1, r1, hm1, hmono1⟩ :=
    swapIterationTargetCompareX a d rd hm hd ha hf hb hov
  obtain ⟨a2, k2, C2, hC2, r2, hm2, hmono2⟩ :=
    swapIterationTargetSelectX a d r1 hm1 hd hb (by omega)
  exact ⟨a2, k2, C2, by omega, r2, hm2, hmono1.trans hmono2⟩

end Benchmarks.UniswapV3.Pool
