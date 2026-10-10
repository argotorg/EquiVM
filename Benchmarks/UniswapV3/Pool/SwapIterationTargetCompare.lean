import Benchmarks.UniswapV3.Pool.SwapIterationPriceStore
import Benchmarks.UniswapV3.Pool.SwapIterationTargetSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationCompareWords (a : SwapArgs)
    (current callRet q p exactWord cache snap dataStart dataLength ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [current, callRet, q] ++ swapLoopWords a p exactWord cache snap dataStart dataLength ret R

theorem swapIterationTargetCompareX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
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
      RD (deployedRuntime v) ee g s0 ⟨3286⟩
        ((swapIterationChooseLimit a d).toUInt256 ::
          swapIterationCompareWords a current callRet q p exactWord cache snap
            dataStart dataLength ret R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  have hq96 := uadd_word_ofNat_toNat q 96
    (show q.toNat + 96 < UInt256.size by change _ < 2 ^ 256; omega)
  have hbound : (UInt256.ofNat 96 + q).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, hq96]; omega
  have hload : memLoad (UInt256.ofNat 96 + q) mem = d.priceNext := by
    rw [u256_add_comm]
    exact SwapIterationMemory.load_priceNext hd (by change _ < 2 ^ 256; omega)
  have hclean : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) d.priceNext = d.priceNext := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hf
  have hlimit : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) a.priceLimit = a.priceLimit := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) ha.2
  cases hz : a.zeroForOne
  · simp only [hz, Bool.false_eq_true, if_false] at rd
    have hcmp : UInt256.gt d.priceNext a.priceLimit = (swapIterationChooseLimit a d).toUInt256 := by
      simp only [swapIterationChooseLimit, hz, Bool.false_eq_true, if_false]
      rfl
    have rr := uniswapV3Pool_block_3231 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 17 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨_, k + 20, C + (65 + memExpansionCost aw (UInt256.ofNat 96 + q) ⟨32⟩), ?_, ?_,
      hm.expand32 (UInt256.ofNat 96 + q) hbound, expandedWords_mono hm.active hbound⟩
    · dsimp only [memExpansionCost, M, expandedWords]; omega
    · simpa only [uniswapV3Pool_block_3231_stack, amountDeltaMask160, hload, hclean, hlimit,
        hcmp, swapIterationCompareWords, swapLoopWords, swapWords,
        List.cons_append, List.nil_append] using rr
  · simp only [hz, if_true] at rd
    have hcmp : UInt256.lt d.priceNext a.priceLimit = (swapIterationChooseLimit a d).toUInt256 := by
      simp only [swapIterationChooseLimit, hz, if_true]
      rfl
    have rr := uniswapV3Pool_block_3260 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 17 ≤ 1024; omega) rd
    refine ⟨_, k + 19, C + (55 + memExpansionCost aw (UInt256.ofNat 96 + q) ⟨32⟩), ?_, ?_,
      hm.expand32 (UInt256.ofNat 96 + q) hbound, expandedWords_mono hm.active hbound⟩
    · dsimp only [memExpansionCost, M, expandedWords]; omega
    · simpa only [uniswapV3Pool_block_3260_stack, amountDeltaMask160, hload, hclean, hlimit,
        hcmp, swapIterationCompareWords, swapLoopWords, swapWords,
        List.cons_append, List.nil_append] using rr

end Benchmarks.UniswapV3.Pool
