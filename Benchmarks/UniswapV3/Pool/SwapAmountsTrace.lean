import Benchmarks.UniswapV3.Pool.SwapAmountsSource
import Benchmarks.UniswapV3.Pool.SwapAccountingMemory
import Benchmarks.UniswapV3.Pool.SwapWriteGuard
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapAmountsX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p free cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨4488⟩
      (swapLoopWords a p (swapExactInput a).toUInt256 cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 16 ≤ 1024) :
    ∃ aw' k' C', RD (deployedRuntime v) ee g s0 ⟨4526⟩
      ([EVM.wordOfInt (swapAmount1 a s), EVM.wordOfInt (swapAmount0 a s)] ++
        swapLoopWords a p (swapExactInput a).toUInt256 cache snap dataStart dataLength ret R)
      mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free := by
  have hr := SwapStateMemory.load_remaining hs (by change _ < 2 ^ 256; omega)
  have hc := SwapStateMemory.load_calculated hs (by change _ < 2 ^ 256; omega)
  have hzero : UInt256.ofNat 0 + p = p := u256_zero_add p
  have hr' : memLoad (UInt256.ofNat 0 + p) mem = EVM.wordOfInt s.remaining := by
    rw [hzero]; exact hr
  have hc' : memLoad (UInt256.ofNat 32 + p) mem = EVM.wordOfInt s.calculated := by
    rw [u256_add_comm]; exact hc
  have hb32 : (p + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)]; omega
  have heq : UInt256.eq
      (UInt256.isZero (UInt256.isZero a.zeroForOne.toUInt256))
      (UInt256.isZero (UInt256.isZero (swapExactInput a).toUInt256)) =
      (decide (a.zeroForOne = swapExactInput a)).toUInt256 := by
    cases a.zeroForOne <;> cases swapExactInput a <;> rfl
  by_cases he : a.zeroForOne = swapExactInput a
  · have r1 := uniswapV3Pool_block_4488_taken (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 13 ≤ 1024; omega)
      (by rw [heq, show decide (a.zeroForOne = swapExactInput a) = true from decide_eq_true he]
          decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    have r2 := uniswapV3Pool_block_4513 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 13 ≤ 1024; omega) r1
    have hm1 := hm.expand32 (UInt256.ofNat 0 + p) (by rw [hzero]; omega)
    have hm2 := hm1.expand32 (UInt256.ofNat 32 + p) (by rw [u256_add_comm]; exact hb32)
    refine ⟨_, k + 10 + 11, C + 35 +
      (31 + memExpansionCost aw (UInt256.ofNat 0 + p) ⟨32⟩ +
        memExpansionCost (M aw (UInt256.ofNat 0 + p) ⟨32⟩) (UInt256.ofNat 32 + p) ⟨32⟩),
      ?_, hm2⟩
    simpa only [uniswapV3Pool_block_4513_stack, hr', hc', swapAmount0, swapAmount1,
      he, if_true, swapAmountDifference_word, swapLoopWords, swapWords,
      List.cons_append, List.nil_append] using r2
  · have r1 := uniswapV3Pool_block_4488_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 13 ≤ 1024; omega)
      (by rw [heq, show decide (a.zeroForOne = swapExactInput a) = false from decide_eq_false he]
          rfl) rd
    have r2 := uniswapV3Pool_block_4500 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 13 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r1
    have hm1 := hm.expand32 (p + UInt256.ofNat 32) hb32
    have hm2 := hm1.expand32 p (by omega)
    refine ⟨_, k + 10 + 10, C + 35 +
      (35 + memExpansionCost aw (p + UInt256.ofNat 32) ⟨32⟩ +
        memExpansionCost (M aw (p + UInt256.ofNat 32) ⟨32⟩) p ⟨32⟩), ?_, hm2⟩
    simpa only [uniswapV3Pool_block_4500_stack, hr, hc, swapAmount0, swapAmount1,
      he, if_false, swapAmountDifference_word, swapLoopWords, swapWords,
      List.cons_append, List.nil_append] using r2

end Benchmarks.UniswapV3.Pool
