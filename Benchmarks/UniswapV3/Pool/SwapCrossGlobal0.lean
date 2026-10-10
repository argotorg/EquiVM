import Benchmarks.UniswapV3.Pool.SwapCrossCallSource
import Benchmarks.UniswapV3.Pool.SwapFeeGrowthStoreTrace
import Benchmarks.UniswapV3.Pool.SwapCrossTick

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapCrossGlobal0X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3775⟩
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d)
    (hbp : p.toNat + 224 ≤ 2 ^ 200) (hbq : q.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 20 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3804⟩
        ([(if a.zeroForOne then s.feeGrowth else feeGrowthWord false σ ee),
          EVM.wordOfInt d.tickNext, ⟨3851⟩, ⟨0⟩, q] ++
          swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  have ht : memLoad (UInt256.ofNat 32 + q) mem = EVM.wordOfInt d.tickNext := by
    rw [u256_add_comm]
    exact SwapIterationMemory.load_tick hd (by change _ < 2 ^ 256; omega)
  have hq : (UInt256.ofNat 32 + q).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat q 32 (by change _ < 2 ^ 256; omega)]; omega
  have hm1 := hm.expand32 (UInt256.ofNat 32 + q) hq
  have hmono1 := expandedWords_mono (off := UInt256.ofNat 32 + q) (size := ⟨32⟩) hm.active hq
  cases hz : a.zeroForOne
  · have r1 := uniswapV3Pool_block_3775_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 17 ≤ 1024; omega) (by rw [hz]; rfl) rd
    simp only [uniswapV3Pool_block_3775_fallthrough_stack, ht] at r1
    obtain ⟨k2, C2, hC2, r2⟩ := rdRoutine_return_mono r1 (fun _ _ rr ↦
      uniswapV3Pool_block_3791 (immWords := wordsOf (immStore v))
        (by change R.length + 17 + 2 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rr)
    change RD (deployedRuntime v) ee g s0 ⟨3804⟩
      ([feeGrowthWord false σ ee, EVM.wordOfInt d.tickNext, ⟨3851⟩, ⟨0⟩, q] ++
        swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem _ rdata σ k2 C2 at r2
    simp only [Bool.false_eq_true, if_false]
    refine ⟨_, k2, C2, ?_, r2, hm1, hmono1⟩
    dsimp only [memExpansionCost, M, expandedWords] at hC2 ⊢
    omega
  · have r1 := uniswapV3Pool_block_3775_taken (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 17 ≤ 1024; omega) (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [uniswapV3Pool_block_3775_taken_stack, ht] at r1
    have hfee : memLoad (UInt256.ofNat 128 + p) mem = s.feeGrowth := by
      rw [u256_add_comm]
      exact SwapStateMemory.load_feeGrowth hs (by change _ < 2 ^ 256; omega)
    have r2 := uniswapV3Pool_block_3798 (immWords := wordsOf (immStore v))
      (by change R.length + 12 + 7 ≤ 1024; omega) r1
    simp only [uniswapV3Pool_block_3798_stack, hfee] at r2
    have hp : (UInt256.ofNat 128 + p).toNat + 32 ≤ 2 ^ 200 := by
      rw [u256_add_comm, uadd_word_ofNat_toNat p 128 (by change _ < 2 ^ 256; omega)]; omega
    have hm2 := hm1.expand32 (UInt256.ofNat 128 + p) hp
    have hmono2 := expandedWords_mono (off := UInt256.ofNat 128 + p) (size := ⟨32⟩) hm1.active hp
    simp only [if_true]
    refine ⟨_, _, _, ?_, r2, hm2, hmono1.trans hmono2⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega

end Benchmarks.UniswapV3.Pool
