import Benchmarks.UniswapV3.Pool.SwapCrossTickSource
import Benchmarks.UniswapV3.Pool.SwapTickStore
import Benchmarks.UniswapV3.Pool.SwapIterationStartTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapCrossTickLoadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3893⟩
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hd : SwapIterationMemory mem q d)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 18 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3917⟩
        ((if a.zeroForOne then UInt256.sub (EVM.wordOfInt d.tickNext) (UInt256.ofNat 1)
            else EVM.wordOfInt d.tickNext) :: q ::
          swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  have hload : memLoad (UInt256.ofNat 32 + q) mem = EVM.wordOfInt d.tickNext := by
    rw [u256_add_comm]
    exact SwapIterationMemory.load_tick hd (by change _ < 2 ^ 256; omega)
  have hbq : (UInt256.ofNat 32 + q).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat q 32 (by change _ < 2 ^ 256; omega)]
    omega
  have hm1 := hm.expand32 (UInt256.ofNat 32 + q) hbq
  have hmono := expandedWords_mono (off := UInt256.ofNat 32 + q) (size := ⟨32⟩) hm.active hbq
  cases hz : a.zeroForOne
  · have r1 := uniswapV3Pool_block_3893_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 14 ≤ 1024; omega) (by rw [hz]; rfl) rd
    have r2 := uniswapV3Pool_block_3899 (immWords := wordsOf (immStore v))
      (by change R.length + 13 + 3 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r1
    simp only [uniswapV3Pool_block_3899_stack, hload] at r2
    simp only [Bool.false_eq_true, if_false]
    refine ⟨_, _, _, ?_, r2, hm1, hmono⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega
  · have r1 := uniswapV3Pool_block_3893_taken (immWords := wordsOf (immStore v))
      (by change R.length + 2 + 14 ≤ 1024; omega) (by rw [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    have r2 := uniswapV3Pool_block_3908 (immWords := wordsOf (immStore v))
      (by change R.length + 13 + 4 ≤ 1024; omega) r1
    simp only [uniswapV3Pool_block_3908_stack, hload] at r2
    simp only [if_true]
    refine ⟨_, _, _, ?_, r2, hm1, hmono⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega

theorem swapCrossTickX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3893⟩
      (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d)
    (ht : -(2 ^ 23 : Int) ≤ d.tickNext ∧ d.tickNext < 2 ^ 23)
    (hp : 96 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 18 ≤ 1024) :
    ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3993⟩
        (q :: swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        mem' aw' rdata σ k' C' ∧ HeapMemory mem' aw' free ∧
      SwapStateMemory mem' p (swapCrossTickState a.zeroForOne s d) ∧
      SwapIterationMemory mem' q d ∧ MemoryPrefix mem mem' p.toNat ∧ aw.toNat ≤ aw'.toNat := by
  obtain ⟨a1, k1, C1, hC1, r1, hm1, hmono1⟩ := swapCrossTickLoadX (v := v) a d rd hm hd hb hov
  obtain ⟨a2, k2, C2, hC2, r2, hm2, hs2, hd2, hp2, hmono2⟩ :=
    swapTickStoreX (v := v) true s d _ (swapCrossTick a.zeroForOne d) r1 hm1 hs hd
      (swapCrossTick_word a.zeroForOne d ht) (swapCrossTick_bounds a.zeroForOne d ht)
      hp hdisj (by omega) (by change R.length + 12 + 5 ≤ 1024; omega)
  exact ⟨_, a2, k2, C2, by omega, r2, hm2, hs2, hd2, hp2, hmono1.trans hmono2⟩

end Benchmarks.UniswapV3.Pool
