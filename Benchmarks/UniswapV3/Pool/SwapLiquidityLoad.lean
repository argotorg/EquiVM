import Benchmarks.UniswapV3.Pool.SwapLiquiditySource
import Benchmarks.UniswapV3.Pool.SwapCrossLoad

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapLiquidityLoadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (net : Int)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3851⟩
      ([EVM.wordOfInt net, ⟨0⟩, q] ++
        swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 19 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨13807⟩
        ([swapLiquidityRaw a.zeroForOne net, s.liquidity, ⟨3877⟩,
          swapLiquidityRaw a.zeroForOne net, q] ++
          swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  have hload : memLoad (UInt256.ofNat 192 + p) mem = s.liquidity := by
    rw [u256_add_comm]
    exact WordArrayMemory.load hs 6 (by change 6 < 7; decide)
      (by change p.toNat + 224 < 2 ^ 256; omega)
  have hp : (UInt256.ofNat 192 + p).toNat + 32 ≤ 2 ^ 200 := by
    rw [u256_add_comm, uadd_word_ofNat_toNat p 192 (by change _ < 2 ^ 256; omega)]
    omega
  have hm1 := hm.expand32 (UInt256.ofNat 192 + p) hp
  have hmono := expandedWords_mono (off := UInt256.ofNat 192 + p) (size := ⟨32⟩)
    hm.active hp
  have r1 : ∃ k1 C1, C + 1 ≤ C1 ∧ RD (deployedRuntime v) ee g s0 ⟨3863⟩
      (swapLiquidityRaw a.zeroForOne net :: q ::
        swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
      mem aw rdata σ k1 C1 := by
    cases hz : a.zeroForOne
    · have rr := uniswapV3Pool_block_3851_taken (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 15 ≤ 1024; omega) (by rw [hz]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
      exact ⟨_, _, by omega, rr⟩
    · have rr := uniswapV3Pool_block_3851_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 15 ≤ 1024; omega) (by rw [hz]; rfl) rd
      have rr' := uniswapV3Pool_block_3860 (immWords := wordsOf (immStore v))
        (by change R.length + 14 + 2 ≤ 1024; omega) rr
      exact ⟨_, _, by omega, rr'⟩
  obtain ⟨k1, C1, hC1, r1⟩ := r1
  have r2 := uniswapV3Pool_block_3863 (immWords := wordsOf (immStore v))
    (by change R.length + 12 + 7 ≤ 1024; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) r1
  simp only [uniswapV3Pool_block_3863_stack, hload] at r2
  refine ⟨_, _, _, ?_, r2, hm1, hmono⟩
  dsimp only [memExpansionCost, M, expandedWords]; omega

end Benchmarks.UniswapV3.Pool
