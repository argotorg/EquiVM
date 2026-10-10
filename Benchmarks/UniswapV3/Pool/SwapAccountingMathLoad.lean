import Benchmarks.UniswapV3.Pool.SwapAccountingMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapAccountingMathLoadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free value ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (exactInput : Bool) (s : SwapStateData)
    (rd : RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3424⟩ else ⟨3487⟩)
      ([value, ret, q, p] ++ R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 6 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (UInt256.ofNat (if exactInput then 12967 else 12995))
        ([value, EVM.wordOfInt s.calculated, ret, q, p] ++ R) mem aw' rdata σ k' C' ∧
      HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  have hload := SwapStateMemory.load_calculated hs (by change _ < 2 ^ 256; omega)
  have hbound : (p + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 32 (by change _ < 2 ^ 256; omega)]
    omega
  have rr : RD (deployedRuntime v) ee g s0
      (UInt256.ofNat (if exactInput then 12967 else 12995))
      ([value, EVM.wordOfInt s.calculated, ret, q, p] ++ R)
      mem (M aw (p + UInt256.ofNat 32) ⟨32⟩) rdata σ (k + 8)
      (C + (27 + memExpansionCost aw (p + UInt256.ofNat 32) ⟨32⟩)) := by
    cases exactInput
    · have r1 := uniswapV3Pool_block_3487 (immWords := wordsOf (immStore v)) hov
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
      simpa only [uniswapV3Pool_block_3487_stack, hload] using r1
    · have r1 := uniswapV3Pool_block_3424 (immWords := wordsOf (immStore v)) hov
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
      simpa only [uniswapV3Pool_block_3424_stack, hload] using r1
  refine ⟨_, _, _, ?_, rr, hm.expand32 (p + UInt256.ofNat 32) hbound,
    expandedWords_mono hm.active hbound⟩
  dsimp only [memExpansionCost, M, expandedWords]
  omega

end Benchmarks.UniswapV3.Pool
