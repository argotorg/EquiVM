import Benchmarks.UniswapV3.Pool.SwapLiquiditySource
import Benchmarks.UniswapV3.Pool.SwapFeeGrowthStoreTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapLiquidityStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (s : SwapStateData) (d : SwapIterationData) (value rawValue rawNet : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3877⟩
      (rawValue :: rawNet :: q :: p :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d)
    (hvalue : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) rawValue = value)
    (hp : 96 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 7 ≤ 1024) :
    let m := writeWord mem (p.toNat + 192) value
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3893⟩ (q :: p :: R) m aw' rdata σ k' C' ∧
      HeapMemory m aw' free ∧ SwapStateMemory m p {s with liquidity := value} ∧
      SwapIterationMemory m q d ∧ MemoryPrefix mem m p.toNat ∧ aw.toNat ≤ aw'.toNat := by
  dsimp only
  have hp192 := uadd_word_ofNat_toNat p 192
    (show p.toNat + 192 < UInt256.size by change _ < 2 ^ 256; omega)
  have hbound : (p + UInt256.ofNat 192).toNat + 32 ≤ 2 ^ 200 := by rw [hp192]; omega
  have rr := uniswapV3Pool_block_3877 (immWords := wordsOf (immStore v)) hov rd
  simp only [uniswapV3Pool_block_3877_stack, uniswapV3Pool_block_3877_memory,
    solcMask128, hvalue, hp192] at rr
  obtain ⟨hm0, hs0, hd0, hpre⟩ := wordArrayWriteBefore hm hs hd hp hdisj 6
    (by change 6 < 7; decide) value
  have hm1 := hm0.expand32 (p + UInt256.ofNat 192) hbound
  refine ⟨_, _, _, ?_, rr, hm1, hs0, hd0, hpre, ?_⟩
  · dsimp only [memExpansionCost, M, expandedWords]; omega
  · exact expandedWords_mono (off := p + UInt256.ofNat 192) (size := ⟨32⟩) hm.active hbound

end Benchmarks.UniswapV3.Pool
