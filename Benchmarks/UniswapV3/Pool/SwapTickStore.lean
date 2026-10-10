import Benchmarks.UniswapV3.Pool.SwapFeeGrowthStoreTrace
import Benchmarks.UniswapV3.Pool.TickLogBoundsModel
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_016

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapTickStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (crossed : Bool) (s : SwapStateData) (d : SwapIterationData) (tickRaw : UInt256) (tick : Int)
    (rd : RD (deployedRuntime v) ee g s0 (if crossed then ⟨3917⟩ else ⟨3980⟩)
      (tickRaw :: q :: p :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d)
    (ht : UInt256.signextend (UInt256.ofNat 2) tickRaw = EVM.wordOfInt tick)
    (hfit : -(2 ^ 23 : Int) ≤ tick ∧ tick < 2 ^ 23)
    (hp : 96 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 5 ≤ 1024) :
    let m := writeWord mem (p.toNat + 96) (EVM.wordOfInt tick)
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3993⟩ (q :: p :: R) m aw' rdata σ k' C' ∧
      HeapMemory m aw' free ∧ SwapStateMemory m p {s with tick := tick} ∧
      SwapIterationMemory m q d ∧ MemoryPrefix mem m p.toNat ∧ aw.toNat ≤ aw'.toNat := by
  dsimp only
  have hclean : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt tick) =
      EVM.wordOfInt tick := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ tick (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hfit.1 hfit.2]
  have hp96 := uadd_word_ofNat_toNat p 96
    (show p.toNat + 96 < UInt256.size by change _ < 2 ^ 256; omega)
  have hbound : (p + UInt256.ofNat 96).toNat + 32 ≤ 2 ^ 200 := by rw [hp96]; omega
  obtain ⟨hm0, hs0, hd0, hpre⟩ := wordArrayWriteBefore hm hs hd hp hdisj 3
    (by change 3 < 7; decide) (EVM.wordOfInt tick)
  have hm1 := hm0.expand32 (p + UInt256.ofNat 96) hbound
  have hmono := expandedWords_mono (off := p + UInt256.ofNat 96) (size := ⟨32⟩) hm.active hbound
  cases crossed
  · have rr := uniswapV3Pool_block_3980 (immWords := wordsOf (immStore v)) hov rd
    simp only [uniswapV3Pool_block_3980_stack, uniswapV3Pool_block_3980_memory,
      ht, hclean, hp96] at rr
    refine ⟨_, _, _, ?_, rr, hm1, hs0, hd0, hpre, hmono⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega
  · have rr := uniswapV3Pool_block_3917 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [uniswapV3Pool_block_3917_stack, uniswapV3Pool_block_3917_memory,
      ht, hclean, hp96] at rr
    refine ⟨_, _, _, ?_, rr, hm1, hs0, hd0, hpre, hmono⟩
    dsimp only [memExpansionCost, M, expandedWords]; omega

end Benchmarks.UniswapV3.Pool
