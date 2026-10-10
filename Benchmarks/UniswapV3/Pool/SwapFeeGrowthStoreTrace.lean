import Benchmarks.UniswapV3.Pool.SwapFeeGrowthSource
import Benchmarks.UniswapV3.Pool.WordArrayPairUpdate
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem SwapStateMemory.load_feeGrowth {mem : ByteArray} {p : UInt256} {s : SwapStateData}
    (hm : SwapStateMemory mem p s) (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 128) mem = s.feeGrowth :=
  WordArrayMemory.load hm 4 (by change 4 < 7; decide) hb

theorem swapFeeGrowthStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (s : SwapStateData) (d : SwapIterationData) (value : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3625⟩ (value :: q :: p :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hp : 96 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat) (hb : p.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 5 ≤ 1024) :
    let m := writeWord mem (p.toNat + 128) (s.feeGrowth + value)
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3637⟩ (q :: p :: R) m aw' rdata σ k' C' ∧
      HeapMemory m aw' free ∧ SwapStateMemory m p {s with feeGrowth := s.feeGrowth + value} ∧
      SwapIterationMemory m q d ∧ MemoryPrefix mem m p.toNat ∧ aw.toNat ≤ aw'.toNat := by
  dsimp only
  have hp128 := uadd_word_ofNat_toNat p 128
    (show p.toNat + 128 < UInt256.size by change _ < 2 ^ 256; omega)
  have hbound : (p + UInt256.ofNat 128).toNat + 32 ≤ 2 ^ 200 := by rw [hp128]; omega
  have hload := SwapStateMemory.load_feeGrowth hs (by change _ < 2 ^ 256; omega)
  have hsum : value + s.feeGrowth = s.feeGrowth + value := u256_add_comm _ _
  have rr := uniswapV3Pool_block_3625 (immWords := wordsOf (immStore v)) hov rd
  simp only [uniswapV3Pool_block_3625_stack, uniswapV3Pool_block_3625_memory,
    hload, hsum, hp128] at rr
  obtain ⟨hm0, hs0, hd0, hpre⟩ := wordArrayWriteBefore hm hs hd hp hdisj 4
    (by change 4 < 7; decide) (s.feeGrowth + value)
  have hm1 := hm0.expand32 (p + UInt256.ofNat 128) hbound
  have hm2 := hm1.expand32 (p + UInt256.ofNat 128) hbound
  refine ⟨_, _, _, ?_, rr, hm2, hs0, hd0, hpre, ?_⟩
  · dsimp only [memExpansionCost, M, expandedWords]; omega
  · exact (expandedWords_mono (off := p + UInt256.ofNat 128) (size := ⟨32⟩) hm.active hbound).trans
      (expandedWords_mono hm1.active hbound)

end Benchmarks.UniswapV3.Pool
