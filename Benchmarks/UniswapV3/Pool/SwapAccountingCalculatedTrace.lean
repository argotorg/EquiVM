import Benchmarks.UniswapV3.Pool.SwapAccountingMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_014

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapAccountingCalculatedX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (exactInput : Bool) (s : SwapStateData) (d : SwapIterationData) (value : Int)
    (rd : RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3435⟩ else ⟨3498⟩)
      (EVM.wordOfInt value :: q :: p :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hp : 96 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat) (hb : p.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 5 ≤ 1024) :
    let m := writeWord mem (p.toNat + 32) (EVM.wordOfInt value)
    ∃ k' C', C + 1 + (Cₘ (M aw (p + UInt256.ofNat 32) ⟨32⟩) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3504⟩ (q :: p :: R)
        m (M aw (p + UInt256.ofNat 32) ⟨32⟩) rdata σ k' C' ∧
      HeapMemory m (M aw (p + UInt256.ofNat 32) ⟨32⟩) free ∧
      SwapStateMemory m p {s with calculated := value} ∧
      SwapIterationMemory m q d ∧ MemoryPrefix mem m p.toNat ∧
      aw.toNat ≤ (M aw (p + UInt256.ofNat 32) ⟨32⟩).toNat := by
  dsimp only
  have hp32 := uadd_word_ofNat_toNat p 32
    (show p.toNat + 32 < UInt256.size by change _ < 2 ^ 256; omega)
  have hbound : (p + UInt256.ofNat 32).toNat + 32 ≤ 2 ^ 200 := by rw [hp32]; omega
  obtain ⟨hm0, hs0, hd0, hpre⟩ := swapAccountingCalculatedMemory s d value hm hs hd hp hdisj
  have hm1 := hm0.expand32 (p + UInt256.ofNat 32) hbound
  cases exactInput
  · have rr := uniswapV3Pool_block_3498 (immWords := wordsOf (immStore v)) hov rd
    refine ⟨k + 5, C + (13 + memExpansionCost aw (p + UInt256.ofNat 32) ⟨32⟩),
      ?_, ?_, hm1, hs0, hd0, hpre, expandedWords_mono hm.active hbound⟩
    · dsimp only [memExpansionCost, M, expandedWords]; omega
    · simpa only [uniswapV3Pool_block_3498_stack, uniswapV3Pool_block_3498_memory,
        hp32, Reasoning.Theory.writeWord] using rr
  · have rr := uniswapV3Pool_block_3435 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨k + 7, C + (24 + memExpansionCost aw (p + UInt256.ofNat 32) ⟨32⟩),
      ?_, ?_, hm1, hs0, hd0, hpre, expandedWords_mono hm.active hbound⟩
    · dsimp only [memExpansionCost, M, expandedWords]; omega
    · simpa only [uniswapV3Pool_block_3435_stack, uniswapV3Pool_block_3435_memory,
        hp32, Reasoning.Theory.writeWord] using rr

end Benchmarks.UniswapV3.Pool
