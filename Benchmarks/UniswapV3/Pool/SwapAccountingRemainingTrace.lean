import Benchmarks.UniswapV3.Pool.SwapAccountingFirstLoad
import Benchmarks.UniswapV3.Pool.SwapAccountingMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapAccountingRemainingX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (exactInput : Bool) (s : SwapStateData) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3401⟩ else ⟨3458⟩)
      (swapAccountingFirst exactInput d :: q :: p :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hp : 96 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat) (hb : q.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 6 ≤ 1024) :
    let m := writeWord mem p.toNat (EVM.wordOfInt (swapAccountingRemaining exactInput s d))
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨12945⟩
        ([swapAccountingSecond exactInput d, (if exactInput then ⟨3424⟩ else ⟨3487⟩),
          (if exactInput then ⟨3435⟩ else ⟨3498⟩), q, p] ++ R) m aw' rdata σ k' C' ∧
      HeapMemory m aw' free ∧
      SwapStateMemory m p {s with remaining := swapAccountingRemaining exactInput s d} ∧
      SwapIterationMemory m q d ∧ MemoryPrefix mem m p.toNat ∧ aw.toNat ≤ aw'.toNat := by
  dsimp only
  have hpword : p.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hqword : q.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hrem := SwapStateMemory.load_remaining hs hpword
  have hp32 : p.toNat + 32 ≤ 2 ^ 200 := by omega
  have hbnd (n : Nat) (hn : n + 32 ≤ 224) :
      (q + UInt256.ofNat n).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat q n (by omega)]
    omega
  obtain ⟨hm0, hs0, hd0, hpre⟩ := swapAccountingRemainingMemory exactInput s d hm hs hd hp hdisj
  have hm1 := hm0.expand32 p hp32
  have hm2 := hm1.expand32 p hp32
  have hw := swapAccountingRemaining_word exactInput s d
  have hmono12 : aw.toNat ≤ (M (M aw p ⟨32⟩) p ⟨32⟩).toNat :=
    (expandedWords_mono (off := p) (size := ⟨32⟩) hm.active hp32).trans
      (expandedWords_mono hm1.active hp32)
  cases exactInput
  · simp only [Bool.false_eq_true, if_false] at hw
    have hin := SwapIterationMemory.load_amountIn hd0 hqword
    have hfee := SwapIterationMemory.load_fee hd0 hqword
    dsimp only [Reasoning.Theory.writeWord] at hin hfee
    have rr := uniswapV3Pool_block_3458 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [uniswapV3Pool_block_3458_stack, uniswapV3Pool_block_3458_memory,
      hrem, ← hw, hin, hfee] at rr
    have hm3 := hm2.expand32 (q + UInt256.ofNat 192) (hbnd 192 (by decide))
    have hm4 := hm3.expand32 (q + UInt256.ofNat 128) (hbnd 128 (by decide))
    refine ⟨_, _, _, ?_, rr, hm4, hs0, hd0, hpre, ?_⟩
    · dsimp only [memExpansionCost, M, expandedWords]; omega
    · exact hmono12.trans
        ((expandedWords_mono (off := q + UInt256.ofNat 192) (size := ⟨32⟩)
          hm2.active (hbnd 192 (by decide))).trans
          (expandedWords_mono hm3.active (hbnd 128 (by decide))))
  · simp only [if_true] at hw
    have hout := SwapIterationMemory.load_amountOut hd0 hqword
    dsimp only [Reasoning.Theory.writeWord] at hout
    have rr := uniswapV3Pool_block_3401 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [uniswapV3Pool_block_3401_stack, uniswapV3Pool_block_3401_memory,
      hrem, ← hw, hout] at rr
    have hm3 := hm2.expand32 (q + UInt256.ofNat 160) (hbnd 160 (by decide))
    refine ⟨_, _, _, ?_, rr, hm3, hs0, hd0, hpre, ?_⟩
    · dsimp only [memExpansionCost, M, expandedWords]; omega
    · exact hmono12.trans (expandedWords_mono hm2.active (hbnd 160 (by decide)))

end Benchmarks.UniswapV3.Pool
