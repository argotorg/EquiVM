import Benchmarks.UniswapV3.Pool.SwapIterationResultMemory
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_014
import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapIterationResultAw (aw p q : UInt256) : UInt256 :=
  M (M (M (M aw (q + UInt256.ofNat 192) ⟨32⟩) (q + UInt256.ofNat 160) ⟨32⟩)
    (q + UInt256.ofNat 128) ⟨32⟩) (p + UInt256.ofNat 64) ⟨32⟩

theorem swapIterationResultStoreX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free priceRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (s : SwapStateData) (d : SwapIterationData) (price amountIn amountOut fee : UInt256)
    (exactInput : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3347⟩
      ([fee, amountOut, amountIn, priceRaw, q, p, exactInput.toUInt256] ++ R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d)
    (hprice : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) priceRaw = price)
    (hp : 96 ≤ p.toNat) (hdisj : p.toNat + 224 ≤ q.toNat)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 9 ≤ 1024) :
    ∃ k' C', C + 1 + (Cₘ (swapIterationResultAw aw p q) - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3383⟩ else ⟨3445⟩)
        ([q, p, exactInput.toUInt256] ++ R)
        (swapIterationResultMem mem p q price amountIn amountOut fee)
        (swapIterationResultAw aw p q) rdata σ k' C' ∧
      HeapMemory (swapIterationResultMem mem p q price amountIn amountOut fee)
        (swapIterationResultAw aw p q) free ∧
      SwapStateMemory (swapIterationResultMem mem p q price amountIn amountOut fee) p
        {s with price := price} ∧
      SwapIterationMemory (swapIterationResultMem mem p q price amountIn amountOut fee) q
        (swapIterationResultData d amountIn amountOut fee) ∧
      MemoryPrefix mem (swapIterationResultMem mem p q price amountIn amountOut fee) p.toNat ∧
      aw.toNat ≤ (swapIterationResultAw aw p q).toNat := by
  have hq192 := uadd_word_ofNat_toNat q 192
    (show q.toNat + 192 < UInt256.size by change _ < 2 ^ 256; omega)
  have hq160 := uadd_word_ofNat_toNat q 160
    (show q.toNat + 160 < UInt256.size by change _ < 2 ^ 256; omega)
  have hq128 := uadd_word_ofNat_toNat q 128
    (show q.toNat + 128 < UInt256.size by change _ < 2 ^ 256; omega)
  have hp64 := uadd_word_ofNat_toNat p 64
    (show p.toNat + 64 < UInt256.size by change _ < 2 ^ 256; omega)
  have rr : RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3383⟩ else ⟨3445⟩)
      ([q, p, exactInput.toUInt256] ++ R)
      (swapIterationResultMem mem p q price amountIn amountOut fee)
      (swapIterationResultAw aw p q) rdata σ (k + 27)
      (C + (86 + memExpansionCost aw (q + UInt256.ofNat 192) ⟨32⟩ +
        memExpansionCost (M aw (q + UInt256.ofNat 192) ⟨32⟩) (q + UInt256.ofNat 160) ⟨32⟩ +
        memExpansionCost (M (M aw (q + UInt256.ofNat 192) ⟨32⟩) (q + UInt256.ofNat 160) ⟨32⟩)
          (q + UInt256.ofNat 128) ⟨32⟩ +
        memExpansionCost
          (M (M (M aw (q + UInt256.ofNat 192) ⟨32⟩) (q + UInt256.ofNat 160) ⟨32⟩)
            (q + UInt256.ofNat 128) ⟨32⟩) (p + UInt256.ofNat 64) ⟨32⟩)) := by
    cases he : exactInput
    · have r1 := uniswapV3Pool_block_3347_taken (immWords := wordsOf (immStore v)) hov
        (by rw [he]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simpa only [uniswapV3Pool_block_3347_taken_stack,
        uniswapV3Pool_block_3347_taken_memory, amountDeltaMask160, hprice,
        swapIterationResultMem, swapIterationResultAw, Reasoning.Theory.writeWord,
        hq192, hq160, hq128, hp64, he, Bool.false_eq_true, if_false] using r1
    · have r1 := uniswapV3Pool_block_3347_fallthrough (immWords := wordsOf (immStore v)) hov
        (by rw [he]; rfl) rd
      simpa only [uniswapV3Pool_block_3347_fallthrough_stack,
        uniswapV3Pool_block_3347_fallthrough_memory, amountDeltaMask160, hprice,
        swapIterationResultMem, swapIterationResultAw, Reasoning.Theory.writeWord,
        hq192, hq160, hq128, hp64, he, if_true] using r1
  obtain ⟨hm0, hs0, hd0, hpre⟩ :=
    swapIterationResultMemory s d price amountIn amountOut fee hm hs hd hp hdisj
  have h192 : (q + UInt256.ofNat 192).toNat + 32 ≤ 2 ^ 200 := by rw [hq192]; omega
  have h160 : (q + UInt256.ofNat 160).toNat + 32 ≤ 2 ^ 200 := by rw [hq160]; omega
  have h128 : (q + UInt256.ofNat 128).toNat + 32 ≤ 2 ^ 200 := by rw [hq128]; omega
  have h64 : (p + UInt256.ofNat 64).toNat + 32 ≤ 2 ^ 200 := by rw [hp64]; omega
  have hm1 := hm0.expand32 (q + UInt256.ofNat 192) h192
  have hm2 := hm1.expand32 (q + UInt256.ofNat 160) h160
  have hm3 := hm2.expand32 (q + UInt256.ofNat 128) h128
  have hm4 := hm3.expand32 (p + UInt256.ofNat 64) h64
  refine ⟨_, _, ?_, rr, hm4, hs0, hd0, hpre, ?_⟩
  · dsimp only [memExpansionCost, swapIterationResultAw, M, expandedWords]
    omega
  · exact (expandedWords_mono (off := q + UInt256.ofNat 192) (size := ⟨32⟩) hm.active h192).trans
      ((expandedWords_mono (off := q + UInt256.ofNat 160) (size := ⟨32⟩) hm1.active h160).trans
        ((expandedWords_mono (off := q + UInt256.ofNat 128) (size := ⟨32⟩) hm2.active h128).trans
          (expandedWords_mono (off := p + UInt256.ofNat 64) (size := ⟨32⟩) hm3.active h64)))

end Benchmarks.UniswapV3.Pool
