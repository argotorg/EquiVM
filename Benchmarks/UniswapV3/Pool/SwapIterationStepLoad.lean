import Benchmarks.UniswapV3.Pool.SwapIterationTargetSelect
import Benchmarks.UniswapV3.Pool.SwapStepPrefixTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem SwapStateMemory.load_liquidity {mem : ByteArray} {p : UInt256} {s : SwapStateData}
    (hm : SwapStateMemory mem p s) (hb : p.toNat + 224 < UInt256.size) :
    memLoad (p + UInt256.ofNat 192) mem = s.liquidity := by
  have h := WordArrayMemory.load hm 6 (by change 6 < 7; decide) hb
  simpa only [SwapStateData.words, List.getElem_cons_succ, List.getElem_cons_zero,
    Nat.reduceMul] using h

theorem swapIterationStepLoadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p q free callRet exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData) (d : SwapIterationData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨3302⟩
      (swapIterationTarget a d :: swapIterationCompareWords a s.price callRet q p exactWord
        cache snap dataStart dataLength ret R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 21 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨12447⟩
        (swapStepRawWords (swapIterationStepArgs v a s d) s.price (swapIterationTarget a d)
          s.liquidity (wordsOf (immStore v) "fee") ++ callRet :: q ::
          swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat := by
  have hb192 : (p + UInt256.ofNat 192).toNat + 32 ≤ 2 ^ 200 := by
    rw [uadd_word_ofNat_toNat p 192 (by change _ < 2 ^ 256; omega)]
    omega
  have hb0 : p.toNat + 32 ≤ 2 ^ 200 := by omega
  have hl := SwapStateMemory.load_liquidity hs (by change _ < 2 ^ 256; omega)
  have hr := SwapStateMemory.load_remaining hs (by change _ < 2 ^ 256; omega)
  have hm1 := hm.expand32 (p + UInt256.ofNat 192) hb192
  have hm2 := hm1.expand32 p hb0
  have hmno1 := expandedWords_mono (off := p + UInt256.ofNat 192) (size := ⟨32⟩) hm.active hb192
  have hmno2 := expandedWords_mono (off := p) (size := ⟨32⟩) hm1.active hb0
  have rr := uniswapV3Pool_block_3302 (immWords := wordsOf (immStore v))
    (by change R.length + 12 + 9 ≤ 1024; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
  simp only [uniswapV3Pool_block_3302_stack, hl, hr] at rr
  refine ⟨_, k + 10, C + (33 + memExpansionCost aw (p + UInt256.ofNat 192) ⟨32⟩ +
    memExpansionCost (M aw (p + UInt256.ofNat 192) ⟨32⟩) p ⟨32⟩),
    ?_, ?_, hm2, hmno1.trans hmno2⟩
  · dsimp only [memExpansionCost, M, expandedWords]
    omega
  · simpa only [swapStepRawWords, swapIterationStepArgs, swapIterationCompareWords,
      swapLoopWords, swapWords, List.cons_append, List.nil_append] using rr

end Benchmarks.UniswapV3.Pool
