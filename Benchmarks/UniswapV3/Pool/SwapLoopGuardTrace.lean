import Benchmarks.UniswapV3.Pool.SwapMemoryModel
import Benchmarks.UniswapV3.Pool.SwapLoopGuardSource
import Benchmarks.UniswapV3.Pool.SwapEntryTrace
import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_013

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapLoopWords (a : SwapArgs)
    (p exactWord cache snap dataStart dataLength ret : UInt256) (R : List UInt256) : List UInt256 :=
  [p, exactWord, cache, snap, ⟨0⟩, ⟨0⟩] ++ swapWords a dataStart dataLength ++ ret :: R

theorem swapLoopPriceCompare (price limit : UInt256) :
    UInt256.isZero (UInt256.eq price limit) = (decide (price.toNat ≠ limit.toNat)).toUInt256 := by
  by_cases he : price = limit
  · have hn : price.toNat = limit.toNat := congrArg UInt256.toNat he
    rw [show decide (price.toNat ≠ limit.toNat) = false by simp only [hn, ne_self_iff_false,
      decide_false]]
    simp only [UInt256.eq, he, decide_true, UInt256.fromBool]
    rfl
  · have hn : price.toNat ≠ limit.toNat := fun h ↦ he (u256_inj h)
    rw [show decide (price.toNat ≠ limit.toNat) = true from decide_eq_true hn]
    simp only [UInt256.eq, he, decide_false, UInt256.fromBool]
    rfl

theorem swapLoopConditionX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2991⟩
      (swapLoopWords a p exactWord cache snap dataStart dataLength ret R) mem aw rdata σ k C)
    (ha : a.Fits) (hs : s.Fits) (hm : SwapStateMemory mem p s) (haw : ActiveWords aw)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 18 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 ⟨3029⟩
        ((swapContinues a s).toUInt256 ::
          swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        mem aw' rdata σ k' C' ∧ ActiveWords aw' := by
  have hfit : p.toNat + 224 < UInt256.size := by change _ < 2 ^ 256; omega
  have hr := SwapStateMemory.load_remaining hm hfit
  have hap := activeWords_expand32 haw (show p.toNat + 32 ≤ 2 ^ 200 by omega)
  by_cases hz : s.remaining = 0
  · have hword : EVM.wordOfInt s.remaining = UInt256.ofNat 0 := by rw [hz]; rfl
    have r1 := uniswapV3Pool_block_2991_taken (immWords := wordsOf (immStore v))
      (by change R.length + 12 + 4 ≤ 1024; omega) (by rw [hr, hword]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    refine ⟨_, k + 9, C + (32 + memExpansionCost aw p ⟨32⟩), ?_, ?_, hap⟩
    · dsimp only [memExpansionCost, expandedWords, M]; omega
    · simpa only [uniswapV3Pool_block_2991_taken_stack, hr, hword,
        swapContinues, hz, ne_self_iff_false, decide_false, Bool.false_and] using r1
  · have hword : EVM.wordOfInt s.remaining ≠ ⟨0⟩ := by
      intro hn
      exact hz ((wordOfInt_zero_iff_signed s.remaining hs.1.1 hs.1.2).mp hn)
    have hremaining : decide (s.remaining ≠ 0) = true := decide_eq_true hz
    have r1 := uniswapV3Pool_block_2991_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 12 + 4 ≤ 1024; omega)
      (by rw [hr]; exact isZero_eq_zero_of_ne hword) rd
    simp only [uniswapV3Pool_block_2991_fallthrough_stack, swapWords] at r1
    have r2 := uniswapV3Pool_block_3002 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 14 ≤ 1024; omega) r1
    have hp : memLoad (UInt256.ofNat 64 + p) mem = s.price := by
      rw [u256_add_comm]
      exact SwapStateMemory.load_price hm hfit
    have hpclean : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) s.price = s.price := by
      rw [u256_land_comm]
      exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) hs.2.2.1
    have hlclean : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) a.priceLimit = a.priceLimit := by
      rw [u256_land_comm]
      exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) ha.2
    have hp64 : (UInt256.ofNat 64 + p).toNat = p.toNat + 64 := by
      rw [u256_add_comm]
      exact uadd_word_ofNat_toNat p 64 (by omega)
    have ha' := activeWords_expand32 hap
      (show (UInt256.ofNat 64 + p).toNat + 32 ≤ 2 ^ 200 by rw [hp64]; omega)
    refine ⟨_, k + 9 + 20, C + (32 + memExpansionCost aw p ⟨32⟩) +
      (59 + memExpansionCost (M aw p ⟨32⟩) (UInt256.ofNat 64 + p) ⟨32⟩), ?_, ?_, ha'⟩
    · dsimp only [memExpansionCost, expandedWords, M]; omega
    · simpa only [uniswapV3Pool_block_3002_stack, amountDeltaMask160, hp, hpclean, hlclean,
        swapLoopPriceCompare, swapContinues, hremaining, Bool.true_and,
        swapLoopWords, swapWords, List.cons_append, List.nil_append] using r2

theorem swapLoopGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p exactWord cache snap dataStart dataLength ret : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapArgs) (s : SwapStateData)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2991⟩
      (swapLoopWords a p exactWord cache snap dataStart dataLength ret R) mem aw rdata σ k C)
    (ha : a.Fits) (hs : s.Fits) (hm : SwapStateMemory mem p s) (haw : ActiveWords aw)
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 18 ≤ 1024) :
    ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
      RD (deployedRuntime v) ee g s0 (if swapContinues a s then ⟨3035⟩ else ⟨3999⟩)
        (swapLoopWords a p exactWord cache snap dataStart dataLength ret R)
        mem aw' rdata σ k' C' ∧ ActiveWords aw' := by
  obtain ⟨aw', k', C', hc, rr, hap⟩ := swapLoopConditionX a s rd ha hs hm haw hb hov
  have ho : (swapLoopWords a p exactWord cache snap dataStart dataLength ret R).length + 2 ≤
      1024 := by change R.length + 13 + 2 ≤ 1024; omega
  cases he : swapContinues a s with
  | false =>
    have rout := uniswapV3Pool_block_3029_taken (immWords := wordsOf (immStore v))
      ho (by rw [he]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
    exact ⟨aw', k' + 4, C' + 17, by omega, by simpa only [he] using rout, hap⟩
  | true =>
    have rout := uniswapV3Pool_block_3029_fallthrough (immWords := wordsOf (immStore v))
      ho (by rw [he]; rfl) rr
    exact ⟨aw', k' + 4, C' + 17, by omega, by simpa only [he] using rout, hap⟩

end Benchmarks.UniswapV3.Pool
