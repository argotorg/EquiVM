import Benchmarks.UniswapV3.Pool.SwapGuardsSource
import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_011
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_012

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapLimitCondX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p price x1 x2 x3 x4 x6 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2543⟩
      (p :: x1 :: x2 :: x3 :: x4 :: a.priceLimit :: x6 :: a.zeroForOne.toUInt256 :: R)
      mem aw rdata σ k C)
    (hl : a.priceLimit.toNat < 2 ^ 160)
    (hp : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) (memLoad p mem) = price)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨2668⟩
      ((decide (swapLimitForPrice a price)).toUInt256 ::
        p :: x1 :: x2 :: x3 :: x4 :: a.priceLimit :: x6 :: a.zeroForOne.toUInt256 :: R)
      mem (M aw p ⟨32⟩) rdata σ k' C' := by
  have hzero : UInt256.ofNat 0 + p = p := u256_zero_add p
  have hmask : UInt256.land a.priceLimit (UInt256.ofNat (2 ^ 160 - 1)) = a.priceLimit :=
    u256LandMaskCleanOfToNat _ _ (by decide) hl
  have hmask' := (u256_land_comm (UInt256.ofNat (2 ^ 160 - 1)) a.priceLimit).trans hmask
  cases hz : a.zeroForOne
  · have r1 := uniswapV3Pool_block_2543_fallthrough (immWords := wordsOf (immStore v))
      (by omega) (by simp only [hz]; rfl) rd
    by_cases hc : price.toNat < a.priceLimit.toNat
    · have hg : UInt256.gt a.priceLimit price = ⟨1⟩ := ugt_one hc
      have r2 := uniswapV3Pool_block_2549_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 11 ≤ 1024; omega)
        (by rw [amountDeltaMask160, hmask', hzero, hp, hg]; rfl) r1
      simp only [uniswapV3Pool_block_2549_fallthrough_stack] at r2
      have r3 := uniswapV3Pool_block_2580 (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 10 ≤ 1024; omega) r2
      have r4 := uniswapV3Pool_block_2613 (immWords := wordsOf (immStore v))
        (by change R.length + 9 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r3
      have hg' : UInt256.lt a.priceLimit
          (UInt256.ofNat 1461446703485210103287273052203988822378723970342) =
          (decide (swapLimitForPrice a price)).toUInt256 := by
        simp only [swapLimitForPrice, hz, Bool.false_eq_true, if_false, hc, true_and]
        rfl
      simpa only [uniswapV3Pool_block_2580_stack, amountDeltaMask160, hmask, hg',
        hzero, hz] using RD.pack r4
    · have hg : UInt256.gt a.priceLimit price = ⟨0⟩ := ugt_zero (by omega)
      have r2 := uniswapV3Pool_block_2549_taken (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 11 ≤ 1024; omega)
        (by rw [amountDeltaMask160, hmask', hzero, hp, hg]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := uniswapV3Pool_block_2613 (immWords := wordsOf (immStore v))
        (by change R.length + 9 + 1 ≤ 1024; omega)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
      simpa only [uniswapV3Pool_block_2549_taken_stack, amountDeltaMask160, hmask',
        hzero, hp, hg, swapLimitForPrice, hz, Bool.false_eq_true, if_false,
        hc, false_and, decide_false] using RD.pack r3
  · have r1 := uniswapV3Pool_block_2543_taken (immWords := wordsOf (immStore v))
      (by omega) (by simp only [hz]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    by_cases hc : a.priceLimit.toNat < price.toNat
    · have hg : UInt256.lt a.priceLimit price = ⟨1⟩ := ult_one hc
      have r2 := uniswapV3Pool_block_2618_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 11 ≤ 1024; omega)
        (by rw [amountDeltaMask160, hmask', hzero, hp, hg]; rfl) r1
      simp only [uniswapV3Pool_block_2618_fallthrough_stack] at r2
      have r3 := uniswapV3Pool_block_2650 (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 10 ≤ 1024; omega) r2
      have hg' : UInt256.gt a.priceLimit (UInt256.ofNat 4295128739) =
          (decide (swapLimitForPrice a price)).toUInt256 := by
        simp only [swapLimitForPrice, hz, if_true, hc, true_and]
        rfl
      simpa only [uniswapV3Pool_block_2650_stack, amountDeltaMask160, hmask, hg',
        hzero, hz] using RD.pack r3
    · have hg : UInt256.lt a.priceLimit price = ⟨0⟩ := ult_zero (by omega)
      have r2 := uniswapV3Pool_block_2618_taken (immWords := wordsOf (immStore v))
        (by change R.length + 2 + 11 ≤ 1024; omega)
        (by rw [amountDeltaMask160, hmask', hzero, hp, hg]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      simpa only [uniswapV3Pool_block_2618_taken_stack, amountDeltaMask160, hmask',
        hzero, hp, hg, swapLimitForPrice, hz, if_true, hc, false_and,
        decide_false] using RD.pack r2


theorem swapLimitX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p price x1 x2 x3 x4 x6 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2543⟩
      (p :: x1 :: x2 :: x3 :: x4 :: a.priceLimit :: x6 :: a.zeroForOne.toUInt256 :: R)
      mem aw rdata σ k C)
    (hl : a.priceLimit.toNat < 2 ^ 160)
    (hp : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) (memLoad p mem) = price)
    (hov : R.length + 13 ≤ 1024) :
    (¬swapLimitForPrice a price ∧ RDrev (deployedRuntime v) g s0) ∨
    (swapLimitForPrice a price ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨2723⟩
      (p :: x1 :: x2 :: x3 :: x4 :: a.priceLimit :: x6 :: a.zeroForOne.toUInt256 :: R)
      mem (M aw p ⟨32⟩) rdata σ k' C') := by
  obtain ⟨kr, Cr, rr⟩ := swapLimitCondX (v := v) a rd hl hp hov
  by_cases hv : swapLimitForPrice a price
  · simp only [hv, decide_true] at rr
    have r1 := uniswapV3Pool_block_2668_taken (immWords := wordsOf (immStore v))
      (by change R.length + 8 + 2 ≤ 1024; omega) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
    exact Or.inr ⟨hv, _, _, r1⟩
  · simp only [hv, decide_false] at rr
    have r1 := uniswapV3Pool_block_2668_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 8 + 2 ≤ 1024; omega) rfl rr
    have r2 := uniswapV3Pool_block_2673 (immWords := wordsOf (immStore v))
      (by change R.length + 8 + 5 ≤ 1024; omega) r1
    exact Or.inl ⟨hv, r2⟩

end Benchmarks.UniswapV3.Pool
