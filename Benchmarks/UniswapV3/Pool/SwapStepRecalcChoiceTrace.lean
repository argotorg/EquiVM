import Benchmarks.UniswapV3.Pool.SwapStepRecalcCallTrace
import Benchmarks.UniswapV3.Pool.SwapStepRecalcReuseTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepRecalcBranchX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (zero input keep : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapStepRecalcGuardPC zero input)
      (keep.toUInt256 :: R) mem aw rdata σ k C) (hov : R.length + 2 ≤ 1024) :
    RD (deployedRuntime v) ee g s0
      (if keep then swapStepRecalcReusePC zero input else swapStepRecalcCallPC zero input)
      R mem aw rdata σ (k + 3) (C + 14) := by
  cases keep
  · cases input <;> cases zero
    · exact uniswapV3Pool_block_12800_fallthrough (immWords := wordsOf (immStore v))
        hov rfl rd
    · exact uniswapV3Pool_block_12722_fallthrough (immWords := wordsOf (immStore v))
        hov rfl rd
    · exact uniswapV3Pool_block_12763_fallthrough (immWords := wordsOf (immStore v))
        hov rfl rd
    · exact uniswapV3Pool_block_12685_fallthrough (immWords := wordsOf (immStore v))
        hov rfl rd
  · cases input <;> cases zero
    · exact uniswapV3Pool_block_12800_taken (immWords := wordsOf (immStore v))
        hov (by decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    · exact uniswapV3Pool_block_12722_taken (immWords := wordsOf (immStore v))
        hov (by decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    · exact uniswapV3Pool_block_12763_taken (immWords := wordsOf (immStore v))
        hov (by decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    · exact uniswapV3Pool_block_12685_taken (immWords := wordsOf (immStore v))
        hov (by decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd

theorem swapStepRecalcChoiceX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw other : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : SwapStepArgs) (input : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapStepRecalcGuardPC (swapStepZeroForOne a) input)
      ((swapStepKeep a input).toUInt256 ::
        swapStepRecalcWords a input currentRaw targetRaw liquidityRaw feeRaw other ++ R)
      mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (ha : a.Fits) (hv : swapStepPriceValid a) (hov : R.length + 42 ≤ 1024) :
    (¬swapStepRecalcValid a input ∧ RDrev (deployedRuntime v) g s0) ∨
    (swapStepRecalcValid a input ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 (swapStepRecalcJoinPC (swapStepZeroForOne a) input)
        (swapStepAmount a input ::
          swapStepRecalcWords a input currentRaw targetRaw liquidityRaw feeRaw other ++ R)
        mem aw rdata σ k' C') := by
  have rb := swapStepRecalcBranchX (v := v) (swapStepZeroForOne a) input
    (swapStepKeep a input) rd (by change R.length + 12 + 2 ≤ 1024; omega)
  cases hk : swapStepKeep a input
  · simp only [hk, Bool.false_eq_true, if_false] at rb
    rcases swapStepRecalcCallX (v := v) a input rb hc ht hl ha hv hov with
      ⟨hbad, rr⟩ | ⟨hd, kr, Cr, rr⟩
    · exact Or.inl ⟨by simpa only [swapStepRecalcValid, hk, Bool.false_eq_true, if_false]
        using hbad, rr⟩
    · refine Or.inr ⟨by simpa only [swapStepRecalcValid, hk, Bool.false_eq_true, if_false]
        using hd, kr, Cr, ?_⟩
      simpa only [swapStepAmount, hk, Bool.false_eq_true, if_false] using rr
  · simp only [hk, if_true] at rb
    have rr := swapStepRecalcReuseX (v := v) a input rb (by omega)
    refine Or.inr ⟨by simp only [swapStepRecalcValid, hk, if_true], ?_⟩
    simpa only [swapStepAmount, hk, if_true] using RD.pack rr

end Benchmarks.UniswapV3.Pool
