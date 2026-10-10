import Benchmarks.UniswapV3.Pool.SwapStepCapTrace
import Benchmarks.UniswapV3.Pool.SwapStepBudgetTrace
import Benchmarks.UniswapV3.Pool.FullMathRoundTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

noncomputable def swapStepFinalWords (a : SwapStepArgs)
    (currentRaw targetRaw liquidityRaw feeRaw : UInt256) : List UInt256 :=
  [(swapStepMax a).toUInt256, (swapStepExactIn a).toUInt256,
   (swapStepZeroForOne a).toUInt256, swapStepFee a, swapStepOutput a, swapStepAmount a true,
   swapStepRawPrice a currentRaw targetRaw] ++
    swapStepRawWords a currentRaw targetRaw liquidityRaw feeRaw

theorem swapStepFeeGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12855⟩
      (swapStepCalcWords a currentRaw targetRaw liquidityRaw feeRaw
        (swapStepAmount a true) (swapStepOutput a) ++ R) mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (ha : a.Fits) (hv : swapStepPriceValid a) (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12886⟩
      ((swapStepUnusedFee a).toUInt256 :: swapStepCalcWords a currentRaw targetRaw liquidityRaw
        feeRaw (swapStepAmount a true) (swapStepOutput a) ++ R) mem aw rdata σ k' C' := by
  have hp : UInt256.land (UInt256.ofNat (2 ^ 160 - 1))
      (swapStepRawPrice a currentRaw targetRaw) = swapStepPrice a := by
    rw [u256_land_comm]
    exact swapStepRawPrice_clean a currentRaw targetRaw hc ht ha hv.2.2
  have ht' : UInt256.land (UInt256.ofNat (2 ^ 160 - 1)) targetRaw = a.target := by
    rw [u256_land_comm, ht]
  have hn : UInt256.isZero (swapStepMax a).toUInt256 = (!swapStepMax a).toUInt256 := by
    cases swapStepMax a <;> rfl
  cases hi : swapStepExactIn a
  · have r1 := uniswapV3Pool_block_12855_taken (immWords := wordsOf (immStore v))
      (by change R.length + 10 + 5 ≤ 1024; omega) (by simp only [hi]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simpa only [uniswapV3Pool_block_12855_taken_stack, swapStepUnusedFee, hi,
      Bool.false_and, swapStepCalcWords, List.cons_append, List.nil_append] using RD.pack r1
  · have r1 := uniswapV3Pool_block_12855_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 10 + 5 ≤ 1024; omega) (by simp only [hi]; rfl) rd
    have r2 := uniswapV3Pool_block_12863 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 16 ≤ 1024; omega) r1
    simpa only [uniswapV3Pool_block_12863_stack, amountDeltaMask160, hp, ht',
      swapStepMaxWord, hn, swapStepUnusedFee, hi, Bool.true_and, swapStepCalcWords,
      swapStepRawWords, List.cons_append, List.nil_append] using RD.pack r2

theorem swapStepFeeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12855⟩
      (swapStepCalcWords a currentRaw targetRaw liquidityRaw feeRaw
        (swapStepAmount a true) (swapStepOutput a) ++ R) mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (hf : UInt256.land feeRaw (UInt256.ofNat (2 ^ 24 - 1)) = a.fee)
    (ha : a.Fits) (hv : swapStepPriceValid a) (hov : R.length + 33 ≤ 1024) :
    (¬swapStepFeeValid a ∧ RDrev (deployedRuntime v) g s0) ∨
    (swapStepFeeValid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12930⟩
      (swapStepFinalWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
      mem aw rdata σ k' C') := by
  obtain ⟨kg, Cg, rg⟩ := swapStepFeeGuardX (v := v) a rd hc ht ha hv (by omega)
  cases hh : swapStepUnusedFee a
  · simp only [hh] at rg
    have r1 := uniswapV3Pool_block_12886_taken (immWords := wordsOf (immStore v))
      (by change R.length + 12 + 2 ≤ 1024; omega) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rg
    have r2 := uniswapV3Pool_block_12901 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 13 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    have hf' : UInt256.land (UInt256.ofNat 16777215) feeRaw = a.fee := by
      rw [u256_land_comm]
      exact hf
    simp only [uniswapV3Pool_block_12901_stack, swapStepComplementRaw a feeRaw hf, hf'] at r2
    rcases fullMathRoundX (v := v) r2
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by change R.length + 12 + 21 ≤ 1024; omega) with
      ⟨hbad, rr⟩ | ⟨hr, kr, Cr, _, rr⟩
    · exact Or.inl ⟨by simpa only [swapStepFeeValid, hh, Bool.false_eq_true, if_false]
        using hbad, rr⟩
    · have r3 := uniswapV3Pool_block_12927 (immWords := wordsOf (immStore v))
        (by change R.length + 8 + 5 ≤ 1024; omega) rr
      refine Or.inr ⟨by simpa only [swapStepFeeValid, hh, Bool.false_eq_true, if_false]
        using hr, ?_⟩
      simpa only [uniswapV3Pool_block_12927_stack, swapStepFinalWords, swapStepCalcWords,
        swapStepRawWords, swapStepFee, hh, Bool.false_eq_true, if_false,
        List.cons_append, List.nil_append] using RD.pack r3
  · simp only [hh] at rg
    have r1 := uniswapV3Pool_block_12886_fallthrough (immWords := wordsOf (immStore v))
      (by change R.length + 12 + 2 ≤ 1024; omega) rfl rg
    have r2 := uniswapV3Pool_block_12892 (immWords := wordsOf (immStore v))
      (by change R.length + 3 + 11 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    refine Or.inr ⟨by simp only [swapStepFeeValid, hh, if_true], ?_⟩
    simpa only [uniswapV3Pool_block_12892_stack, swapStepFinalWords, swapStepCalcWords,
      swapStepRawWords, swapStepFee, hh, if_true, List.cons_append, List.nil_append]
      using RD.pack r2

end Benchmarks.UniswapV3.Pool
