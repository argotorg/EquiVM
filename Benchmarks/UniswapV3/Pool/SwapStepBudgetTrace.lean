import Benchmarks.UniswapV3.Pool.SwapStepPrefixTrace
import Benchmarks.UniswapV3.Pool.WordSubMask
import Benchmarks.UniswapV3.Pool.FullMathTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepComplementRaw (a : SwapStepArgs) (feeRaw : UInt256)
    (hf : UInt256.land feeRaw (UInt256.ofNat (2 ^ 24 - 1)) = a.fee) :
    UInt256.land (UInt256.ofNat 16777215) (UInt256.sub (UInt256.ofNat 1000000) feeRaw) =
      swapStepComplement a := by
  rw [swapStepComplement, ← hf,
    wordSub_land_right ⟨24, by decide⟩ _ _ _ (by decide), u256_land_comm]
  rfl

theorem swapStepBudgetX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12479⟩
      (swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
      mem aw rdata σ k C)
    (hf : UInt256.land feeRaw (UInt256.ofNat (2 ^ 24 - 1)) = a.fee)
    (hi : swapStepExactIn a = true) (hov : R.length + 29 ≤ 1024) :
    (¬swapStepBudgetValid a ∧ RDrev (deployedRuntime v) g s0) ∨
    (swapStepBudgetValid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12504⟩
      (swapStepBudget a :: ⟨0⟩ ::
        swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
      mem aw rdata σ k' C') := by
  have r0 := uniswapV3Pool_block_12479 (immWords := wordsOf (immStore v))
    (R := [liquidityRaw, targetRaw, currentRaw] ++ R)
    (by change R.length + 3 + 14 ≤ 1024; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_12479_stack, swapStepComplementRaw a feeRaw hf] at r0
  rcases fullMathX (v := v) r0
    (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
    (by change R.length + 12 + 16 ≤ 1024; omega)
    with ⟨hb, rr⟩ | ⟨hv, k', C', _, rr⟩
  · exact Or.inl ⟨by simpa only [swapStepBudgetValid, hi, if_true] using hb, rr⟩
  · refine Or.inr ⟨by simpa only [swapStepBudgetValid, hi, if_true] using hv, k', C', ?_⟩
    simpa only [swapStepBudget, hi, if_true, swapStepReadyWords, swapStepRawWords,
      List.cons_append, List.nil_append] using rr

end Benchmarks.UniswapV3.Pool
