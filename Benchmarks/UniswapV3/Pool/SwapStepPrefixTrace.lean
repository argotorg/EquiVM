import Benchmarks.UniswapV3.Pool.SwapStepModel
import Benchmarks.UniswapV3.Pool.AmountDeltaSortTrace
import Benchmarks.UniswapV3.Pool.SignedComparison
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_040

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapStepRawWords (a : SwapStepArgs) (currentRaw targetRaw liquidityRaw feeRaw : UInt256) :
    List UInt256 :=
  [feeRaw, EVM.wordOfInt a.remaining, liquidityRaw, targetRaw, currentRaw]

def swapStepReadyWords (a : SwapStepArgs) (currentRaw targetRaw liquidityRaw feeRaw : UInt256) :
    List UInt256 :=
  [(swapStepExactIn a).toUInt256, (swapStepZeroForOne a).toUInt256, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩] ++
    swapStepRawWords a currentRaw targetRaw liquidityRaw feeRaw

def swapStepBranchPC (a : SwapStepArgs) : UInt256 :=
  if swapStepExactIn a then ⟨12479⟩ else ⟨12580⟩

theorem swapStepDirectionWord (a : SwapStepArgs) :
    UInt256.isZero (UInt256.lt a.current a.target) = (swapStepZeroForOne a).toUInt256 := by
  by_cases h : a.target.toNat ≤ a.current.toNat
  · rw [ult_zero h]
    simp only [swapStepZeroForOne, decide_eq_true h]
    rfl
  · rw [ult_one (by omega : a.current.toNat < a.target.toNat)]
    simp only [swapStepZeroForOne, decide_eq_false h]
    rfl

theorem swapStepInputWord (a : SwapStepArgs)
    (hr : -(2 ^ 255 : Int) ≤ a.remaining ∧ a.remaining < 2 ^ 255) :
    UInt256.isZero (UInt256.slt (EVM.wordOfInt a.remaining) (UInt256.ofNat 0)) =
      (swapStepExactIn a).toUInt256 := by
  have h := slt_wordOfInt a.remaining 0 hr.1 hr.2 (by decide) (by decide)
  change UInt256.slt (EVM.wordOfInt a.remaining) (UInt256.ofNat 0) = _ at h
  rw [h]
  by_cases hn : 0 ≤ a.remaining
  · simp only [if_neg (by omega : ¬a.remaining < 0), swapStepExactIn, decide_eq_true hn]
    rfl
  · simp only [if_pos (by omega : a.remaining < 0), swapStepExactIn, decide_eq_false hn]
    rfl

theorem swapStepPrefixX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12447⟩
      (swapStepRawWords a currentRaw targetRaw liquidityRaw feeRaw ++ R) mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (hr : -(2 ^ 255 : Int) ≤ a.remaining ∧ a.remaining < 2 ^ 255)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (swapStepBranchPC a)
      (swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
      mem aw rdata σ k' C' := by
  have hs : UInt256.slt (EVM.wordOfInt a.remaining) (UInt256.ofNat 0) =
      if a.remaining < 0 then ⟨1⟩ else ⟨0⟩ :=
    slt_wordOfInt a.remaining 0 hr.1 hr.2 (by decide) (by decide)
  by_cases hn : 0 ≤ a.remaining
  · have rr := uniswapV3Pool_block_12447_fallthrough (immWords := wordsOf (immStore v)) hov
      (by rw [hs, if_neg (by omega : ¬a.remaining < 0)]; rfl) rd
    have rr' := RD.pack rr
    simpa only [swapStepBranchPC, swapStepReadyWords, swapStepRawWords,
      uniswapV3Pool_block_12447_fallthrough_stack, amountDeltaMask160, hc, ht,
      swapStepInputWord a hr, swapStepDirectionWord, swapStepExactIn, decide_eq_true hn,
      if_true, List.cons_append, List.nil_append] using rr'
  · have rr := uniswapV3Pool_block_12447_taken (immWords := wordsOf (immStore v)) hov
      (by rw [hs, if_pos (by omega : a.remaining < 0)]; decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have rr' := RD.pack rr
    simpa only [swapStepBranchPC, swapStepReadyWords, swapStepRawWords,
      uniswapV3Pool_block_12447_taken_stack, amountDeltaMask160, hc, ht,
      swapStepInputWord a hr, swapStepDirectionWord, swapStepExactIn, decide_eq_false hn,
      Bool.false_eq_true, if_false, List.cons_append, List.nil_append] using rr'

end Benchmarks.UniswapV3.Pool
