import Benchmarks.UniswapV3.Pool.SwapBalanceAfter
import Benchmarks.UniswapV3.Pool.FlashRepaymentTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapRepayComparePC (zeroForOne : Bool) : UInt256 :=
  if zeroForOne then ⟨4776⟩ else ⟨5078⟩

def swapRepayNextPC (zeroForOne : Bool) : UInt256 :=
  if zeroForOne then ⟨4833⟩ else ⟨5135⟩

theorem swapRepayAddEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw before after p exactWord cache snap amount0 amount1 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapBalanceAfterReturn zeroForOne)
      ([after, before, p, exactWord, cache, snap, amount1, amount0] ++ R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨15885⟩
      ([(if zeroForOne then amount0 else amount1), before, swapRepayComparePC zeroForOne,
        after, before, p, exactWord, cache, snap, amount1, amount0] ++ R) mem aw rdata σ k' C' := by
  cases zeroForOne
  · exact ⟨_, _, uniswapV3Pool_block_5068 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 11 ≤ 1024; omega)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd⟩
  · exact ⟨_, _, uniswapV3Pool_block_4766 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd⟩

theorem swapRepayCompareX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw required after : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapRepayComparePC zeroForOne)
      (required :: after :: R) mem aw rdata σ k C) (hov : R.length + 5 ≤ 1024) :
    (¬ required.toNat ≤ after.toNat ∧ RDrev (deployedRuntime v) g s0) ∨
    (required.toNat ≤ after.toNat ∧ ∃ k' C', RD (deployedRuntime v) ee g s0
      (swapRepayNextPC zeroForOne) R mem aw rdata σ k' C') := by
  by_cases hp : required.toNat ≤ after.toNat
  · refine Or.inr ⟨hp, ?_⟩
    cases zeroForOne
    · exact ⟨_, _, uniswapV3Pool_block_5078_taken (immWords := wordsOf (immStore v))
        (by omega) (by rw [ugt_zero hp]; decide +kernel)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd⟩
    · exact ⟨_, _, uniswapV3Pool_block_4776_taken (immWords := wordsOf (immStore v))
        (by omega) (by rw [ugt_zero hp]; decide +kernel)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd⟩
  · refine Or.inl ⟨hp, ?_⟩
    cases zeroForOne
    · have rr := uniswapV3Pool_block_5078_fallthrough (immWords := wordsOf (immStore v))
        (by omega) (by rw [ugt_one (Nat.lt_of_not_ge hp)]; decide +kernel) rd
      exact uniswapV3Pool_block_5085 (immWords := wordsOf (immStore v)) hov rr
    · have rr := uniswapV3Pool_block_4776_fallthrough (immWords := wordsOf (immStore v))
        (by omega) (by rw [ugt_one (Nat.lt_of_not_ge hp)]; decide +kernel) rd
      exact uniswapV3Pool_block_4783 (immWords := wordsOf (immStore v)) hov rr

theorem swapRepayMergeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw before : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapRepayNextPC zeroForOne)
      (before :: R) mem aw rdata σ k C) (hov : R.length + 1 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨5137⟩ R mem aw rdata σ k' C' := by
  cases zeroForOne
  · exact ⟨_, _, uniswapV3Pool_block_5135 (immWords := wordsOf (immStore v)) hov rd⟩
  · exact ⟨_, _, uniswapV3Pool_block_4833 (immWords := wordsOf (immStore v)) hov
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd⟩

theorem swapRepayMathX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw before after p exactWord cache snap amount0 amount1 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapBalanceAfterReturn zeroForOne)
      ([after, before, p, exactWord, cache, snap, amount1, amount0] ++ R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) :
    (¬ flashRepayValid before (if zeroForOne then amount0 else amount1) after ∧
      RDrev (deployedRuntime v) g s0) ∨
    (flashRepayValid before (if zeroForOne then amount0 else amount1) after ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨5137⟩
        ([p, exactWord, cache, snap, amount1, amount0] ++ R) mem aw rdata σ k' C') := by
  obtain ⟨k1, C1, r1⟩ := swapRepayAddEntryX (v := v) zeroForOne rd (by omega)
  rcases safeAddX (v := v) r1
      (by rw [uniswapV3PoolPatchedValidJumps v]; cases zeroForOne <;> native_decide)
      (by change R.length + 8 + 6 ≤ 1024; omega) with ⟨hbad, rr⟩ | ⟨hgood, k2, C2, _, r2⟩
  · exact Or.inl ⟨fun h ↦ hbad h.1, rr⟩
  rcases swapRepayCompareX (v := v) zeroForOne r2
      (by change R.length + 7 + 5 ≤ 1024; omega) with ⟨hbad, rr⟩ | ⟨hcmp, k3, C3, r3⟩
  · exact Or.inl ⟨fun h ↦ hbad h.2, rr⟩
  · obtain ⟨k4, C4, r4⟩ := swapRepayMergeX (v := v) zeroForOne r3
      (by change R.length + 6 + 1 ≤ 1024; omega)
    exact Or.inr ⟨⟨hgood, hcmp⟩, k4, C4, r4⟩

end Benchmarks.UniswapV3.Pool
