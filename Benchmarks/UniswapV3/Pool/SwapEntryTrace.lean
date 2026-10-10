import Benchmarks.UniswapV3.Pool.SwapPrefixSource
import Benchmarks.UniswapV3.Pool.SignedWordZero
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_011

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapWords (a : SwapArgs) (dataStart dataLength : UInt256) : List UInt256 :=
  [dataLength, dataStart, a.priceLimit, EVM.wordOfInt a.amountSpecified,
    a.zeroForOne.toUInt256, EVM.word a.recipient.val]

theorem swapEntryX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {mem rdata : ByteArray} {aw ret dataStart dataLength : UInt256} {k C : Nat}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨2292⟩
      (swapWords a dataStart dataLength ++ ret :: R) mem aw rdata σ k C)
    (ha : a.Fits) (hov : R.length + 14 ≤ 1024) :
    ((ee.codeOwner ≠ v.original ∨ a.amountSpecified = 0) ∧ RDrev (deployedRuntime v) g s0) ∨
    (ee.codeOwner = v.original ∧ a.amountSpecified ≠ 0 ∧ ∃ k' C',
      RD (deployedRuntime v) ee g s0 ⟨2358⟩
        (⟨0⟩ :: ⟨0⟩ :: swapWords a dataStart dataLength ++ ret :: R) mem aw rdata σ k' C') := by
  have r0 := uniswapV3Pool_block_2292 (immWords := wordsOf (immStore v))
    (by change R.length + 7 + 4 ≤ 1024; omega)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  rcases noDelegateCallX (v := v) r0
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by change R.length + 9 + 5 ≤ 1024; omega) with ⟨rr, hself⟩ | ⟨hself, k1, C1, r1⟩
  · exact Or.inl ⟨Or.inl hself, rr⟩
  · by_cases hn : a.amountSpecified = 0
    · have r2 := uniswapV3Pool_block_2303_fallthrough (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 8 ≤ 1024; omega) (by rw [hn]; rfl) r1
      have r3 := uniswapV3Pool_block_2309 (immWords := wordsOf (immStore v))
        (by change R.length + 9 + 5 ≤ 1024; omega) r2
      exact Or.inl ⟨Or.inr hn, r3⟩
    · have hword : EVM.wordOfInt a.amountSpecified ≠ (UInt256.ofNat 0) := by
        intro hz
        exact hn ((wordOfInt_zero_iff_signed a.amountSpecified ha.1.1 ha.1.2).mp hz)
      have r2 := uniswapV3Pool_block_2303_taken (immWords := wordsOf (immStore v))
        (by change R.length + 3 + 8 ≤ 1024; omega) hword
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      exact Or.inr ⟨hself, hn, _, _, r2⟩

end Benchmarks.UniswapV3.Pool
