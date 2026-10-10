import Benchmarks.UniswapV3.Pool.SwapCallbackBuild
import Benchmarks.UniswapV3.Pool.FlashCallbackCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapCallbackCallPC (zeroForOne : Bool) : UInt256 :=
  if zeroForOne then ⟨4737⟩ else ⟨5039⟩

def swapCallbackAfterPC (zeroForOne : Bool) : UInt256 :=
  if zeroForOne then ⟨4738⟩ else ⟨5040⟩

def swapCallbackExit (zeroForOne : Bool) : UInt256 :=
  if zeroForOne then ⟨4754⟩ else ⟨5056⟩

theorem swapCallbackNoCodeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw len x1 x2 x3 x4 x5 x6 x7 x8 selector target : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapCallbackEntry zeroForOne)
      (len :: x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: selector :: target :: R)
      mem aw rdata σ k C)
    (hc : extCodeSizeWord σ target = ⟨0⟩) (hov : R.length + 14 ≤ 1024) :
    RDrev (deployedRuntime v) g s0 := by
  cases zeroForOne
  · obtain ⟨k', C', rd'⟩ := uniswapV3Pool_block_4987_fallthrough
      (immWords := wordsOf (immStore v)) hov (by rw [hc]; decide +kernel) rd
    exact uniswapV3Pool_block_5032 (immWords := wordsOf (immStore v))
      (by change R.length + 10 + 2 ≤ 1024; omega) rd'
  · obtain ⟨k', C', rd'⟩ := uniswapV3Pool_block_4685_fallthrough
      (immWords := wordsOf (immStore v)) hov (by rw [hc]; decide +kernel) rd
    exact uniswapV3Pool_block_4730 (immWords := wordsOf (immStore v))
      (by change R.length + 10 + 2 ≤ 1024; omega) rd'

theorem swapCallbackGuardX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat}
    {aw p len x1 x3 x4 x5 x6 x7 x8 selector target endPtr size : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapCallbackEntry zeroForOne)
      (len :: x1 :: (p + ⟨132⟩) :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: selector :: target :: R)
      mem aw rdata σ k C)
    (hload : memLoad (UInt256.ofNat 64) mem = p)
    (hend : (p + ⟨132⟩) + UInt256.land (len + UInt256.ofNat 31)
      (UInt256.lnot (UInt256.ofNat 31)) = endPtr)
    (hsize : UInt256.sub endPtr p = size)
    (hc : extCodeSizeWord σ target ≠ ⟨0⟩) (hov : R.length + 14 ≤ 1024) :
    ∃ gasArg k' C', RD (deployedRuntime v) ee g s0 (swapCallbackCallPC zeroForOne)
      ([gasArg, target, ⟨0⟩, p, size, p, ⟨0⟩, endPtr, selector, target] ++ R)
      mem (M aw (UInt256.ofNat 64) ⟨32⟩) rdata σ k' C' := by
  cases zeroForOne
  · obtain ⟨k', C', rd'⟩ := uniswapV3Pool_block_4987_taken
      (immWords := wordsOf (immStore v)) hov
      (by rw [isZero_eq_zero_of_ne hc]; decide +kernel)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [uniswapV3Pool_block_4987_taken_stack, hload, hend, hsize] at rd'
    exact ⟨_, _, _, uniswapV3Pool_block_5036 (immWords := wordsOf (immStore v))
      (by change R.length + 9 + 1 ≤ 1024; omega) rd'⟩
  · obtain ⟨k', C', rd'⟩ := uniswapV3Pool_block_4685_taken
      (immWords := wordsOf (immStore v)) hov
      (by rw [isZero_eq_zero_of_ne hc]; decide +kernel)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
    simp only [uniswapV3Pool_block_4685_taken_stack, hload, hend, hsize] at rd'
    exact ⟨_, _, _, uniswapV3Pool_block_4734 (immWords := wordsOf (immStore v))
      (by change R.length + 9 + 1 ≤ 1024; omega) rd'⟩

theorem swapCallbackFailureX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapCallbackAfterPC zeroForOne)
      (⟨0⟩ :: R) mem aw rdata σ k C) (hov : R.length + 4 ≤ 1024) :
    RDrev (deployedRuntime v) g s0 := by
  cases zeroForOne
  · have rd' := uniswapV3Pool_block_5040_fallthrough (immWords := wordsOf (immStore v))
      (by omega) (by decide +kernel) rd
    exact uniswapV3Pool_block_5047 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 3 ≤ 1024; omega) rd'
  · have rd' := uniswapV3Pool_block_4738_fallthrough (immWords := wordsOf (immStore v))
      (by omega) (by decide +kernel) rd
    exact uniswapV3Pool_block_4745 (immWords := wordsOf (immStore v))
      (by change R.length + 1 + 3 ≤ 1024; omega) rd'

theorem swapCallbackSuccessX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (zeroForOne : Bool)
    (rd : RD (deployedRuntime v) ee g s0 (swapCallbackAfterPC zeroForOne)
      (⟨1⟩ :: R) mem aw rdata σ k C) (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (swapCallbackExit zeroForOne)
      (⟨0⟩ :: R) mem aw rdata σ k' C' := by
  cases zeroForOne
  · exact ⟨_, _, uniswapV3Pool_block_5040_taken (immWords := wordsOf (immStore v))
      hov (by decide +kernel)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd⟩
  · exact ⟨_, _, uniswapV3Pool_block_4738_taken (immWords := wordsOf (immStore v))
      hov (by decide +kernel)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd⟩

end Benchmarks.UniswapV3.Pool
