import Benchmarks.UniswapV4PoolManager.LeastSignificantBit
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_061

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- The inlined least-bit computation also forms the next tick in the increasing direction. -/
theorem leastSignificantBitNextTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw x spacing compressed initialized x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+31 ≤ 1024) (hx : x ≠ ⟨0⟩)
    (h : RD (deployedRuntime v) I g s0 ⟨21213⟩
      ([x, spacing, compressed, initialized, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ R)
      mem aw rdata σ k C) :
    RD (deployedRuntime v) I g s0 ⟨21435⟩
      ([UInt256.signextend ⟨2⟩ (UInt256.mul
          (UInt256.signextend ⟨2⟩ (UInt256.signextend ⟨2⟩ compressed + UInt256.signextend ⟨2⟩
            (UInt256.land (UInt256.sub (leastSignificantBit x) (UInt256.land ⟨255⟩ compressed)) ⟨255⟩))) spacing),
        initialized, UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913128752664,
        x13, ⟨96⟩, ⟨1⟩, ⟨64⟩, UInt256.ofNat 340282366920938463463374607431768211455,
        x15, x9, x12, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15] ++ R)
      mem aw rdata σ (k+61) (C+196) := by
  have rd := poolManagerBlocks.poolManager_block_21213 hstack h
  have hl := lsbCompiledResult_eq hx
  unfold lsbCompiledResult lsbCompiledHigh lsbCompiledIndex lsbLowBit
    lsbMultiplier lsbHighTable lsbLowTable at hl
  simp only [poolManagerBlocks.poolManager_block_21213_stack, hl] at rd
  exact rd

end Benchmarks.UniswapV4PoolManager
