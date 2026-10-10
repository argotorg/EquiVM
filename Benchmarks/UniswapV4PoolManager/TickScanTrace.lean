import Benchmarks.UniswapV4PoolManager.TickScanBranchTrace
import Benchmarks.UniswapV4PoolManager.TickCompressTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

/-- The complete inlined bitmap scan, from the compression remainder to the next-tick join. -/
theorem tickScanTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick spacing step state fee x0 x1 params x3 x4 x6 x7 : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (lte : Bool) (hstack : R.length+33 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨19221⟩
      ([tick, spacing, ⟨0⟩, spacing, tick, spacing, poolSlot id, step, state, fee, if lte then ⟨0⟩ else ⟨1⟩,
        x0, x1, params, x3, x4, fee, x6, x7, if lte then ⟨0⟩ else ⟨1⟩, step, poolSlot id, state] ++ R)
      mem aw rdata evm.accountMap k C) :
    let compressed := tickScanCompressed tick spacing lte
    let masked := tickScanMasked evm id compressed lte
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19401⟩
      ([(decide (masked ≠ ⟨0⟩)).toUInt256, tickScanResultWord compressed spacing masked lte,
        UInt256.ofNat (2^256-887272), step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64,
        UInt256.ofNat (2^128-1), state, fee, if lte then ⟨0⟩ else ⟨1⟩, x0, x1, params, x3, x4,
        fee, x6, x7, if lte then ⟨0⟩ else ⟨1⟩, step, poolSlot id, state] ++ R)
      (tickScanMemory mem id compressed)
      (M (M (M aw ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64))
      rdata evm.accountMap k' C' := by
  have rd1 := tickCompressTrace v lte (by simp; omega) h
  obtain ⟨k2, C2, hC2, rd2⟩ := tickScanBranchTrace v lte hstack hI rd1
  exact ⟨k2, C2, by omega, rd2⟩

end Benchmarks.UniswapV4PoolManager
