import Benchmarks.UniswapV4PoolManager.TickScanTrace
import Benchmarks.UniswapV4PoolManager.TickClampTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickScanPriceTrace {I : ExecutionEnv} {g : Sat256} {s0 evm : State}
    {mem rdata : ByteArray} {aw id tick spacing step state fee x0 x1 params x3 x4 x6 x7 : UInt256}
    {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (lte : Bool) (hstack : R.length+33 ≤ 1024) (hI : evm.executionEnv = I)
    (h : RD (deployedRuntime v) I g s0 ⟨19221⟩
      ([tick, spacing, ⟨0⟩, spacing, tick, spacing, poolSlot id, step, state, fee, if lte then ⟨0⟩ else ⟨1⟩,
        x0, x1, params, x3, x4, fee, x6, x7, if lte then ⟨0⟩ else ⟨1⟩, step, poolSlot id, state] ++ R)
      mem aw rdata evm.accountMap k C) :
    let compressed := tickScanCompressed tick spacing lte
    let masked := tickScanMasked evm id compressed lte
    let next := tickScanResultWord compressed spacing masked lte
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19479⟩
      ([tickSqrtPrice (EVM.signed (tickClampWord next)), UInt256.ofNat (2^160-1),
        step, UInt256.ofNat 96, UInt256.ofNat 1, UInt256.ofNat 64,
        UInt256.ofNat (2^128-1), state, fee, if lte then ⟨0⟩ else ⟨1⟩, x0, x1, params, x3, x4,
        fee, x6, x7, if lte then ⟨0⟩ else ⟨1⟩, step, poolSlot id, state] ++ R)
      (tickClampMemory (tickScanMemory mem id compressed) step next (decide (masked ≠ ⟨0⟩)))
      (M (M (M (M (M aw ⟨0⟩ ⟨32⟩) (UInt256.ofNat 32) ⟨32⟩) ⟨0⟩ (UInt256.ofNat 64))
        (step+UInt256.ofNat 64) ⟨32⟩) (step+UInt256.ofNat 32) ⟨32⟩)
      rdata evm.accountMap k' C' := by
  obtain ⟨k1, C1, hC1, rd1⟩ := tickScanTrace v lte hstack hI h
  obtain ⟨k2, C2, hC2, rd2⟩ := tickClampPriceTrace v
    (by change R.length+28 ≤ 1024; omega) rd1
  exact ⟨k2, C2, hC1.trans hC2, rd2⟩

end Benchmarks.UniswapV4PoolManager
